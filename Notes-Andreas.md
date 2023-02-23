# Setup

* Clone repo
* Install C dependencies

sudo apt install libpcre3-dev and more

Then launch the engine using: `./scripts/dev.sh graphql-engine`
And the benchmarks (which will launch a db):

```
cd server/benchmarks
bench.sh huge_schema
```

Alternatively test if the setup works by launch postgres instead of benchmarks using:

```
./scripts/dev.sh postgres
```

# Closure Sharing results

main = ghc-debug-stub

Notably dictionaries are a large part of these functions free variables. I don’t know enough about the codebase to know if these can be specialized away. But if so this would probably already be a good amount of the possible savings.

The important case is a single recursive group of allocated functions which amounts to ~50% of the potential savings.

# Source of duplication

Almost all of the potential savings come from a small part of the code base:

* Almost all (>90%) originate from Hasura.GraphQL.Schema.Select
* They originate from calls to `columParser` with the biggest chunk of data coming out of the `fieldSelection` function.
* This function ends up being fully inlined into `defaultTableSelectionSet`

# Nature of the shared data:

Most of it comes from recursive groups of (allocated) function closures. That is something along the lines of:

```haskell
foo ... =
    let bar = ... go1 x y z ...
    in ...
  where
    go1 fvs:{go1, go2, go3, more_fvs} x y z = ... go1 ... go2 ... go3 ...
    go2 fvs:{go1, go2, go3, more_fvs} x y z = ... go1 ... go2 ... go3 ...
    go3 fvs:{go1, go2, go3, more_fvs} x y z = ... go1 ... go2 ... go3 ...
```

In terms of savings there are two major parts:

* A large part of the shared data (the `more_fvs` part) are reference to `Applicative` and `MonadParse` instances.
* Another large part are the references to the (mutually recursive) `go` functions.
* A smaller part consists of references to "real" free variables.

## Tackling specialization

Specialization could potentially get rid of the Applicative/MonadParse free variables which seems to make up somewhere around 20-30% of the potential savings.

It's unclear why exactly specialization fails here but things might be better in 9.4/9.6
which contain big improvements to specialization.

## Tackling shared free variables:

The mutual references/free variables could be removed by an optimization called *lambda lifting*.
For example if we have this code:

```haskell
foo = ...
    where
        go1 fvs:{go1, go2} args = -> ... go1 ... go2 ...
        go2 fvs:{go1, go2} args = -> ... go1 ... go2 ...
```

This could be transformed into:

```haskell
foo = ...
    where
        go1 go1_arg go2_arg args = ... go1 go1_arg go2_arg ... go2 go1_arg go2_arg ...
        go2 go1_arg go2_arg args = ... go1 go1_arg go2_arg ... go2 go1_arg go2_arg ...
```

Turning the free variables into function arguments instead.

But it's generally hard to predict when this is beneficial as it can make thing *worse* in cases
where the additional now end up as free variables in the thunk that encloses a call site.

In the source AST the functions are in reverse order compared to the heap. We have code like this:

```haskell
    ...
    Rec {
        let go1 {fvs} args = ...
        let go2 {fvs} args = ...
        let go3 {fvs} args = ...
    } in
    let parent_thk {go1,go2,go3} = ... go1 ... go2 ... go3
```

Which produces a heap structure like this:

```
    parent_thk -\
                |-> go1
                |-> go2
                \-> go3
```

Which in hindsight makes sense, but isn't something I expected. (go1,go2,go3 also refer to each other but that's less interesting).

There are some GHC flags to control GHC's existing late-lambda-lifting pass:
* `-fstg-lift-lams-rec-args`
* `-fstg-lift-lams-non-rec-args`
* `-fstg-lift-lams`

And I opened a ticket on the ghc tracker about this particular scenario: https://gitlab.haskell.org/ghc/ghc/-/issues/23029

The recursive go functions mentioned above come from: `Hasura.GraphQL.Parser.Internal.Parser`

# Specialization Part2

I assume the use of the `FieldParser` type might get in the way of specialization.

```haskell
data FieldParser origin m a = FieldParser
  { fDefinition :: Definition origin (FieldInfo origin),
    fParser :: Field NoFragments Variable -> m a
  }
  deriving (Functor)
```

