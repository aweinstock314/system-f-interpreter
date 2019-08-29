# Ideas for extension
## Vernacular for interacting with the system
- repl currently only supports eval
- list all typeable 1-tree-edits of a term
- bind a name to a term in the global context
- eval a term in the global context

## Figure out how to share machinery between different languages
- it'd be nice to keep an interpreter for F around intact while adding an interpreter for Fomega that can reuse cases from the F interpreter
- Since Rust doesn't yet support HKT, can't do the standard Haskell-idiomatic fixpoint of sum of functors approach
- Possibly can emulate that via traits for folding/constructing each of the functors
- frunk is a too heavy a dependency, but can definitely do this, figure out a lighter-weight approach

## Defmacro via encoding F-asts in F
- possibly use `{expr}` as concrete syntax for quote
- since F doesn't have indices/dependency, can't have `(nil |- x : A) -> (gamma |- quote x : code A)`
- erasing the type and using `(nil |- x : A) -> (gamma |- quote x : code)` allows macros to construct ill-typed expressions, so typechecker needs to be run on macroexpanded fragments
- probably requires implementing (in Rust) the machinery for translating a (sums + products + fixpoints) type descriptor to the F-type of the corresponding fold

## Optimization through parametricity
- representing bool as `forall x, x -> x -> x` naively leads to each bit being a multi-node datastructure with heap pointers
- since church bool has only 2 possible non-bottom values, can represent it as a bit if the runtime/some optimization pass reasons about parametricity and lowers into a more efficient encoding
- representing nat as unary `forall x, x -> (x -> x) -> x` has O(n) instead of O(log(n)) operations
- exposing an optimization hook through defmacro or equivalent to allow F-code to lower unary nats to base-256 bignums implemented in F, made efficient via the representation optimizations

## Actors primitives for extensibility
- Since F is total, extend it with actor primitives to allow long-running processes
- ideal in a system with indices (probably at least Fomega):
+ `spawn : (A -> IO unit) -> IO (prochandle A)`
+ `message : A -> prochandle A -> IO unit`
+ `replace : prochandle A -> ((A -> IO unit) -> (A -> IO unit)) -> IO unit`
- replacing processes would allow e.g. extending a "syscall" actor with strace-like behavior within the language
