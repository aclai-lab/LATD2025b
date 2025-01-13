# Modal FLew-algebra satisfiability through two-sorted first-order translation
## Getting started

Launch a Julia command-line interface in your terminal:

```
$ julia
```

If you want to make use of multi-thread execution, add the `-t` option specifying the number
`n` of threads to be used. Here's and example for launching the session using 8 threads:

```
$ julia -t 8
```

Then include `modalFLewToFirstOrder.jl` file

```
julia> include("modalFLewToFirstOrder.jl");
```

To define a new algebra, first import the `ManyValuedLogics` submodule of `SoleLogics`:

```
julia> using SoleLogics.ManyValuedLogics;
```

In the same module, many common algebras have already been defined; for example, let's
import the Goedel algebra with 3 values G3, as well as the third value α:

```
julia> using SoleLogics.ManyValuedLogics: G3, α;
```

Then, let's define a formula using `SoleLogics` syntax; in the following example, we also
define a diamond and a box operator for the Halpern and Shoham's after relation `IA_A`
also defined in `SoleLogics`, as well as a new atom `p`:

```
julia> diamondA = diamond(IA_A);
julia> boxA = box(IA_A);
julia> p = Atom("p");
julia> φ = ∧(diamondA(p),boxA(→(p,⊥)));
```

To check alphasatisfiability, use the `alphasat` function:

```
julia> alphasat(α, φ, G3; solver="z3")
```