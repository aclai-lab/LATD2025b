using SoleLogics
using SoleLogics: AbstractAlgebra
using SoleLogics.ManyValuedLogics
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth
using UUIDs

struct Point
    label::String
end

struct Interval
    x::Point
    y::Point
end

"""
    releval(
        r::R,
        w::Interval,
        s::Interval
    ) where {
        R<:AbstractRelation
    }

Many-valued evaluation of the accessibility relation between worlds (x,y) and (z,t).

The natural definition of many-valued Allen's relations. 
For every X ∈ {A, Ai, L, Li, B, Bi, E, Ei, D, Di, O, Oi} we have RX: I(D)×I(D)→H defined by:

 - RA([x,y],[z,t]) = =(y,z)
 - RL([x,y],[z,t]) = <(y,z)
 - RB([x,y],[z,t]) = =(x,z) ∩ <(t,y)
 - RE([x,y],[z,t]) = <(x,z) ∩ =(y,t)
 - RD([x,y],[z,t]) = <(x,z) ∩ <(t,y)
 - RO([x,y],[z,t]) = <(x,z) ∩ <(z,y) ∩ <(y,t)

and similarly for the inverse relations:

- RAi([x,y],[z,t]) = =(t,x)
- RLi([x,y],[z,t]) = <(t,x)
- RBi([x,y],[z,t]) = =(z,x) ∩ <(y,t)
- REi([x,y],[z,t]) = <(z,x) ∩ =(t,y)
- RDi([x,y],[z,t]) = <(z,x) ∩ <(y,t)
- ROi([x,y],[z,t]) = <(z,x) ∩ <(x,t) ∩ <(y,t)
"""
function releval(
    r::R,
    w::Interval,
    s::Interval
) where {
    R<:AbstractRelation
}
    if r == SoleLogics.IA_A
        smtfile = "(mveq $(w.y.label) $(s.x.label))"
    elseif r == SoleLogics.IA_L
        smtfile = "(mvlt $(w.y.label) $(s.x.label))"
    elseif r == SoleLogics.IA_B
        smtfile = "(monoid (mveq $(w.x.label) $(s.x.label)) (mvlt $(s.y.label) $(w.y.label)))"
    elseif r == SoleLogics.IA_E
        smtfile = "(monoid (mvlt $(w.x.label) $(s.x.label)) (mveq $(w.y.label) $(s.y.label)))"
    elseif r == SoleLogics.IA_D
        smtfile = "(monoid (mvlt $(w.x.label) $(s.x.label)) (mvlt $(s.y.label) $(w.y.label)))"
    elseif r == SoleLogics.IA_O
        smtfile = "(monoid (monoid (mvlt $(w.x.label) $(s.x.label)) "
        smtfile *= "(mvlt $(s.x.label) $(w.y.label))) (mvlt $(w.y.label) $(s.y.label)))"
    elseif r == SoleLogics.IA_Ai
        smtfile = "(mveq $(s.y.label) $(w.x.label))"
    elseif r == SoleLogics.IA_Li
        smtfile = "(mvlt $(s.y.label) $(w.x.label))"
    elseif r == SoleLogics.IA_Bi
        smtfile = "(monoid (mveq $(s.x.label) $(w.x.label)) (mvlt $(w.y.label) $(s.y.label)))"
    elseif r == SoleLogics.IA_Ei
        smtfile = "(monoid (mvlt $(s.x.label) $(w.x.label)) (mveq $(s.y.label) $(w.y.label)))"
    elseif r == SoleLogics.IA_Di
        smtfile = "(monoid (mvlt $(s.x.label) $(w.x.label)) (mvlt $(w.y.label) $(s.y.label)))"
    elseif r == SoleLogics.IA_Oi
        smtfile = "(monoid (monoid (mvlt $(s.x.label) $(w.x.label)) "
        smtfile *= "(mvlt $(w.x.label) $(s.y.label))) (mvlt $(s.y.label) $(w.y.label)))"
    else
        error("Relation $r not in HS")
    end
    return smtfile
end

"""
    translate(
        φ::F,
        α::FiniteIndexTruth,
        algebra::FiniteIndexFLewAlgebra{N};
        solver::String="z3",
        timeout::Union{Nothing, Int} = nothing
    ) where {
     F<:Formula,
     N
    }

Translate the α-satisfiability problem for modal FLew-algebra formulae into two-sorted
first-order using smt-lib syntax and calling an smt-solver.
"""
function translate(
    φ::F,
    α::FiniteIndexTruth,
    algebra::FiniteIndexFLewAlgebra{N};
    solver::String="z3",
    timeout::Union{Nothing, Int} = nothing
) where {
    F<:Formula,
    N
}
    # algebra
    smtfile = "(declare-sort A)\n"
    for i ∈ 1:N
        smtfile *= "(declare-const a$i A)\n"
    end
    smtfile *= "(assert (distinct"
    for i ∈ 1:N
        smtfile *= " a$i"
    end
    smtfile *= "))\n(declare-fun join (A A) A)\n(declare-fun meet (A A) A)\n"
    smtfile *= "(declare-fun monoid (A A) A)\n(declare-fun implication (A A) A)\n"
    for i ∈ 1:N
        for j ∈ 1:N
            smtfile *= "(assert (= (join a$i a$j) "
            smtfile *= "a$(algebra.join(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (meet a$i a$j) "
            smtfile *= "a$(algebra.meet(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (monoid a$i a$j) "
            smtfile *= "a$(algebra.monoid(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (implication a$i a$j) "
            smtfile *= "a$(algebra.implication(UInt8(i), UInt8(j)).index)))\n"
        end
    end
    smtfile *= "(define-fun precedeq ((x A) (y A)) Bool (= (meet x y) x))\n"

    # order
    smtfile *= "(declare-sort W)\n"
    smtfile *= "(declare-fun mveq (W W) A)\n"
    smtfile *= "(declare-fun mvlt (W W) A)\n"
    smtfile *= "(assert (forall ((x W) (y W)) (and (or "
    for i ∈ 1:N
        smtfile *= "(= (mveq x y) a$i)" # =(x,y) = =(y,x) is checked later
    end
    smtfile *= ") (or "
    for i ∈ 1:N
        smtfile *= "(= (mvlt x y) a$i)"
    end         
    smtfile *= ") (or "
    for i ∈ 1:N
        smtfile *= "(= (mvlt y x) a$i)"
    end        
    smtfile *= "))))"
    # =(x,y) = 1 iff x = y
    smtfile *= "(assert (forall ((x W) (y W)) (= (= (mveq x y) a1) (= x y))))\n"
    # =(x,y) = =(y,x)    
    smtfile *= "(assert (forall ((x W) (y W)) (= (mveq x y) (mveq y x))))\n" 
    # <(x,x) = 0       
    smtfile *= "(assert (forall ((x W)) (= (mvlt x x) a2)))\n"      
    # <(x,z) ⪰ <(x,y) ⋅ <(y,z)                
    smtfile *= "(assert (forall ((x W) (y W) (z W)) "
    smtfile *= "(precedeq (monoid (mvlt x y) (mvlt y z)) (mvlt x z))))\n"   
    # if <(x,y) ≻ 0 and <(y,z) ≻ 0 then <(x,z) ≻ 0        
    smtfile *= "(assert (forall ((x W) (y W) (z W)) "
    smtfile *= "(=> (and (distinct (mvlt x y) a2) "
    smtfile *= "(distinct (mvlt y z) a2)) (distinct (mvlt x z) a2))))\n"
    # if <(x,y) = 0 and <(y,x) = 0 then =(x,y) = 1          
    smtfile *= "(assert (forall ((x W) (y W)) "
    smtfile *= "(=> (and (= (mvlt x y) a2) (= (mvlt y x) a2)) (= (mveq x y) a1))))\n"
    # if =(x,y) ≻ 0 then <(x,y) ≺ 1                       
    smtfile *= "(assert (forall ((x W) (y W)) "
    smtfile *= "(=> (distinct (mveq x y) a2) (distinct (mvlt x y) a1))))\n"

    w = Interval(Point("w0x"),Point("w0y"))
    atoms = Vector{Atom}()
    counter = Ref(1)
    translation = translategeq(φ, w, α, algebra, atoms, counter)
    for p ∈ atoms
        smtfile *= "(declare-fun $(p.value) (W W) A)\n"
    end
    smtfile *= "(assert (exists (($(w.x.label) W) ($(w.y.label) W)) "
    smtfile *= "(and (distinct (mvlt $(w.x.label) $(w.y.label)) a2) "
    smtfile *= "$(translation))))\n"

    smtfile *= "(check-sat)"
    b = IOBuffer()
    uuid = UUIDs.uuid4()
    touch("$(tempdir())/temp$uuid.smt2")
    open("$(tempdir())/temp$uuid.smt2", "w") do file
        write(file, smtfile)
    end
    if solver == "z3"
        if isnothing(timeout)
            run(pipeline(`z3 $(tempdir())/temp$uuid.smt2`, stdout = b))
        else
            run(pipeline(`z3 $(tempdir())/temp$uuid.smt2 -t:$timeout`, stdout = b))
        end
        rm("$(tempdir())/temp$uuid.smt2")
        return take!(b) == UInt8[0x73, 0x61, 0x74, 0x0a]
    else
        rm("$(tempdir())/temp$uuid.smt2")
        error("Please specify a supported solver. At the moment, only z3 is supported.")
    end
end

"""
    translate(
        φ::F,
        α::T,
        algebra::A;
        solver::String="z3",
        timeout::Union{Nothing, Int} = nothing
    ) where {
        T<:Truth,
        F<:Formula,
        A<:AbstractAlgebra
    }

Translate the α-satisfiability problem for modal FLew-algebra formulae into two-sorted
first-order using smt-lib syntax and calling an smt-solver.
"""
function translate(
    φ::F,
    α::T,
    a::A;
    solver::String="z3",
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth,
    F<:Formula,
    A<:AbstractAlgebra
}
    if !isa(α, FiniteIndexTruth) α = convert(FiniteIndexTruth, α) end
    if !isa(a, FiniteIndexFLewAlgebra) a = convert(FiniteIndexFLewAlgebra, a) end
    translate(φ, α, a; solver, timeout)
end

"""
    translategeq(
        p::Atom,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        N
    }

τ(||p||_x ⪰ α) = P(x) ⪰ α

For each atom p, there is a P(x) that returns a value from the algebra corresponing to the
value of p at the world x.
"""
function translategeq(
    p::Atom,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom},
    counter::Ref{Int};
    solver::String="z3"
) where {
    N
}
    if p ∉ atoms push!(atoms, p) end
    smtfile = "(and (or"
    for i ∈ 1:N
        smtfile *= (" (= ($(p.value) $(w.x.label) $(w.y.label)) a$i)")
    end
    smtfile *= ") "
    if isa(α, FiniteIndexTruth)
        smtfile *= "(precedeq a$(α.index) ($(p.value) $(w.x.label) $(w.y.label))))"
    elseif isa(α, FiniteTruth)
        smtfile *= "(precedeq $(α.label) ($(p.value) $(w.x.label) $(w.y.label))))"
    else
        error("Something went wrong")
    end
    return smtfile
end

"""
    translateleq(
        p::Atom,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        N
    }

τ(||p||_x ⪯ α) = P(x) ⪯ α

For each atom p, there is a P(x) that returns a value from the algebra corresponing to the
value of p at the world x.
"""
function translateleq(
    p::Atom,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom},
    counter::Ref{Int};
    solver::String="z3"
) where {
    N
}
    if p ∉ atoms push!(atoms, p) end
    smtfile = "(and (or"
    for i ∈ 1:N
        smtfile *= (" (= ($(p.value) $(w.x.label) $(w.y.label)) a$i)")
    end
    smtfile *= ") "
    if isa(α, FiniteIndexTruth)
        smtfile *= "(precedeq ($(p.value) $(w.x.label) $(w.y.label)) a$(α.index)))"
    elseif isa(α, FiniteTruth)
        smtfile *= "(precedeq ($(p.value) $(w.x.label) $(w.y.label)) $(α.label)))"
    else
        error("Something went wrong")
    end
    return smtfile
end

"""
    translategeq(
        β::T,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom},
        counter::Ref{Int};
        solver::String="z3"
    ) where {
        T<:Truth,
        N
    }

τ(||β||_x ⪰ α) = β ⪰ α
"""
function translategeq(
    β::T,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom},
    counter::Ref{Int};
    solver::String="z3"
) where {
    T<:Truth,
    N
}
    if !isa(β, FiniteIndexTruth) β = convert(FiniteIndexTruth, β) end
    if isa(α, FiniteIndexTruth)
        return "(precedeq a$(α.index) a$(β.index))"
    elseif isa(α, FiniteTruth)
        return "(precedeq $(α.label) a$(β.index))"
    else
        error("Something went wrong")
    end
end

"""
    translateleq(
        β::T,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom},
        counter::Ref{Int};
        solver::String="z3"
    ) where {
        T<:Truth,
        N
    }

τ(||β||_x ⪯ α) = β ⪯ α
"""
function translateleq(
    β::T,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra,
    atoms::Vector{Atom},
    counter::Ref{Int};
    solver::String="z3"
) where {
    T<:Truth
}
    if !isa(β, FiniteIndexTruth) β = convert(FiniteIndexTruth, β) end
    if isa(α, FiniteIndexTruth)
        return "(precedeq a$(β.index) a$(α.index))"
    elseif isa(α, FiniteTruth)
        return "(precedeq a$(β.index) $(α.label))"
    else
        error("Something went wrong")
    end
end

"""
    function translategeq(
        φ::SyntaxBranch,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        algebra::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom},
        counter::Ref{Int};
        solver::String="z3"
    ) where {
        N
    }

τ(||φ∧ψ||_w) ⪰ α = ∃x,y(A(x)∧A(y)∧τ(||φ||_w⪰x)∧τ(||φ||_w⪰y)∧(x⋅y⪰α))
τ(||φ∨ψ||_w) ⪰ α = ∃x,y(A(x)∧A(y)∧τ(||φ||_w⪰x)∧τ(||φ||_w⪰y)∧(x+y⪰α))
τ(||φ→ψ||_w) ⪰ α = ∃x,y(A(x)∧A(y)∧τ(||φ||_w⪯x)∧τ(||φ||_w⪰y)∧(x↪y⪰α))
"""
function translategeq(
    φ::SyntaxBranch,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    algebra::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom},
    counter::Ref{Int};
    solver::String="z3"
) where {
    N
}
    if isa(φ.token, typeof(∧)) || isa(φ.token, typeof(∨)) || isa(φ.token, typeof(→))
        (ψ, ε) = φ.children
        (x, y) = FiniteTruth.(["x$(counter[])", "y$(counter[])"])
        counter[]+=1
        smtfile = "(exists (($(x.label) A) ($(y.label) A)) (and "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(x.label) a$i)")
        end
        smtfile *= ") (or"
        for i ∈ 1:N
            smtfile *= (" (= $(y.label) a$i)")
        end
        smtfile *= ") "
        if isa(φ.token, typeof(∧))
            smtfile *= "$(translategeq(ψ, w, x, algebra, atoms, counter; solver)) "
            counter[]+=1
            smtfile *= "$(translategeq(ε, w, y, algebra, atoms, counter; solver)) "
            counter[]+=1
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq a$(α.index) (monoid $(x.label) $(y.label)))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq $(α.label) (monoid $(x.label) $(y.label)))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(∨))
            smtfile *= "$(translategeq(ψ, w, x, algebra, atoms, counter; solver)) "
            counter[]+=1
            smtfile *= "$(translategeq(ε, w, y, algebra, atoms, counter; solver)) "
            counter[]+=1
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq a$(α.index) (join $(x.label) $(y.label)))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq $(α.label) (join $(x.label) $(y.label)))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(→))
            smtfile *= "$(translateleq(ψ, w, x, algebra, atoms, counter; solver)) "
            counter[]+=1
            smtfile *= "$(translategeq(ε, w, y, algebra, atoms, counter; solver)) "
            counter[]+=1
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq a$(α.index) (implication $(x.label) $(y.label)))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq $(α.label) (implication $(x.label) $(y.label)))))"
            else
                error("Something went wrong")
            end
        else
            error("Something went wrong")
        end
    elseif isa(φ.token, DiamondRelationalConnective) || isa(φ.token, BoxRelationalConnective)
        r = SoleLogics.relation(φ.token)
        ψ = φ.children[1]
        s = Interval(Point("w$(counter[])x"), Point("w$(counter[])y"))
        (x, y, z) = FiniteTruth.(["x$(counter[])", "y$(counter[])", "z$(counter[])"])
        counter[]+=1
        smtfile = "(exists (($(x.label) A)) (and "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(x.label) a$i)")
        end
        smtfile *= ") "
        if isa(α, FiniteIndexTruth)
            smtfile *= "(precedeq a$(α.index) $(x.label)) (forall (($(y.label) A)) (=> "
        elseif isa(α, FiniteTruth)
            smtfile *= "(precedeq $(α.label) $(x.label)) (forall (($(y.label) A)) (=> "
        else
            error("Something went wrong")
        end
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(y.label) a$i)")
        end
        if isa(φ.token, DiamondRelationalConnective)
            smtfile *= ") (= (precedeq $(x.label) $(y.label)) "
        elseif isa(φ.token, BoxRelationalConnective)
            smtfile *= ") (= (precedeq $(y.label) $(x.label)) "
        else
            error("Something went wrong")
        end
        smtfile *= "(forall (($(z.label) A) ($(s.x.label) W) ($(s.y.label) W)) (=> "
        smtfile *= "(and "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(z.label) a$i)")
        end
        smtfile *= ") "
        smtfile *= "(distinct (mvlt $(s.x.label) $(s.y.label)) a2) "
        smtfile *= "$(translategeq(ψ, s, z, algebra, atoms, counter; solver))) "
        counter[]+=1
        if isa(φ.token, DiamondRelationalConnective)
            smtfile *= "(precedeq (monoid $(releval(r, w, s)) $(z.label)) $(y.label)))))))))"
        elseif isa(φ.token, BoxRelationalConnective)
            smtfile *= "(precedeq $(y.label) (implication $(releval(r, w, s)) $(z.label))))))))))"
        else
            error("Something went wrong")
        end
    else
        error("Something went wrong")
    end 
    return smtfile   
end

"""
    function translateleq(
        φ::SyntaxBranch,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        algebra::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        N
    }

τ(||φ∧ψ||_w) ⪯ α = ∃x,y(A(x)∧A(y)∧τ(||φ||_w⪯x)∧τ(||φ||_w⪯y)∧(x⋅y⪯α))
τ(||φ∨ψ||_w) ⪯ α = ∃x,y(A(x)∧A(y)∧τ(||φ||_w⪯x)∧τ(||φ||_w⪯y)∧(x+y⪯α))
τ(||φ→ψ||_w) ⪯ α = ∃x,y(A(x)∧A(y)∧τ(||φ||_w⪰x)∧τ(||φ||_w⪯y)∧(x↪y⪯α))
"""
function translateleq(
    φ::SyntaxBranch,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    algebra::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom},
    counter::Ref{Int};
    solver::String="z3"
) where {
    N
}
    if isa(φ.token, typeof(∧)) || isa(φ.token, typeof(∨)) || isa(φ.token, typeof(→))
        (ψ, ε) = φ.children
        (x, y) = FiniteTruth.(["x$(counter[])", "y$(counter[])"])
        counter[]+=1
        smtfile = "(exists (($(x.label) A) ($(y.label) A)) (and "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(x.label) a$i)")
        end
        smtfile *= ") (or"
        for i ∈ 1:N
            smtfile *= (" (= $(y.label) a$i)")
        end
        smtfile *= ") "
        if isa(φ.token, typeof(∧))
            smtfile *= "$(translateleq(ψ, w, x, algebra, atoms, counter; solver)) "
            counter[]+=1
            smtfile *= "$(translateleq(ε, w, y, algebra, atoms, counter; solver)) "
            counter[]+=1
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq (monoid $(x.label) $(y.label)) a$(α.index))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq (monoid $(x.label) $(y.label)) $(α.label))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(∨))
            smtfile *= "$(translateleq(ψ, w, x, algebra, atoms, counter; solver)) "
            counter[]+=1
            smtfile *= "$(translateleq(ε, w, y, algebra, atoms, counter; solver)) "
            counter[]+=1
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq (join $(x.label) $(y.label)) a$(α.index))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq (join $(x.label) $(y.label)) $(α.label))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(→))
            smtfile *= "$(translategeq(ψ, w, x, algebra, atoms, counter; solver)) "
            counter[]+=1
            smtfile *= "$(translateleq(ε, w, y, algebra, atoms, counter; solver)) "
            counter[]+=1
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq (implication $(x.label) $(y.label)) a$(α.index))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq (implication $(x.label) $(y.label)) $(α.label))))"
            else
                error("Something went wrong")
            end
        else
            error("Something went wrong")
        end
    elseif isa(φ.token, DiamondRelationalConnective) || isa(φ.token, BoxRelationalConnective)
        r = SoleLogics.relation(φ.token)
        ψ = φ.children[1]
        s = Interval(Point("w$(counter[])x"), Point("w$(counter[])y"))
        (x, y, z) = FiniteTruth.(["x$(counter[])", "y$(counter[])", "z$(counter[])"])
        counter[]+=1
        smtfile = "(exists (($(x.label) A)) (and "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(x.label) a$i)")
        end
        smtfile *= ") "
        if isa(α, FiniteIndexTruth)
            smtfile *= "(precedeq $(x.label) a$(α.index)) (forall (($(y.label) A)) (=> "
        elseif isa(α, FiniteTruth)
            smtfile *= "(precedeq $(x.label) $(α.label)) (forall (($(y.label) A)) (=> "
        else
            error("Something went wrong")
        end
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(y.label) a$i)")
        end
        if isa(φ.token, DiamondRelationalConnective)
            smtfile *= ") (= (precedeq $(x.label) $(y.label)) "
        elseif isa(φ.token, BoxRelationalConnective)
            smtfile *= ") (= (precedeq $(y.label) $(x.label)) "
        else
            error("Something went wrong")
        end
        smtfile *= "(forall (($(z.label) A) ($(s.x.label) W) ($(s.y.label) W)) (=> "
        smtfile *= "(and "
        smtfile *= "(distinct (mvlt $(s.x.label) $(s.y.label)) a2) "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= $(z.label) a$i)")
        end
        smtfile *= ")"
        smtfile *= "$(translateleq(ψ, s, z, algebra, atoms, counter; solver))) "
        counter[]+=1
        if isa(φ.token, DiamondRelationalConnective)
            smtfile *= "(precedeq (monoid $(releval(r, w, s)) $(z.label)) $(y.label)))))))))"
        elseif isa(φ.token, BoxRelationalConnective)
            smtfile *= "(precedeq $(y.label) (implication $(releval(r, w, s)) $(z.label))))))))))"
        else
            error("Something went wrong")
        end
    else
        error("Something went wrong")
    end   
    return smtfile 
end

"""
    alphasat(
        α::T,
        φ::F,
        algebra::A;
        solver::String="z3",
        timeout::Union{Nothing, Int} = nothing
    ) where {
        T<:Truth,
        F<:Formula,
        A<:AbstractAlgebra
    }

Check α-satisfiability of the formula `φ` for a given value `α` from an algebra `algebra`
using an smt solver (default=`z3`).
"""
function alphasat(
    α::T,
    φ::F,
    algebra::A;
    solver::String="z3",
    timeout::Union{Nothing, Int} = nothing
) where {
    T<:Truth,
    F<:Formula,
    A<:AbstractAlgebra
}
    return translate(φ, α, algebra; solver, timeout)
end

"""
    sat(φ::F, algebra::A; solver::String="z3", timeout::Union{Nothing, Int} = nothing)

Check 1-satisfiability of the formula `φ` using an smt solver (default=`z3`).
"""
function sat(φ::F, algebra::A; solver::String="z3", timeout::Union{Nothing, Int} = nothing) where {F<:Formula, A<:AbstractAlgebra}
    alphasat(⊤, φ, algebra; solver, timeout)
end