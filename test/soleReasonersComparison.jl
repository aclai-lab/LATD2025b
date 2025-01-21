using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample
using SoleLogics.ManyValuedLogics: booleanalgebra, G3, Ł3, G4, Ł4, H4, G5, G6, H6_1, H6_2, H6_3, H6

diamondA = diamond(IA_A)
diamondL = diamond(IA_L)
diamondB = diamond(IA_B)
diamondE = diamond(IA_E)
diamondD = diamond(IA_D)
diamondO = diamond(IA_O)
diamondAi = diamond(IA_Ai)
diamondLi = diamond(IA_Li)
diamondBi = diamond(IA_Bi)
diamondEi = diamond(IA_Ei)
diamondDi = diamond(IA_Di)
diamondOi = diamond(IA_Oi)
boxA = box(IA_A)
boxL = box(IA_L)
boxB = box(IA_B)
boxE = box(IA_E)
boxD = box(IA_D)
boxO = box(IA_O)
boxAi = box(IA_Ai)
boxLi = box(IA_Li)
boxBi = box(IA_Bi)
boxEi = box(IA_Ei)
boxDi = box(IA_Di)
boxOi = box(IA_Oi)

BASE_MANY_VALUED_MODAL_CONNECTIVES = [
    ∨,
    ∧,
    →,
    diamondA,
    diamondL,
    diamondB,
    diamondE,
    diamondD,
    diamondO,
    diamondAi,
    diamondLi,
    diamondBi,
    diamondEi,
    diamondDi,
    diamondOi,
    boxA,
    boxL,
    boxB,
    boxE,
    boxD,
    boxO,
    boxAi,
    boxLi,
    boxBi,
    boxEi,
    boxDi,
    boxOi
]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_MODAL_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

min_height = 2
max_height = 5
max_it = 2000
max_avg = 50
max_timeout = 30 # seconds
verbose = true

algebras = [
    ("BA",   booleanalgebra),
    ("G3",   G3),
    ("Ł3",   Ł3),
    ("G4",   G4),
    ("Ł4",   Ł4),
    ("H4",   H4),
    ("G5",   G5),
    ("G6",   G6),
    ("H6_1", H6_1),
    ("H6_2", H6_2),
    ("H6_3", H6_3),
    ("H6",   H6)
]

for a in algebras
    # Formula generation
    rng = initrng(Random.GLOBAL_RNG)
    aot = vcat(myalphabet,getdomain(a[2])) # atoms or truths
    aotweights = StatsBase.uweights(length(myalphabet)+length(getdomain(a[2])))
    aotpicker = (rng)->StatsBase.sample(rng, aot, aotweights)
    atomweights = StatsBase.uweights(length(myalphabet))
    truthweights = StatsBase.uweights(length(getdomain(a[2])))
    leafpicker1 = (rng)->SyntaxTree(
        →,
        (StatsBase.sample(rng, myalphabet, atomweights)),
        (StatsBase.sample(rng, getdomain(a[2]), truthweights))
    )
    leafpicker2 = (rng)->SyntaxTree(
        →,
        (StatsBase.sample(rng, getdomain(a[2]), truthweights)),
        (StatsBase.sample(rng, myalphabet, atomweights))
    )
    leafpickers = [leafpicker1, leafpicker2]
    lpweights = StatsBase.uweights(length(leafpickers))
    leafpicker = (rng)->(StatsBase.sample(rng, leafpickers, lpweights))(rng)

    # Confronting results with SoleReasoners tableau system
    for height in min_height:max_height
        j = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            f = randformula(
                MersenneTwister(i),
                height-1,
                myalphabet,
                BASE_MANY_VALUED_MODAL_CONNECTIVES,
                opweights=StatsBase.uweights(length(BASE_MANY_VALUED_MODAL_CONNECTIVES)),
                basecase=leafpicker,    # basecase=aotpicker
                balanced=true
            )
            verbose && println(f)
            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)
                r = mvhsalphasat(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout,
                    verbose=false
                )
                r_translation = ModalFLewToFirstOrder.alphasat(
                    t,
                    f,
                    a[2];
                    timeout=max_timeout
                )
                if !isnothing(r) && !isnothing(r_translation) 
                    @test r == r_translation
                end
                if j == max_avg
                    break
                end
            end
            if i == max_it
                @warn "Warning: maximum iterations reached"
            end
        end
    end
end