using ModalFLewToFirstOrder
using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample

myalphabet = Atom.(["p", "q", "r"])

min_height = 1
max_height = 6
max_it = 99999
max_avg = 200
max_timeout = 60 # seconds

verbose = false

using SoleLogics: HS_A, HS_L, HS_B, HS_E, HS_D, HS_O
using SoleLogics: HS_Ai, HS_Li, HS_Bi, HS_Ei, HS_Di, HS_Oi

mvhsoperators = Vector{Connective}(BASE_MANY_VALUED_CONNECTIVES)
append!(
    mvhsoperators,
    [
        diamond(IA_A),
        diamond(IA_L),
        diamond(IA_B),
        diamond(IA_E),
        diamond(IA_D),
        diamond(IA_O),
        diamond(IA_Ai),
        diamond(IA_Li),
        diamond(IA_Bi),
        diamond(IA_Ei),
        diamond(IA_Di),
        diamond(IA_Oi),
        box(IA_A),
        box(IA_L),
        box(IA_B),
        box(IA_E),
        box(IA_D),
        box(IA_O),
        box(IA_Ai),
        box(IA_Li),
        box(IA_Bi),
        box(IA_Ei),
        box(IA_Di),
        box(IA_Oi)
    ]
)
mvhsopweights = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: booleanalgebra, G3, Ł3, G4, Ł4, H4
using SoleLogics.ManyValuedLogics: G5, G6, H6_1, H6_2, H6_3, H6


algebras = [
    ("BA",   booleanalgebra),
    ("G3",   G3),
    ("Ł3",   Ł3),
    ("G4",   G4),
    ("Ł4",   Ł4),
    ("H4",   H4)
]

for a in algebras
    # Old formula generation
    # rng = initrng(Random.GLOBAL_RNG)
    # aot = vcat(myalphabet,getdomain(a[2])) # atoms or truths
    # aotweights = StatsBase.uweights(length(myalphabet)+length(getdomain(a[2])))
    # aotpicker = (rng)->StatsBase.sample(rng, aot, aotweights)
    # atomweights = StatsBase.uweights(length(myalphabet))
    # truthweights = StatsBase.uweights(length(getdomain(a[2])))
    # leafpicker1 = (rng)->SyntaxTree(
    #     →,
    #     (StatsBase.sample(rng, myalphabet, atomweights)),
    #     (StatsBase.sample(rng, getdomain(a[2]), truthweights))
    # )
    # leafpicker2 = (rng)->SyntaxTree(
    #     →,
    #     (StatsBase.sample(rng, getdomain(a[2]), truthweights)),
    #     (StatsBase.sample(rng, myalphabet, atomweights))
    # )
    # leafpickers = [leafpicker1, leafpicker2]
    # lpweights = StatsBase.uweights(length(leafpickers))
    # leafpicker = (rng)->(StatsBase.sample(rng, leafpickers, lpweights))(rng)
    
    # Formula generation
    rng = initrng(Random.GLOBAL_RNG)
    aot = vcat(myalphabet,getdomain(a[2])) # atoms or truths
    aotweights = StatsBase.uweights(length(myalphabet)+length(getdomain(a[2])))
    aotpicker = (rng)->StatsBase.sample(rng, aot, aotweights)

    # Confronting results with SoleReasoners tableau system
    for height in min_height:max_height
        println("Algebra: " * a[1] * "\theight: " * string(height))
        j = 0
        k = 0
        tot_time_tableau = 0
        tot_time_translation = 0
        errored = 0
        tableau_timeout = 0
        translation_timeout = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            # f = randformula(
            #     MersenneTwister(i),
            #     height-1,
            #     myalphabet,
            #     BASE_MANY_VALUED_MODAL_CONNECTIVES,
            #     opweights=StatsBase.uweights(length(BASE_MANY_VALUED_MODAL_CONNECTIVES)),
            #     basecase=leafpicker,    # basecase=aotpicker
            #     balanced=true
            # )
            f = randformula(
                MersenneTwister(i),
                height,
                myalphabet,
                mvhsoperators,
                opweights = mvhsopweights,
                basecase = aotpicker,
                mode = :full
            )
            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)
                ###########################
                # tableau performance #####
                ###########################
                t0 = time_ns()
                r = SoleReasoners.alphasat(
                    MVHSTableau,
                    t,
                    f,
                    a[2];
                    timeout=max_timeout
                )
                t1 = time_ns()
                ###########################
                # translation performance #
                ###########################
                t2 = time_ns()
                r_translation = ModalFLewToFirstOrder.alphasat(
                    t,
                    f,
                    a[2];
                    timeout=max_timeout
                )
                t3 = time_ns()
                ###########################
                if !isnothing(r)
                    if !isnothing(r_translation)
                        if r != r_translation
                            println(string(f) * " ⪰ " * string(t))
                            println("Tableau: " * string(r) * "\tTranslation: " * string(r_translation))
                            flush(stdout)
                            errored += 1
                        end
                        k += 1
                        tot_time_tableau += t1-t0
                        tot_time_translation += t3-t2
                    else
                        translation_timeout += 1
                    end
                else
                    tableau_timeout += 1
                end
                if j == max_avg
                    break
                end
            end
            if i == max_it
                @warn "Warning: maximum iterations reached"
            end
        end
        println("Tableau avg. " * string(tot_time_tableau/k/1e6) * "ms")
        println("Translation avg. " * string(tot_time_translation/k/1e6) * "ms")
        println("Tableau timeouts: " * string(tableau_timeout))
        println("Translation timeouts: " * string(translation_timeout))
        println("Errored: " * string(errored))
        flush(stdout)
    end
end