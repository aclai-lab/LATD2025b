using SoleLogics
using SoleLogics.ManyValuedLogics: α
using SoleLogics.ManyValuedLogics: G3

p = Atom("p")
diamondA = diamond(IA_A)
boxA = box(IA_A)

# Base cases

@test alphasat(⊥, ⊥, G3) == true
@test alphasat(⊥, α, G3) == true
@test alphasat(⊥, ⊤, G3) == true
@test alphasat(α, ⊥, G3) == false
@test alphasat(α, α, G3) == true
@test alphasat(α, ⊤, G3) == true
@test alphasat(⊤, ⊥, G3) == false
@test alphasat(⊤, α, G3) == false
@test alphasat(⊤, ⊤, G3) == true

@test alphasat(⊥, p, G3) == true
@test alphasat(α, p, G3) == true
@test alphasat(⊤, p, G3) == true

# Conjunction

@test alphasat(⊥, ∧(⊥, ⊥), G3) == true
@test alphasat(⊥, ∧(⊥, α), G3) == true
@test alphasat(⊥, ∧(⊥, ⊤), G3) == true
@test alphasat(⊥, ∧(α, ⊥), G3) == true
@test alphasat(⊥, ∧(α, α), G3) == true
@test alphasat(⊥, ∧(α, ⊤), G3) == true
@test alphasat(⊥, ∧(⊤, ⊥), G3) == true
@test alphasat(⊥, ∧(⊤, α), G3) == true
@test alphasat(⊥, ∧(⊤, ⊤), G3) == true

@test alphasat(α, ∧(⊥, ⊥), G3) == false
@test alphasat(α, ∧(⊥, α), G3) == false
@test alphasat(α, ∧(⊥, ⊤), G3) == false
@test alphasat(α, ∧(α, ⊥), G3) == false
@test alphasat(α, ∧(α, α), G3) == true
@test alphasat(α, ∧(α, ⊤), G3) == true
@test alphasat(α, ∧(⊤, ⊥), G3) == false
@test alphasat(α, ∧(⊤, α), G3) == true
@test alphasat(α, ∧(⊤, ⊤), G3) == true

@test alphasat(⊤, ∧(⊥, ⊥), G3) == false
@test alphasat(⊤, ∧(⊥, α), G3) == false
@test alphasat(⊤, ∧(⊥, ⊤), G3) == false
@test alphasat(⊤, ∧(α, ⊥), G3) == false
@test alphasat(⊤, ∧(α, α), G3) == false
@test alphasat(⊤, ∧(α, ⊤), G3) == false
@test alphasat(⊤, ∧(⊤, ⊥), G3) == false
@test alphasat(⊤, ∧(⊤, α), G3) == false
@test alphasat(⊤, ∧(⊤, ⊤), G3) == true

@test alphasat(⊥, ∧(p, ⊥), G3) == true
@test alphasat(⊥, ∧(p, α), G3) == true
@test alphasat(⊥, ∧(p, ⊤), G3) == true

@test alphasat(α, ∧(p, ⊥), G3) == false
@test alphasat(α, ∧(p, α), G3) == true
@test alphasat(α, ∧(p, ⊤), G3) == true

@test alphasat(⊤, ∧(p, ⊥), G3) == false
@test alphasat(⊤, ∧(p, α), G3) == false
@test alphasat(⊤, ∧(p, ⊤), G3) == true

@test alphasat(⊥, ∧(⊥, p), G3) == true
@test alphasat(⊥, ∧(α, p), G3) == true
@test alphasat(⊥, ∧(⊤, p), G3) == true

@test alphasat(α, ∧(⊥, p), G3) == false
@test alphasat(α, ∧(α, p), G3) == true
@test alphasat(α, ∧(⊤, p), G3) == true

@test alphasat(⊤, ∧(⊥, p), G3) == false
@test alphasat(⊤, ∧(α, p), G3) == false
@test alphasat(⊤, ∧(⊤, p), G3) == true

@test alphasat(⊥, ∧(p, p), G3) == true
@test alphasat(α, ∧(p, p), G3) == true
@test alphasat(⊤, ∧(p, p), G3) == true

# Disjunction

@test alphasat(⊥, ∨(⊥, ⊥), G3) == true
@test alphasat(⊥, ∨(⊥, α), G3) == true
@test alphasat(⊥, ∨(⊥, ⊤), G3) == true
@test alphasat(⊥, ∨(α, ⊥), G3) == true
@test alphasat(⊥, ∨(α, α), G3) == true
@test alphasat(⊥, ∨(α, ⊤), G3) == true
@test alphasat(⊥, ∨(⊤, ⊥), G3) == true
@test alphasat(⊥, ∨(⊤, α), G3) == true
@test alphasat(⊥, ∨(⊤, ⊤), G3) == true

@test alphasat(α, ∨(⊥, ⊥), G3) == false
@test alphasat(α, ∨(⊥, α), G3) == true
@test alphasat(α, ∨(⊥, ⊤), G3) == true
@test alphasat(α, ∨(α, ⊥), G3) == true
@test alphasat(α, ∨(α, α), G3) == true
@test alphasat(α, ∨(α, ⊤), G3) == true
@test alphasat(α, ∨(⊤, ⊥), G3) == true
@test alphasat(α, ∨(⊤, α), G3) == true
@test alphasat(α, ∨(⊤, ⊤), G3) == true

@test alphasat(⊤, ∨(⊥, ⊥), G3) == false
@test alphasat(⊤, ∨(⊥, α), G3) == false
@test alphasat(⊤, ∨(⊥, ⊤), G3) == true
@test alphasat(⊤, ∨(α, ⊥), G3) == false
@test alphasat(⊤, ∨(α, α), G3) == false
@test alphasat(⊤, ∨(α, ⊤), G3) == true
@test alphasat(⊤, ∨(⊤, ⊥), G3) == true
@test alphasat(⊤, ∨(⊤, α), G3) == true
@test alphasat(⊤, ∨(⊤, ⊤), G3) == true

@test alphasat(⊥, ∨(p, ⊥), G3) == true
@test alphasat(⊥, ∨(p, α), G3) == true
@test alphasat(⊥, ∨(p, ⊤), G3) == true

@test alphasat(α, ∨(p, ⊥), G3) == true
@test alphasat(α, ∨(p, α), G3) == true
@test alphasat(α, ∨(p, ⊤), G3) == true

@test alphasat(⊤, ∨(p, ⊥), G3) == true
@test alphasat(⊤, ∨(p, α), G3) == true
@test alphasat(⊤, ∨(p, ⊤), G3) == true

@test alphasat(⊥, ∨(⊥, p), G3) == true
@test alphasat(⊥, ∨(α, p), G3) == true
@test alphasat(⊥, ∨(⊤, p), G3) == true

@test alphasat(α, ∨(⊥, p), G3) == true
@test alphasat(α, ∨(α, p), G3) == true
@test alphasat(α, ∨(⊤, p), G3) == true

@test alphasat(⊤, ∨(⊥, p), G3) == true
@test alphasat(⊤, ∨(α, p), G3) == true
@test alphasat(⊤, ∨(⊤, p), G3) == true

@test alphasat(⊥, ∨(p, p), G3) == true
@test alphasat(α, ∨(p, p), G3) == true
@test alphasat(⊤, ∨(p, p), G3) == true

# Implication

@test alphasat(⊥, →(⊥, ⊥), G3) == true  # ⊤
@test alphasat(⊥, →(⊥, α), G3) == true  # ⊤
@test alphasat(⊥, →(⊥, ⊤), G3) == true  # ⊤
@test alphasat(⊥, →(α, ⊥), G3) == true  # ⊥
@test alphasat(⊥, →(α, α), G3) == true  # ⊤
@test alphasat(⊥, →(α, ⊤), G3) == true  # ⊤
@test alphasat(⊥, →(⊤, ⊥), G3) == true  # ⊥
@test alphasat(⊥, →(⊤, α), G3) == true  # α
@test alphasat(⊥, →(⊤, ⊤), G3) == true  # ⊤

@test alphasat(α, →(⊥, ⊥), G3) == true  # ⊤
@test alphasat(α, →(⊥, α), G3) == true  # ⊤
@test alphasat(α, →(⊥, ⊤), G3) == true  # ⊤
@test alphasat(α, →(α, ⊥), G3) == false # ⊥
@test alphasat(α, →(α, α), G3) == true  # ⊤
@test alphasat(α, →(α, ⊤), G3) == true  # ⊤
@test alphasat(α, →(⊤, ⊥), G3) == false # ⊥
@test alphasat(α, →(⊤, α), G3) == true  # α
@test alphasat(α, →(⊤, ⊤), G3) == true  # ⊤

@test alphasat(⊤, →(⊥, ⊥), G3) == true  # ⊤
@test alphasat(⊤, →(⊥, α), G3) == true  # ⊤
@test alphasat(⊤, →(⊥, ⊤), G3) == true  # ⊤
@test alphasat(⊤, →(α, ⊥), G3) == false # ⊥
@test alphasat(⊤, →(α, α), G3) == true  # ⊤
@test alphasat(⊤, →(α, ⊤), G3) == true  # ⊤
@test alphasat(⊤, →(⊤, ⊥), G3) == false # ⊥
@test alphasat(⊤, →(⊤, α), G3) == false # α
@test alphasat(⊤, →(⊤, ⊤), G3) == true  # ⊤

@test alphasat(⊥, →(p, ⊥), G3) == true
@test alphasat(⊥, →(p, α), G3) == true
@test alphasat(⊥, →(p, ⊤), G3) == true

@test alphasat(α, →(p, ⊥), G3) == true
@test alphasat(α, →(p, α), G3) == true
@test alphasat(α, →(p, ⊤), G3) == true

@test alphasat(⊤, →(p, ⊥), G3) == true
@test alphasat(⊤, →(p, α), G3) == true
@test alphasat(⊤, →(p, ⊤), G3) == true

@test alphasat(⊥, →(⊥, p), G3) == true
@test alphasat(⊥, →(α, p), G3) == true
@test alphasat(⊥, →(⊤, p), G3) == true

@test alphasat(α, →(⊥, p), G3) == true
@test alphasat(α, →(α, p), G3) == true
@test alphasat(α, →(⊤, p), G3) == true

@test alphasat(⊤, →(⊥, p), G3) == true
@test alphasat(⊤, →(α, p), G3) == true
@test alphasat(⊤, →(⊤, p), G3) == true

@test alphasat(⊥, →(p, p), G3) == true
@test alphasat(α, →(p, p), G3) == true
@test alphasat(⊤, →(p, p), G3) == true

# Modal cases

diamondA = diamond(IA_A)
boxA = box(IA_A)

@test alphasat(α, diamondA(⊥), G3) == false
@test alphasat(α, diamondA(⊤), G3) == true
@test alphasat(α, boxA(⊥), G3) == true
@test alphasat(α, boxA(⊤), G3) == true
@test alphasat(α, ∧(diamondA(p), boxA(→(p, ⊥))), G3) == false
