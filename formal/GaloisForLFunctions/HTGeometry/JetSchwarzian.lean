import GaloisForLFunctions.HTGeometry.JetZBranchCoefficient
import GaloisForLFunctions.HTGeometry.JetLevelThreeDescent

/-!
# The Schwarzian coordinate of the free jet field

The weight-zero derivation `∇ = δ/y₁` sends the ratio `z_j` to `z_{j+1} − j·z_j·z₂` and intertwines
with the substitution by a single factor:

`R'·Φ(∇v) = ∇(Φ v)`.

The Schwarzian coordinate `𝔖 = z₃ − (3/2)·z₂²` is the weight-zero object whose substitution law is a
pure translation,

`R'^2·Φ(𝔖) = 𝔖 + S_R`,   `S_R = R'''/R' − (3/2)(R''/R')²`,

and the covariant derivative `D_κ(g) = ∇g + κ·z₂·g` intertwines the relation
`R'^κ·Φ(g) = g + c` with `R'^{κ+1}·Φ(D_κ g) = D_κ g + D_κ c`.  So a jet-level invariant is a
`D`-tower over the Schwarzian, and the obstruction to closing the tower is the rational projective
structure `a(R)·(R')² = a − S_R`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- The weight-zero derivation. -/
def jetNabla : Derivation C (JetField C Unit) (JetField C Unit) :=
  ((JetField.jet ((), 1) : JetField C Unit))⁻¹ • JetField.jetDerivation

theorem jetNabla_apply (v : JetField C Unit) :
    jetNabla v = JetField.jetDerivation v / (JetField.jet ((), 1) : JetField C Unit) := by
  rw [jetNabla, Derivation.smul_apply, smul_eq_mul]
  ring

/-- **The substitution intertwines the weight-zero derivation with a single factor.** -/
theorem jetSubstitution_jetNabla (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (v : JetField C Unit) :
    substitutionDeriv R * jetSubstitution R hR (jetNabla v) = jetNabla (jetSubstitution R hR v) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
      = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
    rw [jetSubstitution_jet, substitutionJet_one]
  rw [jetNabla_apply, jetNabla_apply, map_div₀, hΦ1,
    jetSubstitution_jetDerivation R hR v]
  field_simp

/-! ## The Schwarzian coordinate -/

/-- The Schwarzian coordinate. -/
def schwarzianJet : JetField C Unit :=
  (jetRatio 3 : JetField C Unit) - (3 / 2 : JetField C Unit) * (jetRatio 2 : JetField C Unit) ^ 2

/-- The Schwarzian of the map, as an order-zero element. -/
def ratSchwarzian (R : RatFunc C) : JetField C Unit :=
  JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R)) / substitutionDeriv R
    - (3 / 2 : JetField C Unit)
      * (JetField.pd ((), 0) (substitutionDeriv R) / substitutionDeriv R) ^ 2

theorem substitutionShiftRatio_three (R : RatFunc C) :
    substitutionShiftRatio R 3
      = 3 * JetField.pd ((), 0) (substitutionDeriv R) * (jetRatio 2 : JetField C Unit)
        + JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R)) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  rw [substitutionShiftRatio, substitutionShift_three, jetRatio]
  field_simp

/-- **The Schwarzian coordinate translates.** -/
theorem jetSubstitution_schwarzianJet (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) :
    substitutionDeriv R ^ 2 * jetSubstitution R hR (schwarzianJet : JetField C Unit)
      = (schwarzianJet : JetField C Unit) + ratSchwarzian R := by
  have hρ : substitutionDeriv R ≠ 0 := hR
  have h2 := jetSubstitution_jetRatio R hR 2
  rw [substitutionShiftRatio_two] at h2
  have h3 := jetSubstitution_jetRatio R hR 3
  rw [substitutionShiftRatio_three] at h3
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set ρ₁ : JetField C Unit := JetField.pd ((), 0) ρ with hρ₁def
  set ρ₂ : JetField C Unit := JetField.pd ((), 0) ρ₁ with hρ₂def
  set z₂ : JetField C Unit := (jetRatio 2 : JetField C Unit) with hz₂def
  set z₃ : JetField C Unit := (jetRatio 3 : JetField C Unit) with hz₃def
  have hΦ2 : jetSubstitution R hR z₂ = (ρ * z₂ + ρ₁) / ρ ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hρ)]
    linear_combination h2
  have hΦ3 : jetSubstitution R hR z₃ = (ρ * z₃ + (3 * ρ₁ * z₂ + ρ₂)) / ρ ^ 3 := by
    rw [eq_div_iff (pow_ne_zero 3 hρ)]
    linear_combination h3
  rw [schwarzianJet, ratSchwarzian, map_sub, map_mul, map_pow, hΦ2, hΦ3]
  simp only [map_div₀, map_ofNat]
  field_simp
  ring


/-- The Schwarzian of the map, as a rational function. -/
def ratFuncSchwarzian (R : RatFunc C) : RatFunc C :=
  ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R)) / ratFuncDeriv R
    - RatFunc.C (3 / 2 : C) * (ratFuncDeriv (ratFuncDeriv R) / ratFuncDeriv R) ^ 2

theorem ratFuncEval_ratFuncSchwarzian (R : RatFunc C) :
    ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
        (ratFuncSchwarzian R) = ratSchwarzian R := by
  have hev1 : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
      (ratFuncDeriv R) = substitutionDeriv R := ratFuncEval_ratFuncDeriv R
  have hev2 : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
      (ratFuncDeriv (ratFuncDeriv R)) = JetField.pd ((), 0) (substitutionDeriv R) := by
    rw [ratFuncEval_ratFuncDeriv]
    exact substitutionDeriv_ratFuncDeriv R
  have hev3 : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
      (ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R)))
      = JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R)) := by
    rw [ratFuncEval_ratFuncDeriv]
    show substitutionDeriv (ratFuncDeriv (ratFuncDeriv R))
      = JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R))
    rw [substitutionDeriv_ratFuncDeriv (ratFuncDeriv R), substitutionDeriv_ratFuncDeriv R]
  rw [ratFuncSchwarzian, ratSchwarzian]
  simp only [map_sub, map_div₀, map_mul, map_pow, map_ofNat, hev1, hev2, hev3]


/-- **The weight-zero derivation on the ratios.** -/
theorem jetNabla_jetRatio (j : ℕ) :
    jetNabla (jetRatio j : JetField C Unit)
      = (jetRatio (j + 1) : JetField C Unit)
        - (j : JetField C Unit) * (jetRatio j : JetField C Unit)
          * (jetRatio 2 : JetField C Unit) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hδ1 : JetField.jetDerivation (JetField.jet ((), 1) : JetField C Unit)
      = JetField.jet ((), 2) := JetField.jetDerivation_jet ((), 1)
  have hδj : JetField.jetDerivation (JetField.jet ((), j) : JetField C Unit)
      = JetField.jet ((), j + 1) := JetField.jetDerivation_jet ((), j)
  have hpow : JetField.jetDerivation ((JetField.jet ((), 1) : JetField C Unit) ^ j)
      = (j : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit) ^ (j - 1)
        * (JetField.jet ((), 2) : JetField C Unit) := by
    have h := (JetField.jetDerivation :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
      (JetField.jet ((), 1) : JetField C Unit) j
    simp only [smul_eq_mul, hδ1] at h
    rw [h]
    ring
  have hmul : (jetRatio j : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit) ^ j
      = (JetField.jet ((), j) : JetField C Unit) := by
    rw [jetRatio]
    field_simp
  have hleib := (JetField.jetDerivation (C := C) (ι := Unit)).leibniz
    (jetRatio j : JetField C Unit) ((JetField.jet ((), 1) : JetField C Unit) ^ j)
  simp only [smul_eq_mul] at hleib
  rw [hmul, hδj, hpow] at hleib
  -- clear the denominators
  have hnab : JetField.jetDerivation (jetRatio j : JetField C Unit)
      = (JetField.jet ((), 1) : JetField C Unit) * jetNabla (jetRatio j : JetField C Unit) := by
    rw [jetNabla_apply]
    field_simp
  rw [hnab] at hleib
  rcases j with _ | i
  · have h1 : (jetRatio 0 : JetField C Unit) = (JetField.jet ((), 0) : JetField C Unit) := by
      rw [jetRatio, pow_zero, div_one]
    have h3 : jetNabla (JetField.jet ((), 0) : JetField C Unit) = 1 := by
      rw [jetNabla_apply, JetField.jetDerivation_jet, Nat.zero_add]
      exact div_self hy1
    have h2 : (jetRatio (0 + 1) : JetField C Unit) = 1 := by
      rw [jetRatio, pow_one, Nat.zero_add, div_self hy1]
    rw [h1, h2, h3]
    simp
  · simp only [Nat.add_sub_cancel] at hleib
    have hmul1 : (jetRatio (i + 1 + 1) : JetField C Unit)
        * (JetField.jet ((), 1) : JetField C Unit) ^ (i + 1 + 1)
        = (JetField.jet ((), i + 1 + 1) : JetField C Unit) := by
      rw [jetRatio]
      field_simp
    have hmul2 : (jetRatio 2 : JetField C Unit)
        * (JetField.jet ((), 1) : JetField C Unit) ^ 2
        = (JetField.jet ((), 2) : JetField C Unit) := by
      rw [jetRatio]
      field_simp
    refine mul_right_cancel₀ (pow_ne_zero (i + 1 + 1) hy1) ?_
    linear_combination (-1 : JetField C Unit) * hmul1
      + (((i + 1 : ℕ) : JetField C Unit) * (jetRatio (i + 1) : JetField C Unit)
          * (JetField.jet ((), 1) : JetField C Unit) ^ i) * hmul2
      + (-1 : JetField C Unit) * hleib


end

end GaloisForLFunctions.HTGeometry
