import GaloisForLFunctions.HTGeometry.NonDiscreteTranslationDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Hypertranscendence as a relative two-shift gauge obstruction

Fix two `ℚ`-independent shifts `α, β` and let `x` be a nonzero element of the global meromorphic
differential field.  Its multiplicative translation cocycle is `σ_q x / x`.  Call the cocycle
*`DA`-constant-flat* when it is the cocycle of a differentially algebraic gauge times a constant
character:

`σ_α x / x = (σ_α b / b) · c₁`,  `σ_β x / x = (σ_β b / b) · c₂`

for some nonzero differentially algebraic `b` and nonzero constants `c₁, c₂`.

* **`differentialAlgebraicOver_iff_daConstantFlat`** — `x` is differentially algebraic over the
  rational coordinate field exactly when its cocycle is `DA`-constant-flat.  Hypertranscendence is
  therefore precisely the failure of the cocycle to be reducible to a constant character by a
  differentially algebraic gauge: a relative gauge obstruction.

The forward direction takes `b = x` and the trivial character.  The converse divides the gauge out:
`g = x / b` is reproduced by each shift up to a constant, so its logarithmic derivative `g′ / g` is
fixed by both translations, hence differentially algebraic by the elliptic theorem; therefore `g` is
differentially algebraic, and so is `x = g · b`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance relativeGaugeDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance relativeGaugeDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance relativeGaugeRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance relativeGaugeRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance relativeGaugeDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ

local instance relativeGaugeCharZeroBase : CharZero (RatFunc ℂ) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (RatFunc ℂ)).injective

local instance relativeGaugeCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective

local instance relativeGaugeComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring (Set.univ : Set ℂ)) := (constToAnalytic Set.univ).toAlgebra

local instance relativeGaugeComplexAlgebra : Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

/-! ## Constants are differential constants -/

/-- A constant germ has zero derivative. -/
theorem analyticSubringDeriv_constToAnalytic (c : ℂ) :
    analyticSubringDeriv (U := (Set.univ : Set ℂ)) isOpen_univ (constToAnalytic Set.univ c) = 0 := by
  apply Subtype.ext
  change ((deriv (fun _ : ℂ => c) : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = 0
  rw [deriv_const']
  rfl

/-- The embedded complex constants are constants for the meromorphic derivation. -/
theorem deriv_algebraMap_complex (c : ℂ) :
    (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ = 0 := by
  change (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
    (constToAnalytic Set.univ c))′ = 0
  rw [meroFieldDifferential_algebraMap isOpen_univ isPreconnected_univ Set.univ_nonempty,
    analyticSubringDeriv_constToAnalytic, map_zero]

/-- A nonzero constant embeds to a nonzero germ. -/
theorem algebraMap_complex_ne_zero {c : ℂ} (hc : c ≠ 0) :
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) c ≠ 0 := fun hzero =>
  hc ((algebraMap ℂ (meroField (Set.univ : Set ℂ))).injective (by simpa using hzero))

/-! ## The cocycle and its flatness -/

/-- The multiplicative translation cocycle of a meromorphic germ. -/
def translationCocycle (q : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    meroField (Set.univ : Set ℂ) :=
  addTranslationMeroEquiv q x / x

/-- **`DA`-constant-flatness of the two-shift cocycle.**  The cocycle of `x` at the two shifts is
the cocycle of a nonzero differentially algebraic gauge times a constant character. -/
def DAConstantFlat (α β : ℂ) (x : meroField (Set.univ : Set ℂ)) : Prop :=
  ∃ b : meroField (Set.univ : Set ℂ), b ≠ 0 ∧ DifferentialAlgebraicOver (RatFunc ℂ) b ∧
    ∃ c₁ c₂ : ℂ, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧
      translationCocycle α x =
        translationCocycle α b * algebraMap ℂ (meroField (Set.univ : Set ℂ)) c₁ ∧
      translationCocycle β x =
        translationCocycle β b * algebraMap ℂ (meroField (Set.univ : Set ℂ)) c₂

/-- A differentially algebraic germ is its own gauge. -/
theorem daConstantFlat_of_differentialAlgebraicOver (α β : ℂ)
    {x : meroField (Set.univ : Set ℂ)} (hx : x ≠ 0)
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DAConstantFlat α β x :=
  ⟨x, hx, hDA, 1, 1, one_ne_zero, one_ne_zero, by simp, by simp⟩

/-- Dividing out the gauge leaves a germ reproduced by the shift up to the constant character. -/
theorem addTranslationMeroEquiv_div_eq_const_mul {q : ℂ} {c : ℂ}
    {x b : meroField (Set.univ : Set ℂ)} (hx : x ≠ 0) (hb : b ≠ 0)
    (h : translationCocycle q x =
      translationCocycle q b * algebraMap ℂ (meroField (Set.univ : Set ℂ)) c) :
    addTranslationMeroEquiv q (x / b) =
      algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * (x / b) := by
  have hσb : addTranslationMeroEquiv q b ≠ 0 := by
    intro hzero
    apply hb
    have := congrArg (addTranslationMeroEquiv q).symm hzero
    rwa [RingEquiv.symm_apply_apply, map_zero] at this
  rw [translationCocycle, translationCocycle, div_mul_eq_mul_div, div_eq_div_iff hx hb] at h
  rw [map_div₀, div_eq_iff hσb]
  field_simp
  linear_combination h

/-- The logarithmic derivative of a constant-multiplier germ is translation invariant. -/
theorem addTranslationMeroEquiv_logDeriv_eq {q : ℂ} {c : ℂ} (hc : c ≠ 0)
    {g : meroField (Set.univ : Set ℂ)}
    (hg : addTranslationMeroEquiv q g = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * g) :
    addTranslationMeroEquiv q (g′ / g) = g′ / g := by
  letI : Algebra ℤ (meroField (Set.univ : Set ℂ)) := Ring.toIntAlgebra _
  rw [map_div₀, addTranslationMeroEquiv_deriv, hg, Derivation.leibniz,
    deriv_algebraMap_complex, smul_zero, add_zero, smul_eq_mul]
  exact mul_div_mul_left _ _ (algebraMap_complex_ne_zero hc)

/-! ## The characterization -/

/-- **A germ with a `DA`-constant-flat two-shift cocycle is differentially algebraic.** -/
theorem differentialAlgebraicOver_of_daConstantFlat {α β : ℂ}
    (hindep : LinearIndependent ℚ ![α, β]) {x : meroField (Set.univ : Set ℂ)} (hx : x ≠ 0)
    (hflat : DAConstantFlat α β x) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  obtain ⟨b, hb0, hbDA, c₁, c₂, hc₁, hc₂, hαx, hβx⟩ := hflat
  set g : meroField (Set.univ : Set ℂ) := x / b with hgdef
  have hgα := addTranslationMeroEquiv_div_eq_const_mul hx hb0 hαx
  have hgβ := addTranslationMeroEquiv_div_eq_const_mul hx hb0 hβx
  have hlogDA : DifferentialAlgebraicOver (RatFunc ℂ) (g′ / g) :=
    differentialAlgebraicOver_of_translation_fixed_rat hindep
      (addTranslationMeroEquiv_logDeriv_eq hc₁ hgα)
      (addTranslationMeroEquiv_logDeriv_eq hc₂ hgβ)
  have hgDA : DifferentialAlgebraicOver (RatFunc ℂ) g :=
    (differentialAlgebraicOver_deriv_div_self_iff g).mp hlogDA
  have hxg : x = g * b := by
    rw [hgdef]
    field_simp
  rw [hxg]
  exact differentialAlgebraicOver_mul hgDA hbDA

/-- **The constant-multiplier two-shift law in the meromorphic field.**  A nonzero germ reproduced
by each of two `ℚ`-independent translations up to a nonzero constant is differentially algebraic:
the trivial gauge `b = 1` makes its cocycle `DA`-constant-flat. -/
theorem differentialAlgebraicOver_of_constant_multipliers {α β : ℂ}
    (hindep : LinearIndependent ℚ ![α, β]) {x : meroField (Set.univ : Set ℂ)} (hx : x ≠ 0)
    {c₁ c₂ : ℂ} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hα : addTranslationMeroEquiv α x = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c₁ * x)
    (hβ : addTranslationMeroEquiv β x = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c₂ * x) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  have hone : DifferentialAlgebraicOver (RatFunc ℂ) (1 : meroField (Set.univ : Set ℂ)) := by
    have := differentialAlgebraicOver_algebraMap (F := RatFunc ℂ)
      (E := meroField (Set.univ : Set ℂ)) (1 : RatFunc ℂ)
    simpa using this
  refine differentialAlgebraicOver_of_daConstantFlat hindep hx
    ⟨1, one_ne_zero, hone, c₁, c₂, hc₁, hc₂, ?_, ?_⟩
  · rw [translationCocycle, translationCocycle, map_one, div_one, one_mul, hα,
      mul_div_assoc, div_self hx, mul_one]
  · rw [translationCocycle, translationCocycle, map_one, div_one, one_mul, hβ,
      mul_div_assoc, div_self hx, mul_one]

/-- **Hypertranscendence is exactly a relative gauge obstruction.**  A nonzero meromorphic germ is
differentially algebraic over the rational coordinate field precisely when its two-shift
multiplicative translation cocycle can be reduced to a constant character by a differentially
algebraic gauge. -/
theorem differentialAlgebraicOver_iff_daConstantFlat {α β : ℂ}
    (hindep : LinearIndependent ℚ ![α, β]) {x : meroField (Set.univ : Set ℂ)} (hx : x ≠ 0) :
    DifferentialAlgebraicOver (RatFunc ℂ) x ↔ DAConstantFlat α β x :=
  ⟨daConstantFlat_of_differentialAlgebraicOver α β hx,
    differentialAlgebraicOver_of_daConstantFlat hindep hx⟩

/-- **The hypertranscendental form.**  A nonzero germ is hypertranscendental over the rational
coordinate field exactly when its two-shift cocycle is not `DA`-constant-flat. -/
theorem hypertranscendentalOver_iff_not_daConstantFlat {α β : ℂ}
    (hindep : LinearIndependent ℚ ![α, β]) {x : meroField (Set.univ : Set ℂ)} (hx : x ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ) x ↔ ¬ DAConstantFlat α β x :=
  not_congr (differentialAlgebraicOver_iff_daConstantFlat hindep hx)

end

end GaloisForLFunctions.HTGeometry
