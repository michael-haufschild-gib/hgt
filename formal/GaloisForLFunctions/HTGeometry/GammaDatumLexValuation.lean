import GaloisForLFunctions.HTGeometry.GammaFieldValuation

/-!
# The full boundary datum is a rank-three valuation

Equation (26) orders the data `(k, a, b)` lexicographically: smaller `Γ`-exponent dominates, then
larger argument exponent, then larger logarithm exponent.  The whole triple — not only its first
component — is a valuation for that order: it adds on products, and on a sum it cannot dominate both
summands.

The value group is `ℤ ×ₗ ℤ ×ₗ ℤ` with the first coordinate reversed, so that "dominates" is "larger".
-/

open Filter Set Topology Function
open scoped Differential
open scoped Classical

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaLexDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaLexIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaLexDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaLexComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaLexRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaLexRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaLexRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- **The dominance order of eq. (26)**: `(k, a, b)` dominates `(k', a', b')` when its `Γ`-exponent is
smaller, or equal with a larger argument exponent, or both equal with a larger logarithm exponent. -/
def ShapeDominates (k a b k' a' b' : ℤ) : Prop :=
  k < k' ∨ (k' = k ∧ a' < a) ∨ (k' = k ∧ a' = a ∧ b' < b)

/-- A dominated shape is negligible against the dominating one. -/
theorem tendsto_gammaShapeZ_ratio_zero_of_dominates {σ : ℝ} (hσ : 0 < σ) {k a b k' a' b' : ℤ}
    (h : ShapeDominates k a b k' a' b') :
    Tendsto (fun t : ℝ => gammaShapeZ σ k' a' b' t / gammaShapeZ σ k a b t) atTop (nhds 0) :=
  tendsto_gammaShapeZ_ratio_zero hσ h

/-- A shape dominated by the trivial one vanishes. -/
theorem tendsto_gammaShapeZ_zero_of_dominated {σ : ℝ} (hσ : 0 < σ) {k a b : ℤ}
    (h : ShapeDominates 0 0 0 k a b) : Tendsto (gammaShapeZ σ k a b) atTop (nhds 0) := by
  rcases h with hk | ⟨hk, ha⟩ | ⟨hk, ha, hb⟩
  · exact tendsto_gammaShapeZ_zero_of_gamma_pos hσ (by omega) _ _
  · rw [show k = 0 by omega]
    exact tendsto_gammaShapeZ_zero_of_arg_neg hσ (by omega) _
  · rw [show k = 0 by omega, show a = 0 by omega]
    exact tendsto_gammaShapeZ_zero_of_log_neg (by omega)

/-- An element whose datum is dominated by the trivial one is negligible on the line. -/
theorem tendsto_zero_of_hasGammaDatum_dominated {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    {k a b : ℤ} {c : ℂ} (hdom : ShapeDominates 0 0 0 k a b) (h : HasGammaDatum σ x k a b c) :
    ∃ φ : ℝ → ℂ, RepresentsOnLine σ x φ ∧ (∀ᶠ t : ℝ in atTop, φ t ≠ 0)
      ∧ Tendsto φ atTop (nhds 0) := by
  obtain ⟨hc, φ, hrep, hlim⟩ := h
  refine ⟨φ, hrep, eventually_ne_zero_of_datum hc hlim, ?_⟩
  have hmul := hlim.mul (tendsto_gammaShapeZ_zero_of_dominated hσ hdom)
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gammaShapeZ_ne_zero (σ := σ) hσ k a b] with t hS
  rw [div_mul_cancel₀ _ hS]

/-- **The datum of a sum cannot dominate both summands.**  This is the ultrametric inequality for the
full triple: cancellation can only move the datum down the dominance order, never up past both. -/
theorem not_hasGammaDatum_add_dominates {σ : ℝ} (hσ : 0 < σ) {x y : upperEndMeroField}
    {k a b k' a' b' m A B : ℤ} {c c' C : ℂ}
    (hx : HasGammaDatum σ x k a b c) (hy : HasGammaDatum σ y k' a' b' c')
    (hsum : HasGammaDatum σ (x + y) m A B C) :
    ¬ (ShapeDominates m A B k a b ∧ ShapeDominates m A B k' a' b') := by
  classical
  rintro ⟨hdx, hdy⟩
  have hu0 : x + y ≠ 0 := hsum.ne_zero
  have hp : HasGammaDatum σ (x * (x + y)⁻¹) (k + -m) (a + -A) (b + -B) (c * C⁻¹) :=
    hx.mul hσ (hsum.inv hσ)
  have hq : HasGammaDatum σ (y * (x + y)⁻¹) (k' + -m) (a' + -A) (b' + -B) (c' * C⁻¹) :=
    hy.mul hσ (hsum.inv hσ)
  have hdomp : ShapeDominates 0 0 0 (k + -m) (a + -A) (b + -B) := by
    rcases hdx with h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
  have hdomq : ShapeDominates 0 0 0 (k' + -m) (a' + -A) (b' + -B) := by
    rcases hdy with h1 | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
  obtain ⟨φ₁, hrep₁, hne₁, hzero₁⟩ := tendsto_zero_of_hasGammaDatum_dominated hσ hdomp hp
  obtain ⟨φ₂, hrep₂, hne₂, hzero₂⟩ := tendsto_zero_of_hasGammaDatum_dominated hσ hdomq hq
  obtain ⟨U₁, V₁, G₁, H₁, hU₁, hV₁, hV₁0, hx₁, hφ₁⟩ := hrep₁
  obtain ⟨U₂, V₂, G₂, H₂, hU₂, hV₂, hV₂0, hx₂, hφ₂⟩ := hrep₂
  have hone : x * (x + y)⁻¹ + y * (x + y)⁻¹ = 1 := by
    rw [← add_mul, mul_inv_cancel₀ hu0]
  rw [hx₁, hx₂] at hone
  have hcross : algebraMap upperEndAnalyticSubring upperEndMeroField (U₁ * V₂ + U₂ * V₁)
      = algebraMap upperEndAnalyticSubring upperEndMeroField (V₁ * V₂) := by
    rw [map_add, map_mul, map_mul, map_mul]
    field_simp at hone
    linear_combination hone
  have hprod : U₁ * V₂ + U₂ * V₁ = V₁ * V₂ :=
    IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField hcross
  have hgerm : Germ.coeRingHom upperEndFilter (fun z : ℂ => G₁ z * H₂ z + G₂ z * H₁ z)
      = Germ.coeRingHom upperEndFilter (fun z : ℂ => H₁ z * H₂ z) := by
    have h1 : upperEndAnalyticSubring.subtype (U₁ * V₂ + U₂ * V₁)
        = Germ.coeRingHom upperEndFilter (fun z : ℂ => G₁ z * H₂ z + G₂ z * H₁ z) := by
      rw [map_add, map_mul, map_mul, hU₁, hV₂, hU₂, hV₁, ← map_mul, ← map_mul, ← map_add]
      rfl
    have h2 : upperEndAnalyticSubring.subtype (V₁ * V₂)
        = Germ.coeRingHom upperEndFilter (fun z : ℂ => H₁ z * H₂ z) := by
      rw [map_mul, hV₁, hV₂, ← map_mul]
      rfl
    rw [← h1, ← h2, hprod]
  have hev : ∀ᶠ z : ℂ in upperEndFilter, G₁ z * H₂ z + G₂ z * H₁ z = H₁ z * H₂ z :=
    Filter.Germ.coe_eq.mp hgerm
  have hline := eventually_line_of_upperEnd hev σ
  have hsmall : ∀ᶠ t : ℝ in atTop, φ₁ t + φ₂ t ∈ Metric.ball (0 : ℂ) 1 := by
    have hlim0 : Tendsto (fun t : ℝ => φ₁ t + φ₂ t) atTop (nhds 0) := by
      have := hzero₁.add hzero₂
      rwa [add_zero] at this
    exact hlim0.eventually (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨t, ⟨⟨⟨ht, ht₁⟩, ht₂⟩, htsmall⟩⟩ :=
    (((hline.and hne₁).and hne₂).and hsmall).exists
  have hH₁ : H₁ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact ht₁ (by rw [hφ₁ t, h0, div_zero])
  have hH₂ : H₂ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    exact ht₂ (by rw [hφ₂ t, h0, div_zero])
  have hsum1 : φ₁ t + φ₂ t = 1 := by
    rw [hφ₁ t, hφ₂ t, div_add_div _ _ hH₁ hH₂, div_eq_one_iff_eq (mul_ne_zero hH₁ hH₂)]
    linear_combination ht
  rw [hsum1, Metric.mem_ball, dist_eq_norm, sub_zero, norm_one] at htsmall
  exact lt_irrefl 1 htsmall

/-- **The tube datum of a sum cannot dominate both summands.** -/
theorem not_hasGammaTubeDatum_add_dominates {M : ℝ} (hM : 0 < M) {x y : upperEndMeroField}
    {k a b k' a' b' m A B : ℤ} {c c' C : ℂ}
    (hx : HasGammaTubeDatum M x k a b c) (hy : HasGammaTubeDatum M y k' a' b' c')
    (hsum : HasGammaTubeDatum M (x + y) m A B C) :
    ¬ (ShapeDominates m A B k a b ∧ ShapeDominates m A B k' a' b') :=
  not_hasGammaDatum_add_dominates hM (hx.hasGammaDatum hM le_rfl) (hy.hasGammaDatum hM le_rfl)
    (hsum.hasGammaDatum hM le_rfl)

/-- The value of a datum in the lexicographic group: the `Γ`-exponent reversed, then the argument and
logarithm exponents. -/
def lexValue (k a b : ℤ) : ℤ ×ₗ ℤ ×ₗ ℤ :=
  toLex (-k, toLex (a, b))

/-- The lexicographic value of a datum triple. -/
def lexOfDatum (d : ℤ × ℤ × ℤ) : ℤ ×ₗ ℤ ×ₗ ℤ :=
  lexValue d.1 d.2.1 d.2.2

theorem lexOfDatum_triple (k a b : ℤ) : lexOfDatum (k, a, b) = lexValue k a b := rfl

theorem lexValue_add (k a b k' a' b' : ℤ) :
    lexValue (k + k') (a + a') (b + b') = lexValue k a b + lexValue k' a' b' := by
  rw [lexValue, lexValue, lexValue]
  refine congrArg toLex ?_
  refine Prod.ext ?_ ?_
  · show -(k + k') = -k + -k'
    ring
  · rfl

theorem lexValue_zero : lexValue 0 0 0 = 0 := rfl

/-- Dominance is exactly the order of the lexicographic value. -/
theorem lexValue_lt_iff {k a b k' a' b' : ℤ} :
    lexValue k' a' b' < lexValue k a b ↔ ShapeDominates k a b k' a' b' := by
  rw [lexValue, lexValue, Prod.Lex.lt_iff]
  simp only [ofLex_toLex]
  rw [Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ShapeDominates]
  omega

/-- The datum triple of an element of the Gamma field. -/
def gammaDatumTripleK (x : gammaFieldK) : ℤ × ℤ × ℤ :=
  if h : x = 0 then 0 else (gammaUnitDatum (Units.mk0 x h)).1

/-- The datum triple is read off any datum. -/
theorem gammaDatumTripleK_eq_of {x : gammaFieldK} (hx : x ≠ 0) {k a b : ℤ} {c : ℂ}
    (h : HasGammaTubeDatum 1 (x : upperEndMeroField) k a b c) :
    gammaDatumTripleK x = (k, a, b) := by
  rw [gammaDatumTripleK, dif_neg hx]
  have hunit : gammaUnitDatum (Units.mk0 x hx) = ((k, a, b), Units.mk0 c h.1) :=
    gammaUnitDatum_eq_of h
  rw [hunit]

/-- **The rank-three valuation of the Gamma field.**  Its value group is the lexicographic
`ℤ ×ₗ ℤ ×ₗ ℤ` of eq. (26): the datum triple of a product adds, and the datum of a sum never dominates
both summands. -/
def gammaLexValuation : Valuation gammaFieldK (WithZero (Multiplicative (ℤ ×ₗ ℤ ×ₗ ℤ))) where
  toFun x := if x = 0 then (0 : WithZero (Multiplicative (ℤ ×ₗ ℤ ×ₗ ℤ)))
    else ((Multiplicative.ofAdd (lexOfDatum (gammaDatumTripleK x)) : Multiplicative (ℤ ×ₗ ℤ ×ₗ ℤ)) :
      WithZero (Multiplicative (ℤ ×ₗ ℤ ×ₗ ℤ)))
  map_zero' := by
    rw [if_pos rfl]
  map_one' := by
    have hone : ((1 : gammaFieldK) : upperEndMeroField) = 1 := by simp
    have hdat : HasGammaTubeDatum 1 (((1 : gammaFieldK)) : upperEndMeroField) 0 0 0 1 := by
      rw [hone]
      exact hasGammaTubeDatum_one
    rw [if_neg (one_ne_zero : (1 : gammaFieldK) ≠ 0), gammaDatumTripleK_eq_of one_ne_zero hdat]
    rfl
  map_mul' x y := by
    by_cases hx : x = 0
    · rw [hx, zero_mul, if_pos rfl, zero_mul]
    by_cases hy : y = 0
    · rw [hy, mul_zero, if_pos rfl, mul_zero]
    obtain ⟨k, a, b, c, hdx⟩ := exists_hasGammaTubeDatum_coe hx
    obtain ⟨k', a', b', c', hdy⟩ := exists_hasGammaTubeDatum_coe hy
    have hcoe : ((x * y : gammaFieldK) : upperEndMeroField)
        = (x : upperEndMeroField) * (y : upperEndMeroField) := by simp
    have hdxy : HasGammaTubeDatum 1 ((x * y : gammaFieldK) : upperEndMeroField)
        (k + k') (a + a') (b + b') (c * c') := by
      rw [hcoe]
      exact hdx.mul hdy
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, gammaDatumTripleK_eq_of hx hdx,
      gammaDatumTripleK_eq_of hy hdy, gammaDatumTripleK_eq_of (mul_ne_zero hx hy) hdxy,
      ← WithZero.coe_mul]
    refine congrArg _ ?_
    show Multiplicative.ofAdd (lexValue (k + k') (a + a') (b + b'))
      = Multiplicative.ofAdd (lexValue k a b) * Multiplicative.ofAdd (lexValue k' a' b')
    rw [lexValue_add]
    rfl
  map_add_le_max' x y := by
    by_cases hxy : x + y = 0
    · rw [hxy, if_pos rfl]
      exact zero_le
    by_cases hx : x = 0
    · rw [hx, zero_add, if_pos rfl]
      exact le_max_right _ _
    by_cases hy : y = 0
    · rw [hy, add_zero, if_pos rfl]
      exact le_max_left _ _
    obtain ⟨k, a, b, c, hdx⟩ := exists_hasGammaTubeDatum_coe hx
    obtain ⟨k', a', b', c', hdy⟩ := exists_hasGammaTubeDatum_coe hy
    obtain ⟨m, A, B, C, hdxy⟩ := exists_hasGammaTubeDatum_coe hxy
    have hcoe : ((x + y : gammaFieldK) : upperEndMeroField)
        = (x : upperEndMeroField) + (y : upperEndMeroField) := by simp
    rw [hcoe] at hdxy
    have hnot := not_hasGammaTubeDatum_add_dominates one_pos hdx hdy hdxy
    rw [if_neg hxy, if_neg hx, if_neg hy, gammaDatumTripleK_eq_of hx hdx,
      gammaDatumTripleK_eq_of hy hdy, gammaDatumTripleK_eq_of hxy (by rw [hcoe]; exact hdxy)]
    refine not_lt.mp fun hlt => ?_
    rw [max_lt_iff] at hlt
    obtain ⟨h1, h2⟩ := hlt
    rw [WithZero.coe_lt_coe] at h1 h2
    rw [lexOfDatum_triple, lexOfDatum_triple] at h1
    rw [lexOfDatum_triple, lexOfDatum_triple] at h2
    exact hnot ⟨lexValue_lt_iff.mp h1, lexValue_lt_iff.mp h2⟩

theorem gammaLexValuation_apply_of_ne_zero {x : gammaFieldK} (hx : x ≠ 0) :
    gammaLexValuation x
      = ((Multiplicative.ofAdd (lexOfDatum (gammaDatumTripleK x)) :
        Multiplicative (ℤ ×ₗ ℤ ×ₗ ℤ)) : WithZero (Multiplicative (ℤ ×ₗ ℤ ×ₗ ℤ))) := by
  show (if x = 0 then (0 : WithZero (Multiplicative (ℤ ×ₗ ℤ ×ₗ ℤ))) else _) = _
  rw [if_neg hx]

end

end GaloisForLFunctions.HTGeometry
