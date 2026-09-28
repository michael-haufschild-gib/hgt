import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalCrossFlux

/-!
# The mixed cusp flux of the exceptional source vanishes at infinite height

Let `U` be the literal exceptional finite-deck Maass source and `V` a cusp-zero finite-deck
pre-vector.  Above height one the mixed boundary current
`B(y) = ∑_q ∫_0^L ∂_y U_q(x,y) · conj V_q(x,y) dx` and its Green density `D` are controlled by the
horocycle slice energies: by `ab ≤ (a² + b²)/2` and the cusp-zero slice Poincaré inequality,

`|B(y)| ≤ ½ y⁻² ∫_0^L (‖hypGradY U‖² + (L/2π)² ‖hypGradX V‖²) dx`,

and, after the literal Maass equation `U_xx + U_yy = -λ y⁻² U`, `D` is bounded by the analogous sum of
horizontal, vertical and mass energies.  The weighted slice energies are integrable on every tail
`(c, ∞)`, so `B, D ∈ L¹(c, ∞)`.  The finite-strip identity `B(d) - B(c) = ∫_c^d D` then gives a
finite limit of `B`, which must vanish because `B` is integrable; hence
`∫_c^∞ D = -B(c)` and `B(y) → 0`.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory ModularGroup
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open MaassCongruenceL2 SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
  SelbergMaassMean GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

/-! ### Horocycle slice energies -/

/-- The horocycle slice energy `∫_0^L ‖G(x + iy)‖² dx` over one level period. -/
def deckSliceEnergy {N : ℕ} (G : ℍ → DeckSpace N) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(N + 1 : ℝ), ‖G (ofComplex (point x y))‖ ^ 2

theorem continuous_ofComplex_point {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => ofComplex (point x y) := by
  have he : (fun x : ℝ => ofComplex (point x y)) =
      fun x : ℝ => (⟨point x y, by simpa [point] using hy⟩ : ℍ) := by
    funext x
    exact ofComplex_apply_of_im_pos (by simpa [point] using hy)
  rw [he]
  have hm : Continuous fun x : ℝ => point x y := by
    change Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I
    fun_prop
  exact hm.upperHalfPlaneMk (fun _ => by simpa [point] using hy)

theorem im_ofComplex_point {x y : ℝ} (hy : 0 < y) : (ofComplex (point x y)).im = y := by
  rw [ofComplex_apply_of_im_pos (by simpa [point] using hy)]
  simp [point]

theorem deckSliceEnergy_nonneg {N : ℕ} (G : ℍ → DeckSpace N) (y : ℝ) :
    0 ≤ deckSliceEnergy G y :=
  intervalIntegral.integral_nonneg (by positivity) fun _ _ => by positivity

theorem continuous_component_point {N : ℕ} {G : ℍ → DeckSpace N} (hG : Continuous G)
    (q : Deck N) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => G (ofComplex (point x y)) q :=
  (PiLp.continuous_apply 2 (fun _ : Deck N => ℂ) q).comp (hG.comp (continuous_ofComplex_point hy))

theorem intervalIntegrable_component_normSq {N : ℕ} {G : ℍ → DeckSpace N} (hG : Continuous G)
    (q : Deck N) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => ‖G (ofComplex (point x y)) q‖ ^ 2) volume a b :=
  ((continuous_component_point hG q hy).norm.pow 2).intervalIntegrable _ _

/-- The coordinate masses sum to the slice energy. -/
theorem sum_component_normSq_eq_deckSliceEnergy {N : ℕ} {G : ℍ → DeckSpace N}
    (hG : Continuous G) {y : ℝ} (hy : 0 < y) :
    (∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ), ‖G (ofComplex (point x y)) q‖ ^ 2) =
      deckSliceEnergy G y := by
  rw [← intervalIntegral.integral_finsetSum fun q _ =>
    intervalIntegrable_component_normSq hG q hy _ _]
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  rw [EuclideanSpace.norm_sq_eq]

/-! ### Retracted coordinates above height one -/

theorem retractedDeckComponent_one_of_gt {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {x y : ℝ} (hy : 1 < y) :
    retractedDeckComponent 1 F q (x, y) = (F : ℍ → DeckSpace N) (ofComplex (point x y)) q := by
  unfold retractedDeckComponent
  rw [retractedPoint_eq_of_le one_pos hy.le]
  rfl

theorem stripDerivY_retractedDeckComponent_of_gt {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {x y : ℝ} (hy : 1 < y) :
    stripDeriv (0, 1) (retractedDeckComponent 1 F q) (x, y) =
      (y : ℂ)⁻¹ * hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y)) q := by
  have hy0 : 0 < y := one_pos.trans hy
  have h := retractedDeckComponentY_eq_chartDeriv (x := x) one_pos hy F q
  change retractedDeckComponentY 1 F q (x, y) = _
  rw [h]
  have him := im_ofComplex_point (x := x) hy0
  change _ = (y : ℂ)⁻¹ * (((ofComplex (point x y)).im : ℂ) •
    chartDeriv (F : ℍ → DeckSpace N) Complex.I (ofComplex (point x y))) q
  rw [him]
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hyc, one_mul]
  rfl

theorem stripDerivX_retractedDeckComponent_of_gt {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {x y : ℝ} (hy : 1 < y) :
    stripDeriv (1, 0) (retractedDeckComponent 1 F q) (x, y) =
      (y : ℂ)⁻¹ * hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q := by
  have hy0 : 0 < y := one_pos.trans hy
  have h := retractedDeckComponentX_eq_chartDeriv (x := x) one_pos hy F q
  change retractedDeckComponentX 1 F q (x, y) = _
  rw [h]
  have him := im_ofComplex_point (x := x) hy0
  change _ = (y : ℂ)⁻¹ * (((ofComplex (point x y)).im : ℂ) •
    chartDeriv (F : ℍ → DeckSpace N) 1 (ofComplex (point x y))) q
  rw [him]
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hyc, one_mul]
  rfl

/-! ### Pointwise bilinear bounds -/

theorem norm_mul_star_le (a b : ℂ) : ‖a * star b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  rw [norm_mul, norm_star]
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- A deck-summed slice pairing is bounded by half the sum of the two slice energies. -/
theorem norm_sum_integral_mul_star_le {N : ℕ} {G H : ℍ → DeckSpace N} (hG : Continuous G)
    (hH : Continuous H) {y : ℝ} (hy : 0 < y) (c : ℂ) :
    ‖∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖ ≤
      (‖c‖ ^ 2 * deckSliceEnergy G y + deckSliceEnergy H y) / 2 := by
  have hL : (0 : ℝ) ≤ (N + 1 : ℝ) := by positivity
  have hint : ∀ q : Deck N, IntervalIntegrable (fun x : ℝ =>
      (‖c‖ ^ 2 * ‖G (ofComplex (point x y)) q‖ ^ 2 + ‖H (ofComplex (point x y)) q‖ ^ 2) / 2)
      volume 0 (N + 1 : ℝ) := fun q =>
    (((continuous_const.mul ((continuous_component_point hG q hy).norm.pow 2)).add
      ((continuous_component_point hH q hy).norm.pow 2)).div_const 2).intervalIntegrable _ _
  calc ‖∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖
      ≤ ∑ q : Deck N, ‖∫ x in (0 : ℝ)..(N + 1 : ℝ),
          c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
          (‖c‖ ^ 2 * ‖G (ofComplex (point x y)) q‖ ^ 2 +
            ‖H (ofComplex (point x y)) q‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine (intervalIntegral.norm_integral_le_integral_norm hL).trans ?_
        refine intervalIntegral.integral_mono_on hL ?_ (hint q) fun x _ => ?_
        · exact ((((continuous_const.mul (continuous_component_point hG q hy)).mul
            (continuous_component_point hH q hy).star)).norm).intervalIntegrable _ _
        · rw [norm_mul, norm_mul, norm_star]
          nlinarith [sq_nonneg (‖c‖ * ‖G (ofComplex (point x y)) q‖ - ‖H (ofComplex (point x y)) q‖),
            norm_nonneg c, norm_nonneg (G (ofComplex (point x y)) q)]
    _ = (‖c‖ ^ 2 * deckSliceEnergy G y + deckSliceEnergy H y) / 2 := by
        rw [← sum_component_normSq_eq_deckSliceEnergy hG hy,
          ← sum_component_normSq_eq_deckSliceEnergy hH hy, Finset.mul_sum,
          ← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add
          ((intervalIntegrable_component_normSq hG q hy _ _).const_mul _)
          (intervalIntegrable_component_normSq hH q hy _ _), intervalIntegral.integral_const_mul]

/-- The symmetric form of the slice bound: `‖∑∫ c G H̄‖ ≤ ‖c‖ (E_G + E_H)/2`. -/
theorem norm_sum_integral_mul_star_le' {N : ℕ} {G H : ℍ → DeckSpace N} (hG : Continuous G)
    (hH : Continuous H) {y : ℝ} (hy : 0 < y) (c : ℂ) :
    ‖∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖ ≤
      ‖c‖ * (deckSliceEnergy G y + deckSliceEnergy H y) / 2 := by
  have hL : (0 : ℝ) ≤ (N + 1 : ℝ) := by positivity
  calc ‖∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖
      ≤ ∑ q : Deck N, ‖∫ x in (0 : ℝ)..(N + 1 : ℝ),
          c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
          ‖c‖ * (‖G (ofComplex (point x y)) q‖ ^ 2 + ‖H (ofComplex (point x y)) q‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine (intervalIntegral.norm_integral_le_integral_norm hL).trans ?_
        refine intervalIntegral.integral_mono_on hL ?_ ?_ fun x _ => ?_
        · exact ((((continuous_const.mul (continuous_component_point hG q hy)).mul
            (continuous_component_point hH q hy).star)).norm).intervalIntegrable _ _
        · exact (((intervalIntegrable_component_normSq hG q hy _ _).add
            (intervalIntegrable_component_normSq hH q hy _ _)).const_mul ‖c‖).div_const 2
        · rw [norm_mul, norm_mul, norm_star]
          have hc := norm_nonneg c
          nlinarith [sq_nonneg (‖G (ofComplex (point x y)) q‖ - ‖H (ofComplex (point x y)) q‖),
            mul_nonneg hc (sq_nonneg (‖G (ofComplex (point x y)) q‖ -
              ‖H (ofComplex (point x y)) q‖))]
    _ = ‖c‖ * (deckSliceEnergy G y + deckSliceEnergy H y) / 2 := by
        rw [← sum_component_normSq_eq_deckSliceEnergy hG hy,
          ← sum_component_normSq_eq_deckSliceEnergy hH hy, ← Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add (intervalIntegrable_component_normSq hG q hy _ _)
            (intervalIntegrable_component_normSq hH q hy _ _)]

/-- The weighted slice bound: `‖∑∫ c G H̄‖ ≤ ‖c‖ (t E_G + E_H / t)/2` for every `t > 0`. -/
theorem norm_sum_integral_mul_star_le_weighted {N : ℕ} {G H : ℍ → DeckSpace N} (hG : Continuous G)
    (hH : Continuous H) {y : ℝ} (hy : 0 < y) (c : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖ ≤
      ‖c‖ * (t * deckSliceEnergy G y + deckSliceEnergy H y / t) / 2 := by
  have hL : (0 : ℝ) ≤ (N + 1 : ℝ) := by positivity
  calc ‖∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖
      ≤ ∑ q : Deck N, ‖∫ x in (0 : ℝ)..(N + 1 : ℝ),
          c * G (ofComplex (point x y)) q * star (H (ofComplex (point x y)) q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
          ‖c‖ * (t * ‖G (ofComplex (point x y)) q‖ ^ 2 +
            ‖H (ofComplex (point x y)) q‖ ^ 2 / t) / 2 := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine (intervalIntegral.norm_integral_le_integral_norm hL).trans ?_
        refine intervalIntegral.integral_mono_on hL ?_ ?_ fun x _ => ?_
        · exact ((((continuous_const.mul (continuous_component_point hG q hy)).mul
            (continuous_component_point hH q hy).star)).norm).intervalIntegrable _ _
        · exact ((((intervalIntegrable_component_normSq hG q hy _ _).const_mul t).add
            ((intervalIntegrable_component_normSq hH q hy _ _).div_const t)).const_mul
              ‖c‖).div_const 2
        · rw [norm_mul, norm_mul, norm_star]
          have hc := norm_nonneg c
          have key : ‖G (ofComplex (point x y)) q‖ * ‖H (ofComplex (point x y)) q‖ ≤
              (t * ‖G (ofComplex (point x y)) q‖ ^ 2 + ‖H (ofComplex (point x y)) q‖ ^ 2 / t) / 2 := by
            set a := ‖G (ofComplex (point x y)) q‖
            set b := ‖H (ofComplex (point x y)) q‖
            have h : t * a ^ 2 + b ^ 2 / t - 2 * (a * b) = (t * a - b) ^ 2 / t := by
              field_simp; ring
            have h2 : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
            linarith
          calc ‖c‖ * ‖G (ofComplex (point x y)) q‖ * ‖H (ofComplex (point x y)) q‖
              = ‖c‖ * (‖G (ofComplex (point x y)) q‖ * ‖H (ofComplex (point x y)) q‖) := by ring
            _ ≤ ‖c‖ * ((t * ‖G (ofComplex (point x y)) q‖ ^ 2 +
                ‖H (ofComplex (point x y)) q‖ ^ 2 / t) / 2) := mul_le_mul_of_nonneg_left key hc
            _ = _ := by ring
    _ = ‖c‖ * (t * deckSliceEnergy G y + deckSliceEnergy H y / t) / 2 := by
        rw [← sum_component_normSq_eq_deckSliceEnergy hG hy,
          ← sum_component_normSq_eq_deckSliceEnergy hH hy, Finset.mul_sum, Finset.sum_div,
          ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add ((intervalIntegrable_component_normSq hG q hy _ _).const_mul t)
            ((intervalIntegrable_component_normSq hH q hy _ _).div_const t),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_div]

/-- The sharp cusp-zero slice Poincaré inequality in slice-energy form. -/
theorem deckSliceEnergy_le_poincare {N : ℕ} (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) :
    deckSliceEnergy (F : ℍ → DeckSpace N) y ≤
      ((N + 1 : ℝ) / (2 * Real.pi)) ^ 2 *
        (y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y) := by
  have h := level_cusp_slice_poincare F hy 0
  have hL : (0 : ℝ) + ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by push_cast; ring
  rw [hL] at h
  unfold deckSliceEnergy
  linarith

section Source

variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)

theorem sourceVector_c1 : IsChartC1 (sourceVector N f) :=
  formPreDomain.c1 (sourceInFormPreDomain N lam f)

/-- Above height one the boundary current is the deck-summed slice pairing of `y⁻¹ hypGradY U`
with `V`. -/
theorem sourceTestBoundaryCurrent_eq_of_gt (F : formPreDomain N) {y : ℝ} (hy : 1 < y) :
    sourceTestBoundaryCurrent N lam f F y =
      ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        (y : ℂ)⁻¹ * hypGradY (sourceVector N f) (ofComplex (point x y)) q *
          star ((F : ℍ → DeckSpace N) (ofComplex (point x y)) q) := by
  unfold sourceTestBoundaryCurrent
  refine Finset.sum_congr rfl fun q _ => intervalIntegral.integral_congr fun x _ => ?_
  simp only
  rw [stripDerivY_retractedDeckComponent_of_gt _ q hy, retractedDeckComponent_one_of_gt F q hy]
  rfl

/-- **Current bound.**  `|B(y)| ≤ ½ (y⁻² E_Y(U) + E(V))`. -/
theorem norm_sourceTestBoundaryCurrent_le (F : formPreDomain N) {y : ℝ} (hy : 1 < y) :
    ‖sourceTestBoundaryCurrent N lam f F y‖ ≤
      (y⁻¹ ^ 2 * deckSliceEnergy (hypGradY (sourceVector N f)) y +
        deckSliceEnergy (F : ℍ → DeckSpace N) y) / 2 := by
  have hy0 : 0 < y := one_pos.trans hy
  rw [sourceTestBoundaryCurrent_eq_of_gt N lam f F hy]
  have h := norm_sum_integral_mul_star_le (continuous_hypGradY_vec (sourceVector_c1 N lam f))
    (continuous_of_isChartC1 (formPreDomain.c1 F)) hy0 ((y : ℂ)⁻¹)
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0] at h
  exact h

/-- Above height one the Green density, after the Maass equation, is a sum of three slice
pairings: mass, horizontal and vertical. -/
theorem sourceTestGreenDensity_eq_of_gt (F : formPreDomain N) {y : ℝ} (hy : 1 < y) :
    sourceTestGreenDensity N lam f F y =
      (∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        ((-(lam.1 / y ^ 2) : ℝ) : ℂ) * sourceVector N f (ofComplex (point x y)) q *
          star ((F : ℍ → DeckSpace N) (ofComplex (point x y)) q)) +
      (∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        ((y ^ 2)⁻¹ : ℂ) * hypGradX (sourceVector N f) (ofComplex (point x y)) q *
          star (hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q)) +
      (∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        ((y ^ 2)⁻¹ : ℂ) * hypGradY (sourceVector N f) (ofComplex (point x y)) q *
          star (hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y)) q)) := by
  have hy0 : 0 < y := one_pos.trans hy
  have hS := sourceVector_c1 N lam f
  have hF := formPreDomain.c1 F
  unfold sourceTestGreenDensity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hc0 := continuous_component_point (continuous_of_isChartC1 hS) q hy0
  have hc1 := continuous_component_point (continuous_of_isChartC1 hF) q hy0
  have hc2 := continuous_component_point (continuous_hypGradX_vec hS) q hy0
  have hc3 := continuous_component_point (continuous_hypGradX_vec hF) q hy0
  have hc4 := continuous_component_point (continuous_hypGradY_vec hS) q hy0
  have hc5 := continuous_component_point (continuous_hypGradY_vec hF) q hy0
  have iA : IntervalIntegrable (fun x : ℝ =>
      ((-(lam.1 / y ^ 2) : ℝ) : ℂ) * sourceVector N f (ofComplex (point x y)) q *
        star ((F : ℍ → DeckSpace N) (ofComplex (point x y)) q)) volume 0 (N + 1 : ℝ) :=
    ((continuous_const.mul hc0).mul hc1.star).intervalIntegrable _ _
  have iB : IntervalIntegrable (fun x : ℝ =>
      ((y ^ 2)⁻¹ : ℂ) * hypGradX (sourceVector N f) (ofComplex (point x y)) q *
        star (hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q)) volume 0 (N + 1 : ℝ) :=
    ((continuous_const.mul hc2).mul hc3.star).intervalIntegrable _ _
  have iC : IntervalIntegrable (fun x : ℝ =>
      ((y ^ 2)⁻¹ : ℂ) * hypGradY (sourceVector N f) (ofComplex (point x y)) q *
        star (hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y)) q)) volume 0 (N + 1 : ℝ) :=
    ((continuous_const.mul hc4).mul hc5.star).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add iA iB, ← intervalIntegral.integral_add (iA.add iB) iC]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [sourceTestGreenCoordinateIntegrand]
  have hlap := retractedSourceDeckComponent_laplacian N lam f q (x := x) one_pos hy
  have hU := retractedDeckComponent_one_of_gt (sourceInFormPreDomain N lam f) q (x := x) hy
  have hV := retractedDeckComponent_one_of_gt F q (x := x) hy
  have hUx := stripDerivX_retractedDeckComponent_of_gt (sourceInFormPreDomain N lam f) q (x := x) hy
  have hUy := stripDerivY_retractedDeckComponent_of_gt (sourceInFormPreDomain N lam f) q (x := x) hy
  have hVx := stripDerivX_retractedDeckComponent_of_gt F q (x := x) hy
  have hVy := stripDerivY_retractedDeckComponent_of_gt F q (x := x) hy
  have hsplit : ∀ a b c d e : ℂ, (a * e + b) + (c * e + d) = (a + c) * e + b + d :=
    fun a b c d e => by ring
  rw [hsplit, hlap, hU, hV, hUx, hUy, hVx, hVy]
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  simp only [star_mul', Complex.star_def, map_inv₀, Complex.conj_ofReal]
  change (((-(lam.1 / y ^ 2) : ℝ) : ℂ) * sourceVector N f (ofComplex (point x y)) q *
      star ((F : ℍ → DeckSpace N) (ofComplex (point x y)) q) +
    (y : ℂ)⁻¹ * hypGradX (sourceVector N f) (ofComplex (point x y)) q *
      ((y : ℂ)⁻¹ * star (hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y)) q)) +
    (y : ℂ)⁻¹ * hypGradY (sourceVector N f) (ofComplex (point x y)) q *
      ((y : ℂ)⁻¹ * star (hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y)) q))) = _
  push_cast
  field_simp
  rfl

/-- **Density bound.**  The Green density is bounded by the mass, horizontal and vertical slice
energies. -/
theorem norm_sourceTestGreenDensity_le (F : formPreDomain N) {y : ℝ} (hy : 1 < y) :
    ‖sourceTestGreenDensity N lam f F y‖ ≤
      lam.1 / y ^ 2 * (deckSliceEnergy (sourceVector N f) y +
        deckSliceEnergy (F : ℍ → DeckSpace N) y) / 2 +
      (y ^ 2)⁻¹ * (deckSliceEnergy (hypGradX (sourceVector N f)) y +
        deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y) / 2 +
      (y ^ 2)⁻¹ * (deckSliceEnergy (hypGradY (sourceVector N f)) y +
        deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y) / 2 := by
  have hy0 : 0 < y := one_pos.trans hy
  have hS := sourceVector_c1 N lam f
  have hF := formPreDomain.c1 F
  have hlam : 0 < lam.1 := lam.2.1
  rw [sourceTestGreenDensity_eq_of_gt N lam f F hy]
  have h1 := norm_sum_integral_mul_star_le' (continuous_of_isChartC1 hS)
    (continuous_of_isChartC1 hF) hy0 (((-(lam.1 / y ^ 2) : ℝ) : ℂ))
  have h2 := norm_sum_integral_mul_star_le' (continuous_hypGradX_vec hS)
    (continuous_hypGradX_vec hF) hy0 (((y ^ 2)⁻¹ : ℂ))
  have h3 := norm_sum_integral_mul_star_le' (continuous_hypGradY_vec hS)
    (continuous_hypGradY_vec hF) hy0 (((y ^ 2)⁻¹ : ℂ))
  have hn1 : ‖(((-(lam.1 / y ^ 2) : ℝ) : ℂ))‖ = lam.1 / y ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have hn2 : ‖(((y ^ 2)⁻¹ : ℂ))‖ = (y ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  rw [hn1] at h1
  rw [hn2] at h2 h3
  exact (norm_add₃_le).trans (add_le_add (add_le_add h1 h2) h3)

end Source

/-- A function with a limit at infinity that is integrable on a tail has limit zero. -/
theorem eq_zero_of_integrableOn_Ioi_of_tendsto {g : ℝ → ℂ} {c : ℝ} {ℓ : ℂ}
    (hg : IntegrableOn g (Ioi c)) (hlim : Tendsto g atTop (𝓝 ℓ)) : ℓ = 0 := by
  by_contra hℓ
  have hpos : 0 < ‖ℓ‖ / 2 := by have := norm_pos_iff.mpr hℓ; positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hlim.norm).eventually (lt_mem_nhds
    (by linarith [norm_nonneg ℓ] : ‖ℓ‖ / 2 < ‖ℓ‖)))
  have hint : IntegrableOn (fun _ : ℝ => ‖ℓ‖ / 2) (Ioi (max c T)) := by
    refine Integrable.mono' ((hg.mono_set (Ioi_subset_Ioi (le_max_left _ _))).norm)
      aestronglyMeasurable_const ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact (hT y ((le_max_right _ _).trans hy.le)).le
  rw [integrableOn_const_iff] at hint
  rcases hint with h | h
  · exact hpos.ne' (enorm_eq_zero.mp h)
  · rw [Real.volume_Ioi] at h
    exact lt_irrefl _ h

section Tail

variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)

theorem integrableOn_invSq_deckSliceEnergy_hypGradX (F : cuspidalFormPreDomain N) {c : ℝ}
    (hc : 1 ≤ c) :
    IntegrableOn (fun y => y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y)
      (Ioi c) :=
  level_hypGradX_slice_weighted_integrable F hc

theorem integrableOn_invSq_deckSliceEnergy_hypGradY (F : cuspidalFormPreDomain N) {c : ℝ}
    (hc : 1 ≤ c) :
    IntegrableOn (fun y => y⁻¹ ^ 2 * deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y)
      (Ioi c) :=
  level_hypGradY_slice_weighted_integrable F hc

/-- **The mixed boundary current is integrable on every tail.** -/
theorem integrableOn_sourceTestBoundaryCurrent (F : cuspidalFormPreDomain N) {c : ℝ}
    (hc : 1 < c) :
    IntegrableOn (sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N F))
      (Ioi c) := by
  set CP : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ 2
  have hmaj : IntegrableOn (fun y => (y⁻¹ ^ 2 *
      deckSliceEnergy (hypGradY (sourceVector N f)) y +
      CP * (y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y)) / 2) (Ioi c) :=
    (((integrableOn_invSq_deckSliceEnergy_hypGradY N (sourceInCuspidalFormPreDomain N lam f)
      hc.le).add ((integrableOn_invSq_deckSliceEnergy_hypGradX N F hc.le).const_mul CP)).div_const 2)
  refine Integrable.mono' hmaj
    (sourceTestBoundaryCurrent_continuous N lam f _).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
  have hy1 : 1 < y := hc.trans hy
  refine (norm_sourceTestBoundaryCurrent_le N lam f _ hy1).trans ?_
  have hP := deckSliceEnergy_le_poincare F (one_pos.trans hy1)
  change (y⁻¹ ^ 2 * deckSliceEnergy (hypGradY (sourceVector N f)) y +
      deckSliceEnergy (F : ℍ → DeckSpace N) y) / 2 ≤ _
  linarith

/-- **The Green density is integrable on every tail.** -/
theorem integrableOn_sourceTestGreenDensity (F : cuspidalFormPreDomain N) {c : ℝ} (hc : 1 < c) :
    IntegrableOn (sourceTestGreenDensity N lam f (cuspidalFormPreDomain.toFormPreDomain N F))
      (Ioi c) := by
  set CP : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ 2
  set S := sourceInCuspidalFormPreDomain N lam f
  have hXS := integrableOn_invSq_deckSliceEnergy_hypGradX N S hc.le
  have hXF := integrableOn_invSq_deckSliceEnergy_hypGradX N F hc.le
  have hYS := integrableOn_invSq_deckSliceEnergy_hypGradY N S hc.le
  have hYF := integrableOn_invSq_deckSliceEnergy_hypGradY N F hc.le
  have hmaj : IntegrableOn (fun y =>
      lam.1 * CP * ((y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (sourceVector N f)) y) +
        (y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y)) / 2 +
      ((y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (sourceVector N f)) y) +
        (y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y)) / 2 +
      ((y⁻¹ ^ 2 * deckSliceEnergy (hypGradY (sourceVector N f)) y) +
        (y⁻¹ ^ 2 * deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y)) / 2) (Ioi c) :=
    ((((hXS.add hXF).const_mul (lam.1 * CP)).div_const 2).add
      ((hXS.add hXF).div_const 2)).add ((hYS.add hYF).div_const 2)
  refine Integrable.mono' hmaj
    (sourceTestGreenDensity_continuous N lam f _).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
  have hy1 : 1 < y := hc.trans hy
  have hy0 : 0 < y := one_pos.trans hy1
  refine (norm_sourceTestGreenDensity_le N lam f _ hy1).trans ?_
  have hPS := deckSliceEnergy_le_poincare S hy0
  have hPF := deckSliceEnergy_le_poincare F hy0
  change lam.1 / y ^ 2 * (deckSliceEnergy (sourceVector N f) y +
      deckSliceEnergy (F : ℍ → DeckSpace N) y) / 2 +
    (y ^ 2)⁻¹ * (deckSliceEnergy (hypGradX (sourceVector N f)) y +
      deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y) / 2 +
    (y ^ 2)⁻¹ * (deckSliceEnergy (hypGradY (sourceVector N f)) y +
      deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y) / 2 ≤ _
  change deckSliceEnergy (sourceVector N f) y ≤ CP * (y⁻¹ ^ 2 *
    deckSliceEnergy (hypGradX (sourceVector N f)) y) at hPS
  have hlam : 0 < lam.1 := lam.2.1
  have hyinv : (y ^ 2)⁻¹ = y⁻¹ ^ 2 := by rw [inv_pow]
  have hy2 : lam.1 / y ^ 2 ≤ lam.1 := div_le_self hlam.le (by nlinarith)
  have hE1 := deckSliceEnergy_nonneg (sourceVector N f) y
  have hE2 := deckSliceEnergy_nonneg (F : ℍ → DeckSpace N) y
  have hmass : lam.1 / y ^ 2 * (deckSliceEnergy (sourceVector N f) y +
      deckSliceEnergy (F : ℍ → DeckSpace N) y) ≤ lam.1 * CP *
      ((y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (sourceVector N f)) y) +
        (y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y)) := by
    calc lam.1 / y ^ 2 * (deckSliceEnergy (sourceVector N f) y +
          deckSliceEnergy (F : ℍ → DeckSpace N) y)
        ≤ lam.1 * (deckSliceEnergy (sourceVector N f) y +
          deckSliceEnergy (F : ℍ → DeckSpace N) y) :=
          mul_le_mul_of_nonneg_right hy2 (by positivity)
      _ ≤ lam.1 * (CP * (y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (sourceVector N f)) y) +
          CP * (y⁻¹ ^ 2 * deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y)) :=
          mul_le_mul_of_nonneg_left (add_le_add hPS hPF) hlam.le
      _ = _ := by ring
  rw [hyinv]
  nlinarith

/-- **Full-height flux law (SQB-CMF).**  For a cusp-zero pre-vector `F` and every `c > 1`, the mixed
boundary current and the Green density are integrable on `(c, ∞)`,
`∫_c^∞ D = -B(c)`, and `B(y) → 0` as `y → ∞`. -/
theorem sourceTestFlux_tail_law (F : cuspidalFormPreDomain N) {c : ℝ} (hc : 1 < c) :
    IntegrableOn (sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N F))
        (Ioi c) ∧
      IntegrableOn (sourceTestGreenDensity N lam f (cuspidalFormPreDomain.toFormPreDomain N F))
        (Ioi c) ∧
      (∫ y in Ioi c, sourceTestGreenDensity N lam f (cuspidalFormPreDomain.toFormPreDomain N F) y) =
        -sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N F) c ∧
      Tendsto (sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N F))
        atTop (𝓝 0) := by
  set F₀ := cuspidalFormPreDomain.toFormPreDomain N F
  have hB := integrableOn_sourceTestBoundaryCurrent N lam f F hc
  have hD := integrableOn_sourceTestGreenDensity N lam f F hc
  have hinc : ∀ d, c ≤ d → sourceTestBoundaryCurrent N lam f F₀ d =
      sourceTestBoundaryCurrent N lam f F₀ c + ∫ y in c..d, sourceTestGreenDensity N lam f F₀ y := by
    intro d hd
    rw [sourceTestGreenDensity_increment N lam f F₀ (fun y hy => ?_)]
    · ring
    · rw [uIcc_of_le hd] at hy
      exact hc.trans_le hy.1
  have hlimD : Tendsto (fun d => ∫ y in c..d, sourceTestGreenDensity N lam f F₀ y) atTop
      (𝓝 (∫ y in Ioi c, sourceTestGreenDensity N lam f F₀ y)) :=
    intervalIntegral_tendsto_integral_Ioi c hD tendsto_id
  have hlimB : Tendsto (sourceTestBoundaryCurrent N lam f F₀) atTop
      (𝓝 (sourceTestBoundaryCurrent N lam f F₀ c +
        ∫ y in Ioi c, sourceTestGreenDensity N lam f F₀ y)) := by
    refine (tendsto_const_nhds.add hlimD).congr' ?_
    filter_upwards [eventually_ge_atTop c] with d hd
    exact (hinc d hd).symm
  have hzero := eq_zero_of_integrableOn_Ioi_of_tendsto hB hlimB
  refine ⟨hB, hD, ?_, ?_⟩
  · linear_combination hzero
  · rw [hzero] at hlimB; exact hlimB

/-! ### The quantitative tail law -/

/-- The squared cusp-cylinder energy `E_F(Y)² = ∫_Y^∞ y⁻² (E_X F + E_Y F)(y) dy`, i.e.
`∑_q ∫_Y^∞ ∫_0^L (|∂_x F_q|² + |∂_y F_q|²) dx dy`. -/
def cuspCylinderEnergySq (F : ℍ → DeckSpace N) (Y : ℝ) : ℝ :=
  ∫ y in Ioi Y, y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX F) y + deckSliceEnergy (hypGradY F) y)

/-- The cusp-cylinder energy `E_F(Y)`. -/
def cuspCylinderEnergy (F : ℍ → DeckSpace N) (Y : ℝ) : ℝ := Real.sqrt (cuspCylinderEnergySq N F Y)

theorem cuspCylinderEnergySq_nonneg (F : ℍ → DeckSpace N) (Y : ℝ) :
    0 ≤ cuspCylinderEnergySq N F Y :=
  setIntegral_nonneg measurableSet_Ioi fun y _ => by
    have := deckSliceEnergy_nonneg (hypGradX F) y
    have := deckSliceEnergy_nonneg (hypGradY F) y
    positivity

theorem integrableOn_cylinderDensity (F : cuspidalFormPreDomain N) {c : ℝ} (hc : 1 ≤ c) :
    IntegrableOn (fun y => y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y +
      deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y)) (Ioi c) :=
  ((integrableOn_invSq_deckSliceEnergy_hypGradX N F hc).add
    (integrableOn_invSq_deckSliceEnergy_hypGradY N F hc)).congr_fun
    (fun y _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi

/-- Optimizing `x ≤ K (tP + Q/t)/2` over `t > 0` gives `x ≤ K √P √Q`. -/
theorem le_mul_sqrt_mul_sqrt_of_forall {x K P Q : ℝ} (hK : 0 ≤ K) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : ∀ t : ℝ, 0 < t → x ≤ K * (t * P + Q / t) / 2) : x ≤ K * (Real.sqrt P * Real.sqrt Q) := by
  rcases hP.eq_or_lt with hP0 | hPpos
  · subst hP0
    simp only [Real.sqrt_zero, zero_mul, mul_zero]
    by_contra hx
    push Not at hx
    have ht : 0 < K * Q / x + 1 := by positivity
    have h1 := h (K * Q / x + 1) ht
    have h2 : K * (Q / (K * Q / x + 1)) < x := by
      rw [mul_div_assoc', div_lt_iff₀ ht]
      have : K * Q / x * x = K * Q := div_mul_cancel₀ _ hx.ne'
      nlinarith
    linarith
  rcases hQ.eq_or_lt with hQ0 | hQpos
  · subst hQ0
    simp only [Real.sqrt_zero, mul_zero]
    by_contra hx
    push Not at hx
    have ht : 0 < x / (K * P + 1) := by positivity
    have h1 := h (x / (K * P + 1)) ht
    have h2 : K * (x / (K * P + 1) * P) < x := by
      have hKP : 0 < K * P + 1 := by positivity
      rw [show K * (x / (K * P + 1) * P) = x * (K * P / (K * P + 1)) by field_simp]
      have : K * P / (K * P + 1) < 1 := by rw [div_lt_one hKP]; linarith
      nlinarith
    have : K * (x / (K * P + 1) * P + 0 / (x / (K * P + 1))) / 2 < x := by
      rw [zero_div, add_zero]; linarith
    linarith
  have hsP := Real.sqrt_pos.mpr hPpos
  have hsQ := Real.sqrt_pos.mpr hQpos
  have h1 := h (Real.sqrt Q / Real.sqrt P) (div_pos hsQ hsP)
  have hPP := Real.sq_sqrt hP
  have hQQ := Real.sq_sqrt hQ
  have e0 : ∀ p q : ℝ, 0 < p → 0 < q → q / p * p ^ 2 + q ^ 2 / (q / p) = 2 * (p * q) := by
    intro p q hp hq
    field_simp
    ring
  have e := e0 (Real.sqrt P) (Real.sqrt Q) hsP hsQ
  rw [hPP, hQQ] at e
  rw [e] at h1
  linarith

/-- **Weighted density bound on the cylinder.**  For `y ≥ Y > 1` and `t > 0`,
`|D(y)| ≤ (1 + λ (L/2πY)²) y⁻² (t (E_X U + E_Y U) + (E_X V + E_Y V)/t)/2`. -/
theorem norm_sourceTestGreenDensity_le_weighted (F : cuspidalFormPreDomain N) {Y y t : ℝ}
    (hY : 1 < Y) (hy : Y ≤ y) (ht : 0 < t) :
    ‖sourceTestGreenDensity N lam f (cuspidalFormPreDomain.toFormPreDomain N F) y‖ ≤
      (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) / 2 *
        (t * (y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (sourceVector N f)) y +
            deckSliceEnergy (hypGradY (sourceVector N f)) y)) +
          y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y +
            deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y) / t) := by
  set CP : ℝ := ((N + 1 : ℝ) / (2 * Real.pi)) ^ 2
  have hy1 : 1 < y := hY.trans_le hy
  have hy0 : 0 < y := one_pos.trans hy1
  have hY0 : 0 < Y := one_pos.trans hY
  have hS := sourceVector_c1 N lam f
  have hF := cuspidalFormPreDomain.c1 F
  have hlam : 0 < lam.1 := lam.2.1
  rw [sourceTestGreenDensity_eq_of_gt N lam f _ hy1]
  have h1 := norm_sum_integral_mul_star_le_weighted (continuous_of_isChartC1 hS)
    (continuous_of_isChartC1 hF) hy0 (((-(lam.1 / y ^ 2) : ℝ) : ℂ)) ht
  have h2 := norm_sum_integral_mul_star_le_weighted (continuous_hypGradX_vec hS)
    (continuous_hypGradX_vec hF) hy0 (((y ^ 2)⁻¹ : ℂ)) ht
  have h3 := norm_sum_integral_mul_star_le_weighted (continuous_hypGradY_vec hS)
    (continuous_hypGradY_vec hF) hy0 (((y ^ 2)⁻¹ : ℂ)) ht
  have hn1 : ‖(((-(lam.1 / y ^ 2) : ℝ) : ℂ))‖ = lam.1 / y ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  have hn2 : ‖(((y ^ 2)⁻¹ : ℂ))‖ = (y ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  rw [hn1] at h1
  have hinv : (y ^ 2)⁻¹ = y⁻¹ ^ 2 := by rw [inv_pow]
  rw [hn2, hinv] at h2 h3
  simp only [cuspidalFormPreDomain.coe_toFormPreDomain]
  have hPS := deckSliceEnergy_le_poincare (sourceInCuspidalFormPreDomain N lam f) hy0
  have hPF := deckSliceEnergy_le_poincare F hy0
  change deckSliceEnergy (sourceVector N f) y ≤ CP * (y⁻¹ ^ 2 *
    deckSliceEnergy (hypGradX (sourceVector N f)) y) at hPS
  change deckSliceEnergy (F : ℍ → DeckSpace N) y ≤ CP * (y⁻¹ ^ 2 *
    deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y) at hPF
  set aX := deckSliceEnergy (hypGradX (sourceVector N f)) y
  set aY := deckSliceEnergy (hypGradY (sourceVector N f)) y
  set bX := deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y
  set bY := deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y
  have haX := deckSliceEnergy_nonneg (hypGradX (sourceVector N f)) y
  have haY := deckSliceEnergy_nonneg (hypGradY (sourceVector N f)) y
  have hbX := deckSliceEnergy_nonneg (hypGradX (F : ℍ → DeckSpace N)) y
  have hbY := deckSliceEnergy_nonneg (hypGradY (F : ℍ → DeckSpace N)) y
  have hw : y⁻¹ ^ 2 ≤ Y⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity)
    (inv_anti₀ hY0 hy) 2
  have hKc : lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2 = lam.1 * CP * Y⁻¹ ^ 2 := by
    simp only [CP]; field_simp
  -- the mass term through Poincaré
  have hmass : lam.1 / y ^ 2 * (t * deckSliceEnergy (sourceVector N f) y +
      deckSliceEnergy (F : ℍ → DeckSpace N) y / t) / 2 ≤
      lam.1 * CP * Y⁻¹ ^ 2 * (y⁻¹ ^ 2 * (t * aX + bX / t)) / 2 := by
    have hyp2 : lam.1 / y ^ 2 = lam.1 * y⁻¹ ^ 2 := by rw [div_eq_mul_inv, inv_pow]
    rw [hyp2]
    have hCP : 0 ≤ CP := by positivity
    have e1 : t * deckSliceEnergy (sourceVector N f) y +
        deckSliceEnergy (F : ℍ → DeckSpace N) y / t ≤ CP * (y⁻¹ ^ 2 * (t * aX + bX / t)) := by
      have := mul_le_mul_of_nonneg_left hPS ht.le
      have := div_le_div_of_nonneg_right hPF ht.le
      calc _ ≤ t * (CP * (y⁻¹ ^ 2 * aX)) + CP * (y⁻¹ ^ 2 * bX) / t := by linarith
        _ = CP * (y⁻¹ ^ 2 * (t * aX + bX / t)) := by field_simp
    have e2 : 0 ≤ y⁻¹ ^ 2 * (t * aX + bX / t) := by positivity
    calc lam.1 * y⁻¹ ^ 2 * (t * deckSliceEnergy (sourceVector N f) y +
          deckSliceEnergy (F : ℍ → DeckSpace N) y / t) / 2
        ≤ lam.1 * y⁻¹ ^ 2 * (CP * (y⁻¹ ^ 2 * (t * aX + bX / t))) / 2 := by gcongr
      _ ≤ lam.1 * Y⁻¹ ^ 2 * (CP * (y⁻¹ ^ 2 * (t * aX + bX / t))) / 2 := by gcongr
      _ = _ := by ring
  refine (norm_add₃_le).trans ?_
  rw [hKc]
  have e2 : 0 ≤ y⁻¹ ^ 2 * (t * aY + bY / t) := by positivity
  have e3 : 0 ≤ lam.1 * CP * Y⁻¹ ^ 2 := by positivity
  calc _ ≤ lam.1 * CP * Y⁻¹ ^ 2 * (y⁻¹ ^ 2 * (t * aX + bX / t)) / 2 +
        y⁻¹ ^ 2 * (t * aX + bX / t) / 2 + y⁻¹ ^ 2 * (t * aY + bY / t) / 2 := by
        exact add_le_add (add_le_add (h1.trans hmass) h2) h3
    _ ≤ (1 + lam.1 * CP * Y⁻¹ ^ 2) / 2 * (t * (y⁻¹ ^ 2 * (aX + aY)) +
          y⁻¹ ^ 2 * (bX + bY) / t) := by
        have : y⁻¹ ^ 2 * (t * aY + bY / t) / 2 ≤
            (1 + lam.1 * CP * Y⁻¹ ^ 2) * (y⁻¹ ^ 2 * (t * aY + bY / t)) / 2 := by
          nlinarith
        have eq : (1 + lam.1 * CP * Y⁻¹ ^ 2) / 2 * (t * (y⁻¹ ^ 2 * (aX + aY)) +
            y⁻¹ ^ 2 * (bX + bY) / t) = (1 + lam.1 * CP * Y⁻¹ ^ 2) *
              (y⁻¹ ^ 2 * (t * aX + bX / t)) / 2 +
            (1 + lam.1 * CP * Y⁻¹ ^ 2) * (y⁻¹ ^ 2 * (t * aY + bY / t)) / 2 := by
          field_simp; ring
        rw [eq]
        nlinarith

/-- **Quantitative tail law (1).**  For `Y > 1`,
`|J_V(Y)| ≤ [1 + λ (L/(2πY))²] E_U(Y) E_V(Y)`. -/
theorem norm_sourceTestBoundaryCurrent_le_cylinder (F : cuspidalFormPreDomain N) {Y : ℝ}
    (hY : 1 < Y) :
    ‖sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N F) Y‖ ≤
      (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
        (cuspCylinderEnergy N (sourceVector N f) Y * cuspCylinderEnergy N (F : ℍ → DeckSpace N) Y) := by
  set K : ℝ := 1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2
  have hK : 0 ≤ K := by have := lam.2.1; positivity
  obtain ⟨-, hD, hint, -⟩ := sourceTestFlux_tail_law N lam f F hY
  have hU : IntegrableOn (fun y => y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (sourceVector N f)) y +
      deckSliceEnergy (hypGradY (sourceVector N f)) y)) (Ioi Y) :=
    integrableOn_cylinderDensity N (sourceInCuspidalFormPreDomain N lam f) hY.le
  have hV := integrableOn_cylinderDensity N F hY.le
  refine le_mul_sqrt_mul_sqrt_of_forall hK (cuspCylinderEnergySq_nonneg N _ Y)
    (cuspCylinderEnergySq_nonneg N _ Y) fun t ht => ?_
  rw [← norm_neg, ← hint]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hmaj : IntegrableOn (fun y => K / 2 *
      (t * (y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (sourceVector N f)) y +
          deckSliceEnergy (hypGradY (sourceVector N f)) y)) +
        y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y +
          deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y) / t)) (Ioi Y) :=
    ((hU.const_mul t).add (hV.div_const t)).const_mul (K / 2)
  calc ∫ y in Ioi Y, ‖sourceTestGreenDensity N lam f
        (cuspidalFormPreDomain.toFormPreDomain N F) y‖
      ≤ ∫ y in Ioi Y, K / 2 *
          (t * (y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (sourceVector N f)) y +
              deckSliceEnergy (hypGradY (sourceVector N f)) y)) +
            y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y +
              deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y) / t) :=
        setIntegral_mono_on hD.norm hmaj measurableSet_Ioi fun y hy =>
          norm_sourceTestGreenDensity_le_weighted N lam f F hY (le_of_lt hy) ht
    _ = K * (t * cuspCylinderEnergySq N (sourceVector N f) Y +
          cuspCylinderEnergySq N (F : ℍ → DeckSpace N) Y / t) / 2 := by
        rw [integral_const_mul, integral_add (hU.const_mul t) (hV.div_const t), integral_const_mul,
          integral_div]
        simp only [cuspCylinderEnergySq]
        ring

/-- **The cylinder energy tail vanishes.** -/
theorem tendsto_cuspCylinderEnergy (F : cuspidalFormPreDomain N) :
    Tendsto (fun Y => cuspCylinderEnergy N (F : ℍ → DeckSpace N) Y) atTop (𝓝 0) := by
  have hint := integrableOn_cylinderDensity N F (le_refl (1 : ℝ))
  set g := fun y => y⁻¹ ^ 2 * (deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y +
      deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y)
  have hlim := intervalIntegral_tendsto_integral_Ioi (1 : ℝ) hint tendsto_id
  have htail : Tendsto (fun Y => cuspCylinderEnergySq N (F : ℍ → DeckSpace N) Y) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∫ y in Ioi (1 : ℝ), g y)).sub hlim
    rw [sub_self] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    have hdisj : Disjoint (Ioc (1 : ℝ) Y) (Ioi Y) :=
      Set.disjoint_left.mpr fun y h1 h2 => absurd h2 (not_lt.mpr h1.2)
    have hsplit : ∫ y in Ioi (1 : ℝ), g y = (∫ y in Ioc 1 Y, g y) + ∫ y in Ioi Y, g y := by
      rw [← setIntegral_union hdisj measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self)
        (hint.mono_set (Ioi_subset_Ioi hY)), Ioc_union_Ioi_eq_Ioi hY]
    simp only [id, cuspCylinderEnergySq]
    rw [intervalIntegral.integral_of_le hY, hsplit]
    ring
  have := (Real.continuous_sqrt.tendsto 0).comp htail
  rw [Real.sqrt_zero] at this
  exact this

/-- **Uniform tail law (2).**  For `E_V(Y) ≤ 1`, `|J_V(Y)| ≤ [1 + λ(L/2πY)²] E_U(Y)`, and the
right side tends to zero. -/
theorem uniform_sourceTestBoundaryCurrent_tail :
    (∀ (F : cuspidalFormPreDomain N) {Y : ℝ}, 1 < Y →
      cuspCylinderEnergy N (F : ℍ → DeckSpace N) Y ≤ 1 →
        ‖sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N F) Y‖ ≤
          (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
            cuspCylinderEnergy N (sourceVector N f) Y) ∧
    Tendsto (fun Y => (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
      cuspCylinderEnergy N (sourceVector N f) Y) atTop (𝓝 0) := by
  refine ⟨fun F Y hY hE => ?_, ?_⟩
  · refine (norm_sourceTestBoundaryCurrent_le_cylinder N lam f F hY).trans ?_
    have hK : 0 ≤ 1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2 := by
      have := lam.2.1; positivity
    have hEU := Real.sqrt_nonneg (cuspCylinderEnergySq N (sourceVector N f) Y)
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hEU hE) hK
  · have hE : Tendsto (fun Y => cuspCylinderEnergy N (sourceVector N f) Y) atTop (𝓝 0) :=
      tendsto_cuspCylinderEnergy N (sourceInCuspidalFormPreDomain N lam f)
    have hK : Tendsto (fun Y : ℝ => 1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) atTop
        (𝓝 (1 + lam.1 * 0 ^ 2)) := by
      refine tendsto_const_nhds.add (tendsto_const_nhds.mul ((Tendsto.pow ?_ 2)))
      exact tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by positivity))
    simpa using hK.mul hE

/-! ### Continuity through form completion -/

/-- The level slice energy of a horizontal form coordinate is `L` times its centred unit-period
energy. -/
theorem deckSliceEnergy_hypGradX_eq_centered (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) :
    deckSliceEnergy (hypGradX (F : ℍ → DeckSpace N)) y = (N + 1 : ℝ) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
  have hperiodic : Function.Periodic
      (fun x : ℝ => ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2) 1 :=
    fun x => hypGradX_normSq_one_periodic (cuspidalFormPreDomain.toFormPreDomain N F) hy x
  have hshift := hperiodic.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  have hlevel := hypGradX_normSq_interval_level_period
    (cuspidalFormPreDomain.toFormPreDomain N F) hy 0
  simp only [zero_add, cuspidalFormPreDomain.coe_toFormPreDomain] at hlevel hshift
  unfold deckSliceEnergy
  have hL : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by push_cast; ring
  rw [← hL, hlevel, zsmul_eq_mul]
  rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num] at hshift
  rw [hshift]
  push_cast
  ring

theorem deckSliceEnergy_hypGradY_eq_centered (F : cuspidalFormPreDomain N) {y : ℝ} (hy : 0 < y) :
    deckSliceEnergy (hypGradY (F : ℍ → DeckSpace N)) y = (N + 1 : ℝ) *
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2 := by
  have hperiodic : Function.Periodic
      (fun x : ℝ => ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2) 1 :=
    fun x => hypGradY_normSq_one_periodic (cuspidalFormPreDomain.toFormPreDomain N F) hy x
  have hshift := hperiodic.intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  have hlevel := hypGradY_normSq_interval_level_period
    (cuspidalFormPreDomain.toFormPreDomain N F) hy 0
  simp only [zero_add, cuspidalFormPreDomain.coe_toFormPreDomain] at hlevel hshift
  unfold deckSliceEnergy
  have hL : ((N + 1 : ℕ) : ℝ) = (N + 1 : ℝ) := by push_cast; ring
  rw [← hL, hlevel, zsmul_eq_mul]
  rw [show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num] at hshift
  rw [hshift]
  push_cast
  ring

theorem norm_toDeckL2_sq {G : ℍ → DeckSpace N} (hG : MemLp G 2 cellMeasure) :
    ‖toDeckL2 G hG‖ ^ 2 = ∫ z in fd, ‖G z‖ ^ 2 := by
  have h1 := MeasureTheory.L2.inner_def (𝕜 := ℂ) (toDeckL2 G hG) (toDeckL2 G hG)
  rw [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ∀ v : DeckSpace N, (inner ℂ v v : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := fun v => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [h2] at h1
  rw [integral_complex_ofReal] at h1
  have h3 : ∫ z, ‖(toDeckL2 G hG : ℍ → DeckSpace N) z‖ ^ 2 ∂cellMeasure = ∫ z in fd, ‖G z‖ ^ 2 := by
    refine integral_congr_ae (μ := cellMeasure)
      (f := fun z => ‖(toDeckL2 G hG : ℍ → DeckSpace N) z‖ ^ 2) (g := fun z => ‖G z‖ ^ 2) ?_
    filter_upwards [MemLp.coeFn_toLp hG] with z hz
    rw [show (toDeckL2 G hG : ℍ → DeckSpace N) z = G z from hz]
  have h4 : ((‖toDeckL2 G hG‖ ^ 2 : ℝ) : ℂ) = ((∫ z in fd, ‖G z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h3]; push_cast at h1 ⊢; exact h1
  exact_mod_cast h4

theorem tail_le_toDeckL2 {G : ℍ → DeckSpace N} (hcont : Continuous G) (hG : MemLp G 2 cellMeasure)
    {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ y in Ioi Y, y⁻¹ ^ 2 * ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), ‖G (ofComplex (point x y))‖ ^ 2 ≤
      ‖toDeckL2 G hG‖ ^ 2 := by
  rw [← cusp_normSq_tail_eq_iterated G hcont hG hY, norm_toDeckL2_sq]
  have hfd : IntegrableOn (fun z => ‖G z‖ ^ 2) fd volume :=
    (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mp hG
  exact setIntegral_mono_set hfd (Eventually.of_forall fun _ => by positivity)
    (Eventually.of_forall inter_subset_left)

/-- **The cylinder energy is controlled by the completed form norm.** -/
theorem cuspCylinderEnergySq_le_form (F : cuspidalFormPreDomain N) {Y : ℝ} (hY : 1 ≤ Y) :
    cuspCylinderEnergySq N (F : ℍ → DeckSpace N) Y ≤
      (N + 1 : ℝ) * ‖toCuspidalFormDomain N F‖ ^ 2 := by
  have hY0 : 0 < Y := one_pos.trans_le hY
  have hcX := continuous_hypGradX_vec (cuspidalFormPreDomain.c1 F)
  have hcY := continuous_hypGradY_vec (cuspidalFormPreDomain.c1 F)
  have iX := centered_hypGradX_slice_weighted_integrable F hY
  have iY := centered_hypGradY_slice_weighted_integrable F hY
  have hsplit : cuspCylinderEnergySq N (F : ℍ → DeckSpace N) Y = (N + 1 : ℝ) *
      ((∫ y in Ioi Y, y⁻¹ ^ 2 * ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖hypGradX (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2) +
        ∫ y in Ioi Y, y⁻¹ ^ 2 * ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          ‖hypGradY (F : ℍ → DeckSpace N) (ofComplex (point x y))‖ ^ 2) := by
    rw [← integral_add iX iY, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := hY0.trans hy
    rw [deckSliceEnergy_hypGradX_eq_centered N F hy0, deckSliceEnergy_hypGradY_eq_centered N F hy0]
    ring
  have hX := tail_le_toDeckL2 N hcX (cuspidalFormPreDomain.memLp_gradX F) hY
  have hYb := tail_le_toDeckL2 N hcY (cuspidalFormPreDomain.memLp_gradY F) hY
  have hnorm : ‖toDeckL2 _ (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
      ‖toDeckL2 _ (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2 ≤ ‖toCuspidalFormDomain N F‖ ^ 2 := by
    change _ ≤ ‖(cuspidalFormEmbeddingMap N F : FormTriple N)‖ ^ 2
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
    change _ ≤ ‖formCoordinate N 0 (cuspidalFormPreDomain.toFormPreDomain N F)‖ ^ 2 +
      ‖formCoordinate N 1 (cuspidalFormPreDomain.toFormPreDomain N F)‖ ^ 2 +
      ‖formCoordinate N 2 (cuspidalFormPreDomain.toFormPreDomain N F)‖ ^ 2
    have := sq_nonneg ‖formCoordinate N 0 (cuspidalFormPreDomain.toFormPreDomain N F)‖
    change _ ≤ _ + ‖toDeckL2 _ (cuspidalFormPreDomain.memLp_gradX F)‖ ^ 2 +
      ‖toDeckL2 _ (cuspidalFormPreDomain.memLp_gradY F)‖ ^ 2
    linarith
  rw [hsplit]
  have hN : (0 : ℝ) ≤ N + 1 := by positivity
  nlinarith

/-- The boundary pairing as a linear functional on the cusp-zero pre-domain:
`V ↦ conj J_V(Y)`. -/
def upperBoundaryFunctional (Y : ℝ) (hY : 1 < Y) : cuspidalFormPreDomain N →ₗ[ℂ] ℂ where
  toFun V := star (sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N V) Y)
  map_add' V W := by
    have hy0 : 0 < Y := one_pos.trans hY
    have hS := continuous_hypGradY_vec (sourceVector_c1 N lam f)
    rw [sourceTestBoundaryCurrent_eq_of_gt N lam f _ hY, sourceTestBoundaryCurrent_eq_of_gt N lam f _ hY,
      sourceTestBoundaryCurrent_eq_of_gt N lam f _ hY, ← star_add, ← Finset.sum_add_distrib]
    simp only [cuspidalFormPreDomain.coe_toFormPreDomain]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have hV := continuous_component_point (continuous_of_isChartC1 (cuspidalFormPreDomain.c1 V)) q hy0
    have hW := continuous_component_point (continuous_of_isChartC1 (cuspidalFormPreDomain.c1 W)) q hy0
    have hSq := continuous_component_point hS q hy0
    have iV : IntervalIntegrable (fun x : ℝ => (Y : ℂ)⁻¹ *
        hypGradY (sourceVector N f) (ofComplex (point x Y)) q *
          star ((V : ℍ → DeckSpace N) (ofComplex (point x Y)) q)) volume 0 (N + 1 : ℝ) :=
      ((continuous_const.mul hSq).mul hV.star).intervalIntegrable _ _
    have iW : IntervalIntegrable (fun x : ℝ => (Y : ℂ)⁻¹ *
        hypGradY (sourceVector N f) (ofComplex (point x Y)) q *
          star ((W : ℍ → DeckSpace N) (ofComplex (point x Y)) q)) volume 0 (N + 1 : ℝ) :=
      ((continuous_const.mul hSq).mul hW.star).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add iV iW]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [Submodule.coe_add, Pi.add_apply, PiLp.add_apply, star_add]
    ring
  map_smul' c V := by
    rw [sourceTestBoundaryCurrent_eq_of_gt N lam f _ hY, sourceTestBoundaryCurrent_eq_of_gt N lam f _ hY,
      RingHom.id_apply, smul_eq_mul]
    simp only [cuspidalFormPreDomain.coe_toFormPreDomain]
    have hJ : (∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ), (Y : ℂ)⁻¹ *
        hypGradY (sourceVector N f) (ofComplex (point x Y)) q *
          star (((c • V : cuspidalFormPreDomain N) : ℍ → DeckSpace N) (ofComplex (point x Y)) q)) =
        star c * ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ), (Y : ℂ)⁻¹ *
          hypGradY (sourceVector N f) (ofComplex (point x Y)) q *
            star ((V : ℍ → DeckSpace N) (ofComplex (point x Y)) q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [Submodule.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, star_mul']
      ring
    rw [hJ, star_mul', star_star]

theorem upperBoundaryFunctional_apply (Y : ℝ) (hY : 1 < Y) (V : cuspidalFormPreDomain N) :
    upperBoundaryFunctional N lam f Y hY V =
      star (sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N V) Y) := rfl

/-- The boundary functional is bounded by the completed form norm:
`|J_V(Y)| ≤ [1 + λ(L/2πY)²] E_U(Y) √L ‖V‖_form`. -/
theorem norm_upperBoundaryFunctional_le (Y : ℝ) (hY : 1 < Y) (V : cuspidalFormPreDomain N) :
    ‖upperBoundaryFunctional N lam f Y hY V‖ ≤
      (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
        cuspCylinderEnergy N (sourceVector N f) Y * Real.sqrt (N + 1) *
          ‖toCuspidalFormDomain N V‖ := by
  rw [upperBoundaryFunctional_apply, norm_star]
  refine (norm_sourceTestBoundaryCurrent_le_cylinder N lam f V hY).trans ?_
  have hK : 0 ≤ 1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2 := by
    have := lam.2.1; positivity
  have hEU := Real.sqrt_nonneg (cuspCylinderEnergySq N (sourceVector N f) Y)
  have hEV : cuspCylinderEnergy N (V : ℍ → DeckSpace N) Y ≤
      Real.sqrt (N + 1) * ‖toCuspidalFormDomain N V‖ := by
    rw [cuspCylinderEnergy, ← Real.sqrt_sq (norm_nonneg (toCuspidalFormDomain N V)),
      ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (cuspCylinderEnergySq_le_form N V hY.le)
  calc (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
        (cuspCylinderEnergy N (sourceVector N f) Y * cuspCylinderEnergy N (V : ℍ → DeckSpace N) Y)
      ≤ (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
        (cuspCylinderEnergy N (sourceVector N f) Y *
          (Real.sqrt (N + 1) * ‖toCuspidalFormDomain N V‖)) := by gcongr
    _ = _ := by ring

/-- The cusp-zero pre-domain inside its completion, as a linear map. -/
def toCuspidalFormDomainₗ : cuspidalFormPreDomain N →ₗ[ℂ] CuspidalFormDomain N :=
  (cuspidalFormEmbeddingMap N).codRestrict (cuspidalFormDomainClosure N)
    fun V => subset_closure ⟨V, rfl⟩

theorem toCuspidalFormDomainₗ_apply (V : cuspidalFormPreDomain N) :
    toCuspidalFormDomainₗ N V = toCuspidalFormDomain N V := rfl

theorem dense_range_toCuspidalFormDomainₗ :
    Dense (LinearMap.range (toCuspidalFormDomainₗ N) : Set (CuspidalFormDomain N)) := by
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro x
  have hx : (x : FormTriple N) ∈ closure (LinearMap.range (cuspidalFormEmbeddingMap N) :
      Set (FormTriple N)) := by
    have h := x.2
    change (x : FormTriple N) ∈ ((LinearMap.range (cuspidalFormEmbeddingMap N)).topologicalClosure :
      Set (FormTriple N)) at h
    rwa [Submodule.topologicalClosure_coe] at h
  refine closure_mono ?_ hx
  rintro _ ⟨V, rfl⟩
  exact ⟨toCuspidalFormDomainₗ N V, ⟨V, rfl⟩, rfl⟩

/-- **Continuous extension through form completion.**  For every `Y > 1` the upper boundary
functional `V ↦ conj J_V(Y)` extends to a continuous linear functional on the completed cusp-zero
form domain, with norm at most `[1 + λ(L/2πY)²] E_U(Y) √L`. -/
theorem exists_upperBoundaryFunctional_extension (Y : ℝ) (hY : 1 < Y) :
    ∃ Λ : CuspidalFormDomain N →L[ℂ] ℂ,
      (∀ V : cuspidalFormPreDomain N,
        Λ (toCuspidalFormDomain N V) =
          star (sourceTestBoundaryCurrent N lam f (cuspidalFormPreDomain.toFormPreDomain N V) Y)) ∧
      ‖Λ‖ ≤ (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
        cuspCylinderEnergy N (sourceVector N f) Y * Real.sqrt (N + 1) := by
  have hC : 0 ≤ (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
      cuspCylinderEnergy N (sourceVector N f) Y * Real.sqrt (N + 1) := by
    have := lam.2.1
    have := Real.sqrt_nonneg (cuspCylinderEnergySq N (sourceVector N f) Y)
    simp only [cuspCylinderEnergy]
    positivity
  have hbound : ∀ V, ‖upperBoundaryFunctional N lam f Y hY V‖ ≤
      ((1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
        cuspCylinderEnergy N (sourceVector N f) Y * Real.sqrt (N + 1)) *
          ‖toCuspidalFormDomainₗ N V‖ := fun V =>
    norm_upperBoundaryFunctional_le N lam f Y hY V
  have hker : LinearMap.ker (toCuspidalFormDomainₗ N) ≤
      LinearMap.ker (upperBoundaryFunctional N lam f Y hY) := by
    intro V hV
    rw [LinearMap.mem_ker] at hV ⊢
    have := hbound V
    rw [hV, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.mp this
  let g : LinearMap.range (toCuspidalFormDomainₗ N) →ₗ[ℂ] ℂ :=
    ((LinearMap.ker (toCuspidalFormDomainₗ N)).liftQ (upperBoundaryFunctional N lam f Y hY)
      hker).comp (toCuspidalFormDomainₗ N).quotKerEquivRange.symm.toLinearMap
  have hg : ∀ V : cuspidalFormPreDomain N,
      g ⟨toCuspidalFormDomainₗ N V, ⟨V, rfl⟩⟩ = upperBoundaryFunctional N lam f Y hY V := by
    intro V
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hgb : ∀ r : LinearMap.range (toCuspidalFormDomainₗ N),
      ‖g r‖ ≤ ((1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
        cuspCylinderEnergy N (sourceVector N f) Y * Real.sqrt (N + 1)) * ‖r‖ := by
    rintro ⟨_, ⟨V, rfl⟩⟩
    rw [hg]
    exact hbound V
  let gC := g.mkContinuous _ hgb
  have hdense : DenseRange ((LinearMap.range (toCuspidalFormDomainₗ N)).subtypeL) := by
    rw [DenseRange, Submodule.coe_subtypeL, Submodule.coe_subtype, Subtype.range_coe]
    exact dense_range_toCuspidalFormDomainₗ N
  have hunif : IsUniformInducing ((LinearMap.range (toCuspidalFormDomainₗ N)).subtypeL) :=
    (isometry_subtype_coe (s := ((LinearMap.range (toCuspidalFormDomainₗ N)) :
      Set (CuspidalFormDomain N)))).isUniformInducing
  refine ⟨gC.extend (LinearMap.range (toCuspidalFormDomainₗ N)).subtypeL, fun V => ?_, ?_⟩
  · have h := ContinuousLinearMap.extend_eq gC hdense hunif ⟨toCuspidalFormDomainₗ N V, ⟨V, rfl⟩⟩
    simp only [Submodule.subtypeL_apply] at h
    rw [← toCuspidalFormDomainₗ_apply, h]
    change g ⟨toCuspidalFormDomainₗ N V, ⟨V, rfl⟩⟩ = _
    rw [hg]
    rfl
  · refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
    refine hdense.induction_on x (isClosed_le ((ContinuousLinearMap.continuous _).norm)
      (continuous_const.mul continuous_norm)) fun r => ?_
    rw [ContinuousLinearMap.extend_eq gC hdense hunif r]
    exact hgb r

/-- **The extended boundary functionals tend to zero in norm.** -/
theorem tendsto_upperBoundaryFunctional_norm_bound :
    Tendsto (fun Y => (1 + lam.1 * ((N + 1 : ℝ) / (2 * Real.pi * Y)) ^ 2) *
      cuspCylinderEnergy N (sourceVector N f) Y * Real.sqrt (N + 1)) atTop (𝓝 0) := by
  have h := (uniform_sourceTestBoundaryCurrent_tail N lam f).2
  simpa using h.mul_const (Real.sqrt (N + 1))

end Tail

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
