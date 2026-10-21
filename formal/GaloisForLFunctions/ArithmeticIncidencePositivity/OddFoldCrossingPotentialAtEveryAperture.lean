import GaloisForLFunctions.ArithmeticIncidencePositivity.FoldedSurplusGroundStatePotential

/-!
# The archimedean fold of an odd test at every aperture

For an odd test `F` and an even gauge `0 ≤ P ≤ 1` vanishing outside `(−B, B)`, with `P = 1` on the
support of `F`, the archimedean jump energy `J_P(F) = ∫_{t>0} ω(t) ∫ P(x)P(x+t)(F(x) − F(x+t))² dx dt`
is exactly

    J_P(F) = 2 S_P(F) + 4 ∫_{x>0} F(x)² Π_P(x) dx,      Π_P(x) = ∫_{t>x} ω(t) P(t − x) dt.

Here `S_P(F)` is the surplus energy of the fold (the excess `ω(|x − y|) − ω(x + y)` of every same-side
pair over its crossing partner) and `Π_P` is the **crossing potential** of the gauge: the crossing
pair `(−x, t − x)` of the odd test carries `(F(x) + F(t − x))² = 2F(x)² + 2F(t − x)² − (F(x) − F(t − x))²`;
its killing part `2F(x)² + 2F(t − x)²` integrates to `4F(x)² Π_P(x)`, and its difference part is
absorbed by the same-side pair at the same distance, which keeps the surplus.

The windows of the programme used the inequality `J_P(F) ≥ 4 ∫ F²(Ω(x) − Ω(x + r)) + 2 S_P(F)` and only
apertures `2B ≤ 1`, where `ω(t) ≤ 3/(2t)` bounds every integrand. The bound `ω(t) t² ≤ 3/2 + 4B²` on
`(0, 2B]` (`archLevyDensity_mul_sq_le`) replaces it, so the identities hold at every aperture, and
the crossing potential is kept exact: when `P = 1` on `[−r, r]` it is the killing `Ω(x) − Ω(x + r)`
of the plateau plus the collar potential `∫_{t > x + r} ω(t) P(t − x) dt` of the gauge beyond `r`
(`crossingPotential_eq_killing_add_collar`), between `0` and `Ω(x + r) − Ω(x + B)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The uniform bound `ω(t) t² ≤ 3/2 + 4B²` -/

/-- `ω(t) t² ≤ 3/2 + 4B²` for `0 < t ≤ 2B`: below `1` from `ω(t) ≤ 3/(2t)`, above `1` from
`ω(t) ≤ (3/2) e^{−t/2} ≤ 1`. -/
theorem archLevyDensity_mul_sq_le {t B : ℝ} (ht : 0 < t) (htB : t ≤ 2 * B) :
    archLevyDensity t * t ^ 2 ≤ 3 / 2 + 4 * B ^ 2 := by
  have hB2 : 0 ≤ 4 * B ^ 2 := by positivity
  by_cases h1 : t ≤ 1
  · have hω := archLevyDensity_le_of_le_one ht h1
    calc archLevyDensity t * t ^ 2 ≤ 3 / 2 / t * t ^ 2 :=
          mul_le_mul_of_nonneg_right hω (sq_nonneg t)
      _ = 3 / 2 * t := by field_simp
      _ ≤ 3 / 2 + 4 * B ^ 2 := by nlinarith
  · have ht1 : 1 ≤ t := by linarith [not_le.mp h1]
    have hω := archLevyDensity_le_of_one_le ht1
    -- `e^{−t/2} ≤ e^{−1/2} ≤ 2/3`
    have hexp : Real.exp (-t / 2) ≤ 2 / 3 := by
      have h := Real.add_one_le_exp (1 / 2 : ℝ)
      have hmono : Real.exp (-t / 2) ≤ Real.exp (-(1 / 2)) := Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_neg] at hmono
      have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      calc Real.exp (-t / 2) ≤ (Real.exp (1 / 2 : ℝ))⁻¹ := hmono
        _ ≤ 2 / 3 := by
            rw [inv_le_comm₀ hpos (by norm_num), show ((2 : ℝ) / 3)⁻¹ = 3 / 2 by norm_num]
            linarith
    have hω1 : archLevyDensity t ≤ 1 := by linarith
    have ht2 : t ^ 2 ≤ 4 * B ^ 2 := by nlinarith
    calc archLevyDensity t * t ^ 2 ≤ 1 * t ^ 2 :=
          mul_le_mul_of_nonneg_right hω1 (sq_nonneg t)
      _ ≤ 3 / 2 + 4 * B ^ 2 := by linarith

section Fold

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B)

/-! ### Integrability of the folded integrands at every aperture -/

include hPc hFc hP0 hP1 hFL hPB hB0 in
/-- `ω(t) J_t(x)` is integrable on the quadrant: bounded by `K²(3/2 + 4B²)` and supported in
`t ≤ 2B`, `x ≤ B`. -/
theorem integrable_archLevy_mul_signedShiftJump_prod_everyAperture :
    Integrable (Function.uncurry fun t x => archLevyDensity t * signedShiftJump P F t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : Measurable (Function.uncurry fun t x => archLevyDensity t * signedShiftJump P F t x) := by
    refine (measurable_archLevyDensity.comp measurable_fst).mul ?_
    have : Continuous (Function.uncurry fun t x => signedShiftJump P F t x) := by
      unfold signedShiftJump; fun_prop
    exact this.measurable
  refine integrable_quadrant_of_bound hmeas (C := K ^ 2 * (3 / 2 + 4 * B ^ 2)) (T₁ := 2 * B) (T₂ := B)
    (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · simp only [Function.uncurry_apply_pair]
    by_cases hts : t ≤ 2 * B
    · have hω := archLevyDensity_mul_sq_le ht hts
      have hJ := signedShiftJump_le hP0 hP1 hFL t x
      have hJ0 := signedShiftJump_nonneg' hP0 (F := F) t x
      have hω0 := (archLevyDensity_pos ht).le
      rw [abs_of_nonneg (mul_nonneg hω0 hJ0)]
      calc archLevyDensity t * signedShiftJump P F t x ≤ archLevyDensity t * (K ^ 2 * t ^ 2) :=
            mul_le_mul_of_nonneg_left hJ hω0
        _ = K ^ 2 * (archLevyDensity t * t ^ 2) := by ring
        _ ≤ K ^ 2 * (3 / 2 + 4 * B ^ 2) := mul_le_mul_of_nonneg_left hω (sq_nonneg K)
    · rw [signedShiftJump_eq_zero_of_pos hPB hB0 hx (Or.inl (not_le.mp hts)), mul_zero, abs_zero]
      positivity
  · simp only [Function.uncurry_apply_pair]
    rw [signedShiftJump_eq_zero_of_pos hPB hB0 hx h, mul_zero]

include hPc hFc hP0 hP1 hFL hPB hB0 in
/-- The folded crossing integrand is integrable on the quadrant at every aperture. -/
theorem integrable_foldedCrossingIntegrand_everyAperture :
    Integrable (foldedCrossingIntegrand P F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hset : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1 / 2} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.div_const 2))
  have hc : Continuous fun q : ℝ × ℝ => crossingDiffJump P F q.1 q.2 := by
    unfold crossingDiffJump; fun_prop
  have hmeas : Measurable (foldedCrossingIntegrand P F) :=
    (measurable_archLevyDensity.comp measurable_fst).mul (hc.measurable.indicator hset)
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (by
    have := hFL 1 0; have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h1, mul_one] at this; exact this)
  refine integrable_quadrant_of_bound hmeas (C := K ^ 2 * (3 / 2 + 4 * B ^ 2)) (T₁ := 2 * B) (T₂ := B)
    (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · rw [foldedCrossingIntegrand_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) (t / 2)
    · rw [Set.indicator_of_mem hxt]
      have hD0 := crossingDiffJump_nonneg hP0 (F := F) t x
      by_cases hts : t ≤ 2 * B
      · have hω := archLevyDensity_mul_sq_le ht hts
        have hD : crossingDiffJump P F t x ≤ K ^ 2 * t ^ 2 := by
          unfold crossingDiffJump
          have h := hFL x (t - x)
          have habs : |x - (t - x)| ≤ t := by
            rw [abs_le]; constructor <;> linarith [hxt.1, hxt.2]
          have h2 : |F x - F (t - x)| ≤ K * t := h.trans (mul_le_mul_of_nonneg_left habs hK)
          have hsq : (F x - F (t - x)) ^ 2 ≤ K ^ 2 * t ^ 2 := by
            calc (F x - F (t - x)) ^ 2 = |F x - F (t - x)| ^ 2 := (sq_abs _).symm
              _ ≤ (K * t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
              _ = K ^ 2 * t ^ 2 := by ring
          calc P x * P (t - x) * (F x - F (t - x)) ^ 2 ≤ 1 * (K ^ 2 * t ^ 2) :=
                mul_le_mul (mul_le_one₀ (hP1 _) (hP0 _) (hP1 _)) hsq (sq_nonneg _) zero_le_one
            _ = _ := one_mul _
        have hω0 := (archLevyDensity_pos ht).le
        rw [abs_of_nonneg (mul_nonneg hω0 hD0)]
        calc archLevyDensity t * crossingDiffJump P F t x ≤ archLevyDensity t * (K ^ 2 * t ^ 2) :=
              mul_le_mul_of_nonneg_left hD hω0
          _ = K ^ 2 * (archLevyDensity t * t ^ 2) := by ring
          _ ≤ K ^ 2 * (3 / 2 + 4 * B ^ 2) := mul_le_mul_of_nonneg_left hω (sq_nonneg K)
      · have hP : P (t - x) = 0 := hPB _ (by
          rw [abs_of_pos (by linarith [hxt.2])]; linarith [hxt.2, not_le.mp hts])
        unfold crossingDiffJump
        rw [hP, mul_zero, zero_mul, mul_zero, abs_zero]
        positivity
    · rw [Set.indicator_of_notMem hxt, mul_zero, abs_zero]
      positivity
  · rw [foldedCrossingIntegrand_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) (t / 2)
    · rw [Set.indicator_of_mem hxt]
      unfold crossingDiffJump
      rcases h with h | h
      · rw [hPB (t - x) (by rw [abs_of_pos (by linarith [hxt.2])]; linarith [hxt.2]),
          mul_zero, zero_mul, mul_zero]
      · rw [hPB x (by rw [abs_of_pos hx]; linarith), zero_mul, zero_mul, mul_zero]
    · rw [Set.indicator_of_notMem hxt, mul_zero]

include hPc hFc hP0 hP1 hFL hPB hB0 in
/-- `D_arch = 2 ∫_{x>0} ∫_{s>0} ω(s + 2x) J_s(x) ds dx` at every aperture. -/
theorem archCrossingDiffEnergy_eq_everyAperture :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x) =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) *
        signedShiftJump P F s x := by
  have hID := integrable_foldedCrossingIntegrand_everyAperture hPc hFc hP0 hP1 hPB hFL hB0
  have h1 : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) *
      signedShiftJump P F s x) =
      ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      (integral_foldedCrossingIntegrand_eq (mem_Ioi.mp hx)).symm
  rw [h1, ← integral_integral_swap (f := fun t x => foldedCrossingIntegrand P F (t, x)) hID,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [integral_crossingDiffJump_eq_two_mul_half hPc hFc (mem_Ioi.mp ht)]
  have : (∫ x in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x)) =
      archLevyDensity t * ∫ x in Ioo (0 : ℝ) (t / 2), crossingDiffJump P F t x := by
    simp_rw [foldedCrossingIntegrand_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [this]
  ring

include hPc hFc hP0 hP1 hFL hPB hB0 in
/-- `S_arch = ∫_{x>0} ∫_{s>0} ω(s) J_s(x) ds dx` at every aperture. -/
theorem archSameEnergy_eq_everyAperture :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity s * signedShiftJump P F s x := by
  have hIS := integrable_archLevy_mul_signedShiftJump_prod_everyAperture hPc hFc hP0 hP1 hPB hFL hB0
  rw [← integral_integral_swap (f := fun t x => archLevyDensity t * signedShiftJump P F t x) hIS]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [integral_const_mul]

include hPc hFc hP0 hP1 hFL hPB hB0 in
/-- **The exact surplus of the fold at every aperture.** `2 S_arch − D_arch = 2 S_P(F)`. -/
theorem two_mul_archSame_sub_archCrossingDiff_eq_everyAperture :
    2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) -
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x) =
      2 * surplusEnergy P F := by
  have hIS := integrable_archLevy_mul_signedShiftJump_prod_everyAperture hPc hFc hP0 hP1 hPB hFL hB0
  have hID := integrable_foldedCrossingIntegrand_everyAperture hPc hFc hP0 hP1 hPB hFL hB0
  rw [archCrossingDiffEnergy_eq_everyAperture hPc hFc hP0 hP1 hPB hFL hB0,
    archSameEnergy_eq_everyAperture hPc hFc hP0 hP1 hPB hFL hB0]
  have hO1 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), archLevyDensity s * signedShiftJump P F s x)
      (volume.restrict (Ioi 0)) := hIS.integral_prod_right
  have hO2 : Integrable (fun x => ∫ s in Ioi (0 : ℝ),
      archLevyDensity (s + 2 * x) * signedShiftJump P F s x) (volume.restrict (Ioi 0)) := by
    refine hID.integral_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact integral_foldedCrossingIntegrand_eq (mem_Ioi.mp hx)
  unfold surplusEnergy
  rw [← mul_sub, ← integral_sub hO1 hO2]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hIS.prod_left_ae, ae_restrict_mem measurableSet_Ioi] with x hx hx0
  have hx0' : 0 < x := hx0
  have hi1 : Integrable (fun s => archLevyDensity s * signedShiftJump P F s x)
      (volume.restrict (Ioi 0)) := hx
  have hi2 : Integrable (fun s => archLevyDensity (s + 2 * x) * signedShiftJump P F s x)
      (volume.restrict (Ioi 0)) := by
    refine hi1.mono' ((measurable_archLevyDensity.comp (measurable_id.add_const _)).mul
      (continuous_signedShiftJump_left hPc hFc x).measurable).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
    have hω := strictAntiOn_archLevyDensity.antitoneOn hs0 (show (0 : ℝ) < s + 2 * x by linarith)
      (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (archLevyDensity_pos (by linarith)).le hJ)]
    exact mul_le_mul_of_nonneg_right hω hJ
  rw [← integral_sub hi1 hi2]
  exact integral_congr_ae (Eventually.of_forall fun s => by simp only; ring)

/-! ### The crossing potential of a gauge -/

/-- The crossing potential of a gauge at `x`: `Π_P(x) = ∫_{t>x} ω(t) P(t − x) dt`, the archimedean
rate of all crossing pairs `(−x, t − x)` of the point `x`, weighted by the gauge at the partner. -/
def crossingPotential (P : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Ioi x, archLevyDensity t * P (t - x)

/-- The crossing killing integrand `ω(t) 1_{0<x<t} 4 P(x) P(t − x) F(x)²` on the quadrant. -/
def crossingKillingIntegrand (P F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  archLevyDensity p.1 * ({q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1}.indicator
    (fun q => 4 * P q.2 * P (q.1 - q.2) * F q.2 ^ 2) p)

omit hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 in
theorem crossingKillingIntegrand_apply (t x : ℝ) :
    crossingKillingIntegrand P F (t, x) = archLevyDensity t *
      (Ioo (0 : ℝ) t).indicator (fun y => 4 * P y * P (t - y) * F y ^ 2) x := by
  unfold crossingKillingIntegrand
  simp only [Set.indicator_apply, mem_setOf_eq, mem_Ioo]

include hPc hFc hFo hP0 hP1 hPB hFB hFL hB0 in
/-- The crossing killing integrand is integrable on the quadrant: `F(x)² ≤ K² x² ≤ K² t²` on
`x < t`, and it vanishes for `t > 2B` or `x > B`. -/
theorem integrable_crossingKillingIntegrand :
    Integrable (crossingKillingIntegrand P F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hset : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hc : Continuous fun q : ℝ × ℝ => 4 * P q.2 * P (q.1 - q.2) * F q.2 ^ 2 := by fun_prop
  have hmeas : Measurable (crossingKillingIntegrand P F) :=
    (measurable_archLevyDensity.comp measurable_fst).mul (hc.measurable.indicator hset)
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (by
    have := hFL 1 0; have h1 : |(1 : ℝ) - 0| = 1 := by norm_num
    rw [h1, mul_one] at this; exact this)
  -- the pointwise value vanishes unless `x < B` and `t − x < B`
  have hvan : ∀ t x, 0 < t → 0 < x → (2 * B < t ∨ B < x) →
      4 * P x * P (t - x) * F x ^ 2 = 0 := by
    intro t x ht hx h
    by_cases hxB : B ≤ x
    · rw [hFB x (by rw [abs_of_pos hx]; exact hxB)]; ring
    · have h2 : 2 * B < t := by
        rcases h with h | h
        · exact h
        · exact absurd h.le hxB
      rw [hPB (t - x) (by rw [abs_of_pos (by linarith)]; linarith)]; ring
  refine integrable_quadrant_of_bound hmeas (C := 4 * K ^ 2 * (3 / 2 + 4 * B ^ 2)) (T₁ := 2 * B)
    (T₂ := B) (fun t x ht hx => ?_) (fun t x ht hx h => ?_)
  · rw [crossingKillingIntegrand_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) t
    · rw [Set.indicator_of_mem hxt]
      have hD0 : 0 ≤ 4 * P x * P (t - x) * F x ^ 2 := by
        have := hP0 x; have := hP0 (t - x); positivity
      have hω0 := (archLevyDensity_pos ht).le
      rw [abs_of_nonneg (mul_nonneg hω0 hD0)]
      by_cases hts : t ≤ 2 * B
      · have hω := archLevyDensity_mul_sq_le ht hts
        have hF := abs_le_mul_abs_of_odd hFo hFL x
        rw [abs_of_pos hx] at hF
        have hF2 : F x ^ 2 ≤ K ^ 2 * t ^ 2 := by
          have h1 : F x ^ 2 ≤ (K * x) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hF 2
          have h2 : (K * x) ^ 2 ≤ K ^ 2 * t ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hxt.2.le 2) (sq_nonneg K)
          linarith
        have hD : 4 * P x * P (t - x) * F x ^ 2 ≤ 4 * (K ^ 2 * t ^ 2) := by
          have hPP : P x * P (t - x) ≤ 1 := mul_le_one₀ (hP1 _) (hP0 _) (hP1 _)
          have hPP0 : 0 ≤ P x * P (t - x) := mul_nonneg (hP0 _) (hP0 _)
          calc 4 * P x * P (t - x) * F x ^ 2 = 4 * ((P x * P (t - x)) * F x ^ 2) := by ring
            _ ≤ 4 * (1 * (K ^ 2 * t ^ 2)) := by
                refine mul_le_mul_of_nonneg_left (mul_le_mul hPP hF2 (sq_nonneg _) zero_le_one)
                  (by norm_num)
            _ = 4 * (K ^ 2 * t ^ 2) := by ring
        calc archLevyDensity t * (4 * P x * P (t - x) * F x ^ 2) ≤
              archLevyDensity t * (4 * (K ^ 2 * t ^ 2)) := mul_le_mul_of_nonneg_left hD hω0
          _ = 4 * K ^ 2 * (archLevyDensity t * t ^ 2) := by ring
          _ ≤ 4 * K ^ 2 * (3 / 2 + 4 * B ^ 2) :=
              mul_le_mul_of_nonneg_left hω (by positivity)
      · rw [hvan t x ht hx (Or.inl (not_le.mp hts)), mul_zero]
        positivity
    · rw [Set.indicator_of_notMem hxt, mul_zero, abs_zero]
      positivity
  · rw [crossingKillingIntegrand_apply]
    by_cases hxt : x ∈ Ioo (0 : ℝ) t
    · rw [Set.indicator_of_mem hxt, hvan t x ht hx h, mul_zero]
    · rw [Set.indicator_of_notMem hxt, mul_zero]

omit hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 in
/-- At fixed `t`, the crossing killing integrand integrates in `x` to the crossing killing profile
`ω(t) ∫_{0<x<t} 4P(x)P(t − x)F(x)²`. -/
theorem integral_crossingKillingIntegrand_left (t : ℝ) :
    (∫ x in Ioi (0 : ℝ), crossingKillingIntegrand P F (t, x)) =
      archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2 := by
  simp_rw [crossingKillingIntegrand_apply]
  rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
    Set.inter_eq_right.mpr Ioo_subset_Ioi_self]

omit hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 in
/-- At fixed `x > 0` with `P(x) = 1` wherever `F(x) ≠ 0`, the crossing killing integrand integrates
in `t` to `4F(x)² Π_P(x)`. -/
theorem integral_crossingKillingIntegrand_right (hFM : ∀ x, F x ≠ 0 → P x = 1) {x : ℝ}
    (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), crossingKillingIntegrand P F (t, x)) =
      4 * F x ^ 2 * crossingPotential P x := by
  by_cases hF0 : F x = 0
  · have : (fun t => crossingKillingIntegrand P F (t, x)) = fun _ => 0 := by
      funext t
      rw [crossingKillingIntegrand_apply]
      by_cases h : x ∈ Ioo (0 : ℝ) t
      · rw [Set.indicator_of_mem h, hF0]; ring
      · rw [Set.indicator_of_notMem h, mul_zero]
    rw [this, hF0]
    simp
  · have hPx := hFM x hF0
    have e : (fun t => crossingKillingIntegrand P F (t, x)) =
        (Ioi x).indicator fun t => 4 * F x ^ 2 * (archLevyDensity t * P (t - x)) := by
      funext t
      rw [crossingKillingIntegrand_apply]
      by_cases h : x < t
      · rw [Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) t from ⟨hx, h⟩),
          Set.indicator_of_mem (show t ∈ Ioi x from h), hPx]
        ring
      · rw [Set.indicator_of_notMem (show x ∉ Ioo (0 : ℝ) t from fun hh => h hh.2),
          Set.indicator_of_notMem (show t ∉ Ioi x from fun hh => h hh), mul_zero]
    rw [e, setIntegral_indicator measurableSet_Ioi,
      show Ioi (0 : ℝ) ∩ Ioi x = Ioi x from Set.inter_eq_right.mpr (Ioi_subset_Ioi hx.le),
      integral_const_mul]
    rfl

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 in
/-- **The archimedean fold at every aperture, exactly.** For an odd test `F` and an even gauge
`0 ≤ P ≤ 1` vanishing outside `(−B, B)`, equal to `1` on the support of `F`:
`J_P(F) = 2 S_P(F) + 4 ∫_{x>0} F(x)² Π_P(x) dx`, and the crossing potential density is integrable. -/
theorem archJump_eq_two_mul_surplus_add_crossingPotential (hFM : ∀ x, F x ≠ 0 → P x = 1) :
    IntegrableOn (fun x => F x ^ 2 * crossingPotential P x) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) =
        2 * surplusEnergy P F + 4 * ∫ x in Ioi (0 : ℝ), F x ^ 2 * crossingPotential P x := by
  have hIS := integrable_archLevy_mul_signedShiftJump_prod_everyAperture hPc hFc hP0 hP1 hPB hFL hB0
  have hID := integrable_foldedCrossingIntegrand_everyAperture hPc hFc hP0 hP1 hPB hFL hB0
  have hCK := integrable_crossingKillingIntegrand hPc hFc hFo hP0 hP1 hPB hFB hFL hB0
  -- the three profiles in `t`
  have hS : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x)
      (Ioi 0) :=
    hIS.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [Function.uncurry_apply_pair]
      rw [integral_const_mul])
  have hD : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x)
      (Ioi 0) := by
    have h2 : IntegrableOn (fun t => 2 * ∫ x in Ioi (0 : ℝ), foldedCrossingIntegrand P F (t, x))
        (Ioi 0) := hID.integral_prod_left.const_mul 2
    refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only
    simp_rw [foldedCrossingIntegrand_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self, integral_crossingDiffJump_eq_two_mul_half hPc hFc ht0]
    ring
  have hK : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
      4 * P x * P (t - x) * F x ^ 2) (Ioi 0) :=
    hCK.integral_prod_left.congr (Eventually.of_forall fun t =>
      integral_crossingKillingIntegrand_left t)
  -- the per-shift split
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t =
      2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) +
        archLevyDensity t * (∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2) -
        archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x := fun t ht => by
    unfold gaugeJumpProfile
    rw [integral_signedShiftJump_eq_split hPc hFc hPe hFo hPB ht, integral_crossingSum_eq hPc hFc]
    ring
  have hA : IntegrableOn (fun t => 2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ),
      signedShiftJump P F t x) + archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
        4 * P x * P (t - x) * F x ^ 2) (Ioi 0) := (hS.const_mul 2).add hK
  have hS2 : IntegrableOn (fun t => 2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ),
      signedShiftJump P F t x)) (Ioi 0) := hS.const_mul 2
  have hJ : (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) =
      2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) +
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
          4 * P x * P (t - x) * F x ^ 2) -
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x := by
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hA hD,
      integral_add hS2 hK, integral_const_mul]
  have hSur := two_mul_archSame_sub_archCrossingDiff_eq_everyAperture hPc hFc hP0 hP1 hPB hFL hB0
  -- the crossing killing profile, swapped
  have hswap : (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
      4 * P x * P (t - x) * F x ^ 2) =
      4 * ∫ x in Ioi (0 : ℝ), F x ^ 2 * crossingPotential P x := by
    have e1 : (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
        4 * P x * P (t - x) * F x ^ 2) =
        ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), crossingKillingIntegrand P F (t, x) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ =>
        (integral_crossingKillingIntegrand_left t).symm
    rw [e1, integral_integral_swap (f := fun t x => crossingKillingIntegrand P F (t, x)) hCK,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [integral_crossingKillingIntegrand_right hFM (mem_Ioi.mp hx)]
    ring
  refine ⟨?_, by linarith⟩
  have h : IntegrableOn (fun x => 1 / 4 * ∫ t in Ioi (0 : ℝ), crossingKillingIntegrand P F (t, x))
      (Ioi 0) := (hCK.integral_prod_right).const_mul (1 / 4)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only
  rw [integral_crossingKillingIntegrand_right hFM (mem_Ioi.mp hx)]
  ring

end Fold

/-! ### The crossing potential of a plateau: killing plus collar -/

/-- The collar crossing potential beyond `r`: `∫_{t > x + r} ω(t) P(t − x) dt`, the crossing pairs
`(−x, t − x)` whose partner lies beyond the plateau `[−r, r]`. -/
def collarCrossingPotential (P : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ∫ t in Ioi (x + r), archLevyDensity t * P (t - x)

/-- `ω(t) P(t − x)` is integrable on `(x, ∞)` for `x > 0` and a continuous gauge vanishing outside
`(−B, B)`. -/
theorem integrableOn_archLevy_mul_gauge_shift {P : ℝ → ℝ} {B : ℝ} (hPc : Continuous P)
    (hPB : ∀ y, B ≤ |y| → P y = 0) (hB0 : 0 < B) {x c : ℝ} (hx : 0 < x) (hxc : x ≤ c) :
    IntegrableOn (fun t => archLevyDensity t * P (t - x)) (Ioi c) := by
  refine IntegrableOn.mono_set ?_ (Ioi_subset_Ioi hxc)
  have hunion : Ioi x = Ioc x (x + B) ∪ Ioi (x + B) := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hcont : ContinuousOn (fun t => archLevyDensity t * P (t - x)) (Icc x (x + B)) := by
    refine (continuousOn_archLevyDensity.mono fun t ht => ?_).mul
      (hPc.comp (continuous_id.sub continuous_const)).continuousOn
    exact lt_of_lt_of_le hx ht.1
  rw [hunion]
  refine IntegrableOn.union (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ?_
  refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have hP : P (t - x) = 0 :=
    hPB (t - x) (by rw [abs_of_pos (by linarith [mem_Ioi.mp ht])]; linarith [mem_Ioi.mp ht])
  simp [hP]

/-- **Killing plus collar.** For `x > 0`, `r > 0`, and a continuous gauge with `P = 1` on
`[−r, r]` and `P = 0` outside `(−B, B)`:
`Π_P(x) = (Ω(x) − Ω(x + r)) + ∫_{t > x + r} ω(t) P(t − x) dt`. -/
theorem crossingPotential_eq_killing_add_collar {P : ℝ → ℝ} {B r : ℝ} (hPc : Continuous P)
    (hPB : ∀ y, B ≤ |y| → P y = 0) (hB0 : 0 < B) (hPr : ∀ y, |y| ≤ r → P y = 1) (hr0 : 0 < r)
    {x : ℝ} (hx : 0 < x) :
    crossingPotential P x =
      (archLevyAntideriv x - archLevyAntideriv (x + r)) + collarCrossingPotential P r x := by
  unfold crossingPotential collarCrossingPotential
  have hsplit : Ioi x = Ioc x (x + r) ∪ Ioi (x + r) := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hI := integrableOn_archLevy_mul_gauge_shift hPc hPB hB0 hx le_rfl
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi (by linarith)))]
  congr 1
  have e : (∫ t in Ioc x (x + r), archLevyDensity t * P (t - x)) =
      ∫ t in Ioc x (x + r), archLevyDensity t :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      rw [hPr (t - x) (by rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.2]), mul_one]
  rw [e, ← intervalIntegral.integral_of_le (by linarith), integral_archLevyDensity_Icc hx (by linarith)]

/-- The collar crossing potential is nonnegative and at most `Ω(x + r) − Ω(x + B)`. -/
theorem collarCrossingPotential_bounds {P : ℝ → ℝ} {B r : ℝ} (hPc : Continuous P)
    (hP0 : ∀ y, 0 ≤ P y) (hP1 : ∀ y, P y ≤ 1) (hPB : ∀ y, B ≤ |y| → P y = 0) (hB0 : 0 < B)
    (hr0 : 0 < r) (hrB : r ≤ B) {x : ℝ} (hx : 0 < x) :
    0 ≤ collarCrossingPotential P r x ∧
      collarCrossingPotential P r x ≤ archLevyAntideriv (x + r) - archLevyAntideriv (x + B) := by
  unfold collarCrossingPotential
  have hI := integrableOn_archLevy_mul_gauge_shift hPc hPB hB0 hx (by linarith : x ≤ x + r)
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (by linarith [mem_Ioi.mp ht])).le (hP0 _)
  · have hsplit : Ioi (x + r) = Ioc (x + r) (x + B) ∪ Ioi (x + B) :=
      (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi (by linarith)))]
    have hzero : (∫ t in Ioi (x + B), archLevyDensity t * P (t - x)) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      rw [hPB (t - x) (by rw [abs_of_pos (by linarith [mem_Ioi.mp ht])]; linarith [mem_Ioi.mp ht]),
        mul_zero]
    rw [hzero, add_zero]
    have hcont : ContinuousOn archLevyDensity (Icc (x + r) (x + B)) :=
      continuousOn_archLevyDensity.mono fun t ht => by
        show 0 < t; linarith [ht.1]
    calc (∫ t in Ioc (x + r) (x + B), archLevyDensity t * P (t - x)) ≤
          ∫ t in Ioc (x + r) (x + B), archLevyDensity t := by
          refine setIntegral_mono_on (hI.mono_set Ioc_subset_Ioi_self)
            (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc fun t ht => ?_
          have hω := (archLevyDensity_pos (by linarith [ht.1] : 0 < t)).le
          calc archLevyDensity t * P (t - x) ≤ archLevyDensity t * 1 :=
                mul_le_mul_of_nonneg_left (hP1 _) hω
            _ = archLevyDensity t := mul_one _
      _ = archLevyAntideriv (x + r) - archLevyAntideriv (x + B) := by
          rw [← intervalIntegral.integral_of_le (by linarith),
            integral_archLevyDensity_Icc (by linarith) (by linarith)]

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
