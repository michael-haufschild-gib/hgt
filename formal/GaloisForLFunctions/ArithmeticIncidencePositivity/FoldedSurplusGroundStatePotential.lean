import GaloisForLFunctions.ArithmeticIncidencePositivity.OddPlateauFoldedWindowPositivity

/-!
# The folded surplus of an odd test and its ground-state potential

Let `P` be an even plateau gauge and `F` an odd test, as in `OddPlateauFoldedWindowPositivity`. The
fold of the crossing pairs onto the same-side pairs is exact
(`two_mul_archSame_sub_archCrossingDiff_eq`):

    J_P(F) = ∫_0^∞ ω(t) ∫_0^t 4 P(x) P(t − x) F(x)² dx dt + 2 S_P(F),
    S_P(F) = ∫_{x>0} ∫_{s>0} (ω(s) − ω(s + 2x)) P(x) P(x + s) (F(x) − F(x + s))² ds dx:

the same-side pair `(x, y)` carries the surplus kernel `k(x, y) = ω(|x − y|) − ω(x + y) ≥ 0` of its
rate over the rate of its crossing partner `(−x, y)`. The plateau fold keeps only the killing term.

A ground-state transform turns the surplus into a potential. For every pair and all `p, q > 0`,
`(a − b)² ≥ a²(1 − q/p) + b²(1 − p/q)` (`sq_sub_ge_groundState`); with `p = h(x)`, `q = h(y)` for a
gauge `h` positive on `[0, r]` (`surplusEnergy_ge_potential`):

    S_P(F) ≥ ∫_{x>0} F(x)² U_h(x) dx,      U_h(x) = ∫_{(0, r]} k(x, y) (1 − h(y)/h(x)) dy.

Where `h` peaks, `U_h > 0`: the surplus pays a potential exactly where the plateau potential is
weakest. Together (`fourKilling_add_surplusPotential_le_archJump`):

    J_P(F) ≥ 2 ∫_{x>0} F(x)² [2(Ω(x) − Ω(x + r)) + U_h(x)] dx.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The surplus kernel -/

/-- The surplus kernel `k(x, y) = ω(|x − y|) − ω(x + y)` of a same-side pair over its crossing
partner. -/
def surplusKernel (x y : ℝ) : ℝ := archLevyDensity |x - y| - archLevyDensity (x + y)

theorem surplusKernel_comm (x y : ℝ) : surplusKernel x y = surplusKernel y x := by
  unfold surplusKernel; rw [abs_sub_comm, add_comm]

theorem surplusKernel_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 ≤ surplusKernel x y := by
  unfold surplusKernel
  have h1 : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have h2 : |x - y| ≤ x + y := by rw [abs_le]; constructor <;> linarith
  linarith [strictAntiOn_archLevyDensity.antitoneOn h1 (show (0 : ℝ) < x + y by linarith) h2]

theorem surplusKernel_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    surplusKernel x y ≤ archLevyDensity |x - y| := by
  unfold surplusKernel; linarith [archLevyDensity_pos (show (0 : ℝ) < x + y by linarith)]

theorem measurable_surplusKernel : Measurable fun p : ℝ × ℝ => surplusKernel p.1 p.2 := by
  unfold surplusKernel
  exact (measurable_archLevyDensity.comp (by fun_prop)).sub (measurable_archLevyDensity.comp (by fun_prop))

/-- In a window `[0, r]`, `r ≤ 1`, the transformed surplus weight is bounded by `3|L|/(2a₀)`
whenever `h ≥ a₀ > 0` at `x` and `h` is `L`-Lipschitz between `x` and `y`. -/
theorem abs_surplusKernel_mul_le {h : ℝ → ℝ} {x y a₀ L : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy1 : |x - y| ≤ 1) (ha₀ : 0 < a₀) (hhx : a₀ ≤ h x) (hhL : |h x - h y| ≤ L * |x - y|) :
    |surplusKernel x y * (1 - h y / h x)| ≤ 3 / 2 * |L| / a₀ := by
  have hhx0 : 0 < h x := lt_of_lt_of_le ha₀ hhx
  by_cases hxy : x = y
  · rw [hxy, div_self (by rw [← hxy]; exact hhx0.ne'), sub_self, mul_zero, abs_zero]
    positivity
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hk0 := surplusKernel_nonneg hx hy hxy
  have hk1 := (surplusKernel_le hx hy).trans (archLevyDensity_le_of_le_one hd hxy1)
  have hq : |1 - h y / h x| ≤ |L| * |x - y| / a₀ := by
    rw [show 1 - h y / h x = (h x - h y) / h x by field_simp, abs_div, abs_of_pos hhx0,
      div_le_div_iff₀ hhx0 ha₀]
    have := hhL.trans (mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg _))
    nlinarith [abs_nonneg (h x - h y), mul_nonneg (abs_nonneg L) (abs_nonneg (x - y))]
  rw [abs_mul, abs_of_nonneg hk0]
  calc surplusKernel x y * |1 - h y / h x| ≤ 3 / 2 / |x - y| * (|L| * |x - y| / a₀) :=
        mul_le_mul hk1 hq (abs_nonneg _) (by positivity)
    _ = 3 / 2 * |L| / a₀ := by field_simp

/-- **The pairwise ground-state inequality.** `(a − b)² ≥ a²(1 − q/p) + b²(1 − p/q)` for
`p, q > 0`; the defect is `(aq − bp)²/(pq)`. -/
theorem sq_sub_ge_groundState (a b : ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    a ^ 2 * (1 - q / p) + b ^ 2 * (1 - p / q) ≤ (a - b) ^ 2 := by
  have key : (a - b) ^ 2 - (a ^ 2 * (1 - q / p) + b ^ 2 * (1 - p / q)) =
      (a * q - b * p) ^ 2 / (p * q) := by
    field_simp; ring
  have : 0 ≤ (a * q - b * p) ^ 2 / (p * q) := by positivity
  linarith

/-- The ground-state potential of the surplus in the gauge `h` on `(0, r]`. -/
def surplusPotential (h : ℝ → ℝ) (r x : ℝ) : ℝ :=
  ∫ y in Ioc 0 r, surplusKernel x y * (1 - h y / h x)

/-- The surplus energy `S_P(F) = ∫_{x>0} ∫_{s>0} (ω(s) − ω(s + 2x)) J_s(x) ds dx`. -/
def surplusEnergy (P F : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
    (archLevyDensity s - archLevyDensity (s + 2 * x)) * signedShiftJump P F s x

theorem surplusKernel_add (x s : ℝ) (hs : 0 < s) :
    surplusKernel x (x + s) = archLevyDensity s - archLevyDensity (s + 2 * x) := by
  unfold surplusKernel
  rw [show x - (x + s) = -s by ring, abs_neg, abs_of_pos hs, show x + (x + s) = s + 2 * x by ring]

section Surplus

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc in
theorem continuous_signedShiftJump_left (x : ℝ) : Continuous fun s => signedShiftJump P F s x := by
  unfold signedShiftJump; fun_prop

include hPc hFc hP0 hP1 hFL hPB hB0 hB1 in
/-- **The exact surplus of the fold.** `2 S_arch − D_arch = 2 S_P(F)`. -/
theorem two_mul_archSame_sub_archCrossingDiff_eq :
    2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) -
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x) =
      2 * surplusEnergy P F := by
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  have hID := integrable_foldedCrossingIntegrand hPc hFc hP0 hP1 hPB hFL hB0 hB1
  rw [archCrossingDiffEnergy_eq hPc hFc hP0 hP1 hPB hFL hB0 hB1,
    archSameEnergy_eq hPc hFc hP0 hP1 hPB hFL hB0 hB1]
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

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The fold with its surplus.** `J_P(F) ≥ 4 ∫_{x>0} F(x)² (Ω(x) − Ω(x + r)) + 2 S_P(F)` when
`P = 1` on `[−r, r] ⊇ supp F`. -/
theorem fourKilling_add_surplusEnergy_le_archJump {r : ℝ} (hr0 : 0 < r) (hrB : r ≤ B)
    (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r) (hPcs : HasCompactSupport P) :
    4 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
        2 * surplusEnergy P F ≤
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t := by
  have hI : IntegrableOn (fun t => archLevyDensity t * gaugeJumpProfile P F t) (Ioi 0) :=
    integrableOn_archLevy_mul_gaugeJumpProfile hP1 hP0 hPB hB0.le (by linarith) hFc hPc hPcs hFL
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  have hS : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x)
      (Ioi 0) :=
    hIS.integral_prod_left.congr (Eventually.of_forall fun t => by
      simp only [Function.uncurry_apply_pair]
      rw [integral_const_mul])
  have hID := integrable_foldedCrossingIntegrand hPc hFc hP0 hP1 hPB hFL hB0 hB1
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
  have hsplit : ∀ t ∈ Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t =
      2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) +
        archLevyDensity t * (∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2) -
        archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x := fun t ht => by
    unfold gaugeJumpProfile
    rw [integral_signedShiftJump_eq_split hPc hFc hPe hFo hPB ht, integral_crossingSum_eq hPc hFc]
    ring
  have hK : IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
      4 * P x * P (t - x) * F x ^ 2) (Ioi 0) := by
    refine ((hI.sub (hS.const_mul 2)).add hD).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hsplit t ht]
    ring
  have hJ : (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) =
      2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), signedShiftJump P F t x) +
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
          4 * P x * P (t - x) * F x ^ 2) -
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, crossingDiffJump P F t x := by
    have hA : IntegrableOn (fun t => 2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ),
        signedShiftJump P F t x) + archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
          4 * P x * P (t - x) * F x ^ 2) (Ioi 0) := (hS.const_mul 2).add hK
    have hS2 : IntegrableOn (fun t => 2 * (archLevyDensity t * ∫ x in Ioi (0 : ℝ),
        signedShiftJump P F t x)) (Ioi 0) := hS.const_mul 2
    rw [setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hA hD,
      integral_add hS2 hK, integral_const_mul]
  have hSur := two_mul_archSame_sub_archCrossingDiff_eq hPc hFc hP0 hP1 hPB hFL hB0 hB1
  have hKI := integrable_killingIntegrand hFc hFo hFB hFL hB1 hrB
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (∫ x in Ioi (0 : ℝ), killingIntegrand F r (t, x)) ≤
      archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2 := by
    intro t ht
    have ht0 : 0 < t := ht
    have hω := (archLevyDensity_pos ht0).le
    have e1 : (fun x => killingIntegrand F r (t, x)) =
        fun x => archLevyDensity t * (Ico (t - r) t).indicator (fun x => 4 * F x ^ 2) x := by
      funext x
      rw [killingIntegrand_apply]
      congr 1
      by_cases h : t ∈ Ioc x (x + r)
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ Ico (t - r) t from
          ⟨by linarith [h.2], h.1⟩)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hh => h
          ⟨hh.2, by linarith [hh.1]⟩)]
    have e2 : (archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2) =
        ∫ x in Ioi (0 : ℝ), archLevyDensity t *
          (Ioo (0 : ℝ) t).indicator (fun x => 4 * P x * P (t - x) * F x ^ 2) x := by
      rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
        Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
    rw [e1, e2]
    have hc1 : Continuous fun x => 4 * F x ^ 2 := by fun_prop
    have hc2 : Continuous fun x => 4 * P x * P (t - x) * F x ^ 2 := by fun_prop
    have i1 : Integrable fun x => archLevyDensity t * (Ico (t - r) t).indicator
        (fun x => 4 * F x ^ 2) x :=
      ((hc1.integrableOn_Icc.mono_set Ico_subset_Icc_self).integrable_indicator
        measurableSet_Ico).const_mul _
    have i2 : Integrable fun x => archLevyDensity t * (Ioo (0 : ℝ) t).indicator
        (fun x => 4 * P x * P (t - x) * F x ^ 2) x :=
      ((hc2.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator
        measurableSet_Ioo).const_mul _
    refine setIntegral_mono_on i1.integrableOn i2.integrableOn measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    refine mul_le_mul_of_nonneg_left ?_ hω
    by_cases h : x ∈ Ico (t - r) t
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ Ioo (0 : ℝ) t from ⟨hx0, h.2⟩)]
      by_cases hF0 : F x = 0
      · rw [hF0]; simp
      · rw [hPr x (hFr x hF0), hPr (t - x) (by
          rw [abs_of_pos (by linarith [h.2])]; linarith [h.1])]
        ring_nf; exact le_rfl
    · rw [Set.indicator_of_notMem h]
      exact Set.indicator_nonneg (fun y _ => by
        have := hP0 y; have := hP0 (t - y); positivity) x
  have hK2 : (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), killingIntegrand F r (t, x)) ≤
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, 4 * P x * P (t - x) * F x ^ 2 :=
    setIntegral_mono_on hKI.integral_prod_left hK measurableSet_Ioi hpt
  have hswap : (∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), killingIntegrand F r (t, x)) =
      4 * ∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r)) := by
    rw [integral_integral_swap (f := fun t x => killingIntegrand F r (t, x)) hKI,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [integral_killingIntegrand_eq hr0 (mem_Ioi.mp hx)]
    ring
  linarith

/-- Almost every point of the positive quadrant has positive coordinates. -/
theorem ae_quadrant {p : ℝ × ℝ → Prop} (hp : ∀ t x, 0 < t → 0 < x → p (t, x)) :
    ∀ᵐ q ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))), p q := by
  rw [Measure.prod_restrict]
  exact (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
    (Eventually.of_forall fun q hq => hp q.1 q.2 hq.1 hq.2)

include hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 in
/-- **The ground-state transform of the surplus.** For a gauge `h ≥ a₀ > 0` on `[0, r]`,
`L`-Lipschitz there, `S_P(F) ≥ ∫_{x>0} F(x)² U_h(x) dx`. -/
theorem surplusEnergy_ge_potential {h : ℝ → ℝ} {r a₀ L : ℝ} (hrB : r ≤ B)
    (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hh : Continuous h) (ha₀ : 0 < a₀) (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|) :
    IntegrableOn (fun x => F x ^ 2 * surplusPotential h r x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotential h r x) ≤ surplusEnergy P F := by
  have hr1 : r ≤ 1 := by linarith
  have hK0 : 0 ≤ K := by
    have := hFL 1 0; norm_num at this; linarith [abs_nonneg (F 1 - F 0)]
  have hF2 : ∀ x, 0 ≤ x → x ≤ r → F x ^ 2 ≤ K ^ 2 * r ^ 2 := fun x hx0 hxr => by
    have h1 := abs_le_mul_abs_of_odd hFo hFL x
    rw [abs_of_nonneg hx0] at h1
    have h2 : |F x| ≤ K * r := h1.trans (mul_le_mul_of_nonneg_left hxr hK0)
    calc F x ^ 2 = |F x| ^ 2 := (sq_abs _).symm
      _ ≤ (K * r) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = K ^ 2 * r ^ 2 := by ring
  have hFz : ∀ x, r < |x| → F x = 0 := fun x hx => by
    by_contra h0; exact absurd (hFr x h0) (not_le.mpr hx)
  have hmk := measurable_surplusKernel
  -- the bounded transformed weight of a pair inside the window
  have hw : ∀ x y, 0 < x → x ≤ r → 0 < y → y ≤ r →
      |surplusKernel x y * (1 - h y / h x)| ≤ 3 / 2 * |L| / a₀ := fun x y hx hxr hy hyr =>
    abs_surplusKernel_mul_le hx hy (by rw [abs_le]; constructor <;> linarith) ha₀
      (hhpos x hx.le hxr) (hhL x y hx.le hxr hy.le hyr)
  have hwF : ∀ x y z, 0 < x → x ≤ r → 0 < y → y ≤ r → 0 ≤ z → z ≤ r →
      |F z ^ 2 * (surplusKernel x y * (1 - h y / h x))| ≤ K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀) :=
    fun x y z hx hxr hy hyr hz hzr => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (hF2 z hz hzr) (hw x y hx hxr hy hyr) (abs_nonneg _) (by positivity)
  -- the three pair densities
  set gA : ℝ × ℝ → ℝ := fun p => if p.2 + p.1 ≤ r then
    F p.2 ^ 2 * (surplusKernel p.2 (p.2 + p.1) * (1 - h (p.2 + p.1) / h p.2)) else 0 with hgA
  set gB : ℝ × ℝ → ℝ := fun p => if p.2 + p.1 ≤ r then
    F (p.2 + p.1) ^ 2 * (surplusKernel (p.2 + p.1) p.2 * (1 - h p.2 / h (p.2 + p.1))) else 0
    with hgB
  set G : ℝ × ℝ → ℝ := fun p => if p.1 < p.2 ∧ p.2 ≤ r then
    F p.2 ^ 2 * (surplusKernel p.2 p.1 * (1 - h p.1 / h p.2)) else 0 with hG
  have hmA : Measurable gA := by
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    exact ((hFc.measurable.comp measurable_snd).pow_const 2).mul
      ((hmk.comp (measurable_snd.prodMk (measurable_snd.add measurable_fst))).mul
        (measurable_const.sub ((hh.measurable.comp (measurable_snd.add measurable_fst)).div
          (hh.measurable.comp measurable_snd))))
  have hmB : Measurable gB := by
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    exact ((hFc.measurable.comp (measurable_snd.add measurable_fst)).pow_const 2).mul
      ((hmk.comp ((measurable_snd.add measurable_fst).prodMk measurable_snd)).mul
        (measurable_const.sub ((hh.measurable.comp measurable_snd).div
          (hh.measurable.comp (measurable_snd.add measurable_fst)))))
  have hmG : Measurable G := by
    refine Measurable.ite ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) ?_ measurable_const
    exact ((hFc.measurable.comp measurable_snd).pow_const 2).mul
      ((hmk.comp (measurable_snd.prodMk measurable_fst)).mul
        (measurable_const.sub ((hh.measurable.comp measurable_fst).div
          (hh.measurable.comp measurable_snd))))
  have hIA : Integrable gA ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmA (C := K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀)) (T₁ := r) (T₂ := r) (fun s x hs hx => ?_)
      (fun s x hs hx hout => ?_)
    · simp only [hgA]
      split_ifs with hxs
      · exact hwF x (x + s) x hx (by linarith) (by linarith) hxs hx.le (by linarith)
      · rw [abs_zero]; positivity
    · simp only [hgA]
      rw [if_neg (by rcases hout with h1 | h1 <;> linarith)]
  have hIB : Integrable gB ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmB (C := K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀)) (T₁ := r) (T₂ := r) (fun s x hs hx => ?_)
      (fun s x hs hx hout => ?_)
    · simp only [hgB]
      split_ifs with hxs
      · exact hwF (x + s) x (x + s) (by linarith) hxs hx (by linarith) (by linarith) hxs
      · rw [abs_zero]; positivity
    · simp only [hgB]
      rw [if_neg (by rcases hout with h1 | h1 <;> linarith)]
  have hIG : Integrable G ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmG (C := K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀)) (T₁ := r) (T₂ := r) (fun x y hx hy => ?_)
      (fun x y hx hy hout => ?_)
    · simp only [hG]
      split_ifs with hxy
      · exact hwF y x y hy hxy.2 hx (by linarith [hxy.1, hxy.2]) hy.le hxy.2
      · rw [abs_zero]; positivity
    · simp only [hG]
      rw [if_neg (by rintro ⟨h1, h2⟩; rcases hout with h3 | h3 <;> linarith)]
  -- the surplus density dominates the two transformed densities
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  set fS : ℝ × ℝ → ℝ := fun p =>
    (archLevyDensity p.1 - archLevyDensity (p.1 + 2 * p.2)) * signedShiftJump P F p.1 p.2 with hfS
  have hmS : Measurable fS := by
    have hc : Continuous fun p : ℝ × ℝ => signedShiftJump P F p.1 p.2 := by
      unfold signedShiftJump; fun_prop
    exact ((measurable_archLevyDensity.comp measurable_fst).sub
      (measurable_archLevyDensity.comp (by fun_prop))).mul hc.measurable
  have hIfS : Integrable fS ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine hIS.mono' hmS.aestronglyMeasurable (ae_quadrant fun s x hs hx => ?_)
    have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
    have hω := strictAntiOn_archLevyDensity.antitoneOn hs (show (0 : ℝ) < s + 2 * x by linarith)
      (by linarith)
    have hω2 := (archLevyDensity_pos (show (0 : ℝ) < s + 2 * x by linarith)).le
    simp only [hfS, Function.uncurry_apply_pair, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (by linarith) hJ)]
    exact mul_le_mul_of_nonneg_right (by linarith) hJ
  have hpt : ∀ s x, 0 < s → 0 < x → gA (s, x) + gB (s, x) ≤ fS (s, x) := by
    intro s x hs hx
    have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
    have hk := surplusKernel_nonneg hx (show 0 < x + s by linarith) (by linarith : x ≠ x + s)
    simp only [hgA, hgB, hfS]
    rw [← surplusKernel_add x s hs]
    split_ifs with hxs
    · have hP1' : P x = 1 := hPr x (by rw [abs_of_pos hx]; linarith)
      have hP2' : P (x + s) = 1 := hPr (x + s) (by rw [abs_of_pos (by linarith)]; exact hxs)
      have hgs := sq_sub_ge_groundState (F x) (F (x + s)) (lt_of_lt_of_le ha₀ (hhpos x hx.le
        (by linarith))) (lt_of_lt_of_le ha₀ (hhpos (x + s) (by linarith) hxs))
      unfold signedShiftJump
      rw [hP1', hP2', surplusKernel_comm (x + s) x]
      nlinarith [mul_le_mul_of_nonneg_left hgs hk]
    · rw [add_zero]; exact mul_nonneg hk hJ
  -- the iterated comparison
  have hcmp : (∫ x in Ioi (0 : ℝ), ((∫ s in Ioi (0 : ℝ), gA (s, x)) +
      ∫ s in Ioi (0 : ℝ), gB (s, x))) ≤ surplusEnergy P F := by
    have hO : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ s in Ioi (0 : ℝ), gB (s, x))
        (volume.restrict (Ioi 0)) := hIA.integral_prod_right.add hIB.integral_prod_right
    refine integral_mono_ae hO hIfS.integral_prod_right ?_
    filter_upwards [hIA.prod_left_ae, hIB.prod_left_ae, hIfS.prod_left_ae,
      ae_restrict_mem measurableSet_Ioi] with x hxA hxB hxS hx0
    have hx : 0 < x := hx0
    rw [← integral_add hxA hxB]
    refine integral_mono_ae (hxA.add hxB) hxS ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hpt s x hs hx
  -- the same-side half
  have hA : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), gA (s, x)) =
      F x ^ 2 * ∫ y in Ioc x r, surplusKernel x y * (1 - h y / h x) := by
    intro x hx
    have e := setIntegral_Ioi_translate (fun y => gA (y - x, x)) x
    simp only [add_sub_cancel_right] at e
    rw [← e, ← integral_const_mul, ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hgA, Set.indicator_apply, mem_Iic, add_sub_cancel]
  -- the reflected half
  have hB : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), gB (s, x)) = ∫ y in Ioi (0 : ℝ), G (x, y) := by
    intro x hx
    have e := setIntegral_Ioi_translate (fun y => gB (y - x, x)) x
    simp only [add_sub_cancel_right] at e
    rw [← e, ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext y
    simp only [hgB, hG, Set.indicator_apply, mem_Ioi, add_sub_cancel]
    by_cases hxy : x < y
    · rw [if_pos hxy, if_pos (lt_trans hx hxy)]
      by_cases hyr : y ≤ r
      · rw [if_pos hyr, if_pos ⟨hxy, hyr⟩]
      · rw [if_neg hyr, if_neg (fun h => hyr h.2)]
    · rw [if_neg hxy]
      by_cases hy : 0 < y
      · rw [if_pos hy, if_neg (fun h => hxy h.1)]
      · rw [if_neg hy]
  have hBt : ∀ y, 0 < y → (∫ x in Ioi (0 : ℝ), G (x, y)) = if y ≤ r then
      F y ^ 2 * ∫ x in Ioo 0 y, surplusKernel y x * (1 - h x / h y) else 0 := by
    intro y hy
    split_ifs with hyr
    · rw [← integral_const_mul, ← integral_indicator measurableSet_Ioo,
        ← integral_indicator measurableSet_Ioi]
      congr 1
      funext x
      simp only [hG, Set.indicator_apply, mem_Ioi, mem_Ioo]
      by_cases hx : 0 < x
      · by_cases hxy : x < y
        · rw [if_pos hx, if_pos ⟨hxy, hyr⟩, if_pos ⟨hx, hxy⟩]
        · rw [if_pos hx, if_neg (fun h => hxy h.1), if_neg (fun h => hxy h.2)]
      · rw [if_neg hx, if_neg (fun h => hx h.1)]
    · refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
      simp only [hG, Pi.zero_apply]
      rw [if_neg (fun h => hyr h.2)]
  -- the potential is the sum of the two halves
  have hsum : ∀ x, 0 < x → F x ^ 2 * surplusPotential h r x =
      (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ x' in Ioi (0 : ℝ), G (x', x) := by
    intro x hx
    rw [hA x hx, hBt x hx]
    by_cases hxr : x ≤ r
    · rw [if_pos hxr]
      have hint : IntegrableOn (fun y => surplusKernel x y * (1 - h y / h x)) (Ioc 0 r) := by
        refine Measure.integrableOn_of_bounded (M := 3 / 2 * |L| / a₀) (by simp)
          ((hmk.comp (measurable_const.prodMk measurable_id)).mul (measurable_const.sub
            ((hh.measurable).div measurable_const))).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        rw [Real.norm_eq_abs]
        exact hw x y hx hxr hy.1 hy.2
      unfold surplusPotential
      rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr, setIntegral_union (Set.disjoint_left.mpr fun y h1 h2 =>
        by linarith [h1.2, h2.1]) measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hxr))
        (hint.mono_set (Ioc_subset_Ioc_left hx.le)), integral_Ioc_eq_integral_Ioo (x := 0)]
      have e : (∫ y in Ioo 0 x, surplusKernel x y * (1 - h y / h x)) =
          ∫ x' in Ioo 0 x, surplusKernel x x' * (1 - h x' / h x) := rfl
      rw [mul_add]
      ring
    · rw [if_neg hxr, hFz x (by rw [abs_of_pos hx]; exact not_le.mp hxr)]
      ring
  have hIsum : IntegrableOn (fun x => F x ^ 2 * surplusPotential h r x) (Ioi 0) := by
    have h1 : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ x' in Ioi (0 : ℝ), G (x', x))
        (volume.restrict (Ioi 0)) := hIA.integral_prod_right.add hIG.integral_prod_right
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hsum x hx).symm
  refine ⟨hIsum, ?_⟩
  have hswap : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), gB (s, x)) =
      ∫ x in Ioi (0 : ℝ), ∫ x' in Ioi (0 : ℝ), G (x', x) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => hB x hx]
    exact integral_integral_swap (f := fun x y => G (x, y)) hIG
  have hI1 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), gA (s, x)) (volume.restrict (Ioi 0)) :=
    hIA.integral_prod_right
  have hI2 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), gB (s, x)) (volume.restrict (Ioi 0)) :=
    hIB.integral_prod_right
  have hI3 : Integrable (fun x => ∫ x' in Ioi (0 : ℝ), G (x', x)) (volume.restrict (Ioi 0)) :=
    hIG.integral_prod_right
  rw [setIntegral_congr_fun measurableSet_Ioi hsum, integral_add hI1 hI3, ← hswap,
    ← integral_add hI1 hI2]
  exact hcmp

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The fold with its ground-state potential.**
`J_P(F) ≥ 4 ∫_{x>0} F(x)² (Ω(x) − Ω(x + r)) + 2 ∫_{x>0} F(x)² U_h(x)`. -/
theorem fourKilling_add_surplusPotential_le_archJump {h : ℝ → ℝ} {r a₀ L : ℝ} (hr0 : 0 < r)
    (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hPcs : HasCompactSupport P) (hh : Continuous h) (ha₀ : 0 < a₀)
    (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|) :
    IntegrableOn (fun x => F x ^ 2 * surplusPotential h r x) (Ioi 0) ∧
      4 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
          2 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotential h r x) ≤
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t := by
  obtain ⟨hI, hle⟩ := surplusEnergy_ge_potential hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 hrB hPr hFr
    hh ha₀ hhpos hhL
  have := fourKilling_add_surplusEnergy_le_archJump hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1
    hr0 hrB hPr hFr hPcs
  exact ⟨hI, by linarith⟩

end Surplus

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
