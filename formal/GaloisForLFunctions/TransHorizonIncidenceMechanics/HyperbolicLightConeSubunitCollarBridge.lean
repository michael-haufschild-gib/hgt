import GaloisForLFunctions.TransHorizonIncidenceMechanics.SupportRadiusCollarCutoffAndAllScaleObstacleBBridge
import GaloisForLFunctions.ArithmeticCriticalityTheory.LightConeAntisymmetricVariationLaw

/-!
# Hyperbolic Light-Cone Bridge and Sub-Unit Collar Budget Across `log d ≤ a - R`

In `SupportRadiusCollarCutoffAndAllScaleObstacleBBridge`, comparing the prime-collar anti-diagonals
against the archimedean Lévy drop `ω(s) − ω(s + 2y)` alone discarded `profileVariance` and yielded
an `a`-independent constant `supportArchBudget R δ L ∝ e^{9R} > 1`.

By `LightConeAntisymmetricVariationLaw`, adding `profileVariance` to `2 S_arch − D_arch` replaces
`ω(s) − ω(s + 2y)` by the antisymmetric Weil jump difference `κ(s) − κ(s + 2y)`, which satisfies
the global lower bound `4 sinh(y/2) sinh((y + s)/2) ≤ κ(s) − κ(s + 2y)` on `(0, ∞) × [0, ∞)` with
no finite threshold.

Mediating the low-prime Schur residual (`log d < 2R`) across any continuum bridge interval
`z ∈ (z₁, z₂) ⊆ [3R, a]` therefore integrates `4 sinh((log d)/4) sinh(z/2)` to
`8 sinh((log d)/4) (cosh(z₂/2) − cosh(z₁/2))`, dividing the fixed `a`-independent numerator
`hyperbolicLowPrimeNumerator R` by `cosh(z₂/2) − cosh(z₁/2) → +∞` as `z₂ → +∞`. In particular, for
every support radius `R ≥ 0` and every `ε > 0` (including `ε < 1`), choosing `a` sufficiently large
discharges all prime powers `log d ≤ a − R` using less than an `ε`-fraction of the continuum
light-cone energy on `(0, 3R) × (0, a − 2R)` (disjoint from the exterior strip `y ≥ a − 2R`).
-/

open MeasureTheory Set Filter Topology Real
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ThetaSourceWard _root_.RHTower.PhiDivisorEnergy
open GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ## Section 1: Hyperbolic and Light-Cone Continuum Integrands -/

/-- Smooth hyperbolic lower-bound integrand `4 sinh(y/2) sinh((y + s)/2) J_s(y)` for the
antisymmetric Weil jump kernel. -/
def hyperbolicShiftIntegrand (a : ℝ) (w : ℝ → ℝ) (s y : ℝ) : ℝ :=
  4 * Real.sinh (y / 2) * Real.sinh ((y + s) / 2) * oddProfileShiftJump a w s y

/-- Compact 1D slice `∫_{s ∈ (0, M)} hyperbolicShiftIntegrand a w s y` at starting point `y`. -/
def hyperbolicShiftSlice (a : ℝ) (w : ℝ → ℝ) (M y : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) M, hyperbolicShiftIntegrand a w s y

/-- Full antisymmetric Weil light-cone integrand `(κ(s) − κ(s + 2y)) J_s(y)` in `oddProfile`
normalization. -/
def lightConeOddIntegrand (a : ℝ) (w : ℝ → ℝ) (s y : ℝ) : ℝ :=
  (weilJumpDensity s - weilJumpDensity (s + 2 * y)) * oddProfileShiftJump a w s y

/-- Exact rescaling between `oddProfileShiftJump` and `sameSideGroundJump (shiftedGroundState a)`:
they differ only by the global normalization factor `4 sinh(a/2)²`. -/
theorem four_mul_sinh_sq_mul_oddProfileShiftJump_eq {a : ℝ} (ha : a ≠ 0)
    (w : ℝ → ℝ) (s y : ℝ) :
    4 * Real.sinh (a / 2) ^ 2 * oddProfileShiftJump a w s y =
      sameSideGroundJump (shiftedGroundState a) w s y := by
  have hy := two_mul_sinh_mul_oddProfile_eq ha y
  have hys := two_mul_sinh_mul_oddProfile_eq ha (y + s)
  have ky := riemannKernelReal_mul_shiftedGroundState a y
  have kys := riemannKernelReal_mul_shiftedGroundState a (y + s)
  have h1 : 2 * Real.sinh (a / 2) * oddProfile a y =
      riemannKernelReal y * shiftedGroundState a y := by
    rw [hy, ky]
    unfold shiftDifference
    rw [show y - a = -(a - y) by ring, WeilExcess.riemannKernelReal_neg,
      show y + a = a + y by ring]
  have h2 : 2 * Real.sinh (a / 2) * oddProfile a (y + s) =
      riemannKernelReal (y + s) * shiftedGroundState a (y + s) := by
    rw [hys, kys]
    unfold shiftDifference
    rw [show y + s - a = -(a - (y + s)) by ring, WeilExcess.riemannKernelReal_neg,
      show y + s + a = a + (y + s) by ring]
  unfold oddProfileShiftJump sameSideGroundJump
  calc 4 * Real.sinh (a / 2) ^ 2 *
        (oddProfile a y * oddProfile a (y + s) * (w y - w (y + s)) ^ 2)
      = (2 * Real.sinh (a / 2) * oddProfile a y) *
          (2 * Real.sinh (a / 2) * oddProfile a (y + s)) * (w y - w (y + s)) ^ 2 := by ring
    _ = (riemannKernelReal y * shiftedGroundState a y) *
          (riemannKernelReal (y + s) * shiftedGroundState a (y + s)) *
          (w y - w (y + s)) ^ 2 := by rw [h1, h2]
    _ = _ := by ring

theorem hyperbolicShiftIntegrand_nonneg {a s y : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hy : 0 < y)
    (w : ℝ → ℝ) :
    0 ≤ hyperbolicShiftIntegrand a w s y := by
  unfold hyperbolicShiftIntegrand
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr (by positivity)))
      (Real.sinh_nonneg_iff.mpr (by linarith)))
    (oddProfileShiftJump_nonneg_of_pos ha hy hs w)

theorem hyperbolicShiftIntegrand_le_lightConeOddIntegrand {a s y : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hy : 0 < y) (w : ℝ → ℝ) :
    hyperbolicShiftIntegrand a w s y ≤ lightConeOddIntegrand a w s y := by
  unfold hyperbolicShiftIntegrand lightConeOddIntegrand
  exact mul_le_mul_of_nonneg_right
    (four_mul_sinh_mul_sinh_le_weilJumpDensity_sub hs hy.le)
    (oddProfileShiftJump_nonneg_of_pos ha hy hs.le w)

theorem lightConeOddIntegrand_nonneg {a s y : ℝ} (ha : 0 < a) (hs : 0 < s) (hy : 0 < y)
    (w : ℝ → ℝ) :
    0 ≤ lightConeOddIntegrand a w s y :=
  (hyperbolicShiftIntegrand_nonneg ha hs.le hy w).trans
    (hyperbolicShiftIntegrand_le_lightConeOddIntegrand ha hs hy w)

theorem continuous_uncurry_hyperbolicShiftIntegrand (a : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (fun p : ℝ × ℝ => hyperbolicShiftIntegrand a w p.2 p.1) := by
  unfold hyperbolicShiftIntegrand oddProfileShiftJump
  have hsh1 : Continuous (fun p : ℝ × ℝ => Real.sinh (p.1 / 2)) :=
    Real.continuous_sinh.comp (continuous_fst.div_const 2)
  have hsh2 : Continuous (fun p : ℝ × ℝ => Real.sinh ((p.1 + p.2) / 2)) :=
    Real.continuous_sinh.comp ((continuous_fst.add continuous_snd).div_const 2)
  have hjump : Continuous (fun p : ℝ × ℝ =>
      oddProfile a p.1 * oddProfile a (p.1 + p.2) * (w p.1 - w (p.1 + p.2)) ^ 2) :=
    (((continuous_oddProfile a).comp continuous_fst).mul
      ((continuous_oddProfile a).comp (continuous_fst.add continuous_snd))).mul
      (((hw.comp continuous_fst).sub (hw.comp (continuous_fst.add continuous_snd))).pow 2)
  exact (((continuous_const.mul hsh1).mul hsh2).mul hjump)

theorem continuous_hyperbolicShiftSlice (a : ℝ) {M : ℝ} (hM : 0 ≤ M)
    {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (hyperbolicShiftSlice a w M) := by
  have hc : Continuous (fun y : ℝ => ∫ s in (0 : ℝ)..M, hyperbolicShiftIntegrand a w s y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_uncurry_hyperbolicShiftIntegrand a hw) 0 M
  refine hc.congr fun y => ?_
  rw [hyperbolicShiftSlice, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hM]

theorem hyperbolicShiftSlice_nonneg {a M y : ℝ} (ha : 0 < a) (hy : 0 < y) (w : ℝ → ℝ) :
    0 ≤ hyperbolicShiftSlice a w M y :=
  setIntegral_nonneg measurableSet_Ioo fun _ hs =>
    hyperbolicShiftIntegrand_nonneg ha hs.1.le hy w

theorem continuous_hyperbolicShiftIntegrand_left (a y : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (fun s : ℝ => hyperbolicShiftIntegrand a w s y) := by
  unfold hyperbolicShiftIntegrand oddProfileShiftJump
  exact (continuous_const.mul (Real.continuous_sinh.comp
    ((continuous_const.add continuous_id).div_const 2))).mul
    ((continuous_const.mul ((continuous_oddProfile a).comp (continuous_const.add continuous_id))).mul
      ((continuous_const.sub (hw.comp (continuous_const.add continuous_id))).pow 2))

theorem continuous_hyperbolicShiftIntegrand_sub (a y : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (fun z : ℝ => hyperbolicShiftIntegrand a w (z - y) y) :=
  (continuous_hyperbolicShiftIntegrand_left a y hw).comp (continuous_id.sub continuous_const)

theorem hyperbolicShiftSlice_mono_right {a M₁ M₂ y : ℝ} (ha : 0 < a)
    (hM : M₁ ≤ M₂) (hy : 0 < y) {w : ℝ → ℝ} (hw : Continuous w) :
    hyperbolicShiftSlice a w M₁ y ≤ hyperbolicShiftSlice a w M₂ y := by
  unfold hyperbolicShiftSlice
  have hc := continuous_hyperbolicShiftIntegrand_left a y hw
  refine setIntegral_mono_set (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self) ?_
    (Eventually.of_forall fun s hs => ⟨hs.1, hs.2.trans_le hM⟩)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hyperbolicShiftIntegrand_nonneg ha hs.1.le hy w

/-! ## Section 2: Hyperbolic Continuum Bridge Across `(z₁, z₂) ⊆ [3t/2, a]` -/

/-- Pointwise hyperbolic bridge bound across `z ∈ (z₁, z₂)` (`3t/2 ≤ z₁ < z₂ ≤ a`). -/
theorem oddProfileAcrossJump_mul_sinh_le_two_hyperbolic_legs {a t z₁ z₂ x z : ℝ}
    (ha : 0 < a) (hz₁ : 3 * t / 2 ≤ z₁) (hz₂ : z₂ ≤ a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) (hz : z ∈ Ioo z₁ z₂) (w : ℝ → ℝ) :
    4 * Real.sinh (t / 4) * Real.sinh (z / 2) * oddProfileAcrossJump a w t x ≤
      2 * hyperbolicShiftIntegrand a w (z - (t - x)) (t - x) +
        2 * hyperbolicShiftIntegrand a w (z - (t + x)) (t + x) := by
  have hz_Ioc : z ∈ Ioc (3 * t / 2) a := ⟨hz₁.trans_lt hz.1, hz.2.le.trans hz₂⟩
  have hbridge := oddProfileAcrossJump_le_two_bridge_legs ha hx hz_Ioc w
  have ht0 : 0 < t := by linarith [hx.1, hx.2]
  have hz0 : 0 < z := by linarith [ht0, hz_Ioc.1]
  have hc0 : 0 ≤ 4 * Real.sinh (t / 4) * Real.sinh (z / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr (by positivity)))
      (Real.sinh_nonneg_iff.mpr (by positivity))
  have hsh1 : Real.sinh (t / 4) ≤ Real.sinh ((t - x) / 2) :=
    Real.sinh_le_sinh.mpr (by linarith [hx.2])
  have hsh2 : Real.sinh (t / 4) ≤ Real.sinh ((t + x) / 2) :=
    Real.sinh_le_sinh.mpr (by linarith [hx.1, hx.2])
  have hj1 : 0 ≤ oddProfileShiftJump a w (z - (t - x)) (t - x) :=
    oddProfileShiftJump_nonneg_of_pos ha (by linarith [hx.1, hx.2])
      (by linarith [hx.1, hx.2, hz_Ioc.1]) w
  have hj2 : 0 ≤ oddProfileShiftJump a w (z - (t + x)) (t + x) :=
    oddProfileShiftJump_nonneg_of_pos ha (by linarith [hx.1, hx.2])
      (by linarith [hx.2, hz_Ioc.1]) w
  have hleg1 : 4 * Real.sinh (t / 4) * Real.sinh (z / 2) *
        oddProfileShiftJump a w (z - (t - x)) (t - x) ≤
      hyperbolicShiftIntegrand a w (z - (t - x)) (t - x) := by
    unfold hyperbolicShiftIntegrand
    rw [show t - x + (z - (t - x)) = z by ring]
    refine mul_le_mul_of_nonneg_right ?_ hj1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsh1 (by norm_num))
      (Real.sinh_nonneg_iff.mpr (by positivity))
  have hleg2 : 4 * Real.sinh (t / 4) * Real.sinh (z / 2) *
        oddProfileShiftJump a w (z - (t + x)) (t + x) ≤
      hyperbolicShiftIntegrand a w (z - (t + x)) (t + x) := by
    unfold hyperbolicShiftIntegrand
    rw [show t + x + (z - (t + x)) = z by ring]
    refine mul_le_mul_of_nonneg_right ?_ hj2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsh2 (by norm_num))
      (Real.sinh_nonneg_iff.mpr (by positivity))
  have hmul := mul_le_mul_of_nonneg_left hbridge hc0
  linarith

/-- Exact integral of `sinh(z/2)` on `(z₁, z₂)` (`z₁ ≤ z₂`). -/
theorem integral_Ioo_sinh_half {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) :
    (∫ z in Ioo z₁ z₂, Real.sinh (z / 2)) =
      2 * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hz]
  have hd : ∀ z ∈ uIcc z₁ z₂,
      HasDerivAt (fun u : ℝ => 2 * Real.cosh (u / 2)) (Real.sinh (z / 2)) z := by
    intro z _
    have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2 : ℝ) z :=
      (hasDerivAt_id z).div_const 2
    have h2 : HasDerivAt (fun u : ℝ => Real.cosh (u / 2)) (Real.sinh (z / 2) * (1 / 2)) z :=
      h1.cosh
    exact (h2.const_mul 2).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_sinh.comp (continuous_id.div_const 2)).intervalIntegrable _ _)]
  ring

theorem integral_hyperbolic_leg_le_slice {a t z₁ : ℝ} (z₂ : ℝ) {y : ℝ}
    (ha : 0 < a) (hz₁ : 3 * t / 2 ≤ z₁)
    (hy : y ∈ Ioo (t / 2) (3 * t / 2)) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ z in Ioo z₁ z₂, hyperbolicShiftIntegrand a w (z - y) y) ≤
      hyperbolicShiftSlice a w z₂ y := by
  have hy_pos : 0 < y := by linarith [hy.1, hy.2]
  have hmp : MeasurePreserving (fun s : ℝ => s + y) volume volume :=
    measurePreserving_add_right volume y
  have hemb : MeasurableEmbedding (fun s : ℝ => s + y) :=
    (Homeomorph.addRight y).measurableEmbedding
  have hpre : (fun s : ℝ => s + y) ⁻¹' Ioo z₁ z₂ = Ioo (z₁ - y) (z₂ - y) := by
    ext s; simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith
  have htr := hmp.setIntegral_preimage_emb hemb
    (fun z : ℝ => hyperbolicShiftIntegrand a w (z - y) y) (Ioo z₁ z₂)
  rw [hpre] at htr
  have hcongr : (∫ s in Ioo (z₁ - y) (z₂ - y), hyperbolicShiftIntegrand a w (s + y - y) y) =
      ∫ s in Ioo (z₁ - y) (z₂ - y), hyperbolicShiftIntegrand a w s y :=
    setIntegral_congr_fun measurableSet_Ioo fun s _ => by rw [add_sub_cancel_right]
  rw [← htr, hcongr]
  unfold hyperbolicShiftSlice
  have hc := continuous_hyperbolicShiftIntegrand_left a y hw
  refine setIntegral_mono_set (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self) ?_
    (Eventually.of_forall fun s hs => ⟨by linarith [hs.1, hy.2, hz₁], by linarith [hs.2, hy_pos]⟩)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact hyperbolicShiftIntegrand_nonneg ha hs.1.le hy_pos w

theorem integral_hyperbolicShiftSlice_sub_add_add_eq_Ioo (a : ℝ) {t M : ℝ}
    (ht : 0 ≤ t) (hM : 0 ≤ M) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ x in Ioo (0 : ℝ) (t / 2), hyperbolicShiftSlice a w M (t - x)) +
        (∫ x in Ioo (0 : ℝ) (t / 2), hyperbolicShiftSlice a w M (t + x)) =
      ∫ y in Ioo (t / 2) (3 * t / 2), hyperbolicShiftSlice a w M y := by
  set F := hyperbolicShiftSlice a w M
  have hF : Continuous F := continuous_hyperbolicShiftSlice a hM hw
  have hintF : IntegrableOn F (Icc (t / 2) (3 * t / 2)) := hF.integrableOn_Icc
  have hrefl : (∫ x in Ioo (0 : ℝ) (t / 2), F (t - x)) = ∫ y in Ioo (t / 2) t, F y := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith)]
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t / 2) F t
    rw [sub_zero, show t - t / 2 = t / 2 by ring] at h
    exact h
  have htrans : (∫ x in Ioo (0 : ℝ) (t / 2), F (t + x)) = ∫ y in Ioo t (3 * t / 2), F y := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_of_le (by linarith)]
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := t / 2) F t
    rw [add_zero, show t + t / 2 = 3 * t / 2 by ring] at h
    exact h
  have hunion : Ioc (t / 2) t ∪ Ioc t (3 * t / 2) = Ioc (t / 2) (3 * t / 2) :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc (t / 2) t) (Ioc t (3 * t / 2)) :=
    Ioc_disjoint_Ioc_of_le le_rfl
  rw [hrefl, htrans, ← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← hunion,
    setIntegral_union hdisj measurableSet_Ioc
      (hintF.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl (by linarith))))
      (hintF.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc (by linarith) le_rfl)))]

/-- Pointwise-in-`x` integrated hyperbolic bridge inequality across `z ∈ (z₁, z₂)`. -/
theorem mul_oddProfileAcrossJump_le_two_hyperbolicShiftSlice {a t z₁ z₂ x : ℝ}
    (ha : 0 < a) (hz₁ : 3 * t / 2 ≤ z₁) (hz : z₁ ≤ z₂) (hz₂ : z₂ ≤ a)
    (hx : x ∈ Ioo (0 : ℝ) (t / 2)) {w : ℝ → ℝ} (hw : Continuous w) :
    8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) *
        oddProfileAcrossJump a w t x ≤
      2 * hyperbolicShiftSlice a w z₂ (t - x) + 2 * hyperbolicShiftSlice a w z₂ (t + x) := by
  have hy1 : t - x ∈ Ioo (t / 2) (3 * t / 2) := ⟨by linarith [hx.2], by linarith [hx.1, hx.2]⟩
  have hy2 : t + x ∈ Ioo (t / 2) (3 * t / 2) := ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩
  have hint1 : IntegrableOn (fun z : ℝ => hyperbolicShiftIntegrand a w (z - (t - x)) (t - x))
      (Ioo z₁ z₂) :=
    (continuous_hyperbolicShiftIntegrand_sub a (t - x) hw).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun z : ℝ => hyperbolicShiftIntegrand a w (z - (t + x)) (t + x))
      (Ioo z₁ z₂) :=
    (continuous_hyperbolicShiftIntegrand_sub a (t + x) hw).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hsh_int : IntegrableOn (fun z : ℝ =>
      4 * Real.sinh (t / 4) * Real.sinh (z / 2) * oddProfileAcrossJump a w t x) (Ioo z₁ z₂) :=
    (((Real.continuous_sinh.comp (continuous_id.div_const 2)).const_mul
      (4 * Real.sinh (t / 4))).mul_const
      (oddProfileAcrossJump a w t x)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hmono : (∫ z in Ioo z₁ z₂,
        4 * Real.sinh (t / 4) * Real.sinh (z / 2) * oddProfileAcrossJump a w t x) ≤
      ∫ z in Ioo z₁ z₂,
        (2 * hyperbolicShiftIntegrand a w (z - (t - x)) (t - x) +
          2 * hyperbolicShiftIntegrand a w (z - (t + x)) (t + x)) :=
    setIntegral_mono_on hsh_int ((hint1.const_mul 2).add (hint2.const_mul 2))
      measurableSet_Ioo fun z hzz =>
        oddProfileAcrossJump_mul_sinh_le_two_hyperbolic_legs ha hz₁ hz₂ hx hzz w
  have hlhs : (∫ z in Ioo z₁ z₂,
        4 * Real.sinh (t / 4) * Real.sinh (z / 2) * oddProfileAcrossJump a w t x) =
      8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) *
        oddProfileAcrossJump a w t x := by
    have heq : (fun z : ℝ =>
        4 * Real.sinh (t / 4) * Real.sinh (z / 2) * oddProfileAcrossJump a w t x) =
        fun z : ℝ => (4 * Real.sinh (t / 4) * oddProfileAcrossJump a w t x) *
          Real.sinh (z / 2) := by funext z; ring
    rw [heq, integral_const_mul, integral_Ioo_sinh_half hz]
    ring
  rw [hlhs, integral_add (hint1.const_mul 2) (hint2.const_mul 2),
    integral_const_mul, integral_const_mul] at hmono
  have hleg1 := integral_hyperbolic_leg_le_slice z₂ ha hz₁ hy1 hw
  have hleg2 := integral_hyperbolic_leg_le_slice z₂ ha hz₁ hy2 hw
  linarith

/-- Integrated hyperbolic bridge inequality on `(0, t/2)` across `z ∈ (z₁, z₂)`. -/
theorem integral_oddProfileAcrossJump_le_hyperbolicShiftSlice {a t z₁ z₂ : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hz₁ : 3 * t / 2 ≤ z₁) (hz : z₁ ≤ z₂) (hz₂ : z₂ ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) :
    8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) *
        (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileAcrossJump a w t x) ≤
      2 * ∫ y in Ioo (t / 2) (3 * t / 2), hyperbolicShiftSlice a w z₂ y := by
  have hz₂0 : 0 ≤ z₂ := by linarith
  have hF : Continuous (hyperbolicShiftSlice a w z₂) := continuous_hyperbolicShiftSlice a hz₂0 hw
  have hint_sub : IntegrableOn (fun x : ℝ => hyperbolicShiftSlice a w z₂ (t - x))
      (Ioo (0 : ℝ) (t / 2)) :=
    (hF.comp (continuous_const.sub continuous_id)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_add : IntegrableOn (fun x : ℝ => hyperbolicShiftSlice a w z₂ (t + x))
      (Ioo (0 : ℝ) (t / 2)) :=
    (hF.comp (continuous_const.add continuous_id)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_acr : IntegrableOn (oddProfileAcrossJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileAcrossJump a t hw).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hmono2 : (∫ x in Ioo (0 : ℝ) (t / 2),
        (8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2))) *
          oddProfileAcrossJump a w t x) ≤
      ∫ x in Ioo (0 : ℝ) (t / 2),
        (2 * hyperbolicShiftSlice a w z₂ (t - x) + 2 * hyperbolicShiftSlice a w z₂ (t + x)) :=
    setIntegral_mono_on (hint_acr.const_mul _)
      ((hint_sub.const_mul 2).add (hint_add.const_mul 2)) measurableSet_Ioo
      fun x hx => mul_oddProfileAcrossJump_le_two_hyperbolicShiftSlice ha hz₁ hz hz₂ hx hw
  rw [integral_const_mul, integral_add (hint_sub.const_mul 2) (hint_add.const_mul 2),
    integral_const_mul, integral_const_mul, ← mul_add,
    integral_hyperbolicShiftSlice_sub_add_add_eq_Ioo a ht hz₂0 hw] at hmono2
  exact hmono2

/-- **Unconditional Hyperbolic 1-for-1 Collar-Minus-Direct Excess Bound:**
For any `0 ≤ t`, `3t/2 ≤ z₁ ≤ z₂ ≤ a`, and `3t/2 + (log 2)/2 ≤ a`, subtracting twice the
half-collar direct jump from the full collar integral is bounded by `16 e^{4t}` over
`8 sinh(t/4) (cosh(z₂/2) − cosh(z₁/2))` times the hyperbolic slice integral on `(0, 3t/2) × (0, z₂)`. -/
theorem integral_oddProfileCollarDiffSq_sub_two_direct_le_hyperbolicShiftSlice
    {a t z₁ z₂ : ℝ} (ht : 0 ≤ t) (hz₁ : 3 * t / 2 ≤ z₁) (hz : z₁ ≤ z₂) (hz₂ : z₂ ≤ a)
    (ha_log2 : 3 * t / 2 + Real.log 2 / 2 ≤ a) {w : ℝ → ℝ} (hw : Continuous w) :
    8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) *
        ((∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) -
          2 * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x)) ≤
      16 * Real.exp (4 * t) *
        ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y := by
  have ha_pos : 0 < a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hz₂0 : 0 ≤ z₂ := by linarith
  have hint_col : IntegrableOn (oddProfileCollarDiffSq a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileCollarDiffSq a t hw).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_dir : IntegrableOn (oddProfileShiftJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileShiftJump_right a t hw).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint_acr : IntegrableOn (oddProfileAcrossJump a w t) (Ioo (0 : ℝ) (t / 2)) :=
    (continuous_oddProfileAcrossJump a t hw).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hschur : (∫ x in Ioo (0 : ℝ) (t / 2),
        (oddProfileCollarDiffSq a w t x - oddProfileShiftJump a w t x)) ≤
      ∫ x in Ioo (0 : ℝ) (t / 2), 4 * Real.exp (4 * t) * oddProfileAcrossJump a w t x :=
    setIntegral_mono_on (hint_col.sub hint_dir) (hint_acr.const_mul _) measurableSet_Ioo
      fun x hx => oddProfileCollarDiffSq_sub_direct_le_four_exp_four_mul_across ht ha_log2 hx w
  rw [integral_sub hint_col hint_dir, integral_const_mul] at hschur
  have hfull : (∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) -
        2 * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x) ≤
      8 * Real.exp (4 * t) * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileAcrossJump a w t x) := by
    have hhalf : (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w (t - 2 * x) x) =
        ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileCollarDiffSq a w t x :=
      halfCollarIntegral_eq_integral_oddProfileCollarDiffSq_half a w t
    rw [integral_oddProfileCollarDiffSq_eq_two_mul_half a hw ht, hhalf]
    linarith
  have hc_nn : 0 ≤ 8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) := by
    have hc : Real.cosh (z₁ / 2) ≤ Real.cosh (z₂ / 2) :=
      strictMonoOn_cosh_Ici.monotoneOn (mem_Ici.mpr (by linarith))
        (mem_Ici.mpr (by linarith)) (by linarith)
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr (by positivity)))
      (sub_nonneg.mpr hc)
  have hbridge := integral_oddProfileAcrossJump_le_hyperbolicShiftSlice ha_pos ht hz₁ hz hz₂ hw
  have hsub_y : (∫ y in Ioo (t / 2) (3 * t / 2), hyperbolicShiftSlice a w z₂ y) ≤
      ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y := by
    have hF : Continuous (hyperbolicShiftSlice a w z₂) :=
      continuous_hyperbolicShiftSlice a hz₂0 hw
    refine setIntegral_mono_set (hF.integrableOn_Icc.mono_set Ioo_subset_Icc_self) ?_
      (Eventually.of_forall fun y hy => ⟨by linarith [hy.1], hy.2.trans_le hz₁⟩)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact hyperbolicShiftSlice_nonneg ha_pos hy.1 w
  calc 8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) *
        ((∫ x in Ioo (0 : ℝ) t, oddProfileCollarDiffSq a w t x) -
          2 * (∫ x in Ioo (0 : ℝ) (t / 2), oddProfileShiftJump a w t x))
      ≤ 8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) *
          (8 * Real.exp (4 * t) * ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileAcrossJump a w t x) :=
        mul_le_mul_of_nonneg_left hfull hc_nn
    _ = 8 * Real.exp (4 * t) *
          (8 * Real.sinh (t / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) *
            ∫ x in Ioo (0 : ℝ) (t / 2), oddProfileAcrossJump a w t x) := by ring
    _ ≤ 8 * Real.exp (4 * t) *
          (2 * ∫ y in Ioo (t / 2) (3 * t / 2), hyperbolicShiftSlice a w z₂ y) :=
        mul_le_mul_of_nonneg_left hbridge (by positivity)
    _ ≤ 8 * Real.exp (4 * t) *
          (2 * ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub_y zero_le_two) (by positivity)
    _ = _ := by ring

/-! ## Section 3: Support-Radius Synthesis & Exponentially Vanishing Budget `< ε < 1` -/

/-- Shift-independent low-prime numerator summing `Λ(d) d^{−1/2} · 2 e^{4 log d} / sinh((log d)/4)`
over `d < ⌊e^{2R}⌋ + 1`. -/
def hyperbolicLowPrimeNumerator (R : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (⌊Real.exp (2 * R)⌋₊ + 1),
    vonMangoldtAtom d * ((2 * Real.exp (4 * Real.log d)) / Real.sinh (Real.log d / 4))

theorem hyperbolicLowPrimeNumerator_nonneg (R : ℝ) :
    0 ≤ hyperbolicLowPrimeNumerator R := by
  unfold hyperbolicLowPrimeNumerator
  refine Finset.sum_nonneg fun d _ => mul_nonneg (vonMangoldtAtom_nonneg d) ?_
  have ht : 0 ≤ Real.log (d : ℝ) := Real.log_natCast_nonneg d
  exact div_nonneg (by positivity) (Real.sinh_nonneg_iff.mpr (by positivity))

/-- Shift-dependent continuum collar budget across a bridge window `(z₁, z₂) ⊆ [3R, a]`:
`hyperbolicCollarBudget R z₁ z₂ = hyperbolicLowPrimeNumerator R / (cosh(z₂/2) − cosh(z₁/2))`. -/
def hyperbolicCollarBudget (R z₁ z₂ : ℝ) : ℝ :=
  hyperbolicLowPrimeNumerator R / (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2))

theorem hyperbolicCollarBudget_nonneg (R : ℝ) {z₁ z₂ : ℝ} (hz₁ : 0 ≤ z₁) (hz : z₁ < z₂) :
    0 ≤ hyperbolicCollarBudget R z₁ z₂ := by
  unfold hyperbolicCollarBudget
  have hc : Real.cosh (z₁ / 2) < Real.cosh (z₂ / 2) :=
    strictMonoOn_cosh_Ici (mem_Ici.mpr (by positivity)) (mem_Ici.mpr (by linarith)) (by linarith)
  exact div_nonneg (hyperbolicLowPrimeNumerator_nonneg R) (sub_pos.mpr hc).le

/-- **All-Scale Prime-Collar Domination with Exponentially Decaying Hyperbolic Budget:**
For any `R ≥ 0`, bridge window `3R ≤ z₁ < z₂ ≤ a` with `3R + (log 2)/2 ≤ a`, even continuous
compactly supported `w` vanishing on `[R, ∞)`, and finite set `S` with `∀ d ∈ S, log d + R ≤ a`,
the entire prime-collar sum over `S` is paid by twice the direct prime jumps plus
`hyperbolicCollarBudget R z₁ z₂` times the hyperbolic continuum energy restricted to
`y ∈ (0, z₁)`, `s ∈ (0, z₂)`. -/
theorem sum_vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_hyperbolicBudget
    {a R z₁ z₂ : ℝ} (hR : 0 ≤ R) (hz₁ : 3 * R ≤ z₁) (hz : z₁ < z₂) (hz₂ : z₂ ≤ a)
    (ha_log2 : 3 * R + Real.log 2 / 2 ≤ a)
    (S : Finset ℕ) (hS : ∀ d ∈ S, Real.log d + R ≤ a)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hsupp : ∀ u, R ≤ u → w u = 0) :
    (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x)) ≤
      2 * (∑ d ∈ S, vonMangoldtAtom d *
        (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
      hyperbolicCollarBudget R z₁ z₂ *
        ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y := by
  have ha_pos : 0 < a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hc_lt : Real.cosh (z₁ / 2) < Real.cosh (z₂ / 2) :=
    strictMonoOn_cosh_Ici (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (by linarith)
  have hc_pos : 0 < Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2) := sub_pos.mpr hc_lt
  set ratio : ℕ → ℝ := fun d =>
    if Real.log d < 2 * R then
      ((2 * Real.exp (4 * Real.log d)) / Real.sinh (Real.log d / 4)) /
        (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2))
    else 0
  have hper_prime : ∀ d ∈ S,
      vonMangoldtAtom d *
          (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x) ≤
        2 * vonMangoldtAtom d *
          (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x) +
        (vonMangoldtAtom d * ratio d) *
          ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y := by
    intro d hd
    dsimp only [ratio]
    split_ifs with hlt
    · by_cases hd2 : 2 ≤ d
      · have hd1 : (1 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hd2)
        have ht_pos : 0 < Real.log (d : ℝ) := Real.log_pos hd1
        have hsh_pos : 0 < Real.sinh (Real.log d / 4) :=
          Real.sinh_pos_iff.mpr (by positivity)
        have h1 := integral_oddProfileCollarDiffSq_sub_two_direct_le_hyperbolicShiftSlice
          ht_pos.le (by linarith : 3 * Real.log d / 2 ≤ z₁) hz.le hz₂
          (by linarith : 3 * Real.log d / 2 + Real.log 2 / 2 ≤ a) hw
        have hint_full : IntegrableOn (oddProfileShiftJump a w (Real.log d)) (Ioi (0 : ℝ)) := by
          have hsub : HasCompactSupport (fun x : ℝ => w x - w (x + Real.log d)) :=
            hwc.sub (hwc.comp_homeomorph (Homeomorph.addRight (Real.log d)))
          have hsub2 : HasCompactSupport (fun x : ℝ => (w x - w (x + Real.log d)) ^ 2) := by
            rw [hasCompactSupport_iff_eventuallyEq] at hsub ⊢
            filter_upwards [hsub] with x hx; simp [hx]
          exact ((continuous_oddProfileShiftJump_right a (Real.log d) hw).integrable_of_hasCompactSupport
            hsub2.mul_left).integrableOn
        have hdir_mono : (∫ x in Ioo (0 : ℝ) (Real.log d / 2), oddProfileShiftJump a w (Real.log d) x) ≤
            ∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x := by
          refine setIntegral_mono_set hint_full ?_ (Eventually.of_forall fun x hx => hx.1)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact oddProfileShiftJump_nonneg_of_pos ha_pos (mem_Ioi.mp hx) ht_pos.le w
        set γ := 8 * Real.sinh (Real.log d / 4) * (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2))
        have hγ_pos : 0 < γ := mul_pos (mul_pos (by norm_num) hsh_pos) hc_pos
        have hdiv := (le_div_iff₀' hγ_pos).mpr h1
        have hmul := mul_le_mul_of_nonneg_left hdiv (vonMangoldtAtom_nonneg d)
        have hmul_dir := mul_le_mul_of_nonneg_left hdir_mono (vonMangoldtAtom_nonneg d)
        have halg : (16 * Real.exp (4 * Real.log d) *
            ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y) / γ =
            (((2 * Real.exp (4 * Real.log d)) / Real.sinh (Real.log d / 4)) /
              (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2))) *
              ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y := by
          dsimp [γ]
          field_simp [hsh_pos.ne', hc_pos.ne']
          ring
        rw [halg] at hmul
        linarith
      · have hvm0 : vonMangoldtAtom d = 0 := by unfold vonMangoldtAtom; exact if_neg hd2
        rw [hvm0]; simp
    · have hge : 2 * R ≤ Real.log d := not_lt.mp hlt
      have hmid := integral_oddProfileCollarDiffSq_le_two_Ioi_of_support_radius
        ha_pos (Real.log_natCast_nonneg d) hge (hS d hd) hw hwc hsupp
      have hmul := mul_le_mul_of_nonneg_left hmid (vonMangoldtAtom_nonneg d)
      linarith
  have hstep1 :
      (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x)) ≤
        2 * (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
        (∑ d ∈ S, vonMangoldtAtom d * ratio d) *
          ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d hd => ?_
    have h := hper_prime d hd
    linarith
  set N := ⌊Real.exp (2 * R)⌋₊ + 1
  have hbudget : (∑ d ∈ S, vonMangoldtAtom d * ratio d) ≤ hyperbolicCollarBudget R z₁ z₂ := by
    have hsub : (∑ d ∈ S, vonMangoldtAtom d * ratio d) =
        ∑ d ∈ S.filter (· < N), vonMangoldtAtom d * ratio d := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun d hdS hnot => ?_
      rw [Finset.mem_filter, not_and] at hnot
      have hdN : N ≤ d := not_lt.mp (hnot hdS)
      have hexp_le : Real.exp (2 * R) ≤ (d : ℝ) :=
        ((Nat.floor_lt (Real.exp_pos _).le).mp (Nat.lt_of_succ_le hdN)).le
      have hlog_ge : 2 * R ≤ Real.log (d : ℝ) := by
        rw [← Real.log_exp (2 * R)]
        exact Real.log_le_log (Real.exp_pos _) hexp_le
      dsimp [ratio]
      rw [if_neg (not_lt.mpr hlog_ge), mul_zero]
    rw [hsub]
    unfold hyperbolicCollarBudget hyperbolicLowPrimeNumerator
    rw [Finset.sum_div]
    have hle1 : (∑ d ∈ S.filter (· < N), vonMangoldtAtom d * ratio d) ≤
        ∑ d ∈ S.filter (· < N),
          (vonMangoldtAtom d * ((2 * Real.exp (4 * Real.log d)) / Real.sinh (Real.log d / 4))) /
            (Real.cosh (z₂ / 2) - Real.cosh (z₁ / 2)) := by
      refine Finset.sum_le_sum fun d _ => ?_
      dsimp [ratio]
      split_ifs
      · rw [← mul_div_assoc]
      · rw [mul_zero]
        exact div_nonneg (mul_nonneg (vonMangoldtAtom_nonneg d)
          (div_nonneg (by positivity)
            (Real.sinh_nonneg_iff.mpr (by positivity [Real.log_natCast_nonneg d])))) hc_pos.le
    refine hle1.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun d hd => Finset.mem_range.mpr (Finset.mem_filter.mp hd).2) fun d _ _ => ?_)
    exact div_nonneg (mul_nonneg (vonMangoldtAtom_nonneg d)
      (div_nonneg (by positivity)
        (Real.sinh_nonneg_iff.mpr (by positivity [Real.log_natCast_nonneg d])))) hc_pos.le
  have hint_nn : 0 ≤ ∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y :=
    setIntegral_nonneg measurableSet_Ioo fun y hy => hyperbolicShiftSlice_nonneg ha_pos hy.1 w
  exact hstep1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hbudget hint_nn))

/-- Comparison of the compact hyperbolic rectangle against the full 2D antisymmetric light-cone
integral on `(0, ∞)²`. -/
theorem integral_hyperbolicShiftSlice_le_continuum_lightCone
    {a z₁ z₂ : ℝ} (ha : 0 < a) (hz₂ : 0 ≤ z₂) {w : ℝ → ℝ} (hw : Continuous w)
    (hinner : ∀ y > 0, IntegrableOn (fun s : ℝ => lightConeOddIntegrand a w s y) (Ioi (0 : ℝ)))
    (houter : IntegrableOn
      (fun y : ℝ => ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y) (Ioi (0 : ℝ))) :
    (∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y) ≤
      ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y := by
  have hF : Continuous (hyperbolicShiftSlice a w z₂) := continuous_hyperbolicShiftSlice a hz₂ hw
  have hstep1 : (∫ y in Ioo (0 : ℝ) z₁, hyperbolicShiftSlice a w z₂ y) ≤
      ∫ y in Ioo (0 : ℝ) z₁, ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y := by
    refine setIntegral_mono_on (hF.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (houter.mono_set fun y hy => hy.1) measurableSet_Ioo fun y hy => ?_
    unfold hyperbolicShiftSlice
    have hc := continuous_hyperbolicShiftIntegrand_left a y hw
    have hsub1 : (∫ s in Ioo (0 : ℝ) z₂, hyperbolicShiftIntegrand a w s y) ≤
        ∫ s in Ioo (0 : ℝ) z₂, lightConeOddIntegrand a w s y :=
      setIntegral_mono_on (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
        ((hinner y hy.1).mono_set fun s hs => hs.1) measurableSet_Ioo
        fun s hs => hyperbolicShiftIntegrand_le_lightConeOddIntegrand ha hs.1 hy.1 w
    refine hsub1.trans (setIntegral_mono_set (hinner y hy.1) ?_
      (Eventually.of_forall fun s hs => hs.1))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact lightConeOddIntegrand_nonneg ha (mem_Ioi.mp hs) hy.1 w
  refine hstep1.trans (setIntegral_mono_set houter ?_
    (Eventually.of_forall fun y hy => hy.1))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact setIntegral_nonneg measurableSet_Ioi fun s hs =>
    lightConeOddIntegrand_nonneg ha (mem_Ioi.mp hs) (mem_Ioi.mp hy) w

/-- **Exponential vanishing of the hyperbolic collar budget as `z₂ → +∞`.**
For every support radius `R ≥ 0` and every `ε > 0` (in particular any sub-unit fraction `0 < ε < 1`),
there exists `A₀` such that for all `a ≥ A₀`, the interior bridge window `(3R, a − 2R)` has
`hyperbolicCollarBudget R (3 * R) (a - 2 * R) < ε`. -/
theorem exists_shift_hyperbolicCollarBudget_lt (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A₀ : ℝ, 5 * R + Real.log 2 / 2 < A₀ ∧
      ∀ a ≥ A₀, hyperbolicCollarBudget R (3 * R) (a - 2 * R) < ε := by
  set M := Real.cosh (3 * R / 2) + (hyperbolicLowPrimeNumerator R + 1) / ε
  have hnum_nn := hyperbolicLowPrimeNumerator_nonneg R
  have hM_gt : Real.cosh (3 * R / 2) < M := by
    dsimp [M]; linarith [div_pos (by linarith : 0 < hyperbolicLowPrimeNumerator R + 1) hε]
  set A₀ := max (5 * R + Real.log 2 / 2 + 1) (2 * R + 2 * Real.log (2 * M))
  refine ⟨A₀, lt_of_lt_of_le (by linarith) (le_max_left _ _), fun a ha => ?_⟩
  have ha2 : 2 * R + 2 * Real.log (2 * M) ≤ a := (le_max_right _ _).trans ha
  have hM_pos : 0 < M := lt_trans (Real.cosh_pos _) hM_gt
  have hexp_ge : 2 * M ≤ Real.exp ((a - 2 * R) / 2) := by
    rw [← Real.exp_log (mul_pos two_pos hM_pos)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hcosh_ge : M ≤ Real.cosh ((a - 2 * R) / 2) := by
    rw [Real.cosh_eq]
    have hexp_neg : 0 < Real.exp (-((a - 2 * R) / 2)) := Real.exp_pos _
    linarith
  have hden_gt : (hyperbolicLowPrimeNumerator R + 1) / ε ≤
      Real.cosh ((a - 2 * R) / 2) - Real.cosh (3 * R / 2) := by
    dsimp [M] at hcosh_ge; linarith
  have hden_pos : 0 < Real.cosh ((a - 2 * R) / 2) - Real.cosh (3 * R / 2) :=
    lt_of_lt_of_le (div_pos (by linarith) hε) hden_gt
  unfold hyperbolicCollarBudget
  rw [div_lt_iff₀ hden_pos]
  have hmul : hyperbolicLowPrimeNumerator R + 1 ≤
      ε * (Real.cosh ((a - 2 * R) / 2) - Real.cosh (3 * R / 2)) := by
    have := (div_le_iff₀ hε).mp hden_gt
    linarith
  linarith

/-- **Sub-Unit Obstacle B Domination Across `log d ≤ a - R`:**
For every support radius `R ≥ 0` and every `0 < ε` (in particular `ε = 1` or any `ε < 1`), there
exists `A₀` such that for all shifts `a ≥ A₀`, every finite set `S` of prime powers with
`∀ d ∈ S, log d + R ≤ a`, and every even continuous compactly supported `w` supported in `(-R, R)`
with integrable light-cone continuum fibers, the entire prime-collar sum over `S` is paid by twice
the direct prime jumps plus at most `ε` times the 2D antisymmetric light-cone integral. -/
theorem exists_shift_subunit_collar_domination {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ A₀ : ℝ, 5 * R + Real.log 2 / 2 < A₀ ∧ ∀ a ≥ A₀,
      ∀ (S : Finset ℕ), (∀ d ∈ S, Real.log d + R ≤ a) →
      ∀ (w : ℝ → ℝ), Continuous w → HasCompactSupport w → (∀ u, R ≤ u → w u = 0) →
        (∀ y > 0, IntegrableOn (fun s : ℝ => lightConeOddIntegrand a w s y) (Ioi (0 : ℝ))) →
        IntegrableOn (fun y : ℝ => ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y)
          (Ioi (0 : ℝ)) →
        (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x)) ≤
        2 * (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
        ε * ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y := by
  obtain ⟨A₀, hA₀, hlt⟩ := exists_shift_hyperbolicCollarBudget_lt R hε
  refine ⟨A₀, hA₀, fun a ha S hS w hw hwc hsupp hinner houter => ?_⟩
  have ha_pos : 0 < a := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hz : 3 * R < a - 2 * R := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h1 := sum_vonMangoldt_oddProfileCollarDiffSq_le_two_Ioi_add_hyperbolicBudget
    hR le_rfl hz (by linarith) (by linarith) S hS hw hwc hsupp
  have h2 := integral_hyperbolicShiftSlice_le_continuum_lightCone (z₁ := 3 * R)
    ha_pos (by linarith : 0 ≤ a - 2 * R) hw hinner houter
  have hb_nn := hyperbolicCollarBudget_nonneg R (by positivity) hz
  have hb_le := (hlt a ha).le
  have hcont_nn : 0 ≤ ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y :=
    setIntegral_nonneg measurableSet_Ioi fun y hy =>
      setIntegral_nonneg measurableSet_Ioi fun s hs =>
        lightConeOddIntegrand_nonneg ha_pos (mem_Ioi.mp hs) (mem_Ioi.mp hy) w
  calc (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioo (0 : ℝ) (Real.log d), oddProfileCollarDiffSq a w (Real.log d) x))
      ≤ 2 * (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
        hyperbolicCollarBudget R (3 * R) (a - 2 * R) *
          ∫ y in Ioo (0 : ℝ) (3 * R), hyperbolicShiftSlice a w (a - 2 * R) y := h1
    _ ≤ 2 * (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
        hyperbolicCollarBudget R (3 * R) (a - 2 * R) *
          ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 hb_nn)
    _ ≤ 2 * (∑ d ∈ S, vonMangoldtAtom d *
          (∫ x in Ioi (0 : ℝ), oddProfileShiftJump a w (Real.log d) x)) +
        ε * ∫ y in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), lightConeOddIntegrand a w s y :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hb_le hcont_nn)

end GaloisForLFunctions.TransHorizonIncidenceMechanics

end
