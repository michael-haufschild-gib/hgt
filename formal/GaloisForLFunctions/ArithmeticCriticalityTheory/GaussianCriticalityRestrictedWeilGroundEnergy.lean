import GaloisForLFunctions.ArithmeticCriticalityTheory.WindowGaugeLogarithmicGroundEnergyFloor
import GaloisForLFunctions.ArithmeticCriticalityTheory.OddProfileOriginFailure
import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaLayerBounds
import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaFarTail

/-!
# Gaussian criticality of the restricted Weil operators

Along the plateau truncations `Φ u_L` of Riemann's kernel the full zero form tends to `0`. In the
`Φ`-gauge, `Ẑ(Φu) = J_Φ(u) − ∫ u² Φ cosh(x/2) + 2(∫ Φ u cosh(x/2))² − 2(∫ Φ u sinh(x/2))²`
(`markovEnergy_phiDoob_translateSpan_mul_eq`), and `∫ Φ cosh(x/2) = 1/2`. Two exact cancellations
leave only tail quantities:

* the potential and the even pole term combine to `2(∫ Φ (1 − u_L) cosh(x/2))²` at most
  (`u² ≥ 2u − 1`);
* every jump of `J_Φ(u_L)` with a nonzero increment has one endpoint beyond `L`, and the prime jumps
  issuing from a point `x` carry total weight `Σ_n Λ(n) n^{−1/2}(Φ(x + log n) + Φ(x − log n)) ≤
  cosh(x/2) + κ` (`primeKernelSum_le`).

Hence `Ẑ(Φu_L) ≤ K τ(L) + 2τ(L)²` with the tail weight `τ(L) = ∫_{|x|>L} Φ(x)(cosh(x/2) + κ)`
(`fullZeroForm_thetaPlateau_le`), and `τ(L) ≤ C e^{L} Φ(L)` (`tailWeight_le`). Since `Φ u_L` is a
smooth source supported in `[−L−1, L+1]`:

* **Gaussian upper bound** (`exists_ccmRestrictedWeilGroundEnergy_le_doubleExp`): the restricted Weil
  ground energy satisfies `μ(A) ≤ K exp((11/2)A − π e^{2(A−2)})` for `A ≥ 3`, unconditionally.
* **Gaussian criticality under RH** (`ccmRestrictedWeilGroundEnergy_gaussian_of_riemannHypothesis`):
  `0 ≤ μ(A) ≤ K exp((11/2)A − π e^{2(A−2)})`.

The approach to criticality is doubly exponential, at the rate of the Gaussian tail of Riemann's
kernel; without RH the ground energy instead decreases to `−∞` exponentially.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The prime-shift constant and the tail weight -/

/-- The constant `κ` with `Σ_n Λ(n) n^{−1/2}(Φ(x + log n) + Φ(x − log n)) ≤ cosh(x/2) + κ`. -/
def primeShiftConstant : ℝ :=
  |2 * |archConstantReal| * riemannKernelReal 0 + 2 * gammaSourceBoundMass|

theorem primeShiftConstant_nonneg : 0 ≤ primeShiftConstant := abs_nonneg _

theorem primeKernelSum_le_cosh_add (x : ℝ) :
    primeKernelSum x ≤ Real.cosh (x / 2) + primeShiftConstant := by
  have h := primeKernelSum_le x
  have := le_abs_self (2 * |archConstantReal| * riemannKernelReal 0 + 2 * gammaSourceBoundMass)
  unfold primeShiftConstant
  linarith

theorem one_le_cosh_add (x : ℝ) : 1 ≤ Real.cosh (x / 2) + primeShiftConstant := by
  linarith [Real.one_le_cosh (x / 2), primeShiftConstant_nonneg]

/-- The tail `Φ · 1_{|x| > L}` of Riemann's kernel. -/
def kernelTail (L x : ℝ) : ℝ := Set.indicator {y : ℝ | L < |y|} riemannKernelReal x

/-- The tail weight `τ(L) = ∫_{|x|>L} Φ(x)(cosh(x/2) + κ)`. -/
def tailWeight (L : ℝ) : ℝ := ∫ x, kernelTail L x * (Real.cosh (x / 2) + primeShiftConstant)

theorem measurableSet_tail (L : ℝ) : MeasurableSet {y : ℝ | L < |y|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

theorem kernelTail_nonneg (L x : ℝ) : 0 ≤ kernelTail L x :=
  Set.indicator_nonneg (fun y _ => (riemannKernelReal_pos y).le) x

theorem kernelTail_le (L x : ℝ) : kernelTail L x ≤ riemannKernelReal x :=
  Set.indicator_le_self' (fun y _ => (riemannKernelReal_pos y).le) x

theorem kernelTail_eq_zero {L x : ℝ} (hx : |x| ≤ L) : kernelTail L x = 0 :=
  Set.indicator_of_notMem (not_lt.mpr hx) _

theorem kernelTail_eq {L x : ℝ} (hx : L < |x|) : kernelTail L x = riemannKernelReal x :=
  Set.indicator_of_mem hx _

theorem measurable_kernelTail (L : ℝ) : Measurable (kernelTail L) :=
  continuous_riemannKernelReal.measurable.indicator (measurableSet_tail L)

theorem integrable_kernelTail (L : ℝ) : Integrable (kernelTail L) :=
  integrable_riemannKernelReal.indicator (measurableSet_tail L)

theorem continuous_cosh_add : Continuous fun x : ℝ => Real.cosh (x / 2) + primeShiftConstant :=
  (Real.continuous_cosh.comp (continuous_id.div_const 2)).add continuous_const

theorem integrable_riemannKernelReal_mul_cosh :
    Integrable fun x => riemannKernelReal x * Real.cosh (x / 2) := by
  have h1 := integrable_riemannKernelReal_mul_exp (1 / 2)
  have h2 := integrable_riemannKernelReal_mul_exp (-(1 / 2))
  refine ((h1.add h2).div_const 2).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply, Real.cosh_eq]
  ring_nf

theorem integrable_riemannKernelReal_mul_cosh_add :
    Integrable fun x => riemannKernelReal x * (Real.cosh (x / 2) + primeShiftConstant) := by
  refine (integrable_riemannKernelReal_mul_cosh.add
    (integrable_riemannKernelReal.mul_const primeShiftConstant)).congr
      (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  ring

theorem integrable_kernelTail_mul (L : ℝ) :
    Integrable fun x => kernelTail L x * (Real.cosh (x / 2) + primeShiftConstant) := by
  refine integrable_riemannKernelReal_mul_cosh_add.mono'
    ((measurable_kernelTail L).mul continuous_cosh_add.measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hw := (zero_lt_one.trans_le (one_le_cosh_add x)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kernelTail_nonneg L x) hw)]
  exact mul_le_mul_of_nonneg_right (kernelTail_le L x) hw

theorem tailWeight_nonneg (L : ℝ) : 0 ≤ tailWeight L :=
  integral_nonneg fun x => mul_nonneg (kernelTail_nonneg L x)
    (zero_lt_one.trans_le (one_le_cosh_add x)).le

theorem integral_kernelTail_le_tailWeight (L : ℝ) : ∫ x, kernelTail L x ≤ tailWeight L :=
  integral_mono (integrable_kernelTail L) (integrable_kernelTail_mul L) fun x =>
    le_mul_of_one_le_right (kernelTail_nonneg L x) (one_le_cosh_add x)

theorem tailWeight_le_total (L : ℝ) :
    tailWeight L ≤ ∫ x, riemannKernelReal x * (Real.cosh (x / 2) + primeShiftConstant) :=
  integral_mono (integrable_kernelTail_mul L) integrable_riemannKernelReal_mul_cosh_add fun x =>
    mul_le_mul_of_nonneg_right (kernelTail_le L x) (zero_lt_one.trans_le (one_le_cosh_add x)).le

/-- **The tail weight is a Gaussian tail**: `τ(L) ≤ (1 + κ) E e^{L} Φ(L)` for `L ≥ ½ log 2`, with
`E = ∫ e^{−|x|/2}`. -/
theorem tailWeight_le {L : ℝ} (hL : Real.log 2 / 2 ≤ L) :
    tailWeight L ≤ (1 + primeShiftConstant) * (∫ x : ℝ, Real.exp (-|1 / 2 * x|)) *
      (Real.exp L * riemannKernelReal L) := by
  have hE : Integrable fun x : ℝ => Real.exp (-|1 / 2 * x|) :=
    integrable_exp_neg_abs.comp_mul_left' (by norm_num)
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hκ := primeShiftConstant_nonneg
  have hΦL := (riemannKernelReal_pos L).le
  rw [show (1 + primeShiftConstant) * (∫ x : ℝ, Real.exp (-|1 / 2 * x|)) *
      (Real.exp L * riemannKernelReal L) = ∫ x : ℝ, (1 + primeShiftConstant) *
        (Real.exp L * riemannKernelReal L) * Real.exp (-|1 / 2 * x|) by
    rw [integral_const_mul]; ring]
  refine integral_mono (integrable_kernelTail_mul L) (hE.const_mul _) fun x => ?_
  by_cases hx : |x| ≤ L
  · simp only [kernelTail_eq_zero hx, zero_mul]
    positivity
  · rw [kernelTail_eq (not_le.mp hx), ← riemannKernelReal_abs' x]
    have hxL : L ≤ |x| := (not_le.mp hx).le
    have h1 := riemannKernelReal_le_mul_exp hL hxL
    have hpi : 1 ≤ Real.pi * Real.exp (2 * L) := by
      have := Real.one_le_exp (by linarith : 0 ≤ 2 * L)
      nlinarith [Real.pi_gt_three]
    have h2 : Real.exp (-(Real.pi * Real.exp (2 * L) * (|x| - L))) ≤ Real.exp (L - |x|) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h3 : Real.cosh (x / 2) + primeShiftConstant ≤
        (1 + primeShiftConstant) * Real.exp (|x| / 2) := by
      have he := Real.one_le_exp (by positivity : 0 ≤ |x| / 2)
      have hc : Real.cosh (x / 2) ≤ Real.exp (|x| / 2) := by
        rw [Real.cosh_eq]
        have a1 : Real.exp (x / 2) ≤ Real.exp (|x| / 2) :=
          Real.exp_le_exp.mpr (by linarith [le_abs_self x])
        have a2 : Real.exp (-(x / 2)) ≤ Real.exp (|x| / 2) :=
          Real.exp_le_exp.mpr (by linarith [neg_abs_le x])
        linarith
      nlinarith
    have hΦx : riemannKernelReal |x| ≤ riemannKernelReal L * Real.exp (L - |x|) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hΦL)
    have habs : Real.exp (-|1 / 2 * x|) = Real.exp (-(|x| / 2)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring_nf
    rw [habs]
    calc riemannKernelReal |x| * (Real.cosh (x / 2) + primeShiftConstant)
        ≤ (riemannKernelReal L * Real.exp (L - |x|)) *
            ((1 + primeShiftConstant) * Real.exp (|x| / 2)) :=
          mul_le_mul hΦx h3 (zero_lt_one.trans_le (one_le_cosh_add x)).le (by positivity)
      _ = (1 + primeShiftConstant) * (Real.exp L * riemannKernelReal L) *
            Real.exp (-(|x| / 2)) := by
          rw [show L - |x| = L + -|x| by ring, Real.exp_add]
          have e : Real.exp (-|x|) * Real.exp (|x| / 2) = Real.exp (-(|x| / 2)) := by
            rw [← Real.exp_add]; ring_nf
          calc riemannKernelReal L * (Real.exp L * Real.exp (-|x|)) *
                ((1 + primeShiftConstant) * Real.exp (|x| / 2))
              = (1 + primeShiftConstant) * (Real.exp L * riemannKernelReal L) *
                  (Real.exp (-|x|) * Real.exp (|x| / 2)) := by ring
            _ = _ := by rw [e]

/-! ### The jump energy of `Φ u_L` -/

section Jump

variable {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
  (hΛ : ∀ L x y : ℝ, |smoothPlateau L y - smoothPlateau L x| ≤ Λ * |y - x|)

theorem signedShiftJump_riemannKernel_nonneg (L t x : ℝ) :
    0 ≤ signedShiftJump riemannKernelReal (smoothPlateau L) t x := by
  unfold signedShiftJump
  exact mul_nonneg (mul_nonneg (riemannKernelReal_pos x).le (riemannKernelReal_pos _).le)
    (sq_nonneg _)

include hΛ in
/-- Where the plateau varies, one endpoint lies in the tail. -/
theorem signedShiftJump_riemannKernel_le (L t x : ℝ) :
    signedShiftJump riemannKernelReal (smoothPlateau L) t x ≤
      min 1 (Λ ^ 2 * t ^ 2) * (kernelTail L x * riemannKernelReal (x + t) +
        riemannKernelReal x * kernelTail L (x + t)) := by
  unfold signedShiftJump
  obtain ⟨d, hd⟩ : ∃ d, d = smoothPlateau L x - smoothPlateau L (x + t) := ⟨_, rfl⟩
  rw [← hd]
  have hd1 : d ^ 2 ≤ 1 := by
    have h := abs_smoothPlateau_sub_le_one L x (x + t)
    rw [← hd] at h
    nlinarith [abs_nonneg d, sq_abs d]
  have hdΛ : d ^ 2 ≤ Λ ^ 2 * t ^ 2 := by
    have h := hΛ L (x + t) x
    rw [show x - (x + t) = -t by ring, abs_neg, ← hd] at h
    calc d ^ 2 = |d| ^ 2 := (sq_abs d).symm
      _ ≤ (Λ * |t|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = Λ ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
  have hm0 : 0 ≤ min 1 (Λ ^ 2 * t ^ 2) := le_min zero_le_one (by positivity)
  have hmin : d ^ 2 ≤ min 1 (Λ ^ 2 * t ^ 2) := le_min hd1 hdΛ
  have hΦx := riemannKernelReal_pos x
  have hΦt := riemannKernelReal_pos (x + t)
  have hk1 := kernelTail_nonneg L x
  have hk2 := kernelTail_nonneg L (x + t)
  have hprod := mul_le_mul_of_nonneg_left hmin (mul_pos hΦx hΦt).le
  by_cases hx : |x| ≤ L
  · by_cases ht : |x + t| ≤ L
    · have h0 : d = 0 := by rw [hd, smoothPlateau_eq_one hx, smoothPlateau_eq_one ht, sub_self]
      rw [h0]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · rw [kernelTail_eq (not_le.mp ht)]
      nlinarith [mul_nonneg (mul_nonneg hm0 hk1) hΦt.le]
  · rw [kernelTail_eq (not_le.mp hx)]
    nlinarith [mul_nonneg (mul_nonneg hm0 hΦx.le) hk2]

theorem integrable_kernelTail_mul_shift (L t : ℝ) :
    Integrable fun x => kernelTail L x * riemannKernelReal (x + t) := by
  refine ((integrable_kernelTail L).const_mul (riemannKernelReal 0)).mono'
    ((measurable_kernelTail L).mul (continuous_riemannKernelReal.comp
      (continuous_id.add continuous_const)).measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (kernelTail_nonneg L x)
    (riemannKernelReal_pos _).le), mul_comm]
  exact mul_le_mul_of_nonneg_right (riemannKernelReal_le_zero_point _) (kernelTail_nonneg L x)

/-- Reflecting the second endpoint: `∫ Φ(x) τ_L(x + t) = ∫ τ_L(y) Φ(y − t)`. -/
theorem integral_mul_kernelTail_shift (L t : ℝ) :
    ∫ x, riemannKernelReal x * kernelTail L (x + t) =
      ∫ x, kernelTail L x * riemannKernelReal (x - t) := by
  rw [← integral_add_right_eq_self (fun y => kernelTail L y * riemannKernelReal (y - t)) t]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right]
  ring

include hΛ in
theorem integral_signedShiftJump_riemannKernel_le (L t : ℝ) :
    ∫ x, signedShiftJump riemannKernelReal (smoothPlateau L) t x ≤
      min 1 (Λ ^ 2 * t ^ 2) * ((∫ x, kernelTail L x * riemannKernelReal (x + t)) +
        ∫ x, kernelTail L x * riemannKernelReal (x - t)) := by
  have hi1 := integrable_kernelTail_mul_shift L t
  have hi2 : Integrable fun x => riemannKernelReal x * kernelTail L (x + t) := by
    refine (((integrable_kernelTail L).comp_add_right t).const_mul (riemannKernelReal 0)).mono'
      (continuous_riemannKernelReal.measurable.mul ((measurable_kernelTail L).comp
        (measurable_id.add_const t))).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (riemannKernelReal_pos x).le
      (kernelTail_nonneg L _))]
    exact mul_le_mul_of_nonneg_right (riemannKernelReal_le_zero_point x) (kernelTail_nonneg L _)
  rw [← integral_mul_kernelTail_shift, ← integral_add hi1 hi2, ← integral_const_mul]
  exact integral_mono_of_nonneg
    (Eventually.of_forall fun x => signedShiftJump_riemannKernel_nonneg L t x)
    ((hi1.add hi2).const_mul _)
    (Eventually.of_forall fun x => signedShiftJump_riemannKernel_le hΛ L t x)

theorem shift_tails_le (L t : ℝ) :
    (∫ x, kernelTail L x * riemannKernelReal (x + t)) +
        ∫ x, kernelTail L x * riemannKernelReal (x - t) ≤
      2 * riemannKernelReal 0 * ∫ x, kernelTail L x := by
  have hb : ∀ s, ∫ x, kernelTail L x * riemannKernelReal (x + s) ≤
      riemannKernelReal 0 * ∫ x, kernelTail L x := fun s => by
    rw [← integral_const_mul]
    exact integral_mono (integrable_kernelTail_mul_shift L s)
      ((integrable_kernelTail L).const_mul _) fun x => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (riemannKernelReal_le_zero_point _)
          (kernelTail_nonneg L x)
  have h2 := hb (-t)
  simp only [← sub_eq_add_neg] at h2
  linarith [hb t]

theorem min_le_mul_self {t : ℝ} (ht : 0 < t) : min 1 (Λ ^ 2 * t ^ 2) ≤ (1 + Λ ^ 2) * t := by
  rcases le_or_gt t 1 with h1 | h1
  · have : t ^ 2 ≤ t := by nlinarith
    calc min 1 (Λ ^ 2 * t ^ 2) ≤ Λ ^ 2 * t ^ 2 := min_le_right _ _
      _ ≤ Λ ^ 2 * t := mul_le_mul_of_nonneg_left this (sq_nonneg _)
      _ ≤ (1 + Λ ^ 2) * t := by nlinarith
  · calc min 1 (Λ ^ 2 * t ^ 2) ≤ 1 := min_le_left _ _
      _ ≤ (1 + Λ ^ 2) * t := by nlinarith [sq_nonneg Λ]

include hΛ in
/-- The archimedean jumps: `≤ (1 + Λ²) (∫ ω t) · 2Φ(0) ∫ τ_L`. -/
theorem archJump_riemannKernel_le (L : ℝ) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x, signedShiftJump riemannKernelReal (smoothPlateau L) t x) ≤
      (1 + Λ ^ 2) * archFirstMoment * (2 * riemannKernelReal 0 * ∫ x, kernelTail L x) := by
  have hB0 : 0 ≤ 2 * riemannKernelReal 0 * ∫ x, kernelTail L x :=
    mul_nonneg (by have := riemannKernelReal_pos 0; positivity)
      (integral_nonneg (kernelTail_nonneg L))
  calc (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x, signedShiftJump riemannKernelReal (smoothPlateau L) t x)
      ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * t *
          ((1 + Λ ^ 2) * (2 * riemannKernelReal 0 * ∫ x, kernelTail L x)) := by
        refine integral_mono_of_nonneg ?_ (integrableOn_archLevyDensity_mul_id.mul_const _) ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg (archLevyDensity_pos ht).le
            (integral_nonneg fun x => signedShiftJump_riemannKernel_nonneg L t x)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have hω := (archLevyDensity_pos ht).le
          have h1 := integral_signedShiftJump_riemannKernel_le hΛ L t
          have h2 := shift_tails_le L t
          have hm0 : 0 ≤ min 1 (Λ ^ 2 * t ^ 2) := le_min zero_le_one (by positivity)
          have h3 := min_le_mul_self (Λ := Λ) ht
          calc archLevyDensity t * ∫ x, signedShiftJump riemannKernelReal (smoothPlateau L) t x
              ≤ archLevyDensity t * (min 1 (Λ ^ 2 * t ^ 2) *
                  (2 * riemannKernelReal 0 * ∫ x, kernelTail L x)) :=
                mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hm0)) hω
            _ ≤ archLevyDensity t * ((1 + Λ ^ 2) * t *
                  (2 * riemannKernelReal 0 * ∫ x, kernelTail L x)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hB0) hω
            _ = _ := by ring
    _ = (1 + Λ ^ 2) * archFirstMoment * (2 * riemannKernelReal 0 * ∫ x, kernelTail L x) := by
        rw [integral_mul_const]
        unfold archFirstMoment
        ring

include hΛ in
/-- The prime jumps: `≤ τ(L)`, through `Σ_n Λ(n) n^{−1/2}(Φ(x + log n) + Φ(x − log n)) ≤ cosh(x/2) + κ`. -/
theorem primeJump_riemannKernel_le (L : ℝ) :
    (∑' n : ℕ, vonMangoldtAtom n *
        ∫ x, signedShiftJump riemannKernelReal (smoothPlateau L) (Real.log n) x) ≤
      tailWeight L := by
  refine tsum_le_of_sum_le' (tailWeight_nonneg L) fun s => ?_
  have hint : ∀ n : ℕ, Integrable fun x => kernelTail L x *
      (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)) := fun n => by
    have h := (integrable_kernelTail_mul_shift L (Real.log n)).add
      (integrable_kernelTail_mul_shift L (-Real.log n))
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, ← sub_eq_add_neg]
    ring
  calc ∑ n ∈ s, vonMangoldtAtom n *
        ∫ x, signedShiftJump riemannKernelReal (smoothPlateau L) (Real.log n) x
      ≤ ∑ n ∈ s, ∫ x, vonMangoldtAtom n * (kernelTail L x *
          (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
        have h1 := integral_signedShiftJump_riemannKernel_le hΛ L (Real.log n)
        have hT : 0 ≤ (∫ x, kernelTail L x * riemannKernelReal (x + Real.log n)) +
            ∫ x, kernelTail L x * riemannKernelReal (x - Real.log n) :=
          add_nonneg (integral_nonneg fun x => mul_nonneg (kernelTail_nonneg L x)
            (riemannKernelReal_pos _).le) (integral_nonneg fun x => mul_nonneg
              (kernelTail_nonneg L x) (riemannKernelReal_pos _).le)
        have h2 : (∫ x, kernelTail L x * (riemannKernelReal (x + Real.log n) +
            riemannKernelReal (x - Real.log n))) =
            (∫ x, kernelTail L x * riemannKernelReal (x + Real.log n)) +
              ∫ x, kernelTail L x * riemannKernelReal (x - Real.log n) := by
          rw [← integral_add (integrable_kernelTail_mul_shift L _)
            (integrable_kernelTail_mul_shift L (-Real.log n) |>.congr
              (Eventually.of_forall fun x => by simp only [← sub_eq_add_neg]))]
          congr 1
          funext x
          ring
        rw [h2]
        exact h1.trans (mul_le_of_le_one_left hT (min_le_left _ _))
    _ = ∫ x, ∑ n ∈ s, vonMangoldtAtom n * (kernelTail L x *
          (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n))) :=
        (integral_finsetSum s fun n _ => (hint n).const_mul _).symm
    _ ≤ tailWeight L := by
        refine integral_mono (integrable_finsetSum s fun n _ => (hint n).const_mul _)
          (integrable_kernelTail_mul L) fun x => ?_
        have hk := kernelTail_nonneg L x
        have hpart : ∑ n ∈ s, vonMangoldtAtom n *
            (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)) ≤
              primeKernelSum x :=
          Summable.sum_le_tsum s (fun n _ => mul_nonneg (vonMangoldtAtom_nonneg n)
            (add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le))
            (summable_primeKernelSum x)
        calc ∑ n ∈ s, vonMangoldtAtom n * (kernelTail L x *
              (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)))
            = kernelTail L x * ∑ n ∈ s, vonMangoldtAtom n *
                (riemannKernelReal (x + Real.log n) + riemannKernelReal (x - Real.log n)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun n _ => by ring
          _ ≤ kernelTail L x * (Real.cosh (x / 2) + primeShiftConstant) :=
              mul_le_mul_of_nonneg_left (hpart.trans (primeKernelSum_le_cosh_add x)) hk

end Jump

/-! ### The zero form along the plateaus -/

/-- **`Ẑ(Φ u_L)` is controlled by the tail weight**: `Ẑ(Φu_L) ≤ K τ(L) + 2τ(L)²`. -/
theorem exists_fullZeroForm_thetaPlateau_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      fullZeroForm (thetaPlateau L) ≤ K * tailWeight L + 2 * tailWeight L ^ 2 := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_smoothPlateau_lipschitz
  have hΦ0 := riemannKernelReal_pos 0
  refine ⟨(1 + Λ ^ 2) * archFirstMoment * (2 * riemannKernelReal 0) + 1,
    by have := archFirstMoment_nonneg; positivity, fun L => ?_⟩
  -- the representation in the `Φ`-gauge
  have hrep := markovEnergy_phiDoob_translateSpan_mul_eq (Finset.univ : Finset Unit) (fun _ => 1)
    (fun _ => 0) (contDiff_smoothPlateau L) (hasCompactSupport_smoothPlateau L)
  have hT1 : ∀ y, translateSpan (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => 0) y = 1 :=
    fun y => by simp [translateSpan, translateGroundState, (riemannKernelReal_pos y).ne']
  have hS1 : ∀ x, translateSource (Finset.univ : Finset Unit) (fun _ => 1) (fun _ => 0) x =
      -Real.cosh (x / 2) := fun x => by
    simp [translateSource, translateCoshCoefficient, translateSinhCoefficient]
  simp only [hT1, hS1, one_mul, mul_one] at hrep
  have hJ : signedJumpEnergy riemannKernelReal (smoothPlateau L) ≤
      (1 + Λ ^ 2) * archFirstMoment * (2 * riemannKernelReal 0 * ∫ x, kernelTail L x) +
        tailWeight L := by
    unfold signedJumpEnergy
    exact add_le_add (archJump_riemannKernel_le hΛ L) (primeJump_riemannKernel_le hΛ L)
  -- the potential and the even pole term
  set u := smoothPlateau L with hu
  have hu0 : ∀ x, 0 ≤ u x := smoothPlateau_nonneg L
  have hu1 : ∀ x, u x ≤ 1 := smoothPlateau_le_one L
  have hIc := integrable_riemannKernelReal_mul_cosh
  have hiu : Integrable fun x => riemannKernelReal x * u x * Real.cosh (x / 2) :=
    hIc.mono' ((continuous_riemannKernelReal.mul (contDiff_smoothPlateau L).continuous).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        have hc := (Real.cosh_pos (x / 2)).le
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (riemannKernelReal_pos x).le
          (hu0 x)) hc)]
        have := mul_le_mul_of_nonneg_left (hu1 x) (riemannKernelReal_pos x).le
        nlinarith)
  have hiu2 : Integrable fun x => u x ^ 2 * riemannKernelReal x * Real.cosh (x / 2) :=
    hIc.mono' (((contDiff_smoothPlateau L).continuous.pow 2).mul continuous_riemannKernelReal
      |>.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        have hc := (Real.cosh_pos (x / 2)).le
        have hΦ := (riemannKernelReal_pos x).le
        have h2 : u x ^ 2 ≤ 1 := by nlinarith [hu0 x, hu1 x]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [mul_nonneg hΦ hc])
  set C := evenPoleMoment (thetaPlateau L) with hCdef
  have hC : C = ∫ x, riemannKernelReal x * u x * Real.cosh (x / 2) := rfl
  have hhalf := integral_riemannKernelReal_cosh_half
  -- `∫ u² Φ cosh ≥ 2C − 1/2`
  have hpot : 2 * C - 1 / 2 ≤ ∫ x, u x ^ 2 * riemannKernelReal x * Real.cosh (x / 2) := by
    have hlin : (∫ x, (2 * (riemannKernelReal x * u x * Real.cosh (x / 2)) -
        riemannKernelReal x * Real.cosh (x / 2))) = 2 * C - 1 / 2 := by
      rw [integral_sub (hiu.const_mul 2) hIc, integral_const_mul, hhalf, hC]
    rw [← hlin]
    refine integral_mono ((hiu.const_mul 2).sub hIc) hiu2 fun x => ?_
    have hc := (Real.cosh_pos (x / 2)).le
    have hΦ := (riemannKernelReal_pos x).le
    have := mul_nonneg (mul_nonneg hΦ hc) (sq_nonneg (u x - 1))
    simp only
    nlinarith
  -- `0 ≤ 1/2 − C ≤ τ(L)`
  have hgap : (1 : ℝ) / 2 - C = ∫ x, riemannKernelReal x * (1 - u x) * Real.cosh (x / 2) := by
    rw [hC, ← hhalf, ← integral_sub hIc hiu]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hgap0 : 0 ≤ (1 : ℝ) / 2 - C := by
    rw [hgap]
    exact integral_nonneg fun x => mul_nonneg (mul_nonneg (riemannKernelReal_pos x).le
      (by linarith [hu1 x])) (Real.cosh_pos _).le
  have hgapτ : (1 : ℝ) / 2 - C ≤ tailWeight L := by
    rw [hgap]
    refine integral_mono (hIc.sub hiu |>.congr (Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]; ring)) (integrable_kernelTail_mul L) fun x => ?_
    have hc := (Real.cosh_pos (x / 2)).le
    by_cases hx : |x| ≤ L
    · simp only [hu, smoothPlateau_eq_one hx, sub_self, mul_zero, zero_mul,
        kernelTail_eq_zero hx]
      rfl
    · rw [kernelTail_eq (not_le.mp hx)]
      have hΦ := (riemannKernelReal_pos x).le
      have h1 : 1 - u x ≤ 1 := by linarith [hu0 x]
      have h2 : 0 ≤ 1 - u x := by linarith [hu1 x]
      have hκ := primeShiftConstant_nonneg
      nlinarith [mul_le_mul_of_nonneg_left h1 hΦ, mul_nonneg hΦ hc, mul_nonneg hΦ hκ,
        mul_nonneg (mul_nonneg hΦ h2) hc]
  have hkτ := integral_kernelTail_le_tailWeight L
  have hτ0 := tailWeight_nonneg L
  -- assemble
  have hZ : fullZeroForm (thetaPlateau L) ≤
      signedJumpEnergy riemannKernelReal u + 2 * ((1 : ℝ) / 2 - C) ^ 2 := by
    unfold fullZeroForm
    have hm : markovEnergy (fun x => (thetaPlateau L x : ℂ)) =
        signedJumpEnergy riemannKernelReal u +
          ∫ x, u x ^ 2 * riemannKernelReal x * -Real.cosh (x / 2) := hrep
    have hneg : (∫ x, u x ^ 2 * riemannKernelReal x * -Real.cosh (x / 2)) =
        -∫ x, u x ^ 2 * riemannKernelReal x * Real.cosh (x / 2) := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    rw [hm, hneg, ← hCdef]
    nlinarith [sq_nonneg (oddPoleMoment (thetaPlateau L))]
  have hsq : ((1 : ℝ) / 2 - C) ^ 2 ≤ tailWeight L ^ 2 := pow_le_pow_left₀ hgap0 hgapτ 2
  have hJ' : signedJumpEnergy riemannKernelReal u ≤
      ((1 + Λ ^ 2) * archFirstMoment * (2 * riemannKernelReal 0) + 1) * tailWeight L := by
    have hA := archFirstMoment_nonneg
    have hcoef : 0 ≤ (1 + Λ ^ 2) * archFirstMoment * (2 * riemannKernelReal 0) := by positivity
    have := mul_le_mul_of_nonneg_left hkτ hcoef
    nlinarith
  linarith

/-! ### The Rayleigh bound and the Gaussian decay -/

/-- A real smooth source bounds the restricted Weil ground energy above by its Rayleigh quotient. -/
theorem ccmRestrictedWeilGroundEnergy_le_fullZeroForm_div {A : SuzukiPositiveAperture}
    {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFs : tsupport F ⊆ Ioo (-A.1) A.1) (hpos : 0 < ∫ x, F x ^ 2) :
    ccmRestrictedWeilGroundEnergy A ≤ fullZeroForm F / ∫ x, F x ^ 2 := by
  have hQ := ccmRestrictedWeilSourceQuadratic_realInteriorSource A hF hFc hFs
  have hN := norm_sq_realInteriorSource A hF hFc hFs
  obtain ⟨u, hu⟩ : ∃ u, u = realInteriorSource A hF hFc hFs := ⟨_, rfl⟩
  rw [← hu] at hQ hN
  have hmass : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, F x ^ 2 := by
    unfold suzukiWeilIntervalFormMass
    rw [norm_suzukiWeilIntervalFormEmbedding, hN]
  have hne : suzukiWeilIntervalFormEmbedding A u.toCCMFormVector ≠ 0 := fun h0 => by
    have : suzukiWeilIntervalFormMass A u.toCCMFormVector = 0 := by
      unfold suzukiWeilIntervalFormMass; rw [h0, norm_zero]; ring
    linarith
  have hglb := (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).1 ⟨u, hne, rfl⟩
  rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy] at hglb
  unfold suzukiWeilIntervalFormRayleigh at hglb
  rwa [hQ, hmass] at hglb

/-- **The ground energy is bounded by the Gaussian tail of `Φ`**: `μ(A) ≤ K e^{A} Φ(A − 2)`. -/
theorem exists_ccmRestrictedWeilGroundEnergy_le_kernel :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : SuzukiPositiveAperture, 3 ≤ A.1 →
      ccmRestrictedWeilGroundEnergy A ≤ K * (Real.exp A.1 * riemannKernelReal (A.1 - 2)) := by
  obtain ⟨K₁, hK₁, hZ⟩ := exists_fullZeroForm_thetaPlateau_le
  set W := ∫ x, riemannKernelReal x * (Real.cosh (x / 2) + primeShiftConstant) with hW
  set E := ∫ x : ℝ, Real.exp (-|1 / 2 * x|) with hE
  have hW0 : 0 ≤ W := le_trans (tailWeight_nonneg 0) (tailWeight_le_total 0)
  have hE0 : 0 ≤ E := integral_nonneg fun x => (Real.exp_pos _).le
  have hκ := primeShiftConstant_nonneg
  have hm := riemannKernelReal_pos 1
  set c := 2 * riemannKernelReal 1 ^ 2 with hc
  have hc0 : 0 < c := by positivity
  refine ⟨(K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / c, by positivity, fun A hA => ?_⟩
  set L := A.1 - 2 with hL
  have hL1 : 1 ≤ L := by linarith
  have hlog : Real.log 2 / 2 ≤ L := by linarith [Real.log_two_lt_d9]
  have hs : tsupport (thetaPlateau L) ⊆ Ioo (-A.1) A.1 :=
    (tsupport_thetaPlateau_subset L).trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hmass := two_mul_sq_riemannKernelReal_one_le hL1
  have hray := ccmRestrictedWeilGroundEnergy_le_fullZeroForm_div (contDiff_thetaPlateau L)
    (hasCompactSupport_thetaPlateau L) hs (by linarith)
  have hτ := tailWeight_le hlog
  have hτ0 := tailWeight_nonneg L
  have hτW := tailWeight_le_total L
  have hZL := hZ L
  have hexp : Real.exp L ≤ Real.exp A.1 := Real.exp_le_exp.mpr (by linarith)
  have hΦL := (riemannKernelReal_pos L).le
  -- `Ẑ ≤ (K₁ + 2W) τ ≤ (K₁ + 2W)(1 + κ) E e^{L} Φ(L)`
  have hZτ : fullZeroForm (thetaPlateau L) ≤ (K₁ + 2 * W) * tailWeight L := by nlinarith
  have hbound : fullZeroForm (thetaPlateau L) ≤
      (K₁ + 2 * W) * ((1 + primeShiftConstant) * E) * (Real.exp A.1 * riemannKernelReal L) := by
    have h1 : tailWeight L ≤ (1 + primeShiftConstant) * E * (Real.exp A.1 * riemannKernelReal L) :=
      hτ.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hΦL) (by positivity))
    calc fullZeroForm (thetaPlateau L) ≤ (K₁ + 2 * W) * tailWeight L := hZτ
      _ ≤ (K₁ + 2 * W) * ((1 + primeShiftConstant) * E * (Real.exp A.1 * riemannKernelReal L)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  set R := (K₁ + 2 * W) * ((1 + primeShiftConstant) * E) * (Real.exp A.1 * riemannKernelReal L)
    with hR
  have hR0 : 0 ≤ R := by positivity
  refine hray.trans ?_
  rw [div_le_iff₀ (by linarith), show (K₁ + 2 * W) * ((1 + primeShiftConstant) * E) / c *
    (Real.exp A.1 * riemannKernelReal L) * ∫ x, thetaPlateau L x ^ 2 =
      R * ((∫ x, thetaPlateau L x ^ 2) / c) by rw [hR]; ring]
  have hq : 1 ≤ (∫ x, thetaPlateau L x ^ 2) / c := by rw [le_div_iff₀ hc0]; linarith
  nlinarith

/-- `Φ(u) ≤ C e^{(9/2)|u|} e^{−π e^{2|u|}}`. -/
theorem riemannKernelReal_le_gaussian (u : ℝ) :
    riemannKernelReal u ≤ cuspDecayConst (riemannKernelPoly 0) * Real.exp (9 / 2 * |u|) *
      Real.exp (-Real.pi * Real.exp (2 * |u|)) := by
  have h := norm_riemannKernelDeriv_le 0 u
  rw [riemannKernelDeriv_zero_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (riemannKernelReal_pos u)] at h
  have e : (2 * ((0 : ℕ) : ℝ) + 9 / 2) = 9 / 2 := by norm_num
  rwa [e] at h

/-- **Gaussian upper bound**: `μ(A) ≤ K exp((11/2)A − π e^{2(A−2)})` for `A ≥ 3`. -/
theorem exists_ccmRestrictedWeilGroundEnergy_le_doubleExp :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : SuzukiPositiveAperture, 3 ≤ A.1 →
      ccmRestrictedWeilGroundEnergy A ≤
        K * Real.exp (11 / 2 * A.1 - Real.pi * Real.exp (2 * (A.1 - 2))) := by
  obtain ⟨K, hK0, hK⟩ := exists_ccmRestrictedWeilGroundEnergy_le_kernel
  have hC0 := cuspDecayConst_nonneg (riemannKernelPoly 0)
  refine ⟨K * cuspDecayConst (riemannKernelPoly 0), mul_nonneg hK0 hC0, fun A hA => ?_⟩
  refine (hK A hA).trans ?_
  have hG := riemannKernelReal_le_gaussian (A.1 - 2)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ A.1 - 2)] at hG
  have hexp : Real.exp A.1 * (Real.exp (9 / 2 * (A.1 - 2)) *
      Real.exp (-Real.pi * Real.exp (2 * (A.1 - 2)))) ≤
      Real.exp (11 / 2 * A.1 - Real.pi * Real.exp (2 * (A.1 - 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc K * (Real.exp A.1 * riemannKernelReal (A.1 - 2))
      ≤ K * (Real.exp A.1 * (cuspDecayConst (riemannKernelPoly 0) *
          Real.exp (9 / 2 * (A.1 - 2)) * Real.exp (-Real.pi * Real.exp (2 * (A.1 - 2))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le) hK0
    _ = K * cuspDecayConst (riemannKernelPoly 0) * (Real.exp A.1 *
          (Real.exp (9 / 2 * (A.1 - 2)) * Real.exp (-Real.pi * Real.exp (2 * (A.1 - 2))))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (mul_nonneg hK0 hC0)

/-- **Gaussian criticality under RH**: `0 ≤ μ(A) ≤ K exp((11/2)A − π e^{2(A−2)})`. -/
theorem ccmRestrictedWeilGroundEnergy_gaussian_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : SuzukiPositiveAperture, 3 ≤ A.1 →
      0 ≤ ccmRestrictedWeilGroundEnergy A ∧ ccmRestrictedWeilGroundEnergy A ≤
        K * Real.exp (11 / 2 * A.1 - Real.pi * Real.exp (2 * (A.1 - 2))) := by
  obtain ⟨K, hK0, hK⟩ := exists_ccmRestrictedWeilGroundEnergy_le_doubleExp
  exact ⟨K, hK0, fun A hA =>
    ⟨ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH A, hK A hA⟩⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
