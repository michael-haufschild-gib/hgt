import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Universal spectral-semigroup wall crossing

Every active analytic mode of a contraction semigroup has an integer birth
order. Observation on an inverse-power time horizon has exactly three
regimes: the mode is unresolved below birth, has a universal exponential
window profile at birth, and is averaged away above birth.

The theorem applies equally to purely imaginary unitary modes and to
strictly dissipative modes in the left half-plane.
-/

open Filter Topology
open scoped Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Removable exponential-window kernel
`Φ(z) = (exp z - 1) / z`, with `Φ(0) = 1`. -/
noncomputable def forwardWindowKernel (z : ℂ) : ℂ :=
  dslope Complex.exp 0 z

@[simp] theorem forwardWindowKernel_zero :
    forwardWindowKernel 0 = 1 := by
  simp [forwardWindowKernel, Complex.deriv_exp]

theorem forwardWindowKernel_of_ne {z : ℂ} (hz : z ≠ 0) :
    forwardWindowKernel z = (Complex.exp z - 1) / z := by
  rw [forwardWindowKernel, dslope_of_ne _ hz]
  simp [slope, smul_eq_mul, div_eq_inv_mul]

/-- The exponential-window kernel is continuous across its removable
singularity. -/
theorem continuous_forwardWindowKernel :
    Continuous forwardWindowKernel := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    exact continuousAt_dslope_same.2 Complex.differentiableAt_exp
  · exact (continuousAt_dslope_of_ne hz).2
      Complex.continuous_exp.continuousAt

/-- Normalized forward time average of one complex spectral mode. -/
noncomputable def forwardModeAverage (T : ℝ) (mode : ℂ) : ℂ :=
  (T : ℂ)⁻¹ *
    ∫ t : ℝ in 0..T, Complex.exp (mode * t)

/-- Exact integral identity for a forward spectral-mode average. -/
theorem forwardModeAverage_eq_kernel
    (T : ℝ) (mode : ℂ) (hT : T ≠ 0) :
    forwardModeAverage T mode =
      forwardWindowKernel ((T : ℂ) * mode) := by
  by_cases hm : mode = 0
  · subst mode
    simp [forwardModeAverage]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT)
  · rw [forwardModeAverage,
      integral_exp_mul_complex hm,
      forwardWindowKernel_of_ne]
    · norm_num
      field_simp
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hT) hm

/-- A complex spectral mode has exact birth profile `c g^b` on the
positive-coupling ray. -/
def HasComplexBirthProfile
    (mode : ℝ → ℂ) (b : ℕ) (c : ℂ) : Prop :=
  Tendsto (fun g => mode g / (g : ℂ) ^ b)
    (𝓝[>] 0) (𝓝 c) ∧ c ≠ 0

/-- A positive real variable raised to a positive natural power tends to
zero through positive values. -/
theorem tendsto_real_pow_nhdsGT_zero
    {q : ℕ} (hq : 0 < q) :
    Tendsto (fun g : ℝ => g ^ q) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont :
        ContinuousAt (fun g : ℝ => g ^ q) 0 :=
      continuousAt_id.pow q
    have h :=
      hcont.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hz : (0 : ℝ) ^ q = 0 := zero_pow hq.ne'
    simpa only [hz] using h
  · filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    exact pow_pos hg q

/-- Below birth, the mode multiplied by an inverse-power observation time
tends to zero. -/
theorem tendsto_scaledMode_zero_of_lt_birth
    {mode : ℝ → ℂ} {b r : ℕ} {c : ℂ} {τ : ℝ}
    (hprofile : HasComplexBirthProfile mode b c)
    (hrb : r < b) :
    Tendsto
      (fun g => ((τ / g ^ r : ℝ) : ℂ) * mode g)
      (𝓝[>] 0) (𝓝 0) := by
  have hpowReal :
      Tendsto (fun g : ℝ => g ^ (b - r))
        (𝓝[>] 0) (𝓝 0) :=
    (tendsto_real_pow_nhdsGT_zero (Nat.sub_pos_of_lt hrb)).mono_right
      inf_le_left
  have hpow :
      Tendsto (fun g : ℝ => ((g ^ (b - r) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hpowReal
  have hmul := (hprofile.1.const_mul (τ : ℂ)).mul hpow
  simpa only [mul_zero] using hmul.congr' (by
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    have hg0 : g ≠ 0 := ne_of_gt hg
    change
      ((τ : ℂ) * (mode g / (g : ℂ) ^ b)) *
          ((g ^ (b - r) : ℝ) : ℂ) =
        ((τ / g ^ r : ℝ) : ℂ) * mode g
    push_cast
    have hpowEq :
        (g : ℂ) ^ b =
          (g : ℂ) ^ r * (g : ℂ) ^ (b - r) := by
      rw [← pow_add, Nat.add_sub_of_le hrb.le]
    rw [hpowEq]
    field_simp [pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hg0)])

/-- At birth, the scaled mode tends to its nonzero leading coefficient
times the fixed observation prefactor. -/
theorem tendsto_scaledMode_birth
    {mode : ℝ → ℂ} {b : ℕ} {c : ℂ} {τ : ℝ}
    (hprofile : HasComplexBirthProfile mode b c) :
    Tendsto
      (fun g => ((τ / g ^ b : ℝ) : ℂ) * mode g)
      (𝓝[>] 0) (𝓝 ((τ : ℂ) * c)) := by
  have h := hprofile.1.const_mul (τ : ℂ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  change 0 < g at hg
  have hg0 : g ≠ 0 := ne_of_gt hg
  change
    (τ : ℂ) * (mode g / (g : ℂ) ^ b) =
      ((τ / g ^ b : ℝ) : ℂ) * mode g
  push_cast
  field_simp

/-- Above birth, the magnitude of the time-scaled mode diverges. -/
theorem tendsto_norm_scaledMode_atTop_of_birth_lt
    {mode : ℝ → ℂ} {b r : ℕ} {c : ℂ} {τ : ℝ}
    (hprofile : HasComplexBirthProfile mode b c)
    (hτ : 0 < τ) (hbr : b < r) :
    Tendsto
      (fun g => ‖((τ / g ^ r : ℝ) : ℂ) * mode g‖)
      (𝓝[>] 0) atTop := by
  have hlead :
      Tendsto (fun g => ‖mode g / (g : ℂ) ^ b‖)
        (𝓝[>] 0) (𝓝 ‖c‖) :=
    hprofile.1.norm
  have hpow :
      Tendsto (fun g : ℝ => g ^ (r - b))
        (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_real_pow_nhdsGT_zero (Nat.sub_pos_of_lt hbr)
  have hinv :
      Tendsto (fun g : ℝ => (g ^ (r - b))⁻¹)
        (𝓝[>] 0) atTop :=
    hpow.inv_tendsto_nhdsGT_zero
  have hcoef :
      Tendsto
        (fun g => τ * ‖mode g / (g : ℂ) ^ b‖)
        (𝓝[>] 0) (𝓝 (τ * ‖c‖)) :=
    hlead.const_mul τ
  have hmul :=
    hcoef.pos_mul_atTop
      (mul_pos hτ (norm_pos_iff.mpr hprofile.2)) hinv
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with g hg
  change 0 < g at hg
  have hg0 : g ≠ 0 := ne_of_gt hg
  change
    τ * ‖mode g / (g : ℂ) ^ b‖ * (g ^ (r - b))⁻¹ =
      ‖((τ / g ^ r : ℝ) : ℂ) * mode g‖
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real,
    Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hg,
    abs_of_pos (div_pos hτ (pow_pos hg r))]
  rw [show r = b + (r - b) by omega, pow_add]
  field_simp
  rw [Nat.add_sub_cancel_left]

/-- The exponential-window kernel vanishes along every unbounded path in
the closed left half-plane. -/
theorem tendsto_forwardWindowKernel_zero_of_norm_atTop
    {α : Type*} {l : Filter α} {z : α → ℂ}
    (hnorm : Tendsto (fun x => ‖z x‖) l atTop)
    (hre : ∀ᶠ x in l, (z x).re ≤ 0) :
    Tendsto (fun x => forwardWindowKernel (z x)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hinv :
      Tendsto (fun x => 2 * (‖z x‖)⁻¹) l (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hnorm).const_mul 2
  refine squeeze_zero' (f := fun x => ‖forwardWindowKernel (z x)‖)
    (g := fun x => 2 * (‖z x‖)⁻¹) ?_ ?_ hinv
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · filter_upwards [hre, hnorm.eventually (eventually_gt_atTop 0)] with x hx hzx
    have hz0 : z x ≠ 0 := norm_pos_iff.mp hzx
    rw [forwardWindowKernel_of_ne hz0, norm_div]
    have hexp : ‖Complex.exp (z x)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hx
    have hnum : ‖Complex.exp (z x) - 1‖ ≤ 2 := by
      calc
        ‖Complex.exp (z x) - 1‖ ≤ ‖Complex.exp (z x)‖ + ‖(1 : ℂ)‖ :=
          norm_sub_le _ _
        _ = ‖Complex.exp (z x)‖ + 1 := by rw [norm_one]
        _ ≤ 1 + 1 := by
          simpa [add_comm] using add_le_add_right hexp 1
        _ = 2 := by norm_num
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum
      (inv_nonneg.mpr (norm_nonneg _))

/-- **Universal semigroup wall crossing.** Every complex mode with exact
birth order and nonpositive real part is unresolved below its inverse-power
birth horizon, has the universal exponential-window profile at birth, and
is averaged away above birth. -/
theorem forwardModeAverage_wallCrossing
    {mode : ℝ → ℂ} {b : ℕ} {c : ℂ} {τ : ℝ}
    (hprofile : HasComplexBirthProfile mode b c)
    (hcontractive : ∀ᶠ g in 𝓝[>] 0, (mode g).re ≤ 0)
    (hτ : 0 < τ) :
    (∀ r < b,
      Tendsto
        (fun g => forwardModeAverage (τ / g ^ r) (mode g))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g => forwardModeAverage (τ / g ^ b) (mode g))
      (𝓝[>] 0) (𝓝 (forwardWindowKernel ((τ : ℂ) * c))) ∧
    (∀ r, b < r →
      Tendsto
        (fun g => forwardModeAverage (τ / g ^ r) (mode g))
        (𝓝[>] 0) (𝓝 0)) := by
  constructor
  · intro r hr
    have harg :=
      tendsto_scaledMode_zero_of_lt_birth hprofile hr (τ := τ)
    have hk := continuous_forwardWindowKernel.continuousAt.tendsto.comp harg
    have hk' :
        Tendsto
          (fun g =>
            forwardWindowKernel
              (((τ / g ^ r : ℝ) : ℂ) * mode g))
          (𝓝[>] 0) (𝓝 1) := by
      simpa [Function.comp_def] using hk
    apply hk'.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    symm
    rw [forwardModeAverage_eq_kernel]
    exact div_ne_zero (ne_of_gt hτ) (pow_ne_zero r (ne_of_gt hg))
  constructor
  · have harg := tendsto_scaledMode_birth hprofile (τ := τ)
    have hk := continuous_forwardWindowKernel.continuousAt.tendsto.comp harg
    have hk' :
        Tendsto
          (fun g =>
            forwardWindowKernel
              (((τ / g ^ b : ℝ) : ℂ) * mode g))
          (𝓝[>] 0)
          (𝓝 (forwardWindowKernel ((τ : ℂ) * c))) := by
      simpa [Function.comp_def] using hk
    apply hk'.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    symm
    rw [forwardModeAverage_eq_kernel]
    exact div_ne_zero (ne_of_gt hτ) (pow_ne_zero b (ne_of_gt hg))
  · intro r hr
    let arg : ℝ → ℂ :=
      fun g => ((τ / g ^ r : ℝ) : ℂ) * mode g
    have hnorm :
        Tendsto (fun g => ‖arg g‖) (𝓝[>] 0) atTop :=
      tendsto_norm_scaledMode_atTop_of_birth_lt
        hprofile hτ hr
    have hre : ∀ᶠ g in 𝓝[>] 0, (arg g).re ≤ 0 := by
      filter_upwards [hcontractive, self_mem_nhdsWithin] with g hgmode hg
      change 0 < g at hg
      simp only [arg, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg hτ.le (pow_nonneg hg.le r)) hgmode
    have hk :=
      tendsto_forwardWindowKernel_zero_of_norm_atTop hnorm hre
    apply hk.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    symm
    rw [forwardModeAverage_eq_kernel]
    exact div_ne_zero (ne_of_gt hτ) (pow_ne_zero r (ne_of_gt hg))

end

end GaloisForLFunctions.HTGeometry
