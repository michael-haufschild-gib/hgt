import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedCutoff
import GaloisForLFunctions.RHTower.SimultaneousPhaseRecurrence

/-!
# Below the maximal frequency the damped cutoff escapes to `-∞`

Assume `β > 0` (equivalently not RH), take a real `a < β` and put `d = β - a > 0`.  With the finite
top packet `Q = {q : v_q = β}` and the gap `β₂ < β` of the remaining copies, for `s ≥ 1`

`e^{-as} P(s)/s = card Q e^{-as}/s - ½ Σ_{q∈Q} (e^{ds} + e^{-(β+a)s}) cos(u_q s)/s + e^{-as} P_c(s)/s`,

`|P_c(s)| ≤ (A/2) s² e^{β₂ s}`.  The oscillatory packet satisfies
`T e^{-dT} ∫_1^T e^{ds} cos(us)/s ds = Re(e^{iuT}/(d+iu)) + o(1)` (complex integration by parts),
and every other piece is `O(T³ e^{kT})` with `k < d` after the same scaling.  Simultaneous phase
recurrence on `Q` then gives clocks `T_n → ∞` with

`T_n e^{-dT_n} D_a(T_n) → -½ Σ_{q∈Q} d/(d² + u_q²) < 0`,  hence `D_a(T_n) → -∞`.

Consequently, for every real `a` when `β > 0` and for every `a ≥ 0` in general,
`(∀ T > 0, D_a(T) ≥ 0) ↔ a ≥ β`.
-/

open Set Filter Topology MeasureTheory

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "β" => liEvenCrossActualClockMaxGrowthRate
local notation "u" => liEvenCrossActualClockReciprocalFrequency
local notation "v" => liEvenCrossActualClockReciprocalGrowthRate
local notation "D" => liEvenCrossActualClockDampedCutoff

/-! ## Scaled polynomial-exponential remainders -/

theorem tendsto_mul_exp_neg_mul_of_bound {d k C : ℝ} (hkd : k < d) {g : ℝ → ℝ}
    (hg : ∀ T, 1 ≤ T → |g T| ≤ C * T ^ 2 * Real.exp (k * T)) :
    Tendsto (fun T => T * Real.exp (-(d * T)) * g T) atTop (𝓝 0) := by
  have hc : 0 < d - k := by linarith
  have hlim : Tendsto (fun T : ℝ => |C| / (d - k) ^ 3 * (((d - k) * T) ^ 3 *
      Real.exp (-((d - k) * T)))) atTop (𝓝 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp
      (tendsto_id.const_mul_atTop hc)).const_mul (|C| / (d - k) ^ 3)
    simpa only [mul_zero, Function.comp_def, id] using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hT0 : 0 ≤ T := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hT0, Real.abs_exp]
  have hb := hg T hT
  have hC : C * T ^ 2 * Real.exp (k * T) ≤ |C| * T ^ 2 * Real.exp (k * T) := by
    have := le_abs_self C
    have : 0 ≤ T ^ 2 * Real.exp (k * T) := by positivity
    nlinarith
  calc T * Real.exp (-(d * T)) * |g T| ≤ T * Real.exp (-(d * T)) * (|C| * T ^ 2 * Real.exp (k * T)) :=
        mul_le_mul_of_nonneg_left (hb.trans hC) (by positivity)
    _ = _ := by
        have hdk : (d - k) ^ 3 ≠ 0 := by positivity
        rw [show -((d - k) * T) = -(d * T) + k * T by ring, Real.exp_add]
        field_simp

theorem abs_intervalIntegral_le_of_bound {k C T : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C) (hT : 1 ≤ T)
    {g : ℝ → ℝ} (hg : ∀ s ∈ Icc 1 T, |g s| ≤ C * s * Real.exp (k * s)) :
    |∫ s in (1 : ℝ)..T, g s| ≤ C * T ^ 2 * Real.exp (k * T) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := T)
    (C := C * T * Real.exp (k * T)) (f := g) fun s hs => by
      rw [uIoc_of_le hT] at hs
      rw [Real.norm_eq_abs]
      refine (hg s ⟨hs.1.le, hs.2⟩).trans ?_
      have h1 : Real.exp (k * s) ≤ Real.exp (k * T) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hk)
      have hs0 : 0 ≤ s := by linarith [hs.1]
      gcongr
      exact hs.2
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - 1)] at h
  refine h.trans ?_
  have : 0 ≤ C * T * Real.exp (k * T) := by positivity
  nlinarith

/-! ## The integrated oscillatory packet -/

private theorem hasDerivAt_packet_primitive {c : ℂ} (hc : c ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun x : ℝ => Complex.exp (c * x) / (c * x))
      (Complex.exp (c * s) / s - Complex.exp (c * s) / (c * s ^ 2)) s := by
  have h1 : HasDerivAt (fun x : ℝ => Complex.exp (c * x)) (Complex.exp (c * s) * c) s := by
    have := ((hasDerivAt_id (s : ℂ)).const_mul c).cexp
    simpa using this.comp_ofReal
  have h2 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c s := by
    simpa using ((hasDerivAt_id (s : ℂ)).const_mul c).comp_ofReal
  have hcs : c * (s : ℂ) ≠ 0 := mul_ne_zero hc (by exact_mod_cast hs)
  refine (h1.div h2 hcs).congr_deriv ?_
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  field_simp

private theorem integral_exp_mul_eq {d : ℝ} (hd : 0 < d) (a b : ℝ) :
    ∫ s in a..b, Real.exp (d * s) = (Real.exp (d * b) - Real.exp (d * a)) / d := by
  have h : ∀ x ∈ uIcc a b, HasDerivAt (fun s => Real.exp (d * s) / d) (Real.exp (d * x)) x := by
    intro x _
    have := (((hasDerivAt_id x).const_mul d).exp).div_const d
    refine this.congr_deriv ?_
    simp only [id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h ((by fun_prop : Continuous fun s =>
    Real.exp (d * s)).intervalIntegrable a b)]
  ring

/-- `∫_1^T e^{ds}/s² ≤ T e^{dT/2} + 4 e^{dT}/(d T²)` for `T ≥ 2`. -/
private theorem integral_exp_div_sq_le {d : ℝ} (hd : 0 < d) {T : ℝ} (hT : 2 ≤ T) :
    ∫ s in (1 : ℝ)..T, Real.exp (d * s) / s ^ 2 ≤
      T * Real.exp (d * (T / 2)) + 4 * Real.exp (d * T) / (d * T ^ 2) := by
  have hT0 : 0 < T := by linarith
  have hcont : ContinuousOn (fun s : ℝ => Real.exp (d * s) / s ^ 2) (Ici 1) :=
    ((by fun_prop : Continuous fun s : ℝ => Real.exp (d * s)).continuousOn).div
      (by fun_prop) fun s hs => by have : (1 : ℝ) ≤ s := hs; positivity
  have hii : ∀ a b : ℝ, 1 ≤ a → 1 ≤ b →
      IntervalIntegrable (fun s : ℝ => Real.exp (d * s) / s ^ 2) volume a b := fun a b ha hb =>
    (hcont.mono fun s hs => by
      rcases mem_uIcc.1 hs with h | h <;> exact (show (1 : ℝ) ≤ s by linarith [h.1])).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 1 (T / 2) le_rfl (by linarith))
    (hii (T / 2) T (by linarith) (by linarith))]
  have h1 : ∫ s in (1 : ℝ)..T / 2, Real.exp (d * s) / s ^ 2 ≤ ∫ s in (1 : ℝ)..T / 2,
      Real.exp (d * (T / 2)) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hii 1 (T / 2) le_rfl (by linarith))
      (intervalIntegrable_const (μ := volume)) fun s hs => ?_
    have hs1 : 1 ≤ s := hs.1
    rw [div_le_iff₀ (by positivity)]
    calc Real.exp (d * s) ≤ Real.exp (d * (T / 2)) := Real.exp_le_exp.2 (by nlinarith [hs.2])
      _ ≤ Real.exp (d * (T / 2)) * s ^ 2 := le_mul_of_one_le_right (Real.exp_pos _).le
          (one_le_pow₀ hs1)
  have h2 : ∫ s in T / 2..T, Real.exp (d * s) / s ^ 2 ≤ ∫ s in T / 2..T,
      4 / T ^ 2 * Real.exp (d * s) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hii (T / 2) T (by linarith) (by linarith))
      ((by fun_prop : Continuous fun s : ℝ => 4 / T ^ 2 * Real.exp (d * s)).intervalIntegrable _ _)
      fun s hs => ?_
    have hs1 : T / 2 ≤ s := hs.1
    have hs0 : 0 < s := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : 4 / T ^ 2 * s ^ 2 ≥ 1 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
    nlinarith [Real.exp_pos (d * s)]
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_eq hd] at h2
  have h3 : (T / 2 - 1) * Real.exp (d * (T / 2)) ≤ T * Real.exp (d * (T / 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have h4 : 4 / T ^ 2 * ((Real.exp (d * T) - Real.exp (d * (T / 2))) / d) ≤
      4 * Real.exp (d * T) / (d * T ^ 2) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos (Real.exp_pos (d * (T / 2))) hd) (pow_pos hT0 2)]
  linarith

/-- **Integrated packet (I11).**  For `d > 0`,
`T e^{-dT} ∫_1^T e^{ds} cos(us)/s ds - Re(e^{iuT}/(d+iu)) → 0`. -/
theorem tendsto_integratedPacket_sub (u₀ : ℝ) {d : ℝ} (hd : 0 < d) :
    Tendsto (fun T => T * Real.exp (-(d * T)) *
      (∫ s in (1 : ℝ)..T, Real.exp (d * s) * Real.cos (u₀ * s) / s) -
        (Complex.exp ((u₀ * T : ℝ) * Complex.I) / ((d : ℂ) + u₀ * Complex.I)).re) atTop (𝓝 0) := by
  set c : ℂ := (d : ℂ) + u₀ * Complex.I with hcdef
  have hc : c ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [c] at this; linarith
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hcont1 : ∀ T : ℝ, 1 ≤ T → ContinuousOn (fun s : ℝ => Complex.exp (c * s) / s) (uIcc 1 T) :=
    fun T hT => ((by fun_prop : Continuous fun s : ℝ => Complex.exp (c * s)).continuousOn).div
      (by fun_prop) fun s hs => by
        rw [uIcc_of_le hT] at hs; exact_mod_cast (show s ≠ 0 by linarith [hs.1])
  have hcont2 : ∀ T : ℝ, 1 ≤ T →
      ContinuousOn (fun s : ℝ => Complex.exp (c * s) / (c * (s : ℂ) ^ 2)) (uIcc 1 T) :=
    fun T hT => ((by fun_prop : Continuous fun s : ℝ => Complex.exp (c * s)).continuousOn).div
      (by fun_prop) fun s hs => by
        rw [uIcc_of_le hT] at hs
        exact mul_ne_zero hc (pow_ne_zero 2 (by exact_mod_cast (show s ≠ 0 by linarith [hs.1])))
  -- the exact remainder identity
  have key : ∀ T : ℝ, 1 ≤ T → T * Real.exp (-(d * T)) *
      (∫ s in (1 : ℝ)..T, Real.exp (d * s) * Real.cos (u₀ * s) / s) -
        (Complex.exp ((u₀ * T : ℝ) * Complex.I) / c).re =
      (((T * Real.exp (-(d * T)) : ℝ) : ℂ) *
        (-(Complex.exp c / c) + ∫ s in (1 : ℝ)..T, Complex.exp (c * s) / (c * (s : ℂ) ^ 2))).re := by
    intro T hT
    have hT0 : (0 : ℝ) < T := by linarith
    have hi1 := (hcont1 T hT).intervalIntegrable (μ := volume)
    have hi2 := (hcont2 T hT).intervalIntegrable (μ := volume)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 1) (b := T)
      (f := fun x : ℝ => Complex.exp (c * x) / (c * x))
      (f' := fun s : ℝ => Complex.exp (c * s) / s - Complex.exp (c * s) / (c * (s : ℂ) ^ 2))
      (fun s hs => by
        rw [uIcc_of_le hT] at hs
        exact hasDerivAt_packet_primitive hc (show s ≠ 0 by linarith [hs.1]))
      (IntervalIntegrable.sub (μ := volume) hi1 hi2)
    rw [intervalIntegral.integral_sub hi1 hi2] at hFTC
    have hre : ∫ s in (1 : ℝ)..T, Real.exp (d * s) * Real.cos (u₀ * s) / s =
        (∫ s in (1 : ℝ)..T, Complex.exp (c * s) / s).re := by
      have := Complex.reCLM.intervalIntegral_comp_comm hi1
      simp only [Complex.reCLM_apply] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [Complex.div_ofReal_re, Complex.exp_re]
      congr 2 <;> simp [c]
    rw [hre]
    have hsolve : ∫ s in (1 : ℝ)..T, Complex.exp (c * s) / s =
        Complex.exp (c * T) / (c * T) - Complex.exp c / c +
          ∫ s in (1 : ℝ)..T, Complex.exp (c * s) / (c * (s : ℂ) ^ 2) := by
      have e1 : Complex.exp (c * ((1 : ℝ) : ℂ)) / (c * ((1 : ℝ) : ℂ)) = Complex.exp c / c := by simp
      rw [e1] at hFTC
      linear_combination hFTC
    rw [hsolve, ← Complex.re_ofReal_mul]
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
    have hexp : ((T * Real.exp (-(d * T)) : ℝ) : ℂ) * (Complex.exp (c * T) / (c * T)) =
        Complex.exp ((u₀ * T : ℝ) * Complex.I) / c := by
      have : Complex.exp (c * T) = ((Real.exp (d * T) : ℝ) : ℂ) *
          Complex.exp ((u₀ * T : ℝ) * Complex.I) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; simp only [c]; push_cast; ring
      rw [this]
      push_cast
      field_simp
      rw [← Complex.exp_add]
      simp
    rw [mul_add, mul_sub, hexp, Complex.add_re, Complex.sub_re, mul_add, Complex.add_re, mul_neg,
      Complex.neg_re]
    ring
  -- bounds
  have hbound : ∀ T : ℝ, 2 ≤ T →
      ‖T * Real.exp (-(d * T)) * (∫ s in (1 : ℝ)..T, Real.exp (d * s) * Real.cos (u₀ * s) / s) -
        (Complex.exp ((u₀ * T : ℝ) * Complex.I) / c).re‖ ≤
      T * Real.exp (-(d * T)) * (Real.exp d / ‖c‖) +
        T * Real.exp (-(d * T)) * ((T * Real.exp (d * (T / 2)) +
          4 * Real.exp (d * T) / (d * T ^ 2)) / ‖c‖) := by
    intro T hT
    have hT1 : (1 : ℝ) ≤ T := by linarith
    rw [key T hT1, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
    rw [mul_add]
    gcongr
    · rw [norm_neg, norm_div, Complex.norm_exp, show c.re = d by simp [c]]
    · refine (intervalIntegral.norm_integral_le_integral_norm hT1).trans ?_
      have hle : ∫ s in (1 : ℝ)..T, ‖Complex.exp (c * s) / (c * (s : ℂ) ^ 2)‖ =
          (∫ s in (1 : ℝ)..T, Real.exp (d * s) / s ^ 2) / ‖c‖ := by
        rw [← intervalIntegral.integral_div]
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hT1] at hs
        have hs0 : (0 : ℝ) < s := by linarith [hs.1]
        rw [norm_div, norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hs0]
        have : (c * (s : ℂ)).re = d * s := by simp [c]
        rw [this]
        field_simp
      rw [hle]
      exact div_le_div_of_nonneg_right (integral_exp_div_sq_le hd hT) hcn.le
  refine squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    exact hbound T hT) ?_
  -- the bound tends to zero
  have hTexp : Tendsto (fun T : ℝ => T * Real.exp (-(d * T))) atTop (𝓝 0) := by
    have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.const_mul_atTop hd)).const_mul (1 / d)
    refine (this.congr fun T => ?_).trans (by simp)
    simp only [Function.comp_def, id, pow_one]
    field_simp
  have hA := hTexp.mul_const (Real.exp d / ‖c‖)
  rw [zero_mul] at hA
  have hB : Tendsto (fun T : ℝ => T * Real.exp (-(d * T)) * ((T * Real.exp (d * (T / 2)) +
      4 * Real.exp (d * T) / (d * T ^ 2)) / ‖c‖)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => (2 / d) ^ 2 * ((d / 2 * T) ^ 2 * Real.exp (-(d / 2 * T))))
        atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (tendsto_id.const_mul_atTop (half_pos hd))).const_mul ((2 / d) ^ 2)
      simpa only [mul_zero, Function.comp_def, id] using this
    have h2 : Tendsto (fun T : ℝ => 4 / d * T⁻¹) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.const_mul (4 / d)
      rwa [mul_zero] at this
    have h3 := ((h1.add h2).div_const ‖c‖)
    rw [zero_add, zero_div] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have e1 : Real.exp (-(d * T)) * Real.exp (d * (T / 2)) = Real.exp (-(d / 2 * T)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(d * T)) * Real.exp (d * T) = 1 := by
      rw [← Real.exp_add]; simp
    have hd0 := hd.ne'
    have hT0 := hT.ne'
    have hc0 := hcn.ne'
    have : T * Real.exp (-(d * T)) * ((T * Real.exp (d * (T / 2)) +
        4 * Real.exp (d * T) / (d * T ^ 2)) / ‖c‖) =
          (T ^ 2 * (Real.exp (-(d * T)) * Real.exp (d * (T / 2))) +
            4 / d * T⁻¹ * (Real.exp (-(d * T)) * Real.exp (d * T))) / ‖c‖ := by
      field_simp
    rw [this, e1, e2]
    field_simp
  simpa using hA.add hB

/-! ## The packet split -/

/-- The complement of the top packet: `P_c(s) = P(s) - Σ_{q∈S} (1 - cos(u_q s) cosh(βs))`. -/
def liEvenCrossActualClockTopComplement (S : Finset XiZeroCopy) (s : ℝ) : ℝ :=
  P s - ∑ q ∈ S, (1 - Real.cos (u q * s) * Real.cosh (β * s))

/-- **Complement bound (I10).**  If every copy outside `S` has `v_q ≤ β₂` and every copy of `S` has
`v_q = β`, then `|P_c(s)| ≤ (A/2) s² e^{β₂ s}` for `s ≥ 0`. -/
theorem abs_liEvenCrossActualClockTopComplement_le {S : Finset XiZeroCopy} {β₂ : ℝ}
    (hS : ∀ q ∈ S, v q = β) (hgap : ∀ q, q ∉ S → v q ≤ β₂) {s : ℝ} (hs : 0 ≤ s) :
    |liEvenCrossActualClockTopComplement S s| ≤
      xiShiftAbsoluteMass 0 * s ^ 2 / 2 * Real.exp (β₂ * s) := by
  have hsum := summable_liEvenCrossActualClockCoshCosAtom s
  have hsplit := hsum.sum_add_tsum_compl (s := S)
  have hc : liEvenCrossActualClockTopComplement S s =
      ∑' q : ↑((S : Set XiZeroCopy)ᶜ), liEvenCrossActualClockCoshCosAtom q s := by
    unfold liEvenCrossActualClockTopComplement
    rw [← tsum_liEvenCrossActualClockCoshCosAtom s, ← hsplit]
    have : ∑ q ∈ S, liEvenCrossActualClockCoshCosAtom q s =
        ∑ q ∈ S, (1 - Real.cos (u q * s) * Real.cosh (β * s)) :=
      Finset.sum_congr rfl fun q hq => by
        unfold liEvenCrossActualClockCoshCosAtom; rw [hS q hq]
    rw [this]; ring
  have hb : ∀ q : ↑((S : Set XiZeroCopy)ᶜ), |liEvenCrossActualClockCoshCosAtom q s| ≤
      s ^ 2 / 2 * Real.exp (β₂ * s) * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 := by
    intro q
    have h1 := abs_liEvenCrossActualClockCoshCosAtom_le q hs
    have h2 : Real.exp (v q * s) ≤ Real.exp (β₂ * s) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hgap q fun h => q.2 (Finset.mem_coe.2 h)) hs)
    have h3 : 0 ≤ s ^ 2 / 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 := by positivity
    calc _ ≤ _ := h1
      _ ≤ s ^ 2 / 2 * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 * Real.exp (β₂ * s) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring
  have hsumc : Summable fun q : ↑((S : Set XiZeroCopy)ᶜ) => ‖(xiSpectralPoint q)⁻¹‖ ^ 2 :=
    summable_norm_inv_xiSpectralPoint_sq.subtype _
  rw [hc]
  calc |∑' q : ↑((S : Set XiZeroCopy)ᶜ), liEvenCrossActualClockCoshCosAtom q s| ≤
      ∑' q : ↑((S : Set XiZeroCopy)ᶜ), s ^ 2 / 2 * Real.exp (β₂ * s) * ‖(xiSpectralPoint q)⁻¹‖ ^ 2 := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm (hsum.subtype _).norm |>.trans
          ((hsum.subtype _).norm.tsum_le_tsum (fun q => by rw [Real.norm_eq_abs]; exact hb q)
            (hsumc.mul_left _))
    _ = s ^ 2 / 2 * Real.exp (β₂ * s) * ∑' q : ↑((S : Set XiZeroCopy)ᶜ), ‖(xiSpectralPoint q)⁻¹‖ ^ 2 :=
        tsum_mul_left
    _ ≤ s ^ 2 / 2 * Real.exp (β₂ * s) * xiShiftAbsoluteMass 0 := by
        rw [← tsum_norm_inv_xiSpectralPoint_sq]
        exact mul_le_mul_of_nonneg_left (summable_norm_inv_xiSpectralPoint_sq.tsum_subtype_le _ _
          (fun q => by positivity)) (by positivity)
    _ = _ := by ring

/-- The pointwise split of the damped profile on `s > 0`. -/
theorem liEvenCrossActualClockDampedProfile_split (S : Finset XiZeroCopy) (a : ℝ) {s : ℝ} (hs : s ≠ 0) :
    Real.exp (-a * s) * P s / s = S.card * (Real.exp (-a * s) / s) -
      1 / 2 * ∑ q ∈ S, Real.exp ((β - a) * s) * Real.cos (u q * s) / s -
        1 / 2 * ∑ q ∈ S, Real.exp (-(β + a) * s) * Real.cos (u q * s) / s +
          Real.exp (-a * s) * liEvenCrossActualClockTopComplement S s / s := by
  have e1 : Real.exp ((β - a) * s) = Real.exp (-a * s) * Real.exp (β * s) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(β + a) * s) = Real.exp (-a * s) * Real.exp (-(β * s)) := by
    rw [← Real.exp_add]; ring_nf
  have key : ∀ q, Real.exp (-a * s) * (1 - Real.cos (u q * s) * Real.cosh (β * s)) / s =
      Real.exp (-a * s) / s - 1 / 2 * (Real.exp ((β - a) * s) * Real.cos (u q * s) / s) -
        1 / 2 * (Real.exp (-(β + a) * s) * Real.cos (u q * s) / s) := by
    intro q
    rw [Real.cosh_eq, e1, e2]
    field_simp
    ring
  unfold liEvenCrossActualClockTopComplement
  have hS1 : Real.exp (-a * s) * (P s - ∑ q ∈ S, (1 - Real.cos (u q * s) * Real.cosh (β * s))) / s =
      Real.exp (-a * s) * P s / s -
        ∑ q ∈ S, Real.exp (-a * s) * (1 - Real.cos (u q * s) * Real.cosh (β * s)) / s := by
    rw [mul_sub, sub_div, Finset.mul_sum, Finset.sum_div]
  rw [hS1, Finset.sum_congr rfl (fun q _ => key q), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-! ## The cofinal escape -/

private theorem continuousOn_one_div {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) (hT : 1 ≤ T) :
    ContinuousOn (fun s => f s / s) (uIcc 1 T) :=
  hf.continuousOn.div continuousOn_id fun s hs => by
    rw [uIcc_of_le hT] at hs; exact (show s ≠ 0 by linarith [hs.1])

/-- **Cofinal escape (I12–I13).**  If RH fails and `a < β`, the full top packet `S` gives clocks
`T_n → ∞` with `T_n e^{-(β-a)T_n} D_a(T_n) → -½ Σ_{q∈S} (β-a)/((β-a)² + u_q²) < 0`; in particular
`D_a(T_n) → -∞`. -/
theorem liEvenCrossActualClockDampedCutoff_escape_of_not_rh (hnot : ¬RiemannHypothesis) {a : ℝ}
    (ha : a < β) :
    ∃ S : Finset XiZeroCopy, S.Nonempty ∧ (∀ q, q ∈ S ↔ v q = β) ∧
      ∃ t : ℕ → ℝ, (∀ n : ℕ, (n : ℝ) + 1 ≤ t n) ∧ Tendsto t atTop atTop ∧
        Tendsto (fun n => t n * Real.exp (-((β - a) * t n)) * D a (t n)) atTop
          (𝓝 (-(1 / 2) * ∑ q ∈ S, (β - a) / ((β - a) ^ 2 + u q ^ 2))) ∧
        -(1 / 2) * ∑ q ∈ S, (β - a) / ((β - a) ^ 2 + u q ^ 2) < 0 ∧
        Tendsto (fun n => D a (t n)) atTop atBot := by
  classical
  obtain ⟨hβ, hfin, hne, β₂, hβ₂, hβ₂β, hgap⟩ := liEvenCrossActualClockMaxGrowthRate_top_of_not_rh hnot
  set S := hfin.toFinset
  have hS : ∀ q, q ∈ S ↔ v q = β := fun q => by
    simp [S, liEvenCrossActualClockTopPacket]
  have hSne : S.Nonempty := by simpa [S] using hne
  have hgapS : ∀ q, q ∉ S → v q ≤ β₂ := fun q hq => hgap q (by simpa [S] using hq)
  set d := β - a
  have hd : 0 < d := by simp only [d]; linarith
  -- simultaneous phases on the finite packet
  have hrec (n : ℕ) : ∃ t : ℝ, (n : ℝ) + 1 ≤ t ∧
      ∀ j : S, ‖GaloisForLFunctions.bohrChar (-u j) t - 1‖ ≤ 1 / ((n : ℝ) + 1) :=
    exists_simultaneous_phase_recurrence (fun j : S => -u j) (by positivity) ((n : ℝ) + 1)
  choose t ht hphase using hrec
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have htop : Tendsto t atTop atTop := tendsto_atTop_mono ht hnat
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hchar : ∀ q ∈ S, Tendsto (fun n => Complex.exp ((u q * t n : ℝ) * Complex.I)) atTop (𝓝 1) := by
    intro q hq
    have h : Tendsto (fun n => GaloisForLFunctions.bohrChar (-u q) (t n)) atTop (𝓝 1) :=
      tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
        (fun n => by rw [dist_eq_norm]; exact hphase n ⟨q, hq⟩) heps)
    refine h.congr fun n => ?_
    simp only [GaloisForLFunctions.bohrChar]
    congr 2; push_cast; ring
  -- packet limits
  have hpacket : ∀ q ∈ S, Tendsto (fun n => t n * Real.exp (-(d * t n)) *
      ∫ s in (1 : ℝ)..t n, Real.exp (d * s) * Real.cos (u q * s) / s) atTop
        (𝓝 (d / (d ^ 2 + u q ^ 2))) := by
    intro q hq
    have h1 := (tendsto_integratedPacket_sub (u q) hd).comp htop
    have hval : ((1 : ℂ) / ((d : ℂ) + u q * Complex.I)).re = d / (d ^ 2 + u q ^ 2) := by
      rw [one_div, Complex.inv_re, Complex.normSq_apply]
      simp
      ring
    have h2 : Tendsto (fun n => (Complex.exp ((u q * t n : ℝ) * Complex.I) /
        ((d : ℂ) + u q * Complex.I)).re) atTop (𝓝 (d / (d ^ 2 + u q ^ 2))) := by
      have h3 := (Complex.continuous_re.tendsto _).comp
        ((hchar q hq).div_const ((d : ℂ) + u q * Complex.I))
      rw [hval] at h3
      exact h3
    have h4 := h1.add h2
    rw [zero_add] at h4
    exact h4.congr fun n => by simp only [Function.comp_apply]; ring
  -- the remainder pieces
  set k := max 0 (max (max (-a) (-(β + a))) (β₂ - a))
  have hk0 : 0 ≤ k := le_max_left _ _
  have hkd : k < d := by
    simp only [k, d]
    refine max_lt (by linarith) (max_lt (max_lt (by linarith) (by linarith)) (by linarith))
  have hka : -a ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hkb : -(β + a) ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hkc : β₂ - a ≤ k := (le_max_right _ _).trans (le_max_right _ _)
  have hexpk : ∀ {m s : ℝ}, m ≤ k → 1 ≤ s → Real.exp (m * s) ≤ s * Real.exp (k * s) := by
    intro m s hm hs
    calc Real.exp (m * s) ≤ Real.exp (k * s) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hm (by linarith))
      _ ≤ s * Real.exp (k * s) := le_mul_of_one_le_left (Real.exp_pos _).le hs
  set Pc := liEvenCrossActualClockTopComplement S
  have hPc : Continuous Pc := continuous_liEvenCrossActualClockPrimitive.sub
    (continuous_finsetSum _ fun q _ => by fun_prop)
  have hPcb : ∀ s, 0 ≤ s → |Pc s| ≤ xiShiftAbsoluteMass 0 * s ^ 2 / 2 * Real.exp (β₂ * s) :=
    fun s hs => abs_liEvenCrossActualClockTopComplement_le (fun q hq => (hS q).1 hq) hgapS hs
  have hA := xiShiftAbsoluteMass_nonneg 0
  have hb0 : ∀ T, 1 ≤ T → |∫ s in (1 : ℝ)..T, Real.exp (-a * s) / s| ≤ 1 * T ^ 2 * Real.exp (k * T) :=
    fun T hT => abs_intervalIntegral_le_of_bound hk0 zero_le_one hT fun s hs => by
      have hs1 : 1 ≤ s := hs.1
      rw [abs_div, Real.abs_exp, abs_of_pos (show (0 : ℝ) < s by linarith), one_mul]
      exact (div_le_self (Real.exp_pos _).le hs1).trans (hexpk hka hs1)
  have hb1 : ∀ q, ∀ T, 1 ≤ T → |∫ s in (1 : ℝ)..T, Real.exp (-(β + a) * s) * Real.cos (u q * s) / s| ≤
      1 * T ^ 2 * Real.exp (k * T) :=
    fun q T hT => abs_intervalIntegral_le_of_bound hk0 zero_le_one hT fun s hs => by
      have hs1 : 1 ≤ s := hs.1
      rw [abs_div, abs_mul, Real.abs_exp, abs_of_pos (show (0 : ℝ) < s by linarith), one_mul]
      have hc := Real.abs_cos_le_one (u q * s)
      have he := Real.exp_pos (-(β + a) * s)
      refine (div_le_self (by positivity) hs1).trans ?_
      calc Real.exp (-(β + a) * s) * |Real.cos (u q * s)| ≤ Real.exp (-(β + a) * s) * 1 :=
            mul_le_mul_of_nonneg_left hc he.le
        _ ≤ _ := by rw [mul_one]; exact hexpk hkb hs1
  have hb2 : ∀ T, 1 ≤ T → |∫ s in (1 : ℝ)..T, Real.exp (-a * s) * Pc s / s| ≤
      xiShiftAbsoluteMass 0 / 2 * T ^ 2 * Real.exp (k * T) :=
    fun T hT => abs_intervalIntegral_le_of_bound hk0 (by positivity) hT fun s hs => by
      have hs1 : 1 ≤ s := hs.1
      have hs0 : 0 < s := by linarith
      rw [abs_div, abs_mul, Real.abs_exp, abs_of_pos hs0, div_le_iff₀ hs0]
      have h1 := hPcb s hs0.le
      have h2 : Real.exp ((β₂ - a) * s) ≤ Real.exp (k * s) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hkc hs0.le)
      have e : Real.exp (-a * s) * Real.exp (β₂ * s) = Real.exp ((β₂ - a) * s) := by
        rw [← Real.exp_add]; ring_nf
      calc Real.exp (-a * s) * |Pc s| ≤ Real.exp (-a * s) *
          (xiShiftAbsoluteMass 0 * s ^ 2 / 2 * Real.exp (β₂ * s)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
        _ = xiShiftAbsoluteMass 0 / 2 * s ^ 2 * Real.exp ((β₂ - a) * s) := by rw [← e]; ring
        _ ≤ xiShiftAbsoluteMass 0 / 2 * s ^ 2 * Real.exp (k * s) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
  have hbD : ∀ T, 1 ≤ T → |D a 1| ≤ |D a 1| * T ^ 2 * Real.exp (k * T) := by
    intro T hT
    have h1 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    have h2 : 1 ≤ Real.exp (k * T) := Real.one_le_exp (by nlinarith)
    have := abs_nonneg (D a 1)
    nlinarith [mul_le_mul h1 h2 zero_le_one (by positivity)]
  have l0 := (tendsto_mul_exp_neg_mul_of_bound hkd hb0).comp htop
  have l1 : ∀ q ∈ S, Tendsto (fun n => t n * Real.exp (-(d * t n)) *
      ∫ s in (1 : ℝ)..t n, Real.exp (-(β + a) * s) * Real.cos (u q * s) / s) atTop (𝓝 0) :=
    fun q _ => (tendsto_mul_exp_neg_mul_of_bound hkd (hb1 q)).comp htop
  have l2 := (tendsto_mul_exp_neg_mul_of_bound hkd hb2).comp htop
  have lD := (tendsto_mul_exp_neg_mul_of_bound hkd hbD).comp htop
  -- the decomposition
  have hdecomp : ∀ T, 1 ≤ T → D a T = D a 1 + S.card * (∫ s in (1 : ℝ)..T, Real.exp (-a * s) / s) -
      1 / 2 * (∑ q ∈ S, ∫ s in (1 : ℝ)..T, Real.exp (d * s) * Real.cos (u q * s) / s) -
        1 / 2 * (∑ q ∈ S, ∫ s in (1 : ℝ)..T, Real.exp (-(β + a) * s) * Real.cos (u q * s) / s) +
          ∫ s in (1 : ℝ)..T, Real.exp (-a * s) * Pc s / s := by
    intro T hT
    have c0 := continuousOn_one_div (f := fun s => Real.exp (-a * s)) (by fun_prop) T hT
    have cJ : ∀ q, ContinuousOn (fun s => Real.exp (d * s) * Real.cos (u q * s) / s) (uIcc 1 T) :=
      fun q => continuousOn_one_div (f := fun s => Real.exp (d * s) * Real.cos (u q * s))
        (by fun_prop) T hT
    have cI : ∀ q, ContinuousOn (fun s => Real.exp (-(β + a) * s) * Real.cos (u q * s) / s)
        (uIcc 1 T) := fun q => continuousOn_one_div
          (f := fun s => Real.exp (-(β + a) * s) * Real.cos (u q * s)) (by fun_prop) T hT
    have cc := continuousOn_one_div (f := fun s => Real.exp (-a * s) * Pc s)
      ((by fun_prop : Continuous fun s : ℝ => Real.exp (-a * s)).mul hPc) T hT
    have h1 : IntervalIntegrable (fun s => (S.card : ℝ) * (Real.exp (-a * s) / s)) volume 1 T :=
      (continuousOn_const.mul c0).intervalIntegrable
    have h2 : IntervalIntegrable (fun s => 1 / 2 * ∑ q ∈ S, Real.exp (d * s) * Real.cos (u q * s) / s)
        volume 1 T := (continuousOn_const.mul (continuousOn_finsetSum _ fun q _ => cJ q)).intervalIntegrable
    have h3 : IntervalIntegrable (fun s => 1 / 2 * ∑ q ∈ S, Real.exp (-(β + a) * s) *
        Real.cos (u q * s) / s) volume 1 T :=
      (continuousOn_const.mul (continuousOn_finsetSum _ fun q _ => cI q)).intervalIntegrable
    have h4 : IntervalIntegrable (fun s => Real.exp (-a * s) * Pc s / s) volume 1 T :=
      cc.intervalIntegrable
    have h12 : IntervalIntegrable (fun s => (S.card : ℝ) * (Real.exp (-a * s) / s) -
        1 / 2 * ∑ q ∈ S, Real.exp (d * s) * Real.cos (u q * s) / s) volume 1 T := h1.sub h2
    have h123 : IntervalIntegrable (fun s => (S.card : ℝ) * (Real.exp (-a * s) / s) -
        1 / 2 * ∑ q ∈ S, Real.exp (d * s) * Real.cos (u q * s) / s -
          1 / 2 * ∑ q ∈ S, Real.exp (-(β + a) * s) * Real.cos (u q * s) / s) volume 1 T := h12.sub h3
    unfold liEvenCrossActualClockDampedCutoff
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_liEvenCrossActualClockDampedCutoff_profile a le_rfl zero_le_one)
      (intervalIntegrable_liEvenCrossActualClockDampedCutoff_profile a zero_le_one (by linarith))]
    have hcongr : ∫ s in (1 : ℝ)..T, Real.exp (-a * s) * P s / s =
        ∫ s in (1 : ℝ)..T, ((S.card : ℝ) * (Real.exp (-a * s) / s) -
          1 / 2 * ∑ q ∈ S, Real.exp (d * s) * Real.cos (u q * s) / s -
            1 / 2 * ∑ q ∈ S, Real.exp (-(β + a) * s) * Real.cos (u q * s) / s +
              Real.exp (-a * s) * Pc s / s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hT] at hs
      exact liEvenCrossActualClockDampedProfile_split S a (show s ≠ 0 by linarith [hs.1])
    rw [hcongr, intervalIntegral.integral_add h123 h4, intervalIntegral.integral_sub h12 h3,
      intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun q _ => (cJ q).intervalIntegrable),
      intervalIntegral.integral_finsetSum (fun q _ => (cI q).intervalIntegrable)]
    ring
  -- assembly
  have hsum := tendsto_finsetSum S hpacket
  have hsum1 := tendsto_finsetSum S l1
  simp only [Finset.sum_const_zero] at hsum1
  have hlim := (((lD.add (l0.const_mul (S.card : ℝ))).sub (hsum.const_mul (1 / 2))).sub
    (hsum1.const_mul (1 / 2))).add l2
  simp only [mul_zero, add_zero, zero_sub, sub_zero] at hlim
  have hL : -(1 / 2 * ∑ q ∈ S, d / (d ^ 2 + u q ^ 2)) = -(1 / 2) * ∑ q ∈ S, d / (d ^ 2 + u q ^ 2) := by ring
  rw [hL] at hlim
  have hmain : Tendsto (fun n => t n * Real.exp (-(d * t n)) * D a (t n)) atTop
      (𝓝 (-(1 / 2) * ∑ q ∈ S, d / (d ^ 2 + u q ^ 2))) := by
    refine hlim.congr fun n => ?_
    have h1 : (1 : ℝ) ≤ t n := by linarith [ht n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [Function.comp_apply]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hdecomp (t n) h1]
    ring
  have hneg : -(1 / 2) * ∑ q ∈ S, d / (d ^ 2 + u q ^ 2) < 0 := by
    have : 0 < ∑ q ∈ S, d / (d ^ 2 + u q ^ 2) :=
      Finset.sum_pos (fun q _ => by positivity) hSne
    linarith
  refine ⟨S, hSne, hS, t, ht, htop, hmain, hneg, ?_⟩
  have hgrow : Tendsto (fun n => Real.exp (d * t n) / t n) atTop atTop := by
    have h1 := (Real.tendsto_exp_div_pow_atTop 1).comp (htop.const_mul_atTop hd)
    have h2 := h1.const_mul_atTop hd
    refine h2.congr' ?_
    filter_upwards [htop.eventually_gt_atTop 0] with n hn
    simp only [Function.comp_apply, pow_one]
    field_simp
  refine (hmain.neg_mul_atTop hneg hgrow).congr' ?_
  filter_upwards [htop.eventually_gt_atTop 0] with n hn
  field_simp
  rw [mul_right_comm, ← Real.exp_add]
  simp

/-! ## The exact cutoff classification -/

/-- **Classification (I14), not-RH branch.**  For every real `a`,
`(∀ T > 0, D_a(T) ≥ 0) ↔ β ≤ a`. -/
theorem liEvenCrossActualClockDampedCutoff_nonneg_iff_of_not_rh (hnot : ¬RiemannHypothesis)
    (a : ℝ) : (∀ T, 0 < T → 0 ≤ D a T) ↔ β ≤ a := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨_, _, _, t, ht, _, _, _, hbot⟩ := liEvenCrossActualClockDampedCutoff_escape_of_not_rh hnot hlt
    obtain ⟨n, hn⟩ := (hbot.eventually (eventually_lt_atBot 0)).exists
    have := h (t n) (by linarith [ht n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  · intro ha T hT
    exact (liEvenCrossActualClockDampedCutoff_pos ha hT).le

/-- **Classification (I14).**  For every `a ≥ 0`, `(∀ T > 0, D_a(T) ≥ 0) ↔ β ≤ a`. -/
theorem liEvenCrossActualClockDampedCutoff_nonneg_iff {a : ℝ} (ha : 0 ≤ a) :
    (∀ T, 0 < T → 0 ≤ D a T) ↔ β ≤ a := by
  by_cases hRH : RiemannHypothesis
  · rw [liEvenCrossActualClockMaxGrowthRate_eq_zero_iff.2 hRH]
    exact ⟨fun _ => ha, fun _ T hT => (liEvenCrossActualClockDampedCutoff_pos_of_rh hRH a hT).le⟩
  · exact liEvenCrossActualClockDampedCutoff_nonneg_iff_of_not_rh hRH a

/-- RH holds iff every damped cutoff is positive, for every real damping. -/
theorem rh_iff_forall_liEvenCrossActualClockDampedCutoff_pos :
    RiemannHypothesis ↔ ∀ a T : ℝ, 0 < T → 0 < D a T := by
  constructor
  · intro hRH a T hT
    exact liEvenCrossActualClockDampedCutoff_pos_of_rh hRH a hT
  · intro h
    by_contra hnot
    have hβ := (liEvenCrossActualClockMaxGrowthRate_top_of_not_rh hnot).1
    have := (liEvenCrossActualClockDampedCutoff_nonneg_iff_of_not_rh hnot 0).1
      fun T hT => (h 0 T hT).le
    linarith

end RHTower
