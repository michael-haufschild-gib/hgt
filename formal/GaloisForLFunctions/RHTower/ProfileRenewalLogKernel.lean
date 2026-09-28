import GaloisForLFunctions.RHTower.ThetaRenewalLogKernel
import GaloisForLFunctions.HTGeometry.VolterraConvolutionCalculus

/-!
# The renewal log-kernel of a general increment and the all-real reflection

For a continuous increment `ν` and seam value `c > 0`, the logarithmic renewal kernel
`Q(t) = Σ_{m≥1} ν^{⋆m}(t)/(m c^m)` converges on the whole line (oriented Volterra convolutions),
is continuous, positive for positive increments, and satisfies the Volterra law
`c t Q(t) = t ν(t) + ∫₀^t ν(s)(t - s)Q(t - s) ds`. If `ν = aP - P'` for an even `C¹` profile `P`
with `P(0) = c`, then `Q(-t) + Q(t) = 2 sinh(at)/t`. For a positive increment of subcritical
weighted mass `∫₀^∞ e^{at} ν < c`, the denominator `c - N(s)` has no zeros on `Re s ≥ -a` and
`∫₀^∞ e^{-st} Q = -log(1 - N(s)/c)`.
-/

open Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable {ν : ℝ → ℝ}

/-! ## Convolution powers of an increment -/

/-- The convolution powers `ν^{⋆(m+1)}`. -/
def renewalPower (ν : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => ν
  | m + 1 => volterraConv ν (renewalPower ν m)

theorem continuous_renewalPower (hν : Continuous ν) (m : ℕ) : Continuous (renewalPower ν m) := by
  induction m with
  | zero => exact hν
  | succ m ih => exact continuous_volterraConv hν ih

theorem exists_bound_of_continuous (hν : Continuous ν) (T : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s, |s| ≤ T → |ν s| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hν.continuousOn (s := Icc (-T) T))
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  have := hC s ⟨(abs_le.mp hs).1, (abs_le.mp hs).2⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- `|ν^{⋆(m+1)}(t)| ≤ C^{m+1} |t|^m / m!` when `|ν| ≤ C` on `[-T, T]`, `|t| ≤ T`. -/
theorem abs_renewalPower_le {T C : ℝ} (hC : ∀ s, |s| ≤ T → |ν s| ≤ C) (m : ℕ) {t : ℝ}
    (ht : |t| ≤ T) : |renewalPower ν m t| ≤ C ^ (m + 1) * |t| ^ m / m.factorial := by
  induction m generalizing t with
  | zero => simpa [renewalPower] using hC t ht
  | succ m ih =>
    have h := abs_volterraConv_le (f := ν) (g := renewalPower ν m) (A := C) (B := C ^ (m + 1))
      (n := m) (fun s hs => hC s (hs.trans ht)) (fun s hs => ih (hs.trans ht))
    simp only [renewalPower]
    exact h.trans (le_of_eq (by ring))

theorem renewalPower_pos (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s) (m : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 < renewalPower ν m t := by
  induction m generalizing t with
  | zero => exact hpos t ht.le
  | succ m ih =>
    simp only [renewalPower, volterraConv]
    refine intervalIntegral.integral_pos ht ((by
      have := continuous_renewalPower hν m
      fun_prop : Continuous fun s => ν (t - s) * renewalPower ν m s) |>.continuousOn)
      (fun s hs => (mul_pos (hpos _ (by linarith [hs.2])) (ih hs.1)).le)
      ⟨t, ⟨ht.le, le_rfl⟩, mul_pos (hpos _ (by simp)) (ih ht)⟩

theorem renewalPower_nonneg (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s) (m : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ renewalPower ν m t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · cases m with
    | zero => exact (hpos 0 le_rfl).le
    | succ m => simp [renewalPower, volterraConv_apply_zero]
  · exact (renewalPower_pos hν hpos m ht).le

/-! ## The logarithmic renewal kernel -/

/-- The logarithmic renewal kernel `Q(t) = Σ_{m≥1} ν^{⋆m}(t)/(m c^m)` on the whole line. -/
def renewalLogKernel (ν : ℝ → ℝ) (c t : ℝ) : ℝ :=
  ∑' m : ℕ, renewalPower ν m t / ((m + 1) * c ^ (m + 1))

theorem abs_renewalLogKernel_term_le {c : ℝ} (hc : 0 < c) {T C : ℝ}
    (hC : ∀ s, |s| ≤ T → |ν s| ≤ C) (m : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    |renewalPower ν m t / ((m + 1) * c ^ (m + 1))| ≤ C / c * ((C / c * T) ^ m / m.factorial) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (by simpa using (abs_nonneg t).trans ht))
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * c ^ (m + 1))]
  have h1 := abs_renewalPower_le hC m ht
  have h2 : |t| ^ m ≤ T ^ m := pow_le_pow_left₀ (abs_nonneg t) ht m
  rw [div_le_iff₀ (by positivity)]
  calc |renewalPower ν m t| ≤ C ^ (m + 1) * |t| ^ m / m.factorial := h1
    _ ≤ C ^ (m + 1) * T ^ m / m.factorial := by gcongr
    _ ≤ C / c * ((C / c * T) ^ m / m.factorial) * (((m : ℝ) + 1) * c ^ (m + 1)) := by
        rw [mul_pow, div_pow]
        have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
        have e : C / c * (C ^ m / c ^ m * T ^ m / m.factorial) * (((m : ℝ) + 1) * c ^ (m + 1)) =
            ((m : ℝ) + 1) * (C ^ (m + 1) * T ^ m / m.factorial) := by
          field_simp; ring
        rw [e]
        have : 0 ≤ C ^ (m + 1) * T ^ m / m.factorial := by positivity
        nlinarith

theorem summable_renewalLogKernel_bound (c C T : ℝ) :
    Summable fun m : ℕ => C / c * ((C / c * T) ^ m / m.factorial) :=
  (Real.summable_pow_div_factorial _).mul_left _

theorem summable_renewalLogKernel_terms (hν : Continuous ν) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Summable fun m : ℕ => renewalPower ν m t / ((m + 1) * c ^ (m + 1)) := by
  obtain ⟨C, _, hC⟩ := exists_bound_of_continuous hν |t|
  exact Summable.of_norm_bounded (summable_renewalLogKernel_bound c C |t|) fun m => by
    rw [Real.norm_eq_abs]; exact abs_renewalLogKernel_term_le hc hC m le_rfl

theorem continuous_renewalLogKernel (hν : Continuous ν) {c : ℝ} (hc : 0 < c) :
    Continuous (renewalLogKernel ν c) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  set T := |t| + 1
  obtain ⟨C, _, hC⟩ := exists_bound_of_continuous hν T
  have hon : ContinuousOn (renewalLogKernel ν c) (Icc (-T) T) :=
    continuousOn_tsum (fun m => ((continuous_renewalPower hν m).div_const _).continuousOn)
      (summable_renewalLogKernel_bound c C T) fun m s hs => by
        rw [Real.norm_eq_abs]
        exact abs_renewalLogKernel_term_le hc hC m (abs_le.mpr ⟨hs.1, hs.2⟩)
  refine hon.continuousAt (Icc_mem_nhds ?_ ?_)
  · linarith [neg_abs_le t]
  · linarith [le_abs_self t]

theorem renewalLogKernel_pos (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s) {c : ℝ}
    (hc : 0 < c) {t : ℝ} (ht : 0 < t) : 0 < renewalLogKernel ν c t :=
  (summable_renewalLogKernel_terms hν hc t).tsum_pos
    (fun m => div_nonneg (renewalPower_pos hν hpos m ht).le (by positivity)) 0
    (div_pos (renewalPower_pos hν hpos 0 ht) (by positivity))

/-! ## The positive Volterra law -/

/-- The moment-weighted increment `(τν)(s) = s ν(s)`. -/
def renewalMomentIncrement (ν : ℝ → ℝ) (s : ℝ) : ℝ := s * ν s

theorem continuous_renewalMomentIncrement (hν : Continuous ν) :
    Continuous (renewalMomentIncrement ν) := by
  unfold renewalMomentIncrement; fun_prop

/-- `t ν^{⋆(m+2)}(t) = (m+2) ((τν) ⋆ ν^{⋆(m+1)})(t)`. -/
theorem mul_renewalPower_succ (hν : Continuous ν) (m : ℕ) (t : ℝ) :
    t * renewalPower ν (m + 1) t =
      (m + 2) * volterraConv (renewalMomentIncrement ν) (renewalPower ν m) t := by
  have hτ := continuous_renewalMomentIncrement hν
  induction m generalizing t with
  | zero =>
    have hτdef : (fun s => s * ν s) = renewalMomentIncrement ν := rfl
    simp only [renewalPower]
    rw [mul_volterraConv hν hν, hτdef, volterraConv_comm ν (renewalMomentIncrement ν)]
    push_cast; ring
  | succ m ih =>
    have hA := continuous_renewalPower hν m
    have hA1 := continuous_renewalPower hν (m + 1)
    have hfun : (fun s => s * renewalPower ν (m + 1) s) =
        fun s => ((m : ℝ) + 2) * volterraConv (renewalMomentIncrement ν) (renewalPower ν m) s :=
      funext ih
    have hassoc : volterraConv ν (volterraConv (renewalMomentIncrement ν) (renewalPower ν m)) t =
        volterraConv (renewalMomentIncrement ν) (renewalPower ν (m + 1)) t := by
      rw [← volterraConv_assoc hν hτ hA, volterraConv_comm' ν (renewalMomentIncrement ν),
        volterraConv_assoc hτ hν hA]
      rfl
    conv_lhs => rw [show renewalPower ν (m + 1 + 1) = volterraConv ν (renewalPower ν (m + 1))
      from rfl]
    have hτdef : (fun s => s * ν s) = renewalMomentIncrement ν := rfl
    rw [mul_volterraConv hν hA1, hfun, hτdef, volterraConv_smul_right, hassoc]
    push_cast; ring

/-- The series `S(t) = Σ_{m≥0} ((τν) ⋆ ν^{⋆(m+1)})(t)/c^{m+2}`. -/
def renewalMomentSeries (ν : ℝ → ℝ) (c t : ℝ) : ℝ :=
  ∑' m : ℕ, volterraConv (renewalMomentIncrement ν) (renewalPower ν m) t / c ^ (m + 2)

theorem renewalMomentSeries_term_eq (hν : Continuous ν) {c : ℝ} (hc : 0 < c) (m : ℕ) (t : ℝ) :
    volterraConv (renewalMomentIncrement ν) (renewalPower ν m) t / c ^ (m + 2) =
      t * (renewalPower ν (m + 1) t / ((((m + 1 : ℕ) : ℝ) + 1) * c ^ (m + 1 + 1))) := by
  have h := mul_renewalPower_succ hν m t
  have hm : ((m : ℝ) + 2) ≠ 0 := by positivity
  rw [mul_div_assoc', h]
  push_cast
  rw [show (m : ℝ) + 1 + 1 = m + 2 by ring, show m + 1 + 1 = m + 2 by ring]
  field_simp

theorem mul_renewalLogKernel_eq (hν : Continuous ν) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    t * renewalLogKernel ν c t = t * ν t / c + renewalMomentSeries ν c t := by
  have hsum := (summable_renewalLogKernel_terms hν hc t).mul_left t
  rw [renewalLogKernel, ← tsum_mul_left, hsum.tsum_eq_zero_add, renewalMomentSeries]
  congr 1
  · simp [renewalPower]; ring
  · refine tsum_congr fun m => ?_
    rw [renewalMomentSeries_term_eq hν hc]

theorem abs_renewalMomentSeries_term_le (hν : Continuous ν) {c : ℝ} (hc : 0 < c) {T C : ℝ}
    (hC : ∀ s, |s| ≤ T → |ν s| ≤ C) (m : ℕ) {s : ℝ} (hs : |s| ≤ T) :
    |volterraConv (renewalMomentIncrement ν) (renewalPower ν m) s / c ^ (m + 2)| ≤
      T * (C / c * ((C / c * T) ^ (m + 1) / (m + 1).factorial)) := by
  rw [renewalMomentSeries_term_eq hν hc, abs_mul]
  exact mul_le_mul hs (abs_renewalLogKernel_term_le hc hC (m + 1) hs) (abs_nonneg _)
    ((abs_nonneg _).trans hs)

theorem continuous_renewalMomentSeries (hν : Continuous ν) {c : ℝ} (hc : 0 < c) :
    Continuous (renewalMomentSeries ν c) := by
  have h : renewalMomentSeries ν c = fun t => t * renewalLogKernel ν c t - t * ν t / c := by
    funext t; rw [mul_renewalLogKernel_eq hν hc]; ring
  rw [h]
  have := continuous_renewalLogKernel hν hc
  fun_prop

/-- **The positive Volterra law.** `c t Q(t) = t ν(t) + ∫₀^t ν(s)(t - s) Q(t - s) ds`. -/
theorem renewal_volterra_law (hν : Continuous ν) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    c * (t * renewalLogKernel ν c t) = t * ν t +
      volterraConv ν (fun s => s * renewalLogKernel ν c s) t := by
  have hτ := continuous_renewalMomentIncrement hν
  have hS := continuous_renewalMomentSeries hν hc
  have hfun : (fun s => s * renewalLogKernel ν c s) =
      (fun s => (1 / c) * renewalMomentIncrement ν s) + renewalMomentSeries ν c := by
    funext s; simp only [Pi.add_apply, renewalMomentIncrement]
    rw [mul_renewalLogKernel_eq hν hc]; ring
  obtain ⟨C, _, hC⟩ := exists_bound_of_continuous hν |t|
  have hconvS : volterraConv ν (renewalMomentSeries ν c) t =
      ∑' m : ℕ, volterraConv (renewalMomentIncrement ν) (renewalPower ν (m + 1)) t /
        c ^ (m + 2) := by
    rw [show renewalMomentSeries ν c = fun t => ∑' m : ℕ,
      volterraConv (renewalMomentIncrement ν) (renewalPower ν m) t / c ^ (m + 2) from rfl,
      volterraConv_tsum hν (fun m => (continuous_volterraConv hτ
        (continuous_renewalPower hν m)).div_const _)
        (summable_renewalLogKernel_bound c C |t| |>.comp_injective (add_left_injective 1)
          |>.mul_left |t|)
        (fun m s hs => abs_renewalMomentSeries_term_le hν hc hC m hs)]
    refine tsum_congr fun m => ?_
    have := volterraConv_smul_right (1 / c ^ (m + 2)) ν
      (volterraConv (renewalMomentIncrement ν) (renewalPower ν m)) t
    simp only [one_div_mul_eq_div] at this
    rw [show (fun s => volterraConv (renewalMomentIncrement ν) (renewalPower ν m) s /
      c ^ (m + 2)) = fun s => 1 / c ^ (m + 2) *
        volterraConv (renewalMomentIncrement ν) (renewalPower ν m) s by funext s; ring,
      volterraConv_smul_right, ← volterraConv_assoc hν hτ (continuous_renewalPower hν m),
      volterraConv_comm' ν (renewalMomentIncrement ν),
      volterraConv_assoc hτ hν (continuous_renewalPower hν m)]
    simp only [renewalPower]
    ring
  have hcS : c * renewalMomentSeries ν c t =
      volterraConv (renewalMomentIncrement ν) ν t / c +
        ∑' m : ℕ, volterraConv (renewalMomentIncrement ν) (renewalPower ν (m + 1)) t /
          c ^ (m + 2) := by
    have hsumm : Summable fun m : ℕ =>
        volterraConv (renewalMomentIncrement ν) (renewalPower ν m) t / c ^ (m + 2) := by
      refine Summable.of_norm_bounded ((summable_renewalLogKernel_bound c C |t|
        |>.comp_injective (add_left_injective 1)).mul_left |t|) fun m => ?_
      rw [Real.norm_eq_abs]
      exact abs_renewalMomentSeries_term_le hν hc hC m le_rfl
    rw [renewalMomentSeries, ← tsum_mul_left, (hsumm.mul_left _).tsum_eq_zero_add]
    congr 1
    · simp only [renewalPower]; field_simp; ring
    · refine tsum_congr fun m => ?_
      field_simp; ring
  rw [hfun, volterraConv_add_right (g := fun s => 1 / c * renewalMomentIncrement ν s)
    (h := renewalMomentSeries ν c) hν (by fun_prop) hS, volterraConv_smul_right, hconvS,
    volterraConv_comm ν (renewalMomentIncrement ν), mul_renewalLogKernel_eq hν hc,
    mul_add, hcS]
  field_simp

/-! ## The all-real reflection law for an even profile -/

section Reflection

variable {P : ℝ → ℝ} {a c : ℝ}

/-- `(e^{a·} ⋆ ν)(t) = c e^{at} - P(t)` for a profile with `P' = aP - ν`, `P(0) = c`. -/
theorem volterraConv_exp_renewal (hν : Continuous ν) (hP : ∀ t, HasDerivAt P (a * P t - ν t) t)
    (hP0 : P 0 = c) (t : ℝ) :
    volterraConv (fun s => Real.exp (a * s)) ν t = c * Real.exp (a * t) - P t := by
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  rw [volterraConv]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => -(Real.exp (a * (t - s)) * P s))
      (Real.exp (a * (t - s)) * ν s) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp (a * (t - s))) (Real.exp (a * (t - s)) * (-a)) s := by
      have := (((hasDerivAt_id s).const_sub t).const_mul a).exp
      simpa using this
    refine (h1.mul (hP s)).neg.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun s => Real.exp (a * (t - s)) * ν s).intervalIntegrable _ _), hP0]
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero, one_mul]
  ring

/-- `(e^{a·} ⋆ τν)(t) = -t P(t) + (e^{a·} ⋆ P)(t)`. -/
theorem volterraConv_exp_renewalMoment (hν : Continuous ν) (hP : ∀ t, HasDerivAt P (a * P t - ν t) t)
    (t : ℝ) :
    volterraConv (fun s => Real.exp (a * s)) (renewalMomentIncrement ν) t =
      -(t * P t) + volterraConv (fun s => Real.exp (a * s)) P t := by
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  rw [volterraConv, volterraConv]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => -(s * Real.exp (a * (t - s)) * P s))
      (s * Real.exp (a * (t - s)) * ν s - Real.exp (a * (t - s)) * P s) s := by
    intro s _
    have h1 : HasDerivAt (fun s => Real.exp (a * (t - s))) (Real.exp (a * (t - s)) * (-a)) s := by
      have := (((hasDerivAt_id s).const_sub t).const_mul a).exp
      simpa using this
    refine (((hasDerivAt_id' s).mul h1).mul (hP s)).neg.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hsplit : (∫ s in (0 : ℝ)..t, Real.exp (a * (t - s)) * renewalMomentIncrement ν s) =
      (∫ s in (0 : ℝ)..t, (s * Real.exp (a * (t - s)) * ν s - Real.exp (a * (t - s)) * P s)) +
      ∫ s in (0 : ℝ)..t, Real.exp (a * (t - s)) * P s := by
    rw [← intervalIntegral.integral_add
      ((by fun_prop : Continuous fun s => s * Real.exp (a * (t - s)) * ν s -
        Real.exp (a * (t - s)) * P s).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => Real.exp (a * (t - s)) * P s).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [renewalMomentIncrement]; ring
  rw [hsplit, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun s => s * Real.exp (a * (t - s)) * ν s -
      Real.exp (a * (t - s)) * P s).intervalIntegrable _ _)]
  simp

/-- `P ⋆ (τQ) = -τP + e^{a·} ⋆ P`. -/
theorem volterraConv_profile_momentKernel (hν : Continuous ν) (hc : 0 < c)
    (hP : ∀ t, HasDerivAt P (a * P t - ν t) t) (hP0 : P 0 = c) (t : ℝ) :
    volterraConv P (fun s => s * renewalLogKernel ν c s) t =
      -(t * P t) + volterraConv (fun s => Real.exp (a * s)) P t := by
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have he : Continuous fun s : ℝ => Real.exp (a * s) := by fun_prop
  have hτ := continuous_renewalMomentIncrement hν
  have hw : Continuous fun s => s * renewalLogKernel ν c s := by
    have := continuous_renewalLogKernel hν hc; fun_prop
  have hνw := continuous_volterraConv hν hw
  have hlaw : (fun s => c * (s * renewalLogKernel ν c s)) =
      renewalMomentIncrement ν + volterraConv ν (fun s => s * renewalLogKernel ν c s) := by
    funext s
    simp only [Pi.add_apply, renewalMomentIncrement]
    exact renewal_volterra_law hν hc s
  have h1 : volterraConv (fun s => Real.exp (a * s)) (fun s => c * (s * renewalLogKernel ν c s)) t =
      c * volterraConv (fun s => Real.exp (a * s)) (fun s => s * renewalLogKernel ν c s) t :=
    volterraConv_smul_right _ _ _ _
  rw [hlaw, volterraConv_add_right he hτ hνw, volterraConv_exp_renewalMoment hν hP,
    ← volterraConv_assoc he hν hw] at h1
  have hE1 : volterraConv (fun s => Real.exp (a * s)) ν = fun s => c * Real.exp (a * s) - P s :=
    funext (volterraConv_exp_renewal hν hP hP0)
  rw [hE1, volterraConv_comm (fun s => c * Real.exp (a * s) - P s),
    volterraConv_sub_right (g := fun s => c * Real.exp (a * s)) (h := P) hw
      (continuous_const.mul he) hPc, volterraConv_smul_right,
    volterraConv_comm (fun s => s * renewalLogKernel ν c s),
    volterraConv_comm (fun s => s * renewalLogKernel ν c s)] at h1
  linarith

/-- The reflection profile `y(t) = e^{-at} + t Q(t)`. -/
def renewalReflectionProfile (ν : ℝ → ℝ) (a c t : ℝ) : ℝ :=
  Real.exp (-(a * t)) + t * renewalLogKernel ν c t

theorem continuous_renewalReflectionProfile (hν : Continuous ν) (hc : 0 < c) :
    Continuous (renewalReflectionProfile ν a c) := by
  have := continuous_renewalLogKernel hν hc
  unfold renewalReflectionProfile; fun_prop

/-- `P ⋆ y = P ⋆ (e^{-a·} + e^{a·}) - τP`. -/
theorem volterraConv_profile_reflectionProfile (hν : Continuous ν) (hc : 0 < c)
    (hP : ∀ t, HasDerivAt P (a * P t - ν t) t) (hP0 : P 0 = c) (t : ℝ) :
    volterraConv P (renewalReflectionProfile ν a c) t =
      volterraConv P (fun s => Real.exp (-(a * s)) + Real.exp (a * s)) t - t * P t := by
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have he : Continuous fun s : ℝ => Real.exp (a * s) := by fun_prop
  have he' : Continuous fun s : ℝ => Real.exp (-(a * s)) := by fun_prop
  have hw : Continuous fun s => s * renewalLogKernel ν c s := by
    have := continuous_renewalLogKernel hν hc; fun_prop
  rw [show renewalReflectionProfile ν a c = (fun s => Real.exp (-(a * s))) +
      fun s => s * renewalLogKernel ν c s from rfl, volterraConv_add_right hPc he' hw,
    volterraConv_profile_momentKernel hν hc hP hP0,
    show (fun s : ℝ => Real.exp (-(a * s)) + Real.exp (a * s)) =
      (fun s => Real.exp (-(a * s))) + fun s => Real.exp (a * s) from rfl,
    volterraConv_add_right hPc he' he, volterraConv_comm (fun s => Real.exp (a * s))]
  ring

/-- The reflection profile `y(t) = e^{-at} + t Q(t)` is even. -/
theorem renewalReflectionProfile_neg (hν : Continuous ν) (hc : 0 < c)
    (hP : ∀ t, HasDerivAt P (a * P t - ν t) t) (hP0 : P 0 = c) (hPe : ∀ t, P (-t) = P t) (t : ℝ) :
    renewalReflectionProfile ν a c (-t) = renewalReflectionProfile ν a c t := by
  have hPc : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  have hy := continuous_renewalReflectionProfile (a := a) hν hc
  have he : Continuous fun s : ℝ => Real.exp (a * s) := by fun_prop
  set y := renewalReflectionProfile ν a c
  set yr : ℝ → ℝ := fun s => y (-s)
  have hyr : Continuous yr := hy.comp continuous_neg
  have hPe' : (fun s => P (-s)) = P := funext hPe
  set h2 : ℝ → ℝ := fun s => Real.exp (-(a * s)) + Real.exp (a * s)
  have hh2 : (fun s => h2 (-s)) = h2 := by funext s; simp only [h2]; ring_nf
  have hPh : ∀ u, volterraConv P h2 (-u) = -volterraConv P h2 u := by
    intro u; rw [volterraConv_neg, hPe', hh2]
  have heq : ∀ u, volterraConv P yr u = volterraConv P y u := by
    intro u
    have h := volterraConv_neg P yr (-u)
    rw [neg_neg, hPe'] at h
    have hyy : (fun s => yr (-s)) = y := by funext s; simp [yr]
    rw [hyy] at h
    rw [h, volterraConv_profile_reflectionProfile hν hc hP hP0,
      volterraConv_profile_reflectionProfile hν hc hP hP0, hPh, hPe]
    ring
  set f : ℝ → ℝ := fun s => yr s - y s
  have hf : Continuous f := hyr.sub hy
  have hPf : ∀ u, volterraConv P f u = 0 := by
    intro u
    rw [show f = fun s => yr s - y s from rfl, volterraConv_sub_right hPc hyr hy, heq, sub_self]
  have hPdecomp : P = fun s => c * Real.exp (a * s) -
      volterraConv (fun s => Real.exp (a * s)) ν s := by
    funext s; rw [volterraConv_exp_renewal hν hP hP0]; ring
  have hEc := continuous_volterraConv he hν
  have hkey : ∀ u, volterraConv (fun s => Real.exp (a * s))
      (fun s => c * f s - volterraConv ν f s) u = 0 := by
    intro u
    have h := hPf u
    rw [hPdecomp, volterraConv_comm, volterraConv_sub_right (g := fun s => c * Real.exp (a * s))
      (h := volterraConv (fun s => Real.exp (a * s)) ν) hf (continuous_const.mul he) hEc,
      volterraConv_smul_right, volterraConv_comm f, volterraConv_comm f,
      volterraConv_assoc he hν hf] at h
    rw [volterraConv_sub_right (g := fun s => c * f s) (h := volterraConv ν f) he
      (continuous_const.mul hf) (continuous_volterraConv hν hf), volterraConv_smul_right]
    linarith
  have h0 := eq_zero_of_volterraConv_exp_eq_zero ((continuous_const.mul hf).sub
    (continuous_volterraConv hν hf)) hkey
  have hf0 := eq_zero_of_mul_eq_volterraConv hc.ne' hν hf fun u => by
    have := congrFun h0 u
    simp only [Pi.zero_apply, Pi.sub_apply, Pi.mul_apply] at this
    linarith
  have := congrFun hf0 t
  simp only [f, yr, Pi.zero_apply] at this
  linarith

/-- **The universal reflection.** For an even profile `P` with `P' = aP - ν` and `P(0) = c > 0`,
`Q(-t) + Q(t) = 2 sinh(at)/t` for `t ≠ 0`. -/
theorem renewalLogKernel_neg_add (hν : Continuous ν) (hc : 0 < c)
    (hP : ∀ t, HasDerivAt P (a * P t - ν t) t) (hP0 : P 0 = c) (hPe : ∀ t, P (-t) = P t)
    {t : ℝ} (ht : t ≠ 0) :
    renewalLogKernel ν c (-t) + renewalLogKernel ν c t = 2 * Real.sinh (a * t) / t := by
  have h := renewalReflectionProfile_neg hν hc hP hP0 hPe t
  simp only [renewalReflectionProfile] at h
  rw [Real.sinh_eq, eq_div_iff ht]
  rw [show -(a * -t) = a * t by ring] at h
  linear_combination (-1 : ℝ) * h

end Reflection

/-! ## Integrability of nonnegative convolutions -/

/-- The half-line convolution of two nonnegative integrable continuous functions is integrable. -/
theorem integrableOn_volterraConv_of_nonneg {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G)
    (hF0 : ∀ t, 0 ≤ t → 0 ≤ F t) (hG0 : ∀ t, 0 ≤ t → 0 ≤ G t)
    (hFi : IntegrableOn F (Ioi 0)) (hGi : IntegrableOn G (Ioi 0)) :
    IntegrableOn (volterraConv F G) (Ioi 0) := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let K : ℝ → ℝ → ℝ := fun t u => if u ≤ t then F (t - u) * G u else 0
  have hmeas : Measurable (Function.uncurry K) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      ((by fun_prop : Continuous fun p : ℝ × ℝ => F (p.1 - p.2) * G p.2).measurable)
      measurable_const
  have hshift : ∀ u, IntegrableOn (fun t => F (t - u)) (Ici u) := by
    intro u
    have h1 : IntegrableOn (fun t => F (t - u)) (Ioi u) := by
      have := (measurePreserving_add_right volume u).integrableOn_comp_preimage
        (measurableEmbedding_addRight u) (f := fun t => F (t - u)) (s := Ioi u)
      have hpre : (fun x : ℝ => x + u) ⁻¹' Ioi u = Ioi 0 := by ext x; simp
      rw [hpre] at this
      refine this.mp ?_
      refine hFi.congr_fun (fun t _ => ?_) measurableSet_Ioi
      simp
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr h1
  have hshiftInt : ∀ u, ∫ t in Ici u, F (t - u) = ∫ t in Ioi 0, F t := by
    intro u
    rw [integral_Ici_eq_integral_Ioi]
    have h := (measurePreserving_add_right volume u).setIntegral_preimage_emb
      (measurableEmbedding_addRight u) (fun t => F (t - u)) (Ioi u)
    have hpre : (fun x : ℝ => x + u) ⁻¹' Ioi u = Ioi 0 := by ext x; simp
    rw [hpre] at h
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp
  have hK : Integrable (Function.uncurry K) (μ.prod μ) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_), ?_⟩
    · have hind : (fun t => Function.uncurry K (t, u)) =
          (Ici u).indicator (fun t => F (t - u) * G u) := by
        funext t; simp only [Function.uncurry, K, Set.indicator, mem_Ici]
      rw [hind, integrable_indicator_iff measurableSet_Ici]
      exact ((hshift u).mul_const (G u)).mono_measure
        (Measure.restrict_mono_measure Measure.restrict_le_self _)
    · refine Integrable.congr (hGi.const_mul (∫ r in Ioi (0 : ℝ), F r)) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      have hu0 : (0 : ℝ) < u := hu
      have hind : (fun t => ‖Function.uncurry K (t, u)‖) =
          (Ici u).indicator (fun t => F (t - u) * G u) := by
        funext t; simp only [Function.uncurry, K, Set.indicator, mem_Ici]
        split_ifs with h
        · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 _ (by linarith)) (hG0 _ hu0.le))]
        · simp
      simp only
      rw [hind, setIntegral_indicator measurableSet_Ici,
        show Ioi (0 : ℝ) ∩ Ici u = Ici u by
          ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ici]; constructor
          · exact fun h => h.2
          · exact fun h => ⟨lt_of_lt_of_le hu0 h, h⟩,
        integral_mul_const, hshiftInt]
  have hint := hK.integral_prod_left
  refine hint.congr ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht0 : (0 : ℝ) < t := ht
  simp only [Function.uncurry]
  have hind : (fun u => K t u) = (Iic t).indicator (fun u => F (t - u) * G u) := by
    funext u; simp only [K, Set.indicator, mem_Iic]
  rw [hind, setIntegral_indicator measurableSet_Iic,
    show Ioi (0 : ℝ) ∩ Iic t = Ioc 0 t by ext x; simp [and_comm],
    volterraConv, intervalIntegral.integral_of_le ht0.le]

/-! ## The Laplace identity and stability -/

section Laplace

variable {a c : ℝ}

/-- The complex Laplace transform `N(s) = ∫₀^∞ e^{-st} ν(t) dt`. -/
def renewalLaplace (ν : ℝ → ℝ) (s : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (ν t : ℂ)

theorem integrableOn_exp_mul_renewalPower (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s)
    (hint : IntegrableOn (fun t => Real.exp (a * t) * ν t) (Ioi 0)) (m : ℕ) :
    IntegrableOn (fun t => Real.exp (a * t) * renewalPower ν m t) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (a * t) * renewalPower ν m t =
        (∫ t in Ioi (0 : ℝ), Real.exp (a * t) * ν t) ^ (m + 1) := by
  induction m with
  | zero => exact ⟨hint, by simp [renewalPower]⟩
  | succ m ih =>
    obtain ⟨hi, hv⟩ := ih
    have he : Continuous fun s : ℝ => Real.exp (a * s) := by fun_prop
    have hF : Continuous fun s => Real.exp (a * s) * ν s := he.mul hν
    have hG : Continuous fun s => Real.exp (a * s) * renewalPower ν m s :=
      he.mul (continuous_renewalPower hν m)
    have hF0 : ∀ t, 0 ≤ t → 0 ≤ Real.exp (a * t) * ν t := fun t ht =>
      mul_nonneg (Real.exp_pos _).le (hpos t ht).le
    have hG0 : ∀ t, 0 ≤ t → 0 ≤ Real.exp (a * t) * renewalPower ν m t := fun t ht =>
      mul_nonneg (Real.exp_pos _).le (renewalPower_nonneg hν hpos m ht)
    have hfun : (fun t => Real.exp (a * t) * renewalPower ν (m + 1) t) =
        volterraConv (fun s => Real.exp (a * s) * ν s)
          (fun s => Real.exp (a * s) * renewalPower ν m s) := by
      funext t; simp only [renewalPower]; exact exp_mul_volterraConv a ν (renewalPower ν m) t
    rw [hfun]
    refine ⟨integrableOn_volterraConv_of_nonneg hF hG hF0 hG0 hint hi, ?_⟩
    rw [integral_Ioi_volterraConv hF hG
      (hint.congr_fun (fun t ht => (abs_of_nonneg (hF0 t (le_of_lt ht))).symm) measurableSet_Ioi)
      (hi.congr_fun (fun t ht => (abs_of_nonneg (hG0 t (le_of_lt ht))).symm) measurableSet_Ioi),
      hv, pow_succ]
    ring

/-- `∫₀^∞ e^{-st} ν^{⋆(m+1)} = N(s)^{m+1}` on `Re s ≥ -a`. -/
theorem integral_cexp_mul_renewalPower (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s)
    (hint : IntegrableOn (fun t => Real.exp (a * t) * ν t) (Ioi 0)) {s : ℂ} (hs : -a ≤ s.re)
    (m : ℕ) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (renewalPower ν m t : ℂ)) =
      renewalLaplace ν s ^ (m + 1) := by
  have hdom : ∀ n, IntegrableOn (fun t => Real.exp (-(s.re * t)) * |renewalPower ν n t|) (Ioi 0) := by
    intro n
    refine (integrableOn_exp_mul_renewalPower hν hpos hint n).1.mono'
      ((by have := continuous_renewalPower hν n; fun_prop : Continuous fun t =>
        Real.exp (-(s.re * t)) * |renewalPower ν n t|).aestronglyMeasurable.restrict)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (renewalPower_nonneg hν hpos n ht0)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
      (renewalPower_nonneg hν hpos n ht0)
  induction m with
  | zero => simp [renewalPower, renewalLaplace]
  | succ m ih =>
    simp only [renewalPower]
    rw [integral_Ioi_cexp_mul_volterraConv hν (continuous_renewalPower hν m) (hdom 0) (hdom m), ih]
    rw [← renewalLaplace, pow_succ]
    ring

theorem norm_renewalLaplace_le (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s)
    (hint : IntegrableOn (fun t => Real.exp (a * t) * ν t) (Ioi 0)) {s : ℂ} (hs : -a ≤ s.re) :
    ‖renewalLaplace ν s‖ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (a * t) * ν t := by
  rw [renewalLaplace]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on ?_ hint measurableSet_Ioi
    fun t ht => ?_)
  · refine hint.mono' ((by fun_prop : Continuous fun t : ℝ =>
      ‖Complex.exp (-(s * t)) * (ν t : ℂ)‖).aestronglyMeasurable.restrict)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_norm, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hpos t (le_of_lt ht))]
    have : (-(s * (t : ℂ))).re = -(s.re * t) := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [(le_of_lt ht : (0:ℝ) ≤ t)]))
      (hpos t (le_of_lt ht)).le
  · have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos t ht0)]
    have : (-(s * (t : ℂ))).re = -(s.re * t) := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) (hpos t ht0).le

/-- **Stability.** With subcritical weighted mass `∫₀^∞ e^{at} ν < c`, the denominator
`D(s) = c - N(s)` has no zeros on `Re s ≥ -a`. -/
theorem renewalDenominator_ne_zero (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s)
    (hint : IntegrableOn (fun t => Real.exp (a * t) * ν t) (Ioi 0))
    (hmass : ∫ t in Ioi (0 : ℝ), Real.exp (a * t) * ν t < c) {s : ℂ} (hs : -a ≤ s.re) :
    (c : ℂ) - renewalLaplace ν s ≠ 0 := by
  intro h
  have hN := norm_renewalLaplace_le hν hpos hint hs
  rw [show renewalLaplace ν s = c by linear_combination -h, Complex.norm_real,
    Real.norm_eq_abs] at hN
  linarith [le_abs_self c]

/-- **The logarithmic renewal identity.** On `Re s ≥ -a`,
`∫₀^∞ e^{-st} Q(t) dt = -log(1 - N(s)/c)`, and `c - N(s) = c exp(-Q̂(s))`. -/
theorem integral_cexp_mul_renewalLogKernel (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s)
    (hint : IntegrableOn (fun t => Real.exp (a * t) * ν t) (Ioi 0)) (hc : 0 < c)
    (hmass : ∫ t in Ioi (0 : ℝ), Real.exp (a * t) * ν t < c) {s : ℂ} (hs : -a ≤ s.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (renewalLogKernel ν c t : ℂ)) =
      -Complex.log (1 - renewalLaplace ν s / c) := by
  set M := ∫ t in Ioi (0 : ℝ), Real.exp (a * t) * ν t
  have hM0 : 0 < M := setIntegral_pos_iff_support_of_nonneg_ae (f := fun t => Real.exp (a * t) * ν t)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
      mul_nonneg (Real.exp_pos _).le (hpos t (le_of_lt ht)).le)) hint |>.mpr (by
        rw [show Function.support (fun t => Real.exp (a * t) * ν t) ∩ Ioi 0 = Ioi 0 by
          ext t; simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨(mul_pos (Real.exp_pos _) (hpos t h.le)).ne', h⟩]
        simp)
  have hq : M / c < 1 := (div_lt_one hc).mpr hmass
  have hq0 : 0 < M / c := div_pos hM0 hc
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set F : ℕ → ℝ → ℂ := fun m t =>
    Complex.exp (-(s * t)) * ((renewalPower ν m t / ((m + 1) * c ^ (m + 1)) : ℝ) : ℂ)
  have hPi := fun m => integrableOn_exp_mul_renewalPower hν hpos hint m
  have hnormF : ∀ m t, 0 ≤ t → ‖F m t‖ ≤
      Real.exp (a * t) * renewalPower ν m t / ((m + 1) * c ^ (m + 1)) := by
    intro m t ht
    simp only [F]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * c ^ (m + 1)),
      abs_of_nonneg (renewalPower_nonneg hν hpos m ht)]
    have hre : (-(s * (t : ℂ))).re = -(s.re * t) := by simp
    rw [hre, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
      (div_nonneg (renewalPower_nonneg hν hpos m ht) (by positivity))
  have hFi : ∀ m, Integrable (F m) (volume.restrict (Ioi 0)) := by
    intro m
    refine ((hPi m).1.div_const (((m : ℝ) + 1) * c ^ (m + 1))).mono'
      ((by have := continuous_renewalPower hν m; fun_prop : Continuous (F m)).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        hnormF m t (le_of_lt ht)))
  have hFle : ∀ m, (∫ t in Ioi (0 : ℝ), ‖F m t‖) ≤ (M / c) ^ (m + 1) / (m + 1) := by
    intro m
    calc (∫ t in Ioi (0 : ℝ), ‖F m t‖) ≤ ∫ t in Ioi (0 : ℝ),
          Real.exp (a * t) * renewalPower ν m t / ((m + 1) * c ^ (m + 1)) :=
          setIntegral_mono_on (hFi m).norm ((hPi m).1.div_const _) measurableSet_Ioi
            fun t ht => hnormF m t (le_of_lt ht)
      _ = M ^ (m + 1) / ((m + 1) * c ^ (m + 1)) := by rw [integral_div, (hPi m).2]
      _ = (M / c) ^ (m + 1) / (m + 1) := by rw [div_pow]; field_simp
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := M / c)
    (by rw [abs_of_pos hq0]; exact hq)
  have hsumm : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _) hFle hlog.summable
  have hpt : ∀ t : ℝ, Complex.exp (-(s * t)) * (renewalLogKernel ν c t : ℂ) = ∑' m, F m t := by
    intro t
    rw [renewalLogKernel, Complex.ofReal_tsum, ← tsum_mul_left]
  have hFint : ∀ m, (∫ t in Ioi (0 : ℝ), F m t) =
      renewalLaplace ν s ^ (m + 1) / (((m : ℂ) + 1) * (c : ℂ) ^ (m + 1)) := by
    intro m
    rw [← integral_cexp_mul_renewalPower hν hpos hint hs m, div_eq_mul_inv, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [F]
    push_cast
    field_simp
  have hz : ‖renewalLaplace ν s / (c : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, div_lt_one hc]
    exact lt_of_le_of_lt (norm_renewalLaplace_le hν hpos hint hs) hmass
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFi hsumm]
  simp_rw [hFint]
  have hser := Complex.hasSum_taylorSeries_neg_log hz
  have hser1 := (hasSum_nat_add_iff' 1).mpr hser
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
    sub_zero] at hser1
  rw [← hser1.tsum_eq]
  refine tsum_congr fun m => ?_
  push_cast
  rw [div_pow]
  field_simp

/-- `c - N(s) = c exp(-Q̂(s))` on `Re s ≥ -a`. -/
theorem renewalDenominator_eq_exp (hν : Continuous ν) (hpos : ∀ s, 0 ≤ s → 0 < ν s)
    (hint : IntegrableOn (fun t => Real.exp (a * t) * ν t) (Ioi 0)) (hc : 0 < c)
    (hmass : ∫ t in Ioi (0 : ℝ), Real.exp (a * t) * ν t < c) {s : ℂ} (hs : -a ≤ s.re) :
    (c : ℂ) - renewalLaplace ν s =
      c * Complex.exp (-∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (renewalLogKernel ν c t : ℂ)) := by
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hne : 1 - renewalLaplace ν s / c ≠ 0 := by
    intro h
    apply renewalDenominator_ne_zero hν hpos hint hmass hs
    have h1 := sub_eq_zero.mp h
    rw [eq_div_iff hcC, one_mul] at h1
    rw [h1, sub_self]
  rw [integral_cexp_mul_renewalLogKernel hν hpos hint hc hmass hs, neg_neg, Complex.exp_log hne]
  field_simp

end Laplace

end

end RHTower
