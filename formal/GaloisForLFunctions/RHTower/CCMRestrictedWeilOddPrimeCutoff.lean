import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimePoleMatrix

/-!
# Unique sign cutoff for literal odd-pole prime atoms

The normalized hyperbolic overlap decreases strictly in the positive half-log
shift. At every positive aperture it has exactly one zero, strictly between
one third and one half of the aperture. These are exact analytic inequalities;
no numerical prime data, RH premise, or full-source positivity is used.
The actual transport operator and signed prime budgets are connected in the
successor leaf.
-/

open Set
noncomputable section
namespace RHTower

private theorem sinh_lt_self_mul_cosh {x : ℝ} (hx : 0<x) :
    Real.sinh x < x*Real.cosh x := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t*Real.cosh t-Real.sinh t)
      (t*Real.sinh t) t := by
    intro t
    convert! ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
      (Real.hasDerivAt_sinh t) using 1; simp
  have hm : StrictMonoOn (fun t : ℝ => t*Real.cosh t-Real.sinh t) (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop) ?_
    intro t ht
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hd t).deriv]
    exact mul_pos ht (Real.sinh_pos_iff.mpr ht)
  have h := hm (show 0∈Ici (0:ℝ) by simp) hx.le hx
  simp only [zero_mul,Real.sinh_zero,sub_zero] at h
  linarith

private theorem sinh_div_strictMono : StrictMonoOn (fun t : ℝ => Real.sinh t/t) (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · exact Real.continuous_sinh.continuousOn.div continuousOn_id (fun t ht => ne_of_gt ht)
  · intro t ht
    rw [interior_Ioi,mem_Ioi] at ht
    have hd : HasDerivAt (fun t : ℝ => Real.sinh t/t)
        ((Real.cosh t*t-Real.sinh t)/t^2) t := by
      simpa only [Pi.div_apply,id_eq,mul_one] using!
        (Real.hasDerivAt_sinh t).div (hasDerivAt_id t) ht.ne'
    rw [hd.deriv]
    apply div_pos _ (sq_pos_of_pos ht)
    have h := sinh_lt_self_mul_cosh ht
    nlinarith

private def cutoffProfile (a h : ℝ) : ℝ := Real.sinh (a-h)/(a-h)-Real.cosh h

private theorem cutoffProfile_strictAnti (a : ℝ) :
    StrictAntiOn (cutoffProfile a) (Ioo 0 a) := by
  intro h hh k hk hhk
  have h1 := sinh_div_strictMono (show a-k∈Ioi (0:ℝ) by simpa using sub_pos.mpr hk.2)
    (show a-h∈Ioi (0:ℝ) by simpa using sub_pos.mpr hh.2) (by linarith : a-k<a-h)
  have h2 := Real.cosh_strictMonoOn hh.1.le hk.1.le hhk
  unfold cutoffProfile
  linarith

private theorem cutoffProfile_third_pos (a : SuzukiPositiveAperture) :
    0 < cutoffProfile a.1 (a.1/3) := by
  have hh : 0<a.1/3 := by linarith [a.2]
  have hs := Real.self_lt_sinh_iff.mpr hh
  have hc := Real.cosh_pos (a.1/3)
  have ht : a.1-a.1/3=2*(a.1/3) := by ring
  unfold cutoffProfile
  rw [sub_pos, lt_div_iff₀ (by linarith [a.2] : 0<a.1-a.1/3),ht,Real.sinh_two_mul]
  nlinarith [mul_pos (sub_pos.mpr hs) hc]

private theorem cutoffProfile_half_neg (a : SuzukiPositiveAperture) :
    cutoffProfile a.1 (a.1/2) < 0 := by
  have hh : 0<a.1/2 := by linarith [a.2]
  have hs := sinh_lt_self_mul_cosh hh
  unfold cutoffProfile
  rw [sub_lt_zero,div_lt_iff₀ (by linarith [a.2] : 0<a.1-a.1/2)]
  rw [show a.1-a.1/2=a.1/2 by ring]
  simpa only [mul_comm] using hs

private theorem exists_cutoff (a : SuzukiPositiveAperture) :
    ∃ h : ℝ, a.1/3<h ∧ h<a.1/2 ∧ cutoffProfile a.1 h=0 := by
  have hlo := cutoffProfile_third_pos a
  have hhi := cutoffProfile_half_neg a
  have hcont : ContinuousOn (cutoffProfile a.1) (Icc (a.1/3) (a.1/2)) := by
    apply ContinuousOn.sub
    · exact (Real.continuous_sinh.comp (continuous_const.sub continuous_id)).continuousOn.div
        (continuous_const.sub continuous_id).continuousOn (fun h hh => by linarith [a.2,hh.2])
    · exact Real.continuous_cosh.continuousOn
  obtain ⟨h,hh,heq⟩ := intermediate_value_Icc' (by linarith [a.2] : a.1/3≤a.1/2) hcont
    (show (0:ℝ)∈Icc (cutoffProfile a.1 (a.1/2)) (cutoffProfile a.1 (a.1/3)) from ⟨hhi.le,hlo.le⟩)
  refine ⟨h,lt_of_le_of_ne hh.1 ?_,lt_of_le_of_ne hh.2 ?_,heq⟩
  · intro e
    rw [e,heq] at hlo
    exact (lt_irrefl 0) hlo
  · intro e
    rw [← e,heq] at hhi
    exact (lt_irrefl 0) hhi

/-- Exact sign-bearing kernel of a visible prime atom on the literal odd pole. -/
def ccmOddPolePrimeKernel (a h : ℝ) : ℝ := Real.sinh (a-h)-(a-h)*Real.cosh h

/-- The half-log prime cutoff separating the two signs at a fixed aperture. -/
def ccmOddPolePrimeCutoff (a : SuzukiPositiveAperture) : ℝ := (exists_cutoff a).choose

/-- The cutoff lies strictly between one third and one half of the aperture. -/
theorem ccmOddPolePrimeCutoff_bounds (a : SuzukiPositiveAperture) :
    a.1/3<ccmOddPolePrimeCutoff a ∧ ccmOddPolePrimeCutoff a<a.1/2 :=
  ⟨(exists_cutoff a).choose_spec.1,(exists_cutoff a).choose_spec.2.1⟩

private theorem cutoff_eq_zero (a : SuzukiPositiveAperture) :
    cutoffProfile a.1 (ccmOddPolePrimeCutoff a)=0 := (exists_cutoff a).choose_spec.2.2

private theorem kernel_eq (a h : ℝ) (hh : h<a) :
    ccmOddPolePrimeKernel a h=(a-h)*cutoffProfile a h := by
  unfold ccmOddPolePrimeKernel cutoffProfile
  field_simp [ne_of_gt (sub_pos.mpr hh)]

private theorem cutoff_mem (a : SuzukiPositiveAperture) :
    ccmOddPolePrimeCutoff a ∈ Ioo 0 a.1 := by
  have h := ccmOddPolePrimeCutoff_bounds a
  constructor <;> linarith [a.2]

/-- Below the unique cutoff the literal odd prime-operator kernel is positive. -/
theorem ccmOddPolePrimeKernel_pos_iff (a : SuzukiPositiveAperture) {h : ℝ}
    (hh : h∈Ioo 0 a.1) :
    0<ccmOddPolePrimeKernel a.1 h ↔ h<ccmOddPolePrimeCutoff a := by
  rw [kernel_eq _ _ hh.2,mul_pos_iff_of_pos_left (sub_pos.mpr hh.2)]
  simpa only [cutoff_eq_zero] using
    (cutoffProfile_strictAnti a.1).lt_iff_gt (cutoff_mem a) hh

/-- Above the unique cutoff a visible literal odd prime-operator kernel is negative. -/
theorem ccmOddPolePrimeKernel_neg_iff (a : SuzukiPositiveAperture) {h : ℝ}
    (hh : h∈Ioo 0 a.1) :
    ccmOddPolePrimeKernel a.1 h<0 ↔ ccmOddPolePrimeCutoff a<h := by
  rw [kernel_eq _ _ hh.2]
  have he : (a.1-h)*cutoffProfile a.1 h<0 ↔ cutoffProfile a.1 h<0 := by
    have hp := sub_pos.mpr hh.2
    constructor
    · intro hn
      nlinarith
    · exact mul_neg_of_pos_of_neg hp
  rw [he]
  simpa only [cutoff_eq_zero] using
    (cutoffProfile_strictAnti a.1).lt_iff_gt hh (cutoff_mem a)

/-- The kernel has exactly one zero among strictly visible positive half-log shifts. -/
theorem ccmOddPolePrimeKernel_eq_zero_iff (a : SuzukiPositiveAperture) {h : ℝ}
    (hh : h∈Ioo 0 a.1) :
    ccmOddPolePrimeKernel a.1 h=0 ↔ h=ccmOddPolePrimeCutoff a := by
  rw [kernel_eq _ _ hh.2,mul_eq_zero,or_iff_right (ne_of_gt (sub_pos.mpr hh.2))]
  simpa only [cutoff_eq_zero] using
    ((cutoffProfile_strictAnti a.1).eq_iff_eq hh (cutoff_mem a)).trans eq_comm

/-- The canonical cutoff solves the exact undivided kernel equation. -/
theorem ccmOddPolePrimeKernel_cutoff (a : SuzukiPositiveAperture) :
    ccmOddPolePrimeKernel a.1 (ccmOddPolePrimeCutoff a)=0 :=
  (ccmOddPolePrimeKernel_eq_zero_iff a (cutoff_mem a)).mpr rfl

/-- At the exact entry aperture the prime atom has zero odd kernel. -/
theorem ccmOddPolePrimeKernel_entry (a : ℝ) : ccmOddPolePrimeKernel a a=0 := by
  simp [ccmOddPolePrimeKernel]

/-- Every half-log shift at most one third of the aperture is strictly old in sign. -/
theorem ccmOddPolePrimeKernel_pos_of_le_third (a : SuzukiPositiveAperture) {h : ℝ}
    (hh : 0<h) (hbound : h≤a.1/3) : 0<ccmOddPolePrimeKernel a.1 h := by
  exact (ccmOddPolePrimeKernel_pos_iff a ⟨hh,by linarith [a.2]⟩).mpr
    (lt_of_le_of_lt hbound (ccmOddPolePrimeCutoff_bounds a).1)

/-- Every half-log shift at least one half of the aperture and before entry is recent in sign. -/
theorem ccmOddPolePrimeKernel_neg_of_half_le (a : SuzukiPositiveAperture) {h : ℝ}
    (hbound : a.1/2≤h) (hh : h<a.1) : ccmOddPolePrimeKernel a.1 h<0 := by
  exact (ccmOddPolePrimeKernel_neg_iff a ⟨by linarith [a.2],hh⟩).mpr
    (lt_of_lt_of_le (ccmOddPolePrimeCutoff_bounds a).2 hbound)

end RHTower
