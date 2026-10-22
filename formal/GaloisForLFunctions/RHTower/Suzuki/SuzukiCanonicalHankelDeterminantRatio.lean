import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelEquation419
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelNormalizationDerivative

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace RHTower

open ContinuousKernelFredholm

/-- Uniqueness for a complex scalar linear ODE on a compact real interval.  This is the
Gronwall step needed below; no division by a possibly vanishing solution is used. -/
theorem eq_at_right_of_hasDerivWithinAt_eq_mul_self
    {f g p : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hp : ContinuousOn p (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (p x * f x) (Ici x) x)
    (hg' : ∀ x ∈ Ico a b, HasDerivWithinAt g (p x * g x) (Ici x) x)
    (hi : f a = g a) : f b = g b := by
  have hdiff : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun u => f u - g u) (p x * (f x - g x)) (Ici x) x := by
    intro x hx
    apply ((hf' x hx).sub (hg' x hx)).congr_deriv
    ring
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hp.norm
  have hbound : ∀ x ∈ Ico a b,
      ‖p x * (f x - g x)‖ ≤ K * ‖f x - g x‖ := by
    intro x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hK (mem_image_of_mem (fun u => ‖p u‖) ⟨hx.1, hx.2.le⟩)) (norm_nonneg _)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (hf.sub hg) hdiff (sub_eq_zero.mpr hi) hbound b ⟨hab, le_rfl⟩
  exact sub_eq_zero.mp hzero

/-- The moving Fredholm determinant has zero derivative at the support threshold. -/
theorem hasDerivAt_suzukiFredholmDeterminant_one_zero
    (epsilon : SuzukiHankelSign) {omega : ℝ} (homega : 1 < omega) :
    HasDerivAt (fun u : ℝ => suzukiFredholmDeterminant epsilon omega u) 0 1 := by
  let K := suzukiFredholmKernel omega
  have hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖K x y‖ ≤ 0 := by
    intro x hx y hy
    have hxy : x * y ≤ 1 := by
      calc
        x * y ≤ 1 * y := mul_le_mul_of_nonneg_right hx.2 hy.1
        _ ≤ 1 := by simpa using hy.2
    simp only [K, suzukiFredholmKernel, suzukiSourceHFinite]
    rw [if_neg (not_lt_of_ge hxy), norm_zero]
  have hcoeff (n : ℕ) :
      orderedFredholmMinorCoefficient K 1 n 1 1 = 0 := by
    have hnorm := orderedFredholmMinorCoefficient_norm_le K zero_le_one le_rfl
      (show (1 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp)
      hzero n
    have hnorm0 : ‖orderedFredholmMinorCoefficient K 1 n 1 1‖ ≤ 0 := by
      simpa using hnorm
    exact norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))
  have hminor : orderedFredholmMinor K 1 epsilon.coeff 1 1 = 0 := by
    simp only [orderedFredholmMinor, hcoeff, mul_zero, tsum_zero]
  obtain ⟨M, hM, hbound⟩ :=
    exists_suzukiFredholmKernel_bound (a := (2 : ℝ)) homega
  have hderiv := hasDerivAt_determinant K
    (continuous_suzukiFredholmKernel homega) zero_lt_one one_lt_two hM hbound
    epsilon.coeff
  change HasDerivAt (fun u : ℝ => suzukiFredholmDeterminant epsilon omega u)
    (epsilon.coeff * orderedFredholmMinor K 1 epsilon.coeff 1 1) 1 at hderiv
  simpa only [hminor, mul_zero] using hderiv

/-- Suzuki's literal normalization multiplies the negative determinant into the positive one. -/
theorem suzukiFredholmDeterminant_positive_eq_M_mul_negative
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 ≤ a) :
    suzukiFredholmDeterminant SuzukiHankelSign.positive omega a =
      (suzukiHankelM omega homega a : ℂ) *
        suzukiFredholmDeterminant SuzukiHankelSign.negative omega a := by
  let Dp : ℝ → ℂ := fun u =>
    suzukiFredholmDeterminant SuzukiHankelSign.positive omega u
  let Dn : ℝ → ℂ := fun u =>
    suzukiFredholmDeterminant SuzukiHankelSign.negative omega u
  let M : ℝ → ℂ := fun u => (suzukiHankelM omega homega u : ℂ)
  let p : ℝ → ℂ := fun u =>
    suzukiHankelBoundaryTraceReal SuzukiHankelSign.positive omega homega u / (u : ℂ)
  have hDp : ∀ x ∈ Ico (1 : ℝ) a, HasDerivWithinAt Dp (p x * Dp x) (Ici x) x := by
    intro x hx
    rcases hx.1.eq_or_lt with rfl | hx1
    · have h := hasDerivAt_suzukiFredholmDeterminant_one_zero
        SuzukiHankelSign.positive homega
      simpa [Dp, p, suzukiHankelBoundaryTraceReal] using h.hasDerivWithinAt
    · have h := hasDerivAt_suzukiFredholmDeterminant
        SuzukiHankelSign.positive homega hx1
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx1))
      have hp : p x =
          suzukiHankelPhiGlobal SuzukiHankelSign.positive omega x homega hx1 x := by
        simp only [p, suzukiHankelBoundaryTraceReal_of_one_lt _ homega hx1]
        field_simp [hxC]
      simpa only [Dp, p, hp, SuzukiHankelSign.coeff_positive, one_mul,
        mul_comm] using h.hasDerivWithinAt
  have hMDn : ∀ x ∈ Ico (1 : ℝ) a,
      HasDerivWithinAt (fun u => M u * Dn u) (p x * (M x * Dn x)) (Ici x) x := by
    intro x hx
    rcases hx.1.eq_or_lt with rfl | hx1
    · have hM := (hasDerivAt_suzukiHankelM (a := (1 : ℝ)) homega).ofReal_comp
      have hDn := hasDerivAt_suzukiFredholmDeterminant_one_zero
        SuzukiHankelSign.negative homega
      have hprod := hM.mul hDn
      have hprodWithin := hprod.hasDerivWithinAt (s := Ici (1 : ℝ))
      change HasDerivWithinAt
        (fun u : ℝ => (suzukiHankelM omega homega u : ℂ) *
          suzukiFredholmDeterminant SuzukiHankelSign.negative omega u)
        _ (Ici (1 : ℝ)) 1 at hprodWithin
      simpa [M, Dn, p, suzukiHankelBoundaryTraceReal,
        suzukiHankelMuScalar_eq_zero_of_le_one homega le_rfl] using
        hprodWithin
    · have hM := (hasDerivAt_suzukiHankelM (a := x) homega).ofReal_comp
      have hDn := hasDerivAt_suzukiFredholmDeterminant
        SuzukiHankelSign.negative homega hx1
      have hprod := hM.mul hDn
      have hmu := ofReal_suzukiHankelMuScalar_eq homega x
      rw [suzukiHankelMuReal_of_one_lt homega hx1] at hmu
      have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx1))
      have hp : p x =
          suzukiHankelPhiGlobal SuzukiHankelSign.positive omega x homega hx1 x := by
        simp only [p, suzukiHankelBoundaryTraceReal_of_one_lt _ homega hx1]
        field_simp [hxC]
      apply hprod.hasDerivWithinAt.congr_deriv
      simp only [M, Dn, p, hp, SuzukiHankelSign.coeff_negative, neg_one_mul]
      rw [Complex.ofReal_mul, Complex.ofReal_div, hmu]
      simp only [suzukiHankelMu]
      field_simp [hxC]
      ring
  have hDpCont : ContinuousOn Dp (Icc (1 : ℝ) a) := by
    intro x hx
    by_cases hx1 : x = 1
    · subst x
      simpa only [Dp] using
        (hasDerivAt_suzukiFredholmDeterminant_one_zero
          SuzukiHankelSign.positive homega).continuousAt.continuousWithinAt
    · simpa only [Dp] using
        (hasDerivAt_suzukiFredholmDeterminant SuzukiHankelSign.positive homega
          (lt_of_le_of_ne hx.1 (Ne.symm hx1))).continuousAt.continuousWithinAt
  have hMDnCont : ContinuousOn (fun u => M u * Dn u) (Icc (1 : ℝ) a) := by
    have hMCont : Continuous M := by
      change Continuous (fun u : ℝ => (suzukiHankelM omega homega u : ℂ))
      exact Complex.continuous_ofReal.comp
        (continuous_iff_continuousAt.mpr fun x =>
          (hasDerivAt_suzukiHankelM (a := x) homega).continuousAt)
    have hDnCont : ContinuousOn Dn (Icc (1 : ℝ) a) := by
      intro x hx
      by_cases hx1 : x = 1
      · subst x
        simpa only [Dn] using
          (hasDerivAt_suzukiFredholmDeterminant_one_zero
            SuzukiHankelSign.negative homega).continuousAt.continuousWithinAt
      · simpa only [Dn] using
          (hasDerivAt_suzukiFredholmDeterminant SuzukiHankelSign.negative homega
            (lt_of_le_of_ne hx.1 (Ne.symm hx1))).continuousAt.continuousWithinAt
    exact hMCont.continuousOn.mul
      hDnCont
  have hpCont : ContinuousOn p (Icc (1 : ℝ) a) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
    have htrace : ContinuousAt
        (suzukiHankelBoundaryTraceReal SuzukiHankelSign.positive omega homega) x := by
      by_cases hx1 : x = 1
      · subst x
        exact continuousAt_suzukiHankelBoundaryTraceReal_one
          SuzukiHankelSign.positive homega
      · exact continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
          SuzukiHankelSign.positive homega (lt_of_le_of_ne hx.1 (Ne.symm hx1))
    have hquot :=
      (htrace.div Complex.continuous_ofReal.continuousAt hx0).continuousWithinAt
        (s := Icc (1 : ℝ) a)
    change ContinuousWithinAt
      (fun u : ℝ => suzukiHankelBoundaryTraceReal SuzukiHankelSign.positive
        omega homega u / (u : ℂ)) (Icc (1 : ℝ) a) x at hquot
    simpa only [p] using hquot
  have hinitial : Dp 1 = M 1 * Dn 1 := by
    simp only [Dp, Dn, M, suzukiFredholmDeterminant_one,
      suzukiHankelM_eq_one_of_le_one homega le_rfl, Complex.ofReal_one, one_mul]
  exact eq_at_right_of_hasDerivWithinAt_eq_mul_self ha hDpCont hMDnCont hpCont
    hDp hMDn hinitial

/-- Determinant-ratio identity used to identify Suzuki's Hamiltonian normalization. -/
theorem suzukiHankelM_eq_fredholmDeterminant_ratio
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    (suzukiHankelM omega homega a : ℂ) =
      suzukiFredholmDeterminant SuzukiHankelSign.positive omega a /
        suzukiFredholmDeterminant SuzukiHankelSign.negative omega a := by
  have hmain := suzukiFredholmDeterminant_positive_eq_M_mul_negative homega ha.le
  rw [eq_div_iff (suzukiFredholmDeterminant_ne_zero
    SuzukiHankelSign.negative homega ha)]
  exact hmain.symm

/-- Suzuki's determinant definition of `m(a)` agrees with the integral normalization on the
entire printed aperture range.  The subcritical case is not hidden in the supercritical ODE:
both literal Fredholm series reduce to one there. -/
theorem suzukiHankelM_eq_fredholmDeterminant_ratio_of_pos
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) :
    (suzukiHankelM omega homega a : ℂ) =
      suzukiFredholmDeterminant SuzukiHankelSign.positive omega a /
        suzukiFredholmDeterminant SuzukiHankelSign.negative omega a := by
  rcases lt_or_ge 1 a with ha1 | ha1
  · exact suzukiHankelM_eq_fredholmDeterminant_ratio homega ha1
  · rw [suzukiHankelM_eq_one_of_le_one homega ha1,
      suzukiFredholmDeterminant_eq_one_of_nonneg_of_le_one
        SuzukiHankelSign.positive ha.le ha1,
      suzukiFredholmDeterminant_eq_one_of_nonneg_of_le_one
        SuzukiHankelSign.negative ha.le ha1]
    norm_num

/-- The literal Fredholm quotient in Suzuki's Theorem 4 is real-valued. -/
theorem suzukiFredholmDeterminant_ratio_im_eq_zero
    {omega a : ℝ} (homega : 1 < omega) (ha : 0 < a) :
    (suzukiFredholmDeterminant SuzukiHankelSign.positive omega a /
        suzukiFredholmDeterminant SuzukiHankelSign.negative omega a).im = 0 := by
  rw [← suzukiHankelM_eq_fredholmDeterminant_ratio_of_pos homega ha]
  simp

/-- The literal determinant quotient is continuous on all positive apertures, including the
Fredholm seam at `a = 1`. -/
theorem continuousOn_suzukiFredholmDeterminant_ratio
    {omega : ℝ} (homega : 1 < omega) :
    ContinuousOn
      (fun a : ℝ =>
        suzukiFredholmDeterminant SuzukiHankelSign.positive omega a /
          suzukiFredholmDeterminant SuzukiHankelSign.negative omega a)
      (Ioi 0) := by
  have hM : Continuous (fun a : ℝ => (suzukiHankelM omega homega a : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun a =>
        (hasDerivAt_suzukiHankelM (a := a) homega).continuousAt)
  intro a ha
  apply ContinuousAt.continuousWithinAt
  apply hM.continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with b hb
  exact (suzukiHankelM_eq_fredholmDeterminant_ratio_of_pos homega hb).symm

end RHTower
