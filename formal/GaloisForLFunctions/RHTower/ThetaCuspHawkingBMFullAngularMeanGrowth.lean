import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceAdvancedAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat
import GaloisForLFunctions.RHTower.CothInfra
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Growth of the constructed full angular circle mean, with the literal theta-square
forcing retained. The limiting characteristic modes give an energy estimate with
an exponent strictly below two. The original physical clock then supplies an
integrable source-horizon majorant, uniform in both radial variables.
-/
namespace RHTower.D4BMFullAngularGrowth
open Set Filter Topology MeasureTheory
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMFullAngularCircle
open D4BMNativeCircle D4BMFullSourceAdvanced
open scoped ContDiff
noncomputable section
set_option autoImplicit false

private theorem smooth_even_quadratic_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : Icc (0 : ℝ) 2, ‖f d - f 0‖ ≤ C * d.val ^ 2 := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    hf2.continuous.continuousOn (s := Icc (0 : ℝ) 2)
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hzero : deriv f 0 = 0 := by
    have hcomp := ((hf.contDiffAt.differentiableAt (by simp)).hasDerivAt).scomp 0
      (hasDerivAt_neg 0)
    have hfun : (fun t : ℝ => f (-t)) = f := funext he
    change HasDerivAt (fun t : ℝ => f (-t)) _ 0 at hcomp
    rw [hfun] at hcomp
    have hneg : -(deriv f 0) = deriv f 0 := by simpa using hcomp.deriv.symm
    linear_combination -(1 / 2 : ℂ) * hneg
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) : ‖deriv f t‖ ≤ C * t := by
    have h := (convex_Icc (0 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le (C := C)
      (fun u _ => hf1.differentiable (by simp) u)
      (fun u hu => (hB u hu).trans (show B ≤ C from le_max_left _ _))
      (show (0 : ℝ) ∈ Icc 0 2 by constructor <;> norm_num) ht
    simpa [hzero, Real.norm_eq_abs, abs_of_nonneg ht.1] using h
  refine ⟨C, hC, fun d => ?_⟩
  have h := (convex_Icc (0 : ℝ) d.val).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => hf.differentiable (by simp) u)
    (fun u hu => (hd u ⟨hu.1, hu.2.trans d.property.2⟩).trans
      (mul_le_mul_of_nonneg_left hu.2 hC))
    (show (0 : ℝ) ∈ Icc 0 d.val from ⟨le_rfl, d.property.1⟩)
    (show d.val ∈ Icc 0 d.val from ⟨d.property.1, le_rfl⟩)
  simpa [Real.norm_eq_abs, abs_of_nonneg d.property.1, mul_assoc, pow_two] using h

private theorem deriv_even_odd (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f) (x : ℝ) : deriv f (-x) = -deriv f x := by
  have hcomp := ((hf.contDiffAt.differentiableAt (by simp)).hasDerivAt).scomp x
    (hasDerivAt_neg x)
  have hfun : (fun t : ℝ => f (-t)) = f := funext he
  change HasDerivAt (fun t : ℝ => f (-t)) _ x at hcomp
  rw [hfun] at hcomp
  have hneg : -(deriv f (-x)) = deriv f x := by
    simpa using hcomp.deriv.symm
  linear_combination -hneg

private theorem deriv_odd_even (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (ho : ∀ x, f (-x) = -f x) (x : ℝ) : deriv f (-x) = deriv f x := by
  have hcomp := ((hf.contDiffAt.differentiableAt (by simp)).hasDerivAt).scomp x
    (hasDerivAt_neg x)
  have hfun : (fun t : ℝ => f (-t)) = fun t => -f t := funext ho
  change HasDerivAt (fun t : ℝ => f (-t)) _ x at hcomp
  rw [hfun] at hcomp
  have hneg : HasDerivAt (fun t : ℝ => -f t) (-deriv f x) x :=
    ((hf.contDiffAt.differentiableAt (by simp)).hasDerivAt).neg
  have heq := hneg.unique hcomp
  simpa using heq.symm

private theorem smooth_even_quartic_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : Icc (0 : ℝ) 2,
      ‖f d - f 0 - (d.val ^ 2 / 2) • deriv (deriv f) 0‖ ≤ C * d.val ^ 4 := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  have hodd : ∀ x : ℝ, deriv f (-x) = -deriv f x := deriv_even_odd f hf he
  have heven : Function.Even (deriv (deriv f)) :=
    fun x => deriv_odd_even (deriv f) hf1 hodd x
  obtain ⟨C, hC, hCbound⟩ := smooth_even_quadratic_bound (deriv (deriv f)) hf2 heven
  have hf0 : deriv f 0 = 0 := by
    have h := hodd 0
    have h' : deriv f 0 = -deriv f 0 := by simpa using h
    linear_combination (1 / 2 : ℂ) * h'
  let g : ℝ → ℂ := fun t => deriv f t - deriv f 0 - t • deriv (deriv f) 0
  have hg_deriv (t : ℝ) : HasDerivAt g (deriv (deriv f) t - deriv (deriv f) 0) t := by
    have h1 : HasDerivAt (deriv f) (deriv (deriv f) t) t :=
      (hf1.contDiffAt.differentiableAt (by simp)).hasDerivAt
    have h2 : HasDerivAt (fun _ : ℝ => deriv f 0) 0 t := hasDerivAt_const t _
    have h3 : HasDerivAt (fun u : ℝ => u • deriv (deriv f) 0)
        (deriv (deriv f) 0) t := by
      simpa using (hasDerivAt_id t).smul_const (deriv (deriv f) 0)
    change HasDerivAt ((fun u : ℝ => deriv f u) - (fun _ => deriv f 0) -
      fun u => u • deriv (deriv f) 0) _ t
    simpa using h1.sub h2 |>.sub h3
  have hg_bound (d : Icc (0 : ℝ) 2) : ‖g d.val‖ ≤ C * d.val ^ 3 := by
    have h := (convex_Icc (0 : ℝ) d.val).norm_image_sub_le_of_norm_deriv_le
      (fun u _ => (hg_deriv u).differentiableAt)
      (fun u hu => by
        rw [(hg_deriv u).deriv]
        have hsq : u ^ 2 ≤ d.val ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (add_nonneg hu.1 d.property.1)]
        exact (hCbound ⟨u, ⟨hu.1, hu.2.trans d.property.2⟩⟩).trans
          (mul_le_mul_of_nonneg_left hsq hC))
      (show (0 : ℝ) ∈ Icc 0 d.val from ⟨le_rfl, d.property.1⟩)
      (show d.val ∈ Icc 0 d.val from ⟨d.property.1, le_rfl⟩)
    have hg0 : g 0 = 0 := by simp [g]
    have hdabs : ‖d.val - 0‖ = d.val := by
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg d.property.1]
    rw [hg0, sub_zero, hdabs] at h
    calc
      ‖g d.val‖ ≤ (C * d.val ^ 2) * d.val := h
      _ = C * d.val ^ 3 := by ring
  let R : ℝ → ℂ := fun t => f t - f 0 - (t ^ 2 / 2) • deriv (deriv f) 0
  have hR_deriv (t : ℝ) : HasDerivAt R (g t) t := by
    have h1 : HasDerivAt f (deriv f t) t :=
      (hf.contDiffAt.differentiableAt (by simp)).hasDerivAt
    have h2 : HasDerivAt (fun _ : ℝ => f 0) 0 t := hasDerivAt_const t _
    have hquad : HasDerivAt (fun u : ℝ => ((u ^ 2 / 2 : ℝ) : ℂ)) (t : ℂ) t := by
      have hc := ((hasDerivAt_pow 2 t).div_const (2 : ℝ)).ofReal_comp
      convert hc using 1
      · norm_num
    have h3 := hquad.mul_const (deriv (deriv f) 0)
    have hder := h1.sub h2 |>.sub h3
    change HasDerivAt ((f - fun _ : ℝ => f 0) -
      fun u : ℝ => (u ^ 2 / 2) • deriv (deriv f) 0)
      (deriv f t - deriv f 0 - t • deriv (deriv f) 0) t
    rw [hf0]
    simpa only [Complex.real_smul, sub_zero] using hder
  refine ⟨C, hC, fun d => ?_⟩
  have h := (convex_Icc (0 : ℝ) d.val).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (hR_deriv u).differentiableAt)
    (fun u hu => by
      rw [(hR_deriv u).deriv]
      have hsq : u ^ 2 ≤ d.val ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (add_nonneg hu.1 d.property.1)]
      have hcube : u ^ 3 ≤ d.val ^ 3 := by
        calc
          u ^ 3 = u ^ 2 * u := by ring
          _ ≤ d.val ^ 2 * u := mul_le_mul_of_nonneg_right hsq hu.1
          _ ≤ d.val ^ 2 * d.val := mul_le_mul_of_nonneg_left hu.2 (sq_nonneg _)
          _ = d.val ^ 3 := by ring
      exact (hg_bound ⟨u, ⟨hu.1, hu.2.trans d.property.2⟩⟩).trans
        (mul_le_mul_of_nonneg_left hcube hC))
    (show (0 : ℝ) ∈ Icc 0 d.val from ⟨le_rfl, d.property.1⟩)
    (show d.val ∈ Icc 0 d.val from ⟨d.property.1, le_rfl⟩)
  have hR0 : R 0 = 0 := by simp [R]
  have hdabs : ‖d.val - 0‖ = d.val := by
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg d.property.1]
  rw [hR0, sub_zero, hdabs] at h
  calc
    ‖R d.val‖ ≤ (C * d.val ^ 3) * d.val := h
    _ = C * d.val ^ 4 := by ring

private theorem arcosh_small_bound (u : Icc (0 : ℝ) 1) :
    0 ≤ Real.arcosh (1 + u.val) ∧ Real.arcosh (1 + u.val) ≤ 2 ∧
      (Real.arcosh (1 + u.val)) ^ 2 ≤ 3 * u.val := by
  have hu : 1 ≤ 1 + u.val := le_add_of_nonneg_right u.property.1
  have hd := Real.arcosh_nonneg hu
  have hs := Real.self_le_sinh_iff.mpr hd
  have hh := Real.cosh_sq_sub_sinh_sq (Real.arcosh (1 + u.val))
  rw [Real.cosh_arcosh hu] at hh
  have hs0 := Real.sinh_nonneg_iff.mpr hd
  have hsq : (Real.arcosh (1 + u.val)) ^ 2 ≤ 3 * u.val := by
    nlinarith [u.property.1, u.property.2]
  refine ⟨hd, ?_, hsq⟩
  nlinarith [u.property.2]

private theorem cosh_corner_quadratic_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d u : ℝ, d ∈ Icc (0 : ℝ) 2 → u ∈ Icc (0 : ℝ) 1 →
      Real.cosh d = 1 + u → d ^ 2 ≤ 3 * u → |d ^ 2 - 2 * u| ≤ C * u ^ 2 := by
  let f : ℝ → ℂ := fun t => (Real.cosh t : ℂ)
  have hf : ContDiff ℝ ∞ f := by
    dsimp [f]
    exact Complex.ofRealCLM.contDiff.comp Real.contDiff_cosh
  have he : Function.Even f := by
    intro t
    simp only [f, Real.cosh_neg]
  obtain ⟨B, hB, hbound⟩ := smooth_even_quartic_bound f hf he
  have hdfirst (t : ℝ) : deriv f t = (Real.sinh t : ℂ) := by
    exact ((Real.hasDerivAt_cosh t).ofReal_comp).deriv
  have hdsecond : deriv (deriv f) 0 = 1 := by
    rw [show deriv f = fun t => (Real.sinh t : ℂ) by funext t; exact hdfirst t]
    simpa using ((Real.hasDerivAt_sinh 0).ofReal_comp).deriv
  refine ⟨18 * B, by positivity, fun d u hd hu hcosh hsq => ?_⟩
  have h := hbound ⟨d, hd⟩
  have hreal : |Real.cosh d - 1 - d ^ 2 / 2| ≤ B * d ^ 4 := by
    rw [hdsecond] at h
    dsimp [f] at h
    simp only [Real.cosh_zero, Complex.ofReal_one, mul_one] at h
    have hrewriteC : (Real.cosh d : ℂ) - 1 - (d ^ 2 / 2 : ℝ) =
        (Real.cosh d - 1 - d ^ 2 / 2 : ℝ) := by
      push_cast
      ring
    rw [hrewriteC, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hd4 : d ^ 4 ≤ 9 * u ^ 2 := by
    nlinarith [sq_nonneg (d ^ 2 - 3 * u)]
  have hrewrite : Real.cosh d - 1 - d ^ 2 / 2 = u - d ^ 2 / 2 := by
    rw [hcosh]
    ring
  rw [hrewrite] at hreal
  rw [show d ^ 2 - 2 * u = -2 * (u - d ^ 2 / 2) by ring, abs_mul]
  norm_num
  have hmul := mul_le_mul_of_nonneg_left hd4 hB
  nlinarith

private theorem arcosh_sq_quadratic_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Icc (0 : ℝ) 1,
      |(Real.arcosh (1 + u.val)) ^ 2 - 2 * u.val| ≤ C * u.val ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := cosh_corner_quadratic_bound
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨hd0, hd2, hsq⟩ := arcosh_small_bound u
  apply hbound (Real.arcosh (1 + u.val)) u.val ⟨hd0, hd2⟩ u.property
  · exact Real.cosh_arcosh (le_add_of_nonneg_right u.property.1)
  · exact hsq

private theorem smooth_even_arcosh_quadratic_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Icc (0 : ℝ) 1,
      ‖f (Real.arcosh (1 + u.val)) - f 0 - u.val • deriv (deriv f) 0‖ ≤ C * u.val ^ 2 := by
  obtain ⟨B, hB, hquartic⟩ := smooth_even_quartic_bound f hf he
  obtain ⟨D, hD, hcorner⟩ := arcosh_sq_quadratic_bound
  let A := deriv (deriv f) 0
  refine ⟨9 * B + D * ‖A‖, by positivity, fun u => ?_⟩
  obtain ⟨hd0, hd2, hsq⟩ := arcosh_small_bound u
  let d := Real.arcosh (1 + u.val)
  have hquartic' := hquartic (⟨d, ⟨hd0, hd2⟩⟩ : Icc (0 : ℝ) 2)
  have hcorner' := hcorner u
  have hd4 : d ^ 4 ≤ 9 * u.val ^ 2 := by
    dsimp [d] at hsq ⊢
    nlinarith [sq_nonneg ((Real.arcosh (1 + u.val)) ^ 2 - 3 * u.val)]
  have hfirst : B * d ^ 4 ≤ (9 * B) * u.val ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hd4 hB
    nlinarith
  have hhalf : |d ^ 2 / 2 - u.val| ≤ D * u.val ^ 2 := by
    rw [show d ^ 2 / 2 - u.val = (d ^ 2 - 2 * u.val) / 2 by ring, abs_div]
    have habs : |(2 : ℝ)| = 2 := by norm_num
    rw [habs]
    have hdiv : |d ^ 2 - 2 * u.val| / 2 ≤ |d ^ 2 - 2 * u.val| :=
      div_le_self (abs_nonneg _) (by norm_num)
    exact hdiv.trans hcorner'
  have hsecond : ‖(d ^ 2 / 2 - u.val) • A‖ ≤ (D * ‖A‖) * u.val ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |d ^ 2 / 2 - u.val| * ‖A‖ ≤ (D * u.val ^ 2) * ‖A‖ :=
        mul_le_mul_of_nonneg_right hhalf (norm_nonneg _)
      _ = (D * ‖A‖) * u.val ^ 2 := by ring
  change ‖f d - f 0 - u.val • A‖ ≤ _
  have heq : f d - f 0 - u.val • A =
      (f d - f 0 - (d ^ 2 / 2) • A) + (d ^ 2 / 2 - u.val) • A := by
    module
  rw [heq]
  calc
    ‖f d - f 0 - (d ^ 2 / 2) • A + (d ^ 2 / 2 - u.val) • A‖ ≤
        ‖f d - f 0 - (d ^ 2 / 2) • A‖ + ‖(d ^ 2 / 2 - u.val) • A‖ := norm_add_le _ _
    _ ≤ (9 * B) * u.val ^ 2 + (D * ‖A‖) * u.val ^ 2 :=
      add_le_add (hquartic'.trans hfirst) hsecond
    _ = (9 * B + D * ‖A‖) * u.val ^ 2 := by ring

private theorem normSq_hasDerivAt {a : ℝ → ℂ} {v : ℂ} {y : ℝ} (ha : HasDerivAt a v y) :
    HasDerivAt (fun t => Complex.normSq (a t))
      (2*(v*(starRingEnd ℂ) (a y)).re) y := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y ha
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y ha
  convert (hr.mul hr).add (hi.mul hi) using 1 <;> try rfl
  simp only [Function.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

private theorem mode_real (a nu F : ℂ) :
    ((nu*a+F)*(starRingEnd ℂ) a).re=nu.re*Complex.normSq a+(F*(starRingEnd ℂ) a).re := by
  simp only [Complex.mul_re,Complex.add_re,Complex.add_im,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

private theorem young_two (eta c x y n : ℝ) (he : 0 < eta) :
    2*c*n*(x+y) ≤ eta*(x^2+y^2)+(2*c^2/eta)*n^2 := by
  apply le_of_mul_le_mul_left (a := eta) ?_ he
  calc
    eta*(2*c*n*(x+y)) ≤ eta^2*(x^2+y^2)+2*c^2*n^2 := by
      nlinarith [sq_nonneg (eta*x-c*n),sq_nonneg (eta*y-c*n)]
    _ = eta*(eta*(x^2+y^2)+(2*c^2/eta)*n^2) := by
      field_simp

/-- A one-sided derivative gives a literal linear increment bound near its endpoint. -/
private theorem local_increment_bound {f : ℝ → ℂ} {a : ℂ}
    (hf : HasDerivWithinAt f a (Ici 1) 1) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u → u ≤ δ →
      ‖f (1+u)-f 1‖ ≤ B*u := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (1:ℝ) ∉ Ioi 1)).mp
    (hf.mono Ioi_subset_Ici_self)
  have hnear : ∀ᶠ z in 𝓝[Ioi 1] (1:ℝ), slope f 1 z ∈ Metric.ball a 1 :=
    hs.eventually (Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  refine ⟨δ,‖a‖+1,hδ,by positivity,?_⟩
  intro u hu huδ
  by_cases hu0 : u=0
  · subst u
    simp
  · have hu0' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hmem : slope f 1 (1+u) ∈ Metric.ball a 1 := by
      apply hsub
      constructor
      · rw [Metric.mem_ball]
        simpa only [Real.dist_eq,abs_of_nonneg hu] using huδ
      · exact lt_add_of_pos_right 1 hu0'
    have hdist : ‖slope f 1 (1+u)-a‖ < 1 := by
      simpa only [Metric.mem_ball,Complex.dist_eq] using hmem
    have hnorm : ‖slope f 1 (1+u)‖ < ‖a‖+1 := by
      calc
        _ ≤ ‖a‖+‖slope f 1 (1+u)-a‖ := norm_le_norm_add_norm_sub _ _
        _ < _ := by linarith
    rw [slope_def_module,sub_eq_add_neg,show (1+u:ℝ)-1=u by ring]
    simp only [Complex.real_smul,Complex.ofReal_inv]
    have huC : (u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0
    rw [div_eq_mul_inv,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0']
    rw [div_lt_iff₀ hu0']
    exact hnorm

/-- Young's inequality absorbs the small hyperbolic correction in the spectral gap. -/
private theorem pair_energy_bound (a b d n nu mu kap : ℂ) (g eta K eps : ℝ)
    (he : 0 < eta) (hK : 0 ≤ K) (heps : 0 ≤ eps)
    (hnu : nu.re ≤ g) (hmu : mu.re ≤ g)
    (hd : ‖d‖ ≤ K*(‖a‖+‖b‖)) (hsmall : 4*K*eps ≤ eta) :
    2*((nu*a+(kap*n-(eps:ℂ)*d))*(starRingEnd ℂ) a).re+
      2*((mu*b+(kap*n-(eps:ℂ)*d))*(starRingEnd ℂ) b).re ≤
      2*(g+eta)*(Complex.normSq a+Complex.normSq b)+(2*‖kap‖^2/eta)*‖n‖^2 := by
  let u := ‖a‖+‖b‖
  let E := Complex.normSq a+Complex.normSq b
  have hE : 0 ≤ E := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hu : 0 ≤ u := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hu2 : u^2 ≤ 2*E := by
    dsimp only [u,E]
    rw [← Complex.sq_norm a,← Complex.sq_norm b]
    nlinarith [sq_nonneg (‖a‖-‖b‖)]
  have hF : ‖kap*n-(eps:ℂ)*d‖ ≤ ‖kap‖*‖n‖+eps*K*u := by
    calc
      _ ≤ ‖kap*n‖+‖(eps:ℂ)*d‖ := norm_sub_le _ _
      _ = ‖kap‖*‖n‖+eps*‖d‖ := by
        rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg heps]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd heps]
  have hc (z : ℂ) : ((kap*n-(eps:ℂ)*d)*(starRingEnd ℂ) z).re ≤
      (‖kap‖*‖n‖+eps*K*u)*‖z‖ := by
    calc
      _ ≤ ‖(kap*n-(eps:ℂ)*d)*(starRingEnd ℂ) z‖ := Complex.re_le_norm _
      _ = ‖kap*n-(eps:ℂ)*d‖*‖z‖ := by rw [norm_mul,Complex.norm_conj]
      _ ≤ _ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)
  have hdiag : nu.re*Complex.normSq a+mu.re*Complex.normSq b ≤ g*E := by
    dsimp only [E]
    nlinarith [mul_le_mul_of_nonneg_right hnu (Complex.normSq_nonneg a),
      mul_le_mul_of_nonneg_right hmu (Complex.normSq_nonneg b)]
  have hsource : 2*‖kap‖*‖n‖*u ≤ eta*E+(2*‖kap‖^2/eta)*‖n‖^2 := by
    simpa only [u,E,← Complex.sq_norm] using young_two eta ‖kap‖ ‖a‖ ‖b‖ ‖n‖ he
  have hpert : 2*eps*K*u^2 ≤ eta*E := by
    have h1 := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ 2*eps*K by positivity)
    have h2 := mul_le_mul_of_nonneg_right hsmall hE
    nlinarith only [h1,h2]
  rw [mode_real,mode_real]
  have ha := hc a
  have hb := hc b
  change _ ≤ 2*(g+eta)*E+_
  dsimp only [u] at hsource hpert ha hb
  nlinarith only [ha,hb,hdiag,hsource,hpert]

private def nu (q : XiZeroCopy) (branch : Bool) : ℂ := 2*physicalRate q branch+1
private def mu (q : XiZeroCopy) (branch : Bool) : ℂ := -2*physicalRate q branch-2

private theorem roots (q : XiZeroCopy) (branch : Bool) :
    (nu q branch).re ≤ sourceGrowthExponent q ∧
    (mu q branch).re ≤ sourceGrowthExponent q ∧ nu q branch-mu q branch ≠ 0 := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hp := le_abs_self ((q.1:ℂ).re-1/2)
  have hm := neg_le_abs ((q.1:ℂ).re-1/2)
  have hg : 1 ≤ sourceGrowthExponent q := (sourceGrowthExponent_bounds q).1
  have hnu : (nu q branch).re < -1 := by
    cases branch <;> simp only [nu,physicalRate,↓reduceIte,Complex.add_re,Complex.sub_re,
      Complex.mul_re] <;> norm_num <;> linarith
  have hmu : (mu q branch).re ≤ sourceGrowthExponent q := by
    cases branch <;> simp only [mu,physicalRate,sourceGrowthExponent,D4BMGlobalAngularResponse.center,↓reduceIte,
      Complex.sub_re,Complex.neg_re,Complex.mul_re] <;> norm_num <;> linarith
  refine ⟨by linarith,hmu,?_⟩
  have he : (nu q branch-mu q branch).re=2*(nu q branch).re+1 := by
    dsimp only [nu,mu]
    simp only [Complex.sub_re,Complex.add_re,Complex.neg_re,Complex.mul_re]
    norm_num
    ring
  intro hz
  have hr := congrArg Complex.re hz
  rw [he] at hr
  norm_num at hr
  linarith

private theorem mean_derivatives (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) :
    HasDerivAt (fun t => angularMean q branch t X k)
      (deriv (fun t => angularMean q branch t X k) d) d ∧
    HasDerivAt (deriv (fun t => angularMean q branch t X k))
      (deriv (deriv (fun t => angularMean q branch t X k)) d) d := by
  have hs := angularMean_smooth q branch X k
  exact ⟨(hs.differentiable (by simp) d).hasDerivAt,
    (((contDiff_infty_iff_deriv.mp hs).2).differentiable (by simp) d).hasDerivAt⟩

private theorem mean_equation (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) (hd : 0 < d) :
    deriv (deriv (fun t => angularMean q branch t X k)) d =
      parameter q branch*(angularMean q branch d X k+D4BMNativeCircle.mean q d X k)-
      (rcoth d:ℂ)*deriv (fun t => angularMean q branch t X k) d := by
  have h := angularMean_forced q branch d X k
  have hn : (Real.sinh d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sinh_pos_iff.mpr hd))
  have hc : (Real.sinh d:ℂ)*(rcoth d:ℂ)=(Real.cosh d:ℂ) := by
    rw [rcoth,Complex.ofReal_div]
    field_simp
  have hc2 : (Real.sinh d:ℂ)^2*(rcoth d:ℂ)=(Real.sinh d:ℂ)*(Real.cosh d:ℂ) := by
    rw [pow_two,mul_assoc,hc]
  apply mul_left_cancel₀ (pow_ne_zero 2 hn)
  rw [mul_sub,← mul_assoc ((Real.sinh d:ℂ)^2) (rcoth d:ℂ),hc2]
  linear_combination h

private def modeA (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) : ℂ :=
  deriv (fun t => angularMean q branch t X k) d-mu q branch*angularMean q branch d X k
private def modeB (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) : ℂ :=
  deriv (fun t => angularMean q branch t X k) d-nu q branch*angularMean q branch d X k
private def energy (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) : ℝ :=
  Complex.normSq (modeA q branch X k d)+Complex.normSq (modeB q branch X k d)
private def decoder (q : XiZeroCopy) (branch : Bool) : ℝ :=
  (‖nu q branch‖+‖mu q branch‖)/‖nu q branch-mu q branch‖

private theorem modes_derivative (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) (hd : 0 < d) :
    HasDerivAt (modeA q branch X k)
      (nu q branch*modeA q branch X k d+parameter q branch*D4BMNativeCircle.mean q d X k-
        ((rcoth d-1:ℝ):ℂ)*deriv (fun t => angularMean q branch t X k) d) d ∧
    HasDerivAt (modeB q branch X k)
      (mu q branch*modeB q branch X k d+parameter q branch*D4BMNativeCircle.mean q d X k-
        ((rcoth d-1:ℝ):ℂ)*deriv (fun t => angularMean q branch t X k) d) d := by
  obtain ⟨hM,hD⟩ := mean_derivatives q branch X k d
  have he := mean_equation q branch X k d hd
  constructor
  · have h : HasDerivAt (modeA q branch X k)
        (deriv (deriv (fun t => angularMean q branch t X k)) d-
          mu q branch*deriv (fun t => angularMean q branch t X k) d) d :=
      hD.sub (hM.const_mul (mu q branch))
    apply h.congr_deriv
    rw [he,parameter_physicalRate]
    simp only [modeA,mu,nu,D4BMQuadraticMixedSource.resolventParameter,Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  · have h : HasDerivAt (modeB q branch X k)
        (deriv (deriv (fun t => angularMean q branch t X k)) d-
          nu q branch*deriv (fun t => angularMean q branch t X k) d) d :=
      hD.sub (hM.const_mul (nu q branch))
    apply h.congr_deriv
    rw [he,parameter_physicalRate]
    simp only [modeB,mu,nu,D4BMQuadraticMixedSource.resolventParameter,Complex.ofReal_sub,
      Complex.ofReal_one]
    ring

private theorem decode_derivative (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) :
    ‖deriv (fun t => angularMean q branch t X k) d‖ ≤
      decoder q branch*(‖modeA q branch X k d‖+‖modeB q branch X k d‖) := by
  have hn : 0 < ‖nu q branch-mu q branch‖ := norm_pos_iff.mpr (roots q branch).2.2
  have he : (nu q branch-mu q branch)*deriv (fun t => angularMean q branch t X k) d=
      nu q branch*modeA q branch X k d-mu q branch*modeB q branch X k d := by
    dsimp only [modeA,modeB]
    ring
  have hb := norm_sub_le (nu q branch*modeA q branch X k d) (mu q branch*modeB q branch X k d)
  rw [← he,norm_mul,norm_mul,norm_mul] at hb
  dsimp only [decoder]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).mpr
  have ht := (hb.trans (show _ ≤
      (‖nu q branch‖+‖mu q branch‖)*(‖modeA q branch X k d‖+‖modeB q branch X k d‖) by
    nlinarith [mul_nonneg (norm_nonneg (nu q branch)) (norm_nonneg (modeB q branch X k d)),
      mul_nonneg (norm_nonneg (mu q branch)) (norm_nonneg (modeA q branch X k d))]))
  nlinarith only [ht]

/-- A decaying additive correction makes the weighted forced energy nonincreasing. -/
private theorem energy_comparison (E : ℝ → ℝ) (D g gamma C : ℝ)
    (hgap : g < gamma) (hC : 0 ≤ C) (hE : ∀ d, D ≤ d → 0 ≤ E d)
    (hd : ∀ d, D ≤ d → HasDerivAt E (deriv E d) d)
    (hb : ∀ d, D ≤ d → deriv E d ≤ 2*gamma*E d+C*Real.exp (2*g*d)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d, D ≤ d → E d ≤ B*Real.exp (2*gamma*d) := by
  let eta := gamma-g
  have he : 0 < eta := sub_pos.mpr hgap
  let W := fun d => Real.exp (-2*gamma*d)*E d+C/(2*eta)*Real.exp (-2*eta*d)
  have hWd (d : ℝ) (hD : D ≤ d) : HasDerivAt W
      (Real.exp (-2*gamma*d)*(deriv E d-2*gamma*E d)-C*Real.exp (-2*eta*d)) d := by
    have hx1 : HasDerivAt (fun t : ℝ => Real.exp (-2*gamma*t))
        (Real.exp (-2*gamma*d)*(-2*gamma)) d :=
      (Real.hasDerivAt_exp _).comp d (hasDerivAt_const_mul (-2*gamma))
    have hx2 : HasDerivAt (fun t : ℝ => Real.exp (-2*eta*t))
        (Real.exp (-2*eta*d)*(-2*eta)) d :=
      (Real.hasDerivAt_exp _).comp d (hasDerivAt_const_mul (-2*eta))
    have h1 : HasDerivAt (fun t => Real.exp (-2*gamma*t)*E t)
        ((Real.exp (-2*gamma*d)*(-2*gamma))*E d+Real.exp (-2*gamma*d)*deriv E d) d :=
      hx1.mul (hd d hD)
    have h2 : HasDerivAt (fun t => C/(2*eta)*Real.exp (-2*eta*t))
        (C/(2*eta)*(Real.exp (-2*eta*d)*(-2*eta))) d := hx2.const_mul (C/(2*eta))
    have hh : HasDerivAt W
        ((Real.exp (-2*gamma*d)*(-2*gamma))*E d+Real.exp (-2*gamma*d)*deriv E d+
          C/(2*eta)*(Real.exp (-2*eta*d)*(-2*eta))) d := by
      exact h1.add h2
    apply hh.congr_deriv
    field_simp
    ring
  have hWnonpos (d : ℝ) (hD : D ≤ d) : deriv W d ≤ 0 := by
    rw [(hWd d hD).deriv]
    have h := mul_le_mul_of_nonneg_left (hb d hD) (Real.exp_pos (-2*gamma*d)).le
    have hex : Real.exp (-2*gamma*d)*Real.exp (2*g*d)=Real.exp (-2*eta*d) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [eta]
      ring
    rw [← hex]
    nlinarith only [h]
  refine ⟨W D,add_nonneg (mul_nonneg (Real.exp_pos _).le (hE D le_rfl))
    (mul_nonneg (div_nonneg hC (by positivity)) (Real.exp_pos _).le),?_⟩
  intro d hD
  have hcont : ContinuousOn W (Icc D d) := fun v hv =>
    (hWd v hv.1).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ W (interior (Icc D d)) := by
    rw [interior_Icc]
    exact fun v hv => (hWd v hv.1.le).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn W (Icc D d) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc D d) hcont hdiff
    rw [interior_Icc]
    exact fun v hv => hWnonpos v hv.1.le
  have hle := hanti (left_mem_Icc.mpr hD) (right_mem_Icc.mpr hD) hD
  have hpos : 0 ≤ C/(2*eta)*Real.exp (-2*eta*d) := by positivity
  have hbare : Real.exp (-2*gamma*d)*E d ≤ W D := by
    change Real.exp (-2*gamma*d)*E d+C/(2*eta)*Real.exp (-2*eta*d) ≤ W D at hle
    linarith
  have hmul := mul_le_mul_of_nonneg_right hbare (Real.exp_pos (2*gamma*d)).le
  have hex : Real.exp (-2*gamma*d)*Real.exp (2*gamma*d)=1 := by
    rw [← Real.exp_add,show -2*gamma*d+2*gamma*d=0 by ring,Real.exp_zero]
  calc
    E d = (Real.exp (-2*gamma*d)*E d)*Real.exp (2*gamma*d) := by
      rw [mul_right_comm,hex,one_mul]
    _ ≤ _ := hmul

private theorem energy_inequality (q : XiZeroCopy) (branch : Bool) (X k d eta : ℝ)
    (hd : 0 < d) (he : 0 < eta)
    (hsmall : 4*decoder q branch*(rcoth d-1) ≤ eta) :
    HasDerivAt (energy q branch X k) (deriv (energy q branch X k) d) d ∧
    deriv (energy q branch X k) d ≤
      2*(sourceGrowthExponent q+eta)*energy q branch X k d+
      (2*‖parameter q branch‖^2/eta)*‖D4BMNativeCircle.mean q d X k‖^2 := by
  obtain ⟨hA,hB⟩ := modes_derivative q branch X k d hd
  have hE := (normSq_hasDerivAt hA).add (normSq_hasDerivAt hB)
  change HasDerivAt (energy q branch X k) _ d at hE
  refine ⟨hE.differentiableAt.hasDerivAt,?_⟩
  rw [hE.deriv]
  have hb := pair_energy_bound (modeA q branch X k d) (modeB q branch X k d)
    (deriv (fun t => angularMean q branch t X k) d) (D4BMNativeCircle.mean q d X k)
    (nu q branch) (mu q branch) (parameter q branch) (sourceGrowthExponent q) eta
    (decoder q branch) (rcoth d-1) he (by dsimp only [decoder]; positivity)
    (sub_nonneg.mpr (one_lt_rcoth_of_pos hd).le) (roots q branch).1 (roots q branch).2.1
    (decode_derivative q branch X k d) hsmall
  simpa only [energy,sub_eq_add_neg,add_assoc] using hb

/-- The existing literal-source bound discharges the forcing estimate for the actual modes. -/
private theorem energy_tail_at (q : XiZeroCopy) (branch : Bool) (X k gamma : ℝ)
    (hgamma : sourceGrowthExponent q < gamma) :
    ∃ D B : ℝ, 0 < D ∧ 0 ≤ B ∧ ∀ d, D ≤ d →
      energy q branch X k d ≤ B*Real.exp (2*gamma*d) := by
  let g := sourceGrowthExponent q
  let eta := gamma-g
  let K := decoder q branch
  have he : 0 < eta := by
    dsimp only [eta,g]
    exact sub_pos.mpr hgamma
  have hK : 0 ≤ K := by dsimp only [K,decoder]; positivity
  let D := max 1 (4*K/eta)
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨C,hC,hN⟩ := mean_global_growth q
  let L := C*Real.exp (g*|k|)
  have hL : 0 ≤ L := mul_nonneg hC (Real.exp_pos _).le
  have hNb (d : ℝ) (hd : 0 ≤ d) : ‖D4BMNativeCircle.mean q d X k‖ ≤ L*Real.exp (g*d) := by
    have h := hN d X k hd
    rw [mul_add,Real.exp_add] at h
    change _ ≤ (C*Real.exp (g*|k|))*Real.exp (g*d)
    convert h using 1
    ring
  have ht (d : ℝ) (hd : D ≤ d) :
      HasDerivAt (energy q branch X k) (deriv (energy q branch X k) d) d ∧
      deriv (energy q branch X k) d ≤ 2*gamma*energy q branch X k d+
        ((2*‖parameter q branch‖^2/eta)*L^2)*Real.exp (2*g*d) := by
    have hd0 := lt_of_lt_of_le hD hd
    have hKd : 4*K ≤ eta*d := by
      have h := (div_le_iff₀ he).mp ((le_max_right _ _).trans hd)
      nlinarith only [h]
    have hc : rcoth d-1 ≤ 1/d := by linarith [rcoth_lt_one_add_inv hd0]
    have hs : 4*K*(rcoth d-1) ≤ eta := by
      have h1 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*K by positivity)
      have h2 : 4*K/d ≤ eta := (div_le_iff₀ hd0).mpr (by nlinarith only [hKd])
      exact h1.trans (by simpa only [one_div,div_eq_mul_inv,one_mul] using h2)
    obtain ⟨hed,heb⟩ := energy_inequality q branch X k d eta hd0 he hs
    refine ⟨hed,heb.trans ?_⟩
    have hn := hNb d hd0.le
    have hsq : ‖D4BMNativeCircle.mean q d X k‖^2 ≤ L^2*Real.exp (2*g*d) := by
      have hp : Real.exp (g*d)^2=Real.exp (2*g*d) := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      have hx : ‖D4BMNativeCircle.mean q d X k‖^2 ≤ (L*Real.exp (g*d))^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (Real.exp_pos _).le)).mpr hn
      simpa only [mul_pow,hp] using hx
    have hm := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ 2*‖parameter q branch‖^2/eta by positivity)
    have hge : sourceGrowthExponent q+eta=gamma := by dsimp only [eta,g]; ring
    rw [hge]
    nlinarith only [hm]
  obtain ⟨B,hB,hb⟩ := energy_comparison (energy q branch X k) D g gamma
    ((2*‖parameter q branch‖^2/eta)*L^2) (by
      dsimp only [g]
      exact hgamma) (by positivity)
    (fun d _ => add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (fun d hd => (ht d hd).1) (fun d hd => (ht d hd).2)
  exact ⟨D,B,hD,hB,hb⟩

private theorem decode_field (q : XiZeroCopy) (branch : Bool) (X k d : ℝ) :
    ‖angularMean q branch d X k‖+‖deriv (fun t => angularMean q branch t X k) d‖ ≤
      (1/‖nu q branch-mu q branch‖+decoder q branch)*
        (‖modeA q branch X k d‖+‖modeB q branch X k d‖) := by
  have hn : 0 < ‖nu q branch-mu q branch‖ := norm_pos_iff.mpr (roots q branch).2.2
  have he : (nu q branch-mu q branch)*angularMean q branch d X k=
      modeA q branch X k d-modeB q branch X k d := by
    dsimp only [modeA,modeB]
    ring
  have hb := norm_sub_le (modeA q branch X k d) (modeB q branch X k d)
  rw [← he,norm_mul] at hb
  have hm : ‖angularMean q branch d X k‖ ≤
      (‖modeA q branch X k d‖+‖modeB q branch X k d‖)/‖nu q branch-mu q branch‖ :=
    (le_div_iff₀ hn).mpr (by nlinarith only [hb])
  have hd := decode_derivative q branch X k d
  calc
    _ ≤ (‖modeA q branch X k d‖+‖modeB q branch X k d‖)/‖nu q branch-mu q branch‖+
        decoder q branch*(‖modeA q branch X k d‖+‖modeB q branch X k d‖) := add_le_add hm hd
    _ = _ := by ring

/-- Every exponent strictly above the literal source growth controls the actual full
angular circle mean and its radial derivative. -/
private theorem angularMean_growth_at (q : XiZeroCopy) (branch : Bool) (X k gamma : ℝ)
    (hgamma : sourceGrowthExponent q < gamma) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 ≤ d →
      ‖angularMean q branch d X k‖+‖deriv (fun r => angularMean q branch r X k) d‖ ≤
        C*Real.exp (gamma*d) := by
  obtain ⟨D,B,hD,hB,hb⟩ := energy_tail_at q branch X k gamma hgamma
  let L := 1/‖nu q branch-mu q branch‖+decoder q branch
  have hL : 0 ≤ L := by dsimp only [L,decoder]; positivity
  have ht (d : ℝ) (hd : D ≤ d) :
      ‖angularMean q branch d X k‖+‖deriv (fun r => angularMean q branch r X k) d‖ ≤
        (L*(B+1))*Real.exp (gamma*d) := by
    let u := ‖modeA q branch X k d‖+‖modeB q branch X k d‖
    have hu : 0 ≤ u := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hu2 : u^2 ≤ 2*energy q branch X k d := by
      dsimp only [u,energy]
      rw [← Complex.sq_norm,← Complex.sq_norm]
      nlinarith [sq_nonneg (‖modeA q branch X k d‖-‖modeB q branch X k d‖)]
    have hex : Real.exp (2*gamma*d)=Real.exp (gamma*d)^2 := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    have hbe := hb d hd
    rw [hex] at hbe
    have hc : 2*B ≤ (B+1)^2 := by nlinarith [sq_nonneg B]
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.exp (gamma*d)))
    have hs : u^2 ≤ ((B+1)*Real.exp (gamma*d))^2 := by
      nlinarith only [hu2,hbe,hm]
    have hb1 : 0 ≤ (B+1)*Real.exp (gamma*d) := by positivity
    have hub := (sq_le_sq₀ hu hb1).mp hs
    exact (decode_field q branch X k d).trans (by
      change L*u ≤ _
      have hh := mul_le_mul_of_nonneg_left hub hL
      nlinarith only [hh])
  have hs := angularMean_smooth q branch X k
  have hds := (contDiff_infty_iff_deriv.mp hs).2
  have hc : Continuous (fun d => ‖angularMean q branch d X k‖+
      ‖deriv (fun r => angularMean q branch r X k) d‖) :=
    hs.continuous.norm.add hds.continuous.norm
  obtain ⟨C0,hC0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := D)).exists_bound_of_continuousOn hc.continuousOn
  let C := max C0 0+L*(B+1)
  have hLB : 0 ≤ L*(B+1) := by positivity
  have hC : 0 ≤ C := add_nonneg (le_max_right _ _) hLB
  refine ⟨C,hC,fun d hd => ?_⟩
  rcases le_total d D with hleft | hright
  · have hb0 := hC0 d ⟨hd,hleft⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at hb0
    have hg : 0 ≤ gamma := by
      have h1 := (sourceGrowthExponent_bounds q).1
      linarith
    have he1 : 1 ≤ Real.exp (gamma*d) := Real.one_le_exp_iff.mpr (mul_nonneg hg hd)
    have h01 : C0 ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right hLB)
    exact (hb0.trans h01).trans (by nlinarith [mul_le_mul_of_nonneg_left he1 hC])
  · exact (ht d hright).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (le_max_right _ _)) (Real.exp_pos _).le)

/-- The actual full angular circle mean and its radial derivative have an exponent
strictly below two. The constants come from the constructed field and literal source. -/
theorem angularMean_growth (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 ≤ d →
      ‖angularMean q branch d X k‖+‖deriv (fun r => angularMean q branch r X k) d‖ ≤
        C*Real.exp (decayExponent q*d) :=
  angularMean_growth_at q branch X k (decayExponent q) (decayExponent_bounds q).1

/-- Midway between the literal source and clock exponents, retaining strict tail slack. -/
def strictGrowthExponent (q : XiZeroCopy) : ℝ :=
  (sourceGrowthExponent q+decayExponent q)/2

theorem strictGrowthExponent_bounds (q : XiZeroCopy) :
    sourceGrowthExponent q < strictGrowthExponent q ∧
      strictGrowthExponent q < decayExponent q := by
  dsimp only [strictGrowthExponent]
  linarith [(decayExponent_bounds q).1]

/-- The literal full angular response has a strict gap below the physical clock
exponent. This is the tail slack required by the unrenormalized seed-cap limit. -/
theorem angularMean_strict_growth (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 ≤ d →
      ‖angularMean q branch d X k‖+‖deriv (fun r => angularMean q branch r X k) d‖ ≤
        C*Real.exp (strictGrowthExponent q*d) :=
  angularMean_growth_at q branch X k (strictGrowthExponent q)
    (strictGrowthExponent_bounds q).1

private theorem fullKernel_local_bound (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      ‖angularMean q branch (Real.arcosh (1+u)) X k-fullAngularField q branch ![X,Real.exp k]‖ ≤
        B*u := by
  obtain ⟨δ,B,hδ,hB,hb⟩ := local_increment_bound
    (D4BMFullAngularGoursat.fullAngularKernel_right_derivative q branch X k)
  have hc : ContinuousOn (fun z : ℝ => angularMean q branch (Real.arcosh z) X k) (Icc 1 2) :=
    (angularMean_smooth q branch X k).continuous.comp_continuousOn
      ((Real.continuousOn_arcosh 1 (by simp)).mono Icc_subset_Ici_self)
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let D := max A 0+‖fullAngularField q branch ![X,Real.exp k]‖
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨B+D/δ,add_nonneg hB (div_nonneg hD hδ.le),?_⟩
  intro u hu hu1
  by_cases huδ : u ≤ δ
  · have h := hb u hu huδ
    have hB : B*u ≤ (B+D/δ)*u := by gcongr
    exact (by simpa only [Real.arcosh_zero,angularMean_zero] using h).trans hB
  · have hδu : δ ≤ u := (lt_of_not_ge huδ).le
    have hz : 1+u ∈ Icc (1:ℝ) 2 := by constructor <;> linarith
    have hK : ‖angularMean q branch (Real.arcosh (1+u)) X k‖ ≤ max A 0 :=
      (hA (1+u) hz).trans (le_max_left _ _)
    have hdiff : ‖angularMean q branch (Real.arcosh (1+u)) X k-
        fullAngularField q branch ![X,Real.exp k]‖ ≤ D := by
      calc
        _ ≤ ‖angularMean q branch (Real.arcosh (1+u)) X k‖+
            ‖fullAngularField q branch ![X,Real.exp k]‖ := norm_sub_le _ _
        _ ≤ _ := by dsimp only [D]; linarith
    have hscale : D ≤ (D/δ)*u := by
      calc
        D = (D/δ)*δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hδu (div_nonneg hD hδ.le)
    exact hdiff.trans (hscale.trans (by gcongr))

/-- Literal quadratic corner jet of the full angular response used by the B2 cap. -/
theorem fullKernel_quadratic_remainder (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Icc (0 : ℝ) 1,
      ‖angularMean q branch (Real.arcosh (1 + u.val)) X k -
        fullAngularField q branch ![X, Real.exp k] -
        u.val • deriv (deriv (fun d => angularMean q branch d X k)) 0‖ ≤ C * u.val ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := smooth_even_arcosh_quadratic_bound
    (fun d => angularMean q branch d X k) (angularMean_smooth q branch X k)
    (fun d => angularMean_neg_radius q branch d X k)
  refine ⟨C, hC, fun u => ?_⟩
  simpa only [angularMean_zero] using hbound u

private theorem not_integrableOn_exp_pos_mul_Ioi (c : ℝ) (hc : 0 < c) :
    ¬ IntegrableOn (fun h : ℝ => Real.exp (c * h)) (Ioi (0 : ℝ)) volume := by
  intro hi
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (0 : ℝ)) volume := by
    apply hi.mono' (aestronglyMeasurable_const)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    simpa using Real.one_le_exp_iff.mpr (mul_nonneg hc.le hh.le)
  rw [integrableOn_const_iff] at hone
  rcases hone with hzero | hfinite
  · norm_num at hzero
  · rw [Real.volume_Ioi] at hfinite
    exact (lt_irrefl _) hfinite

/-- The absolute unrenormalized second cap-scale tail cannot furnish a DCT majorant.
The first-order cap majorant survives; this does not rule out a cancellation-based second limit. -/
theorem secondCapScale_absolute_tail_noGo (q : XiZeroCopy) :
    ¬ IntegrableOn (fun h : ℝ => Real.exp ((2 - decayExponent q) * h)) (Ioi (0 : ℝ)) volume :=
  not_integrableOn_exp_pos_mul_Ioi _ (sub_pos.mpr (decayExponent_bounds q).2)

private theorem full_large_radius_bound (b h : ℝ) (hb : 0 < b)
    (hu : 1 ≤ b*(Real.exp h-1)) :
    Real.arcosh (1+b*(Real.exp h-1)) ≤ Real.log 4+Real.log b+h := by
  have hbe : 1 < b*Real.exp h := by nlinarith
  have hp : 0 ≤ Real.log 4+Real.log b+h := by
    have ht : Real.log (b*Real.exp h)=Real.log b+h := by
      rw [Real.log_mul hb.ne' (Real.exp_pos h).ne',Real.log_exp]
    have hi := Real.log_nonneg hbe.le
    rw [ht] at hi
    linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)]
  have hz : 1 ≤ 1+b*(Real.exp h-1) := by linarith
  have hx : 1+b*(Real.exp h-1) ≤ 2*b*Real.exp h := by nlinarith
  have he : Real.exp (Real.log 4+Real.log b+h)=4*b*Real.exp h := by
    rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4),Real.exp_log hb]
  have hc : 2*b*Real.exp h ≤ Real.cosh (Real.log 4+Real.log b+h) := by
    rw [Real.cosh_eq,he]
    linarith [Real.exp_pos (-(Real.log 4+Real.log b+h))]
  have hl := Real.cosh_le_cosh.mp ((Real.cosh_arcosh hz).trans_le (hx.trans hc))
  simpa only [abs_of_nonneg (Real.arcosh_nonneg hz),abs_of_nonneg hp] using hl

/-- Scale-normalized full seed increments admit a strict-clock majorant.  This
uses the literal full characteristic coefficient and full response tail, not a
source surrogate or a renormalized kernel. -/
theorem fullAngularKernel_scaled_bound (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b h : ℝ, 0 < b → b ≤ 1 → 0 ≤ h →
      ‖angularMean q branch (Real.arcosh (1+b*(Real.exp h-1))) X k-
        fullAngularField q branch ![X,Real.exp k]‖ ≤
        b*C*(Real.exp h+Real.exp (strictGrowthExponent q*h)) := by
  obtain ⟨B,hB,hb⟩ := fullKernel_local_bound q branch X k
  obtain ⟨D,hD,hd⟩ := angularMean_strict_growth q branch X k
  let A := D*Real.exp (strictGrowthExponent q*(Real.log 4+|k|))
  let Q := fullAngularField q branch ![X,Real.exp k]
  have hgamma : 1 ≤ strictGrowthExponent q := by
    linarith [(sourceGrowthExponent_bounds q).1,(strictGrowthExponent_bounds q).1]
  have hgamma0 : 0 ≤ strictGrowthExponent q := hgamma.trans (by norm_num)
  have hA : 0 ≤ A := mul_nonneg hD (Real.exp_pos _).le
  refine ⟨B+A+‖Q‖,by positivity,fun b h hb0 hb1 hh => ?_⟩
  have he : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hu0 : 0 ≤ b*(Real.exp h-1) := by positivity
  by_cases hu : b*(Real.exp h-1) ≤ 1
  · apply (hb _ hu0 hu).trans
    have hprod : B*b*(Real.exp h-1) ≤ b*B*Real.exp h := by nlinarith
    have hm : b*B*Real.exp h ≤ b*(B+A+‖Q‖)*
        (Real.exp h+Real.exp (strictGrowthExponent q*h)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg Q]) hb0.le)
        (by linarith [Real.exp_pos (strictGrowthExponent q*h)]) (Real.exp_pos h).le (by positivity)
    nlinarith
  · have hu1 : 1 ≤ b*(Real.exp h-1) := (lt_of_not_ge hu).le
    have hz : 1 ≤ 1+b*(Real.exp h-1) := by linarith
    have hr0 := Real.arcosh_nonneg hz
    have hlog : Real.log b ≤ 0 := Real.log_nonpos hb0.le hb1
    have hpow : Real.exp (strictGrowthExponent q*Real.log b) ≤ b := by
      calc
        _ ≤ Real.exp (Real.log b) := Real.exp_le_exp.mpr (by nlinarith)
        _ = b := Real.exp_log hb0
    have hg : ‖angularMean q branch (Real.arcosh (1+b*(Real.exp h-1))) X k‖ ≤
        A*b*Real.exp (strictGrowthExponent q*h) := by
      have hm := hd (Real.arcosh (1+b*(Real.exp h-1))) hr0
      have hm' : ‖angularMean q branch (Real.arcosh (1+b*(Real.exp h-1))) X k‖ ≤
          D*Real.exp (strictGrowthExponent q*Real.arcosh (1+b*(Real.exp h-1))) :=
        (le_add_of_nonneg_right (norm_nonneg _)).trans hm
      apply hm'.trans
      calc
        _ ≤ D*Real.exp (strictGrowthExponent q*(Real.log 4+Real.log b+h+|k|)) := by
          apply mul_le_mul_of_nonneg_left _ hD
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ hgamma0
          linarith [full_large_radius_bound b h hb0 hu1]
        _ = A*Real.exp (strictGrowthExponent q*Real.log b)*
            Real.exp (strictGrowthExponent q*h) := by
          have heq : Real.exp (strictGrowthExponent q*(Real.log 4+Real.log b+h+|k|))=
              Real.exp (strictGrowthExponent q*(Real.log 4+|k|))*
              Real.exp (strictGrowthExponent q*Real.log b)*
              Real.exp (strictGrowthExponent q*h) := by
            rw [← Real.exp_add,← Real.exp_add]
            congr 1
            ring
          rw [heq]
          dsimp only [A]
          ring
        _ ≤ _ := by gcongr
    have hQ : ‖Q‖ ≤ b*‖Q‖*Real.exp h := by
      have hbe : 1 ≤ b*Real.exp h := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbe (norm_nonneg Q)]
    apply (norm_sub_le _ _).trans
    change ‖angularMean q branch (Real.arcosh (1+b*(Real.exp h-1))) X k‖+‖Q‖ ≤ _
    have hc : 0 ≤ b*B*(Real.exp h+Real.exp (strictGrowthExponent q*h)) := by positivity
    have h1 : 0 ≤ b*A*Real.exp h := by positivity
    have h2 : 0 ≤ b*‖Q‖*Real.exp (strictGrowthExponent q*h) := by positivity
    nlinarith

/-- The original doubled physical clock dominates the full mean's proved growth. -/
theorem terminal_exponent_neg (q : XiZeroCopy) (branch : Bool) :
    2*(physicalRate q branch).re+decayExponent q < 0 := by
  have hs := xi_divisor_support_re_mem_open_unit q.1
  have hg := (decayExponent_bounds q).2
  cases branch <;> simp only [physicalRate,↓reduceIte,Complex.sub_re] <;>
    norm_num <;> linarith

/-- The strict full-response exponent remains integrable against the unchanged
doubled physical clock. -/
theorem strict_terminal_exponent_neg (q : XiZeroCopy) (branch : Bool) :
    2*(physicalRate q branch).re+strictGrowthExponent q < 0 := by
  linarith [terminal_exponent_neg q branch,(strictGrowthExponent_bounds q).2]

/-- An integrable clock-weighted majorant, uniform over all circle radii
bounded by ingoing time plus a fixed offset. This is the terminal-face regime. -/
theorem angularMean_terminal_majorant (q : XiZeroCopy) (branch : Bool) (X k R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      MeasureTheory.IntegrableOn
        (fun v : ℝ => B*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v)) (Ioi 0) ∧
      ∀ v d : ℝ, 0 ≤ d → d ≤ v+|R| →
        Real.exp (2*(physicalRate q branch).re*v)*
          (‖angularMean q branch d X k‖+‖deriv (fun r => angularMean q branch r X k) d‖) ≤
          B*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v) := by
  obtain ⟨C,hC,hb⟩ := angularMean_growth q branch X k
  let B := C*Real.exp (decayExponent q*|R|)
  have hB : 0 ≤ B := mul_nonneg hC (Real.exp_pos _).le
  refine ⟨B,hB,(integrableOn_exp_mul_Ioi (terminal_exponent_neg q branch) 0).const_mul B,?_⟩
  intro v d hd hr
  have hg : 0 ≤ decayExponent q := by
    have h1 := (sourceGrowthExponent_bounds q).1
    have h2 := (decayExponent_bounds q).1
    linarith
  have hmono : C*Real.exp (decayExponent q*d) ≤ C*Real.exp (decayExponent q*(v+|R|)) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hg)) hC
  have h := mul_le_mul_of_nonneg_left ((hb d hd).trans hmono)
    (Real.exp_pos (2*(physicalRate q branch).re*v)).le
  calc
    _ ≤ Real.exp (2*(physicalRate q branch).re*v)*(C*Real.exp (decayExponent q*(v+|R|))) := h
    _ = _ := by
      dsimp only [B]
      simp only [mul_add,add_mul,Real.exp_add]
      ring

private theorem ingoing_invariant_formula (tau x v y : ℝ) :
    D4BMCausalKernel.invariant (v-y-tau) x y =
      (Real.cosh (v-tau)+(Real.sinh (v-tau)-Real.sinh x)*D4BMJointSource.radialUnit y)/Real.cosh x := by
  rw [show v-y-tau=v-tau-y by ring,D4BMCausalKernel.invariant,Real.cosh_sub,D4BMJointSource.radialUnit]
  field_simp [(Real.cosh_pos x).ne',(Real.cosh_pos y).ne']
  ring

/-- Source-null coordinates give a circle-radius bound uniform in the target
radius and in the entire negative source radial half-line. -/
theorem source_horizon_radius_bound (tau v x y : ℝ) (hv : 0 ≤ v) (hy : y ≤ 0) :
    Real.arcosh (max 1 (D4BMCausalKernel.invariant (v-y-tau) x y)) ≤
      v+|tau|+Real.log 4 := by
  have hu : 0 ≤ D4BMJointSource.radialUnit y ∧ D4BMJointSource.radialUnit y ≤ 1 := by
    rcases lt_or_eq_of_le hy with hy | rfl
    · exact ⟨(D4BMJointSource.radialUnit_bounds y hy).1.le,
        (D4BMJointSource.radialUnit_bounds y hy).2.le⟩
    · simp [D4BMJointSource.radialUnit]
  let u := D4BMJointSource.radialUnit y
  let T := v+|tau|
  have hT : 0 ≤ T := add_nonneg hv (abs_nonneg _)
  have he : 1 ≤ Real.exp T := Real.one_le_exp_iff.mpr hT
  have ha : Real.exp (v-tau) ≤ Real.exp T :=
    Real.exp_le_exp.mpr (by dsimp only [T]; linarith [neg_le_abs tau])
  have hb : Real.exp (-(v-tau)) ≤ Real.exp T :=
    Real.exp_le_exp.mpr (by dsimp only [T]; linarith [le_abs_self tau])
  have hc : Real.cosh (v-tau)+Real.sinh (v-tau)*u ≤ Real.exp T := by
    have h1 := mul_le_mul_of_nonneg_left ha (show 0 ≤ (1+u)/2 by dsimp only [u]; linarith [hu.1])
    have h2 := mul_le_mul_of_nonneg_left hb (show 0 ≤ (1-u)/2 by dsimp only [u]; linarith [hu.2])
    rw [Real.cosh_eq,Real.sinh_eq]
    nlinarith only [h1,h2]
  have hcx := Real.one_le_cosh x
  have hsx : -Real.cosh x ≤ Real.sinh x := by
    rw [Real.cosh_eq,Real.sinh_eq]
    linarith [Real.exp_pos x]
  have hsu : -(Real.sinh x)*u ≤ Real.cosh x := by
    have h1 := mul_le_mul_of_nonneg_right hsx hu.1
    have h2 := mul_le_mul_of_nonneg_left hu.2 (Real.cosh_pos x).le
    change -(Real.cosh x)*u ≤ Real.sinh x*u at h1
    change Real.cosh x*u ≤ Real.cosh x*1 at h2
    nlinarith only [h1,h2]
  have hI : D4BMCausalKernel.invariant (v-y-tau) x y ≤ 2*Real.exp T := by
    rw [ingoing_invariant_formula]
    apply (div_le_iff₀ (Real.cosh_pos x)).mpr
    have h1 := mul_le_mul_of_nonneg_left hcx (Real.exp_pos T).le
    have h2 := mul_le_mul_of_nonneg_right he (Real.cosh_pos x).le
    change Real.cosh (v-tau)+(Real.sinh (v-tau)-Real.sinh x)*u ≤ _
    nlinarith only [hc,hsu,h1,h2]
  have hz : 1 ≤ max 1 (D4BMCausalKernel.invariant (v-y-tau) x y) := le_max_left _ _
  have hZ : max 1 (D4BMCausalKernel.invariant (v-y-tau) x y) ≤ 2*Real.exp T :=
    max_le (by linarith only [he]) hI
  have hp : 0 ≤ T+Real.log 4 := add_nonneg hT (Real.log_nonneg (by norm_num))
  have hcosh : 2*Real.exp T ≤ Real.cosh (T+Real.log 4) := by
    rw [Real.cosh_eq,Real.exp_add T (Real.log 4),Real.exp_log (by norm_num : (0:ℝ)<4)]
    linarith [Real.exp_pos (-(T+Real.log 4))]
  have hh := Real.cosh_le_cosh.mp ((Real.cosh_arcosh hz).trans_le (hZ.trans hcosh))
  simpa only [T,abs_of_nonneg (Real.arcosh_nonneg hz),abs_of_nonneg hp] using hh

/-- The full source angular kernel has an integrable physical-clock majorant
uniform in both radial variables along ingoing source slices. -/
theorem angularMean_source_horizon_majorant (q : XiZeroCopy) (branch : Bool) (tau X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      MeasureTheory.IntegrableOn
        (fun v : ℝ => B*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v)) (Ioi 0) ∧
      ∀ v x y : ℝ, 0 ≤ v → y ≤ 0 →
        let d := Real.arcosh (max 1 (D4BMCausalKernel.invariant (v-y-tau) x y))
        Real.exp (2*(physicalRate q branch).re*v)*
          (‖angularMean q branch d X k‖+‖deriv (fun r => angularMean q branch r X k) d‖) ≤
          B*Real.exp ((2*(physicalRate q branch).re+decayExponent q)*v) := by
  obtain ⟨B,hB,hi,hb⟩ := angularMean_terminal_majorant q branch X k (|tau|+Real.log 4)
  refine ⟨B,hB,hi,fun v x y hv hy => ?_⟩
  dsimp only
  apply hb v _ (Real.arcosh_nonneg (le_max_left _ _))
  rw [abs_of_nonneg (add_nonneg (abs_nonneg tau) (Real.log_nonneg (by norm_num)))]
  have h := source_horizon_radius_bound tau v x y hv hy
  linarith only [h]

end
end RHTower.D4BMFullAngularGrowth
