import GaloisForLFunctions.RHTower.WeilWorkDeficitPrimeKernelBudget

/-!
# Mellin transform of the actual derivative product kernel

The single Bessel Mellin integral is justified by absolute Fubini. A finite
polynomial functional then transports `cuspDeriv` to multiplication by `1/2-s`.
This identifies `productKernel` on the full chamber `0 < s.re`, with absolute
integrability proved independently of the value formula. No growing-order
estimate or spectral-deficit upper bound is asserted here.
-/

noncomputable section
open MeasureTheory Set Polynomial
open scoped BigOperators
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
namespace RHTower.WeilWorkDeficitMellin

private def joint (s ν : ℂ) (z : ℝ × ℝ) : ℂ :=
  (z.1:ℂ)^(s-1) * besselOrderExpKernel z.1 ν z.2

private theorem section_factor (s ν : ℂ) (t x : ℝ) :
    joint s ν (x,t) = Complex.exp (ν*(t:ℂ)) *
      ((x:ℂ)^(s-1) * Complex.exp (-((Real.cosh t:ℝ):ℂ)*(x:ℂ))) := by
  simp only [joint, besselOrderExpKernel, ← Complex.ofReal_cosh]
  rw [show -(x:ℂ)*(Real.cosh t:ℂ)+ν*(t:ℂ) =
    ν*(t:ℂ)+ -((Real.cosh t:ℝ):ℂ)*(x:ℂ) by ring, Complex.exp_add]
  ring

private theorem section_integrable {s : ℂ} (hs : 0 < s.re) (ν : ℂ) (t : ℝ) :
    IntegrableOn (fun x => joint s ν (x,t)) (Ioi 0) := by
  have h := (integrableOn_cpow_mul_exp_neg_mul_Ioi hs
    (show 0 < ((Real.cosh t:ℝ):ℂ).re by simpa using Real.cosh_pos t)).const_mul
      (Complex.exp (ν*(t:ℂ)))
  change Integrable (fun x => joint s ν (x,t)) (volume.restrict (Ioi 0))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [section_factor, neg_mul]

private theorem section_integral {s : ℂ} (hs : 0 < s.re) (ν : ℂ) (t : ℝ) :
    (∫ x in Ioi (0:ℝ), joint s ν (x,t)) = Complex.Gamma s *
      (((Real.cosh t:ℝ):ℂ)^(-s)*Complex.exp (ν*(t:ℂ))) := by
  simp_rw [section_factor]
  rw [integral_const_mul]
  have h := integral_cpow_mul_exp_neg_mul_Ioi hs
    (show 0 < ((Real.cosh t:ℝ):ℂ).re by simpa using Real.cosh_pos t)
  simp only [neg_mul] at h ⊢
  rw [h]
  ring

private theorem norm_joint (s ν : ℂ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖joint s ν (x,t)‖ = Real.exp (ν.re*t) *
      ‖Complex.exp (-((Real.cosh t*x:ℝ):ℂ))‖ * x^(s.re-1) := by
  rw [section_factor, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.sub_re, Complex.one_re, Complex.neg_re]
  ring_nf

private theorem norm_section_integral {s : ℂ} (hs : 0 < s.re) (ν : ℂ) (t : ℝ) :
    (∫ x in Ioi (0:ℝ), ‖joint s ν (x,t)‖) = Real.Gamma s.re *
      ‖((Real.cosh t:ℝ):ℂ)^(-(s.re:ℂ))*Complex.exp ((ν.re:ℂ)*(t:ℂ))‖ := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => norm_joint s ν t hx)]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have he : (∫ x in Ioi (0:ℝ), ‖Complex.exp (-((Real.cosh t*x:ℝ):ℂ))‖ * x^(s.re-1)) =
      ∫ x in Ioi (0:ℝ), ‖Real.exp (-(Real.cosh t*x))*x^(s.re-1)‖ := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (le_of_lt hx) _))]
    simp only [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]
  rw [he, DaiYoshikawa.integral_norm_exp_neg_mul_rpow (Real.cosh_pos t) hs]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (Real.cosh_pos t), Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [Real.rpow_neg (Real.cosh_pos t).le]
  field_simp

private theorem joint_integrable {s ν : ℂ} (h : |ν.re| < s.re) :
    Integrable (joint s ν) ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hs : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) h
  have hm : AEStronglyMeasurable (joint s ν)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
    unfold joint besselOrderExpKernel
    fun_prop
  rw [integrable_prod_iff' hm]
  constructor
  · exact ae_of_all _ fun t => section_integrable hs ν t
  · have hi := integrable_complex_cosh_cpow_neg_mul_exp
      (s := (s.re:ℂ)) (a := (ν.re:ℂ)) (by simpa using h)
    refine (hi.norm.const_mul (Real.Gamma s.re)).congr (ae_of_all _ fun t => ?_)
    exact (norm_section_integral hs ν t).symm

private theorem bessel_mellin {s ν : ℂ} (h : |ν.re| < s.re) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*modifiedBesselKOrder x ν) =
      (2:ℂ)^(s-2)*Complex.Gamma ((s+ν)/2)*Complex.Gamma ((s-ν)/2) := by
  have hs : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) h
  have hj := joint_integrable h
  have hi := integral_integral_swap (f := fun x t => joint s ν (x,t)) hj
  have ht : ∀ x ∈ Ioi (0:ℝ), (∫ t, joint s ν (x,t)) =
      2*((x:ℂ)^(s-1)*modifiedBesselKOrder x ν) := by
    intro x hx
    simp only [joint, integral_const_mul]
    rw [integral_besselOrderExpKernel_eq_two_mul hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi ht, integral_const_mul] at hi
  simp_rw [section_integral hs ν] at hi
  rw [integral_const_mul] at hi
  have hp : 0 < ((s+ν)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.add_re]
    linarith [neg_abs_le ν.re]
  have hn : 0 < ((s-ν)/2).re := by
    simp only [Complex.div_ofNat_re, Complex.sub_re]
    linarith [le_abs_self ν.re]
  rw [integral_complex_cosh_cpow_neg_mul_exp hp hn] at hi
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have htwo : (2:ℂ)^(s-1) = 2*(2:ℂ)^(s-2) := by
    rw [show s-1=(s-2)+1 by ring, Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),
      Complex.cpow_one]
    ring
  rw [htwo] at hi
  apply mul_left_cancel₀ (show (2:ℂ)≠0 by norm_num)
  calc _ = _ := hi
       _ = _ := by field_simp

private def gammaMoment (s : ℂ) : ℝ[X] →ₗ[ℝ] ℂ :=
  Polynomial.lsum (fun j => LinearMap.toSpanSingleton ℝ ℂ
    ((Real.pi:ℂ)^(-(j:ℂ))*Complex.Gamma (s/2+j)))

private theorem gammaMoment_monomial (s : ℂ) (j : ℕ) (c : ℝ) :
    gammaMoment s (monomial j c) =
      (c:ℂ)*(Real.pi:ℂ)^(-(j:ℂ))*Complex.Gamma (s/2+j) := by
  simp [gammaMoment, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
    Complex.real_smul, mul_assoc]

private theorem cuspDeriv_monomial (j : ℕ) (c : ℝ) :
    cuspDeriv (monomial j c) = monomial j ((1/2+2*(j:ℝ))*c) -
      monomial (j+1) (2*Real.pi*c) := by
  cases j with
  | zero =>
    simp [← C_mul_X_pow_eq_monomial, cuspDeriv]
    ring
  | succ j =>
    simp only [cuspDeriv, derivative_monomial, Nat.add_sub_cancel, mul_assoc,
      X_mul_monomial, C_mul_monomial]
    rw [← map_add (monomial (j+1))]
    congr 2
    push_cast
    ring

private theorem gammaMoment_cuspDeriv {s : ℂ} (hs : 0 < s.re) (P : ℝ[X]) :
    gammaMoment s (cuspDeriv P) = (1/2-s)*gammaMoment s P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have hc : cuspDeriv (P+Q) = cuspDeriv P+cuspDeriv Q := by
      simp only [cuspDeriv, derivative_add]
      ring
    rw [hc, map_add, map_add, hP, hQ, mul_add]
  | monomial j c =>
    rw [cuspDeriv_monomial, map_sub, gammaMoment_monomial, gammaMoment_monomial,
      gammaMoment_monomial]
    have hz : s/2+(j:ℂ) ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
      positivity
    have hG : Complex.Gamma (s/2+(j+1:ℕ)) =
        (s/2+(j:ℂ))*Complex.Gamma (s/2+j) := by
      push_cast
      rw [← add_assoc, Complex.Gamma_add_one _ hz]
    have hp : (Real.pi:ℂ)^(-((j+1:ℕ):ℂ)) =
        (Real.pi:ℂ)^(-(j:ℂ))*(Real.pi:ℂ)⁻¹ := by
      push_cast
      rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast Real.pi_ne_zero), Complex.cpow_neg_one]
    rw [hG, hp]
    push_cast
    field_simp
    ring

private theorem gammaMoment_riemann (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    gammaMoment s (riemannKernelPoly k) =
      (1/2-s)^k * (s*(s-1)*Complex.Gamma (s/2)) := by
  induction k with
  | zero =>
    simp only [riemannKernelPoly, Function.iterate_zero_apply, riemannCuspPoly,
      map_sub, pow_zero, one_mul]
    rw [gammaMoment_cuspDeriv hs, gammaMoment_cuspDeriv hs]
    have hC : gammaMoment s (C (1/4) * (1:ℝ[X])) = (1/4:ℂ)*gammaMoment s 1 := by
      rw [← smul_eq_C_mul, map_smul]
      simp [Complex.real_smul]
    rw [hC, show (1:ℝ[X])=monomial 0 1 by simp, gammaMoment_monomial]
    simp only [Nat.cast_zero, neg_zero, Complex.cpow_zero, mul_one, Complex.ofReal_one,
      one_mul, add_zero]
    ring
  | succ k ih =>
    change gammaMoment s (cuspDeriv^[k+1] riemannCuspPoly) = _
    rw [Function.iterate_succ_apply', gammaMoment_cuspDeriv hs]
    change (1/2-s)*gammaMoment s (riemannKernelPoly k) = _
    rw [ih, pow_succ]
    ring

private theorem bessel_mellin_integrable {s ν : ℂ} (h : |ν.re| < s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*modifiedBesselKOrder x ν) (Ioi 0) := by
  have hi := ((joint_integrable h).integral_prod_left).div_const (2:ℂ)
  change Integrable _ (volume.restrict (Ioi 0))
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [joint, integral_const_mul]
  rw [integral_besselOrderExpKernel_eq_two_mul hx]
  ring

private theorem scale_factor (s ν : ℂ) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (x:ℂ)^(s-1)*modifiedBesselKOrder (c*x) ν =
      (c:ℂ)^(1-s)*((c*x:ℝ):ℂ)^(s-1)*modifiedBesselKOrder (c*x) ν := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hx.le]
  have he : (c:ℂ)^(1-s)*(c:ℂ)^(s-1) = 1 := by
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hc.ne'), show (1-s)+(s-1)=0 by ring,
      Complex.cpow_zero]
  rw [← mul_assoc, he, one_mul]

theorem scaled_integrable {s ν : ℂ} (h : |ν.re| < s.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*modifiedBesselKOrder (c*x) ν) (Ioi 0) := by
  let f : ℝ → ℂ := fun x => (x:ℂ)^(s-1)*modifiedBesselKOrder x ν
  have hi : IntegrableOn (fun x => f (c*x)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff f 0 hc).mpr (by
      simpa only [mul_zero] using bessel_mellin_integrable h)
  refine IntegrableOn.congr_fun (hi.const_mul ((c:ℂ)^(1-s))) (fun x hx => ?_) measurableSet_Ioi
  simpa only [f, mul_assoc] using (scale_factor s ν hc hx).symm

theorem scaled_mellin {s ν : ℂ} (h : |ν.re| < s.re) {c : ℝ} (hc : 0 < c) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*modifiedBesselKOrder (c*x) ν) =
      (c:ℂ)^(-s)*((2:ℂ)^(s-2)*Complex.Gamma ((s+ν)/2)*Complex.Gamma ((s-ν)/2)) := by
  let f : ℝ → ℂ := fun x => (x:ℂ)^(s-1)*modifiedBesselKOrder x ν
  have he : (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*modifiedBesselKOrder (c*x) ν) =
      ∫ x in Ioi (0:ℝ), (c:ℂ)^(1-s)*f (c*x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simpa only [f, mul_assoc] using scale_factor s ν hc hx
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi f 0 hc]
  simp only [mul_zero, Complex.real_smul, Complex.ofReal_inv]
  have hp : (c:ℂ)^(1-s)*(c:ℂ)⁻¹ = (c:ℂ)^(-s) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ (by exact_mod_cast hc.ne')]
    congr 1
    ring
  rw [← mul_assoc, hp]
  congr 1
  exact bessel_mellin h

private def mono (j l : ℕ) (x : ℝ) : ℂ :=
  (x:ℂ)^(j+l)*modifiedBesselKOrder (2*Real.pi*x) ((j:ℂ)-l)

private theorem mono_chamber {s : ℂ} (hs : 0 < s.re) (j l : ℕ) :
    |((j:ℂ)-l).re| < (s+(j+l:ℕ)).re := by
  simp only [Complex.sub_re, Complex.natCast_re, Complex.add_re, Nat.cast_add]
  rw [abs_lt]
  constructor <;> linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j), (Nat.cast_nonneg l : (0:ℝ) ≤ l)]

private theorem mono_factor (s : ℂ) (j l : ℕ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(s-1)*mono j l x =
      (x:ℂ)^(s+(j+l:ℕ)-1)*modifiedBesselKOrder (2*Real.pi*x) ((j:ℂ)-l) := by
  rw [mono, ← Complex.cpow_natCast, ← mul_assoc,
    ← Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]
  congr 2
  ring

private theorem mono_integrable {s : ℂ} (hs : 0 < s.re) (j l : ℕ) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*mono j l x) (Ioi 0) := by
  refine IntegrableOn.congr_fun (scaled_integrable (mono_chamber hs j l)
    (by positivity : (0:ℝ)<2*Real.pi)) (fun x hx => ?_) measurableSet_Ioi
  exact (mono_factor s j l hx).symm

private theorem mono_mellin {s : ℂ} (hs : 0 < s.re) (j l : ℕ) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*mono j l x) =
      (Real.pi:ℂ)^(-s)/4 *
        (((Real.pi:ℂ)^(-(j:ℂ))*Complex.Gamma (s/2+j))*
          ((Real.pi:ℂ)^(-(l:ℂ))*Complex.Gamma (s/2+l))) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => mono_factor s j l hx),
    scaled_mellin (mono_chamber hs j l) (by positivity : (0:ℝ)<2*Real.pi)]
  have hplus : (s+(j+l:ℕ)+((j:ℂ)-l))/2=s/2+j := by push_cast; ring
  have hminus : (s+(j+l:ℕ)-((j:ℂ)-l))/2=s/2+l := by push_cast; ring
  rw [hplus,hminus]
  have hp : (((2*Real.pi:ℝ):ℂ)^(-(s+(j+l:ℕ)))) * (2:ℂ)^(s+(j+l:ℕ)-2) =
      (Real.pi:ℂ)^(-s)/4*(Real.pi:ℂ)^(-(j:ℂ))*(Real.pi:ℂ)^(-(l:ℂ)) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ)≤2) Real.pi_pos.le]
    norm_num only [Complex.ofReal_ofNat]
    have he : (2:ℂ)^(-(s+(j+l:ℕ)))*(2:ℂ)^(s+(j+l:ℕ)-2) = (1/4:ℂ) := by
      rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),
        show -(s+(j+l:ℕ))+(s+(j+l:ℕ)-2)=(-2:ℂ) by ring]
      norm_num [Complex.cpow_neg]
    have hpi : (Real.pi:ℂ)^(-(s+(j+l:ℕ))) =
        (Real.pi:ℂ)^(-s)*(Real.pi:ℂ)^(-(j:ℂ))*(Real.pi:ℂ)^(-(l:ℂ)) := by
      push_cast
      rw [show -(s+((j:ℂ)+l))=(-s+ -(j:ℂ))+ -(l:ℂ) by ring,
        Complex.cpow_add _ _ (by exact_mod_cast Real.pi_ne_zero),
        Complex.cpow_add _ _ (by exact_mod_cast Real.pi_ne_zero)]
    rw [show (2:ℂ)^(-(s+(j+l:ℕ)))*(Real.pi:ℂ)^(-(s+(j+l:ℕ)))*(2:ℂ)^(s+(j+l:ℕ)-2) =
        ((2:ℂ)^(-(s+(j+l:ℕ)))*(2:ℂ)^(s+(j+l:ℕ)-2))*(Real.pi:ℂ)^(-(s+(j+l:ℕ))) by ring,
      he,hpi]
    ring
  calc _ = ((((2*Real.pi:ℝ):ℂ)^(-(s+(j+l:ℕ)))) * (2:ℂ)^(s+(j+l:ℕ)-2)) *
      Complex.Gamma (s/2+j)*Complex.Gamma (s/2+l) := by ring
       _ = _ := by rw [hp]; ring

private theorem gammaMoment_range (s : ℂ) (P : ℝ[X]) :
    gammaMoment s P = ∑ j ∈ Finset.range (P.natDegree+1),
      (P.coeff j:ℂ)*((Real.pi:ℂ)^(-(j:ℂ))*Complex.Gamma (s/2+j)) := by
  unfold gammaMoment
  rw [Polynomial.lsum_apply, Polynomial.sum_eq_of_subset _
    (fun j => (LinearMap.toSpanSingleton ℝ ℂ _).map_zero)
    Polynomial.supp_subset_range_natDegree_succ]
  simp [Complex.real_smul]

open WeilWorkDeficitPrimeKernel

private theorem kernel_cast (k : ℕ) {x : ℝ} (hx : 0 < x) :
    (productKernel k x:ℂ) = (-1:ℂ)^k *
      ∑ j ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
        ∑ l ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
          ((riemannKernelPoly k).coeff j:ℂ)*((riemannKernelPoly k).coeff l:ℂ)*mono j l x := by
  simp only [productKernel, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  simp only [mono, ← modifiedBesselKOrder_ofReal (by positivity : 0 < 2*Real.pi*x),
    Complex.ofReal_sub, Complex.ofReal_natCast]

private theorem weighted_kernel (k : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x:ℂ)^(s-1)*(productKernel k x:ℂ) = (-1:ℂ)^k *
      ∑ j ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
        ∑ l ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
          (((riemannKernelPoly k).coeff j:ℂ)*((riemannKernelPoly k).coeff l:ℂ))*
            ((x:ℂ)^(s-1)*mono j l x) := by
  rw [kernel_cast k hx, mul_left_comm, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Absolute Mellin integrability of the actual finite derivative product kernel. -/
theorem productKernel_mellin_integrable (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*(productKernel k x:ℂ)) (Ioi 0) := by
  have hi : IntegrableOn (fun x : ℝ =>
      ∑ j ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
        ∑ l ∈ Finset.range ((riemannKernelPoly k).natDegree+1),
          (((riemannKernelPoly k).coeff j:ℂ)*((riemannKernelPoly k).coeff l:ℂ))*
            ((x:ℂ)^(s-1)*mono j l x)) (Ioi 0) := by
    apply integrable_finsetSum
    intro j hj
    apply integrable_finsetSum
    intro l hl
    exact (mono_integrable hs j l).const_mul _
  refine IntegrableOn.congr_fun (hi.const_mul ((-1:ℂ)^k)) (fun x hx => ?_) measurableSet_Ioi
  exact (weighted_kernel k s hx).symm

private theorem productKernel_mellin_moment (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*(productKernel k x:ℂ)) =
      (-1:ℂ)^k * ((Real.pi:ℂ)^(-s)/4) * (gammaMoment s (riemannKernelPoly k))^2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => weighted_kernel k s hx),
    integral_const_mul, integral_finsetSum _ (fun j hj =>
      integrable_finsetSum _ (fun l hl => (mono_integrable hs j l).const_mul _))]
  simp_rw [integral_finsetSum _ (fun l hl => (mono_integrable hs _ l).const_mul _),
    integral_const_mul, mono_mellin hs]
  rw [gammaMoment_range, pow_two]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Exact Mellin transform of the actual derivative product kernel, throughout its
positive-real-part chamber. The polynomial is the corpus's `riemannKernelPoly`. -/
theorem productKernel_mellin (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(s-1)*(productKernel k x:ℂ)) =
      (-1:ℂ)^k * (s-1/2)^(2*k) * s^2 * (s-1)^2 *
        (Real.pi:ℂ)^(-s) * (Complex.Gamma (s/2))^2 / 4 := by
  rw [productKernel_mellin_moment k hs, gammaMoment_riemann k hs, mul_pow]
  have hp : ((1/2-s)^k)^2 = (s-1/2)^(2*k) := by
    calc ((1/2-s)^k)^2 = ((1/2-s)^2)^k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
         _ = ((s-1/2)^2)^k := by congr 1; ring
         _ = (s-1/2)^(2*k) := (pow_mul _ 2 k).symm
  rw [hp]
  ring

end RHTower.WeilWorkDeficitMellin
