import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.LaguerreInequality

/-!
# The unconditional Xi Laguerre--Polya interface

The exact Xi canonical product is exhausted by deterministic reflection-closed finite subsets of
the actual divisor.  Under RH their spectral points are real, the genus-one exponentials cancel in
pairs, and the resulting real-split polynomials converge locally uniformly together with their
first two derivatives.  This supplies `RiemannHypothesis → LaguerrePolya Xi` and removes the former
Pólya hypothesis from the strict Laguerre-margin detector.
-/

open Complex Metric Set Real Filter Topology Polynomial

namespace RHTower

noncomputable section

open scoped Classical

lemma xiZeroReflectEquiv_involutive (ρ : XiDivisorSupport) :
    xiZeroReflectEquiv (xiZeroReflectEquiv ρ) = ρ := by
  apply Subtype.ext
  simp [xiZeroReflectEquiv]

def xiSupportSymmFinset (s : Finset XiDivisorSupport) : Finset XiDivisorSupport :=
  s ∪ s.image xiZeroReflectEquiv

lemma xiSupportSymmFinset_reflect_mem_iff (s : Finset XiDivisorSupport)
    (ρ : XiDivisorSupport) :
    xiZeroReflectEquiv ρ ∈ xiSupportSymmFinset s ↔ ρ ∈ xiSupportSymmFinset s := by
  simp only [xiSupportSymmFinset, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hρ | ⟨u, hu, heq⟩)
    · right
      exact ⟨xiZeroReflectEquiv ρ, hρ, xiZeroReflectEquiv_involutive ρ⟩
    · left
      exact (xiZeroReflectEquiv.injective heq) ▸ hu
  · rintro (hρ | ⟨u, hu, heq⟩)
    · right
      exact ⟨ρ, hρ, rfl⟩
    · left
      rw [← heq, xiZeroReflectEquiv_involutive]
      exact hu

def xiPairedCopyFinset (s : Finset XiDivisorSupport) : Finset XiZeroCopy :=
  (xiSupportSymmFinset s).sigma fun _ => Finset.univ

lemma xiSupportSymmFinset_mono : Monotone xiSupportSymmFinset := by
  intro s t hst
  exact Finset.union_subset_union hst (Finset.image_mono _ hst)

lemma xiPairedCopyFinset_mono : Monotone xiPairedCopyFinset := by
  intro s t hst
  apply Finset.sigma_mono (xiSupportSymmFinset_mono hst)
  intro ρ
  exact Finset.Subset.rfl

theorem xiPairedCopyFinset_tendsto_atTop :
    Tendsto xiPairedCopyFinset atTop atTop := by
  apply xiPairedCopyFinset_mono.tendsto_atTop_finset
  intro q
  refine ⟨{q.1}, ?_⟩
  simp [xiPairedCopyFinset, xiSupportSymmFinset]

@[simp]
lemma xiZeroCopyReflectEquiv_fst (q : XiZeroCopy) :
    (xiZeroCopyReflectEquiv q).1 = xiZeroReflectEquiv q.1 := rfl

lemma xiPairedCopyFinset_reflect_mem_iff (s : Finset XiDivisorSupport) (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv q ∈ xiPairedCopyFinset s ↔ q ∈ xiPairedCopyFinset s := by
  simp only [xiPairedCopyFinset, Finset.mem_sigma]
  constructor
  · intro h
    exact ⟨(xiSupportSymmFinset_reflect_mem_iff s q.1).mp
      (by simpa only [xiZeroCopyReflectEquiv_fst] using h.1), Finset.mem_univ _⟩
  · intro h
    exact ⟨(by simpa only [xiZeroCopyReflectEquiv_fst] using
      (xiSupportSymmFinset_reflect_mem_iff s q.1).mpr h.1), Finset.mem_univ _⟩

lemma xiPairedCopyFinset_image_reflect (s : Finset XiDivisorSupport) :
    (xiPairedCopyFinset s).image xiZeroCopyReflectEquiv = xiPairedCopyFinset s := by
  ext q
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (xiPairedCopyFinset_reflect_mem_iff s u).mpr hu
  · intro hq
    obtain ⟨u, rfl⟩ := xiZeroCopyReflectEquiv.surjective q
    exact ⟨u, (xiPairedCopyFinset_reflect_mem_iff s u).mp hq, rfl⟩

lemma xiPairedCopyFinset_inv_sum_zero (s : Finset XiDivisorSupport) :
    ∑ q ∈ xiPairedCopyFinset s, (xiSpectralPoint q)⁻¹ = 0 := by
  let A := xiPairedCopyFinset s
  have hreindex : (∑ q ∈ A, (xiSpectralPoint q)⁻¹) =
      ∑ q ∈ A, (xiSpectralPoint (xiZeroCopyReflectEquiv q))⁻¹ := by
    calc
      (∑ q ∈ A, (xiSpectralPoint q)⁻¹) =
          ∑ q ∈ A.image xiZeroCopyReflectEquiv, (xiSpectralPoint q)⁻¹ := by
        rw [xiPairedCopyFinset_image_reflect]
      _ = ∑ q ∈ A, (xiSpectralPoint (xiZeroCopyReflectEquiv q))⁻¹ := by
        rw [Finset.sum_image]
        exact xiZeroCopyReflectEquiv.injective.injOn
  have hneg : (∑ q ∈ A, (xiSpectralPoint q)⁻¹) =
      -(∑ q ∈ A, (xiSpectralPoint q)⁻¹) := by
    simpa only [xiSpectralPoint_reflect, inv_neg, Finset.sum_neg_distrib] using hreindex
  change (∑ q ∈ A, (xiSpectralPoint q)⁻¹) = 0
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hneg)

def xiPairedE1Product (s : Finset XiDivisorSupport) (z : ℂ) : ℂ :=
  ∏ q ∈ xiPairedCopyFinset s, weierstrassE1 (z / xiSpectralPoint q)

lemma xiPairedE1Product_eq_linear_product (s : Finset XiDivisorSupport) (z : ℂ) :
    xiPairedE1Product s z =
      ∏ q ∈ xiPairedCopyFinset s, (1 - z / xiSpectralPoint q) := by
  rw [xiPairedE1Product]
  simp_rw [weierstrassE1]
  rw [Finset.prod_mul_distrib]
  have hexp : (∏ q ∈ xiPairedCopyFinset s,
      Complex.exp (z / xiSpectralPoint q)) = 1 := by
    rw [← Complex.exp_sum]
    have hsum : (∑ q ∈ xiPairedCopyFinset s, z / xiSpectralPoint q) = 0 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum, xiPairedCopyFinset_inv_sum_zero, mul_zero]
    rw [hsum]
    simp
  rw [hexp, mul_one]

def xiRealSpectralPoint (q : XiZeroCopy) : ℝ := (xiSpectralPoint q).re

lemma xiSpectralPoint_eq_ofReal_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiSpectralPoint q = (xiRealSpectralPoint q : ℂ) := by
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [xiRealSpectralPoint, ht]
  simp

lemma xiRealSpectralPoint_ne_zero (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiRealSpectralPoint q ≠ 0 := by
  intro h
  apply xiSpectralPoint_ne_zero q
  rw [xiSpectralPoint_eq_ofReal_of_rh hRH q, h]
  norm_num

def xiPairedPolynomial (s : Finset XiDivisorSupport) : Polynomial ℝ :=
  ∏ q ∈ xiPairedCopyFinset s,
    C (-(xiRealSpectralPoint q)⁻¹) * (X - C (xiRealSpectralPoint q))

lemma xiPairedPolynomial_splits (s : Finset XiDivisorSupport) :
    (xiPairedPolynomial s).Splits := by
  rw [xiPairedPolynomial]
  let A := xiPairedCopyFinset s
  change (∏ q ∈ A,
    C (-(xiRealSpectralPoint q)⁻¹) * (X - C (xiRealSpectralPoint q))).Splits
  induction A using Finset.induction_on with
  | empty => simp
  | @insert q A hq ih =>
      rw [Finset.prod_insert hq]
      exact ((Splits.C _).mul (Splits.X_sub_C _)).mul ih

lemma xiPairedPolynomial_eval_eq_product_of_rh (hRH : RiemannHypothesis)
    (s : Finset XiDivisorSupport) (x : ℝ) :
    ((Polynomial.eval x (xiPairedPolynomial s) : ℝ) : ℂ) =
      xiPairedE1Product s (x : ℂ) := by
  rw [xiPairedE1Product_eq_linear_product, xiPairedPolynomial]
  simp only [eval_prod, eval_mul, eval_C, eval_sub, eval_X]
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro q hq
  rw [xiSpectralPoint_eq_ofReal_of_rh hRH q]
  have ht := xiRealSpectralPoint_ne_zero hRH q
  have htc : (xiRealSpectralPoint q : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [htc]
  ring

lemma xiPairedPolynomial_map_eval_eq_product_of_rh (hRH : RiemannHypothesis)
    (s : Finset XiDivisorSupport) (z : ℂ) :
    ((xiPairedPolynomial s).map Complex.ofRealHom).eval z = xiPairedE1Product s z := by
  rw [xiPairedE1Product_eq_linear_product, xiPairedPolynomial]
  rw [Polynomial.eval_map, eval₂_finsetProd]
  simp only [eval₂_mul, eval₂_C, eval₂_sub, eval₂_X]
  apply Finset.prod_congr rfl
  intro q hq
  rw [xiSpectralPoint_eq_ofReal_of_rh hRH q]
  have ht := xiRealSpectralPoint_ne_zero hRH q
  have htc : (xiRealSpectralPoint q : ℂ) ≠ 0 := by exact_mod_cast ht
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_neg, Complex.ofReal_inv]
  field_simp [htc]
  ring

theorem xiPairedE1Product_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn xiPairedE1Product xiCanonicalProduct atTop Set.univ := by
  have hbase := xiCanonicalProduct_hasProdLocallyUniformlyOn
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at hbase
  intro u hu z hz
  obtain ⟨t, ht, hevent⟩ :=
    hbase u hu z hz
  refine ⟨t, ht, ?_⟩
  have hevent' := xiPairedCopyFinset_tendsto_atTop.eventually hevent
  filter_upwards [hevent'] with s hs
  simpa only [xiPairedE1Product] using hs

lemma xiPairedE1Product_differentiable (s : Finset XiDivisorSupport) :
    Differentiable ℂ (xiPairedE1Product s) := by
  intro z
  unfold xiPairedE1Product
  simp_rw [weierstrassE1]
  fun_prop

theorem xiPairedE1Product_deriv_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn (deriv ∘ xiPairedE1Product)
      (deriv xiCanonicalProduct) atTop Set.univ :=
  xiPairedE1Product_tendstoLocallyUniformlyOn.deriv
    (Filter.Eventually.of_forall fun s => (xiPairedE1Product_differentiable s).differentiableOn)
    isOpen_univ

theorem xiPairedE1Product_secondDeriv_tendstoLocallyUniformlyOn :
    TendstoLocallyUniformlyOn (deriv ∘ deriv ∘ xiPairedE1Product)
      (deriv (deriv xiCanonicalProduct)) atTop Set.univ := by
  apply xiPairedE1Product_deriv_tendstoLocallyUniformlyOn.deriv
  · apply Filter.Eventually.of_forall
    intro s z _
    exact (((xiPairedE1Product_differentiable s).analyticAt z).deriv).differentiableAt
      |>.differentiableWithinAt
  · exact isOpen_univ

lemma xiPairedE1Product_deriv_ofReal_eq (hRH : RiemannHypothesis)
    (s : Finset XiDivisorSupport) (x : ℝ) :
    deriv (xiPairedE1Product s) (x : ℂ) =
      ((Polynomial.eval x (derivative (xiPairedPolynomial s)) : ℝ) : ℂ) := by
  have heq : (fun z => ((xiPairedPolynomial s).map Complex.ofRealHom).eval z) =
      xiPairedE1Product s := by
    funext z
    exact xiPairedPolynomial_map_eval_eq_product_of_rh hRH s z
  have hd := congrArg (fun f : ℂ → ℂ => deriv f (x : ℂ)) heq
  change deriv (fun z => ((xiPairedPolynomial s).map Complex.ofRealHom).eval z) (x : ℂ) =
    deriv (xiPairedE1Product s) (x : ℂ) at hd
  rw [(((xiPairedPolynomial s).map Complex.ofRealHom).hasDerivAt (x : ℂ)).deriv,
    Polynomial.derivative_map] at hd
  have hcast : ((derivative (xiPairedPolynomial s)).map Complex.ofRealHom).eval (x : ℂ) =
      ((Polynomial.eval x (derivative (xiPairedPolynomial s)) : ℝ) : ℂ) := by
    exact Polynomial.eval_map_apply (p := derivative (xiPairedPolynomial s))
      Complex.ofRealHom x
  rw [hcast] at hd
  exact hd.symm

lemma xiPairedE1Product_secondDeriv_ofReal_eq (hRH : RiemannHypothesis)
    (s : Finset XiDivisorSupport) (x : ℝ) :
    deriv (deriv (xiPairedE1Product s)) (x : ℂ) =
      ((Polynomial.eval x (derivative (derivative (xiPairedPolynomial s))) : ℝ) : ℂ) := by
  have heq : (fun z => ((xiPairedPolynomial s).map Complex.ofRealHom).eval z) =
      xiPairedE1Product s := by
    funext z
    exact xiPairedPolynomial_map_eval_eq_product_of_rh hRH s z
  have hd1 := congrArg (fun f : ℂ → ℂ => deriv f) heq
  have hd2 := congrArg (fun f : ℂ → ℂ => deriv f (x : ℂ)) hd1
  change deriv (deriv (fun z => ((xiPairedPolynomial s).map Complex.ofRealHom).eval z))
      (x : ℂ) = deriv (deriv (xiPairedE1Product s)) (x : ℂ) at hd2
  rw [show deriv (fun z => ((xiPairedPolynomial s).map Complex.ofRealHom).eval z) =
      fun z => (((xiPairedPolynomial s).map Complex.ofRealHom).derivative).eval z by
        funext z
        exact (((xiPairedPolynomial s).map Complex.ofRealHom).hasDerivAt z).deriv,
    show deriv (fun z => (((xiPairedPolynomial s).map Complex.ofRealHom).derivative).eval z) (x : ℂ) =
      (((xiPairedPolynomial s).map Complex.ofRealHom).derivative.derivative).eval (x : ℂ) by
        exact ((((xiPairedPolynomial s).map Complex.ofRealHom).derivative.hasDerivAt
          (x : ℂ))).deriv,
    Polynomial.derivative_map, Polynomial.derivative_map] at hd2
  have hcast : ((derivative (derivative (xiPairedPolynomial s))).map
      Complex.ofRealHom).eval (x : ℂ) =
      ((Polynomial.eval x (derivative (derivative (xiPairedPolynomial s))) : ℝ) : ℂ) := by
    exact Polynomial.eval_map_apply
      (p := derivative (derivative (xiPairedPolynomial s))) Complex.ofRealHom x
  rw [hcast] at hd2
  exact hd2.symm

theorem xiPairedPolynomial_eval_tendsto (hRH : RiemannHypothesis) (x : ℝ) :
    Tendsto (fun s : Finset XiDivisorSupport => (xiPairedPolynomial s).eval x)
      atTop (𝓝 (xiCanonicalProduct (x : ℂ)).re) := by
  have hc := xiPairedE1Product_tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ (x : ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  refine hr.congr' (Filter.Eventually.of_forall fun s => ?_)
  change (xiPairedE1Product s (x : ℂ)).re = (xiPairedPolynomial s).eval x
  exact (congrArg Complex.re (xiPairedPolynomial_eval_eq_product_of_rh hRH s x)).symm

theorem xiPairedPolynomial_derivative_eval_tendsto (hRH : RiemannHypothesis) (x : ℝ) :
    Tendsto (fun s : Finset XiDivisorSupport =>
      (derivative (xiPairedPolynomial s)).eval x)
      atTop (𝓝 (deriv xiCanonicalProduct (x : ℂ)).re) := by
  have hc := xiPairedE1Product_deriv_tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ (x : ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  refine hr.congr' (Filter.Eventually.of_forall fun s => ?_)
  change (deriv (xiPairedE1Product s) (x : ℂ)).re =
    (derivative (xiPairedPolynomial s)).eval x
  rw [xiPairedE1Product_deriv_ofReal_eq hRH]
  simp

theorem xiPairedPolynomial_secondDerivative_eval_tendsto (hRH : RiemannHypothesis) (x : ℝ) :
    Tendsto (fun s : Finset XiDivisorSupport =>
      (derivative (derivative (xiPairedPolynomial s))).eval x)
      atTop (𝓝 (deriv (deriv xiCanonicalProduct) (x : ℂ)).re) := by
  have hc := xiPairedE1Product_secondDeriv_tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ (x : ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  refine hr.congr' (Filter.Eventually.of_forall fun s => ?_)
  change (deriv (deriv (xiPairedE1Product s)) (x : ℂ)).re =
    (derivative (derivative (xiPairedPolynomial s))).eval x
  rw [xiPairedE1Product_secondDeriv_ofReal_eq hRH]
  simp

theorem xiCanonicalProduct_laguerre_re_of_rh (hRH : RiemannHypothesis) (x : ℝ) :
    (xiCanonicalProduct (x : ℂ)).re *
        (deriv (deriv xiCanonicalProduct) (x : ℂ)).re ≤
      (deriv xiCanonicalProduct (x : ℂ)).re ^ (2 : ℕ) := by
  have hprod := (xiPairedPolynomial_eval_tendsto hRH x).mul
    (xiPairedPolynomial_secondDerivative_eval_tendsto hRH x)
  have hsq := (xiPairedPolynomial_derivative_eval_tendsto hRH x).pow 2
  exact le_of_tendsto_of_tendsto' hprod hsq fun s =>
    laguerre_inequality_poly (xiPairedPolynomial_splits s) x

lemma complex_deriv_eq_of_real_restriction (F : ℂ → ℂ) (f : ℝ → ℝ)
    (hF : Differentiable ℂ F) (hrestrict : ∀ x : ℝ, F (x : ℂ) = (f x : ℂ)) (x : ℝ) :
    deriv F (x : ℂ) = ((deriv f x : ℝ) : ℂ) := by
  have hFc : HasDerivAt F (deriv F (x : ℂ)) (x : ℂ) := (hF (x : ℂ)).hasDerivAt
  have hFr : HasDerivAt (fun y : ℝ => (F (y : ℂ)).re)
      (deriv F (x : ℂ)).re x := hFc.real_of_complex
  have hfunR : (fun y : ℝ => (F (y : ℂ)).re) = f := by
    funext y
    rw [hrestrict y]
    simp
  rw [hfunR] at hFr
  have hcast : HasDerivAt (fun y : ℝ => (f y : ℂ))
      ((deriv F (x : ℂ)).re : ℂ) x := hFr.ofReal_comp
  have hcomp : HasDerivAt (fun y : ℝ => F (y : ℂ)) (deriv F (x : ℂ)) x :=
    hFc.comp_ofReal
  have hfunC : (fun y : ℝ => (f y : ℂ)) = fun y : ℝ => F (y : ℂ) := by
    funext y
    exact (hrestrict y).symm
  rw [hfunC] at hcast
  have him : ((deriv F (x : ℂ)).re : ℂ) = deriv F (x : ℂ) := hcast.unique hcomp
  rw [hFr.deriv]
  exact him.symm

theorem XiC_deriv_ofReal (x : ℝ) :
    deriv XiC (x : ℂ) = ((deriv Xi x : ℝ) : ℂ) :=
  complex_deriv_eq_of_real_restriction XiC Xi
    (analyticOnNhd_univ_iff_differentiable.mp XiC_analytic) XiC_ofReal x

theorem XiC_secondDeriv_ofReal (x : ℝ) :
    deriv (deriv XiC) (x : ℂ) = ((deriv (deriv Xi) x : ℝ) : ℂ) := by
  apply complex_deriv_eq_of_real_restriction (deriv XiC) (deriv Xi)
  · intro z
    exact (((XiC_analytic z (Set.mem_univ z)).deriv).differentiableAt)
  · exact XiC_deriv_ofReal

theorem XiC_deriv_eq_constant_mul_canonicalProduct (z : ℂ) :
    deriv XiC z = XiC 0 * deriv xiCanonicalProduct z := by
  have h := (hasDerivAt_const (x := z) (c := XiC 0)).mul
    ((xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt.hasDerivAt)
  calc
    deriv XiC z = deriv ((fun _ => XiC 0) * xiCanonicalProduct) z := by
      exact congrArg (fun f : ℂ → ℂ => deriv f z) XiC_eq_constant_mul_canonicalProduct
    _ = XiC 0 * deriv xiCanonicalProduct z := by
      simpa only [Pi.mul_apply, zero_mul, zero_add] using h.deriv

theorem XiC_secondDeriv_eq_constant_mul_canonicalProduct (z : ℂ) :
    deriv (deriv XiC) z = XiC 0 * deriv (deriv xiCanonicalProduct) z := by
  have hfun : deriv XiC = fun w => XiC 0 * deriv xiCanonicalProduct w := by
    funext w
    exact XiC_deriv_eq_constant_mul_canonicalProduct w
  rw [hfun]
  have hP : HasDerivAt (deriv xiCanonicalProduct)
      (deriv (deriv xiCanonicalProduct) z) z := by
    exact ((((xiCanonicalProduct_analytic z (Set.mem_univ z)).deriv).differentiableAt).hasDerivAt)
  exact (hP.const_mul (XiC 0)).deriv

theorem Xi_eq_center_mul_canonicalProduct_re (x : ℝ) :
    Xi x = Xi 0 * (xiCanonicalProduct (x : ℂ)).re := by
  have hXi0 : XiC 0 = (Xi 0 : ℂ) := by simpa using XiC_ofReal 0
  have h := congrFun XiC_eq_constant_mul_canonicalProduct (x : ℂ)
  have hre := congrArg Complex.re h
  simp only [Pi.mul_apply] at hre
  rw [XiC_ofReal x, hXi0] at hre
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

theorem Xi_deriv_eq_center_mul_canonicalProduct_re (x : ℝ) :
    deriv Xi x = Xi 0 * (deriv xiCanonicalProduct (x : ℂ)).re := by
  have hXi0 : XiC 0 = (Xi 0 : ℂ) := by simpa using XiC_ofReal 0
  have h := XiC_deriv_eq_constant_mul_canonicalProduct (x : ℂ)
  rw [XiC_deriv_ofReal, hXi0] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

theorem Xi_secondDeriv_eq_center_mul_canonicalProduct_re (x : ℝ) :
    deriv (deriv Xi) x =
      Xi 0 * (deriv (deriv xiCanonicalProduct) (x : ℂ)).re := by
  have hXi0 : XiC 0 = (Xi 0 : ℂ) := by simpa using XiC_ofReal 0
  have h := XiC_secondDeriv_eq_constant_mul_canonicalProduct (x : ℂ)
  rw [XiC_secondDeriv_ofReal, hXi0] at h
  have hre := congrArg Complex.re h
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hre

/-- Under RH, the first Laguerre inequality for Xi follows from reflection-closed real-split
finite products converging locally uniformly with their first two derivatives. -/
theorem xi_laguerre_inequality_of_rh (hRH : RiemannHypothesis) (x : ℝ) :
    Xi x * deriv (deriv Xi) x ≤ (deriv Xi x) ^ (2 : ℕ) := by
  have hP := xiCanonicalProduct_laguerre_re_of_rh hRH x
  have hscaled := mul_le_mul_of_nonneg_left hP (sq_nonneg (Xi 0))
  rw [Xi_eq_center_mul_canonicalProduct_re,
    Xi_deriv_eq_center_mul_canonicalProduct_re,
    Xi_secondDeriv_eq_center_mul_canonicalProduct_re]
  nlinarith

theorem xiDivisorSupport_countable : Countable XiDivisorSupport := by
  rw [Set.countable_coe_iff]
  have hL : IsLindelof (MeromorphicOn.divisor xi Set.univ).support :=
    isLindelof_univ.of_isClosed_subset
      ((MeromorphicOn.divisor xi Set.univ).closedSupport isClosed_univ)
      (Set.subset_univ _)
  exact hL.countable_of_isDiscrete
    (MeromorphicOn.divisor xi Set.univ).discreteSupport

noncomputable def xiSupportFiniteExhaustion :
    Set.FiniteExhaustion (Set.univ : Set XiDivisorSupport) := by
  letI : Countable XiDivisorSupport := xiDivisorSupport_countable
  exact (Set.to_countable Set.univ).finiteExhaustion

noncomputable def xiSupportExhaustionFinset (n : ℕ) : Finset XiDivisorSupport :=
  (xiSupportFiniteExhaustion n).toFinite.toFinset

lemma xiSupportExhaustionFinset_mono : Monotone xiSupportExhaustionFinset := by
  intro m n hmn ρ hρ
  have hmem : ρ ∈ xiSupportFiniteExhaustion m := by
    simpa [xiSupportExhaustionFinset] using hρ
  have := xiSupportFiniteExhaustion.mono hmn hmem
  simpa [xiSupportExhaustionFinset] using this

lemma xiSupportExhaustionFinset_covers (ρ : XiDivisorSupport) :
    ∃ n, ρ ∈ xiSupportExhaustionFinset n := by
  have hρ : ρ ∈ (Set.univ : Set XiDivisorSupport) := Set.mem_univ ρ
  rw [← xiSupportFiniteExhaustion.iUnion_eq] at hρ
  simp only [Set.mem_iUnion] at hρ
  obtain ⟨n, hn⟩ := hρ
  exact ⟨n, by simpa [xiSupportExhaustionFinset] using hn⟩

theorem xiSupportExhaustionFinset_tendsto_atTop :
    Tendsto xiSupportExhaustionFinset atTop atTop :=
  xiSupportExhaustionFinset_mono.tendsto_atTop_finset
    xiSupportExhaustionFinset_covers

noncomputable def xiLaguerrePolynomial (n : ℕ) : Polynomial ℝ :=
  C (Xi 0) * xiPairedPolynomial (xiSupportExhaustionFinset n)

lemma xiLaguerrePolynomial_splits (n : ℕ) : (xiLaguerrePolynomial n).Splits :=
  (Splits.C _).mul (xiPairedPolynomial_splits _)

lemma xiLaguerrePolynomial_eval_tendsto (hRH : RiemannHypothesis) (x : ℝ) :
    Tendsto (fun n => (xiLaguerrePolynomial n).eval x) atTop (𝓝 (Xi x)) := by
  have hbase := (xiPairedPolynomial_eval_tendsto hRH x).comp
    xiSupportExhaustionFinset_tendsto_atTop
  have hc : Tendsto (fun _ : ℕ => Xi 0) atTop (𝓝 (Xi 0)) := tendsto_const_nhds
  have hmul := hc.mul hbase
  rw [Xi_eq_center_mul_canonicalProduct_re]
  simpa [xiLaguerrePolynomial, Function.comp_def] using hmul

lemma xiLaguerrePolynomial_derivative_eval_tendsto (hRH : RiemannHypothesis) (x : ℝ) :
    Tendsto (fun n => (derivative (xiLaguerrePolynomial n)).eval x)
      atTop (𝓝 (deriv Xi x)) := by
  have hbase := (xiPairedPolynomial_derivative_eval_tendsto hRH x).comp
    xiSupportExhaustionFinset_tendsto_atTop
  have hc : Tendsto (fun _ : ℕ => Xi 0) atTop (𝓝 (Xi 0)) := tendsto_const_nhds
  have hmul := hc.mul hbase
  rw [Xi_deriv_eq_center_mul_canonicalProduct_re]
  simpa [xiLaguerrePolynomial, derivative_mul, Function.comp_def] using hmul

lemma xiLaguerrePolynomial_secondDerivative_eval_tendsto
    (hRH : RiemannHypothesis) (x : ℝ) :
    Tendsto (fun n => (derivative (derivative (xiLaguerrePolynomial n))).eval x)
      atTop (𝓝 (deriv (deriv Xi) x)) := by
  have hbase := (xiPairedPolynomial_secondDerivative_eval_tendsto hRH x).comp
    xiSupportExhaustionFinset_tendsto_atTop
  have hc : Tendsto (fun _ : ℕ => Xi 0) atTop (𝓝 (Xi 0)) := tendsto_const_nhds
  have hmul := hc.mul hbase
  rw [Xi_secondDeriv_eq_center_mul_canonicalProduct_re]
  simpa [xiLaguerrePolynomial, derivative_mul, Function.comp_def] using hmul

/-- The former Pólya interface is discharged: RH itself supplies an explicit sequence of
reflection-closed real-split divisor polynomials converging with two derivatives to Xi. -/
theorem xi_laguerrePolya_of_rh : RiemannHypothesis → LaguerrePolya Xi := by
  intro hRH
  exact ⟨xiLaguerrePolynomial, xiLaguerrePolynomial_splits,
    xiLaguerrePolynomial_eval_tendsto hRH,
    xiLaguerrePolynomial_derivative_eval_tendsto hRH,
    xiLaguerrePolynomial_secondDerivative_eval_tendsto hRH⟩

theorem laguerre_margin_neg_not_RH
    (h : ∃ t : ℝ, (deriv Xi t) ^ (2 : ℕ) < Xi t * deriv (deriv Xi) t) :
    ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨t, ht⟩ := h
  exact (not_lt_of_ge (xi_laguerre_inequality_of_rh hRH t)) ht

end

end RHTower
