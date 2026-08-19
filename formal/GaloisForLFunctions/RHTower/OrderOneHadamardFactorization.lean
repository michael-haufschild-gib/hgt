/-
# Hadamard factorization at order one

An entire function with the growth envelope `‖f z‖ ≤ exp (C (1+‖z‖) log (2+‖z‖))` is the product
of `exp` of an affine function with the genus-one canonical product over its own zero divisor, and
if it is even the exponential factor is a constant.

Every ingredient is already available: Jensen's inequality gives the order-one zero density, the
logarithmic bucket decomposition turns that into square-summability of the inverse zeros, the
genus-one product then converges and carries exactly the divisor of `f`, and order-one rigidity
makes the entire zero-free quotient the exponential of an affine function.
-/
import GaloisForLFunctions.HTGeometry.CanonicalProductE1Divisor
import GaloisForLFunctions.HTGeometry.OrderOneZeroDensity
import GaloisForLFunctions.HTGeometry.CanonicalProductGrowth
import GaloisForLFunctions.RHTower.OrderOneFixedDivisorRigidity

noncomputable section

open Complex Filter Topology Metric Set
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.CountableDivisor
open GaloisForLFunctions.EntireQuotient

namespace RHTower.OrderOneHadamard

variable {f : ℂ → ℂ}

/-- The genus-one canonical product over the exact zero divisor of an entire function. -/
def hadamardProduct (f : ℂ → ℂ) : ℂ → ℂ := canonicalProductE1Indexed (zeroCopyPoint f)

@[simp] theorem hadamardProduct_zero : hadamardProduct f 0 = 1 :=
  canonicalProductE1Indexed_zero

/-- The zero divisor of a function with an order-one envelope is square-summable. -/
theorem summable_inv_sq_zeroCopyPoint {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    Summable (fun q : ZeroCopy f => 1 / ‖zeroCopyPoint f q‖ ^ 2) :=
  summable_inv_norm_sq_idx (zeroCopyPoint_ne_zero hf hf0) (locallyFinite_zeroCopyPoint hf)
    (orderOneDensityIdx_zeroCopyPoint hC hf hf0 hbound)

theorem hadamardProduct_analytic (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hsum : Summable (fun q : ZeroCopy f => 1 / ‖zeroCopyPoint f q‖ ^ 2)) :
    AnalyticOnNhd ℂ (hadamardProduct f) Set.univ :=
  canonicalProductE1Indexed_analytic _ (zeroCopyPoint_ne_zero hf hf0) hsum

/-- **The canonical product carries the divisor.**  The genus-one product over the zero divisor of
`f` has the same analytic order as `f` at every point. -/
theorem analyticOrderAt_hadamardProduct_eq (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (hsum : Summable (fun q : ZeroCopy f => 1 / ‖zeroCopyPoint f q‖ ^ 2)) (w : ℂ) :
    analyticOrderAt (hadamardProduct f) w = analyticOrderAt f w := by
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hloc := locallyFinite_zeroCopyPoint hf
  have hPan := hadamardProduct_analytic hf hf0 hsum
  by_cases hw : w = 0
  · subst hw
    rw [(hPan 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr
        (by rw [hadamardProduct_zero]; exact one_ne_zero),
      (hf 0 (Set.mem_univ 0)).analyticOrderAt_eq_zero.mpr hf0]
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt f w = (n : ℕ∞) :=
      ⟨(analyticOrderAt f w).toNat, (ENat.coe_toNat (hford w)).symm⟩
    have hdiv : (MeromorphicOn.divisor f Set.univ) w = (n : ℤ) := by
      rw [divisor_univ_eq_analyticOrder hf, hn]
      rfl
    rw [hadamardProduct, analyticOrderAt_canonicalProductE1Indexed hane hloc hsum hw, hn]
    congr 1
    have hfib : {p : ZeroCopy f | zeroCopyPoint f p = w}.ncard
        = ((MeromorphicOn.divisor f Set.univ) w).toNat := ncard_zeroCopy_fiber w
    rw [hfib, hdiv]
    simp

/-- **Hadamard factorization at order one.**  An entire function with an order-one growth envelope
and no zero at the origin is `exp` of an affine function times the genus-one canonical product over
its own zero divisor. -/
theorem exists_expAffine_mul_hadamardProduct {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b) * hadamardProduct f z := by
  have hsum := summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hPan := hadamardProduct_analytic hf hf0 hsum
  have horder := analyticOrderAt_hadamardProduct_eq hf hf0 hford hsum
  obtain ⟨h, hhdiff, hhne, hfac⟩ :=
    exists_entire_nonvanishing_quotient hf hPan hford (fun z => (horder z).symm)
      (z₀ := 0) (by rw [hadamardProduct_zero]; exact one_ne_zero)
  have hPdiff : Differentiable ℂ (hadamardProduct f) :=
    fun z => (hPan z (Set.mem_univ z)).differentiableAt
  have hfdiff : Differentiable ℂ f := fun z => (hf z (Set.mem_univ z)).differentiableAt
  have hPord : ∀ z, meromorphicOrderAt (hadamardProduct f) z ≠ ⊤ := by
    intro z
    rw [(hPan z (Set.mem_univ z)).meromorphicOrderAt_eq, horder z]
    simp [hford z]
  have hFord : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z (Set.mem_univ z)).meromorphicOrderAt_eq]
    simp [hford z]
  have hproxP := canonicalProductE1Indexed_proximity_isLittleO_sq _ hane hsum
  have hproxf := RHTower.OrderOneRigidity.proximity_isLittleO_sq_of_growth hC hfdiff hbound
  obtain ⟨a, b, hab⟩ := RHTower.OrderOneRigidity.exists_expAffine_of_entire_quotient
    hPdiff hfdiff hhdiff hPord hFord hhne hfac hproxP hproxf
  exact ⟨a, b, fun z => by rw [hfac z, hab z]⟩

/-! ## Reflection symmetry -/

/-- The divisor of an even entire function is symmetric. -/
theorem divisor_neg_of_even (hf : AnalyticOnNhd ℂ f Set.univ) (heven : ∀ z, f (-z) = f z) (w : ℂ) :
    (MeromorphicOn.divisor f Set.univ) (-w) = (MeromorphicOn.divisor f Set.univ) w := by
  have hg_an : AnalyticAt ℂ (fun z : ℂ => -z) w := by fun_prop
  have hg_deriv : deriv (fun z : ℂ => -z) w ≠ 0 := by
    have hg' : HasDerivAt (fun z : ℂ => -z) (-1) w := (hasDerivAt_id w).neg
    rw [hg'.deriv]
    exact neg_ne_zero.mpr one_ne_zero
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := f) hg_an hg_deriv
  have hfun : f ∘ (fun z : ℂ => -z) = f := funext heven
  rw [hfun] at hcomp
  rw [divisor_univ_eq_analyticOrder hf, divisor_univ_eq_analyticOrder hf, hcomp]

/-- Reflection as an involution of the zero-divisor support of an even entire function. -/
def zeroSupportReflect (hf : AnalyticOnNhd ℂ f Set.univ) (heven : ∀ z, f (-z) = f z) :
    ZeroSupport f ≃ ZeroSupport f where
  toFun w := ⟨-(w : ℂ), by
    apply Function.mem_support.mpr
    rw [divisor_neg_of_even hf heven]
    exact Function.mem_support.mp w.2⟩
  invFun w := ⟨-(w : ℂ), by
    apply Function.mem_support.mpr
    rw [divisor_neg_of_even hf heven]
    exact Function.mem_support.mp w.2⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

@[simp]
theorem zeroSupportReflect_apply (hf : AnalyticOnNhd ℂ f Set.univ) (heven : ∀ z, f (-z) = f z)
    (w : ZeroSupport f) : ((zeroSupportReflect hf heven w : ZeroSupport f) : ℂ) = -(w : ℂ) := rfl

/-- Reflection lifted to the multiplicity-copy index. -/
def zeroCopyReflect (hf : AnalyticOnNhd ℂ f Set.univ) (heven : ∀ z, f (-z) = f z) :
    ZeroCopy f ≃ ZeroCopy f :=
  Equiv.sigmaCongr (zeroSupportReflect hf heven) (fun w => Equiv.cast (by
    change Fin ((MeromorphicOn.divisor f Set.univ) ((w : ZeroSupport f) : ℂ)).toNat =
      Fin ((MeromorphicOn.divisor f Set.univ) (-((w : ZeroSupport f) : ℂ))).toNat
    rw [divisor_neg_of_even hf heven]))

theorem zeroCopyPoint_reflect (hf : AnalyticOnNhd ℂ f Set.univ) (heven : ∀ z, f (-z) = f z)
    (q : ZeroCopy f) :
    zeroCopyPoint f (zeroCopyReflect hf heven q) = -zeroCopyPoint f q := rfl

/-- **The canonical product of an even function is even.** -/
theorem hadamardProduct_even (hf : AnalyticOnNhd ℂ f Set.univ) (heven : ∀ z, f (-z) = f z)
    (z : ℂ) : hadamardProduct f (-z) = hadamardProduct f z := by
  change (∏' q : ZeroCopy f, weierstrassE1 (-z / zeroCopyPoint f q)) =
    ∏' q : ZeroCopy f, weierstrassE1 (z / zeroCopyPoint f q)
  calc
    (∏' q : ZeroCopy f, weierstrassE1 (-z / zeroCopyPoint f q)) =
        ∏' q : ZeroCopy f,
          weierstrassE1 (-z / zeroCopyPoint f (zeroCopyReflect hf heven q)) :=
      ((zeroCopyReflect hf heven).tprod_eq
        (fun q => weierstrassE1 (-z / zeroCopyPoint f q))).symm
    _ = ∏' q : ZeroCopy f, weierstrassE1 (z / zeroCopyPoint f q) := by
      refine tprod_congr (fun q => ?_)
      rw [zeroCopyPoint_reflect hf heven]
      congr 1
      field_simp

/-- **Hadamard factorization for an even function at order one.**  The exponential factor is a
constant, fixed by the value at the origin. -/
theorem eq_const_mul_hadamardProduct_of_even {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∀ z, f z = f 0 * hadamardProduct f z := by
  have hsum := summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hPan := hadamardProduct_analytic hf hf0 hsum
  have horder := analyticOrderAt_hadamardProduct_eq hf hf0 hford hsum
  obtain ⟨h, hhdiff, hhne, hfac⟩ :=
    exists_entire_nonvanishing_quotient hf hPan hford (fun z => (horder z).symm)
      (z₀ := 0) (by rw [hadamardProduct_zero]; exact one_ne_zero)
  have hPdiff : Differentiable ℂ (hadamardProduct f) :=
    fun z => (hPan z (Set.mem_univ z)).differentiableAt
  have hfdiff : Differentiable ℂ f := fun z => (hf z (Set.mem_univ z)).differentiableAt
  have hPord : ∀ z, meromorphicOrderAt (hadamardProduct f) z ≠ ⊤ := by
    intro z
    rw [(hPan z (Set.mem_univ z)).meromorphicOrderAt_eq, horder z]
    simp [hford z]
  have hFord : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
    intro z
    rw [(hf z (Set.mem_univ z)).meromorphicOrderAt_eq]
    simp [hford z]
  have hproxP := canonicalProductE1Indexed_proximity_isLittleO_sq _ hane hsum
  have hproxf := RHTower.OrderOneRigidity.proximity_isLittleO_sq_of_growth hC hfdiff hbound
  -- the quotient is even
  have hP0 : hadamardProduct f 0 ≠ 0 := by rw [hadamardProduct_zero]; exact one_ne_zero
  have hPne : ∀ᶠ w in 𝓝 (0 : ℂ), hadamardProduct f w ≠ 0 :=
    (hPan 0 (Set.mem_univ _)).continuousAt.eventually_ne hP0
  have hlocal : (fun w => h (-w)) =ᶠ[𝓝 0] h := by
    filter_upwards [hPne] with w hp
    have hneg := hfac (-w)
    have hpos := hfac w
    rw [hadamardProduct_even hf heven, heven w] at hneg
    exact mul_right_cancel₀ hp (hneg.symm.trans hpos)
  have hhan : AnalyticOnNhd ℂ h Set.univ := fun z _ => Differentiable.analyticAt hhdiff z
  have hneg_an : AnalyticOnNhd ℂ (fun w => h (-w)) Set.univ := by
    intro w _
    exact (hhan (-w) (Set.mem_univ _)).comp (by fun_prop : AnalyticAt ℂ (fun u : ℂ => -u) w)
  have hheven : ∀ z, h (-z) = h z :=
    congrFun (hneg_an.eq_of_eventuallyEq hhan hlocal)
  have hconst := RHTower.OrderOneRigidity.exists_const_of_even_entire_quotient
    hPdiff hfdiff hhdiff hPord hFord hhne hfac hheven hproxP hproxf
  have hh0 : h 0 = f 0 := by
    have := hfac 0
    rw [hadamardProduct_zero, mul_one] at this
    exact this.symm
  intro z
  rw [hfac z, hconst z, hh0]

end RHTower.OrderOneHadamard
