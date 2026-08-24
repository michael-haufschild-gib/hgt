import GaloisForLFunctions.RHTower.PrimeIndexedRVMSignedSkeleton
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantEntire
import GaloisForLFunctions.HTGeometry.CanonicalProduct
import GaloisForLFunctions.HTGeometry.FredholmDeterminantZeta

open scoped BigOperators InnerProductSpace Nat.Prime
open Filter

namespace RHTower

noncomputable section

def routeKRVMCanonicalZero (n : ℕ) : ℂ :=
  (routeKRVMQuantile n : ℂ)

theorem routeKRVMCanonicalZero_ne_zero (n : ℕ) :
    routeKRVMCanonicalZero n ≠ 0 := by
  rw [routeKRVMCanonicalZero]
  exact_mod_cast
    (routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n)).ne'

theorem summable_routeKRVMCanonicalZero_inv_norm_sq :
    Summable (fun n : ℕ => 1 / ‖routeKRVMCanonicalZero n‖ ^ 2) := by
  exact summable_routeKRVMQuantile_reciprocal_sq.congr fun n => by
    rw [routeKRVMCanonicalZero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (routeKRVMBase_pos.trans (routeKRVMBase_lt_quantile n))]
    field_simp [(routeKRVMBase_pos.trans
      (routeKRVMBase_lt_quantile n)).ne']

def routeKRVMSmoothPositiveCanonicalProduct (z : ℂ) : ℂ :=
  canonicalProductE1 routeKRVMCanonicalZero z

theorem routeKRVMSmoothPositiveCanonicalProduct_analytic :
    AnalyticOnNhd ℂ routeKRVMSmoothPositiveCanonicalProduct Set.univ := by
  exact canonicalProductE1_analytic routeKRVMCanonicalZero
    routeKRVMCanonicalZero_ne_zero
    summable_routeKRVMCanonicalZero_inv_norm_sq

def routeKRVMSmoothCanonicalProduct (z : ℂ) : ℂ :=
  routeKRVMSmoothPositiveCanonicalProduct z *
    routeKRVMSmoothPositiveCanonicalProduct (-z)

theorem routeKRVMSmoothCanonicalProduct_analytic :
    AnalyticOnNhd ℂ routeKRVMSmoothCanonicalProduct Set.univ := by
  have hpos := routeKRVMSmoothPositiveCanonicalProduct_analytic
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -z) Set.univ := by
    intro z hz
    fun_prop
  exact hpos.mul (hpos.comp hneg (by simp))

theorem routeKRVMSmoothCanonicalProduct_differentiable :
    Differentiable ℂ routeKRVMSmoothCanonicalProduct := by
  rw [← differentiableOn_univ]
  exact routeKRVMSmoothCanonicalProduct_analytic.differentiableOn

theorem routeKRVMSmoothCanonicalProduct_eq_tprod (z : ℂ) :
    routeKRVMSmoothCanonicalProduct z =
      ∏' n : ℕ, (1 - z ^ 2 / (routeKRVMQuantile n : ℂ) ^ 2) := by
  have hmulPos : Multipliable (fun n =>
      weierstrassE1 (z / routeKRVMCanonicalZero n)) :=
    (canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      routeKRVMCanonicalZero routeKRVMCanonicalZero_ne_zero
      summable_routeKRVMCanonicalZero_inv_norm_sq
      |>.multipliableLocallyUniformlyOn).multipliable (Set.mem_univ z)
  have hmulNeg : Multipliable (fun n =>
      weierstrassE1 ((-z) / routeKRVMCanonicalZero n)) :=
    (canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      routeKRVMCanonicalZero routeKRVMCanonicalZero_ne_zero
      summable_routeKRVMCanonicalZero_inv_norm_sq
      |>.multipliableLocallyUniformlyOn).multipliable (Set.mem_univ (-z))
  change
    (∏' n, weierstrassE1 (z / routeKRVMCanonicalZero n)) *
      (∏' n, weierstrassE1 ((-z) / routeKRVMCanonicalZero n)) = _
  rw [← hmulPos.tprod_mul hmulNeg]
  apply tprod_congr
  intro n
  have ha : (routeKRVMQuantile n : ℂ) ≠ 0 :=
    routeKRVMCanonicalZero_ne_zero n
  rw [weierstrassE1, weierstrassE1]
  let x : ℂ := z / (routeKRVMQuantile n : ℂ)
  calc
    (1 - z / routeKRVMCanonicalZero n) *
          Complex.exp (z / routeKRVMCanonicalZero n) *
        ((1 - -z / routeKRVMCanonicalZero n) *
          Complex.exp (-z / routeKRVMCanonicalZero n)) =
        (1 - x) * (1 + x) *
          (Complex.exp x * Complex.exp (-x)) := by
      simp only [routeKRVMCanonicalZero, x]
      ring_nf
    _ = (1 - x) * (1 + x) := by
      rw [← Complex.exp_add]
      simp
    _ = 1 - z ^ 2 / (routeKRVMQuantile n : ℂ) ^ 2 := by
      simp only [x]
      field_simp [ha]
      ring_nf

def routeKSignedPrimeRVMKernel :
    RouteKSignedPrimeIndex × RouteKSignedPrimeIndex → ℂ :=
  HilbertSchmidt.diagMul routeKSignedPrimeRVMMultiplier

theorem summable_norm_routeKSignedPrimeRVMMultiplier_sq :
    Summable (fun i : RouteKSignedPrimeIndex =>
      ‖routeKSignedPrimeRVMMultiplier i‖ ^ 2) := by
  apply Summable.sum
  · simpa [Function.comp_def, routeKSignedPrimeRVMMultiplier,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (routeKPrimeRVMReciprocal_pos _)] using
      summable_routeKPrimeRVMReciprocal_sq
  · simpa [Function.comp_def, routeKSignedPrimeRVMMultiplier,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (routeKPrimeRVMReciprocal_pos _)] using
      summable_routeKPrimeRVMReciprocal_sq

theorem fredholmDet_routeKSignedPrimeRVMKernel_eq_canonicalProduct
    (r : ℝ) (hr : r * HilbertSchmidt.hsNorm routeKSignedPrimeRVMKernel < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    HilbertSchmidt.fredholmDet routeKSignedPrimeRVMKernel z =
      routeKRVMSmoothCanonicalProduct z := by
  rw [routeKSignedPrimeRVMKernel,
    HilbertSchmidt.fredholmDet_tprod_diagMul
      routeKSignedPrimeRVMMultiplier
      summable_norm_routeKSignedPrimeRVMMultiplier_sq r hr z hz]
  let f : RouteKSignedPrimeIndex → ℂ := fun i =>
    (1 - z * routeKSignedPrimeRVMMultiplier i) *
      Complex.exp (z * routeKSignedPrimeRVMMultiplier i)
  have hnatPos : HasProd
      (fun n : ℕ => weierstrassE1 (z / routeKRVMCanonicalZero n))
      (routeKRVMSmoothPositiveCanonicalProduct z) :=
    (canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      routeKRVMCanonicalZero routeKRVMCanonicalZero_ne_zero
      summable_routeKRVMCanonicalZero_inv_norm_sq).hasProd (Set.mem_univ z)
  have hnatNeg : HasProd
      (fun n : ℕ => weierstrassE1 ((-z) / routeKRVMCanonicalZero n))
      (routeKRVMSmoothPositiveCanonicalProduct (-z)) :=
    (canonicalProductE1Indexed_hasProdLocallyUniformlyOn
      routeKRVMCanonicalZero routeKRVMCanonicalZero_ne_zero
      summable_routeKRVMCanonicalZero_inv_norm_sq).hasProd (Set.mem_univ (-z))
  have hprimePos : HasProd (f ∘ Sum.inl)
      (routeKRVMSmoothPositiveCanonicalProduct z) := by
    apply nthPrimeEquiv.hasProd_iff.mp
    have hfac :
        (fun n : ℕ => weierstrassE1 (z / routeKRVMCanonicalZero n)) =
          (f ∘ Sum.inl) ∘ nthPrimeEquiv := by
      funext n
      simp only [Function.comp_apply, f, routeKSignedPrimeRVMMultiplier,
        routeKRVMCanonicalZero, routeKPrimeRVMReciprocal]
      rw [show routeKPrimeRVMIndex (nthPrimeEquiv n) = n by
        simpa [nthPrimeEquiv] using routeKPrimeRVMIndex_nthPrimeSubtype n,
        weierstrassE1]
      congr 2 <;> push_cast
      all_goals
        have ht : (routeKRVMQuantile n : ℂ) ≠ 0 := by
          exact_mod_cast (routeKRVMBase_pos.trans
            (routeKRVMBase_lt_quantile n)).ne'
        field_simp [ht]
    rw [← hfac]
    exact hnatPos
  have hprimeNeg : HasProd (f ∘ Sum.inr)
      (routeKRVMSmoothPositiveCanonicalProduct (-z)) := by
    apply nthPrimeEquiv.hasProd_iff.mp
    have hfac :
        (fun n : ℕ => weierstrassE1 ((-z) / routeKRVMCanonicalZero n)) =
          (f ∘ Sum.inr) ∘ nthPrimeEquiv := by
      funext n
      simp only [Function.comp_apply, f, routeKSignedPrimeRVMMultiplier,
        routeKRVMCanonicalZero, routeKPrimeRVMReciprocal]
      rw [show routeKPrimeRVMIndex (nthPrimeEquiv n) = n by
        simpa [nthPrimeEquiv] using routeKPrimeRVMIndex_nthPrimeSubtype n,
        weierstrassE1]
      congr 2 <;> push_cast
      all_goals
        have ht : (routeKRVMQuantile n : ℂ) ≠ 0 := by
          exact_mod_cast (routeKRVMBase_pos.trans
            (routeKRVMBase_lt_quantile n)).ne'
        field_simp [ht]
    rw [← hfac]
    exact hnatNeg
  change (∏' i, f i) = routeKRVMSmoothCanonicalProduct z
  exact (hprimePos.sum hprimeNeg).tprod_eq

theorem routeKSignedPrimeRVMKernel_isRegularizedDet :
    GaloisForLFunctions.HTGeometry.IsRegularizedDet
      routeKSignedPrimeRVMKernel routeKRVMSmoothCanonicalProduct := by
  refine ⟨routeKRVMSmoothCanonicalProduct_differentiable, ?_⟩
  let r : ℝ := (HilbertSchmidt.hsNorm routeKSignedPrimeRVMKernel + 1)⁻¹
  have hden : 0 < HilbertSchmidt.hsNorm routeKSignedPrimeRVMKernel + 1 := by
    linarith [HilbertSchmidt.hsNorm_nonneg routeKSignedPrimeRVMKernel]
  have hr : 0 < r := inv_pos.mpr hden
  have hrK : r * HilbertSchmidt.hsNorm routeKSignedPrimeRVMKernel < 1 := by
    dsimp [r]
    rw [inv_mul_eq_div, div_lt_one hden]
    linarith
  exact ⟨r, hr, hrK, fun z hz =>
    (fredholmDet_routeKSignedPrimeRVMKernel_eq_canonicalProduct r hrK z hz).symm⟩

end

end RHTower
