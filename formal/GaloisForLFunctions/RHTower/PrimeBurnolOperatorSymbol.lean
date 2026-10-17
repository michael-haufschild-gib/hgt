import GaloisForLFunctions.RHTower.PrimeBurnolFeatureTotality

/-! Prime eigenlines force a bounded holomorphic symbol on every complex Burnol feature. -/

noncomputable section
open Complex Set
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

private def burnolSymbolAnchor : BurnolHalfLineL2 := burnolComplexFeature 1 (by norm_num)

private theorem burnolSymbolAnchor_coordinate {z : ℂ} (hz : 0 < z.re) :
    burnolComplexCoordinate burnolSymbolAnchor z = 2 / (z + 1)^3 := by
  rw [burnolComplexCoordinate_eq_inner _ hz, burnolSymbolAnchor, inner_burnolComplexFeature]
  simp

private theorem burnolSymbolAnchor_coordinate_ne_zero {z : ℂ} (hz : 0 < z.re) :
    burnolComplexCoordinate burnolSymbolAnchor z ≠ 0 := by
  rw [burnolSymbolAnchor_coordinate hz]
  apply div_ne_zero (by norm_num)
  apply pow_ne_zero
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
  linarith

/-- Canonical holomorphic scalar readout of a bounded Burnol operator. -/
def burnolOperatorSymbol (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (z : ℂ) : ℂ :=
  burnolComplexCoordinate (ContinuousLinearMap.adjoint T burnolSymbolAnchor) z /
    burnolComplexCoordinate burnolSymbolAnchor z

theorem burnolOperatorSymbol_analytic (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
    AnalyticOnNhd ℂ (burnolOperatorSymbol T) PrimeBlindCarlson.rightHalf := by
  intro z hz
  exact (burnolComplexCoordinate_analytic _ z hz).div
    (burnolComplexCoordinate_analytic _ z hz) (burnolSymbolAnchor_coordinate_ne_zero hz)

/-- Physical and raw prime features impose exactly the same eigenvalue equations. -/
theorem primeBurnol_eigenvalue_iff (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2)
    (p : Nat.Primes) (a : ℂ) :
    T (primeLogCriticalLaplaceFeatureL2 p) = a • primeLogCriticalLaplaceFeatureL2 p ↔
      T (primeBurnolRawFeature p) = a • primeBurnolRawFeature p := by
  have hc : (primeBurnolFeatureScale p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (primeBurnolFeatureScale_pos p).ne'
  rw [primeLogCriticalLaplaceFeatureL2_eq_burnol, map_smul,
    smul_comm a (primeBurnolFeatureScale p : ℂ), smul_right_inj hc]

private theorem burnolOperator_pairingDet_zero
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeBurnolRawFeature p) = a p • primeBurnolRawFeature p)
    (f : BurnolHalfLineL2) :
    EqOn (fun z =>
      burnolComplexCoordinate (ContinuousLinearMap.adjoint T f) z *
        burnolComplexCoordinate burnolSymbolAnchor z -
      burnolComplexCoordinate (ContinuousLinearMap.adjoint T burnolSymbolAnchor) z *
        burnolComplexCoordinate f z) 0 PrimeBlindCarlson.rightHalf := by
  apply PrimeBlindCarlson.eqOn_zero_of_primeLog_zeros
  · intro z hz
    exact ((burnolComplexCoordinate_analytic _ z hz).mul
      (burnolComplexCoordinate_analytic _ z hz)).sub
      ((burnolComplexCoordinate_analytic _ z hz).mul
        (burnolComplexCoordinate_analytic _ z hz))
  · intro δ hδ
    obtain ⟨A,hA⟩ := burnolComplexCoordinate_bounded (ContinuousLinearMap.adjoint T f) hδ
    obtain ⟨B,hB⟩ := burnolComplexCoordinate_bounded burnolSymbolAnchor hδ
    obtain ⟨C,hC⟩ := burnolComplexCoordinate_bounded (ContinuousLinearMap.adjoint T burnolSymbolAnchor) hδ
    obtain ⟨D,hD⟩ := burnolComplexCoordinate_bounded f hδ
    refine ⟨|A| * |B| + |C| * |D|, fun z hz => ?_⟩
    calc ‖burnolComplexCoordinate (ContinuousLinearMap.adjoint T f) z *
          burnolComplexCoordinate burnolSymbolAnchor z -
        burnolComplexCoordinate (ContinuousLinearMap.adjoint T burnolSymbolAnchor) z *
          burnolComplexCoordinate f z‖ ≤
        ‖burnolComplexCoordinate (ContinuousLinearMap.adjoint T f) z‖ *
          ‖burnolComplexCoordinate burnolSymbolAnchor z‖ +
        ‖burnolComplexCoordinate (ContinuousLinearMap.adjoint T burnolSymbolAnchor) z‖ *
          ‖burnolComplexCoordinate f z‖ := by
            rw [← norm_mul, ← norm_mul]
            exact norm_sub_le _ _
      _ ≤ |A| * |B| + |C| * |D| := add_le_add
        (mul_le_mul ((hA z hz).trans (le_abs_self _)) ((hB z hz).trans (le_abs_self _))
          (norm_nonneg _) (abs_nonneg _))
        (mul_le_mul ((hC z hz).trans (le_abs_self _)) ((hD z hz).trans (le_abs_self _))
          (norm_nonneg _) (abs_nonneg _))
  · intro p hp
    have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    simp only [burnolComplexCoordinate_eq_inner (z := (Real.log (p : ℝ) : ℂ)) _ hl,
      ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ f (T (primeBurnolRawFeature ⟨p,hp⟩)) *
      inner ℂ burnolSymbolAnchor (primeBurnolRawFeature ⟨p,hp⟩) -
      inner ℂ burnolSymbolAnchor (T (primeBurnolRawFeature ⟨p,hp⟩)) *
      inner ℂ f (primeBurnolRawFeature ⟨p,hp⟩) = 0
    rw [ha]
    simp only [inner_smul_right]
    ring

/-- Preserving every actual-prime line forces every complex Burnol line to be invariant. -/
theorem burnolOperatorSymbol_eigen
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    {z : ℂ} (hz : 0 < z.re) :
    T (burnolComplexFeature z hz) = burnolOperatorSymbol T z • burnolComplexFeature z hz := by
  have hraw : ∀ p, T (primeBurnolRawFeature p) = a p • primeBurnolRawFeature p :=
    fun p => (primeBurnol_eigenvalue_iff T p (a p)).mp (ha p)
  apply ext_inner_left ℂ
  intro f
  calc inner ℂ f (T (burnolComplexFeature z hz)) =
        burnolComplexCoordinate (ContinuousLinearMap.adjoint T f) z := by
          rw [burnolComplexCoordinate_eq_inner _ hz, ContinuousLinearMap.adjoint_inner_left]
    _ = burnolOperatorSymbol T z * burnolComplexCoordinate f z := by
      have h := burnolOperator_pairingDet_zero T a hraw f hz
      change burnolComplexCoordinate (ContinuousLinearMap.adjoint T f) z *
          burnolComplexCoordinate burnolSymbolAnchor z -
        burnolComplexCoordinate (ContinuousLinearMap.adjoint T burnolSymbolAnchor) z *
          burnolComplexCoordinate f z = 0 at h
      rw [burnolOperatorSymbol, div_mul_eq_mul_div, eq_div_iff (burnolSymbolAnchor_coordinate_ne_zero hz)]
      exact sub_eq_zero.mp h
    _ = inner ℂ f (burnolOperatorSymbol T z • burnolComplexFeature z hz) := by
      rw [inner_smul_right, burnolComplexCoordinate_eq_inner _ hz]

theorem burnolOperatorSymbol_bound
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    {z : ℂ} (hz : 0 < z.re) : ‖burnolOperatorSymbol T z‖ ≤ ‖T‖ := by
  have h := T.le_opNorm (burnolComplexFeature z hz)
  rw [burnolOperatorSymbol_eigen T a ha hz, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr (burnolComplexFeature_ne_zero hz))

theorem burnolOperatorSymbol_prime
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (p : Nat.Primes) : burnolOperatorSymbol T (Real.log (p : ℝ)) = a p := by
  have hl : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have h1 := burnolOperatorSymbol_eigen T a ha (z := (Real.log (p : ℝ))) hl
  have h2 := (primeBurnol_eigenvalue_iff T p (a p)).mp (ha p)
  exact smul_left_injective ℂ (burnolComplexFeature_ne_zero hl) (h1.symm.trans h2)

/-- Bounded holomorphic symbols are uniquely determined by their actual-prime samples. -/
theorem eqOn_bounded_holomorphic_of_primeLog {φ ψ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ PrimeBlindCarlson.rightHalf)
    (hψ : AnalyticOnNhd ℂ ψ PrimeBlindCarlson.rightHalf)
    {M N : ℝ} (hM : ∀ z ∈ PrimeBlindCarlson.rightHalf, ‖φ z‖ ≤ M)
    (hN : ∀ z ∈ PrimeBlindCarlson.rightHalf, ‖ψ z‖ ≤ N)
    (heq : ∀ p : Nat.Primes, φ (Real.log (p : ℝ)) = ψ (Real.log (p : ℝ))) :
    EqOn φ ψ PrimeBlindCarlson.rightHalf := by
  have hzero : EqOn (fun z => φ z - ψ z) 0 PrimeBlindCarlson.rightHalf := by
    apply PrimeBlindCarlson.eqOn_zero_of_primeLog_zeros
    · intro z hz
      exact (hφ z hz).sub (hψ z hz)
    · intro δ hδ
      refine ⟨M + N, fun z hz => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add (hM z (hδ.trans_le hz)) (hN z (hδ.trans_le hz)))
    · intro p hp
      exact sub_eq_zero.mpr (heq ⟨p,hp⟩)
  intro z hz
  exact sub_eq_zero.mp (hzero hz)

end RHTower
