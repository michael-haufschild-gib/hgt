import GaloisForLFunctions.RHTower.PrimeBurnolPickCone

/-! Exact bounded-holomorphic classification, norm, and product law for actual-prime Burnol operators. -/

noncomputable section
open Complex Set
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

/-- The holomorphic symbol and the physical operator have the same optimal bound. -/
theorem primeBurnol_operator_norm_le_iff
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    {M : ℝ} (hM : 0 ≤ M) :
    ‖T‖ ≤ M ↔ ∀ z ∈ PrimeBlindCarlson.rightHalf, ‖burnolOperatorSymbol T z‖ ≤ M := by
  constructor
  · intro h z hz
    exact (burnolOperatorSymbol_bound T a ha hz).trans h
  · intro hb
    obtain ⟨U,hU,he⟩ := (primeBurnol_bounded_operator_iff_holomorphic a hM).mpr
      ⟨burnolOperatorSymbol T, burnolOperatorSymbol_analytic T, hb,
        burnolOperatorSymbol_prime T a ha⟩
    have hUT : U = T := primeBurnol_operator_ext (fun p => (he p).trans (ha p).symm)
    rwa [hUT] at hU

/-- Exact operator norm as the supremum of the holomorphic symbol on the full half-plane. -/
theorem primeBurnol_operator_norm_eq_sup
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p) :
    ‖T‖ = sSup (Set.range (fun z : {z : ℂ // 0 < z.re} => ‖burnolOperatorSymbol T z‖)) := by
  let S := Set.range (fun z : {z : ℂ // 0 < z.re} => ‖burnolOperatorSymbol T z‖)
  have hne : S.Nonempty := ⟨‖burnolOperatorSymbol T 1‖, ⟨⟨1,by norm_num⟩,rfl⟩⟩
  have hb : BddAbove S := ⟨‖T‖, by
    rintro _ ⟨z,rfl⟩
    exact burnolOperatorSymbol_bound T a ha z.property⟩
  have h0 : 0 ≤ sSup S := (norm_nonneg (burnolOperatorSymbol T 1)).trans
    (le_csSup hb ⟨⟨1,by norm_num⟩,rfl⟩)
  apply le_antisymm
  · exact (primeBurnol_operator_norm_le_iff T a ha h0).mpr
      (fun z hz => le_csSup hb ⟨⟨z,hz⟩,rfl⟩)
  · exact csSup_le hne (by rintro _ ⟨z,rfl⟩; exact burnolOperatorSymbol_bound T a ha z.property)

/-- Every bounded holomorphic symbol is realized by exactly one physical Burnol operator. -/
theorem existsUnique_burnol_operator_of_holomorphic {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ PrimeBlindCarlson.rightHalf) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ PrimeBlindCarlson.rightHalf, ‖φ z‖ ≤ M) :
    ∃! T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2,
      ‖T‖ ≤ M ∧ ∀ (z : ℂ) (hz : 0 < z.re), T (burnolComplexFeature z hz) =
        φ z • burnolComplexFeature z hz := by
  let a : Nat.Primes → ℂ := fun p => φ (Real.log (p : ℝ))
  obtain ⟨T,hT,ha⟩ := (primeBurnol_bounded_operator_iff_holomorphic a hM).mpr
    ⟨φ,hφ,hb,fun _ => rfl⟩
  have hs : EqOn (burnolOperatorSymbol T) φ PrimeBlindCarlson.rightHalf :=
    eqOn_bounded_holomorphic_of_primeLog (burnolOperatorSymbol_analytic T) hφ
      (fun z hz => burnolOperatorSymbol_bound T a ha hz) hb
      (burnolOperatorSymbol_prime T a ha)
  refine ⟨T,⟨hT,fun z hz => ?_⟩,?_⟩
  · rw [burnolOperatorSymbol_eigen T a ha hz, hs hz]
  · rintro U ⟨hU,hUa⟩
    apply primeBurnol_operator_ext
    intro p
    have hraw : U (primeBurnolRawFeature p) = a p • primeBurnolRawFeature p := hUa _ _
    exact ((primeBurnol_eigenvalue_iff U p (a p)).mpr hraw).trans (ha p).symm

/-- Multiplication of holomorphic symbols is exactly composition of the physical operators. -/
theorem burnolOperatorSymbol_comp
    (T U : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) (a b : Nat.Primes → ℂ)
    (ha : ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p)
    (hb : ∀ p, U (primeLogCriticalLaplaceFeatureL2 p) = b p • primeLogCriticalLaplaceFeatureL2 p)
    {z : ℂ} (hz : 0 < z.re) :
    burnolOperatorSymbol (T.comp U) z = burnolOperatorSymbol T z * burnolOperatorSymbol U z := by
  have hc : ∀ p, (T.comp U) (primeLogCriticalLaplaceFeatureL2 p) =
      (a p * b p) • primeLogCriticalLaplaceFeatureL2 p := by
    intro p
    rw [ContinuousLinearMap.comp_apply, hb, map_smul, ha, smul_smul, mul_comm]
  apply smul_left_injective ℂ (burnolComplexFeature_ne_zero hz)
  change burnolOperatorSymbol (T.comp U) z • burnolComplexFeature z hz =
    (burnolOperatorSymbol T z * burnolOperatorSymbol U z) • burnolComplexFeature z hz
  rw [← burnolOperatorSymbol_eigen (T.comp U) (fun p => a p * b p) hc hz,
    ContinuousLinearMap.comp_apply, burnolOperatorSymbol_eigen U b hb hz,
    map_smul, burnolOperatorSymbol_eigen T a ha hz, smul_smul, mul_comm]

/-- Prime-line preservation has no extra bounded operators beyond the holomorphic symbol class. -/
theorem primeBurnol_preserves_lines_iff_holomorphic
    (T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2) :
    (∀ p : Nat.Primes, ∃ a : ℂ, T (primeLogCriticalLaplaceFeatureL2 p) =
      a • primeLogCriticalLaplaceFeatureL2 p) ↔
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ PrimeBlindCarlson.rightHalf ∧
      (∀ z ∈ PrimeBlindCarlson.rightHalf, ‖φ z‖ ≤ ‖T‖) ∧
      ∀ (z : ℂ) (hz : 0 < z.re), T (burnolComplexFeature z hz) = φ z • burnolComplexFeature z hz := by
  constructor
  · intro h
    choose a ha using h
    exact ⟨burnolOperatorSymbol T, burnolOperatorSymbol_analytic T,
      fun z hz => burnolOperatorSymbol_bound T a ha hz, fun z hz => burnolOperatorSymbol_eigen T a ha hz⟩
  · rintro ⟨φ,hφ,hb,he⟩ p
    refine ⟨φ (Real.log (p : ℝ)), (primeBurnol_eigenvalue_iff T p _).mpr ?_⟩
    exact he _ _

end RHTower
