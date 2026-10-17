import GaloisForLFunctions.RHTower.PrimeBurnolOperatorSymbol
import GaloisForLFunctions.HTGeometry.HolomorphicHalfPlanePickKernel

/-! The infinite-prime cubic and first-order Pick cones have the same bounded realization class. -/

noncomputable section
open Complex Set
open scoped InnerProductSpace ComplexConjugate

namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

/-- The first-order and cubic Pick defects on the entire actual-prime set. -/
def primeBurnolPickKernel (k : ℕ) (a : Nat.Primes → ℂ) (M : ℝ)
    (p q : Nat.Primes) : ℂ :=
  ((M : ℂ)^2 - a p * conj (a q)) /
    ((Real.log (p : ℝ) : ℂ) + (Real.log (q : ℝ) : ℂ))^k

theorem primeBurnol_firstPick_of_holomorphic {φ : ℂ → ℂ}
    (hφ : AnalyticOnNhd ℂ φ PrimeBlindCarlson.rightHalf) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ z ∈ PrimeBlindCarlson.rightHalf, ‖φ z‖ ≤ M) :
    IsPSDKernel (primeBurnolPickKernel 1 (fun p => φ (Real.log (p : ℝ))) M) := by
  refine (halfPlane_holomorphic_pickKernel_pos hφ hM hb
      (fun p : Nat.Primes => (Real.log (p : ℝ) : ℂ))
      (fun p => Real.log_pos (by exact_mod_cast p.property.one_lt))).congr (fun p q => ?_)
  simp only [primeBurnolPickKernel, pow_one, Complex.conj_ofReal]

private theorem primeBurnol_cauchy_pos :
    IsPSDKernel (fun p q : Nat.Primes =>
      (1 : ℂ) / ((Real.log (p : ℝ) : ℂ) + (Real.log (q : ℝ) : ℂ))) := by
  have h := primeBurnol_firstPick_of_holomorphic (φ := fun _ => 0)
    (fun _ _ => analyticAt_const) (M := 1) (by norm_num) (by intros; norm_num)
  refine h.congr (fun p q => ?_)
  simp only [primeBurnolPickKernel, Complex.ofReal_one, one_pow, zero_mul, sub_zero, pow_one]

/-- Schur multiplication always carries the first-order prime cone into the cubic cone. -/
theorem primeBurnol_cubicPick_of_first {a : Nat.Primes → ℂ} {M : ℝ}
    (h : IsPSDKernel (primeBurnolPickKernel 1 a M)) :
    IsPSDKernel (primeBurnolPickKernel 3 a M) := by
  refine (h.mul (primeBurnol_cauchy_pos.mul primeBurnol_cauchy_pos)).congr (fun p q => ?_)
  simp only [primeBurnolPickKernel, pow_one, div_eq_mul_inv, ← inv_pow, one_mul]
  ring

private theorem primeBurnol_gramDefect_eq (a : Nat.Primes → ℂ) (M : ℝ) (p q : Nat.Primes) :
    featureGramDefect primeBurnolRawFeature (fun p => a p • primeBurnolRawFeature p) M p q =
      2 * primeBurnolPickKernel 3 a M p q := by
  simp only [featureGramDefect, inner_smul_left, inner_smul_right, primeBurnolRawFeature,
    inner_burnolComplexFeature, Complex.conj_ofReal, primeBurnolPickKernel, div_eq_mul_inv]
  ring

/-- Cubic prime positivity is exactly bounded realizability on the literal output space. -/
theorem primeBurnol_cubicPick_iff_bounded_operator (a : Nat.Primes → ℂ) {M : ℝ} (hM : 0 ≤ M) :
    IsPSDKernel (primeBurnolPickKernel 3 a M) ↔
      ∃ T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2, ‖T‖ ≤ M ∧
        ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p := by
  constructor
  · intro h
    have hD : IsPSDKernel (featureGramDefect primeBurnolRawFeature
        (fun p => a p • primeBurnolRawFeature p) M) := by
      exact (h.const_mul (c := 2) (by norm_num)).congr
        (fun p q => (primeBurnol_gramDefect_eq a M p q).symm)
    obtain ⟨T,hT,he⟩ := exists_bounded_feature_map _ _ denseRange_primeBurnolRawSynthesis hM hD
    exact ⟨T,hT,fun p => (primeBurnol_eigenvalue_iff T p (a p)).mpr (he p)⟩
  · rintro ⟨T,hT,ha⟩
    have he : ∀ p, T (primeBurnolRawFeature p) = a p • primeBurnolRawFeature p :=
      fun p => (primeBurnol_eigenvalue_iff T p (a p)).mp (ha p)
    have hD : IsPSDKernel (featureGramDefect primeBurnolRawFeature
        (fun p => a p • primeBurnolRawFeature p) M) := by
      apply (isPSDKernel_featureGramDefect_iff _ _ hM).mpr
      intro c
      have hmap : Finsupp.linearCombination ℂ (fun p => a p • primeBurnolRawFeature p) c =
          T (Finsupp.linearCombination ℂ primeBurnolRawFeature c) := by
        simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, he]
      rw [hmap]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
    refine (hD.const_mul (c := 1 / 2) (by norm_num)).congr (fun p q => ?_)
    rw [primeBurnol_gramDefect_eq]
    push_cast
    ring

/-- The cubic prime cone has a complete bounded-holomorphic parametrization. -/
theorem primeBurnol_cubicPick_iff_holomorphic (a : Nat.Primes → ℂ) {M : ℝ} (hM : 0 ≤ M) :
    IsPSDKernel (primeBurnolPickKernel 3 a M) ↔
      ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ PrimeBlindCarlson.rightHalf ∧
        (∀ z ∈ PrimeBlindCarlson.rightHalf, ‖φ z‖ ≤ M) ∧
        ∀ p : Nat.Primes, φ (Real.log (p : ℝ)) = a p := by
  constructor
  · intro h
    obtain ⟨T,hT,ha⟩ := (primeBurnol_cubicPick_iff_bounded_operator a hM).mp h
    exact ⟨burnolOperatorSymbol T, burnolOperatorSymbol_analytic T,
      fun z hz => (burnolOperatorSymbol_bound T a ha hz).trans hT,
      burnolOperatorSymbol_prime T a ha⟩
  · rintro ⟨φ,hφ,hb,he⟩
    have h := primeBurnol_cubicPick_of_first (primeBurnol_firstPick_of_holomorphic hφ hM hb)
    have heq : (fun p : Nat.Primes => φ (Real.log (p : ℝ))) = a := funext he
    rwa [heq] at h

/-- On the entire actual-prime set, the cubic and first-order contraction cones coincide. -/
theorem primeBurnol_cubicPick_iff_firstPick (a : Nat.Primes → ℂ) {M : ℝ} (hM : 0 ≤ M) :
    IsPSDKernel (primeBurnolPickKernel 3 a M) ↔ IsPSDKernel (primeBurnolPickKernel 1 a M) := by
  constructor
  · intro h
    obtain ⟨φ,hφ,hb,he⟩ := (primeBurnol_cubicPick_iff_holomorphic a hM).mp h
    have h := primeBurnol_firstPick_of_holomorphic hφ hM hb
    have heq : (fun p : Nat.Primes => φ (Real.log (p : ℝ))) = a := funext he
    rwa [heq] at h
  · exact primeBurnol_cubicPick_of_first

/-- Exact classification of bounded eigenvalue data on the actual critical-prime columns. -/
theorem primeBurnol_bounded_operator_iff_holomorphic (a : Nat.Primes → ℂ) {M : ℝ} (hM : 0 ≤ M) :
    (∃ T : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2, ‖T‖ ≤ M ∧
      ∀ p, T (primeLogCriticalLaplaceFeatureL2 p) = a p • primeLogCriticalLaplaceFeatureL2 p) ↔
    ∃ φ : ℂ → ℂ, AnalyticOnNhd ℂ φ PrimeBlindCarlson.rightHalf ∧
      (∀ z ∈ PrimeBlindCarlson.rightHalf, ‖φ z‖ ≤ M) ∧
      ∀ p : Nat.Primes, φ (Real.log (p : ℝ)) = a p :=
  (primeBurnol_cubicPick_iff_bounded_operator a hM).symm.trans
    (primeBurnol_cubicPick_iff_holomorphic a hM)

end RHTower
