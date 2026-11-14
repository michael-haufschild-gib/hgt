import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.AdicInertiaCardinality
import GaloisForLFunctions.HTGeometry.ValuationSubringDecompositionOrder

/-!
# Decomposition cardinality for normalized adic valuations

The decomposition group of a height-one place in a finite Galois
normalization has order `e f`. Its valuation center identifies the
ideal-theoretic residue degree, and the adic inertia comparison
identifies the ramification factor.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open IsDedekindDomain IsLocalRing

variable {A B K L : Type*}
  [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A B] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L] [IsIntegralClosure B A L]
  [Module.IsTorsionFree A B]

/-- The decomposition group at an adic place has order equal to ramification times residue degree. -/
theorem heightOne_decomposition_card (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] [PerfectField v.asIdeal.ResidueField] :
    Nat.card ((w.valuation L).valuationSubring.decompositionSubgroup K) =
      v.asIdeal.ramificationIdx' w.asIdeal * v.asIdeal.inertiaDeg' w.asIdeal := by
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  let W := (w.valuation L).valuationSubring
  have hW : W ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := w.valuation_surjective L (WithZero.exp (1 : ℤ))
    have hle : w.valuation L x ≤ 1 := by
      change x ∈ W
      rw [htop]
      trivial
    rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    omega
  have hAW : ∀ a : A, algebraMap A L a ∈ W := by
    intro a
    change w.valuation L (algebraMap A L a) ≤ 1
    rw [IsScalarTower.algebraMap_apply A B L, HeightOneSpectrum.valuation_of_algebraMap]
    exact w.intValuation_le_one _
  have hcent : ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔ a ∈ v.asIdeal := by
    intro a
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, Valuation.mem_maximalIdeal_iff]
    change w.valuation L (algebraMap A L a) < 1 ↔ a ∈ v.asIdeal
    rw [IsScalarTower.algebraMap_apply A B L, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact (Ideal.mem_of_liesOver w.asIdeal v.asIdeal a).symm
  have h := GaloisForLFunctions.HTGeometry.ValuationInertia.natCard_decompositionSubgroup_eq_natCard_inertiaSubgroup_mul_inertiaDegIn
    (T := B) K v.asIdeal W hW hAW hcent
  letI : Algebra.IsIntegral A B := ⟨IsIntegralClosure.isIntegral A L⟩
  letI : MulSemiringAction (L ≃ₐ[K] L) B := IsIntegralClosure.MulSemiringAction A K L B
  letI : IsGaloisGroup (L ≃ₐ[K] L) A B := IsGaloisGroup.of_isFractionRing _ _ _ K L
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal (L ≃ₐ[K] L),
    heightOne_inertia_card v w] at h
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
