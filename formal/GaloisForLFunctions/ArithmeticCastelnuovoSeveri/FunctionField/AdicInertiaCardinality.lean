import GaloisForLFunctions.HTGeometry.ValuationInertiaRamificationIndex

/-!
# Inertia cardinality for normalized adic valuations

The valuation subring attached to a height-one prime has that prime as
its center. The valuation-theoretic inertia group therefore has order
equal to the ideal-theoretic ramification index in a finite Galois
normalization with perfect base residue field.
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

/-- The inertia group of the normalized adic valuation has order equal to its ramification index. -/
theorem heightOne_inertia_card (v : HeightOneSpectrum A) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] [PerfectField v.asIdeal.ResidueField] :
    Nat.card ((w.valuation L).valuationSubring.inertiaSubgroup K) =
      v.asIdeal.ramificationIdx' w.asIdeal := by
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
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
  have h := GaloisForLFunctions.HTGeometry.ValuationInertia.natCard_inertiaSubgroup_eq_ramificationIdxIn
    (T := B) K v.asIdeal W hW hAW hcent
  letI : Algebra.IsIntegral A B := ⟨IsIntegralClosure.isIntegral A L⟩
  letI : MulSemiringAction (L ≃ₐ[K] L) B := IsIntegralClosure.MulSemiringAction A K L B
  letI : IsGaloisGroup (L ≃ₐ[K] L) A B := IsGaloisGroup.of_isFractionRing _ _ _ K L
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (L ≃ₐ[K] L)] at h
  exact h.trans (Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
