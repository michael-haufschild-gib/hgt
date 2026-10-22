import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianResolvedAdmission
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittCompletedXiGreenIncidenceComparison
import GaloisForLFunctions.RHTower.Deninger.DeningerCompletedXiHellingerGammaGreenResolvedProvenance

/-!
# Green range wall for the reflected Meyer Gaussian horizon

Continuous compact-support arithmetic cohomology is exactly the algebraic direct sum of finite
Xi-jet families.  The comparison-model source Green operator therefore has exactly the finite-jet
range inside completed Xi cohomology, although that range is dense.

The reflected-Gaussian horizon vector is nonzero at every divisor copy.  Since the actual Xi
divisor has infinitely many copies, this vector is not in the comparison-model Green range but is
in its closure.  The same exact `closure \ range` classification survives the isometric
Calderon--Witt incidence comparison and the injective resolved Hellinger--Gamma provenance source.

Thus the current compact dual cannot supply a Green primitive for the admitted singular source.
Any such primitive requires a genuinely nonlocal completion of the compact-support source; density
shows that this completion, rather than a different coefficient vector, is the sharp survivor.
-/

open Complex Function Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The comparison-model source Green range is exactly the algebraic finite-jet subspace. -/
theorem deningerArithmeticSourceGreen_range_eq_finiteJetHilbert_range :
    Set.range deningerArithmeticSourceGreen =
      Set.range deningerArithmeticJetTestToHilbert := by
  ext x
  constructor
  · rintro ⟨ell, rfl⟩
    let a : DeningerArithmeticJetTest :=
      deningerArithmeticJetTestCompactEquiv.symm ell
    refine ⟨deningerArithmeticOrientedGreenJetTest a, ?_⟩
    rw [← deningerArithmeticSourceGreen_test a]
    congr 1
    exact deningerArithmeticJetTestCompactEquiv.apply_symm_apply ell
  · rintro ⟨b, rfl⟩
    refine ⟨deningerArithmeticJetTestToCompact
      (-deningerArithmeticOrientedGreenJetTest b), ?_⟩
    rw [deningerArithmeticSourceGreen_test]
    have hgreen :
        deningerArithmeticOrientedGreenJetTest
            (-deningerArithmeticOrientedGreenJetTest b) = b := by
      rw [map_neg, deningerArithmeticOrientedGreenJetTest_sq]
      exact neg_neg b
    rw [hgreen]

/-- A completed Xi vector nonzero at every divisor copy cannot come from the compact source dual. -/
theorem not_mem_deningerArithmeticSourceGreen_range_of_forall_ne_zero
    (x : DeningerArithmeticCompletedH1)
    (hx : ∀ r : XiZeroCopy, x r ≠ 0) :
    x ∉ Set.range deningerArithmeticSourceGreen := by
  letI : Infinite DeningerArithmeticJetCoordinate :=
    xiZeroCopyEquivDeningerArithmeticJetCoordinate.infinite_iff.mp inferInstance
  rw [deningerArithmeticSourceGreen_range_eq_finiteJetHilbert_range]
  rintro ⟨b, hb⟩
  have hfinite : ((↑b.support : Set DeningerArithmeticJetCoordinate)).Finite :=
    b.support.finite_toSet
  have hne :
      (↑b.support : Set DeningerArithmeticJetCoordinate) ≠ Set.univ := by
    intro heq
    have huniv : (Set.univ : Set DeningerArithmeticJetCoordinate).Finite := by
      rw [← heq]
      exact hfinite
    exact Set.infinite_univ huniv
  have houtside : ∃ r : DeningerArithmeticJetCoordinate, r ∉ b.support := by
    by_contra h
    apply hne
    ext r
    simp only [Set.mem_univ, iff_true]
    by_contra hr
    exact h ⟨r, hr⟩
  obtain ⟨r, hr⟩ := houtside
  have hbr : b r = 0 := by
    by_contra hbr
    exact hr (Finsupp.mem_support_iff.mpr hbr)
  have hcoeff := congrArg
    (fun y : DeningerArithmeticCompletedH1 => y r) hb
  rw [deningerArithmeticJetTestToHilbert_apply, hbr] at hcoeff
  exact hx r hcoeff.symm

namespace DeningerMeyerGaussianGreen

/-- The reflected-Gaussian admitted residue has no current compact-source Green primitive. -/
theorem reflectedGaussianHorizonAdmittedResidue_not_mem_sourceGreen_range :
    reflectedGaussianHorizonAdmittedResidue ∉
      Set.range deningerArithmeticSourceGreen := by
  exact not_mem_deningerArithmeticSourceGreen_range_of_forall_ne_zero
    reflectedGaussianHorizonAdmittedResidue fun r => by
      rw [reflectedGaussianHorizonAdmittedResidue_apply]
      exact reflectedGaussianHorizonGrade_ne_zero r

/-- The missing primitive is a completion wall: the admitted vector is approximable by source
Green vectors even though no compact-source vector maps to it. -/
theorem reflectedGaussianHorizonAdmittedResidue_mem_closure_sourceGreen_range :
    reflectedGaussianHorizonAdmittedResidue ∈
      closure (Set.range deningerArithmeticSourceGreen) := by
  have hd := deningerArithmeticSourceGreen_dense
  rw [denseRange_iff_closure_range] at hd
  rw [hd]
  exact Set.mem_univ _

/-- The actual completed incidence image is outside the current completed Green range. -/
theorem reflectedGaussianHorizonAdmittedIncidence_not_mem_completedGreen_range
    (p q : Nat.Primes) (hpq : p ≠ q) :
    reflectedGaussianHorizonAdmittedIncidence p q hpq ∉
      Set.range
        (deningerArithmeticCompletedGreenToCrossPrimeIncidence p q hpq) := by
  rintro ⟨ell, hell⟩
  apply reflectedGaussianHorizonAdmittedResidue_not_mem_sourceGreen_range
  refine ⟨ell, ?_⟩
  apply (deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq).injective
  rw [← deningerArithmeticCompletedGreenToCrossPrimeIncidence_apply,
    ← reflectedGaussianHorizonAdmittedIncidence]
  exact hell

/-- The actual completed incidence image remains in the closure of the completed Green range. -/
theorem reflectedGaussianHorizonAdmittedIncidence_mem_closure_completedGreen_range
    (p q : Nat.Primes) (hpq : p ≠ q) :
    reflectedGaussianHorizonAdmittedIncidence p q hpq ∈
      closure
        (Set.range
          (deningerArithmeticCompletedGreenToCrossPrimeIncidence p q hpq)) := by
  have hd :=
    deningerArithmeticCompletedGreenToCrossPrimeIncidence_dense p q hpq
  rw [denseRange_iff_closure_range] at hd
  rw [hd]
  exact Set.mem_univ _

/-- Comparison-model Green transport followed by resolved provenance. -/
def deningerArithmeticCompletedGreenToResolvedProvenance
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    DeningerArithmeticTopologicalH1Compact →ₗ[ℂ]
      (HellingerGammaResolvedProvenanceCofaceCompletion p q hpq ⧸
        hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a) :=
  (hellingerGammaResolvedProvenanceQuotientSource hpq a).comp
    (deningerArithmeticCompletedGreenToCrossPrimeIncidence p q hpq).toLinearMap

/-- The resolved provenance source is continuous, despite being recorded as a linear map. -/
theorem continuous_hellingerGammaResolvedProvenanceQuotientSource
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    Continuous (hellingerGammaResolvedProvenanceQuotientSource hpq a) := by
  change Continuous (fun x =>
    (hellingerGammaResolvedProvenanceAdjacentCofaceClosedSpan hpq a).mkQ
      (0, x))
  exact continuous_quot_mk.comp (continuous_const.prodMk continuous_id)

/-- Resolved provenance retains the failure of current compact-source Green realization. -/
theorem reflectedGaussianHorizonAdmittedResolvedClass_not_mem_completedGreen_range
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    reflectedGaussianHorizonAdmittedResolvedClass p q hpq a ∉
      Set.range
        (deningerArithmeticCompletedGreenToResolvedProvenance p q hpq a) := by
  rintro ⟨ell, hell⟩
  apply reflectedGaussianHorizonAdmittedIncidence_not_mem_completedGreen_range
    p q hpq
  refine ⟨ell, ?_⟩
  apply hellingerGammaResolvedProvenanceQuotientSource_injective hpq a
  exact hell

/-- The resolved class is nevertheless a limit of current compact-source Green classes. -/
theorem reflectedGaussianHorizonAdmittedResolvedClass_mem_closure_completedGreen_range
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    reflectedGaussianHorizonAdmittedResolvedClass p q hpq a ∈
      closure
        (Set.range
          (deningerArithmeticCompletedGreenToResolvedProvenance p q hpq a)) := by
  have hx :=
    reflectedGaussianHorizonAdmittedIncidence_mem_closure_completedGreen_range
      p q hpq
  have himage :
      hellingerGammaResolvedProvenanceQuotientSource hpq a
          (reflectedGaussianHorizonAdmittedIncidence p q hpq) ∈
        closure
          (hellingerGammaResolvedProvenanceQuotientSource hpq a ''
            Set.range
              (deningerArithmeticCompletedGreenToCrossPrimeIncidence p q hpq)) := by
    apply image_closure_subset_closure_image
      (continuous_hellingerGammaResolvedProvenanceQuotientSource p q hpq a)
    exact ⟨_, hx, rfl⟩
  have hrange :
      hellingerGammaResolvedProvenanceQuotientSource hpq a ''
          Set.range
            (deningerArithmeticCompletedGreenToCrossPrimeIncidence p q hpq) =
        Set.range
          (deningerArithmeticCompletedGreenToResolvedProvenance p q hpq a) := by
    ext z
    constructor
    · rintro ⟨_, ⟨ell, rfl⟩, rfl⟩
      exact ⟨ell, rfl⟩
    · rintro ⟨ell, rfl⟩
      exact ⟨_, ⟨ell, rfl⟩, rfl⟩
  change
    hellingerGammaResolvedProvenanceQuotientSource hpq a
        (reflectedGaussianHorizonAdmittedIncidence p q hpq) ∈ _
  rw [← hrange]
  exact himage

end DeningerMeyerGaussianGreen

end


end RHTower
