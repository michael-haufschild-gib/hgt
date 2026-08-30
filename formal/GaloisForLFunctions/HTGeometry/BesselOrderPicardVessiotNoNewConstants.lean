import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedPicardVessiot
import GaloisForLFunctions.HTGeometry.DifferencePicardVessiotGeneration
import GaloisForLFunctions.HTGeometry.DifferencePicardVessiotConstants
import GaloisForLFunctions.HTGeometry.FiniteAutomorphismOrbitAlgebraicity

/-!
# Ordinary Picard--Vessiot ring for the concrete Bessel order system

The fixed field of the rational-coordinate shift is the concrete differential closure of the
complex constants.  That field is algebraically closed and infinite, so the general ordinary
Picard--Vessiot construction specializes to the Bessel companion with no new constants.
-/

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions.HTGeometry Polynomial

/-- The concrete rational-shift constant field is infinite. -/
theorem besselDifferenceConstants_infinite :
    (((differenceConstants
      (FieldShift.ratShiftEquiv : RatFunc Constants ≃+* RatFunc Constants)) :
        Subfield (RatFunc Constants)) : Set (RatFunc Constants)).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := algebraMap Constants (RatFunc Constants))
    (algebraMap Constants (RatFunc Constants)).injective
  intro a
  change FieldShift.ratShiftEquiv (algebraMap Constants (RatFunc Constants) a) =
    algebraMap Constants (RatFunc Constants) a
  simpa using FieldShift.ratShift_const a

/-- Every positive-degree invariant monic polynomial over the concrete rational shift field has a
shift-fixed root.  Invariance descends every coefficient to the algebraically closed constant
field, where the root is chosen. -/
theorem besselRatShift_invariant_monic_has_fixed_root
    (g : (RatFunc Constants)[X]) (hmonic : g.Monic) (hdegree : 0 < g.natDegree)
    (hinvariant : g.map
      (FieldShift.ratShiftEquiv : RatFunc Constants ≃+* RatFunc Constants) = g) :
    ∃ a : RatFunc Constants,
      FieldShift.ratShiftEquiv a = a ∧ g.IsRoot a := by
  have hcoeff : ∀ n, g.coeff n ∈
      (algebraMap Constants (RatFunc Constants)).range := by
    intro n
    have hc := congrArg (fun p : (RatFunc Constants)[X] => p.coeff n) hinvariant
    have hfixed : FieldShift.ratShift (g.coeff n) = g.coeff n := by
      rw [Polynomial.coeff_map] at hc
      change FieldShift.ratShift (g.coeff n) = g.coeff n at hc
      exact hc
    obtain ⟨c, hc⟩ := FieldShift.ratShift_fixed_eq_const hfixed
    exact ⟨c, hc.symm⟩
  obtain ⟨q, hq⟩ := exists_map_polynomial_eq_of_coeff_mem_range
    (algebraMap Constants (RatFunc Constants)) g hcoeff
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.map_zero] at hq
    exact hmonic.ne_zero hq.symm
  have hqNatDegree : q.natDegree = g.natDegree := by
    have h := Polynomial.natDegree_map_eq_of_injective
      (algebraMap Constants (RatFunc Constants)).injective q
    rw [hq] at h
    exact h.symm
  have hqDegreePos : 0 < q.natDegree := by omega
  have hqDegree : q.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hq0]
    exact_mod_cast (Nat.ne_of_gt hqDegreePos)
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root q hqDegree
  refine ⟨algebraMap Constants (RatFunc Constants) a, ?_, ?_⟩
  · simpa using FieldShift.ratShift_const a
  · have hmap := ha.map (f := algebraMap Constants (RatFunc Constants))
    rw [hq] at hmap
    exact hmap

/-- Difference automorphism on the localized ordinary coordinate ring of the concrete Bessel
system. -/
def besselOrderPVSigma (s : ℝ) :
    pvLocalization (RatFunc Constants) 2 ≃+* pvLocalization (RatFunc Constants) 2 :=
  pvSigma FieldShift.ratShiftEquiv
    (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
    (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s)

/-- Complete ordinary Picard--Vessiot data for the concrete Bessel order companion, including
sigma-simplicity and the exact no-new-constants property. -/
structure BesselOrderPVNoNewConstantsData (s : ℝ) where
  M : Ideal (pvLocalization (RatFunc Constants) 2)
  isSigmaIdeal : IsSigmaIdeal (besselOrderPVSigma s) M
  ne_top : M ≠ ⊤
  isSigmaIdeal_symm : IsSigmaIdeal (besselOrderPVSigma s).symm M
  isSigmaSimple :
    IsSigmaSimple
      (sigmaQuotientEquiv (besselOrderPVSigma s) M isSigmaIdeal isSigmaIdeal_symm)
  fundamental : ∀ i j,
    sigmaQuotientEquiv (besselOrderPVSigma s) M isSigmaIdeal isSigmaIdeal_symm
        (Ideal.Quotient.mk M (pvFundamental (RatFunc Constants) 2 i j)) =
      ((((FieldShift.besselOrderCompanion (slope s)).map
          (pvBaseMap (RatFunc Constants) 2)).map (Ideal.Quotient.mk M)) *
        ((pvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M))) i j
  fundamental_det_isUnit :
    IsUnit ((pvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M)).det
  detInverse : (pvLocalization (RatFunc Constants) 2) ⧸ M
  fundamental_det_mul_inverse :
    ((pvFundamental (RatFunc Constants) 2).map (Ideal.Quotient.mk M)).det * detInverse = 1
  generated : Algebra.adjoin (RatFunc Constants)
    (Set.range (fun p : Fin 2 × Fin 2 =>
      Ideal.Quotient.mk M (pvFundamental (RatFunc Constants) 2 p.1 p.2)) ∪
      {detInverse}) = ⊤
  noNewConstants : ∀ x : (pvLocalization (RatFunc Constants) 2) ⧸ M,
    sigmaQuotientEquiv (besselOrderPVSigma s) M isSigmaIdeal isSigmaIdeal_symm x = x →
      ∃ a : RatFunc Constants,
        FieldShift.ratShiftEquiv a = a ∧
          x = algebraMap (RatFunc Constants)
            ((pvLocalization (RatFunc Constants) 2) ⧸ M) a

/-- Ordinary Picard--Vessiot existence with exact constants for every concrete Bessel slope. -/
theorem besselOrder_picardVessiot_noNewConstants_exists :
    ∀ s : ℝ, Nonempty (BesselOrderPVNoNewConstantsData s) := by
  intro s
  obtain ⟨M, hM, hMne, hM', hsimple, hfund, hdet, hconstants⟩ :=
    exists_picardVessiot_no_new_constants
      FieldShift.ratShiftEquiv
      (FieldShift.besselOrderCompanion (slope s)) (besselOrderCompanionInverse s)
      (besselOrderCompanion_mul_inverse s) (besselOrderCompanion_inverse_mul s)
      besselDifferenceConstants_infinite
      besselRatShift_invariant_monic_has_fixed_root
  exact ⟨{
    M := M
    isSigmaIdeal := hM
    ne_top := hMne
    isSigmaIdeal_symm := hM'
    isSigmaSimple := hsimple
    fundamental := hfund
    fundamental_det_isUnit := hdet
    detInverse := Ideal.Quotient.mk M
      (IsLocalization.Away.invSelf
        ((fundamentalMatrix (RatFunc Constants) 2).det))
    fundamental_det_mul_inverse := pvQuotient_det_mul_inverse M
    generated := pvQuotient_adjoin M
    noNewConstants := hconstants
  }⟩

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
