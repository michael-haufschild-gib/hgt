import GaloisForLFunctions.RHTower.JointAncestryAllPrimeReversibleRFHMSewingNoGo

/-!
# C(PrimeTorus)-linear RFHM sewing no-go

This closes the literal-RFHM version of the prime-support-synchronized `C(PrimeTorus)` sewing
named as the remaining JAS core. Full source-linearity already supplies the inverse-coordinate
predecessor required by the all-prime reversible no-go: apply covariance to the negative coordinate
character. No algebraic law for the target family is needed.

Consequently every nonzero target coefficient of such a relation has empty native prime support.
Thus no closed densely defined single-valued `C(PrimeTorus)`-source-linear sewing can both realize
actual RFHM insertion on positive prime coordinates and retain the prime-support payload needed by
JAS. A survivor must replace literal RFHM insertion by a non-reversible compression,
correspondence, corner, or other carrier outside this source-linear target-family interface.
-/

open Complex Real Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Full `C(PrimeTorus)` source-linearity plus literal positive-coordinate RFHM covariance erase
every coefficient with nonempty native prime support. The negative coordinate character supplies
the inverse source predecessor automatically; its target operator remains arbitrary. -/
theorem jasCPrimeTorusRFHM_relation_output_eq_zero_of_support_nonempty
    {sigma t : ℝ} (hsigma : 0 < sigma)
    (x : Nat.Primes → ℝ) (P : Nat.Primes → Finset Nat.Primes)
    (rho : C(PrimeTorus, ℂ) → JASPacketHilbert →L[ℂ] JASPacketHilbert)
    (R : Submodule ℂ
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert))
    (hsingle : HilbertRelationSingleValued R)
    (hlinear : ∀ f z, z ∈ R →
      hilbertBlockDiagonal
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f)
        (rho f) z ∈ R)
    (hcoord : ∀ p,
      rho (torusCharacter (Finsupp.single p (1 : ℤ))) =
        jasGammaInsertionRFHM x P p)
    {z : HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert}
    (hz : z ∈ R) (i : JASPrimeSupport × JASLogGrade)
    (hi : i.1.Nonempty) :
    ((hilbertSumSnd z : JASPacketHilbert) :
        (JASPrimeSupport × JASLogGrade) → ℂ) i = 0 := by
  apply jasReversibleRFHM_relation_output_eq_zero_of_support_nonempty
    hsigma x P R hsingle
  · intro p w hw
    have h := hlinear (torusCharacter (Finsupp.single p (1 : ℤ))) w hw
    rw [hcoord p] at h
    exact h
  · intro p w hw
    let fminus : C(PrimeTorus, ℂ) :=
      torusCharacter (Finsupp.single p (-1 : ℤ))
    let wminus := hilbertBlockDiagonal
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) fminus)
      (rho fminus) w
    refine ⟨wminus, hlinear fminus w hw, ?_⟩
    rfl
  · exact hz
  · exact hi

/-- Sharp positive boundary: any nonzero output coefficient of a literal-RFHM
`C(PrimeTorus)`-source-linear relation lies in the empty native-support sector. -/
theorem jasCPrimeTorusRFHM_relation_output_support_eq_empty_of_ne_zero
    {sigma t : ℝ} (hsigma : 0 < sigma)
    (x : Nat.Primes → ℝ) (P : Nat.Primes → Finset Nat.Primes)
    (rho : C(PrimeTorus, ℂ) → JASPacketHilbert →L[ℂ] JASPacketHilbert)
    (R : Submodule ℂ
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert))
    (hsingle : HilbertRelationSingleValued R)
    (hlinear : ∀ f z, z ∈ R →
      hilbertBlockDiagonal
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f)
        (rho f) z ∈ R)
    (hcoord : ∀ p,
      rho (torusCharacter (Finsupp.single p (1 : ℤ))) =
        jasGammaInsertionRFHM x P p)
    {z : HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert}
    (hz : z ∈ R) (i : JASPrimeSupport × JASLogGrade)
    (hne : ((hilbertSumSnd z : JASPacketHilbert) :
        (JASPrimeSupport × JASLogGrade) → ℂ) i ≠ 0) :
    i.1 = ∅ := by
  by_contra hi
  exact hne (jasCPrimeTorusRFHM_relation_output_eq_zero_of_support_nonempty
    hsigma x P rho R hsingle hlinear hcoord hz i
      (Set.nonempty_iff_ne_empty.mpr hi))

/-- Exact remaining JAS interface specialized to literal state-dependent RFHM insertion on every
positive prime coordinate and requiring one retained nonempty native-support coefficient. -/
def JASPrimeSupportSynchronizedCPrimeTorusRFHMSewing : Prop :=
  ∃ (sigma t : ℝ) (hsigma : 0 < sigma)
      (x : Nat.Primes → ℝ) (P : Nat.Primes → Finset Nat.Primes)
      (rho : C(PrimeTorus, ℂ) → JASPacketHilbert →L[ℂ] JASPacketHilbert)
      (R : Submodule ℂ
        (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert)),
    IsClosed (R : Set
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert)) ∧
    Dense (hilbertRelationDomain R : Set (PrimePoissonL2 sigma t hsigma)) ∧
    HilbertRelationSingleValued R ∧
    (∀ f z, z ∈ R →
      hilbertBlockDiagonal
        (continuousL2Mul (primePoissonMeasure sigma t hsigma) f)
        (rho f) z ∈ R) ∧
    (∀ p, rho (torusCharacter (Finsupp.single p (1 : ℤ))) =
      jasGammaInsertionRFHM x P p) ∧
    ∃ z ∈ R, ∃ i : JASPrimeSupport × JASLogGrade,
      i.1.Nonempty ∧
      ((hilbertSumSnd z : JASPacketHilbert) :
        (JASPrimeSupport × JASLogGrade) → ℂ) i ≠ 0

/-- Terminal route-class kill for the missing literal-RFHM JAS
prime-support-synchronized `C(PrimeTorus)` sewing. -/
theorem not_JASPrimeSupportSynchronizedCPrimeTorusRFHMSewing :
    ¬ JASPrimeSupportSynchronizedCPrimeTorusRFHMSewing := by
  rintro ⟨sigma, t, hsigma, x, P, rho, R, _hclosed, _hdense,
    hsingle, hlinear, hcoord, z, hz, i, hi, hne⟩
  exact hne (jasCPrimeTorusRFHM_relation_output_eq_zero_of_support_nonempty
    hsigma x P rho R hsingle hlinear hcoord hz i hi)

end

end RHTower
