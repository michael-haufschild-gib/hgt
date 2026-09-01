import GaloisForLFunctions.RHTower.JointAncestryPrimeSupportUnitaryObstruction
import GaloisForLFunctions.RHTower.JointAncestryPrimeCoordinateGammaThetaNilpotentLandingNoGo

/-!
# All-prime reversible RFHM sewing no-go

This kills the literal-RFHM reversible survivor of the JAS route.  The argument needs neither an
adjoint nor any target action for an inverse coordinate.  Suppose a single-valued relation admits
every inverse source prime coordinate and forward covariance uses the actual RFHM Gamma insertion.
Move backward in the source and then forward through the literal insertion.  The source returns to
its starting point, so single-valuedness forces the original output into that insertion's range.
The range omits every coordinate whose native support contains the inserted prime.  Repeating over
all primes confines every nonzero output coefficient to empty native support.

Closedness and dense domain occur only in the final route predicate.  The core theorem therefore
also covers unbounded, non-diagonal, infinite-support sewings and arbitrary inverse reconstruction
encoded existentially by the relation.
-/

open Complex Real Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Literal RFHM operator for one actual, state-dependent Gamma insertion. -/
def jasGammaInsertionRFHM
    (x : Nat.Primes → ℝ) (P : Nat.Primes → Finset Nat.Primes)
    (p : Nat.Primes) : JASPacketHilbert →L[ℂ] JASPacketHilbert :=
  RestrictionPacket.packetOperator (jasGammaInsertionPacket (x p) p (P p))

/-- Forward covariance by the literal RFHM insertion plus inverse invariance of the source domain
already erase every coefficient with nonempty native prime support. No inverse target action is
needed. -/
theorem jasReversibleRFHM_relation_output_eq_zero_of_support_nonempty
    {sigma t : ℝ} (hsigma : 0 < sigma)
    (x : Nat.Primes → ℝ) (P : Nat.Primes → Finset Nat.Primes)
    (R : Submodule ℂ
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert))
    (hsingle : HilbertRelationSingleValued R)
    (hplus : ∀ p z, z ∈ R →
      hilbertBlockDiagonal
        (jasPrimeCoordinateMul sigma t hsigma p 1)
        (jasGammaInsertionRFHM x P p) z ∈ R)
    (hpre : ∀ p z, z ∈ R →
      ∃ zminus ∈ R, hilbertSumFst zminus =
        jasPrimeCoordinateMul sigma t hsigma p (-1) (hilbertSumFst z))
    {z : HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert}
    (hz : z ∈ R) (i : JASPrimeSupport × JASLogGrade)
    (hi : i.1.Nonempty) :
    ((hilbertSumSnd z : JASPacketHilbert) :
        (JASPrimeSupport × JASLogGrade) → ℂ) i = 0 := by
  classical
  obtain ⟨p, hp⟩ := hi
  obtain ⟨zminus, hzminus, hsource⟩ := hpre p z hz
  let zback := hilbertBlockDiagonal
    (jasPrimeCoordinateMul sigma t hsigma p 1)
      (jasGammaInsertionRFHM x P p) zminus
  have hzback : zback ∈ R := hplus p zminus hzminus
  have hfst : hilbertSumFst zback = hilbertSumFst z := by
    dsimp only [zback]
    rw [hilbertBlockDiagonal_fst, hsource]
    exact jasPrimeCoordinateMul_pos_neg sigma t hsigma p (hilbertSumFst z)
  have hout : hilbertSumSnd zback = hilbertSumSnd z :=
    hilbertRelation_snd_eq_of_fst_eq hsingle hzback hz hfst
  have hnot : ¬ i.1 ⊆ jasFiniteSupportComplement {p} := by
    intro hle
    have hp' : p ∈ jasFiniteSupportComplement {p} := hle hp
    simp [jasFiniteSupportComplement] at hp'
  dsimp only [zback] at hout
  rw [hilbertBlockDiagonal_snd] at hout
  have hcoord := congrArg
    (fun y : JASPacketHilbert =>
      ((y : JASPacketHilbert) : (JASPrimeSupport × JASLogGrade) → ℂ) i) hout
  rw [jasGammaInsertionRFHM, RestrictionPacket.packetOperator_apply] at hcoord
  change (if i.1 ⊆ jasFiniteSupportComplement {p} then _ else 0) = _ at hcoord
  rw [if_neg hnot] at hcoord
  exact hcoord.symm

/-- Exact classification: any nonzero output coefficient of an all-prime reversible literal-RFHM
relation lies in the empty native-support sector, regardless of inverse target transport. -/
theorem jasReversibleRFHM_relation_output_support_eq_empty_of_ne_zero
    {sigma t : ℝ} (hsigma : 0 < sigma)
    (x : Nat.Primes → ℝ) (P : Nat.Primes → Finset Nat.Primes)
    (R : Submodule ℂ
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert))
    (hsingle : HilbertRelationSingleValued R)
    (hplus : ∀ p z, z ∈ R →
      hilbertBlockDiagonal
        (jasPrimeCoordinateMul sigma t hsigma p 1)
        (jasGammaInsertionRFHM x P p) z ∈ R)
    (hpre : ∀ p z, z ∈ R →
      ∃ zminus ∈ R, hilbertSumFst zminus =
        jasPrimeCoordinateMul sigma t hsigma p (-1) (hilbertSumFst z))
    {z : HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert}
    (hz : z ∈ R) (i : JASPrimeSupport × JASLogGrade)
    (hne : ((hilbertSumSnd z : JASPacketHilbert) :
        (JASPrimeSupport × JASLogGrade) → ℂ) i ≠ 0) :
    i.1 = ∅ := by
  by_contra hi
  exact hne (jasReversibleRFHM_relation_output_eq_zero_of_support_nonempty
    hsigma x P R hsingle hplus hpre hz i (Set.nonempty_iff_ne_empty.mpr hi))

/-- Route predicate for an all-prime reversible literal-RFHM sewing whose source domain admits every
inverse prime coordinate and whose output retains one nonempty-support coefficient. -/
def JASAllPrimeReversibleRFHMSewing : Prop :=
  ∃ (sigma t : ℝ) (hsigma : 0 < sigma)
      (x : Nat.Primes → ℝ) (P : Nat.Primes → Finset Nat.Primes)
      (R : Submodule ℂ
        (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert)),
    IsClosed (R : Set
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASPacketHilbert)) ∧
    Dense (hilbertRelationDomain R : Set (PrimePoissonL2 sigma t hsigma)) ∧
    HilbertRelationSingleValued R ∧
    (∀ p z, z ∈ R →
      hilbertBlockDiagonal
        (jasPrimeCoordinateMul sigma t hsigma p 1)
        (jasGammaInsertionRFHM x P p) z ∈ R) ∧
    (∀ p z, z ∈ R →
      ∃ zminus ∈ R, hilbertSumFst zminus =
        jasPrimeCoordinateMul sigma t hsigma p (-1) (hilbertSumFst z)) ∧
    ∃ z ∈ R, ∃ i : JASPrimeSupport × JASLogGrade,
      i.1.Nonempty ∧
      ((hilbertSumSnd z : JASPacketHilbert) :
        (JASPrimeSupport × JASLogGrade) → ℂ) i ≠ 0

/-- Exact route-class kill: no closed, densely defined, single-valued all-prime reversible sewing
can use literal RFHM insertion operators while retaining nonempty native prime support, even with
arbitrary inverse transport and non-diagonal infinite-support reconstruction. -/
theorem not_JASAllPrimeReversibleRFHMSewing :
    ¬ JASAllPrimeReversibleRFHMSewing := by
  rintro ⟨sigma, t, hsigma, x, P, R, _hclosed, _hdense, hsingle,
    hplus, hpre, z, hz, i, hi, hne⟩
  exact hne (jasReversibleRFHM_relation_output_eq_zero_of_support_nonempty
    hsigma x P R hsingle hplus hpre hz i hi)

end

end RHTower
