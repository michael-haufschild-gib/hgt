import GaloisForLFunctions.RHTower.JointAncestryRestrictionHistoryArithmeticSpecialization
import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.HTGeometry.PrimePoissonSourceLinearSuperselection

open scoped ENNReal

/-!
# JAS prime-support unitary obstruction

The most direct prime-support-synchronized JAS source action cannot exist. A prime-torus
coordinate character is invertible, so every unital multiplicative operator representation sends
it to a surjective operator. The actual RFHM Gamma insertion operator cuts native support and is
not surjective.

The positive boundary is exact: a canonical arithmetic RFHM packet operator is surjective if and
only if its native support is all primes. Thus reversible support-free history may represent source
units, while genuine prime insertion must enter through a compression, correspondence, corner, or
group completion rather than as the `C(PrimeTorus)` action itself.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Canonical RFHM Hilbert carrier for the arithmetic JAS specialization. -/
abbrev JASPacketHilbert :=
  RestrictionPacket.PacketHilbert (E := JASPrimeSupport) (G := JASLogGrade)

private theorem jasSupportProjection_univ :
    RestrictionPacket.supportProjection (G := JASLogGrade)
        (Set.univ : JASPrimeSupport) =
      ContinuousLinearMap.id ℂ JASPacketHilbert := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp [RestrictionPacket.supportProjection_apply]

/-- Exact unit classification: a canonical JAS packet operator is onto precisely when it carries
no proper native-support cut. -/
theorem jasPacketOperator_surjective_iff_support_eq_univ
    (s : JASRestrictionPacket) :
    Function.Surjective (RestrictionPacket.packetOperator s) ↔
      s.support = Set.univ := by
  constructor
  · intro hsurj
    by_contra hs
    have hnot : ¬ (Set.univ : JASPrimeSupport) ≤ s.support := by
      intro h
      exact hs (Set.eq_univ_of_univ_subset h)
    let i : JASPrimeSupport × JASLogGrade := (Set.univ, 1)
    obtain ⟨x, hx⟩ := hsurj (RestrictionPacket.packetBasis i)
    have hcoord := congrArg
      (fun w : JASPacketHilbert =>
        (w : (JASPrimeSupport × JASLogGrade) → ℂ) i) hx
    rw [RestrictionPacket.packetOperator_apply, if_neg hnot] at hcoord
    have hone :
        ((RestrictionPacket.packetBasis i : JASPacketHilbert) :
          (JASPrimeSupport × JASLogGrade) → ℂ) i = 1 := by
      simp [RestrictionPacket.packetBasis, i]
    rw [hone] at hcoord
    exact zero_ne_one hcoord
  · intro hs
    have hright :
        RestrictionPacket.packetOperator s ∘L
            RestrictionPacket.packetOperator s.star =
          ContinuousLinearMap.id ℂ JASPacketHilbert := by
      rw [RestrictionPacket.packetOperator_mul, RestrictionPacket.mul_star,
        RestrictionPacket.packetOperator_neutralGrade, hs]
      exact jasSupportProjection_univ
    intro y
    refine ⟨RestrictionPacket.packetOperator s.star y, ?_⟩
    have hy := DFunLike.congr_fun hright y
    simpa using hy

/-- Every actual Gamma insertion has a proper support cut and is therefore non-surjective. -/
theorem jasGammaInsertionPacket_operator_not_surjective
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) :
    ¬ Function.Surjective
      (RestrictionPacket.packetOperator (jasGammaInsertionPacket x p P)) := by
  rw [jasPacketOperator_surjective_iff_support_eq_univ]
  simp only [jasGammaInsertionPacket, jasFiniteSupportComplement]
  intro h
  have hp := Set.ext_iff.mp h p
  simp at hp

/-- The direct prime-support-synchronized source realization: coordinate characters act by the
literal arithmetic RFHM insertion operators. -/
def JASPrimeSupportCoordinateRaisingRepresentation : Prop :=
  ∃ (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes)
      (rho : C(PrimeTorus, ℂ) → JASPacketHilbert →L[ℂ] JASPacketHilbert),
    rho 1 = ContinuousLinearMap.id ℂ JASPacketHilbert ∧
    (∀ f g, rho (f * g) = rho f ∘L rho g) ∧
    rho (torusCharacter (Finsupp.single p (1 : ℤ))) =
      RestrictionPacket.packetOperator (jasGammaInsertionPacket x p P)

/-- Closed route-class no-go: no unital multiplicative `C(PrimeTorus)` action can send a prime
coordinate unit to an actual support-cutting Gamma insertion. -/
theorem not_JASPrimeSupportCoordinateRaisingRepresentation :
    ¬ JASPrimeSupportCoordinateRaisingRepresentation := by
  rintro ⟨x, p, P, rho, hone, hmul, hcoord⟩
  apply jasGammaInsertionPacket_operator_not_surjective x p P
  let up : C(PrimeTorus, ℂ) := torusCharacter (Finsupp.single p (1 : ℤ))
  let um : C(PrimeTorus, ℂ) := torusCharacter (Finsupp.single p (-1 : ℤ))
  have hprod : up * um = 1 := by
    ext z
    rw [show (up * um) z = up z * um z by rfl,
      ← torusCharacter_add_index]
    simp [torusCharacter_zero]
  have hright :
      RestrictionPacket.packetOperator (jasGammaInsertionPacket x p P) ∘L rho um =
        ContinuousLinearMap.id ℂ JASPacketHilbert := by
    rw [← hcoord, ← hmul, hprod, hone]
  intro y
  refine ⟨rho um y, ?_⟩
  have hy := DFunLike.congr_fun hright y
  simpa using hy

end

end RHTower
