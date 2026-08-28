import GaloisForLFunctions.RHTower.JointAncestrySingularMellinPolarization
import GaloisForLFunctions.HTGeometry.ConstitutiveRestrictionFormationHistory

/-!
# Arithmetic restriction-formation history for joint ancestry

The abstract restriction-formation history monoid retains two pieces of data that scalar Mellin
translation forgets: a semilattice support and a reversible grade.  This module specializes that
carrier to the corpus-native Gamma-sewn synchronized-lcm states and BV--Wold transport anomaly.

Finite prime support `P` is encoded by its complement.  Packet multiplication intersects
complements, so adjoining a prime is literal packet multiplication.  The reversible grade is the
negative logarithm of the exact positive arithmetic coefficient.  Consequently:

* one Gamma insertion multiplies the old state packet into the enlarged state packet;
* both orders around every two-prime insertion square give the same packet;
* two BV--Wold transports followed by the determinant-two anomaly equal direct transport;
* all identities survive in the faithful RFHM partial-isometry representation;
* the represented Gamma states remain injective in finite prime support.

This closes the arithmetic-specialization test for the RFHM carrier.  It does not construct a
`C(PrimeTorus)`-source-linear sewing, evade prime-Poisson superselection, identify completed theta
tomography, or prove an Xi landing.
-/

open Complex Real Set

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Prime-support semilattice used by the arithmetic RFHM specialization. -/
abbrev JASPrimeSupport := Set Nat.Primes

/-- Reversible additive log history, written multiplicatively for RFHM composition. -/
abbrev JASLogGrade := Multiplicative ℝ

/-- Arithmetic gains change reversible history but do not relabel prime support. -/
instance : SupportGradeAction JASLogGrade JASPrimeSupport where
  smul _ e := e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_inf _ _ _ := rfl
  smul_bot _ := rfl

@[simp] theorem jasLogGrade_smul_support (g : JASLogGrade) (e : JASPrimeSupport) :
    g • e = e := rfl

/-- Arithmetic packets with prime support and reversible real log history. -/
abbrev JASRestrictionPacket := RestrictionPacket JASPrimeSupport JASLogGrade

/-- Complement encoding turns packet-support intersection into finite-support union. -/
def jasFiniteSupportComplement (P : Finset Nat.Primes) : JASPrimeSupport :=
  {p | p ∉ P}

@[simp] theorem jasFiniteSupportComplement_mem (P : Finset Nat.Primes) (p : Nat.Primes) :
    p ∈ jasFiniteSupportComplement P ↔ p ∉ P := Iff.rfl

/-- A synchronized-lcm state remembers both its exact finite support and coefficient history. -/
def jasGammaStatePacket (x : ℝ) (P : Finset Nat.Primes) : JASRestrictionPacket :=
  ⟨jasFiniteSupportComplement P,
    Multiplicative.ofAdd (-Real.log (gammaSewnSynchronizedLcmWeight x P))⟩

/-- Prime insertion carries its singleton support loss and state-dependent coefficient gain. -/
def jasGammaInsertionPacket
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) : JASRestrictionPacket :=
  ⟨jasFiniteSupportComplement {p},
    Multiplicative.ofAdd (-Real.log (gammaSewnSynchronizedLcmInsertionGain x p P))⟩

/-- Every nonempty synchronized-lcm state has strictly positive weight. -/
theorem jasGammaWeight_pos
    {x : ℝ} (hx : 0 < x) {P : Finset Nat.Primes} (hP : P.Nonempty) :
    0 < gammaSewnSynchronizedLcmWeight x P := by
  rw [gammaSewnSynchronizedLcmWeight, if_neg hP.ne_empty]
  apply div_pos
  · unfold gammaSewnSynchronizedLcmNumerator
    apply Finset.prod_pos
    intro r hr
    exact mul_pos
      (mul_pos
        (gammaSewnMobiusValuationContractionMultiplier_pos x r)
        (div_pos
          (xiTransversePrimeApertureDiskNode_pos 1 r)
          (by linarith [xiTransversePrimeApertureDiskNode_pos 1 r])))
      (sub_pos.mpr (xiMobiusContinuousApertureDiskNode_lt_one hx r))
  · exact sub_pos.mpr (gammaSewnSynchronizedLcmNode_nonneg_lt_one hx hP).2

/-- Exact arithmetic specialization: old state times insertion is the enlarged state packet. -/
theorem jasGammaStatePacket_mul_insertion
    {x : ℝ} (hx : 0 < x) {p : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) :
    jasGammaStatePacket x P * jasGammaInsertionPacket x p P =
      jasGammaStatePacket x (insert p P) := by
  apply RestrictionPacket.ext
  · ext r
    simp [jasGammaStatePacket, jasGammaInsertionPacket,
      jasFiniteSupportComplement, and_comm]
  · change -Real.log (gammaSewnSynchronizedLcmWeight x P) +
        -Real.log (gammaSewnSynchronizedLcmInsertionGain x p P) =
      -Real.log (gammaSewnSynchronizedLcmWeight x (insert p P))
    rw [gammaSewnSynchronizedLcmWeight_insert hx hP hp,
      Real.log_mul
        (jointAncestry_gammaSewnSynchronizedLcmInsertionGain_pos hx p hP).ne'
        (jasGammaWeight_pos hx hP).ne']
    ring

/-- Both future insertion orders agree as support-and-history packets, not only as scalars. -/
theorem jasGammaStatePacket_twoInsertionPaths
    {x : ℝ} (hx : 0 < x) {p q : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) (hq : q ∉ P) (hpq : p ≠ q) :
    (jasGammaStatePacket x P * jasGammaInsertionPacket x p P) *
        jasGammaInsertionPacket x q (insert p P) =
      (jasGammaStatePacket x P * jasGammaInsertionPacket x q P) *
        jasGammaInsertionPacket x p (insert q P) := by
  calc
    (jasGammaStatePacket x P * jasGammaInsertionPacket x p P) *
          jasGammaInsertionPacket x q (insert p P) =
        jasGammaStatePacket x (insert q (insert p P)) := by
      rw [jasGammaStatePacket_mul_insertion hx hP hp,
        jasGammaStatePacket_mul_insertion hx (Finset.insert_nonempty p P)
          (by simp [hq, hpq.symm])]
    _ = jasGammaStatePacket x (insert p (insert q P)) := by
      congr 1
      exact Finset.insert_comm q p P
    _ = (jasGammaStatePacket x P * jasGammaInsertionPacket x q P) *
          jasGammaInsertionPacket x p (insert q P) := by
      rw [jasGammaStatePacket_mul_insertion hx hP hq,
        jasGammaStatePacket_mul_insertion hx (Finset.insert_nonempty q P)
          (by simp [hp, hpq])]

/-- BV--Wold transport packet with unrestricted support and exact reversible log grade. -/
def jasBVTransportPacket
    (a : ℝ) (i j : PrimeDepthBVWoldCell) : JASRestrictionPacket :=
  ⟨Set.univ, Multiplicative.ofAdd (-Real.log (primeDepthBVWoldTransport a i j))⟩

/-- Determinant-two countercurvature packet. -/
def jasBVAnomalyPacket
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) : JASRestrictionPacket :=
  ⟨Set.univ,
    Multiplicative.ofAdd (-Real.log (primeDepthBVWoldGradedDet2Anomaly a i j k))⟩

/-- The graded anomaly makes the BV--Wold transport triangle flat inside RFHM itself. -/
theorem jasBVTransportPacket_triangle
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    (jasBVTransportPacket a i j * jasBVTransportPacket a j k) *
        jasBVAnomalyPacket a i j k = jasBVTransportPacket a i k := by
  apply RestrictionPacket.ext
  · simp [jasBVTransportPacket, jasBVAnomalyPacket]
  · change
      (-Real.log (primeDepthBVWoldTransport a i j) +
          -Real.log (primeDepthBVWoldTransport a j k)) +
        -Real.log (primeDepthBVWoldGradedDet2Anomaly a i j k) =
      -Real.log (primeDepthBVWoldTransport a i k)
    rw [← neg_add, ← Real.log_mul
        (primeDepthBVWoldTransport_pos a i j).ne'
        (primeDepthBVWoldTransport_pos a j k).ne',
      ← neg_add, ← Real.log_mul
        (mul_pos (primeDepthBVWoldTransport_pos a i j)
          (primeDepthBVWoldTransport_pos a j k)).ne'
        (primeDepthBVWoldGradedDet2Anomaly_pos a i j k).ne',
      primeDepthBVWoldTransport_mul_gradedDet2Anomaly]

/-- Packet states are coefficient-independent and faithful in finite prime support. -/
theorem jasGammaStatePacket_injective (x : ℝ) :
    Function.Injective (jasGammaStatePacket x) := by
  intro P Q h
  apply Finset.ext
  intro p
  have hs := congrArg RestrictionPacket.support h
  have hp := Set.ext_iff.mp hs p
  simpa [jasGammaStatePacket, jasFiniteSupportComplement] using not_congr hp

/-- RFHM partial-isometry realization still distinguishes every finite prime support. -/
theorem jasGammaStateOperator_injective (x : ℝ) :
    Function.Injective (fun P : Finset Nat.Primes =>
      RestrictionPacket.packetOperator (jasGammaStatePacket x P)) :=
  RestrictionPacket.packetOperator_injective.comp (jasGammaStatePacket_injective x)

/-- Exact one-prime arithmetic formation law in the faithful operator realization. -/
theorem jasGammaStateOperator_mul_insertion
    {x : ℝ} (hx : 0 < x) {p : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) :
    RestrictionPacket.packetOperator (jasGammaStatePacket x P) ∘L
        RestrictionPacket.packetOperator (jasGammaInsertionPacket x p P) =
      RestrictionPacket.packetOperator (jasGammaStatePacket x (insert p P)) := by
  rw [RestrictionPacket.packetOperator_mul,
    jasGammaStatePacket_mul_insertion hx hP hp]

/-- Two-prime arithmetic path independence survives as an operator identity. -/
theorem jasGammaStateOperator_twoInsertionPaths
    {x : ℝ} (hx : 0 < x) {p q : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) (hq : q ∉ P) (hpq : p ≠ q) :
    (RestrictionPacket.packetOperator (jasGammaStatePacket x P) ∘L
          RestrictionPacket.packetOperator (jasGammaInsertionPacket x p P)) ∘L
        RestrictionPacket.packetOperator (jasGammaInsertionPacket x q (insert p P)) =
      (RestrictionPacket.packetOperator (jasGammaStatePacket x P) ∘L
          RestrictionPacket.packetOperator (jasGammaInsertionPacket x q P)) ∘L
        RestrictionPacket.packetOperator (jasGammaInsertionPacket x p (insert q P)) := by
  simpa only [RestrictionPacket.packetOperator_mul] using
    congrArg RestrictionPacket.packetOperator
      (jasGammaStatePacket_twoInsertionPaths hx hP hp hq hpq)

/-- BV--Wold anomaly-corrected flatness survives in the same partial-isometry carrier. -/
theorem jasBVPacketOperator_triangle
    (a : ℝ) (i j k : PrimeDepthBVWoldCell) :
    (RestrictionPacket.packetOperator (jasBVTransportPacket a i j) ∘L
          RestrictionPacket.packetOperator (jasBVTransportPacket a j k)) ∘L
        RestrictionPacket.packetOperator (jasBVAnomalyPacket a i j k) =
      RestrictionPacket.packetOperator (jasBVTransportPacket a i k) := by
  rw [RestrictionPacket.packetOperator_mul,
    RestrictionPacket.packetOperator_mul, jasBVTransportPacket_triangle]

end

end RHTower
