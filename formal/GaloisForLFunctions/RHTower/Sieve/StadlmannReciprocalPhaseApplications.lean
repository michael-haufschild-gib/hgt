import GaloisForLFunctions.RHTower.Sieve.KloostermanSecondMoment
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaNine

/-!
# Stadlmann reciprocal-phase applications

The one-modulus reciprocal phase in the exponential-sum lemma of Stadlmann's bounded-gaps paper
is a zero-frequency Kloosterman sum on a complete reduced residue system.  Unit inversion also
identifies it exactly with the corpus's Chen--Gupta--Li Ramanujan sum.  At odd prime modulus this
is the exceptional quadratic Jacobi factor from Bondarenko--Heap.
-/

open scoped BigOperators

noncomputable section

namespace RHTower.Sieve

/-- Explicit equivalence between unit residues and residues certified to be units. -/
def zmodUnitsEquivIsUnit (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {a : ZMod q // IsUnit a} where
  toFun x := ⟨x, x.isUnit⟩
  invFun x := x.2.unit
  left_inv x := Units.ext x.isUnit.unit_spec
  right_inv x := Subtype.ext x.2.unit_spec

/-- Complete one-modulus reciprocal phase from Stadlmann's exponential-sum input. -/
def stadlmannReciprocalPhaseSum (q : ℕ) [NeZero q] (c : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ,
    ZMod.stdAddChar (c * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- The complete reciprocal phase is the zero-frequency Kloosterman sum. -/
theorem stadlmannReciprocalPhaseSum_eq_kloosterman
    (q : ℕ) [NeZero q] (c : ZMod q) :
    stadlmannReciprocalPhaseSum q c = kloostermanSum q 0 c := by
  simp [stadlmannReciprocalPhaseSum, kloostermanSum, kloostermanPhase]

/-- Inversion permutes unit residues, converting reciprocal phase to direct Ramanujan phase. -/
theorem stadlmannReciprocalPhaseSum_eq_direct
    (q : ℕ) [NeZero q] (c : ZMod q) :
    stadlmannReciprocalPhaseSum q c =
      ∑ x : (ZMod q)ˣ, ZMod.stdAddChar (c * (x : ZMod q)) := by
  let e := kloostermanUnitInvEquiv q
  change (∑ x : (ZMod q)ˣ, ZMod.stdAddChar (c * ((e x : (ZMod q)ˣ) : ZMod q))) = _
  exact e.sum_comp (fun x : (ZMod q)ˣ => ZMod.stdAddChar (c * (x : ZMod q)))

/-- The complete reciprocal phase is exactly the Chen--Gupta--Li Ramanujan coefficient. -/
theorem stadlmannReciprocalPhaseSum_eq_cglRamanujan
    (q : ℕ) [NeZero q] (c : ZMod q) :
    stadlmannReciprocalPhaseSum q c =
      RHTower.cglRamanujanAdditiveSum
        ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ c := by
  let e := zmodUnitsEquivIsUnit q
  letI : Fintype {a : ZMod q // IsUnit a} := Fintype.ofEquiv (ZMod q)ˣ e
  rw [stadlmannReciprocalPhaseSum_eq_direct]
  unfold RHTower.cglRamanujanAdditiveSum
  calc
    (∑ x : (ZMod q)ˣ, ZMod.stdAddChar (c * (x : ZMod q))) =
        ∑ a : {a : ZMod q // IsUnit a}, ZMod.stdAddChar (c * a.1) := by
      exact e.sum_comp
        (fun a : {a : ZMod q // IsUnit a} => ZMod.stdAddChar (c * a.1))
    _ = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ZMod.stdAddChar (c * a) := by
      exact (Finset.sum_subtype ((Finset.univ : Finset (ZMod q)).filter IsUnit)
        (fun a => by simp) (fun a => ZMod.stdAddChar (c * a))).symm
    _ = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ZMod.stdAddChar (a * c) := by
      apply Finset.sum_congr rfl
      intro a ha
      congr 1
      ring

/-- Zero reciprocal frequency has full reduced-residue mass. -/
@[simp] theorem stadlmannReciprocalPhaseSum_zero
    (q : ℕ) [NeZero q] :
    stadlmannReciprocalPhaseSum q 0 = (Nat.totient q : ℂ) := by
  rw [stadlmannReciprocalPhaseSum_eq_kloosterman, kloostermanSum_zero_zero]

/-- Elementary pointwise bound inherited from the Kloosterman representation. -/
theorem norm_stadlmannReciprocalPhaseSum_le_totient
    (q : ℕ) [NeZero q] (c : ZMod q) :
    ‖stadlmannReciprocalPhaseSum q c‖ ≤ (Nat.totient q : ℝ) := by
  rw [stadlmannReciprocalPhaseSum_eq_kloosterman]
  exact norm_kloostermanSum_le_totient q 0 c

/-- Conjugating a reciprocal phase negates its additive frequency. -/
theorem star_stadlmannReciprocalPhaseSum
    (q : ℕ) [NeZero q] (c : ZMod q) :
    star (stadlmannReciprocalPhaseSum q c) =
      stadlmannReciprocalPhaseSum q (-c) := by
  rw [stadlmannReciprocalPhaseSum_eq_kloosterman,
    stadlmannReciprocalPhaseSum_eq_kloosterman]
  simpa using star_kloostermanSum q 0 c

/-- Exact additive-frequency second moment of Stadlmann's complete reciprocal phase. -/
theorem sum_normSq_stadlmannReciprocalPhaseSum
    (q : ℕ) [NeZero q] :
    ∑ c : ZMod q, Complex.normSq (stadlmannReciprocalPhaseSum q c) =
      (q : ℝ) * Nat.totient q := by
  simp_rw [stadlmannReciprocalPhaseSum_eq_kloosterman]
  exact sum_normSq_kloostermanSum q 0

/-- Pointwise Ramanujan bound transferred into the Chen--Gupta--Li API. -/
theorem norm_cglRamanujanAdditiveSum_le_totient
    (q : ℕ) [NeZero q] (c : ZMod q) :
    ‖RHTower.cglRamanujanAdditiveSum
        ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ c‖ ≤
      (Nat.totient q : ℝ) := by
  rw [← stadlmannReciprocalPhaseSum_eq_cglRamanujan]
  exact norm_stadlmannReciprocalPhaseSum_le_totient q c

/-- Exact Ramanujan-frequency second moment transferred into the Chen--Gupta--Li API. -/
theorem sum_normSq_cglRamanujanAdditiveSum
    (q : ℕ) [NeZero q] :
    ∑ c : ZMod q, Complex.normSq
        (RHTower.cglRamanujanAdditiveSum
          ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ c) =
      (q : ℝ) * Nat.totient q := by
  simp_rw [← stadlmannReciprocalPhaseSum_eq_cglRamanujan]
  exact sum_normSq_stadlmannReciprocalPhaseSum q

/-- At an odd prime, the CGL coefficient is Bondarenko--Heap's prime Ramanujan factor. -/
theorem cglRamanujanAdditiveSum_eq_oddPrimeRamanujan
    (p : RHTower.OddPrime) (c : ZMod p.1) :
    RHTower.cglRamanujanAdditiveSum ⟨p.1, p.2.1.pos⟩ c =
      RHTower.oddPrimeRamanujanAdditiveSum p c := by
  unfold RHTower.cglRamanujanAdditiveSum RHTower.oddPrimeRamanujanAdditiveSum
  have hset :
      (Finset.univ : Finset (ZMod p.1)).filter IsUnit =
        Finset.univ.erase 0 := by
    ext a
    simp [isUnit_iff_ne_zero]
  rw [hset]

/-- Stadlmann's complete reciprocal phase is the prime Ramanujan factor. -/
theorem stadlmannReciprocalPhaseSum_eq_oddPrimeRamanujan
    (p : RHTower.OddPrime) (c : ZMod p.1) :
    stadlmannReciprocalPhaseSum p.1 c =
      RHTower.oddPrimeRamanujanAdditiveSum p c := by
  rw [stadlmannReciprocalPhaseSum_eq_cglRamanujan,
    cglRamanujanAdditiveSum_eq_oddPrimeRamanujan]

/-- Stadlmann's reciprocal phase is Bondarenko--Heap's exceptional quadratic Jacobi factor. -/
theorem stadlmannReciprocalPhaseSum_eq_quadraticRamanujanLocalSum
    (p : RHTower.OddPrime) (c : ZMod p.1) :
    stadlmannReciprocalPhaseSum p.1 c =
      RHTower.oddPrimeQuadraticRamanujanLocalSum p c := by
  rw [stadlmannReciprocalPhaseSum_eq_oddPrimeRamanujan]
  exact (RHTower.oddPrime_quadraticRamanujanLocalSum_eq_additive p c).symm

/-- The source's inverse-incidence shift has exactly the Bondarenko--Heap two-valued law. -/
theorem stadlmannReciprocalPhaseSum_unitInverse
    (p : RHTower.OddPrime) (r : ZMod p.1) (m : (ZMod p.1)ˣ) :
    stadlmannReciprocalPhaseSum p.1
        (RHTower.unitInverseIncidenceClass p.1 r m) =
      if r = 0 then (p.1 : ℂ) - 1 else -1 := by
  rw [stadlmannReciprocalPhaseSum_eq_quadraticRamanujanLocalSum]
  exact RHTower.oddPrime_quadraticRamanujanLocalSum_unitInverse p r m

end RHTower.Sieve
