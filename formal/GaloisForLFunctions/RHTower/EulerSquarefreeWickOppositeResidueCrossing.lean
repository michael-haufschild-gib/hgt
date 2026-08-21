import GaloisForLFunctions.RHTower.EulerSquarefreeWickRegularOrbitFlux
import GaloisForLFunctions.RHTower.EulerCharacterGroupCompletion

/-!
# Opposite-residue crossing for the Euler--Wick regular orbit

The regular-orbit landing has a canonical fundamental symmetry: translation by the unique gauge
element `(-1,-1)`.  In Fourier coordinates it fixes vacuum and joint interaction, while negating
both marginal sectors.  Composing the split residue form with this symmetry produces the ordinary
positive sum of four squares.  Thus a literal source event is lightlike before translation but
crosses its opposite residue cell with strictly positive value.

This finite gauge crossing joins canonically to the Euler character group completion.  Source
reflection pairs a positive prime mode with its inverse mode, whose residue seam is exactly
`log p`.  Their product is the local law

`oppositeCrossing(p,z) = 4 log(p) z² > 0`.

Finite sums therefore form a strict positive source energy as soon as one actual prime amplitude
is nonzero.  This supplies a source-native orientation absent from the scalar Xi landing; it does
not by itself assert transport of that orientation to the completed Xi divisor.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Translation by the unique residue gauge which is negative in both quadratic legs. -/
def quadraticResidueDoubleNegativeTranslation
    {K : Type*} [Ring K]
    (A : QuadraticResidueFourierCoordinates K) : QuadraticResidueFourierCoordinates K where
  vacuum := A.vacuum
  fst := -A.fst
  snd := -A.snd
  joint := A.joint

@[simp]
theorem quadraticResidueDoubleNegativeTranslation_involutive
    {K : Type*} [Ring K] (A : QuadraticResidueFourierCoordinates K) :
    quadraticResidueDoubleNegativeTranslation
      (quadraticResidueDoubleNegativeTranslation A) = A := by
  ext <;> simp [quadraticResidueDoubleNegativeTranslation]

/-- At odd depth, multiplication by `(-1,-1)` on actual units is exactly the fundamental
symmetry on Fourier sectors. -/
theorem quadraticResidueGaugeDepthCoordinates_doubleNegative_odd
    (z : ℂ) (n : ℕ) (w : QuadraticResidueGaugeSpace) :
    quadraticResidueGaugeDepthCoordinates z (2 * n + 1) (-w.1, -w.2) =
      quadraticResidueDoubleNegativeTranslation
        (quadraticResidueGaugeDepthCoordinates z (2 * n + 1) w) := by
  have hthree : quadraticCharacterThreeUnit (-w.1) =
      -quadraticCharacterThreeUnit w.1 := by
    rw [show -w.1 = (-1) * w.1 by simp, quadraticCharacterThreeUnit]
    rw [Units.val_mul, map_mul]
    change quadraticCharacterThreeUnit (-1) * quadraticCharacterThreeUnit w.1 = _
    rw [quadraticCharacterThreeUnit_neg_one]
    ring
  have hfour : quadraticCharacterFourUnit (-w.2) =
      -quadraticCharacterFourUnit w.2 := by
    rw [show -w.2 = (-1) * w.2 by simp, quadraticCharacterFourUnit]
    rw [Units.val_mul, map_mul]
    change quadraticCharacterFourUnit (-1) * quadraticCharacterFourUnit w.2 = _
    rw [quadraticCharacterFourUnit_neg_one]
    ring
  have hodd : Odd (2 * n + 1) := ⟨n, by omega⟩
  ext <;>
    simp [quadraticResidueGaugeDepthCoordinates,
      quadraticResidueDoubleNegativeTranslation, hthree, hfour,
      hodd.neg_pow, mul_pow]

/-- Double-negative translation is the fundamental symmetry of the split residue form. -/
theorem quadraticResidueKreinForm_doubleNegativeTranslation_self
    (A : QuadraticResidueFourierCoordinates ℝ) :
    quadraticResidueKreinForm A (quadraticResidueDoubleNegativeTranslation A) =
      A.vacuum ^ 2 + A.fst ^ 2 + A.snd ^ 2 + A.joint ^ 2 := by
  simp [quadraticResidueKreinForm, quadraticResidueDoubleNegativeTranslation]
  ring

/-- Opposite point of the two-cell sign gauge. -/
def finTwoOpposite (x : Fin 2) : Fin 2 :=
  if x = 0 then 1 else 0

@[simp]
theorem finTwoAnchoredSign_opposite (x : Fin 2) :
    finTwoAnchoredSign (finTwoOpposite x) = -finTwoAnchoredSign x := by
  fin_cases x <;> simp [finTwoOpposite, finTwoAnchoredSign]

/-- Double-negative translation moves a literal packet to the opposite residue cell. -/
theorem quadraticResidueDoubleNegativeTranslation_pureDepth
    (z : ℝ) (x y : Fin 2) :
    quadraticResidueDoubleNegativeTranslation
        (quadraticResiduePureRealDepthCoordinates z x y) =
      quadraticResiduePureRealDepthCoordinates z (finTwoOpposite x) (finTwoOpposite y) := by
  ext <;>
    simp [quadraticResidueDoubleNegativeTranslation,
      quadraticResiduePureRealDepthCoordinates, finTwoAnchoredSign_opposite]

/-- Opposite residue cells have exact positive crossing `4zw`. -/
theorem quadraticResidueKreinForm_pureDepth_opposite
    (z w : ℝ) (x y : Fin 2) :
    quadraticResidueKreinForm (quadraticResiduePureRealDepthCoordinates z x y)
      (quadraticResiduePureRealDepthCoordinates w (finTwoOpposite x) (finTwoOpposite y)) =
        4 * z * w := by
  fin_cases x <;> fin_cases y <;>
    simp [quadraticResidueKreinForm, quadraticResiduePureRealDepthCoordinates,
      finTwoOpposite, finTwoAnchoredSign] <;> ring

/-- A nonzero literal residue event has strictly positive double-negative crossing. -/
theorem quadraticResidueKreinForm_pureDepth_doubleNegative_pos
    {z : ℝ} (hz : z ≠ 0) (x y : Fin 2) :
    0 < quadraticResidueKreinForm (quadraticResiduePureRealDepthCoordinates z x y)
      (quadraticResidueDoubleNegativeTranslation
        (quadraticResiduePureRealDepthCoordinates z x y)) := by
  rw [quadraticResidueDoubleNegativeTranslation_pureDepth,
    quadraticResidueKreinForm_pureDepth_opposite]
  nlinarith [sq_pos_of_ne_zero hz]

/-- Euler residue seam times the double-negative residue crossing at one actual prime. -/
def eulerPrimeQuadraticResidueOppositeCrossing
    (p : Nat.Primes) (z : ℝ) (x y : Fin 2) : ℝ :=
  (GaloisForLFunctions.residuePairing
      (MonoidAlgebra.single
        (GaloisForLFunctions.EulerCharGroup.ofNat p.1 p.2.pos) (1 : ℂ))
      (MonoidAlgebra.single
        (GaloisForLFunctions.EulerCharGroup.ofNat p.1 p.2.pos)⁻¹ (1 : ℂ))).re *
    quadraticResidueKreinForm (quadraticResiduePureRealDepthCoordinates z x y)
      (quadraticResidueDoubleNegativeTranslation
        (quadraticResiduePureRealDepthCoordinates z x y))

/-- Exact local reflected-crossing law: prime scale times positive residue norm. -/
theorem eulerPrimeQuadraticResidueOppositeCrossing_eq
    (p : Nat.Primes) (z : ℝ) (x y : Fin 2) :
    eulerPrimeQuadraticResidueOppositeCrossing p z x y =
      4 * Real.log (p.1 : ℝ) * z ^ 2 := by
  rw [eulerPrimeQuadraticResidueOppositeCrossing,
    GaloisForLFunctions.residuePairing_opposite,
    quadraticResidueDoubleNegativeTranslation_pureDepth,
    quadraticResidueKreinForm_pureDepth_opposite,
    GaloisForLFunctions.EulerCharGroup.logVal_eq_natLog p.2.pos]
  change Real.log (p.1 : ℝ) * (4 * z * z) = 4 * Real.log (p.1 : ℝ) * z ^ 2
  ring

/-- Every nonzero actual prime packet has strictly positive reflected crossing. -/
theorem eulerPrimeQuadraticResidueOppositeCrossing_pos
    (p : Nat.Primes) {z : ℝ} (hz : z ≠ 0) (x y : Fin 2) :
    0 < eulerPrimeQuadraticResidueOppositeCrossing p z x y := by
  rw [eulerPrimeQuadraticResidueOppositeCrossing_eq]
  have hp : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp
  positivity

/-- Reflected crossing is nonnegative even when the packet amplitude vanishes. -/
theorem eulerPrimeQuadraticResidueOppositeCrossing_nonneg
    (p : Nat.Primes) (z : ℝ) (x y : Fin 2) :
    0 ≤ eulerPrimeQuadraticResidueOppositeCrossing p z x y := by
  rw [eulerPrimeQuadraticResidueOppositeCrossing_eq]
  have hp : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp
  positivity

/-- Finite source energy obtained by summing the canonical opposite crossing over actual primes. -/
def eulerPrimeQuadraticResidueOppositeCrossingEnergy
    (P : Finset Nat.Primes) (z : Nat.Primes → ℝ)
    (x y : Nat.Primes → Fin 2) : ℝ :=
  ∑ p ∈ P, eulerPrimeQuadraticResidueOppositeCrossing p (z p) (x p) (y p)

/-- Exact sum-of-squares form of the finite opposite-residue source energy. -/
theorem eulerPrimeQuadraticResidueOppositeCrossingEnergy_eq
    (P : Finset Nat.Primes) (z : Nat.Primes → ℝ)
    (x y : Nat.Primes → Fin 2) :
    eulerPrimeQuadraticResidueOppositeCrossingEnergy P z x y =
      ∑ p ∈ P, 4 * Real.log (p.1 : ℝ) * (z p) ^ 2 := by
  simp_rw [eulerPrimeQuadraticResidueOppositeCrossingEnergy,
    eulerPrimeQuadraticResidueOppositeCrossing_eq]

/-- Finite opposite-residue energy is always nonnegative. -/
theorem eulerPrimeQuadraticResidueOppositeCrossingEnergy_nonneg
    (P : Finset Nat.Primes) (z : Nat.Primes → ℝ)
    (x y : Nat.Primes → Fin 2) :
    0 ≤ eulerPrimeQuadraticResidueOppositeCrossingEnergy P z x y := by
  apply Finset.sum_nonneg
  intro p hp
  exact eulerPrimeQuadraticResidueOppositeCrossing_nonneg p (z p) (x p) (y p)

/-- One nonzero actual prime event makes the finite opposite-residue energy strictly positive. -/
theorem eulerPrimeQuadraticResidueOppositeCrossingEnergy_pos_of_mem_ne
    {P : Finset Nat.Primes} {z : Nat.Primes → ℝ}
    (x y : Nat.Primes → Fin 2) {p : Nat.Primes} (hp : p ∈ P) (hz : z p ≠ 0) :
    0 < eulerPrimeQuadraticResidueOppositeCrossingEnergy P z x y := by
  apply Finset.sum_pos'
  · intro q hq
    exact eulerPrimeQuadraticResidueOppositeCrossing_nonneg q (z q) (x q) (y q)
  · exact ⟨p, hp, eulerPrimeQuadraticResidueOppositeCrossing_pos p hz (x p) (y p)⟩

end

end GaloisForLFunctions.RHTower
