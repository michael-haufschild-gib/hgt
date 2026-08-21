import GaloisForLFunctions.RHTower.EulerSquarefreeWickRegularOrbitDivisorQuantization
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticCRT
import GaloisForLFunctions.HTGeometry.CofinitePacketCriterion
import GaloisForLFunctions.HTGeometry.PrimeWalshTailConstraint

/-!
# Arbitrary-rank binary gauge tower for the Euler--Wick interaction

The rank-two EWQ packet is not exceptional.  Every finite binary gauge cube carries a canonical
parity-split Krein form.  Literal residue cells are null, translation by the all-negative gauge is
its fundamental symmetry, and a cell crosses its opposite with exact weight `2^r`.  Joining this
crossing to the Euler character-group reflection gives the strictly positive source law

`2^r log(p) z²`.

The full interaction Euler coefficient is the exterior-Fock supertrace
`prod_i (1 - chi_i^k)`.  Independent quadratic gauges kill it at even depths and produce the
maximal packet `2^r` on the all-negative cell at odd depths.  Finally, certified pairwise-distinct
odd-prime gauge families exist at every positive rank, and every factor has an actual negative
quadratic-residue unit.  Thus the unbounded binary tower required by EWQ divisor quantization is a
closed arithmetic source construction rather than a formal relabelling of a fixed rank-two cube.

This module does not assume completed cell landing.  Combined with
`EulerSquarefreeWickRegularOrbitDivisorQuantization`, it isolates proper-marginal completed descent
as the remaining analytic obstruction.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Real Walsh sign of one binary gauge coordinate. -/
def binaryGaugeSign (b : Bool) : ℝ := if b then -1 else 1

/-- Real Walsh character indexed by a gauge subset. -/
def binaryGaugeWalshCharacter {I : Type*} (B : Finset I) (x : I → Bool) : ℝ :=
  ∏ i ∈ B, binaryGaugeSign (x i)

@[simp]
theorem binaryGaugeSign_not (b : Bool) :
    binaryGaugeSign (!b) = -binaryGaugeSign b := by
  cases b <;> norm_num [binaryGaugeSign]

theorem binaryGaugeWalshCharacter_sq {I : Type*} (B : Finset I) (x : I → Bool) :
    binaryGaugeWalshCharacter B x * binaryGaugeWalshCharacter B x = 1 := by
  classical
  rw [binaryGaugeWalshCharacter, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  cases x i <;> norm_num [binaryGaugeSign]

theorem binaryGaugeWalshCharacter_complement {I : Type*}
    (B : Finset I) (x : I → Bool) :
    binaryGaugeWalshCharacter B (fun i => !(x i)) =
      (-1 : ℝ) ^ B.card * binaryGaugeWalshCharacter B x := by
  classical
  simp_rw [binaryGaugeWalshCharacter, binaryGaugeSign_not]
  calc
    (∏ i ∈ B, -binaryGaugeSign (x i)) =
        (∏ _i ∈ B, (-1 : ℝ)) * ∏ i ∈ B, binaryGaugeSign (x i) := by
      rw [← Finset.prod_mul_distrib]
      congr 1
      funext i
      ring
    _ = (-1 : ℝ) ^ B.card * ∏ i ∈ B, binaryGaugeSign (x i) := by simp

/-- Real regular-orbit coordinates of a literal binary residue cell. -/
def binaryGaugePureCoordinates {I : Type*}
    (z : ℝ) (x : I → Bool) (B : Finset I) : ℝ :=
  z * binaryGaugeWalshCharacter B x

/-- Split form whose sign is interaction-grade parity. -/
def binaryGaugeKreinForm {I : Type*} [Fintype I]
    (A B : Finset I → ℝ) : ℝ :=
  ∑ S : Finset I, (-1 : ℝ) ^ S.card * A S * B S

/-- Translation by the all-negative quadratic gauge in Fourier coordinates. -/
def binaryGaugeDoubleNegativeTranslation {I : Type*}
    (A : Finset I → ℝ) (S : Finset I) : ℝ :=
  (-1 : ℝ) ^ S.card * A S

private theorem neg_one_pow_mul_self (n : ℕ) :
    (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
  rw [← pow_add]
  simp [← two_mul]

@[simp]
theorem binaryGaugeDoubleNegativeTranslation_involutive {I : Type*}
    (A : Finset I → ℝ) :
    binaryGaugeDoubleNegativeTranslation (binaryGaugeDoubleNegativeTranslation A) = A := by
  funext S
  rw [binaryGaugeDoubleNegativeTranslation, binaryGaugeDoubleNegativeTranslation]
  calc
    (-1 : ℝ) ^ S.card * ((-1 : ℝ) ^ S.card * A S) =
        ((-1 : ℝ) ^ S.card * (-1 : ℝ) ^ S.card) * A S := by ring
    _ = A S := by rw [neg_one_pow_mul_self]; simp

/-- The all-negative translation is the fundamental symmetry of the parity-split form. -/
theorem binaryGaugeKreinForm_doubleNegativeTranslation_self
    {I : Type*} [Fintype I] (A : Finset I → ℝ) :
    binaryGaugeKreinForm A (binaryGaugeDoubleNegativeTranslation A) =
      ∑ S : Finset I, (A S) ^ 2 := by
  classical
  apply Finset.sum_congr rfl
  intro S hS
  rw [binaryGaugeDoubleNegativeTranslation, pow_two]
  calc
    (-1 : ℝ) ^ S.card * A S * ((-1 : ℝ) ^ S.card * A S) =
        ((-1 : ℝ) ^ S.card * (-1 : ℝ) ^ S.card) * (A S * A S) := by ring
    _ = A S * A S := by rw [neg_one_pow_mul_self]; simp

private theorem sum_neg_one_pow_finset_card_eq_zero
    {I : Type*} [Fintype I] [Nonempty I] :
    (∑ S : Finset I, (-1 : ℝ) ^ S.card) = 0 := by
  classical
  rw [show (Finset.univ : Finset (Finset I)) =
    (Finset.univ : Finset I).powerset by ext S; simp]
  calc
    (∑ S ∈ (Finset.univ : Finset I).powerset, (-1 : ℝ) ^ S.card) =
        ∏ _i ∈ (Finset.univ : Finset I), ((1 : ℝ) - 1) := by
      simpa using (Finset.prod_sub (fun _ : I => (1 : ℝ))
        (fun _ : I => (1 : ℝ)) Finset.univ).symm
    _ = 0 := by simp

/-- All-negative translation sends a literal cell to its bitwise opposite. -/
theorem binaryGaugeDoubleNegativeTranslation_pure
    {I : Type*} (z : ℝ) (x : I → Bool) :
    binaryGaugeDoubleNegativeTranslation (binaryGaugePureCoordinates z x) =
      binaryGaugePureCoordinates z (fun i => !(x i)) := by
  funext S
  rw [binaryGaugeDoubleNegativeTranslation, binaryGaugePureCoordinates,
    binaryGaugePureCoordinates, binaryGaugeWalshCharacter_complement]
  ring

/-- Every literal cell is lightlike for a nontrivial binary gauge tower. -/
theorem binaryGaugeKreinForm_pure_self_eq_zero
    {I : Type*} [Fintype I] [Nonempty I] (z : ℝ) (x : I → Bool) :
    binaryGaugeKreinForm (binaryGaugePureCoordinates z x)
      (binaryGaugePureCoordinates z x) = 0 := by
  classical
  rw [binaryGaugeKreinForm]
  calc
    (∑ S : Finset I,
        (-1 : ℝ) ^ S.card * binaryGaugePureCoordinates z x S *
          binaryGaugePureCoordinates z x S) =
        ∑ S : Finset I, (-1 : ℝ) ^ S.card * z ^ 2 := by
      apply Finset.sum_congr rfl
      intro S hS
      have hsq := binaryGaugeWalshCharacter_sq S x
      simp only [binaryGaugePureCoordinates]
      calc
        (-1 : ℝ) ^ S.card * (z * binaryGaugeWalshCharacter S x) *
            (z * binaryGaugeWalshCharacter S x) =
            (-1 : ℝ) ^ S.card *
              (binaryGaugeWalshCharacter S x * binaryGaugeWalshCharacter S x) * z ^ 2 := by
                ring
        _ = (-1 : ℝ) ^ S.card * z ^ 2 := by rw [hsq]; ring
    _ = 0 := by
      rw [← Finset.sum_mul, sum_neg_one_pow_finset_card_eq_zero]
      simp

/-- Opposite binary residue cells have exact positive crossing `2^r zw`. -/
theorem binaryGaugeKreinForm_pure_opposite
    {I : Type*} [Fintype I] (z w : ℝ) (x : I → Bool) :
    binaryGaugeKreinForm (binaryGaugePureCoordinates z x)
      (binaryGaugePureCoordinates w (fun i => !(x i))) =
        (2 : ℝ) ^ Fintype.card I * z * w := by
  classical
  rw [← binaryGaugeDoubleNegativeTranslation_pure]
  simp only [binaryGaugeKreinForm, binaryGaugeDoubleNegativeTranslation,
    binaryGaugePureCoordinates]
  calc
    (∑ S : Finset I,
        (-1 : ℝ) ^ S.card * (z * binaryGaugeWalshCharacter S x) *
          ((-1 : ℝ) ^ S.card * (w * binaryGaugeWalshCharacter S x))) =
        ∑ _S : Finset I, z * w := by
      apply Finset.sum_congr rfl
      intro S hS
      have hsq := binaryGaugeWalshCharacter_sq S x
      have hparity := neg_one_pow_mul_self S.card
      calc
        (-1 : ℝ) ^ S.card * (z * binaryGaugeWalshCharacter S x) *
            ((-1 : ℝ) ^ S.card * (w * binaryGaugeWalshCharacter S x)) =
            ((-1 : ℝ) ^ S.card * (-1 : ℝ) ^ S.card) *
              (binaryGaugeWalshCharacter S x * binaryGaugeWalshCharacter S x) *
                (z * w) := by ring
        _ = z * w := by rw [hparity, hsq]; simp
    _ = (2 : ℝ) ^ Fintype.card I * z * w := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset]
      ring

/-- Every nonzero literal binary residue event has strictly positive opposite crossing. -/
theorem binaryGaugeKreinForm_pure_doubleNegative_pos
    {I : Type*} [Fintype I] {z : ℝ} (hz : z ≠ 0) (x : I → Bool) :
    0 < binaryGaugeKreinForm (binaryGaugePureCoordinates z x)
      (binaryGaugeDoubleNegativeTranslation (binaryGaugePureCoordinates z x)) := by
  rw [binaryGaugeDoubleNegativeTranslation_pure,
    binaryGaugeKreinForm_pure_opposite]
  have hpow : 0 < (2 : ℝ) ^ Fintype.card I := by positivity
  nlinarith [sq_pos_of_ne_zero hz]

/-- Euler residue seam times arbitrary-rank opposite binary-gauge crossing at one actual prime. -/
def eulerPrimeBinaryGaugeOppositeCrossing
    {I : Type*} [Fintype I]
    (p : Nat.Primes) (z : ℝ) (x : I → Bool) : ℝ :=
  (GaloisForLFunctions.residuePairing
      (MonoidAlgebra.single
        (GaloisForLFunctions.EulerCharGroup.ofNat p.1 p.2.pos) (1 : ℂ))
      (MonoidAlgebra.single
        (GaloisForLFunctions.EulerCharGroup.ofNat p.1 p.2.pos)⁻¹ (1 : ℂ))).re *
    binaryGaugeKreinForm (binaryGaugePureCoordinates z x)
      (binaryGaugeDoubleNegativeTranslation (binaryGaugePureCoordinates z x))

/-- Exact arbitrary-rank reflected source law: `2^r log(p) z²`. -/
theorem eulerPrimeBinaryGaugeOppositeCrossing_eq
    {I : Type*} [Fintype I]
    (p : Nat.Primes) (z : ℝ) (x : I → Bool) :
    eulerPrimeBinaryGaugeOppositeCrossing p z x =
      (2 : ℝ) ^ Fintype.card I * Real.log (p.1 : ℝ) * z ^ 2 := by
  rw [eulerPrimeBinaryGaugeOppositeCrossing,
    GaloisForLFunctions.residuePairing_opposite,
    binaryGaugeDoubleNegativeTranslation_pure,
    binaryGaugeKreinForm_pure_opposite,
    GaloisForLFunctions.EulerCharGroup.logVal_eq_natLog p.2.pos]
  simp only [Complex.ofReal_re]
  ring

/-- Nonzero arbitrary-rank prime packets have strictly positive reflected crossing. -/
theorem eulerPrimeBinaryGaugeOppositeCrossing_pos
    {I : Type*} [Fintype I]
    (p : Nat.Primes) {z : ℝ} (hz : z ≠ 0) (x : I → Bool) :
    0 < eulerPrimeBinaryGaugeOppositeCrossing p z x := by
  rw [eulerPrimeBinaryGaugeOppositeCrossing_eq]
  have hp : (1 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p.1 : ℝ) := Real.log_pos hp
  positivity

/-- The full interaction Euler coefficient of an independent binary gauge family. -/
def binaryGaugeTopEulerDepthCoefficient {I : Type*} [Fintype I]
    (χ : I → ℂ) (k : ℕ) : ℂ :=
  ∏ i, (1 - χ i ^ k)

/-- Exterior-Fock supertrace over all gauge subsets. -/
def binaryGaugeExteriorFockSupertrace {I : Type*} [Fintype I]
    (χ : I → ℂ) (k : ℕ) : ℂ :=
  ∑ B : Finset I, (-1 : ℂ) ^ B.card * ∏ i ∈ B, χ i ^ k

/-- Full binary interaction coefficient is exactly the exterior-Fock supertrace. -/
theorem binaryGaugeTopEulerDepthCoefficient_eq_exteriorFockSupertrace
    {I : Type*} [Fintype I] (χ : I → ℂ) (k : ℕ) :
    binaryGaugeTopEulerDepthCoefficient χ k =
      binaryGaugeExteriorFockSupertrace χ k := by
  classical
  rw [binaryGaugeTopEulerDepthCoefficient, binaryGaugeExteriorFockSupertrace]
  calc
    (∏ i, (1 - χ i ^ k)) =
        ∑ B ∈ (Finset.univ : Finset I).powerset,
          (-1 : ℂ) ^ B.card * ∏ i ∈ B, χ i ^ k := by
      simpa using (Finset.prod_sub (fun _ : I => (1 : ℂ)) (fun i => χ i ^ k)
        Finset.univ)
    _ = ∑ B : Finset I, (-1 : ℂ) ^ B.card * ∏ i ∈ B, χ i ^ k := by
      rw [show (Finset.univ : Finset (Finset I)) =
        (Finset.univ : Finset I).powerset by ext B; simp]

private theorem pow_even_of_sq_one {z : ℂ} (hz : z * z = 1) (n : ℕ) :
    z ^ (2 * n) = 1 := by
  rw [pow_mul, pow_two, hz, one_pow]

private theorem pow_odd_of_sq_one {z : ℂ} (hz : z * z = 1) (n : ℕ) :
    z ^ (2 * n + 1) = z := by
  rw [pow_succ, pow_even_of_sq_one hz]
  simp

/-- Quadratic gauges kill the full interaction coefficient at every even depth. -/
theorem binaryGaugeTopEulerDepthCoefficient_even_eq_zero
    {I : Type*} [Fintype I] [Nonempty I] (χ : I → ℂ)
    (hsq : ∀ i, χ i * χ i = 1) (n : ℕ) :
    binaryGaugeTopEulerDepthCoefficient χ (2 * n) = 0 := by
  classical
  simp_rw [binaryGaugeTopEulerDepthCoefficient, pow_even_of_sq_one (hsq _), sub_self]
  simp

/-- At odd depth the top coefficient is the product of local quadratic defects. -/
theorem binaryGaugeTopEulerDepthCoefficient_odd
    {I : Type*} [Fintype I] (χ : I → ℂ)
    (hsq : ∀ i, χ i * χ i = 1) (n : ℕ) :
    binaryGaugeTopEulerDepthCoefficient χ (2 * n + 1) =
      ∏ i, (1 - χ i) := by
  classical
  simp_rw [binaryGaugeTopEulerDepthCoefficient, pow_odd_of_sq_one (hsq _)]

/-- The all-negative gauge produces the maximal packet `2^r` at every odd depth. -/
theorem binaryGaugeTopEulerDepthCoefficient_allNegative_odd
    {I : Type*} [Fintype I] (n : ℕ) :
    binaryGaugeTopEulerDepthCoefficient (fun _ : I => (-1 : ℂ)) (2 * n + 1) =
      (2 : ℂ) ^ Fintype.card I := by
  classical
  rw [binaryGaugeTopEulerDepthCoefficient_odd]
  · norm_num
  · intro i
    norm_num

/-- Every certified odd prime has a unit in its negative quadratic residue class. -/
theorem exists_oddPrimeQuadraticUnit_eq_neg_one (p : _root_.RHTower.OddPrime) :
    ∃ u : (ZMod p.1)ˣ,
      _root_.RHTower.oddPrimeQuadraticCharacter p (u : ZMod p.1) = -1 := by
  by_contra hnone
  push Not at hnone
  apply _root_.RHTower.oddPrimeQuadraticCharacter_ne_one p
  apply MulChar.ext
  intro u
  rcases _root_.RHTower.oddPrimeQuadraticCharacter_isQuadratic p
    (u : ZMod p.1) with hzero | hone | hneg
  · have hnezero :
        _root_.RHTower.oddPrimeQuadraticCharacter p (u : ZMod p.1) ≠ 0 := by
      exact Units.ne_zero
        ((_root_.RHTower.oddPrimeQuadraticCharacter p).toUnitHom u)
    exact (hnezero hzero).elim
  · simpa using hone
  · exact (hnone u hneg).elim

/-- Canonical chosen all-negative point of an actual independent quadratic residue gauge cube. -/
def oddPrimeFamilyAllNegativeGauge {I : Type*} [Fintype I]
    (P : _root_.RHTower.OddPrimeFamily I) : ∀ i, (ZMod (P.prime i).1)ˣ :=
  fun i => Classical.choose (exists_oddPrimeQuadraticUnit_eq_neg_one (P.prime i))

@[simp]
theorem oddPrimeFamilyAllNegativeGauge_character {I : Type*} [Fintype I]
    (P : _root_.RHTower.OddPrimeFamily I) (i : I) :
    _root_.RHTower.oddPrimeQuadraticCharacter (P.prime i)
        (oddPrimeFamilyAllNegativeGauge P i : ZMod (P.prime i).1) = -1 :=
  Classical.choose_spec (exists_oddPrimeQuadraticUnit_eq_neg_one (P.prime i))

/-- Full interaction coefficient of the actual independent prime-residue gauges. -/
def oddPrimeFamilyTopEulerDepthCoefficient {I : Type*} [Fintype I]
    (P : _root_.RHTower.OddPrimeFamily I)
    (u : ∀ i, (ZMod (P.prime i).1)ˣ) (k : ℕ) : ℂ :=
  binaryGaugeTopEulerDepthCoefficient
    (fun i => _root_.RHTower.oddPrimeQuadraticCharacter (P.prime i)
      (u i : ZMod (P.prime i).1)) k

/-- Actual prime-residue gauges kill the top packet at even depths. -/
theorem oddPrimeFamilyTopEulerDepthCoefficient_even_eq_zero
    {I : Type*} [Fintype I] [Nonempty I]
    (P : _root_.RHTower.OddPrimeFamily I)
    (u : ∀ i, (ZMod (P.prime i).1)ˣ) (n : ℕ) :
    oddPrimeFamilyTopEulerDepthCoefficient P u (2 * n) = 0 := by
  apply binaryGaugeTopEulerDepthCoefficient_even_eq_zero
  intro i
  exact _root_.RHTower.oddPrimeQuadraticCharacter_square_at_nonzero
    (P.prime i) (Units.ne_zero (u i))

/-- Actual all-negative prime-residue gauges realize the maximal odd packet `2^r`. -/
theorem oddPrimeFamilyTopEulerDepthCoefficient_allNegative_odd
    {I : Type*} [Fintype I] (P : _root_.RHTower.OddPrimeFamily I) (n : ℕ) :
    oddPrimeFamilyTopEulerDepthCoefficient P (oddPrimeFamilyAllNegativeGauge P) (2 * n + 1) =
      (2 : ℂ) ^ Fintype.card I := by
  classical
  unfold oddPrimeFamilyTopEulerDepthCoefficient
  convert binaryGaugeTopEulerDepthCoefficient_allNegative_odd (I := I) n using 1
  apply congrArg (fun χ : I → ℂ =>
    binaryGaugeTopEulerDepthCoefficient χ (2 * n + 1))
  funext i
  exact oddPrimeFamilyAllNegativeGauge_character P i

/-- Arbitrarily high finite ranks of pairwise independent odd-prime quadratic gauges exist. -/
theorem exists_oddPrimeFamily_fin_succ (r : ℕ) :
    Nonempty (_root_.RHTower.OddPrimeFamily (Fin (r + 1))) := by
  classical
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hodd : (Set.univ \ ({twoPrime} : Set Nat.Primes)).Infinite :=
    Set.infinite_univ.sdiff (Set.finite_singleton twoPrime)
  obtain ⟨q, hqinj, hqodd⟩ :=
    GaloisForLFunctions.HTGeometry.exists_injective_primes_mem r hodd
  refine ⟨{
    prime := fun i => ⟨q i, (q i).2, ?_⟩
    pairwise_ne := ?_
  }⟩
  · intro htwo
    exact (hqodd i).2 (Subtype.ext htwo)
  · intro i j hij hval
    exact hij (hqinj (Subtype.ext hval))

end

end GaloisForLFunctions.RHTower
