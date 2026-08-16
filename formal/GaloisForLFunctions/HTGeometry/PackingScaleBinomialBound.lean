import GaloisForLFunctions.HTGeometry.BalancedCharacterTransversalityTail
import GaloisForLFunctions.HTGeometry.ReplicaCrowdingCollisionAssembly
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The packing scale against a binomial count, and the crowded-mass ratio

The multiplicity vectors of replica order `r` include the indicator vectors of the `r`-element
subsets of the level set, so their number is at least a binomial coefficient.  Since the packing
scale is inversely proportional to the `d`-th root of that number minus one, it is bounded by an
explicit decreasing function of the binomial coefficient: exponentially small in the level count
divided by the observer dimension.

Dividing the crowding floor by the capture scale turns it into the ratio the card compares against
one: the crowded mass exceeds the capture scale by the `r`-th power of an explicit constant.
-/

open MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The indicator vectors of the `r`-element subsets are multiplicity vectors of order `r`, so the
number of multiplicity vectors is at least a binomial coefficient. -/
theorem choose_le_card_piAntidiag (r : ℕ) :
    (Fintype.card I).choose r ≤ (Finset.univ.piAntidiag r : Finset (I → ℕ)).card := by
  classical
  have hmap : ∀ S ∈ (Finset.univ : Finset I).powersetCard r,
      (fun j => if j ∈ S then 1 else 0) ∈ (Finset.univ.piAntidiag r : Finset (I → ℕ)) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one, hS.2]
  have hinj : ∀ S ∈ (Finset.univ : Finset I).powersetCard r,
      ∀ T ∈ (Finset.univ : Finset I).powersetCard r,
      (fun j => if j ∈ S then 1 else 0) = (fun j => if j ∈ T then 1 else 0) → S = T := by
    intro S _ T _ h
    ext j
    have hj := congrFun h j
    by_cases hS : j ∈ S
    · rw [if_pos hS] at hj
      by_cases hT : j ∈ T
      · simp [hS, hT]
      · rw [if_neg hT] at hj
        exact absurd hj one_ne_zero
    · rw [if_neg hS] at hj
      by_cases hT : j ∈ T
      · rw [if_pos hT] at hj
        exact absurd hj.symm one_ne_zero
      · simp [hS, hT]
  have hcard := Finset.card_le_card_of_injOn (fun S : Finset I => fun j => if j ∈ S then 1 else 0)
    hmap (fun S hS T hT h => hinj S hS T hT h)
  rwa [Finset.card_powersetCard, Finset.card_univ] at hcard

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Corollary A1, equation (8).**  The packing scale is bounded by an explicit decreasing function
of a binomial coefficient in the number of levels, hence is exponentially small when the level count
greatly exceeds the observer dimension. -/
theorem packingScale_le_choose_bound (r : ℕ) {L : ℝ} (hL0 : 0 ≤ L)
    (hlow : 1 < ((Fintype.card I).choose r : ℝ) ^ ((Module.finrank ℝ W : ℝ)⁻¹)) :
    packingScale (W := W) I r L ≤
      r * L / (((Fintype.card I).choose r : ℝ) ^ ((Module.finrank ℝ W : ℝ)⁻¹) - 1) := by
  have hchoose : ((Fintype.card I).choose r : ℝ) ≤
      ((Finset.univ.piAntidiag r : Finset (I → ℕ)).card : ℝ) := by
    exact_mod_cast choose_le_card_piAntidiag (I := I) r
  have hdnn : (0 : ℝ) ≤ (Module.finrank ℝ W : ℝ)⁻¹ := by positivity
  have hroot : ((Fintype.card I).choose r : ℝ) ^ ((Module.finrank ℝ W : ℝ)⁻¹) ≤
      ((Finset.univ.piAntidiag r : Finset (I → ℕ)).card : ℝ) ^
        ((Module.finrank ℝ W : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) hchoose hdnn
  rw [packingScale]
  refine div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- **Corollary C1, equations (19)–(20).**  Multiplying the crowding floor by the filtered mass
factor and dividing by the capture scale gives the ratio the card compares against one: it is at
least the `r`-th power of `9/(4a)` times the floor. -/
theorem crowded_mass_ratio_ge {S₀ a floorTerm crowded : ℝ} (hS₀ : 3 / 4 ≤ S₀)
    (ha : 0 < a) (hfloor : 0 ≤ floorTerm) (hle : floorTerm ≤ crowded) (r : ℕ) :
    (9 / (4 * a)) ^ r * floorTerm ≤ S₀ ^ (2 * r) * crowded / (a / 4) ^ r := by
  have hS₀pos : (0 : ℝ) < S₀ := by linarith
  have hapow : (0 : ℝ) < (a / 4) ^ r := by positivity
  have hstep : ((9 : ℝ) / 16) ^ r * floorTerm ≤ S₀ ^ (2 * r) * crowded := by
    have h1 : ((9 : ℝ) / 16) ^ r ≤ S₀ ^ (2 * r) := by
      rw [two_mul, pow_add, ← mul_pow]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith) r
    have h2 : (0 : ℝ) ≤ ((9 : ℝ) / 16) ^ r := by positivity
    nlinarith [pow_nonneg hS₀pos.le (2 * r)]
  rw [le_div_iff₀ hapow]
  have hcalc : (9 / (4 * a)) ^ r * floorTerm * (a / 4) ^ r =
      ((9 : ℝ) / 16) ^ r * floorTerm := by
    rw [mul_comm ((9 / (4 * a)) ^ r) floorTerm, mul_assoc, ← mul_pow]
    rw [show (9 : ℝ) / (4 * a) * (a / 4) = 9 / 16 by field_simp; ring]
    ring
  rw [hcalc]
  exact hstep

/-! ## The fixed-shell path-local generator count -/

/-- The generator index of the fixed-shell path-local ensemble on an open chain of `n` qubits: one
Pauli axis at each site, and a pair of axes on each nearest-neighbour edge. -/
abbrev PathLocalGeneratorIndex (n : ℕ) : Type :=
  (Fin n × Fin 3) ⊕ (Fin (n - 1) × Fin 3 × Fin 3)

/-- **The card's `m = 12n − 9`.**  The open chain of `n ≥ 1` qubits carries `3n` one-site and
`9(n−1)` nearest-neighbour two-site Pauli generators. -/
theorem card_pathLocalGeneratorIndex (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (PathLocalGeneratorIndex n) = 12 * n - 9 := by
  have hcard : Fintype.card (PathLocalGeneratorIndex n) = 3 * n + 9 * (n - 1) := by
    simp [PathLocalGeneratorIndex, Fintype.card_sum, Fintype.card_prod]
    ring
  rw [hcard]
  omega

/-- **The card's `D = 2^n`.**  The computational basis of `n` qubits has `2^n` levels. -/
theorem card_qubitBasis (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

end GaloisForLFunctions.HTGeometry
