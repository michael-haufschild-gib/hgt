import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTruncatedValuationLadderIsExactlySolvable
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheValuationChainOfFinitelyManyPrimesHasGapTwoLogTwo

/-!
# The finite prime chain has the spectrum of the integers

On the box of `Q`-smooth numbers with exponents at most `J`, with weights `1/a` and the Dirichlet
form of all its prime-power edges (`boxEnergy`), the product modes
`Ψ_m(a) = Π_{p<Q} ψ_{p, v_p(m)}(v_p(a))` (`boxMode`), indexed by the box itself, are orthogonal
eigenvectors with eigenvalues `λ(m) = Σ_{p<Q} λ_{p, v_p(m)}` (`boxEig`); as `J → ∞`,
`λ(m) → log m + Σ_{p ∣ m} log p/(p − 1)`.

* **The spectral inequality** (`boxSpectral`): for every real `T` and every `f`,
  `T ‖f‖² − Σ_{λ(m) < T} (T − λ(m)) ⟨f, Ψ_m⟩²/‖Ψ_m‖² ≤ E(f)`. By induction over the primes:
  expanding `f(Q^j a) = Σ_k c_k(a) ψ_k(j)` in the eigenbasis of the top ladder, the energy splits as
  `Σ_k ‖ψ_k‖² (E_Q(c_k) + λ_k ‖c_k‖²)`, and `⟨f, Ψ_{Q^k m}⟩ = ‖ψ_k‖² ⟨c_k, Ψ_m⟩`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. Inner product, modes and eigenvalues of a box -/

/-- The harmonic inner product on the box. -/
def boxInner (J Q : ℕ) (f g : ℕ → ℝ) : ℝ := ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (f a * g a)

/-- The product mode `Ψ_m(a) = Π_{p<Q} ψ_{p, v_p(m)}(v_p(a))`. -/
def boxMode (J Q m a : ℕ) : ℝ :=
  ∏ p ∈ (range Q).filter Nat.Prime, ladMode p J (m.factorization p) (a.factorization p)

/-- The eigenvalue `λ(m) = Σ_{p<Q} λ_{p, v_p(m)}`. -/
def boxEig (J Q m : ℕ) : ℝ := ∑ p ∈ (range Q).filter Nat.Prime, ladEig p J (m.factorization p)

/-- The spectral penalty `Σ_{λ(m) < T} (T − λ(m)) ⟨f, Ψ_m⟩²/‖Ψ_m‖²`. -/
def boxPenalty (J Q : ℕ) (T : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ smoothBox J Q, if boxEig J Q m < T then
    (T - boxEig J Q m) * (boxInner J Q f (boxMode J Q m) ^ 2 /
      boxInner J Q (boxMode J Q m) (boxMode J Q m)) else 0

theorem filter_prime_range_succ {Q : ℕ} (hQ : Q.Prime) :
    (range (Q + 1)).filter Nat.Prime = insert Q ((range Q).filter Nat.Prime) := by
  rw [range_add_one, filter_insert, if_pos hQ]

theorem filter_prime_range_succ_of_not {Q : ℕ} (hQ : ¬ Q.Prime) :
    (range (Q + 1)).filter Nat.Prime = (range Q).filter Nat.Prime := by
  rw [range_add_one, filter_insert, if_neg hQ]

theorem smoothBox_succ_of_not {J Q : ℕ} (hQ : ¬ Q.Prime) : smoothBox J (Q + 1) = smoothBox J Q := by
  simp [smoothBox, hQ]

theorem ne_zero_of_mem_smoothBox {J Q a : ℕ} (ha : a ∈ smoothBox J Q) : a ≠ 0 := by
  have := (mem_smoothBox.mp ha).1; omega

theorem factorization_pow_mul_self {Q j a : ℕ} (hQ : Q.Prime) (ha : a ≠ 0) (hQa : ¬ Q ∣ a) :
    (Q ^ j * a).factorization Q = j := by
  rw [Nat.factorization_mul (pow_ne_zero _ hQ.ne_zero) ha, Finsupp.add_apply,
    hQ.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hQa,
    add_zero]

theorem factorization_pow_mul_ne {Q j a p : ℕ} (hQ : Q.Prime) (ha : a ≠ 0) (hpQ : p ≠ Q) :
    (Q ^ j * a).factorization p = a.factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero _ hQ.ne_zero) ha, Finsupp.add_apply,
    hQ.factorization_pow, Finsupp.single_eq_of_ne hpQ, zero_add]

theorem boxMode_succ {J Q m a k j : ℕ} (hQ : Q.Prime) (hm : m ∈ smoothBox J Q)
    (ha : a ∈ smoothBox J Q) :
    boxMode J (Q + 1) (Q ^ k * m) (Q ^ j * a) = ladMode Q J k j * boxMode J Q m a := by
  rw [boxMode, filter_prime_range_succ hQ, prod_insert (by simp),
    factorization_pow_mul_self hQ (ne_zero_of_mem_smoothBox hm) (not_dvd_of_mem_smoothBox hm hQ),
    factorization_pow_mul_self hQ (ne_zero_of_mem_smoothBox ha) (not_dvd_of_mem_smoothBox ha hQ),
    boxMode]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have hpQ : p ≠ Q := by have := mem_range.mp (mem_filter.mp hp).1; omega
  rw [factorization_pow_mul_ne hQ (ne_zero_of_mem_smoothBox hm) hpQ,
    factorization_pow_mul_ne hQ (ne_zero_of_mem_smoothBox ha) hpQ]

theorem boxEig_succ {J Q m k : ℕ} (hQ : Q.Prime) (hm : m ∈ smoothBox J Q) :
    boxEig J (Q + 1) (Q ^ k * m) = ladEig Q J k + boxEig J Q m := by
  rw [boxEig, filter_prime_range_succ hQ, sum_insert (by simp),
    factorization_pow_mul_self hQ (ne_zero_of_mem_smoothBox hm) (not_dvd_of_mem_smoothBox hm hQ),
    boxEig]
  congr 1
  refine sum_congr rfl fun p hp => ?_
  have hpQ : p ≠ Q := by have := mem_range.mp (mem_filter.mp hp).1; omega
  rw [factorization_pow_mul_ne hQ (ne_zero_of_mem_smoothBox hm) hpQ]

/-! ### 2. The levels of the top prime -/

/-- The `Q`-slice `j ↦ f(Q^j a)`. -/
def boxSlice (Q : ℕ) (f : ℕ → ℝ) (a : ℕ) (j : ℕ) : ℝ := f (Q ^ j * a)

theorem one_div_pow_mul_cast {Q j a : ℕ} :
    1 / ((Q ^ j * a : ℕ) : ℝ) = 1 / (a : ℝ) * ladWeight Q j := by
  rw [ladWeight]; push_cast; rw [one_div_pow, one_div_mul_one_div, mul_comm]

theorem boxInner_succ {J Q : ℕ} (hQ : Q.Prime) (f g : ℕ → ℝ) :
    boxInner J (Q + 1) f g =
      ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * ladInner Q J (boxSlice Q f a) (boxSlice Q g a) := by
  rw [boxInner, sum_smoothBox_succ hQ, sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [ladInner, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [one_div_pow_mul_cast, boxSlice, boxSlice]
  ring

theorem ladderEnergy_mul_pow {p Q u J j : ℕ} (f : ℕ → ℝ) :
    ladderEnergy p (Q ^ j * u) J f = ladWeight Q j * ladderEnergy p u J (fun n => f (Q ^ j * n)) := by
  rw [ladderEnergy, ladderEnergy, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i' _ => ?_
  split_ifs
  · rw [show Q ^ j * u * p ^ i' = Q ^ j * (u * p ^ i') by ring,
      show Q ^ j * u * p ^ i = Q ^ j * (u * p ^ i) by ring, one_div_pow_mul_cast.symm ▸ rfl]
    rw [show ((Q ^ j * (u * p ^ i') : ℕ) : ℝ) = (Q : ℝ) ^ j * ((u * p ^ i' : ℕ) : ℝ) by push_cast; ring,
      ladWeight]
    have hQ : ((Q : ℝ) ^ j) ≠ 0 ∨ ((Q : ℝ) ^ j) = 0 := em _
    rcases hQ with hQ | hQ
    · field_simp
    · rw [hQ]; simp [one_div_pow, ← inv_pow, hQ]
  · rw [mul_zero]

theorem ladderEnergy_eq_ladForm (p u J : ℕ) (f : ℕ → ℝ) :
    ladderEnergy p u J f = 1 / (u : ℝ) * ladForm p J (boxSlice p f u) (boxSlice p f u) := by
  rw [ladderEnergy, ladForm, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  split_ifs
  · rw [boxSlice, boxSlice, mul_comm (p ^ j) u, mul_comm (p ^ i) u, ladWeight]
    push_cast
    rw [one_div_pow, div_eq_mul_one_div (Real.log p), ← one_div_mul_one_div]
    ring
  · rw [mul_zero]

/-- The box energy splits into the top ladders and the levels. -/
theorem boxEnergy_succ {J Q : ℕ} (hQ : Q.Prime) (f : ℕ → ℝ) :
    boxEnergy J (Q + 1) f = ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) *
        ladForm Q J (boxSlice Q f a) (boxSlice Q f a) +
      ∑ j ∈ range (J + 1), ladWeight Q j * boxEnergy J Q (fun n => f (Q ^ j * n)) := by
  rw [boxEnergy, filter_prime_range_succ hQ, sum_insert (by simp)]
  congr 1
  · rw [sum_filter, sum_smoothBox_succ hQ, Finset.sum_range_succ']
    simp only [pow_zero, one_mul]
    have hzero : ∑ j ∈ range J, ∑ a ∈ smoothBox J Q,
        (if ¬ Q ∣ Q ^ (j + 1) * a then ladderEnergy Q (Q ^ (j + 1) * a) J f else 0) = 0 :=
      sum_eq_zero fun j _ => sum_eq_zero fun a _ => by
        rw [if_neg (not_not.mpr (Dvd.dvd.mul_right (dvd_pow_self Q (Nat.succ_ne_zero j)) a))]
    rw [hzero, zero_add]
    refine sum_congr rfl fun a ha => ?_
    rw [if_pos (not_dvd_of_mem_smoothBox ha hQ), ladderEnergy_eq_ladForm]
    congr 2 <;> exact funext fun j => by rw [boxSlice, boxSlice, mul_comm]
  · have hp : ∀ p ∈ (range Q).filter Nat.Prime,
        ∑ u ∈ (smoothBox J (Q + 1)).filter (fun u => ¬ p ∣ u), ladderEnergy p u J f =
          ∑ j ∈ range (J + 1), ladWeight Q j *
            ∑ a ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
              ladderEnergy p a J (fun n => f (Q ^ j * n)) := by
      intro p hp
      obtain ⟨hpQ, hpp⟩ := mem_filter.mp hp
      have hpQ' : p ≠ Q := by have := mem_range.mp hpQ; omega
      rw [sum_filter, sum_smoothBox_succ hQ]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_filter, mul_sum]
      refine sum_congr rfl fun a _ => ?_
      have hdvd : p ∣ Q ^ j * a ↔ p ∣ a := by
        constructor
        · intro h
          rcases (Nat.Prime.dvd_mul hpp).mp h with h' | h'
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp hQ).mp (hpp.dvd_of_dvd_pow h')) hpQ'
          · exact h'
        · exact fun h => h.mul_left _
      by_cases hpa : p ∣ a
      · rw [if_neg (not_not.mpr (hdvd.mpr hpa)), if_neg (not_not.mpr hpa), mul_zero]
      · rw [if_pos (fun h => hpa (hdvd.mp h)), if_pos hpa, ladderEnergy_mul_pow]
    calc ∑ p ∈ (range Q).filter Nat.Prime,
          ∑ u ∈ (smoothBox J (Q + 1)).filter (fun u => ¬ p ∣ u), ladderEnergy p u J f
        = ∑ p ∈ (range Q).filter Nat.Prime, ∑ j ∈ range (J + 1), ladWeight Q j *
            ∑ a ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
              ladderEnergy p a J (fun n => f (Q ^ j * n)) := sum_congr rfl hp
      _ = ∑ j ∈ range (J + 1), ∑ p ∈ (range Q).filter Nat.Prime, ladWeight Q j *
            ∑ a ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
              ladderEnergy p a J (fun n => f (Q ^ j * n)) := sum_comm
      _ = _ := sum_congr rfl fun j _ => by rw [boxEnergy, mul_sum]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
