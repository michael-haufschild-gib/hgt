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
      show Q ^ j * u * p ^ i = Q ^ j * (u * p ^ i) by ring, ladWeight]
    push_cast
    ring
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

/-! ### 3. Expanding along the top prime -/

theorem mul_pow_mem_smoothBox {J Q p u i : ℕ} (hp : p ∈ (range Q).filter Nat.Prime)
    (hu : u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u)) (hi : i ∈ range (J + 1)) :
    u * p ^ i ∈ smoothBox J Q := by
  obtain ⟨hpQ, hpp⟩ := mem_filter.mp hp
  obtain ⟨hu', hpu⟩ := mem_filter.mp hu
  obtain ⟨h1, h2, h3⟩ := mem_smoothBox.mp hu'
  have hu0 : u ≠ 0 := by omega
  refine mem_smoothBox.mpr ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hu0 (pow_ne_zero _ hpp.ne_zero)),
    fun q hq => ?_, fun q => ?_⟩
  · rw [Nat.primeFactors_mul hu0 (pow_ne_zero _ hpp.ne_zero), mem_union] at hq
    rcases hq with hq | hq
    · exact h2 q hq
    · rw [Nat.primeFactors_prime_pow (by have := mem_range.mp hi; omega) hpp] at hq
      · rw [mem_singleton.mp hq]; exact mem_range.mp hpQ
  · rw [Nat.factorization_mul hu0 (pow_ne_zero _ hpp.ne_zero), Finsupp.add_apply,
      hpp.factorization_pow]
    by_cases hqp : q = p
    · subst hqp
      rw [Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpu, zero_add]
      have := mem_range.mp hi; omega
    · rw [Finsupp.single_eq_of_ne (Ne.symm hqp), add_zero]; exact h3 q

/-- Moving a weighted sum through the four sums of the box energy. -/
theorem sum_mul_boxEnergy_eq (J Q : ℕ) (s : Finset ℕ) (w : ℕ → ℝ) (F : ℕ → ℕ → ℝ) :
    ∑ j ∈ s, w j * boxEnergy J Q (F j) =
      ∑ p ∈ (range Q).filter Nat.Prime, ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
        ∑ i ∈ range (J + 1), ∑ i' ∈ range (J + 1), if i < i' then
          Real.log p / ((u * p ^ i' : ℕ) : ℝ) *
            ∑ j ∈ s, w j * (F j (u * p ^ i') - F j (u * p ^ i)) ^ 2 else 0 := by
  simp only [boxEnergy, ladderEnergy, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i' _ => ?_
  split_ifs
  · rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  · simp

/-- **The levels of the box energy** in the top eigenbasis:
`Σ_j w_j E_Q(f(q^j ·)) = Σ_k ‖ψ_k‖² E_Q(c_k)` when `f(q^j x) = Σ_k c_k(x) ψ_k(j)` on the box. -/
theorem sum_ladWeight_boxEnergy {J Q q : ℕ} (hq : 1 < q) (F c : ℕ → ℕ → ℝ)
    (hF : ∀ x ∈ smoothBox J Q, ∀ j ∈ range (J + 1),
      F j x = ∑ k ∈ range (J + 1), c k x * ladMode q J k j) :
    ∑ j ∈ range (J + 1), ladWeight q j * boxEnergy J Q (F j) =
      ∑ k ∈ range (J + 1), ladInner q J (ladMode q J k) (ladMode q J k) * boxEnergy J Q (c k) := by
  rw [sum_mul_boxEnergy_eq, sum_mul_boxEnergy_eq]
  refine sum_congr rfl fun p hp => sum_congr rfl fun u hu => sum_congr rfl fun i hi =>
    sum_congr rfl fun i' hi' => ?_
  split_ifs
  · congr 1
    have hx := mul_pow_mem_smoothBox hp hu hi'
    have hy := mul_pow_mem_smoothBox hp hu hi
    rw [sum_congr rfl fun j hj => by
      rw [hF _ hx j hj, hF _ hy j hj, ← sum_sub_distrib,
        show ∑ k ∈ range (J + 1), (c k (u * p ^ i') * ladMode q J k j - c k (u * p ^ i) *
          ladMode q J k j) = ∑ k ∈ range (J + 1), (c k (u * p ^ i') - c k (u * p ^ i)) *
            ladMode q J k j from sum_congr rfl fun k _ => by ring],
      sum_ladWeight_sq_sum hq]
    exact sum_congr rfl fun k _ => by ring
  · rfl

/-! ### 4. The spectral inequality -/

theorem boxSpectral_succ {J Q : ℕ} (hQ : Q.Prime)
    (ih : ∀ (T : ℝ) (f : ℕ → ℝ), T * boxInner J Q f f - boxPenalty J Q T f ≤ boxEnergy J Q f)
    (T : ℝ) (f : ℕ → ℝ) :
    T * boxInner J (Q + 1) f f - boxPenalty J (Q + 1) T f ≤ boxEnergy J (Q + 1) f := by
  have hq : 1 < Q := hQ.one_lt
  set N : ℕ → ℝ := fun k => ladInner Q J (ladMode Q J k) (ladMode Q J k)
  set c : ℕ → ℕ → ℝ := fun k a => ladCoeff Q J k (boxSlice Q f a)
  have hN : ∀ k ∈ range (J + 1), 0 < N k := fun k hk =>
    ladInner_ladMode_self_pos hq (by have := mem_range.mp hk; omega)
  have hexp : ∀ a ∈ smoothBox J Q, ∀ j ∈ range (J + 1),
      f (Q ^ j * a) = ∑ k ∈ range (J + 1), c k a * ladMode Q J k j :=
    fun a _ j hj => ladExpansion hq J (boxSlice Q f a) j hj
  have hcoef : ∀ a, ∀ k ∈ range (J + 1),
      ladInner Q J (ladMode Q J k) (boxSlice Q f a) = c k a * N k := fun a k hk =>
    ladInner_ladMode_eq_coeff hq (by have := mem_range.mp hk; omega) _
  -- the energy
  have hE : boxEnergy J (Q + 1) f = ∑ k ∈ range (J + 1),
      N k * (boxEnergy J Q (c k) + ladEig Q J k * boxInner J Q (c k) (c k)) := by
    rw [boxEnergy_succ hQ, sum_ladWeight_boxEnergy hq (fun j n => f (Q ^ j * n)) c hexp]
    have htop : ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * ladForm Q J (boxSlice Q f a) (boxSlice Q f a) =
        ∑ k ∈ range (J + 1), N k * (ladEig Q J k * boxInner J Q (c k) (c k)) := by
      simp only [ladForm_self_eq hq, boxInner, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun k hk => sum_congr rfl fun a _ => ?_
      rw [hcoef a k hk]
      ring
    rw [htop, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  -- the norm
  have hI : boxInner J (Q + 1) f f = ∑ k ∈ range (J + 1), N k * boxInner J Q (c k) (c k) := by
    rw [boxInner_succ hQ]
    simp only [ladInner_self_eq hq, boxInner, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k hk => sum_congr rfl fun a _ => ?_
    rw [hcoef a k hk]
    ring
  -- the penalty
  have hP : boxPenalty J (Q + 1) T f =
      ∑ k ∈ range (J + 1), N k * boxPenalty J Q (T - ladEig Q J k) (c k) := by
    rw [boxPenalty, sum_smoothBox_succ hQ]
    refine sum_congr rfl fun k hk => ?_
    rw [boxPenalty, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hslice : ∀ a ∈ smoothBox J Q, boxSlice Q (boxMode J (Q + 1) (Q ^ k * m)) a =
        fun j => ladMode Q J k j * boxMode J Q m a := fun a ha =>
      funext fun j => by rw [boxSlice, boxMode_succ hQ hm ha]
    have hin : boxInner J (Q + 1) f (boxMode J (Q + 1) (Q ^ k * m)) =
        N k * boxInner J Q (c k) (boxMode J Q m) := by
      rw [boxInner_succ hQ, boxInner, mul_sum]
      refine sum_congr rfl fun a ha => ?_
      rw [hslice a ha]
      have : ladInner Q J (boxSlice Q f a) (fun j => ladMode Q J k j * boxMode J Q m a) =
          boxMode J Q m a * ladInner Q J (ladMode Q J k) (boxSlice Q f a) := by
        simp only [ladInner, mul_sum]
        exact sum_congr rfl fun j _ => by ring
      rw [this, hcoef a k hk]
      ring
    have hnorm : boxInner J (Q + 1) (boxMode J (Q + 1) (Q ^ k * m)) (boxMode J (Q + 1) (Q ^ k * m)) =
        N k * boxInner J Q (boxMode J Q m) (boxMode J Q m) := by
      rw [boxInner_succ hQ, boxInner, mul_sum]
      refine sum_congr rfl fun a ha => ?_
      rw [hslice a ha]
      simp only [ladInner, mul_sum, N]
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [boxEig_succ hQ hm, hin, hnorm]
    have hNk := hN k hk
    by_cases hlt : ladEig Q J k + boxEig J Q m < T
    · rw [if_pos hlt, if_pos (by linarith)]
      rcases eq_or_ne (boxInner J Q (boxMode J Q m) (boxMode J Q m)) 0 with h0 | h0
      · rw [h0]; simp
      · field_simp
        ring
    · rw [if_neg hlt, if_neg (by linarith), mul_zero]
  -- the induction
  rw [hE, hI, hP, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun k hk => ?_
  have := mul_le_mul_of_nonneg_left (ih (T - ladEig Q J k) (c k)) (hN k hk).le
  nlinarith

/-- **The finite prime chain has the spectrum of its product modes.** For every real `T` and every
`f` on the box, `T ‖f‖² − Σ_{λ(m) < T} (T − λ(m)) ⟨f, Ψ_m⟩²/‖Ψ_m‖² ≤ E(f)`. -/
theorem boxSpectral (J Q : ℕ) :
    ∀ (T : ℝ) (f : ℕ → ℝ), T * boxInner J Q f f - boxPenalty J Q T f ≤ boxEnergy J Q f := by
  induction Q with
  | zero =>
    intro T f
    have hB : smoothBox J 0 = {1} := rfl
    have hP : (range 0).filter Nat.Prime = ∅ := by simp
    simp only [boxInner, boxPenalty, boxEnergy, boxMode, boxEig, hB, hP, sum_singleton,
      prod_empty, sum_empty, Nat.cast_one, div_one, one_mul, mul_one]
    split_ifs with hT
    · nlinarith
    · nlinarith [sq_nonneg (f 1), mul_self_nonneg (f 1)]
  | succ Q ih =>
    intro T f
    by_cases hQ : Q.Prime
    · exact boxSpectral_succ hQ ih T f
    · have h1 := smoothBox_succ_of_not (J := J) hQ
      have h2 := filter_prime_range_succ_of_not hQ
      have := ih T f
      simp only [boxInner, boxPenalty, boxEnergy, boxMode, boxEig] at this ⊢
      simp only [h1, h2]
      exact this

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
