import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicMeasureTensorizesOverPrimes

/-!
# The valuation chain of finitely many primes has gap `2 log 2`

Fix `Q`. On the `Q`-smooth numbers of `[1, X]` (every prime factor below `Q`) with the harmonic
weights `1/a`, the multiplicative walk moves `a ↦ a p^k`, `p < Q`, with conductance `log p/(a p^k)`.
Its Dirichlet form `E_X` (`smoothEnergy`) satisfies, for every `ε > 0` and all large `X`,

  `(2 log 2 − ε) Var(h) ≤ E_X(h)` (`eventually_smoothVar_le_smoothEnergy`),

and `2 log 2` is the gap of the valuation step at `p = 2`: finitely many primes make the chain a
product up to a halo of vanishing mass.

* **Boxes** (`smoothBox`): the `Q`-smooth numbers with exponents `≤ J` are a product of geometric
  ladders. Efron–Stein holds exactly (`boxVar_le_boxGlauber`): the variance is at most the sum of the
  ladder variances, by induction over the primes with commuting ladder means.
* **Sharp ladders** (`boxLadderVar_le`): on a ladder `{u p^i : i ≤ J}` the pairwise form of the
  variance gives gap `log p · Σ_{i ≤ J} p^{−i}`, which is `2 log 2 (1 − 2^{−J−1})` at `p = 2` and
  `≥ 2 log 2` for `p ≥ 3`.
* **Zero extension** (`smoothVar_le_of_box`): extending `h − mean` by `0` from `[1, X]` to a box costs
  only the edges leaving `[1, X]`: weight `≤ 2 log p · a/X` below `√X`, and on the halo `a > √X` the
  down-edges carry `log a ≥ ½ log X` (`sum_log_mul_sq_le_smoothEnergy`), so the halo mass is
  `O((E + Var)/log X)`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. Boxes of smooth numbers -/

/-- The box of `Q`-smooth numbers with every exponent at most `J`. -/
def smoothBox (J : ℕ) : ℕ → Finset ℕ
  | 0 => {1}
  | Q + 1 => if Q.Prime then (range (J + 1)).biUnion fun j => (smoothBox J Q).image (Q ^ j * ·)
      else smoothBox J Q

theorem mem_smoothBox {J Q a : ℕ} :
    a ∈ smoothBox J Q ↔ 1 ≤ a ∧ (∀ p ∈ a.primeFactors, p < Q) ∧ ∀ p, a.factorization p ≤ J := by
  induction Q generalizing a with
  | zero =>
    simp only [smoothBox, mem_singleton, not_lt_zero']
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, h2, -⟩
      by_contra hne
      obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (show a ≠ 1 from hne)
      exact h2 p (Nat.mem_primeFactors.mpr ⟨hp, hpa, by omega⟩)
  | succ Q ih =>
    by_cases hQ : Q.Prime
    · simp only [smoothBox, if_pos hQ, mem_biUnion, mem_range, mem_image]
      constructor
      · rintro ⟨j, hj, a', ha', rfl⟩
        obtain ⟨h1, h2, h3⟩ := ih.mp ha'
        have hQa : ¬ Q ∣ a' := fun h => by
          have := h2 Q (Nat.mem_primeFactors.mpr ⟨hQ, h, by omega⟩); omega
        refine ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hQ.ne_zero) (by omega)),
          fun p hp => ?_, fun p => ?_⟩
        · rw [Nat.primeFactors_mul (pow_ne_zero _ hQ.ne_zero) (by omega), mem_union] at hp
          rcases hp with hp | hp
          · have hp' := Nat.mem_primeFactors.mp hp
            have := (Nat.prime_dvd_prime_iff_eq hp'.1 hQ).mp (hp'.1.dvd_of_dvd_pow hp'.2.1)
            omega
          · have := h2 p hp; omega
        · rw [Nat.factorization_mul (pow_ne_zero _ hQ.ne_zero) (by omega), Finsupp.add_apply,
            hQ.factorization_pow]
          by_cases hpQ : p = Q
          · subst hpQ
            rw [Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hQa]; omega
          · rw [Finsupp.single_eq_of_ne hpQ, zero_add]; exact h3 p
      · rintro ⟨h1, h2, h3⟩
        refine ⟨a.factorization Q, Nat.lt_succ_of_le (h3 Q), a / Q ^ a.factorization Q,
          ih.mpr ⟨Nat.ordCompl_pos Q (by omega), fun p hp => ?_, fun p => ?_⟩,
          Nat.ordProj_mul_ordCompl_eq_self a Q⟩
        · have hpa := Nat.mem_primeFactors.mp hp
          have hpn : p ∈ a.primeFactors := Nat.mem_primeFactors.mpr
            ⟨hpa.1, hpa.2.1.trans (Nat.ordCompl_dvd a Q), by omega⟩
          have hlt := h2 p hpn
          have hne : p ≠ Q := fun h => Nat.not_dvd_ordCompl hQ (by omega) (h ▸ hpa.2.1)
          omega
        · exact ((Nat.factorization_le_iff_dvd (Nat.ordCompl_pos Q (by omega)).ne'
            (by omega)).mpr (Nat.ordCompl_dvd a Q) p).trans (h3 p)
    · simp only [smoothBox, if_neg hQ]
      rw [ih]
      refine and_congr_right fun _ => and_congr_left fun _ => ⟨fun h p hp => (h p hp).trans
        (Nat.lt_succ_self Q), fun h p hp => ?_⟩
      have := h p hp
      rcases Nat.lt_succ_iff_lt_or_eq.mp this with h' | h'
      · exact h'
      · exact absurd (h' ▸ (Nat.prime_of_mem_primeFactors hp)) hQ

theorem one_mem_smoothBox (J Q : ℕ) : 1 ∈ smoothBox J Q :=
  mem_smoothBox.mpr ⟨le_rfl, by simp, by simp⟩

theorem not_dvd_of_mem_smoothBox {J Q a : ℕ} (ha : a ∈ smoothBox J Q) (hQ : Q.Prime) : ¬ Q ∣ a :=
  fun h => by
    obtain ⟨h1, h2, -⟩ := mem_smoothBox.mp ha
    have := h2 Q (Nat.mem_primeFactors.mpr ⟨hQ, h, by omega⟩)
    omega

/-- **Levels of a box**: `Box(Q + 1) = ⊔_{j ≤ J} Q^j Box(Q)` for a prime `Q`. -/
theorem sum_smoothBox_succ {J Q : ℕ} (hQ : Q.Prime) (φ : ℕ → ℝ) :
    ∑ a ∈ smoothBox J (Q + 1), φ a = ∑ j ∈ range (J + 1), ∑ a ∈ smoothBox J Q, φ (Q ^ j * a) := by
  classical
  rw [smoothBox, if_pos hQ, sum_biUnion]
  · refine sum_congr rfl fun j _ => ?_
    rw [sum_image]
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hQ.pos j) h
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun n hn hn' => ?_
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    obtain ⟨b, hb, hab⟩ := mem_image.mp hn'
    have ha0 : a ≠ 0 := by have := (mem_smoothBox.mp ha).1; omega
    have hb0 : b ≠ 0 := by have := (mem_smoothBox.mp hb).1; omega
    have hfa := not_dvd_of_mem_smoothBox ha hQ
    have hfb := not_dvd_of_mem_smoothBox hb hQ
    have key := congrArg (fun n => n.factorization Q) hab
    simp only [Nat.factorization_mul (pow_ne_zero _ hQ.ne_zero) ha0,
      Nat.factorization_mul (pow_ne_zero _ hQ.ne_zero) hb0, Finsupp.add_apply,
      hQ.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hfa,
      Nat.factorization_eq_zero_of_not_dvd hfb] at key
    exact hij key.symm

/-! ### 2. Efron–Stein on boxes -/

/-- The harmonic variance of `f` along the box ladder `{u p^i : i ≤ J}`. -/
def boxLadderVar (p u J : ℕ) (f : ℕ → ℝ) : ℝ :=
  wVar (range (J + 1)) (fun i => 1 / ((u * p ^ i : ℕ) : ℝ)) (fun i => f (u * p ^ i))

/-- The harmonic variance of `f` on the box. -/
def boxVar (J Q : ℕ) (f : ℕ → ℝ) : ℝ := wVar (smoothBox J Q) (fun a => 1 / (a : ℝ)) f

/-- The Glauber form of the box: the sum of its ladder variances. -/
def boxGlauber (J Q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (range Q).filter Nat.Prime, ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
    boxLadderVar p u J f

theorem boxLadderVar_nonneg (p u J : ℕ) (f : ℕ → ℝ) : 0 ≤ boxLadderVar p u J f :=
  wVar_nonneg fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _)

theorem boxGlauber_nonneg (J Q : ℕ) (f : ℕ → ℝ) : 0 ≤ boxGlauber J Q f :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => boxLadderVar_nonneg _ _ _ _

theorem boxLadderVar_mul_pow {p Q u J j : ℕ} (hQ : 0 < Q) (f : ℕ → ℝ) :
    boxLadderVar p (Q ^ j * u) J f =
      (1 / (Q : ℝ)) ^ j * boxLadderVar p u J (fun n => f (Q ^ j * n)) := by
  rw [boxLadderVar, boxLadderVar, ← wVar_const_mul (pow_ne_zero _ (by positivity))]
  refine wVar_congr rfl (fun i _ => ?_) (fun i _ => by rw [mul_assoc])
  push_cast
  rw [one_div_pow, one_div_mul_one_div, mul_assoc]

/-- The box Glauber form splits into the top ladders and the levels. -/
theorem boxGlauber_succ {J Q : ℕ} (hQ : Q.Prime) (f : ℕ → ℝ) :
    boxGlauber J (Q + 1) f = ∑ a ∈ smoothBox J Q, boxLadderVar Q a J f +
      ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j * boxGlauber J Q (fun n => f (Q ^ j * n)) := by
  have hins : (range (Q + 1)).filter Nat.Prime = insert Q ((range Q).filter Nat.Prime) := by
    rw [range_add_one, filter_insert, if_pos hQ]
  have hnot : Q ∉ (range Q).filter Nat.Prime := by simp
  rw [boxGlauber, hins, sum_insert hnot]
  congr 1
  · rw [sum_filter, sum_smoothBox_succ hQ]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul]
    have hzero : ∑ j ∈ range J, ∑ a ∈ smoothBox J Q,
        (if ¬ Q ∣ Q ^ (j + 1) * a then boxLadderVar Q (Q ^ (j + 1) * a) J f else 0) = 0 :=
      sum_eq_zero fun j _ => sum_eq_zero fun a _ => by
        rw [if_neg (not_not.mpr (Dvd.dvd.mul_right (dvd_pow_self Q (Nat.succ_ne_zero j)) a))]
    rw [hzero, zero_add]
    exact sum_congr rfl fun a ha => by rw [if_pos (not_dvd_of_mem_smoothBox ha hQ)]
  · have hp : ∀ p ∈ (range Q).filter Nat.Prime,
        ∑ u ∈ (smoothBox J (Q + 1)).filter (fun u => ¬ p ∣ u), boxLadderVar p u J f =
          ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
            ∑ a ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
              boxLadderVar p a J (fun n => f (Q ^ j * n)) := by
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
      · rw [if_pos (fun h => hpa (hdvd.mp h)), if_pos hpa, boxLadderVar_mul_pow hQ.pos]
    calc ∑ p ∈ (range Q).filter Nat.Prime,
          ∑ u ∈ (smoothBox J (Q + 1)).filter (fun u => ¬ p ∣ u), boxLadderVar p u J f
        = ∑ p ∈ (range Q).filter Nat.Prime, ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
            ∑ a ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
              boxLadderVar p a J (fun n => f (Q ^ j * n)) := sum_congr rfl hp
      _ = ∑ j ∈ range (J + 1), ∑ p ∈ (range Q).filter Nat.Prime, (1 / (Q : ℝ)) ^ j *
            ∑ a ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
              boxLadderVar p a J (fun n => f (Q ^ j * n)) := sum_comm
      _ = _ := sum_congr rfl fun j _ => by rw [boxGlauber, mul_sum]

/-- **Efron–Stein on a box**: the harmonic variance is at most the sum of the ladder variances. -/
theorem boxVar_le_boxGlauber (J Q : ℕ) (f : ℕ → ℝ) : boxVar J Q f ≤ boxGlauber J Q f := by
  induction Q generalizing f with
  | zero =>
    rw [boxVar, wVar_eq_zero_of_subsingleton (fun _ _ => by positivity) (i₀ := 1)
      (fun a ha => by simpa [smoothBox] using ha)]
    exact boxGlauber_nonneg _ _ _
  | succ Q ih =>
    by_cases hQ : Q.Prime
    · have hμ : ∀ n : ℕ, (0 : ℝ) ≤ 1 / (n : ℝ) := fun n => by positivity
      set M := ∑ a ∈ smoothBox J Q, 1 / (a : ℝ)
      have hM : 0 < M := by
        have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ≤ M :=
          single_le_sum (f := fun a : ℕ => 1 / (a : ℝ)) (fun a _ => hμ a) (one_mem_smoothBox J Q)
        have : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
        linarith
      -- the ladder means and their harmonic average
      set ℓ : ℕ → ℝ := fun a => wMean (range (J + 1)) (fun i => 1 / ((a * Q ^ i : ℕ) : ℝ))
        (fun i => f (a * Q ^ i))
      set c := (∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * ℓ a) / M
      have hstep1 : boxVar J (Q + 1) f ≤ ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
          (boxVar J Q (fun n => f (Q ^ j * n)) +
            M * (wMean (smoothBox J Q) (fun a => 1 / (a : ℝ)) (fun n => f (Q ^ j * n)) - c) ^ 2) := by
        refine (wVar_le (fun n _ => hμ n) c).trans (le_of_eq ?_)
        rw [sum_smoothBox_succ hQ]
        refine sum_congr rfl fun j _ => ?_
        have hS := sum_mul_sub_sq_eq (s := smoothBox J Q) (w := fun n => 1 / (n : ℝ))
          (v := fun n => f (Q ^ j * n)) (fun n _ => hμ n) c
        have e : ∑ a ∈ smoothBox J Q, 1 / ((Q ^ j * a : ℕ) : ℝ) * (f (Q ^ j * a) - c) ^ 2 =
            (1 / (Q : ℝ)) ^ j * ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (f (Q ^ j * a) - c) ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun a _ => ?_
          push_cast
          rw [one_div_pow, ← mul_assoc, one_div_mul_one_div]
        rw [e, hS]
        rfl
      -- between the levels: the variance of the level means is at most the ladder variances
      have hbetween : ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
          (M * (wMean (smoothBox J Q) (fun a => 1 / (a : ℝ)) (fun n => f (Q ^ j * n)) - c) ^ 2) ≤
          ∑ a ∈ smoothBox J Q, boxLadderVar Q a J f := by
        have hj : ∀ j ∈ range (J + 1),
            M * (wMean (smoothBox J Q) (fun a => 1 / (a : ℝ)) (fun n => f (Q ^ j * n)) - c) ^ 2 ≤
              ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (f (Q ^ j * a) - ℓ a) ^ 2 := by
          intro j _
          have hdiff : wMean (smoothBox J Q) (fun a => 1 / (a : ℝ)) (fun n => f (Q ^ j * n)) - c =
              (∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (f (Q ^ j * a) - ℓ a)) / M := by
            rw [wMean, ← sub_div, ← sum_sub_distrib]
            exact congrArg (· / M) (sum_congr rfl fun a _ => by ring)
          rw [hdiff, div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
          have hCS : (∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (f (Q ^ j * a) - ℓ a)) ^ 2 ≤
              M * ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (f (Q ^ j * a) - ℓ a) ^ 2 :=
            sq_sum_mul_le (fun a _ => hμ a) _
          linarith [mul_le_mul_of_nonneg_left hCS hM.le]
        calc ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
              (M * (wMean (smoothBox J Q) (fun a => 1 / (a : ℝ)) (fun n => f (Q ^ j * n)) - c) ^ 2)
            ≤ ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
                ∑ a ∈ smoothBox J Q, 1 / (a : ℝ) * (f (Q ^ j * a) - ℓ a) ^ 2 :=
              sum_le_sum fun j hjr => mul_le_mul_of_nonneg_left (hj j hjr) (by positivity)
          _ = ∑ a ∈ smoothBox J Q, ∑ j ∈ range (J + 1),
                (1 / (Q : ℝ)) ^ j * (1 / (a : ℝ) * (f (Q ^ j * a) - ℓ a) ^ 2) := by
              simp only [mul_sum]
              exact sum_comm
          _ = ∑ a ∈ smoothBox J Q, boxLadderVar Q a J f := by
              refine sum_congr rfl fun a _ => ?_
              rw [boxLadderVar, wVar]
              refine sum_congr rfl fun i _ => ?_
              have e1 : (1 / (Q : ℝ)) ^ i * (1 / (a : ℝ)) = 1 / ((a * Q ^ i : ℕ) : ℝ) := by
                push_cast
                rw [one_div_pow, one_div_mul_one_div, mul_comm]
              rw [← mul_assoc, e1, mul_comm (Q ^ i) a]
      -- within the levels: induction
      have hwithin : ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j * boxVar J Q (fun n => f (Q ^ j * n)) ≤
          ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j * boxGlauber J Q (fun n => f (Q ^ j * n)) :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _) (by positivity)
      rw [boxGlauber_succ hQ]
      have hsplit : ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
          (boxVar J Q (fun n => f (Q ^ j * n)) +
            M * (wMean (smoothBox J Q) (fun a => 1 / (a : ℝ)) (fun n => f (Q ^ j * n)) - c) ^ 2) =
          ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j * boxVar J Q (fun n => f (Q ^ j * n)) +
          ∑ j ∈ range (J + 1), (1 / (Q : ℝ)) ^ j *
            (M * (wMean (smoothBox J Q) (fun a => 1 / (a : ℝ)) (fun n => f (Q ^ j * n)) - c) ^ 2) := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
      linarith
    · have hbox : smoothBox J (Q + 1) = smoothBox J Q := by rw [smoothBox, if_neg hQ]
      have hpr : (range (Q + 1)).filter Nat.Prime = (range Q).filter Nat.Prime := by
        rw [range_add_one, filter_insert, if_neg hQ]
      rw [boxVar, hbox, boxGlauber, hpr, hbox]
      exact ih f

/-! ### 3. Sharp ladders -/

/-- The pairwise form of a variance: `2 (Σ w) Var = Σ_{i,j} w_i w_j (v_i − v_j)²`. -/
theorem two_mul_sum_mul_wVar {ι : Type*} {s : Finset ι} {w : ι → ℝ} (hw : ∀ i ∈ s, 0 ≤ w i)
    (v : ι → ℝ) :
    2 * (∑ i ∈ s, w i) * wVar s w v = ∑ i ∈ s, ∑ j ∈ s, w i * w j * (v i - v j) ^ 2 := by
  have hS := sum_mul_sub_sq_eq (v := v) hw 0
  simp only [sub_zero] at hS
  by_cases hW : ∑ i ∈ s, w i = 0
  · have h0 := (sum_eq_zero_iff_of_nonneg hw).mp hW
    rw [hW, mul_zero, zero_mul]
    exact (sum_eq_zero fun i hi => sum_eq_zero fun j _ => by rw [h0 i hi, zero_mul, zero_mul]).symm
  · have hmean : (∑ i ∈ s, w i) * wMean s w v = ∑ i ∈ s, w i * v i := by
      rw [wMean, mul_div_cancel₀ _ hW]
    have expand : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (v i - v j) ^ 2 =
        2 * (∑ i ∈ s, w i) * ∑ i ∈ s, w i * v i ^ 2 - 2 * (∑ i ∈ s, w i * v i) ^ 2 := by
      have : ∀ i ∈ s, ∑ j ∈ s, w i * w j * (v i - v j) ^ 2 =
          w i * v i ^ 2 * ∑ j ∈ s, w j - 2 * (w i * v i) * ∑ j ∈ s, w j * v j +
            w i * ∑ j ∈ s, w j * v j ^ 2 := fun i _ => by
        rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun j _ => by ring
      rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul, ← sum_mul,
        ← mul_sum]
      ring
    rw [expand]
    have h2 : (∑ i ∈ s, w i) * ∑ i ∈ s, w i * v i ^ 2 = (∑ i ∈ s, w i) * wVar s w v +
        ((∑ i ∈ s, w i) * wMean s w v) ^ 2 := by
      rw [hS]; ring
    rw [hmean] at h2
    linarith

/-- The Dirichlet form of a box ladder: all edges `u p^i → u p^j`, `i < j ≤ J`. -/
def ladderEnergy (p u J : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (J + 1), ∑ j ∈ range (J + 1),
    if i < j then Real.log p / ((u * p ^ j : ℕ) : ℝ) * (f (u * p ^ j) - f (u * p ^ i)) ^ 2 else 0

/-- The mass of a ladder, `W_p(J) = Σ_{i ≤ J} p^{−i}`. -/
def ladderMass (p J : ℕ) : ℝ := ∑ i ∈ range (J + 1), (1 / (p : ℝ)) ^ i

/-- **Sharp ladder Poincaré**: `Var ≤ E/(log p · W_p(J))` on `{u p^i : i ≤ J}`. -/
theorem boxLadderVar_le {p u J : ℕ} (hp : 2 ≤ p) (hu : 1 ≤ u) (f : ℕ → ℝ) :
    boxLadderVar p u J f ≤ ladderEnergy p u J f / (Real.log p * ladderMass p J) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hW : 0 < ladderMass p J :=
    lt_of_lt_of_le one_pos (by
      have := single_le_sum (f := fun i => (1 / (p : ℝ)) ^ i) (fun i _ => by positivity)
        (mem_range.mpr (Nat.succ_pos J))
      simpa [ladderMass] using this)
  set w : ℕ → ℝ := fun i => 1 / ((u * p ^ i : ℕ) : ℝ)
  have hw : ∀ i ∈ range (J + 1), 0 ≤ w i := fun i _ => by positivity
  have hwi : ∀ i, w i = (1 / (u : ℝ)) * (1 / (p : ℝ)) ^ i := fun i => by
    simp only [w]; push_cast; rw [one_div_pow, one_div_mul_one_div]
  have hsum : ∑ i ∈ range (J + 1), w i = (1 / (u : ℝ)) * ladderMass p J := by
    rw [ladderMass, mul_sum]; exact sum_congr rfl fun i _ => hwi i
  have hpair := two_mul_sum_mul_wVar hw (fun i => f (u * p ^ i))
  -- the ordered pairs, each term bounded by the edge conductance
  have hterm : ∀ i ∈ range (J + 1), ∀ j ∈ range (J + 1),
      w i * w j * (f (u * p ^ i) - f (u * p ^ j)) ^ 2 ≤
        (1 / (u : ℝ)) / Real.log p * ((if i < j then Real.log p / ((u * p ^ j : ℕ) : ℝ) *
          (f (u * p ^ j) - f (u * p ^ i)) ^ 2 else 0) +
          (if j < i then Real.log p / ((u * p ^ i : ℕ) : ℝ) *
          (f (u * p ^ i) - f (u * p ^ j)) ^ 2 else 0)) := by
    intro i _ j _
    have hwi1 : w i ≤ 1 / (u : ℝ) := by
      rw [hwi]; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity)
        (by rw [div_le_one hp0]; exact_mod_cast (show 1 ≤ p by omega)))
    have hwj1 : w j ≤ 1 / (u : ℝ) := by
      rw [hwi]; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity)
        (by rw [div_le_one hp0]; exact_mod_cast (show 1 ≤ p by omega)))
    have hsq : 0 ≤ (f (u * p ^ i) - f (u * p ^ j)) ^ 2 := sq_nonneg _
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (by omega), add_zero]
      have e : (1 / (u : ℝ)) / Real.log p * (Real.log p / ((u * p ^ j : ℕ) : ℝ) *
          (f (u * p ^ j) - f (u * p ^ i)) ^ 2) = 1 / (u : ℝ) * w j *
          (f (u * p ^ i) - f (u * p ^ j)) ^ 2 := by
        simp only [w]; field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwi1 (hw j (by assumption)))
        hsq
    · simp
    · rw [if_neg (by omega), if_pos h, zero_add]
      have e : (1 / (u : ℝ)) / Real.log p * (Real.log p / ((u * p ^ i : ℕ) : ℝ) *
          (f (u * p ^ i) - f (u * p ^ j)) ^ 2) = 1 / (u : ℝ) * w i *
          (f (u * p ^ i) - f (u * p ^ j)) ^ 2 := by
        simp only [w]; field_simp
      rw [e, mul_comm (w i) (w j)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwj1 (hw i (by assumption)))
        hsq
  have htotal : ∑ i ∈ range (J + 1), ∑ j ∈ range (J + 1), w i * w j *
      (f (u * p ^ i) - f (u * p ^ j)) ^ 2 ≤ (1 / (u : ℝ)) / Real.log p * (2 * ladderEnergy p u J f) := by
    refine (sum_le_sum fun i hi => sum_le_sum fun j hj => hterm i hi j hj).trans (le_of_eq ?_)
    simp only [← mul_sum]
    congr 1
    rw [sum_congr rfl (fun i _ => sum_add_distrib), sum_add_distrib, two_mul]
    congr 1
    rw [sum_comm]
    rfl
  rw [boxLadderVar, le_div_iff₀ (mul_pos hlog hW)]
  have h1 : 2 * ((1 / (u : ℝ)) * ladderMass p J) * wVar (range (J + 1)) w (fun i => f (u * p ^ i)) ≤
      (1 / (u : ℝ)) / Real.log p * (2 * ladderEnergy p u J f) := by
    rw [← hsum]; exact hpair.le.trans htotal
  have hpos : 0 < 1 / (u : ℝ) := by positivity
  have h2 : wVar (range (J + 1)) w (fun i => f (u * p ^ i)) * (Real.log p * ladderMass p J) * (2 / u) ≤
      ladderEnergy p u J f * (2 / u) := by
    have e1 : wVar (range (J + 1)) w (fun i => f (u * p ^ i)) * (Real.log p * ladderMass p J) * (2 / u) =
        Real.log p * (2 * ((1 / (u : ℝ)) * ladderMass p J) * wVar (range (J + 1)) w (fun i => f (u * p ^ i))) := by
      ring
    have e2 : ladderEnergy p u J f * (2 / u) = Real.log p * ((1 / (u : ℝ)) / Real.log p *
        (2 * ladderEnergy p u J f)) := by
      field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1 hlog.le
  exact le_of_mul_le_mul_right h2 (by positivity)

/-- The Dirichlet form of a box: the sum of its ladder energies. -/
def boxEnergy (J Q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (range Q).filter Nat.Prime, ∑ u ∈ (smoothBox J Q).filter (fun u => ¬ p ∣ u),
    ladderEnergy p u J f

theorem ladderEnergy_nonneg (p u J : ℕ) (f : ℕ → ℝ) : 0 ≤ ladderEnergy p u J f :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by
    split_ifs
    · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)) (sq_nonneg _)
    · exact le_rfl

/-- The box gap `g_J = 2 log 2 (1 − 2^{−J−1})`. -/
def boxGap (J : ℕ) : ℝ := 2 * Real.log 2 * (1 - (1 / 2 : ℝ) ^ (J + 1))

/-- Every ladder has gap at least `g_J`: `log p · W_p(J) ≥ 2 log 2 (1 − 2^{−J−1})`, `J ≥ 1`. -/
theorem boxGap_le_ladder {p J : ℕ} (hp : p.Prime) (hJ : 1 ≤ J) :
    boxGap J ≤ Real.log p * ladderMass p J := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgeo : ∀ q : ℝ, q ≠ 1 → ∑ i ∈ range (J + 1), q ^ i = (q ^ (J + 1) - 1) / (q - 1) :=
    fun q hq => geom_sum_eq hq (J + 1)
  have hJlt : (0 : ℝ) < 1 - (1 / 2 : ℝ) ^ (J + 1) := by
    have : (1 / 2 : ℝ) ^ (J + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have hgap_le : boxGap J ≤ 2 * Real.log 2 := by
    rw [boxGap]
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (J + 1) := by positivity
    nlinarith
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- `p = 2`: equality
    rw [ladderMass, hgeo _ (by norm_num), boxGap]
    push_cast
    have : ((1 / 2 : ℝ) ^ (J + 1) - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ (J + 1)) := by
      field_simp; ring
    rw [this]; nlinarith
  · have hp3 : 3 ≤ p := by have := hp.two_le; rcases hodd with ⟨k, hk⟩; omega
    have hW1 : 1 + 1 / (p : ℝ) ≤ ladderMass p J := by
      rw [ladderMass]
      have hsub : range 2 ⊆ range (J + 1) := range_subset_range.mpr (by omega)
      have := sum_le_sum_of_subset_of_nonneg (f := fun i => (1 / (p : ℝ)) ^ i) hsub
        (fun i _ _ => by positivity)
      simpa [Finset.sum_range_succ] using this
    rcases Nat.lt_or_ge p 4 with h4 | h4
    · -- `p = 3`: `(4/3) log 3 ≥ 2 log 2` since `81 ≥ 64`
      have hp3' : p = 3 := by omega
      subst hp3'
      have hlog : 2 * Real.log 2 ≤ Real.log 3 * (1 + 1 / (3 : ℝ)) := by
        have h1 : Real.log 64 ≤ Real.log 81 := Real.log_le_log (by norm_num) (by norm_num)
        rw [show (64 : ℝ) = 2 ^ 6 by norm_num, show (81 : ℝ) = 3 ^ 4 by norm_num,
          Real.log_pow, Real.log_pow] at h1
        push_cast at h1
        linarith
      push_cast at hW1 ⊢
      have := mul_le_mul_of_nonneg_left hW1 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3))
      linarith
    · -- `p ≥ 5`: `log p ≥ log 4 = 2 log 2`
      have hlp : 2 * Real.log 2 ≤ Real.log p := by
        rw [show 2 * Real.log 2 = Real.log 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast h4)
      have hW : 1 ≤ ladderMass p J := by
        have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith
      have := mul_le_mul_of_nonneg_left hW
        (Real.log_nonneg (show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le))
      linarith

/-- **Box Poincaré**: `g_J · Var ≤ E` on the box, for `J ≥ 1`. -/
theorem boxGap_mul_boxVar_le {J : ℕ} (hJ : 1 ≤ J) (Q : ℕ) (f : ℕ → ℝ) :
    boxGap J * boxVar J Q f ≤ boxEnergy J Q f := by
  have hg : 0 < boxGap J := by
    rw [boxGap]
    have : (1 / 2 : ℝ) ^ (J + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    nlinarith
  refine (mul_le_mul_of_nonneg_left (boxVar_le_boxGlauber J Q f) hg.le).trans ?_
  rw [boxGlauber, boxEnergy, mul_sum]
  refine sum_le_sum fun p hp => ?_
  rw [mul_sum]
  refine sum_le_sum fun u hu => ?_
  have hpp := (mem_filter.mp hp).2
  have hu1 := (mem_smoothBox.mp (mem_filter.mp hu).1).1
  have hlad := boxLadderVar_le (J := J) hpp.two_le hu1 f
  have hW := boxGap_le_ladder hpp hJ
  have hlW : 0 < Real.log p * ladderMass p J := hg.trans_le hW
  rw [le_div_iff₀ hlW] at hlad
  calc boxGap J * boxLadderVar p u J f ≤ Real.log p * ladderMass p J * boxLadderVar p u J f :=
        mul_le_mul_of_nonneg_right hW (boxLadderVar_nonneg _ _ _ _)
    _ ≤ ladderEnergy p u J f := by linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
