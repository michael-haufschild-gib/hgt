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

/-! ### 4. Truncation at `X` -/

/-- The `Q`-smooth numbers of `[1, X]`. -/
def smoothSet (Q X : ℕ) : Finset ℕ := (Icc 1 X).filter fun a => ∀ p ∈ a.primeFactors, p < Q

/-- The harmonic variance on the `Q`-smooth numbers of `[1, X]`. -/
def smoothVar (Q X : ℕ) (h : ℕ → ℝ) : ℝ := wVar (smoothSet Q X) (fun a => 1 / (a : ℝ)) h

/-- The Dirichlet form of the `Q`-smooth valuation chain on `[1, X]`. -/
def smoothEnergy (Q X : ℕ) (h : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (range Q).filter Nat.Prime, ∑ u ∈ (smoothSet Q X).filter (fun u => ¬ p ∣ u),
    ∑ i ∈ range (X + 1), ∑ j ∈ range (X + 1),
      if i < j ∧ u * p ^ j ≤ X then
        Real.log p / ((u * p ^ j : ℕ) : ℝ) * (h (u * p ^ j) - h (u * p ^ i)) ^ 2 else 0

theorem mem_smoothSet {Q X a : ℕ} :
    a ∈ smoothSet Q X ↔ 1 ≤ a ∧ a ≤ X ∧ ∀ p ∈ a.primeFactors, p < Q := by
  simp [smoothSet, and_assoc]

theorem smoothSet_subset_smoothBox (Q X : ℕ) : smoothSet Q X ⊆ smoothBox X Q := fun a ha => by
  obtain ⟨h1, h2, h3⟩ := mem_smoothSet.mp ha
  exact mem_smoothBox.mpr ⟨h1, h3, fun p => (Nat.factorization_lt p (by omega)).le.trans h2⟩

/-- The `p`-ladders of the smooth numbers of `[1, X]`. -/
theorem sum_smoothSet_eq_ladders {Q X p : ℕ} (hp : p.Prime) (hpQ : p < Q) (φ : ℕ → ℝ) :
    ∑ a ∈ smoothSet Q X, φ a = ∑ u ∈ (smoothSet Q X).filter (fun u => ¬ p ∣ u),
      ∑ i ∈ (range (X + 1)).filter (fun i => u * p ^ i ≤ X), φ (u * p ^ i) := by
  rw [sum_sigma']
  symm
  refine sum_nbij' (fun x => x.1 * p ^ x.2)
    (fun a => ⟨a / p ^ a.factorization p, a.factorization p⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, i⟩ h
    rw [mem_sigma, mem_filter, mem_filter, mem_range] at h
    obtain ⟨⟨hu, -⟩, -, hle⟩ := h
    obtain ⟨h1, -, h3⟩ := mem_smoothSet.mp hu
    refine mem_smoothSet.mpr ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega)
      (pow_ne_zero _ hp.ne_zero)), hle, fun q hq => ?_⟩
    rw [Nat.primeFactors_mul (by omega) (pow_ne_zero _ hp.ne_zero), mem_union] at hq
    rcases hq with hq | hq
    · exact h3 q hq
    · have hq' := Nat.mem_primeFactors.mp hq
      have := (Nat.prime_dvd_prime_iff_eq hq'.1 hp).mp (hq'.1.dvd_of_dvd_pow hq'.2.1)
      omega
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := mem_smoothSet.mp ha
    rw [mem_sigma, mem_filter, mem_filter, mem_range]
    refine ⟨⟨mem_smoothSet.mpr ⟨Nat.ordCompl_pos p (by omega), ?_, fun q hq => ?_⟩,
      Nat.not_dvd_ordCompl hp (by omega)⟩, ?_, ?_⟩
    · exact (Nat.div_le_self _ _).trans h2
    · exact h3 q (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primeFactors.mp hq).1,
        (Nat.mem_primeFactors.mp hq).2.1.trans (Nat.ordCompl_dvd a p), by omega⟩)
    · show a.factorization p < X + 1
      have := Nat.factorization_lt p (show a ≠ 0 by omega); omega
    · show a / p ^ a.factorization p * p ^ a.factorization p ≤ X
      rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]; exact h2
  · rintro ⟨u, i⟩ h
    rw [mem_sigma, mem_filter, mem_filter] at h
    dsimp only at h
    obtain ⟨⟨hu, hpu⟩, -⟩ := h
    have hu0 : u ≠ 0 := by have := (mem_smoothSet.mp hu).1; omega
    have hfac : (u * p ^ i).factorization p = i := by
      rw [Nat.factorization_mul hu0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpu,
        zero_add]
    dsimp only
    rw [hfac, Nat.mul_div_cancel _ (pow_pos hp.pos i)]
  · intro a _
    dsimp only
    rw [mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
  · intro _ _
    rfl

/-- `log a = Σ_{p < Q} v_p(a) log p` on the `Q`-smooth numbers. -/
theorem log_eq_sum_factorization {Q a : ℕ} (ha : 1 ≤ a) (hs : ∀ p ∈ a.primeFactors, p < Q) :
    Real.log a = ∑ p ∈ (range Q).filter Nat.Prime, (a.factorization p : ℝ) * Real.log p := by
  have hprod : (∏ p ∈ a.primeFactors, p ^ a.factorization p : ℕ) = a := by
    have := Nat.prod_factorization_pow_eq_self (show a ≠ 0 by omega)
    rwa [Finsupp.prod, Nat.support_factorization] at this
  have hlog : Real.log a = ∑ p ∈ a.primeFactors, (a.factorization p : ℝ) * Real.log p := by
    conv_lhs => rw [← hprod]
    push_cast
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast
      (Nat.prime_of_mem_primeFactors hp).ne_zero))]
    exact sum_congr rfl fun p _ => by rw [Real.log_pow]
  rw [hlog]
  refine sum_subset (fun p hp => mem_filter.mpr ⟨mem_range.mpr (hs p hp),
    Nat.prime_of_mem_primeFactors hp⟩) fun p _ hp => ?_
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hp (Nat.mem_primeFactors.mpr
    ⟨(mem_filter.mp ‹_›).2, h, by omega⟩)), Nat.cast_zero, zero_mul]

/-- The ladder constant `M_Q = Σ_{p < Q} log p/(p − 1)`. -/
def ladderConstant (Q : ℕ) : ℝ := ∑ p ∈ (range Q).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)

theorem ladderConstant_nonneg (Q : ℕ) : 0 ≤ ladderConstant Q :=
  sum_nonneg fun p hp => div_nonneg (Real.log_natCast_nonneg p)
    (by have := (mem_filter.mp hp).2.one_lt; have : (1 : ℝ) < p := by exact_mod_cast this
        linarith)

/-- `Σ_{i < j ≤ X, u p^j ≤ X} p^{−j} ≤ p^{−i}/(p − 1)`. -/
theorem sum_up_ladder_le {p u X i : ℕ} (hp : p.Prime) (hu : 1 ≤ u) :
    ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ j ≤ X then 1 / ((u * p ^ j : ℕ) : ℝ) else 0) ≤
      1 / ((u * p ^ i : ℕ) : ℝ) * (1 / ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  calc ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ j ≤ X then 1 / ((u * p ^ j : ℕ) : ℝ) else 0)
      ≤ ∑ j ∈ range (X + 1), (if i < j then 1 / ((u * p ^ j : ℕ) : ℝ) else 0) :=
        sum_le_sum fun j _ => by
          split_ifs with h1 h2 <;> first | exact le_rfl | (exact absurd h1.1 h2) | positivity
    _ ≤ ∑ j ∈ range (i + 1 + X), (if i < j then 1 / ((u * p ^ j : ℕ) : ℝ) else 0) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          fun j _ _ => by split_ifs <;> positivity
    _ = ∑ k ∈ range X, 1 / ((u * p ^ i : ℕ) : ℝ) * ((1 / (p : ℝ)) * (1 / (p : ℝ)) ^ k) := by
        rw [Finset.sum_range_add]
        have h0 : ∑ j ∈ range (i + 1), (if i < j then 1 / ((u * p ^ j : ℕ) : ℝ) else 0) = 0 :=
          sum_eq_zero fun j hj => if_neg (by have := mem_range.mp hj; omega)
        rw [h0, zero_add]
        refine sum_congr rfl fun k _ => ?_
        rw [if_pos (by omega)]
        push_cast
        rw [pow_add, pow_succ, one_div_pow]
        field_simp
    _ = 1 / ((u * p ^ i : ℕ) : ℝ) * ((1 / (p : ℝ)) * ∑ k ∈ range X, (1 / (p : ℝ)) ^ k) := by
        rw [mul_sum, mul_sum]
    _ ≤ 1 / ((u * p ^ i : ℕ) : ℝ) * ((1 / (p : ℝ)) * (1 / (1 - 1 / p))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hr0) (by positivity)
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := X) hr0 hr1
        rwa [← range_eq_Ico, pow_zero] at this
    _ = 1 / ((u * p ^ i : ℕ) : ℝ) * (1 / ((p : ℝ) - 1)) := by
        congr 1
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp

/-- One prime of the halo bound, ladder by ladder. -/
theorem halo_ladder_aux {Q X p : ℕ} (hp : p ∈ (range Q).filter Nat.Prime) (u : ℕ → ℝ) :
    ∑ a ∈ smoothSet Q X, Real.log p * (1 / (a : ℝ) * (a.factorization p : ℝ) * u a ^ 2) ≤
      2 * (∑ v ∈ (smoothSet Q X).filter (fun v => ¬ p ∣ v), ∑ i ∈ range (X + 1),
        ∑ j ∈ range (X + 1), if i < j ∧ v * p ^ j ≤ X then
          Real.log p / ((v * p ^ j : ℕ) : ℝ) * (u (v * p ^ j) - u (v * p ^ i)) ^ 2 else 0) +
      2 * (Real.log p / ((p : ℝ) - 1)) * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * u a ^ 2 := by
  obtain ⟨hpQ, hpp⟩ := mem_filter.mp hp
  have hpQ' := mem_range.mp hpQ
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [sum_smoothSet_eq_ladders hpp hpQ',
    sum_smoothSet_eq_ladders hpp hpQ' (fun a => 1 / (a : ℝ) * u a ^ 2), mul_sum, mul_sum,
    ← sum_add_distrib]
  refine sum_le_sum fun v hv => ?_
  obtain ⟨hvS, hpv⟩ := mem_filter.mp hv
  have hv1 := (mem_smoothSet.mp hvS).1
  have hv0 : v ≠ 0 := by omega
  -- the valuation along the ladder
  have hval : ∀ i : ℕ, ((v * p ^ i).factorization p : ℝ) = i := fun i => by
    rw [Nat.factorization_mul hv0 (pow_ne_zero _ hpp.ne_zero), Finsupp.add_apply,
      hpp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpv,
      zero_add]
  set x : ℕ → ℝ := fun i => u (v * p ^ i)
  -- `i x_i² ≤ Σ_{l < i} (2(x_i − x_l)² + 2x_l²)`
  have hpt : ∀ i : ℕ, (i : ℝ) * x i ^ 2 ≤ ∑ l ∈ range i, (2 * (x i - x l) ^ 2 + 2 * x l ^ 2) := by
    intro i
    calc (i : ℝ) * x i ^ 2 = ∑ _l ∈ range i, x i ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun l _ => by nlinarith [sq_nonneg (x i - 2 * x l)]
  -- the energy and mass parts of the ladder
  have hE : ∑ i ∈ (range (X + 1)).filter (fun i => v * p ^ i ≤ X),
      Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ) * ∑ l ∈ range i, 2 * (x i - x l) ^ 2) =
      2 * ∑ l ∈ range (X + 1), ∑ i ∈ range (X + 1),
        (if l < i ∧ v * p ^ i ≤ X then
          Real.log p / ((v * p ^ i : ℕ) : ℝ) * (u (v * p ^ i) - u (v * p ^ l)) ^ 2 else 0) := by
    rw [sum_filter]
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    split_ifs with hiX
    · rw [← sum_range_add_sum_Ico _ (show i ≤ X + 1 by have := mem_range.mp hi; omega)]
      have hrest : ∑ l ∈ Ico i (X + 1), 2 * (if l < i ∧ v * p ^ i ≤ X then
          Real.log p / ((v * p ^ i : ℕ) : ℝ) * (u (v * p ^ i) - u (v * p ^ l)) ^ 2 else 0) = 0 :=
        sum_eq_zero fun l hl => by rw [if_neg (by have := (mem_Ico.mp hl).1; omega), mul_zero]
      rw [hrest, add_zero]
      refine sum_congr rfl fun l hl => ?_
      rw [if_pos ⟨mem_range.mp hl, hiX⟩]
      simp only [x]; ring
    · exact (sum_eq_zero fun l _ => by rw [if_neg (fun h => hiX h.2), mul_zero]).symm
  have hM : ∑ i ∈ (range (X + 1)).filter (fun i => v * p ^ i ≤ X),
      Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ) * ∑ l ∈ range i, 2 * x l ^ 2) ≤
      2 * (Real.log p / ((p : ℝ) - 1)) * ∑ i ∈ (range (X + 1)).filter (fun i => v * p ^ i ≤ X),
        1 / ((v * p ^ i : ℕ) : ℝ) * u (v * p ^ i) ^ 2 := by
    rw [sum_filter, sum_filter, mul_sum]
    have hswap : ∑ i ∈ range (X + 1), (if v * p ^ i ≤ X then
        Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ) * ∑ l ∈ range i, 2 * x l ^ 2) else 0) =
        ∑ l ∈ range (X + 1), 2 * x l ^ 2 * (Real.log p * ∑ i ∈ range (X + 1),
          (if l < i ∧ v * p ^ i ≤ X then 1 / ((v * p ^ i : ℕ) : ℝ) else 0)) := by
      have : ∀ i ∈ range (X + 1), (if v * p ^ i ≤ X then
          Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ) * ∑ l ∈ range i, 2 * x l ^ 2) else 0) =
          ∑ l ∈ range (X + 1), (if l < i ∧ v * p ^ i ≤ X then
            2 * x l ^ 2 * (Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ))) else 0) := by
        intro i hi
        split_ifs with hiX
        · rw [← sum_range_add_sum_Ico _ (show i ≤ X + 1 by have := mem_range.mp hi; omega)]
          have hrest : ∑ l ∈ Ico i (X + 1), (if l < i ∧ v * p ^ i ≤ X then
              2 * x l ^ 2 * (Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ))) else 0) = 0 :=
            sum_eq_zero fun l hl => if_neg (by have := (mem_Ico.mp hl).1; omega)
          rw [hrest, add_zero, mul_sum, mul_sum]
          exact sum_congr rfl fun l hl => by rw [if_pos ⟨mem_range.mp hl, hiX⟩]; ring
        · exact (sum_eq_zero fun l _ => if_neg (fun h => hiX h.2)).symm
      rw [sum_congr rfl this, sum_comm]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by split_ifs <;> ring
    rw [hswap]
    refine sum_le_sum fun l _ => ?_
    by_cases hlX : v * p ^ l ≤ X
    · rw [if_pos hlX]
      have hup := sum_up_ladder_le (X := X) (i := l) hpp hv1
      have := mul_le_mul_of_nonneg_left hup hlp
      have hx : 0 ≤ 2 * x l ^ 2 := by positivity
      calc 2 * x l ^ 2 * (Real.log p * ∑ i ∈ range (X + 1),
            (if l < i ∧ v * p ^ i ≤ X then 1 / ((v * p ^ i : ℕ) : ℝ) else 0))
          ≤ 2 * x l ^ 2 * (Real.log p * (1 / ((v * p ^ l : ℕ) : ℝ) * (1 / ((p : ℝ) - 1)))) :=
            mul_le_mul_of_nonneg_left this hx
        _ = 2 * (Real.log p / ((p : ℝ) - 1)) * (1 / ((v * p ^ l : ℕ) : ℝ) * u (v * p ^ l) ^ 2) := by
            simp only [x]; ring
    · rw [if_neg hlX]
      have : ∑ i ∈ range (X + 1), (if l < i ∧ v * p ^ i ≤ X then 1 / ((v * p ^ i : ℕ) : ℝ) else 0) = 0 :=
        sum_eq_zero fun i _ => if_neg fun h => hlX (le_trans (Nat.mul_le_mul_left v
          (Nat.pow_le_pow_right hpp.pos h.1.le)) h.2)
      rw [this]
      simp
  -- assemble the ladder
  calc ∑ i ∈ (range (X + 1)).filter (fun i => v * p ^ i ≤ X),
        Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ) * ((v * p ^ i).factorization p : ℝ) * u (v * p ^ i) ^ 2)
      ≤ ∑ i ∈ (range (X + 1)).filter (fun i => v * p ^ i ≤ X),
        (Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ) * ∑ l ∈ range i, 2 * (x i - x l) ^ 2) +
          Real.log p * (1 / ((v * p ^ i : ℕ) : ℝ) * ∑ l ∈ range i, 2 * x l ^ 2)) := by
        refine sum_le_sum fun i _ => ?_
        rw [hval, ← mul_add, ← mul_add, ← sum_add_distrib]
        refine mul_le_mul_of_nonneg_left ?_ hlp
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hpt i) (by positivity)
    _ ≤ 2 * ∑ l ∈ range (X + 1), ∑ i ∈ range (X + 1),
          (if l < i ∧ v * p ^ i ≤ X then
            Real.log p / ((v * p ^ i : ℕ) : ℝ) * (u (v * p ^ i) - u (v * p ^ l)) ^ 2 else 0) +
        2 * (Real.log p / ((p : ℝ) - 1)) * ∑ i ∈ (range (X + 1)).filter (fun i => v * p ^ i ≤ X),
          1 / ((v * p ^ i : ℕ) : ℝ) * u (v * p ^ i) ^ 2 := by
        rw [sum_add_distrib, hE]
        exact add_le_add le_rfl hM

/-- **The halo pays its mass**: `Σ (1/a) log a · u_a² ≤ 2E(u) + 2M_Q Σ (1/a) u_a²`. -/
theorem sum_log_mul_sq_le_smoothEnergy (Q X : ℕ) (u : ℕ → ℝ) :
    ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * Real.log a * u a ^ 2 ≤
      2 * smoothEnergy Q X u + 2 * ladderConstant Q * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * u a ^ 2 := by
  have hlog : ∀ a ∈ smoothSet Q X, 1 / (a : ℝ) * Real.log a * u a ^ 2 =
      ∑ p ∈ (range Q).filter Nat.Prime, Real.log p * (1 / (a : ℝ) * (a.factorization p : ℝ) * u a ^ 2) :=
    fun a ha => by
      obtain ⟨h1, -, h3⟩ := mem_smoothSet.mp ha
      rw [log_eq_sum_factorization h1 h3, mul_sum, sum_mul]
      exact sum_congr rfl fun p _ => by ring
  have hper : ∀ p ∈ (range Q).filter Nat.Prime,
      ∑ a ∈ smoothSet Q X, Real.log p * (1 / (a : ℝ) * (a.factorization p : ℝ) * u a ^ 2) ≤
        2 * (∑ v ∈ (smoothSet Q X).filter (fun v => ¬ p ∣ v), ∑ i ∈ range (X + 1),
          ∑ j ∈ range (X + 1), if i < j ∧ v * p ^ j ≤ X then
            Real.log p / ((v * p ^ j : ℕ) : ℝ) * (u (v * p ^ j) - u (v * p ^ i)) ^ 2 else 0) +
        2 * (Real.log p / ((p : ℝ) - 1)) * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * u a ^ 2 := by
    intro p hp
    exact halo_ladder_aux hp u
  calc ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * Real.log a * u a ^ 2
      = ∑ p ∈ (range Q).filter Nat.Prime, ∑ a ∈ smoothSet Q X,
          Real.log p * (1 / (a : ℝ) * (a.factorization p : ℝ) * u a ^ 2) := by
        rw [sum_congr rfl hlog, sum_comm]
    _ ≤ ∑ p ∈ (range Q).filter Nat.Prime,
        (2 * (∑ v ∈ (smoothSet Q X).filter (fun v => ¬ p ∣ v), ∑ i ∈ range (X + 1),
          ∑ j ∈ range (X + 1), if i < j ∧ v * p ^ j ≤ X then
            Real.log p / ((v * p ^ j : ℕ) : ℝ) * (u (v * p ^ j) - u (v * p ^ i)) ^ 2 else 0) +
        2 * (Real.log p / ((p : ℝ) - 1)) * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * u a ^ 2) :=
        sum_le_sum hper
    _ = 2 * smoothEnergy Q X u + 2 * ladderConstant Q * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * u a ^ 2 := by
        rw [sum_add_distrib, ← mul_sum, ← sum_mul, ← mul_sum]
        rfl


/-! ### 5. Zero extension and the gap -/

/-- The zero extension of `h − mean` from `[1, X]`. -/
def zeroExt (Q X : ℕ) (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n ≤ X then h n - wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h else 0

theorem smoothVar_le_boxVar (Q X : ℕ) (h : ℕ → ℝ) : smoothVar Q X h ≤ boxVar X Q (zeroExt Q X h) := by
  set c := wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h
  set c' := wMean (smoothBox X Q) (fun a => 1 / (a : ℝ)) (zeroExt Q X h)
  calc smoothVar Q X h ≤ ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - (c + c')) ^ 2 :=
        wVar_le (fun a _ => by positivity) _
    _ = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (zeroExt Q X h a - c') ^ 2 :=
        sum_congr rfl fun a ha => by
          rw [zeroExt, if_pos (mem_smoothSet.mp ha).2.1]; ring
    _ ≤ ∑ a ∈ smoothBox X Q, 1 / (a : ℝ) * (zeroExt Q X h a - c') ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (smoothSet_subset_smoothBox Q X) fun a _ _ => by positivity
    _ = boxVar X Q (zeroExt Q X h) := rfl

/-- The boundary of `[1, X]` in the box: edges `a → a p^k` with `a ≤ X < a p^k`. -/
def smoothBoundary (Q X : ℕ) (h : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (range Q).filter Nat.Prime, ∑ u ∈ (smoothSet Q X).filter (fun u => ¬ p ∣ u),
    ∑ i ∈ range (X + 1), ∑ j ∈ range (X + 1),
      if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then Real.log p / ((u * p ^ j : ℕ) : ℝ) *
        (h (u * p ^ i) - wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h) ^ 2 else 0

/-- **The extension costs only the boundary**: `E_box(h⁰) ≤ E_X(h) + boundary`. -/
theorem boxEnergy_zeroExt_le (Q X : ℕ) (h : ℕ → ℝ) :
    boxEnergy X Q (zeroExt Q X h) ≤ smoothEnergy Q X h + smoothBoundary Q X h := by
  rw [boxEnergy, smoothEnergy, smoothBoundary, ← sum_add_distrib]
  refine sum_le_sum fun p hp => ?_
  have hpp := (mem_filter.mp hp).2
  -- ladders based above `X` carry nothing
  have hsub : (smoothSet Q X).filter (fun u => ¬ p ∣ u) ⊆ (smoothBox X Q).filter (fun u => ¬ p ∣ u) :=
    fun u hu => mem_filter.mpr ⟨smoothSet_subset_smoothBox Q X (mem_filter.mp hu).1,
      (mem_filter.mp hu).2⟩
  rw [← sum_subset hsub fun u hu hu' => ?_, ← sum_add_distrib]
  · refine sum_le_sum fun u hu => ?_
    have hu1 := (mem_smoothSet.mp (mem_filter.mp hu).1).1
    rw [ladderEnergy, ← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    have hmono : ∀ {i j : ℕ}, i < j → u * p ^ i ≤ u * p ^ j := fun hij =>
      Nat.mul_le_mul_left u (Nat.pow_le_pow_right hpp.pos hij.le)
    by_cases hij : i < j
    · by_cases hjX : u * p ^ j ≤ X
      · rw [if_pos hij, if_pos ⟨hij, hjX⟩, if_neg (fun h => absurd h.2.2 (not_lt.mpr hjX)),
          add_zero, zeroExt, zeroExt, if_pos hjX, if_pos ((hmono hij).trans hjX)]
        ring_nf; exact le_rfl
      · by_cases hiX : u * p ^ i ≤ X
        · rw [if_pos hij, if_neg (fun h => hjX h.2), if_pos ⟨hij, hiX, not_le.mp hjX⟩, zero_add,
            zeroExt, zeroExt, if_neg hjX, if_pos hiX]
          ring_nf; exact le_rfl
        · rw [if_pos hij, if_neg (fun h => hjX h.2), if_neg (fun h => hiX h.2.1), add_zero,
            zeroExt, zeroExt, if_neg hjX, if_neg hiX, sub_self, sq, mul_zero, mul_zero]
    · rw [if_neg hij, if_neg (fun h => hij h.1), if_neg (fun h => hij h.1), add_zero]
  · -- `u ∈ box \ [1, X]`: `u > X`
    obtain ⟨huB, hpu⟩ := mem_filter.mp hu
    have hnot : ¬ u ≤ X := fun hle => hu' (mem_filter.mpr ⟨mem_smoothSet.mpr
      ⟨(mem_smoothBox.mp huB).1, hle, (mem_smoothBox.mp huB).2.1⟩, hpu⟩)
    refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
    have hle : ∀ k, ¬ u * p ^ k ≤ X := fun k hk => hnot ((Nat.le_mul_of_pos_right u
      (pow_pos hpp.pos k)).trans hk)
    split_ifs
    · rw [zeroExt, zeroExt, if_neg (hle j), if_neg (hle i), sub_self, sq, mul_zero, mul_zero]
    · rfl

/-- `p^{−k} ≤ √(a/X) (1/√p)^k` when `X < a p^k`. -/
theorem inv_pow_le_sqrt {p a X k : ℕ} (hp : 2 ≤ p) (hX : 1 ≤ X) (hk : X < a * p ^ k) :
    1 / (p : ℝ) ^ k ≤ Real.sqrt ((a : ℝ) / X) * (1 / Real.sqrt p) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  set r := Real.sqrt (p : ℝ)
  have hr0 : 0 < r := Real.sqrt_pos.mpr hp0
  have hr2 : r ^ 2 = p := Real.sq_sqrt hp0.le
  have hpk : (p : ℝ) ^ k = (r ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, hr2]
  have hrk : 0 < r ^ k := pow_pos hr0 k
  have hak : 1 / (p : ℝ) ^ k ≤ (a : ℝ) / X := by
    rw [div_le_div_iff₀ (by positivity) hX0, one_mul]
    have : (X : ℝ) < a * p ^ k := by exact_mod_cast hk
    linarith
  have hsq : 1 / r ^ k ≤ Real.sqrt ((a : ℝ) / X) := by
    have : Real.sqrt (1 / (p : ℝ) ^ k) = 1 / r ^ k := by
      rw [hpk, one_div, Real.sqrt_inv, Real.sqrt_sq hrk.le, one_div]
    rw [← this]
    exact Real.sqrt_le_sqrt hak
  calc 1 / (p : ℝ) ^ k = 1 / r ^ k * (1 / r ^ k) := by rw [hpk, sq, one_div_mul_one_div]
    _ ≤ Real.sqrt ((a : ℝ) / X) * (1 / r ^ k) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = Real.sqrt ((a : ℝ) / X) * (1 / r) ^ k := by rw [one_div_pow]

/-- The boundary weight of a point `a = u p^i ≤ X`: `Σ_{j > i, X < u p^j} log p/(u p^j) ≤
4 (log p/a) √(a/X)`. -/
theorem sum_boundary_weight_le {p u X i : ℕ} (hp : p.Prime) (hu : 1 ≤ u) (hX : 1 ≤ X) :
    ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
      Real.log p / ((u * p ^ j : ℕ) : ℝ) else 0) ≤
      4 * (Real.log p / ((u * p ^ i : ℕ) : ℝ)) * Real.sqrt (((u * p ^ i : ℕ) : ℝ) / X) := by
  have hp2 := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  set q := 1 / Real.sqrt (p : ℝ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 3 / 4 := by
    have h2 : (4 / 3 : ℝ) ≤ Real.sqrt p := by
      rw [show (4 / 3 : ℝ) = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      have h2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      exact Real.sqrt_le_sqrt (by nlinarith)
    rw [div_le_iff₀ (by positivity)]; nlinarith
  set B := Real.log p / ((u * p ^ i : ℕ) : ℝ) * Real.sqrt (((u * p ^ i : ℕ) : ℝ) / X)
  have hB : 0 ≤ B := by positivity
  calc ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
        Real.log p / ((u * p ^ j : ℕ) : ℝ) else 0)
      ≤ ∑ j ∈ range (i + (X + 1)), (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
        Real.log p / ((u * p ^ j : ℕ) : ℝ) else 0) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          fun j _ _ => by split_ifs <;> positivity
    _ = ∑ k ∈ range (X + 1), (if 0 < k ∧ u * p ^ i ≤ X ∧ X < u * p ^ (i + k) then
        Real.log p / ((u * p ^ (i + k) : ℕ) : ℝ) else 0) := by
        rw [Finset.sum_range_add]
        have h0 : ∑ j ∈ range i, (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
            Real.log p / ((u * p ^ j : ℕ) : ℝ) else 0) = 0 :=
          sum_eq_zero fun j hj => if_neg (by have := mem_range.mp hj; omega)
        rw [h0, zero_add]
        refine sum_congr rfl fun k _ => ?_
        congr 1
        exact propext ⟨fun h => ⟨by omega, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
    _ ≤ ∑ k ∈ range (X + 1), B * q ^ k := by
        refine sum_le_sum fun k _ => ?_
        split_ifs with hk
        · have hkey := inv_pow_le_sqrt (a := u * p ^ i) (k := k) hp2 hX
            (by rw [mul_assoc, ← pow_add]; exact hk.2.2)
          have e : Real.log p / ((u * p ^ (i + k) : ℕ) : ℝ) =
              Real.log p / ((u * p ^ i : ℕ) : ℝ) * (1 / (p : ℝ) ^ k) := by
            push_cast; rw [pow_add]; field_simp
          rw [e]
          calc Real.log p / ((u * p ^ i : ℕ) : ℝ) * (1 / (p : ℝ) ^ k)
              ≤ Real.log p / ((u * p ^ i : ℕ) : ℝ) *
                (Real.sqrt (((u * p ^ i : ℕ) : ℝ) / X) * q ^ k) :=
                mul_le_mul_of_nonneg_left hkey (by positivity)
            _ = B * q ^ k := by simp only [B]; ring
        · positivity
    _ = B * ∑ k ∈ range (X + 1), q ^ k := by rw [mul_sum]
    _ ≤ B * 4 := by
        refine mul_le_mul_of_nonneg_left ?_ hB
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := X + 1) hq0 (by linarith)
        rw [← range_eq_Ico, pow_zero] at this
        refine this.trans ?_
        rw [div_le_iff₀ (by linarith)]; linarith
    _ = 4 * (Real.log p / ((u * p ^ i : ℕ) : ℝ)) * Real.sqrt (((u * p ^ i : ℕ) : ℝ) / X) := by
        simp only [B]; ring

/-- The sum `L_Q = Σ_{p < Q} log p`. -/
def logSum (Q : ℕ) : ℝ := ∑ p ∈ (range Q).filter Nat.Prime, Real.log p

theorem logSum_nonneg (Q : ℕ) : 0 ≤ logSum Q := sum_nonneg fun p _ => Real.log_natCast_nonneg p

/-- **The boundary**: `Σ_{boundary} ≤ 4 L_Q Σ_a (1/a)(h_a − c)² √(a/X)`. -/
theorem smoothBoundary_le {Q X : ℕ} (hX : 1 ≤ X) (h : ℕ → ℝ) :
    smoothBoundary Q X h ≤ 4 * logSum Q * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) *
      (h a - wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h) ^ 2 * Real.sqrt ((a : ℝ) / X) := by
  set c := wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h
  set S := ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2 * Real.sqrt ((a : ℝ) / X)
  suffices hp : smoothBoundary Q X h ≤ ∑ p ∈ (range Q).filter Nat.Prime, 4 * Real.log p * S by
    refine hp.trans (le_of_eq ?_)
    rw [← sum_mul, ← mul_sum]; rfl
  rw [smoothBoundary]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨hpQ, hpp⟩ := mem_filter.mp hp
  rw [show S = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2 * Real.sqrt ((a : ℝ) / X) from rfl,
    sum_smoothSet_eq_ladders hpp (mem_range.mp hpQ), mul_sum]
  refine sum_le_sum fun u hu => ?_
  have hu1 := (mem_smoothSet.mp (mem_filter.mp hu).1).1
  rw [sum_filter, mul_sum]
  refine sum_le_sum fun i _ => ?_
  have hpull : ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
      Real.log p / ((u * p ^ j : ℕ) : ℝ) * (h (u * p ^ i) - c) ^ 2 else 0) =
      (h (u * p ^ i) - c) ^ 2 * ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
        Real.log p / ((u * p ^ j : ℕ) : ℝ) else 0) := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => by split_ifs <;> ring
  rw [hpull]
  have hD : 0 ≤ (h (u * p ^ i) - c) ^ 2 := sq_nonneg _
  have hw := sum_boundary_weight_le (X := X) (i := i) hpp hu1 hX
  split_ifs with hiX
  · calc (h (u * p ^ i) - c) ^ 2 * ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
          Real.log p / ((u * p ^ j : ℕ) : ℝ) else 0)
        ≤ (h (u * p ^ i) - c) ^ 2 * (4 * (Real.log p / ((u * p ^ i : ℕ) : ℝ)) *
          Real.sqrt (((u * p ^ i : ℕ) : ℝ) / X)) := mul_le_mul_of_nonneg_left hw hD
      _ = 4 * Real.log p * (1 / ((u * p ^ i : ℕ) : ℝ) * (h (u * p ^ i) - c) ^ 2 *
          Real.sqrt (((u * p ^ i : ℕ) : ℝ) / X)) := by ring
  · have : ∑ j ∈ range (X + 1), (if i < j ∧ u * p ^ i ≤ X ∧ X < u * p ^ j then
        Real.log p / ((u * p ^ j : ℕ) : ℝ) else 0) = 0 :=
      sum_eq_zero fun j _ => if_neg fun h => hiX h.2.1
    rw [this]
    simp

theorem smoothEnergy_sub_const (Q X : ℕ) (h : ℕ → ℝ) (c : ℝ) :
    smoothEnergy Q X (fun n => h n - c) = smoothEnergy Q X h := by
  refine sum_congr rfl fun p _ => sum_congr rfl fun u _ => sum_congr rfl fun i _ =>
    sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- **From the box to the horizon**: if the zero extension of `h − mean` has box Poincaré constant
`g`, then `(g − 4L/X^{1/4} − 16LM/log X) Var ≤ (1 + 16L/log X) E` on the `Q`-smooth numbers of
`[1, X]`, `X ≥ 2`: the boundary is small below `√X` and paid by the halo above. -/
theorem smoothVar_mul_le_of_box {Q X : ℕ} (hX : 2 ≤ X) (h : ℕ → ℝ) {g : ℝ}
    (hbox : g * smoothVar Q X h ≤ boxEnergy X Q (zeroExt Q X h)) :
    (g - 4 * logSum Q / Real.sqrt (Real.sqrt X) -
        16 * logSum Q * ladderConstant Q / Real.log X) * smoothVar Q X h ≤
      (1 + 16 * logSum Q / Real.log X) * smoothEnergy Q X h := by
  set c := wMean (smoothSet Q X) (fun a => 1 / (a : ℝ)) h
  set V := smoothVar Q X h
  set E := smoothEnergy Q X h
  set L := logSum Q
  set M := ladderConstant Q
  have hL := logSum_nonneg Q
  have hM := ladderConstant_nonneg Q
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hT : 0 < Real.sqrt (Real.sqrt X) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hX0)
  have hV : V = ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2 := rfl
  have hVnn : 0 ≤ V := wVar_nonneg fun _ _ => by positivity
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    sum_nonneg fun _ _ => by
      split_ifs
      · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)
      · exact le_rfl
  have hext := boxEnergy_zeroExt_le Q X h
  -- the boundary: small below `√X`, the halo above
  have hbd := smoothBoundary_le (Q := Q) (by omega : 1 ≤ X) h
  have hsplit : ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * (h a - c) ^ 2 * Real.sqrt ((a : ℝ) / X) ≤
      V / Real.sqrt (Real.sqrt X) +
        2 / Real.log X * ∑ a ∈ smoothSet Q X, 1 / (a : ℝ) * Real.log a * (h a - c) ^ 2 := by
    rw [hV, div_eq_mul_one_div, sum_mul, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun a ha => ?_
    obtain ⟨ha1, haX, -⟩ := mem_smoothSet.mp ha
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hD : 0 ≤ 1 / (a : ℝ) * (h a - c) ^ 2 := by positivity
    have hlog_a : 0 ≤ Real.log a := Real.log_natCast_nonneg a
    by_cases hsq : a * a ≤ X
    · -- `√(a/X) ≤ X^{−1/4}`
      have hs : Real.sqrt ((a : ℝ) / X) ≤ 1 / Real.sqrt (Real.sqrt X) := by
        have h1 : (a : ℝ) ≤ Real.sqrt X := by
          rw [show (a : ℝ) = Real.sqrt ((a : ℝ) * a) by rw [Real.sqrt_mul_self ha0.le]]
          exact Real.sqrt_le_sqrt (by exact_mod_cast hsq)
        have h2 : (a : ℝ) / X ≤ 1 / Real.sqrt X := by
          rw [div_le_div_iff₀ hX0 (Real.sqrt_pos.mpr hX0), one_mul]
          have : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
          nlinarith [Real.sqrt_nonneg (X : ℝ)]
        calc Real.sqrt ((a : ℝ) / X) ≤ Real.sqrt (1 / Real.sqrt X) := Real.sqrt_le_sqrt h2
          _ = 1 / Real.sqrt (Real.sqrt X) := by rw [Real.sqrt_div' 1 (Real.sqrt_nonneg _),
              Real.sqrt_one]
      have : 0 ≤ 2 / Real.log X * (1 / (a : ℝ) * Real.log a * (h a - c) ^ 2) := by positivity
      calc 1 / (a : ℝ) * (h a - c) ^ 2 * Real.sqrt ((a : ℝ) / X)
          ≤ 1 / (a : ℝ) * (h a - c) ^ 2 * (1 / Real.sqrt (Real.sqrt X)) :=
            mul_le_mul_of_nonneg_left hs hD
        _ ≤ _ := le_add_of_nonneg_right this
    · -- the halo: `log a ≥ ½ log X`
      have hs : Real.sqrt ((a : ℝ) / X) ≤ 1 := by
        rw [Real.sqrt_le_one]
        exact div_le_one_of_le₀ (by exact_mod_cast haX) hX0.le
      have hla : Real.log X ≤ 2 * Real.log a := by
        rw [← Real.log_rpow ha0, show ((a : ℝ) ^ (2 : ℝ)) = (a : ℝ) * a by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring]
        exact Real.log_le_log hX0 (by exact_mod_cast (not_le.mp hsq).le)
      have h1 : 1 / (a : ℝ) * (h a - c) ^ 2 ≤ 2 / Real.log X * (1 / (a : ℝ) * Real.log a * (h a - c) ^ 2) := by
        have hr : 1 ≤ 2 / Real.log X * Real.log a := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlX]; linarith
        calc 1 / (a : ℝ) * (h a - c) ^ 2 = 1 * (1 / (a : ℝ) * (h a - c) ^ 2) := (one_mul _).symm
          _ ≤ (2 / Real.log X * Real.log a) * (1 / (a : ℝ) * (h a - c) ^ 2) :=
              mul_le_mul_of_nonneg_right hr hD
          _ = 2 / Real.log X * (1 / (a : ℝ) * Real.log a * (h a - c) ^ 2) := by ring
      have h0 : 0 ≤ 1 / (a : ℝ) * (h a - c) ^ 2 * (1 / Real.sqrt (Real.sqrt X)) := by positivity
      calc 1 / (a : ℝ) * (h a - c) ^ 2 * Real.sqrt ((a : ℝ) / X) ≤ 1 / (a : ℝ) * (h a - c) ^ 2 :=
            mul_le_of_le_one_right hD hs
        _ ≤ _ := h1.trans (le_add_of_nonneg_left h0)
  have hhalo := sum_log_mul_sq_le_smoothEnergy Q X (fun n => h n - c)
  rw [smoothEnergy_sub_const, ← hV] at hhalo
  -- assemble
  have hB : smoothBoundary Q X h ≤ 4 * L * (V / Real.sqrt (Real.sqrt X) +
      2 / Real.log X * (2 * E + 2 * M * V)) :=
    hbd.trans (mul_le_mul_of_nonneg_left (hsplit.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hhalo (by positivity)))) (by positivity))
  have key : g * V ≤ E + 4 * L * (V / Real.sqrt (Real.sqrt X) +
      2 / Real.log X * (2 * E + 2 * M * V)) :=
    hbox.trans (hext.trans (add_le_add le_rfl hB))
  have e1 : 4 * L * (V / Real.sqrt (Real.sqrt X) + 2 / Real.log X * (2 * E + 2 * M * V)) =
      4 * L / Real.sqrt (Real.sqrt X) * V + 16 * L * M / Real.log X * V + 16 * L / Real.log X * E := by
    field_simp; ring
  rw [e1] at key
  nlinarith

/-- **The finite-prime chain at a horizon**: `(g_X − 4L/X^{1/4} − 16LM/log X) Var ≤
(1 + 16L/log X) E` for `X ≥ 2`. -/
theorem smoothVar_mul_le {Q X : ℕ} (hX : 2 ≤ X) (h : ℕ → ℝ) :
    (boxGap X - 4 * logSum Q / Real.sqrt (Real.sqrt X) -
        16 * logSum Q * ladderConstant Q / Real.log X) * smoothVar Q X h ≤
      (1 + 16 * logSum Q / Real.log X) * smoothEnergy Q X h := by
  have hg : 0 ≤ boxGap X := by
    rw [boxGap]
    have : (1 / 2 : ℝ) ^ (X + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    nlinarith
  exact smoothVar_mul_le_of_box hX h ((mul_le_mul_of_nonneg_left (smoothVar_le_boxVar Q X h) hg).trans
    (boxGap_mul_boxVar_le (J := X) (by omega) Q (zeroExt Q X h)))

/-- **The finite-prime valuation chain has gap `2 log 2`.** For every finite prime cutoff `Q` and
every `ε > 0`, eventually in `X`, `(2 log 2 − ε) Var ≤ E` on the `Q`-smooth numbers of `[1, X]`. -/
theorem eventually_smoothVar_le_smoothEnergy (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → ∀ h : ℕ → ℝ,
      (2 * Real.log 2 - ε) * smoothVar Q X h ≤ smoothEnergy Q X h := by
  set A := 2 * Real.log 2
  set L := logSum Q
  set M := ladderConstant Q
  have hA : 0 < A := by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  have hL := logSum_nonneg Q
  have hM := ladderConstant_nonneg Q
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq := (Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have ev := ((hlog.eventually_ge_atTop (max 1 (max (64 * A * L / ε) (128 * L * M / ε)))).and
    (hsq.eventually_ge_atTop (32 * L / ε + 1))).and
    ((hpow.eventually_le_const (show (0 : ℝ) < ε / (4 * A) by positivity)).and
      (Filter.eventually_ge_atTop 2))
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp ev
  refine ⟨X₀, fun X hX h => ?_⟩
  obtain ⟨⟨hl, hs⟩, hp, hX2⟩ := hX₀ X hX
  simp only [Function.comp] at hl hs
  have hl1 : 1 ≤ Real.log X := (le_max_left _ _).trans hl
  have hl2 : 64 * A * L / ε ≤ Real.log X := ((le_max_left _ _).trans (le_max_right _ _)).trans hl
  have hl3 : 128 * L * M / ε ≤ Real.log X := ((le_max_right _ _).trans (le_max_right _ _)).trans hl
  have hlX : 0 < Real.log X := by linarith
  have hT : 0 < Real.sqrt (Real.sqrt X) := by linarith [show 0 ≤ 32 * L / ε by positivity]
  have hpow' : (1 / 2 : ℝ) ^ (X + 1) ≤ ε / (4 * A) :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ X)).trans hp
  have hmain := smoothVar_mul_le (Q := Q) hX2 h
  have hV : 0 ≤ smoothVar Q X h := wVar_nonneg fun _ _ => by positivity
  -- the three small quantities
  have ht : A * (16 * L / Real.log X) ≤ ε / 4 := by
    rw [div_le_iff₀ hε] at hl2
    rw [mul_div_assoc', div_le_iff₀ hlX]; nlinarith
  have hs1 : 4 * L / Real.sqrt (Real.sqrt X) ≤ ε / 8 := by
    rw [div_le_iff₀ hT]
    have : 32 * L / ε ≤ Real.sqrt (Real.sqrt X) := by linarith
    rw [div_le_iff₀ hε] at this; nlinarith
  have hs2 : 16 * L * M / Real.log X ≤ ε / 8 := by
    rw [div_le_iff₀ hε] at hl3
    rw [div_le_iff₀ hlX]; nlinarith
  have hg : A - ε / 4 ≤ boxGap X := by
    rw [boxGap]
    have := mul_le_mul_of_nonneg_left hpow' hA.le
    rw [mul_div_assoc', mul_comm A ε, mul_div_mul_right _ _ hA.ne'] at this
    nlinarith
  have hcoef : (A - ε) * (1 + 16 * L / Real.log X) ≤
      boxGap X - 4 * L / Real.sqrt (Real.sqrt X) - 16 * L * M / Real.log X := by
    have h16 : 0 ≤ 16 * L / Real.log X := by positivity
    nlinarith
  have h1t : 0 < 1 + 16 * L / Real.log X := by positivity
  have := mul_le_mul_of_nonneg_right hcoef hV
  have h2 : (A - ε) * smoothVar Q X h * (1 + 16 * L / Real.log X) ≤
      smoothEnergy Q X h * (1 + 16 * L / Real.log X) := by nlinarith
  exact le_of_mul_le_mul_right h2 h1t

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

