import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheForcedJumpsOfAProducer

/-!
# The coefficient mass and the peak of a producer

The multiplicity of a producer is periodic and palindromic, which makes `w = −Σ c(k) = −D_c(0)` its
exact maximum, attained at `L − 1`, with mean `w/2` over a period.

The coefficients are controlled by the multiplicities through Möbius inversion. The pronic series
weighs `g(r)` by `1/r²`, and inversion against `⌊K/d⌋` needs `g(r)` weighted by `1/r`. So on an
alphabet in `[1, K]`,

`Σ |c(k)| ≤ 2K (m (1 + log K) + (K + 1) T)`,  `T` the excess of the slope.

With `ε = A − 1` the rate, the Chebyshev bound of the producer becomes
`ψ(x) ≤ (1 + ε) x + 2K (5 + log K)(1 + log K + (K + 1) ε)(1 + log x)(1 + log x / log 2)`.
The error term of a producer is never free: it grows like `K` and then like `εK²`.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The peak `w = −Σ c(k)`. -/
def peak (c : ℕ →₀ ℤ) : ℤ := -∑ k ∈ c.support, c k

/-- The coefficient mass `Σ |c(k)|`. -/
def coeffMass (c : ℕ →₀ ℤ) : ℝ := ∑ k ∈ c.support, |(c k : ℝ)|

/-- The rate of a producer: the excess of the normalized slope over `1`. -/
def rate (c : ℕ →₀ ℤ) (m B : ℕ) : ℝ := normSlope c m B - 1

theorem coeffMass_nonneg (c : ℕ →₀ ℤ) : 0 ≤ coeffMass c :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem peak_le_coeffMass (c : ℕ →₀ ℤ) : (peak c : ℝ) ≤ coeffMass c := by
  rw [peak, coeffMass]
  push_cast
  rw [← sum_neg_distrib]
  exact sum_le_sum fun k _ => neg_le_abs _

private lemma sum_Icc_one_eq_range (f : ℕ → ℝ) (K : ℕ) :
    ∑ r ∈ Icc 1 K, f r = ∑ j ∈ range K, f (j + 1) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Swapping a divisor sum: `Σ_{k ≤ K} Σ_{d ∣ k} f(d) = Σ_{d ≤ K} ⌊K/d⌋ f(d)`. -/
private lemma sum_Icc_sum_divisors (f : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Icc 1 K, ∑ d ∈ k.divisors, f d = ∑ d ∈ Icc 1 K, ((K / d : ℕ) : ℝ) * f d := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hstep : ∀ d ∈ Icc 1 (K + 1), (((K + 1) / d : ℕ) : ℝ) * f d =
        ((K / d : ℕ) : ℝ) * f d + if d ∣ K + 1 then f d else 0 := by
      intro d _
      rw [Nat.succ_div]
      split_ifs <;> push_cast <;> ring
    rw [sum_congr rfl hstep, sum_add_distrib, Finset.sum_Icc_succ_top (a := 1) (b := K) (by omega)
      (f := fun d => ((K / d : ℕ) : ℝ) * f d)]
    have hlast : ((K / (K + 1) : ℕ) : ℝ) * f (K + 1) = 0 := by
      rw [Nat.div_eq_of_lt (Nat.lt_succ_self K)]
      simp
    rw [hlast, add_zero, ← sum_filter]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.succ_pos K), Nat.le_of_dvd (Nat.succ_pos K) hd⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, Nat.succ_ne_zero K⟩

/-- A coefficient is bounded by the divisor sum of the increments. -/
theorem abs_coeff_le_sum_increment (c : ℕ →₀ ℤ) {n : ℕ} (hn : 0 < n) :
    |(c n : ℝ)| ≤ ∑ d ∈ n.divisors, |(increment c d : ℝ)| := by
  rw [coeff_eq_moebius_increment c hn]
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hle : ∀ x ∈ n.divisorsAntidiagonal,
      |((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * (increment c x.2 : ℝ)| ≤
        |(increment c x.2 : ℝ)| := by
    intro x _
    have hmu : |((ArithmeticFunction.moebius x.1 : ℤ) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_mul]
    nlinarith [abs_nonneg (increment c x.2 : ℝ)]
  refine (sum_le_sum hle).trans (le_of_eq ?_)
  exact Nat.sum_divisorsAntidiagonal' (fun _ b => |(increment c b : ℝ)|)

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- The product of the alphabet, a common period of the multiplicity. -/
def period (c : ℕ →₀ ℤ) : ℕ := ∏ k ∈ c.support, k

theorem period_pos (hP : IsProducer c m B) : 0 < period c :=
  prod_pos fun k hk => Nat.pos_of_ne_zero fun h => by
    subst h; exact Finsupp.mem_support_iff.mp hk hP.zero

theorem dvd_period (k : ℕ) (hk : k ∈ c.support) : k ∣ period c := dvd_prod_of_mem _ hk

/-- **The palindromic law.** `g(L − 1 − r) + g(r) = w` on a period. -/
theorem stepWeight_reflect (hP : IsProducer c m B) {r : ℕ} (hr : r < period c) :
    stepWeight c (period c - 1 - r) + stepWeight c r = peak c :=
  stepWeight_reflect_add hP.zero hP.balanced dvd_period hr

/-- **The peak bounds the multiplicity.** `g(r) ≤ w` for all `r`. -/
theorem stepWeight_le_peak (hP : IsProducer c m B) (r : ℕ) : stepWeight c r ≤ peak c := by
  have hL := hP.period_pos
  have hmod : r = r / period c * period c + r % period c := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod r _).symm
  rw [hmod, stepWeight_periodic hP.zero hP.balanced dvd_period]
  have := hP.stepWeight_reflect (Nat.mod_lt r hL)
  have h0 := hP.nonneg (period c - 1 - r % period c)
  linarith

/-- **The peak is attained** at `L − 1`. -/
theorem stepWeight_period_sub_one (hP : IsProducer c m B) :
    stepWeight c (period c - 1) = peak c := by
  have := hP.stepWeight_reflect (r := 0) hP.period_pos
  rw [stepWeight_zero, add_zero, Nat.sub_zero] at this
  exact this

/-- **The mean of the multiplicity over a period is half the peak.** -/
theorem two_mul_sum_range_stepWeight (hP : IsProducer c m B) :
    2 * ∑ r ∈ range (period c), stepWeight c r = (period c : ℤ) * peak c := by
  have hsum : ∑ r ∈ range (period c), stepWeight c (period c - 1 - r) =
      ∑ r ∈ range (period c), stepWeight c r :=
    Finset.sum_range_reflect (fun r => stepWeight c r) (period c)
  have hadd : ∑ r ∈ range (period c), (stepWeight c (period c - 1 - r) + stepWeight c r) =
      ∑ _r ∈ range (period c), peak c :=
    sum_congr rfl fun r hr => hP.stepWeight_reflect (mem_range.mp hr)
  rw [sum_add_distrib, hsum, sum_const, card_range, nsmul_eq_mul] at hadd
  linarith

/-- The peak is at least the multiplicity floor. -/
theorem le_peak (hP : IsProducer c m B) : (m : ℤ) ≤ peak c := by
  have h1 := hP.window 1 (mem_Ico.mpr ⟨le_rfl, by have := hP.two_le_B; omega⟩)
  exact h1.trans (hP.stepWeight_le_peak 1)

/-- The excess is positive: a prime beyond the alphabet always jumps. -/
theorem excess_pos (hP : IsProducer c m B) : 0 < excess c m B := by
  classical
  obtain ⟨p, hpK, hp⟩ := Nat.exists_infinite_primes (c.support.sup id + 1)
  have hK : AlphabetLE c (c.support.sup id) := fun k hk => Finset.le_sup (f := id) hk
  have hrough := isRough_of_prime_of_alphabet hK hp (by omega)
  have h := hP.sum_rough_le_excess {p} (by
    intro r hr
    rw [mem_singleton] at hr
    subst hr
    exact ⟨hp.two_le, hrough⟩)
  rw [sum_singleton] at h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hm := hP.m_pos
  exact lt_of_lt_of_le (by positivity) h

/-- The excess in terms of the rate: `T = m (1 − 1/B) ε`. -/
theorem excess_eq_rate (hP : IsProducer c m B) :
    excess c m B = (m : ℝ) * (1 - 1 / (B : ℝ)) * rate c m B := by
  have hd : (m : ℝ) * (1 - 1 / (B : ℝ)) ≠ 0 := (mul_pos hP.m_pos hP.one_sub_pos).ne'
  rw [excess, rate, normSlope, mul_sub, mul_div_cancel₀ _ hd, mul_one]

theorem rate_pos (hP : IsProducer c m B) : 0 < rate c m B := by
  have hd : 0 < (m : ℝ) * (1 - 1 / (B : ℝ)) := mul_pos hP.m_pos hP.one_sub_pos
  have h := hP.excess_pos
  rw [hP.excess_eq_rate] at h
  exact pos_of_mul_pos_of_pos_left h hd.le |> fun h' => h'

/-- The excess is at most `m ε`. -/
theorem excess_le (hP : IsProducer c m B) : excess c m B ≤ (m : ℝ) * rate c m B := by
  rw [hP.excess_eq_rate]
  have hr := hP.rate_pos
  have hm := hP.m_pos
  have h1 : 1 - 1 / (B : ℝ) ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
    linarith
  calc (m : ℝ) * (1 - 1 / (B : ℝ)) * rate c m B
      ≤ (m : ℝ) * 1 * rate c m B := by gcongr
    _ = (m : ℝ) * rate c m B := by ring

/-- `g(r)/r ≤ m/r + (K + 1) · excessTerm`, for `r = j + 1 ≤ K`. -/
private lemma stepWeight_div_le (hP : IsProducer c m B) {K j : ℕ} (hj : j + 1 ≤ K) :
    (stepWeight c (j + 1) : ℝ) / ((j : ℝ) + 1) ≤
      (m : ℝ) / ((j : ℝ) + 1) + ((K : ℝ) + 1) * excessTerm m B c j := by
  have hE := hP.excessTerm_nonneg j
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  have hKj : (j : ℝ) + 2 ≤ (K : ℝ) + 1 := by
    have : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hj
    push_cast at this
    linarith
  have hkey : ((j : ℝ) + 2) * excessTerm m B c j ≤ ((K : ℝ) + 1) * excessTerm m B c j :=
    mul_le_mul_of_nonneg_right hKj hE
  have hid : ((j : ℝ) + 2) * excessTerm m B c j =
      ((stepWeight c (j + 1) : ℝ) - (if j + 1 < B then (m : ℝ) else 0)) / ((j : ℝ) + 1) := by
    rw [excessTerm]
    field_simp
  have hite : (if j + 1 < B then (m : ℝ) else 0) ≤ m := by
    split_ifs
    · exact le_rfl
    · exact hP.m_pos.le
  have hdiv : (if j + 1 < B then (m : ℝ) else 0) / ((j : ℝ) + 1) ≤ (m : ℝ) / ((j : ℝ) + 1) :=
    div_le_div_of_nonneg_right hite hj1.le
  have hsplit : (stepWeight c (j + 1) : ℝ) / ((j : ℝ) + 1) =
      ((stepWeight c (j + 1) : ℝ) - (if j + 1 < B then (m : ℝ) else 0)) / ((j : ℝ) + 1) +
        (if j + 1 < B then (m : ℝ) else 0) / ((j : ℝ) + 1) := by
    rw [← add_div, sub_add_cancel]
  linarith

/-- The harmonic mass of the multiplicity: `Σ_{r ≤ K} g(r)/r ≤ m (1 + log K) + (K + 1) T`. -/
theorem sum_stepWeight_div_le (hP : IsProducer c m B) (K : ℕ) :
    ∑ r ∈ Icc 1 K, (stepWeight c r : ℝ) / r ≤
      (m : ℝ) * (1 + Real.log K) + ((K : ℝ) + 1) * excess c m B := by
  have hharm : ∑ j ∈ range K, (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 + Real.log K := by
    have h := harmonic_le_one_add_log K
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    rw [sum_Icc_one_eq_range (fun i => ((i : ℝ))⁻¹) K] at h
    refine le_trans (le_of_eq (sum_congr rfl fun j _ => ?_)) h
    push_cast
    rw [one_div]
  have hex : ∑ j ∈ range K, excessTerm m B c j ≤ excess c m B :=
    sum_le_hasSum _ (fun j _ => hP.excessTerm_nonneg j) hP.hasSum_excess
  rw [sum_Icc_one_eq_range (fun r => (stepWeight c r : ℝ) / r) K]
  have hterm : ∀ j ∈ range K, (stepWeight c (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ) ≤
      (m : ℝ) * (1 / ((j : ℝ) + 1)) + ((K : ℝ) + 1) * excessTerm m B c j := by
    intro j hj
    have := hP.stepWeight_div_le (K := K) (j := j) (by have := mem_range.mp hj; omega)
    push_cast
    rw [mul_one_div]
    exact this
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hm := hP.m_pos
  have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  exact add_le_add (mul_le_mul_of_nonneg_left hharm hm.le) (mul_le_mul_of_nonneg_left hex hK1)

/-- The same mass shifted by one. -/
private lemma sum_stepWeight_pred_div_le (hP : IsProducer c m B) (K : ℕ) :
    ∑ d ∈ Icc 1 (K + 1), (stepWeight c (d - 1) : ℝ) / d ≤ ∑ r ∈ Icc 1 K, (stepWeight c r : ℝ) / r := by
  induction K with
  | zero => simp [stepWeight_zero]
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (a := 1) (b := K) (by omega)]
    have hg : (0 : ℝ) ≤ stepWeight c (K + 1) := by exact_mod_cast hP.nonneg (K + 1)
    have hdiv : (stepWeight c (K + 1 + 1 - 1) : ℝ) / ((K + 1 + 1 : ℕ) : ℝ) ≤
        (stepWeight c (K + 1) : ℝ) / ((K + 1 : ℕ) : ℝ) := by
      rw [Nat.add_sub_cancel]
      refine div_le_div_of_nonneg_left hg (by positivity) ?_
      push_cast
      linarith
    linarith

private lemma sum_stepWeight_pred_div_le' (hP : IsProducer c m B) (K : ℕ) :
    ∑ d ∈ Icc 1 K, (stepWeight c (d - 1) : ℝ) / d ≤ ∑ r ∈ Icc 1 K, (stepWeight c r : ℝ) / r := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
    refine (hP.sum_stepWeight_pred_div_le n).trans ?_
    rw [Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega)]
    have hg : (0 : ℝ) ≤ (stepWeight c (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) :=
      div_nonneg (by exact_mod_cast hP.nonneg (n + 1)) (by positivity)
    linarith

/-- **The coefficient mass law.** On an alphabet in `[1, K]`,
`Σ |c(k)| ≤ 2K (m (1 + log K) + (K + 1) T)`. -/
theorem coeffMass_le (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) :
    coeffMass c ≤ 2 * (K : ℝ) * ((m : ℝ) * (1 + Real.log K) + ((K : ℝ) + 1) * excess c m B) := by
  have hsub := hP.support_subset_Icc hK
  have hstep : coeffMass c ≤ ∑ k ∈ Icc 1 K, ∑ d ∈ k.divisors, |(increment c d : ℝ)| := by
    calc coeffMass c ≤ ∑ k ∈ c.support, ∑ d ∈ k.divisors, |(increment c d : ℝ)| := by
          refine sum_le_sum fun k hk => abs_coeff_le_sum_increment c ?_
          exact (mem_Icc.mp (hsub hk)).1
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          sum_nonneg fun _ _ => abs_nonneg _
  rw [sum_Icc_sum_divisors] at hstep
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hterm : ∀ d ∈ Icc 1 K, ((K / d : ℕ) : ℝ) * |(increment c d : ℝ)| ≤
      (K : ℝ) * ((stepWeight c d : ℝ) / d + (stepWeight c (d - 1) : ℝ) / d) := by
    intro d hd
    obtain ⟨hd1, _⟩ := mem_Icc.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hsucc : (stepWeight c (e + 1) : ℝ) = stepWeight c e + increment c (e + 1) := by
      exact_mod_cast stepWeight_succ c e
    have h0 : (0 : ℝ) ≤ stepWeight c (e + 1) := by exact_mod_cast hP.nonneg (e + 1)
    have h1 : (0 : ℝ) ≤ stepWeight c e := by exact_mod_cast hP.nonneg e
    have habs : |(increment c (e + 1) : ℝ)| ≤ stepWeight c (e + 1) + stepWeight c e := by
      rw [abs_le]
      constructor <;> linarith
    have hdiv : ((K / (e + 1) : ℕ) : ℝ) ≤ (K : ℝ) / ((e + 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [Nat.add_sub_cancel]
    calc ((K / (e + 1) : ℕ) : ℝ) * |(increment c (e + 1) : ℝ)|
        ≤ (K : ℝ) / ((e + 1 : ℕ) : ℝ) * ((stepWeight c (e + 1) : ℝ) + stepWeight c e) :=
          mul_le_mul hdiv habs (abs_nonneg _) (by positivity)
      _ = (K : ℝ) * ((stepWeight c (e + 1) : ℝ) / ((e + 1 : ℕ) : ℝ) +
            (stepWeight c e : ℝ) / ((e + 1 : ℕ) : ℝ)) := by
          field_simp
  have hsum := sum_le_sum hterm
  rw [← mul_sum, sum_add_distrib] at hsum
  have h1 := hP.sum_stepWeight_div_le K
  have h2 := hP.sum_stepWeight_pred_div_le' K
  have hfinal : (K : ℝ) * (∑ d ∈ Icc 1 K, (stepWeight c d : ℝ) / d +
      ∑ d ∈ Icc 1 K, (stepWeight c (d - 1) : ℝ) / d) ≤
      (K : ℝ) * (2 * ((m : ℝ) * (1 + Real.log K) + ((K : ℝ) + 1) * excess c m B)) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  calc coeffMass c ≤ _ := hstep
    _ ≤ _ := hsum
    _ ≤ _ := hfinal
    _ = _ := by ring

/-- **The normalized coefficient mass law.** `Σ|c(k)|/m ≤ 2K (1 + log K + (K + 1) ε)`. -/
theorem coeffMass_div_le (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) :
    coeffMass c / m ≤ 2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * rate c m B) := by
  have hm := hP.m_pos
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [div_le_iff₀ hm]
  refine (hP.coeffMass_le hK).trans ?_
  have hex := hP.excess_le
  have hK1 : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  have hmul : ((K : ℝ) + 1) * excess c m B ≤ ((K : ℝ) + 1) * ((m : ℝ) * rate c m B) :=
    mul_le_mul_of_nonneg_left hex hK1
  have h2 : (0 : ℝ) ≤ 2 * (K : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hmul h2
  nlinarith

/-- The Stirling constant is bounded by the coefficient mass. -/
theorem stencilErrorConst_le_coeffMass (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) :
    stencilErrorConst c ≤ (5 + Real.log K) * coeffMass c := by
  have hsub := hP.support_subset_Icc hK
  rw [stencilErrorConst, coeffMass, mul_sum]
  refine sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hkK⟩ := mem_Icc.mp (hsub hk)
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkKR : (k : ℝ) ≤ K := by exact_mod_cast hkK
  have hlog : Real.log k ≤ Real.log K := Real.log_le_log (by linarith) hkKR
  have habs := abs_nonneg (c k : ℝ)
  nlinarith

/-- **The sharp Chebyshev bound of a producer.** For `x ≥ 1`, with `ε` the rate,
`ψ(x) ≤ (1 + ε) x + 2K (5 + log K)(1 + log K + (K + 1) ε)(1 + log x)(1 + log x / log 2)`. -/
theorem psi_le_sharp (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x ≤ (1 + rate c m B) * x +
      2 * (K : ℝ) * (5 + Real.log K) * (1 + Real.log K + ((K : ℝ) + 1) * rate c m B) *
        ((1 + Real.log x) * (1 + Real.log x / Real.log 2)) := by
  have hm := hP.m_pos
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_natCast_nonneg K
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfac : 0 ≤ (1 + Real.log x) * (1 + Real.log x / Real.log 2) := by positivity
  have hE : stencilErrorConst c / m ≤
      (5 + Real.log K) * (2 * (K : ℝ) * (1 + Real.log K + ((K : ℝ) + 1) * rate c m B)) := by
    have h1 := hP.stencilErrorConst_le_coeffMass hK
    have h2 := hP.coeffMass_div_le hK
    have h3 : stencilErrorConst c / m ≤ (5 + Real.log K) * (coeffMass c / m) := by
      rw [div_le_iff₀ hm]
      calc stencilErrorConst c ≤ (5 + Real.log K) * coeffMass c := h1
        _ = (5 + Real.log K) * (coeffMass c / m) * m := by field_simp
    exact h3.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  have h := hP.psi_le hx
  have hA : normSlope c m B = 1 + rate c m B := by rw [rate]; ring
  rw [hA] at h
  have hmul := mul_le_mul_of_nonneg_right hE hfac
  nlinarith

end IsProducer

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
