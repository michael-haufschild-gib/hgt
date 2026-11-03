import GaloisForLFunctions.WindowTowerOfSpecZ.TheRationalLatticeOfAWindow
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# No Tate positivity is uniform along the tower

In every fixed positive dimension `k`, the Tate operators `ρ_A(J_k)` stop being positive once the
window is long enough. The witness is the star of the rational lattice centred at `1` with the primes
`p ≤ M` as leaves: on it the Tate form is `y₁² + Σ_p y_p² + Σ_p J_k(p)p^{−1/2}y₁y_p` (no two leaves are
linked, since `p·q` and `p/q` are not primes), and the amplitudes `y₁ = 1`, `y_p = −J_k(p)/(2√p)` give
`1 − X/4`, `X = Σ_{p≤M} J_k(p)²/p`.

* **Star test** (`exists_tateFunction_neg_of_primeSum`): if `M < e^A` and `Σ_{p≤M}(p^k − 1)²/p > 4`, some
  window test has `τ_H(k) < 0`.
* **No uniform Tate positivity** (`exists_tateFunction_neg`): for every `k > 0` there is a window
  length `A` and a window test with `τ_H(k) < 0`, because `Σ_p 1/p` diverges.

Together with the positivity below `kN^kψ_{1/2}(N) ≤ log 2` (`tateFunction_nonneg_of_le_log_two`), the Tate
horizon `k*(A)` is positive on every window and tends to `0` along the tower: only the tangent at
dimension zero — Weil's form — is uniform.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory MeasureTheory Set

variable {A : ℝ}

/-- The primes `≤ M`. -/
def primesTo (M : ℕ) : Finset ℕ := (Finset.range (M + 1)).filter Nat.Prime

/-- The star configuration `{1} ∪ {p ≤ M}`. -/
def starConfig (M : ℕ) : Finset ℚ := insert 1 ((primesTo M).image (Nat.cast : ℕ → ℚ))

theorem mem_starConfig {M : ℕ} {q : ℚ} :
    q ∈ starConfig M ↔ q = 1 ∨ ∃ p ∈ primesTo M, (p : ℚ) = q := by
  simp [starConfig]

theorem mem_primesTo {M p : ℕ} : p ∈ primesTo M ↔ p ≤ M ∧ p.Prime := by
  simp [primesTo]

/-- The multiplicative coincidences of the star: `s = n r` with `n ≥ 2` only for `r = 1`, `s = n` prime. -/
theorem star_coincidence {M n : ℕ} (hn : 2 ≤ n) {r s : ℚ} (hr : r ∈ starConfig M)
    (hs : s ∈ starConfig M) : (s : ℝ) = n * r ↔ r = 1 ∧ s = n ∧ n ∈ primesTo M := by
  have hcast : (s : ℝ) = n * r ↔ s = n * r := by
    constructor
    · intro h; exact_mod_cast h
    · intro h; rw [h]; push_cast; ring
  rw [hcast]
  rcases mem_starConfig.mp hr with rfl | ⟨p, hp, rfl⟩
  · rw [mul_one]
    constructor
    · intro h
      subst h
      refine ⟨rfl, rfl, ?_⟩
      rcases mem_starConfig.mp hs with h1 | ⟨q, hq, hqn⟩
      · exact absurd h1 (by exact_mod_cast (by omega : n ≠ 1))
      · have : q = n := by exact_mod_cast hqn
        rwa [← this]
    · rintro ⟨-, h, -⟩; exact h
  · obtain ⟨hpM, hpp⟩ := mem_primesTo.mp hp
    constructor
    · intro h
      exfalso
      rcases mem_starConfig.mp hs with h1 | ⟨q, hq, hqn⟩
      · rw [h1] at h
        have : (1 : ℕ) = n * p := by exact_mod_cast h
        have := hpp.two_le
        nlinarith
      · have hq' : q = n * p := by exact_mod_cast hqn.trans h
        have hqp := (mem_primesTo.mp hq).2
        rw [hq', Nat.prime_mul_iff] at hqp
        rcases hqp with ⟨_, h1⟩ | ⟨_, h1⟩
        · exact absurd h1 hpp.one_lt.ne'
        · omega
    · rintro ⟨h1, -, -⟩
      exfalso
      have : (p : ℕ) = 1 := by exact_mod_cast h1
      exact hpp.one_lt.ne' this

theorem one_not_mem_image_primes (M : ℕ) : (1 : ℚ) ∉ (primesTo M).image (Nat.cast : ℕ → ℚ) := by
  intro h
  obtain ⟨p, hp, hp1⟩ := Finset.mem_image.mp h
  have : p = 1 := by exact_mod_cast hp1
  exact (mem_primesTo.mp hp).2.one_lt.ne' this

/-- **Star test**: if `M < e^A` and `Σ_{p≤M} J_k(p)²/p > 4`, the Tate function is negative on some window
test. -/
theorem exists_tateFunction_neg_of_primeSum {M : ℕ} (hM : (M : ℝ) < Real.exp A) {k : ℝ}
    (hX : 4 < ∑ p ∈ primesTo M, jordanTotient k p ^ 2 / p) :
    ∃ H, IsWindowTest A H ∧ tateFunction A H k < 0 := by
  set P := primesTo M
  set N := windowLevel A
  have hMN : M ≤ N := Nat.le_floor hM.le
  -- the configuration fits in the window
  have hpos : ∀ r ∈ starConfig M, (0 : ℚ) < r := fun r hr => by
    rcases mem_starConfig.mp hr with rfl | ⟨p, hp, rfl⟩
    · norm_num
    · exact_mod_cast (mem_primesTo.mp hp).2.pos
  have hPne : P.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hX
    linarith
  have hM1 : 1 ≤ M := by
    obtain ⟨p, hp⟩ := hPne
    exact (mem_primesTo.mp hp).2.one_lt.le.trans (mem_primesTo.mp hp).1
  have hle : ∀ r ∈ starConfig M, 1 ≤ (r : ℝ) ∧ (r : ℝ) ≤ M := fun r hr => by
    rcases mem_starConfig.mp hr with rfl | ⟨p, hp, rfl⟩
    · exact ⟨by norm_num, by push_cast; exact_mod_cast hM1⟩
    · obtain ⟨hpM, hpp⟩ := mem_primesTo.mp hp
      push_cast
      exact ⟨by exact_mod_cast hpp.one_lt.le, by exact_mod_cast hpM⟩
  have hspread : ∀ r ∈ starConfig M, ∀ s ∈ starConfig M, Real.log s - Real.log r < A := by
    intro r hr s hs
    obtain ⟨hr1, -⟩ := hle r hr
    obtain ⟨hs1, hsM⟩ := hle s hs
    have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have h1 : Real.log s ≤ Real.log M := Real.log_le_log (by linarith) hsM
    have h2 : 0 ≤ Real.log r := Real.log_nonneg hr1
    have h3 : Real.log M < A := (Real.log_lt_iff_lt_exp (by linarith)).mpr hM
    linarith
  -- amplitudes
  set X := ∑ p ∈ P, jordanTotient k p ^ 2 / p
  set w : ℕ → ℝ := fun p => jordanTotient k p / Real.sqrt p
  set y : ℚ → ℝ := fun q => (if q = 1 then 1 else 0) +
    ∑ p ∈ P, if q = (p : ℚ) then -(w p / 2) else 0
  have hy1 : y 1 = 1 := by
    simp only [y, if_true]
    rw [Finset.sum_eq_zero fun p hp => if_neg fun h => by
      have : p = 1 := by exact_mod_cast h.symm
      exact (mem_primesTo.mp hp).2.one_lt.ne' this]
    ring
  have hyp : ∀ p ∈ P, y p = -(w p / 2) := fun p hp => by
    simp only [y]
    rw [if_neg (fun h => (mem_primesTo.mp hp).2.one_lt.ne' (by exact_mod_cast h)),
      Finset.sum_eq_single_of_mem p hp fun q _ hq => if_neg fun h => hq (Nat.cast_injective h).symm,
      if_pos rfl, zero_add]
  obtain ⟨H, hH, I, hI, hval⟩ := exists_windowTest_eq_heckeForm (starConfig M) hpos hspread N
    (fun n => jordanTotient k n / Real.sqrt n) y
  refine ⟨H, hH, ?_⟩
  -- the Tate function is the Hecke form with the Jordan weights
  have htate : tateFunction A H k = (∫ u, H u ^ 2) +
      ∑ n ∈ Finset.Icc 2 N, jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) := by
    have hN1 : 1 ≤ N := hM1.trans hMN
    rw [tateFunction_eq hH, show Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) by ext; simp; omega,
      Finset.sum_insert (by simp), jordanTotient_one]
    simp only [Nat.cast_one, Real.sqrt_one, div_one, one_mul, Real.log_one, add_zero]
    have e : ∫ u, H u * H u = ∫ u, H u ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun u => by simp [sq])
    rw [e]
  -- evaluate the Hecke form of the star
  have hgraph : ∀ n ∈ Finset.Icc 2 N, (∑ r ∈ starConfig M, ∑ s ∈ starConfig M,
      if (s : ℝ) = n * r then y r * y s else 0) = if n ∈ P then y 1 * y n else 0 := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hcongr : ∀ r ∈ starConfig M, ∀ s ∈ starConfig M,
        (if (s : ℝ) = n * r then y r * y s else 0) =
          if r = 1 ∧ s = n ∧ n ∈ P then y r * y s else 0 := fun r hr s hs => by
      rw [if_congr (star_coincidence hn2 hr hs) rfl rfl]
    rw [Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s hs => hcongr r hr s hs]
    by_cases hnP : n ∈ P
    · rw [if_pos hnP, Finset.sum_eq_single_of_mem (1 : ℚ) (mem_starConfig.mpr (Or.inl rfl))
        fun r _ hr1 => Finset.sum_eq_zero fun s _ =>
          if_neg fun (h : r = 1 ∧ s = (n : ℚ) ∧ n ∈ P) => hr1 h.1]
      have hnS : (n : ℚ) ∈ starConfig M :=
        mem_starConfig.mpr (Or.inr ⟨n, hnP, rfl⟩)
      rw [Finset.sum_eq_single_of_mem (n : ℚ) hnS fun s _ hs =>
        if_neg fun (h : (1 : ℚ) = 1 ∧ s = (n : ℚ) ∧ n ∈ P) => hs h.2.1,
        if_pos ⟨rfl, rfl, hnP⟩]
    · rw [if_neg hnP]
      exact Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ =>
        if_neg fun h => hnP h.2.2
  -- the value `I(1 − X/4)`
  have hsq : ∑ r ∈ starConfig M, y r ^ 2 = 1 + X / 4 := by
    rw [starConfig, Finset.sum_insert (one_not_mem_image_primes M), hy1,
      Finset.sum_image fun a _ b _ h => by exact_mod_cast h]
    have hsum : ∑ p ∈ P, y p ^ 2 = ∑ p ∈ P, (-(w p / 2)) ^ 2 :=
      Finset.sum_congr rfl fun p hp => by rw [hyp p hp]
    rw [hsum, one_pow]
    simp only [X, w]
    rw [Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesTo.mp hp).2.pos
    rw [show (-(jordanTotient k p / Real.sqrt p / 2)) ^ 2 =
      jordanTotient k p ^ 2 / Real.sqrt p ^ 2 / 4 by ring, Real.sq_sqrt hp0.le]
  have hfold : ∑ n ∈ Finset.Icc 2 N, jordanTotient k n / Real.sqrt n *
      (∑ r ∈ starConfig M, ∑ s ∈ starConfig M, if (s : ℝ) = n * r then y r * y s else 0) =
      -(X / 2) := by
    rw [Finset.sum_congr rfl fun n hn => by rw [hgraph n hn]]
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilt : (Finset.Icc 2 N).filter (· ∈ P) = P := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, and_iff_right_iff_imp]
      intro hp
      obtain ⟨hpM, hpp⟩ := mem_primesTo.mp hp
      exact ⟨hpp.two_le, hpM.trans hMN⟩
    rw [hfilt]
    simp only [X]
    rw [Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hy1, hyp p hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_primesTo.mp hp).2.pos
    simp only [w]
    rw [show jordanTotient k p / Real.sqrt p * (1 * -(jordanTotient k p / Real.sqrt p / 2)) =
      -(jordanTotient k p ^ 2 / Real.sqrt p ^ 2 / 2) by ring, Real.sq_sqrt hp0.le]
  rw [htate, hval, hsq, hfold]
  nlinarith [mul_pos hI (by linarith : (0 : ℝ) < X / 4 - 1)]

/-- **No uniform Tate positivity**: for every `k > 0` some window carries a test with `τ_H(k) < 0`. -/
theorem exists_tateFunction_neg {k : ℝ} (hk : 0 < k) :
    ∃ A : ℝ, ∃ H, IsWindowTest A H ∧ tateFunction A H k < 0 := by
  -- `J_k(p)²/p ≥ (2^k − 1)²/p` and `Σ 1/p` diverges
  set c := ((2 : ℝ) ^ k - 1) ^ 2
  have hc : 0 < c := by
    have : 1 < (2 : ℝ) ^ k := Real.one_lt_rpow (by norm_num) hk
    positivity
  have hdiv := not_summable_one_div_on_primes
  have hf : ∀ n, 0 ≤ (Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n)) n := fun n =>
    indicator_nonneg (fun _ _ => by positivity) n
  obtain ⟨M₀, hM₀⟩ : ∃ M₀, 4 / c < ∑ i ∈ Finset.range M₀,
      Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i := by
    by_contra h
    push Not at h
    exact hdiv (summable_of_sum_range_le hf h)
  set M := M₀
  have hrange : ∑ i ∈ Finset.range M₀, Set.indicator {p | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i ≤
      ∑ p ∈ primesTo M, (1 : ℝ) / p := by
    rw [primesTo, Finset.sum_filter]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ M₀))
      fun i _ _ => hf i).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Set.indicator, Set.mem_setOf_eq]
  have hX : 4 < ∑ p ∈ primesTo M, jordanTotient k p ^ 2 / p := by
    have hbound : ∀ p ∈ primesTo M, c * (1 / (p : ℝ)) ≤ jordanTotient k p ^ 2 / p := fun p hp => by
      have hpp := (mem_primesTo.mp hp).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hJ : jordanTotient k p = (p : ℝ) ^ k - 1 := by
        simpa using jordanTotient_prime_pow hpp k (a := 1) le_rfl
      have h2 : (2 : ℝ) ^ k ≤ (p : ℝ) ^ k :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hpp.two_le) hk.le
      have h1 : 0 ≤ (2 : ℝ) ^ k - 1 := by linarith [Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hk]
      rw [hJ, mul_one_div]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h1 (by linarith) 2) hp0.le
    have := Finset.sum_le_sum hbound
    rw [← Finset.mul_sum] at this
    have h4 : 4 < c * ∑ p ∈ primesTo M, (1 : ℝ) / p := by
      have := (div_lt_iff₀' hc).mp (hM₀.trans_le hrange)
      linarith
    linarith
  refine ⟨Real.log (M + 1), exists_tateFunction_neg_of_primeSum ?_ hX⟩
  rw [Real.exp_log (by positivity)]
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
