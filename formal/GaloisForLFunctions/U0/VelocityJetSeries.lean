/-
# The first Böttcher parameter jet as a lacunary Mahler power series

The logarithmic first parameter jet of the Böttcher deformation of `z² + c` at `c = 0`
satisfies the dyadic Mahler equation `A(t²) = 2·A(t) − t²`, and its unique power-series
solution with zero constant term is the lacunary series `Σ_{j≥0} 2^{-(j+1)} t^{2^{j+1}}`.
This module constructs that series formally, proves the Mahler equation under dyadic
substitution, and proves nonrationality: a rational power series whose denominator does not
vanish at the origin satisfies a backwards linear recurrence on coefficients, so one zero gap
of denominator length kills every later coefficient, while the lacunary series keeps nonzero
coefficients beyond every bound.
-/
import Mathlib
import GaloisForLFunctions.U0.MahlerEndo

namespace GaloisForLFunctions

open PowerSeries

noncomputable section

/-- The dyadic-power support predicate: `n = 2^(j+1)` for some `j`. -/
def IsDyadicPow (n : ℕ) : Prop := ∃ j : ℕ, n = 2 ^ (j + 1)

theorem isDyadicPow_two : IsDyadicPow 2 := ⟨0, rfl⟩

theorem not_isDyadicPow_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) : ¬ IsDyadicPow n := by
  rintro ⟨j, rfl⟩
  exact hn ⟨2 ^ j, by ring⟩

theorem isDyadicPow_double {m : ℕ} (h : IsDyadicPow m) : IsDyadicPow (2 * m) := by
  obtain ⟨j, rfl⟩ := h
  exact ⟨j + 1, by ring⟩

theorem isDyadicPow_of_double {m : ℕ} (hm : 1 < m) (h : IsDyadicPow (2 * m)) :
    IsDyadicPow m := by
  obtain ⟨j, hj⟩ := h
  rcases j with _ | j
  · omega
  · refine ⟨j, ?_⟩
    have : 2 * m = 2 * 2 ^ (j + 1) := by
      rw [hj]
      ring
    omega

theorem not_isDyadicPow_one : ¬ IsDyadicPow 1 := by
  rintro ⟨j, hj⟩
  have : 1 < 2 ^ (j + 1) := Nat.one_lt_two_pow_iff.mpr (by omega)
  omega

/-- Between consecutive dyadic powers there is no dyadic power. -/
theorem not_isDyadicPow_of_between {n j : ℕ} (h₁ : 2 ^ (j + 1) < n) (h₂ : n < 2 ^ (j + 2)) :
    ¬ IsDyadicPow n := by
  rintro ⟨k, rfl⟩
  rcases lt_or_ge k (j + 1) with hk | hk
  · have : 2 ^ (k + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have : 2 ^ (j + 2) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- The lacunary coefficient sequence: `1/n` at the dyadic powers `n = 2^(j+1)`, else `0`. -/
def velocityCoeff (n : ℕ) : ℂ :=
  open scoped Classical in if IsDyadicPow n then (n : ℂ)⁻¹ else 0

theorem velocityCoeff_of_isDyadicPow {n : ℕ} (h : IsDyadicPow n) :
    velocityCoeff n = (n : ℂ)⁻¹ := by
  rw [velocityCoeff, if_pos h]

theorem velocityCoeff_of_not_isDyadicPow {n : ℕ} (h : ¬ IsDyadicPow n) :
    velocityCoeff n = 0 := by
  rw [velocityCoeff, if_neg h]

theorem velocityCoeff_ne_zero_of_isDyadicPow {n : ℕ} (h : IsDyadicPow n) :
    velocityCoeff n ≠ 0 := by
  rw [velocityCoeff_of_isDyadicPow h]
  apply inv_ne_zero
  have hn0 : n ≠ 0 := by
    obtain ⟨j, rfl⟩ := h
    have := Nat.two_pow_pos (j + 1)
    omega
  exact_mod_cast hn0

/-- **The first parameter jet.**  The lacunary series `Σ_{j≥0} 2^{-(j+1)} X^{2^{j+1}}`. -/
def velocityJet : ℂ⟦X⟧ := PowerSeries.mk velocityCoeff

theorem coeff_velocityJet (n : ℕ) : (coeff n) velocityJet = velocityCoeff n :=
  coeff_mk n velocityCoeff

/-- Dyadic substitution `f(t) ↦ f(t²)` at the coefficient level. -/
def dyadicSubst (f : ℂ⟦X⟧) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => open scoped Classical in
    if 2 ∣ n then (coeff (n / 2)) f else 0

theorem coeff_dyadicSubst_even (f : ℂ⟦X⟧) (m : ℕ) :
    (coeff (2 * m)) (dyadicSubst f) = (coeff m) f := by
  classical
  rw [dyadicSubst, coeff_mk, if_pos ⟨m, rfl⟩]
  have hdiv : 2 * m / 2 = m := by omega
  rw [hdiv]

theorem coeff_dyadicSubst_odd (f : ℂ⟦X⟧) {n : ℕ} (hn : ¬ 2 ∣ n) :
    (coeff n) (dyadicSubst f) = 0 := by
  classical
  rw [dyadicSubst, coeff_mk, if_neg hn]

/-- **The dyadic Mahler equation** `A(t²) = 2·A(t) − t²`. -/
theorem dyadicSubst_velocityJet :
    dyadicSubst velocityJet = 2 * velocityJet - X ^ 2 := by
  rw [two_mul]
  ext n
  rw [map_sub, map_add, coeff_velocityJet, coeff_X_pow]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have h2m : n = 2 * m := by omega
    subst h2m
    rw [coeff_dyadicSubst_even, coeff_velocityJet]
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [velocityCoeff_of_not_isDyadicPow (by
          rintro ⟨j, hj⟩
          have := Nat.two_pow_pos (j + 1)
          omega)]
        norm_num
      · rw [velocityCoeff_of_not_isDyadicPow not_isDyadicPow_one,
          velocityCoeff_of_isDyadicPow isDyadicPow_two]
        norm_num
    · have hne2 : 2 * m ≠ 2 := by omega
      rw [if_neg hne2]
      by_cases hdy : IsDyadicPow m
      · rw [velocityCoeff_of_isDyadicPow hdy,
          velocityCoeff_of_isDyadicPow (isDyadicPow_double hdy)]
        have hm0 : (m : ℂ) ≠ 0 := by
          exact_mod_cast (by omega : m ≠ 0)
        push_cast
        field_simp
        ring
      · rw [velocityCoeff_of_not_isDyadicPow hdy,
          velocityCoeff_of_not_isDyadicPow
            (fun h => hdy (isDyadicPow_of_double (by omega) h))]
        ring
  · have hn2 : ¬ 2 ∣ n := by
      rw [Nat.odd_iff] at hodd
      omega
    have hne2 : n ≠ 2 := by
      intro h
      apply hn2
      rw [h]
    rw [coeff_dyadicSubst_odd _ hn2,
      velocityCoeff_of_not_isDyadicPow (not_isDyadicPow_of_odd hn2), if_neg hne2]
    ring

/-! ## Nonrationality of the first jet -/

/-- A power series equal to a rational function regular at the origin satisfies a backwards
linear recurrence of length the denominator degree, beyond the numerator degree. -/
theorem coeff_recurrence {f : ℂ⟦X⟧} {p q : Polynomial ℂ} (hq0 : q.coeff 0 ≠ 0)
    (hf : (q : ℂ⟦X⟧) * f = (p : ℂ⟦X⟧)) {n : ℕ} (hn : p.natDegree < n)
    (hn' : q.natDegree ≤ n) :
    (coeff n) f =
      -(q.coeff 0)⁻¹ * ∑ i ∈ Finset.Icc 1 q.natDegree, q.coeff i * (coeff (n - i)) f := by
  have hcoeff := congrArg (coeff n) hf
  rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hn,
    PowerSeries.coeff_mul] at hcoeff
  have hsum : ∑ ij ∈ Finset.antidiagonal n, (coeff ij.1) (q : ℂ⟦X⟧) * (coeff ij.2) f =
      ∑ i ∈ Finset.range (n + 1), q.coeff i * (coeff (n - i)) f := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (coeff i) (q : ℂ⟦X⟧) * (coeff k) f)]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_coe]
  rw [hsum] at hcoeff
  have hshrink : ∑ i ∈ Finset.range (n + 1), q.coeff i * (coeff (n - i)) f =
      ∑ i ∈ Finset.Icc 0 q.natDegree, q.coeff i * (coeff (n - i)) f := by
    symm
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_range]
      omega
    · intro i _ hi
      rw [Finset.mem_Icc] at hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  rw [hshrink] at hcoeff
  have hsplit : ∑ i ∈ Finset.Icc 0 q.natDegree, q.coeff i * (coeff (n - i)) f =
      q.coeff 0 * (coeff n) f +
        ∑ i ∈ Finset.Icc 1 q.natDegree, q.coeff i * (coeff (n - i)) f := by
    have hins : Finset.Icc 0 q.natDegree = insert 0 (Finset.Icc 1 q.natDegree) := by
      ext i
      simp [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, Finset.sum_insert (by simp)]
    simp
  rw [hsplit] at hcoeff
  have h1 : q.coeff 0 * (coeff n) f =
      -∑ i ∈ Finset.Icc 1 q.natDegree, q.coeff i * (coeff (n - i)) f := by
    linear_combination hcoeff
  calc (coeff n) f = (q.coeff 0)⁻¹ * (q.coeff 0 * (coeff n) f) := by
        field_simp
    _ = (q.coeff 0)⁻¹ *
        -∑ i ∈ Finset.Icc 1 q.natDegree, q.coeff i * (coeff (n - i)) f := by rw [h1]
    _ = -(q.coeff 0)⁻¹ *
        ∑ i ∈ Finset.Icc 1 q.natDegree, q.coeff i * (coeff (n - i)) f := by ring

/-- One all-zero coefficient window of denominator length kills every later coefficient. -/
theorem coeff_eventually_zero_of_gap {f : ℂ⟦X⟧} {p q : Polynomial ℂ} (hq0 : q.coeff 0 ≠ 0)
    (hf : (q : ℂ⟦X⟧) * f = (p : ℂ⟦X⟧)) {N : ℕ} (hNp : p.natDegree < N)
    (hNq : q.natDegree ≤ N)
    (hwindow : ∀ m, N < m → m ≤ N + q.natDegree → (coeff m) f = 0) :
    ∀ n, N < n → (coeff n) f = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge (N + q.natDegree) n with hcase | hcase
    · rw [coeff_recurrence hq0 hf (by omega) (by omega)]
      have hzero : ∀ i ∈ Finset.Icc 1 q.natDegree,
          q.coeff i * (coeff (n - i)) f = 0 := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        rw [ih (n - i) (by omega) (by omega), mul_zero]
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, mul_zero]
    · exact hwindow n hn hcase

/-- **The first parameter jet is not rational.**  No polynomial identity
`q(t)·A(t) = p(t)` with `q(0) ≠ 0` holds: the lacunary gaps beyond every degree bound feed
the recurrence a zero window, forcing all later coefficients to vanish, while dyadic
coefficients persist. -/
theorem velocityJet_not_rational :
    ¬ ∃ p q : Polynomial ℂ, q.coeff 0 ≠ 0 ∧
      (q : ℂ⟦X⟧) * velocityJet = (p : ℂ⟦X⟧) := by
  rintro ⟨p, q, hq0, hf⟩
  set j₀ : ℕ := p.natDegree + q.natDegree + 2 with hj₀
  set N : ℕ := 2 ^ (j₀ + 1) with hN
  have hj₀N : j₀ < N := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hNp : p.natDegree < N := by omega
  have hNq : q.natDegree ≤ N := by omega
  have hwindow : ∀ m, N < m → m ≤ N + q.natDegree → (coeff m) velocityJet = 0 := by
    intro m hm₁ hm₂
    rw [coeff_velocityJet]
    apply velocityCoeff_of_not_isDyadicPow
    apply not_isDyadicPow_of_between (j := j₀) hm₁
    have hpow : 2 ^ (j₀ + 2) = 2 * N := by
      rw [hN]
      ring
    omega
  have hkill := coeff_eventually_zero_of_gap hq0 hf hNp hNq hwindow
  have hbig : (coeff (2 ^ (j₀ + 2))) velocityJet ≠ 0 := by
    rw [coeff_velocityJet]
    exact velocityCoeff_ne_zero_of_isDyadicPow ⟨j₀ + 1, rfl⟩
  apply hbig
  apply hkill
  have : N < 2 * N := by
    have : 0 < N := Nat.two_pow_pos _
    omega
  have hpow : 2 ^ (j₀ + 2) = 2 * N := by
    rw [hN]
    ring
  omega

/-! ## No rational dyadic telescoper -/

/-- Coefficient recursion of a dyadic telescoper equation
`μ·k(t²) − k(t) = γ·t^{2N}`. -/
theorem telescoper_coeff {μ γ : ℂ} {N : ℕ} {k : ℂ⟦X⟧}
    (heq : (C μ : ℂ⟦X⟧) * dyadicSubst k - k = PowerSeries.monomial (2 * N) γ) (n : ℕ) :
    (coeff n) k = μ * (if 2 ∣ n then (coeff (n / 2)) k else 0) -
      (if n = 2 * N then γ else 0) := by
  have h := congrArg (coeff n) heq
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_monomial] at h
  have hd : (coeff n) (dyadicSubst k) = if 2 ∣ n then (coeff (n / 2)) k else 0 := by
    classical
    rw [dyadicSubst, coeff_mk]
  rw [hd] at h
  linear_combination -h

/-- Odd coefficients of a dyadic telescoper solution vanish. -/
theorem telescoper_coeff_odd {μ γ : ℂ} {N : ℕ} {k : ℂ⟦X⟧}
    (heq : (C μ : ℂ⟦X⟧) * dyadicSubst k - k = PowerSeries.monomial (2 * N) γ)
    {n : ℕ} (hn : ¬ 2 ∣ n) : (coeff n) k = 0 := by
  rw [telescoper_coeff heq n, if_neg hn, if_neg (by omega : n ≠ 2 * N), mul_zero, sub_zero]

/-- Coefficients up to `N` of a dyadic telescoper solution vanish. -/
theorem telescoper_coeff_le {μ γ : ℂ} {N : ℕ} (hN : 0 < N) {k : ℂ⟦X⟧}
    (heq : (C μ : ℂ⟦X⟧) * dyadicSubst k - k = PowerSeries.monomial (2 * N) γ) :
    ∀ n, 0 < n → n ≤ N → (coeff n) k = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hnN
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
    · have h2 : 2 ∣ n := ⟨m, by omega⟩
      rw [telescoper_coeff heq n, if_pos h2, if_neg (by omega : n ≠ 2 * N),
        ih (n / 2) (by omega) (by omega) (by omega), mul_zero, sub_zero]
    · exact telescoper_coeff_odd heq (by rw [Nat.odd_iff] at hodd; omega)

/-- The dyadic tree of a telescoper solution carries the forced lacunary values. -/
theorem telescoper_coeff_tree {μ γ : ℂ} {N : ℕ} (hN : 0 < N) {k : ℂ⟦X⟧}
    (heq : (C μ : ℂ⟦X⟧) * dyadicSubst k - k = PowerSeries.monomial (2 * N) γ) :
    ∀ r : ℕ, (coeff (2 ^ (r + 1) * N)) k = -(μ ^ r * γ) := by
  intro r
  induction r with
  | zero =>
    rw [telescoper_coeff heq (2 ^ 1 * N), if_pos ⟨N, by ring⟩]
    have hdiv : 2 ^ 1 * N / 2 = N := by omega
    rw [hdiv, if_pos (by ring)]
    rcases Nat.eq_or_lt_of_le hN with h1 | h1
    · rw [show N = 1 by omega]
      rw [show (coeff 1) k = 0 from telescoper_coeff_odd heq (by omega)]
      ring
    · rw [telescoper_coeff_le hN heq N hN le_rfl]
      ring
  | succ r ihr =>
    rw [telescoper_coeff heq (2 ^ (r + 2) * N), if_pos ⟨2 ^ (r + 1) * N, by ring⟩]
    have hdiv : 2 ^ (r + 2) * N / 2 = 2 ^ (r + 1) * N := by
      have h2 : 2 ^ (r + 2) * N = 2 * (2 ^ (r + 1) * N) := by ring
      rw [h2]
      omega
    have hne : 2 ^ (r + 2) * N ≠ 2 * N := by
      have h4 : 4 ≤ 2 ^ (r + 2) := by
        calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (r + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have := Nat.mul_le_mul_right N h4
      omega
    rw [hdiv, if_neg hne, ihr]
    ring

/-- A descent from any nonzero coefficient above `2N` to the base window. -/
theorem telescoper_descent {μ γ : ℂ} {N : ℕ} {k : ℂ⟦X⟧}
    (heq : (C μ : ℂ⟦X⟧) * dyadicSubst k - k = PowerSeries.monomial (2 * N) γ) :
    ∀ n, (coeff n) k ≠ 0 → 2 * N < n →
      ∃ (j : ℕ) (m : ℕ), n = 2 ^ j * m ∧ 0 < m ∧ m ≤ 2 * N ∧ 1 ≤ j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h2N
    have heven : 2 ∣ n := by
      by_contra hodd
      exact hn (telescoper_coeff_odd heq hodd)
    have hhalf : (coeff (n / 2)) k ≠ 0 := by
      intro h0
      apply hn
      rw [telescoper_coeff heq n, if_pos heven, h0, mul_zero, if_neg (by omega), sub_zero]
    rcases Nat.lt_or_ge (2 * N) (n / 2) with hbig | hsmall
    · obtain ⟨j, m, hjm, hm0, hm2N, hj1⟩ := ih (n / 2) (by omega) hhalf hbig
      refine ⟨j + 1, m, ?_, hm0, hm2N, by omega⟩
      have h2 : n = 2 * (n / 2) := by omega
      rw [h2, hjm, pow_succ]
      ring
    · exact ⟨1, n / 2, by omega, by omega, hsmall, le_rfl⟩

/-- **No rational solution of the dyadic telescoper equation.**  For `μ, γ ≠ 0` and `N ≥ 1`
the unique power-series solution of `μ·k(t²) − k(t) = γ·t^{2N}` is forced to carry nonzero
coefficients along the doubling tree `2^{r+1}·N` with all-zero gaps between deep tree points,
so it cannot be rational. -/
theorem no_rational_dyadic_telescoper {μ γ : ℂ} (hμ : μ ≠ 0) (hγ : γ ≠ 0) {N : ℕ}
    (hN : 0 < N) {k : ℂ⟦X⟧}
    (heq : (C μ : ℂ⟦X⟧) * dyadicSubst k - k = PowerSeries.monomial (2 * N) γ) :
    ¬ ∃ p q : Polynomial ℂ, q.coeff 0 ≠ 0 ∧ (q : ℂ⟦X⟧) * k = (p : ℂ⟦X⟧) := by
  rintro ⟨p, q, hq0, hk⟩
  set R : ℕ := p.natDegree + q.natDegree + 2 * N + 2 with hR
  have hRbig : R < 2 ^ R := Nat.lt_two_pow_self
  set M : ℕ := 2 ^ (R + 1) * N with hM
  have hMp : p.natDegree < M := by
    have h1 : R ≤ 2 ^ R * N := le_trans hRbig.le (Nat.le_mul_of_pos_right _ hN)
    have h2 : 2 ^ R * N ≤ 2 ^ (R + 1) * N := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : R ≤ R + 1)
      exact Nat.mul_le_mul_right N this
    omega
  have hMq : q.natDegree ≤ M := by
    have h1 : R ≤ 2 ^ R * N := le_trans hRbig.le (Nat.le_mul_of_pos_right _ hN)
    have h2 : 2 ^ R * N ≤ 2 ^ (R + 1) * N := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : R ≤ R + 1)
      exact Nat.mul_le_mul_right N this
    omega
  have hwindow : ∀ m, M < m → m ≤ M + q.natDegree → (coeff m) k = 0 := by
    intro m hm1 hm2
    by_contra hc
    obtain ⟨j, w, hjw, hw0, hw2N, hj1⟩ := telescoper_descent heq m hc (by
      have h1 : 2 * N ≤ 2 ^ (R + 1) * N := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ R + 1)
        exact Nat.mul_le_mul_right N (by simpa using this)
      omega)
    -- the descent point forces divisibility by a huge power of two
    have hpow : 2 ^ R < 2 ^ j := by
      have hmw : 2 ^ (R + 1) * N < 2 ^ j * w := by omega
      have hup : 2 ^ j * w ≤ 2 ^ j * (2 * N) := Nat.mul_le_mul_left _ hw2N
      have h2N0 : 0 < 2 * N := by omega
      have := lt_of_lt_of_le hmw hup
      rw [pow_succ] at this
      have h2 : 2 ^ R * (2 * N) < 2 ^ j * (2 * N) := by
        calc 2 ^ R * (2 * N) = 2 ^ R * 2 * N := by ring
        _ < 2 ^ j * (2 * N) := this
      exact lt_of_mul_lt_mul_right h2 (by omega)
    have hjR : R + 1 ≤ j := by
      by_contra hlt
      have : 2 ^ j ≤ 2 ^ R := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    -- m is a multiple of 2^(R+1) strictly between consecutive multiples
    have hdvd : 2 ^ (R + 1) ∣ m := by
      rw [hjw]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 hjR) w
    obtain ⟨c, hc'⟩ := hdvd
    have hcN : N < c := by
      by_contra hle
      have : m ≤ 2 ^ (R + 1) * N := by
        rw [hc']
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    have hnext : 2 ^ (R + 1) * (N + 1) ≤ m := by
      rw [hc']
      exact Nat.mul_le_mul_left _ (by omega)
    have hgap : q.natDegree < 2 ^ (R + 1) := by
      have h1 : q.natDegree < 2 ^ R := by
        have : q.natDegree ≤ R := by omega
        omega
      have h2 : (2:ℕ) ^ R ≤ 2 ^ (R + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have : M + 2 ^ (R + 1) ≤ m := by
      rw [hM]
      calc 2 ^ (R + 1) * N + 2 ^ (R + 1) = 2 ^ (R + 1) * (N + 1) := by ring
      _ ≤ m := hnext
    omega
  have hkill := coeff_eventually_zero_of_gap hq0 hk hMp hMq hwindow
  -- yet the tree value beyond `M` is nonzero
  have htree := telescoper_coeff_tree hN heq (R + 1)
  have hbig : M < 2 ^ (R + 2) * N := by
    rw [hM]
    have h2 : (2:ℕ) ^ (R + 1) < 2 ^ (R + 2) :=
      Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega : R + 1 < R + 2)
    exact (Nat.mul_lt_mul_right hN).mpr h2
  have hzero := hkill (2 ^ (R + 2) * N) hbig
  rw [htree] at hzero
  exact (mul_ne_zero (pow_ne_zero _ hμ) hγ) (neg_eq_zero.mp hzero)

/-! ## Dyadic substitution is a ring homomorphism -/

theorem dyadicSubst_mul (a b : ℂ⟦X⟧) :
    dyadicSubst (a * b) = dyadicSubst a * dyadicSubst b := by
  classical
  ext n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have h2m : n = 2 * m := by omega
    subst h2m
    rw [coeff_dyadicSubst_even, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    -- reindex the convolution along doubling
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (coeff i) (dyadicSubst a) * (coeff k) (dyadicSubst b)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (coeff i) a * (coeff k) b)]
    -- restrict the big sum to even indices
    have hsplit : ∑ i ∈ Finset.range (2 * m + 1),
        (coeff i) (dyadicSubst a) * (coeff (2 * m - i)) (dyadicSubst b) =
        ∑ j ∈ Finset.range (m + 1),
        (coeff (2 * j)) (dyadicSubst a) * (coeff (2 * m - 2 * j)) (dyadicSubst b) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * m + 1)) (fun i => 2 ∣ i)]
      have hodd_zero : ∑ i ∈ (Finset.range (2 * m + 1)).filter (fun i => ¬ 2 ∣ i),
          (coeff i) (dyadicSubst a) * (coeff (2 * m - i)) (dyadicSubst b) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [coeff_dyadicSubst_odd _ hi.2, zero_mul]
      rw [hodd_zero, add_zero]
      apply Finset.sum_nbij' (fun i => i / 2) (fun j => 2 * j)
      · intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        rw [Finset.mem_range]
        omega
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, ⟨j, by ring⟩⟩
      · intro i hi
        rw [Finset.mem_filter] at hi
        obtain ⟨w, hw⟩ := hi.2
        omega
      · intro j _
        omega
      · intro i hi
        rw [Finset.mem_filter] at hi
        obtain ⟨w, hw⟩ := hi.2
        have h1 : 2 * (i / 2) = i := by omega
        rw [h1]
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [coeff_dyadicSubst_even, show 2 * m - 2 * j = 2 * (m - j) by omega,
      coeff_dyadicSubst_even]
  · have hn2 : ¬ 2 ∣ n := by
      rw [Nat.odd_iff] at hodd
      omega
    rw [coeff_dyadicSubst_odd _ hn2, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (coeff i) (dyadicSubst a) * (coeff k) (dyadicSubst b))]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rcases Nat.even_or_odd i with ⟨w, hw⟩ | hoddi
    · have : ¬ 2 ∣ (n - i) := by
        rw [Finset.mem_range] at hi
        rw [Nat.odd_iff] at hodd
        omega
      rw [coeff_dyadicSubst_odd _ this, mul_zero]
    · have : ¬ 2 ∣ i := by
        rw [Nat.odd_iff] at hoddi
        omega
      rw [coeff_dyadicSubst_odd _ this, zero_mul]

theorem dyadicSubst_one : dyadicSubst (1 : ℂ⟦X⟧) = 1 := by
  classical
  ext n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have h2m : n = 2 * m := by omega
    subst h2m
    rw [coeff_dyadicSubst_even, PowerSeries.coeff_one, PowerSeries.coeff_one]
    rcases eq_or_ne m 0 with rfl | hm0
    · norm_num
    · rw [if_neg hm0, if_neg (by omega)]
  · have hn2 : ¬ 2 ∣ n := by
      rw [Nat.odd_iff] at hodd
      omega
    rw [coeff_dyadicSubst_odd _ hn2, PowerSeries.coeff_one, if_neg (by omega)]

theorem dyadicSubst_add (a b : ℂ⟦X⟧) :
    dyadicSubst (a + b) = dyadicSubst a + dyadicSubst b := by
  classical
  ext n
  rw [map_add]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have h2m : n = 2 * m := by omega
    subst h2m
    rw [coeff_dyadicSubst_even, coeff_dyadicSubst_even, coeff_dyadicSubst_even, map_add]
  · have hn2 : ¬ 2 ∣ n := by
      rw [Nat.odd_iff] at hodd
      omega
    rw [coeff_dyadicSubst_odd _ hn2, coeff_dyadicSubst_odd _ hn2,
      coeff_dyadicSubst_odd _ hn2, add_zero]

/-- Dyadic substitution as a ring homomorphism. -/
def dyadicSubstHom : ℂ⟦X⟧ →+* ℂ⟦X⟧ where
  toFun := dyadicSubst
  map_one' := dyadicSubst_one
  map_mul' := dyadicSubst_mul
  map_zero' := by
    classical
    ext n
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
    · have h2m : n = 2 * m := by omega
      subst h2m
      rw [coeff_dyadicSubst_even]
      simp
    · rw [coeff_dyadicSubst_odd _ (by rw [Nat.odd_iff] at hodd; omega)]
      simp
  map_add' := dyadicSubst_add

/-- Dyadic substitution restricts to the polynomial `expand` on polynomial series. -/
theorem dyadicSubst_coe (p : Polynomial ℂ) :
    dyadicSubst (p : ℂ⟦X⟧) = ((Polynomial.expand ℂ 2 p : Polynomial ℂ) : ℂ⟦X⟧) := by
  classical
  ext n
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | hodd
  · have h2m : n = 2 * m := by omega
    subst h2m
    rw [coeff_dyadicSubst_even, Polynomial.coeff_coe, Polynomial.coeff_coe,
      Polynomial.coeff_expand (by omega : 0 < 2), if_pos ⟨m, by omega⟩]
    congr 1
    omega
  · have hn2 : ¬ 2 ∣ n := by
      rw [Nat.odd_iff] at hodd
      omega
    rw [coeff_dyadicSubst_odd _ hn2, Polynomial.coeff_coe,
      Polynomial.coeff_expand (by omega : 0 < 2), if_neg hn2]

/-! ## No rational dyadic telescoper, field level -/

theorem coprime_eval_zero_ne {p q : Polynomial ℂ} (hco : IsCoprime p q)
    (hq : q.eval 0 = 0) : p.eval 0 ≠ 0 := by
  intro hp
  obtain ⟨u, v, huv⟩ := hco
  have h := congrArg (Polynomial.eval 0) huv
  simp [hp, hq] at h

/-- **No rational solution of the dyadic telescoper equation, field level.**  For
`μ, γ ≠ 0` and `N ≥ 1` no rational function satisfies `μ·k(t²) − k(t) = γ·t^{2N}`:
a pole at the origin is excluded by trailing degrees, and a regular solution expands to
a power series killed by the lacunary tree. -/
theorem no_ratFunc_dyadic_telescoper {μ γ : ℂ} (hμ : μ ≠ 0) (hγ : γ ≠ 0) {N : ℕ}
    (hN : 0 < N) (k : RatFunc ℂ) :
    RatFunc.C μ * MahlerPolynomial.mahlerHom 0 k - k ≠ RatFunc.C γ * RatFunc.X ^ (2 * N) := by
  intro heq
  classical
  set p : Polynomial ℂ := k.num with hp
  set q : Polynomial ℂ := k.denom with hq
  have hq0 : q ≠ 0 := k.denom_ne_zero
  have hco : IsCoprime p q := k.isCoprime_num_denom
  set p₂ : Polynomial ℂ := Polynomial.expand ℂ 2 p with hp₂
  set q₂ : Polynomial ℂ := Polynomial.expand ℂ 2 q with hq₂
  have hq₂0 : q₂ ≠ 0 := by
    intro h
    apply hq0
    apply Polynomial.expand_injective (n := 2) (by omega)
    rw [← hq₂, h, map_zero]
  -- the polynomial cross identity
  have hcomp : ∀ r : Polynomial ℂ, r.comp (Polynomial.X ^ 2 + Polynomial.C 0) =
      Polynomial.expand ℂ 2 r := by
    intro r
    rw [map_zero, add_zero, ← Polynomial.expand_eq_comp_X_pow]
  have hmah : MahlerPolynomial.mahlerHom 0 k =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p₂ / algebraMap (Polynomial ℂ) (RatFunc ℂ) q₂ := by
    conv_lhs => rw [← k.num_div_denom]
    rw [map_div₀, MahlerPolynomial.mahlerHom_algebraMap, MahlerPolynomial.mahlerHom_algebraMap, hcomp, hcomp]
  have hqne : algebraMap (Polynomial ℂ) (RatFunc ℂ) q ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq0
  have hq₂ne : algebraMap (Polynomial ℂ) (RatFunc ℂ) q₂ ≠ 0 :=
    RatFunc.algebraMap_ne_zero hq₂0
  have hE : Polynomial.C μ * p₂ * q - p * q₂ =
      Polynomial.C γ * Polynomial.X ^ (2 * N) * q * q₂ := by
    apply IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)
    have hX : (RatFunc.X : RatFunc ℂ) = algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X :=
      (RatFunc.algebraMap_X).symm
    have hCμ : (RatFunc.C μ : RatFunc ℂ) =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C μ) :=
      (RatFunc.algebraMap_C μ).symm
    have hCγ : (RatFunc.C γ : RatFunc ℂ) =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C γ) :=
      (RatFunc.algebraMap_C γ).symm
    have hknum : (k : RatFunc ℂ) =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) p / algebraMap (Polynomial ℂ) (RatFunc ℂ) q :=
      k.num_div_denom.symm
    rw [hmah, hknum, hX, hCμ, hCγ] at heq
    push_cast [map_mul, map_sub, map_pow]
    field_simp at heq
    linear_combination heq
  rcases eq_or_ne (q.eval 0) 0 with hq00 | hq00
  · -- a pole at the origin is impossible: trailing degrees mismatch
    have hp00 : p.eval 0 ≠ 0 := coprime_eval_zero_ne hco hq00
    have hp0 : p ≠ 0 := fun h => hp00 (by rw [h, Polynomial.eval_zero])
    have hp₂0 : p₂ ≠ 0 := by
      intro h
      apply hp0
      apply Polynomial.expand_injective (n := 2) (by omega)
      rw [← hp₂, h, map_zero]
    set m : ℕ := q.natTrailingDegree with hm
    have hq000 : q.coeff 0 = 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
    have hmpos : 0 < m := by
      by_contra h0
      have hm0 : q.natTrailingDegree = 0 := by omega
      have htc : q.trailingCoeff ≠ 0 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq0
      apply htc
      rw [Polynomial.trailingCoeff, hm0, hq000]
    have hp₂00 : p₂.coeff 0 ≠ 0 := by
      rw [hp₂, Polynomial.coeff_expand (by omega : 0 < 2), if_pos ⟨0, by ring⟩]
      have h02 : (0 : ℕ) / 2 = 0 := by omega
      rw [h02, Polynomial.coeff_zero_eq_eval_zero]
      exact hp00
    have hCμ0 : Polynomial.C μ ≠ 0 := by simpa using hμ
    have hA0 : Polynomial.C μ * p₂ * q ≠ 0 := mul_ne_zero (mul_ne_zero hCμ0 hp₂0) hq0
    have hntdp₂ : p₂.natTrailingDegree = 0 := by
      by_contra hne
      exact hp₂00 (Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega))
    have hntdA : (Polynomial.C μ * p₂ * q).natTrailingDegree = m := by
      rw [Polynomial.natTrailingDegree_mul (mul_ne_zero hCμ0 hp₂0) hq0,
        Polynomial.natTrailingDegree_mul hCμ0 hp₂0, Polynomial.natTrailingDegree_C, hntdp₂]
      omega
    have hntdq₂ : q₂.natTrailingDegree = 2 * m := by
      apply le_antisymm
      · apply Polynomial.natTrailingDegree_le_of_ne_zero
        rw [hq₂, Polynomial.coeff_expand (by omega : 0 < 2), if_pos ⟨m, by ring⟩]
        have hdm : 2 * m / 2 = m := by omega
        rw [hdm]
        exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq0
      · by_contra hlt
        have hq₂0' : q₂ ≠ 0 := hq₂0
        have htc : q₂.coeff q₂.natTrailingDegree ≠ 0 :=
          Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq₂0'
        rw [hq₂, Polynomial.coeff_expand (by omega : 0 < 2)] at htc
        by_cases hdvd : 2 ∣ (Polynomial.expand ℂ 2 q).natTrailingDegree
        · rw [if_pos hdvd] at htc
          have hle := Polynomial.natTrailingDegree_le_of_ne_zero htc
          rw [hq₂] at hlt
          omega
        · rw [if_neg hdvd] at htc
          exact htc rfl
    have hB : (p * q₂).coeff m = 0 := by
      apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      rw [Polynomial.natTrailingDegree_mul hp0 hq₂0, hntdq₂]
      omega
    have hRHS : (Polynomial.C γ * Polynomial.X ^ (2 * N) * q * q₂).coeff m = 0 := by
      apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      have hCγ0 : Polynomial.C γ ≠ 0 := by simpa using hγ
      have hX0 : (Polynomial.X : Polynomial ℂ) ^ (2 * N) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
      rw [Polynomial.natTrailingDegree_mul (mul_ne_zero (mul_ne_zero hCγ0 hX0) hq0) hq₂0,
        Polynomial.natTrailingDegree_mul (mul_ne_zero hCγ0 hX0) hq0,
        Polynomial.natTrailingDegree_mul hCγ0 hX0, Polynomial.natTrailingDegree_C,
        Polynomial.natTrailingDegree_X_pow, hntdq₂]
      omega
    have hAcoeff : (Polynomial.C μ * p₂ * q).coeff m ≠ 0 := by
      have := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hA0
      rwa [Polynomial.trailingCoeff, hntdA] at this
    have hcoeffE := congrArg (fun r : Polynomial ℂ => r.coeff m) hE
    simp only [Polynomial.coeff_sub] at hcoeffE
    rw [hB, hRHS, sub_zero] at hcoeffE
    exact hAcoeff hcoeffE
  · -- regular at the origin: pass to power series and use the lacunary obstruction
    have hq0' : q.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]
    have hq₂0' : q₂.coeff 0 ≠ 0 := by
      rw [hq₂, Polynomial.coeff_expand (by omega : 0 < 2), if_pos ⟨0, by ring⟩]
      have h02 : (0 : ℕ) / 2 = 0 := by omega
      rwa [h02]
    have hqPSu : IsUnit ((q : Polynomial ℂ) : ℂ⟦X⟧) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have hc : PowerSeries.constantCoeff ((q : Polynomial ℂ) : ℂ⟦X⟧) = q.coeff 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
      rw [hc]
      exact isUnit_iff_ne_zero.mpr hq0'
    obtain ⟨u, hu⟩ := hqPSu
    set kPS : ℂ⟦X⟧ := ((u⁻¹ : ℂ⟦X⟧ˣ) : ℂ⟦X⟧) * (p : ℂ⟦X⟧) with hkPS
    have hqk : ((q : Polynomial ℂ) : ℂ⟦X⟧) * kPS = (p : ℂ⟦X⟧) := by
      rw [hkPS, ← hu, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    have hdyq : dyadicSubst ((q : Polynomial ℂ) : ℂ⟦X⟧) = ((q₂ : Polynomial ℂ) : ℂ⟦X⟧) := by
      rw [dyadicSubst_coe, hq₂]
    have hdyp : dyadicSubst ((p : Polynomial ℂ) : ℂ⟦X⟧) = ((p₂ : Polynomial ℂ) : ℂ⟦X⟧) := by
      rw [dyadicSubst_coe, hp₂]
    have hdyk : ((q₂ : Polynomial ℂ) : ℂ⟦X⟧) * dyadicSubst kPS = ((p₂ : Polynomial ℂ) : ℂ⟦X⟧) := by
      rw [← hdyq, ← hdyp, ← dyadicSubst_mul, hqk]
    have hq₂PS0 : ((q₂ : Polynomial ℂ) : ℂ⟦X⟧) ≠ 0 := by
      intro h
      apply hq₂0'
      have := congrArg (coeff 0) h
      rw [Polynomial.coeff_coe] at this
      simpa using this
    have hqPS0 : ((q : Polynomial ℂ) : ℂ⟦X⟧) ≠ 0 := by
      intro h
      apply hq0'
      have := congrArg (coeff 0) h
      rw [Polynomial.coeff_coe] at this
      simpa using this
    -- the power-series telescoper equation
    have hPS : (C μ : ℂ⟦X⟧) * dyadicSubst kPS - kPS = PowerSeries.monomial (2 * N) γ := by
      apply mul_left_cancel₀ (mul_ne_zero hqPS0 hq₂PS0)
      have hEPS : ((Polynomial.C μ * p₂ * q - p * q₂ : Polynomial ℂ) : ℂ⟦X⟧) =
          ((Polynomial.C γ * Polynomial.X ^ (2 * N) * q * q₂ : Polynomial ℂ) : ℂ⟦X⟧) := by
        rw [hE]
      have hCμ : ((Polynomial.C μ : Polynomial ℂ) : ℂ⟦X⟧) = (C μ : ℂ⟦X⟧) :=
        Polynomial.coe_C μ
      have hCγ : ((Polynomial.C γ : Polynomial ℂ) : ℂ⟦X⟧) = (C γ : ℂ⟦X⟧) :=
        Polynomial.coe_C γ
      have hXc : ((Polynomial.X : Polynomial ℂ) : ℂ⟦X⟧) = (X : ℂ⟦X⟧) := Polynomial.coe_X
      have hmono : (PowerSeries.monomial (2 * N)) γ = (C γ : ℂ⟦X⟧) * X ^ (2 * N) := by
        ext j
        rw [PowerSeries.coeff_monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
        rcases eq_or_ne j (2 * N) with rfl | hj
        · rw [if_pos rfl, if_pos rfl, mul_one]
        · rw [if_neg hj, if_neg hj, mul_zero]
      calc ((q : Polynomial ℂ) : ℂ⟦X⟧) * ((q₂ : Polynomial ℂ) : ℂ⟦X⟧) *
            ((C μ : ℂ⟦X⟧) * dyadicSubst kPS - kPS)
          = (C μ : ℂ⟦X⟧) * (((q : Polynomial ℂ) : ℂ⟦X⟧) *
              (((q₂ : Polynomial ℂ) : ℂ⟦X⟧) * dyadicSubst kPS)) -
            ((q₂ : Polynomial ℂ) : ℂ⟦X⟧) * (((q : Polynomial ℂ) : ℂ⟦X⟧) * kPS) := by ring
        _ = (C μ : ℂ⟦X⟧) * (((q : Polynomial ℂ) : ℂ⟦X⟧) * ((p₂ : Polynomial ℂ) : ℂ⟦X⟧)) -
            ((q₂ : Polynomial ℂ) : ℂ⟦X⟧) * ((p : Polynomial ℂ) : ℂ⟦X⟧) := by
            rw [hdyk, hqk]
        _ = ((Polynomial.C μ * p₂ * q - p * q₂ : Polynomial ℂ) : ℂ⟦X⟧) := by
            push_cast
            ring
        _ = ((Polynomial.C γ * Polynomial.X ^ (2 * N) * q * q₂ : Polynomial ℂ) : ℂ⟦X⟧) := hEPS
        _ = ((q : Polynomial ℂ) : ℂ⟦X⟧) * ((q₂ : Polynomial ℂ) : ℂ⟦X⟧) *
            ((PowerSeries.monomial (2 * N)) γ) := by
            rw [hmono]
            push_cast
            ring
    exact no_rational_dyadic_telescoper hμ hγ hN hPS ⟨p, q, hq0', hqk⟩

end

end GaloisForLFunctions
