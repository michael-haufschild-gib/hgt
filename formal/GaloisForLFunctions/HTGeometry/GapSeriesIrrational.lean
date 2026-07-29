import Mathlib

/-!
# Support-gap irrationality for formal power series

A rational power series `A = p/q` satisfies the eventual linear recurrence read off from
`q·A = p`: beyond the degree of `p`, every coefficient of `q·A` vanishes.  A series whose
support contains arbitrarily late points each preceded by a zero window longer than the
recurrence is therefore not rational: the recurrence at such a point collapses to
`(trailing coefficient of q)·(the nonzero coefficient)` (`powerSeries_not_rational_of_gaps`).

Instance: the first Böttcher parameter-velocity series `∑_{j≥0} 2^{−(j+1)} t^{2^{j+1}}`, whose
`k`-th coefficient is `1/k` at the powers `k = 2^{j+1}` and `0` elsewhere.  Its support gaps
double, so it is irrational (`bottcherVelocitySeries_not_rational`) — the elementary half of
the hypertranscendence mechanism for the Böttcher parameter jets: combined with the order-one
Mahler dichotomy, irrationality upgrades to differential transcendence.
-/

open PowerSeries

namespace GaloisForLFunctions

/-- **Support-gap irrationality criterion.**  If for every window length `g` and threshold `M`
the series has a nonzero coefficient at some `N ≥ M` preceded by a zero window of length `g`,
then no polynomial relation `q·A = p` holds. -/
theorem powerSeries_not_rational_of_gaps {A : ℂ⟦X⟧}
    (h : ∀ g M : ℕ, ∃ N, M ≤ N ∧ coeff N A ≠ 0 ∧
      ∀ k, N - g ≤ k → k < N → coeff k A = 0)
    (p q : Polynomial ℂ) (hq : q ≠ 0) :
    (q : ℂ⟦X⟧) * A ≠ (p : ℂ⟦X⟧) := by
  intro heq
  obtain ⟨N, hNM, hN0, hgap⟩ := h q.natDegree (p.natDegree + q.natDegree + 1)
  have hrhs : p.coeff (N + q.natTrailingDegree) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  have hsum : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (N + q.natTrailingDegree),
      PowerSeries.coeff ij.1 (q : ℂ⟦X⟧) * PowerSeries.coeff ij.2 A = 0 := by
    rw [← PowerSeries.coeff_mul, heq, Polynomial.coeff_coe]
    exact hrhs
  have hred : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (N + q.natTrailingDegree),
      PowerSeries.coeff ij.1 (q : ℂ⟦X⟧) * PowerSeries.coeff ij.2 A
      = q.coeff q.natTrailingDegree * PowerSeries.coeff N A := by
    have hmem : ((q.natTrailingDegree, N) : ℕ × ℕ)
        ∈ Finset.HasAntidiagonal.antidiagonal (N + q.natTrailingDegree) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
    rw [Finset.sum_eq_single_of_mem _ hmem ?_, Polynomial.coeff_coe]
    rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [Polynomial.coeff_coe]
    rcases lt_or_ge i q.natTrailingDegree with hi | hi
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]
    rcases le_or_gt i q.natDegree with hiD | hiD
    · have hij_ne : i ≠ q.natTrailingDegree := by
        intro hi_eq
        apply hne
        have hj : j = N := by omega
        rw [hi_eq, hj]
      have hjlt : j < N := by
        have : q.natTrailingDegree < i := lt_of_le_of_ne hi (Ne.symm hij_ne)
        omega
      have hjge : N - q.natDegree ≤ j := by omega
      rw [hgap j hjge hjlt, mul_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hiD, zero_mul]
  rw [hred] at hsum
  have hqd : q.coeff q.natTrailingDegree ≠ 0 := fun h0 =>
    hq (Polynomial.trailingCoeff_eq_zero.mp h0)
  rcases mul_eq_zero.mp hsum with h0 | h0
  · exact hqd h0
  · exact hN0 h0

open Classical in
/-- The first Böttcher parameter-velocity series: coefficient `1/k` at each `k = 2^{j+1}`,
zero elsewhere. -/
noncomputable def bottcherVelocitySeries : ℂ⟦X⟧ :=
  PowerSeries.mk fun k =>
    if _h : ∃ m : ℕ, k = 2 ^ (m + 1) then (k : ℂ)⁻¹ else 0

theorem coeff_bottcherVelocitySeries_pow (m : ℕ) :
    coeff (2 ^ (m + 1)) bottcherVelocitySeries = ((2 ^ (m + 1) : ℕ) : ℂ)⁻¹ := by
  rw [bottcherVelocitySeries, coeff_mk, dif_pos ⟨m, rfl⟩]

theorem coeff_bottcherVelocitySeries_of_ne (k : ℕ) (hk : ∀ m : ℕ, k ≠ 2 ^ (m + 1)) :
    coeff k bottcherVelocitySeries = 0 := by
  rw [bottcherVelocitySeries, coeff_mk, dif_neg]
  rintro ⟨m, rfl⟩
  exact hk m rfl

/-- **The Böttcher velocity series is irrational**: its dyadic support gaps double, so the
support-gap criterion applies. -/
theorem bottcherVelocitySeries_not_rational (p q : Polynomial ℂ) (hq : q ≠ 0) :
    (q : ℂ⟦X⟧) * bottcherVelocitySeries ≠ (p : ℂ⟦X⟧) := by
  refine powerSeries_not_rational_of_gaps (fun g M => ?_) p q hq
  refine ⟨2 ^ (max g M + 1), ?_, ?_, ?_⟩
  · have h1 : M ≤ max g M := le_max_right _ _
    have h2 : max g M < 2 ^ max g M := Nat.lt_two_pow_self
    have h3 : 2 ^ max g M ≤ 2 ^ (max g M + 1) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)
    omega
  · rw [coeff_bottcherVelocitySeries_pow]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (by positivity))
  · intro k hk1 hk2
    apply coeff_bottcherVelocitySeries_of_ne
    intro m hm
    subst hm
    have hlt : m + 1 < max g M + 1 :=
      (Nat.pow_lt_pow_iff_right (by norm_num)).mp hk2
    have h2 : 2 ^ (m + 1) ≤ 2 ^ max g M :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hg : g < 2 ^ max g M :=
      lt_of_le_of_lt (le_max_left g M) Nat.lt_two_pow_self
    have hpow : 2 ^ (max g M + 1) = 2 * 2 ^ max g M := by ring
    omega

end GaloisForLFunctions
