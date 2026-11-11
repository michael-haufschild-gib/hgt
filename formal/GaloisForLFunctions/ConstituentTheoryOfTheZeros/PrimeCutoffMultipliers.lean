import GaloisForLFunctions.RHTower.ZetaTwistedDirichletHeadsNearAZeroHaveVanishingHaarMass
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Simultaneous contraction of omitted prime coordinates

Fixing finitely many prime coordinates controls any continuous function on the
prime torus near its identity. Replacing every remaining coordinate by the same
disc parameter gives polynomial coefficient multipliers. At zero these retain
exactly the smooth indices; on the circle they are unitary twists.
-/

open Complex Filter Topology Set Metric
open _root_.RHTower

noncomputable section
namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

/-- Continuity at the torus identity is controlled by finitely many primes. -/
theorem exists_prime_cutoff_of_continuousAt
    {f : (Nat.Primes → Circle) → ℂ} (hf : ContinuousAt f 1)
    {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N ≥ N₀, ∀ ω : Nat.Primes → Circle,
      (∀ p : Nat.Primes, (p : ℕ) < N → ω p = 1) → ‖f ω - f 1‖ < ε := by
  by_contra h
  push Not at h
  have hbad (k : ℕ) := h (N₀ + k) (Nat.le_add_right N₀ k)
  choose ω hfix hfar using hbad
  have hlim : Tendsto ω atTop (𝓝 (1 : Nat.Primes → Circle)) := by
    apply tendsto_pi_nhds.mpr
    intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (p : ℕ)] with k hk
    exact (hfix k p (lt_of_lt_of_le hk (Nat.le_add_left k N₀))).symm
  have hnear : ∀ᶠ k in atTop, ‖f (ω k) - f 1‖ < ε := by
    have hh := (hf.tendsto.comp hlim).eventually (Metric.ball_mem_nhds (f 1) hε)
    simpa only [mem_ball, dist_eq_norm, Function.comp_apply] using hh
  obtain ⟨k, hk⟩ := hnear.exists
  exact (not_lt_of_ge (hfar k)) hk

/-- All primes at or above the cutoff share one phase. -/
def retainedPrimePhase (N : ℕ) (w : Circle) : Nat.Primes → Circle :=
  fun p => if (p : ℕ) < N then 1 else w

theorem continuous_retainedPrimePhase (N : ℕ) : Continuous (retainedPrimePhase N) := by
  apply continuous_pi
  intro p
  by_cases hp : (p : ℕ) < N
  · simp only [retainedPrimePhase, if_pos hp]
    fun_prop
  · simp only [retainedPrimePhase, if_neg hp]
    fun_prop

@[simp] theorem retainedPrimePhase_one (N : ℕ) : retainedPrimePhase N 1 = 1 := by
  funext p
  simp only [retainedPrimePhase, Pi.one_apply, ite_self]

/-- Polynomial damping of every prime factor outside the cutoff. -/
def primeCutoffMultiplier (N : ℕ) (w : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    ∏ p ∈ n.primeFactors, (if p < N then 1 else w) ^ n.factorization p

@[simp] theorem primeCutoffMultiplier_index_zero (N : ℕ) (w : ℂ) :
    primeCutoffMultiplier N w 0 = 0 := by
  simp only [primeCutoffMultiplier, ite_true]

theorem differentiable_primeCutoffMultiplier (N n : ℕ) :
    Differentiable ℂ (fun w => primeCutoffMultiplier N w n) := by
  by_cases hn : n = 0
  · simp only [hn, primeCutoffMultiplier_index_zero]
    exact differentiable_const _
  · simp only [primeCutoffMultiplier, if_neg hn]
    apply Differentiable.fun_finsetProd
    intro p hp
    by_cases hpN : p < N
    · simp only [if_pos hpN]
      exact differentiable_const _
    · simp only [if_neg hpN]
      exact differentiable_pow _

theorem norm_primeCutoffMultiplier_le_one (N n : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖primeCutoffMultiplier N w n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp only [hn, primeCutoffMultiplier_index_zero, norm_zero, zero_le_one]
  · rw [primeCutoffMultiplier, if_neg hn, norm_prod]
    apply Finset.prod_le_one
    · intro p hp
      exact norm_nonneg _
    · intro p hp
      rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      split_ifs
      · simp only [norm_one, le_refl]
      · exact hw

theorem primeCutoffMultiplier_of_smooth {N n : ℕ} (hn : n ∈ Nat.smoothNumbers N)
    (w : ℂ) : primeCutoffMultiplier N w n = 1 := by
  rw [primeCutoffMultiplier, if_neg (Nat.ne_zero_of_mem_smoothNumbers hn)]
  apply Finset.prod_eq_one
  intro p hp
  have hpN := (Nat.mem_primesBelow.mp (Nat.primeFactors_subset_of_mem_smoothNumbers hn hp)).1
  simp only [if_pos hpN, one_pow]

/-- The central parameter deletes precisely the nonsmooth indices. -/
theorem primeCutoffMultiplier_zero (N n : ℕ) :
    primeCutoffMultiplier N 0 n = if n ∈ Nat.smoothNumbers N then 1 else 0 := by
  by_cases hn : n ∈ Nat.smoothNumbers N
  · rw [if_pos hn, primeCutoffMultiplier_of_smooth hn]
  · rw [if_neg hn]
    by_cases hn0 : n = 0
    · exact hn0 ▸ primeCutoffMultiplier_index_zero N 0
    · rw [primeCutoffMultiplier, if_neg hn0]
      have hex : ∃ p ∈ n.primeFactors, ¬p < N := by
        by_contra h
        push Not at h
        apply hn
        apply Nat.mem_smoothNumbers_of_primeFactors_subset hn0
        intro p hp
        exact Finset.mem_range.mpr (h p hp)
      obtain ⟨p, hp, hpN⟩ := hex
      have hv : n.factorization p ≠ 0 := by
        apply Finsupp.mem_support_iff.mp
        rwa [Nat.support_factorization]
      exact Finset.prod_eq_zero hp (by rw [if_neg hpN, zero_pow hv])

/-- On the circle, polynomial damping is the corresponding prime twist. -/
theorem primeCutoffMultiplier_circle (N : ℕ) (w : Circle) {n : ℕ} (hn : n ≠ 0) :
    primeCutoffMultiplier N (w : ℂ) n = primePhaseTwist (retainedPrimePhase N w) n := by
  rw [primeCutoffMultiplier, if_neg hn, primePhaseTwist]
  apply Finset.prod_congr rfl
  intro p hp
  rw [dif_pos (Nat.prime_of_mem_primeFactors hp)]
  simp only [retainedPrimePhase]
  split_ifs <;> rfl

/-- Damping does not increase the absolute Dirichlet terms. -/
theorem term_primeCutoffMultiplier (a : ℕ → ℂ) (N : ℕ) (w s : ℂ) (n : ℕ) :
    LSeries.term (fun m => a m * primeCutoffMultiplier N w m) s n =
      primeCutoffMultiplier N w n * LSeries.term a s n := by
  by_cases hn : n = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    ring

theorem lSeriesSummable_primeCutoffMultiplier {a : ℕ → ℂ} {s w : ℂ} (N : ℕ)
    (hs : LSeriesSummable a s) (hw : ‖w‖ ≤ 1) :
    LSeriesSummable (fun m => a m * primeCutoffMultiplier N w m) s := by
  apply hs.norm.of_norm_bounded
  intro n
  rw [term_primeCutoffMultiplier, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_primeCutoffMultiplier_le_one N n hw)

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
