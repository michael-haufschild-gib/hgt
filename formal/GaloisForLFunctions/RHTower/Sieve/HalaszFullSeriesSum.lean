import GaloisForLFunctions.RHTower.Sieve.DistanceAbscissaBridge
import GaloisForLFunctions.RHTower.Sieve.HalaszUniqueClose

/-!
# The Halász sum bound for the whole Dirichlet series

The corpus's dichotomy bounds the squarefree smooth proxy `∏_{p ≤ z}(1 + f(p)p^{-it})`.  With the
Euler bound for the whole series the same argument applies to `∑_n f(n) n^{-s}` itself: a frequency at
distance more than `δ` gives a damped series, at most one frequency of a separated set is close, and
the close one is controlled by the trivial bound.  Hence for a separated frequency set `S`

`∑_{t ∈ S} ‖∑_n f(n)n^{-σ-it}‖ ≤ (1 + 1/(σ−1)) · e^{7/2 + shift} · (|S| e^{-δ²} + 1)`,

with `shift = 2(σ−1)(log z + log 4)`, which is `O(1)` at `σ = 1 + 1/log z`.

This is the discrete large-values input of Halász's method, stated for the object Perron inversion
consumes rather than for the proxy.
-/

namespace RHTower.Sieve

open Complex Finset

section

variable {f : ℕ → ℂ} {s : ℂ}

/-- **The trivial size of a bounded multiplicative Dirichlet series.**  Distance is nonnegative, so
the damping bound at distance zero already gives an absolute estimate. -/
theorem norm_tsum_twistedSummand_le_trivial
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    ‖∑' n : ℕ, twistedSummand f s n‖ ≤ (1 + 1 / (s.re - 1)) * Real.exp (7 / 2) := by
  have hpos : 0 < 1 + 1 / (s.re - 1) := by
    have h1 : 0 < s.re - 1 := by linarith
    positivity
  refine le_trans (norm_tsum_twistedSummand_le_mul_exp_neg_dist hf1 hmul hbdd hs)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos.le)
  linarith [mulDistSqTsum_nonneg hbdd hs]

/-- **A far frequency gives a damped series.** -/
theorem norm_tsum_twistedSummand_le_of_far
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hs : 1 < s.re) {z : ℕ} (hz : 1 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hfar : δ ≤ Real.sqrt (mulDistSqPair f (charFn s.im) (Nat.primesLE z))) :
    ‖∑' n : ℕ, twistedSummand f s n‖ ≤
      (1 + 1 / (s.re - 1)) *
        Real.exp (7 / 2 + 2 * (s.re - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) := by
  have hpos : 0 < 1 + 1 / (s.re - 1) := by
    have h1 : 0 < s.re - 1 := by linarith
    positivity
  have hnn : 0 ≤ mulDistSqPair f (charFn s.im) (Nat.primesLE z) :=
    mulDistSqPair_nonneg_disc (fun p _ => hbdd p)
      (fun p _ => (norm_charFn s.im p).le)
      (fun p hp => (Nat.prime_of_mem_primesLE hp).pos)
  have hsq : δ ^ (2 : ℕ) ≤ mulDistSqPair f (charFn s.im) (Nat.primesLE z) := by
    have hmono := pow_le_pow_left₀ hδ hfar 2
    rwa [Real.sq_sqrt hnn] at hmono
  refine le_trans (norm_tsum_twistedSummand_le_of_mulDistSqPair hf1 hmul hbdd hs hz)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos.le)
  linarith

end

/-! ## The separated-set sum -/

section

variable {f : ℕ → ℂ}

theorem re_ofReal_add_mul_I (σ t : ℝ) : (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re = σ := by
  simp

theorem im_ofReal_add_mul_I (σ t : ℝ) : (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).im = t := by
  simp

/-- **The Halász sum bound for the whole series.**  Over a frequency set on which at most one point is
close, every other point contributes a damped series and the close point contributes the trivial
size. -/
theorem sum_norm_tsum_twistedSummand_le_of_card
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z)
    {δ : ℝ} (hδ : 0 ≤ δ) (S : Finset ℝ)
    (hclose : (S.filter (fun t =>
      Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ)).card ≤ 1) :
    ∑ t ∈ S, ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖ ≤
      (1 + 1 / (σ - 1)) *
        (Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4)) *
          ((S.card : ℝ) * Real.exp (-(δ ^ (2 : ℕ))) + 1)) := by
  classical
  have hpos : 0 < 1 + 1 / (σ - 1) := by
    have h1 : 0 < σ - 1 := by linarith
    positivity
  have hshift0 : 0 ≤ 2 * (σ - 1) * (Real.log z + Real.log 4) := by
    have h1 : (0 : ℝ) ≤ σ - 1 := by linarith
    have h2 : (0 : ℝ) ≤ Real.log z := Real.log_natCast_nonneg z
    have h3 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  set E : ℝ := Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set F : ℝ → ℝ := fun t =>
    ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖ with hF
  have hsre : ∀ t : ℝ, (1 : ℝ) < (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re := by
    intro t
    rw [re_ofReal_add_mul_I]
    exact hσ
  -- the close points are bounded by the trivial size
  have htriv : ∀ t : ℝ, F t ≤ (1 + 1 / (σ - 1)) * E := by
    intro t
    have h := norm_tsum_twistedSummand_le_trivial hf1 hmul hbdd (hsre t)
    rw [re_ofReal_add_mul_I] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ hpos.le)
    rw [hE]
    exact Real.exp_le_exp.mpr (by linarith)
  -- the far points are damped
  have hfarbound : ∀ t : ℝ,
      ¬ (Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ) →
      F t ≤ (1 + 1 / (σ - 1)) * (E * Real.exp (-(δ ^ (2 : ℕ)))) := by
    intro t ht
    have hfar : δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) :=
      le_of_lt (not_le.mp ht)
    have h := norm_tsum_twistedSummand_le_of_far hf1 hmul hbdd (hsre t) hz hδ
      (by rw [im_ofReal_add_mul_I]; exact hfar)
    rw [re_ofReal_add_mul_I] at h
    refine le_trans h (mul_le_mul_of_nonneg_left (le_of_eq ?_) hpos.le)
    have harg : 7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)
        = (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4)) + -(δ ^ (2 : ℕ)) := by ring
    rw [hE, harg, Real.exp_add]
  -- split and add
  have hsplit : ∑ t ∈ S, F t =
      (∑ t ∈ S.filter (fun t =>
          Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ), F t) +
        ∑ t ∈ S.filter (fun t =>
          ¬ (Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ)), F t :=
    (Finset.sum_filter_add_sum_filter_not S _ F).symm
  have hclosesum : (∑ t ∈ S.filter (fun t =>
      Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ), F t)
      ≤ (1 + 1 / (σ - 1)) * E := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ ((1 + 1 / (σ - 1)) * E)
      (fun t _ => htriv t)) ?_
    rw [nsmul_eq_mul]
    have hcard : ((S.filter (fun t =>
        Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ)).card : ℝ) ≤ 1 := by
      exact_mod_cast hclose
    have hnn : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * E := by positivity
    nlinarith
  have hfarsum : (∑ t ∈ S.filter (fun t =>
      ¬ (Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ)), F t)
      ≤ (S.card : ℝ) * ((1 + 1 / (σ - 1)) * (E * Real.exp (-(δ ^ (2 : ℕ))))) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _
      ((1 + 1 / (σ - 1)) * (E * Real.exp (-(δ ^ (2 : ℕ))))) (fun t ht => ?_)) ?_
    · exact hfarbound t (Finset.mem_filter.mp ht).2
    · rw [nsmul_eq_mul]
      have hcard : ((S.filter (fun t =>
          ¬ (Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)) ≤ δ))).card : ℝ)
          ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hnn : (0 : ℝ) ≤ (1 + 1 / (σ - 1)) * (E * Real.exp (-(δ ^ (2 : ℕ)))) := by positivity
      exact mul_le_mul_of_nonneg_right hcard hnn
  rw [hsplit]
  have hfinal : (1 + 1 / (σ - 1)) * E +
      (S.card : ℝ) * ((1 + 1 / (σ - 1)) * (E * Real.exp (-(δ ^ (2 : ℕ))))) =
      (1 + 1 / (σ - 1)) * (E * ((S.card : ℝ) * Real.exp (-(δ ^ (2 : ℕ))) + 1)) := by
    ring
  linarith [hclosesum, hfarsum, hfinal]

/-- **The same bound with a checkable spacing hypothesis.**  Points spaced further apart than the
frequency window cannot both be close, so the uniqueness input is supplied by the corpus's window
estimate. -/
theorem sum_norm_tsum_twistedSummand_le_of_spacing
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z)
    {δ Δ : ℝ} (hδ : 0 ≤ δ) (hΔ0 : 0 ≤ Δ) (hW : 0 < logSqWeight z)
    (hΔ : 2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z < Δ ^ (2 : ℕ))
    (S : Finset ℝ)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → Δ ≤ |t - u|)
    (hsmall : ∀ t ∈ S, ∀ u ∈ S, ∀ p ∈ Nat.primesLE z,
      |(t - u) * Real.log (p : ℝ)| ≤ Real.pi) :
    ∑ t ∈ S, ‖∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n‖ ≤
      (1 + 1 / (σ - 1)) *
        (Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4)) *
          ((S.card : ℝ) * Real.exp (-(δ ^ (2 : ℕ))) + 1)) :=
  sum_norm_tsum_twistedSummand_le_of_card hf1 hmul hbdd hσ hz hδ S
    (card_filter_close_le_one_of_spacing hz (fun p _ => hbdd p) hΔ0 hW hΔ S hspace hsmall)

end

end RHTower.Sieve
