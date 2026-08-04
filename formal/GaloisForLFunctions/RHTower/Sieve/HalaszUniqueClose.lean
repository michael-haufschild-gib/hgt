import GaloisForLFunctions.RHTower.Sieve.HalaszDichotomy
import GaloisForLFunctions.RHTower.Sieve.HalaszWindow

/-!
# At most one close character

The mean-value theorem for Dirichlet polynomials is valid for arbitrary coefficients, so it cannot
see multiplicativity and is sharp for concentrated coefficient vectors.  What Halász's method adds
is that a *multiplicative* function of modulus at most one is close, in the Granville–Soundararajan
distance, to at most one character among well-separated points.

`eq_of_both_close` says two close points coincide.  Iterated over a finite set of pairwise separated
points, this bounds the number of close points by one — so every other point of the set is far, and
the exponential decay of `norm_sum_smooth_le_exp_of_far` applies there.
-/

namespace RHTower.Sieve

open Finset

/-- **At most one point of a separated set is close to the function.** -/
theorem card_filter_close_le_one {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) {δ : ℝ} (S : Finset ℝ)
    (hsmall : ∀ t ∈ S, ∀ u ∈ S, ∀ p ∈ P, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi)
    (hsep : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → 2 * Real.pi ^ 2 * δ ^ 2
      < (t - u) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 / (p : ℝ)) :
    ((S.filter (fun t => Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)).card) ≤ 1 := by
  classical
  refine Finset.card_le_one.2 ?_
  intro t ht u hu
  rw [Finset.mem_filter] at ht hu
  exact eq_of_both_close hf hP ht.2 hu.2
    (fun p hp => hsmall t ht.1 u hu.1 p hp)
    (fun hne => hsep t ht.1 u hu.1 hne)

/-- **Every other point is far.**  Outside a single exceptional point of a separated set, the
Granville–Soundararajan distance exceeds `δ`. -/
theorem exists_subset_far {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) {δ : ℝ} (S : Finset ℝ)
    (hsmall : ∀ t ∈ S, ∀ u ∈ S, ∀ p ∈ P, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi)
    (hsep : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → 2 * Real.pi ^ 2 * δ ^ 2
      < (t - u) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 / (p : ℝ)) :
    ∃ E : Finset ℝ, E ⊆ S ∧ E.card ≤ 1
      ∧ ∀ t ∈ S \ E, δ < Real.sqrt (mulDistSqPair f (charFn t) P) := by
  classical
  refine ⟨S.filter (fun t => Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ),
    Finset.filter_subset _ _, card_filter_close_le_one hf hP S hsmall hsep, ?_⟩
  intro t ht
  rw [Finset.mem_sdiff, Finset.mem_filter] at ht
  by_contra hcon
  rw [not_lt] at hcon
  exact ht.2 ⟨ht.1, hcon⟩

/-- The smooth multiplicative sum over the squarefree integers built from `P`. -/
noncomputable def smoothMulSum (f : ℕ → ℂ) (P : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ P.powerset.image (fun T => ∏ p ∈ T, p), ((1 / (n : ℝ) : ℝ) : ℂ)
    * (f n * Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I))

/-- **The Halász sum bound over a separated set.**  All but one point contributes the decayed
bound; the exceptional point contributes the trivial one. -/
theorem sum_norm_smoothMulSum_le_of_card {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPpos : ∀ p ∈ P, 0 < p)
    {δ : ℝ} (hδ : 0 ≤ δ) (S : Finset ℝ)
    (hEcard : ((S.filter
      (fun t => Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)).card) ≤ 1) :
    ∑ t ∈ S, ‖smoothMulSum f P t‖
      ≤ (S.card : ℝ)
          * Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - δ ^ 2)
        + Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2)) := by
  classical
  have htriv : ∀ t : ℝ, ‖smoothMulSum f P t‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2)) := by
    intro t
    rw [smoothMulSum]
    refine le_trans (norm_sum_smooth_le_exp hf hmul h1 t hP) (Real.exp_le_exp.mpr ?_)
    have hnn : 0 ≤ mulDistSq f t P := by
      rw [mulDistSq_eq_pair]
      exact mulDistSqPair_nonneg_disc (fun p _ => hf p) (fun p _ => (norm_charFn t p).le) hPpos
    linarith
  have hfar : ∀ t ∈ S.filter (fun t => ¬ Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ),
      ‖smoothMulSum f P t‖
        ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - δ ^ 2) := by
    intro t ht
    rw [Finset.mem_filter, not_le] at ht
    rw [smoothMulSum]
    exact norm_sum_smooth_le_exp_of_far hf hmul h1 t hP hδ (le_of_lt ht.2)
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun t => Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)
    (fun t => ‖smoothMulSum f P t‖)
  have hEbound : ∑ t ∈ S.filter (fun t => Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ),
      ‖smoothMulSum f P t‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2)) := by
    refine le_trans (Finset.sum_le_sum fun t _ => htriv t) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (((S.filter (fun t => Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)).card : ℕ) : ℝ)
        ≤ 1 := by exact_mod_cast hEcard
    have hpos : (0 : ℝ) ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2)) :=
      (Real.exp_pos _).le
    nlinarith [hc, hpos]
  have hFbound : ∑ t ∈ S.filter (fun t => ¬ Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ),
      ‖smoothMulSum f P t‖
      ≤ (S.card : ℝ)
          * Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - δ ^ 2) := by
    refine le_trans (Finset.sum_le_sum hfar) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : (((S.filter
        (fun t => ¬ Real.sqrt (mulDistSqPair f (charFn t) P) ≤ δ)).card : ℕ) : ℝ)
        ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hpos : (0 : ℝ)
        ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - δ ^ 2) :=
      (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right hc hpos
  linarith [hsplit, hEbound, hFbound]

/-- **At most one close point, from a spacing hypothesis.**  The frequency window turns the abstract
separation condition into a checkable one: points spaced further apart than the window width cannot
both be close. -/
theorem card_filter_close_le_one_of_spacing {f : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N)
    (hf : ∀ p ∈ Nat.primesLE N, ‖f p‖ ≤ 1) {δ Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hW : 0 < logSqWeight N)
    (hΔ : 2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight N < Δ ^ 2)
    (S : Finset ℝ)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → Δ ≤ |t - u|)
    (hsmall : ∀ t ∈ S, ∀ u ∈ S, ∀ p ∈ Nat.primesLE N,
      |(t - u) * Real.log (p : ℝ)| ≤ Real.pi) :
    ((S.filter (fun t =>
      Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE N)) ≤ δ)).card) ≤ 1 := by
  classical
  refine Finset.card_le_one.2 ?_
  intro t ht u hu
  rw [Finset.mem_filter] at ht hu
  by_contra hne
  have hwin := sq_sub_le_div hN hf hW ht.2 hu.2 (fun p hp => hsmall t ht.1 u hu.1 p hp)
  have hsp := hspace t ht.1 u hu.1 hne
  have hsq : Δ ^ 2 ≤ (t - u) ^ 2 := by
    have habs : Δ ^ 2 ≤ |t - u| ^ 2 := pow_le_pow_left₀ hΔ0 hsp 2
    rwa [sq_abs] at habs
  linarith

/-- **The Halász sum bound with the separation hypothesis.** -/
theorem sum_norm_smoothMulSum_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPpos : ∀ p ∈ P, 0 < p)
    {δ : ℝ} (hδ : 0 ≤ δ) (S : Finset ℝ)
    (hsmall : ∀ t ∈ S, ∀ u ∈ S, ∀ p ∈ P, |(t - u) * Real.log (p : ℝ)| ≤ Real.pi)
    (hsep : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → 2 * Real.pi ^ 2 * δ ^ 2
      < (t - u) ^ 2 * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 / (p : ℝ)) :
    ∑ t ∈ S, ‖smoothMulSum f P t‖
      ≤ (S.card : ℝ)
          * Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - δ ^ 2)
        + Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2)) :=
  sum_norm_smoothMulSum_le_of_card hf hmul h1 hP hPpos hδ S
    (card_filter_close_le_one (fun p _ => hf p) hPpos S hsmall hsep)

/-- **The Halász sum bound with a checkable spacing hypothesis.**  Every hypothesis is a comparison
of explicit quantities: the mesh `Δ` of the frequency set against the window width. -/
theorem sum_norm_smoothMulSum_le_of_spacing {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {N : ℕ} (hN : 1 ≤ N) {δ Δ : ℝ} (hδ : 0 ≤ δ) (hΔ0 : 0 ≤ Δ)
    (hW : 0 < logSqWeight N)
    (hΔ : 2 * Real.pi ^ 2 * δ ^ 2 / logSqWeight N < Δ ^ 2)
    (S : Finset ℝ)
    (hspace : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → Δ ≤ |t - u|)
    (hsmall : ∀ t ∈ S, ∀ u ∈ S, ∀ p ∈ Nat.primesLE N,
      |(t - u) * Real.log (p : ℝ)| ≤ Real.pi) :
    ∑ t ∈ S, ‖smoothMulSum f (Nat.primesLE N) t‖
      ≤ (S.card : ℝ)
          * Real.exp ((∑ p ∈ Nat.primesLE N, 1 / (p : ℝ))
            + (∑ p ∈ Nat.primesLE N, 1 / (p : ℝ) ^ 2) - δ ^ 2)
        + Real.exp ((∑ p ∈ Nat.primesLE N, 1 / (p : ℝ))
            + (∑ p ∈ Nat.primesLE N, 1 / (p : ℝ) ^ 2)) :=
  sum_norm_smoothMulSum_le_of_card hf hmul h1
    (fun _ hp => Nat.prime_of_mem_primesLE hp)
    (fun _ hp => (Nat.prime_of_mem_primesLE hp).pos) hδ S
    (card_filter_close_le_one_of_spacing hN (fun p _ => hf p) hΔ0 hW hΔ S hspace hsmall)

end RHTower.Sieve
