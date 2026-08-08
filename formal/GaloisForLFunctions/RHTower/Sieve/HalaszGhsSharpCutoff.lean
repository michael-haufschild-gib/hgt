import GaloisForLFunctions.RHTower.Sieve.GhsPerronDamped
import GaloisForLFunctions.RHTower.Sieve.PartialSumVsTripleConvolution

/-!
# A Halász-type mean value bound in the sharp-cutoff architecture

Joining the two halves of the Granville–Harper–Soundararajan argument as they now stand:

* the paper half — `(∑_{n ≤ N} f(n))·log N` is the summatory function of the triple convolution up to
  `O(N log log N)`;
* the analytic half — that summatory function is bounded through the sharp Perron formula, the dyadic
  height split, the prime-sieve mean squares, and the damped size of the third factor.

Truncating the third factor at `L ≥ N` changes nothing below `N`, because every index a convolution
touches at `n` divides `n`.  So the two halves speak about the same object and compose into

`‖∑_{n ≤ N} f(n)‖·log N ≤ (recursion error) + (Perron truncation error) + (analytic bound)`,

unconditional, for every completely multiplicative `f` with `‖f‖ ≤ 1`, with the distance `δ` entering only
through `dampedSize`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- Truncating the inner factor of a convolution changes nothing below the truncation point: every
index the convolution touches at `m` divides `m`. -/
theorem convolution_truncSeq_eq_of_le {B f : ℕ → ℂ} {L m : ℕ} (hm : m ≤ L) :
    (LSeries.convolution B f) m = (LSeries.convolution B (truncSeq f L)) m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  simp only [LSeries.convolution_def]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hq
  have hq0 : q.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hq.2 hq.1.symm
  have hqdvd : q.2 ∣ m := ⟨q.1, by rw [← hq.1]; ring⟩
  have hqle : q.2 ≤ m := Nat.le_of_dvd hm0 hqdvd
  have hmem : q.2 ∈ Finset.Icc 1 L :=
    Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hq0, le_trans hqle hm⟩
  rw [truncSeq, if_pos hmem]

/-- Truncating the third factor of a threefold convolution changes nothing below the truncation
point. -/
theorem convolution_triple_truncSeq_eq_of_le {A B f : ℕ → ℂ} {L n : ℕ} (hn : n ≤ L) :
    (LSeries.convolution A (LSeries.convolution B f)) n
      = (LSeries.convolution A (LSeries.convolution B (truncSeq f L))) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  simp only [LSeries.convolution_def]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have hdvd : p.2 ∣ n := ⟨p.1, by rw [← hp.1]; ring⟩
  have hple : p.2 ≤ n := Nat.le_of_dvd hn0 hdvd
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hq
  have hq0 : q.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hq
    exact hq.2 hq.1.symm
  have hqdvd : q.2 ∣ p.2 := ⟨q.1, by rw [← hq.1]; ring⟩
  have hqle : q.2 ≤ p.2 := Nat.le_of_dvd (Nat.pos_of_ne_zero hq.2) hqdvd
  have hmem : q.2 ∈ Finset.Icc 1 L :=
    Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hq0, by omega⟩
  rw [truncSeq, if_pos hmem]

/-- The partial sum of a threefold convolution is unchanged by truncating the third factor at any
point beyond the range of summation. -/
theorem sum_Icc_convolution_triple_truncSeq_eq {A B f : ℕ → ℂ} {L N : ℕ} (hNL : N ≤ L) :
    (∑ n ∈ Finset.Icc 1 N, (LSeries.convolution A (LSeries.convolution B f)) n)
      = ∑ n ∈ Finset.Icc 1 N,
          (LSeries.convolution A (LSeries.convolution B (truncSeq f L))) n :=
  Finset.sum_congr rfl fun _ hn =>
    convolution_triple_truncSeq_eq_of_le (le_trans (Finset.mem_Icc.1 hn).2 hNL)

/-- **A Halász-type mean value bound, unconditional.**  For a completely multiplicative `f` with
`‖f‖ ≤ 1` at multiplicative distance at least `δ` from every character `n^{it}`, `|t| ≤ t₀2^K`, the
partial sum obeys

`‖∑_{n ≤ N} f(n)‖·log N ≤ (recursion error) + (Perron truncation error) + (analytic bound)`,

the distance entering only through `dampedSize σ δ z N`.  Every constant is explicit and every
ingredient — the logarithmic recursion, Perron's lemma, the dyadic height split, the Selberg-sieve mean
squares, the damped Euler bound — is unconditional. -/
theorem norm_sum_Icc_mul_log_le_damped {f : ℕ → ℂ} (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (hf1 : f 1 = 1) {N : ℕ} (hN : 2 ≤ N)
    {σ t₀ δ : ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀) (hδ : 0 ≤ δ) {z : ℕ} (hz : 1 ≤ z) (K : ℕ)
    (hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
          + (9 + RHTower.Mertens.mertensTail)
              * ((N : ℝ)
                  * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                        / Real.log 2)
                      * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
        + (2 * ((N : ℝ) + 1) * ((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
                * (((N : ℝ) + 1 / 2)) ^ σ
                * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) / (Real.pi * (t₀ * 2 ^ K))
            + (1 / (2 * Real.pi))
                * (2 * perronVerticalProductBound (ghsOuter f N) (ghsInner f N)
                      (Finset.Icc 1 N) (Finset.Icc 1 N) σ ((N : ℝ) + 1 / 2) t₀
                      (dampedSize σ δ z N) zA YA zB YB K
                    + ((dampedSize σ δ z N) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                        * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N) (Finset.Icc 1 N) σ YA
                              + sieveMeanSquareRate (ghsOuter f N) (Finset.Icc 1 N) σ zA YA * t₀)
                            * Real.sqrt (sieveMeanSquareConst (ghsInner f N) (Finset.Icc 1 N) σ YB
                              + sieveMeanSquareRate (ghsInner f N) (Finset.Icc 1 N) σ zB YB
                                  * t₀)))) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := fun {m n} _ => hf m n
  have hNcube : N ≤ N * (N * N) := by
    calc N = N * 1 := by ring
      _ ≤ N * (N * N) := Nat.mul_le_mul_left N (by nlinarith)
  have hprod : 1 ≤ N * (N * N) := le_trans hN1 hNcube
  -- the paper half
  have hpaper := norm_sum_Icc_mul_log_sub_ghsTriple_le hf hbdd N hN
  -- the analytic half, at the truncation `L = N`
  have hanalytic := norm_sum_Icc_ghsTriple_damped_le (f := f) hf1 hmul hbdd
    (N₀ := N) (M := N) (L := N) (N := N) hprod hN1 hN1 hσ ht₀ hδ hz K hunif
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB
  rw [min_eq_right hNcube] at hanalytic
  rw [← sum_Icc_convolution_triple_truncSeq_eq (le_refl N)] at hanalytic
  -- assemble
  have hsplit : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ n ∈ Finset.Icc 1 N,
              (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖
          + ‖∑ n ∈ Finset.Icc 1 N,
              (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N,
          (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
      (∑ n ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
    simpa using this
  have hnorm : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      = ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
  rw [hnorm] at hsplit
  linarith [hsplit, hpaper, hanalytic]

/-- **A Halász-type mean value bound with the near-diagonal truncation error.**  The same assembly,
with the Perron truncation error taken in its near-diagonal form: its dependence on the length of the
sum is `x^σ·log N` rather than `N·x^σ·log N`, so the height `t₀2^K` no longer has to grow with `N` for
the truncation error to be negligible. -/
theorem norm_sum_Icc_mul_log_le_damped_near {f : ℕ → ℂ} (hf : ∀ a b : ℕ, f (a * b) = f a * f b)
    (hbdd : ∀ n : ℕ, ‖f n‖ ≤ 1) (hf1 : f 1 = 1) {N : ℕ} (hN : 2 ≤ N)
    {σ t₀ δ : ℝ} (hσ : 1 < σ) (ht₀ : 1 ≤ t₀) (hδ : 0 ≤ δ) {z : ℕ} (hz : 1 ≤ z) (K : ℕ)
    (hunif : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ K →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z)))
    (zA YA zB YB : ℕ) (hYA : 1 ≤ YA) (hYzA : YA ≤ zA) (hzA : 2 ≤ zA) (hlogA : 0 < Real.log YA)
    (hYB : 1 ≤ YB) (hYzB : YB ≤ zB) (hzB : 2 ≤ zB) (hlogB : 0 < Real.log YB) :
    ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ)
      ≤ ((9 + RHTower.Mertens.mertensTail) * (N : ℝ) + (N : ℝ) * Real.log 4
          + (9 + RHTower.Mertens.mertensTail)
              * ((N : ℝ)
                  * (((Real.log 3 + 2 * ((Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)))
                        / Real.log 2)
                      * (1 + Real.log ((Nat.log 2 N : ℕ) : ℝ)))))
        + (((Real.log ((N * (N * N) : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3)
                * (((N : ℝ) + 1 / 2)) ^ σ
                * (5 * (1 + Real.log ((N * (N * N) : ℕ) : ℝ)) + 4 * (1 + Real.log N))
                / (Real.pi * (t₀ * 2 ^ K))
            + (1 / (2 * Real.pi))
                * (2 * perronVerticalProductBound (ghsOuter f N) (ghsInner f N)
                      (Finset.Icc 1 N) (Finset.Icc 1 N) σ ((N : ℝ) + 1 / 2) t₀
                      (dampedSize σ δ z N) zA YA zB YB K
                    + ((dampedSize σ δ z N) * ((N : ℝ) + 1 / 2) ^ σ / σ)
                        * (Real.sqrt (sieveMeanSquareConst (ghsOuter f N) (Finset.Icc 1 N) σ YA
                              + sieveMeanSquareRate (ghsOuter f N) (Finset.Icc 1 N) σ zA YA * t₀)
                            * Real.sqrt (sieveMeanSquareConst (ghsInner f N) (Finset.Icc 1 N) σ YB
                              + sieveMeanSquareRate (ghsInner f N) (Finset.Icc 1 N) σ zB YB
                                  * t₀)))) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := fun {m n} _ => hf m n
  have hNcube : N ≤ N * (N * N) := by
    calc N = N * 1 := by ring
      _ ≤ N * (N * N) := Nat.mul_le_mul_left N (by nlinarith)
  have hprod : 1 ≤ N * (N * N) := le_trans hN1 hNcube
  have hpaper := norm_sum_Icc_mul_log_sub_ghsTriple_le hf hbdd N hN
  have hanalytic := norm_sum_Icc_ghsTriple_damped_near_le (f := f) hf1 hmul hbdd
    (N₀ := N) (M := N) (L := N) (N := N) hprod hN1 hσ ht₀ hδ hz K hunif
    zA YA zB YB hYA hYzA hzA hlogA hYB hYzB hzB hlogB
  rw [min_eq_right hNcube] at hanalytic
  rw [← sum_Icc_convolution_triple_truncSeq_eq (le_refl N)] at hanalytic
  have hsplit : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
            - ∑ n ∈ Finset.Icc 1 N,
              (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖
          + ‖∑ n ∈ Finset.Icc 1 N,
              (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n‖ := by
    have := norm_add_le ((∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ∑ n ∈ Finset.Icc 1 N,
          (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
      (∑ n ∈ Finset.Icc 1 N,
        (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f N) f)) n)
    simpa using this
  have hnorm : ‖(∑ n ∈ Finset.Icc 1 N, f n) * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      = ‖∑ n ∈ Finset.Icc 1 N, f n‖ * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogN]
  rw [hnorm] at hsplit
  linarith [hsplit, hpaper, hanalytic]

end RHTower.Sieve
end
