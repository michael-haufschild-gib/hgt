import GaloisForLFunctions.RHTower.DeningerAbelCoefficient

/-!
# The Möbius harmonic series converges

`∑ μ(n)/n` is only conditionally convergent, so it is not `Summable` in the unordered sense; its
convergence has to be stated for the partial sums.  Summation by parts turns it into

`∑_{n ≤ N} μ(n)/n = M(N)/N + ∑_{n < N} M(n)/(n(n+1))`,

where the boundary term vanishes by the prime number theorem in Mertens form and the remaining
series is absolutely convergent — the same inverse-square control the unconditional saving gives.

* `deningerMertensHarmonic_summable` : the signed coefficient series converges absolutely.
* `deningerMobiusHarmonic_tendsto` : **the partial sums of `∑ μ(n)/n` converge.**
-/

namespace RHTower

open ArithmeticFunction Filter Topology

noncomputable section

/-- The signed coefficient series converges absolutely. -/
theorem deningerMertensHarmonic_summable :
    Summable fun i : ℕ => Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1)) := by
  refine Summable.of_abs ?_
  refine deningerAbelCoefficient_summable.congr fun i => ?_
  rw [abs_div]
  congr 1
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
    exact (abs_of_nonneg (by positivity)).symm

/-- **The Möbius harmonic partial sums converge.**  Summation by parts moves the weight onto the
summatory function; the boundary term vanishes by the prime number theorem. -/
theorem deningerMobiusHarmonic_tendsto :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℝ) / (n : ℝ)) atTop
      (𝓝 (∑' i : ℕ, Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1)))) := by
  classical
  set F : ℕ → ℝ := fun i => 1 / (i : ℝ) with hF
  set G : ℕ → ℝ := fun i => ((moebius i : ℤ) : ℝ) with hG
  have hMsum : ∀ i : ℕ, (∑ j ∈ Finset.range (i + 1), G j) = Sieve.mertensM i := fun i => rfl
  have hparts : ∀ N : ℕ,
      (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℝ) / (n : ℝ))
        = F N * Sieve.mertensM N
          + ∑ i ∈ Finset.range N, Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1)) := by
    intro N
    have hbp := Finset.sum_range_by_parts F G (N + 1)
    simp only [Nat.add_sub_cancel, smul_eq_mul] at hbp
    rw [hMsum N] at hbp
    have hinner : ∀ i ∈ Finset.range N,
        (F (i + 1) - F i) * (∑ j ∈ Finset.range (i + 1), G j)
          = -(Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1))) := by
      intro i hi
      rw [hMsum i, hF]
      simp only
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · have hz : Sieve.mertensM 0 = 0 := by
          rw [Sieve.mertensM]
          simp
        rw [hz]
        simp
      · have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hipos
        have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
        have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        field_simp
        ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_neg_distrib] at hbp
    have hlhs : (∑ n ∈ Finset.range (N + 1), ((moebius n : ℤ) : ℝ) / (n : ℝ))
        = ∑ n ∈ Finset.range (N + 1), F n * G n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hF, hG]
      simp only
      ring
    rw [hlhs, hbp]
    ring
  have hbdry : Tendsto (fun N : ℕ => F N * Sieve.mertensM N) atTop (𝓝 0) := by
    have hpnt := Sieve.tendsto_abs_mertensM_div
    refine squeeze_zero_norm (fun N => ?_) hpnt
    rw [hF]
    simp only
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_one, one_div, abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [inv_mul_eq_div]
  have htail : Tendsto (fun N : ℕ =>
      ∑ i ∈ Finset.range N, Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1))) atTop
      (𝓝 (∑' i : ℕ, Sieve.mertensM i / ((i : ℝ) * ((i : ℝ) + 1)))) :=
    deningerMertensHarmonic_summable.hasSum.tendsto_sum_nat
  have hsum := hbdry.add htail
  rw [zero_add] at hsum
  exact hsum.congr fun N => (hparts N).symm

end

end RHTower
