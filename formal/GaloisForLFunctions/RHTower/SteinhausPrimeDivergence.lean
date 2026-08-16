import GaloisForLFunctions.RHTower.SteinhausPrimeUnbounded
import GaloisForLFunctions.HTGeometry.SeriesConvergenceZeroOne

/-!
# The prime random Dirichlet series diverges almost surely up to the half line

The prime-indexed terms of the Steinhaus series read one coordinate each — for a prime `p` the
character is `X_p(ω) = e^{2πi ω_p}` — so the convergence of `∑_p p^{−σ} X_p` is a tail event and has
probability `0` or `1`.  The escape bound puts the partial sums outside every ball with probability
at least `1/8`, so the probability of convergence is at most `7/8`, hence zero:

```text
Haar { ω : ∑_p p^{−σ} X_p(ω) converges }  =  0        for every σ ≤ 1/2 .
```

This is the almost-sure divergence statement, obtained from Paley–Zygmund, the prime fourth moment
and Mertens — with no appeal to Kolmogorov's three-series theorem or to Itô–Nisio.
-/

noncomputable section

open MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- For a prime index the Steinhaus character reads a single coordinate. -/
theorem X_prime_eq {p : ℕ} (hp : p.Prime) (ω : Omega) :
    X p ω = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((ω p : ℝ) : ℂ)) := by
  rw [X, hp.primeFactors]
  congr 2
  rw [Finset.sum_singleton, hp.factorization_self]
  push_cast
  ring

/-- The `n`-th term of the prime Dirichlet series, as a function of the `n`-th coordinate alone. -/
def primeTerm (σ : ℝ) (n : ℕ) : ℝ → ℂ :=
  fun x => if n.Prime then (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
    * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((x : ℝ) : ℂ)) else 0

theorem measurable_primeTerm (σ : ℝ) (n : ℕ) : Measurable (primeTerm σ n) := by
  by_cases h : n.Prime
  · have heq : primeTerm σ n = fun x : ℝ => (((n : ℝ) ^ (-σ) : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((x : ℝ) : ℂ)) := by
      funext x
      rw [primeTerm, if_pos h]
    rw [heq]
    exact measurable_const.mul (Complex.measurable_exp.comp (by fun_prop))
  · have heq : primeTerm σ n = fun _ : ℝ => (0 : ℂ) := by
      funext x
      rw [primeTerm, if_neg h]
    rw [heq]
    exact measurable_const

/-- The coordinatewise partial sums are exactly the prime Dirichlet polynomials. -/
theorem coordPartialSum_primeTerm (σ : ℝ) (N : ℕ) (ω : Omega) :
    coordPartialSum (primeTerm σ) N ω = steinhausPrimePoly σ N ω := by
  rw [coordPartialSum, steinhausPrimePoly, primeSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [primeTerm]
  by_cases h : n.Prime
  · rw [if_pos h, if_pos h, X_prime_eq h]
  · rw [if_neg h, if_neg h]

/-- A convergent series has bounded partial sums, so it misses the escape set. -/
theorem not_unbounded_of_converges (σ : ℝ) {ω : Omega}
    (hconv : ω ∈ coordSeriesConverges (primeTerm σ)) :
    ¬ (∀ K : ℕ, ∃ N, (K : ℝ) < ‖steinhausPrimePoly σ N ω‖) := by
  obtain ⟨L, hL⟩ := hconv
  have hcauchy : CauchySeq (fun N => coordPartialSum (primeTerm σ) N ω) := hL.cauchySeq
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hcauchy.isBounded_range
  intro hall
  obtain ⟨K, hK⟩ := exists_nat_gt C
  obtain ⟨N, hN⟩ := hall K
  have hbd : ‖coordPartialSum (primeTerm σ) N ω‖ ≤ C := hC _ (Set.mem_range_self N)
  rw [coordPartialSum_primeTerm] at hbd
  linarith

/-- **The prime random Dirichlet series diverges almost surely up to the half line.** -/
theorem measure_coordSeriesConverges_primeTerm_eq_zero {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    steinhausMeasure (coordSeriesConverges (primeTerm σ)) = 0 := by
  have hdich := measure_coordSeriesConverges_eq_zero_or_one
    (μ := fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ => 0)
    (primeTerm σ) (measurable_primeTerm σ)
  rw [← steinhausMeasure] at hdich
  rcases hdich with h | h
  · exact h
  · exfalso
    set U : Set Omega := {ω | ∀ K : ℕ, ∃ N, (K : ℝ) < ‖steinhausPrimePoly σ N ω‖} with hU
    have hUmeas : ENNReal.ofReal (1 / 8) ≤ steinhausMeasure U :=
      measure_steinhausPrimePoly_unbounded hσ
    have hdisj : coordSeriesConverges (primeTerm σ) ⊆ Uᶜ := by
      intro ω hω
      exact not_unbounded_of_converges σ hω
    have hle : steinhausMeasure U ≤ steinhausMeasure (coordSeriesConverges (primeTerm σ))ᶜ :=
      measure_mono (Set.subset_compl_comm.1 hdisj)
    have hone : steinhausMeasure (coordSeriesConverges (primeTerm σ))ᶜ = 0 := by
      have hmeas := measurableSet_coordSeriesConverges (primeTerm σ) (measurable_primeTerm σ)
      rw [prob_compl_eq_one_sub hmeas, h, tsub_self]
    rw [hone] at hle
    have hcon : ENNReal.ofReal (1 / 8) ≤ 0 := le_trans hUmeas hle
    rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hcon
    norm_num at hcon

end GaloisForLFunctions.RHTower

end
