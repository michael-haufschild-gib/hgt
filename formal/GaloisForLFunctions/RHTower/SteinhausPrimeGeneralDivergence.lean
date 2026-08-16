import GaloisForLFunctions.RHTower.SteinhausPrimeDivergence

/-!
# Divergence for arbitrary prime-supported coefficients

The whole chain — second moment, fourth moment, escape, zero–one law — uses nothing about the
coefficients `p^{−σ}` beyond the divergence of `∑_p a_p²`.  Stated for a general real sequence:

```text
∑_{p<N} a_p² → ∞   ⟹   Haar { ω : ∑_p a_p X_p(ω) converges } = 0 .
```

The fourth moment is `2(∑ a_p²)² − ∑ a_p⁴ ≤ 2(∑ a_p²)²` for every real sequence, because the two
diagonals of `p r = q t` over primes do not see the coefficients at all.
-/

noncomputable section

open MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- The prime-supported Steinhaus polynomial with arbitrary coefficients. -/
def steinhausPrimeGenPoly (a : ℕ → ℝ) (N : ℕ) (ω : Omega) : ℂ :=
  ∑ p ∈ primeSet N, ((a p : ℝ) : ℂ) * X p ω

theorem integral_normSq_genPoly (a : ℕ → ℝ) (N : ℕ) :
    ∫ ω, ‖steinhausPrimeGenPoly a N ω‖ ^ 2 ∂steinhausMeasure
      = ∑ p ∈ primeSet N, (a p) ^ 2 := by
  simp only [steinhausPrimeGenPoly]
  exact integral_normSq_dpoly a (primeSet N) fun p hp => ne_zero_of_mem_primeSet hp

theorem integral_normSq_sq_genPoly (a : ℕ → ℝ) (N : ℕ) :
    ∫ ω, ‖steinhausPrimeGenPoly a N ω‖ ^ 4 ∂steinhausMeasure
      = 2 * (∑ p ∈ primeSet N, (a p) ^ 2) ^ 2 - ∑ p ∈ primeSet N, (a p) ^ 4 := by
  simp only [steinhausPrimeGenPoly]
  rw [integral_normSq_sq_dpoly a (primeSet N) fun p hp => ne_zero_of_mem_primeSet hp]
  refine quadruple_diagonal_sum (primeSet N) a ?_
  intro p hp q hq r hr t ht
  constructor
  · intro h
    exact prime_mul_eq_prime_mul (prime_of_mem_primeSet hp) (prime_of_mem_primeSet hq)
      (prime_of_mem_primeSet hr) h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ring

theorem norm_genPoly_le (a : ℕ → ℝ) (N : ℕ) (ω : Omega) :
    ‖steinhausPrimeGenPoly a N ω‖ ≤ ∑ p ∈ primeSet N, |a p| := by
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun p _ => ?_
  rw [norm_mul, norm_X, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem measurable_genPoly (a : ℕ → ℝ) (N : ℕ) : Measurable (steinhausPrimeGenPoly a N) := by
  refine Finset.measurable_sum _ fun p _ => ?_
  exact (measurable_X p).const_mul _

theorem integrable_normSq_genPoly (a : ℕ → ℝ) (N : ℕ) :
    Integrable (fun ω => ‖steinhausPrimeGenPoly a N ω‖ ^ 2) steinhausMeasure := by
  set B : ℝ := ∑ p ∈ primeSet N, |a p| with hB
  apply Integrable.mono' (integrable_const (B ^ 2))
  · exact (((measurable_genPoly a N).norm).pow_const 2).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [norm_genPoly_le a N ω, norm_nonneg (steinhausPrimeGenPoly a N ω)]

theorem integrable_normSq_sq_genPoly (a : ℕ → ℝ) (N : ℕ) :
    Integrable (fun ω => (‖steinhausPrimeGenPoly a N ω‖ ^ 2) ^ 2) steinhausMeasure := by
  set B : ℝ := ∑ p ∈ primeSet N, |a p| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun p _ => abs_nonneg _
  apply Integrable.mono' (integrable_const ((B ^ 2) ^ 2))
  · refine Measurable.aestronglyMeasurable ?_
    exact (((measurable_genPoly a N).norm.pow_const 2).pow_const 2)
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := norm_genPoly_le a N ω
    have h0 : (0 : ℝ) ≤ ‖steinhausPrimeGenPoly a N ω‖ := norm_nonneg _
    have h1 : ‖steinhausPrimeGenPoly a N ω‖ ^ 2 ≤ B ^ 2 := by nlinarith [hb, h0, hB0]
    nlinarith [h1, sq_nonneg (‖steinhausPrimeGenPoly a N ω‖ ^ 2), sq_nonneg B]

/-- **Unbounded partial sums whenever the coefficient square-sum diverges.** -/
theorem measure_genPoly_unbounded {a : ℕ → ℝ}
    (hdiv : Tendsto (fun N => ∑ p ∈ primeSet N, (a p) ^ 2) atTop atTop) :
    ENNReal.ofReal (1 / 8) ≤ steinhausMeasure
      {ω | ∀ K : ℕ, ∃ N, (K : ℝ) < ‖steinhausPrimeGenPoly a N ω‖} := by
  have hup : ∀ N : ℕ,
      (∫ ω, (‖steinhausPrimeGenPoly a N ω‖ ^ 2) ^ 2 ∂steinhausMeasure)
        ≤ 2 * (∫ ω, ‖steinhausPrimeGenPoly a N ω‖ ^ 2 ∂steinhausMeasure) ^ 2 := by
    intro N
    have hpow : ∀ ω : Omega, (‖steinhausPrimeGenPoly a N ω‖ ^ 2) ^ 2
        = ‖steinhausPrimeGenPoly a N ω‖ ^ 4 := fun ω => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpow),
      integral_normSq_sq_genPoly, integral_normSq_genPoly]
    have hnn : (0 : ℝ) ≤ ∑ p ∈ primeSet N, (a p) ^ 4 :=
      Finset.sum_nonneg fun p _ => by positivity
    linarith
  have hA : Tendsto (fun N => ∫ ω, ‖steinhausPrimeGenPoly a N ω‖ ^ 2 ∂steinhausMeasure)
      atTop atTop := by
    simpa [integral_normSq_genPoly] using hdiv
  have hres := measure_unbounded_ge (μ := steinhausMeasure)
    (f := fun N ω => ‖steinhausPrimeGenPoly a N ω‖)
    (fun N => (measurable_genPoly a N).norm) (fun N ω => norm_nonneg _)
    (fun N => integrable_normSq_genPoly a N) (fun N => integrable_normSq_sq_genPoly a N)
    (C := 2) (by norm_num) hup hA
  have hval : (1 : ℝ) / (4 * 2) = 1 / 8 := by norm_num
  rw [hval] at hres
  exact hres

/-! ## The coordinatewise form and the divergence theorem -/

/-- The general prime-supported term as a function of one coordinate. -/
def genTerm (a : ℕ → ℝ) (n : ℕ) : ℝ → ℂ :=
  fun x => if n.Prime then ((a n : ℝ) : ℂ)
    * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((x : ℝ) : ℂ)) else 0

theorem measurable_genTerm (a : ℕ → ℝ) (n : ℕ) : Measurable (genTerm a n) := by
  by_cases h : n.Prime
  · have heq : genTerm a n = fun x : ℝ => ((a n : ℝ) : ℂ)
        * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((x : ℝ) : ℂ)) := by
      funext x
      rw [genTerm, if_pos h]
    rw [heq]
    exact measurable_const.mul (Complex.measurable_exp.comp (by fun_prop))
  · have heq : genTerm a n = fun _ : ℝ => (0 : ℂ) := by
      funext x
      rw [genTerm, if_neg h]
    rw [heq]
    exact measurable_const

theorem coordPartialSum_genTerm (a : ℕ → ℝ) (N : ℕ) (ω : Omega) :
    coordPartialSum (genTerm a) N ω = steinhausPrimeGenPoly a N ω := by
  rw [coordPartialSum, steinhausPrimeGenPoly, primeSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [genTerm]
  by_cases h : n.Prime
  · rw [if_pos h, if_pos h, X_prime_eq h]
  · rw [if_neg h, if_neg h]

theorem not_unbounded_of_converges_gen (a : ℕ → ℝ) {ω : Omega}
    (hconv : ω ∈ coordSeriesConverges (genTerm a)) :
    ¬ (∀ K : ℕ, ∃ N, (K : ℝ) < ‖steinhausPrimeGenPoly a N ω‖) := by
  obtain ⟨L, hL⟩ := hconv
  have hcauchy : CauchySeq (fun N => coordPartialSum (genTerm a) N ω) := hL.cauchySeq
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hcauchy.isBounded_range
  intro hall
  obtain ⟨K, hK⟩ := exists_nat_gt C
  obtain ⟨N, hN⟩ := hall K
  have hbd : ‖coordPartialSum (genTerm a) N ω‖ ≤ C := hC _ (Set.mem_range_self N)
  rw [coordPartialSum_genTerm] at hbd
  linarith

/-- **Almost-sure divergence for any prime-supported coefficients with divergent square sum.** -/
theorem measure_coordSeriesConverges_genTerm_eq_zero {a : ℕ → ℝ}
    (hdiv : Tendsto (fun N => ∑ p ∈ primeSet N, (a p) ^ 2) atTop atTop) :
    steinhausMeasure (coordSeriesConverges (genTerm a)) = 0 := by
  have hdich := measure_coordSeriesConverges_eq_zero_or_one
    (μ := fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1)) (fun _ => 0)
    (genTerm a) (measurable_genTerm a)
  rw [← steinhausMeasure] at hdich
  rcases hdich with h | h
  · exact h
  · exfalso
    set U : Set Omega := {ω | ∀ K : ℕ, ∃ N, (K : ℝ) < ‖steinhausPrimeGenPoly a N ω‖} with hU
    have hUmeas : ENNReal.ofReal (1 / 8) ≤ steinhausMeasure U := measure_genPoly_unbounded hdiv
    have hdisj : coordSeriesConverges (genTerm a) ⊆ Uᶜ := fun ω hω =>
      not_unbounded_of_converges_gen a hω
    have hle : steinhausMeasure U ≤ steinhausMeasure (coordSeriesConverges (genTerm a))ᶜ :=
      measure_mono (Set.subset_compl_comm.1 hdisj)
    have hone : steinhausMeasure (coordSeriesConverges (genTerm a))ᶜ = 0 := by
      have hmeas := measurableSet_coordSeriesConverges (genTerm a) (measurable_genTerm a)
      rw [prob_compl_eq_one_sub hmeas, h, tsub_self]
    rw [hone] at hle
    have hcon : ENNReal.ofReal (1 / 8) ≤ 0 := le_trans hUmeas hle
    rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hcon
    norm_num at hcon

end GaloisForLFunctions.RHTower

end
