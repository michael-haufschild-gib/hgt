import GaloisForLFunctions.RHTower.SteinhausFourthMoment
import GaloisForLFunctions.RHTower.PrimeSecondMomentDivergence
import GaloisForLFunctions.HTGeometry.QuadrupleDiagonalSum
import GaloisForLFunctions.HTGeometry.FourthMomentEscape

/-!
# The prime random Dirichlet series has unbounded partial sums up to the half line

Assembling the pieces: for the prime-supported Steinhaus Dirichlet polynomial

```text
S_N(ω) = ∑_{p < N, p prime} p^{−σ} X_p(ω)
```

the second moment is `∑_{p<N} p^{−2σ}`, which diverges for `σ ≤ 1/2`, and the fourth moment is
`2(∑ p^{−2σ})² − ∑ p^{−4σ} ≤ 2(second moment)²`, because over primes the divisor diagonal
`p r = q t` degenerates to two diagonals.  The fourth-moment escape engine then gives

```text
P( sup_N ‖S_N‖ = ∞ ) ≥ 1/8 ,
```

for every `σ ≤ 1/2`.  With the zero–one law this upgrades to probability one, and in particular the
series cannot converge almost everywhere to the left of the half line.
-/

noncomputable section

open MeasureTheory Filter GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- The primes below a cut. -/
def primeSet (N : ℕ) : Finset ℕ := (Finset.range N).filter Nat.Prime

theorem prime_of_mem_primeSet {N p : ℕ} (hp : p ∈ primeSet N) : p.Prime :=
  (Finset.mem_filter.1 hp).2

theorem ne_zero_of_mem_primeSet {N p : ℕ} (hp : p ∈ primeSet N) : p ≠ 0 :=
  (prime_of_mem_primeSet hp).ne_zero

/-- The prime-supported Steinhaus Dirichlet polynomial. -/
def steinhausPrimePoly (σ : ℝ) (N : ℕ) (ω : Omega) : ℂ :=
  ∑ p ∈ primeSet N, (((p : ℝ) ^ (-σ) : ℝ) : ℂ) * X p ω

/-! ## The two moments -/

theorem integral_normSq_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    ∫ ω, ‖steinhausPrimePoly σ N ω‖ ^ 2 ∂steinhausMeasure
      = ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) := by
  simp only [steinhausPrimePoly]
  rw [integral_normSq_dpoly (fun p => ((p : ℝ) ^ (-σ))) (primeSet N)
    fun p hp => ne_zero_of_mem_primeSet hp]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (prime_of_mem_primeSet hp).pos
  rw [sq, ← Real.rpow_add hp0]
  congr 1
  ring

theorem integral_normSq_sq_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    ∫ ω, ‖steinhausPrimePoly σ N ω‖ ^ 4 ∂steinhausMeasure
      = 2 * (∑ p ∈ primeSet N, ((p : ℝ) ^ (-σ)) ^ 2) ^ 2
        - ∑ p ∈ primeSet N, ((p : ℝ) ^ (-σ)) ^ 4 := by
  simp only [steinhausPrimePoly]
  rw [integral_normSq_sq_dpoly (fun p => ((p : ℝ) ^ (-σ))) (primeSet N)
    fun p hp => ne_zero_of_mem_primeSet hp]
  refine quadruple_diagonal_sum (primeSet N) (fun p => ((p : ℝ) ^ (-σ))) ?_
  intro p hp q hq r hr t ht
  constructor
  · intro h
    exact prime_mul_eq_prime_mul (prime_of_mem_primeSet hp) (prime_of_mem_primeSet hq)
      (prime_of_mem_primeSet hr) h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · ring

/-! ## Boundedness and integrability -/

theorem norm_steinhausPrimePoly_le (σ : ℝ) (N : ℕ) (ω : Omega) :
    ‖steinhausPrimePoly σ N ω‖ ≤ ∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))| := by
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun p _ => ?_
  rw [norm_mul, norm_X, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem measurable_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    Measurable (steinhausPrimePoly σ N) := by
  refine Finset.measurable_sum _ fun p _ => ?_
  exact (measurable_X p).const_mul _

theorem integrable_normSq_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    Integrable (fun ω => ‖steinhausPrimePoly σ N ω‖ ^ 2) steinhausMeasure := by
  set B : ℝ := ∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))| with hB
  apply Integrable.mono' (integrable_const (B ^ 2))
  · exact (((measurable_steinhausPrimePoly σ N).norm).pow_const 2).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := norm_steinhausPrimePoly_le σ N ω
    have h0 : (0 : ℝ) ≤ ‖steinhausPrimePoly σ N ω‖ := norm_nonneg _
    nlinarith [hb, h0]

theorem integrable_normSq_sq_steinhausPrimePoly (σ : ℝ) (N : ℕ) :
    Integrable (fun ω => (‖steinhausPrimePoly σ N ω‖ ^ 2) ^ 2) steinhausMeasure := by
  set B : ℝ := ∑ p ∈ primeSet N, |((p : ℝ) ^ (-σ))| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun p _ => abs_nonneg _
  apply Integrable.mono' (integrable_const ((B ^ 2) ^ 2))
  · refine Measurable.aestronglyMeasurable ?_
    exact (((measurable_steinhausPrimePoly σ N).norm.pow_const 2).pow_const 2)
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := norm_steinhausPrimePoly_le σ N ω
    have h0 : (0 : ℝ) ≤ ‖steinhausPrimePoly σ N ω‖ := norm_nonneg _
    have h1 : ‖steinhausPrimePoly σ N ω‖ ^ 2 ≤ B ^ 2 := by nlinarith [hb, h0, hB0]
    nlinarith [h1, sq_nonneg (‖steinhausPrimePoly σ N ω‖ ^ 2), sq_nonneg B]

/-! ## Divergence of the second moment -/

theorem sum_primeSet_eq (σ : ℝ) (N : ℕ) :
    (∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))))
      = ∑ n ∈ Finset.range N, primeCoeff σ n := by
  rw [primeSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [primeCoeff, Set.indicator_apply]

theorem tendsto_integral_normSq_steinhausPrimePoly {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    Tendsto (fun N => ∫ ω, ‖steinhausPrimePoly σ N ω‖ ^ 2 ∂steinhausMeasure) atTop atTop := by
  have h : ∀ N : ℕ, (∫ ω, ‖steinhausPrimePoly σ N ω‖ ^ 2 ∂steinhausMeasure)
      = ∑ n ∈ Finset.range N, primeCoeff σ n := by
    intro N
    rw [integral_normSq_steinhausPrimePoly, sum_primeSet_eq]
  simpa [h] using tendsto_sum_primeCoeff_atTop hσ

/-! ## The escape -/

/-- **The prime random Dirichlet series has unbounded partial sums, with probability at least
`1/8`, everywhere up to the half line.** -/
theorem measure_steinhausPrimePoly_unbounded {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    ENNReal.ofReal (1 / 8) ≤ steinhausMeasure
      {ω | ∀ K : ℕ, ∃ N, (K : ℝ) < ‖steinhausPrimePoly σ N ω‖} := by
  have hup : ∀ N : ℕ,
      (∫ ω, (‖steinhausPrimePoly σ N ω‖ ^ 2) ^ 2 ∂steinhausMeasure)
        ≤ 2 * (∫ ω, ‖steinhausPrimePoly σ N ω‖ ^ 2 ∂steinhausMeasure) ^ 2 := by
    intro N
    have hpow : ∀ ω : Omega, (‖steinhausPrimePoly σ N ω‖ ^ 2) ^ 2
        = ‖steinhausPrimePoly σ N ω‖ ^ 4 := fun ω => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpow),
      integral_normSq_sq_steinhausPrimePoly, integral_normSq_steinhausPrimePoly]
    have hsq : ∀ p : ℕ, ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-(2 * σ)) ∨ (p : ℕ) = 0 := by
      intro p
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · exact Or.inr rfl
      · refine Or.inl ?_
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
        rw [sq, ← Real.rpow_add hp0]
        congr 1
        ring
    have hcongr : (∑ p ∈ primeSet N, ((p : ℝ) ^ (-σ)) ^ 2)
        = ∑ p ∈ primeSet N, ((p : ℝ) ^ (-(2 * σ))) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (prime_of_mem_primeSet hp).pos
      rw [sq, ← Real.rpow_add hp0]
      congr 1
      ring
    rw [hcongr]
    have hnn : (0 : ℝ) ≤ ∑ p ∈ primeSet N, ((p : ℝ) ^ (-σ)) ^ 4 :=
      Finset.sum_nonneg fun p _ => by positivity
    linarith
  have hres := measure_unbounded_ge (μ := steinhausMeasure)
    (f := fun N ω => ‖steinhausPrimePoly σ N ω‖)
    (fun N => (measurable_steinhausPrimePoly σ N).norm)
    (fun N ω => norm_nonneg _)
    (fun N => integrable_normSq_steinhausPrimePoly σ N)
    (fun N => integrable_normSq_sq_steinhausPrimePoly σ N)
    (C := 2) (by norm_num) hup (tendsto_integral_normSq_steinhausPrimePoly hσ)
  have hval : (1 : ℝ) / (4 * 2) = 1 / 8 := by norm_num
  rw [hval] at hres
  exact hres

end GaloisForLFunctions.RHTower

end
