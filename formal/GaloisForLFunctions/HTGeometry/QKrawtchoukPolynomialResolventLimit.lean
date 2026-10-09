import GaloisForLFunctions.HTGeometry.QKrawtchoukPinnedQuadrature
import GaloisForLFunctions.HTGeometry.CauchyKernelWeakConvergence

/-!
# Polynomial resolvent integrals for the selected edge measure

The scalar-to-operator step of arXiv:2609.24149, Theorem 6.1, involves
polynomial-weighted Cauchy integrals. For the concrete pinned quadratures,
these converge for every complex polynomial and every upper-half-plane pole.
Polynomial division reduces the assertion to moment convergence and weak
convergence against the bounded Cauchy kernel. The monomial recurrence below
implements that division and also proves all required integrability.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace HTGeometry

private theorem power_cauchy_succ {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) (y : ℝ) :
    (y : ℂ) ^ (k + 1) * ((y : ℂ) - z)⁻¹ =
      (y : ℂ) ^ k + z * ((y : ℂ) ^ k * ((y : ℂ) - z)⁻¹) := by
  have hne : (y : ℂ) - z ≠ 0 := by
    intro he
    apply hz
    have hzy : z = (y : ℂ) := by linear_combination -he
    rw [hzy]
    simp
  field_simp
  ring

private theorem integrable_power_cauchy (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : ∀ k : ℕ, Integrable (fun y : ℝ => (y : ℂ) ^ k) μ)
    {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) :
    Integrable (fun y : ℝ => (y : ℂ) ^ k * ((y : ℂ) - z)⁻¹) μ := by
  induction k with
  | zero => simpa only [pow_zero, one_mul] using integrable_cauchy_kernel μ hz
  | succ k ih =>
      exact ((hm k).add (ih.const_mul z)).congr
        (ae_of_all μ fun y => (power_cauchy_succ hz k y).symm)

private theorem integral_power_cauchy_succ (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : ∀ k : ℕ, Integrable (fun y : ℝ => (y : ℂ) ^ k) μ)
    {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) :
    (∫ y, (y : ℂ) ^ (k + 1) * ((y : ℂ) - z)⁻¹ ∂μ) =
      (∫ y, (y : ℂ) ^ k ∂μ) + z * (∫ y, (y : ℂ) ^ k * ((y : ℂ) - z)⁻¹ ∂μ) := by
  simp_rw [power_cauchy_succ hz k]
  rw [integral_add (hm k) ((integrable_power_cauchy μ hm hz k).const_mul z),
    integral_const_mul]

private theorem tendsto_power_cauchy {μs : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hweak : Tendsto μs atTop (𝓝 μ))
    (hs : ∀ n k : ℕ, Integrable (fun y : ℝ => (y : ℂ) ^ k) (μs n : Measure ℝ))
    (hm : ∀ k : ℕ, Integrable (fun y : ℝ => (y : ℂ) ^ k) (μ : Measure ℝ))
    (hlim : ∀ k : ℕ, Tendsto (fun n => ∫ y, (y : ℂ) ^ k ∂(μs n : Measure ℝ)) atTop
      (𝓝 (∫ y, (y : ℂ) ^ k ∂(μ : Measure ℝ))))
    {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) :
    Tendsto (fun n => ∫ y, (y : ℂ) ^ k * ((y : ℂ) - z)⁻¹ ∂(μs n : Measure ℝ)) atTop
      (𝓝 (∫ y, (y : ℂ) ^ k * ((y : ℂ) - z)⁻¹ ∂(μ : Measure ℝ))) := by
  induction k with
  | zero =>
      simpa only [pow_zero, one_mul] using tendsto_cauchyTransform_of_tendsto hweak hz
  | succ k ih =>
      have heq n := integral_power_cauchy_succ (μs n : Measure ℝ) (hs n) hz k
      rw [integral_power_cauchy_succ (μ : Measure ℝ) hm hz k]
      simpa only [heq] using (hlim k).add (ih.const_mul z)

private theorem integral_polynomial_cauchy (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hm : ∀ k : ℕ, Integrable (fun y : ℝ => (y : ℂ) ^ k) μ)
    {z : ℂ} (hz : z.im ≠ 0) (P : Polynomial ℂ) :
    (∫ y, P.eval (y : ℂ) * ((y : ℂ) - z)⁻¹ ∂μ) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * (∫ y, (y : ℂ) ^ k * ((y : ℂ) - z)⁻¹ ∂μ) := by
  have heq (y : ℝ) : P.eval (y : ℂ) * ((y : ℂ) - z)⁻¹ =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * ((y : ℂ) ^ k * ((y : ℂ) - z)⁻¹) := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  simp_rw [heq]
  rw [integral_finsetSum _ (fun k _ => (integrable_power_cauchy μ hm hz k).const_mul _)]
  exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _

/-- Every polynomial resolvent matrix element converges for the explicitly
constructed finite quadratures. The pole parametrization discharges the
nonreal condition for the entire upper half-plane. -/
theorem inverseQHermitePinnedQuadrature_polynomialCauchy_tendsto
    (t u x r a b : ℝ) (P : Polynomial ℂ) :
    Tendsto (fun n : ℕ =>
      ∫ y, P.eval (y : ℂ) * ((y : ℂ) - Complex.mk a (Real.exp b))⁻¹
        ∂(inverseQHermitePinnedQuadrature t u (x + r / ((n : ℝ) + 1)) n : Measure ℝ))
      atTop (𝓝 (∫ y, P.eval (y : ℂ) * ((y : ℂ) - Complex.mk a (Real.exp b))⁻¹
        ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ))) := by
  let μs := fun n : ℕ => inverseQHermitePinnedQuadrature t u (x + r / ((n : ℝ) + 1)) n
  let μ := inverseQHermiteAtomMeasure t u x
  let z := Complex.mk a (Real.exp b)
  have hz : z.im ≠ 0 := (Real.exp_pos b).ne'
  have hs (n k : ℕ) : Integrable (fun y : ℝ => (y : ℂ) ^ k) (μs n : Measure ℝ) := by
    have hr : Integrable (fun y : ℝ => y ^ k) (μs n : Measure ℝ) :=
      integrable_quasiProb (inverseQHermiteMoment_positive t u) _ _ _
    exact (hr.ofReal (𝕜 := ℂ)).congr (ae_of_all _ fun y => Complex.ofReal_pow y k)
  have hm (k : ℕ) : Integrable (fun y : ℝ => (y : ℂ) ^ k) (μ : Measure ℝ) := by
    exact ((inverseQHermiteAtomMeasure_moments t u x k).1.ofReal (𝕜 := ℂ)).congr
      (ae_of_all _ fun y => Complex.ofReal_pow y k)
  have hlim (k : ℕ) :
      Tendsto (fun n => ∫ y, (y : ℂ) ^ k ∂(μs n : Measure ℝ)) atTop
        (𝓝 (∫ y, (y : ℂ) ^ k ∂(μ : Measure ℝ))) := by
    have heq : (fun n => ∫ y, y ^ k ∂(μs n : Measure ℝ)) =ᶠ[atTop]
        fun _ => inverseQHermiteMoment t u k := by
      filter_upwards [inverseQHermitePinnedQuadrature_moments t u
        (fun n : ℕ => x + r / ((n : ℝ) + 1)) k] with n hn
      exact hn.2
    have ht : Tendsto (fun n => ∫ y, y ^ k ∂(μs n : Measure ℝ)) atTop
        (𝓝 (inverseQHermiteMoment t u k)) := tendsto_const_nhds.congr' heq.symm
    have hc := (Complex.continuous_ofReal.tendsto _).comp ht
    rw [← (inverseQHermiteAtomMeasure_moments t u x k).2] at hc
    change Tendsto (fun n => ((∫ y, y ^ k ∂(μs n : Measure ℝ) : ℝ) : ℂ)) atTop
      (𝓝 ((∫ y, y ^ k ∂(μ : Measure ℝ) : ℝ) : ℂ)) at hc
    simpa only [← Complex.ofReal_pow, integral_complex_ofReal] using hc
  have hweak : Tendsto μs atTop (𝓝 μ) := inverseQHermitePinnedQuadrature_tendsto t u x r
  have heq n := integral_polynomial_cauchy (μs n : Measure ℝ) (hs n) hz P
  change Tendsto (fun n => ∫ y, P.eval (y : ℂ) * ((y : ℂ) - z)⁻¹ ∂(μs n : Measure ℝ))
    atTop (𝓝 (∫ y, P.eval (y : ℂ) * ((y : ℂ) - z)⁻¹ ∂(μ : Measure ℝ)))
  rw [integral_polynomial_cauchy (μ : Measure ℝ) hm hz P]
  simp only [heq]
  exact tendsto_finsetSum _ fun k _ => (tendsto_power_cauchy hweak hs hm hlim hz k).const_mul _

end HTGeometry
