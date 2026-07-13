import GaloisForLFunctions.HTGeometry.ToeplitzPolynomialGraph

/-!
# Multiplication by `z` on `L²(μ)`: the shift isometry behind OPUC-norm monotonicity

On the unit circle the coordinate `z` has modulus `1`, so multiplication by `z` preserves the
`L²(μ)` norm.  This shift isometry is the structural input that makes the monic orthogonal
polynomial norms `‖Φₙ‖` monotone decreasing: `z · span{1,…,zⁿ⁻¹} ⊆ span{1,…,zⁿ}` and the map is
norm-preserving, so the least-squares distance can only shrink as the spanning set grows.

* `circleZMul_memLp` — `z·f ∈ L²(μ)` whenever `f ∈ L²(μ)`;
* `circleZMulLp` — multiplication by `z` as a self-map of `L²(μ)`;
* `circleZMulLp_norm` — it is an `L²(μ)` isometry;
* `circleZMulLp_monomial` — it sends the `n`th monomial to the `(n+1)`st.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- `z·f` lies in `L²(μ)` whenever `f` does: multiplication by the unit-modulus coordinate `z`
preserves the pointwise norm. -/
theorem circleZMul_memLp (mu : Measure Circle) [IsFiniteMeasure mu] (f : Lp ℂ 2 mu) :
    MemLp (fun z : Circle => (z : ℂ) * f z) 2 mu := by
  have haesm : AEStronglyMeasurable (fun z : Circle => (z : ℂ) * f z) mu :=
    (by fun_prop : Continuous (fun z : Circle => (z : ℂ))).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  have heq : ∀ᵐ z : Circle ∂mu, ‖(z : ℂ) * f z‖ = ‖f z‖ := by
    filter_upwards with z
    rw [norm_mul, Circle.norm_coe, one_mul]
  exact ⟨haesm, by rw [eLpNorm_congr_norm_ae heq]; exact (Lp.memLp f).2⟩

/-- Multiplication by `z` as a self-map of `L²(μ)`. -/
def circleZMulLp (mu : Measure Circle) [IsFiniteMeasure mu] (f : Lp ℂ 2 mu) :
    Lp ℂ 2 mu :=
  MemLp.toLp (fun z : Circle => (z : ℂ) * f z) (circleZMul_memLp mu f)

/-- **Multiplication by `z` is an `L²(μ)` isometry.**  Since `|z| = 1` on the circle it preserves
the `L²` norm. -/
theorem circleZMulLp_norm (mu : Measure Circle) [IsFiniteMeasure mu] (f : Lp ℂ 2 mu) :
    ‖circleZMulLp mu f‖ = ‖f‖ := by
  rw [circleZMulLp, Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  exact eLpNorm_congr_norm_ae (by
    filter_upwards with z
    rw [norm_mul, Circle.norm_coe, one_mul])

/-- The shift isometry sends the `n`th analytic monomial to the `(n+1)`st: `z · zⁿ = zⁿ⁺¹`. -/
theorem circleZMulLp_monomial (mu : Measure Circle) [IsFiniteMeasure mu] (n : ℕ) :
    circleZMulLp mu (circleMonomialLp mu n) = circleMonomialLp mu (n + 1) := by
  have hae : (fun z : Circle => (z : ℂ) * (circleMonomialLp mu n) z)
      =ᵐ[mu] (fun z : Circle => (z : ℂ) ^ (n + 1)) := by
    filter_upwards [circleMonomialLp_coeFn_ae mu n] with z hz
    rw [hz, pow_succ]; ring
  rw [circleZMulLp, circleMonomialLp]
  exact MemLp.toLp_congr (circleZMul_memLp mu (circleMonomialLp mu n))
    (circleMonomial_memLp mu (n + 1)) hae

end

end GaloisForLFunctions.HTGeometry
