import GaloisForLFunctions.HTGeometry.ToeplitzPolynomialGraph
import GaloisForLFunctions.HTGeometry.GramDeterminantDistance

/-!
# Multiplication by `z` on `L²(μ)`: the shift isometry and OPUC-norm monotonicity

On the unit circle the coordinate `z` has modulus `1`, so multiplication by `z` preserves the
`L²(μ)` norm.  This shift isometry is the structural input that makes the monic orthogonal
polynomial norms `‖Φₙ‖` monotone decreasing: `z · span{1,…,zⁿ⁻¹} ⊆ span{1,…,zⁿ}` and the map is
norm-preserving, so the least-squares distance can only shrink as the spanning set grows.

* `circleZMul_memLp` — `z·f ∈ L²(μ)` whenever `f ∈ L²(μ)`;
* `circleZMulLp` — multiplication by `z` as a self-map of `L²(μ)`;
* `circleZMulLp_norm` — it is an `L²(μ)` isometry;
* `circleZMulLp_monomial` — it sends the `n`th monomial to the `(n+1)`st;
* `circleZMulLpHom` — the same map, bundled `ℂ`-linearly;
* `norm_gramSchmidt_circleMonomial_succ_le` — the monic OPUC norms decrease: `‖Φₙ₊₁‖ ≤ ‖Φₙ‖`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InnerProductSpace
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

/-- Pointwise almost-everywhere value of the shift image. -/
theorem circleZMulLp_coeFn_ae (mu : Measure Circle) [IsFiniteMeasure mu] (f : Lp ℂ 2 mu) :
    ⇑(circleZMulLp mu f) =ᵐ[mu] fun z : Circle => (z : ℂ) * f z :=
  MemLp.coeFn_toLp _

/-- Multiplication by `z` is additive on `L²(μ)`. -/
theorem circleZMulLp_add (mu : Measure Circle) [IsFiniteMeasure mu] (f g : Lp ℂ 2 mu) :
    circleZMulLp mu (f + g) = circleZMulLp mu f + circleZMulLp mu g := by
  apply Lp.ext
  filter_upwards [circleZMulLp_coeFn_ae mu (f + g),
    Lp.coeFn_add (circleZMulLp mu f) (circleZMulLp mu g),
    circleZMulLp_coeFn_ae mu f, circleZMulLp_coeFn_ae mu g,
    Lp.coeFn_add f g] with z h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]

/-- Multiplication by `z` is homogeneous on `L²(μ)`. -/
theorem circleZMulLp_smul (mu : Measure Circle) [IsFiniteMeasure mu] (c : ℂ) (f : Lp ℂ 2 mu) :
    circleZMulLp mu (c • f) = c • circleZMulLp mu f := by
  apply Lp.ext
  filter_upwards [circleZMulLp_coeFn_ae mu (c • f),
    Lp.coeFn_smul c (circleZMulLp mu f),
    circleZMulLp_coeFn_ae mu f, Lp.coeFn_smul c f] with z h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- Multiplication by `z` bundled as a `ℂ`-linear self-map of `L²(μ)`. -/
def circleZMulLpHom (mu : Measure Circle) [IsFiniteMeasure mu] :
    Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun := circleZMulLp mu
  map_add' := circleZMulLp_add mu
  map_smul' c f := by rw [RingHom.id_apply, circleZMulLp_smul]

@[simp] theorem circleZMulLpHom_apply (mu : Measure Circle) [IsFiniteMeasure mu] (f : Lp ℂ 2 mu) :
    circleZMulLpHom mu f = circleZMulLp mu f := rfl

/-- The shift carries the span of the low monomials into the span of one more monomial. -/
theorem circleZMulLp_maps_span (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) :
    Submodule.map (circleZMulLpHom mu)
        (Submodule.span ℂ (circleMonomialLp mu '' Set.Iio N))
      ≤ Submodule.span ℂ (circleMonomialLp mu '' Set.Iio (N + 1)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, circleZMulLpHom_apply, circleZMulLp_monomial]
  exact Submodule.subset_span ⟨i + 1, by simp only [Set.mem_Iio] at hi ⊢; omega, rfl⟩

/-- **Monic OPUC norms are monotone decreasing.**  `‖Φₙ₊₁‖ ≤ ‖Φₙ‖`: the shift isometry `z·` carries
the degree-`n` least-squares approximation into the degree-`(n+1)` competition without changing its
norm, so the Gram–Schmidt distance from `zⁿ⁺¹` to the span of the lower monomials can only shrink. -/
theorem norm_gramSchmidt_circleMonomial_succ_le
    (mu : Measure Circle) [IsFiniteMeasure mu] (N : ℕ) :
    ‖gramSchmidt ℂ (circleMonomialLp mu) (N + 1)‖
      ≤ ‖gramSchmidt ℂ (circleMonomialLp mu) N‖ := by
  set cm := circleMonomialLp mu with hcm
  set gs := gramSchmidt ℂ cm with hgs
  set w := circleZMulLp mu (cm N - gs N) with hwdef
  have h1 : cm N - gs N ∈ Submodule.span ℂ (cm '' Set.Iio N) := by
    rw [← span_gramSchmidt_Iio ℂ cm N, ← hgs]
    have hdef := gramSchmidt_def'' ℂ cm N
    rw [← hgs] at hdef
    rw [hdef, add_sub_cancel_left]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  have h2 : w ∈ Submodule.span ℂ (gs '' Set.Iio (N + 1)) := by
    rw [hgs, span_gramSchmidt_Iio ℂ cm (N + 1)]
    exact circleZMulLp_maps_span mu N (Submodule.mem_map_of_mem h1)
  have h3 : cm (N + 1) - w = circleZMulLp mu (gs N) := by
    rw [hwdef, hcm, ← circleZMulLp_monomial mu N,
      show circleZMulLp mu (circleMonomialLp mu N)
        = circleZMulLpHom mu (circleMonomialLp mu N) from rfl,
      show circleZMulLp mu (circleMonomialLp mu N - gs N)
        = circleZMulLpHom mu (circleMonomialLp mu N - gs N) from rfl,
      show circleZMulLp mu (gs N) = circleZMulLpHom mu (gs N) from rfl,
      ← map_sub]
    congr 1
    abel
  calc ‖gs (N + 1)‖ ≤ ‖cm (N + 1) - w‖ := norm_gramSchmidt_le_of_mem_span cm (N + 1) h2
    _ = ‖circleZMulLp mu (gs N)‖ := by rw [h3]
    _ = ‖gs N‖ := circleZMulLp_norm mu (gs N)

end

end GaloisForLFunctions.HTGeometry
