import GaloisForLFunctions.BiScaleUncertainty.Observation.BoundedCoordinateSignCone

/-!
# Cofinite coordinate powers remain dense

Orthogonality to every sufficiently high power becomes a moment problem after
multiplication by one coordinate power. A nonzero almost-everywhere coordinate
therefore retains density after any finite deletion of exponents.
-/

open MeasureTheory Set
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
variable {μ : Measure ℝ} [IsFiniteMeasure μ] {φ : ℝ → ℝ}
    (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)

/-- Coordinate polynomials whose first prescribed number of coefficients vanish. -/
def coordinateTailSpan (N : ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ (range (fun n => coordinateMonomial hφ hb (n + N)))

/-- Removing finitely many powers preserves density when the coordinate is nonzero almost everywhere. -/
theorem coordinateTailSpan_orthogonal (hzero : ∀ᵐ x ∂μ, φ x ≠ 0) (N : ℕ) :
    (coordinateTailSpan hφ hb N)ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have hint : Integrable (v : ℝ → ℝ) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp v).mono_exponent (by norm_num))
  have hweighted : Integrable (fun x => φ x ^ N * v x) μ := by
    apply hint.bdd_mul (c := 1) (hφ.measurable.pow_const N).aestronglyMeasurable
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs, abs_pow] using
      (pow_le_one₀ (n := N) (abs_nonneg (φ x)) hx)
  have hmom (n : ℕ) : (∫ x, φ x ^ n * (φ x ^ N * v x) ∂μ) = 0 := by
    have h := (Submodule.mem_orthogonal _ v).mp hv (coordinateMonomial hφ hb (n + N))
      (Submodule.subset_span ⟨n, rfl⟩)
    rw [L2.inner_def] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [coordinateMonomial_ae hφ hb (n + N)] with x hx
    rw [hx]
    simp [RCLike.inner_apply, pow_add, mul_comm, mul_left_comm, mul_assoc]
  have hz := _root_.HTGeometry.ae_eq_zero_of_boundedCoordinate_moments hφ hb hweighted hmom
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hz, hzero] with x hx hφx
  exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero N hφx)

/-- Every prescribed monomial factor retains density in the physical square-integrable space. -/
theorem coordinateTailSpan_dense (hzero : ∀ᵐ x ∂μ, φ x ≠ 0) (N : ℕ) :
    Dense (coordinateTailSpan hφ hb N : Set (Lp ℝ 2 μ)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr (coordinateTailSpan_orthogonal hφ hb hzero N))

/-- Each vector in the tail span has an actual polynomial representative divisible by the prescribed power. -/
theorem exists_polynomial_coordinate_tail_of_mem (N : ℕ) {v : Lp ℝ 2 μ}
    (hv : v ∈ coordinateTailSpan hφ hb N) :
    ∃ P : Polynomial ℝ, v =ᵐ[μ] fun x => φ x ^ N * P.eval (φ x) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨n, rfl⟩ := hv
    refine ⟨Polynomial.X ^ n, ?_⟩
    filter_upwards [coordinateMonomial_ae hφ hb (n + N)] with x hx
    rw [hx, Polynomial.eval_X_pow, pow_add, mul_comm]
  | zero =>
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | add u v _ _ hu hv =>
    obtain ⟨P, hP⟩ := hu
    obtain ⟨Q, hQ⟩ := hv
    refine ⟨P + Q, ?_⟩
    filter_upwards [Lp.coeFn_add u v, hP, hQ] with x huv hx hy
    rw [huv]
    change u x + v x = _
    rw [hx, hy, Polynomial.eval_add]
    ring
  | smul c v _ hv =>
    obtain ⟨P, hP⟩ := hv
    refine ⟨c • P, ?_⟩
    filter_upwards [Lp.coeFn_smul c v, hP] with x hcv hx
    rw [hcv]
    change c * v x = _
    rw [hx, Polynomial.eval_smul]
    change c * (φ x ^ N * P.eval (φ x)) = φ x ^ N * (c * P.eval (φ x))
    ring

/-- Arbitrary cofinite exponent sets retain the same completed polynomial test space. -/
theorem coordinate_exponent_span_dense (hzero : ∀ᵐ x ∂μ, φ x ≠ 0) (E : Set ℕ)
    (N : ℕ) (hE : ∀ n, N ≤ n → n ∈ E) :
    Dense (↑(Submodule.span ℝ (coordinateMonomial hφ hb '' E)) : Set (Lp ℝ 2 μ)) := by
  apply (coordinateTailSpan_dense hφ hb hzero N).mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact Submodule.subset_span ⟨n + N, hE _ (by omega), rfl⟩

#print axioms coordinateTailSpan_dense
#print axioms coordinate_exponent_span_dense
end GaloisForLFunctions.BiScaleUncertainty.Observation
