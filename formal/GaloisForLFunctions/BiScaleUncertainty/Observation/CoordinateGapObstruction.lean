import GaloisForLFunctions.BiScaleUncertainty.Observation.CoordinateTailDensity
import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ResidueColumns

/-!
# The exact obstruction to cofinite coordinate density

Lost modes are supported at coordinate zero. Retaining the constant removes this obstruction for an injective coordinate.
-/

open MeasureTheory Set
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
variable {μ : Measure ℝ} [IsFiniteMeasure μ] {φ : ℝ → ℝ}
    (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)

/-- Square-integrable coordinate monomials with a prescribed exponent set. -/
def coordinateExponentSpan (E : Set ℕ) : Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ (coordinateMonomial hφ hb '' E)

private theorem exponent_inner_integral (n : ℕ) (v : Lp ℝ 2 μ) :
    inner ℝ (coordinateMonomial hφ hb n) v = ∫ x, φ x ^ n * v x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coordinateMonomial_ae hφ hb n] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- The only modes lost by cofinite exponents are supported at coordinate zero; retaining the constant also kills their mean. -/
theorem coordinateExponentSpan_orthogonal_iff (E : Set ℕ) (N : ℕ)
    (hE : ∀ n, N ≤ n → n ∈ E) (v : Lp ℝ 2 μ) :
    v ∈ (coordinateExponentSpan hφ hb E)ᗮ ↔
      (∀ᵐ x ∂μ, φ x ≠ 0 → v x = 0) ∧ (0 ∈ E → ∫ x, v x ∂μ = 0) := by
  constructor
  · intro hv
    have hmom (n : ℕ) (hn : n ∈ E) : (∫ x, φ x ^ n * v x ∂μ) = 0 := by
      rw [← exponent_inner_integral hφ hb]
      exact (Submodule.mem_orthogonal _ v).mp hv _ (Submodule.subset_span ⟨n, hn, rfl⟩)
    have hint : Integrable (v : ℝ → ℝ) μ :=
      memLp_one_iff_integrable.mp ((Lp.memLp v).mono_exponent (by norm_num))
    -- Tail moments are full moments of the density multiplied by one coordinate power.
    have hweighted : Integrable (fun x => φ x ^ N * v x) μ := by
      apply hint.bdd_mul (c := 1) (hφ.measurable.pow_const N).aestronglyMeasurable
      filter_upwards [hb] with x hx
      simpa only [Real.norm_eq_abs, abs_pow] using
        (pow_le_one₀ (n := N) (abs_nonneg (φ x)) hx)
    have hz := _root_.HTGeometry.ae_eq_zero_of_boundedCoordinate_moments hφ hb hweighted
      (fun n => by
        rw [← hmom (n + N) (hE _ (by omega))]
        apply integral_congr_ae
        filter_upwards [] with x
        rw [pow_add, mul_assoc])
    constructor
    · filter_upwards [hz] with x hx hφx
      exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero N hφx)
    · intro h0
      simpa only [pow_zero, one_mul] using hmom 0 h0
  · rintro ⟨hsupp, hmean⟩
    apply (Submodule.mem_orthogonal _ v).mpr
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, hn, rfl⟩ := hu
      rw [exponent_inner_integral]
      by_cases hn0 : n = 0
      · subst n
        simpa only [pow_zero, one_mul] using hmean hn
      · calc
          _ = ∫ x, (0 : ℝ) ∂μ := by
            apply integral_congr_ae
            filter_upwards [hsupp] with x hx
            by_cases hφx : φ x = 0
            · rw [hφx, zero_pow hn0, zero_mul]
            · rw [hx hφx, mul_zero]
          _ = 0 := integral_zero _ _
    | zero => simp
    | add u w _ _ hu hw => rw [_root_.inner_add_left, hu, hw, add_zero]
    | smul c u _ hu => rw [real_inner_smul_left, hu, mul_zero]

/-- Keeping the constant and all sufficiently high powers is dense even when coordinate zero has positive mass. -/
theorem coordinateExponentSpan_dense_of_zero_mem (E : Set ℕ) (N : ℕ)
    (hE : ∀ n, N ≤ n → n ∈ E) (h0 : 0 ∈ E) :
    Dense (coordinateExponentSpan hφ hb E : Set (Lp ℝ 2 μ)) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  obtain ⟨hsupp, hmean⟩ := (coordinateExponentSpan_orthogonal_iff hφ hb E N hE v).mp hv
  have hint : Integrable (v : ℝ → ℝ) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp v).mono_exponent (by norm_num))
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply _root_.HTGeometry.ae_eq_zero_of_boundedCoordinate_moments hφ hb hint
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [pow_zero, one_mul] using hmean h0
  · calc
      _ = ∫ x, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hsupp] with x hx
        by_cases hφx : φ x = 0
        · rw [hφx, zero_pow hn, zero_mul]
        · rw [hx hφx, mul_zero]
      _ = 0 := integral_zero _ _

/-- Every residue-column test space containing constants is dense, without an assumption on mass at coordinate zero. -/
theorem columnCoordinateSpan_dense (m : ℕ) (k : ℕ → ℕ) (h0 : k 0 = 0) :
    Dense (coordinateExponentSpan hφ hb (ArithmeticEffectivityTheory.ResidueColumns.carrier m k) :
      Set (Lp ℝ 2 μ)) := by
  apply coordinateExponentSpan_dense_of_zero_mem hφ hb _
    (ArithmeticEffectivityTheory.ResidueColumns.tailBound m k)
    (fun n hn => ArithmeticEffectivityTheory.ResidueColumns.mem_of_tailBound_le m k hn)
  change k (0 % (m + 1)) ≤ 0 / (m + 1)
  simp [h0]

#print axioms coordinateExponentSpan_orthogonal_iff
#print axioms coordinateExponentSpan_dense_of_zero_mem
#print axioms columnCoordinateSpan_dense
end GaloisForLFunctions.BiScaleUncertainty.Observation
