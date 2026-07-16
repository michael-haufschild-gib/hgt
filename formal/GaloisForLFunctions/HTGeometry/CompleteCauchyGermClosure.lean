import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection

/-!
# Complete Cauchy germs determine probability laws

Finite regular Cauchy jets and complete germs have sharply different selection behavior.  This
module supplies the unconditional closure half: equality of every derivative of the resolvent
transform at either canonical regular node `i` or `-i` forces equality of the underlying real
probability measures.

The proof is intrinsic to the existing finite frame.  At every finite depth, Cauchy-jet equality
is equivalent to equality of the corresponding Cayley moments.  Passing through all depths gives
the complete moment sequence, and the Cayley moment uniqueness theorem then identifies the law.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory

noncomputable section

/-- **Complete upper Cauchy-germ closure.**  A real probability measure is uniquely determined by
the complete Taylor jet of its resolvent transform at `i`. -/
theorem measure_eq_of_completeCauchyJet_pos_I_eq
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hjet : ∀ n : ℕ,
      iteratedDeriv n (resolventTransform mu) I =
        iteratedDeriv n (resolventTransform nu) I) :
    mu = nu := by
  apply measure_eq_of_forall_cayleyMoment_eq
  intro k
  have hprefix := (cayleyMoment_prefix_iff_cauchyJet_pos_I_prefix mu nu (k + 1)).2
    (fun n _hn => hjet n)
  exact hprefix k (by omega)

/-- **Complete lower Cauchy-germ closure.**  The same selection theorem at the conventional
lower regular node `-i`. -/
theorem measure_eq_of_completeCauchyJet_neg_I_eq
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hjet : ∀ n : ℕ,
      iteratedDeriv n (resolventTransform mu) (-I) =
        iteratedDeriv n (resolventTransform nu) (-I)) :
    mu = nu := by
  apply measure_eq_of_forall_cayleyMoment_eq
  intro k
  have hprefix := (cayleyMoment_prefix_iff_cauchyJet_prefix mu nu (k + 1)).2
    (fun n _hn => hjet n)
  exact hprefix k (by omega)

/-- Equality of all finite upper Cauchy-jet prefixes is already complete-germ equality, hence
selects one probability measure.  This is the exact inverse-limit formulation of the closure
law. -/
theorem measure_eq_of_allFiniteCauchyJet_pos_I_prefix_eq
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hprefix : ∀ N : ℕ, ∀ n < N,
      iteratedDeriv n (resolventTransform mu) I =
        iteratedDeriv n (resolventTransform nu) I) :
    mu = nu := by
  apply measure_eq_of_completeCauchyJet_pos_I_eq
  intro n
  exact hprefix (n + 1) n (by omega)

/-! ## Transport from an arbitrary regular node -/

/-- Real affine normalization carrying an arbitrary nonreal node to `i` in the resolvent
coordinate. -/
def cauchyNodeNormalize (a : ℂ) (x : ℝ) : ℝ :=
  (x - a.re) / a.im

theorem continuous_cauchyNodeNormalize (a : ℂ) :
    Continuous (cauchyNodeNormalize a) := by
  unfold cauchyNodeNormalize
  fun_prop

theorem injective_cauchyNodeNormalize {a : ℂ} (ha : a.im ≠ 0) :
    Function.Injective (cauchyNodeNormalize a) := by
  intro x y hxy
  dsimp [cauchyNodeNormalize] at hxy
  apply (div_left_inj' ha).mp at hxy
  linarith

theorem measurableEmbedding_cauchyNodeNormalize {a : ℂ} (ha : a.im ≠ 0) :
    MeasurableEmbedding (cauchyNodeNormalize a) :=
  (continuous_cauchyNodeNormalize a).measurableEmbedding
    (injective_cauchyNodeNormalize ha)

/-- Affine normalization intertwines the resolvent at `a` with the canonical resolvent at `i`. -/
theorem resolvent_I_cauchyNodeNormalize {a : ℂ} (ha : a.im ≠ 0) (x : ℝ) :
    resolvent I (cauchyNodeNormalize a x) =
      (a.im : ℂ) * resolvent a x := by
  have hden :
      (algebraMap ℝ ℂ) (cauchyNodeNormalize a x) - I =
        (a.im : ℂ)⁻¹ * ((algebraMap ℝ ℂ) x - a) := by
    apply Complex.ext
    · simp [cauchyNodeNormalize, div_eq_mul_inv, ha]
      ring
    · simp [cauchyNodeNormalize, div_eq_mul_inv, ha]
  simp only [resolvent, hden]
  rw [Ring.inverse_eq_inv, Ring.inverse_eq_inv, mul_inv_rev]
  simp only [inv_inv]
  ring

/-- Resolvent-power integrals transform diagonally under the affine normalization. -/
theorem resolventPowerTransform_map_cauchyNodeNormalize
    (mu : Measure ℝ) {a : ℂ} (ha : a.im ≠ 0) (r : ℕ) :
    resolventPowerTransform (Measure.map (cauchyNodeNormalize a) mu) r I =
      (a.im : ℂ) ^ r * resolventPowerTransform mu r a := by
  unfold resolventPowerTransform
  have hstrong : AEStronglyMeasurable (fun x : ℝ => resolvent I x ^ r)
      (Measure.map (cauchyNodeNormalize a) mu) := by
    fun_prop
  rw [integral_map
    (measurableEmbedding_cauchyNodeNormalize ha).measurable.aemeasurable hstrong]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [resolvent_I_cauchyNodeNormalize ha, mul_pow]

/-- A nonreal point lies outside the complex image of every real measure support. -/
theorem nonreal_notMem_real_support_image
    (mu : Measure ℝ) {a : ℂ} (ha : a.im ≠ 0) :
    a ∉ algebraMap ℝ ℂ '' mu.support := by
  rintro ⟨x, _hx, hxa⟩
  have him := congrArg Complex.im hxa
  simp at him
  exact ha him.symm

/-- Every normalized Cauchy derivative is the corresponding original derivative times the
expected nonzero affine scale. -/
theorem iteratedDeriv_resolventTransform_map_cauchyNodeNormalize
    (mu : Measure ℝ) [IsFiniteMeasure mu] {a : ℂ} (ha : a.im ≠ 0) (n : ℕ) :
    iteratedDeriv n
        (resolventTransform (Measure.map (cauchyNodeNormalize a) mu)) I =
      (a.im : ℂ) ^ (n + 1) * iteratedDeriv n (resolventTransform mu) a := by
  rw [iteratedDeriv_resolventTransform n I
      (nonreal_notMem_real_support_image
        (Measure.map (cauchyNodeNormalize a) mu) (by simp)),
    iteratedDeriv_resolventTransform n a
      (nonreal_notMem_real_support_image mu ha)]
  unfold cauchyJetFunction
  rw [resolventPowerTransform_map_cauchyNodeNormalize mu ha]
  ring

/-- **Complete Cauchy-germ closure at every regular node.**  Equality of all derivatives of the
resolvent transform at one arbitrary nonreal point determines the probability measure. -/
theorem measure_eq_of_completeCauchyJet_eq
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {a : ℂ} (ha : a.im ≠ 0)
    (hjet : ∀ n : ℕ,
      iteratedDeriv n (resolventTransform mu) a =
        iteratedDeriv n (resolventTransform nu) a) :
    mu = nu := by
  letI : IsProbabilityMeasure (Measure.map (cauchyNodeNormalize a) mu) :=
    Measure.isProbabilityMeasure_map
      (measurableEmbedding_cauchyNodeNormalize ha).measurable.aemeasurable
  letI : IsProbabilityMeasure (Measure.map (cauchyNodeNormalize a) nu) :=
    Measure.isProbabilityMeasure_map
      (measurableEmbedding_cauchyNodeNormalize ha).measurable.aemeasurable
  apply (measurableEmbedding_cauchyNodeNormalize ha).map_injective
  apply measure_eq_of_completeCauchyJet_pos_I_eq
  intro n
  rw [iteratedDeriv_resolventTransform_map_cauchyNodeNormalize mu ha,
    iteratedDeriv_resolventTransform_map_cauchyNodeNormalize nu ha,
    hjet n]

end

end GaloisForLFunctions.HTGeometry
