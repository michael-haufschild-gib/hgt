import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeSpectralEnergy

/-! # Every positive two-atom source is an exact rescaled actual Gibbs source -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section
open MeasureTheory

/-- The full nonnegative cone on the two thermal collision nodes. -/
def egbFixedChargeAGibbsConeSource (x y : NNReal) : Measure HausdorffSourceSpace :=
  hausdorffAtomSource x egbFixedChargeAGibbsCollisionSlowNode +
    hausdorffAtomSource y egbFixedChargeAGibbsCollisionFastNode

instance (x y : NNReal) : IsFiniteMeasure (egbFixedChargeAGibbsConeSource x y) := by
  unfold egbFixedChargeAGibbsConeSource
  infer_instance

/-- Every source moment records its two independent nonnegative masses. -/
theorem egbFixedChargeAGibbsConeSource_moment (x y : NNReal) (l : ℕ) :
    hausdorffMoment (egbFixedChargeAGibbsConeSource x y) l =
      (x : ℝ) * (4 / 9 : ℝ) ^ l + (y : ℝ) * (1 / 36 : ℝ) ^ l := by
  unfold egbFixedChargeAGibbsConeSource
  have hx := integrable_hausdorffDifferenceIntegrand
    (hausdorffAtomSource x egbFixedChargeAGibbsCollisionSlowNode) 0 l
  have hy := integrable_hausdorffDifferenceIntegrand
    (hausdorffAtomSource y egbFixedChargeAGibbsCollisionFastNode) 0 l
  change (∫ z, (z : ℝ) ^ l ∂(hausdorffAtomSource x egbFixedChargeAGibbsCollisionSlowNode +
    hausdorffAtomSource y egbFixedChargeAGibbsCollisionFastNode)) = _
  rw [integral_add_measure (by simpa using hx) (by simpa using hy)]
  change hausdorffMoment (hausdorffAtomSource x egbFixedChargeAGibbsCollisionSlowNode) l +
    hausdorffMoment (hausdorffAtomSource y egbFixedChargeAGibbsCollisionFastNode) l = _
  rw [hausdorffMoment_atom, hausdorffMoment_atom]
  rfl

/-- Source equality is exactly equality of both atom masses, proved by the first two moments. -/
theorem egbFixedChargeAGibbsConeSource_eq_iff (x y u v : NNReal) :
    egbFixedChargeAGibbsConeSource x y = egbFixedChargeAGibbsConeSource u v ↔ x = u ∧ y = v := by
  constructor
  · intro h
    have h0 := congrArg (fun μ : Measure HausdorffSourceSpace => hausdorffMoment μ 0) h
    have h1 := congrArg (fun μ : Measure HausdorffSourceSpace => hausdorffMoment μ 1) h
    rw [egbFixedChargeAGibbsConeSource_moment, egbFixedChargeAGibbsConeSource_moment] at h0 h1
    norm_num at h0 h1
    have hx : (x : ℝ) = (u : ℝ) := by linarith
    have hy : (y : ℝ) = (v : ℝ) := by linarith
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The cone vertex is the only zero source; neither nonzero pure ray disappears. -/
theorem egbFixedChargeAGibbsConeSource_zero_iff (x y : NNReal) :
    egbFixedChargeAGibbsConeSource x y = 0 ↔ x = 0 ∧ y = 0 := by
  have hz : egbFixedChargeAGibbsConeSource 0 0 = 0 := by
    simp [egbFixedChargeAGibbsConeSource, hausdorffAtomSource]
  rw [← hz, egbFixedChargeAGibbsConeSource_eq_iff]

/-- Mass scaling is literally scaling of the positive measure. -/
theorem egbFixedChargeAGibbsConeSource_scale (c x y : NNReal) :
    egbFixedChargeAGibbsConeSource (c * x) (c * y) = c • egbFixedChargeAGibbsConeSource x y := by
  simp only [egbFixedChargeAGibbsConeSource, hausdorffAtomSource, smul_add, smul_smul]

/-- Actual full-support Gibbs sources realize the whole prescribed cone up to one strictly positive scalar. -/
theorem egbFixedChargeAGibbsCone_source_factorization (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsConeScale n k m x y • egbFixedChargeAGibbsConeSource x y := by
  rw [egbFixedChargeAGibbsCollisionHausdorffSource, egbFixedChargeAGibbsCone_slow_mass,
    egbFixedChargeAGibbsCone_fast_mass]
  exact egbFixedChargeAGibbsConeSource_scale _ x y

/-- Positive normalization recovers every cone point, including both pure rays and zero. -/
theorem egbFixedChargeAGibbsCone_rescaled_source_eq (n k m : ℕ) (x y : NNReal) :
    (egbFixedChargeAGibbsConeScale n k m x y)⁻¹ •
      egbFixedChargeAGibbsCollisionHausdorffSource n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
        egbFixedChargeAGibbsConeSource x y := by
  have hc : egbFixedChargeAGibbsConeScale n k m x y ≠ 0 := by
    intro h
    have hp := egbFixedChargeAGibbsConeScale_pos n k m x y
    rw [h] at hp
    norm_num at hp
  rw [egbFixedChargeAGibbsCone_source_factorization, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Every prescribed positive source ray has a genuine full-support Gibbs realization on every grid and offset. -/
theorem egbFixedChargeAGibbsCone_source_realizable (n m : ℕ) (x y : NNReal) :
    ∃ E : Fin (2 ^ (n + 3)) → ℝ, ∃ c : NNReal,
      0 < (c : ℝ) ∧ egbFixedChargeAGibbsCollisionHausdorffSource n m 1 E =
        c • egbFixedChargeAGibbsConeSource x y ∧ ∀ i, 0 < _root_.HTGeometry.finiteGibbsStateWeight 1 E i := by
  exact ⟨egbFixedChargeAGibbsConeEnergy n 0 m x y, egbFixedChargeAGibbsConeScale n 0 m x y,
    egbFixedChargeAGibbsConeScale_pos n 0 m x y, egbFixedChargeAGibbsCone_source_factorization n 0 m x y,
    egbFixedChargeAGibbsCone_probability_pos n 0 m x y⟩

end
end GaloisForLFunctions.HTGeometry
