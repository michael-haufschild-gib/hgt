import GaloisForLFunctions.HTGeometry.ConfocalEnvelopeHull
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission

/-!
# Lorentz admissibility margins for conservative states

Fu--Liu, arXiv:2608.29229v1, Lemma 4.1 uses the concave margin
`energy - norm(momentum)` to prove invariant-cone properties. The argument is
valid in any real normed space. In one spatial dimension it is exactly the
corpus's confocal Lorentz cone. Positive exponential margins construct strict
states directly and remain controlled under finite probability mixtures.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Metric-independent energy reserve above the null boundary. -/
def lorentzAdmissibilityMargin (energy : ℝ) (momentum : E) : ℝ := energy - ‖momentum‖

/-- Closed relativistic admissibility cone. -/
def closedLorentzAdmissibility : Set (ℝ × E) := {u | ‖u.2‖ ≤ u.1}

/-- Strict relativistic admissibility cone. -/
def strictLorentzAdmissibility : Set (ℝ × E) := {u | ‖u.2‖ < u.1}

omit [NormedSpace ℝ E] in
/-- The reserve is superadditive: mixing cannot create a cone deficit. -/
theorem lorentzAdmissibilityMargin_add (a b : ℝ) (u v : E) :
    lorentzAdmissibilityMargin a u + lorentzAdmissibilityMargin b v ≤
      lorentzAdmissibilityMargin (a + b) (u + v) := by
  unfold lorentzAdmissibilityMargin
  linarith [norm_add_le u v]

/-- Positive densitization scales the reserve exactly. -/
theorem lorentzAdmissibilityMargin_smul (c : ℝ≥0) (a : ℝ) (u : E) :
    lorentzAdmissibilityMargin ((c : ℝ) * a) ((c : ℝ) • u) =
      (c : ℝ) * lorentzAdmissibilityMargin a u := by
  simp only [lorentzAdmissibilityMargin, norm_smul, Real.norm_eq_abs,
    ]
  rw [abs_of_nonneg (show 0 ≤ (c : ℝ) from c.property)]
  ring

omit [NormedSpace ℝ E] in
/-- Every state receives a strict reserve by adjoining any positive exponential energy. -/
theorem lorentzAdmissibilityMargin_exp (u : E) (r : ℝ) :
    lorentzAdmissibilityMargin (‖u‖ + Real.exp r) u = Real.exp r := by
  simp only [lorentzAdmissibilityMargin, add_sub_cancel_left]

omit [NormedSpace ℝ E] in
/-- This produces a strict admissible state for every vector and real parameter. -/
theorem norm_add_exp_mem_strictLorentzAdmissibility (u : E) (r : ℝ) :
    (‖u‖ + Real.exp r, u) ∈ strictLorentzAdmissibility := by
  change ‖u‖ < ‖u‖ + Real.exp r
  exact lt_add_of_pos_right _ (Real.exp_pos r)

omit [NormedSpace ℝ E] in
/-- Margin sensitivity is bounded by energy and momentum perturbations. -/
theorem lorentzAdmissibilityMargin_perturbation (a b : ℝ) (u v : E) :
    |lorentzAdmissibilityMargin a u - lorentzAdmissibilityMargin b v| ≤
      |a - b| + ‖u - v‖ := by
  have he : lorentzAdmissibilityMargin a u - lorentzAdmissibilityMargin b v =
      (a - b) - (‖u‖ - ‖v‖) := by unfold lorentzAdmissibilityMargin; ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add le_rfl (abs_norm_sub_norm_le u v))

omit [NormedSpace ℝ E] in
/-- Closedness includes the physically important null boundary. -/
theorem isClosed_closedLorentzAdmissibility : IsClosed (closedLorentzAdmissibility (E := E)) :=
  isClosed_le continuous_snd.norm continuous_fst

omit [NormedSpace ℝ E] in
/-- Strictly admissible states form an open set. -/
theorem isOpen_strictLorentzAdmissibility : IsOpen (strictLorentzAdmissibility (E := E)) :=
  isOpen_lt continuous_snd.norm continuous_fst

/-- The closed admissible states form a convex cone slice. -/
theorem convex_closedLorentzAdmissibility : Convex ℝ (closedLorentzAdmissibility (E := E)) := by
  intro u hu v hv a b ha hb _
  change ‖a • u.2 + b • v.2‖ ≤ a * u.1 + b * v.1
  calc
    _ ≤ ‖a • u.2‖ + ‖b • v.2‖ := norm_add_le _ _
    _ = a * ‖u.2‖ + b * ‖v.2‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)

/-- Strict admissibility survives every convex mixture of strict states. -/
theorem convex_strictLorentzAdmissibility : Convex ℝ (strictLorentzAdmissibility (E := E)) := by
  intro u hu v hv a b ha hb hab
  change ‖a • u.2 + b • v.2‖ < a * u.1 + b * v.1
  have hu' : 0 < u.1 - ‖u.2‖ := sub_pos.mpr hu
  have hv' : 0 < v.1 - ‖v.2‖ := sub_pos.mpr hv
  have hgap : 0 < a * (u.1 - ‖u.2‖) + b * (v.1 - ‖v.2‖) := by
    rcases eq_or_lt_of_le ha with hzero | hpos
    · have hbpos : 0 < b := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha hu'.le) (mul_pos hbpos hv')
    · exact add_pos_of_pos_of_nonneg (mul_pos hpos hu') (mul_nonneg hb hv'.le)
  calc
    _ ≤ ‖a • u.2‖ + ‖b • v.2‖ := norm_add_le _ _
    _ = a * ‖u.2‖ + b * ‖v.2‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < _ := by nlinarith [hgap]

/-- One-dimensional admissibility is precisely the existing confocal cone. -/
theorem closedLorentzAdmissibility_iff_confocal (a x : ℝ) :
    (a, x) ∈ closedLorentzAdmissibility (E := ℝ) ↔ (x, a) ∈ _root_.HTGeometry.confocalLorentzCone := by
  simp only [closedLorentzAdmissibility, _root_.HTGeometry.confocalLorentzCone, Set.mem_setOf_eq, Real.norm_eq_abs]

/-- A probability mixture has at least the mean reserve of its individual states. -/
theorem lorentzAdmissibilityMargin_probability_mix
    {ι : Type*} [Fintype ι] (p : FiniteProbabilityLaw ι) (a : ι → ℝ) (u : ι → E) :
    (∑ i, p.prob i * lorentzAdmissibilityMargin (a i) (u i)) ≤
      lorentzAdmissibilityMargin (∑ i, p.prob i * a i) (∑ i, p.prob i • u i) := by
  have hn : ‖∑ i, p.prob i • u i‖ ≤ ∑ i, p.prob i * ‖u i‖ := by
    calc
      _ ≤ ∑ i, ‖p.prob i • u i‖ := norm_sum_le _ _
      _ = _ := by simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (p.nonneg _)]
  simp only [lorentzAdmissibilityMargin, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- Explicit strict states retain their full mean exponential reserve after mixing. -/
theorem lorentzAdmissibilityMargin_regularized_mix
    {ι : Type*} [Fintype ι] (p : FiniteProbabilityLaw ι) (u : ι → E) (r : ι → ℝ) :
    (∑ i, p.prob i * Real.exp (r i)) ≤
      lorentzAdmissibilityMargin (∑ i, p.prob i * (‖u i‖ + Real.exp (r i)))
        (∑ i, p.prob i • u i) := by
  simpa only [lorentzAdmissibilityMargin_exp] using
    lorentzAdmissibilityMargin_probability_mix p (fun i => ‖u i‖ + Real.exp (r i)) u

end
end GaloisForLFunctions.HTGeometry
