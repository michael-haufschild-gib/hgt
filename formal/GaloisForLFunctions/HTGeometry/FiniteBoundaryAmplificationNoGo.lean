import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# No finite boundary audit under exponential amplification

A rank-one boundary channel can remain positive throughout any prescribed finite audit window and
cross into the negative sector immediately afterward. The scalar below is the unique nontrivial
eigenvalue of `I - ε(t) vv*` on `span(v)`; the orthogonal complement stays fixed at eigenvalue one.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Amplitude placing the rank-one boundary crossing one unit beyond audit scale `T`. -/
noncomputable def finiteAuditBoundaryAmplitude (kappa T : ℝ) : ℝ :=
  Real.exp (-kappa * (T + 1))

/-- Unique nontrivial eigenvalue of the one-channel family `I - ε(t) vv*`. -/
noncomputable def finiteAuditBoundaryEigenvalue (kappa T t : ℝ) : ℝ :=
  1 - finiteAuditBoundaryAmplitude kappa T * Real.exp (kappa * t)

theorem finiteAuditBoundaryAmplitude_pos (kappa T : ℝ) :
    0 < finiteAuditBoundaryAmplitude kappa T := by
  exact Real.exp_pos _

theorem finiteAuditBoundaryEigenvalue_eq (kappa T t : ℝ) :
    finiteAuditBoundaryEigenvalue kappa T t =
      1 - Real.exp (kappa * (t - (T + 1))) := by
  rw [finiteAuditBoundaryEigenvalue, finiteAuditBoundaryAmplitude, ← Real.exp_add]
  congr 2
  ring

theorem finiteAuditBoundaryEigenvalue_pos_of_le
    {kappa T t : ℝ} (hkappa : 0 < kappa) (ht : t ≤ T) :
    0 < finiteAuditBoundaryEigenvalue kappa T t := by
  rw [finiteAuditBoundaryEigenvalue_eq]
  have harg : kappa * (t - (T + 1)) < 0 := by
    exact mul_neg_of_pos_of_neg hkappa (by linarith)
  have hexp : Real.exp (kappa * (t - (T + 1))) < 1 :=
    Real.exp_lt_one_iff.mpr harg
  linarith

@[simp] theorem finiteAuditBoundaryEigenvalue_crossing (kappa T : ℝ) :
    finiteAuditBoundaryEigenvalue kappa T (T + 1) = 0 := by
  rw [finiteAuditBoundaryEigenvalue_eq]
  simp

theorem finiteAuditBoundaryEigenvalue_neg_after
    {kappa T delta : ℝ} (hkappa : 0 < kappa) (hdelta : 0 < delta) :
    finiteAuditBoundaryEigenvalue kappa T (T + 1 + delta) < 0 := by
  rw [finiteAuditBoundaryEigenvalue_eq]
  have harg : 0 < kappa * ((T + 1 + delta) - (T + 1)) := by
    rw [show (T + 1 + delta) - (T + 1) = delta by ring]
    exact mul_pos hkappa hdelta
  have hexp : 1 < Real.exp (kappa * ((T + 1 + delta) - (T + 1))) :=
    Real.one_lt_exp_iff.mpr harg
  linarith

/-- Every finite audit window admits a one-channel family that is positive throughout the window,
crosses exactly one unit later, and is negative immediately afterward. -/
theorem noFiniteBoundaryAudit_under_exponentialAmplification
    (T kappa : ℝ) (_hT : 0 ≤ T) (hkappa : 0 < kappa) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧
      (∀ t, 0 ≤ t → t ≤ T → 0 < 1 - epsilon * Real.exp (kappa * t)) ∧
      1 - epsilon * Real.exp (kappa * (T + 1)) = 0 ∧
      ∀ delta, 0 < delta →
        1 - epsilon * Real.exp (kappa * (T + 1 + delta)) < 0 := by
  refine ⟨finiteAuditBoundaryAmplitude kappa T,
    finiteAuditBoundaryAmplitude_pos kappa T, ?_, ?_, ?_⟩
  · intro t _ ht
    exact finiteAuditBoundaryEigenvalue_pos_of_le hkappa ht
  · exact finiteAuditBoundaryEigenvalue_crossing kappa T
  · intro delta hdelta
    exact finiteAuditBoundaryEigenvalue_neg_after hkappa hdelta

end GaloisForLFunctions.HTGeometry
