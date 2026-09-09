import GaloisForLFunctions.HTGeometry.GomesJacobiInvariantForms

/-!
# Sharp positive metrics for Jacobi internal frames

Application of the invariant-metric questions in https://arxiv.org/abs/2607.24901
and https://arxiv.org/abs/2404.10461. The spectral-family obstruction has a sharp
positive survivor: a fixed step admits a positive metric precisely when its
trace squared is less than four times its determinant. Every such metric is
classified, including its explicit construction.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Canonical quadratic metric for a single real recurrence step with trace `u`. -/
def gomesJacobiMetric (u b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,-u/2;-u/2,b]

/-- The fixed-step metric transports with the recurrence's determinant character. -/
theorem gomesJacobiMetric_transport (a b x : ℝ) :
    (gomesJacobiStep a b x)ᵀ*gomesJacobiMetric (x-a) b*gomesJacobiStep a b x =
      b • gomesJacobiMetric (x-a) b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gomesJacobiStep,gomesJacobiMetric,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

/-- The metric determinant is the exact elliptic discriminant divided by four. -/
theorem gomesJacobiMetric_det (u b : ℝ) : (gomesJacobiMetric u b).det = b-u^2/4 := by
  simp [gomesJacobiMetric,Matrix.det_fin_two]
  ring

/-- Completing the square exposes the sharp positive direction and the boundary defect. -/
theorem gomesJacobiMetric_quadratic (u b : ℝ) (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (gomesJacobiMetric u b *ᵥ v) =
      (v 0-u/2*v 1)^2+(b-u^2/4)*(v 1)^2 := by
  simp [gomesJacobiMetric,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

/-- The canonical fixed-step metric is positive precisely in the strict elliptic region. -/
theorem gomesJacobiMetric_posDef_iff (u b : ℝ) :
    (gomesJacobiMetric u b).PosDef ↔ u^2 < 4*b := by
  constructor
  · intro h
    have hv : (![u/2,1] : Fin 2 → ℝ) ≠ 0 := by
      intro he
      have h1 := congrFun he 1
      simp at h1
    have hq := h.dotProduct_mulVec_pos hv
    rw [gomesJacobiMetric_quadratic] at hq
    simp at hq
    linarith
  · intro hd
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [gomesJacobiMetric]
    · intro v hv
      rw [gomesJacobiMetric_quadratic]
      have hdelta : 0 < b-u^2/4 := by linarith
      by_cases h1 : v 1 = 0
      · have h0 : v 0 ≠ 0 := by
          intro he
          apply hv
          ext i
          fin_cases i <;> simp [he,h1]
        simpa [h1] using sq_pos_of_ne_zero h0
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdelta (sq_pos_of_ne_zero h1))

/-- Every positive fixed-step metric is a positive multiple of the canonical elliptic metric. -/
theorem gomesJacobiStep_positive_metric_classification (a b x : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (B.PosDef ∧ (gomesJacobiStep a b x)ᵀ*B*gomesJacobiStep a b x = b • B) ↔
      ∃ c : ℝ, 0 < c ∧ (x-a)^2 < 4*b ∧ B = c • gomesJacobiMetric (x-a) b := by
  constructor
  · rintro ⟨hB,h⟩
    have hp : 0 < B 0 0 := hB.diag_pos
    have hsym : B 1 0 = B 0 1 := by
      have hh := hB.isHermitian
      change Bᴴ = B at hh
      have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hh
      simpa using he
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
    have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 1 1) h
    simp [gomesJacobiStep,Matrix.mul_apply,Fin.sum_univ_two,hsym] at h00 h01 h11
    have hv : (![x-a,1] : Fin 2 → ℝ) ≠ 0 := by
      intro he
      have h1 := congrFun he 1
      simp at h1
    have hq := hB.dotProduct_mulVec_pos hv
    simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,hsym] at hq
    have hb : 0 < b := by nlinarith
    have hq0 : b*((x-a)*B 0 0+2*B 0 1) = 0 := by linear_combination -h01
    have hq1 := (mul_eq_zero.mp hq0).resolve_left hb.ne'
    have hq2 : B 0 1 = -(x-a)/2*B 0 0 := by linarith
    have hr0 : b*(B 1 1-b*B 0 0) = 0 := by linear_combination -h11
    have hr1 := (mul_eq_zero.mp hr0).resolve_left hb.ne'
    have hr2 : B 1 1 = b*B 0 0 := by linarith
    have he : B = B 0 0 • gomesJacobiMetric (x-a) b := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gomesJacobiMetric,hsym,hq2,hr2] <;> ring
    have hG := hB.smul (inv_pos.mpr hp)
    have hscale : (B 0 0)⁻¹ • B = gomesJacobiMetric (x-a) b := by
      calc
        _ = (B 0 0)⁻¹ • (B 0 0 • gomesJacobiMetric (x-a) b) :=
          congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => (B 0 0)⁻¹ • M) he
        _ = _ := by rw [smul_smul,inv_mul_cancel₀ hp.ne',one_smul]
    rw [hscale] at hG
    exact ⟨B 0 0,hp,(gomesJacobiMetric_posDef_iff (x-a) b).mp hG,he⟩
  · rintro ⟨c,hc,hd,rfl⟩
    refine ⟨((gomesJacobiMetric_posDef_iff (x-a) b).mpr hd).smul hc,?_⟩
    rw [Matrix.mul_smul,Matrix.smul_mul,gomesJacobiMetric_transport,
      smul_smul,smul_smul,mul_comm]

/-- A fixed spectral step admits a positive metric exactly below the sharp discriminant boundary. -/
theorem gomesJacobiStep_exists_positive_metric_iff (a b x : ℝ) :
    (∃ B : Matrix (Fin 2) (Fin 2) ℝ, B.PosDef ∧
      (gomesJacobiStep a b x)ᵀ*B*gomesJacobiStep a b x = b • B) ↔ (x-a)^2 < 4*b := by
  constructor
  · rintro ⟨B,h⟩
    obtain ⟨c,hc,hd,he⟩ := (gomesJacobiStep_positive_metric_classification a b x B).mp h
    exact hd
  · intro hd
    exact ⟨gomesJacobiMetric (x-a) b,(gomesJacobiMetric_posDef_iff (x-a) b).mpr hd,
      gomesJacobiMetric_transport a b x⟩

end GaloisForLFunctions.HTGeometry
