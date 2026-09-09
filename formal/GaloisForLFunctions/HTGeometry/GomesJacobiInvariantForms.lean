import GaloisForLFunctions.HTGeometry.GomesUnipotentInvariantForms
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Invariant tensors and flux for Jacobi recurrence frames

Application of the invariant-tensor reconstruction viewpoint of
https://arxiv.org/abs/2607.24901 and the internal-frame viewpoint of
https://arxiv.org/abs/2404.10461 to monic three-term recurrence matrices.
These are corpus applications, not transcriptions of numbered paper results.
The full real spectral family retains only alternating area; complex spectral
transport instead has an exact Hermitian flux defect with a sharp sign boundary.
-/

open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The actual companion step of a monic three-term recurrence at a real spectral parameter. -/
def gomesJacobiStep (a b x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![x-a,-b;1,0]

/-- The same recurrence step at a complex spectral parameter. -/
def gomesJacobiComplexStep (a b : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![z-a,-(b : ℂ);1,0]

/-- The off-diagonal recurrence coefficient is exactly the area character of one step. -/
theorem gomesJacobiStep_det (a b x : ℝ) : (gomesJacobiStep a b x).det = b := by
  simp [gomesJacobiStep,Matrix.det_fin_two]

/-- The spectral parameter is invisible to the step's alternating area transport. -/
theorem gomesJacobiStep_area (a b x : ℝ) :
    (gomesJacobiStep a b x)ᵀ*gomesShearAreaMatrix ℝ *gomesJacobiStep a b x =
      b • gomesShearAreaMatrix ℝ := by
  rw [gomesShearArea_transport,gomesJacobiStep_det]

/-- Across the whole real spectral family, the only conformally preserved bilinear tensors are area forms. -/
theorem gomesJacobiStep_common_forms (a b : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ x, (gomesJacobiStep a b x)ᵀ*B*gomesJacobiStep a b x = b • B) ↔
      ∃ c : ℝ, B = c • gomesShearAreaMatrix ℝ := by
  constructor
  · intro h
    have h0 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) (h a)
    have hp := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) (h (a+1))
    have hm := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) (h (a-1))
    simp [gomesJacobiStep,Matrix.mul_apply,Fin.sum_univ_two] at h0 hp hm
    have h00 : B 0 0 = 0 := by linarith
    have h11 : B 1 1 = 0 := by rw [h00] at h0; simpa using h0
    have h10 : B 1 0 = -B 0 1 := by linarith
    refine ⟨B 0 1,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gomesShearAreaMatrix,h00,h11,h10]
  · rintro ⟨c,rfl⟩ x
    rw [Matrix.mul_smul,Matrix.smul_mul,gomesJacobiStep_area,smul_smul,smul_smul,mul_comm]

/-- No positive definite real metric can follow every spectral step with its area scaling. -/
theorem gomesJacobiStep_no_common_positive_metric (a b : ℝ) :
    ¬∃ B : Matrix (Fin 2) (Fin 2) ℝ, B.PosDef ∧
      ∀ x, (gomesJacobiStep a b x)ᵀ*B*gomesJacobiStep a b x = b • B := by
  rintro ⟨B,hB,h⟩
  obtain ⟨c,rfl⟩ := (gomesJacobiStep_common_forms a b B).mp h
  have h0 := hB.diag_pos (i := (0 : Fin 2))
  simp [gomesShearAreaMatrix] at h0

/-- Real spectral transport retains one complex line of sesquilinear tensors. -/
theorem gomesJacobiComplexStep_real_forms (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ x : ℝ, (gomesJacobiComplexStep a b x)ᴴ*H*gomesJacobiComplexStep a b x = (b : ℂ) • H) ↔
      ∃ c : ℂ, H = c • gomesShearAreaMatrix ℂ := by
  constructor
  · intro h
    have h0 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) (h a)
    have hp := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) (h (a+1))
    have hm := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) (h (a-1))
    simp [gomesJacobiComplexStep,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.conjTranspose_apply] at h0 hp hm
    have h00 : H 0 0 = 0 := by linear_combination (hp+hm-2*h0)/2
    have h11 : H 1 1 = 0 := by rw [h00] at h0; simpa using h0
    have h10 : H 1 0 = -H 0 1 := by linear_combination hp-h0-h00
    refine ⟨H 0 1,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gomesShearAreaMatrix,h00,h11,h10]
  · rintro ⟨c,rfl⟩ x
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gomesJacobiComplexStep,gomesShearAreaMatrix,Matrix.mul_apply,
        Fin.sum_univ_two,Matrix.conjTranspose_apply] <;> ring

/-- Allowing every complex spectral parameter leaves no nonzero common sesquilinear tensor. -/
theorem gomesJacobiComplexStep_complex_forms (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ z : ℂ, (gomesJacobiComplexStep a b z)ᴴ*H*gomesJacobiComplexStep a b z = (b : ℂ) • H) ↔ H = 0 := by
  constructor
  · intro h
    obtain ⟨c,rfl⟩ := (gomesJacobiComplexStep_real_forms a b H).mp (fun x => h x)
    have hi := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) (h ((a : ℂ)+Complex.I))
    simp [gomesJacobiComplexStep,gomesShearAreaMatrix,Matrix.mul_apply,
      Fin.sum_univ_two,Matrix.conjTranspose_apply] at hi
    have hc : c = 0 := by
      apply Complex.ext
      · have h := congrArg Complex.im hi
        simpa using h
      · have h := congrArg Complex.re hi
        simpa using h
    rw [hc,zero_smul]
  · rintro rfl z
    simp

/-- The Hermitian flux tensor associated with real recurrence area. -/
def gomesJacobiFlux : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • gomesShearAreaMatrix ℂ

/-- The source projection governing the complex-spectral flux defect. -/
def gomesJacobiSource : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,0]

/-- The surviving real-spectral flux is Hermitian. -/
theorem gomesJacobiFlux_isHermitian : gomesJacobiFlux.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gomesJacobiFlux,gomesShearAreaMatrix]

/-- Complex spectral transport has an exact rank-one imaginary-part flux defect. -/
theorem gomesJacobiComplexStep_flux_defect (a b : ℝ) (z : ℂ) :
    (gomesJacobiComplexStep a b z)ᴴ*gomesJacobiFlux*gomesJacobiComplexStep a b z -
      (b : ℂ) • gomesJacobiFlux = (2*z.im : ℝ) • gomesJacobiSource := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [gomesJacobiComplexStep,gomesJacobiFlux,gomesShearAreaMatrix,gomesJacobiSource,
      Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply]
  all_goals ring

/-- The real spectral family's Hermitian tensors are exactly real multiples of its flux. -/
theorem gomesJacobiComplexStep_real_hermitian_forms (a b : ℝ) (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (H.IsHermitian ∧ ∀ x : ℝ,
      (gomesJacobiComplexStep a b x)ᴴ*H*gomesJacobiComplexStep a b x = (b : ℂ) • H) ↔
        ∃ r : ℝ, H = r • gomesJacobiFlux := by
  constructor
  · rintro ⟨hH,h⟩
    obtain ⟨c,rfl⟩ := (gomesJacobiComplexStep_real_forms a b H).mp h
    change (c • gomesShearAreaMatrix ℂ)ᴴ = c • gomesShearAreaMatrix ℂ at hH
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).re) hH
    simp [gomesShearAreaMatrix,Matrix.conjTranspose_apply] at he
    have hc : c.re = 0 := by linarith
    refine ⟨c.im,?_⟩
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [gomesJacobiFlux,gomesShearAreaMatrix,hc]
  · rintro ⟨r,rfl⟩
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [gomesJacobiFlux,gomesShearAreaMatrix]
    · apply (gomesJacobiComplexStep_real_forms a b _).mpr
      refine ⟨(r : ℂ)*Complex.I,?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gomesJacobiFlux,gomesShearAreaMatrix]

/-- Even complex Hermitian metrics cannot be positive and follow every real spectral step. -/
theorem gomesJacobiComplexStep_no_common_positive_metric (a b : ℝ) :
    ¬∃ H : Matrix (Fin 2) (Fin 2) ℂ, H.PosDef ∧ ∀ x : ℝ,
      (gomesJacobiComplexStep a b x)ᴴ*H*gomesJacobiComplexStep a b x = (b : ℂ) • H := by
  rintro ⟨H,hH,h⟩
  obtain ⟨c,rfl⟩ := (gomesJacobiComplexStep_real_forms a b H).mp h
  have h0 := hH.diag_pos (i := (0 : Fin 2))
  simp [gomesShearAreaMatrix] at h0

/-- The flux defect is positive semidefinite precisely in the closed upper half-plane. -/
theorem gomesJacobiComplexStep_flux_defect_nonneg (a b : ℝ) (z : ℂ) :
    ((gomesJacobiComplexStep a b z)ᴴ*gomesJacobiFlux*gomesJacobiComplexStep a b z -
      (b : ℂ) • gomesJacobiFlux).PosSemidef ↔ 0 ≤ z.im := by
  rw [gomesJacobiComplexStep_flux_defect]
  have hd : (2*z.im : ℝ) • gomesJacobiSource =
      Matrix.diagonal ![((2*z.im : ℝ) : ℂ),0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gomesJacobiSource]
  rw [hd,Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h
    have h0 : (0 : ℂ) ≤ ((2*z.im : ℝ) : ℂ) := h 0
    have hr := Complex.zero_le_real.mp h0
    linarith
  · intro hz i
    fin_cases i
    · change (0 : ℂ) ≤ ((2*z.im : ℝ) : ℂ)
      exact Complex.zero_le_real.mpr (by linarith)
    · simp

end GaloisForLFunctions.HTGeometry
