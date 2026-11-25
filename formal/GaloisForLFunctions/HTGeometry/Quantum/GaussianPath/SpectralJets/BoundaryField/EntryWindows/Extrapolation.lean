import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.Pencil
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez
import GaloisForLFunctions.QuantumAlg.Util.Polynomial.Basic

/-! # Sublevel lengths from a field witness away from the observation interval -/

open Polynomial Matrix MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem real_gap_norm (A Z : Matrix I I ℂ) (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian)
    (b y : ℝ) :
    |(QuantumAlg.complexPolynomialRealPart (gapPencil A Z b).det).eval y| =
      ‖(gapPencil A Z b).det.eval (y:ℂ)‖ := by
  rw [QuantumAlg.complexPolynomialRealPart_eval_ofReal,eval_gapPencil,gap_determinant _ (hH y)]
  have he : (∏ p : I × I, ((b:ℂ)-(((hH y).eigenvalues p.1:ℂ)-((hH y).eigenvalues p.2:ℂ))))=
      ((∏ p : I × I, b-((hH y).eigenvalues p.1-(hH y).eigenvalues p.2):ℝ):ℂ) := by
    simp only [Complex.ofReal_prod,Complex.ofReal_sub]
  rw [he,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs]

/-- A pointwise nonzero witness gives a length estimate for determinant
sublevels on every bounded field interval. Only its distance from the
interval enters the bound; polynomial leading coefficients may change. -/
theorem field_sublevel_length (A Z : Matrix I I ℂ) (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian)
    (b z R r : ℝ) (hR : 0≤R) (hr : 0<r)
    (hz : 0<‖(gapPencil A Z b).det.eval (z:ℂ)‖) :
    let P := (gapPencil A Z b).det
    let D := Fintype.card I^2
    volume.real {y∈Ioo (-R) R | ‖P.eval (y:ℂ)‖≤‖P.eval (z:ℂ)‖/2*r^D} ≤
      4*exp 1*(|z|+R+1)*r := by
  intro P D
  let Q := QuantumAlg.complexPolynomialRealPart P
  let C := ‖P.eval (z:ℂ)‖
  have hd : Q.natDegree≤D := (QuantumAlg.complexPolynomialRealPart_natDegree_le P).trans (gapPencil_degree A Z b)
  have hq (y : ℝ) : |Q.eval y|=‖P.eval (y:ℂ)‖ := real_gap_norm A Z hH b y
  have hf : C/2*r^D*(1/r)^D<|Q.eval z| := by
    rw [hq,one_div,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),mul_one]
    exact half_lt_self hz
  have h := volume_sublevel_comp_le Q hd (g:=id) (a:= -R) (c:=R) (lam:=1) (b:=|z|+R+1)
    (q:=1/r) zero_lt_one (by linarith only [abs_nonneg z,hR]) (one_div_pos.mpr hr)
    (fun _ _ _ _ _ => by simp only [one_mul,id_eq,le_refl]) (z:=z) (fun y hy => by
      have hh : |y|≤R := abs_le.mpr ⟨hy.1.le,hy.2.le⟩
      exact (abs_sub _ _).trans (by dsimp only [id]; linarith only [hh])) hf
  simpa only [hq,Measure.real,id_eq,one_mul,div_one_div] using h

#print axioms field_sublevel_length
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
