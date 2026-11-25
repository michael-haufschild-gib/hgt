import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.Pencil
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.EntryWindows.RealWitness

/-! # Sublevel lengths from a field witness away from the observation interval -/

open Polynomial Matrix MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem gap_eval_im (A Z : Matrix I I ℂ) (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian)
    (b y : ℝ) : ((gapPencil A Z b).det.eval (y:ℂ)).im=0 := by
  rw [eval_gapPencil,gap_determinant _ (hH y)]
  simp only [←Complex.ofReal_sub,←Complex.ofReal_prod,Complex.ofReal_im]

/-- A pointwise nonzero witness gives a length estimate for determinant
sublevels on every bounded field interval. Only its distance from the
interval enters the bound. The leading coefficient may vary. -/
theorem field_sublevel_length (A Z : Matrix I I ℂ) (hH : ∀ y : ℝ, (A+(y:ℂ) • Z).IsHermitian)
    (b z R r : ℝ) (hR : 0≤R) (hr : 0<r)
    (hz : 0<‖(gapPencil A Z b).det.eval (z:ℂ)‖) :
    let P := (gapPencil A Z b).det
    let D := Fintype.card I^2
    volume.real {y∈Ioo (-R) R | ‖P.eval (y:ℂ)‖≤‖P.eval (z:ℂ)‖/2*r^D} ≤
      4*exp 1*(|z|+R+1)*r := by
  intro P D
  obtain ⟨Q,hdeg,hq⟩ := real_evaluation_witness P (gap_eval_im A Z hH b)
  let C := ‖P.eval (z:ℂ)‖
  have hd : Q.natDegree≤D := hdeg.trans (gapPencil_degree A Z b)
  have hf : C/2*r^D*(1/r)^D < |Q.eval z| := by
    rw [hq,one_div,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),mul_one]
    exact half_lt_self hz
  have h := volume_sublevel_comp_le Q hd (g:=id) (a:= -R) (c:=R) (lam:=1) (b:=|z|+R+1)
    (q:=1/r) zero_lt_one (by linarith only [abs_nonneg z,hR]) (one_div_pos.mpr hr)
    (fun _ _ _ _ _ => by simp only [one_mul,id_eq,le_refl]) (z:=z) (fun y hy => by
      have hh : |y|≤R := abs_le.mpr ⟨hy.1.le,hy.2.le⟩
      exact (abs_sub _ _).trans (by dsimp only [id]; linarith only [hh])) hf
  simpa only [hq,Measure.real,id_eq,one_mul,one_div,div_inv_eq_mul] using h

#print axioms field_sublevel_length
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
