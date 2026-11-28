import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.Measurements

/-! # A common spectral bound for a selected family of affine phase tests -/

open Finset Matrix
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open _root_.RiemannGaussian.HermitianRankTrace
open private diagonalEnergy_spectral from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

def cutEnergy (S : Finset I) (e : I → ℝ) := ∑ i ∈ S, e i

/-- Sum of both adjacent partial energy sums at each tested rank. -/
def edgeEnergy (R : Finset I) (e : I → ℝ) :=
  ∑ j ∈ R, (cutEnergy (preceding j) e+cutEnergy (insert j (preceding j)) e)

private theorem combine {H B C : selfAdjoint (Mat I)} {a : ℝ} (hm : B.val+C.val=(2*a) • H.val)
    (S : Finset I) :
    let U := H.2.isHermitian.eigenvectorUnitary
    let e (M : selfAdjoint (Mat I)) := M.2.isHermitian.eigenvalues
    let d (M : selfAdjoint (Mat I)) := cutDeficit (normSqMatrix (U⁻¹*M.2.isHermitian.eigenvectorUnitary).val) (e M) S
    d B+d C=cutEnergy S (e B)+cutEnergy S (e C)-2*a*cutEnergy S (e H) := by
  intro U e d
  have he : U.valᴴ*H.val*U.val=diagonal (fun j => (e H j:ℂ)) := by
    conv_lhs => rw [isHermitian_eq_conj_diagonal H.2.isHermitian]
    change U.valᴴ*(U.val*diagonal _*U.valᴴ)*U.val=_
    have hu : U.valᴴ*U.val=1 := U.2.1
    simp only [mul_assoc]
    rw [hu,mul_one,←mul_assoc,hu,one_mul]
  have h (i : I) : diagonalEnergy U B.val i+diagonalEnergy U C.val i=2*a*e H i := by
    have he' : U.valᴴ*B.val*U.val+U.valᴴ*C.val*U.val=(2*a) • (U.valᴴ*H.val*U.val) := by
      rw [←add_mul,←mul_add,hm,Matrix.mul_smul,Matrix.smul_mul]
    simpa only [diagonalEnergy,he,Matrix.add_apply,Complex.add_re,Matrix.smul_apply,diagonal_apply_eq,
      Complex.real_smul,Complex.re_ofReal_mul,Complex.ofReal_re] using congrArg (fun X : Mat I => (X i i).re) he'
  have hsum := sum_congr (s₁:=S) rfl (fun i _ => h i)
  simp only [sum_add_distrib,←mul_sum] at hsum
  simp only [d,cutDeficit,e,←diagonalEnergy_spectral,cutEnergy]
  linarith only [hsum]

/-- The total measurement error on any chosen rank set uses only its
adjacent spectral cuts. The bound is simultaneous in the observation time. -/
theorem paired_edge_error (H B C : selfAdjoint (Mat I)) {a : ℝ} (hm : B.val+C.val=(2*a) • H.val)
    (R : Finset I) (t : ℝ) :
    let U := H.2.isHermitian.eigenvectorUnitary
    let F (M : selfAdjoint (Mat I)) := edgeEnergy R M.2.isHermitian.eigenvalues
    ∑ j ∈ R, (phaseError U B t j+phaseError U C t j) ≤ 2*|t| *(F B+F C-2*a*F H) := by
  intro U F
  let d (M : selfAdjoint (Mat I)) (S : Finset I) :=
    cutDeficit (normSqMatrix (U⁻¹*M.2.isHermitian.eigenvectorUnitary).val) M.2.isHermitian.eigenvalues S
  let f (M : selfAdjoint (Mat I)) (j : I) :=
    cutEnergy (preceding j) M.2.isHermitian.eigenvalues+cutEnergy (insert j (preceding j)) M.2.isHermitian.eigenvalues
  have hj (j : I) : phaseError U B t j+phaseError U C t j ≤ 2*|t| *(f B j+f C j-2*a*f H j) := by
    have hS := combine hm (preceding j)
    have hT := combine hm (insert j (preceding j))
    dsimp only at hS hT
    have he : (d B (preceding j)+d B (insert j (preceding j)))+
        (d C (preceding j)+d C (insert j (preceding j)))=f B j+f C j-2*a*f H j := by
      dsimp only [d,f]
      linarith only [hS,hT]
    exact (add_le_add (phaseError_le U B t j) (phaseError_le U C t j)).trans_eq
      ((mul_add (2*|t|) _ _).symm.trans (congrArg (fun x : ℝ => 2*|t| *x) he))
  apply (sum_le_sum fun j _ => hj j).trans_eq
  simp only [←mul_sum,sum_sub_distrib,sum_add_distrib,F,edgeEnergy,f]

#print axioms paired_edge_error
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
