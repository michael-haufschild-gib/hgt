import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.SectorHamiltonian
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Regular characteristic equation of a spin with one longitudinal bond -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ

/-- Characteristic block after removing the square of the fast energy. -/
def reduced (L V : M) (a z u : ℂ) := (2*z) • L-(2*a) • V+u • ((L+V)*(L-V))

private theorem blocks_product (L V : M) {a d z B u : ℂ} (h : z^2=a^2+d^2) (hu : B*u=1) :
    (((z+a)*B) • (1:M)+(L+V))*(((z-a)*B) • (1:M)+(L-V))-(d*B)^2 • (1:M)=
      B • reduced L V a z u := by
  have he : ((z+a)*B)*((z-a)*B)=(d*B)^2 := by
    calc _ = (z^2-a^2)*B^2 := by ring
         _ = _ := by rw [h]; ring
  unfold reduced
  rw [add_mul,mul_add,mul_add]
  have he' : ((z-a)*B)*((z+a)*B)=(d*B)^2 := (mul_comm _ _).trans he
  simp only [Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,smul_add,smul_sub,smul_smul,he',hu,one_smul]
  module

private theorem block_singular (X Y : M) {q : ℂ} (hq : q≠0)
    (h : (Y*X-q^2 • (1:M)).det=0) :
    (fromBlocks X ((-q) • (1:M)) ((-q) • (1:M)) Y).det=0 := by
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  rw [sub_mulVec,←mulVec_mulVec,smul_mulVec,one_mulVec,sub_eq_zero] at hker
  let w := q⁻¹ • (X *ᵥ v)
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨Sum.elim v w,fun hz => hv (funext fun i => congrFun hz (.inl i)),?_⟩
  rw [fromBlocks_mulVec]
  change Sum.elim (X *ᵥ v+((-q) • (1:M)) *ᵥ w) (((-q) • (1:M)) *ᵥ v+Y *ᵥ w)=0
  rw [smul_mulVec,one_mulVec,smul_mulVec,one_mulVec]
  simp only [w,mulVec_smul,smul_smul,hker,neg_mul,mul_inv_cancel₀ hq,
    one_smul,add_neg_cancel,show q⁻¹*q^2=q by field_simp,neg_smul,neg_add_cancel]
  funext i
  cases i <;> rfl

/-- Finite physical Hamiltonian, in the two sectors of the new spin. -/
def physical (H V : M) (a d : ℂ) : Matrix (I⊕I) (I⊕I) ℂ :=
  fromBlocks (H+V+a • 1) (d • 1) (d • 1) (H-V-a • 1)

/-- A root of the regular equation gives a root of the physical spectrum
at every nonzero inverse splitting and nonzero transverse field. -/
theorem reduced_root_physical (H V : M) (e : ℂ) {a d z B u : ℂ}
    (h : z^2=a^2+d^2) (hu : B*u=1) (hd : d*B≠0)
    (hr : (reduced (scalar I e-H) V a z u).det=0) :
    matrixCharpolyRelation (physical H V (a*B) (d*B),z*B+e)=0 := by
  let L := scalar I e-H
  let X := ((z-a)*B) • (1:M)+(L-V)
  let Y := ((z+a)*B) • (1:M)+(L+V)
  have hz : (Y*X-(d*B)^2 • (1:M)).det=0 := by
    rw [show Y*X-(d*B)^2 • (1:M)=B • reduced L V a z u from blocks_product L V h hu,
      det_smul,hr,mul_zero]
  have hem : scalar (I⊕I) (z*B+e)-physical H V (a*B) (d*B)=
      fromBlocks X ((-(d*B)) • (1:M)) ((-(d*B)) • (1:M)) Y := by
    rw [scalar_eq_smul,←fromBlocks_one (l:=I) (m:=I),fromBlocks_smul,physical,
      sub_eq_add_neg,fromBlocks_neg,fromBlocks_add]
    simp only [smul_zero,zero_add,neg_smul]
    congr 1 <;> simp only [X,Y,L,scalar_eq_smul,add_smul] <;> module
  change (scalar (I⊕I) (z*B+e)-physical H V (a*B) (d*B)).det=0
  rw [hem]
  exact block_singular X Y hd hz

#print axioms reduced_root_physical
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
