import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneOperations
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Tensor products of Weil–Deligne representations carry the
tensor action and the sum of the two monodromy operators. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial TensorProduct
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V W V' W' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup W'] [Module ℂ W'] [FiniteDimensional ℂ W']

private theorem isSemisimple_algHom (φ : End ℂ V →ₐ[ℂ] End ℂ W) {f : End ℂ V}
    (hf : f.IsSemisimple) : (φ f).IsSemisimple :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero])

private theorem isSemisimple_tensorMap {f : End ℂ V} {g : End ℂ W}
    (hf : f.IsSemisimple) (hg : g.IsSemisimple) :
    End.IsSemisimple (TensorProduct.map f g : End ℂ (V ⊗[ℂ] W)) := by
  have hf' : End.IsSemisimple (f.rTensor W : End ℂ (V ⊗[ℂ] W)) :=
    isSemisimple_algHom (End.rTensorAlgHom ℂ V W) hf
  have hg' : End.IsSemisimple (g.lTensor V : End ℂ (V ⊗[ℂ] W)) :=
    isSemisimple_algHom (End.lTensorAlgHom ℂ W V) hg
  rw [show (TensorProduct.map f g : End ℂ (V ⊗[ℂ] W)) = f.rTensor W * g.lTensor V by ext; simp]
  exact End.IsSemisimple.mul_of_commute (by show _ = _; ext; simp) hf' hg'

/-- The tensor product with monodromy acting as a derivation. -/
def WDRep.tensor (a : WDRep h V) (b : WDRep h W) : WDRep h (V ⊗[ℂ] W) where
  ρ := a.ρ.tprod b.ρ
  N := a.N.rTensor W + b.N.lTensor V
  smooth := a.smooth.of_le₂ b.smooth fun σ h₁ h₂ => by
    rw [Representation.tprod_apply, h₁, h₂, TensorProduct.map_one]
  semisimple σ := isSemisimple_tensorMap (a.semisimple σ) (b.semisimple σ)
  nilpotent := by
    refine Commute.isNilpotent_add ?_ (a.nilpotent.map (End.rTensorAlgHom ℂ V W))
      (b.nilpotent.map (End.lTensorAlgHom ℂ W V))
    show _ = _
    ext; simp
  comm σ := by
    ext x y
    simp [a.comm_apply, b.comm_apply, smul_tmul']

@[simp] theorem WDRep.tensor_ρ (a : WDRep h V) (b : WDRep h W) (σ : Weil h) :
    (a.tensor b).ρ σ = TensorProduct.map (a.ρ σ) (b.ρ σ) := rfl

@[simp] theorem WDRep.tensor_N (a : WDRep h V) (b : WDRep h W) :
    (a.tensor b).N = a.N.rTensor W + b.N.lTensor V := rfl

theorem WDRep.Iso.tensor {a : WDRep h V} {a' : WDRep h V'}
    {b : WDRep h W} {b' : WDRep h W'} (ha : a.Iso a') (hb : b.Iso b') : (a.tensor b).Iso (a'.tensor b') := by
  obtain ⟨e, hρ, hN⟩ := ha
  obtain ⟨f, hρ', hN'⟩ := hb
  refine ⟨TensorProduct.congr e f, fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hρ, hρ']
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hN, hN']
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensor product on isomorphism classes. -/
def WD.lpTensor (x y : WD h) : WD h :=
  Quotient.lift₂ (s₁ := isoSetoid h) (s₂ := isoSetoid h) (fun a b => WD.mk (a.2.tensor b.2))
    (fun _ _ _ _ ha hb => WD.sound (WDRep.Iso.tensor ha hb)) x y

@[simp] theorem WD.lpTensor_mk (a : WDRep h V) (b : WDRep h W) :
    (WD.mk a).lpTensor (WD.mk b) = WD.mk (a.tensor b) :=
  WD.sound ((WD.iso_std a).tensor (WD.iso_std b)).symm

theorem WD.lpDim_tensor (x y : WD h) : (x.lpTensor y).lpDim = x.lpDim * y.lpDim := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  simp only [WD.lpTensor_mk, WD.lpDim_mk, Module.finrank_tensorProduct]

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.tensor
#print axioms GlobalTheory.WeilDeligne.WD.lpDim_tensor
