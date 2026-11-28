import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneCharacterTwists
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.IrreducibleWeilDeligne
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The dual Weil action uses inverse transpose. Its monodromy is
the negative transpose, and its determinant character is inverse. -/

noncomputable section

open NumberField IsDedekindDomain Module Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameKummer

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

private theorem aeval_dualMap (f : End ℂ V) (P : ℂ[X]) :
    aeval (f.dualMap : End ℂ (Dual ℂ V)) P = (aeval f P : End ℂ V).dualMap := by
  have hp (n : ℕ) : (f.dualMap : End ℂ (Dual ℂ V)) ^ n = (f ^ n : End ℂ V).dualMap := by
    induction n with
    | zero => ext; simp
    | succ n ih => rw [pow_succ, ih, pow_succ']; ext; simp
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]; ext; simp
  | monomial n c => rw [aeval_monomial, aeval_monomial, hp]; ext; simp

private theorem isSemisimple_dualMap {f : End ℂ V} (hf : f.IsSemisimple) :
    End.IsSemisimple (f.dualMap : End ℂ (Dual ℂ V)) :=
  End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree (by
    rw [aeval_dualMap, minpoly.aeval]; ext; simp)

/-- The contragredient parameter. -/
def WDRep.dual (a : WDRep h V) : WDRep h (Dual ℂ V) where
  ρ := a.ρ.dual
  N := -a.N.dualMap
  smooth := a.smooth.of_le fun σ hσ => by
    have he : a.ρ σ⁻¹ = 1 := by
      rw [← one_mul (a.ρ σ⁻¹), ← hσ, ← map_mul, mul_inv_cancel, map_one, hσ]
    rw [Representation.dual_apply, he]
    exact LinearMap.ext fun f => LinearMap.ext fun v => rfl
  semisimple σ := isSemisimple_dualMap (a.semisimple σ⁻¹)
  nilpotent := by
    obtain ⟨n, hn⟩ := a.nilpotent
    refine IsNilpotent.neg ⟨n, ?_⟩
    rw [← aeval_X_pow (R := ℂ), aeval_dualMap, aeval_X_pow, hn]
    ext; simp
  comm σ := by
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
    ext f v
    simp [Dual.transpose_apply, a.comm_apply, zpow_ne_zero _ hq]

@[simp] theorem WDRep.dual_ρ (a : WDRep h V) (σ : Weil h) :
    a.dual.ρ σ = (a.ρ σ⁻¹).dualMap := rfl

@[simp] theorem WDRep.dual_N (a : WDRep h V) : a.dual.N = -a.N.dualMap := rfl

theorem WDRep.Iso.dual {a : WDRep h V} {b : WDRep h W} (hab : a.Iso b) : a.dual.Iso b.dual := by
  obtain ⟨e, hρ, hN⟩ := hab.symm
  exact ⟨e.dualMap, fun σ f => by ext; simp [hρ], fun f => by ext; simp [hN]⟩

theorem WDRep.Tame.dual {a : WDRep h V} (ha : a.Tame) : a.dual.Tame := by
  intro σ hσ
  have h1 : a.ρ σ⁻¹ = 1 := ha σ⁻¹ ((wildInertia A).inv_mem hσ)
  rw [WDRep.dual_ρ, h1]
  ext
  simp

theorem WDRep.irreducible_dual (a : WDRep h V) (ha : a.ρ.IsIrreducible) : a.dual.ρ.IsIrreducible := by
  letI := ha
  letI : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Weil h)) a.ρ.asModule
  letI : Nontrivial (Subrepresentation a.dual.ρ) :=
    ⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩
  refine ⟨fun U => ?_⟩
  let S : Subrepresentation a.ρ :=
    ⟨U.toSubmodule.dualCoannihilator, fun g {v} hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro f hf
      have h := hv (a.dual.ρ g⁻¹ f) (U.apply_mem_toSubmodule g⁻¹ hf)
      simpa only [WDRep.dual_ρ, inv_inv, LinearMap.dualMap_apply] using h⟩
  have hS : S.toSubmodule.dualAnnihilator = U.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top S with hs | hs
  · right
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊤
    exact hS.symm.trans
      ((congrArg (fun T : Subrepresentation a.ρ => T.toSubmodule.dualAnnihilator) hs).trans
        Submodule.dualAnnihilator_bot)
  · left
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊥
    exact hS.symm.trans
      ((congrArg (fun T : Subrepresentation a.ρ => T.toSubmodule.dualAnnihilator) hs).trans
        Submodule.dualAnnihilator_top)

def WD.lpDual (x : WD h) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => WD.mk a.2.dual)
    (fun _ _ hab => WD.sound (WDRep.Iso.dual hab)) x

@[simp] theorem WD.lpDual_mk (a : WDRep h V) : (WD.mk a).lpDual = WD.mk a.dual :=
  WD.sound (WD.iso_std a).dual.symm

@[simp] theorem WD.lpDim_dual (x : WD h) : x.lpDual.lpDim = x.lpDim := by
  refine WD.ind (fun n a => ?_) x
  rw [WD.lpDual_mk, WD.lpDim_mk, WD.lpDim_mk, Subspace.dual_finrank_eq]

theorem WD.detChar_dual (x : WD h) (σ : Weil h) : x.lpDual.detChar σ = (x.detChar σ)⁻¹ := by
  refine WD.ind (fun n a => ?_) x
  rw [WD.lpDual_mk, WD.detChar_mk, WD.detChar_mk, ← map_inv]
  apply Units.ext
  change ((a.ρ σ⁻¹).dualMap : End ℂ (Dual ℂ (Fin n → ℂ))).det = (a.ρ σ⁻¹).det
  exact LinearMap.det_dualMap _

theorem WD.Irreducible.dual {x : WD h} (hx : x.Irreducible) : x.lpDual.Irreducible := by
  obtain ⟨n, a, rfl, ha⟩ := hx
  rw [WD.lpDual_mk, WD.irreducible_mk_iff]
  exact a.irreducible_dual ha

end GlobalTheory.WeilDeligne

#print axioms GlobalTheory.WeilDeligne.WDRep.dual
#print axioms GlobalTheory.WeilDeligne.WD.detChar_dual
#print axioms GlobalTheory.WeilDeligne.WD.Irreducible.dual
