import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneCharacterTwists

/-! Finite sums of parameters are independent of the ordering
of their summands. Their determinant is the product of the
determinants of the summands. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A v}

def lpZero : WD h := lpUnr fun _ : Fin 0 => 1

@[simp] theorem lpDim_zero : (lpZero (h := h)).lpDim = 0 := by rw [lpZero, lpDim_lpUnr, Fintype.card_fin]

@[simp] theorem lpSum_zero (x : WD h) : x.lpSum lpZero = x := by
  refine WD.ind (fun n a => ?_) x
  rw [lpZero, lpUnr, lpSum_mk]
  refine sound ⟨LinearEquiv.prodUnique (R := ℂ), fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_comm (x y : WD h) : x.lpSum y = y.lpSum x := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  simp only [lpSum_mk]
  refine sound ⟨LinearEquiv.prodComm ℂ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem lpSum_assoc (x y z : WD h) : (x.lpSum y).lpSum z = x.lpSum (y.lpSum z) := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  refine WD.ind (fun l c => ?_) z
  simp only [lpSum_mk]
  refine sound ⟨LinearEquiv.prodAssoc ℂ _ _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem detChar_sum (x y : WD h) : (x.lpSum y).detChar = x.detChar * y.detChar := by
  refine WD.ind (fun n a => ?_) x
  refine WD.ind (fun m b => ?_) y
  simp only [lpSum_mk, detChar_mk]
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  change LinearMap.det ((a.ρ σ).prodMap (b.ρ σ)) = LinearMap.det (a.ρ σ) * LinearMap.det (b.ρ σ)
  exact LinearMap.det_prodMap _ _

def sumList (l : List (WD h)) : WD h := l.foldr lpSum lpZero

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  haveI : LeftCommutative (lpSum (h := h)) :=
    ⟨fun a b c => by rw [← lpSum_assoc, lpSum_comm a b, lpSum_assoc]⟩
  exact hp.foldr_eq _

end GlobalTheory.WeilDeligne.WD

#print axioms GlobalTheory.WeilDeligne.WD.detChar_sum
#print axioms GlobalTheory.WeilDeligne.WD.sumList_perm
