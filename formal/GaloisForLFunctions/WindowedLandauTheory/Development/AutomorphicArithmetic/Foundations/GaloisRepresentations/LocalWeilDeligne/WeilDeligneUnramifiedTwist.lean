import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalWeilDeligne.WeilDeligneRankOne

/-! Real unramified twists act additively on Weil–Deligne classes. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual

namespace GlobalTheory.WeilDeligne.WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/-- Unramified twist by the real power of the residue cardinality. -/
def lpTw (x : WD h) (s : ℝ) : WD h :=
  x.lpTwist (unrChar h (qPow w s)) (isSmooth_unrChar h _)

@[simp] theorem lpTw_zero (x : WD h) : x.lpTw 0 = x := by
  refine WD.ind (fun n a => ?_) x
  rw [lpTw, lpTwist_mk]
  apply sound
  refine ⟨LinearEquiv.refl ℂ _, fun σ v => ?_, fun v => rfl⟩
  change (unrChar h (qPow w 0) σ : ℂ) • a.ρ σ v = a.ρ σ v
  simp

theorem lpTwist_congr (x : WD h) {χ ψ : Weil h →* ℂˣ} (he : χ = ψ)
    (hχ : IsSmooth χ) (hψ : IsSmooth ψ) : x.lpTwist χ hχ = x.lpTwist ψ hψ := by
  subst ψ
  rfl

theorem lpTw_add (x : WD h) (s t : ℝ) : (x.lpTw s).lpTw t = x.lpTw (s + t) := by
  have he : unrChar h (qPow w (s + t)) = unrChar h (qPow w s) * unrChar h (qPow w t) := by
    ext σ
    simp only [unrChar_apply, qPow_add, mul_zpow, MonoidHom.mul_apply]
  unfold lpTw
  exact (lpTwist_mul _ _ _ _ _ (he ▸ isSmooth_unrChar h _)).trans
    (lpTwist_congr x he.symm _ _)

end GlobalTheory.WeilDeligne.WD

#print axioms GlobalTheory.WeilDeligne.WD.lpTw_add
