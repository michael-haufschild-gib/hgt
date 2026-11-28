import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.DepthZeroDeterminantTwistCompletion
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalGLIrreducibleClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicFirstUnitCharacter

/-! First principal-congruence fixed vectors define depth zero on
irreducible classes. On a p-adic chart two depth-zero classes
related by a determinant twist have a tame twisting character. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation
open GlobalTheory.Reciprocity GlobalTheory.PRep

namespace GlobalTheory.GLp

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "L" => HeightOneSpectrum.adicCompletion F v

namespace IrrGL

/-- The first principal-congruence subgroup has a nonzero fixed vector. -/
def DepthZero (x : IrrGL L) : Prop :=
  invariants (x.2.rep.ρ.comp (completionPrincipalCongruenceOne v (Fin x.1)).subtype) ≠ ⊥

private theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (H : Subgroup G) (h : invariants (ρ.comp H.subtype) ≠ ⊥) :
    invariants (σ.comp H.subtype) ≠ ⊥ := by
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  intro hb
  have hm : e.toLinearEquiv x ∈ invariants (σ.comp H.subtype) := by
    intro g
    change σ g.val (e.toLinearEquiv x) = _
    exact (IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g.val x).symm.trans
      (congrArg e.toLinearEquiv (hx g))
  rw [hb, Submodule.mem_bot] at hm
  exact hx₀ (e.toLinearEquiv.map_eq_zero_iff.mp hm)

theorem depthZero_mk_iff {n : ℕ} (a : IrrRep (GL (Fin n) L)) :
    DepthZero v (⟨n, a.cl⟩ : IrrGL L) ↔
      invariants (a.ρ.comp (completionPrincipalCongruenceOne v (Fin n)).subtype) ≠ ⊥ := by
  obtain ⟨e⟩ := IrrRep.cl_eq_iff.mp a.cl.cl_rep
  exact ⟨fixed_ne_bot_of_equiv e _, fixed_ne_bot_of_equiv e.symm _⟩

theorem depthZero_detTwist_iff {p : ℕ} [Fact p.Prime] (i : ℚ_[p] ≃+* L) (hi : Continuous i)
    (x : IrrGL L) (hn : 0 < x.1) (hx : x.DepthZero v)
    (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)) :
    (x.detTwist χ hχ).DepthZero v ↔ ∀ u : Lˣ, u ∈ unitsLevel v 1 → χ u = 1 := by
  let a := x.2.rep
  let b := a.twist (χ.comp GeneralLinearGroup.det) (hχ.preimage GeneralLinearGroup.continuous_det)
  have hclass : (⟨x.1, b.cl⟩ : IrrGL L) = x.detTwist χ hχ := by
    apply congrArg (Sigma.mk x.1)
    simp only [b, a, IrrRep.cl_twist, IrrCl.cl_rep]
  letI : a.ρ.IsIrreducible := a.irr
  rw [← hclass, depthZero_mk_iff, kills_firstUnits_iff_padic v i hi]
  exact determinantTwist_completionFixed_ne_bot_iff v i hi hn a.ρ a.smooth hx χ hχ

/-- Rank one, or a twist of a depth-zero class over a p-adic chart. -/
def GoodCusp (x : IrrGL L) : Prop :=
  x.1 = 1 ∨
    ((∃ (p : ℕ) (_ : Fact p.Prime) (i : ℚ_[p] ≃+* L), Continuous i) ∧
      ∃ (y : IrrGL L) (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)),
        y.DepthZero v ∧ x = y.detTwist χ hχ)

theorem GoodCusp.detTwist {x : IrrGL L} (hx : x.GoodCusp v)
    (χ : Lˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set Lˣ)) : (x.detTwist χ hχ).GoodCusp v := by
  rcases hx with h | ⟨hp, y, ψ, hψ, hy, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨hp, y, ψ * χ, isOpen_ker_mul _ _ hψ hχ, hy, detTwist_mul _ _ _ _ _ _⟩

theorem goodCusp_detTwist_iff (x : IrrGL L) (χ : Lˣ →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set Lˣ)) : (x.detTwist χ hχ).GoodCusp v ↔ x.GoodCusp v := by
  refine ⟨fun hx => ?_, fun hx => hx.detTwist v χ hχ⟩
  let hχ' := isOpen_ker_inv χ hχ
  have h := hx.detTwist v χ⁻¹ hχ'
  have he : χ * χ⁻¹ = 1 := MonoidHom.ext fun z => mul_inv_cancel (χ z)
  simpa only [detTwist_mul _ _ _ _ _ (isOpen_ker_mul _ _ hχ hχ'), he, detTwist_one] using h

end IrrGL
end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.IrrGL.depthZero_detTwist_iff
#print axioms GlobalTheory.GLp.IrrGL.goodCusp_detTwist_iff
