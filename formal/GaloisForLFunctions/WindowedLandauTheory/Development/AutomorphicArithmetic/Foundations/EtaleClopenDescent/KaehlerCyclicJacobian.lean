import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CyclicDeterminantAnnihilator
import Mathlib.RingTheory.Kaehler.Basic

/-! The determinant of a pullback of differentials when the relative
Kähler module is cyclic. -/

noncomputable section

open KaehlerDifferential TensorProduct

namespace GlobalTheory.PD

variable {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  {d : ℕ}

/-- In local bases for the two absolute differential modules, the
annihilator of the cyclic relative module is the ideal of the Jacobian. -/
theorem kaehler_annihilator_eq_span_det
    (a : Module.Basis (Fin d) B (B ⊗[A] Ω[A⁄k]))
    (b : Module.Basis (Fin d) B Ω[B⁄k])
    (g : B →ₗ[B] Ω[B⁄A]) (hg : Function.Surjective g) :
    Module.annihilator B Ω[B⁄A] =
      Ideal.span {(LinearMap.toMatrix a b (mapBaseChange k A B)).det} := by
  let m := mapBaseChange k A B
  let q := KaehlerDifferential.map k A B B
  let M := LinearMap.toMatrix a b m
  let π := q.comp b.equivFun.symm.toLinearMap
  have he (x : B ⊗[A] Ω[A⁄k]) : M.mulVecLin (a.equivFun x) = b.equivFun (m x) :=
    LinearMap.toMatrix_mulVec_repr a b m x
  have hc : LinearMap.range M.mulVecLin = LinearMap.ker π := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      let w := a.equivFun.symm x
      have hx : M.mulVecLin x = b.equivFun (m w) :=
        (congrArg M.mulVecLin (a.equivFun.apply_symm_apply x)).symm.trans (he w)
      rw [hx, LinearMap.mem_ker]
      change q (b.equivFun.symm (b.equivFun (m w))) = 0
      rw [LinearEquiv.symm_apply_apply]
      exact (exact_mapBaseChange_map k A B (m w)).mpr ⟨w, rfl⟩
    · intro hy
      have hy' : q (b.equivFun.symm y) = 0 := LinearMap.mem_ker.mp hy
      obtain ⟨w, hw⟩ := (exact_mapBaseChange_map k A B _).mp hy'
      exact ⟨a.equivFun w, (he w).trans ((congrArg b.equivFun hw).trans (b.equivFun.apply_symm_apply y))⟩
  exact annihilator_eq_span_det_of_cyclic M π
    ((KaehlerDifferential.map_surjective k A B).comp b.equivFun.symm.surjective) hc g hg

end GlobalTheory.PD
