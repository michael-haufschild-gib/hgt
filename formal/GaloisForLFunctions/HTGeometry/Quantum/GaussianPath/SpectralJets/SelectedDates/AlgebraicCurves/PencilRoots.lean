import GaloisForLFunctions.HTGeometry.MeromorphicGermField
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-! # Algebraicity of a local eigenvalue branch on a polynomial matrix line -/

open Polynomial Filter Topology Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
noncomputable section

private abbrev puncture := 𝓝[≠] (0:ℂ)

private theorem coefficient_germ (p : ℂ[X]) :
    ratGerm (algebraMap ℂ[X] (RatFunc ℂ) p)=ofMero (fun z => p.eval z) (polynomial_meromorphicAt p) := by
  unfold ratGerm
  rw [RatFunc.liftRingHom_algebraMap]
  exact aeval_zGerm p

/-- A meromorphic germ satisfying a monic polynomial with polynomial
coefficients is algebraic over the rational functions of its parameter. -/
theorem algebraic_of_polynomial_root {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (P : ℂ[X][X]) (hP : P.Monic)
    (hz : ∀ᶠ z in puncture, P.eval₂ (Polynomial.evalRingHom z) (f z)=0) :
    IsAlgebraic (RatFunc ℂ) (ofMero f hf) := by
  let g : MeroGerm →+* Germ puncture ℂ := meroGermSubring.subtype
  let coeff := algebraMap ℂ[X] (RatFunc ℂ)
  let L := (aeval (R:=RatFunc ℂ) (ofMero f hf)).toRingHom.comp (Polynomial.mapRingHom coeff)
  let V : ℂ[X][X] →+* (ℂ → ℂ) :=
    RingHom.pi fun z => Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (f z)
  let J : (ℂ → ℂ) →+* Germ puncture ℂ := Germ.coeRingHom puncture
  have ev : g.comp L=J.comp V := by
    apply Polynomial.ringHom_ext
    · intro p
      have hv : V (Polynomial.C p)=(fun z => p.eval z) := by
        funext z
        exact Polynomial.eval₂_C ..
      simp only [RingHom.comp_apply,L,Polynomial.coe_mapRingHom,Polynomial.map_C,
        AlgHom.toRingHom_eq_coe,RingHom.coe_coe,aeval_C,hv]
      change (ratGerm (coeff p)).germ=_
      rw [coefficient_germ]
      rfl
    · have hv : V Polynomial.X=f := by
        funext z
        exact Polynomial.eval₂_X ..
      simp only [RingHom.comp_apply,L,Polynomial.coe_mapRingHom,Polynomial.map_X,
        AlgHom.toRingHom_eq_coe,RingHom.coe_coe,aeval_X,hv]
      rfl
  refine ⟨P.map coeff,(hP.map coeff).ne_zero,?_⟩
  apply MeroGerm.germ_injective
  change (g.comp L) P=0
  rw [ev]
  exact Germ.coe_eq.mpr hz

/-- Every local eigenvalue germ of a polynomial matrix family is
algebraic, including a branch selected by its real energy label. -/
theorem algebraic_pencil_root {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ[X]) {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (hz : ∀ᶠ z in puncture, matrixCharpolyRelation (M.map (Polynomial.evalRingHom z),f z)=0) :
    IsAlgebraic (RatFunc ℂ) (ofMero f hf) := by
  apply algebraic_of_polynomial_root hf M.charpoly M.charpoly_monic
  filter_upwards [hz] with z hz
  rwa [Polynomial.eval₂_eq_eval_map,←Matrix.charpoly_map,Matrix.eval_charpoly]

#print axioms algebraic_pencil_root
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves
