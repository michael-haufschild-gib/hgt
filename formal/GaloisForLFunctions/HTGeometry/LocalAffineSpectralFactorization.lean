import GaloisForLFunctions.HTGeometry.LocalMatrixTensorFactorization

/-!
# Spectator independence of finite local spectral branches

Exact tensor factorization transfers to analytic simple-eigenvalue branches. A generator supported
on a finite site packet has a branch equal to its active-sector branch plus the fixed onsite energy
of the spectator configuration. This is the concrete spectral locality theorem needed before
connected-cluster Möbius cancellation can be applied to actual local generators.
-/

open scoped Kronecker BigOperators Matrix.Norms.Elementwise
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Injectivity of a full additive product spectrum forces injectivity on every site packet. -/
theorem localOnsiteEnergy_injective_of_product
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (S : Finset V) :
    Function.Injective (localOnsiteEnergy onsite S) := by
  intro x y hxy
  let xout : OutsideConfiguration A S := Classical.choice inferInstance
  let e := configurationSplitEquiv A S
  have henergy :
      onsiteProductEnergy onsite (e.symm (x, xout)) =
        onsiteProductEnergy onsite (e.symm (y, xout)) := by
    rw [onsiteProductEnergy_configurationSplit,
      onsiteProductEnergy_configurationSplit, hxy]
  have hconfig := hinj henergy
  have hpairs := congrArg e hconfig
  simpa using congrArg Prod.fst hpairs

/-- Injectivity of a full additive product spectrum also forces injectivity on every complementary
site sector. -/
theorem outsideOnsiteEnergy_injective_of_product
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (S : Finset V) :
    Function.Injective (outsideOnsiteEnergy onsite S) := by
  intro x y hxy
  let xlocal : LocalConfiguration A S := Classical.choice inferInstance
  let e := configurationSplitEquiv A S
  have henergy :
      onsiteProductEnergy onsite (e.symm (xlocal, x)) =
        onsiteProductEnergy onsite (e.symm (xlocal, y)) := by
    rw [onsiteProductEnergy_configurationSplit,
      onsiteProductEnergy_configurationSplit, hxy]
  have hconfig := hinj henergy
  have hpairs := congrArg e hconfig
  simpa using congrArg Prod.snd hpairs

/-- **Spectator-independent local spectral branch.** For every finite complex affine generator
supported on `S` and every simple additive product spectrum, the global branch born from `x` is
exactly the active-sector branch plus the fixed onsite energy outside `S`. No self-adjointness,
normality, positivity, or closed-system assumption is used. -/
theorem exists_localAffineEigenvalueBranch_add_spectator
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (onsite : ∀ v, A v → ℂ)
    (hinj : Function.Injective (onsiteProductEnergy onsite))
    (S : Finset V)
    (interaction :
      E → Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ)
    (x : ∀ v, A v) :
    ∃ localBranch globalBranch : (E → ℂ) → ℂ,
      AnalyticAt ℂ localBranch 0 ∧
      AnalyticAt ℂ globalBranch 0 ∧
      localBranch 0 =
        localOnsiteEnergy onsite S (restrictLocalConfiguration S x) ∧
      globalBranch 0 = onsiteProductEnergy onsite x ∧
      (∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (localOnsiteEnergy onsite S))
            interaction coupling,
            localBranch coupling) = 0) ∧
      (∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (fun label => liftLocalMatrix S (interaction label))
            coupling,
            globalBranch coupling) = 0) ∧
      globalBranch =
        fun coupling =>
          localBranch coupling +
            outsideOnsiteEnergy onsite S
              (restrictOutsideConfiguration S x) := by
  let xlocal := restrictLocalConfiguration S x
  let xout := restrictOutsideConfiguration S x
  have hinjLocal :
      Function.Injective (localOnsiteEnergy onsite S) :=
    localOnsiteEnergy_injective_of_product onsite hinj S
  obtain ⟨localBranch, hlocalAnalytic, hlocal0, hlocalRoot⟩ :=
    affineMatrixFamily_eigenvalueBranch
      (localOnsiteEnergy onsite S) hinjLocal interaction xlocal
  let spectatorEnergy := outsideOnsiteEnergy onsite S xout
  let globalBranch : (E → ℂ) → ℂ :=
    fun coupling => localBranch coupling + spectatorEnergy
  have hglobalAnalytic : AnalyticAt ℂ globalBranch 0 :=
    hlocalAnalytic.add analyticAt_const
  have hsplitX :
      onsiteProductEnergy onsite x =
        localOnsiteEnergy onsite S xlocal + spectatorEnergy := by
    let e := configurationSplitEquiv A S
    have hex : e.symm (xlocal, xout) = x := e.symm_apply_apply x
    rw [← hex, onsiteProductEnergy_configurationSplit]
  have hglobal0 : globalBranch 0 = onsiteProductEnergy onsite x := by
    rw [show globalBranch 0 = localBranch 0 + spectatorEnergy by rfl,
      hlocal0, hsplitX]
  have hspectatorRoot :
      matrixCharpolyRelation
        (Matrix.diagonal (outsideOnsiteEnergy onsite S), spectatorEnergy) = 0 :=
    matrixCharpolyRelation_diagonal_root
      (outsideOnsiteEnergy onsite S) xout
  have hglobalRoot :
      ∀ᶠ coupling in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (fun label => liftLocalMatrix S (interaction label))
            coupling,
            globalBranch coupling) = 0 := by
    filter_upwards [hlocalRoot] with coupling hroot
    have hlocalEval :
        (affineMatrixFamily
          (Matrix.diagonal (localOnsiteEnergy onsite S))
          interaction coupling).charpoly.eval (localBranch coupling) = 0 := by
      rw [Matrix.eval_charpoly]
      exact hroot
    have hspectatorEval :
        (Matrix.diagonal (outsideOnsiteEnergy onsite S)).charpoly.eval
          spectatorEnergy = 0 := by
      rw [Matrix.eval_charpoly]
      exact hspectatorRoot
    have hsumEval :=
      charpoly_eval_kroneckerSum_eq_zero
        (affineMatrixFamily
          (Matrix.diagonal (localOnsiteEnergy onsite S))
          interaction coupling)
        (Matrix.diagonal (outsideOnsiteEnergy onsite S))
        hlocalEval hspectatorEval
    have hreindex :
        Matrix.reindex (configurationSplitEquiv A S)
          (configurationSplitEquiv A S)
          (affineMatrixFamily
            (Matrix.diagonal (onsiteProductEnergy onsite))
            (fun label => liftLocalMatrix S (interaction label))
            coupling) =
          kroneckerSum
            (affineMatrixFamily
              (Matrix.diagonal (localOnsiteEnergy onsite S))
              interaction coupling)
            (Matrix.diagonal (outsideOnsiteEnergy onsite S)) :=
      reindex_affine_liftLocalMatrix_eq_kroneckerSum
        onsite S interaction coupling
    have hglobalEval :
        (affineMatrixFamily
          (Matrix.diagonal (onsiteProductEnergy onsite))
          (fun label => liftLocalMatrix S (interaction label))
          coupling).charpoly.eval (globalBranch coupling) = 0 := by
      rw [← Matrix.charpoly_reindex (configurationSplitEquiv A S)]
      rw [hreindex]
      exact hsumEval
    rw [Matrix.eval_charpoly] at hglobalEval
    exact hglobalEval
  exact ⟨localBranch, globalBranch, hlocalAnalytic, hglobalAnalytic,
    hlocal0, hglobal0, hlocalRoot, hglobalRoot, rfl⟩

end GaloisForLFunctions.HTGeometry
