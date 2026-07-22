import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolPretemporalAnchorRigidity

/-!
# Universal pretemporal phase boundary

An honest selected-derivation jet tower over one algebraically independent ancestral packet cannot
simultaneously have a nonempty regular principal fibre and a law-linear zeroth symbol.  With
coefficient flatness, the same pretemporal anchor moreover removes the entire varying-law
differential-dependence spectrum.

This packages the two consequences into one universal phase law.  In particular, the regular
nonempty-fibre hypotheses used by a causal linear pencil or a finite-hyperplane holographic model
cannot occur at selected-jet level zero.  Nontrivial horizons must instead retain coefficient
curvature, change their source with the law, lose regularity, or enter after the pretemporal layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k K L h ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k L] [Algebra K L] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [AddCommGroup h] [Module K h]

/-- **Universal pretemporal phase boundary.**  A common algebraically independent source, exact
selected-derivation jets, coefficient flatness, and one regular law force an empty dependence
spectrum.  The same honest regular realization excludes every law-linear zeroth matrix symbol.

The second conclusion simultaneously discharges the law-linear premise of nonempty-fibre causal
chamber and finite-hyperplane holography models at the selected-jet zeroth layer. -/
theorem pretemporalAnchor_emptySpectrum_and_noLinearZeroSymbol
    (source : ℕ → ι → L) (observable : ι → L)
    (law : h → Derivation k L L)
    (symbol : ℕ → h → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : h) (he : ∀ n, (symbol n e).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw source
      (fun n i ↦ selectedDerivationJet (law A) n (observable i))
      (fun n ↦ symbol n A))
    (hsource : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ source p.1 p.2)) :
    derivationLawDependentSet (K := K) law observable = ∅ ∧
      ∀ S : h →ₗ[K] Matrix ι ι K, ¬ ∀ A, symbol 0 A = S A := by
  constructor
  · exact derivationLawDependentSet_eq_empty_of_pretemporalAnchor
      source observable law symbol hflat e he hlaw hsource
  · intro S hS
    exact (not_regular_linear_zeroSymbol_of_selectedDerivation_lowerLaw
      source observable law symbol hlaw hsource S hS) ⟨e, he 0⟩

end

end GaloisForLFunctions.HTGeometry
