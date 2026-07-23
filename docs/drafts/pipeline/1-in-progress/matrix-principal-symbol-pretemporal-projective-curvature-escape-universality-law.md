# Matrix principal-symbol pretemporal projective-curvature escape universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL PROJECTIVE CURVATURE ESCAPE; LITERATURE AUDITED]`

## Lean-derived conjecture

An honest selected-derivation tower with one algebraically independent ancestral packet,
coefficient flatness, one regular law, and a law-independent source is pretemporally rigid:

- its varying-law differential-dependence spectrum is empty;
- its zeroth matrix principal symbol cannot be law-linear.

The corpus's universal quadric tower supplies the exact escape mechanism:

- its dependence spectrum is the nonlinear cone `A₀² = A₁A₂`;
- dependence and differential independence are invariant under every nonzero rescaling of `A`;
- its positive-definite causal chamber is nonempty and lies in the independent phase;
- its coefficient curvature is nonzero;
- its dependence cone is not any vector subspace;
- its law family admits no first-order commutator closure.

Thus nontrivial pretemporal dependence can survive projectivization only by leaving the
flat-linear common-source class; the concrete escape is curved and noncommutative.

## Corpus inputs

- `pretemporalAnchor_emptySpectrum_and_noLinearZeroSymbol`
- `universalQuadric_nonemptyCausalChamber_curvedBoundary`
- `universalQuadric_dependentSet`
- `quadricCone_not_submodule`
- `universalQuadric_no_commutatorClosure`

## Proof plan

1. Rewrite universal-quadric dependence membership by its exact quadratic equation.
2. Cancel `c²` for `c ≠ 0`, proving punctured-ray invariance.
3. Complement the dependence equivalence to obtain differential-independence invariance.
4. Package causal chamber, curvature, non-subspace, and noncommutator certificates.
5. Conjoin the concrete escape with the generic pretemporal rigidity theorem.

No numerical computation is used.

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof searches covered projective determinantal hypersurfaces, hyperbolicity cones,
positive-definite linear matrix pencils, homogeneous matrix cones, noncommutative determinantal
representations, differential-algebraic derivation families, and principal-symbol curvature.

Nearest sources:

- Shamovich--Vinnikov, *Livsic-type determinantal representations and hyperbolicity*,
  arXiv:1410.2826, treats real projective determinantal varieties and definite Hermitian
  representations:
  <https://arxiv.org/abs/1410.2826>
- Tunçel--Vandenberghe, *Linear optimization over homogeneous matrix cones*,
  arXiv:2211.00761, studies homogeneous cones and spectrahedral linear-matrix representations:
  <https://arxiv.org/abs/2211.00761>
- Volčič, *Stable noncommutative polynomials and their determinantal representations*,
  SIAM J. Applied Algebra and Geometry 2020, relates noncommutative stability to linear matrix
  pencils:
  <https://doi.org/10.1137/18M1206734>

No source found couples an exact differential-dependence spectrum for selected derivations with
pretemporal common-source rigidity, punctured-ray invariance, a nonempty independent causal
chamber, nonzero coefficient curvature, failure of every subspace horizon, and failure of
first-order commutator closure. Novelty claim is restricted to that joint law.

## Lean target

`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolPretemporalProjectiveCurvatureEscapeUniversalityLaw.lean`

## Verification

- source proof exact and warning-free:
  `lake env lean GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolPretemporalProjectiveCurvatureEscapeUniversalityLaw.lean`
- imported by `formal/GaloisForLFunctions/HTGeometry.lean`
- final module and umbrella builds deferred to terminal audit
