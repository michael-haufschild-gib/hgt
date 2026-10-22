# Involutive-clock fidelity--Fisher sector-factorization universality law

- **ID:** `involutive-clock-fidelity-fisher-sector-factorization-universality-law`
- **Law:** LAW512
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Targets:**
  - `formal/GaloisForLFunctions/HTGeometry/InvolutiveClockFidelityFisherSectorFactorizationUniversalityLaw.lean`
  - `formal/GaloisForLFunctions/RHTower/SoninLogClockFidelityFisherSectorFactorizationUniversalityLaw.lean`

## Theorem

Let `U` be an isometric involution, let `ψ` be a unit `U`-fixed state, let `X` be any bounded
operator, and write `P = (1 + U) / 2`.  Then the homogeneous fidelity deficit of the observed
vector `Xψ` factors exactly as

```text
||Xψ||⁴ - |⟨Xψ, U Xψ⟩|²
  = ||P Xψ||² · QFIψ((1 - P)Xψ).
```

Equivalently, projective clock asymmetry of `Xψ` is visible-sector mass times the quantum Fisher
information erased from `Xψ` by the two-reading clock.  No self-adjointness, positivity, or
nonzero-observation hypothesis on `X` is required.

For logarithmic Sonin scattering, the same law identifies Fourier-scattering infidelity of every
observed physical state with invariant Sonin-sector mass times hidden logarithmic-clock QFI.

## Theorem-generated derivation

Whole-corpus leaf comparison exposed three independent evaluations:

- `finiteInvolutiveClock_homogeneousFidelityDeficit_eq_four_mul_sectorWeights`;
- `finiteInvolutiveClock_erasedPureStateQuantumFisherValue_eq_commutatorNormSq`;
- the fixed-state half-commutator identity used inside
  `re_inner_finiteInvolutiveObservableTwirlStarKadisonDefect_eq_quarter_commutatorNormSq_of_fixed`.

The first gives `4 ||P Xψ||² ||(1-P)Xψ||²`.  Since `Uψ = ψ`, the ordinary commutator obeys

```text
(XU - UX)ψ = 2(1-P)Xψ.
```

The second theorem therefore gives

```text
QFIψ((1-P)Xψ) = 4 ||(1-P)Xψ||².
```

Substitution produces the factorization.

## Dependency-closed paper proof

Set `y = Xψ`.  Isometric involutivity gives the orthogonal sector decomposition
`y = Py + (1-P)y`.  Existing homogeneous fidelity asymmetry yields

```text
||y||⁴ - |⟨y, Uy⟩|² = 4 ||Py||² ||(1-P)y||².
```

Fixedness of `ψ` and `P = (1+U)/2` imply

```text
(XU - UX)ψ = Xψ - UXψ = 2(1-P)Xψ.
```

Existing involutive-clock QFI/dephasing gives QFI equal to squared commutator norm, hence equal to
`4 ||(1-P)Xψ||²`.  Multiplying by `||PXψ||²` and comparing the two exact expressions proves the
law.  No numerical computation is used.

## Strict corpus delta

Corpus separately identifies fidelity deficit with a product of sector weights and erased QFI
with commutator/dephasing energy.  It never eliminates the anti-invariant weight to express
fidelity deficit as the product of visible mass and hidden QFI, either abstractly or for Sonin
logarithmic scattering.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit

## Lean result

The two target modules prove:

- `finiteInvolutiveClock_homogeneousFidelityDeficit_eq_invariantWeight_mul_erasedQFI`;
- `soninLogClock_homogeneousFidelityDeficit_eq_invariantWeight_mul_erasedQFI`.

Both direct exact checks passed without warnings:

- `lake env lean GaloisForLFunctions/HTGeometry/InvolutiveClockFidelityFisherSectorFactorizationUniversalityLaw.lean`;
- `lake env lean GaloisForLFunctions/RHTower/SoninLogClockFidelityFisherSectorFactorizationUniversalityLaw.lean`.

The modules are imported by the corresponding `HTGeometry.lean` and `RHTower.lean` umbrellas.

## Post-proof novelty audit

Performed only after both dependency-closed Lean proofs passed.  Targeted searches recovered:

- general QFI--Bures/fidelity susceptibility relations;
- QFI as a continuous-symmetry asymmetry resource;
- fidelity with a symmetry-transformed apparatus state in quantitative WAY bounds for arbitrary
  unitary and antiunitary symmetries;
- even/odd QFI decompositions for Gaussian states.

They did not recover the exact finite-involution identity in which homogeneous discrete-symmetry
fidelity deficit of `Xψ` factors as invariant observed mass times QFI erased from the same
observation, nor its logarithmic Sonin specialization.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for this exact
stationary-observation sector factorization, not for general fidelity susceptibility, Bures/QFI
geometry, or resource theories of asymmetry.
