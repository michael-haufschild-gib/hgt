# FZZ parity two-scale Krein self-adjointness no-go

## Status

Route F5 retired. Formal self-adjointness in the literal two-scale FZZ Krein form does not force
spectral reality. Strongest complex-pair survivor is formalized in Lean.

## Attempted conjecture F5

F4 exposes a canonical split-signature form from the literal FZZ parity kernel. Test whether formal
self-adjointness with respect to this particular source form nevertheless forces spectral reality,
despite failure of Hilbert positivity.

## Proof outcome

The conjecture is false by an exact source-derived model. From the three literal values
`P(1),P(2),P(4)`, Lean constructs:

- the Hermitian two-scale FZZ Krein pairing;
- a canonical traceless operator formally self-adjoint for that pairing;
- a strictly positive discriminant equal to the positive complement of the negative F4 minor;
- a strictly nonreal eigenvalue `i sqrt(Δ)`;
- an explicit nonzero eigenvector `(P(2), i sqrt(Δ)-P(1))`;
- exact nullity of that eigenvector for the source Krein pairing.

Consequently the fixed formally source-self-adjoint operator itself refutes spectral reality.

## Why route fails

In a positive-definite Hilbert form, self-adjointness forces eigenvalues real because a nonzero
eigenvector has nonzero norm. In the literal FZZ form, the negative two-scale determinant creates a
neutral cone. Formal self-adjointness forces a nonreal eigenmode onto that cone but does not exclude
it. The constructed eigenpair realizes this failure without fitted zeros, external parameters, or
an abstract existence premise.

This retires bare Krein self-adjointness and pseudo-Hermiticity as FZZ orientation principles. It
does not retire a source-derived definite invariant sector, a positive commutator/crossing law, or
dynamics that excludes neutral eigenmodes.

## Positive survivor

The negative Fermi–Hankel minor canonically generates a complex-pair Krein normal form. Its
nonreal eigenvalue scale is exactly the square root of

`P(1) (P(2)^2 - P(1)P(4)) / P(4)`.

The associated eigenmode is exactly neutral. This gives a coefficient-faithful local model for the
precise obstruction any surviving FZZ dynamics must remove: not indefiniteness itself, but neutral
complex modes inside it.

Lean module:
`formal/GaloisForLFunctions/RHTower/FZZCigarParityTwoScaleKreinSelfAdjointNoGo.lean`.

Key declarations:

- `fzzCigarParityTwoScaleKreinOperator_formallySelfAdjoint`
- `fzzCigarParityTwoScaleKreinDiscriminant_pos`
- `fzzCigarParityTwoScaleKreinEigenpair`
- `fzzCigarParityTwoScaleKreinEigenvalue_not_real`
- `fzzCigarParityTwoScaleKreinEigenvector_null`
- `not_fzzCigarParityTwoScaleKreinSelfAdjointSpectrallyReal`

## Corpus audit

- `FZZCigarParityFermiHankelPositivityNoGo` proves the exact source form has negative determinant
  and split signature.
- `HedenmalmSpectralInterpretationCompletion` proves generally that formal pair self-adjointness
  makes a nonreal mode null and that definiteness would recover spectral reality.
- `FiniteHankelBoundaryKreinCrossing` identifies signed crossing data, rather than square
  positivity, as the orientation variable at a Hankel null face.
- Existing FZZ two-channel classifications concern affine puncture pencils and target-energy
  occurrence. They do not build this literal parity-kernel Krein operator or its closed nonreal
  source eigenpair.

## Literature audit (27 August 2026)

- Günther–Stefani, *Third order spectral branch points in Krein space related setups*,
  arXiv:math-ph/0506021, states and models the general phenomenon that Krein-self-adjoint operators
  can have conjugate nonreal spectral sectors. It does not derive a matrix or discriminant from the
  FZZ/Salem Fermi source: https://arxiv.org/abs/math-ph/0506021
- Behrndt–Philipp–Trunk, *Bounds on the non-real spectrum of differential operators with indefinite
  weights*, arXiv:1204.1112, controls nonreal spectra under added definitizability/critical-point
  hypotheses. It confirms that indefinite self-adjointness alone is insufficient but contains no
  FZZ parity kernel: https://arxiv.org/abs/1204.1112
- Georgescu–Gérard–Häfner, *Boundary values of resolvents of self-adjoint operators in Krein
  spaces*, arXiv:1211.0791, requires definite spectral projections and a positive commutator for
  its Krein-space estimates. These are precisely the kinds of extra laws absent from bare FZZ
  self-adjointness: https://arxiv.org/abs/1211.0791
- Targeted searches found no primary source constructing this exact FZZ/Salem source-coefficient
  nonreal Krein eigenpair. Absence claim remains bounded by the searched arXiv corpus.

Novelty verdict: the coefficient-faithful FZZ two-scale Krein normal form, exact nonreal neutral
eigenpair, and formal spectral-reality no-go appear corpus-new and literature-unlocated. They close
another substantial operator orientation family but do not prove RH.

## Lean verification

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityTwoScaleKreinSelfAdjointNoGo.lean`
- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.FZZCigarParityTwoScaleKreinSelfAdjointNoGo`
- Key theorem axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Scoped banned-token and diff checks passed.
- Module is wired into `GaloisForLFunctions.RHTower` umbrella.
- Global lint has no error in this module; current failures are unrelated concurrently owned
  unreachable-module entries.

## Surviving open core

Derive from literal interacting FZZ/GFZZ dynamics one of: a definite invariant physical sector
containing every divisor mode, a signed Krein crossing law excluding neutral complex pairs, or a
positive commutator estimate strong enough to remove the nonreal sector. Formal self-adjointness,
even for the exact source form, is terminal.
