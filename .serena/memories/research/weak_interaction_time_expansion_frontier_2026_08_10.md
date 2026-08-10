# Weak-interaction singular time expansion — frontier (2026-08-10, updated)

Card `2-fully-proven/weak-interaction-singular-quantum-time-expansion.md`.  Still stage 2.
Lean gates: 4 of 5 now closed; only "formalization of local generator" is open, and see below —
it is nearly discharged by an already-formalized parent.

## Closed this session

1. `HTGeometry/FiniteHorizonReporterHausdorff.lean` — equation `(7)`, the finite-family Hausdorff
   assembly, for arbitrary unital C*-algebras (`reporterFamily`, `norm_reporterFamily` = the
   card's `B_O`, `reporterOrbit`, `norm_reporterOrbit_sub_le`,
   `hausdorffDist_reporterOrbit_le`, `hausdorffDist_coupledReporterOrbit_le`).
2. `HTGeometry/ComplexAffineLinePolynomialAvoidance.lean` — the real affine-line avoidance layer
   lifted to complex-coefficient polynomials at real parameters via a coefficientwise
   real/imaginary split (`mvPolynomialRealShadow`).
3. `HTGeometry/OneKnobSpectralActivationLaw.lean` — the one-knob law instantiated with the ACTUAL
   spectral relation polynomials: `countable_exceptional_coupling_of_maximallyProjective_witness`
   (one maximally projective member ⇒ along a.e. affine line `A + gV`, maximal projective rank off
   a countable set of `g`), plus the witness transfer
   `mem_polynomialMatrixProjectiveGenericSet_of_maximallyProjective`.

All axiom-clean, wired into the HTGeometry umbrella, `lake build ...HTGeometry` green.

## Key discovery: the "local generator" is already formalized upstream

The card's parent chain ends at `3-formalized/nearest-neighbor-qudit-projective-spectral-maximality`
whose Lean stack (`TracelessLocalHamiltonianGenericityLaw.lean`,
`NearestNeighborQuditPathGenericityLaw.lean`) already proves, for every `n,q ≥ 2`, a *physical*
uniform-qudit-path witness with maximally projective spectrum, hence dense/residual/full-measure
genericity in the trace-zero local space
(`exists_uniformQuditPathTracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure`).
That is exactly the hypothesis consumed by item 3 above.

**Remaining work for the last gate**: bind the parent capstone's witness (stated via
`realHermitianSubmoduleMaximalSet L hL`, i.e. `polynomialHermitianMatrixMaximalSet` of
`realAffineMatrixPolynomial 0 (realMatrixSubmoduleGenerator L)`) to the `M`/`hHerm`/`p₀` slots of
`countable_exceptional_coupling_of_maximallyProjective_witness`.  Both sides already speak
`polynomialHermitianMatrixMaximalSet`, so this is plumbing (unfold `realAffineHermitianMaximalSet`,
`realHermitianSubmoduleMaximalSet`, and use `Dense` ⇒ nonempty to extract `p₀`), not new
mathematics.

## Do not redo

Diagonal 2-local Hamiltonians can never be the maximal witness: their eigenvalues are a linear image
of the parameters, and for `n=3, q=2` the achievable eigenvalue vectors span only 6 of 8 dimensions,
so the balanced relation with pattern `(1,-1,-1,1)` in `(x₁,x₃)` holds identically.  The parent's
witness is necessarily non-diagonal — and it already exists in Lean, so no perturbative
(Rayleigh–Schrödinger) construction is needed after all.
