# Uniform sinh absorption for arbitrary compact odd theta profiles

- **ID:** thim-uniform-sinh-absorption
- **Stage:** 5-failed
- **Type:** NO-GO, with positive survivors
- **Source:** review-1910/astra.md, §5 T3
- **Retired claim:** A fixed coefficient absorbs the literal theta-cosh mass into the sinh potential for every even smooth compact profile, over arbitrarily large support radii.

## Exact obstruction

Let `m_a=oddProfile a`, `ψ_a=m_a/Θ`, and `0<a≤log(2)/2`. For `x≥log 2`,

\[
\psi_a(x)\cosh(x/2)\ge
\pi e^{2x-5\log(2)/4}\sinh(x/2).
\]

Every legitimate derivative majorant therefore gives
`coshSinhPolarRatio a M R ≥ π exp(2R−5log(2)/4)>1` when `R≥log 2`.
Allowing `a` and `M` to vary with the radius does not avoid this bound.
Smooth paired bump localization proves the stronger statement: **every fixed
integrated coefficient fails** on this source class. This retires the universal
absorption mechanism, not THIM, restricted source families, or compensated nonlocal estimates.

## Positive survivors and their exact status

1. **Confinement:** `K(L) P_tail(L,w)≤C_a(w)` with
   `K(L)=π exp(2L−5log(2)/4)`. Bounded cosh mass forces exponential sinh-tail control.
2. **Minimal local repair:** among continuous even nonnegative multiplication
   densities, the exact least correction is
   `[Θ ψ_a² cosh(x/2)−θ m_a sinh(x/2)]_+`. Its complete energy identity retains
   reflected-prime collar compensation. This correction is not asserted to be paid
   by jump energy on arbitrary profiles.
3. **Complete primitive horizon bound:** apply a shared cutoff to theta **before**
   shifting, then subtract two normalized odd translates. Both polar moments cancel
   exactly. Full edge and finite translated-source moments pay the moving boundary
   errors. The explicit admitted sequence is eventually nonzero, and its complete
   original Markov energy satisfies `|E(g_n)|≤2(L_a+L_b)/(n+1)²`.

**New insight:** failure of mass-only absorption forces a specific local excess;
the usable alternative on the canonical primitive family is signed-radical
cancellation with moment-preserving cutoffs. That cancellation improves the energy
error from first order to second order in graph distance. It proves neither a
finite-horizon sign nor density in the full primitive sector.

**Paper status:** dependency-closed proofs, parameter costs and parent-theory audit
are in [the research card](../3-formalized/thim-review1910-complete-absorption.md).

**Lean status:** both survivor modules passed named-source audits. All 84 public
declarations passed the axiom audit, using only the standard Lean axioms
`propext`, `Classical.choice` and `Quot.sound`. Repository lint was run; its remaining
errors concern concurrent BVI wiring and generated indexes, with no THIM error reported.
Modules:

- `GaloisForLFunctions.TransHorizonIncidenceMechanics.OddPolarAbsorptionBoundaryAndCompensatedHorizon`
- `GaloisForLFunctions.TransHorizonIncidenceMechanics.CanonicalOddPrimitiveHorizonBounds`

## Novelty boundary

Kernel slope control, graph admission, radical pairing and general ground-state
machinery are prior work. Localization, Cauchy–Schwarz and weighted cutoff bounds
are standard. The result is the explicit obstruction and complete source-specific
replacement at this interface; no external scientific-priority claim is made.
