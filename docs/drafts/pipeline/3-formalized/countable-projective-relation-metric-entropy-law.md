# Countable projective relation-metric entropy law

- **ID:** `countable-projective-relation-metric-entropy-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / INFINITE MASTER-LAW EXTENSION
- **Date:** 2026-07-31
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CountableSpectralProjectiveRelationMetricEntropyLaw.lean`

## Exact countable law

Let \((E_k)_{k\ge0}\) be any countable real pure-point energy packet and
let \(p_k\ge0\), \(\sum_kp_k=1\). Remove common phase by anchoring

\[
  \omega_k=E_k-E_0.
\]

Every finitely supported integer character \(n\) of the anchored packet is
canonically balanced by moving its total charge to the zeroth coordinate:

\[
  B(n)=n-\Big(\sum_kn_k\Big)e_0.
\]

Then

\[
  \boxed{
  \sum_kn_k(E_k-E_0)
  =
  \sum_kB(n)_kE_k,}
\]

so the anchored integer relation lattice is exactly the original
spectrum's balanced projective relation lattice.

The closure \(K_E\) of the anchored phase line is exactly the annihilator of
that lattice. Spectral weights induce the exact Hilbert pullback metric

\[
  \|\Psi_p(z)-\Psi_p(w)\|^2
  =
  2\,S_p(z-w),
\]

and survival coherence is unchanged by the anchoring. Therefore, for every
\(r>0\),

\[
  \boxed{
  \tau_{2r^2}(p,E)
  \le
  N_r\big(\Psi_p(K_E)\big),}
\]

where the right side is the minimal number of radius-\(r\) Hilbert balls
covering the exact weighted projective relation hull.

No finite dimension, rational independence, spectral simplicity, finite
temporal rank, or finite-support state premise is used.

## Formal declarations

- `anchoredCountableFrequency`;
- `projectivizeCountablePhase`;
- `projectivizeCountablePhase_screwPhase`;
- `balanceCountableCharacterAtZero`;
- `balanceCountableCharacterAtZero_projective`;
- `infiniteTorusCharacterDetuning_anchored`;
- `mem_anchoredScrewRelationLattice_iff_balancedRelation`;
- `norm_summableWeightedPhaseAmplitude_projectivize`;
- `countableTorusWeightedCoherenceAt_projectivize_iff`;
- `countableTorusWeightedFirstCoherenceTime_projectivize`;
- `countableSpectralFirstCoherenceTime_anchored`;
- `countableSpectralProjectiveRelationHullCoveringNumber`;
- `countableSpectralFirstCoherenceTime_le_projectiveRelationHullCoveringNumber`;
- `exists_countableSpectralProjectiveRelationLatticeFirstReturnBound`.

## Role in the master paper

This theorem replaces the false impression that the master law is
finite-dimensional:

1. balanced relation lattice determines exact projective orbit carrier;
2. weights determine operational metric on that carrier;
3. metric entropy bounds actual first survival recurrence;
4. finite temporal rank is only the finite-dimensional numerical shadow;
5. weak-interaction constraint conversion is the sharp finite physical
   realization of the same relation-hull mechanism.

The theorem does not assert a countable weak interaction can erase every
relation. That stronger interaction realization remains finite in the
current corpus.

## Verification

Targeted foreground compilation with cached output passes:

```text
lake env lean \
  GaloisForLFunctions/RHTower/CountableSpectralProjectiveRelationMetricEntropyLaw.lean \
  -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CountableSpectralProjectiveRelationMetricEntropyLaw.olean
```

Axiom audit of all load-bearing declarations reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration is
used. Final module build and repository lint are reserved for publication
audit.
