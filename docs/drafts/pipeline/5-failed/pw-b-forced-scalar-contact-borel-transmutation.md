# PW-B forced scalar-contact Borel transmutation

- **ID:** pw-b-forced-scalar-contact-borel-transmutation
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B literal cyclic-Peierls / B2 ordered source bridge
- **Statement:** No nonzero common scalar multiplier of the literal horizon Peierls full-minus-square vertex can turn its intrinsic coefficient into any natural-grade PW Borel recoil edge.

## Goal

Test the sharp remaining scalar-normalization mechanism after the literal Peierls rates were shown to realize exact PW labels `(q,1-q)` and the bare metric numerator was shown unequal to every forward PW edge.

## Gates

- [x] 0 → 1 in-progress: exact horizon factorization and source parameter/rate identities located in literal cyclic-Peierls corpus.
- [x] 1 → 2 fully-proven: coefficient-pair contradiction dependency-closed.
- [ ] 2 → 3 formalized audit: direct Lean check and axiom audit green; leaf OLean audit remains pending under no-long-build rule.
- [ ] 3 → 4 publication-ready: not applicable to retired scalar subroute.

## Approach

The actual corrected-future horizon identity factors the vertex as
`parameter · (full - r₊(r₊-1)/4 · square)`.  Its prefactor is nonzero because its imaginary part is a nonzero literal Xi-source resolvent parameter.  Equating the resulting coefficient pair with the same nonzero multiplier times `full - PWedge(q,k)/4 · square` permits cancellation.  It yields `r₊(r₊-1)=PWedge(q,k)`, already impossible because imaginary parts give `(4k+6) Im(q)=0` while every actual Xi support point has nonzero imaginary part.

## No-go closure

- **Exact killing theorem/mechanism:** `d4BMPeierlsScalarContactCoefficients_ne_borel` kills every nonzero common scalar normalization; `d4BMPeierlsForcedContactCoefficients_ne_borel` specializes it to literal forced `parameter`.
- **Strongest positive survivor:** the source factorization is rigid enough to identify the exact missing type of law. Any viable ordered PW-B source bridge must be a field-valued lift defect that changes the relative full/square coefficient. A scalar contact prefactor, including the literal forced one, cannot do so.
- **New insight:** The remaining bridge is narrower than “derive a contact.” It must derive an exchange-odd ordered lift-defect term with a new relative field coefficient. The nonzero prefactor cannot hide the raw Borel mismatch. This retains the direct PW spectral bridge and does not revive RBH/B2 as an independent RH producer.
- **Status:** Paper proof is cancellation of a nonzero source prefactor plus the direct imaginary-part contradiction. Lean module `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekForcedContactScalarTransmutationNoGo.lean`; direct `lake env lean` passed and scratch `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. The literal corrected-future source leaf cannot currently be directly refreshed because immediate dependency `ThetaCuspHawkingBMCorrectedFutureFixedArmDecomposition.olean` is absent; rebuilding it was deferred under the no-long-build rule. Leaf `lake build` remains pending for same reason.

## Log

- 2026-09-21 — scalar forced-contact Borel transmutation retired; field-valued relative-coefficient lift defect is sole survivor.
