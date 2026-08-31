# Formation Stokes/Følner isoperimetric current and rank-width selection -- Lean certification

- **Paper theorem:** ULF-TAFM-10
- **Lean module:** `GaloisForLFunctions.HTGeometry.FormationStokesFolnerSelection`
- **Status:** formalized

## Certified content

The module builds and proves:

1. signed incidence, vertex divergence, cut coefficient, cut flux, cut traffic, and edge boundary
   for arbitrary finite directed packets;
2. exact finite formation Stokes identity;
3. cut incidence equals endpoint-indicator difference;
4. absolute cut coefficient is exactly the boundary-edge indicator;
5. oriented flux is bounded by positive traffic, which is exactly the sum of absolute boundary
   currents;
6. uniform edge capacity bounds traffic by boundary cardinality;
7. constant bulk current times volume is bounded by cut traffic and boundary capacity;
8. a bundled packet type whose vertex and edge carriers may vary across a family;
9. inverse-isoperimetric existence of one boundary edge carrying the compulsory average bulk
   current;
10. weighted formation Følner selection;
11. box rank-width current bound and sublinear-rank selection; and
12. positive lower bound on channel-rank density, plus the bundled packet specialization.

No RH hypothesis, Xi zero, compactness premise, density premise, divisor-fitted current, or route
receiver occurs.

## Verification

- Scratch elaboration -- pass.
- Project-path elaboration -- pass.
- Final targeted leaf audit:
  `lake build GaloisForLFunctions.HTGeometry.FormationStokesFolnerSelection` -- pass (`973/973`).
- Batched scratch `#print axioms` on twelve significant declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Module is imported by `HTGeometry.UniversalLawField`; umbrella is not built.

No full project, theorem-area, or umbrella build was run.

## Selection boundary

The certificate replaces a postulated traffic ceiling by a mechanism: local divergence makes bulk
grade exact boundary flux, and vanishing formation-isoperimetric density makes total boundary
traffic sublinear. Off-neutrality must therefore pay through positive boundary density or
inverse-isoperimetric local-current blow-up. Hypertranscendence is sharpened to channel rank per
legal packet width; rank alone is nonselective. Constructing literal divisor-independent
prime/theta packets and proving their uniform local edge capacity remain the RH-bearing source
obligations.
