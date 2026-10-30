# Localization of the actual prime defect at a macroscopic cutoff

- **ID:** macroscopic-prime-defect-localization
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** A fixed-fraction cutoff loses only bounded outgoing prime mass;
  the full prime defect is controlled by the retained defect and logarithmic tail mass.

## Target

For `1≤M≤N`, put `S=Σ_(n≤N)x_n²`,
`T=Σ_(M<n≤N)log(n)x_n²`, and
`C=log(N)-log(M)+log(4)+log(8)+8`.
For every real coefficient packet,

`T≤(1+1/t)D_N+(1+t)CS` for every `t>0`, and
`D_N≤D_M+2T+2CS`.

The first estimate approaches unit defect cost without a factor `N/M`.
The second supplies the cutoff comparison needed to combine a separated low
block with high-band Gamma coercivity in the complete Weil form.

## Arithmetic mechanism

The existing exact upward rows give
`A(floor(N/m))-A(floor(M/m))≤C` for every `m≤N`.
For `m≤M`, subtract the lower row bound at `M` from the upper bound at `N`.
For `m>M`, the lower Mertens sum vanishes and `log(m)≥log(M)`.
Reindex prime edges by their upper endpoint. Young's inequality pays every
tail value by its edge defect and this bounded outgoing remainder.
Retaining the edges below `M` gives the second inequality.

## Lean audit

`RenormalizedArithmeticPotentialTheory/ThePrimeDefectLocalizesAtAMacroscopicCutoff.lean`:
`logarithmicTailMass_le_poleDefect` and
`poleDefect_le_cutoff_add_logarithmicTail` prove these exact inequalities.
Direct no-olean Lean check passed. Both declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. RAPT umbrella import added.

No complete-Weil claim or contribution credit before an actual source application.
