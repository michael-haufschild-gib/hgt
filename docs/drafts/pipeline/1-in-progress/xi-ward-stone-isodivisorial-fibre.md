# Ward--Stone universality on the isodivisorial zeta fibre

- **ID:** `xi-ward-stone-isodivisorial-fibre`
- **Stage:** 1-in-progress
- **Type:** THEOREM CANDIDATE / HT APPLICATION TO RH / DIVISOR-FIBRE CLASSIFICATION
- **Scientific status:** `[PARENTS LEAN-PROVED] [CONNECTOR IN PROGRESS] [NOVELTY AUDIT OPEN]`

## Constraint

The existing publication draft built positive hypertranscendental channels sharing the zeta
divisor, but did not use the stronger exponent-zero Euler-gauge, Prime-Walsh/Stone, or quantized
Ward corpus.  The candidate must connect those theories without presenting another decorative RH
equivalence.

## Candidate theorem

Let `G_0` be the exponent-zero Euler-gauge group

```text
G_0 = {omega : for every sigma>0,
               sum_p p^(-sigma) |1-omega(p)| < infinity}.
```

For every pointed compact metrizable Stone space `(K,k_0)`, there is an exponentially sparse
`G_0`-family through the positive zeta phase such that:

1. the continued Euler products have exactly the zeta divisor, with multiplicity, at every point
   of `Re s>0`;
2. the distinguished Boolean anchor is exactly zeta;
3. the recurring prime-tail spectrum is homeomorphic to `(K,k_0)`;
4. every finite Prime-Walsh chamber has its exact differential-basis and rank law;
5. every divisor-profile observable is constant on this family.

The strict-right Xi Ward response is a divisor-profile observable.  Consequently the complete
family lies in one Ward phase.  For the zeta divisor that phase obeys the unconditional alternative

```text
E_W = 0  iff RH,
not RH   iff E_W > 8 pi,
```

and the infinitesimal absolute charge is exactly `8 pi` per strict-right upper Schwarz pair.
Finite Gamma-sewn recovery changes only squarefree parity of the signed first-order density and
preserves the absolute `8 pi` index.

Independently, the critical spectral-budget theorem supplies genuine zero exclusion:

```text
every off-line Xi pair has |height| > 8,
every nontrivial zeta zero in Re s>0 has |height| > sqrt(32).
```

## New conclusion

The complete source-tail Stone marginal and the Ward/divisor marginal are independent on the
zeta fibre.  Combining an HT statement with a Ward statement without a source--reflection
incidence is therefore provably non-discriminating.  The useful RH route is not “more HT” or “more
divisor energy” separately; it is a gauge-sensitive incidence whose absolute Ward index survives
the natural Gamma-sewn recovery.

## Hostile falsifiers

1. **Juxtaposition.**  Reject if the connector proves only two unrelated parent facts.  Required
   survivor: a universal constancy theorem for every divisor-profile observable on the realized
   Stone family, with Ward phase as a concrete specialization.
2. **Fake zeta specialization.**  Use the actual all-positive zeta phase and `riemannZeta`; no
   assumed Helson divisor realizer.
3. **Reflection overclaim.**  Do not claim the concrete Riemann reflection class is a transversal
   unless the required strong multiplicity-one theorem is unconditional in Lean.
4. **Ward relabeling.**  Do not score `E_W=0 iff RH` as novelty.  Novelty can lie only in the
   divisor-fibre Stone universality, Ward constancy on that fibre, and recovery-stable index.
5. **Zero-exclusion inflation.**  State the computation-free height floors exactly; do not imply
   they improve the known numerical zero-free range.
6. **Marginal no-go inflation.**  The theorem excludes separable divisor/source-tail readings,
   not all Hilbert--Polya, CCM, or source-incidence constructions.
7. **Open-core leakage.**  The paper must not suggest that the missing global upper bound
   `E_W <= 8 pi` has been proved.

## Gates

- [x] complete `8 pi` Ward theorem graph reconstructed
- [x] exact zeta zero-exclusion theorems located
- [x] exponent-zero isodivisorial Stone and maximal-HT parents located
- [x] Gamma-sewn parity-index preservation located
- [ ] formalize divisor-profile observable constancy and zeta Ward--Stone capstone
- [ ] direct `lake env lean` checks and axiom audit
- [ ] independent primary-literature novelty audit
- [ ] hostile general-journal review
- [ ] publication-ready paper with no formalization references

## Primary literature boundary

- Grosswald--Schnitzer: modified zeta/L-functions with the same nontrivial zeros.
- Seip; Bochkov--Romanov; Andersson: Helson-zeta universality and prescribed divisors.
- Weil/de Branges/Connes--Consani: RH positivity and divisor-space formulations.
- Sondow--Dumitrescu: xi-modulus monotonicity equivalence.

No priority claim is made until the combined Stone-fibre/Ward-index theorem is searched directly.
