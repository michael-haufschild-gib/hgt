# Single-flux transition: preregistered mechanism test

Status: designed before execution; numerical guidance only, forbidden as a Lean sign premise.

## Frozen question

At the unique positive center τ where the literal compensation carrier
`G/Φ² = 3 + 2x Φ′/Φ` vanishes, is either native parity Hankel block indefinite at size at most ten?
This is a test of one all-order compensation architecture, not a new RH conjecture.

## Corpus basis and uncertain residue

`ThetaCuspCenterCompensationSign` proves uniqueness of τ. `ThetaCuspCenterCompensationFlux`
proves the exact flux derivative and zero integral. Dividing that derivative by
`r sinh(ar)` gives `G(r/2) + [ar coth(ar)−1] Φ(r/2)²`; the bracket tends to zero as a→0.
Therefore any fixed finite matrix of aperture-independent correction coefficients loses its
correction at τ in the small-aperture limit. Negative native quadratic data there would obstruct
that specific all-order pointwise-compensation scheme. No sign at τ is being assumed.

Prior reflected-fibre scans covered centers only through 137/2000 and do not answer this question.
The completed low-rank compensation and fixed-order tail results likewise do not determine it.

## Design

- Literal-source finite-atom runs: 120 digits/12 atoms and 200 digits/20 atoms.
- Mechanism control: first atom alone at its own compensation transition, 200 digits.
- Three independent processes; one BLAS/OpenMP thread per process; Runpod only.
- Generate derivatives through order38 by the exact recurrence already used in corpus scripts.
- Solve the source-defined transition by bisection, then inspect even and odd parity blocks up to size10.
- Use LDL pivots to locate the first failure; independently check its sign with a symmetrically
  scaled eigenvalue calculation and an explicit quadratic witness.
- Hard wall-time cap180 seconds. No adaptive rank expansion or broad scan in this run.

## Decision rules

1. Stable negative block in both literal-source runs: seek an analytic complete-source proof of
   the transition obstruction; then study corrections with different source carriers or necessary
   aperture-dependent growth. This does not disprove RH or the center-integration route.
2. No negative block through size10: retain the single-flux possibility at this diagnostic center;
   do not infer all-order positivity or enlarge the scan automatically.
3. Precision/truncation disagreement: inconclusive; inspect conditioning before any mathematical claim.
4. First-atom agreement/disagreement distinguishes a leading-atom obstruction from a tail-sensitive one.

No numerical value, witness or finite truncation certifies a theorem. Any later Lean theorem needs
an independent analytic argument retaining the complete source. Follow docs/meta/scientific-method.md.
