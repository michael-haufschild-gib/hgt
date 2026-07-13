# Publication audit

## Verdict

Publication readiness score: **96/100**.

The score applies to the theorem note as a new unconditional divisor-side result, not as a proof
of the Riemann hypothesis.

## Score

- Correctness and proof closure: 25/25
  - Every substantive manuscript claim has a direct unconditional Lean declaration.
  - The manuscript capstones compile from the concrete Xi divisor, shifted-zeta carrier, Landau
    transfer, and global analytic remainder; there is no abstract proposition standing in for the
    hard input.
  - Checked axioms are only propext, Classical.choice, and Quot.sound.
- Novelty: 22/23
  - Primary comparison includes Weil, Yoshida, Bombieri, Connes, Connes--Consani,
    Connes--Consani--Moscovici, Voros's superzeta theory, Suzuki through June 2026, and Groskin
    through July 2026.
  - No located parent gives the conjunction of fixed arbitrary positive width, logarithmic mesh,
    lower-bound and norm criteria, cofinal negative divergence, the exact closed-ray one-sided
    exponent spectrum, the universal negative-mass Dirichlet abscissa, maximum-abscissa
    conservation for every nonnegative allocation, positive order-ideal cover equivalence, its
    exceptional and budget-matched power corollaries, and exact cutoff-free observable
    multiplicity-weighted pole tomography of the complete sequence.
  - The Landau and screw-function mechanisms are classical parents and are not claimed as new.
- Significance: 21/22
  - One scalar cofinal family recovers every off-critical divisor coordinate, its exact analytic
    multiplicity, its supremal transverse displacement, and every horizontal zero-free region
    through both its one-sided polynomial lower-loss spectrum and its exact negative Dirichlet
    abscissa.
  - The negative-mass abscissa is universal across all positive rectangular widths and admissible
    cutoffs.  Every exact positive principal/residual split conserves it as the maximum of the
    channel abscissae, so the transverse exponent cannot be diluted by positive allocation.
  - Pole locations recover support and normalized residues recover multiplicity, so the theorem
    identifies the weighted pole divisor rather than only an unweighted detector set.
  - The continuation is attached to the complete sequence itself; finite deletion is only an
    internal summability device and is absent from the theorem.
  - The normalized divisor is intrinsic: it is independent of the positive rectangular width and
    the multiplicity-copy presentation.
  - The result isolates a weaker and precise positive source obligation for the Connes route:
    dominate the actual negative mass by any nonnegative carrier, or any positive two-channel
    cover, having shifted Dirichlet energy.  Exact source splitting and pointwise control of one
    channel are unnecessary.  At every exponent this is equivalent to the corresponding
    horizontal zero-free region; the RH criterion is exactly its zero endpoint.
  - The remaining prime/semilocal construction of that critical energy majorant is open, so the
    note is not an RH proof.
- Exposition and standalone quality: 18/20
  - Definitions, multiplicity-safe continuation, Landau pole bound, completeness, exact growth,
    universal abscissa and split-conservation laws, order-ideal carrier spectrum,
    amplitude--thickness corollaries, observable tomography, screw identity, literature boundary,
    and limitations are included.
  - The note is concise; a journal may request expansion of standard zero-count and vertical-zeta
    estimates.
- Reproducibility and artifact quality: 10/10
  - Exact formal build, lint, axiom audit, claim trace, warning-free TeX build, and visual PDF review
    passed.

## Promotion boundary

The paper may claim only the statements listed in CLAIM_TRACE_AUDIT.md. Any further strengthening,
especially a prime-side lower bound, requires a new Lean declaration and a refreshed literature
audit before inclusion. The residue refinement is not advertised as an independent novelty claim;
it is the multiplicity-exact completion of the observable tomography theorem.
