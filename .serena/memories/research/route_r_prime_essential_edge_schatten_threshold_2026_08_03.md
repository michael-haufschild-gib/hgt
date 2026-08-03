# Route R prime essential-edge exact Schatten threshold (2026-08-03)

New unconditional source object and theorem:
- Module: `formal/GaloisForLFunctions/RHTower/PrimeFirstTraceEssentialEdgeSchattenThreshold.lean`.
- Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-prime-essential-edge-schatten-threshold.md`.
- Frontier updates: `rh-current-frontier-map.md`, `riemann-arithmetic-conormal-socle-gauge-law.md`.
- Umbrella wired in `formal/GaloisForLFunctions/RHTower.lean`.

Definitions:
`a_p = log(p) • primeHardyKernelMap(w_(p,farPrime p)) - e1`;
`b_p = p • primeFirstTraceEssentialResponse p - e2`.

Exact theorem:
`a_p(2) = 1/p - p/(farPrime p)^2 >= 3/(4p)`.
Upper bounds: `||a_p|| <= 4/p`, `||b_p|| <= 5/p`.
Therefore source and response deviations have summable norm squares, but source norms are not summable. Explicit `lp 2` source/response objects and paired edge correction constructed. Source deviation is proved not `Memℓp ... 1`.

Scientific consequence: literal all-prime normalized strict-preclosure correction is Hilbert-Schmidt but not trace class. Ordinary coefficient trace/Fredholm determinant is excluded; first admissible regularization is det2 with a quadratic trace cocycle. This narrows Route R open core to:
1. diagonal/operator realization of this ell2/not-ell1 edge;
2. identify det2 quadratic cocycle with regular Wold-Gamma anomaly;
3. identify BV first trace as singular boundary of same relative class;
4. carry before scalarization/divisor specialization to source-to-Xi arithmetic annihilation.

Killed shortcuts: invariant positive trace and crossed-product vacuum coefficient are circular because positivity+invariance+non-erasure or star compatibility on centered eigenline already forces character unitarity.

Verification:
- direct lake env lean passed;
- targeted lake build module passed (9071 jobs);
- axiom audit only propext, Classical.choice, Quot.sound;
- no stale Route-R Lean process.
- repository-wide lint currently fails only on unrelated concurrently added modules missing umbrella imports; this new module is umbrella-wired and contains no forbidden declaration.
- External novelty boundary: det2 for Hilbert-Schmidt perturbations is parent theory; exact arithmetic threshold for actual prime essential edge is new internal result.
