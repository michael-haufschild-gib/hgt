# Exploratory aperture profile, frozen before execution

C2 passes all original bands. Preserving multiplication by 2 and 3 reduces ensemble mean square,
but adding constraints through 31 increases it again. This is an observed effect, not a new
monotonicity conjecture. Locate its source without interpreting every change as progress.

Use endpoints `M=2^e+i*2^(e-6)`, `e=12,16,20`, `i=0,16,32,48`. Use the fixed cutoffs
`1,2,3,5,7,11,16,32,64,...,2^21`, skipping cutoffs larger than M and appending M.
Retain actual squarefree support and the same rough-part ensemble. At every cutoff record:

- total ensemble mean square `sum B_r^2`;
- deterministic smooth-fiber mean `B_1` and squared mean `B_1^2`;
- centered ensemble variance `sum_(r>1) B_r^2`;
- actual complete source and the signed rough remainder `S-B_1`;
- the maximizing recorded cutoff (only among this prescribed grid).

This is a diagnostic profile, not a held-out test or a fitted asymptotic scaling law. Report all
endpoints, including unfavorable shapes. A peak does not establish a universal transition scale.

For an inserted prime p, old squarefree rough fibers r and p*r merge, so the exact finite change
in mean square is `2 sum_r B_r B_(p*r)`, with `p` not dividing `r`. Audit this identity at p=5,
M=4096, and check that point using an independent 60-digit implementation.
