# Frozen SD1 counterexample search

Target every integer 1<=M<=2^21, including small and endpoint cases. Reuse the independently
checked source arrays from the earlier complete-dilation experiment. Do not discard a finite
initial segment from the mathematical conjecture. SD1 is the fixed factor-one inequality
`S(M)^2<=sum_d mu(d)^2 K_d(M)^2` for the actual divisor source.

On each interval `d*q<=M<d*(q+1)`,

`K_d(M)=sqrt(d)c_q+D(q)sqrt(M)`, `c_q=A(q-1)-sqrt(q)D(q)`.

The diagonal is piecewise quadratic in sqrt(M). Accumulate jumps of its three coefficients at
every product d*q, retaining the complete integer incidence. A hyperbola split at sqrt(N)
allows the O(N log N) updates without N^2 endpoint work. Eight processes at most, BLAS1,120s cap.

Compare the recurrence at every previously stored endpoint with its independent direct diagonal.
Independently evaluate all apparent violations and the ten largest ratios. Treat M=1 (0/0) and
M=2 (exact equality) separately. A floating discrepancy near equality is not a counterexample.
No sign determined numerically may be imported into Lean as a proof certificate.

Record the entire ratio/source/diagonal vectors, not only a selected maximum. Download scripts,
results, audit and a compact report. Mathematical attacks on the all-scale inequality proceed
separately; a finite pass does not establish SD1.
