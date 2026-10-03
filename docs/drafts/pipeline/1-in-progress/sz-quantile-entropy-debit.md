# SZ: finite total entropy debit of the actual quantile cells

Status: paper mechanism complete; Lean audit pending. RH remains open.

The hard target remains the signed Gamma--prime--polar gap on canonical
heads. This ingredient concerns its literal outgoing quantile cells, not
an approximation to the complete Gamma reservoir or a new RH criterion.

Write w_n = criticalMellinAtomWeight n, M_n = sum_(j<n) w_j,
b_n = 2 log(1+M_n/2), and define

    D_n = integral_[b_n,b_(n+1)] exp(h/2) (h-b_n) dh.

Conjecture: D_n is nonnegative and summable over all actual arithmetic
cells. Its sum is the finite positive price of replacing each integrated
cell centroid by its left boundary. The signed node displacement must
retain that price.

Paper proof: exact cell mass is w_n, so

    0 <= D_n <= w_n (b_(n+1)-b_n)
              <= 2 w_n^2/(2+M_n).

The last step is log(1+x)<=x. Existing source theorems give w_n<=2 for
n>0 and M_(n+1)>=c sqrt(n) eventually, c=log(2)/2>0. Hence the last
denominator is at least c sqrt(n). The corpus already proves summability
of w_n^2/exp(log(n)/2). This proves summability of D without an RH,
source-sign, or cancellation premise.

The exact signed identity to retain is

    integral_cell exp(h/2)(log(n)-h) dh
      = w_n(log(n)-b_n)-D_n.

Thus complete finite-block barycentric displacement differs from the
left-node signed current by a convergent nonnegative correction. This
does not prove the remaining left-node current has a floor, or pay the
canonical-head Gamma gap. The full checkpoint reservoir's Legendre
conjugate is not substituted by the exponential quantile conjugate.

Corpus searches: phase1191511, canonical1191548, midpoint1191582,
checkpoint1215392, entropy1215412. Most were partial/source-only;
checkpoint1215392 reported complete retrieval but not compiler freshness.
No absence or novelty claim follows from these searches. Source reads
verified the exact cell mass, cumulative lower bound, weight ceiling and
summable square-weight theorem used above.
