# Remove the finite head from the actual Haar Weil payment

- **ID:** acs-low-haar-head-payment
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Target:** Prove nonnegativity of `roughWeil (haarSectionProfile d X)`
  for every signed coefficient family d and every horizon X, including
  the finite low-index head.

## Current evidence

`exists_haarTail_roughWeil_floor` proves a uniform mass floor above one
fixed lower index. Its proof pays the full actual prime sum and both pole
moments, but its coarse outgoing-row constant leaves the head untreated.

`exists_uniform_finite_head_for_haar_prime` now approximates the entire
prime diagonal by a literal finite coefficient head, within ε times the
original complete-profile Gamma energy. The corresponding nonfirst mixed
source retains any complete Gamma share below one after a head.
Neither theorem pays the remaining head or its interaction with the tail.

## Concrete diagonal payment

First discharge the actual diagonal at every index, including index one.
For adjacent widths u,v, put w=u+v, M=uv/w and let E(s) be Gamma energy
per unit mass of an interval indicator of width s. Quadratic polarization
gives the exact normalized balanced energy E(u)+E(v)−E(w).

The corpus supplies the exact interval exterior kernel, elementary bounds
on its antiderivative, and polynomial bounds on its first moment. These
give

`Gamma(h)/M + 2*gammaHardyPhaseRate(0)
 ≥ 1−gamma_E−log(2*pi*M)−w^2/16−5*w^3/192`.

For the actual pairs, w≤log(2) and M≤w/4. Mean zero and support width w
also bound the adverse pole product by `−w^3*exp(w)*M/8`. These estimates
are intended to establish a positive diagonal without excluding any
coefficient index. The prime diagonal of one Haar atom is exactly zero.
All statements in this paragraph remain under formalization; positivity
of arbitrary signed sums still requires the cross-pair terms.

## Investigation

Seek a direct shared Gamma–prime–pole payment on all actual Haar cells.
Examine the exact Gamma kernel on mean-zero pairs, exact outgoing prime
rows, and the actual two exponential moments. An all-head conclusion
must preserve cross terms, not combine separate diagonal inequalities.

No all-head positivity claim is established. No numerical experiment,
web search, novelty check, or axiom check is authorized. If this target
fails, record its precise obstruction and extract the strongest actual
positive payment before retiring it.

Even a successful all-Haar theorem leaves first-prime coarse/detail
mixing and the coarse signed source open; it would remove one actual
finite-head cost, not close full ACS.
