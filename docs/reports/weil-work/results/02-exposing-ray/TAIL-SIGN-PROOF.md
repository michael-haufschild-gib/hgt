# Literal exposing tail: sign and exponential scale

Status: dependency-closed paper argument and Lean formalization verified. Final installed leaf audit exits 0 without warnings; the eight capstone axiom audits show only propext, Classical.choice and Quot.sound. The universal dual lower bound remains open.

## Exact conjecture

Let w(n) be the existing `exposingWeight`, with c_k=1/(k+1) and a_k=1/(2 cosh(c_k/2)). Then w(n)>0 eventually and

    log(w(n))/n -> -2*pi*exp(-2).

Consequently, for every r with 0<r<2*pi*exp(-2), the existing box tail is bounded by C_r exp(-r N). Every finite cutoff has a strictly positive tail. No numerical estimation is needed.

## Source bounds and normalization

Write Phi=`riemannKernelReal` and K=`riemannKernelAutocorr`. Corpus definitions give K(y)=integral Phi(t)Phi(t-y) dt. The leading theta term is bounded below by 2*pi^2*exp(-pi*exp(2|t|)); this follows from `riemannLeadTerm_ge`, since its remaining exponential factors are at least one. The proved theta threshold gives Phi(t)<=C_d exp(-d exp(2|t|)) for every 0<d<pi.

Fix 0<c<pi and choose d between c and pi. From x*exp(-(d-c)x)<=1/(d-c), x=exp(2|t|), obtain

    Phi(t) <= B_c exp(-c exp(2|t|)) exp(-|t|).

The arithmetic-geometric mean inequality and |t|+|t-y|>=|y| give exp(2|t|)+exp(2|t-y|)>=2exp(|y|). Integrating the product and discarding one factor exp(-|t-y|) yields

    0<K(y)<=2 B_c^2 exp(-2c exp(|y|)).

For b>2*pi choose delta=log(b/(2*pi))/2>0. If y>=2delta and |t-y/2|<=delta, both |t| and |t-y| are at most y/2+delta. The leading-term lower bound on this interval of length 2delta yields

    K(y)>=2delta*(2*pi^2)^2 exp(-b exp(y)).

Thus log K(y)/exp(y) tends to -2*pi. This argument uses actual theta bounds, not an assumed kernel asymptotic.

## Outermost-shift dominance

Expand the literal polar operator:

    P_c^2 K(y) = (1+2a_c^2)K(y)
      -2a_c(K(y-c)+K(y+c))
      +a_c^2(K(y-2c)+K(y+2c)).

Here 0<a_c<=1/2 for 0<c<=1. Every summand except the displayed negative pair is nonnegative. The k=0 term has c=1 and supplies a_1^2 K(y-2), while every negative term has displacement at most one. The geometric k weights sum to two. Existing absolute summability legitimizes summation of these estimates.

An upper bound on every shift (displacement at most two) gives |w(n)|<=C_c exp(-2c*exp(-2)*n) for all sufficiently large n. For a lower bound, retain a_1^2 K(log n-2) from the positive terms and bound the full negative sum by C_c exp(-2c*exp(-1)*n). Choose b>2*pi and c<pi so that b<2c*exp(1). Then

    w(n)>=D_b exp(-b*exp(-2)*n)
             -C_c exp(-2c*exp(-1)*n).

The second rate is strictly faster. Eventually it is less than half the first term. This proves eventual strict positivity. Taking b down to 2*pi and c up to pi proves the stated logarithmic rate. The second copy of the kernel at -log n causes no sign problem: its negative terms obey the same bound and all its positive terms can be dropped. No evenness identity is needed for the lower estimate.

## Tail and relevance

The tail summands are (log n+boxConst)|w(n)| for n>N and n>=2. Absorb the logarithm into an arbitrarily small loss in the exponential rate, then sum a geometric series. A sufficiently large n>N has w(n)>0 and log n+boxConst>0, so the tail is strictly positive.

This sharpens the existing repair budget and identifies the sign of the actual ray at all sufficiently large integers. It supplies no lower bound for the energy of arbitrary matched families. In particular, exponential smallness of the allowed deficit makes that remaining source estimate more demanding, not automatic.

## Attack and novelty audit

Potential cancellation was retained: the only negative shifts have size at most one, strictly less than the positive outer shift of size two. Arbitrarily small c_k do not erase this gap; their total coefficient mass is summable. All constants are independent of k. Small integer coefficients may have either sign; no claim is made about them.

Parent mechanism: elementary Laplace bounds for the theta autocorrelation and dominance of separated exponential scales. External search found Pólya-like theta-kernel approximations (arXiv:1502.06844) and Bessel-K representations (arXiv:1710.09987); these do not by themselves establish novelty or the literal exposing-weight theorem. Corpus searches were partial in several retrieval stages; absence of a prior result is not certified. Scientific classification pending exact-source and Lean audits.

At N comparable to exp(2A), the tail therefore has scale exp(-r exp(2A)) for every subcritical r. This explains why fixed-order aperture errors cannot directly meet this literal tail budget. It is not a necessary precision barrier for every RH proof: the existing compactness argument can be adapted to slack tending to zero, after which RH supplies the exact receiver. That adaptation is a paper observation here, not a newly claimed Lean theorem.

The Lean proof derives the subcritical envelope directly from `riemannKernelReal_sandwich`: with X=exp(2|t|), absorb X^3 using X^3*exp(-(pi-c)X)<=6/(pi-c)^3. Thus it needs no additional theta-threshold import.
