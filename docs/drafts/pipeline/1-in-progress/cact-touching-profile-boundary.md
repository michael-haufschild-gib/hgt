# Profile boundary vanishing at touching

## Mathematical question

Can the separated matrix estimates reach c=1 without losing the actual source?
Two apparent degeneracies should be separated: the charge was bounded by c,
and the cross-integral error used a worst-point distance (1-c)^-2.

## Established inputs

- CompleteWeilEnergyControlsThePrimeDefect retains a prime-defect coefficient
  (1-c)/4 after replacing the actual pole charge alpha=c*(integral phi)^2/M by c.
- TheAtomCrossReplacementHasUniformErrors bounds the normalized cross error by
  38*(integral |phi|)^2/(M*(1-c)^2), before summing reciprocal integer distances.
- TheRowsAtBoundedOverlap gives the exact non-ratio prime correction at every
  width. No actual overlapping source sign estimate has been supplied.

## Proposed mechanism; not a proof claim

Retain the actual charge alpha in the Young estimate. A coefficient
(1-alpha)/4 survives, with Young parameter 2/(1-alpha); alpha can equal zero.
For every fixed nonzero continuous compact profile on [0,1], strict
Cauchy-Schwarz should give q=(integral phi)^2/M<1. This removes the charge
coefficient's apparent degeneration at c=1, but not the cross-error issue.

For the cross error, a C1 profile vanishing at both endpoints satisfies
|phi(u)|<=L*min(u,1-u) on [0,1]. In the potentially singular corner u near1,
v near0, the product is at most L^2*(1-u)*v. The denominator has the form
(d-w+w*(1-u+v))^2. When d>=w the endpoint product cancels this singularity.
For d>=2w retain the usual w^2/d^2 estimate; for w<=d<=2w use boundary
vanishing and then w^2/d^2>=1/4. This suggests one profile-dependent cross
error constant uniform up to touching, including a reciprocal integer-square
majorant. Actual cross-integral formula and admissible integrations must be
checked before formalization.

At width1/N all distinct log nodes in [1,N] are still separated: their loggap
exceeds1/N. The existing atomSpacing lower bound is conservative. Non-ratio
prime lags can first enter through a product just outside N; these are a
separate actual-source error and cannot be omitted. For c>1 genuine support
overlap requires the renormalized Gram contribution too; the separated
cross-integral formula cannot be continued through its singularity alone.

## Required success criteria

Prove a uniform actual cross-error estimate, then discharge the boundary
non-ratio source and full spectral transfer. A charge-only refinement or a
padded narrow profile is not an endpoint/overlap positivity theorem.

## Status

New analytic investigation. No theorem claimed and no new Lean file yet.

## Refined cross-error estimate

A Lipschitz bump g on [0,w], vanishing at its endpoints, has
 |G_g(z)| <= (L_g^2*w/4)*(w-|z|)^2   (|z|<=w).
Pointwise this is the product of the two endpoint distances; its integral
requires only the interval length w, so no plane change of variables is needed.
For s>w, the density increment is at most 38w/(s-|z|)^2. Hence the weighted
error integrand is at most (38/4)L_g^2*w^2 uniformly in s-w. Integration over
[-w,w] gives cross error <=19 L_g^2*w^3.
For g(u)=phi(u/w), L_g=L_phi/w, and normalization by w*M yields
19 L_phi^2/M. If s<=2w this is at most 76 L_phi^2/M * w^2/s^2.
If s>=2w the existing far estimate is at most
152 (integral|phi|)^2/M * w^2/s^2.
Thus C_phi=76*(L_phi^2+2*(integral|phi|)^2)/M is a candidate global
reciprocal-square coefficient for every s>w, with no (1-c)^-2 divergence.
This is a proof plan, not a verified theorem. Remaining formal work: endpoint
values, autocorrelation bound, exact translated integral, then normalized rows.

## Arithmetic boundary at c=1: proposed exact classification

For N>=2, integers1<=m,n<=N and k>=2, a non-ratio lag inside width1/N can occur only
when m=N and kn=N+1 (or the transposed term). Reason: among unequal positive
integers a,b with min(a,b)<=N, a loggap below1/N forces the consecutive pair
N,N+1. Any pair wholly inside1..N has loggap>1/N; a pair with gap>=2 or outside
N+1 also exceeds1/N. This uses strict log(1+x)>x/(1+x), not a numerical check.

If formalized, the non-ratio form is one boundary star:
 2*G_g(log((N+1)/N))*x_N*sum_{k|N+1,k>=2} Lambda(k)/sqrt(k)*x_{(N+1)/k}.
The divisor identity sum Lambda(k)=log(N+1) bounds its operator norm.
The overlap length w-log(1+w) is <=w^2/2 forw=1/N; even a bounded profile gives
normalized star error O(log(N+1)/N). Endpoint Lipschitz decay strengthens this
to O(log(N+1)/N^2) with the coarser quadratic autocorrelation estimate.
All terms must be included in the exact source; atom-atom separation alone did
not justify dropping this star.

A complete endpoint proof would then combine: uniform crosserror; strict
profile charge q<1; self/pole endpoint bounds; boundary-star disappearance;
and full bounded-spectrum exhaustion using the retained prime-defect fraction.
The present c<1 proof cannot be extended merely by taking a pointwise limit
in c after N. None of these new endpoint conclusions has yet been formalized.

## Strict charge and uniform reserve: analytic plan

For a nonzero continuous profile supported in[0,1], let I=integral(phi),
M=integral(phi^2). The exact variance on[0,1] is M-I^2. If I=0 this is positive;
if I!=0, phi(0)=0 makes (phi(0)-I)^2>0, and continuity gives a strictly positive
variance integral. Hence q=I^2/M<1. Mathlib intervalIntegral.integral_pos
accepts a positive value at either endpoint of a nondegenerate interval.
This is a strict statement for each fixed profile, consistent with q_eta->1.

Retaining alpha=c*q in the existing center Young estimate gives a positive
prime-defect coefficient (1-alpha)/4. For allc<=1 one may instead choose the
single reserve epsilon=(1-q)/4 and Young parameter2/(1-q), independent ofc.
The new cross bound would be uniform in this range; the pole/self errors also
need their endpoint versions. Together with the boundary-star estimate this
suggests uniform coercivity through touching. A separate complete spectral
argument is still required; these are proposed deductions, not completed results.

## Stronger bounded-width variant to investigate

Corpus search found AIP/CubicGaugeSurplusPotential.archLevyDensity_le_inv:
 omega(t)<=1/(2t)+1/4 for everyt>0. Together with the elementary overlap bound
|G_g(z)|<=B^2*(w-|z|), this can remove derivative dependence at0<w<=1.
Indeed |omega(s+z)-omega(s)|<=1/(2(s+z))+1/(2s)+1/2. Multiplication by
B^2*(w-|z|) costs at most3B^2/2 since s>w andw<=1. Integration costs3B^2*w.
After normalizing g=phi(u/w), the near-touching error is<=3B_phi^2/M, hence
<=12B_phi^2/M*w^2/s^2 when s<=2w. Combine with the far bound152I_abs^2/M.
This would be uniform for plateau transitions shrinking to0 (B_phi<=1,
M boundedbelow), unlike the Lipschitz constant. Existing draft's all-width
Lipschitz theorem remains useful and is being checked first; this bounded-width
variant is not yetwritten or proved. Original source estimate, not numerical work.
