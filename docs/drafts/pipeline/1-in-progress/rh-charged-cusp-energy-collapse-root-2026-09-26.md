# Complete-source energy collapse at a charged cusp

- **ID:** RH-CHARGED-CUSP-ENERGY-COLLAPSE-ROOT-20260926
- **Stage:** 1-in-progress
- **Type:** [BRIDGE] frozen source-specific conjecture and comparison test
- **Owner:** root
- **Parent:** `../5-failed/rh-reflection-compatible-comparison-root-2026-09-26.md`

## Frozen C10

Let Phi be the complete theta source, z_N=log(N^(-2)+2i)/2, and J the
already formalized complex Hermitian realization, equal to 2K on real nodes.

**Conjecture:** J(z_N,z_N)/|Phi(z_N)|^2 tends to zero as N tends to infinity.
More intrinsically, the horizontal source section normalized by its value at
z_N tends to zero in the weighted L2 norm with weight 1+s on s>0.

Public meaning: exact arithmetic phase alignment creates a point value that
outgrows its full integrated energy. No numerical experiment is proposed.
The claim is a bridge, not a new universal law or an RH proof.

## Evidence and whole-route relevance

C9 proves |Phi(z_N)|>=A*N^5 and |Phi(z_N+s)|<=486*N^5*exp(-s/2).
These only bound the normalized energy; they do not make it vanish.
The full source has quadratic phases exp(-2*pi*i*n^2*t), t=exp(2s).
On a compact t interval the integrated pairs have denominators n^2-m^2;
|n^2-m^2|>=(n-m)^2 gives summable row bounds. The Gaussian diagonal has
scale N^9 rather than the aligned point's N^10.

A proof would constrain every analytic scalar feature dominated by K on a
real tail: its ratio to Phi must vanish at the charged cusp. In particular,
adding a bounded nonzero boundary rate to C9's failed Cauchy reference cannot
repair it. This tests a class of repairs rather than another chosen constant.
It still supplies no sign for unsubtracted K; source-specific all-rank
positivity remains the RH-strength obstacle.

## Interrogation

- Where is the complete source used? Exact quadratic phases and full Gaussian
  sum; no first-atom replacement.
- What was being removed? Relative arithmetic phases. Keep them through the
  integral before taking absolute values.
- What changes representation? Normalize an actual Hilbert-space section by
  its point value, then test strong convergence, instead of comparing only
  pointwise envelopes.
- Closest parents: C9 Gaussian growth, exact diagonal integral, analytic
  boundary admissibility; general oscillatory mean-value estimates.
- Unoccupied assertion: disappearance of the normalized full integrated
  energy, not a renamed existing positivity receiver.
- Right problem? Useful only if it closes the complete-source limit and its
  all-feature consequence. A generic finite-sum lemma alone is insufficient.

## Proof/falsification plan

1. Prove a rank-uniform mean-square bound for damped quadratic-frequency
   sums on compact intervals. Keep damping inside the exact pair integral.
2. Pass to the complete Gaussian sums and obtain the N^9 compact bound.
3. Use C9's integrable N^10 envelope for the remaining horizontal tail;
   first take N to infinity on a fixed compact interval, then its endpoint
   to infinity. No unjustified exchange of moving limits.
4. Divide by C9's N^10 point-value lower bound and apply scalar boundary
   admissibility. Freeze any stronger consequence separately.
5. Scratch verification at default limits, named leaf audit, all public
   axiom reports, umbrella wiring, formal lint; record facts in root log.

## Corpus and method audit

Deep searches `quadratic exponential sums integrated mean square separated
frequencies Gaussian damping` and `method prove oscillatory Laplace integral
mean square sum using frequency gaps integration by parts` completed.
Source inventory complete; compiler metadata mostly pending/stale.
`GeneralizedDirichletMeanValue` supplies exact undamped finite-pair integrals;
`OscillatoryIntegrationByParts` supplies derivative-controlled bounds.
Neither retrieved statement proves the damped complete-source limit.
Search artifacts: `/tmp/rh-c10-quadratic-deep.json`,
`/tmp/rh-c10-method-deep.json`. No global priority claim.

## Falsifiers / failed shortcuts

C9's pointwise N^10 bound alone cannot prove C10. Extending individual
weighted Gaussian pair integrals to t=0 before combining terms may lose
cancellation and destroy absolute summability; retain t>=1 throughout.
A positive lower limit of normalized energy would falsify C10; inability
to formalize or a failure of one estimate would not.

## Dependency-closed paper proof of C10

Write Cq=sum_(j in Z) 1/j^2, with the zero term interpreted as zero.
For a>=0, b!=0, T>=0 and summable complex coefficients c_n, expand the
mean square of sum c_n*exp((-a+ib)n^2*t). The diagonal pair integral has
norm at most T. For n!=m the exact exponential primitive bounds it by
2/(|b|*|n^2-m^2|). Since n,m>=0,
(n-m)^2<=|n^2-m^2|. Mapping m to m-n injects each row into Z, giving
row bound Cq. Young's inequality and symmetry therefore bound the whole
integral by (T+2*Cq/|b|)*sum |c_n|^2. Uniform absolute convergence (or
dominated convergence on [0,T]) justifies the complete sum.

Set a=pi/N^2, b=-2*pi, and
c_(N,k,n)=n^k*exp((-a+ib)n^2). Its squared coefficient energy is the
complete Gaussian sum with exponent 2k and parameter 2*pi/N^2. C9's
integral-test estimate gives the exact bound

    sum |c_(N,k,n)|^2 <= k!/(2*pi^k)*N^(2k+1).

Let G_(N,k)(u)=sum c_(N,k,n)*exp((-a+ib)n^2*u). On s in [0,S] put
u=exp(2s)-1. Then du/ds=2*exp(2s)>=1, so the integral of
|G_(N,k)(exp(2s)-1)|^2 over [0,S] is at most its u-integral over
[0,exp(2S)-1]. Thus it is bounded by B_(S,k)*N^(2k+1), with B_(S,k)
independent of N.

For Q=N^(-2)+2i the literal source identity is

    Phi(z_N+s)=exp((z_N+s)/2)*[
      4*pi^2*Q^2*exp(4s)*G_(N,4)(exp(2s)-1)
      -6*pi*Q*exp(2s)*G_(N,2)(exp(2s)-1)].

C9 gives 0<=Re z_N<=1 and |Q|<=3. Every displayed prefactor is bounded
on [0,S], uniformly in N>=1. Squaring with |v+w|^2<=2|v|^2+2|w|^2
and using N^5<=N^9 gives integral_0^S |Phi(z_N+s)|^2 <=B_S*N^9.
Consequently the actual normalized diagonal density

    F_N(s)=4*(Re z_N+s)*|Phi(z_N+s)|^2/N^10

has integral over [0,S] tending to zero for every fixed S>=0. C9's
horizontal bound and (1+s)*exp(-s)<=3*exp(-s/2) give, for every s>=0,

    0<=F_N(s)<=12*486^2*exp(-s/2).

Given epsilon>0 choose S with the majorant tail below epsilon/2, then N
large enough that the compact integral is below epsilon/2. This proves
J(z_N,z_N)/N^10->0 without interchanging two moving limits. Finally C9's
|Phi(z_N)|>=A*N^5, A=12*pi^2*exp(-4*pi)>0, implies

    0<=J(z_N,z_N)/|Phi(z_N)|^2<=A^(-2)*J(z_N,z_N)/N^10->0.

The identical proof with weight 1+s proves the normalized weighted-L2
version. No RH hypothesis or source sign assumption is used.

**Lean status:** the rank-uniform damped finite and infinite mean-square
bound, coefficient summability, and exact Gaussian energy bound compile in
`ThetaCuspQuadraticMeanSquare`; its required named dependency build passes.
`ThetaCuspChargedSourceMeanSquare` closes horizontal clock substitution,
literal full-source identification, and the compact N^9 bound; its named
build passes. The final C10 limit is not yet Lean-closed.
