# Exact cancellation of the short triangular head

- **ID:** MC-C12.99
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; paper argument below, Lean connection pending
- **Source:** `LiouvilleTriangularShortHead.squareTriangle_remainder`, `MertensSquareRootOmega`, `LiouvilleDirichletSeries`, and the exact hyperbola reconstruction in MC-C12.98.
- **Statement:** An uncancelled nonzero multiple of the actual short head forces both signs above every power below three quarters. The full source must retain the exact combination `P=2A-B`.

## Hard target and assessment

Route MC still requires `P(x) >= -C_epsilon*x^(1/2+epsilon)`. The preceding short-head theorem excluded separate absolute estimates of A. This attempt addresses a remaining, stronger possibility: paying the quadratic term B separately by a one-sided critical estimate. No bound for P is asserted.

## Source definitions

For x>=1, let U=floor(sqrt(x)), Z=sum_(n>=1)1/n^2, and

```
W(y) = sum_(n^2<=y)(y/n^2-1),
A(x) = sum_(m<=U) mu(m) W(x/m),
P(x) = sum_(n<=x) lambda(n)(x/n-1),
a = one * squareIndicator,
B(x) = sum_(m,n<=U) mu(m)mu(n) W_a(x/(mn)).
```

The coefficient identities mu*a=squareIndicator and mu*mu*a=lambda give
`P=2A-B`. Terms with both m,n>U vanish since mn>x. This retains the complete square kernel and every admission boundary.

## Candidate and positive survivor

For every nonzero real c, set `F_c=P+c*A`. For every beta<3/4 and C>0, conjectured conclusion:

```
frequently at infinity, F_c(x) > C*x^beta,
frequently at infinity, F_c(x) < -C*x^beta.
```

The choice c=-2 gives F_c=-B. Thus neither sign of B can be paid separately at any exponent between one half and three quarters. This is not a statement about an arbitrary coefficient matrix.

The positive survivor is an exact holomorphic remainder decomposition and its uncancelled pole: the moving cutoff sends a zero rho to (1+rho)/2, and at least one such pole survives in F_c whenever c!=0. The complete combination cancels this whole shifted-pole term identically. No claim that the remaining original zeta poles disappear is made.

## Paper derivation under audit

Define r(y)=W(y)-Z*y+2*sqrt(y). The existing Lean theorem gives |r(y)|<=1 for y>=1. Hence, exactly,

```
A(x) = Z*x*sum_(m<=sqrt(x))mu(m)/m
       -2*sqrt(x)*sum_(m<=sqrt(x))mu(m)/sqrt(m) + E(x),
E(x) = sum_(m<=sqrt(x))mu(m)*r(x/m),
|E(x)| <= floor(sqrt(x)).
```

E is measurable: every term and the floor cutoff are measurable. Its Mellin transform
`R(s)=integral_1^infinity E(x)*x^(-s-1) dx` is holomorphic for Re(s)>1/2 by domination on compact sub-half-planes. For Re(s)>1, absolute summation and integration give

```
M_A(s) = Z/((s-1)*zeta(2s-1))
         -2/((s-1/2)*zeta(2s-1/2)) + R(s),
M_P(s) = zeta(2s)/(s*(s-1)*zeta(s)).
```

For example, the first head integral starts at x=m^2, so its m-th contribution is
`Z*mu(m)*m^(1-2s)/(s-1)`. This lower endpoint is essential. The second contribution is
`-2*mu(m)*m^(1/2-2s)/(s-1/2)`. All errors remain in R.

Consequently the continued transform of F_c is

```
Q_c(s) = zeta(2s)/(s*(s-1)*zeta(s))
         + c*Z/((s-1)*zeta(2s-1))
         - 2*c/((s-1/2)*zeta(2s-1/2)) + c*R(s).
```

It is analytic at every real s>1/2: zeta has no positive real zero; at s=1 the apparent factors are removable using (s-1)zeta(s)->1 and (s-1)zeta(2s-1)->1/2. No zero-free assertion off the real axis is used here.

Suppose either sign of F_c has an eventual upper bound C*x^beta, with 1/2<beta<3/4. Add a compact correction and increase C by one to obtain a nonnegative density dominating x^beta. It has finite Mellin abscissa in [beta,2] since the source has polynomial growth. Landau's theorem and the real-axis analyticity just established force that abscissa to be beta. Thus M_Fc would be holomorphic throughout Re(s)>beta.

Now start with a critical zero rho=1/2+i*gamma, gamma!=0, supplied by the corpus's Hardy theorem. Put w=(1+rho)/2. If zeta(w)!=0, then the c*Z term in Q_c has a genuine pole at w. The other terms are analytic there: zeta(rho+1/2)!=0 on Re=1, zeta(2w) is regular on Re>1, and R is holomorphic. If zeta(w)=0, repeat with rho replaced by w. At every iteration rho has Re>=1/2, Re<1, and nonzero imaginary part, while zeta(rho+1/2)!=0 on Re>=1. Iteration cannot consist entirely of zeros: rho_k=1+(rho_0-1)/2^k tends to1, where the analytic residue unit (s-1)zeta(s) is nonzero. Therefore an uncancelled pole exists with Re(w)>=3/4>beta, contradicting that holomorphic continuation.

Apply the argument to both signs. Smaller beta follow by comparison with a beta in (1/2,3/4). The statement only rules out a separate estimate; it does not give the bound for P. The general c formulation records the rigidity of the exact cancellation, rather than another generic PSD obstruction.

## Lean obligations and no-go status

- DONE: unconditional shifted-zero separation and exact pole-coefficient rigidity, audited in `LiouvilleTriangularPoleSeparation`. See `../../../3-formalized/mc-triangular-shifted-pole-separation.md`.
- Formalize the real-cutoff decomposition and the two exact Mellin formulas.
- Transfer Landau to this actual source and prove both cofinal sign statements.
- Audit the full positive survivor and sign theorem before retiring the separate-payment construction.

No no-go is retired yet. No Lean proof of this card's new conclusion is claimed.

The new leaf proves the complete analytic three-term model has an actual point of nonanalyticity unless its shifted short-head coefficient vanishes. It does not yet identify that model with the Mellin transform of the physical sum. For `F_c`, the model parameters are exactly `a=2*c*Z`, `b=-2*c`, `d=1`; the remainder is `c*R`. More generally, `u*A-v*B=v*P+(u-2v)*A` can only avoid the proposed obstruction on the line `u=2v`. This necessity is the proposed source-level rigidity law, not a bound along the surviving line.

## Search audit

2026-10-04, turn1005s: documented deep search `Mobius short triangular quadratic Mellin pole cascade Landau oscillation Liouville` completed with exit0, partial=false. Snapshot65311 files, compiled43, stale2660, pending49246; snapshot/current generation1224224/1224230, query index1224219; semantic coverage unmeasured, older-generation warning, background refresh incomplete. Candidate lemmas, source arguments, empty proof ideas and generated ingredient sets inspected. Hits establish the previous short-head asymptotic and unrelated quadratic identities; no retrieved hit establishes this pole-cancellation argument. An exhaustive source-text search for the displayed half-shift expression found no directly applicable declaration. Novelty claim is limited to this inspection, not the entire mathematical literature.

## Log

- 2026-10-04 — Created during1005s after the joint positivity and rough-prime attempts left their signed remainders uncontrolled. Paper derivation written for audit; formal work pending.
- 2026-10-04 — Analytic separation step formalized and audited. Targeted build, required direct leaf audit and two standard-only axiom checks passed. The actual-source Mellin/remainder/Landau connection remains the next obligation; the full MC lower bound is unchanged.
- 2026-10-05 — Source connection, Mellin formulas, remainder holomorphy and the Landau sign argument formalized and
  audited (Opus): `LiouvilleTriangularHeadOscillation.frequently_gt_and_frequently_lt`, card
  `../../../3-formalized/mc-triangular-head-supercritical-oscillation.md`. The separate-payment construction is excluded
  at every exponent below 3/4; the critical lower bound for P = 2A − B remains open.
