# Moving theta cutoff: first-Laguerre boundary-layer transition

- **ID:** LA-C5-20260929
- **Stage:** 2-fully-proven (paper); Lean transfer open
- **Type:** Candidate new theorem; no universal priority claim
- **Route:** LA, literal theta prefix versus complete arithmetic source
- **Parent log:** ../1-in-progress/la-frontier-conjecture-loop-2026-09-29.md

## Statement

Use the corpus normalization

`phi_n(x)=exp(x/2) 2pi(2pi n^4 exp(4x)-3n^2 exp(2x)) exp(-pi n^2 exp(2x))`.

Set `P_N=sum_(1<=n<=N) phi_n`, `F_N(t)=integral_(x>0) P_N(x) cos(tx) dx`,
`m=N+1`, and `L_N(t)=F_N'(t)^2-F_N(t)F_N''(t)`.
For every fixed real `lambda>4`,

`exp(2pi m^2) L_N(lambda m^2)
 -> 128pi^6(4pi^2-lambda^2)/(4pi^2+lambda^2)^4`.

Consequently `L_N(5m^2)>0` eventually and `L_N(8m^2)<0` eventually.
More generally the asymptotic sign is positive for `4<lambda<2pi` and negative
for `lambda>2pi`. No assertion is made at equality `lambda=2pi`, where the
leading term vanishes. This sharp moving-cutoff boundary strengthens the known
fixed-prefix obstruction: it exhibits a failure height proportional to the
square of the number of retained shells.

## Dependency-closed paper proof

### 1. One shell, exact coordinate

For `a=n^2`, substitute `v=a exp(2x)=a+u`. The existing exact incomplete-Gamma
coordinate yields, with `q_a(u)=a log(1+u/a)/2`,

`exp(pi a)/a integral_(x>0) phi_n(x) cos(lambda a x) dx
 = integral_(u>0) A_a(u) cos(lambda q_a(u)) du`,

`A_a(u)=pi exp(log(1+u/a)/4)
              (2pi(1+u/a)-3/a) exp(-pi u)`.

As `a->infinity`, `q_a(u)->u/2` and `A_a(u)->2pi^2 exp(-pi u)`.
For `a>=1`, `u>=0`,

`0<=q_a(u)<=u/2`,
`|A_a(u)|<=pi(1+u)(2pi(1+u)+3)exp(-pi u)`.

The first bound follows from `0<=log(1+u/a)<=u/a`. The second uses
`(1+u/a)^(1/4)<=1+u`, `a^(-1)<=1` and the triangle inequality. Thus for
`k=0,1,2` all frequency derivatives are dominated by one fixed polynomial
times `exp(-pi u)`. Dominated convergence, including the two differentiated
integrals, gives

`exp(pi a) a^(k-1) C_n^(k)(lambda a) -> H^(k)(lambda)`,

where `C_n` is the one-shell cosine transform and

`H(lambda)=integral_(u>0) 2pi^2 exp(-pi u) cos(lambda u/2)du
          =8pi^3/(4pi^2+lambda^2)`.

Derivative exchange follows from the same integrable polynomial majorants.
This proof uses ordinary dominated convergence and the exact exponential
Laplace integral, not a numerical approximation or certificate.

### 2. Complete omitted tail

Let `T_N=sum_(n>=m) C_n`. For `n=m+j`, the absolute value of each normalized
jet is bounded by

`B_k (1+j)^2 exp(-pi(2mj+j^2))`,

uniformly in `m>=1` and the real frequency. Indeed the scaling ratio is
`(m^2/n^2)^(k-1)`; it is at most one for `k>=1`, and for `k=0` at most
`(1+j)^2`. The polynomial integral majorants from step 1 give finite `B_k`.
For each fixed `j>=1` this bound tends to zero; it is dominated by the
summable sequence `B_k(1+j)^2 exp(-pi j^2)`. Dominated convergence on counting
measure removes every shell beyond the first omitted shell. Absolute
integrability justifies both the original source-series integral and the two
frequency-derivative exchanges. Hence

`exp(pi m^2) m^(2k-2) T_N^(k)(lambda m^2) -> H^(k)(lambda)`

for `k=0,1,2` and every fixed real `lambda`.

### 3. Full source is negligible for lambda>4

The existing near-line Xi bound is

`|XiC(z)|<=K(1+Re z)^3 exp(-pi Re z/4)`

when `|Im z|<=1/2`, `Re z>=2`. Cauchy estimates on a fixed disk of radius
less than `1/2` give the same exponential rate, times a fixed polynomial,
for derivatives of orders zero, one and two on the real axis. The complete
cosine source is a fixed nonzero scalar multiple of `XiC`; its three jets
therefore obey the same bound. If `lambda>4`, multiplication by
`exp(pi m^2) m^(2k-2)` leaves a polynomial times
`exp(-pi(lambda/4-1)m^2)`, which tends to zero.

Since `F_N=F_infinity-T_N`, the normalized prefix jets tend to `-H^(k)`.
Multiplying the three convergent scalar jets proves

`exp(2pi m^2)L_N(lambda m^2)->H'(lambda)^2-H(lambda)H''(lambda)`.

### 4. Exact sign and positive survivor

For `D=4pi^2+lambda^2`, differentiation gives

`H'=-16pi^3 lambda/D^2`,
`H''=16pi^3(3lambda^2-4pi^2)/D^3`,
`H'^2-HH''=128pi^6(4pi^2-lambda^2)/D^4`.

The denominator is strictly positive. Thus the sign boundary is exact.
The constants `5` and `8` use the analytical bounds `3<pi<4`; no computation
of a theta integral or zero is used. The positive survivor is the complete
three-jet tail profile and its exact sign classification, not only a negative
prefix statement. The full arithmetic source remains outside this no-go.

## Novelty and limits

Existing corpus proves fixed-cutoff boundary asymptotics and infinitely many
nonreal zeros of every finite prefix. Haglund's 2009 paper analyzes fixed
incomplete-Gamma sums. Searches for a moving shell cutoff, the square-height
scaling, and this Laguerre transition found no matching theorem. This is a
candidate novelty assessment, not proof of absence from all literature or
training data. Ordinary Laplace boundary-layer methods are established tools;
the claimed new content is this joint-cutoff three-jet law and its exact
first-Laguerre transition for the literal theta source.

No result here proves or falsifies RH. The theorem restricts one live
approximation route and identifies its precise surviving scaling boundary.

## Lean ledger

- Existing inputs: `ThetaCuspShellIncompleteGammaCoordinate` (exact coordinate),
  `XiCTaylorThetaTailDensityAtoms` (atom integrability),
  `XiOnLineZeroLocalBounds` (near-line exponential bound).
- `ThetaMovingShellBoundaryLayer.lean`: direct Lean check passed for the
  all-order normalized Gamma-coordinate jet limit and frequency-uniform bound.
  Targeted `lake build --old GaloisForLFunctions.RHTower.ThetaMovingShellBoundaryLayer`
  passed (one new leaf, 27 seconds); no axiom audit yet.
- Open transfer: exact literal-shell connector; omitted-tail domination;
  full-source derivative decay; exact limit and unconditional 5/8 capstones.
- No Lean certificate yet; no axiom audit claim.
