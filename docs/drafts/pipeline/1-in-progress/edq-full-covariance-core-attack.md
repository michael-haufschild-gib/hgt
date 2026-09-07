# EDQ full covariance: complete-column bound and compensated double tail

Stage: 1-in-progress. Primary target remains an unconditional proof or falsification of RH through EDQ.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Hard target and work constraint

Prove an actual cofinal subpower ceiling in the preserved inner cutoff X for
the complete averaged current, or for a full compensated arithmetic energy
that supplies it. This card does not replace that target with another receiver.
The proposed additional Hardy-transfer module is not being written. Further
formal infrastructure must follow a successful attack on the missing bound,
not serve as the main output while that bound remains untouched.

## Direct proof attempt: Graham followed by Cauchy

Use the actual error increments c(k)=[k=1]-g(k)+H, with
g(k)=(b_M(k)-b_X(k))/(log M-log X). Their cumulative sum is the literal
target error. Cauchy gives

`E_T <= sum_(j<=T)c(j)^2 * sum_(n=j..T)1/(n+1)`.

Thus even a mean-square bound `sum_(j<=t)c(j)^2<=A*t+B` supplies a term of
order A*T after summation, as well as a boundary/error cost. The simpler
bound by `(1+log(T+1))*sum_(j<=T)c(j)^2` already makes the loss explicit.
For T>=M the inspected Graham theorem supplies
`sum g(k)^2 <= 2*(B(M,T)+B(X,T))/L^2`, with
`B(Y,T)=4*C^2*T*(1+log Y)+(Y*log Y)^2` and L=log M-log X.
Including the actual compensation gives
`sum c(k)^2 <= 3+3*T*H^2+3*sum g(k)^2`.
The complete tail also retains its bound `(M+1)^2/(T+1)`.
These estimates do not yield the required subpower inner-scale ceiling.
The failed step is replacing the signed cumulative correlations by individual
squares. This rejects this direct estimate as a proof, not the arithmetic
source, Graham's theorem, or the possibility of a stronger use of it.

## Direct proof attempt: exact congruence correlations

Retain the actual coefficients a(d), set A=sum |a(d)|, H=sum a(d)/d,
g(j)=sum_(d|j)a(d), and u(j)=g(j)-H. For a positive shift h,
Chinese remaindering gives

`count{1<=j<=R : d|j and e|(j+h)}
 = R*[gcd(d,e)|h]/lcm(d,e) + Delta_(d,e,h)(R)`,

where |Delta|<=1: the compatible solutions form one residue class modulo
lcm(d,e), and incompatible congruences have no solutions. Expanding the
centered product therefore gives the exact period main term

`C_h=sum_(d,e) a(d)*a(e)/(d*e) * (gcd(d,e)*[gcd(d,e)|h]-1)`

and the uniform finite-prefix estimate

`|sum_(j<=R)u(j)u(j+h)-R*C_h| <= A^2+2*|H|*A`.

The two linear floor-count errors supply the second term. Against the actual
decreasing weight q(j+h)=1/(j+h)-1/(T+1), summation by parts bounds the
corresponding weighted error by
`(A^2+2*|H|*A)*q(h+1)`. Summing positive shifts costs a further harmonic
factor. Even the resulting O((A^2+|H|A)*log(T+1)) allowance is too large:
using A<=M and M=4X leaves an X^2 cost. The signed main terms themselves
also require control. Centering does not remove the unit impulse:
`c=delta_1-u`, so its full covariance is the u-covariance plus q(1)
minus `2*sum_(k<=T)q(k)u(k)`.

Thus exact CRT counts do expose the desired arithmetic signs, but bounding
their defects one pair at a time discards the cancellation needed for RH.
This is a paper derivation of the loss, not a new formalized theorem or a
proof that every congruence method fails. The surviving object is the full
signed, coefficient-weighted floor-count defect, with its actual interval
and compensation retained.

The corpus's `Sieve.DirichletCorrelationMultiplicative` cannot shortcut
this problem: its hypotheses require complete multiplicativity and modulus
one. Möbius coefficients satisfy neither. Its misleading Möbius/character
examples have been corrected in comments; no theorem or proof changed.

## Direct proof attempt: continued-fraction cancellation across moduli

[Maier--Rassias, Theorem 2.1](https://arxiv.org/pdf/1806.05070) gives a
power saving for a Möbius-weighted cotangent-related sum over
`k^D<=n<2*k^D`, with D>=2. This does not cover comparable numerator and
denominator sizes. Applying it to separated arithmetic ranges therefore
leaves the balanced ranges uncontrolled. The paper's continuous Gram kernel
also needs comparison with this corpus's compensated discrete carrier;
that identification has not been supplied here.

Trying to iterate Euclidean reciprocity on a balanced pair creates another
unpaid step: writing m=q*n+r changes the actual coefficient product to
`mu(q*n+r)*mu(n)`. It does not produce a fresh single Möbius coefficient in
the remainder r. An iteration needs estimates for these transformed joint
coefficients with the continued-fraction weights retained. No such estimate
was located by the corpus searches `Estermann`, `"continued fraction"
moebius`, and `cotangent cancellation`, or established in this attack.
No formalization of the external estimate is started without an argument
that also handles its missing balanced range and carrier comparison.

## Coprime complete-column cancellation: formalized arithmetic bound

The proved estimate uses the actual Möbius signs before taking absolute values.
For positive n, finite divisor inversion gives

`sum_(e|n, gcd(d,e)=1) mu(e) = [every prime dividing n divides d]`.

Let S(d,R) count positive n<=R supported on the primes of d. For alpha,delta>0,
Rankin's inequality and the finite prime Euler product give

`S(d,R) <= R^alpha * prod_(p|d)(1-p^(-alpha))^(-1)
          <= C_(alpha,delta) R^alpha d^delta`.

The second inequality is uniform in d: beyond a fixed prime threshold the
geometric factor is at most p^delta; the finite small-prime product is the
constant, and the product of distinct prime divisors divides d. Thus the
complete inner floor sum `sum_(e<=R, gcd(d,e)=1)mu(e)*floor(R/e)` is exactly
S(d,R), with subpower growth in both parameters.

Consequently, for every epsilon>0 the mixed floor correlation

`sum_(d<=N) mu(d)*floor(R/d) *
    sum_(e<=R, gcd(d,e)=1) mu(e)*floor(R/e)`

has absolute value at most C_epsilon R^(1+epsilon), uniformly in N. Indeed
terms d>R vanish, the support bound gives a harmonic sum, and its logarithm
is absorbed into a further arbitrarily small power. The same absolute
majorant applies when the outer divisors are restricted to N<d<=R.
This is a quantitative cancellation estimate for a component of the
arithmetic expansion, not an RH assumption or a norm-transfer theorem.

The full two-cutoff form still has an unpaid term. Split each complete divisor
sum into d<=N and d>N. The complete form and the two mixed terms can use the
preceding estimate; the term with both d>N and e>N keeps both Möbius signs
and the coprimality constraint and has no such complete-column inversion.
Residue/harmonic compensation must also stay paired in the actual energy.
`EulerDeletionCoprimeColumnCancellation` proves this estimate uniformly over
every finite outer divisor selection, including outer cutoffs and outer tails.
Its `complete_floor_column` proves the exact support-count identity;
`exists_floorCorrelation_le` supplies the unconditional quantitative bound.
These are statements about the explicit coprime floor correlation, not an
identification of that correlation alone with the full weighted EDQ energy.

The raw complementary double tail cannot have the desired smaller bound.
At cutoff one, let T(R) have both divisor ranges restricted to 2..R, and let
F(R) be the complete correlation. For every positive R, Lean proves
`T(R)=R^2-2*R+F(R)` and
`|T(R)-R^2+2*R|<=C_epsilon*R^(1+epsilon)`.
The positive survivor is the exact polynomial and its controlled remainder.
The active target is therefore the compensated double tail at growing
cutoffs, retaining the actual residue/harmonic terms and infinite energy
tail. A raw-tail subpower target would discard the polynomial exposed here.

[Full theorem statements and validation](../3-formalized/edq-coprime-column-cancellation.md).
The complete scratch, single-leaf build, and audit of eleven new public
declarations passed. Current repository lint passes.
No numerical experiment was needed for these algebraically forced facts.
The frontier map is read-only under the current user instruction.

## Active direct attack: exact common-divisor groups of the compensated Gram

The actual carrier has residue coordinates
`F(k)=sum_(d<=M) a(d)*(k mod d)/d`, with the literal raw or tapered coefficients.
Completing unweighted floor columns does not remove these normalized residues.
Before trying a separate estimate for every common-divisor group, test whether
that grouping preserves the cancellation seen in the complete carrier.

Define `E_q=sum_(k>=1)(sum_(q|d, d<=M)a(d)*(k mod d)/d)^2/[k(k+1)]`.
Finite Möbius inversion gives the exact-gcd group
`C_r=sum_(l<=M/r)mu(l)*E_(rl)` and `sum_r C_r=E_1`.
The proposed separate-group strategy needs a small total variation
`V=sum_r |C_r|`, not merely a small signed sum. Its numerical truth is unknown.
The frozen finite discriminator tests `V<=4*D`, where D is the actual full
Gram diagonal, at M=64,128,256,512 for raw coefficients and the literal
logarithmic taper with X=M/4. The factor four is a fixed diagnostic threshold,
not a fitted constant or a proposed universal theorem. Report every signed
group, the total variation, the diagonal, and the complete signed norm.

This experiment retains analytic bounds for every omitted infinite tail.
For k=qt+i, a multiples channel is exactly
`A_q(t)+(i/q)*H_q`, where
`A_q(t)=sum_j a(qj)*(t mod j)/j` and `H_q=sum_j a(qj)/j`.
This compresses the full weighted sum into q-block moments. Finite-block
moments use direct sums at small t and a convergent geometric expansion at
large t. The tail bound is `(sum_j |a(qj)|)^2/(q*B_q)`.
Choose block counts before seeing signed outcomes so that the sum of all
divisor-multiplicity-weighted tail bounds is at most 0.05. Numerical rounding
controls are separate from these analytic truncation bounds; none enters Lean.

Run only on the authorized RunPod, eight independent Python workers, native
thread pools limited to one, with a 180-second wall limit. Controls compare
compressed moments against direct finite sums and reconstruct the signed norm
by divisor inversion. If the lower bound on V exceeds 4D, a separate-group
majorant at that tested constant fails and the next attack must retain larger
joint groups. If every upper bound is below 4D, attack the actual groupwise
arithmetic estimate on paper. Neither outcome proves or disproves RH.

### Outcome and the next arithmetic estimate

The unchanged eight-worker test completed in 4.048 seconds. All eight cases
have upper total-variation bounds below 4D. Raw V/D intervals range from
2.319..2.344 at M=64 to 1.452..1.466 at M=512; the averaged intervals remain
below 1.899. Both positive and negative exact-gcd groups occur in every case.
The shared infinite-tail allowance is at most 0.05 in each total variation.
[Downloaded results, source, controls and tail bounds](../2-fully-proven/computations/edq-gcd-gram-variation-2026-09-07/REPORT.md).
This supports attempting separate complete-gcd estimates, without assuming
that every group has one sign. Numerical controls and analytic series errors
are recorded separately in the computation artifacts; no result enters Lean.

The direct sign shortcut for the head coefficient is false. Define
`W(N)=sum_(d,e<=N, gcd(d,e)=1)mu(d)mu(e)/(de)`.
At N=22, finite divisor inversion gives `W(22)=H(22)^2-P+Q`, where
P is the sum over p=2,3,5,7,11,13,17,19 of
`(sum_(j<=22/p, gcd(j,p)=1)mu(j)/j)^2/p^2`, and Q is the positive sum over
r=6,10,14,15,21,22 of `1/r^2`.
The inner sums for p=2 and 3 lie between zero and 1/4 and 1/6 respectively;
for p=5,7 they are 1/6, for p=11 they are 1/2, and for p=13,17,19 they are 1.
Thus
`P < 1/64+1/324+1/900+1/1764+1/484+1/169+1/289+1/361 < 29/800`.
The four paired bounds are respectively 1/50,1/500,1/125,1/160.
Meanwhile `Q >= 1/36+1/100+1/196 > 1/25`, so `W(22)>3/800`.
This is a rational paper derivation, not a numerical experiment or an audited
Lean counterexample. No numerical sign scan was run.

The positive survivor is a quantitative head remainder. Put
`B_N(t)=sum_(d,e<=N, gcd(d,e)=1)mu(d)mu(e)*{t/d}*{t/e}`.
For 1<=t<=N, the complete-column identity gives
`B_N(t)=t^2*W(N)-2t*L_N(t)+F_[1,t](t)`, where
`L_N(t)=sum_(d<=N)mu(d)*S(d,t)/d`.
For every delta>0 the proved support count gives
`|L_N(t)|<=C_delta*t^delta*N^delta*H_N` and
`|F_[1,t](t)|<=C_delta*t^(1+2delta)*H_t`.
Consequently
`|sum_(t<=N)(B_N(t)-t^2*W(N))/[t(t+1)]|
 <=3*C_delta*N^(2delta)*H_N^2`.
Absorbing the harmonic factors proves an arbitrarily small power bound for
this exact remainder. This closes the small-divisor cancellation on paper;
it leaves the explicit `W(N)*sum_(t<=N)t/(t+1)` term and its complete later
tail together. The [survivor is now formalized](../3-formalized/edq-coprime-head-subpower.md)
in `EulerDeletionCoprimeHeadSubpower`: `residueQuadratic_eq` isolates the exact
term and `exists_initialEnergy_remainder_subpower` bounds the actual weighted
initial remainder by every positive cutoff power. The complete scratch,
single-leaf build, seven-declaration axiom audit, and repository lint passed.
The full EDQ energy ceiling is still open. The exact common-factor version
additionally retains coprimality with that factor and within-block affine offsets.

## Full-tail closure attack: reciprocity and the cost of splitting the source

The primary [Bettin--Conrey formula (13)](https://msp.org/ant/2013/7-1/ant-v7-n1-p08-p.pdf)
expresses the fractional-part autocorrelation using the Vasyunin sums V.
Combining that formula with the corpus's exact normalized generator gives,
for positive h,k, g=gcd(h,k), a=h/g and b=k/g, the paper identity

`2hk*G_BD(h,k)=(k-1)log h+(h-1)log k
 +pi*(V(1/h)+V(1/k)-g*V(a/b)-g*V(b/a))`.

All universal constant terms cancel under this normalization. The identity
uses the complete autocorrelation before subtracting its three normalization
terms; it does not replace the actual weighted Gram by a uniform period mean.
For coprime balanced h,k of size N, the elementary complete cotangent bound
`|V(h/k)|<=C*k*log k` still permits an O(N log N) pairwise absolute budget.
The required saving is in the signed coefficient-weighted aggregate. The
reciprocity relation for c_0 uses a modular inverse in passing from V to c_0;
the original Möbius coefficient cannot be silently replaced by the coefficient
at that inverse. No new Lean representation module is being built from this
formula without a successful estimate of that signed aggregate.

Before assuming that the initial polynomial must cancel predominantly against
the later tail, freeze a direct diagnostic using the already computed complete
gcd groups. For the same eight raw/tapered sources, split each exact group at
k=X (X=M for raw, X=M/4 for the taper). Write C_r=H_r+T_r. Also define
`K_r=sum_(gcd(d,e)=r)a(d)a(e)/(de)` and
`P_r=K_r*sum_(k<=X)k/(k+1)`, the exact quadratic head contribution.
Compute H_r by the actual finite residue Gram, retaining all affine offsets;
use the stored complete C_r intervals to bound T_r. The new unknown is the
budget lost by separating these actual pieces, not their signed total.

Two predeclared finite tests, at the same threshold four as the full-group
experiment: (A) `sum_r |H_r|+sum_r |T_r|<=4D`; (B)
`sum_r |P_r|+sum_r |H_r-P_r|+sum_r |T_r|<=4D`.
Report every group's head, polynomial, corrected head and tail interval,
including failures; do not fit thresholds or add scales after seeing results.
Failure of (A) directs the next proof attempt to complete groups. Failure of
(B) with (A) surviving means polynomial subtraction helps algebraically but
its separate absolute budget loses the observed cancellation. Passing these
finite tests is guidance only and supplies no uniform or Lean bound.

Run eight independent Python workers on the authorized RunPod under a
60-second limit, reusing the previous full-source results instead of recomputing
their tails. Validate divisor inversion against the direct gcd Gram at M=64;
validate the full initial sum against `F(k)=k*H-1` through X, and verify
`sum_r K_r=H^2`. Keep the existing analytic infinite-tail bounds and distinguish
floating-point sensitivity from formal numerical certification.

### Head/tail diagnostic outcome and present estimate gap

The frozen eight-worker diagnostic completed on RunPod in 0.03812 seconds.
Test (A) passes in all eight cases. Test (B) fails for the raw sources at
M=64 and M=128, with lower B/D bounds 7.849413 and 4.920854 respectively;
the other six cases pass. All head/tail intervals retain the archived full
infinite-tail allowances. Direct gcd-Gram, literal initial-source and divisor
inversion controls passed. [Complete results, source and validation](../2-fully-proven/computations/edq-gcd-head-tail-budget-2026-09-07/REPORT.md).

The finite evidence does not support assuming that the retained polynomial
must cancel mainly against the later tail. Separately charging it and the
corrected head can already lose the fixed budget within the head. This does
not refute their subpower asymptotic bounds. The next bound must control the
actual signed head or the complete group, and account for the complete tail;
the corrected-head theorem alone supplies neither bound.

For the raw source, summing the heads over all gcd groups gives exactly
`sum_(k<=M)(k*H(M)-1)^2/[k(k+1)]`. Corpus
`BaezDuarteMobiusPrefixApproximation` already records the corresponding
harmonic obstruction for the error energy. Thus passing finite head budgets
cannot be promoted to an unconditional growth estimate. Coprime product
regrouping also preserves the missing signs: `mu(d)*mu(e)=mu(d*e)` for
coprime d,e, but the rectangular cutoff becomes a restricted divisor weight
on d*e, not a free complete Möbius convolution.

No successful estimate of the complete signed arithmetic sum was obtained
from the cotangent reciprocity or head splitting attempts. No new Lean file,
receiver, axiom audit or build was added for this diagnostic. No route is
retired. The full EDQ ceiling remains open, and the frontier map remains
read-only.

## All-gcd head remainder: closed arithmetic bound

The finite head-budget test does not distinguish subpower asymptotics. The
sum of absolute corrected heads over all exact gcd groups is now proved
subpower, unconditionally, including the original coprimality masks and
within-block affine offsets.

For r>=1 write Q=floor(N/r), t=floor(k/r), v=k/r as a real number. On
coprime cofactor pairs a,b<=Q retain the masks gcd(a,r)=gcd(b,r)=1.
The actual coefficients factor as mu(r)^2*mu(a)*mu(b), with zero contribution
outside those masks. Expanding the two literal residues gives

`B_r(N,k)-k^2*K_r(N)=mu(r)^2*(-2*v*L_r(Q,t)+F_r(Q,t))`,

where `L_r=sum_(a<=Q,gcd(a,r)=1)mu(a)/a*S_(r*a)(t)` and
`F_r=sum_(a<=Q,gcd(a,r)=1)mu(a)*floor(t/a)*S_(r*a)(t)`.
The complete inner column is precisely the already proved prime-supported
count S_(r*a), since k<=N ensures t<=Q. This expansion retains the affine
offset k/r-t; replacing it by zero would change the head.

For any delta>0, r*a<=N and t<=N give the uniform count bound
`S_(r*a)(t)<=C_delta*N^(2*delta)`. Hence
`|L_r|<=C_delta*N^(2*delta)*(1+log N)` and
`|F_r|<=C_delta*N^(2*delta)*(k/r)*(1+log N)`.
For t=0 the remainder is exactly zero. Otherwise, after multiplying by
1/[k(k+1)], its absolute value is at most
`3*C_delta*N^(2*delta)*(1+log N)/(r*k)`.
Summing both coordinates r,k<=N costs only two further harmonic factors.
Taking delta=epsilon/5 absorbs the three logarithmic factors and yields
`sum_r |H_r(N)-headMass(N)*K_r(N)|<=C_epsilon*N^epsilon`.

This is an actual cancellation estimate, with no RH, harmonic
decay or numerical premise. It still leaves the full leading-coefficient
variation and complete later tail uncontrolled. In particular, a finite
constant-budget failure cannot distinguish the head and polynomial budgets
at the level of cutoff exponents. Both the aggregate remainder bound and the
resulting total-variation comparison are closed in
`EulerDeletionGcdHeadSubpower`; source-identification theorems retain the
original Möbius coefficients and exact gcd-pair parametrization. The complete
scratch, targeted leaf build and eight-declaration axiom audit passed.
[Formal statement, paper proof and validation](../3-formalized/edq-gcd-head-subpower.md).

The next unresolved arithmetic estimate is the retained polynomial variation
`headMass(N)*sum_r |K_r(N)|` together with the complete later tail. The new
theorem removes the aggregate corrected-head remainder from that growth
obligation; it does not estimate either remaining term. The joint finite-word
and full-energy factorization modules do not supply that missing sign law:
their proved convergence extends off the critical line, and the full
factorization identity retains rather than controls the signed cross terms.

## Retained harmonic coefficients and same-cutoff tail control

Write `J_q(N)=sum_(q|d,d<=N)mu(d)/d`. Exact finite divisor inversion gives
`K_r(N)=sum_(l<=N/r)mu(l)*J_(rl)(N)^2`. For squarefree q,
`J_q(N)=mu(q)/q*sum_(j<=N/q,gcd(j,q)=1)mu(j)/j`; nonsquarefree q contributes
zero. Taking absolute values outside that inversion gives
`sum_r |K_r|<=sum_q tau(q)*J_q^2`. The corpus's prime-supported expansion
preserves these exact coprime masks. Its logarithmic rates do not supply
the reciprocal-cutoff saving needed after multiplication by headMass(N).
In particular, the q=1 square remains the literal harmonic defect, so a
fixed-modulus rate cannot be promoted to the required all-cutoff power rate.

[BRIDGE candidate, not a replacement RH conjecture.] The complete harmonic
gcd family may provide a useful selector for the full source, beyond
minimizing its one scalar harmonic defect. The previous complete-source
measurements and the now-proved all-gcd head comparison motivate testing
this before building a tail comparison theorem. No such theorem is assumed.

Freeze four bands `[64,127]`, `[128,255]`, `[256,511]`, `[512,1023]`.
In each band choose the least minimizer of (S) `N*H(N)^2`, and independently
of (G) `headMass(N)*sum_r |K_r(N)|`. The parameter-free prediction is that
the G-selected cutoff has no greater complete raw residue energy than the
S-selected cutoff in each band. Compute complete energy intervals at all
selected cutoffs, retaining an analytic infinite-tail allowance at most
0.005. Compare intervals: separated reversal falsifies the prediction;
overlap is unresolved. Report every band and the full selection scan. Do
not change the selectors, add bands, fit constants or increase precision
after results. Also retain the literal head and later-tail energy intervals
to identify where a reversal occurs.

This asks whether a newly available finite arithmetic selector controls the
same cutoff's unobserved tail. It is not another power-of-two energy scan
or a numerical test of RH. A reversal directs proof work toward an explicit
tail observable in any selector; uniform improvement would support attacking
a comparison with the complete harmonic family. Either outcome is finite
guidance, not an asymptotic theorem. Run eight independent full-energy jobs
on the authorized RunPod under 120 seconds, with one native thread per
worker. Use exact bounded-residue tail inequalities and distinguish their
analytic error from floating-point sensitivity. No result enters Lean.

### Same-cutoff outcome and surviving arithmetic target

The frozen eight-worker experiment completed on RunPod in 0.77751 seconds.
The scalar/gcd selections are respectively 77/78, 154/190, 390/266 and
859/571. The proposed full-energy ordering reverses in the first two bands
and holds in the other two, with all four comparisons separated after
retaining the complete analytic tail allowance and the floating-point
sensitivity margin. The gcd-selected later tail is strictly larger in the
first, second and fourth bands; its ordering is unresolved in the third.
[Complete scan, results, identities and validation](../2-fully-proven/computations/edq-harmonic-lattice-cutoff-selection-2026-09-07/REPORT.md).

The exact raw head energy is
`H(N)^2*headMass(N)-2*H(N)*sum_(k<=N)1/(k+1)+1-1/(N+1)`.
The retained linear unit-source cross term matters for these finite
comparisons. At N=571, the smaller head lowers total energy despite a larger
complete later tail than at N=859. Thus an observed improvement in total
energy need not diagnose an improvement in the tail.

Only the finite selector-dominance prediction is contradicted by these
measurements. A constant-factor or subpower full-energy bound in terms of
the harmonic expression would not imply that minimizing the expression
minimizes actual energy, so such a bound is not refuted here. The positive
survivor is the already formalized all-gcd remainder and variation comparison.
The open mathematical task remains a direct bound for the retained harmonic
coefficients and the same source's complete tail. No route is retired, no
numerical fact is promoted into Lean, and no new receiver module is added.

## Frozen experiment design: where does the cancellation occur?

Question: can temporal correlations of range at most sqrt(X) approximate the
actual finite compensated covariance, or does even range X miss substantial
signed mass? This tests whether short-interval estimates are a plausible next
producer. Earlier experiments measured full error and cutoff-averaging gains;
they did not measure the correlation range.

For X=2^k, k=10,...,16, use T=256X and two actual sources: raw cutoff X,
and the logarithmic average over [X,4X). Keep their literal compensators.
Let c denote their full error increments and S their cumulative sums.
The exact finite energy is
`E=sum_(n<=T) S(n)^2/[n(n+1)]`.
For each range h, record the signed band covariance
`D+2*sum_(k<=T)c(k)*(1/k-1/(T+1))*sum_(max(1,k-h)<=j<k)c(j)`,
where `D=sum_(k<=T)c(k)^2*(1/k-1/(T+1))`.
Ranges: 1, floor(sqrt(X)), X/16, X/4, X, 4X, 16X, 64X, T.
Also record the signed omitted covariance and its absolute size divided by E.
The band-restricted kernel need not be positive: negative values must be
reported as signed covariances, never called negative physical energy.

Predeclared primary classification uses only the averaged source, evaluated in the listed order:

- Local: all seven relative discrepancies at h=floor(sqrt(X)) are <=1/4.
- Nonlocal: at least four relative discrepancies at h=X exceed 1.
- Otherwise: mixed.

No threshold or range will change after data. This finite comparison does not
prove a uniform asymptotic estimate or a full-tail bound. It can change which
correlation estimate is worth attempting next.

## Validation and execution controls

Run only on the authorized RunPod, seven independent scale workers, BLAS
threads one, and a 180-second external deadline. Validate Möbius values against
direct factorization; averaged coefficients against suffix sums of the actual
cutoff probability; fixed coordinates against direct divisor/floor sums;
initial prefix identities; and the full h=T covariance against E computed
independently from cumulative errors. Download the script, protocol, complete
results, log, report and hashes to the computations directory. No numerical
result enters Lean.

## Measured outcome and current proof boundary

The unchanged seven-worker experiment completed in 8.658 seconds on RunPod.
All validations passed. Predeclared classification: **NONLOCAL**, all seven
averaged-source discrepancies at h=X exceed one. They range from 5.567 to
18.944 times the finite energy. In every averaged case the h=X covariance
is negative, while the complete finite energy is positive: the omitted
signed contribution is positive and cannot be discarded for an upper bound.
Even h=64X is not uniformly accurate at these scales. This diagnoses only
the tested finite truncations; it does not exclude all uses of short-interval
estimates, relative-coordinate decompositions, or a proved bound for the
omitted contribution. Absolute temporal separation and the ratio of two
arithmetic moduli are different variables.

Artifacts and full signed values: [experiment report](../2-fully-proven/computations/edq-temporal-correlation-range-2026-09-07/REPORT.md).
The available infinite-tail ceiling is still too large to certify the full
energy numerically. No computation is evidence for an unconditional ceiling
in Lean. None of the three direct estimate attempts closes the hard bound.
RH remains open in the corpus. The active mathematical task is to bound the
complete signed arithmetic remainder, including the balanced moduli and
literal infinite tail, at subpower cost in X; another transfer theorem alone
does not advance that task.

## Direct full-tail attempt: signed modular Abel flux

Status: paper calculation of the attempted estimate and its unpaid term;
no new arithmetic growth bound or Lean theorem. RH remains unproved.

The inspected corpus identities are
`HTGeometry.CenteredModularAbel.sum_centeredModularRamp_mul_eq`,
`sum_centeredModularRamp_mul_bounds`, and
`HTGeometry.SecondCenteredModularAbel.abs_centeredModularRamp_second_abel_le`.
The first bounds a single channel against a nonnegative decreasing weight;
the second Abel bound additionally requires decreasing nonnegative first
weight differences. Those hypotheses cannot be assumed after multiplying
the weight by the signed arithmetic source whose square is being estimated.

For N>=1 retain the literal quantities

```
F(k) = sum_(d<=N) mu(d)*(k mod d)/d,
H = sum_(d<=N) mu(d)/d,
c = (sum_(d<=N) mu(d) - H)/2,
g(k) = sum_(d<=N, d|k) mu(d),
P_d(k) = (k mod d)*((k mod d)-d)/(2*d),
U(k) = sum_(d<=N) mu(d)*P_d(k),
w(k) = 1/(k*(k+1)).
```

All divisor sums run over positive integers. The corpus's primitive
successor identity gives `F(k)=c+U(k+1)-U(k)`; the literal residue jump
gives `F(k)-F(k-1)=H-g(k)` for k>=1. Finite summation by parts therefore
gives, for 1<=a<=b, the exact identity

```
sum_(k=a..b) F(k)^2*w(k)
 = c*sum_(k=a..b) F(k)*w(k)
   + U(b+1)*F(b)*w(b) - U(a)*F(a)*w(a)
   + sum_(k=a+1..b) U(k)*F(k-1)*(w(k-1)-w(k))
   - H*sum_(k=a+1..b) U(k)*w(k)
   + sum_(k=a+1..b) U(k)*g(k)*w(k).
```

For each fixed N, F, U and g are bounded, so every displayed series on
the right converges absolutely as b tends to infinity, and its upper
boundary vanishes. Setting a=N+1 retains the complete actual tail. It
does not replace that tail with a uniform period average or alter c.

The last term is the exact remaining divisor-sampled primitive flux:

```
sum_(k>=N+2) U(k)*g(k)*w(k)
 = sum_(d,e<=N) mu(d)*mu(e)
     * sum_(j>=1, d*j>=N+2) P_e(d*j)*w(d*j).
```

Its d=e contribution vanishes exactly because `P_d(d*j)=0`. This leaves
every unequal pair, with both signs and the actual physical weight.
Nonpositivity of each P_e does not determine the signed aggregate.

The direct absolute bound is insufficient. The proved primitive bound
gives `|U(k)|<=N*(N+1)/16`. For 1<=d<=N, put q=floor(N/d)>=1. Then

```
sum_(j>q) 1/(d*j*(d*j+1))
 <= (1/d^2)*sum_(j>q) 1/(j*(j-1))
 = 1/(d^2*q) <= 2/(d*N).
```

Consequently the absolute flux is at most
`(N+1)*harmonic(N)/8`, an O(N log N) allowance. This is an upper bound
produced by this attempted estimate, not a lower bound or a proof that
all Abel methods fail. Iterating the single-channel Abel theorem does
not remove the flux: differentiating the source factor produces its
literal divisor jumps. A successful use needs an independent signed
bound for these terms together with the retained mean, gradient and
lower-boundary terms. The identity alone is not progress on that bound.

## Direct sign-return attempt: retained two-index transform

Cofinal nonpositive values of `DeletionMobiusGram.cross` would suffice
by the existing `riemannHypothesis_of_cofinally_log_bounded_cross`.
This is a stronger sufficient condition than the existing cofinal
subpower criterion; it has not been proved here.

Trying to force such returns from a scalar real-axis continuation leaves
an unsupplied analytic input. In the absolutely convergent region Re(s)>1,
reordering the literal cutoff series gives

```
sum_(N>=1) cross(N)/N^(s+1)
 = sum_(d,e>=1, d!=e) entry(d,e)
     * sum_(N>=max(d,e)) 1/N^(s+1).
```

Absolute convergence there follows from Gram Cauchy--Schwarz and the
proved diagonal bound `G(d,d)<=2/d`: the absolute entry sum on the
boundary max(d,e)=m is uniformly bounded, and the remaining m-sum is
dominated by a constant times sum m^(-Re(s)). The exact maximum-index
kernel couples the two arithmetic indices. No identity reducing this
series to the single reciprocal-zeta transform, and no continuation
through every positive real s, has been established. Real-axis facts
about that single transform therefore do not supply the required input.
The already bounded diagonal can be subtracted, but this does not prove
continuation or a sign law for the full quadratic source.

These two attempts do not close the EDQ producer. No numerical experiment
was run: the identified losses follow by reasoning. No Lean build,
umbrella build, repeated axiom audit or new receiver module was needed.
The frontier map remains read-only.

## Homogeneous flux weights: aggregate error bound formalized

For N>=1, keep the literal primitive U above and sum every divisor channel
at k=d*(floor(N/d)+j+1), j>=0. Replacing w(k)=1/[k(k+1)] by 1/k^2
changes the complete signed flux by at most harmonic(N)/4. Indeed,
the weight difference is w(k)/k<=w(k)/N. The complete absolute flux
majorant proved on paper above therefore gives error at most
`(N+1)*harmonic(N)/(8*N)<=harmonic(N)/4`. All infinite tails are retained;
no computation or assumed Möbius cancellation enters this bound.

`DeletionFlux.channels_summable` proves convergence
of both complete channels, and `DeletionFlux.flux_weight_replacement` proves the bound
for every N, including the empty cutoff. The actual namespace is
`RHTower.DeletionFlux`. The scratch check, single-leaf build and five-new-
declaration axiom audit passed; only the standard three axioms occur.
The leaf is wired into RHTower without an umbrella build.
[Exact definitions, proof and validation](../3-formalized/edq-flux-weight-replacement.md).
This closes a correction term; the homogeneous signed flux remains open.

### Reciprocal pairing and the retained mean correction

For the complete uncut channel define

```
K(d,e) = sum_(j>=1) P_e(d*j)/(d*j)^2,
Phi_2(x) = sum_(j>=1) B_2(j*x)/j^2,
B_2(x) = fract(x)^2-fract(x)+1/6.
```

Direct substitution gives
`K(d,e)=e/(2*d^2)*(Phi_2(d/e)-zeta(2)/6)`.
The series Phi_2 is the function in
[Balazard--Martin, equation (56)](https://arxiv.org/pdf/1305.4395).
Their Proposition 28, equation (70), relates it to fractional-part
autocorrelation with a retained integral term; it is not a bound for the
literal signed Möbius sum here.

Both K(d,e) and K(e,d) are nonpositive because each P_e is nonpositive.
Swapping d,e also preserves mu(d)*mu(e). Consequently pairing these two
directed terms gives equality in the absolute-value triangle inequality:
it supplies no cancellation within that pair. Cancellation, if used, must
involve different arithmetic pairs or the other retained source terms.
This rejects the proposed within-pair cancellation mechanism, not the EDQ
route or all possible uses of reciprocity. No numerical test is needed for
this sign calculation.

The complete-kernel version must also retain an exact mean correction.
Finite expansion and the full Möbius divisor identity give, on paper,

`reciprocalFlux(N)=sum_(d,e<=N)mu(d)*mu(e)*K(d,e)+c`,

where `c=(M(N)-H)/2`. Indeed the time-indexed complete sum is
`sum_(k>=1)U(k)*g(k)/k^2`; g(1)=1, g(k)=0 for 2<=k<=N, and U(1)=-c.
Thus removing its initial portion adds c. This correction cannot be
discarded or assumed subpower. The new Lean flux is defined directly by
the complete divisor channels beyond N; this Phi_2/complete-kernel
representation is a paper identity, not an additional Lean theorem.

The earlier Abel formula with a=N+1 uses k>=N+2. To use that exact split,
subtract the k=N+1 atom from the beyond-N flux and retain it at the boundary;
alternatively the Abel formula with a=N uses the new beyond-N flux directly.
No source coordinate or boundary term has been declared negligible.

There is also an exact one-complement form, on paper:

`reciprocalFlux(N)=-sum_(d>N, 1<=e<=N)mu(d)*mu(e)*K(d,e)`.

For fixed e, the complete first-index sum is absolutely convergent and
Möbius inversion gives
`sum_(d>=1)mu(d)*K(d,e)=P_e(1)`: substitute k=d*j and use
`sum_(d|k)mu(d)=[k=1]`. Absolute convergence follows from
`|P_e(k)|<=e/8` and the product of two inverse-square series. Summing the
finitely many e channels gives -c, proving the displayed complement form.
Thus this form incorporates the mean correction exactly. The remaining
arithmetic range has d>N and e<=N; its balanced part still includes d and
e both comparable to N. Bounding K by `e*zeta(2)/(8*d^2)` and taking
absolute Möbius values costs O(N). No estimate closing that signed
complementary rectangle has been proved or formalized here.

## Full reciprocal flux: sign diagnostic and exact square decomposition

The frozen RunPod diagnostic classified the literal complete reciprocal
flux as positive at every cutoff N=2,...,512; N=1 is exactly zero. All
analytic-tail, divisor-identity and independent time-source controls passed.
The unchanged eight-worker run took 0.669 seconds. These are floating-point
evaluations of analytic tail bounds, not certified interval arithmetic or
Lean proofs. Uniform positivity and the required subpower ceiling remain
unproved. [Protocol, all cutoffs, matrices and validation](../2-fully-proven/computations/edq-complete-flux-sign-2026-09-07/REPORT.md).

The direct attempt at a positive-square interpretation retains a negative
square term. Set l=N+1, v(k)=1/k^2, and
`t(k)=U(k+1)-U(k)=F(k)-c`, with the actual quantities above. The divisor
jump identity gives `g(k)=H-t(k)+t(k-1)`. For N>=1, finite summation by
parts followed by the complete-tail limit therefore gives, on paper,

```
reciprocalFlux(N)
 = H*sum_(k>=l) v(k)*U(k)
   + v(l)*U(l)*(U(l)-U(l-1))
   + (v(l)-v(l+1))*U(l)^2/2
   + sum_(k>=l) (v(k)+v(k+1))*(U(k+1)-U(k))^2/2
   - sum_(k>=l+1) (v(k+1)-2*v(k)+v(k-1))*U(k)^2/2.
```

To check the signs, first telescope
`-sum v(k)*U(k)*(t(k)-t(k-1))`. Its interior summand is
`(v(k+1)*U(k+1)-v(k)*U(k))*t(k)`. Expand this as

```
(v(k+1)+v(k))*t(k)^2/2
 + (v(k+1)-v(k))*(U(k+1)^2-U(k)^2)/2,
```

then telescope the second term. At a finite upper endpoint b the remaining
upper boundary is
`-v(b)*U(b)*t(b)+(v(b)-v(b-1))*U(b)^2/2`.
It tends to zero because U and t are bounded for each fixed N. All infinite
series displayed above converge absolutely: v is summable and its second
differences have order k^(-4). No upper-tail term is omitted.

For k>=2 the exact coefficient is

`v(k+1)-2*v(k)+v(k-1)=2*(3*k^2-1)/(k^2*(k^2-1)^2)>0`.

Thus this identity is not itself a sum of nonnegative terms. The lower
boundary is also fixed by the initial divisor identity, rather than free:

```
U(l) = H*N*(N+1)/2-N-(N+1)*c,
U(l)-U(l-1) = N*H-1-c.
```

These follow from F(k)=k*H-1 for 1<=k<=N and U(1)=-c. The gradient square
still contains the same source `F-c`, and the mean, primitive-square and
boundary terms have no supplied subpower aggregate bound. In particular,
positivity of the measured flux, even if eventually proved for all N,
would be a lower bound and would not supply the needed upper bound.
This is a paper decomposition of the attempted sign proof, not a new
growth estimate, a retirement of EDQ, or a new Lean theorem. The actual
signed complementary-rectangle estimate remains the hard target.

## Affine primitive change: exact arithmetic cost of cancelling the mean

This direct upper-bound attempt preserves F and cancels the mean before
summation. It does not close the upper bound. The regularized divisor
identity was checked against the corpus's
`RegularizedDivisorHarmonic.divisorSummatory_reciprocal_harmonic` and
`tendsto_regularizedDivisorHarmonic`, and the fixed-divisor harmonic limit
used by `SummableDivisorHarmonicMean`. Their finite-support application
justifies the limit below; their absolute-summability hypotheses must not
be applied to the untruncated Möbius sequence.

Keep N>=1 and l=N+1. Write h_N=sum_(k<=N)1/k for the ordinary harmonic
number, h_N^(2)=sum_(k<=N)1/k^2, zeta_2=sum_(k>=1)1/k^2,
and L_N=sum_(d<=N)mu(d)*log(d)/d. The two centered divisor moments are

```
alpha_N = lim_(B->infinity) sum_(k=N+1..B) (g(k)-H)/k
        = H*h_N-1-L_N,
beta_N  = sum_(k>N) (g(k)-H)/k^2
        = zeta_2*sum_(d<=N)mu(d)/d^2-1-H*(zeta_2-h_N^(2)).
```

For the first identity, finite divisor rearrangement gives

```
sum_(k<=B) (g(k)-H)/k
 = sum_(d<=N) mu(d)/d * (h_(floor(B/d))-h_B)    (B>=N).
```

Each bracket tends to -log(d). Removing k=1,...,N subtracts 1-H*h_N,
because g(1)=1 and g(k)=0 for 2<=k<=N. This proves alpha_N as an
ordinary ordered-series limit; no absolute-convergence assertion is made.
For beta_N the inverse-square series are absolutely convergent and
reindexing each divisor channel gives the displayed expression directly.

Define V(k)=U(k)+c*k. Then V(k+1)-V(k)=F(k), and the full centered flux
obeys the exact paper identity

```
J(V) := lim_(B->infinity) sum_(k=l..B) V(k)*(g(k)-H)/k^2
      = reciprocalFlux(N)-H*sum_(k>=l)U(k)/k^2+c*alpha_N.
```

Thus the affine change has the actual Möbius logarithmic moment as its
cost. The separate expressions sum V(k)*g(k)/k^2 and H*sum V(k)/k^2
are not legitimate replacements: if c*H is nonzero, both have a
logarithmically divergent leading term. Their centered difference has
the ordered limit proved above.

One can also remove the lower boundary exactly. Put

```
A=V(l)=N*(H*(N+1)/2-1),
W(k)=V(k)-A,
E_v=sum_(k>=l) (v(k)+v(k+1))*F(k)^2/2,
P_v(W)=sum_(k>=l+1) (v(k+1)-2*v(k)+v(k-1))*W(k)^2/2.
```

Then W(l)=0, the square decomposition above gives J(W)=E_v-P_v(W),
and J(W)=J(V)-A*beta_N. Combining these identities yields

```
E_v = reciprocalFlux(N)+P_v(W)-H*sum_(k>=l)U(k)/k^2
      +c*alpha_N-A*beta_N.
```

This keeps all terms together until the finite identities are established.
Since W(k)=O_N(k), every square series converges, and both upper boundary
terms still tend to zero. The formula is a source-preserving change of
primitive, not a modification of the harmonic counterterm in F.

The attempted closure remains circular: the left side is the full source
tail energy with comparable inverse-square weights; P_v(W) is a positive
primitive-square term; and no independent subpower bound for the complete
right side has been supplied. The exact alpha_N and beta_N identities do
not supply that bound. The whole-corpus searches also found no applicable
estimate for the balanced complementary Möbius rectangle. No numerical
experiment is warranted for these algebraic consequences, and no new
receiver or restatement of the existing regularization theorem is being
formalized as a substitute for the missing arithmetic estimate.
