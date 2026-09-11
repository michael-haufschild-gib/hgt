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

## Full-flux Fourier truncation: logarithmic error formalized

For Q>=1 retain the actual finite-frequency primitive

```
P_(e,Q)(k)=e/(2*pi^2)*sum_(m=1..Q)
  (cos(2*pi*m*k/e)-1)/m^2.
```

The corpus's absolutely convergent Bernoulli cosine series identifies its
complete sum with P_e(k). The omitted frequencies cost at most
`e/(pi^2*Q)`, uniformly in k. Applying the actual Möbius coefficients and
all divisor-channel times proves

```
|reciprocalFlux(N)-truncatedReciprocalFlux(N,Q)|
 <= (N+1)*harmonic(N)/(pi^2*Q).
```

`DeletionFlux.flux_fourier_cutoff_error` specializes to Q=N+1 and proves
the unconditional bound `harmonic(N)/pi^2` for every N, including zero.
All time tails remain present. Here m is the Bernoulli frequency; the
product m*j after expanding a divisor channel is not being truncated.
The proof establishes absolute convergence of the new and error channels
before subtracting their infinite sums.
[Definitions, paper proof and validation](../3-formalized/edq-flux-fourier-truncation.md).
The scratch check, single-leaf build and five-new-declaration axiom audit
passed. No numerical input, added axiom or umbrella build was used.

### What the bilinear attempt still has to bound

The complete-kernel expansion also has the exact paper form

```
K(d,e)=-e/(2*pi^2*d^2)*sum_(r>=1)
  tau(r)*(1-cos(2*pi*r*d/e))/r^2.
```

Here tau(r) counts positive divisors. Insert the Bernoulli expansion into
the complete j series and group r=m*j; absolute convergence follows from
the product of two inverse-square sums. This r expansion is a separate
paper identity, not the definition of the new Lean truncation.

Already the m=j=1 summand has phase 2*pi*d/e. On the balanced rectangle
N<d<=2N, N/2<e<=N its phase lies between 2*pi and 8*pi, independently of
N. Increasing N therefore supplies no growing phase variation for this
fixed summand. After d=N*x,e=N*y its amplitude is N^(-1) times a fixed
smooth function on [1,2]x[1/2,1]. Two finite summations by parts bound
that summand by a constant times N^(-1) times the two maximal Möbius block
partial sums. The available arbitrary logarithmic savings in those partial
sums leave an N times logarithmic-saving allowance, not subpower growth.
This diagnoses this particular estimate; it does not give a lower bound
for the signed block or exclude a different arithmetic argument.

The inspected `TypeIIEnergyBound` treats a different curved phase, and
`VinogradovTaylorPerturbation` needs its stated rational-approximation and
denominator conditions. Neither supplies this low-frequency bound merely
because the sum is bilinear. `MRFibreReduction` retains an averaged
short-interval hypothesis. The source-specific complete block must still
be bounded. The inspected [Maier--Rassias theorem](https://arxiv.org/pdf/1806.05070)
also retains D>=2 in Theorem 2.1, leaving the comparable-modulus range.
[Chavez's fractional-part correlation statement](https://arxiv.org/pdf/2402.09343)
uses direct integer dilations averaged uniformly over an integer number
of periods; it is not the reciprocal-dilation, physically weighted EDQ
source. No transfer of that statement to the present norm is asserted.

The proved new frequency-tail bound is a correction bound. The remaining
finite-frequency signed arithmetic flux and its full energy comparison
are still open; no RH proof or falsification has been obtained.

## Modulus-ratio test and complete reduced-denominator head

The direct cutoff recurrence does not remove the unknown correlation. Since
K(N,N)=0, the complete-kernel formula gives

```
R_N-R_(N-1) = mu(N)*(1-1/N)/2
             +mu(N)*sum_(e<N)mu(e)*(K(N,e)+K(e,N)).
```

Using complete first-column inversion on the reverse term gives
`R_N-R_(N-1)=mu(N)*(sum_(e<N)mu(e)K(N,e)-sum_(d>N)mu(d)K(d,N))`.
The boundary cancels exactly; the two signed source sums still need a bound.
No new ceiling follows from this recurrence.

The frozen RunPod diagnostic decomposes the literal one-complement formula
by d/e. The prediction that d/e<=4 approximates the complete flux within 25%
failed at N=48,64,96 among the nine frozen cutoffs. Its predeclared outcome is
MIXED; no ratio-four relative discrepancy exceeds one. Every tested (16,32]
band is negative and every (32,64] band positive. A separately frozen
attribution test found that reduced denominators b=2,3 have the wrong sign
for the former band at all nine cutoffs. Thus its stable signs cannot be
attributed to those selected rays alone. Both experiments retain the complete
infinite time kernels and obtain their complete omitted parts by subtracting
from existing full-flux intervals. These are floating evaluations of analytic
bounds, not certified intervals or Lean evidence.
[Protocols, complete results, controls and hashes](../2-fully-proven/computations/edq-modulus-ratio-locality-2026-09-07/REPORT.md).

The exact reduced-pair coordinates are d=r*a,e=r*b, gcd(a,b)=1. They satisfy

```
K(r*a,r*b)=K(a,b)/r,
mu(r*a)*mu(r*b)=mu(a)*mu(b)*mu(r)^2*[gcd(r,a*b)=1].
```

An entire fixed reduced pair has constant sign and a nonnegative harmonic
common-factor mass over N/a<r<=N/b. This is an exact paper identity; it does
not by itself show that finitely many pairs determine a complete band.

The positive quantitative result is stronger than bounding finitely many
pairs: retain every numerator and time coordinate and restrict only b<=B.
Define J(N,B) by the literal coprime a tail a>floor(N/r), with r<=floor(N/b),
actual coefficients mu(r*a)mu(r*b), and b<=min(B,N). The primitive bound and
the first reciprocal-square estimate give |K(d,e)|<=e/(4*d^2). Summing the
entire numerator tail costs at most b/(4*r*floor(N/r))<=b/(2*N). Summing
the admitted r then costs at most 1/2 for each b. Consequently

```
|J(N,B)| <= B/2   for every natural N,B.
```

`DeletionFlux.reducedHead_bound` in `EulerDeletionReducedDenominatorHead`
formalizes this unconditional bound, including N=0 and B=0, with summability
proved before infinite sums are used. The scratch check, single-leaf build and
four-new-declaration axiom audit passed. Only the new leaf compiled; no umbrella
build or numerical Lean input was used. The exact statement and remaining
source-identification boundary are [documented](../3-formalized/edq-reduced-denominator-head.md).

Thus a subpower-sized reduced-denominator head has a proved subpower cost.
The source with b>B remains signed and uncontrolled; the experiments rule out
discarding it at the tested small cutoff. The paper identification J(N,N)=R_N
has not been added as a Lean theorem. Neither the new head bound nor the finite
diagnostics proves the complete EDQ ceiling or RH. No frontier-map edit was made.


## Completed numerator columns: Euler main and absolute subpower remainder

The literal complete coprime column
`C(m,b)=sum_(a>=1,gcd(m,a)=1)mu(a)*K(a,b)` is now identified in Lean with
`sum_(k>=1,prime-support(k) subset prime-support(m))P_b(k)/k^2`.
Absolute two-index convergence justifies the divisor inversion. For positive
m,b and 0<alpha<1, the new exact source estimate is

```
0 <= C(m,b)+E_1(m)/2 <= E_alpha(m)*b^(alpha-1)/2,
E_alpha(m)=prod_(p|m)(1-p^(-alpha))^(-1).
```

At squarefree m, E_1(m)=m/phi(m). The proof uses
`0<=P_b(k)+k/2<=min(k/2,k^2/(2*b))` and the corpus's exact finite-prime Euler
mass. Its uniform subpower modulus bound then gives the stronger aggregate
statement, for every epsilon>0,

```
sum_(1<=r,b<=N) |C(r*b,b)+E_1(r*b)/2|/r <= C_epsilon*N^epsilon.
```

This absolute bound covers the entire rectangle, hence the admitted triangle
r*b<=N and every outer Möbius or coprimality mask of magnitude at most one.
`EulerDeletionCompletedColumnMain` formalizes the column identity, its main
term, and the aggregate bound. The scratch check, single-leaf build, and
eight-new-declaration axiom audit passed; only the new leaf's olean changed.
[Exact statements, proof and validation](../3-formalized/edq-completed-coprime-column-main.md).

The actual numerator tail is C(r*b,b) minus the finite signed head
`sum_(a<=floor(N/r),gcd(r*b,a)=1)mu(a)*K(a,b)`. The completed-column estimate
does not bound this subtraction. The remaining task is a cutoff-dependent
bound on those finite heads with their Euler mains and actual outer signs
retained. No estimate of that hard term, complete EDQ ceiling, or RH proof is
asserted. The frontier map remains read-only.


## Complete-column coherence and the retained Bernoulli oscillation

The frozen RunPod diagnostic keeps the complete actual numerator tail in
`x_e(N)=-mu(e)*(P_e(1)-sum_(d<=N)mu(d)*K(d,e))`, so R(N)=sum_(e<=N)x_e(N).
It reuses the archived infinite-kernel enclosures; no time or numerator tail
is dropped. The proposed finite comparison `sum_e|x_e|<=4*R` fails at N=96,
where its ratio lies between 6.0063 and 6.0140. It survives the other eight
frozen cutoffs. This rejects that constant-four comparison, not a uniform
subpower bound for the row variation.

The parameter-free Bernoulli mean is

```
t_2(N)=6/pi^2-sum_(d<=N)mu(d)/d^2,
y_e(N)=pi^2*mu(e)*e*t_2(N)/72.
```

The proposed 25% absolute row-approximation test fails at all nine cutoffs.
At N=384 its residual retains over 99% of the actual absolute row mass.
The mean's signed total is negative at eight cutoffs while the full flux
is positive. Hence the tested mean-only reduction loses material signed
arithmetic information. All cases, both positive/negative row masses,
controls, frozen hashes, and limitations are in the
[computation report](../2-fully-proven/computations/edq-column-coherence-2026-09-07/REPORT.md).
The unchanged eight-worker run took 0.082191 seconds. These are numerical
research observations, not formal counterexamples or asymptotic estimates.

The ensuing direct upper-bound attempt keeps the mean exactly. For N>=1,
write M(N)=sum_(n<=N)mu(n). Finite Abel summation and the absolutely
convergent inverse-square tail give

```
sum_(e<=N)mu(e)*e=N*M(N)-sum_(0<=k<N)M(k),
t_2(N)=-M(N)/N^2+sum_(k>=N)M(k)*(1/k^2-1/(k+1)^2).
```

The upper boundary in the second identity vanishes already from |M(k)|<=k.
The corpus's arbitrary fixed logarithmic Mertens savings bound the first
factor by O_A(N^2/log(N)^A) and the second by O_A(1/(N*log(N)^A)), after
adjusting the arbitrary log power to handle the initial finite ranges.
Their product still has an N times logarithmic-saving allowance. This
calculation supplies no positive power improvement. The oscillatory
remainder is also retained and has no independent subpower estimate.

A second attempted transfer through the logarithmically weighted Selberg
forms does not close the same source: their coefficient taper and gcd
kernel are not the literal untapered, inverse-square-time EDQ kernel.
The exact cutoff-average receiver retains its actual taper and full tail;
no comparison from a period mean to that physical tail is supplied here.

The hard signed finite-head estimate remains open. This attempt added no
Lean theorem, no replacement RH equivalence, and no universal-law entry.
No route is retired on the numerical tests, and the frontier map was not
edited by this task. The experiment's remote files were removed only after
all downloaded hashes were verified and its process check was empty.

## Wider corpus search and direct mixed-difference attempt

The indexed search uses single terms or explicit `--any` for alternatives;
multiple unqualified terms mean AND. The broad inventories for `bilinear`
and `cancellation offdiagonal --any` contain respectively 401 and 987
matching modules. These are search matches, not claims that every proof
in those modules has been audited. Additional unfiltered searches cover
`cotangent reciprocity --any`, `renewal`, `coboundary`, `antipodal`,
`Landau`, `Graham`, `fractional`, `Davenport`, `dispersion`, `transport`,
and `Bernoulli`. One declaration per module exposes different families
before reading selected exact statements and their premises.

The inspected candidate transfers have these precise boundaries:

| Corpus source | Available result and missing EDQ transfer |
| --- | --- |
| `Sieve.BilinearMultiplier`, `Sieve.HilbertBilinear` | Bounded finite Fourier symbols control their own kernels. The harmonic symbol is bounded, but no such representation and symbol bound for the actual K is supplied. |
| `Sieve.DirichletRow` | The bilinear inequality retains the Gram-row bound as a premise. It does not prove that premise for the reciprocal-dilation source. |
| `HTGeometry.AcrossClassReciprocity`, `HTGeometry.CorrelationExponentBridge` | These concern specified square-root phases and their exponent budgets. Their conclusions cannot be transferred to d/e merely because both problems are bilinear. |
| `Sieve.OffDiagonalShiftBound`, `Sieve.OffDiagonalUniformBound` | Exact reductions retain bounds for partial arithmetic correlations. Those are required inputs, not unconditional subpower bounds for EDQ. |
| `Sieve.KloostermanCompleteColumnCorrelation`, `Sieve.KloostermanTerminalGeometricCancellation` | Complete-column orthogonality and unequal-modulus geometric-orbit bounds retain terminal windows and frequency-dependent denominators. No collective estimate for the present Möbius rectangle follows. |
| `MobiusMultiplicativeRectangleCubature` | The exponential-kernel four-corner estimate is proved for prescribed Möbius rectangles. An actual covering and its uncovered residual remain required. Its smooth kernel is also different from K. |
| `MobiusDivisorDilationMeanUniformRenewal` | Uniformity in dilation is for each fixed finite prime core. The bound depends on that core, so it cannot silently become uniform in the growing EDQ cutoff. |
| `Sieve.MoebiusSmoothCancellation`, `Sieve.MoebiusTwistSharpLittleO`, `Sieve.RouteTMoebiusSharp` | Finite prime-product damping and sharp-prefix transfers preserve their support, twist range, and supplied prefix bound. None supplies the missing square-root-scale cancellation for the literal cutoff. |

The newly present `MobiusDivisorCorrectedCoareaAction` was inspected
read-only, without building or auditing another task's declarations.
Its source text retains mixed-cell head dominance and gives an exact
late-block action law; it does not assert a uniform corrected-action
ceiling. No transfer from that action to EDQ is proved here.

The direct estimate keeps the full kernel on a balanced rectangle. Write
`d=N+i`, `e=floor(N/2)+j`, let u_i and v_j be their actual Möbius
coefficients, and put A_i=sum_(a<=i)u_a, B_j=sum_(b<=j)v_b.
If L,H are the two side lengths, applying finite Abel summation twice gives

```
sum_(i<=L,j<=H) u_i*v_j*K_ij
 = A_L*B_H*K_LH
   + sum_(i<L) A_i*B_H*(K_iH-K_(i+1,H))
   + sum_(j<H) A_L*B_j*(K_Lj-K_(L,j+1))
   + sum_(i<L,j<H) A_i*B_j*
       (K_ij-K_(i+1,j)-K_(i,j+1)+K_(i+1,j+1)).
```

Indices in these finite sums start at one. No modulus, numerator, or
time term is removed from K. Taking absolute values yields
`max|A_i|*max|B_j|*V(K)`, where V is the sum of the absolute corner,
boundary differences, and mixed differences displayed above.
Reversing the same telescoping shows `V(K)>=max|K_ij|`.
At N=8m, the actual interior pair d=9m,e=6m already contributes
`P_(6m)(9m)/(9m)^2=-1/(108m)` at time j=1; all other time terms
are nonpositive. Hence `V(K)>=2/(27N)` on these cutoffs.
Using only the available envelopes `max|A|,max|B|<=C_A*N/log(N)^A`
therefore cannot make this absolute-variation certificate subpower:
the certificate itself retains at least a constant times
`N/log(N)^(2A)` for each fixed A. This does not lower-bound the signed
sum or the actual Möbius partial sums. It identifies the loss in this
specific attempted upper bound.

The full kernel also prevents an unproved scale-independent smoothness
assumption. Let h_(e-1)=sum_(j=1..e-1)1/j be the ordinary harmonic sum.
Periodicity gives, for e>=2,

```
K(2e,e)=0,
K(2e+1,e)=K(1,e)/(2e+1)^2,
(h_(e-1)-(e-1)/e)/2 <= -K(1,e) <= h_(e-1)/2+1/4.
```

For the bounds, sum the terms j<e exactly using
`P_e(j)/j^2=1/(2e)-1/(2j)`. Every later term is nonpositive,
and its total absolute mass is at most
`(e/8)*sum_(j>=e)1/j^2<=e/(8(e-1))<=1/4`.
Thus the adjacent jump at this resonance has order `log(e)/e^2`;
a fixed bound C/e^2 fails. The positive local estimate also shows that
the strip d=2e+1, N/2<e<N, costs only `O(log(N)/N)` in absolute value.
The problem is therefore not that narrow strip by itself. The remaining
bulk still needs a bound retaining the signs in the mixed-difference sum,
or a different comparison that controls the same complete source.

These are paper calculations for a failed direct transfer, not newly
formalized theorems. No hard EDQ ceiling, RH proof, or falsification was
obtained. No computation or Lean build was needed for these deterministic
checks, and no universal-law or frontier-map entry was changed by this task.

## Deep corpus search: contraction and literal prime deletion

Four `research --mode deep --budget-seconds 120 --json` requests were
executed on 2026-09-10. The first allowed an index refresh; the remaining
three used `--no-refresh`. No module restriction was imposed. The queries
were:

1. `Bound the full signed Mobius bilinear reciprocal dilation kernel over complementary cutoffs d greater than N and e at most N by every positive power of N retaining finite subtracted coprime numerator heads Euler main and all time tails`
2. `Mobius bilinear cancellation reciprocal dilation subpower` with `--any`.
3. `Euler deletion signed Gram offdiagonal cofinal ceiling` with `--any`.
4. `Bound signed Mobius sums by cancellation across prime scales while retaining cutoff boundary terms` with `--any`.

| Request | Elapsed seconds | Candidate lemmas | Source arguments | Proof ideas / ingredient sets | Completion |
| --- | ---: | ---: | ---: | --- | --- |
| 1 | 70.125 | 13 | 20 | 0 / 0 | Partial; retrieval interrupted, model stages failed or expired, refresh deferred to running indexer |
| 2 | 120.010 | 20 | 20 | 0 / 0 | Partial; deadline during decomposition |
| 3 | 120.013 | 20 | 20 | 0 / 0 | Partial; deadline during decomposition |
| 4 | 120.008 | 12 | 12 | 0 / 0 | Partial; deadline during filtering/judgment |

Request 1's lexical AND stage found no declaration; its relaxed retrieval
did return candidates. Requests 2 and 3 generated follow-up query terms,
but their traces contain only round 1. Request 4's trace reaches round 2.
Request 3 drifted to Euler characteristics and ordinary ceiling functions;
those hits do not address Euler deletion. Empty proof-idea and ingredient
sections are recorded as empty, not as evidence that no mathematical
argument exists in the corpus.

The first coverage snapshot inventoried 55,915 indexed files: 46,518 Lean
and 9,397 prose files, with 719,312 declarations. Its compiler metadata
listed every Lean file as pending. Later coverage snapshots were themselves
pending. Semantic coverage was incomplete in every returned result; the
last snapshot reports expected 2,166,650, ready 2,166,644 and pending 1,
which does not itself reconcile the total. No complete-coverage claim is
made. All 137 returned candidate/source-argument occurrences were checked
against the current declaration-block hashes using the search extractor;
all matched. This verifies source freshness, not Lean applicability or
the truth of a model-suggested transfer. Returned applicability fields
were unchecked and compiler status was `source_only`.

Selected exact statements and bodies give these usable boundaries:

- `RHTower.additive_floor_is_epsilon` in `RecurrenceTypeDichotomy` delegates to
  `subpower_bound_of_dyadic_contraction`. This supplies the desired
  conclusion only after proving the actual recurrence with q<1.
- `GaloisForLFunctions.HTGeometry.mobiusLogInversion_ge` in
  `MonotoneMobiusPositivity` assumes a nonnegative
  monotone density and sums inverse-square dilates. The actual modular
  source is not supplied with that monotonicity, and the conclusion is
  a lower comparison, not the missing energy upper bound.
- `RHTower.weightedLambertMobius_inversion` in `PrimeLambertMobiusInversion` preserves
  the explicit double-series summability premise. Inversion alone does
  not give a cutoff estimate for the retained finite numerator head.
- `MenonFinalRangeRamareReduction` retains its literal bilinear energy;
  `GhsBlockPlainMass` uses sigma>=1 and its own prime-block weights;
  `DeningerMobiusPreimage` obtains its inverse-square bound by absolute
  values. None supplies the EDQ cancellation rate.
- `RHTower.Sieve.exists_gt_tsum_routeEStaticAntiscaleTerm_lt` in
  `RouteEStaticAntiscaleFrameDichotomy`
  gives small returns in a free frequency variable for fixed summable
  diagonal weights. EDQ requires returns in the arithmetic cutoff for
  its full signed source. No identification of these quantifiers exists
  in this attempted transfer.
- The private `primeScale_remainder_bound` in `PrimeLogBlockCompression` bounds the
  higher-prime-power correction to an exponential first term; the
  first term remains. The inspected Type-I prime-amplifier schedule and
  prime-deletion harmonic-mass bounds likewise retain their own weights
  and source assumptions.

The direct contraction attempt uses the literal generator
`b_d(u)=bdGenReal(1/d,u)=({u/d}-{u}/d)/u`. Its exact identity is

```
b_(p*d)(u) = p^(-1)*b_d(u/p) + d^(-1)*b_p(u).
```

For a prime p, define
`A_N^p=sum_(d<=N,p not dividing d)mu(d)*b_d`,
`h_M^p=sum_(d<=M,p not dividing d)mu(d)/d`, and M=floor(N/p).
Splitting the original coefficients at p, including the zero coefficients
at multiples of p^2, gives the exact paper identity

```
F_N = A_N^p - D_p A_M^p - h_M^p*b_p,
F_N=sum_(d<=N)mu(d)*b_d,
(D_p f)(u)=p^(-1)*f(u/p).
```

Here `||F_N||` is the norm of the actual raw modular approximant, whose
sign convention is opposite. All integer generators vanish for 0<u<1.
Consequently change of variables in the full integral on u>1 yields
`||D_p A_M^p||^2=p^(-1)*||A_M^p||^2`; no lower-limit integral has been
dropped. But the other two terms remain. In particular, with
`Z=D_p A_M^p+h_M^p*b_p`, the full energy is

```
||F_N||^2 = ||A_N^p||^2 + ||Z||^2 - 2*<A_N^p,Z>.
```

The same-cutoff prime-free norm and this literal mixed pairing have no
supplied recurrence bound. A contracting dilation therefore does not
establish a contraction of the full arithmetic energy. Substituting the
triangle inequality preserves the uncontrolled same-cutoff norm. This
attempt has not proved the required q<1 recurrence or a subpower ceiling.

A temporary `lake env lean` file checked both the generator identity and
application of `subpower_bound_of_dyadic_contraction` to the actual
`||bdMobiusModularApproximantVec N||^2`. The latter explicitly retained
the unproved source recurrence as a premise; it is an applicability
check, not a new arithmetic theorem. Broad initial imports encountered
a missing unrelated olean; using the direct leaf imports completed the
check with exit 0 and one unnecessary-sequence-focus style warning.
No dependency rebuild, umbrella build, axiom audit, or new Lean module
was performed. The finite prime split and integral norm calculation
above remain paper calculations. RH and the hard signed ceiling remain
unproved; no universal-law or frontier-map change is justified here.

## Deep search: mixed prime correlation and the full-tail estimate

The target remains an upper ceiling for the complete signed source, on
the same cofinal cutoffs used by the zero-balance receiver. Three further
requests used `--any --mode deep --budget-seconds 120 --no-refresh`, with
one result per module:

| Query | Candidate lemmas / source arguments | Result |
|---|---:|---|
| `coprime Mobius dilation energy mixed correlation` | 12 / 12 | partial, 120.006 seconds |
| `Mobius Gram Bessel dilation cutoff correlation` | 16 / 16 | partial, 120.013 seconds |
| `signed bilinear cancellation Hilbert Cotlar` | 12 / 12 | partial, 120.035 seconds |

All three reached the deadline with `filter_and_judge` unfinished.
All returned empty `proof_ideas` and `ingredient_sets`; this is a retrieval
outcome, not evidence that no useful argument exists in the corpus.
Coverage was pending and semantic coverage incomplete. All 80 returned
declaration occurrences matched their current source-block hashes when
checked, but all had `source_only` compiler status and unchecked
applicability. Their statements were inspected; selected relevant proof
bodies were then read directly.

The source-specific candidates expose the following exact boundaries:

- `MobiusDivisorLocalizedInteractions` bounds a mixed second selection
  difference by `(18/25)*4^(|P|-1)*M*(floor((M-1)/(p*q)) +
  floor((M-1)/max(p,q)))`. Both support restrictions are genuine, but the
  processed-prime factor remains. This is not a bound for the raw
  prime-free Gram pairing in the preceding section.
- `MobiusDivisorPrimeCorrelationPhysical` identifies the complete
  fixed-core release with `2*density(P union {p})*p^(-3/2)*D_P(p)`.
  `MobiusDivisorDilationMeanUniformRenewal` bounds `D_P(Y)` uniformly in
  Y for each fixed P. Its bound explicitly contains the core's residue
  and an absolute Mellin-boundary integral. The same module proves
  `D_(P union {p})(Y) <= -c_P*sqrt(p)` throughout a comparable-ratio
  band after a sufficiently large insertion. Thus even these changing-core
  correlations have source-derived negative bands; a positive mixed
  pairing cannot be supplied by generic dilation geometry. The release
  prefactor must remain when judging their size.
- `MobiusAdditiveDilationDiagonalization` gives exact Parseval for signed
  divisor-incidence coefficients. The point-evaluation estimate needed
  after that diagonalization remains unproved.
- `Sieve.HilbertBilinear` controls its harmonic Fourier multiplier;
  `HTGeometry.MontgomeryVaughanDampedMeanSquare` retains frequency-spacing
  costs. Neither statement identifies that multiplier with the actual
  symmetric EDQ Gram kernel or bounds its remaining signed part.

The literal prime split still gives `F_N=A_N^p-Z`, hence a proposed
contraction `||F_N||^2 <= q*||F_(floor(N/p))||^2+C*N^epsilon` requires

```
2*<A_N^p,Z> >= ||A_N^p||^2+||Z||^2
               -q*||F_(floor(N/p))||^2-C*N^epsilon.
```

None of the inspected candidates proves this lower comparison for the
actual finite prime-free vectors. Their fixed-core, selection-energy,
and multiplier hypotheses cannot be silently substituted for it.

A second attempt tested whether choosing cutoffs with small harmonic
counterterm could make the existing complete tail bound sufficient.
The lexical `deningerHarmonicPartial` search and source follow-ups did
not supply the required cofinal selection theorem. Even granting the
stronger condition `H_N=0`, the existing certificate from
`DeletionQuotientTail.primitiveEnergy_le_harmonic_depth` is

```
4+2*N*L*(eta_N*(1+harmonic(L)))^2+N/L
  >= 2*N*L*eta_N^2+N/L >= 2*N*eta_N       (N>=0, L>0).
```

The last inequality follows from
`2*(L*eta_N)^2+1 >= 2*L*eta_N`. For the available positive rate constant
and `eta_N=B*exp(-(log N)^(1/3)/108)`, its right side divided by N^epsilon
tends to infinity for every fixed `0<epsilon<1`. This is a lower bound
on the *upper-bound certificate*, not on the actual energy. It shows
that optimizing L within this estimate, even at a vanishing harmonic
counterterm, cannot produce the required subpower ceiling. A stronger
estimate of the signed quotient-increment field is still needed.

Scratch validation of the three fixed-core/selection candidates stopped
at the missing transitive `XiCTaylorThetaTailPrimitiveRayInteriorSquare.olean`,
before their examples were checked. No dependency rebuild was attempted.
The elementary certificate inequality was checked separately with narrow
mathlib imports. No new Lean module, axiom audit, mathematical computation,
or umbrella build was needed. These attempts do not close the signed
source bound or RH; no route is retired and no universal-law entry is added.

## Completed argument assembly: audit against the compensated quotient source

The previous certificate calculation rules out obtaining a subpower bound
merely by optimizing tail depth, even after granting a vanishing harmonic
counterterm. The next attempt therefore kept the signed samples and their
compensating mass together.

Three corpus requests used OR matching and current source verification:

| Query | Budget / elapsed | Candidate lemmas / source arguments | Argument assembly |
|---|---:|---:|---|
| `compensated quotient sampling signed quadrature Mobius` | 120 / 120.010 seconds | 14 / 14 | deadline before completion |
| `Mertens quadrature` | 300 / 56.914 seconds | 8 / 8 | one proposed ingredient set |
| `moebius "bounded variation" "quotient sampling"` | 300 / 58.312 seconds | 10 / 10 | one proposed ingredient set |

The latter two requests finished without runtime errors or an unfinished
search stage; `partial` remained true solely because the semantic index
was incomplete. Their inventory covered 55,940 files, including 46,540
Lean files and 9,400 prose files. None returned `proof_ideas`. All 64
candidate/source occurrences matched current declaration-block hashes;
all still had `source_only` compiler status. The proposed ingredient sets
were explicitly marked `not_verified`.

The first proposed argument does not identify one mathematical source.
`MertensSecondPrimeRecipSum.mertensFloorError` is the prime-weight error
`sum_(p<=t) log(p)/p-log(t)`, integrated against `1/(t*log(t)^2)`.
`BeurlingSensitivity.mertensIntegrand` is the adjoined-prime density
`2*exp(beta*t)*(1-cos(gamma*t))`. The third ingredient, `RHTower.mertensM`
in `MobiusFriableLargestPrimeDecomposition`, is the actual Möbius sum.
The package gives no identities joining these different objects. Its
integrability theorem cannot be read as an estimate for the EDQ increment.

The second proposed argument combines a norm bound for each Möbius value,
bounded variation of a smooth prolate source, and the BV lattice estimate
`CCMBVMuntzSummation.abs_sum_le_variation`. Neither the norm bound nor the
prolate theorem supplies bounded variation of the actual reciprocal
Mertens field. The additional formal Dirichlet convolution identity does
not repair that missing hypothesis.

To audit the actual quadrature substitution, put

```
f_N(x) = M(floor(1/x))-M(N)   for 0<x<=1/N,
         0                  otherwise.
```

The reciprocal cells have lengths `1/(k*(k+1))`. Thus the existing
absolutely convergent increment-mass identity gives, on paper,

```
integral f_N = -H_N,
e_N(n) = sum_(j>=1) f_N(j/n) - n*integral f_N.
```

This is the correct compensated source. Every prime p>N produces a unit
jump at x=1/p, since `M(p)-M(p-1)=mu(p)=-1`. Infinitely many such jumps
accumulate at zero, so bounded variation on the full source interval
cannot follow from `|mu(p)|<=1`. A finite source truncation preserves an
explicit positive result, but also preserves the missing tail: define

```
f_(N,K)(x) = sum_(N<k<=K) mu(k)*1_(0,1/k](x),
Q_(N,K)(n) = sum_(j>=1) f_(N,K)(j/n)-n*integral f_(N,K).
```

It has variation at most `2*(K-N)`, integral `H_K-H_N`, and exact
quadrature `Q_(N,K)(n)=F_K(n)-F_N(n)`. Consequently
`e_N(n)=Q_(N,K)(n)+e_K(n)` at every coordinate. Truncating to obtain a BV
source therefore leaves the full error at K; pointwise convergence as
K grows is not a norm bound for that residual. These are applicability
calculations, not a retirement of EDQ or a new subpower producer.

Other inspected candidates also retain their missing inputs:
`Sieve.MoebiusMaximalWindow` transfers a supplied first moment to a second
moment with the window-length factor; `MobiusBlockDefectEnergyInterpolation`
retains the cubic block interpolation cost. Riesz compensation and theta
quadrature identities use their own kernels and do not identify the
complete EDQ covariance.

A narrow `lake env lean` scratch file checked the two public BV lattice
API names and the exact Möbius prime-prefix jump, with exit 0 and no
diagnostics. The continuous reciprocal-source calculations above were
not formalized in that check. No new Lean module, dependency rebuild,
umbrella build, axiom audit, or mathematical computation was performed.
The signed quotient discrepancy still has no required cofinal subpower
bound; RH remains unproved. Frontier and universal-law ledgers are unchanged.

## Ramaré decomposition of the physical source: recurrence audit

The attempted producer is a recurrence for the complete EDQ carrier energy,
with both prime-pair and rough-packet interactions retained. Two broad OR
searches used `--mode deep --budget-seconds 300 --max-rounds 2 --no-refresh
--per-module 1 --limit 12 --explore 0 --json`:

1. `Ramare "signed Gram" "largest prime"`;
2. `derive a contracting recurrence for full Mobius Gram energy by prime
   deletion retaining rough packet and signed mixed dilations`.

The first finished argument assembly in 89.509 seconds, with no runtime
errors. Its only unfinished item was incomplete semantic coverage. It
returned 12 candidate lemmas, 12 source arguments, no proof ideas, and one
unverified ingredient set, “Prime diagonal and off-diagonal sum equality.”
That set combines the existing exact Ramaré Gram decomposition and bilinear
identification; it supplies neither a sign nor an upper bound. The second
request reached its 300.013-second budget during filtering/judgment, with
interrupted text/source retrieval, malformed local-model JSON and a semantic
retrieval deadline. It returned another 12 candidate lemmas and 12 source
arguments, but no proof ideas or ingredient sets. Its trace reached round 2.

All 48 candidate/source-argument occurrences matched current declaration-block
hashes when checked. All carried `source_only` compiler status and unchecked
applicability. The first inventory covered 55,942 files, including 46,540 Lean
and 9,402 prose files, and 720,488 declarations. Semantic coverage was incomplete:
2,167,627 ready out of 2,331,223 expected in the first result and 2,167,881 out
of 2,331,272 in the second. The second inventory snapshot was pending. These
results do not establish exhaustive mathematical coverage.

Write `b_d(u)=bdGenReal(1/d,u)`, `G_N=sum_(d<=N)mu(d)*b_d`, and let P be
a finite set of primes. Define the following finite physical packets:

```
omega_P(m) = card {p in P : p divides m},
U_(P,N) = sum_(n<=N, omega_P(n)=0) mu(n)*b_n,
A_p = sum_(m<=floor(N/p), p not dividing m) mu(m)/(1+omega_P(m))*b_m,
B_p = sum_(m<=floor(N/p), p not dividing m) mu(m)/(m*(1+omega_P(m))),
Z_p = D_p A_p+B_p*b_p,       (D_p f)(u)=f(u/p)/p.
```

All integer sums start at 1. Ramaré's identity, the vanishing of mu(p*m)
when p divides m, and `b_(p*m)=D_p b_m+b_p/m` give the exact paper identity

```
G_N = U_(P,N)-sum_(p in P) Z_p,
||G_N||^2 = ||U_(P,N)||^2+sum_p ||Z_p||^2
            +sum_(p != q) Re<Z_p,Z_q>-2*sum_p Re<U_(P,N),Z_p>.
```

The prime-pair sum is ordered. Each packet norm includes its full cofactor
cross terms and affine correction. The existing O(log N) bound for the
individual-generator diagonal is not a bound for this packet diagonal.
A narrow foreground `lake env lean` scratch check instantiated
`Sieve.sum_eq_ramare_add_rough` with `mu(n)*bdGenReal(1/n,u)` and the literal
cutoff `Icc 1 N`; it exited 0 without diagnostics. That check certifies the
pointwise Ramaré splitting, not the entire paper calculation or a growth bound.

Two choices of P expose the actual recurrence requirements:

- For `P={p prime : N/2<p<=N}`, every cofactor is 1. Hence `A_p=0`, `B_p=1`,
  and `Z_p=b_p`. The existing `DeletionPrimePacket.packet_norm_sq_eventually_lower`
  gives squared norm at least `N/(8*32768^2*log(N)^2)` for their sum.
  These packets reinforce each other; cancellation with U is essential.
  This is the previously formalized weighted-prime result applied to the
  proposed splitting, not a new obstruction theorem.
- For P containing every prime up to N, the rough packet vanishes because
  only n=1 remains and `b_1=0`. All cofactor cutoffs are at most N/2, but their
  coefficients are `mu(m)/(1+omega(m))`, with the p-divisibility exclusion
  retained. `Sieve.DampedCofactorIntegral` already represents these weights
  by the integral of `mu(m)*t^omega(m)` over `0<=t<=1`.
  `DampedCofactorTransfer` assumes the uniform saving it transfers. No bound
  for the full physical packets or their signed sum follows from that identity.

Conditional negativity of the Ramaré incidence complement also does not
close the recurrence: its scalar centering condition is the vanishing of
the total coefficient. Substituting the actual pointwise EDQ coefficients
makes that total G_N(u), whose squared integral is the unknown source energy.
The finite spectral-centering classification concerns logarithmic phases;
it is not a theorem that centers the physical history.

The second search's smaller-cutoff interpolation bound in
`MobiusDivisorPrimeFibreInterpolation` controls the copied packet in its
retained-label space. Its prime fibre carries a square-root-p factor and
the full merger retains a signed overlap. The late-prime contraction in
`MobiusDivisorNonemptyEnergy` explicitly subtracts the empty-label head square;
it does not bound the complete energy. Theta dilation inversion uses its
theta source, and the retrieved EDQ logarithmic saving is the existing
`N/log(N)^q` estimate. None supplies the missing subpower bound.

No new unconditional source estimate was obtained. No Lean module, dependency
build, umbrella build, axiom audit, or mathematical computation was added.
No route is retired by this audit; the full signed source bound and RH remain
open. The frontier map and route-independent STATUS ledger were left unchanged.

## Growing-prime correction budget for the damped cofactor

**Prime-mass budget and all-prime majorant obstruction.** The all-frequency theorem
`Sieve.exists_norm_sum_dampedTwist_le_rate` has constants and an eventual
threshold uniform in the finite prime set P. It bounds the damped twisted sum
by `K*C(P,c)*N*exp(-v)`, where

```
C(P,c) = product_(p in P) (1+p^(-c))/(1-p^(-c)),
v = (log N)^(1/20),
c = routeTContourLeft A delta (abs(tau)+N).
```

Thus fixed-P quantifiers are not the obstruction to using that theorem with
all primes up to N. The explicit correction is. For `c>=1/2`, put
`S(P,c)=sum_(p in P)p^(-c)`. The dependency-closed paper comparison is

```
exp(S(P,c)) <= C(P,c) <= exp(5*S(P,c)).
```

For `x=p^(-c)`, one has `0<x<=3/4`. The lower bound follows from
`1-x<=exp(-x)`; the upper follows from `1+x<=exp(x)` and
`1/(1-x)<=exp(4*x)`, since `(1-x)*(1+4*x)>=1` on this interval.
Multiplying the factor bounds proves the comparison. Consequently
`5*S<=v-r` suffices for `C*exp(-v)<=exp(-r)`, and `S<=v-r` is necessary.
This is a positive prime-mass budget for preserving the contour saving.

For `P=primesLE N`, `N>=1`, and `c>=1/2`, the finite Euler product gives

```
C(P,c) >= product_(p in P) (1-p^(-c))^(-1)
       >= sum_(1<=n<=N) n^(-c)
       >= N^(1-c).
```

Every positive integer up to N is supported on these primes, so the
convergent nonnegative smooth-number expansion contains the displayed sum.
Monotonicity gives its lower bound. No prime-count estimate is needed.
The existing contour data give `(1-c)*log N>=10*v`, uniformly for
`abs(tau)<=N`, eventually in N. Hence

```
C(primesLE N,c)*exp(-v) >= exp(9*v).
```

At zero frequency this product tends to infinity. The displayed contour
majorant, even divided by N, therefore cannot give a saving at the
all-prime substitution. This is a
statement about that upper-bound formula, not a lower bound on the actual
damped cofactor or the EDQ source. A smaller prime set can meet the mass
budget but restores the rough packet and its mixed correlations.

The six public declarations in
`RHTower.Sieve.DampedCorrectionMassBudget` formalize the two mass bounds,
the all-prime power lower bound, both budget implications, the uniform
contour lower bound, and divergence at zero frequency. Scratch verification
and `lake build --old GaloisForLFunctions.RHTower.Sieve.DampedCorrectionMassBudget`
passed. All six new declarations have only `propext`, `Classical.choice`, and
`Quot.sound`; no extra axiom or proof debt was introduced. The module is
wired into the RHTower umbrella, generated indexes are refreshed, and
`scripts/formal_tools.py lint` passed with existing file-size warnings.
No umbrella build was run.
The growing-prime substitution in
`Sieve.exists_norm_sum_dampedTwist_le_rate` was also checked in Lean,
with the explicit correction retained. The all-prime Ramaré architecture
remains open: a successful estimate must retain cancellation lost by this
correction or control the rough packet and all mixed correlations for a
smaller prime set.

**Deep-search audit.** Two OR searches used `--mode deep --any`, two rounds,
`--budget-seconds 300`, and cached corpus data:

```
dampedOmegaMoebius "Ramare cofactor" "prime-count deformation"
"divisor transform" "inverse prime count" "binomial integral"
```

Both completed argument assembly (50.254 s and 41.193 s). The inventory
contained 55,947 files and 720,511 declarations; semantic coverage was
incomplete, so both responses were marked partial. All 56 returned
candidate/source-argument occurrences matched current declaration-block
hashes, but were source-only with unchecked applicability. The generated
prime-power-ladder proposals concern valuation powers and disjoint support,
and supply no estimate for the Ramaré weight `mu(m)/(1+omega_P(m))`.
Direct source inspection instead found the uniform-in-P contour theorem
above. The useful bridge is its explicit prime-mass budget; the full signed
source estimate and RH remain open. No numerical experiment was run.


## Adaptive prime window and the actual cofactor boundary

**Current obstruction: the literal all-prime cofactor has a logarithmic
boundary layer.** Put omega(n)=card(n.primeFactors), a(n)=mu(n)/(1+omega(n)),
and A(x)=sum_(1<=n<=x) a(n). The following paper argument proves

```
F(s) = sum_(n>=1) a(n)*n^(-s),
F(s)*log zeta(s) -> 1                         (real s -> 1+),
A(x) is not O(x/(log x)^q)                    for every fixed q>1.
```

The statement is about the actual signed coefficient. It is stronger than
failure of the preceding Euler-correction majorant. It does not assert a
partial-sum asymptotic, a lower bound at every cutoff, or an obstruction to
the complete signed EDQ source.

**Dependency-closed paper proof.** For s>1, absolute convergence, boundedness
of u^omega(n) on [0,1], and the Euler product give

```
H_s(u)=sum_n mu(n)*u^omega(n)*n^(-s)=product_p(1-u*p^(-s)),
F(s)=integral_0^1 H_s(u) du.
S(s)=sum_p p^(-s),  B(s)=sum_p -log(1-p^(-s))=log zeta(s).
```

For 0<=x<1 and 0<=u<=1, concavity of log gives
u*log(1-x)<=log(1-u*x); the elementary exponential inequality gives
1-u*x<=exp(-u*x). Multiply over finite prime sets and pass to their
convergent products. Consequently

```
exp(-u*B(s)) <= H_s(u) <= exp(-u*S(s)),
(1-exp(-B(s)))/B(s) <= F(s) <= (1-exp(-S(s)))/S(s).
```

For 0<=x<=1/2, the logarithm inequalities give
0<=-log(1-x)-x<=2*x^2. Therefore
0<=B(s)-S(s)<=2*sum_p p^(-2), uniformly for s>1. The pole of zeta at one
implies B(s)->infinity and B(s)~log(1/(s-1)); alternatively, divergence of
sum_p 1/p directly proves S(s)->infinity. The squeeze proves the displayed
boundary asymptotic and F(s)->0.

Suppose |A(x)|<=C*x/(log x)^q eventually, with q>1. Finite-prefix absorption
and Abel summation give F(1+t)=(1+t)*integral_1^infinity A(x)*x^(-2-t) dx.
The integral of |A(x)|/x^2 converges; dominated convergence identifies its
value at t=0 with lim F(1+t)=0. Subtract this zero value. Since
0<=1-exp(-t*log x)<=min(t*log x,1), the difference is bounded by a constant
times t plus

```
integral_1^infinity v^(-q)*min(t*v,1) dv.
```

Split at v=1/t. This is O(t^(q-1)) for 1<q<2, O(t*log(1/t)) for q=2,
and O(t) for q>2. Every bound is o(1/log(1/t)), contradicting the positive
boundary asymptotic. Removing any fixed finite set of primes from the
coefficients gives the same proof: remove those terms from S and B. In
particular, imposing p not dividing m for a fixed Ramaré prime p does not
repair the proposed super-polylogarithmic cofactor estimate.

**Positive survivor and required cancellation.** The exact Laplace squeeze
above identifies the cofactor's boundary scale without any assumption on RH.
The fixed-prime exclusion version shows why independently bounding each
all-prime cofactor by an arbitrary logarithmic saving is unavailable. The
complete source still retains cancellations between prime packets and their
cutoff-dependent counterparts. Neither replacing this source by its cofactor
norms nor dropping its full tail is justified.

**Lean status.** Scratch verifies the literal all-prime damped coefficient,
its multiplicativity, absolute summability, Euler product, cofactor integral
interchange, Laplace squeeze, and the unconditional boundary limit
`tendsto_fullPrimeCofactorSeries_mul_log_zeta`. The coefficient identity
`fullPrimeCofactor_eq_ramare` joins it to the existing cutoff-dependent
Ramaré coefficient. The new leaf
`RHTower.Sieve.FullPrimeCofactorBoundary` passes scratch checks and
`lake build --old GaloisForLFunctions.RHTower.Sieve.FullPrimeCofactorBoundary`.
It is wired into the RHTower umbrella without building that umbrella.
All 16 new public theorems were audited in a temporary scratch file;
they use only `propext`, `Classical.choice`, and `Quot.sound`. No added axiom
or proof debt was introduced. Generated indexes are refreshed, and formal
lint passes with existing file-size warnings. Its first run caught an
unrelated concurrent module before its umbrella import appeared; the
second run passed after that import was present. The partial-sum obstruction
and the fixed-excluded-prime extension remain paper results; their Abel and
exclusion transfers have not been formalized. No route is retired.

**Adaptive-contour alternative, paper estimate.** The all-heights Perron theorem
leaves height U independent of cutoff N. Let L=log N and choose
Q=exp(L^(19/20)), U=exp(L^(19/18)), H=N*exp(-L^(1/40)), d=1+1/L.
For abs(tau)<=N, its height argument lies between U and 2U eventually.
The exact binary-shell definitions give

```
c1/((log U)^(9/10)*(log log U)^2) <= eta=1-c
                                                <= c2/(log U)^(9/10).
```

The constants depend only on the fixed contour data. For the upper bound,
clog bounds log U from below and nthRoot(10,L)+3 exceeds L^(1/10);
the strip denominator and zero-free-budget denominator are bounded below by
positive constants. The lower bound is the existing explicit contour-shift
envelope. Thus eta*log Q is bounded, while
eta*L is bounded below by a positive multiple of L^(1/20)/(log L)^2.
For every prime p<=Q, p^(-c)<=exp(c2)/p, so Mertens' reciprocal-prime bound
makes the correction polynomial in log Q. The logarithm of the contour-edge
constant is O((log L)^2); d lies inside the right contour because
1/L=o(eta). In the four-edge formula, the right-tail and both horizontal
terms contain N/U times exp(O(L^(1/40)+(log L)^2)); the left edge is at most
N*exp(-eta*L+2*L^(1/40)+O((log L)^2)); smoothing costs H+1.
Each is O(N*exp(-L^(1/40))). This proves a uniform growing-prime-window
cofactor estimate on paper. Its exact parameter substitutions are not
formalized. It retains a rough packet, and its saving alone does not imply
subpower growth of the complete physical source.

**Broad recent-paper transfer tests.** Broad arXiv searches for `dephasing`,
`renewal`, `hypocoercivity`, and `pinning` were sorted by announcement date;
some endpoints return older cached pages, so dates were checked on papers.
[Eberle--Lörler, 12 July 2026](https://arxiv.org/html/2607.10801v1), Theorem 18,
uses an invariant probability measure, a contraction semigroup, a positive
second-order collapse gap, and a bound on the interaction between two
orthogonal subspaces. Its two-point generator distinguishes time-averaged
relaxation from ordinary relaxation. In EDQ, damping is diagonal in the
coefficient labels but the physical generators have a non-diagonal Gram
matrix. Dissipativity in that physical norm requires controlling the mixed
pairing with the prime-count generator; the paper does not establish that
arithmetic inequality. Its theorem cannot currently supply the source bound.

[Zhang--Shi--Wang--Yang, 6 September 2026](https://arxiv.org/html/2609.06632v1),
Theorems 1 and 3, retains a weighted off-diagonal anomaly in its coherence
identity and requires an explicit anomaly threshold for its logarithmic
bound. The trajectory weights may be signed or complex. Normalizing the pure state of the coherent physical sum divides by its
unknown energy. Normalizing the coefficient Gram instead retains
E_N=D_N*1^*rho_N*1, where D_N is the known diagonal trace; the remaining
coherent readout is not bounded by the paper's coherence-change theorem.
An arithmetic channel and its anomaly bound are also unproved. Neither
recent mechanism closes the covariance obstacle; the useful tests retain
both the physical norm and its forcing/cross terms.


**Corpus search and method audit.** Seven broad OR queries used `--mode deep`,
two rounds, cached content, and bounded requests:

```
"multiplicative martingale" "Ramare covariance" "rough Mobius"
"dilation square function" "bilinear cancellation" "signed covariance"
"multiplicative difference" Cotlar "Moebius short interval" "bilinear Type II"
"damped contour" "prime correction" "contour shift"
deletion semigroup dissipation with affine forcing and mixed covariance
inverse prime count damped Euler product logarithmic singularity Abel summation
Abel summation logarithmic partial sum bound boundary Holder continuity
```

The first four completed argument assembly with partial indexing coverage;
the last three returned deadline snapshots with interrupted retrieval/ranking
stages and no assembled proof ideas or ingredient sets. Semantic coverage
remained incomplete (the last snapshot had 2,183,768 of 2,333,081 items ready).
All 168 candidate/source-argument occurrences matched current declaration-block
hashes; their compiler metadata remained source-only. Generated ingredient
sets in the completed searches did not discharge the covariance bounds.
In particular, the adaptive-contour proposal misread a lower divergence bound
as an upper bound and was rejected. Source inspection of
`MobiusHalfSelectionEulerProduct` supplied the useful multiplicative Euler
product method; the new proof changes the coefficient to full variable
damping and verifies that transfer in Lean. The final Abel search returned
finite summation-by-parts and power-bound receivers, without a completed
logarithmic boundary-continuity transfer. No numerical experiment was run.

## Prime-count damping: actual physical amplification

The producer under test is contraction of the literal finite physical source
under coefficient damping by the number of distinct prime factors. Write

```
H_N(u) = sum_(1<=n<=N) mu(n)*u^omega(n)*b_n,
P_N = sum_(p<=N, p prime) b_p,
t_N = ||P_N||/(8*sqrt(N)).
```

Thus H_N(1) is the negative of the existing modular approximant. All norms
below are its full carrier norm, including the infinite physical tail.
The following paper proof directly tests contraction on this actual source.

Every nonzero nonprime coefficient other than n=1 has omega(n)>=2; b_1=0.
For 0<=u<=1, the existing diagonal bound ||b_n||^2<=2/n and the telescoping
sum of reciprocal square roots therefore give

```
sum_(1<=n<=N) ||b_n|| <= 4*sqrt(N),
||H_N(u)+u*P_N|| <= 4*u^2*sqrt(N).
```

In particular 0<=t_N<=1/2. Reverse triangle inequality at this value gives

```
||P_N||^2 <= 16*sqrt(N)*||H_N(t_N)||,
||P_N||^4 <= 256*N*||H_N(t_N)||^2.
```

All integer-generator Gram entries are nonnegative. Hence the all-prime
packet dominates the existing upper-half packet in squared norm. With
C=8*32768^2, its existing unconditional prime-shell bound gives eventually

```
N/(256*C^2*(log N)^4) <= ||H_N(t_N)||^2.
```

The already proved full-source estimate E_N=o(N/(log N)^q), for every fixed
q, then implies E_N*(log N)^q/||H_N(t_N)||^2 -> 0 for every fixed q.
Consequently no fixed multiplicative contraction budget works uniformly in
damping value and cutoff. This is stronger than a generic nonorthogonal
matrix counterexample: it concerns the actual signed arithmetic source.
It does not rule out a forcing-aware estimate at u=1 or retire EDQ. The
positive survivor is the quantitative small-damping amplification law and
its full quadratic remainder estimate. Paper proof and Lean formalization
are complete in `EulerDeletionPrimeCountAmplification.lean`, namespace
`RHTower.PrimeCountDamping`. The required absolute cofinal subpower source
ceiling remains open.

The 15 public theorems include `source_add_prime_norm_le`,
`aperture_energy_eventually_lower`,
`source_relative_energy_log_pow_tendsto_zero`, `eventually_amplifies`, and
`not_exists_uniform_damping_budget`. A scratch check passed, followed by the
warning-free leaf audit
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionPrimeCountAmplification`.
Only this leaf compiled in that final build (181 seconds); the 13,641-job
display includes cached dependencies. Two missing dependency oleans were
resolved beforehand using individual leaf targets. All 15 new public
theorems were checked through a `/tmp` axiom-audit file and depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The umbrella import is wired;
no umbrella build was run. Generated indexes were refreshed and formal lint
passed. No numerical experiment, frontier-map edit, or universal-law-ledger
edit was made by this agent for this result.

An additional algebraic observation, not needed for that proof, is
sum_(d|n) mu(d)*u^omega(d)=(1-u)^omega(n) for n>=1. Integration over u in
[0,1] gives sum_(d|n) fullPrimeCofactor(d)=1/(1+omega(n)). Prime counting
thus cancels this positive divisor-convolution bulk at u=1. This identifies
the cancellation; it supplies no bound on the remaining truncated divisors.

**Recent broad-paper intake and premise audit.** Broad `commutation` and
`coagulation` arXiv searches were sorted by newest announcement, after broad
web queries mostly returned older material. The following September papers
were read at the relevant theorem/hypothesis level; none is used as an axiom
or as evidence that the arithmetic estimate holds.

- [Shen--Wang--Zhi, 9 September 2026](https://arxiv.org/html/2609.09938v1):
  Theorem 1.1 permits freely chosen commutator factors. Theorem 1.2 gives
  a dimension-dependent obstruction when a factor must be diagonal in a
  prescribed basis. EDQ fixes the prime-count diagonal and the physical
  Gram metric. The free-factor theorem therefore does not establish its
  mixed-energy sign. Its reported Lean implementation was not imported.
- [Bellavita--Stylogiannis, 8 September 2026](https://arxiv.org/html/2609.09453v1):
  Theorem 4.8 bounds sampled Mellin product defects for the kernel classes
  of Definition 4.3. That definition requires continuity away from a finite
  exceptional set and a weighted variation estimate. The physical sampled
  fractional-part kernel kappa(v)={1/v} has jumps at every v=1/k. Thus this
  theorem cannot directly bound its defect. Even a bounded operator estimate
  alone would retain the linear coefficient-energy scale.
- [Shinoda, 2 September 2026](https://arxiv.org/html/2609.02960v1):
  The scalar moment relation follows under an explicitly approximate local
  scale-covariance reduction of parent-resolved stationary balance. No such
  stationary positive transfer law has been established for the full signed
  EDQ source. The paper retains transitions across the parent window boundary;
  its moment relation gives no license to omit the arithmetic tail.
- [Guo--Huang, 9 September 2026](https://arxiv.org/html/2609.09599v1):
  The curvature identity splits a quantum Markov generator using the BKM
  adjoint associated with a full-rank stationary state. Its Cauchy--Schwarz
  bound retains both dissipative and transport activities. Coefficient
  diagonality does not identify that adjoint with the physical Gram adjoint.
  The amplification proof above supplies a direct arithmetic test against
  silently assuming physical contraction.

**Corpus search and method audit.** Four further requests used deep mode,
180-second budgets, two rounds, cached content, and both declaration and
source-argument lanes. Queries were `prime count generator Gram commutator
physical damping energy`, `"nonorthogonal damping" "anticommutator positivity"
"sampled ratio" "Mellin product"`, `"Möbius partial sum" "fractional part
continuity" "prime count" "dissipativity"` (all OR), and the mechanism query
`Möbius damping divisor convolution equals product over distinct prime
divisors binomial expansion`. All 100 candidate/source-argument occurrences
matched current declaration-block hashes; compiler metadata was source-only.
The first hit its retrieval/reranking deadline; the last left filtering and
judgment incomplete. Other inventories covered roughly 56,100 files and
721,747 declarations with source/semantic gaps. Generated premise groups
mixed unrelated damping, Floquet-density, measurability, or convolution facts
and did not prove the requested inequalities. Exhaustive source-text follow-up
located the actual prime-packet floor, global Möbius logarithmic saving,
generator diagonal bound, reciprocal-square-root telescope, and squarefree
prime-power classification used in the new direct proof.


## Prime-count endpoint: prime-power forcing and spatial variance

The current attack asks whether the count-damping path becomes inexpensive near
its arithmetic endpoint u=1. Set J_N=H_N'(1), with the full Hilbert carrier from
the preceding section. Finite divisor convolution gives, for n>=1,

```
sum_(d|n) mu(d)*u^omega(d) = (1-u)^omega(n),
sum_(d|n) mu(d)*omega(d) = -1_(n is a prime power).
```

Consequently, writing Q(k)=#{1<=m<=k: m is a prime power} and
h_N=sum_(n<=N) mu(n)*omega(n)/n, the exact cell numerator for k<=N is
k*h_N+Q(k). The full energy therefore dominates

```
sum_(1<=k<=N) (k*h_N+Q(k))^2/(k*(k+1)).
```

Minimizing this finite quadratic over the scalar h leaves the explicit
weighted spatial variance C-B^2/A, where
A=sum k/(k+1), B=sum Q(k)/(k+1), C=sum Q(k)^2/(k*(k+1)).
This variance includes cross-cell mismatch and is independent of h_N.
The complete infinite tail is retained on the upper side of the inequality.

The following asymptotic consequence has a paper proof; its Lean proof is
pending. For each fixed 0<alpha<1, prime counting and the elementary bound
O(sqrt(x)*log(x)) for proper prime powers give Q(x)~x/log(x). Uniformly on
[N^alpha,2*N^alpha], Q(k)/k=(1/alpha+o(1))/log(N); uniformly on [N/2,N],
Q(k)/k=(1+o(1))/log(N). The two ranges are eventually disjoint. For any real
h, at least one range stays a fixed positive multiple of 1/log(N) away from
-h. Its length is at least a fixed multiple of N^alpha, and k/(k+1)>=1/2.
Thus ||J_N||^2>=c_alpha*N^alpha/(log N)^2 eventually, with c_alpha>0.
This excludes a subpower absolute bound on the endpoint count derivative.
It does not bound ||H_N(1)|| or its signed pairing with J_N. An energy
transport proof must still exploit that pairing; bounding the forcing by
its norm alone loses the needed cancellation.

Two preliminary upper-bound attempts fail at identifiable estimates.
The exact convolution mu(n)*(1-t)^omega(n)=(mu * t^omega)(n) transports
smaller cutoffs, but its positive dilation majorant contains
sum_(p<=N) t/sqrt(p), which grows at fixed t. Grouping the endpoint Taylor
jets by exact distinct-prime count preserves the convolution support but
supplies no bound uniform in jet order and cutoff. Neither calculation is
an RH proof. No numerical experiment is needed for these deductions.

Broad newest-first arXiv searches for `avalanche` and `screening` supplied
two September premise checks. [Janssens--Moll--Schindler, 8 September 2026](https://arxiv.org/html/2609.08666v1)
prove variance reduction for normalized positive cluster weights, using
independent equal-variance cluster times and neglecting time-ordering
correlations in that analytical proof. EDQ's signed physical Gram form does
not satisfy those assumptions. [Huang--Breizman, 7 September 2026](https://arxiv.org/html/2609.08051v1)
use a marginal-stability balance, a one-dimensional spectral-ridge assumption,
and a capped regularized response in a reduced kinetic model. These are
model closure assumptions, not a proof of EDQ's arithmetic covariance sign.
No external result is imported into Lean.


A stronger paper consequence uses the corpus theorem
`Sieve.primeCounting_sub_logIntegral_isBigO`, whose current declaration hash
was verified against the deep-search result. Integrating the logarithmic
integral twice by parts and absorbing the proper prime powers gives
Q(x)=x/log(x)+x/log(x)^2+O(x/log(x)^3). Uniformly for t in [1/4,1],
Q(tN)/(tN)=1/L+(1-log(t))/L^2+O(L^-3), L=log(N).
The values on [N/4,N/3] and [2N/3,N] have a gap at least
log(2)/(2*L^2) eventually. Both windows have length proportional to N.
Thus the sharper lower bound is ||J_N||^2>=c*N/(log N)^4 for some c>0.
This asymptotic lower bound is paper-proved, not yet Lean-closed.

It also yields a paper-proved local curvature statement. With K_N=H_N''(1),
the elementary bound omega(n)<=log(N)/log(2) for squarefree n<=N and the
already formalized sum of generator norms give ||K_N||=O(sqrt(N)*log(N)^2).
The existing unconditional raw-source estimate gives
||H_N(1)||*||K_N||=o(N/log(N)^4). Differentiating the finite Hilbert polynomial
therefore yields

```
(d^2/du^2)||H_N(u)||^2 at u=1
  = 2*||J_N||^2 + 2*Re <H_N(1),K_N>
  = (2+o(1))*||J_N||^2 > 0 eventually.
```

This is curvature of the literal full-energy path, with its mixed term
controlled rather than discarded. Its Lean proof is pending. It neither
controls the first derivative nor bounds the energy height at u=1; local
convexity therefore does not provide the missing RH producer.

Four current deep searches covered endpoint count convolution, factorial
jets/resolvents, prime-count curvature, and divisor/powerset methods. All
returned partial results. Three coverage snapshots were pending; the resolved
snapshot inventoried 56,124 files (46,699 Lean), with pending/stale compiler
coverage. Candidate lemmas and source arguments were inspected. The proposed
resolvent ingredient group remained unverified and had no physical source
identification. The squarefree truncated-divisor theorem also had a verified
current source hash, but its squarefree hypothesis does not establish the
required identity for arbitrary n. The direct multiplicative arithmetic-
function proof and derivative were used instead; their validation is listed below. Search metadata
marked these external candidates `source_only`; no compiler closure is
inferred from retrieval status.


The positive invariant admits a sharper paper evaluation:

```
jetVariance(N) * (log N)^4 / N -> 1.
```

Here is a dependency-closed asymptotic argument from the preceding prime
counting estimate. Put L=log N, t_k=k/N, w_k=k/(k+1), and
r_k=L^2*(Q(k)/k-1/L). For k>=N*exp(-sqrt L), the two-term expansion above
implies r_k=1-log(t_k)+O((1+log(t_k)^2)/L), uniformly in that range.
For the omitted head, Q(k)/k<=1 bounds its normalized squared r-mass by
O(exp(-sqrt L)*L^4). Its normalized log moments also tend to zero.
The integral comparison for decreasing (-log t)^j gives bounded normalized
fourth log moments and convergence of the first two moments to 1 and 2;
these are the elementary integrals over (0,1). The weights w_k can be replaced
by 1 with a vanishing error, using the same head split. Hence
A/N->1, (sum w_k*r_k)/N->2, and (sum w_k*r_k^2)/N->5.
Translation invariance of variance now gives the displayed limit as 5-2^2=1.
This proves the intrinsic prime-power forcing scale with leading constant
one, independent of the actual harmonic scalar. Formalization of this limit
remains pending; the exact finite invariant and its physical lower bound are
the statements formalized in the module listed below.

A fifth deep/method query on second-order logarithmic variance returned
partial results with pending coverage. Candidate and source-argument lanes
were inspected. It found a bounded-variation Riemann-sum error theorem,
ordinary covariance identities, and scalar log-weight telescopes, but no
ready-made theorem identifying this prime-power variance asymptotic. These
hits are not treated as verified applications.


The exact finite part is now formalized in
`EulerDeletionPrimeCountEndpointVariance.lean`, namespace
`RHTower.PrimeCountDamping`. Its 13 public theorems prove the damped divisor
identity, prime-power derivative support, full carrier derivative, exact
infinite energy series, finite prefix bound, scalar square completion,
sharp/nonnegative/monotone variance, and pairwise determinant identity.
`jetVariance_le_endpointJet_energy N` is the unconditional actual-source
lower bound. The full asymptotic limit and eventual strict curvature remain
paper results, explicitly outside this module's claims.

The scratch check and all 13 new-theorem axiom checks passed with only
`propext`, `Classical.choice`, and `Quot.sound`. The final leaf command
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionPrimeCountEndpointVariance`
passed in 133 seconds, compiling only that leaf; its 13,642-job count includes
cached dependencies. The umbrella import is wired, with no umbrella build.
The actual cofinal subpower bound on the undamped source remains open.
The frontier map was not edited by this agent. The universal ledger already
separates energy shape from the value at a minimum, so no duplicate entry was
added. No numerical experiment was run.

Generated indexes were refreshed and formal lint passed (existing large-file
warnings only). The final source has no new warnings. All eight owned
temporary files were removed, and all Lean/search processes started for
this result have finished.


## Endpoint signed pairing: full-tail profile coupling [BRIDGE]

The target remains the signed physical covariance bound, not the size of an
isolated derivative. The current derived question is whether the continuous
prime-power forcing profile can be orthogonal to a right-half-plane source
mode. This is a bridge question exposed by the finite endpoint variance;
it is not a new primary RH conjecture.

For x>0 define the real seed b(x)={x}/x and

```
j(x) = integral_x^infinity {v}/v^2 dv,
f_rho(x) = x^(rho-1) integral_x^infinity {v} v^(-rho-1) dv,
C_rho = integral_0^infinity f_rho(x) j(x) dx.
```

The coupling is linear in f_rho. In Lean's conjugate-linear-first convention
it is `inner complex j f_rho`, not the reversed inner product. For
Re(rho)>1/2 these are square integrable on the full positive ray. The same
holds at Re(rho)=1/2 when zeta(rho)=0. The following identity is proved on
paper below; it is not yet formalized:

```
Re(rho*C_rho) = (Re(rho)-1/2)*||f_rho||_2^2 + ||j||_2^2/2 > 0.
```

Here are the full boundary and regularity checks. Both tail primitives are
locally absolutely continuous; their differential equations hold almost
everywhere, with no differentiation of the fractional-part jumps:

```
x*j' = -b,       x*f_rho' = (rho-1)*f_rho-b.
```

At infinity, |f_rho(x)|<=1/(Re(rho)*x) and 0<=j(x)<=1/x. At zero, j(x)
is -log(x)+j(1). For 1/2<Re(rho)<1 the full fractional Mellin identity gives
f_rho(x)=-(zeta(rho)/rho)*x^(rho-1)-1/(1-rho) on (0,1).
At a critical zero the first term vanishes. At Re(rho)=1 the elementary
head integral gives O(1+|log x|); at Re(rho)>1 it gives O(1), with the
exception rho=1 already covered by f_1=j. These estimates prove L2
integrability and vanishing at both ends of x*|f_rho|^2, x*j^2, and
x*f_rho*j. All product integrals below are absolutely integrable by
Cauchy--Schwarz, since b also lies in L2.

Integrate the derivative of x*f_rho*j on [epsilon,R], then pass to the
endpoints. It gives rho*C_rho=integral f_rho*b+integral b*j. Integrating
the derivatives of x*|f_rho|^2 and x*j^2 gives respectively
Re(integral f_rho*b)=(Re(rho)-1/2)*||f_rho||^2 and
integral b*j=||j||^2/2. Finally j>0 on (0,1), so its squared norm is
strictly positive. In particular C_rho cannot vanish. The full tail is
essential to this proof; no sign of a truncated mixed term is assumed.

The finite-source transfer is still open. The derived asymptotic candidate
is `(log N)^2*J_N(N*x) -> j(x)` in the rescaled L2 carrier, extending the
physical source by zero below its original left endpoint. A proof must
retain the harmonic correction and control both ends of the rescaled ray.
The profile identity alone does not prove this convergence, the sign of
`Re <H_N(1),J_N>`, or a subpower bound for `||H_N(1)||^2`. In particular a
positive value of Re(rho*C_rho) does not fix the phase of an arithmetic
coefficient multiplying the rho mode. The endpoint-optimization attempt
therefore has not supplied the missing energy estimate.

Broad recent arXiv searches for `entrainment` and `rejuvenation` led to
[Massas--Margaliot, 28 July 2026](https://arxiv.org/html/2607.25435v1).
Their translation-flow proof combines an exact weighted telescoping
identity with periodic quadratic-energy balance; positivity uses positive
rates and occupancies in a fixed interval. EDQ has no established
identification satisfying those assumptions. The useful method was to
keep the complete boundary term while deriving a mixed-energy identity,
which produced the paper calculation above. No external theorem or
numerical result is imported into Lean.


### Derived arithmetic-to-carrier transfer: proof under audit

A second bridge attack targets the missing norm transfer directly. Write
A(x)=sum_(n<=x) mu(n)*omega(n), M(x)=sum_(n<=x) mu(n), and Q(x) for the
prime-power count. Möbius inversion gives the exact identity

```
A(x) = -sum_(m<=y) mu(m)*Q(x/m)
       -sum_(q prime power <= x/y) (M(x/q)-M(y)),
```

for integer 1<=y<=x. The second sum includes its boundary correction.
With y=floor(exp(sqrt(log x))), the existing arbitrary logarithmic
Mertens bound makes this second term O_R(x/(log x)^R) for any fixed R.
Indeed its absolute value is bounded by
C_K*x/(log y)^K * (1+sum_(q<=x/y)1/q), and the last sum is at most
1+log x. The prime-counting error allows the logarithmic-integral
expansion of Q(x/m) to any fixed order uniformly for m<=y. Expanding
1/(log x-log m), retaining enough terms before estimating the remainder,
and using the Möbius harmonic logarithmic moments gives an expansion

```
A(x) = x*sum_(2<=j<=R) c_j/(log x)^j + O_R(x/(log x)^(R+1)), c_2=1.
```

The zero-order moment is zero and the first logarithmic moment is -1;
these account respectively for the absent 1/log x term and c_2=1.
The higher moments exist by the corpus's arbitrary-logarithmic harmonic
decay and Abel summation. The same argument supplies arbitrary-logarithmic
rates for their tails. To justify the uniform Taylor remainder, expand
beyond 2R+4 terms while log m<=sqrt(log x); the absolute harmonic sum
costs only O(sqrt(log x)). Terms beyond the desired order have bounded
signed logarithmic moments. This is a paper argument under audit, not a
Lean-closed asymptotic statement.

Here is the required full-carrier estimate, independently of that
asymptotic. For real coefficients a_n supported on 1<=n<=N put
P(k)=sum_(n<=k) a_n, W=sum_(n<=N)|a_n|, H=sum_(n<=N)1/n, and
V=sum_(n<=N) a_n*b_n in the original physical carrier. If
|P(k)|<=epsilon*k for k<=N, finite Abel summation with nonnegative
antitone weights gives |sum a_n*w_n|<=epsilon*sum w_n. Apply it to 1/n
and floor(k/n) to get the exact-cell estimate

```
|sum_(n<=N) a_n*(k mod n)/n| <= 2*epsilon*H*k.
```

The same numerator is at most W in absolute value. Its complete energy
series, split after cell T, therefore gives

```
||V||^2 <= 4*T*(epsilon*H)^2 + W^2/(T+1).
```

This retains every cell of the infinite tail. It is the finite estimate
being formalized next; no arithmetic error bound is assumed proved merely
because this transfer estimate is available.

The proposed application removes n<sqrt(N), whose generator-norm cost is
O(N^(1/4)*log N), and subtracts the increments of the smooth R-term model
for A on the remaining interval. For that error, epsilon=O_R((log N)^(-R-1))
and W=O(N*log N). Taking T=floor(N*(log N)^8) makes its squared norm
o(N/(log N)^4) when R is sufficiently large. The smooth model's increments
can then be compared with the constant (log N)^(-2) in the weighted
sum of generator norms: n>=sqrt(N) has bounded logarithmic ratio, and
n/N away from zero has ratio tending to one. The residual lower segment
is bounded by its reciprocal-square-root sum. Thus the intended full-norm
consequence is

```
||J_N - (log N)^(-2)*sum_(n<=N) b_n|| = o(sqrt(N)/(log N)^2).
```

The constant-coefficient source has rescaled L2 limit j: its unbalanced
fractional dilates form an L2 Riemann sum for
integral_0^1 {x/u}/x du=j(x), with dilate norm proportional to u^(-1/2).
The harmonic balance term has norm O(log N/sqrt N) after rescaling.
Strong dilation continuity handles compact u intervals; the integrable
u^(-1/2) bound controls the omitted head. This completes the proposed
paper route to the full profile and energy constant ||j||_2^2, subject to
formalization and proof audit of the displayed asymptotic transfers.

Even this norm asymptotic has only a relative logarithmic error. It does
not resolve a smaller power-scale signed pairing against the raw source.
Multiplying a complex source mode by an uncontrolled arithmetic phase also
prevents converting Re(rho*C_rho)>0 into a first-derivative sign. These are
the precise remaining obstacles to endpoint energy transport.


A further endpoint-optimization check does not require computation. The
single-profile projection cannot remove a complete rho profile when
1/2<=Re(rho)<1 in the admissible cases above. If f_rho=c*j in L2, local
absolute continuity upgrades the equality to pointwise equality, and the
two differential equations give (1-c)*b=(rho-1)*c*j almost everywhere.
On (0,1), b=1 whereas j=-log x+j(1) is nonconstant. Since rho!=1, this
forces c=0 and then 1=0. Thus f_rho is not in the complex span of j, and
its orthogonal residual has strictly positive squared norm. Together with
C_rho!=0, the projection removes a nonzero fraction but leaves a nonzero
fraction. Neither fraction is claimed uniform in rho. This is a sharp
paper classification of the one-profile correction, not a retirement of
EDQ or a subpower bound for the uncorrected arithmetic source.


The corpus searches for signed endpoint pairing, Schur projection,
prime-power logarithmic moments, dilation/resolvent coupling, and full
coefficient-error transfer all returned partial results with pending
coverage (generations 822518--822539). Their declaration, candidate-lemma,
and source-argument lanes were inspected; no proof-idea or ingredient-set
closure was returned for these requests. The useful local dependencies
were the actual Möbius logarithmic moments, finite divisor swap, full
discrete Gram identity, and Abel summation by parts. The resolvent and
Schur-complement candidates had additional source-identification or
invertibility premises and supplied no arithmetic signed bound. Compiler
metadata for the retrieved candidates was source-only; applicability of
the finite identities used below is checked in the scratch proof.

The universal ledger's existing `MUST-CONTROL-CANCELLATION-AT-THE-ABSOLUTE-SCALE`
entry already covers the remaining precision issue, so no duplicate law
was added. The frontier map remains read-only for this work.


The coefficients in the proposed summatory expansion are explicit. If
m_k=sum_(n>=1) mu(n)*(log n)^k/n, interpreted by its convergent partial
sums, then

```
c_j = -(j-1)! * sum_(0<=k<j) m_k/k!.
```

This follows by expanding each logarithmic-integral term:
(l-1)!/(L-log m)^l contributes
(l-1)!*binomial(j-1,j-l)*(log m)^(j-l)/L^j.
Setting k=j-l makes its scalar coefficient (j-1)!/k!.
Thus c_1=0 and c_2=1 use only the two established normalizations m_0=0
and m_1=-1. This formula fixes the model to be formalized and avoids
hiding arbitrary fitted constants in the transfer argument.


The Riemann-sum step has a direct full-ray domination check. For u in a
compact subinterval of (0,infinity), Phi_u(x)={x/u}/x is pointwise
continuous in u except on a countable set of x, and is bounded by
min(1/u_min,1/x). The square of this bound is integrable on the positive
ray, proving L2 continuity by dominated convergence. Moreover
||Phi_u||_2=u^(-1/2)*||b||_2. Both the integral and the uniform-grid
Riemann sum over 0<u<delta therefore have norm at most
2*sqrt(delta)*||b||_2. This supplies the small-u control required by the
proposed profile transfer; compact-interval convergence alone would not.


The general transfer estimate is now Lean-closed in
`EulerDeletionCoefficientPrefixEnergy.lean`:
`RHTower.DeletionCoefficientTransfer.source_energy_le_envelope` bounds the
complete physical energy using the actual finite maximum of normalized
signed prefixes and the actual coefficient mass. Eight public theorems
include the Abel comparison, both cell bounds, exact infinite energy
series, and the finite maximum formulation. The scratch check passed
without warnings. The leaf-only build passed, compiling only this module
(477 seconds under shared machine load; 9,101 jobs include cached dependencies).
The eight new core theorems passed their axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`. The endpoint application is now checked
in `EulerDeletionPrimeCountEndpointTransfer.lean`; its audit is recorded below.


### Reflection test of the positive coupling [BRIDGE; paper]

The next conjecture-to-test was that reflection plus the strict rotated
coupling might force Re(rho)=1/2. The spectral calculation instead exposes
a conservation identity, so this implication is not justified. At a
nontrivial zero, the head cancellation makes f_rho square integrable even
when 0<Re(rho)<1/2. The same holds for the reflected zero.

Set B(y)=exp(y/2)*b(exp y), g_rho(y)=exp(y/2)*f_rho(exp y), and a=rho-1/2.
Then g_rho'=a*g_rho-B in L2; this follows from the locally absolutely
continuous physical functions and their differential equations. In the
angular Fourier variable lambda, g_hat=B_hat/(a-i*lambda) almost everywhere.
The possible exceptional frequency when Re(a)=0 is a null set. The real
seed B has even |B_hat|^2. Parseval therefore gives

```
||f_rho||_2 = ||f_(1-conj rho)||_2,
rho*C_rho + (1-rho)*C_(1-rho) = ||j||_2^2.
```

For the second formula, reflect lambda in the second integral. Its
combined numerator is
rho*(1/2-i*lambda)-(1-rho)*(1/2+i*lambda)=a-i*lambda,
which cancels the shared denominator. What remains is exactly the
Parseval integral for ||j||^2. All cross integrals exist by L2
Cauchy--Schwarz. These are paper identities; the required concrete
Fourier/domain identifications have not been formalized in this work.

The reflected rotated couplings therefore add to a fixed positive mass;
they are not forced equal. Their real-part difference is
(2*Re(rho)-1)*||f_rho||^2. Consequently the positive-coupling argument
survives as an exact flux decomposition, but supplies no sign
contradiction for an off-line pair. This records the failed reflection
implication and its positive survivor without retiring EDQ.


The core import is wired into `RHTower.lean`; no umbrella build was run.
Its generated index was refreshed and formal lint passed, with existing
large-file warnings only. The five endpoint declarations are now in
`formal/GaloisForLFunctions/RHTower/EulerDeletionPrimeCountEndpointTransfer.lean`.
Their imported closure became available after the external rebuild stopped
and the two remaining required leaf artifacts were restored. The obsolete
unchecked draft has been removed. No numerical experiment was run, and the
actual RH-producing signed covariance estimate remains open.

All 14 owned temporary files were removed after preserving the draft.
All Lean, search, index, and lint processes started for this work have ended.

## Endpoint pairing: exact forcing before an operator sign [BRIDGE]

The target remains a cofinal subpower bound on the complete signed physical
source. The endpoint transfer supplies arithmetic identities and a norm-error
estimate; it does not supply the required signed covariance bound.

Three candidate mechanisms were tested against the literal source:

1. **Centered prime incidence.**
   `Sieve/RouteERamareIncidenceConditionalNegative.lean` proves conditional
   negativity under an exact zero-sum condition. With the physical history
   `c_n(x)=mu(n)*b_n(x)`, that sum is `G_N(x)`, not zero. Harmonic balancing
   inside each `b_n` does not center this history. Centering it by hand changes
   the source and leaves the original total mode to estimate. Thus this
   theorem does not establish the desired physical sign.
2. **Accretive prime-power propagation.** The finite convolution has both an
   invisible input mode and an indefinite mixed form, as checked below.
   Positivity for arbitrary coefficients is false; a surviving estimate must
   use the actual arithmetic coefficients and retain the forcing.
3. **Hyperbola reversal followed by absolute values.** Reversing the complete
   omitted divisor sum gives the harmonic depth cost already formalized in
   `EulerDeletionQuotientHarmonicBound.floorResidual_le_harmonic`. This is not
   a new estimate. Absolute values still remove the signed cancellation
   needed at the target scale. Likewise, the exact complete-period formula
   in `EulerDeletionMobiusPeriodCovariance.mobius_primitive_period_energy`
   does not replace the nonuniform physical weights by a uniform average.

Here the full-ray representatives are

```
b(x) = {x}/x,
b_n(x) = ({x/n}-{x}/n)/x,
G_N = sum_(n<=N) mu(n)*b_n,
a_N = sum_(n<=N) mu(n)/n,
D_q f(x) = f(x/q)/q.
```

The exact identity `b_(qm)=D_q b_m+b_q/m` follows by expanding both
fractional-part differences. It holds on the entire positive ray; the
representatives `b_m` vanish below 1. Change of variable gives
`||D_q f||_2^2=||f||_2^2/q`. Consequently the prime-power convolution gives
the following **paper identity with the complete boundary forcing**:

```
J_N = -sum_(q prime power <=N) [D_q G_floor(N/q) + a_floor(N/q)*b_q],
Re<G_N,J_N> =
  -sum_q Re<G_N,D_q G_floor(N/q)>
  -sum_q a_floor(N/q)*Re<G_N,b_q>.
```

All sums are finite, and all terms lie in the original L2 carrier. No
estimate or exchange of infinite sums is used. The vector-valued packet
identity and its harmonic specialization are the positive algebraic
survivors checked in the endpoint transfer module. The identification
with `D_q` above has not been formalized here.

For the operator test, let
`R_N(a)=sum_(q prime power <=N) sum_(m<=N/q) a_m*b_(qm)`.
The coefficient vector supported at 1 has zero physical source (`b_1=0`)
but, already at N=2, has response `b_2 != 0`. Hence `R_N` does not factor
through the physical source alone. Even after fixing that coefficient to
zero, at N=4 take `a_2=1, a_4=t` and all other coefficients zero. Then the
source is `b_2+t*b_4` and the response is `b_4`. Since `b_4(x)=1/(4*x)` on
`1<x<2`, its norm is positive. The mixed pairing is
`Re<b_2,b_4>+t*||b_4||^2`, which takes every real value. This is an exact
paper counterexample to a coefficient-independent accretivity claim, not
a counterexample for the actual Mobius coefficients or a retirement of EDQ.

Broad recent-paper search selected Brown--Rosenthal--Zhou,
[Markov Chain CLTs: Resolving Open Problems](https://arxiv.org/html/2609.07819v1)
(7 September 2026). Sections 5.1--5.3 construct covariances using finite
excursions and fresh symmetric signs. The covariance representation does
not provide reversibility of the resulting chain, even though the transition
can factor into reversible kernels. Applying it to EDQ would require a
source-preserving representation and the missing tightness or variance
bound; randomness cannot be assigned to the actual Mobius coefficients.
The construction therefore supplies no signed energy estimate here.

The independently selected Jha--Dayal paper,
[Continuum Limit of Nonlocal Electrostatics in Random Media](https://arxiv.org/html/2609.06354v1)
(5 September 2026), Appendix C, obtains a local correction by retaining a
distributional boundary contribution. The relevant methodological transfer
is to retain the forcing above. Its stationary random charge assumptions
and electrostatic kernel have not been identified with EDQ, and no theorem
from the paper is used in Lean.

Four deep/method searches examined declaration, candidate, and source-argument
lanes for signed pairing, flux, prime-power propagation, and floor covariance.
Coverage was pending (generations 822592--822604); candidates were source-only,
and no proof-idea or ingredient-set lane completed. The propagation query
also reported a semantic-backend timeout. These are partial searches, not
evidence that the corpus contains no other mechanism. No numerical experiment
was needed for the operator counterexamples, and none was run.

### Candidate forcing profile and a second cancellation scale [BRIDGE; paper audit]

The boundary term above admits a more specific attack than an abstract
operator estimate. Define `P_L=sum_(q prime power <=L) b_q` and
`B_N=sum_q a_floor(N/q)*b_q`. Finite interchange gives

```
B_N = sum_(m<=N) mu(m)/m * P_floor(N/m).
```

The candidate full-ray limit is

```
log(N)*B_N(N*x) -> h(x) in L2(0,infinity),
h(x) = sum_(m>=1) mu(m)/m * j(m*x).
```

This is a paper argument under audit, not a Lean theorem. The following
checks specify the complete proposed proof and the scale it would deliver.

* The prime number theorem and the proper-prime-power error give
  `Q(L)~L/log(L)` and a global bound `Q(L)<=C*L/log(L+2)`. Abel summation
  then gives `sum_(q<=L) q^(-1/2)<=C'*sqrt(L)/log(L+2)`. The physical
  generator bound implies `||P_L||<=C''*sqrt(L)/log(L+2)`.
* In the full carrier,
  `P_L(L*x)=L^(-1)*sum_q Phi_(q/L)(x)-H_Q(L)*b(L*x)`, where
  `Phi_u(x)={x/u}/x` and `H_Q(L)=sum_q 1/q`. The normalized prime-power
  counting measures converge to Lebesgue measure on every compact
  subinterval of (0,1]. L2 continuity of `Phi_u` was checked above.
  The weighted prime-count bound controls the omitted `u<delta` part in
  L2 by `C*sqrt(delta)` in the limit. Also
  `log(L)*H_Q(L)*||b(L*.)||=O(log(L)*log(log(L))/sqrt(L))->0`.
  Thus `log(L)*P_L(L*.) -> integral_0^1 Phi_u du = j` in full-ray L2.
* For each fixed m, set `L=floor(N/m)`. Then `N/L->m` and
  `log(N)/log(L)->1`; continuity of L2 dilation transfers the last limit
  to `log(N)*P_L(N*.) -> j(m*.)`.
* The m-tail is uniform. Its L2 norm is bounded by
  `C*log(N)*sum_(M<m<=N) m^(-3/2)/log(2+N/m)`.
  For `m<=sqrt(N)` the logarithmic ratio is at most 2. For larger m the
  whole bound is `O(log(N)*N^(-1/4))`. Replacing `N/m` by its floor changes
  this bound by a fixed constant only. First send N to infinity, then M
  to infinity. The limiting series converges absolutely in L2 because
  `||j(m*.)/m||=m^(-3/2)*||j||`.

The proposed profile is nonzero, without assuming cancellation in its
coefficients. Let `c2=sum_(m>=1) mu(m)/m^2`. The elementary comparison
`sum_(m>=2) 1/m^2 <= 1/4+sum_(m>=3) 1/(m*(m-1))=3/4` gives `c2>=1/4`.
For the periodic primitive `F(t)=({t}^2-{t})/2`, integration by parts
gives `|j(y)-1/(2*y)|<=1/(4*y^2)` since `|F|<=1/8`.
Termwise application in the absolutely convergent series gives

```
h(y) = c2/(2*y) + O(1/y^2),
|h(y)-c2/(2*y)| <= (sum_(m>=1) m^(-3))/(4*y^2).
```

Since the latter sum is at most 2, `h(y)>=1/(16*y)` for `y>=8`.
Hence `||h||>0`. The asserted forcing limit would therefore give the
sharp order `||B_N||^2 ~ ||h||^2*N/log(N)^2`.

There is also an exact shape distinction. On compact positive intervals,
termwise one-sided differentiation is justified by the summable derivative
majorant `m^(-2)/x^2`. At `x=1/2` the derivative jump of h is
`4*sum_(2|m) mu(m)/m^2 = -4*c2/3`, which is nonzero. To obtain the last
identity, separate even and odd m and use `mu(2*k)=-mu(k)` for odd k
and zero for even k. The profile j has a continuous derivative at 1/2.
Both representatives are continuous on the positive ray (the series for h
converges locally uniformly), so this also excludes equality in L2.
Thus h is not a scalar multiple of j. A scalar subtraction of the earlier
jet profile cannot remove this entire forcing profile.

If the earlier paper-level endpoint limit
`log(N)^2*J_N(N*.) -> j` is completed, the exact packet identity then
forces `log(N)*sum_q D_q G_floor(N/q)(N*.) -> -h`.
Thus the two terms inside the endpoint response would each have energy
of order `N/log(N)^2`, while their sum has order `N/log(N)^4`.
This identifies a concrete leading profile to cancel. It still gives no
absolute-scale estimate for their pairing with G_N, and cannot close RH
by treating a relative error as an absolute bound. None of these new
asymptotic or profile statements has been formalized here.

The shape difference should not be mistaken for a new loss of information.
On full-ray L2 define `A_m f(x)=f(m*x)/m`. Then
`||A_m||=m^(-3/2)` and `A_m A_n=A_(mn)`. Both operator series

```
T = sum_(m>=1) mu(m)*A_m,
Z = sum_(m>=1) A_m
```

converge absolutely in operator norm. Their product double series is
absolutely convergent, so finite divisor regrouping followed by the
norm limit and `sum_(d|n) mu(d)=1_(n=1)` gives `TZ=ZT=Id`.
In particular `h=Tj` and `j=Zh`, with both operator norms at most
`sum_(m>=1) m^(-3/2)`. This is a paper-level bounded inverse with no
arithmetic cancellation hypothesis. It preserves subpower norm bounds
under a fixed full-ray transformation.

It does not identify the finite forcing `B_N` with `T` applied to a fixed
physical source: `B_N` uses the moving cutoffs `floor(N/m)`, whereas `T`
dilates the physical variable. Nor does this uncompressed `T` preserve
the original support condition below 1.

However, the subsequent corpus search exposed a way to retain the cutoff
exactly. `FloorTransformHarmonicInverse.lean` proves the scalar harmonic
floor inverse. The same finite regrouping is valid for vector-valued sums:

```
B_N = sum_(m<=N) mu(m)/m * P_floor(N/m),
P_N = sum_(d<=N) B_floor(N/d)/d.
```

Indeed, composing the two sums makes the coefficient at
`P_floor(N/r)` equal to `(sum_(m|r) mu(m))/r`. This is one at r=1 and
zero otherwise; `floor(floor(N/d)/m)=floor(N/(dm))` retains the actual
cutoff. Both transformations preserve a uniform norm bound `C*N^epsilon`
for any epsilon>0, at a cost at most `sum_d d^(-1-epsilon)`.
This does not transfer a bound assumed only on a cofinal subsequence,
because smaller quotient cutoffs need not belong to that subsequence.
The vector specialization is paper-only here. Thus finite-cutoff inversion
of the isolated forcing is not the remaining mathematical obstacle; the
signed cancellation with the other propagated source still is.

### Tail-test proof of the forcing lower bound [BRIDGE; paper, not Lean]

The forcing lower bound can be proved without waiting for the full L2
profile limit. Let

```
W_N = sum_q a_floor(N/q),
V_N = sum_q a_floor(N/q)/q,
R_N = sum_q |a_floor(N/q)|*(q+1/q),
g_T(x) = 1_(x>=T)/x.
```

All q sums run over prime powers at most N. For fixed m, the prime number
theorem gives
`log(N)*Q(floor(N/m))/N -> 1/m`. The bound
`Q(L)<=C*L/log(L+2)` and the split at `m=sqrt(N)` give a summable
`C'/m^2` majorant on the first part of
`log(N)*W_N/N=sum_m mu(m)/m * log(N)*Q(floor(N/m))/N`.
The remaining absolute tail is `O(log(N)/sqrt(N))`. Hence
`W_N~c2*N/log(N)`, with `c2>=1/4` as above.

The absolute bound `|a_M|<=H_M` gives `|V_N|<=H_N^2`.
Reversing the positive majorant and using the same prime-count bound gives
`R_N<=K*N^2/log(N)` eventually: the inner q sum is at most
`2*(N/m)*Q(floor(N/m))`, and splitting the resulting m sum at sqrt(N)
uses the convergent weight `m^(-3)`.

An exact change of variable and the elementary j remainder above give

```
<b_q,g_T> = [j(T/q)-j(T)]/q,
|<b_q,g_T> - (1-1/q)/(2*T)| <= (q+1/q)/(4*T^2),
||g_T||^2 = 1/T.
```

Thus `<B_N,g_T> >= (W_N-V_N)/(2*T)-R_N/(4*T^2)`.
Choose c>0 so that `W_N-V_N>=c*N/log(N)` eventually, and a fixed
`A>=max(1,K/c)`. With `T=A*N`, the pairing is at least
`c/(4*A*log(N))`. Cauchy--Schwarz now yields

```
||B_N||^2 >= c^2/(16*A) * N/log(N)^2
```

for all sufficiently large N. This is a dependency-closed paper proof
using PNT, finite reindexing, the bounded periodic primitive, and
Cauchy--Schwarz. Its Lean formalization is outstanding. It proves the
size of the actual boundary forcing; it does not estimate the signed
pairing after that forcing is combined with the propagated source.

### Endpoint transfer validation

`EulerDeletionPrimeCountEndpointTransfer.lean` now contains five checked
public declarations: `endpointJet_error_energy_le`,
`jetCoeff_eq_primePower_convolution`, `sum_jetCoeff_smul`,
`endpointJet_eq_primePower_packets`, and
`jetHarmonic_eq_primePower_harmonic`. The scratch check passed without
warnings. The leaf-only final build compiled only this new module and
passed in 186 seconds; its 13,644 jobs include cached dependencies.
The separate scratch axiom audit of these five new declarations reported
only `propext`, `Classical.choice`, and `Quot.sound`. Existing declarations
were not re-audited. The import is wired into `RHTower.lean`; no umbrella
build was run. Index refresh and formal lint passed.

The only prerequisite compilations were the two missing leaf artifacts
`Sieve.MaynardLongAmplitudeExclusion` (90 seconds) and
`Sieve.MaynardEndpointReserve` (5.4 seconds), after their external build had
stopped. The five endpoint declarations supersede the deleted unchecked
draft. The subsequent fifth deep search, on summable dilation inverses,
had pending coverage generation 822612 and source-only candidates; it
identified the existing harmonic floor inverse used in the paper audit.
The forcing tail-test lower bound and the new profile statements remain
unformalized. The required full signed RH estimate remains open.

All processes started for this endpoint transfer work have ended. Its 14
owned temporary files were removed, and the final scoped diff check passed.
The frontier map was not edited.

## Finite-window coercivity and the joint-source test [BRIDGE]

The hard target remains a cofinal subpower ceiling for the complete signed
physical source. The following argument closes a lower-bound mechanism for
the actual boundary forcing. It does not supply that ceiling.

For arbitrary real coefficients c supported through N, write

```
u_c(k) = sum_(1<=n<=N) c_n*(k mod n)/n,
mu_c = sum_(1<=n<=N) c_n*(n-1)/(2*n),
R_c = sum_(1<=n<=N) |c_n|*n,
G_c = sum_(1<=n<=N) c_n*b_n.
```

The centered residue primitive
`P_n(k)=r*(r-n)/(2*n)`, where `r=k mod n`, satisfies

```
P_n(k+1)-P_n(k) = (k mod n)/n-(n-1)/(2*n),
-n/8 <= P_n(k) <= 0,
|P_n(k)-P_n(l)| <= n/8.
```

The last constant uses the range of one primitive; adding two independent
absolute bounds would lose a factor of two. Summing the exact difference
first over a spatial window and then over the literal signed coefficients
proves, for every natural T and L,

```
|sum_(0<=i<L) u_c(T+i)-L*mu_c| <= R_c/8.
```

Finite Cauchy--Schwarz and the existing complete physical energy series give

```
(sum_(0<=i<L) u_c(T+1+i))^2 <= L*(T+L+1)^2*||G_c||^2.
```

This retains the weights `1/[k*(k+1)]`; no period average or asymptotic
integral replaces the physical energy. In particular,

```
max(0,L*|mu_c|-R_c/8)^2 <= L*(T+L+1)^2*||G_c||^2.
```

There is also a window-free consequence:

```
|mu_c|^3 <= 8*R_c*||G_c||^2.
```

Indeed, `|mu_c|<=R_c/8` follows termwise from
`4*(n-1)<=n^2`. If the mean is nonzero, take
`L=ceil(R_c/(4*|mu_c|))`, so `L>=2`,
`R_c<=4*L*|mu_c|`, and `L*|mu_c|<=R_c/2`.
The window starting at 1 has absolute sum at least `L*|mu_c|/2`.
Since `(L+1)^2<=4*L^2`, its energy bound yields
`|mu_c|^2<=16*L*||G_c||^2`. Multiplication by `|mu_c|`
proves the cubic bound. The zero-mean case is immediate.

For the literal forcing, substitute
`c_q=1_(q prime power)*a_floor(N/q)`. Then
`G_c=B_N`, `mu_c=(W_N-V_N)/2`, and `R_c<=R_N` with the
quantities defined in the preceding tail-test argument. Its dependency-closed
paper estimates `W_N-V_N>=c*N/log(N)` and
`R_N<=K*N^2/log(N)` imply

```
||B_N||^2 >= c^3/(64*K) * N/log(N)^2
```

for all sufficiently large N. This avoids formalizing the infinite tail-test
integral and the proposed full-ray profile limit. The PNT-derived weighted
moment estimates themselves remain unformalized here. This is a forcing
size result, not a bound on the complete signed source.

### Attempts to obtain the missing signed bound

The critical-boundary cancellation theorem found by deep search,
`coupledFloorMobiusCriticalBoundary_singularCancellation`, is backed by the
actual source estimate in `ShiftedEulerFloorMobiusTailCoupling.lean`.
Its incidence coefficients contain `d^(-(1+2*omega))`, with `omega>0`.
The elementary constant is
`2+2/(1-2*omega)+1/[(1+omega)*2*omega]`.
It diverges as omega approaches zero; the logarithmic carrier bound also
loses its decay rate there. Thus the candidate transfer by removing that
weight does not prove an EDQ endpoint estimate. The positive theorem is
valid on its stated weighted carrier.

Broad newest-first arXiv searches on **impedance** and **memory** selected
Hallinan--Lestas, [Part I](https://arxiv.org/html/2609.07315v1) and
[Part II](https://arxiv.org/html/2609.07331v1), 7 September 2026.
Part I's separation proof and Part II's multiplier congruence suggest
retaining off-diagonal terms in a quadratic graph test. At proof level,
they require a strict separator for the actual two graphs and the stated
stability conditions. Finite Euler-deletion invertibility supplies no
cutoff-uniform separator or inverse norm bound. The high-pass change of
variables does not discharge those conditions. No theorem from these
papers is used in Lean.

The third deep/method search proposed a Lindblad-to-hypocoercivity ingredient
set. Inspection of `ConservativeDissipativeQuantum.lean` and
`ConservativeDissipativeBures.lean` does not identify their constructed flow
with the EDQ derivative. The latter's coercivity rate is
`2/(1+||B||^2)^3`, so its quantitative transfer also retains a raw-operator
norm cost. The exact conditional-variance contraction in
`RouteEPhysicalFibreCoarea.lean` concerns normalized fibre masses; an
identity with the original signed physical energy has not been supplied.
None of these candidates closes the signed arithmetic estimate.

The three deep searches used OR matching across broad mechanism terms and
inspected declaration, candidate-lemma, source-argument, and available
method-group lanes. Coverage was partial (generations 822633 and 822648);
returned candidates were source-only. The final ingredient set was explicitly
`not_verified`; its unresolved off-diagonal-energy obligation is not a proof.
No numerical experiment was run.

### Centered-window validation

`EulerDeletionCenteredCellWindow.lean` closes eleven public theorems,
including `mean_window_source_certificate` and
`abs_mean_cube_le_moment_energy`. The complete scratch file passed without
warnings. The final `lake build --old` invocation compiled only this leaf
and passed in 120 seconds; the 9,102 jobs include cached dependencies.
A separate `/tmp` axiom audit checked only these eleven new declarations;
each reported only `propext`, `Classical.choice`, and `Quot.sound`.
The import is wired into `RHTower.lean`; no umbrella build was run.
The generated index includes all new declarations, and formal lint passed
with existing large-file warnings only.

The paper specialization to the literal prime-power forcing is recorded
above. Its arithmetic moment estimates and the RH-producing complete
signed bound remain open in Lean. The frontier map and universal-law
ledger were not edited; the existing absolute-scale cancellation law
already covers this distinction. No numerical experiment was run.
All processes started for this work have ended, and its thirteen owned
temporary files have been removed after preserving the proofs and audit
results here.

## Physical residue martingale: bounded innovations, unpaid drift [BRIDGE]

The next direct cancellation conjecture was that the actual residue history
might make the signed source a martingale with a summable variance budget.
The literal physical measure does give that budget for the innovations.
It does not identify the full source with them.

Put probability mass `nu{k}=1/[k*(k+1)]` on positive integers and write
`R_n(k)=(k mod n)/n`, `X_n(k)=mu(n)*R_n(k)`. Let
`L_n=lcm(1,...,n)`, with `L_0=1`, and let `F_n` be the sigma-algebra
generated by `k mod L_n`. These are deterministic partitions of the
physical cells, not random Mobius coefficients. The cumulative literal
source is `S_N=sum_(n<=N) X_n`, and the existing discrete Gram formula
identifies `||S_N||_(L2(nu))^2` with the full physical carrier energy.

Every `X_n` is `F_n`-measurable. Define the actual innovations and drift by

```
Delta_n = X_n - E_nu[X_n | F_(n-1)],
M_N = sum_(n<=N) Delta_n,
D_N = sum_(n<=N) E_nu[X_n | F_(n-1)],
S_N = M_N + D_N.
```

There is an unconditional, cutoff-independent paper bound

```
||M_N||_(L2(nu))^2 <= 2.
```

Here is the complete proof. For any positive L, the function
`p_(n,L)(k)=mu(n)*R_n(k mod L)` is measurable with respect to `k mod L`.
It agrees with `X_n` for `k<L`, and its difference from `X_n` has absolute
value at most one. The exact telescoping physical tail is
`nu{k>=L}=1/L`. Minimality of conditional expectation as an L2 projection
therefore gives `||Delta_n||^2<=1/L_(n-1)`.
The first increment is zero. For n>=3, both n-1 and n-2 divide L_(n-1)
and are coprime, so `L_(n-1)>=(n-1)*(n-2)`. Consequently

```
sum_(3<=n<=N) ||Delta_n||^2
 <= sum_(3<=n<=N) 1/[(n-1)*(n-2)] <= 1.
```

The n=2 contribution is at most one. Distinct innovations are orthogonal:
for i<j, Delta_i is F_(j-1)-measurable, while Delta_j has conditional
expectation zero on that same sigma-algebra. Finite Pythagoras proves the
bound. All conditional expectations exist because each X_n is bounded
and nu is a probability measure.

The proposed martingale proof of the full source bound fails at its
identification step. Already X_6 is a nonzero F_5-measurable increment,
because 6 divides L_5=60, so its innovation is zero and the entire increment
lies in the predictable drift. In general every squarefree composite n
divides L_(n-1), and its innovation vanishes. Only prime increments can
contribute nontrivial innovations. Thus the proved variance budget does
not control the actual drift: `| ||S_N||-||D_N|| |<=sqrt(2)`, with every
cross term retained in the exact identity above. The required cofinal
subpower energy bound remains a bound on D_N. No bound for D_N has been
established, and EDQ is not retired.

This paper proof uses the literal physical weights and supplies a positive
bounded component, rather than assuming independence or dropping a
conditional mean. `EulerDeletionResidueMartingale.lean` now contains the
actual residue measure, projections, complete innovation estimate, original
carrier norm identity and prime-support theorem. Its complete scratch
check passed without warnings, and the final leaf build and new-theorem
axiom audit passed. No drift growth estimate or RH proof is claimed.

The Lean indexing is `j=k-1`, with cell weight `1/[(j+1)*(j+2)]`.
It records `j mod L`, an equivalent residue history, and predicts using
`R_n(1+(j mod L))`. This predictor agrees for `k<=L`, giving the stronger
single-increment bound `1/(L+1)`. The stated cumulative budget two follows
with the same telescoping comparison.

### Drift attack: fixed-source projection and uniform integrability fail

The first proposed way to pay the drift was to view it as conditional
expectations of a single limiting observable. The deep search returned
`Integrable.uniformIntegrable_condExp_filtration`, but its source is one
fixed integrable function; the actual drift is a growing sum of projections
of different residue functions. The theorem does not apply to that sum.
Moreover, it is an L1 statement, whereas the required energy is quadratic.

There is a stronger obstruction to the proposed L2 convergence strategy.
`BaezDuarteMobiusPrefixApproximation.one_sub_bdMobiusModularApproximant`
gives `S_N(k)+1=k*H_N` for `1<=k<=N`, where
`H_N=sum_(n<=N) mu(n)/n`. The corpus proves `H_N -> 0`, so `S_N(k)->-1`
at every physical cell. The same corpus proves unconditionally
`not_tendsto_bdMobiusFullErrorEnergy_zero`: the full energy of `S_N+1`
does not tend to zero. Consequently the squares of the literal source
cannot be uniformly integrable. This conclusion follows directly by
Vitali convergence on the probability measure above.

The orthogonal innovations have summable squared norms, hence M_N converges
in L2 to some M. On this countable space every singleton has positive
measure, so that convergence also gives convergence at each coordinate.
Thus D_N converges pointwise to `-1-M`. Uniform integrability of D_N squared
would force L2 convergence to that same limit and then L2 convergence of
S_N to -1, contradicting the existing full-error obstruction. This rejects
uniform-integrability and strong-convergence proofs for this raw drift;
it does not reject a cofinal subpower ceiling. The bounded innovation
component remains the positive result of this attempt. This consequence
is a dependency-closed paper argument; it is not yet a new Lean theorem.

The corpus also gives the exact physical residue mean
`E_nu R_n=log(n)/n` in `BaezDuartePairingSeries.hasSum_pairing_discrete`.
Subtracting this mean retains the full centered covariance and does not
supply its bound. Neither a constant-mode estimate nor the innovation
budget controls the escaping squared energy.

### External method checks

Broad newest-first arXiv searches on **memory** and **transport** selected
Aoki et al., [low-frequency merger waveforms](https://arxiv.org/html/2609.10329v1),
9 September 2026, and Hashemi--Hyun,
[finite free curves](https://arxiv.org/html/2609.10367v1), 9 September 2026.
The first cancellation uses an explicit equality between particular
on-shell integral coefficients; the paper distinguishes that identity
from ordinary unitarity. No matching identity for the EDQ covariance
has been derived. The second paper's matrix defect formula requires a
real symmetric pencil and identification with the convolution root map.
Its noncentered formula retains a mean-product term. Those conditions
have not been established for the arithmetic source.

Further broad **screening** and **renewal** searches did not return verified
June--September 2026 papers; newest-first arXiv pages failed to load.
The accessible primary source was Schulz--Barkai--Metzler,
[aging renewal theory](https://arxiv.org/html/1310.1058v1), submitted in 2013.
Its renewal and subordination formulas assume independent waiting times,
and the subordinated process is independent of its clock. The physical
residue clock satisfies neither supplied identification. In particular,
composite increments remain determined by the same cell coordinate.
No external theorem is used in Lean, and no numerical experiment was run.

### Renewal estimate: signed transform values remain essential

The next candidate was to bound the drift through the positive dilation
renewal kernel. The corpus's exact critical-coordinate identity is

```
sum_(k>=1) k^(-1/2) F(y-log k)
  = exp(-y/2)*exp(-exp(-y)).
```

`MobiusLaplaceCriterionFrontier.tsum_mobiusLaplaceCriticalRenewal` proves
this for the actual Mobius--Laplace profile. Its absolute convergence is
for the products containing F. Replacing F by a uniform norm bound loses
that convergence: `MobiusLaplaceCriticalDilationNoGo` proves the weights
are nonsummable even on primes. Thus this is not a probability renewal
kernel or an absolute Neumann contraction at the critical exponent.

The alternative changing-prime-core identity in
`MobiusDivisorDilationMeanRenewal.mobiusDivisorDilationMean_insert` retains
two cross-scale correlations. The available eventual release sign in
`MobiusDivisorPrimeCorrelationPhysical` fixes the prime core first and
depends on its parity. It supplies neither a common dissipative sign nor
a threshold uniform along the growing core. Those are precisely the
missing conditions for this proposed iteration; they are not supplied
by the identity itself.

The drift and renewal deep searches used OR matching, inspected all
declaration, candidate-lemma and source-argument lanes, and returned no
proof-idea or ingredient-set certificate. Generation 823332 had partial
coverage and source-only candidates. For the drift search the semantic
coverage reported 2,196,271 ready out of 2,336,631 expected entries; the
renewal coverage query was interrupted at its deadline. Candidate
statements were checked in their source files before this assessment.

### Physical residue validation

`EulerDeletionResidueMartingale.lean` closes 26 public theorems in 435 lines.
The main unconditional bounds are `martingalePart_sq_le_two` and
`source_drift_norm_gap`; `sourceVec_energy` identifies the original
complete carrier, and `signedInnovation_eq_zero_of_not_prime` gives exact
prime support. The final complete scratch check passed without warnings.
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionResidueMartingale`
passed in 82 seconds, compiling only this leaf; the 9,102 jobs include
cached dependencies. The umbrella import is wired, without an umbrella
build. A separate scratch axiom audit inspected only the 26 new public
theorems: every axiom list is contained in `propext`, `Classical.choice`,
and `Quot.sound`.

The new declarations appear in the generated API. Formal lint passed
with existing large-file warnings. The stronger generated-file freshness
check initially found eight newly added declarations in another research
module and its umbrella import absent from the generated snapshot.
That discrepancy does not involve the new residue module; a final
regeneration followed immediately by a fresh-process
`scripts/formal_tools.py lint --check-generated` passed, with existing
large-file warnings only.

The route-independent ledger now states the need to bound accumulated
conditional means as well as innovations. This agent did not edit the
frontier map. No numerical experiment was run. The unresolved mathematical
target is still an actual cofinal subpower bound for the complete signed
source, equivalently for its predictable part under the bounded norm gap.
All processes started for this work have ended. Its fifteen owned temporary
files were removed after preserving the proof and validation results here.

## Complete-source stretched-exponential ceiling [Lean]

The target remains the actual cofinal subpower ceiling. Rechecking the gcd
head and harmonic-cutoff proposals did not close it: the existing
`EulerDeletionGcdHeadSubpower` retains its harmonic coefficients and later
cells, and `EulerDeletionFirstTailMertens` retains the first complementary
Mertens-increment energy. These are existing results, not new progress.

The new upper-bound attack keeps the quantitative saving already proved
for the actual Mertens function instead of weakening it to each fixed
inverse-log power. Write

```
u(N) = (log N)^(1/3),
s(N) = exp(-u(N)/216),
|M(N)| <= B*N*s(N)^2                     (eventually).
```

The half-saving ray has finite total mass
`T=sum_(n>=1) s(n)/n`. Indeed it is nonnegative and decreasing, and
Cauchy condensation turns its series into
`sum_k exp(-((log 2)^(1/3)/216)*k^(1/3))`, which the corpus already
bounds by a convergent inverse-square series. For k>=N, monotonicity
therefore gives

```
|M(k)|/[k(k+1)] <= B*s(N)*s(k)/k.
```

The exact boundary-minus-tail identity then yields
`|H_N| <= B*(1+T)*s(N)` eventually. The complete energy theorem with
logarithmic quotient-depth cost, including every physical coordinate,
gives for every positive integer L

```
E_N <= 4 + 2*N*L*(|H_N|+B*s(N)^2*(2+log L))^2 + N/L.
```

Choose `L=floor(1/s(N))`. Eventually `1/s(N)>=2`, hence
`1/(2*s(N))<=L<=1/s(N)`. If `t=u(N)/216`, then
`s(N)*(2+log L)<=exp(-t)*(2+t)<=3`, using `1+t<=exp(t)`.
Thus the parenthesized term is at most `B*(4+T)*s(N)`, and

```
E_N <= 4 + (2*B^2*(4+T)^2+2)*N*s(N).
```

Eventually `N*s(N)>=1`, so a single constant absorbs 4. This proves
an unconditional stretched-exponential ceiling for the complete actual
primitive energy and its modular Hilbert source. It strengthens the
previous separate fixed-order logarithmic bounds. A single constant and
a single eventual cutoff also give, simultaneously for all q>=0,

```
E_N*(log N)^q <= C*N*216^(3*q)*(3*q)!.
```

This follows from the positive exponential-series term
`t^(3*q)/(3*q)!<=exp(t)` with `t=(log N)^(1/3)/216`.
It is an upper bound of factorial order three, not a claim that this is
the exact best order of the actual source. It does not prove a subpower
ceiling: `log(N*s(N))/log N -> 1`. Moreover the same exponential-series
inequality gives `(3*q)!/t^(3*q)>=exp(-t)` for t>0 and every q.
Consequently optimizing q in this particular certified family cannot
produce a subpower majorant. This lower-bounds the proposed certificates,
not the actual arithmetic energy.

The attempted further upgrade was order-uniform asymptotic cancellation.
For a nonnegative normalized remainder r(t), a bound
`r(t)<=C*A^q*q!/t^q` for all integers q would imply exponential decay:
choose `q=floor(t/(2*A))`, use `q!<=q^q`, and obtain
`r(t)<=2*C*exp(-(log 2)*t/(2*A))` for sufficiently large t.
In contrast, `exp(-c*t^(1/3))` has no estimate of that form for any
fixed C,A>0; its ratio to every `exp(-d*t)` diverges. The available
all-orders logarithmic estimates do not supply the missing uniform
factorial bound. No such bound for the actual signed remainder was
proved, and no equality between a formal asymptotic series and that
remainder is assumed.

Recent broad external searches used synchronization and resurgence.
[Xu et al., submitted 3 September 2026, revised 7 September](https://arxiv.org/html/2609.04122v2)
use independent local choices and conditional interval min-entropy before
a local-lemma construction. Those hypotheses are not available for the
fixed Möbius sequence or the physical residue measure. The paper's
square-free words concern repeated substrings, not squarefree integers.
[de Mello Koch, Raj and Rudra, submitted 4 September 2026](https://arxiv.org/html/2609.04664v1)
relate large-order coefficients to other saddle sectors using an exact
matrix integral and its thimble connections. That suggested testing
order-uniform remainder control; EDQ has no identified integral/thimble
representation to import the result. Neither external paper supplies a
Lean premise or a bound for the actual EDQ source.

Five bounded deep searches covered signed drift, gcd grouping, harmonic
cutoffs, signed dilation covariance, and factorial remainder mechanisms.
Their declaration, candidate-lemma and proof-source lanes were inspected.
Results were partial at generation 823339; reported semantic coverage,
when available, was 2,196,271 of 2,336,767 chunks. No validated proof-idea
or ingredient group was returned. Applied candidates are checked against
source and in Lean. These searches do not establish corpus exhaustion.

A self-improvement attempt also fails at the available reverse estimates.
The initial-block coercivity `N*H_N^2/2<=fullErrorEnergy N` yields only
`H_N=O(s(N)^(1/2))` from a full-error bound of order `N*s(N)` (the
source/error comparison adds only a bounded term). The direct harmonic
estimate above is already `O(s(N))`. Thus this return step weakens the
saving rather than amplifying it. The surviving target is a new estimate
for the actual signed correlations; neither order optimization nor this
energy-to-harmonic feedback provides it.

### Stretched-energy validation

`EulerDeletionStretchedEnergy.lean` (260 lines), namespace
`RHTower.DeletionStretchedEnergy`, contains four new unconditional public
theorems: `harmonic_rate`, `primitiveEnergy_rate`,
`modular_norm_sq_rate`, and `primitiveEnergy_factorial_rate`.
All were developed with foreground `lake env lean` scratch checks.
After the final local-definition correction,
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionStretchedEnergy`
passed, compiling only this leaf in 218 seconds; the 13,112 jobs include
cached dependencies. Lake replayed existing dependency messages. The new
leaf emitted no warning. Its umbrella import is wired; no umbrella build
was run.

A separate scratch audit printed axioms only for these four new theorems.
Each depends only on `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom, unproved premise, admitted proof, or numerical result is
used. No numerical experiment was run. The frontier map was not edited
by this work. The route-independent ledger records the need for order
uniformity before optimizing asymptotic estimates. RH remains unproved;
the complete signed source still lacks its required cofinal subpower bound.

The declaration index was regenerated. After one refresh for concurrent
source changes, the generated-file freshness errors cleared. Overall
`lint --check-generated` still fails solely because these other modules
are not reachable from their theorem-area umbrellas:

- `RHTower.EulerDeletionSignatureWordExpansion`
- `RHTower.Sieve.MenonHarmonicRamareLadderSwapped`
- `RHTower.Sieve.MenonHarmonicRamareLadderSwappedVolume`
- `HTGeometry.WeightedMinimax.Alternation`
- `HTGeometry.WeightedMinimax.Coefficient`

This work did not edit those modules or their wiring. The new
stretched-energy module is reachable and has no reported lint error.
The repository-wide lint gate is therefore not reported as passing.

All owned Lean, search, index and lint processes have ended. The 12
owned temporary files were removed after preserving their conclusions
and validation results here.

## Direct-current phase cancellation and inverse Abel attack [Lean]

The next attempted producer is a bound on the zero-specific current that
uses the phases lost in the complete primitive norm estimate. Before
claiming such a gain, test whether that phase transform has a bounded
inverse on the physical energy space. Write `A(k)=primitive N k`,
`S(k)=sourcePrefix N s k`, and `b(k)=(k+1)^(Re s-1)*|S(k+1)|`.
Finite summation by parts, retaining the endpoint, gives

```
A(k+1)=(k+1)^s*S(k+1)
        - sum_{n<k} ((n+2)^s-(n+1)^s)*S(n+1).
```

For `0<Re s<1`, the complex first difference is bounded by
`|s|*(n+1)^(Re s-1)`. Consequently

```
|A(k+1)|/(k+1) <= b(k)+|s|*sum_{n<k} b(n)/(k+1).
```

The finite Cesaro operator has a cutoff-independent square-energy bound.
One available proof uses domination by the transpose of the existing
Hardy kernel at `sigma=3/4`, whose squared operator bound is 25. Thus
the primitive's finite energy is at most
`2*(1+25*|s|^2)*sum b(k)^2`. If `a=2*Re s-1` lies in `(0,1)`, concavity
of `x^a` gives `(k+2)^a-(k+1)^a >= (a/2)*(k+1)^(a-1)`.
At an actual right-half zero the exact positive-current identity therefore
gives

```
primitiveEnergy N <= 4*(1+25*|s|^2)/a * Re(sourceCurrent N s).
```

The existing forward inequality and reflection give two-sided
comparison at every hypothetical off-line zero. This rules out a
growth-exponent gain from changing only between these two energy
descriptions. It does not bound either energy, and does not assert a
converse from RH to a bound on the unweighted norm. All three statements
are now proved in `EulerDeletionInverseAbel.lean`: the finite inverse
identity, the explicit reverse energy bound, and the cutoff-uniform
two-sided comparison. A new arithmetic argument using the zero equation
is still possible; the result only rules out a gain from the bounded
change of energy description itself. The signed arithmetic Gram estimate
remains a separate, unresolved producer.

### Independent attempts to produce the missing signed bound

**Conjecture: reciprocal-frequency orthogonality supplies the aggregate
Gram saving.** Four broad deep/method queries inspected signed quotient
correlations, inverse Hardy transport, signed residue Gram bounds, and
reciprocal Fourier/Kloosterman mechanisms. All returned partial results
at index generation 823339. The first two reported 2,196,271 of 2,336,767
semantic items ready, incomplete coverage and interrupted source/text
retrieval; the latter two did not complete their coverage response.
Candidate, declaration, source-argument, proof-idea and ingredient lanes
were inspected. No validated proof idea or ingredient set was returned.
Source-only candidates were not treated as verified Lean applications.

The inspected `KloostermanPhysicalResidueModulusBilinear` retains the
signed physical residue carrier, but its upper bound is a fixed-modulus
operator estimate. `KloostermanTerminalOrbitParseval` retains source
residue energies and a modulus-pair terminal budget.
`KloostermanGlobalFrequencyParseval` is an exact frequency identity.
`KloostermanProductFrequencyGcdBound` takes absolute source masses in its
quadratic bound. None supplies the EDQ Möbius-weighted upper bound. The
existing full-flux frequency expansion above gives a sharper test of
applicability: its `m=j=1` phase is `2*pi*d/e`, with bounded variation on
the balanced scaled rectangle, independent of N. That term gains no
large oscillatory parameter merely by increasing N. This attempt does
not close the signed estimate; the earlier finite-frequency remainder
bound remains valid.

**Conjecture: local sign-annihilation constraints transfer a small or zero
energy to the physical source.** The broad single-word arXiv search
`holonomy`, sorted by announcement date, found
[Kránitz–Iqbal–Penc, Chiral Color Ice](https://arxiv.org/html/2608.30802v1)
(31 August 2026). Sections III.1 and VI construct local positive parent
terms around an explicitly chosen state space and identify the global
zero-energy space with their common kernel. The paper's Möbius maps are
fractional-linear transformations, not arithmetic Möbius coefficients.
The method prompted an exact EDQ toy test: the coefficient vector
`(mu(1),mu(2))=(1,-1)` is annihilated by the scalar-sum map, while its
actual residue source at the positive physical integer k=1 is
`(1 mod 1)/1-(1 mod 2)/2=-1/2` (index zero in `residueVec`).
Thus a parent quadratic built only from that local
coefficient-sum constraint cannot dominate the actual physical Gram
quadratic, even at this cutoff. The positive kernel construction would
need a different, source-compatible constraint; declaring the desired
coefficient state to be a zero mode does not provide one. No numerical
experiment or new parent-operator module was warranted. This finite test
rejects that kernel transfer, not a different asymptotic family of
source-compatible local constraints.

Other broad searches included `avalanche`, `suspension`, `catalysis`, and
`inertia`. Primary sources inspected were
[Zhang, Tomter's example revisited](https://arxiv.org/html/2608.11097v1)
(11 August 2026) and
[Chen et al., Quantum hot carrier spectra in plasmonic catalysis](https://arxiv.org/html/2609.06949v1)
(7 September 2026). The first propagates already uniform hyperbolicity
from a dense orbit family; EDQ has no such uniform arithmetic estimate
to propagate. The second models material-specific carrier generation
and scattering, with no applicable arithmetic identity or bound found.
These papers were method prompts, not proof inputs.

### Inverse-Abel validation and remaining goal

`EulerDeletionInverseAbel.lean` has 305 lines and three public theorems:
`primitive_inverse_abel`, `primitiveEnergy_le_current`, and
`off_line_energy_comparison`. Development used foreground
`lake env lean` scratch checks. The final
`lake build --old GaloisForLFunctions.RHTower.EulerDeletionInverseAbel`
passed, compiling only this leaf in 229 seconds. The 13,108 jobs include
cached dependencies; no full or umbrella build was run. The module is
wired into `RHTower.lean`. One non-blocking tactic-sequence style warning
remains at line 264; there are no proof errors.

A separate `/tmp` audit printed axioms only for these three new theorems.
Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom or numerical result is used. The new comparison is a
closed universally quantified theorem about hypothetical off-line zeros,
not a proof of their absence.

After regenerating the index and refreshing once for concurrent changes,
`lint --check-generated` reports no generated-file freshness error and
no error for this module. Its only errors are two other modules still
unreachable from their theorem-area umbrella:

- `HTGeometry.WeightedMinimax.Coefficient`
- `HTGeometry.WeightedMinimax.PolyRoots`

Those modules were not edited by this work. The global lint gate is not
reported as passing. The frontier map remained read-only. No numerical
experiment was run. The RH goal remains open: neither the inverse
comparison, reciprocal-frequency attempt, nor local-kernel test supplies
the required cofinal subpower bound on the complete signed source.

All owned Lean, search, index and lint commands have finished. The 11
owned temporary files were removed after recording the proofs, search
conclusions and validation results. No owned Lean process remains.

## Logarithmic prime renewal: transport and feedback audit

**Status: unsuccessful estimate attack; paper calculations only.** No new
Lean theorem or stronger arithmetic ceiling is claimed. The surviving
question is an estimate for the complete signed source, not a missing
Abel identity. This audit does not retire EDQ or exclude an eventual or
cofinal estimate.

Write, on the full positive ray,

```
phi_n(u) = fract(u/n)/u,
R_N = sum_(1<=n<=N) mu(n)*phi_n,
J_N = sum_(1<=n<=N) mu(n)*log(n)*phi_n,
D_q f(u) = f(u/q)/q.
```

For the actual compensated generator sum G_N and harmonic sum H_N,
`R_N(u)=G_N(u)+H_N*fract(u)/u`. The compensated source vanishes on
`0<u<1`; its full-ray norm is therefore its original physical norm.
The correction has norm at most `sqrt(2)*|H_N|`: bound its seed by 1
below 1 and by `1/u` above 1. Thus this change preserves the question
of a cofinal subpower ceiling. It does not supply that ceiling.

The exact coefficient identity `mu*Lambda=-mu*log` and the finite
hyperbola interchange give

```
J_N = -sum_(2<=q<=N) Lambda(q)*D_q R_floor(N/q),
log(N)*R_N = sum_(1<=k<N) log((k+1)/k)*R_k - P_N,
P_N = sum_(2<=q<=N) Lambda(q)*D_q R_floor(N/q).
```

The second equality is finite Abel summation, with `log(1)=0` retained.
The divisor identities in `LocalizedHalfDensityCurvature` and
`TatuzawaIsekiIdentity`, and the Abel formula in `DeningerAbelSummation`,
provide existing source-level ingredients. This particular full-ray
package has not been checked in Lean.

**Conjecture → failure: joint rescaling makes a scalar renewal.** For
real cutoff t, put `V_t(x)=t*R_floor(t)(t*x)`. The prime packet does
become `t*D_q R_floor(t/q)(t*x)=V_(t/q)(x)`. However, the Abel integral
becomes

```
integral_(1<=v<=t) (t/v)*V_v((t/v)*x) dv/v.
```

It still contains spatial transport. Moreover,
`||V_t||^2=t*||R_floor(t)||^2` on the full positive ray. Removing that
factor or the transport would change the growth question. Keeping them
does not produce a contracting scalar kernel.

**Conjecture → failure: the actual prime feedback is nonnegative.**
At N=5, `H_5=-1/30` and all nonzero non-unit coefficients are negative:
`mu(2)=mu(3)=mu(5)=-1`, `mu(4)=0`. Each compensated generator is
nonnegative: with k=floor(u), its numerator is `(k mod d)/d`.
Consequently `R_5<=0` on the whole positive ray. Also
`J_5=-log(2)*phi_2-log(3)*phi_3-log(5)*phi_5<=0`.
On `0<u<1` both are strictly negative, with
`R_5=-1/30` and `J_5=-log(2)/2-log(3)/3-log(5)/5`.
All these finite sums are in L2. Hence
`<R_5,P_5>=-<R_5,J_5><0`. This disproves the proposed sign at all
cutoffs; it says nothing by itself against a large-cutoff or accumulated
bound. No numerical experiment is needed.

**Second pass: retain the cutoff-history variance.** Set
`w_k=log((k+1)/k)`, `E_N=||R_N||^2`, and

```
B_N = sum_(1<=k<N) w_k*E_k,
V_N = sum_(1<=k<N) w_k*||R_N-R_k||^2,
Gamma_N = V_N + 2*<R_N,P_N>.
```

Polarization gives `log(N)*E_N=B_N-Gamma_N`. Expanding the finite sums
also gives

```
Gamma_N = -sum_(m,n<=N) mu(m)*mu(n)*log(max(m,n))*<phi_m,phi_n>.
```

The nonnegative history variance therefore does not automatically
absorb the adverse feedback. Its combination with the feedback is a
signed Gram sum requiring an independent arithmetic bound. The second
pass found no such bound. The displayed identities are bookkeeping for
the attempted estimate, not a new producer or a completed no-go package.
No positive estimate was salvaged from scalarization or feedback
positivity; no replacement hypothesis is asserted as proved.

**Search and external-method audit.** Five deep/method searches used
120-second budgets, two rounds, all retrieval views, cached content,
`--any`, and no per-module cap. The mechanisms were largest-prime
factorization/renewal, joint cutoff/spatial scaling, signed transport
dissipation, hypocoercivity/Bellman memory, and logarithmic Abel energy.
Declaration, candidate-lemma, source-argument, proof-idea and ingredient
lanes were inspected. Results were partial, with pending coverage at
generations 823340/823347, source-only compiler metadata, interrupted
retrieval and unavailable/timed-out semantic service. They are not an
exhaustive absence certificate; no service was started to bypass this.

`GibbsSignedCovarianceAccumulation` preserves a partition mass in its
positive energy identity. `RouteEPhysicalFibreCoarea` uses normalized
factor masses and conditional means. Neither identifies its energy with
the present unnormalized source. `HodgeEdgeCochain.Energy` requires the
actual two-field equations and a skew cancellation identity.

Broad newest-first arXiv searches on renewal and dissipation supplied
two concrete transfer tests. [Ding--Tran--Vicente, 10 September 2026](https://arxiv.org/html/2609.11567v1)
use a memory-dependent merit function with sufficient-decrease polling;
the fixed arithmetic cutoff sequence supplies neither their polling
directions nor their decrease law. [Fischer--Krhac--Reis--Wierzba,
6 August 2026](https://arxiv.org/html/2608.05606v1) cancel the magnetic and
mechanical power terms through an explicit adjoint relation, retaining
external input and dissipation. Attempting that mechanism here leaves
the displayed Gamma_N; no opposite adjoint equation for a second
arithmetic state was obtained. Neither paper supplies the missing bound.

No Lean process, build, axiom re-audit or numerical experiment was run
for this attack. No new route-independent law is asserted from these
unformalized calculations. The frontier map remains read-only.
All five owned searches finished; their temporary JSON files were removed
after the findings were recorded. No owned process remains.

## Complete gcd groups: logarithmic budget diagnostic and transfer audit

The open target remains a cofinal subpower upper bound for the complete
signed physical source. No new bound or Lean theorem is claimed here.
The cotangent/Euclidean reciprocity proposal repeats the coefficient
transport obstruction already audited above; it is not a new result.

Two recent papers supplied different transfer attempts. In
[Vu et al., 6 September 2026, version 2](https://arxiv.org/html/2609.04169v2),
mechanical reciprocity restricts the response to symmetric operators,
with an additional positive-semidefinite restriction in the shared-block
case. The forbidden-component error floor does not upper-bound a quadratic
form in the permitted component. The actual EDQ Gram is already symmetric
and positive semidefinite, so this mechanism supplies no upper bound on its
Möbius quadratic form.

[Beier--Eckstein, 11 August 2026](https://arxiv.org/html/2608.11016v1)
use block means and quantization of kernels under probability measures.
For the actual finite Gram, let nu be uniform on {1,...,N}, and suppose
only that ||G-Ghat||_(L2(nu x nu))<=delta. Finite Cauchy--Schwarz gives

```
|sum_(m,n<=N) mu(m)*mu(n)*(G(m,n)-Ghat(m,n))| <= N^2*delta,
```

because |mu|<=1. Thus a subpower error in the original source would require
delta<=N^(-2+epsilon), or a sharper estimate that uses the signs. The
block-mean approximation does not itself supply either condition. This is
a normalization check, not a rejection of quantization or a new EDQ
receiver. No regularity bound for a normalized EDQ kernel curve has been
proved here.

The deep-search candidate
`eventually_sum_norm_sq_mtLiteralSignedSourceErrorLayer_dilation_le`
has also been checked against its source definition and terminal identity.
It bounds one Matomäki--Teräväinen error layer, under the displayed
rounded-geometric certificate, by `25*B^2*Y*(log X)^(-3*A)`.
`matomakiTeravainen_lemma23ii_terminal_all_layers` retains a separate sum
of signed main layers after the terminal remainder vanishes. Neither the
identification of that expansion with the EDQ physical source nor an
estimate for its resulting signed main term was obtained. Applying the
error-layer bound alone would leave the required energy uncontrolled.

The next finite diagnostic is frozen in
[the logarithmic gcd-budget protocol](../2-fully-proven/computations/edq-logarithmic-gcd-budget-2026-09-11/PROTOCOL.md).
For the original compensated Gram and literal Möbius coefficients it tests
both `sum_r |C_r(N)|<=4*D(N)` and
`sum_r |L_r(N)|<=4*Dlog(N)` at every cutoff 2<=N<=128. Here L inserts
`log(max(m,n))` inside each complete gcd group. Its aggregate is the exact
logarithmic cutoff-history difference of the original source energy.
The purpose is to distinguish whether this weighting loses the earlier
finite groupwise cancellation budget; no finite outcome establishes the
asymptotic estimate. Infinite physical tails have explicit allowances.

**NOT RUN:** the prescribed RunPod endpoint refused two SSH connections.
The four-worker program passed static syntax parsing only. It was not
uploaded or executed; its runtime and numerical controls remain unverified.
The endpoint question is pending. No computation was moved to another host.

Five broad deep/method searches used OR matching for divisor Gram
cancellation, cotangent reciprocity, continued-fraction transfer,
nearby-modulus clustering, and signed arithmetic convolution. All returned
partial coverage (generations 823348/823349), with source-only compiler
metadata and interrupted or unavailable retrieval stages. Declaration,
candidate-lemma, source-argument, proof-idea and ingredient lanes were
inspected; no candidate was accepted as a new proved source estimate.
These partial searches are not an exhaustive absence certificate.
No Lean process, build, axiom re-audit, frontier-map edit or universal-law
entry was needed for this transfer audit. The hard arithmetic bound remains
open; no route is retired.

## Compensated logarithmic renewal: compulsory linear forcing

The [compensated renewal attack](edq-compensated-log-renewal.md) tests whether
the harmonic correction in prime feedback can be discarded. It cannot:
the [formal source theorem](../3-formalized/edq-log-prime-forcing.md) proves
`c*N<=||B_N||^2<=C*N` eventually for the literal coefficients
`Lambda(q)*H_floor(N/q)`. The exact original-carrier identity is
`J_N=-A_N-B_N`, retaining the compensator at every earlier cutoff.
Its positive cell mean follows by PNT and dominated signed hyperbola
interchange; the lower bound uses the existing physical-window inequality.

The positive survivor is the complete forcing size law and exact renewal,
not an estimate for the original source G_N. The existing stretched source
bound also gives `||A_N+B_N||/||B_N||->0` by finite Abel summation on paper.
This identifies leading cancellation but leaves the RH-scale residual
uncontrolled. The next target remains the complete signed logarithmic
gcd-group budget, with A_N and B_N retained jointly. No route is retired.

Five additional deep/method searches were partial at generation 823349;
the exact search and source-freshness limitations are recorded on the attack
card. The broad recent-arXiv majorization candidate requires positive
weights and independent positions absent from the actual Mobius Gram.
The frozen RunPod diagnostic remains unrun after a third SSH refusal.
