# Route E: literal renewal energy attack

- **ID:** E-LREA-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ACTIVE PROOF ATTEMPT
- **Target:** unconditional bounded returns of the literal Möbius Gamma–Hankel covariance for orders cofinal above one.
- **Status:** RH remains unproved. The [shifted-moment and mixed-pairing sign](../3-formalized/mobius-renewal-shifted-moment-sign.md) is closed in Lean. No numerical experiments authorized or used.

## Proof chain and hard obstacle

For `F_N(x)=sum_{1<=n<=N} mu(n) exp(-n*x)`, the existing exact integral is
`E_N(r)=integral_0^infinity x^(r-1) F_N(x)^2 dx`.
The diagonal is uniformly bounded for each `r>1`. Bounded returns of the signed
off-diagonal covariance, for orders cofinal above one, imply RH through the
existing Mellin–Plancherel theorem. The unresolved step is this upper bound for
the literal integer prefix, with its whole shrinking cusp retained.

## Work plan

1. Search full corpus statements and proof methods for signed renewal energy
   mechanisms; inspect exact source identities and applicability.
2. Attack the finite divisor-renewal equation by an energy pairing. Test every
   proposed sign on the actual coefficients before attempting an infinite limit.
3. If it fails, retain its exact source defect and test a compensated inequality;
   formalize only a dependency-closed result that settles the attempted mechanism.
4. Check targeted Lean files; update only justified route-independent
   facts in the global ledger. Do not count a conditional receiver as an RH proof.
   User subsequently excluded `#print axioms` checks; do not run them.

## Source and method search

- `research 'Mobius Laplace covariance cusp' --mode deep`: partial result;
  semantic deadlines and unavailable Qdrant lane; generated queries confused
  Möbius arithmetic with Möbius transformations. No applicable producer found.
- Exact-name and signed-renewal method searches launched next. Available corpus
  hits must be checked against source and this Lean toolchain.
- Broad arXiv searches: hypocoercivity, renewal, discrepancy, balayage, prioritizing
  June–September 2026. [Bouin–Dolbeault–Ziviani, 2608.28120](https://arxiv.org/abs/2608.28120)
  suggests coupling a weighted norm with dissipation; its kinetic equation and
  stationary-state assumptions have not been realized for this source.
- [Doron et al., 2606.24471](https://arxiv.org/abs/2606.24471) tracks second moments
  during random-generator insertion. A random-code theorem supplies no estimate
  for deterministic Möbius coefficients without a proved arithmetic comparison.

## Conjecture/proof loop

### Attempt 1: uncompensated renewal accretivity

Write `R_N=exp(-x)-F_N`. Divisor inversion identifies it with the full
nonidentity part of `sum_{1<=k<=N} F_floor(N/k)(k*x)=exp(-x)`.
The proposed sufficient sign `integral x^(r-1) F_N R_N >= 0` fails already
for the actual three-term section at `r=1`: the integrand is
`exp(-3*x)-2*exp(-5*x)-exp(-6*x)`, with integral `-7/30`.
This exact algebra uses no numerical experiment. It does not refute bounded
returns or diagonal dominance of the original covariance.

### Attempt 2: retain a fixed compensation budget

Put `U_N(r)=sum_{n=1}^N mu(n)/(n+1)^r` and
`V_N(r)=sum_{n=1}^N mu(n)/n^r`. The exact energy equation is
`integral x^(r-1) F_N R_N = Gamma(r)*U_N(r)-E_N(r)`.
Hence a lower bound `>= -kappa*E_N-B`, with `kappa<1`, would give a
uniform upper energy bound once `U_N` is bounded. The equation itself supplies
no such lower bound: declaring it would reinsert the unresolved estimate.

There is a source-specific sign accessible before that estimate. Set
`d_n(r)=n^(-r)-(n+1)^(-r)`. For `r>=1`, all `d_n` are nonnegative.
Using `mu(1)=1`, `mu(4)=0`, and `mu(n)>=-1`, for every `N>=4`,

```
V_N(r)-U_N(r)
 = sum_{n=1}^N (1+mu(n))*d_n(r) - sum_{n=1}^N d_n(r)
 >= 2*d_1(r)+d_4(r)-1+(N+1)^(-r)
 >= d_4(r).
```

For `r>1`, `V_N(r)` converges to the regular reciprocal zeta value.
That value tends to zero as `r` decreases to one, whereas `d_4(r)` tends
to `1/20`. Thus, on an entire interval immediately above one, `U_N(r)`
is eventually strictly negative, uniformly bounded away from zero.
Consequently the full renewal pairing is eventually negative there, not just
at a small exceptional cutoff. The finite lower bound, original-moment convergence,
and eventual inequality `U_N(r)<-1/80` pass `lake env lean` in scratch.
The exact integral pairing and its eventual bound `<-Gamma(r)/80` are also
closed; the complete leaf passed its targeted `lake build`.
It still supplies no upper bound for `E_N` or `C_N`.

### Attempt 3: transfer a compensated-energy method

The August hypocoercivity paper's Section 2 requires microscopic and macroscopic
coercivity, compatibility with projection onto the collision kernel, and bounded
auxiliary operators. Its Section 3 instead constructs a positive weight with
`L* m <= C*1_B - eta*m^(1-ell)`. Neither hypothesis is furnished by the
arithmetic renewal identity. Assigning either to the source is not a proof.
The June random-code paper controls one common self-convolution before using its
exact one-step variance identity. For literal deterministic prime insertion,
the corresponding signed covariance is precisely what is unpaid. No random
generator theorem can be applied without establishing the conditional source law.

The deep compensated-covariance search returned the existing RH receivers and
finite divisor-channel counterexamples, with no validated ingredient set. The
direct compensated bound remains open; the next attack must estimate it from
literal incomplete integer/product incidence.

### Attempt 4: primitive-ray nonlinear addition

The source already satisfies the complete nonlinear identity
`sum_{(a,b)=1} Phi(a*x)*Phi(b*y)=Phi(x+y)` for positive `x,y`, in
`VisibleCoprimeMobiusLaplaceAddition.visibleCoprimeMobiusLaplaceSum_eq_add`.
Its proof includes absolute convergence at each fixed positive pair.
Setting `x=y` retains the desired square and all coprime cross terms. An integral
over the shrinking cusp cannot discard those terms or assume their norm-summability.
No such uniform integral estimate was found or proved. Reusing the exact identity
alone would not advance the open upper bound.

### Attempt 5: audit the strength of collective diagonal dominance

[PAPER PROOF; NOT LEAN] The frozen assertion `C_N(r)<=0` for all `N` and
`r>1` would imply simplicity of every critical-line zero, as well as RH.
This does not falsify the assertion. It identifies an additional conclusion
that the proposed bound would have to deliver; no converse from RH is proved.

Here is the complete argument, retaining the literal prefix. Put
`Phi(x)=sum_(n>=1) mu(n) exp(-n*x)` and
`E(r)=integral_0^infinity x^(r-1)|Phi(x)|^2 dx`. Under the asserted finite
diagonal dominance, the diagonal estimate and Fatou give, for `0<d<1/4`,

```
E(1+d) <= Gamma(1+d) * 2^(-1-d) * zeta(1+d) <= A/d.
```

The same `A` works on this interval: Gamma is bounded on the compact interval,
and integral comparison gives `zeta(1+d)<=1+1/d`. Fatou is applied to the
nonnegative squared densities using the existing pointwise convergence of
integer prefixes; no inverse Fatou step or complete-prime substitution occurs.

Fix a critical-line zero `rho`, and set `s_d=rho+d`. The finite base energy
at exponent `1+d` admits the Mellin transform on `Re(s)>(1+d)/2`. The corpus's
`mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base`
then gives `M(s_d)*zeta(s_d)=Gamma(s_d)`; `s_d!=1`, and Gamma is nonzero.
On the head, Cauchy--Schwarz gives exactly

```
|integral_0^1 x^(s_d-1) Phi(x) dx|
 <= sqrt(E(1+d)) * sqrt(integral_0^1 x^(d-1) dx)
 <= sqrt(A)/d.
```

On `x>=1`, the unconditional geometric majorant for `Phi` is exponential;
since `Re(s_d)<3/4`, the tail is bounded by one constant `T`, independent of
`d`. Hence `d*M(s_d)` is bounded as `d` tends to zero from above. If also
`zeta'(rho)=0`, the definition of derivative and `zeta(rho)=0` give
`zeta(rho+d)/d -> 0`. Multiplying the two factors in the canonical Mellin
identity would give `Gamma(rho)=0`, a contradiction. Thus `zeta'(rho)!=0`.
Analyticity makes every such zero simple.

The existing `MobiusLaplaceBoundaryMultiplicity` implements this last bounded
factor/vanishing factor contradiction with a different source hypothesis
(pointwise half-power decay). That hypothesis is not being reused here:
the displayed energy estimate supplies the radial bound directly. The
energy-to-radial estimate and its composition above have not been formalized.

**Decision:** retain collective diagonal dominance as an open, stronger
candidate. Keep the main attack on bounded returns with arbitrary constants
depending on `r`; do not insert an inverse-distance growth bound into that
target without an independent arithmetic proof.

### Attempt 6: diagonalize the additive kernel while retaining the source

[PAPER IDENTITY; NOT LEAN] For `n>=1`, define `q_n=(n-1)/(n+1)` and

```
b_(N,k)(r) = sum_(1<=n<=N) mu(n)/(n+1)^r * q_n^k,
w_k(r) = r*(r+1)*...*(r+k-1)/k!,    w_0(r)=1.
```

For every finite `N` and `r>0`, the exact energy expansion is

```
E_N(r) = Gamma(r) * 2^r * sum_(k>=0) w_k(r) * b_(N,k)(r)^2.       (6.1)
```

Indeed, `0<=q_n<1` and
`m+n=((m+1)*(n+1)/2)*(1-q_m*q_n)`. Apply the binomial series to
`(1-q_m*q_n)^(-r)`, then interchange its convergent series with the finite
double sum. Each coefficient is a square. At `r=1` this is just the geometric
series. The installed corpus contains the general real binomial-series
identity in `Mathlib/Analysis/Analytic/Binomial.lean`,
`Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`; its use in (6.1)
has not been checked in Lean.

These are literal arithmetic packets, not freely chosen coordinates. They
obey the exact adjacent-order relation

```
b_(N,k+1)(r) = b_(N,k)(r) - 2*b_(N,k)(r+1),
```

and `b_(N,0)(r)` is the shifted moment proved negative near `r=1` in the
completed leaf. The relation follows termwise from `q_n=1-2/(n+1)`.

**Conjecture tested:** positivity of the expansion, combined with absolute
packet estimates or separate convergence of its coordinates, supplies the
missing energy ceiling. **Failed proof attempt.** For fixed `r>1`,
`|mu(n)|<=1` and `q_n^k<=exp(-2k/(n+1))` give only
`|b_(N,k)(r)|<=C_r*(k+1)^(1-r)`, uniformly in `N`. One proof divides the
positive integers into dyadic intervals above and below `k+1`: the upper
tail is geometric with exponent `1-r`; below that scale the exponential
beats the dyadic power. Also `w_k(r)` is comparable to `(k+1)^(r-1)`:
take logarithms of `product_(j=1..k)(1+(r-1)/j)` and bound the difference
from `(r-1)*sum_(j=1..k)1/j` by a convergent reciprocal-square series.
The resulting summable-majorant argument works only for `r>2`, giving no
estimate in the required interval `1<r<=2`.

For each fixed `k` and `r>1`, the infinite arithmetic packet exists by
absolute convergence in `n`. This is insufficient for (6.1): energy may
escape to packet indices growing with `N`. The adjacent-order identity has
a signed cross term after squaring, so it supplies no monotone energy
telescope. A uniform bound on the complete weighted square sum, or on a
subsequence of literal cutoffs, is still unpaid. No new receiver module is
counted as progress on that bound.

### Further method-transfer checks

- Broad searches `pinching`, `intertwining`, and `dissipation` found
  [Cho, arXiv:2608.26598v2](https://arxiv.org/html/2608.26598v2),
  [Vega Coso, arXiv:2608.15140v1](https://arxiv.org/html/2608.15140v1), and
  [Elber--Lheem, arXiv:2608.01485](https://arxiv.org/abs/2608.01485).
  Cho retains coupled coefficients and proves a cone inequality by a
  nonnegative combination of frame inequalities. Version 2 explicitly
  restricts the completed gluing argument to dimension eight; the
  dimension-seven gluing is not established. No corresponding source
  inequalities have been proved for the Möbius packets. Vega Coso's
  resolvent symmetry requires a proved transition-operator intertwining;
  divisor reconstruction does not establish such a symmetry. Elber--Lheem
  concerns finite-field matrix families; its abstract supplies no transfer
  to incomplete ordinary-integer Möbius sums.
- Deep queries for diagonal dominance, coupled coercivity, and
  Legendre/Laplace moments returned available statement and proof-method
  hits, but no validated ingredient set. The searches reported partial
  coverage and local semantic/reranking deadlines, not exhaustive absence.
  A lexical Mellin/Cauchy--Schwarz search recovered the actual energy
  continuation bridge used in Attempt 5. The retrieved
  `MonotoneMobiusPositivity` source uses an absolute reciprocal-square
  tail smaller than one; it does not cross the critical exponent barrier.

### Attempt 7: test a sign-preserving packet recurrence on the literal source

[CONJECTURE UNDER TEST] A scalar sign can orient the packet sequence into
a completely monotone sequence: all iterates of `D b(k)=b(k)-b(k+1)` are
nonnegative. Such a representation would admit positive moment methods.
This is a proposed intermediate mechanism, not the bounded-return target.

The direct source test is stronger than inspecting a few low-order differences.
With the packets of Attempt 6, their exact differences satisfy

```
D^j b_(N,k)(r)
 = sum_(1<=n<=N) mu(n)/(n+1)^r * q_n^k * (2/(n+1))^j.
```

For every fixed `r>=0`, uniformly over **all** `N>=2`, the proposed limits are

```
D^(h+2) b_(N,0)(r) -> 2^(-r),
(3/2)^h * D^(h+2) b_(N,1)(r) -> -(4/27)*3^(-r).
```

Paper proof: the first detector retains `mu(1)=1` while all other normalized
bases are at most `2/3`. The second kills the first coefficient through
`q_1=0`, retains `mu(2)=-1`, and gives base at most `3/4` to every later
coefficient. The two extra differences give the common summable majorant
`4/(n+1)^2`; `r>=0` only decreases its size. The errors are bounded by a
fixed summable budget times `(2/3)^h` and `(3/4)^h`, respectively. Thus no
scalar orientation can make every difference nonnegative.

The positive result to formalize is the **uniform quantitative recovery of
these two opposite source coefficients**, together with the exact difference
identity. This preserves the literal integer cutoff, gives no energy ceiling,
and does not reject arbitrary signed recurrence methods. The subsequent
signed-energy attempt must retain both channels and estimate their aggregate
interaction instead of turning them into positive probability masses.

## Checkpoint

- Completed leaf: `GaloisForLFunctions.RHTower.MobiusRenewalEnergySign`;
  namespace `RHTower.MobiusRenewalEnergy`. All six public theorems passed
  together in scratch and the final targeted build; umbrella import wired.
- Generated indexes refreshed. Formal lint passed with existing file-size warnings.
- One foreground Lean invocation at a time; no numerical experiments, no
  `#print axioms`, no umbrella/full build.
- Do not promote this card as an RH proof. Even after the sign theorem is closed,
  the compensated source-energy estimate remains open.
- Attempts 5--6 are paper work only. Diagonal dominance would also force
  critical-zero simplicity; the positive packet expansion does not provide
  cancellation. No additional Lean result or covariance bound is claimed.
- Next hard target: derive a source-specific lower bound for the mixed feedback
  with coefficient strictly better than `-E_N`, or bound the original signed
  moving-cusp covariance directly. The bound must come from incomplete physical
  integer/product incidence, not be assumed in an abstract energy inequality.

## Log

- 2026-09-11 — Opened source-specific energy attack from Route E's moving-cusp
  frontier. Existing absolute renewal contraction and complete-prime substitutions
  are excluded; this attempt retains signed finite cutoffs.
