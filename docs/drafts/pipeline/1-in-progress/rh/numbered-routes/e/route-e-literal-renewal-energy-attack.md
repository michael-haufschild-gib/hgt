# Route E: literal renewal energy attack

- **ID:** E-LREA-001
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ACTIVE PROOF ATTEMPT
- **Target:** unconditional bounded returns of the literal Möbius Gamma–Hankel covariance for orders cofinal above one.
- **Status:** RH remains unproved. The [shifted-moment and mixed-pairing sign](../../../../3-formalized/mobius-renewal-shifted-moment-sign.md) is closed in Lean. No numerical experiments authorized or used.

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

[FALSIFIED IN LEAN] A scalar sign can orient the packet sequence into
a completely monotone sequence: all iterates of `D b(k)=b(k)-b(k+1)` are
nonnegative. Such a representation would admit positive moment methods.
This is a proposed intermediate mechanism, not the bounded-return target.

The direct source test is stronger than inspecting a few low-order differences.
With the packets of Attempt 6, their exact differences satisfy

```
D^j b_(N,k)(r)
 = sum_(1<=n<=N) mu(n)/(n+1)^r * q_n^k * (2/(n+1))^j.
```

For every fixed `r>=0`, uniformly over **all** `N>=2`, the proved limits are

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

The formalized positive result is the **uniform quantitative recovery of
these two opposite source coefficients**, together with the exact difference
identity. The same leaf retains `mu(2),mu(3),mu(5)` and `mu(4)=0` to prove the
shifted moment eventually exceeds `1/200` throughout a nonempty interval above
exponent two. Together with its negative sign above one and the exact
adjacent-exponent recurrence, this proves `b_(N,0)(r)^2 < b_(N,1)(r)^2`
eventually in cutoff near `r=1`. This excludes descent from the first packet
step, not every possible eventual tail estimate. See the
[closed source theorem and positive survivor](../../../../5-failed/mobius-packet-complete-monotonicity.md).
This preserves the literal integer cutoff, gives no energy ceiling,
and does not reject arbitrary signed recurrence methods. The subsequent
signed-energy attempt must retain both channels and estimate their aggregate
interaction instead of turning them into positive probability masses.

### Attempt 8: retain the adjacent-exponent mixed term

[FAILED BOOTSTRAP; PAPER CALCULATION] Test whether the known absolute bound
at `r+1>2` can control the energy at `r>1` through the exact packet recurrence.
Write `S_N(r)=sum_k w_k(r)*b_(N,k)(r)^2`. The cumulative binomial weights
are `sum_(j<=k) w_j(r)=w_k(r+1)`. At every fixed finite integer cutoff,
all the packets decay geometrically in `k`, so summation by parts retains
no boundary term and gives

```
S_N(r) = 4 * (X_N(r) - S_N(r+1)),
X_N(r) = sum_k w_k(r+1)*b_(N,k)(r)*b_(N,k)(r+1).
```

This mixed term can be evaluated before any inequality. Applying the same
convergent binomial series as in Attempt 6 gives

```
X_N(r) = 2^(-r-1) * sum_(m,n<=N) mu(m)*mu(n)*(m+1)/(m+n)^(r+1)
       = S_N(r)/4 + S_N(r+1).
```

The second equality symmetrizes the numerator into `(m+n+2)/2`; it retains
every ordered pair. Thus the proposed bootstrap is an identity. In particular,
substituting an upper bound for `S_N(r+1)` cannot isolate `S_N(r)`.
Cauchy--Schwarz instead asks for the different norm
`sum_k w_k(r+1)*b_(N,k)(r)^2`; the known higher-exponent energy has
`b_(N,k)(r+1)` in that position. No comparison between those norms has been
proved. This rejects this inference, not every possible signed recurrence
estimate. No new bounded-return theorem results, and these infinite packet
identities remain paper work rather than a claimed Lean module.

### Further source and method checks for Attempts 7--8

- Broad `avalanche` search found [Hénard, August 2026](https://arxiv.org/html/2608.10992v1).
  His triangular tail system uses a stochastic regeneration construction;
  its uniform-mixture extremal inequality requires decreasing nonnegative
  probability masses. Neither property has been established for the literal
  Möbius packets. Complete monotonicity in Attempt 7 was our proposed stronger
  representation, not an assumption claimed to occur in that paper.
- Broad `Carleson` search found [Bényi--Hu--Zhou, June 2026](https://arxiv.org/html/2606.28292v1).
  Proposition 2.4 requires a scale-invariant gradient tent norm, while
  Theorem 3.2 decomposes a function already in the specified oscillation space.
  Neither establishes the missing arithmetic mixed-norm bound. The related
  [August embedding counterexample](https://arxiv.org/abs/2608.04981) was
  checked at abstract level only; no transfer of its construction is claimed.
- Broad `Lyapunov` search found [Fayad et al., September 2026](https://arxiv.org/html/2609.03722v1).
  The theorem perturbs indefinite Hamiltonians while retaining a prescribed
  finite normal form. No such perturbation or Hamiltonian realization of the
  literal source has been constructed here.
- Deep corpus queries for packet cancellation, signed-atom finite differences,
  and weighted adjacent-exponent compensation inspected `candidate_lemmas`,
  `source_arguments`, `proof_ideas`, and `ingredient_sets`. Coverage was partial;
  no returned ingredient set supplied the missing bound. A proposed inverse-load
  transfer left its source-identification and cancellation obligations open.
  The lexical `Hardy telescoping` follow-up recovered
  `MobiusThetaAdaptivePrimeNormalCodiagonal`: its quartic tail contraction
  changes the spectral exponent and explicitly leaves the physical completion
  comparison open. It is not an estimate for the packets at the fixed exponent.

## Attempt 9: exact product fibres and removal of the diagonal

[CLOSED CLASSIFICATION; NO SIGNED CEILING] Group every original pair by
`q=m*n`, retaining its weight and both cutoff inequalities. The complete
result is recorded in [the product-fibre card](../../../../5-failed/mobius-product-fibre-absolute-summation.md).
The exact identity `mu(m)*mu(n)=lambda(m*n)*mu(m)^2*mu(n)^2` proves
that every nonzero pair in one fibre has the same sign, including pairs
with common prime factors. Square-product fibres are exactly the diagonal;
nonsquare-product fibres are exactly the covariance.

The total absolute fibre mass is at least
`(2^(-r)/16)*N^(2-r)` for `N>=1,r>=0`. Removing the complete bounded
diagonal still leaves absolute variation tending to infinity for `1<r<2`.
These are unconditional Lean theorems in `MobiusProductFibreVariation`.
Thus neither internal product-fibre cancellation nor absolute summation of
the remaining fibres can produce the desired bound. A signed comparison
between different products remains possible and unpaid.

## Attempt 10: retain the boundary in a one-prime pairing

[PAPER TEST; NO COVARIANCE ESTIMATE] The corpus theorem
`mobiusComplexCoefficient_eq_primeFree_difference` suggests pairing a
cofactor with its prime multiple. For a prime `p`, put

```
A_N^p(x) = sum_(1<=n<=N, p does not divide n) mu(n)*exp(-n*x),
M = floor(N/p),
B_(N,p)(x) = A_N^p(x)-A_M^p(x).
```

Squarefree prime insertion gives the exact physical cutoff identity

```
F_N(x) = A_N^p(x)-A_M^p(p*x)
       = H_(N,p)(x)+B_(N,p)(x),
H_(N,p)(x) = A_M^p(x)-A_M^p(p*x).
```

For `r>0`, the complete prime cells inside `H` have kernel

```
Q_(p,r)(m,n) = (m+n)^(-r)-(p*m+n)^(-r)
              -(m+p*n)^(-r)+(p*m+p*n)^(-r).
Gamma(r)*Q_(p,r)(m,n)
 = integral_0^infinity x^(r-1)
     *(exp(-m*x)-exp(-p*m*x))*(exp(-n*x)-exp(-p*n*x)) dx.
```

The integral representation follows by expanding four admitted exponential
integrals. For positive `m,n`, each factor is positive on `x>0`, so `Q>0`.
The complete cell still carries the sign `mu(m)*mu(n)=lambda(m*n)` on
squarefree cofactors. Pointwise `0<=Q<=K`, where `K=(m+n)^(-r)`, cannot
be promoted to an inequality between quadratic forms with signed coefficients.
Moreover the actual source energy retains all three contributions

```
E_N(r) = ||H_(N,p)||_r^2
         +2*<H_(N,p),B_(N,p)>_r+||B_(N,p)||_r^2.
```

The interval defining `B` is exactly `(floor(N/p),N]`; it is not an error
that this identity bounds. No estimate for its mixed term or complete energy
has been derived. Hence the proposed direct inference from prime sign reversal
and kernel positivity to a covariance ceiling fails. These paper identities
are not a new Lean producer and do not exclude a collective many-prime estimate.

Deep source/method searches for weighted prime remainders and dilation
differences had partial coverage and returned no closed ingredient set.
`LiouvilleSignedCofactorDilation` retains the full nondivisible-cofactor
remainder. `MobiusMultiplicativeRectangleCubature` controls an already-admitted
rectangle family and retains the uncovered residual; it constructs no covering.
The fixed-prime window identity in `MobiusMertensPrimeRemovalTentLaw` similarly
leaves its signed interval sum. The next arithmetic target is an actual
many-prime incidence estimate for the retained weights and boundary, not
another prime-removal identity or complete-prime replacement.

## Checkpoint

- Completed leaf: `GaloisForLFunctions.RHTower.MobiusRenewalEnergySign`;
  namespace `RHTower.MobiusRenewalEnergy`. All six public theorems passed
  together in scratch and the final targeted build; umbrella import wired.
- New leaf: `GaloisForLFunctions.RHTower.MobiusPacketDifferenceSign`. Its complete
  source proof passed `lake env lean /tmp/route_e_packet_combined.lean` without
  warnings; umbrella import wired. The final targeted command
  `lake build GaloisForLFunctions.RHTower.MobiusPacketDifferenceSign` passed.
  Lake replayed informational tactic suggestions from existing dependencies;
  the new module emitted no warnings.
- Generated indexes refreshed. Formal lint passed with existing file-size warnings.
- Product-fibre source passed its complete scratch check and the final targeted
  `lake build GaloisForLFunctions.RHTower.MobiusProductFibreVariation`;
  umbrella import wired. Its subsequent index refresh and formal lint passed;
  no own Lean process remains.
- One foreground Lean invocation at a time; no numerical experiments, no
  `#print axioms`, no umbrella/full build.
- Do not promote this card as an RH proof. Even after the sign theorem is closed,
  the compensated source-energy estimate remains open.
- Attempts 5--6 and 8 are paper work only. Diagonal dominance would also force
  critical-zero simplicity; the positive packet expansion does not provide
  cancellation. Attempt 7's source signs and recurrence are now formal, but
  no covariance bound is claimed.
- Next hard target: derive a source-specific lower bound for the mixed feedback
  with coefficient strictly better than `-E_N`, or bound the original signed
  moving-cusp covariance directly. The bound must come from incomplete physical
  integer/product incidence, not be assumed in an abstract energy inequality.

## Log

- 2026-09-11 — Opened source-specific energy attack from Route E's moving-cusp
  frontier. Existing absolute renewal contraction and complete-prime substitutions
  are excluded; this attempt retains signed finite cutoffs.
- 2026-09-11 — Closed the exact product-sign, square-product diagonal and divergent
  nonsquare absolute-variation theorems. Retained the full boundary in the next
  paper prime-pairing test; no signed covariance estimate follows.
