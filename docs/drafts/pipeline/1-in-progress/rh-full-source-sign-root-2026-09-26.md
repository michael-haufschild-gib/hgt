# Direct attack on the complete theta source sign

- **ID:** RH-FULL-SOURCE-SIGN-ROOT-20260926
- **Owner:** root
- **Stage:** 1-in-progress
- **Type:** attack on the existing RH sign problem; no new primary conjecture claimed
- **Status:** S1 formalized and audited; unrestricted source sign remains open

## Fixed target

For the literal complete theta source Phi, prove, for every finite real node
family x and complex coefficient family c,

`sum_ij conj(c_i)*c_j*K(x_i,x_j) >= 0`,

where `K(x,y)=integral_(s>0) (x+y+2s)*Phi(x+s)*Phi(y+s) ds`.
The inequality concerns the real value of the Hermitian form. No finite-rank,
fixed-tail, or strict-reserve replacement is the target. The existing source
weld supplies the RH implication. C12 identifies the negative dimensions but
does not prove that they vanish.

## Proof attacks and exact outstanding content

1. **Translation propagation.** The inspected actual-source theorem
   `thetaTailCommonTranslationGenerator_twoNode_det_neg` already refutes
   Loewner monotonicity. Its determinant is
   `-(x-y)^2*(Phi(x+a)*Phi(y+a))^2`.
   A first-crossing argument would need a different, independently proved
   condition on null vectors. No such condition was proved. Repackaging this
   existing obstruction is not new progress.

2. **Divisor compensation.** The exact divisor regrouping is already present
   in `ThetaCuspFinitePrimeFluxSplit`. The actual packet identity in
   `ThetaCuspFinitePrimeFluxWindow` retains an archimedean term minus the
   von Mangoldt term. The divisor identity alone supplies no inequality
   between those paired terms. No new positive decomposition was obtained.

3. **Ground-state proof attempt.** A candidate way to attack the sign is to
   keep the literal theta density in a signed jump-energy comparison. Put

   `D_Phi(f,u)=integral_R Phi(x)*Phi(x+u)*|f(x+u)-f(x)|^2 dx`,

   for smooth compactly supported f, and test

   `integral_0^infinity [exp(-u/2)/(1-exp(-2u))-2*cosh(u/2)]*D_Phi(f,u) du`
   ` + sum_(n>=2) Lambda(n)/sqrt(n)*D_Phi(f,log n) >= 0`.

   **Unproved attack target, not a theorem or certified RH equivalence.**
   The proposed ground-state identity relating this expression to the
   literal Weil form now has the S1 source-annihilation input. Exact form
   normalization and the remaining test-function exchanges still need proof.
   Even that identity would only relocate the sign obligation.

   The direct proof attempt by positivity of each jump fails: the continuous
   coefficient is half the existing `ArchimedeanKernel.weilKernel` and is
   strictly negative beyond its proved threshold. The atomic prime terms
   must compensate this entire negative contribution. Omitting it or
   assuming the comparison would assume the missing mathematics.

## Frozen S1: literal source equation needed by the direct attack

**Derived [BRIDGE], frozen before formal proof; not a new primary conjecture.**
Let `rho(u)=exp(-u/2)/(1-exp(-2u))` and

`G_+(x)=-(EulerGamma+log(pi))*Phi(x)/2`
` + integral_0^infinity [exp(-2u)*Phi(x)-exp(-u/2)*Phi(x+u)]/(1-exp(-2u)) du`
` + integral_0^infinity 2*cosh(u/2)*Phi(x+u) du`,

`P_+(x)=sum_(n>=2) Lambda(n)/sqrt(n)*Phi(x+log n)`.

The frozen identity is `G_+(x)-P_+(x)=x*Phi(x)` for every real x,
with all displayed integrals and sums absolutely convergent. Reflection then
gives the full signed source equation at x by adding the identities at x and
-x. The subtraction in the first integral is kept inside the integrand.

Paper mechanism: on `Re(w)>1/2`, absolute Fubini sends a right shift by u
to multiplication by `exp(-w*u)`. The polar integrals give
`1/(w-1/2)+1/(w+1/2)`. Gauss's digamma formula gives the remaining
Gamma factor; the prime sum gives the actual von Mangoldt L-series.
The known completed-Xi logarithmic-derivative identity times the actual
theta transform yields its first moment. Weighted Fourier uniqueness then
gives S1. This mechanism is now proved in Lean, including convergence and pointwise
recovery. S1 alone does not prove the jump-energy comparison.

## Right-problem gate

Only a proof or counterexample for the complete-source inequality, or a
source-specific argument that discharges a genuine part of its unrestricted
sign obstruction, counts as RH progress. Another equivalent criterion,
generic positive-form lemma, or already-known comparison failure does not.
No additional Lean receiver is to be presented as advancement of the sign.

## Evidence and limits

Inspected actual sources: `ThetaTailCommonTranslationLoewnerNoGo`,
`ThetaCuspFinitePrimeFluxSplit`, `ThetaCuspFinitePrimeFluxWindow`,
`SuzukiRestrictedWeilSourceForm`, `ArchimedeanWeilKernelSign`.
Search records: `/tmp/rh-c13-translation-sign-search.json`,
`/tmp/rh-c13-inertia-flow-search.json`,
`/tmp/rh-c13-divisor-compensation-search.json`,
`/tmp/rh-c13-ground-state-search.json`. These searches completed without
reported partial-stage errors. Inventory coverage does not certify proof
applicability; compiler metadata is predominantly pending/source-only/stale.

Frozen S1, including the literal `Lambda(n)/sqrt(n)` coefficient, is proved in
`/tmp/rh-s1-full.lean` (exit 0). `literal_complete_theta_source_equation` and
all reported dependencies use only `propext`, `Classical.choice`, `Quot.sound`.
The proof retains the complete source and infinite sum. Its supporting lemmas
prove pointwise absolute summability, continuity, the Gamma cancellation at
zero, joint absolute Fubini, and weighted Fourier uniqueness. All four named leaf builds pass; each leaf is wired exactly once. All 71 public
declarations pass the axiom audit, standard axioms only, none missing. Index
regeneration succeeds. Global lint exits 1 only for unrelated unwired
`RHTower.CircleLinearPhaseSeamMargin`; no new-leaf or stale-index error.

Formal leaves: `ThetaSourcePrimeAction`, `ThetaCuspGammaSourceAction`,
`ThetaCuspPolarSourceAction`, `ThetaCuspPrimeArchSourceEquation`. The literal
statement is `RHTower.ThetaSourceWard.literal_complete_theta_source_equation`.
Logs: `/tmp/rh-s1-{prime,gamma,polar,equation}-build.log`,
`/tmp/rh-s1-final-axioms.log`, `/tmp/rh-s1-index.log`, `/tmp/rh-s1-lint.log`.

Paper proof: choose the Fourier line `Re(w)=3/4`. The physical Gamma integrand
has a uniform small-u bound `C*exp(-|x|)` from the actual derivative envelope;
for `u>=1`, its x-L1 norm is bounded by a constant times
`exp(-2u)+exp(-(1/2+Re(w))*u)`. Thus scalar Fubini is absolute. Substitution
`t=2u` gives half the Gauss digamma integral. The two polar transforms give
`(w-1/2)^(-1)` and `(w+1/2)^(-1)`. The full prime transform is the actual
von Mangoldt L-series at `1/2+w`, with absolute exchange. Subtracting the
completed-Xi symbol identity makes every Fourier value of the weighted
continuous residual zero. Fourier inversion makes that residual zero at every
real x. This proves exactly S1, with no RH or positivity premise.

### Further sign attempt: commuting the two one-sided actions

The source equation suggests splitting the symmetric annihilator into its
right and left actions. A naive commutation argument is invalid before a
new convergence proof: the two positive polar pieces alone have double
integrand `exp((u+v)/2)*Phi(x+u-v)`. On `v=u+s`, `0<=s<=1`, compact positivity
of Phi gives a positive lower bound times `exp(u)`, so its double absolute
integral diverges. This is a paper diagnostic for that exchange, not a
no-go for the compensated complete operator. No positive factorization or
bound for the required signed energy was obtained from this attempt.
**Whole route:** S1 enables the exact ground-state calculation; commuting
uncompensated pieces would erase an uncontrolled boundary term and cannot
supply the missing sign.

These are bridge obligations, not an advance of the sign inequality or a
literature-priority claim. No git command, numerical mathematical experiment,
or proof-limit override. RH remains unresolved; this card remains in progress.

## Next mathematical obligation

### S2: sharp comparison audit — no sign bound established

For the literal even positive Phi, put

`A = integral_R cosh(x/2)*Phi(x) dx`,
`dmu(x) = cosh(x/2)*Phi(x) dx / A`, `tau(x)=tanh(x/2)`.

The polar jump energy has the exact paper identity

`E_pole(f) = 2*A^2 * (Var_mu(f) + |integral tau*f dmu|^2)`.

Here `Var_mu(f)=integral |f|^2 dmu-|integral f dmu|^2` for complex f.
Proof: replace `(x,u>0)` by `(x,y>x)`, then symmetrize to obtain
`integral_R^2 cosh((y-x)/2)*Phi(x)*Phi(y)*|f(y)-f(x)|^2`.
Expand the square and use
`cosh((y-x)/2)=cosh(x/2)*cosh(y/2)-sinh(x/2)*sinh(y/2)`.
Evenness gives `integral sinh(x/2)*Phi(x) dx=0`. The two diagonal terms
sum to `2*A*integral cosh(x/2)*Phi(x)*|f(x)|^2 dx`; the cross term is
`-2*|integral cosh(x/2)*Phi(x)*f(x) dx|^2`
`+2*|integral sinh(x/2)*Phi(x)*f(x) dx|^2`.
All exchanges are absolutely admitted for bounded f by the existing
half-exponential source moments. A is finite and strictly positive.
This calculation is not yet formalized and carries no novelty claim.

Consequently the proposed sign attack requires the positive Gamma-plus-prime
jump energy to dominate both the variance and the displayed odd moment,
with the exact coefficient `2*A^2`. A scalar variance estimate alone omits
a positive term. **Whole route:** this fixes the comparison target; it does
not provide the comparison or advance its sign.

Proof attempts audited against this target:

- **Weighted gap:** retrieved graph-gap and ground-state results do not supply
  the exact bound for this source and these jump weights. No estimate was
  derived. The additional odd moment remains explicit. **Whole route:**
  generic gap existence cannot discharge the required inequality.
- **First contact:** the actual CCM first-contact and translation-saturation
  laws permit an aperture-filling null state. The pole-source positivity
  lemma inspected assumes positive ground energy. No contradiction at contact
  was derived. **Whole route:** these existing laws do not exclude the failure
  alternative; another restatement would not advance RH.
- **Arithmetic square factorization:** the literal finite-prime divisor
  regrouping retains archimedean flux minus prime flux. Expanding the source
  into translated seeds supplies no nonnegative coefficient representation
  of their difference. No sum-of-squares formula was obtained. **Whole route:**
  the exact arithmetic weights are retained, but their compensation remains
  the same open sign problem. This is a failed proof attempt, not a theorem
  that every such factorization is impossible.

Deep/method retrievals: `/tmp/rh-s2-ground-gap-search.json`,
`/tmp/rh-s2-markov-search.json`, `/tmp/rh-s2-theta-factor-search.json`,
`/tmp/rh-s2-compensation-sharp-search.json`,
`/tmp/rh-s2-divisor-square-search.json`. Each completed against its available
index; incomplete compiler/method enrichment prevents treating that as an
exhaustive mathematical absence result. Generated ingredient groups were
not proofs. No new Lean theorem, numerical experiment, or sign conclusion
is claimed for S2. No route is retired by these attempts.

### S3: parity, ground selection, and commutator attacks

The even-test restriction removes F100's odd moment, but folding the jump
kernel adds its values at `|x-y|` and `x+y`; it does not remove its negative
continuous part. No sharp variance comparison was derived on this sector.
**Whole route:** parity alone supplies no sign producer.

The ground-state attempt requires more than S1. The precise
[Connes–van Suijlekom Theorem 6.1](https://arxiv.org/html/2511.23257v1)
requires a lower-bounded essentially selfadjoint operator, a simple isolated
lowest eigenvalue, and an even eigenfunction on a finite interval. S1 proves
none of those ground-selection properties for Phi. The corpus ground-selection
lemmas inspected likewise retain a gap hypothesis. No Perron or convergence
argument discharged it. **Whole route:** applying the real-zero theorem here
would import the missing selection premise.

A domain-free finite-packet calculation diagnoses the proposed commutator
factorization. With real shifts `a_j`, complex `c_j`, and
`F(x)=sum c_j Phi(x+a_j)`, `H(x)=sum a_j*c_j Phi(x+a_j)`, put
`Q=integral (|2*x*F(x)+H(x)|^2-|H(x)|^2) dx`.
Expansion and the substitution `y=x+(a_j+a_k)/2` give

`Q=sum_jk conj(c_j)*c_k * C(a_j-a_k)`,
`C(d)=4*integral y^2*Phi(y+d/2)*Phi(y-d/2) dy`.

The discarded linear term is odd in y; every integral is admitted by the
source's Schwartz bounds. In the convention `hat Phi(t)=integral exp(-itx)Phi(x)dx
=Xi(t)`, let `P(t)=sum c_j exp(i*a_j*t)`. Then `hat H=-i*Xi*P'` and
`hat(2*x*F+H)=i*(2*Xi'*P+Xi*P')`. Plancherel and one integration by parts yield

`Q=(1/pi)*integral (Xi'(t)^2-Xi(t)*Xi''(t))*|P(t)|^2 dt`.

This is paper algebra, not a formalized theorem or a domain assertion about
composing the one-sided source operators. It produces no nonnegative square
decomposition: a difference of two squared norms remains. Its prospective
sign is the existing first-Laguerre problem (frontier route LA), not a new
arithmetic bound. **Whole route:** reject this as a shortcut; even a proof of
the first Laguerre inequality alone would not complete RH.

Four deep/method searches completed against the available index:
`/tmp/rh-s3-{even-gap,ground-rank,levy-reflection,laguerre-commutator}-search.json`.
Returned conditional Laguerre theorems retain RH or Laguerre–Polya premises.
No unconditional source sign, counterexample to RH, or new Lean theorem was
obtained. These failures do not retire the full source-sign route.

Prove or falsify the simultaneous signed jump-energy inequality stated above
for every smooth compactly supported complex f, keeping all prime and pole
terms. First write its exact ground-state algebra using S1; do not claim that
annihilating a positive source proves positivity of a signed operator. The
proof attempt must then discharge the sign itself. Another equivalent
criterion, domain-only result, comparison no-go, or generic receiver does not
count as resolution of this obligation.

### S4: real-zero removal and sharp comparison — no sign advance

The attempted induction was to remove real zeros of the actual transform
while preserving a positive decreasing physical source. For an even smooth
rapidly decreasing source Phi and a real Fourier zero gamma > 0, the candidate
is

`Psi_gamma(x) = gamma * integral_x^infinity sin(gamma*(y-x))*Phi(y) dy`.

Paper calculation: `Psi_gamma'' + gamma^2*Psi_gamma = gamma^2*Phi`.
Evenness and the zero equation make Psi_gamma even. Its transform is
`hat Phi(t)/(1-t^2/gamma^2)`, with removable singularities at the removed
zeros. On the positive half-line, integration by parts gives

`Psi_gamma(x) = integral_x^infinity (1-cos(gamma*(y-x)))*(-Phi'(y)) dy`.

Thus a decreasing source gives a nonnegative source after one removal.
This is a paper calculation, not a new formal theorem or a proof of the
iteration needed for the actual theta source.

The attempted inheritance of decreasingness fails already for an elementary
even decreasing source: take
`Phi(x)=1_(|x|<1)+epsilon*1_(|x|<3)`, with `0<epsilon<1`.
Its Fourier transform is
`2*sin(t)/t * (1+3*epsilon-4*epsilon*sin(t)^2)`.
The parenthesized factor is at least `1-epsilon>0`, so pi is the first
positive real zero. For `1<x<3`, its source after removal is
`epsilon*(1-cos(pi*(3-x)))`; its derivative at `x=3/2` is `epsilon*pi>0`.
This counterexample concerns the proposed general induction step, not the
actual theta source. Its nonnegative one-step formula is the positive
survivor, stated above; it has not been promoted or formalized as an RH
advance. No actual-source deflation route is declared closed.

**Whole route:** neither one-step positivity nor the existence of real zeros
supplies the shape invariant, iteration, and residual-factor control needed
to exclude off-line zeros. Those conditions were not proved for Phi.

The second attack tried to obtain the S2 sharp variance comparison by
isolating the polar channels and using a Schur complement. The inspected
`CCMRestrictedWeilActualBirmanSchwinger` keeps the signed prime--polar forcing;
`CCMRestrictedWeilActualHeadPrimePolarGammaProducer` identifies its producer
with the source quadratic and retains nonnegativity as an obligation.
`SelbergThetaSourceVariance` proves a positive variance for actual divisor
modes but asserts no native spectral occurrence. None supplied, and this
attempt did not derive, the missing comparison. **Whole route:** replacing
the form by one of these identities leaves its unrestricted sign open.

Search evidence: `/tmp/rh-s4-theta-kernel-search.json` reports partial results;
`/tmp/rh-s4-real-deflation-search.json`,
`/tmp/rh-s4-real-zero-division-search.json`, and
`/tmp/rh-s4-polar-schur-search.json` completed against the available index.
Method retrieval returned no verified sign producer. Compiler coverage is
predominantly pending/source-only/stale. No numerical mathematical experiment,
Lean theorem, or RH sign advance is claimed for S4.

### S5 target: arithmetic cancellation of the actual transverse current

The current corpus gives, for every actual Xi copy with spectral point
`z=b+i*c`, a nonvanishing two-ended mode `u` satisfying
`u'=-i*z*u-i*Phi`. With `r=u/Phi`, the existing exact identity is

`integral (log Phi)'*|u|^2/Phi = 2*c*V`, with `V>0`.

The target of this attack is to prove the left side zero from the literal
arithmetic source equation, keeping the selected copy fixed. That would
force `c=0`; merely exchanging it with its reflected copy would not.
This is an attack on the existing RH obstruction, not a newly asserted
theorem or a new primary conjecture. The tested proof must use the actual
prime coefficients in a step that establishes cancellation or a sign.

The source energy estimate `m/b^2<M<2*m/b^2` and the pointwise disk
`|1+b*r(x)|<1` are already formalized in `SelbergThetaSourceEnergy`.
They concern one mode, retain the transverse parameter in their weight,
and supply no integer free-orbit upper bound. Repackaging the number two
as a counting bound without a proved pairwise comparison is inadmissible.
