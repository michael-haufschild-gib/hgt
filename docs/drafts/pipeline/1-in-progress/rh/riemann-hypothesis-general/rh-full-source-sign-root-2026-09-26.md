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

### S5 attacks and exact remaining gaps

**Current cancellation.** Substituting the literal S1 source equation into
the current leaves signed prime, Gamma, and pole terms. No cancellation for
the selected copy was derived. Reflection exchanges the two copies and their
currents; cancelling their sum does not cancel either current.

**Full-kernel falsification attempt.** The proposed test uses several actual
charged nodes `z_k(eps)=log(eps+2*i*k)/2`, with fixed positive integers k.
The endpoint layer `s=O(eps)` alone is not an admitted approximation to the
whole horizontal integral: the ray meets further charged phases. No estimate
making the omitted ray negligible was proved. In particular the existing
compact `O(N^9)` energy bound does not justify an `N^8` endpoint model.

For the full degree-four source channel put `t=exp(2s)`. Its product has
frequency `k*n^2-l*m^2`, damping `pi*eps*(n^2+m^2)*t`, and weight `t^(7/2)`
times the kernel's logarithmic factor. When `k=d*a^2`, `l=d*b^2`, and
`g=gcd(a,b)`, the exact resonant indices are `n=(b/g)*j`, `m=(a/g)*j`.
Their polynomial and damping factors are respectively

`a^4*b^4*j^8/g^8`, and `(a^2+b^2)*j^2/g^2`.

This suggests, but does NOT prove, a full-ray leading scale
`eps^(-9/2)*log(1/eps)^2`. Up to positive diagonal congruence and a common
positive scalar, the suggested leading matrix has squarefree blocks

`M(a,b)=gcd(a,b)*a^4*b^4/(a^2+b^2)^(9/2)`.

The sign test for this proposed matrix is positive, not negative. Indeed
`gcd(a,b)=sum_(r|a,r|b) totient(r)` and
`(a^2+b^2)^(-9/2)=1/Gamma(9/2)*integral_0^infinity
u^(7/2)*exp(-a^2*u)*exp(-b^2*u) du` give a positive Gram representation.
For a finite set of distinct positive a, the r=1 term is strictly positive
on every nonzero coefficient vector: a finite sum of exponentials with
distinct exponents cannot vanish identically, as successive multiplication
by the slowest exponential and passage to infinity proves.

**Unproved analytic obligations:** the Gaussian-sum asymptotic under the
unbounded t integral, the off-resonant error, and the lower-degree source
channels. No asymptotic theorem about the actual kernel is claimed. The
positive candidate matrix gives no support for this fixed-family negative
witness. It gives no bound uniform in rank and no RH sign theorem either.
Do not spend a formalization pass on that fixed-family model as a substitute
for the full sign problem.

**Reflected-mode energy attack.** A direct paper calculation supplies the
mixed identity and exposes the missing orthogonality. Let z,w be actual
spectral zero points, `u_z'=-i*z*u_z-i*Phi`, `Q=Phi'/Phi`, and
`m=integral Phi`. Put

`G(z,w)=integral u_z*conj(u_w)/Phi`,
`V(z,w)=G(z,w)-m/(z*conj(w))`.

The source-ratio bounds give absolute convergence and zero endpoint values
for `u_z*conj(u_w)/Phi`; the existing source and current envelopes admit its
derivative. Integrating the mode equation gives `integral u_z=-m/z`.
Differentiating the product and integrating therefore gives exactly

`integral Q*u_z*conj(u_w)/Phi = i*(conj(w)-z)*V(z,w)`.

Here V is the Gram matrix of the centered ratios `u_z/Phi+1/z` for the
positive measure `Phi(x) dx`. For w=conj(z), the mixed current is zero.
The diagonal currents are `2*Im(z)*V(z,z)` and their reflected opposites.
The mixed zero concerns multiplication by Q, which changes sign; it is NOT
orthogonality in the positive source measure. Thus the existing individual
energy upper bounds below two do not combine into a Bessel/counting
contradiction by this calculation. This is paper algebra, not a new Lean
theorem, and no claim that actual off-axis modes exist is made.

**Whole-route decision:** both attacks leave the same sharp sign obligation
open. No full-kernel negative packet, current cancellation, uniform integer
bound, or unconditional RH theorem was obtained. The next proof attempt must
control the simultaneous prime--Gamma--pole form itself, or derive a joint
mode bound that retains the mixed terms. Another symmetry cancellation or
fixed-rank cusp estimate does not meet that requirement.

### S5 direct arithmetic action: the retained zero-mode residue

Let A+ be the literal right-shift operator in S1: the constant term,
paired Gamma integral, both polar integrals, and full prime sum. Let
`A- = R A+ R`, where `(Rf)(x)=f(-x)`. Thus `A+ Phi=x*Phi` and
`A- Phi=-x*Phi`. Keep the Gamma numerator paired at u=0.

Write the actual Volterra modes, before imposing a zero, as

`U+(z,x)= i*integral_(t>0) exp(i*z*t)*Phi(x+t) dt`,
`U-(z,x)=-i*integral_(t<0) exp(i*z*t)*Phi(x+t) dt`.

Here U+ is the anti-causal mode; U- is causal. For `|Im z|<1`, their
existing exact difference is

`U- - U+ = -i*exp(-i*z*x)*Xi(z)`.

The paper calculation of the arithmetic action is

`A+ U+ = x*U+ - i*partial_z U+`,
`A- U- = -x*U- + i*partial_z U-`.

The exchanges use the actual source, not an assumed operator domain:
for fixed x the existing exponential envelopes for the source and its first
derivative bound their values on `x+t+u`, t,u>=0, by
`C_x*exp(-(t+u))`.
For the paired Gamma term on 0<u<=1, split its numerator into
`(exp(-2u)-exp(-u/2))*Phi(x+t)` and
`exp(-u/2)*(Phi(x+t)-Phi(x+t+u))`; both contain a factor u, cancelling
the denominator. This gives an integrable `C*exp(-(1-|Im z|)*t)`
majorant. For u>=1 the Gamma denominator stays away from zero and
the polar weight is at most `2*exp(u/2)`. Prime terms are dominated
by `C*exp(-(1-|Im z|)*t)*Lambda(n)*n^(-3/2)`, summable for n>=2.
Reflection gives the left-shift exchanges. An extra factor t admits
the displayed spectral derivatives. These are paper admission estimates;
they have not been translated into Lean.

Adding the two actions and differentiating the exact Volterra difference
cancels both x terms, leaving

`A+ U+ + A- U- = exp(-i*z*x)*Xi'(z)`.

At an actual zero the two modes coincide, so with `L=A++A-`:

`L u_z = exp(-i*z*x)*Xi'(z)`.

Source annihilation therefore leaves a spectral derivative residue on a
zero mode. Setting that action to zero would additionally require Xi'(z)=0;
at a simple zero its action is nonzero. For a nonreal zero, the mode equation also gives
`integral exp(i*w*x)*u_z(x) dx=Xi(w)/(w-z)` for w!=z in the admitted
strip. Taking w=conj(z) shows `integral conj(u_z)*L u_z=0`.
That zero quadratic value is compatible with an indefinite form; no
positivity may be inferred from it. Multiple zeros require higher jets,
since Xi'(z) can vanish. No simplicity assumption is introduced.

**Whole route:** an exact arithmetic residue has been identified on paper,
but it does not control the form's sign. The open task is still to show the
full prime--Gamma--pole form nonnegative on all admitted packets (or produce
a negative packet unconditionally). Do not promote this identity to an RH
proof, an RH sign advance, or a new priority claim. The targeted deep search
`/tmp/rh-s5-mode-residue-search.json` completed but supplied no checked exact
match; most compiler metadata remains pending/source-only/stale.

### S6: test the bare-atom falsifier after exact arithmetic inversion

The preceding turn changed the next attack through its paper residue
identity, but made no verified RH sign advance. The positive ordinary
differential operator built from Phi leaves the complex spectral term in
the Volterra pencil. STATUS's explicit order-one, strongly log-concave
Riccati countermodels also rule out using those scalar curvature laws as
zero selectors. No curvature-only proof is being pursued.

The concrete falsification attempt is instead to isolate the first source
atom using the actual arithmetic coefficients and retain its entire energy
correction. Write `psi(x)=thetaCuspSourceTerm x 1` and
`Ppsi(x)=sum_(n>=2) Lambda(n)/sqrt(n)*psi(x+log n)`. Exact divisor regrouping
gives the paper identities

`sum_(n>=1) mu(n)/sqrt(n)*Phi(x+log n)=psi(x)`,
`sum_(n>=1) mu(n)*log(n)/sqrt(n)*Phi(x+log n)=-Ppsi(x)`.

The second equality uses `sum_(d|n) mu(d)*log(d)=-Lambda(n)`, not a
termwise deletion of the logarithmic channel. For each fixed x, the
Gaussian atom bounds admit both double series absolutely. They also give
convergence in the two weighted L2 channels on s>0: the n-th translated
channel is bounded by a polynomial in n and log n times `exp(-c_x*n^2)`.
The corresponding statement for the differentiated theta-tail density
already exists in `XiCTaylorThetaTailMobiusConstraint`; no novelty is
claimed for ordinary Mobius inversion.

For the actual finite packet with nodes `x+log n` and coefficients
`mu(n)/sqrt(n)`, its K quadratic value therefore tends, on paper, to

`D(x)=2*integral_x^infinity [y*psi(y)^2-psi(y)*Ppsi(y)] dy`.

This is the full arithmetic correction to the bare-atom negative diagonal.
Replacing D by `integral 2*y*psi(y)^2` drops a channel from the actual
packet. There is no justified negative witness from the bare atom alone.
No interchange of this fixed-x limit with x->-infinity has been assumed.

The corrected expression itself has a full-line limit. With
`C(a)=integral psi(y)*psi(y+log a) dy`, the existing exact Wigner pair
formula specializes, by the change of variable v=exp(2y), to

`C(a)=(3/2)*a^(5/2)*(-6*a^4+23*a^2-6)/(1+a^2)^(9/2)` (a>0).

For integer n>=2 this is strictly negative: writing r=n^2>=4, the
numerator polynomial is `-6*(r-4)^2-25*(r-4)-10`.
Absolute correlations are O(n^(-5/2)); multiplying by
`Lambda(n)/sqrt(n)` gives an absolutely summable majorant. Thus

`D(-infinity)= [33/(32*sqrt(2))]*(8/3-gamma-log(8*pi))`
`  +3*sum_(n>=2) Lambda(n)*n^2*(6*n^4-23*n^2+6)/(1+n^2)^(9/2)`.

The first term is the negative bare-atom center moment, while every
displayed prime correction is positive. This calculation does not compare
their sizes and is not a claim that D(x) is nonnegative.

The correlation sign was independently checked in Lean scratch:
`/tmp/rh-s6-prime-correction-sign.lean`, theorem
`RHTower.RootS6Audit.first_atom_integer_cross_neg`, exit 0. It states
`integral thetaCuspSourceTerm(x,1)*thetaCuspSourceTerm(x,n)<0` for every
n>=2; the positive half-density scaling gives the same sign for C(n).
Proof uses the existing exact pair formula and
`cosh(log n)>=(5/4)`, not a numerical experiment. Axiom audit reports only
`propext`, `Classical.choice`, `Quot.sound`. No limit was raised.

**Sector test for this particular full-line probe.** The first atom has
Fourier--Laplace transform

`A(z)=-(z^2+1/4)/2 * pi^(-1/4-i*z/2)*Gamma(1/4+i*z/2)`.

Put `G(z)=A(z)*A(-z)`. A paper Euler-product argument gives
`Re G(z)>0` throughout `|Im z|<1/2`. For z=b+ic with b,c>0 and c<1/2,
set `a_n=2*n+1/2` and

`delta_n=arg(z^2+a_n^2)=integral_(a_n-c)^(a_n+c) b/(t^2+b^2) dt`.

The intervals for n>=1 are disjoint and contained in `(a_1-c,infinity)`.
Consequently `sum_(n>=1) delta_n < pi/2`, while `0<delta_0<pi/2`.
Euler's Gamma limit, with the n=0 denominator cancelled, gives G as the
limit of positive real constants times
`(z^2+a_0^2)/product_(n=1..N)(z^2+a_n^2)`.
Their arguments are `delta_0-sum_(n=1..N)delta_n`, uniformly inside
`(-pi/2,pi/2)` at each fixed z. The limit is nonzero because both Gamma
arguments have positive real part and `z^2+1/4!=0` in the open strip.
The axes are positive directly; conjugation and evenness give the other
quadrants. This establishes the stated sector law on paper without RH.

**Admission still to audit:** identifying the literal D(-infinity) with
the full divisor sum of G, including the source-form normalization and the
extension from compact tests to psi. The inspected Guinand--Weil leaf is
for a resolvent test algebra; its name is not evidence of that extension.
The spectral sector law alone does not certify the arithmetic inequality.
If that extension is discharged, this one full-line probe is positive
regardless of off-line zeros, so it cannot be the sought falsifier. Finite
tail values and mixed packets remain separate sign questions.

A more applicable unconditional compact-test identity was subsequently
located: `ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution`
and `suzukiWeilDistribution_hermitianConvolution`. The proposed admission
proof takes smooth cutoffs `psi_R=chi(x/R)*psi`, chi=1 near zero and
0<=chi<=1. The exact Gaussian formula gives convergence in H1 and in both
half-exponential L1 norms. This handles the logarithmic Gamma multiplier
and polar pairings. The absolute atom-correlation O(n^(-5/2)) envelope
dominates all cutoff prime terms after weighting by Lambda(n)/sqrt(n).
Twice integrating by parts gives uniform Fourier bounds
`|hat psi_R(z)|<=C/(1+|Re z|^2)` on `|Im z|<=1/2`; the existing
inverse-square summability of the Xi divisor then dominates the zero sums.
The remaining normalization check is the first atom's archimedean-only
source equation `G+psi=x*psi` (its Laplace transform is the displayed
Gamma factor without zeta). None of this cutoff admission or Gamma-sector
argument has been Lean-checked; retain this as the next concrete proof
obligation before calling the proposed full-line falsifier refuted.

**Whole route:** exact prime correction is now explicit for a concrete
attempted negative packet. No negative full-source packet or uniform
positive form has been obtained. Paper identities and sector law are not
Lean theorems; the route remains active, and the RH objective is unchanged.

## S7: mixed packets and admission of the attempted falsifier

For real logarithmic displacement t, differentiating the existing exact
pair Mellin formula gives the paper expressions

`C(t)=3/(32*sqrt(2))*(35*cosh(t)^(-9/2)-24*cosh(t)^(-5/2))`,
`J(t)=C(t)*(8/3-gamma-log(8*pi)-log(cosh(t)))`
`     -9/(4*sqrt(2))*sinh(t)^2/cosh(t)^(9/2)`,
`R(t)=J(t)-sum_(n>=2) Lambda(n)/sqrt(n)*(C(t+log(n))+C(t-log(n)))`.

Here J is the integral of `(2*x+t)*psi(x)*psi(x+t)`. The two-node
full-line mixed packet asks for `abs(R(t))<=R(0)`. No such uniform
bound or negative witness has been obtained; coarse absolute prime
bounds leave the same exponential scale as the existing route obstacle.
This is not a new criterion claimed as RH progress.

Current concrete obligation: check the S6 Gamma-sector argument in Lean
before using it to exclude the single-packet witness. Its finite angle
sum can be bounded by telescoping arctans because the intervals
`[2*n+1/2-c,2*n+1/2+c]` are disjoint for `abs(c)<1/2`.
Full source-form admission remains separate. A sector theorem alone
does not establish the mixed sign or the RH objective.

**S7 result:** the exact Gamma-sector law is now formalized in
`ThetaCuspAtomGammaSector.lean`. Its public statements are
`RHTower.thetaCuspAtomGammaCore_re_pos` and
`RHTower.thetaCuspAtomGammaPair_re_pos`. The proof uses the closed bound
`norm(H_N)*cos(M)<=Re(H_N)` for Euler's finite Gamma products, with
`M=atan(b/(1/2-c))<pi/2`, before passing to the nonzero Gamma limit.
Axes and both other sign choices are included by conjugation and evenness.
Scratch and named leaf build pass at default limits; the leaf is wired.
The dependency-closed proof is recorded in
`../../../3-formalized/rh-first-atom-gamma-sector-root-2026-09-26.md`.

**Whole route:** the spectral component of the attempted single-packet
falsifier has been settled. Noncompact source/Weil admission is still
needed to certify that packet's arithmetic sign; mixed-packet positivity
and RH remain open. This is component progress, not an RH sign advance.

Final S7 verification: named leaf build exits 0; all three public
declarations have only `propext`, `Classical.choice`, `Quot.sound`;
`scripts/formal_tools.py lint` exits 0. No heartbeat/recursion override,
numerical mathematical experiment, or git command was used. All owned
Lean/search processes have exited. Logs are
`/tmp/rh-s7-gamma-sector-build.log`, `/tmp/rh-s7-final-axioms.log`,
and `/tmp/rh-s7-lint.log`.

## S8: exact main-term cancellation in the mixed packet

The fixed target remains the full mixed-packet sign. The source equation
still gives no sharp jump comparison. Grouping Wigner atom pairs before
the full-line integral also requires new convergence evidence: reflection
makes every finite translated complete-source center pairing zero, so a
nonzero Mobius limit must retain the escaping boundary current. The
existing `ThetaCuspCenterCurrentReflection` already proves the underlying
reflection identity; no novelty is claimed for it.

Current derived calculation to verify: write `f(t)=cosh(t)^(-5/2)` and
`c=3/(8*sqrt(2))`. The existing Helmholtz formula gives
`C=c*(1/4-D^2)f`. The proposed exact continuous-prime cancellation is

`integral_(v>0) exp(v/2)*(C(t+v)+C(t-v)) dv = -c*f(t)`.

Thus, with `E(v)=psi_Chebyshev(exp v)-exp v`, the actual mixed kernel is

`R(t)=J(t)+c*f(t)`
`  - integral_(v>0) exp(-v/2)*(C(t+v)+C(t-v)) dE(v)`.

This is a derived identity candidate, not a new primary conjecture or
a sign proof. Its purpose is to remove the prime main term exactly before
testing the remaining signed arithmetic correlation. No bound for that
correlation has been established.


**S8 checked component.** The exact continuous-prime cancellation now passes
Lean in `/tmp/rh-s8-mainterm.lean` (exit 0, standard axioms only), including
its identification with the existing `thetaCuspWignerPairKernel (1/2)`.
The production source `ThetaCuspWignerPrimeMainTerm.lean` also passes direct
Lean checking. Named build and final public-axiom/lint audits are pending.
The public theorem is
`RHTower.thetaCuspWignerPairKernel_continuousPrimeMainTerm`.

**Proof.** Put `f(t)=cosh(t)^(-5/2)`, `d=f'`,
`k=35/4*cosh(t)^(-9/2)-6*f=(1/4-D^2)f`.
For `B(t,v)=exp(v/2)*(d(t+v)-f(t+v)/2)`, direct differentiation gives
`partial_v B=-exp(v/2)*k(t+v)`. The bounds
`0<f(x)<=4*exp(-2*x)`, `abs(d(x))<=5/2*f(x)` and
`abs(k(x))<=15*f(x)` imply absolute integrability and `B(t,v)->0`.
The positive displacement integral is `d(t)-f(t)/2`; evenness of k and
oddness of d give `-d(t)-f(t)/2` for the negative displacement. Their sum
is `-f(t)`. The existing Helmholtz theorem identifies the literal kernel
as `c*k`, with `c=(2*pi)^(-1/2)*Gamma(5/2)/2`. All these analytic
obligations are in the checked proof; no improper integral is silently
assigned a value without convergence.

**Attack after the identity.** Estimating the signed prime remainder by
its absolute size does not produce a uniform displacement bound: the
moving factor `exp(-v/2)` leaves the half-exponential scale near `v=t`.
Combining the prime and terminal transport vectors before taking their
norm was also tested against the corpus. The existing
`CCMActualHeadCoherentQuantileGammaProducer` already does exactly this,
and `CCMActualHeadCoherentQuantileGammaPhaseSquare` retains the cross
phase. Their missing lower bound is still the full source sign. This
rephrasing is not new knowledge and supplies no new inequality.

**Whole-route gate.** The continuous-prime part is now eliminated exactly,
without an absolute-value loss. The Stieltjes remainder identity above
remains a paper derivation; it is not proved by the new leaf. No bound on
that remainder, mixed-packet positivity, negative full-source witness,
or RH conclusion has been obtained. Do not replace the frozen source
sign target by more kernel identities. The remaining task is an actual
signed arithmetic inequality or an actual negative packet.


**Second factorization attempt (paper diagnostic, no theorem promoted).**
For a sufficiently regular decaying primitive h with
`Phi=(D^2-1/4)h`, applying this differential operator in both variables
to `K_h` leaves the endpoint correction
`K_Phi=L_x L_y K_h + 2*h'(x)*h'(y) - h(x)*h(y)/2`.
The product rule gives this from the derivative of
`h'(x+s)*h'(y+s)-h(x+s)*h(y+s)/4`. Thus a positive primitive kernel
would not by itself supply the desired positive congruence. Neither
positivity of the actual primitive kernel nor control of its negative
rank-one endpoint term has been proved. No new positivity claim or
formal no-go is inferred from this conditional calculation.

**Final S8 verification.** Named leaf build exits 0. Its sole public
theorem's axiom audit exits 0 with only `propext`, `Classical.choice`,
`Quot.sound`. The leaf is wired once. Global formal lint exits 1 only for
unrelated unwired `CircleSeamModulusMargin` and
`XiZeroFreeDiscSeamModulusMargin`; no own-leaf or stale-index error.
The dependency-closed component proof is recorded in
`../../../3-formalized/rh-wigner-continuous-prime-main-term-root-2026-09-26.md`.
Logs: `/tmp/rh-s8-mainterm-build.log`, `/tmp/rh-s8-final-axioms.log`,
`/tmp/rh-s8-lint.log`. All owned Lean/search processes have exited.
No git, numerical mathematical experiment, or proof-limit override.
The full source sign and RH goal remain open.


## S9: attack the sign after exact main-term removal

The previous turn made component progress: S8 is built and axiom-audited.
It did not improve a source-sign bound. The fixed target remains full K
positivity or a negative actual packet. This turn tests whether the
arithmetic action constrains a hypothetical negative direction, and
whether the zero-mode inhomogeneous derivative equation admits a genuine
selfadjoint compression. These are proof attacks on the existing target,
not new primary conjectures. A universal matrix inequality or a new
receiver would not count as their success. The explicit arithmetic
remainder is kept intact.
