# Signed boundary–arithmetic control of Weil pole forcing

- **Stage:** 1-in-progress
- **Type:** Physical Gamma action, full cancellation, exact parity-ground forcing, separate and joint source nonvanishing, actual ground variance and the unrestricted-gap source bound FORMALIZED; exclusion of the arithmetic zero ground OPEN.
- **Formal cards:** [Scalar integral and actual operator domain](../3-formalized/weil-gamma-polar-jump-boundary-integral.md); [physical action and full cancellation](../3-formalized/weil-gamma-physical-action-and-pole-source-cancellation.md); [ground source moment and nonvanishing](../3-formalized/weil-ground-source-moment-and-nonvanishing.md); [parity kernels and joint moments](../3-formalized/weil-parity-source-kernels-and-joint-moments.md).
- **Corpus sources:** `CCMRestrictedWeilGammaPolarAction`, `CCMRestrictedWeilPolarSourceCancellation`, `CCMRestrictedWeilPrimePolarArithmeticAction`, `CCMRestrictedWeilPolarGroundForcing`, and `CCMRestrictedWeilPolarGroundParityForcing`.

## Full proof chain
Exact prime–Gamma action on the pole profiles → source control of constrained ground forcing → exclusion of the unique possible constrained zero ground → positive floor at every finite aperture → weighted pole exclusion → RH. The first arrow's operator identities are closed. This card retains the missing source inequality; neither the physical formula nor the positive boundary kernel determines its sign on a constrained ground.

## Exact source now available
For `-a<x<a`, write `R=a-x`, `L=a+x`, `p±(x)=exp(±x/2)`,

`B_a(x)=-(1/2)log(1-exp(-2R))-(1/2)log(tanh(L/2))>0`,

`kappa=-EulerGamma-log(2pi)`,

`E_psi(Y)=psi(Y)-Y`, `E_M(t)=sum_{2≤n≤floor(exp t)} Lambda(n)/n-t`.

Every truncated real exponential belongs to the actual unrestricted Weil Friedrichs domain. The normalized compressed Gamma image has the exact almost-everywhere representative

`A_a p+=p+[-(a-x)+kappa+B_a]`.

Complex polarization proves the absolutely integrable mixed Gamma form identity on the entire completed domain. The sharper jump bound `J(R,L,h)≥-1_(0,R](h)` gives `integral |J|≤integral C+R+B(R,L)`. Joint measurability and this bound justify Fubini against every smooth compactly supported strict-interior test. Locally integrable smooth-test separation identifies the existing L² operator representative, with no additional boundary trace or global candidate-integrability premise.

The exact rank-two Gram action is

`polarOp p+=2a p+ + 2sinh(a)p-`.

Together with the literal prime-power action, this gives the actual full operator formula

`H_a p+=p+[kappa+B_a-E_psi(exp(a-x))-E_M(a+x)]-exp(-a)p-`.

The linear ramp, aperture term, and exponential main contribution cancel exactly. For every vector in the completed space with both exponential moments zero,

`<H_a p+,f>=integral p+(x)[B_a(x)-E_psi(exp(a-x))-E_M(a+x)] f(x) dx`.

The integral is over the aperture. It is an actual L² pairing, not a formal interchange. All prime powers remain in the arithmetic errors. The existing bound `|E_M(t)|≤log 4+5` holds for all `t≥0`.

## Live conjecturing obligations
1. Use the ground-specific comparison `4|F_a(u)|²≤(mu-lambda)||J_a u||²[Q(p_r)-2lambda D_r]`, where `D_r=2sinh(a)+2ar>0`, `mu` is the constrained floor and `lambda` the unrestricted floor. All quantities belong to the actual source. Its variance is exactly `2|F_a(u)|²/D_r`; neither positive variance nor this shifted-form bound excludes `mu=0`.
2. Search the corpus for a comparison controlling the combined boundary and arithmetic errors on that same constrained ground. Separate absolute bounds lose their cancellation; positivity of `B_a` cannot by itself sign its pairing with a sign-changing function.
3. Test a source inequality against the possible zero-ground equation. A successful comparison must exclude that equation at the unique possible threshold, rather than assume an RH-equivalent all-aperture sign.
4. If a proposed comparison fails, extract its sharp positive survivor before abandoning it. The prior absolute-jump bound and complete mixed-form identity are examples of such proved survivors.

## Closed obligations
Scalar Gamma integral and normalization; squared exact-weight Fourier energy; actual unrestricted operator-domain membership; joint physical test integrability and Fubini; smooth-test identification of the normalized Gamma image; exact pole Gram action; full source cancellation; completed constraint pairing; exact source determination of the parity-ground forcing scalar; actual parity kernels and half-integral normalization; separate source surjectivity in each parity; joint independence of the original and reflected source moments; normalized actual parity grounds; exact residual and operator-norm variance; full shifted-form Cauchy–Schwarz and the source-gap bound; its literal integral version; zero-source eigenstate classification and strict-gap consequence of nonzero coupling.

No numerical computation, unproved interchange, extra axiom, or RH premise supplies these identities. The signed source inequality remains open.

## Exact nonzero coupling and bounded boundary asymmetry
`CCMRestrictedWeilPolarSourceNonvanishing` proves that the real boundary–arithmetic profile tends to positive infinity at the right endpoint, with all prime powers retained. Thus the actual defect is outside the entire two-pole span. The exact annihilator theorem and dense physical embedding imply that `F_a` is nonzero on the complete constrained space and takes every complex value there. The actual `H_a p+` is also outside the pole span. Automatic invariance is excluded; a particular ground could still lie in the kernel of `F_a`, and a nonzero source moment could still satisfy its forced equation.

The exact boundary decomposition is

`B(R,L)=-[log(1-exp(-2R))+log(1-exp(-2L))]/2+log(1+exp(-L))`.

The divergent part is reflection-symmetric. Its asymmetry is exactly `log(1+exp(-L))-log(1+exp(-R))`, of absolute size less than `log 2`. This exposes an explicit bounded term for parity comparisons while retaining both endpoint singularities.

## Exact parity kernels and separate nonvanishing
The two actual parity profiles are `K_(a,r)(x)=K_a(x)+r K_a(-x)`, `r=±1`. Write `A_a(x)=E_psi(exp(a-x))+E_M(a+x)` and `Delta_a(x)=B(a-x,a+x)-B(a+x,a-x)`. Then

`K_(a,r)=[exp(x/2)+r exp(-x/2)]B(a-x,a+x)-T_(a,r)`,

`T_(a,r)=exp(x/2)A_a(x)+r exp(-x/2)[A_a(-x)+Delta_a(x)]`.

The arithmetic bound `|A_a|≤C_a=psi(exp(2a))+exp(2a)+log 4+5` and `|Delta_a|<log 2` imply `|T_(a,r)|≤exp(a/2)(2C_a+log 2)`. Both endpoint coefficients `exp(a/2)+r exp(-a/2)` are positive. Thus each parity profile diverges at the right endpoint.

`CCMRestrictedWeilPolarParitySourceCoupling` identifies each profile with an actual reflected aperture L² defect and proves

`F_a(u)=(1/2)integral K_(a,r)(x)(J_a u)(x) dx` whenever `R u=r u`.

Each constrained parity sector realizes every complex value of `F_a`; the pair `(F_a(u),F_a(Ru))` is jointly surjective on the complete constrained space. Automatic decoupling cannot be recovered by choosing either parity. This does not restrict the source moment of a selected ground.

The two-ended source rank is now formalized in `CCMPolarSourceEndpointRank`: every nonzero real combination of the two actual parity profiles diverges with one sign at one endpoint. Its right/left singular coefficients are `c(E+F)±d(E−F)`, `E=e^(a/2)>F=e^(−a/2)`. Thus no bounded correction erases both endpoint channels. This sharpens source independence but still gives no sign for the selected constrained ground; see [certificate](../3-formalized/weil-polar-source-endpoint-rank.md).

## Exact pole matrix and integrated prime error
The literal pole energy in the ground bound is now `Q(p_r)=2(A+rC)`, where `A=Q(p_+)` and `C=Re Q(p_+,p_-)`. Both entries retain the full Gamma, rank-two polar, and finite prime-power terms. Arbitrary complex pole combinations diagonalize exactly in the two parity directions; their nonnegativity is equivalent to `|C|≤A`.

The cross entry equals the integrated Chebyshev deficit plus the Gamma boundary mass, scalar radius term, and a reciprocal-Mangoldt correction bounded by `(log 4+5)2a`. This supplies a concrete arithmetic comparison for the ground bound and an exact fixed-exponential RH criterion. Uniform diagonal/boundary estimates and the full primitive-to-resolvent handoff are closed; all-aperture source positivity remains open. See [current candidate](weil-two-pole-compression-prime-error.md) and [formal matrix and integrated-error package](../3-formalized/weil-two-pole-matrix-and-integrated-prime-error.md).

## Next mathematical comparisons
- Control the joint arithmetic quantities in the new actual-ground inequality. At `mu=0`, nonzero forcing requires `lambda<0`; proving that this cannot occur needs more than the nonnegative shifted form. The exact pole energy and source moment must remain coupled.
- Test whether arithmetic information sharpens the two-dimensional comparison. Its generic constant is saturated by the Hermitian swap model: zero constrained energy, nonzero source, unrestricted floor `-1`. This model is formal and is not a counterexample for the arithmetic operator.
- Use the explicit parity integral `I_r=integral K_(a,r)J_a u`, whose bound is `|I_r|²≤(mu-lambda)||J_a u||²[Q(p_r)-2lambda D_r]`. Boundary divergence and a fixed-aperture remainder bound do not select the sign of either spectral floor.

The complete positive survivor and countermodel are recorded in [ground source variance and gap](../3-formalized/weil-ground-source-variance-and-gap.md), with the exact operator, Gram factors, equality cases, and normalized existence theorem in `CCMRestrictedWeilPolarGroundVariance`.
