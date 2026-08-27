# BM third-order Peierls-polarized causal cut

- **ID:** HB-BM3-PPC
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `HB-BM3-PNCC` hostile attack · current Lean causal-cut corpus · Peierls reciprocity
- **Statement:** `[CONJECTURE]` Complete augmented Birmingham--Mokhtari cubic causal cut is a polarized `++/--` Peierls pairing; mixed `+-` self-channel cancels identically.

## Goal

Replace unsupported one-channel optical landing by exact variational channel law. Identify complete
phase-normalized `++-` cut with polarization between conjugate second-harmonic sources. On physical
Schwarz-real slice this pairing may become total horizon-plus-AdS flux; on complex Xi fibres it
remains bilinear and need not have sign.

This does not prove RH. Remaining endpoint requires actual augmented BM action/Green weld and a
source-global law forcing cut vanishing or simultaneous retarded/advanced solvability.

## Gates

- [x] 0 → 1 in-progress: exact claim, closed abstract proof, corpus/literature attack, physical weld isolated
- [ ] 1 → 2 fully-proven: augmented BM action, boundary pairing, Green transpose, and left-QNM identification proved
- [ ] 2 → 3 formalized: physical BM theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: standalone proof, conventions, boundary analysis, Lean certificate, priority audit

## Exact frozen claim

Let `X` be gauge-fixed field space, `Y` complete bulk-plus-horizon-plus-AdS residual space,

\[
P:X\times Y\to\mathbb C,
\qquad B:X\times X\to Y,
\qquad \Delta:Y\to X.
\]

Here `P` is augmented action pairing, `B` second derivative of Euler--Lagrange residual, and
`Delta=R^ret-R^adv` is one global causal propagator whose frequency blocks give corpus `++`, `+-`,
and `--` response jumps. Require

1. Hessian symmetry: `B(x,y)=B(y,x)`;
2. cyclic third variation: `P(x,B(y,z))=P(z,B(x,y))`;
3. Peierls skewness: `P(Delta f,g)=-P(Delta g,f)`.

For linear branches `p,m`, set

\[
f_{++}=\tfrac12B(p,p),\qquad
f_{+-}=\tfrac12(B(p,m)+B(m,p)),\qquad
f_{--}=\tfrac12B(m,m).
\]

Define phase-normalized cubic cut with target leg `m` by

\[
\mathcal C(p,m)=
P\bigl(m,B(p,\Delta f_{+-})\bigr)
+P\bigl(m,B(m,\Delta f_{++})\bigr).
\]

Frozen physical claim is that complete augmented BM retarded-minus-advanced section, including
external conjugate amplitude, is this `C` and hence

\[
\boxed{\mathcal C(p,m)=2P(\Delta f_{++},f_{--})},
\tag{PPC}
\]

with

\[
\mathcal C(m,p)=-\mathcal C(p,m),\qquad \mathcal C(p,p)=0.
\]

For `p_A=A p`, `m_A=conj(A)m`, both sides scale by
`A^2 conj(A)^2=|A|^4`; phase invariance is automatic. No Hermitian norm or one-variable
holomorphic continuation is asserted off physical slice.

## Complete abstract paper proof

`[PROVED HERE]` Hessian symmetry gives `f_+-=B(p,m)=B(m,p)`. Cyclicity gives

\[
P(m,B(p,\Delta f_{+-}))=P(\Delta f_{+-},B(m,p))
=P(\Delta f_{+-},f_{+-}).
\]

Peierls skewness with equal source arguments makes last term equal its negative; characteristic
zero forces it to vanish. Thus mixed response may be nonzero as field, but its contribution to
phase-normalized cubic action coefficient is exactly zero.

For second term, cyclicity gives

\[
P(m,B(m,\Delta f_{++}))
=P(\Delta f_{++},B(m,m))
=2P(\Delta f_{++},f_{--}),
\]

proving `(PPC)`. Swapping `p,m` swaps `f_++` and `f_--`; Peierls skewness changes sign. Setting
`p=m` therefore gives zero. Complex multilinearity gives `A^2 conj(A)^2` under physical amplitude
scaling. No analytic, spectral, or positivity premise enters abstract proof.

## Second-harmonic Schwarz infrastructure

`[PROVED HERE]` The surviving `++/--` carrier requires two independent complex-momentum
fibres. Define the missing minus-minus frequency by

\[
\omega_{--}(n,\chi)=2\omega_-(n,\chi).
\]

Direct substitution into the corpus BM frequencies gives

\[
\omega_{--}(n,\bar\chi)=-\overline{\omega_{++}(n,\chi)}.
\]

Substitution into the BM radial parameters gives the exact Schwarz permutation

\[
A_{--}(\bar\chi)=\overline{B_{++}(\chi)},\qquad
B_{--}(\bar\chi)=\overline{A_{++}(\chi)},\qquad
C_{--}(\bar\chi)=\overline{C_{++}(\chi)}.
\]

Because complex Gamma commutes with conjugation, the chiral Jost factors swap, while their product
is fixed up to conjugation. Shifted hypergeometric parameters swap as well. Therefore complete
pole-cancelled projective boundary response satisfies

\[
\mathcal R_{--}(n,\bar\chi)=\overline{\mathcal R_{++}(n,\chi)}.
\tag{SCHWARZ-2}
\]

Proof uses only definitions, ring normalization, and `Gamma(conj z)=conj(Gamma z)`; it has no
reality, nonvanishing, or spectral premise. This is dependency-closed algebraic infrastructure for
a polarized flux identity. It does not identify response with Peierls boundary flux.

## Polarized radial Green identity

`[PROVED HERE]` Let `a,b,c` be the `++` BM hypergeometric parameters and

\[
L_{++}y=z(1-z)y''+[c-(a+b+1)z]y'-aby.
\]

Corpus definitions give the universal exponent balance `a+b-c+1=1/2`. On `0<z<1`, define

\[
p(z)=e^{c\log z}\sqrt{1-z},\qquad
w(z)=\frac{p(z)}{z(1-z)}.
\]

Then

\[
p'(z)=w(z)[c-(a+b+1)z].
\]

By `(SCHWARZ-2)`, the `--` jet at momentum `bar chi` conjugates exactly to the `++` jet:

\[
\overline{L_{--}v}=L_{++}\bar v.
\]

For forced equations `L_++ y=f` and `L_-- v=g`, differentiate the polarized concomitant

\[
J_{++/--}(z)=p(z)[\bar v(z)y'(z)-\overline{v'(z)}y(z)].
\]

Using the integrating-factor equation in each term cancels the complete `ab` potential and gives

\[
\boxed{J_{++/--}'(z)=w(z)[\bar v(z)f(z)-\bar g(z)y(z)]}.
\tag{GREEN-2}
\]

Thus on every compact `0<a<=b<1`, assuming only differentiability and integrability,

\[
\int_a^b w(z)[\bar v f-\bar g y]dz=J_{++/--}(b)-J_{++/--}(a).
\]

This closes radial formal-transpose reciprocity on independent second-harmonic fibres. It is not
yet the augmented Einstein Peierls identity: horizon/AdS limits, master-field reconstruction,
counterterms, gauge constraints, and retarded/advanced boundary conditions remain outside theorem.

### Literature audit for `(GREEN-2)`

- Birmingham--Mokhtari, arXiv:hep-th/0609028, derives exact topological-black-hole gravitational
  QNM frequencies from the hypergeometric master equation, but does not state this polarized
  nonlinear-source Green identity.
- Kodama--Ishibashi, arXiv:hep-th/0305147, derives gauge-invariant second-order master equation,
  but not BM `++/--` second-harmonic causal block reciprocity.
- Esposito--Marmo--Stornaiolo, arXiv:hep-th/0209147, gives generic Peierls transpose reciprocity for
  symmetric action Hessians. It does not prove singular AdS/horizon endpoint terms required here.

Novelty label remains `[BRIDGE]`: exact specialization appears absent from audited sources, but
mathematical mechanism is classical Lagrange identity.

### Hostile attack of `(GREEN-2)`

- `SURVIVES`: no physical reality assumption on `chi`; `--` lives on independent conjugate fibre.
- `SURVIVES`: no Jost nonvanishing, pole cancellation, QNM residue, or positivity enters identity.
- `SURVIVES`: both forced source terms occur, as required by transpose reciprocity.
- `INCOMPLETE`: complex integrating factor is singular/oscillatory at horizon and may require
  finite-part renormalization; compact-interval identity alone gives no endpoint limit.
- `INCOMPLETE`: hypergeometric master-field pairing is not yet proved equal to full gauge-fixed
  Einstein action pairing after reconstruction, ghosts/constraints, and counterterms.
- `INCOMPLETE`: retarded and advanced boundary conditions are not yet imposed, so boundary
  concomitant is not yet a causal jump or positive total radiation flux.

## Same-branch projective-response no-go

`[PROVED HERE]` Write outer-boundary coefficient vectors as `(S_++,V_++)` and `(S_--,V_--)`,
where `S` is forbidden/source coefficient and `V` is decaying/response coefficient. The endpoint
form of `(GREEN-2)` is the antisymmetric determinant

\[
\mathfrak B=\frac12(\bar V_{--}S_{++}-\bar S_{--}V_{++}).
\]

If `V_++=R_ret S_++` and `V_--=bar(R_adv) S_--`, direct factorization gives

\[
\boxed{\mathfrak B=\frac12\bar S_{--}S_{++}(R_{adv}-R_{ret}).}
\tag{RESP-JUMP}
\]

Therefore using one projective response on both causal legs forces `B=0`. More sharply, the exact
corpus BM connection coefficients obey

\[
S_{--}(\bar\chi)=\bar S_{++}(\chi),\qquad
V_{--}(\bar\chi)=\bar V_{++}(\chi),
\]

so their same-branch polarized boundary concomitant vanishes identically. This rules out the
single pole-cancelled projective ratio as the nonzero Peierls carrier. Positive survivor is exact
`R_adv-R_ret` response jump, with affine horizon/AdS augmentation retained until subtraction.

## Corpus-grounded frontier

- `[LEAN-PROVED]` `ThetaCuspHawkingTotalThirdOrderCausalCut.lean`: exact cut is sum of mixed `+-` and `++` response-jump contributions; direct third jet cancels.
- `[LEAN-PROVED]` `ThetaCuspHawkingTotalThirdOrderCokernelSchurSection.lean`: exact factors `1/2` in `++` and symmetrized `+-` sources match proof above.
- `[LEAN-PROVED]` `ContinuumChronometricGravity.lean`: causal pairing self-contraction vanishes and pairing is skew.
- `[LEAN-PROVED]` `SplitLInfinityObserverExtension.lean`: corpus cyclic action already turns action variation into pairing with nonlinear residual.
- `[LEAN-PROVED]` `FrankensteinCCMGammaWoldCubicSourcePolarization.lean`: nonholomorphic Schwarz specialization must be produced from independent holomorphic fibres, not inserted into one-variable continuation.
- `[LEAN-PROVED, CONDITIONAL LANDING]` `ThetaCuspHawkingBMMixedHorizonCausalOpticalProducer.lean`: assumes mixed contribution carries optical square and `++` jump vanishes; Peierls law reverses this channel attribution if its hypotheses weld to actual augmented action.
- `[LEAN-PROVED NO-GO]` `ThetaCuspHawkingBMMixedOpticalPeierlsNoGo.lean`: off critical, conditional mixed incidence, zero sourced `++` jump, positive reciprocity, and physical Peierls hypotheses are mutually inconsistent.
- `[LEAN-PROVED]` `ThetaCuspHawkingBMTotalRenormalizedAngularPeriod.lean`: total Green-boundary jump is flux, but explicitly does not identify an individual cyclic bulk pairing with Hermitian Gram. This is compatible with polarized `++/--` carrier.
- `[LEAN-PROVED]` `ThetaCuspHawkingBMSecondHarmonicSchwarzPolarization.lean`: independent `--` fibre is the exact Schwarz partner of `++` at conjugate momentum, including frequency, radial parameters, Jost determinant, hypergeometric parameters, and projective response.
- `[LEAN-PROVED]` `ThetaCuspHawkingBMSecondHarmonicPolarizedGreenIdentity.lean`: exact complex integrating factor, Schwarz-adjoint jet law, local polarized source identity, and compact-interval integrated Green identity `(GREEN-2)`.
- `[LEAN-PROVED NO-GO]` `ThetaCuspHawkingBMSecondHarmonicProjectiveCausalNoGo.lean`: same-branch Schwarz connection data have zero outer concomitant; general outer form factors exactly through `R_adv-R_ret`.
- `[LEAN-PROVED NO-GO + SURVIVOR]` `ThetaCuspHawkingBMSecondHarmonicHorizonWronskianMonodromy.lean`: the normalized complementary `++` Wronskian tends to `4n+3+2iχ`; its lateral jump is `exp(-4πχ)-exp(4πχ)` and is nonzero on every Xi fibre, so horizon monodromy is causal normalization rather than a critical-line selector.
- `[LEAN-PROVED INFRASTRUCTURE]` `ThetaCuspHawkingBMSecondHarmonicComplementaryHypergeometric.lean`: exact transformed parameters, nonpositive-integral exclusion, unit convergence radius, horizon value/continuity, and coefficient recurrence for the genuine complementary `₂F₁` factor.
- `[LEAN-PROVED INFRASTRUCTURE]` `ThetaCuspHawkingBMSecondHarmonicHypergeometricFormalODE.lean`: generic Euler-form Gauss residual vanishes coefficientwise and specializes to every BM Xi fibre.
- `[LEAN-PROVED INFRASTRUCTURE]` `ThetaCuspHawkingBMSecondHarmonicHypergeometricAnalyticDerivatives.lean`: first and second complex derivatives exist throughout the open unit disk with exact derivative-series values.
- `[OPEN]` Corpus has no theorem identifying BM Frobenius lateral response maps with blocks of one augmented Peierls propagator, nor proving transpose adjointness including horizon and AdS counterterms.

Mandatory corpus searches found no cubic Peierls polarization theorem specialized to BM data.

## External frontier

- Peierls literature derives antisymmetric causal propagator from advanced/retarded Green maps for Lagrangian gauge theories.
- Covariant phase-space literature warns spatial boundaries contribute additional terms even in general relativity; boundary stationarity is required before Peierls equivalence.
- No audited source proves BM topological-AdS gauge-fixed action cyclicity, augmented Green transpose identity, or cubic polarization `(PPC)` at QNM frequencies.

Abstract identity is a direct new specialization of standard Peierls skewness, labeled `[BRIDGE]`,
not claimed as literature-new theorem. BM boundary/QNM weld remains `[OPEN]`.

## Hostile attack

- `FALSE` if corpus retarded/advanced maps are independent Frobenius lateral choices rather than frequency blocks of one global causal propagator.
- `FALSE` if horizon or normalizable-AdS augmentation breaks variational cyclicity or adds uncancelled corner terms.
- `FALSE` if gauge fixing does not yield a Green-hyperbolic operator on allowed history space.
- `FALSE` if unit-Wronskian left QNM functional is not `y -> P(m,y)` after all boundary normalizations.
- `FALSE` if causal turn-on profiles make two occurrences of nominal mixed source distinct histories, preventing self-pairing cancellation.
- `INCOMPLETE` if proved only for scalar master field without metric reconstruction, constraints, ghosts/Jacobian, and boundary residual.
- `CIRCULAR` if physical conjugacy `m=star p` is imposed at complex Xi momentum rather than obtained by independent Schwarz-fibre specialization.
- Current verdict: `ABSTRACT LAW PROVED`; `PHYSICAL BM WELD OPEN`.

## Proof programme

1. Formalize dependency-closed abstract polarization theorem as positive survivor of PNCC hostile attack.
2. Derive one gauge-fixed augmented BM action including horizon, AdS counterterms, constraints, and corner terms.
3. Prove its second residual derivative is symmetric and third action variation is cyclic on allowed histories.
4. Construct global retarded/advanced Green maps and prove transpose reciprocity under complete augmented pairing.
5. Show frequency-block restrictions equal corpus `RppRet-RppAdv`, `RpmRet-RpmAdv`, and missing `RmmRet-RmmAdv` maps with exact turn-on conventions.
6. Identify unit-Wronskian left target QNM with paired Schwarz leg; audit `N+1` horizon normalization and physical boundary Jost derivative.
7. Only on Schwarz-real slice, evaluate polarized `++/--` pairing as total radiation flux. Continue two independent fibres before Schwarz specialization.
8. Determine whether this flux has critical-line zero locus and find non-circular source-global equality forcing its vanishing.

## No-go closure

- **Exact killing theorem/mechanism:** pending augmented BM weld attack
- **Strongest positive survivor:** dependency-closed abstract Peierls polarization law `(PPC)`
- **New insight:** mixed Frobenius field jump can be nonzero while its cubic action self-contraction vanishes; surviving carrier is polarized second-harmonic channel
- **Status:** `[LEAN-PROVED]` `ThetaCuspHawkingCubicPeierlsPolarization.lean`; physical theorem open

## Log

- 2026-08-27 — created after Peierls hostile attack reversed channel attribution and exposed invalid one-variable norm-square continuation in `HB-BM3-PNCC`.
- 2026-08-27 — formalized corpus-cut bridge, mixed self-channel cancellation, polarized formula,
  branch antisymmetry, diagonal vanishing, and quartic amplitude covariance. Direct Lean and
  targeted module build pass; axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.
  Repository lint reaches unrelated existing `HTGeometry.PositiveContactTropicalization` umbrella
  error; new module is imported by `RHTower.lean`.
- 2026-08-27 — formalized sharp incompatibility with old conditional one-channel optical landing:
  Peierls mixed cancellation plus its zero-`++` hypothesis forces zero total cut, contradicting
  off-critical optical nonvanishing.
- 2026-08-27 — proved `(SCHWARZ-2)` on paper and in Lean. This supplies missing independent-fibre
  algebra for polarized `++/--` channel but leaves augmented Green transpose reciprocity and
  physical boundary-flux identification open.
- 2026-08-27 — proved `(GREEN-2)` on paper and in Lean: exact finite-radius polarized BM Green
  identity on independent second-harmonic fibres. Direct Lean, targeted build, and axiom audit pass.
- 2026-08-27 — retired single-projective-response flux. Exact `++`/Schwarz-`--` connection vectors
  have zero symplectic determinant; nonzero survivor is normalized advanced-minus-retarded response
  difference with augmentation retained.

## Nonresonant second-harmonic horizon normalization

The `++` second-harmonic BM radial equation has complementary Frobenius exponent

\[
\lambda_{++}=1-c(\omega_{++})=4n+3+2i\chi.
\tag{FROB-2}
\]

On the positive radial interval choose the leading complementary branch
`h(z)=exp(lambda * log z)`. With the exact integrating factor from `(GREEN-2)`,

\[
p_{++}(z)=\exp(c(\omega_{++})\log z)\sqrt{1-z},
\]

the exponent balance `c+lambda=1` gives the dependency-closed identity

\[
p_{++}(z)h'(z)=\lambda_{++}\sqrt{1-z}
  \longrightarrow \lambda_{++}\qquad(z\to0^+).
\tag{HORIZON-W}
\]

Counterclockwise and clockwise continuation of `log z` therefore multiply the complementary
branch by

\[
M_+=\exp(2\pi i\lambda_{++})=\exp(-4\pi\chi),\qquad
M_-=\exp(-2\pi i\lambda_{++})=\exp(4\pi\chi).
\tag{MONO-2}
\]

The integer phase `exp(2*pi*i*(4n+3))` is one. Hence the oriented nonresonant horizon jump is

\[
\Delta M_{++}=\exp(-4\pi\chi)-\exp(4\pi\chi).
\tag{JUMP-2}
\]

If this jump vanished, equality of complex norms and injectivity of the real exponential would
give `-4*pi*Re chi = 4*pi*Re chi`, hence `Re chi=0`. Every corpus Xi fibre has `Re chi != 0`, so
`Delta M_++` never vanishes there.

Hostile conclusion: `(JUMP-2)` is not an RH selector; it is universal nonzero causal horizon data.
Together with the zero same-projective AdS determinant, it forces the physical Peierls carrier to
retain augmented horizon/branch information and an independently normalized advanced-minus-retarded
response difference. Strong positive survivor is the exact horizon Wronskian normalization
`(HORIZON-W)` plus the explicit nonzero lateral jump `(JUMP-2)`.

- 2026-08-27 — formalized `(FROB-2)`--`(JUMP-2)` in
  `ThetaCuspHawkingBMSecondHarmonicHorizonWronskianMonodromy.lean`. Direct Lean and targeted build
  pass; axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`. Monodromy-zero endpoint
  retired; normalized lateral jump retained as augmented causal horizon datum.

## Complementary hypergeometric solution infrastructure

The exact second local solution requires more than its leading power. For original `++`
hypergeometric parameters `(a,b,c)`, define transformed complementary parameters

\[
\alpha=a-c+1,
\qquad \beta=b-c+1,
\qquad \gamma=2-c.
\tag{COMP-PARAM}
\]

Direct BM substitution gives

\[
\alpha=2n+\frac74+\frac32 i\chi,
\quad
\beta=2n+\frac74+\frac12 i\chi,
\quad
\gamma=4n+4+2i\chi.
\tag{COMP-EXACT}
\]

If `Re chi != 0`, imaginary parts of these three parameters are respectively
`3 Re chi/2`, `Re chi/2`, and `2 Re chi`; none can be a nonpositive integer. Mathlib's exact
ordinary-hypergeometric radius theorem therefore gives radius one for

\[
{}_2F_1(\alpha,\beta;\gamma;z).
\tag{COMP-RADIUS}
\]

Writing its coefficient as

\[
u_j=\frac{(\alpha)_j(\beta)_j}{j!(\gamma)_j},
\]

the Pochhammer and factorial successor identities give

\[
(j+1)(\gamma+j)u_{j+1}=(\alpha+j)(\beta+j)u_j.
\tag{HG-REC}
\]

`(HG-REC)` is the coefficientwise engine proving that the convergent series solves the BM
hypergeometric ODE on `|z|<1`. This route builds the exact solution; it does not define
retarded/advanced maps by fiat.

For the formal series `F=sum u_j X^j` and Euler operator `theta=X d/dX`, the Gauss equation is
equivalently

\[
\theta^2F+(\gamma-1)\theta F
 -X\bigl(\theta^2F+(\alpha+\beta)\theta F+\alpha\beta F\bigr)=0.
\tag{HG-EULER}
\]

Coefficient zero is immediate at degree zero. At degree `j+1`, left block contributes
`(j+1)(gamma+j)u_(j+1)` and shifted right block contributes
`(alpha+j)(beta+j)u_j`; `(HG-REC)` makes them equal. Thus `(HG-EULER)` is a
dependency-closed formal-power-series theorem. Remaining analytic bridge is termwise
differentiation/evaluation inside radius one, followed by multiplication with `z^lambda`.

For the formal multilinear series `P` defining the same `₂F₁`, Mathlib's convergence theorem gives
`HasFDerivAt P.sum (P.derivSeries.sum z)` whenever `enorm z < P.radius`. Since `(COMP-RADIUS)` gives
`P.radius=1`, this proves the first derivative throughout the open unit disk. The general radius
inequality `P.radius <= P.derivSeries.radius`, followed by continuous-linear evaluation at `1`,
proves the second derivative there as well. This is the exact termwise-differentiation bridge needed
to interpret `(HG-EULER)` analytically; no new regularity premise is introduced.

- 2026-08-27 — formalized `(COMP-PARAM)`--`(HG-EULER)` and the two analytic derivative layers in
  `ThetaCuspHawkingBMSecondHarmonicComplementaryHypergeometric.lean`,
  `ThetaCuspHawkingBMSecondHarmonicHypergeometricFormalODE.lean`, and
  `ThetaCuspHawkingBMSecondHarmonicHypergeometricAnalyticDerivatives.lean`. Direct Lean, targeted
  builds, and axiom audits pass; axioms only `propext`, `Classical.choice`, `Quot.sound`. Remaining
  local theorem is equality of analytic Euler residual with the zero formal residual, then the full
  `z^lambda * ₂F₁` BM jet equation and exact endpoint sewing.

## Analytic Gauss equation from coefficient shifts

Let `d_j=(j+1)u_(j+1)` and `e_j=(j+2)(j+1)u_(j+2)`. Inside the convergence disk, termwise
differentiation supplies convergent sums

\[
 F(z)=\sum_{j\ge0}u_jz^j,
 \qquad F'(z)=\sum_{j\ge0}d_jz^j,
 \qquad F''(z)=\sum_{j\ge0}e_jz^j.
\tag{HG-DERIV-SUMS}
\]

For a coefficient sequence `v`, define `Sv` by `(Sv)_0=0` and `(Sv)_(j+1)=v_j`. Prepending the
zero term and reindexing a convergent series gives

\[
 \sum_{j\ge0}(Sv)_jz^j=z\sum_{j\ge0}v_jz^j,
 \qquad
 \sum_{j\ge0}(S^2v)_jz^j=z^2\sum_{j\ge0}v_jz^j.
\tag{HG-SHIFT}
\]

The coefficient sequence of the standard Gauss residual is therefore

\[
 R_j=(Se)_j-(S^2e)_j+\gamma d_j-(\alpha+\beta+1)(Sd)_j-\alpha\beta u_j.
\tag{HG-RES-COEFF}
\]

At `j=0`, `(HG-REC)` gives `gamma*u_1=alpha*beta*u_0`, hence `R_0=0`. At every positive degree,
expanding the shifts reduces `(HG-RES-COEFF)` exactly to

\[
 R_j=(j+1)(\gamma+j)u_{j+1}-(\alpha+j)(\beta+j)u_j=0
\]

by `(HG-REC)`. Combining `(HG-DERIV-SUMS)` and `(HG-SHIFT)`, then using uniqueness of convergent
sums, proves the dependency-closed analytic equation

\[
 z(1-z)F''(z)+\bigl(\gamma-(\alpha+\beta+1)z\bigr)F'(z)-\alpha\beta F(z)=0,
 \qquad |z|<1.
\tag{HG-ANALYTIC}
\]

The prior derivative theorems identify both derivative-series values in `(HG-ANALYTIC)` with the
actual complex derivatives. No analytic ODE theorem external to the corpus is assumed.

## Full complementary BM radial jet

Write original `++` Gauss parameters as `(a,b,c)`, put `lambda=1-c`, and retain

\[
 \alpha=a+\lambda,
 \qquad \beta=b+\lambda,
 \qquad \gamma=1+\lambda.
\tag{HG-TRANSFORM}
\]

On `0<z<1`, let `h(z)=exp(lambda log z)` and `y=hF`. Direct real differentiation gives

\[
 h'=\frac{\lambda h}{z},
 \qquad
 h''=\frac{\lambda(\lambda-1)h}{z^2},
\tag{FROB-DERIV-2}
\]

and hence

\[
 y'=h'F+hF',
 \qquad
 y''=h''F+2h'F'+hF''.
\tag{FULL-COMP-JET}
\]

Substitution in original Gauss operator and factoring `h` gives derivative coefficient

\[
 2\lambda(1-z)+c-(a+b+1)z
 =\gamma-(\alpha+\beta+1)z.
\]

The apparent `1/z` coefficient of `F` has constant numerator
`lambda*((lambda-1)+c)=0`; its remaining part is

\[
 -\lambda(\lambda+a+b)-ab=-(a+\lambda)(b+\lambda)=-\alpha\beta.
\]

Thus original residual of `y` is exactly `h` times transformed residual `(HG-ANALYTIC)`, so it
vanishes on `0<z<1`. This proves a dependency-closed full solution jet; endpoint sewing still
requires the normalized Wronskian limit and independent advanced/retarded incidence data.

- 2026-08-27 — formalized `(HG-DERIV-SUMS)`--`(HG-ANALYTIC)` in
  `ThetaCuspHawkingBMSecondHarmonicHypergeometricAnalyticODE.lean`, including generic and Xi-fibre
  actual-derivative forms. Formalized `(FROB-DERIV-2)`--`(FULL-COMP-JET)` and exact original BM
  radial-jet annihilation in `ThetaCuspHawkingBMSecondHarmonicComplementarySolutionJet.lean`.
  Direct Lean and targeted builds pass (`11141/11141`, `11142/11142`); axiom audits report only
  `propext`, `Classical.choice`, `Quot.sound`. Remaining local boundary core is exact singular
  endpoint sewing of independently normalized advanced/retarded solutions into augmented Peierls
  reciprocity; analytic complementary-solution existence is closed.

## Exact regular/complementary basis and full horizon Wronskian

For original second-harmonic parameters, direct corpus substitution gives

\[
 a=-2n-\frac54-\frac12 i\chi,
 \quad b=-2n-\frac54-\frac32 i\chi,
 \quad c=-4n-2-2i\chi.
\tag{REG-PARAM}
\]

If `Re chi != 0`, their imaginary parts are `-Re chi/2`, `-3 Re chi/2`, and `-2 Re chi`, so none
is a nonpositive integer. The regular horizon factor

\[
 R(z)={}_2F_1(a,b;c;z)
\tag{REG-SOL}
\]

therefore has radius one, `R(0)=1`, two analytic derivatives, and solves the original Gauss
equation by `(HG-ANALYTIC)`. Together with complementary solution `C(z)=h(z)F(z)`, define full
integrating-factor Wronskian

\[
 W(z)=p(z)\bigl(R(z)C'(z)-R'(z)C(z)\bigr).
\tag{FULL-W}
\]

Exact Frobenius balance gives

\[
 p(z)h'(z)=\lambda\sqrt{1-z},
 \qquad p(z)h(z)=z\sqrt{1-z}.
\tag{FULL-W-BAL}
\]

Hence

\[
 W(z)=R(z)F(z)\lambda\sqrt{1-z}
      +z\sqrt{1-z}\bigl(R(z)F'(z)-R'(z)F(z)\bigr).
\tag{FULL-W-EXP}
\]

Both factors and first derivatives are continuous at zero, while `R(0)=F(0)=1`. The second term
tends to zero and the first tends to `lambda`, proving

\[
 W(z)\longrightarrow\lambda=4n+3+2i\chi\ne0
 \qquad(z\to0^+).
\tag{FULL-W-LIM}
\]

This is the nondegenerate exact local basis needed for a Green kernel. It does not yet choose
retarded versus advanced endpoint incidence; that choice must come from augmented boundary data.

## Exact local Cauchy kernel

Where `(FULL-W)` is nonzero, define for fixed source radius `t`

\[
 K_t(z)=\frac{C(z)R(t)-R(z)C(t)}{W(t)}.
\tag{CAUCHY-K}
\]

Linearity and the two exact solution jets imply `L_z K_t=0`. Product and quotient rules give its
first two actual `z` derivatives from the corresponding jets. On the diagonal,

\[
 K_t(t)=0,
 \qquad
 p(t)\,\partial_zK_t(t)
 =\frac{p(t)(C'(t)R(t)-R'(t)C(t))}{W(t)}=1.
\tag{CAUCHY-JUMP}
\]

Thus Heaviside sewing of `K_t` has exact unit delta normalization. `(CAUCHY-K)` is a genuine local
fundamental kernel derived from solutions, not an assumed retarded/advanced response. Global
causal direction and AdS counterterm incidence remain open endpoint data.

- 2026-08-27 — formalized `(REG-PARAM)`--`(FULL-W-LIM)` in
  `ThetaCuspHawkingBMSecondHarmonicRegularSolution.lean` and
  `ThetaCuspHawkingBMSecondHarmonicExactHorizonBasis.lean`. Formalized `(CAUCHY-K)`--`(CAUCHY-JUMP)`
  in `ThetaCuspHawkingBMSecondHarmonicExactCauchyKernel.lean`. Direct Lean and targeted builds pass
  (`11143/11143`, `11144/11144`, `11145/11145`); representative axiom audits report only
  `propext`, `Classical.choice`, `Quot.sound`.

## Global normalized-Wronskian conservation conjecture

Let `R,C` be exact regular and complementary solutions, and abbreviate

\[
 p'=qD,\qquad
 qL[y]=p'y'+py''-qVy.
\tag{W-DIV}
\]

Here `p` is BM integrating factor, `q` its integrating weight, `D` first-derivative coefficient,
and `V=ab`. Both exact jets satisfy `L[R]=L[C]=0` on `0<z<1`. Differentiating `(FULL-W)` gives

\[
 W'=p'(RC'-R'C)+p(RC''-R''C).
\tag{W-DERIV}
\]

Multiply `(W-DIV)` for `C` by `R`, subtract `(W-DIV)` for `R` multiplied by `C`, and use
commutativity. Potential terms `qVRC` cancel exactly, leaving right side of `(W-DERIV)`.
Therefore

\[
 W'(z)=0\qquad(0<z<1).
\tag{W-CONS}
\]

Open interval is connected, so `W` is constant there. Combining constancy with one-sided horizon
limit `(FULL-W-LIM)` forces exact global identity

\[
 W(z)=\lambda=4n+3+2i\chi\qquad(0<z<1).
\tag{W-GLOBAL}
\]

For `Re chi != 0`, `(W-GLOBAL)` is nonzero at every interior source radius. Thus exact Cauchy
kernel denominator is globally invertible; remaining retarded/advanced problem is endpoint
incidence and distributional sewing, not an interior conjugate-point obstruction.

- 2026-08-27 — formalized `(W-DIV)`--`(W-GLOBAL)` in
  `ThetaCuspHawkingBMSecondHarmonicExactWronskianConservation.lean`. The exact normalized
  Wronskian has zero actual derivative on `(0,1)`, connectedness and its horizon limit give
  `W(z)=4n+3+2i chi` globally, every Xi-fibre basis is interior-nondegenerate, and the exact Cauchy
  kernel now has homogeneous radial equation plus unit diagonal jump at every interior source
  radius without an assumed nonvanishing premise. Direct Lean and targeted build pass
  (`11146/11146`); axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.

## Exact AdS outer Frobenius basis conjecture

Put `w=1-z` and retain original Gauss parameters `a,b,c`. Under this orientation reversal,

\[
 z(1-z)y''+[c-(a+b+1)z]y'-aby=0
\]

becomes

\[
 w(1-w)Y''+[c_0-(a+b+1)w]Y'-abY=0,
 \qquad c_0=a+b+1-c.
\tag{ADS-GAUSS}
\]

Exact BM exponent balance gives

\[
 c_0=\frac12,
 \qquad 1-c_0=c-a-b=\frac12.
\tag{ADS-EXP}
\]

Therefore canonical outer branches are

\[
 S(z)={}_2F_1\!\left(a,b;\frac12;1-z\right),
\tag{ADS-S}
\]

\[
 V(z)=(1-z)^{1/2}
 {}_2F_1\!\left(c-b,c-a;\frac32;1-z\right).
\tag{ADS-V}
\]

Nonzero `Re chi` excludes denominator and numerator termination collisions for both series, so
they have radius one. Coefficientwise analytic Gauss equations plus chain rule under `w=1-z`
give exact first and second real derivatives and `L[S]=L[V]=0` throughout `0<z<1`.

At `z->1-`, their normalized outer data are

\[
 S\to1,\quad S'\text{ bounded},\qquad
 V\to0,\quad \sqrt{1-z}\,V'\to-\frac12.
\tag{ADS-DATA}
\]

Since BM integrating factor is asymptotic to `sqrt(1-z)`, outer normalized Wronskian satisfies

\[
 p(SV'-S'V)\to-\frac12.
\tag{ADS-W-LIM}
\]

Wronskian conservation then forces exact global value `-1/2`, yielding genuine nondegenerate AdS
source/normalizable basis. Next obligation is express horizon basis `(R,C)` in `(S,V)` and prove
those actual connection coefficients equal corpus Gamma/Jost formulas rather than assuming them.

- 2026-08-27 — formalized `(ADS-GAUSS)`--`(ADS-W-LIM)` in
  `ThetaCuspHawkingBMSecondHarmonicExactAdSForbiddenSolution.lean`,
  `ThetaCuspHawkingBMSecondHarmonicExactAdSNormalizableSolution.lean`, and
  `ThetaCuspHawkingBMSecondHarmonicExactAdSOuterBasis.lean`. Both exact outer branches have two
  actual derivatives and solve original BM jet; normalized outer Wronskian has endpoint limit and
  exact global value `-1/2`, hence every Xi-fibre outer basis is nondegenerate. Added generic Abel
  identity `hasDerivAt_d4BMPlusPlusNormalizedWronskian_of_solutionJets`. Direct Lean and targeted
  builds pass through `11149/11149`; axiom audits report only `propext`, `Classical.choice`,
  `Quot.sound`.

## Exact horizon-to-AdS connection matrix conjecture

For any exact solution `Y`, conserved cross-Wronskians against outer basis `(S,V)` define

\[
 A_Y=\frac{W(Y,V)}{W(S,V)},\qquad
 B_Y=\frac{W(S,Y)}{W(S,V)}.
\tag{CONN-COEFF}
\]

Because `W(S,V)=-1/2`, Cramer's rule applies at every interior radius and gives simultaneous phase
decomposition

\[
 (Y,Y')=A_Y(S,S')+B_Y(V,V').
\tag{CONN-PHASE}
\]

Cross-Wronskian conservation makes `A_Y,B_Y` independent of radius, so they may be defined at
canonical basepoint `z=1/2`. Apply `(CONN-PHASE)` to horizon basis `(R,C)` and write connection
matrix

\[
 M=\begin{pmatrix}A_R&B_R\\A_C&B_C\end{pmatrix}.
\]

Bilinearity of Wronskian plus global normalizations `W(R,C)=lambda` and `W(S,V)=-1/2` force

\[
 \det M=A_RB_C-B_RA_C=-2\lambda.
\tag{CONN-DET}
\]

Hence horizon-to-AdS connection matrix is unconditionally invertible on every Xi fibre. This
constructs genuine analytic connection data without presupposing Gamma formulas. Remaining bridge
is identify these Cramer coefficients with existing Gamma/Jost coefficients and then impose
physical retarded/advanced endpoint incidence.

- 2026-08-27 — formalized `(CONN-COEFF)`--`(CONN-DET)` in
  `ThetaCuspHawkingBMSecondHarmonicExactConnectionMatrix.lean`. Generic conserved
  cross-Wronskians and pointwise Cramer's rule give radius-independent exact phase decompositions
  of both horizon branches in the AdS source/normalizable basis. Connection determinant is exactly
  `-2 * (4n + 3 + 2i chi)` and is nonzero on every Xi fibre. Direct Lean and targeted build pass
  (`11150/11150`); axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`. Gamma/Jost
  identification, endpoint incidence, and distributional retarded/advanced sewing remain open.

## Gauss-summation contiguous-transport conjecture

Write

\[
 t_j(a,b;c)=\frac{(a)_j(b)_j}{(c)_j\,j!},
 \qquad d=c-a-b.
\tag{GAUSS-TERM}
\]

For parameters avoiding denominator collisions, direct Pochhammer algebra gives

\[
 \frac{c-a}{c}\,t_j(a,b+1;c+1)-t_j(a,b;c)
 =\frac{j}{b}t_j(a,b;c)-\frac{j+1}{b}t_{j+1}(a,b;c).
\tag{GAUSS-SHIFT-B}
\]

Indeed `(b+1)_j=(b+j)(b)_j/b`, `(c+1)_j=(c+j)(c)_j/c`, and the numerator
remaining after a common denominator is `jd-ab`; the coefficient recurrence converts this into
the displayed first difference. Summing through `N` telescopes:

\[
 \frac{c-a}{c}\sum_{j=0}^{N}t_j(a,b+1;c+1)-
 \sum_{j=0}^{N}t_j(a,b;c)
 =-\frac{N+1}{b}t_{N+1}(a,b;c).
\tag{GAUSS-FIN-B}
\]

When `Re d>0`, hypergeometric coefficient asymptotics give `j t_j -> 0`; hence

\[
 F(a,b;c;1)=\frac{c-a}{c}F(a,b+1;c+1;1).
\tag{GAUSS-INF-B}
\]

Symmetry gives the companion simultaneous shift `(a,c) -> (a+1,c+1)` with factor `(c-b)/c`.
Both shifts preserve `d`. Repeating them moves any collision-free BM triple into an Euler chamber
`Re b>0`, `Re(c-b)>0`; choosing the second shift still larger gives the simple absolute majorant
`Re(c-b)>|a|`. There the binomial expansion of `(1-t)^(-a)` is dominated by
`(1-t)^(-|a|)`, so termwise integration against
`t^(b-1)(1-t)^(c-b-1)` is valid. The complex beta integral then proves

\[
 F(a,b;c;1)=
 \frac{\Gamma(c)\Gamma(c-a-b)}{\Gamma(c-a)\Gamma(c-b)}.
\tag{GAUSS-SUM}
\]

Gamma recurrence obeys exactly the inverse finite shift factors, so `(GAUSS-INF-B)` and its
`a`-analogue transport `(GAUSS-SUM)` back to the original BM parameters without parameter-space
analytic continuation. Since BM has `d=1/2`, this identifies the regular-to-forbidden Cramer
coefficient with `d4BMCausalForbiddenBoundaryCoefficient`; the derivative/companion Gauss value
then identifies the normalizable coefficient. This is infrastructure construction, not a new route.
