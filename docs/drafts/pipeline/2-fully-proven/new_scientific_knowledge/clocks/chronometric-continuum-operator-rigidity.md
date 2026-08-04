# Chronometric graph rigidity for continuum metric gravity

- **ID:** `chronometric-continuum-operator-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / TIME / CAUSALITY / INVERSE LAW
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** dependency-closed paper proof, fully formalized. Continuum-indexed polarization,
  graph rigidity, Ramsey phase recovery, the tangent-bundle and chart lifts, the quotient lift
  under label-preserving frame automorphisms, and ordered-product recovery for a regular pulse
  family with unbounded generators are all unconditional in Lean. No stated theorem of this card
  is unformalized.

## Headline

> **No two different laws of gravity can make every clock agree.**

Exact public form:

> **The full nonlinear law of metric gravity is the graph of how calibrated matter changes
> squared clock intervals.**

This is an operator-identification theorem, not a reconstruction of one metric under an assumed
field equation.

## Continuum data

Let \(M\) be a smooth manifold and let \(\mathcal G\) be any class of smooth time-oriented
Lorentzian metrics on \(M\). No perturbative, analytic, globally hyperbolic, or unique-solvability
assumption is needed for the theorem below.

For \(g\in\mathcal G\), define its infinitesimal chronometric field

\[
  \mathsf Q(g)(x,v)=g_x(v,v),\qquad x\in M,\quad v\in T_xM.                 \tag{1}
\]

Operationally, negative values are squared proper-time rates of infinitesimal clock trajectories,
zero is the light-cone boundary, and positive values are obtained by clock-radar/rod calibration.
The mathematical theorem uses the complete signed squared-interval field `(1)`, but only its
negative part is needed: the timelike values alone already determine `\mathsf Q(g)`, so no
reconstruction of the spacelike part is required. See Lemma 1b.

Let \(\mathcal J\) be the set of independently calibrated physical source labels. A gauge-fixed
metric gravity law is a map

\[
  \mathcal E:\mathcal G\longrightarrow\mathcal J.                           \tag{2}
\]

Its chronometric solution graph is

\[
  \Gamma_{\mathrm{chr}}(\mathcal E)
  =
  \{\,(\mathcal E(g),\mathsf Q(g)):g\in\mathcal G\,\}
  \subseteq
  \mathcal J\times \mathsf Q(\mathcal G).                                  \tag{3}
\]

Unlike a source-to-solution function, `(3)` retains every branch when one source has several
solutions.

## Lemma 1 — squared clock intervals determine the metric

The map

\[
  \mathsf Q:\mathcal G\longrightarrow
  \prod_{x\in M}\mathbb R^{T_xM}
\]

is injective.

### Proof

Let \(\mathsf Q(g)=\mathsf Q(h)\). For every \(x\in M\) and \(u,v\in T_xM\), symmetry and
bilinearity give the polarization identities

\[
\begin{aligned}
  2g_x(u,v)
  &=g_x(u+v,u+v)-g_x(u,u)-g_x(v,v),\\
  2h_x(u,v)
  &=h_x(u+v,u+v)-h_x(u,u)-h_x(v,v).
\end{aligned}                                                              \tag{4}
\]

Every diagonal term on the right is a value of `(1)`, so the two right-hand sides agree.
Therefore \(g_x(u,v)=h_x(u,v)\) for all \(x,u,v\), hence \(g=h\). \(\square\)

The proof does not use Lorentz signature: diagonal values determine every symmetric bilinear
field. Lorentz signature supplies the physical clock interpretation.

## Lemma 1b — proper time alone suffices

Let \(B\) be a symmetric bilinear form on a topological real vector space and let \(U\) be any
nonempty open set with \(B(v,v)=0\) for all \(v\in U\). Then \(B=0\).

### Proof

Fix \(v_0\in U\) and an arbitrary \(w\). The line \(t\mapsto v_0+tw\) is continuous, so it meets
\(U\) on an interval \(|t|<\varepsilon\). There

\[
  0=B(v_0+tw,v_0+tw)=B(v_0,v_0)+2t\,B(v_0,w)+t^2B(w,w)
   =t\bigl(2B(v_0,w)+t\,B(w,w)\bigr),
\]

using \(B(v_0,v_0)=0\). For \(t\neq0\) this gives \(2B(v_0,w)+t\,B(w,w)=0\); evaluating at
\(t=\varepsilon/2\) and \(t=\varepsilon/4\) and subtracting gives \(B(w,w)=0\). Since \(w\) was
arbitrary the diagonal vanishes identically, and Lemma 1's polarization gives \(B=0\).
\(\square\)

Consequently two chronometric fields agreeing on any fiberwise nonempty open family of directions
— in particular on their timelike cones, which are open because the squared interval is continuous
— are equal. Proper time is complete data; the clock-radar reconstruction of spacelike separations
is an operational convenience, not a mathematical requirement.

## Theorem 1b — nine before/after boundaries and one tick determine a four-metric

In a four-dimensional frame \((t,x,y,z)\), consider six axis light-clock directions

\[
  t\pm x,\qquad t\pm y,\qquad t\pm z                                      \tag{4a}
\]

and three mixed Pythagorean directions

\[
  5t+3x+4y,\qquad 5t+3x+4z,\qquad 5t+3y+4z.                               \tag{4b}
\]

Let \(B\) be any symmetric real bilinear form. If all nine directions in `(4a)`--`(4b)` are
\(B\)-null and one calibrated clock gives \(B(t,t)=-1\), then

\[
  [B]_{(t,x,y,z)}=\operatorname{diag}(-1,1,1,1).                           \tag{4c}
\]

### Proof

For each \(e\in\{x,y,z\}\), subtracting
\(B(t+e,t+e)=0\) and \(B(t-e,t-e)=0\) gives \(B(t,e)=0\). Adding them gives
\(B(e,e)=-B(t,t)=1\).

Now expand, for example,

\[
  0=B(5t+3x+4y,5t+3x+4y)
   =25B(t,t)+9B(x,x)+16B(y,y)+24B(x,y).
\]

The first three terms sum to \(-25+9+16=0\), so \(B(x,y)=0\). The other two mixed directions give
\(B(x,z)=B(y,z)=0\). These are all ten independent entries of a symmetric four-metric, proving
`(4c)`. \(\square\)

The nine null channels determine conformal metric in an adapted frame; one timelike tick fixes its
scale. Their count, nine plus one, equals the ten independent entries of a symmetric four-metric.
No minimality claim is made without a separate lower-bound theorem.

## Theorem 2 — continuum chronometric operator rigidity

For any two gravity laws \(\mathcal E_1,\mathcal E_2:\mathcal G\to\mathcal J\),

\[
  \boxed{
  \Gamma_{\mathrm{chr}}(\mathcal E_1)
  =
  \Gamma_{\mathrm{chr}}(\mathcal E_2)
  \quad\Longleftrightarrow\quad
  \mathcal E_1=\mathcal E_2.}                                               \tag{5}
\]

### Proof

The reverse implication is immediate. Suppose the two graphs are equal and fix
\(g\in\mathcal G\). Then

\[
  (\mathcal E_1(g),\mathsf Q(g))
  \in\Gamma_{\mathrm{chr}}(\mathcal E_1)
  =\Gamma_{\mathrm{chr}}(\mathcal E_2).
\]

Thus some \(h\in\mathcal G\) satisfies

\[
  \mathcal E_2(h)=\mathcal E_1(g),
  \qquad
  \mathsf Q(h)=\mathsf Q(g).
\]

Lemma 1 forces \(h=g\), hence \(\mathcal E_2(g)=\mathcal E_1(g)\). Since \(g\) was arbitrary,
\(\mathcal E_1=\mathcal E_2\). \(\square\)

## Corollary 3 — the gravity equation is an inverse clock law

If \(\mathcal E\) is restricted to a region on which it is bijective, then

\[
  \mathcal E
  =
  \left(\mathsf Q\circ\mathcal E^{-1}\right)^{-1}\circ\mathsf Q.              \tag{6}
\]

Here the inverse is taken from \(\mathsf Q(\mathcal G)\) back to \(\mathcal J\). Equivalently, the
source-to-clock map and the metric field equation are inverse descriptions of the same law.

Equation `(5)`, not the notation `(6)`, is the branch-safe universal statement.

## Lemma 4 — exact Ramsey recovery removes detector phase loss

Let \(\mathcal A\) be a unital operator algebra, \(\omega\) a state, and \(U\in\mathcal A\) a
unitary that can be applied on one branch of a two-level clock. Prepare the clock in
\(\lvert+\rangle\), apply

\[
  C_U
  =
  \lvert0\rangle\!\langle0\rvert\otimes 1
  +
  \lvert1\rangle\!\langle1\rvert\otimes U,                                 \tag{7}
\]

and read both equatorial clock quadratures. Direct multiplication gives

\[
  \langle\sigma_x\rangle=\operatorname{Re}\omega(U),
  \qquad
  \langle\sigma_y\rangle=\operatorname{Im}\omega(U)                         \tag{8}
\]

up to the fixed sign convention used for \(\sigma_y\). Thus clock outcome probabilities in two
readout bases recover the complex expectation, not merely its modulus or symmetrized part.

For controlled sequential pulses \(U_1\cdots U_n\), the same calculation recovers
\(\omega(U_1\cdots U_n)\). If

\[
  U_j(\lambda_j)=\exp(i\lambda_j\Phi(f_j))
\]

is a regular family, then

\[
  i^{-n}
  \left.
  \frac{\partial^n}{\partial\lambda_1\cdots\partial\lambda_n}
  \omega\!\left(U_1(\lambda_1)\cdots U_n(\lambda_n)\right)
  \right|_{\lambda=0}
  =
  \omega\!\left(\Phi(f_1)\cdots\Phi(f_n)\right).                            \tag{9}
\]

Consequently a causally ordered, controlled-clock family reconstructs all ordered correlation
distributions that its realizable local unitary pulses separate. The remaining physical
assumption is controllability of those pulses, not a polarization or phase-recovery gap.

## What is new and what is not

Prior work proves substantially harder partial-data geometry theorems: boundary time separation
can determine metric jets; nonlinear wave observations can recover causal diamonds; local QFT
probe schemes can asymptotically measure every observable of a linear scalar field. Those results
are required for a realistic small-laboratory theorem.

The new exact point isolated here is different:

1. vary the calibrated source rather than reconstruct one background;
2. retain the full solution relation rather than assume one solution per source;
3. identify the complete nonlinear metric operator, not only geometry or selected coefficients;
4. prove phase-complete ordered clock tomography by controlled Ramsey readout.

The theorem is not yet a Nature result by itself because `(3)` is complete continuum data. The
Nature-level step is to prove that the restricted chronometric intervention functor of one
laboratory determines `(3)` on its causal diamond.

## Hostile scope audit

1. **Diffeomorphisms:** `(5)` uses fixed relational event and tangent labels. Resolved: the
   quotient theorem replaces equality by pullback equivalence under clock-label-preserving frame
   automorphisms, and that equivalence is proved strictly coarser than equality.
2. **Gauge:** resolved. `(2)` is gauge-fixed, and with an extra gravitational sector the complete
   encoding is never injective. The correct replacement is *fibre constancy* — a law that is a
   function of its observation — which a gauge-invariant law satisfies as soon as its extra sector
   is reported completely up to field redefinition. Rigidity then holds without injectivity; if the
   sector is unreported, the clock-dark no-go of point 6 applies instead.
3. **Clock-only realization:** resolved. Proper time supplies the timelike values of `(1)`, and by
   Lemma 1b those alone determine the whole signed quadratic germ. What remains is the operational
   question of measuring the timelike values, not a missing reconstruction step.
4. **Partial laboratories:** made exact. Region data determine the chronometric field of that
   region, hence every law that is a function of it. They determine the field outside the region
   exactly when unique continuation from the region holds — and in this model class, where nothing
   relates different events, unique continuation is *false* for every proper subregion: a form
   planted at one outside event is invisible. Supplying the continuation is the role of a field
   equation, and closing it is the nonlinear Lorentzian inverse theorem this card does not prove.
5. **Source calibration:** proved sharp. Relabelling the calibrated source set by a bijection
   changes the operator but only transports its graph, so graph comparison up to a theory-chosen
   relabelling carries no information. Operational source channels must be fixed independently.
6. **Hidden sectors:** proved sharp. Rigidity holds *exactly* when the observation encoding is
   injective, and a factor of the geometry absent from every channel makes it non-injective, so
   two laws separating that factor have identical graphs. Clock-dark sectors are outside the
   admissible class, not silently identified.
7. **Quantum gravity:** `(5)` identifies classical continuum metric operators. It does not by
   itself reconstruct a quantum gravitational state or path integral.

## Lean obligations

Formalize unconditionally:

1. [complete] diagonal injectivity of an indexed field of symmetric bilinear forms;
2. [complete] graph rigidity for an arbitrary injective observation encoding;
3. [complete] specialization from squared intervals to coordinate-trivialized continuum metric
   fields;
4. [complete] two-quadrature Ramsey recovery;
5. [complete] nine null-order comparisons plus one tick determine a symmetric four-metric;
6. [complete] ordered-product recovery by characteristic-functional differentiation, for a regular
   family with unbounded generators;
7. [complete] smooth tangent-bundle/chart lift;
8. [complete] quotient lift under label-preserving equivalences;
9. [complete] the pointwise inverse-law form `(6)` on a region where the law is bijective;
10. [complete] Lemma 1b: proper time alone determines the chronometric field;
11. [complete] sharpness of `(5)`: injectivity of the encoding is necessary, clock-dark sectors
    defeat rigidity, and theory-dependent source relabelling only transports the graph;
12. [complete] extra gravitational sectors: fibre-constant rigidity, reporter completeness up to
    gauge, and the reported/clock-dark dichotomy;
13. [complete] bounded laboratory regions: region rigidity, the exact continuation criterion, and
    the proper-subregion no-go;
14. [complete] causal diamonds: proper-time determination localized to a region
    (`SmoothPseudoMetric.eqOn_of_properTime_eqOn`), the coordinate diamond `coneFuture`/`conePast`/
    `coneDiamond`, its traversing timelike segment (`mem_coneDiamond_segment`), and clock-only
    determination inside it (`eqOn_coneDiamond_of_properTime`), in
    `formal/GaloisForLFunctions/HTGeometry/ChronometricCausalDiamond.lean`.

The existing all-orders symmetric multilinear polarization theorem supplies a stronger reusable
dependency for item 1.

### Formal artifacts

`formal/GaloisForLFunctions/HTGeometry/ContinuumChronometricGravity.lean` — items 1–5:
`ChronometricMetricField.squaredInterval_injective`,
`chronometricSolutionGraph_eq_iff_of_injective`, `continuumChronometricOperatorRigidity`,
`chronometricRamseyQuadratures_injective`,
`nineNullClockComparisons_oneTick_metricRigidity`.

`formal/GaloisForLFunctions/HTGeometry/ChronometricBundleMetricRigidity.lean` — item 7. The
polarization argument is fiberwise, so it lifts to a family of fibers indexed by the event set:

- `bilinForm_eq_of_diagonal_eq` — diagonal values determine a symmetric bilinear form;
- `BundleChronometricMetric` and `BundleChronometricMetric.squaredInterval_injective` — squared
  clock intervals determine a metric field on an arbitrary bundle of fibers;
- `bundleChronometricOperatorRigidity` — `(5)` over that bundle;
- `TangentChronometricMetric`, `tangentSquaredInterval_injective`,
  `tangentChronometricOperatorRigidity` — the same statements with `Fiber = TangentSpace I x` on a
  charted smooth manifold;
- `SmoothPseudoMetric.squaredInterval_injective`,
  `SmoothPseudoMetric.chronometricOperatorRigidity` — the chart lift, for a smooth nondegenerate
  symmetric matrix metric field;
- `law_eq_invFun_encode_comp_symm`, `injective_encode_comp_symm` — Corollary 3, equation `(6)`:
  on a region where the law is bijective it equals the inverse of the induced source-to-clock map
  composed with the clock encoding.

`formal/GaloisForLFunctions/HTGeometry/ChronometricRegionLocalization.lean` — item 13, which makes
hostile-audit point 4 exact:

- `restrictRegion`, `regionObservation`, `restrictRegion_eq_of_regionObservation_eq` — squared
  clock intervals inside a region determine the chronometric field inside that region;
- `FactorsThroughRegion`, `chronometricRegionRigidity` — a laboratory identifies every law that is
  a function of the field over its own region;
- `UniqueContinuation`, `injective_regionObservation_iff_uniqueContinuation`,
  `chronometricRegionRigidity_of_uniqueContinuation` — region data give unrestricted rigidity
  **exactly when** unique continuation from the region holds;
- `pointForm`, `not_uniqueContinuation_of_exists_notMem`, `exists_ne_law_regionGraph_eq` — in this
  model class unique continuation fails for every proper subregion, so worldtube data alone cannot
  determine an arbitrary nonlinear law;
- `exists_ne_zero_symmetric_bilinForm_real` — the no-go's hypothesis is inhabited.

`formal/GaloisForLFunctions/HTGeometry/ChronometricGaugeRigidity.lean` — item 12, which answers
hostile-audit point 2. Injectivity of the complete encoding is the wrong hypothesis once an extra
sector is present; fibre constancy is the right one:

- `FiberConstant`, `chronometricSolutionGraph_eq_iff_of_fiberConstant` — a law that is a function
  of its observation is determined by the branch-safe graph, whether or not the encoding separates
  points; fibre constancy of either law suffices;
- `fiberConstant_of_injective` — the injective rigidity theorem is the special case;
- `reporterCompleteEncode`, `GaugeInvariant`, `ReporterComplete`,
  `fiberConstant_of_gaugeInvariant`, `chronometricGaugeRigidity` — with the clock channel
  injective on the metric sector and the reporter determining the extra sector up to a field
  redefinition, gauge-invariant nonlinear laws are rigid;
- `potentialReporter`, `potentialReporter_gaugeInvariant`, `potentialReporter_complete`,
  `chronometricGaugeRigidity_potential` — the worked case of a scalar gravitational potential
  defined up to an additive constant and reported by its differences;
- `gauge_dichotomy` — with the same geometry space but an unreported sector, rigidity fails.

`formal/GaloisForLFunctions/HTGeometry/ChronometricRigiditySharpness.lean` — item 11, which
answers hostile-audit points 5 and 6 by proving the two hypotheses of `(5)` load-bearing:

- `exists_ne_law_graph_eq_of_not_injective` — if two geometries share an observation, the two laws
  separating them have identical branch-safe graphs;
- `chronometricSolutionGraph_rigid_iff_injective` — **rigidity holds exactly when the encoding is
  injective**, so the hypothesis of `(5)` is necessary and not merely convenient;
- `not_injective_hiddenSector`, `exists_ne_law_graph_eq_of_hiddenSector`,
  `exists_ne_law_graph_eq_of_hiddenSector_chronometric` — a clock-dark factor of the geometry
  restores the ambiguity, concretely for `ChronometricMetricField × Hidden`;
- `chronometricSolutionGraph_relabel`, `exists_ne_law_with_transported_graph` — a bijective
  relabelling of the calibrated source set produces a genuinely different operator whose graph is
  the transported image of the original, so source labels must be fixed independently of the
  theory.

`formal/GaloisForLFunctions/HTGeometry/ChronometricTimelikeConeDetermination.lean` — item 10,
which answers hostile-audit point 3:

- `bilin_diag_eq_zero_of_diag_eqOn_open`, `bilinForm_eq_of_diagonal_eqOn_open` — Lemma 1b in a
  topological real vector space; no finite dimension, signature or continuity of the form is used;
- `BundleChronometricMetric.eq_of_squaredInterval_eqOn_open` — squared intervals on any fiberwise
  nonempty open family of directions determine the bundle metric field;
- `SmoothPseudoMetric.continuous_squaredInterval`, `timelikeCone`, `isOpen_timelikeCone` — the
  timelike cone of a chart metric is open;
- `SmoothPseudoMetric.eq_of_properTime_eq`, `properTimeObservation`,
  `properTimeObservation_injOn` — proper time alone determines a smooth chart metric field;
- `SmoothPseudoMetric.chronometricOperatorRigidity_properTime` — `(5)` from proper-time data
  alone;
- `SmoothPseudoMetric.minkowski_timelikeCone_nonempty` — Minkowski space has a timelike direction
  at every event, so the hypothesis is not vacuous.

`formal/GaloisForLFunctions/HTGeometry/ChronometricQuotientRigidity.lean` — item 8, which answers
hostile-audit point 1. Equality of laws is replaced by equivalence, not weakened away:

- `orbitQuotientMap`, `orbitQuotientMap_injective` — an injective equivariant encoding induces an
  injective map of orbit quotients;
- `chronometricSolutionGraph_orbitQuotient_eq_iff` — quotient solution graphs coincide exactly
  when the two laws agree pointwise up to the action;
- `ClockFrameAut` with its `Group` instance — a clock-label-preserving frame automorphism is a
  relabelling of events together with a linear reframing of each tangent fiber, the trivialized
  model of a bundle automorphism covering a diffeomorphism;
- `MulAction` of `ClockFrameAut` on metric fields and on squared-interval observations, and
  `chronometricObservationOf_equivariant` — squared clock intervals are equivariant;
- `chronometricOperatorRigidity_mod_frameAut` — `(5)` modulo frame automorphisms;
- `smul_form_scaling`, `smul_scaling_ne_self` — the action is strictly coarser than equality, so
  the quotient theorem is not a restatement of the fixed-label one.

`formal/GaloisForLFunctions/HTGeometry/ChronometricOrderedTomography.lean` — item 6, equation
`(9)` for a regular pulse family in a unital Banach algebra:

- `nestedDerivAtZero` — the iterated mixed derivative at zero, one coupling at a time in causal
  order;
- `pulseProduct`, `orderedProduct` — the ordered pulse family and the ordered generator product;
- `nestedDerivAtZero_pulseProduct` — one derivative in each coupling turns the state value of the
  ordered pulse family into `ω(a₀ ⋯ a_{n-1})`;
- `nestedDerivAtZero_pulseProduct_imaginary` — the `U_j(λ)=exp(iλΦ_j)` normalization, carrying the
  factor `iⁿ` of `(9)`;
- `ordered_correlation_of_ramsey_quadratures` — composed with the two-quadrature recovery: any
  reported functional with the same Ramsey quadratures yields the same ordered correlations.

`formal/GaloisForLFunctions/HTGeometry/ChronometricRegularPulseTomography.lean` — item 6 in the
generality Lemma 4 states it, with **unbounded** generators. The hypotheses are exactly: each pulse
is a bounded operator at fixed coupling, the generators are linear maps of one common invariant
domain, and each pulse family is differentiable at zero coupling on that domain with derivative `i`
times its generator. No continuity, boundedness, self-adjointness or group law is assumed:

- `nestedRealDerivAtZero` — the iterated mixed derivative at zero in real couplings;
- `orderedPulseApply`, `orderedGenerator` — the ordered pulse family and the ordered composite of
  the generators as a linear map of the domain;
- `nestedRealDerivAtZero_orderedPulseApply` — **equation `(9)`**: the mixed derivative of the
  characteristic functional equals `iⁿ ω(Φ_0 ⋯ Φ_{n-1} v)`;
- `exists_regularPulseFamily` — the hypothesis class is inhabited.

`formal/GaloisForLFunctions/HTGeometry/ChronometricUnboundedPulseModel.lean` — the class contains
genuinely unbounded generators, so `(9)` is not a disguised Banach-algebra statement:

- `finiteSupportSeq` — finitely supported bounded sequences, the common invariant domain inside the
  supremum-norm space `ℕ →ᵇ ℂ`;
- `natPulse` — multiplication by the unimodular sequence `k ↦ e^{itk}`, a bounded operator;
- `natGenerator` — multiplication by the unbounded sequence `k ↦ k`, a linear endomorphism of the
  domain;
- `hasDerivAt_natPulse` — the regular-family derivative property, proved from the elementary bound
  `‖e^z - 1 - z‖ ≤ ‖z‖²`;
- `natGenerator_unbounded` — no constant controls the generator's norm on the domain;
- `exists_unbounded_regularPulseFamily` — a regular pulse family all of whose generators are
  unbounded.

All of these depend only on `propext`, `Classical.choice`, `Quot.sound`.

The Fock-space *instantiation* — constructing Segal field operators and their Weyl unitaries — is a
separate object construction absent from mathlib and from this corpus. It is an input to `(9)`, not
a gap in it: any such construction supplies the three hypotheses above and the theorem then applies
verbatim.

## Primary sources and closest collisions

- P. Stefanov, G. Uhlmann, and A. Vasy, *Determination of the spacetime from local time
  measurements*, <https://arxiv.org/abs/1412.1350>.
- C. J. Fewster, I. Jubb, and M. H. Ruep, *Asymptotic measurement schemes for every observable
  of a quantum field theory*, <https://arxiv.org/abs/2203.09529>.
- C. J. Fewster and R. Verch, *Quantum fields and local measurements*,
  <https://arxiv.org/abs/1810.06512>.
- Y. Kurylev, M. Lassas, L. Oksanen, and G. Uhlmann,
  *Inverse problem for Einstein--scalar field equations*,
  <https://arxiv.org/abs/1406.4776>.
- M. Rotondo, *A Detector-Based Inference Framework for Quantum Theory and Spacetime Geometry*,
  <https://arxiv.org/abs/2604.10349>. This reconstructs a detector information metric and selects
  the Einstein--Hilbert term through an effective low-energy ansatz; it does not prove `(5)` or
  recover an unknown gravitational operator from source-indexed clock data.
