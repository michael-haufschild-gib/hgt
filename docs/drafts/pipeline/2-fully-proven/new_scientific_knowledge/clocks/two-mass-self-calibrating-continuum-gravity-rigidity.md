# Two-mass self-calibrating continuum gravity rigidity

- **ID:** `two-mass-self-calibrating-continuum-gravity-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / OPERATOR IDENTIFICATION
- **Parents:**
  `two-mass-self-calibrating-clock-metric-law.md`,
  `chronometric-continuum-operator-rigidity.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/SelfCalibratingBundleQuotientRigidity.lean`
- **Status:** paper-proved and formalized unconditionally in Lean, including the lift off
  coordinate-trivialized fields to tangent bundles and coordinate charts, and the descent to the
  quotient by clock-label-preserving frame automorphisms.

## Headline

> **Two kinds of clocks determine spacetime and its law of gravity—even when every detector has
> an unknown local calibration.**

This is the complete-data continuum theorem. It preserves nonlinear solution branches and makes
the remaining experimental/analytic gap explicit.

## Self-calibrating chronometric field

Let \(X\) be an event set and let \(V\) be a real model cotangent fiber. At every event \(x\), let

- \(\kappa(x)\neq0\) be an unknown common endpoint-calibration product;
- \(g_x^{-1}:V\times V\to\mathbb R\) be a symmetric bilinear inverse-metric form.

Choose two calibrated squared masses \(\mu_1\neq\mu_2\). The ideal complete two-mass observation is

\[
\begin{aligned}
  D(x)&=(\mu_1-\mu_2)\kappa(x),\\
  S(x,\xi)&=\kappa(x)g_x^{-1}(\xi,\xi).                                  \tag{1}
\end{aligned}
\]

For dressed inverse Green operators, \(D\) is their zeroth-order difference and \(S\) is the
quadratic principal-symbol channel.

## Theorem 1 — continuum metric and calibration injectivity

The map

\[
  (\kappa,g^{-1})\longmapsto(D,S)                                        \tag{2}
\]

is injective.

### Proof

The first channel gives calibration pointwise:

\[
  \kappa(x)=\frac{D(x)}{\mu_1-\mu_2}.                                    \tag{3}
\]

Since \(\kappa(x)\neq0\), the second channel gives every diagonal value

\[
  g_x^{-1}(\xi,\xi)=\frac{S(x,\xi)}{\kappa(x)}.                           \tag{4}
\]

Polarization gives every off-diagonal component:

\[
  2g_x^{-1}(\xi,\eta)
  =
  g_x^{-1}(\xi+\eta,\xi+\eta)
  -g_x^{-1}(\xi,\xi)
  -g_x^{-1}(\eta,\eta).                                                   \tag{5}
\]

Thus equal observations imply equal calibration fields and equal continuum metric fields.
\(\square\)

No signature, nondegeneracy, smoothness, analyticity, or field equation is required for this
injectivity theorem. Lorentzian signature is a physical restriction on the admissible recovered
forms, not an ingredient of the proof.

## Theorem 2 — branch-safe nonlinear gravity-operator rigidity

Let \(\mathcal G\) be the space of self-calibrating metric fields and let

\[
  \mathcal E:\mathcal G\to\mathcal J
\]

be any source operator; it need not be linear, perturbative, analytic, or single-valued after
solving for geometry. Define its branch-safe two-mass graph

\[
  \Gamma_{2m}(\mathcal E)
  =
  \left\{
    \bigl(\mathcal E(\kappa,g),D_{\kappa},S_{\kappa,g}\bigr):
    (\kappa,g)\in\mathcal G
  \right\}.                                                              \tag{6}
\]

Then

\[
  \boxed{
  \Gamma_{2m}(\mathcal E_1)=\Gamma_{2m}(\mathcal E_2)
  \quad\Longleftrightarrow\quad
  \mathcal E_1=\mathcal E_2.}                                            \tag{7}
\]

### Proof

The reverse implication is immediate. For the forward implication, fix
\((\kappa,g)\). Its graph point under \(\mathcal E_1\) occurs in the graph of
\(\mathcal E_2\), so there is \((\kappa',g')\) with the same two-mass observation and

\[
  \mathcal E_1(\kappa,g)=\mathcal E_2(\kappa',g').
\]

Theorem 1 forces \((\kappa',g')=(\kappa,g)\). Therefore the two operators agree at every field.
\(\square\)

## What is and is not solved

Equations `(2)` and `(7)` close the exact complete-data identifiability problem:

> Unknown local detector gain, conformal scale, multiple nonlinear solution branches, and
> arbitrary nonlinear operator dependence do not create a residual ambiguity once the complete
> two-mass symbol graph is known.

The remaining open core is not algebraic identifiability. It is physical realization:

1. recover complete complex dressed Green responses from finite clock interventions in a
   worldtube;
2. split causal/retarded support without assuming the unknown geometry;
3. prove common or known relative endpoint gain for two physical species;
4. include backreaction and conservation-constrained active sources.

Item 5 of the earlier list — passing from coordinate-trivialized fields to smooth bundles modulo
diffeomorphism and gauge — is now closed mathematically; see below.

Until the remaining steps close, `(7)` is a conditional continuum reconstruction theorem, not a
claim that Nature has already been experimentally reduced to two clock species.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean` carries Theorems 1
and 2 on coordinate-trivialized fields: `SelfCalibratingMetricField`, `twoMassObservation`,
`twoMassObservation_injective` (equation `(2)`), and
`twoMassSelfCalibratingContinuumGravityRigidity` (equation `(7)`).

`formal/GaloisForLFunctions/HTGeometry/SelfCalibratingBundleQuotientRigidity.lean` removes both
restrictions the coordinate-trivialized statement carried.

**Bundle lift.** The calibration channel is pointwise and the symbol channel is fiberwise, so the
argument lifts verbatim to a family of fibers indexed by the event set:

- `BundleSelfCalibratingMetric Event Fiber` with `Fiber : Event → Type`, its
  `twoMassObservation` and `twoMassObservation_injective`;
- `bundleTwoMassSelfCalibratingRigidity` — `(7)` over an arbitrary fiber bundle;
- `TangentSelfCalibratingMetric`, `tangentTwoMassObservation_injective`,
  `tangentTwoMassSelfCalibratingRigidity` — the same with `Fiber = TangentSpace I x` on a charted
  smooth manifold;
- `SmoothSelfCalibratingChart`, `SmoothSelfCalibratingChart.twoMassObservation_injective`,
  `SmoothSelfCalibratingChart.twoMassSelfCalibratingRigidity` — the coordinate-chart case, with a
  smooth nowhere-vanishing calibration and a smooth nondegenerate symmetric inverse-metric field.

**Quotient lift.** A clock-label-preserving frame automorphism — a relabelling of events together
with a linear reframing of each tangent fiber — pulls back the calibration as a scalar and the
inverse metric as a quadratic form:

- `MulAction (ClockFrameAut Event Tangent)` on `SelfCalibratingMetricField` and on
  `SelfCalibratingObservation`;
- `twoMassObservationOf_equivariant`, `twoMassObservationOf_injective`;
- `twoMassSelfCalibratingRigidity_mod_frameAut` — `(7)` on the orbit quotients: equality of
  gravity operators is replaced by equality up to a frame automorphism of the source labels;
- `smul_scaling_selfCalibrating_form`, `smul_scaling_selfCalibrating_ne_self` — a conformal
  reframing with `c⁻² ≠ 1` moves every field with a nonzero symbol component, so the quotient
  statement is a genuine weakening of equality rather than a restatement.

The quotient theorem it rests on, `chronometricSolutionGraph_orbitQuotient_eq_iff`, holds for an
arbitrary group acting equivariantly with an injective equivariant observation encoding. Any gauge
group of local field redefinitions that preserves the two-mass observation channel is therefore
covered by the same statement; the frame-automorphism group is the instance constructed here.

All of these depend only on `propext`, `Classical.choice`, `Quot.sound`.
