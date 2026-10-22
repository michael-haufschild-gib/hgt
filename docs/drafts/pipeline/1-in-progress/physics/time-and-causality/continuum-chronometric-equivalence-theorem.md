# Continuum chronometric equivalence: clocks determine the law of gravity

- **ID:** `continuum-chronometric-equivalence-theorem`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL PHYSICS LAW / CONTINUUM GRAVITY / TIME / CAUSALITY / INVERSE PROBLEM
- **Parent:** `chronometric-causal-susceptibility-law.md`
- **Status:** exact continuum theorem target stated; complete-data metric-operator rigidity,
  Ramsey phase recovery, four-dimensional conformal cancellation, and two-mass detector
  self-calibration are paper-proved and formalized; restricted-laboratory, gauge, and quantum lifts
  remain open.

## Headline

> **Gravity is matter changing what “before” means.**

Equivalent public law:

> **Two universes obey the same law of gravity if and only if every possible addition of matter
> changes every possible clock comparison in the same way.**

The second sentence is the theorem. It is intentionally stronger than recovering one metric inside
a previously fixed field equation.

## Chronometric intervention functor

Let \(\mathcal E\) be a local continuum gravity--matter theory on a four-dimensional globally
hyperbolic spacetime. A clock laboratory is a timelike worldtube \(V\) carrying calibrated quantum
clocks, rods, and tunable local detector couplings. For each compactly supported, independently
calibrated physical source \(J\) in \(V\), record all clock outcomes for:

1. every compact switching function and clock gap;
2. every preparation and readout basis;
3. every finite ordered sequence of clock couplings;
4. every finite joint clock product and commutator;
5. proper-time and local-volume calibration data.

The resulting operational object is

\[
  \mathfrak C_{\mathcal E,V}:
  J\longmapsto
  \{\text{all finite quantum-clock outcome laws in }V\}.   \tag{1}
\]

It is a functor because source restriction, laboratory inclusion, clock relabelling, and ordered
composition of interventions act on the data.

## Continuum Chronometric Equivalence Theorem — target

Let \(\mathcal E_1,\mathcal E_2\) belong to the admissible class below and let \(V_1,V_2\) be
operationally identified clock laboratories. Then

\[
  \boxed{
  \mathfrak C_{\mathcal E_1,V_1}
  \cong
  \mathfrak C_{\mathcal E_2,V_2}
  \quad\Longleftrightarrow\quad
  \mathcal E_1|_{\mathbb D(V_1)}
  \simeq
  \mathcal E_2|_{\mathbb D(V_2)}.}                         \tag{2}
\]

Here \(\mathbb D(V)\) is the maximal causal diamond probed from and returned to \(V\).
Equivalence on the right means:

- a time-orientation-preserving diffeomorphism of causal diamonds;
- an invertible local physical field redefinition fixing calibrated source and reporter channels;
- gauge equivalence;
- equality of the local Euler--Lagrange operator germ;
- quotient by boundary terms and topological terms with identically zero local variation.

Decoupled sectors are not silently quotiented. They violate admissibility unless a clock channel
couples to them.

## Admissible continuum class

The theorem is not claimed across arbitrary formal Lagrangians. Initial target class:

1. smooth, time-oriented, globally hyperbolic four-manifolds;
2. local real-analytic second-order quasilinear Euler--Lagrange systems after a specified
   hyperbolic gauge fixing;
3. well-posed retarded source-to-solution map for sufficiently small compact sources;
4. independently calibrated sources satisfying the physical conservation constraints;
5. local source-jet controllability on the reachable solution germ;
6. a detector-complete clock laboratory whose couplings separate the local observable algebra;
7. no propagating clock-dark sector;
8. proper-time or volume calibration sufficient to remove the residual conformal scale;
9. dynamical locality: no nontrivial sector is invisible to every relative source response.

The class includes a first milestone consisting of Einstein gravity coupled to scalar reference and
probe fields under the hypotheses of the nonlinear Lorentzian inverse theorems. Higher-curvature
and scalar--tensor theories enter only after their extra characteristics and modes are included in
the clock laboratory.

## Exact proof architecture

### A. Quantum clocks reconstruct continuum observations

For an Unruh--DeWitt-type clock on a timelike trajectory \(\gamma\), a leading transition
functional is

\[
  P_{J,\Omega}[\chi]
  =\lambda^2\!\int d\tau\,d\tau'\,
  \chi(\tau)\chi(\tau')e^{-i\Omega(\tau-\tau')}
  W_J(\gamma(\tau),\gamma(\tau'))+O(\lambda^4).            \tag{3}
\]

Transition probability `(3)` alone is not used for injectivity. A controlled Ramsey clock applied
to a local unitary \(U\) reads \(\operatorname{Re}\omega(U)\) and
\(\operatorname{Im}\omega(U)\) in its two equatorial quadratures. Sequential controlled pulses
recover \(\omega(U_1\cdots U_n)\) exactly, and derivatives of regular local-unitary families recover
ordered \(n\)-point distributions. The phase-recovery algebra is proved on paper in
`../2-fully-proven/new_scientific_knowledge/chronometric-continuum-operator-rigidity.md`.

For a Weyl probe sector, opposite controlled orderings obey the exact state-independent law

\[
  W(\lambda f)W(\eta h)W(\lambda f)^{-1}W(\eta h)^{-1}
  =
  e^{-i\lambda\eta E(f,h)}I.
\]

Ramsey quadratures recover the two ordered complex expectations, and the derivative of the
continuously calibrated phase at zero recovers \(E(f,h)\) without a logarithm branch. This algebra
is unconditional in Lean. Paper proof:
`../2-fully-proven/new_scientific_knowledge/ramsey-weyl-causal-phase-law.md`.

**Open core A:** realize a separating family of controlled local unitaries by compactly supported
relativistic clock/probe couplings, including gauge-invariant gravitational reporters,
backreaction, and continuum test-function topology. Phase loss is closed; relativistic
controllability is not.

### B. Continuum clock observations reconstruct spacetime

Primary Lorentzian inverse results already show:

- active nonlinear Einstein--scalar measurements near an observer worldline determine topology,
  differentiable structure, and conformal geometry of the optimal causal diamond; in a vacuum
  unknown region they determine the metric;
- nonlinear wave observations on a single timelike curve can determine conformal structure;
- chronological order plus number/volume determines a smooth spacetime up to isometry under
  stated hypotheses.

**New bridge B:** replace direct field observations in those theorems by only the clock outcome
functor using A, and close conformal scale from physical clock calibration rather than assuming the
metric in the laboratory.

The exact scale mechanism is now identified. For two minimally coupled scalar clock species with
distinct calibrated squared masses \(\mu_1\neq\mu_2\), conformal conjugation by
\(\widetilde g=e^{2\sigma}g\) gives effective potentials

\[
  V_{\mu_i}^\sigma
  =
  \mu_i e^{2\sigma}
  -a\Box_g\sigma-a^2|d\sigma|_g^2,
  \qquad a=(d-2)/2.
\]

Therefore

\[
  e^{2\sigma}
  =
  \frac{V_{\mu_1}^\sigma-V_{\mu_2}^\sigma}{\mu_1-\mu_2}.    \tag{3a}
\]

The shared derivative defect cancels pointwise. Paper proof:
`../2-fully-proven/new_scientific_knowledge/two-species-conformal-clock-scale-law.md`.
The algebraic separation is unconditional in Lean.

A stronger operational route now removes absolute amplitude calibration. If complete measured
Green operators have common unknown receiver/source gains,

\[
  \widehat G_\mu=A\,G_\mu\,B,
\]

then their inverse operators satisfy

\[
  Q_{\mu_1}-Q_{\mu_2}
  =
  (\mu_1-\mu_2)B^{-1}A^{-1}.                              \tag{3b}
\]

The difference isolates the unknown endpoint-gain product. Since
\(\sigma_2(Q_\mu)=(ab)^{-1}g^{-1}\), dividing the measured principal symbol by the recovered gain
gives the full metric. This noncommutative operator cancellation and the pointwise
calibration/metric injectivity theorem are unconditional in Lean. Paper proof:
`../2-fully-proven/new_scientific_knowledge/two-mass-self-calibrating-clock-metric-law.md`.

**Open clock-to-propagator bridge:** prove that the restricted backreacting clock functor
reconstructs the two complete dressed Green operators on a common support domain, and that the two
species share or have known relative endpoint calibration. Wavefront locations alone are
insufficient; complex amplitude and principal-symbol data are essential.

The same cancellation gives a falsifiable locality law: within the minimal common-metric probe
class, the inverse-response difference is purely zeroth order and diagonal-supported. With DA
instrument gain it cannot be HT. A derivative, nonlocal, or HT inverse residual falsifies at least
one single-metric/locality/calibration premise. Paper proof:
`../2-fully-proven/new_scientific_knowledge/two-clock-locality-law.md`.

### C. All source responses reconstruct the gravitational operator

Write the gauge-fixed equation and response map as

\[
  \mathcal E(\Psi)=J,\qquad \Psi=\mathcal S(J).             \tag{4}
\]

On a locally invertible reachable germ,

\[
  \mathcal E=\mathcal S^{-1}.                              \tag{5}
\]

For pure metric gravity, the stronger branch-safe result is already paper-proved. Let
\(\mathsf Q(g)(x,v)=g_x(v,v)\) be the signed infinitesimal squared-clock field and define

\[
  \Gamma_{\rm chr}(\mathcal E)
  =\{(\mathcal E(g),\mathsf Q(g)):g\in\mathcal G\}.          \tag{5a}
\]

Polarization makes \(\mathsf Q\) injective. Therefore

\[
  \Gamma_{\rm chr}(\mathcal E_1)=\Gamma_{\rm chr}(\mathcal E_2)
  \quad\Longleftrightarrow\quad
  \mathcal E_1=\mathcal E_2.                               \tag{5b}
\]

This needs neither real analyticity nor a unique source-to-solution map and retains every nonlinear
solution branch. It identifies the complete metric operator once full continuum chronometric data
are available.

**Open core C:** lift `(5b)` from fixed relational labels and a gauge-fixed pure metric operator to
the diffeomorphism/gauge/local-field-redefinition quotient, then prove restricted laboratory data
determine \(\Gamma_{\rm chr}\) throughout the reachable causal diamond. A Fréchet jet theorem is
now optional machinery for partial data, not the logical core of full operator recovery.

### D. Equality and converse

A--C give the reverse implication in `(2)`. The forward implication follows from local covariance:
diffeomorphism, gauge transformation, allowed field redefinition, and a locally variationally
trivial action term cannot change calibrated clock outcome laws.

## What is genuinely new

The following are prior art and cannot be sold as the discovery:

- causal order or commutator support determines conformal geometry;
- order plus number determines one smooth spacetime;
- a clock compass measures curvature;
- relative Cauchy evolution differentiates with respect to metric perturbations;
- nonlinear source-to-solution data reconstructs geometry or selected coefficients;
- relational scalar fields can be used as clocks and rods.

The new claim is the biconditional `(2)` for the **full gravitational operator**, with direct field
observations replaced by quantum-clock outcomes and with all residual equivalences classified.
If only the metric of one solution is recovered, the theorem has failed.

## Hypertranscendence enters natively

The source-response jet has a differential-algebraic species filtration. Complete reporter
inversion and nondegenerate exterior propagation must preserve that filtration. Existing exact
strong-field witnesses include:

1. the AdS\(_2\) scalar-clock odd-DA/even-HT/noninteger-HT species law;
2. hypertranscendence of the exact extremal RN modified-Bessel intensity scan.

These are not the definition of gravity. They are theory-sensitive invariants of the continuum
chronometric functor in `(1)`.

## Hostile kill conditions

The universal form dies if any survives after the equivalence class is fixed:

1. two inequivalent local gravitational operators have identical complete clock functors;
2. a propagating sector can remain invisible to every physically allowed clock coupling;
3. conservation constraints prevent source-jet controllability;
4. clock probabilities recover only symmetrized noise and not causal orientation;
5. proper-time data in \(V\) cannot remove the conformal ambiguity in \(\mathbb D(V)\);
6. different nonlinearities have the same all-order clock data because of a nonlocal duality not
   represented by an allowed local field redefinition;
7. detector backreaction destroys injectivity rather than supplying additional calibrated
   interventions;
8. equality of the reachable response germ does not determine the local operator away from that
   germ;
9. the result reduces to defining “same theory” as “same observations.”

## Lean dependency ledger

Already unconditional:

- exact Green-element fracture and inverse operator change;
- complete finite clock reporter reconstruction;
- all finite source packets and ordered intervention words;
- formal compositional inverse uniqueness and coefficient-freeness;
- AdS\(_2\) strong-field differential-species witness.

Missing continuum machinery:

- test-function and distributional polarization/injectivity for clock detector kernels;
- globally hyperbolic support categories and retarded/advanced Green operators;
- Lorentzian causal-order/conformal reconstruction;
- volume/proper-time scale recovery;
- Fréchet source jets and analytic inverse operator reconstruction;
- diffeomorphism, gauge, local field-redefinition, and variationally trivial quotients;
- microlocal nonlinear wave-interaction reconstruction used by the Einstein--scalar theorem.

No continuum claim will be labelled Lean-proved until these dependencies are formalized without
`axiom`, `sorry`, `admit`, `opaque`, or `unsafe`.

## Primary SOTA inputs

- Y. Kurylev, M. Lassas, L. Oksanen, and G. Uhlmann,
  *Inverse problem for Einstein-scalar field equations*,
  <https://arxiv.org/abs/1406.4776>.
- M. Nursultanov, L. Oksanen, and L. Tzou,
  *Determining Lorentzian manifold from non-linear wave observation at a single point*,
  <https://arxiv.org/abs/2310.06925>.
- M. Braun, *Spacetime reconstruction by order and number*,
  <https://arxiv.org/abs/2507.01907>.
- M. Lassas, G. Uhlmann, and Y. Wang,
  *Inverse problems for semilinear wave equations on Lorentzian manifolds*,
  <https://arxiv.org/abs/1606.06261>.
- R. Brunetti, K. Fredenhagen, and R. Verch,
  *The generally covariant locality principle*,
  <https://arxiv.org/abs/math-ph/0112041>.
- C. J. Fewster and R. Verch,
  *Dynamical locality and covariance*,
  <https://arxiv.org/abs/1106.4785>.
- K. Giesel, V. Kabel, and W. Wieland,
  *Linking Edge Modes and Geometrical Clocks in Linearized Gravity*,
  <https://arxiv.org/abs/2410.17339>.
- P. Stefanov, G. Uhlmann, and A. Vasy,
  *Determination of the spacetime from local time measurements*,
  <https://arxiv.org/abs/1412.1350>.
- C. J. Fewster, I. Jubb, and M. H. Ruep,
  *Asymptotic measurement schemes for every observable of a quantum field theory*,
  <https://arxiv.org/abs/2203.09529>.
- M. Rotondo,
  *A Detector-Based Inference Framework for Quantum Theory and Spacetime Geometry*,
  <https://arxiv.org/abs/2604.10349>.

## Next proof obligations

1. Prove relativistic controlled-clock realization of the exact Ramsey tomography lemma.
2. Select Einstein--scalar inverse theorem hypotheses verbatim and map each direct observation to
   a clock experiment.
3. Formalize squared-interval injectivity and branch-safe graph rigidity in Lean.
4. Lift complete-data operator rigidity to diffeomorphism, gauge, and field-redefinition quotients.
5. Construct an explicit counterexample search over dual, topological, and clock-dark sectors.
5. Formalize A and C before importing deeper Lorentzian reconstruction.

## Log

- 2026-07-28 — continuum biconditional `(2)` fixed as Nature-scale apex.
- 2026-07-28 — finite algebra and black-hole special functions demoted to dependencies and
  witnesses; neither counts as solving continuum gravity.
- 2026-07-28 — narrative gate tightened after hostile lay-reader audit. Sole publication claim is
  now the causal-susceptibility equivalence theorem
  \(\mathfrak R_{\mathcal E_1}\cong\mathfrak R_{\mathcal E_2}\iff
  \mathcal E_1\simeq\mathcal E_2\), with
  \(\mathfrak R_{\mathcal E}:J\mapsto\Omega_J\). Public headline:
  **“Matter rewrites which events can cause which. That rewriting is gravity.”** Metric
  self-calibration, probe subtraction, conservation balancing, and HT are Methods/falsifiers,
  not separate headline claims.
- 2026-07-28 — exact finite-coupling probe-backreaction subtraction closed on paper and in Lean.
  For target/probe block operator
  \(T_\mu=\left(\begin{smallmatrix}P_\mu&R\\S&Q\end{smallmatrix}\right)\), the exact coupled probe
  response is \(H_\mu=(Q-SG_\mu R)^{-1}\). With common unknown endpoint gains,
  \[
    \widehat H_{\rm off}^{-1}-\widehat H_{\mu,\rm on}^{-1}
    =B^{-1}S\,G_\mu\,RA^{-1}.
  \]
  Thus switching coupling off/on turns complete probe-only data into precisely the
  endpoint-dressed hidden Green operator required by two-mass self-calibration. Schur inversion
  is `[REDISCOVERED]`; its exact composition with local QFT measurement, two masses, metric
  recovery, nonlinear graph rigidity, and the HT locality falsifier is `[CANDIDATE-NEW]`.
  Linear target--probe backreaction is included to all coupling orders. Nonlinear metric
  backreaction, conserved gauge-invariant source completeness, finite-resolution stability, and
  realistic separating rather than invertible compact couplings remain open.
- 2026-07-28 — conservation-source obstruction reduced to one exact coframe condition. If the
  scalar clock gradients synthesize the cotangent space, the adaptive source
  \(a_b=\Theta^{-1}(-b)\) cancels every stress-divergence defect \(b\). A separately modelled
  signal channel survives unchanged and jointly injectively. In 4D, four independent clock
  gradients pay the four conservation constraints; a fifth channel is required only when an
  additional independently prescribed scalar signal is demanded. This mechanism is
  `[REDISCOVERED]` from Einstein--scalar adaptive-source work and is recorded as
  `[DEPENDENCY-CLOSURE]`, not new physics. Physical actuation, global nondegeneracy, and nonlinear
  gauge-compatible source construction remain open.
