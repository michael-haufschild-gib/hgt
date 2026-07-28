# Matter rewrites which events can cause which. That rewriting is gravity.

- **ID:** `chronometric-causal-susceptibility-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL PHYSICS LAW / TIME / CAUSALITY / GRAVITY / QUANTUM OBSERVABLES
- **Status:** conjectural universal apex; exact causal-fracture algebra, finite intervention
  tomography, and first black-hole complexity corollary formalized; clock-only nonlinear
  reconstruction theorem open
- **Continuum theorem target:**
  `continuum-chronometric-equivalence-theorem.md`

## Headline

> **Matter rewrites which events can cause which. That rewriting is gravity.**

## One paper, one law

This paper must not present metric rigidity, two-mass calibration, probe Schur subtraction,
conservation balancing, black-hole HT, and inverse geometry as co-equal discoveries. Those are
Methods, controls, or falsifiers for one claim:

\[
  \boxed{
  \mathfrak R_{\mathcal E_1}\cong\mathfrak R_{\mathcal E_2}
  \quad\Longleftrightarrow\quad
  \mathcal E_1\simeq\mathcal E_2,}
  \qquad
  \mathfrak R_{\mathcal E}:J\longmapsto\Omega_J.             \tag{0}
\]

Here \(J\) is a controlled matter intervention and \(\Omega_J\) is the complete relational
order-phase of clock comparisons after that intervention. The right side identifies complete
continuum gravity laws up to diffeomorphism, gauge, physical local field redefinition, and
variationally trivial terms.

Public worldview:

> Spacetime is not a stage on which clocks sit. Spacetime is the complete pattern of which clocks
> can influence which. Matter changes that pattern. Gravity is the rule of that change.

Every result kept in the main text must prove one arrow of `(0)`, supply one finite experimental
readout of \(\mathfrak R\), or distinguish \(\mathfrak R\) from a rival theory. Everything else
belongs in Methods or Supplementary Information.

Technical form:

> **Spacetime is the complete orientation algebra of clock comparisons. Gravity is its causal
> susceptibility to an independently calibrated stress intervention.**

This is deliberately stronger than saying clocks measure a pre-existing metric. The candidate law
defines geometry and gravity operationally from one observable:

\[
  \Omega_{ij}[J](x,y)
  :=\frac{1}{i\hbar}[C_i(x;J),C_j(y;J)],
  \qquad
  \chi_{ij|A}(x,y;z)
  :=\left.\frac{\delta\Omega_{ij}[J](x,y)}
    {\delta J^A(z)}\right|_{J=0}.                         \tag{1}
\]

Here \(C_i\) are complete clock-compass reporters and \(J^A\) is a compactly supported,
independently calibrated matter/stress intervention satisfying the physical conservation
constraints. The antisymmetric carrier \(\Omega\), not the symmetrized noise kernel, retains the
orientation “which event can affect which.” The proposed universal identification is

\[
  \boxed{\text{geometry}=[\Omega],\qquad
         \text{gravity}=[\chi]=
         \left[\frac{\delta\,(\text{causal orientation})}
         {\delta\,(\text{matter})}\right].}               \tag{2}
\]

Brackets denote the appropriate diffeomorphism, gauge, reporter-calibration, and local
field-redefinition quotient. Proper-time calibration must restore the conformal scale.

## Why this could be a law rather than a slogan

For a Green-hyperbolic reporter equation \(P_g C=0\), compact metric change gives the exact
resolvent identity

\[
  E_{g'}-E_g=-E_g(P_{g'}-P_g)E_{g'},                       \tag{3}
\]

with retarded or advanced Green operators in the correct support class. At first order,

\[
  \delta_J E_g
  =-E_g\,(D_gP)[\delta_J g]\,E_g,\qquad
  \delta_J g=(D_g\mathcal E)^{-1}\delta_J T,               \tag{4}
\]

after gauge fixing, where \(\mathcal E(g,T)=0\) is the gravitational field equation. Equation
`(4)` is the causal-response chain rule behind `(2)`. A complete reporter left inverse should
recover the gauge class of \((D_gP)[\delta_Jg]\), while nonlinear source jets recover interaction
vertices invisible to the linearized map.

The required theorem is not merely `(3)`. It is injectivity:

\[
  \mathfrak C_{(M,g,\Phi)}
  :J\longmapsto
  \{\text{all finite clock-product laws in the laboratory region}\}
                                                               \tag{5}
\]

must determine the causal diamond, full metric after proper-time calibration, quantum curvature
product law, and gravitational response functional up to the stated equivalences.

The non-negotiable continuum form is now the biconditional

\[
  \mathfrak C_{\mathcal E_1}\cong\mathfrak C_{\mathcal E_2}
  \quad\Longleftrightarrow\quad
  \mathcal E_1\simeq\mathcal E_2,                          \tag{5a}
\]

on the probed causal diamonds. The right side is equality of the full local gravitational operator
up to diffeomorphism, gauge, physical local field redefinition, and variationally trivial
boundary/topological terms. Recovering only one background metric does not satisfy `(5a)`.

The exact algebraic portion of `(3)`--`(4)` is now Lean-formalized in
`ChronometricCausalSusceptibility.lean`: Green-element fracture and operator recovery hold in every
noncommutative ring, and a complete reporter left inverse reconstructs every finite source
difference, every finite source stencil, and every ordered intervention word. This is not yet the
analytic support, gauge, conservation, or nonlinear-inverse theorem.

## Exact new strong-field corollary already obtained

For the scalar-curvature mode of \(R+\alpha R^2\) gravity on a near-extremal
Reissner--Nordström throat,

\[
  g_\ell^2=(2\ell+1)^2+\frac{2Q^2}{3\alpha}.                \tag{6}
\]

The exact renormalized AdS₂ clock response obeys the unconditional species law

\[
  \boxed{
  \begin{array}{c|c}
  g_\ell>0 & \text{differential species of the clock response}\\ \hline
  g_\ell\in2\mathbb N+1 & \mathrm{DA}\\
  g_\ell\in2\mathbb N   & \mathrm{HT}\text{ after every finite local subtraction}\\
  g_\ell\notin\mathbb Z & \mathrm{HT}.
  \end{array}}                                             \tag{7}
\]

Lean proves exact odd pole cancellation and nonvanishing, exact even Laurent extraction,
scheme-independent HT of the whole meromorphic finite part, and exact-normalization noninteger
HT. The package theorem is `ads2GravitationalClockSpeciesLaw` in
`formal/GaloisForLFunctions/HTGeometry/AdS2RenormalizedScalarClockParity.lean`.

Public translation:

> **A black hole can change the mathematical species of time. Adding one resonance can change a
> clock from a finite differential law to a response no finite algebraic differential equation
> can satisfy.**

Equation `(7)` is the first nontrivial test of `(2)`: gravitational parameters alter not only
clock rates or poles but the differential-algebraic species of the complete response.

## Hostile novelty audit

The headline alone is **not new**:

1. Pauli--Jordan commutators and wavefront sets already encode causal propagation for
   Green-hyperbolic quantum fields.
2. Brunetti--Fredenhagen--Verch relative Cauchy evolution already describes algebraic response to
   compact metric changes; its metric derivative yields stress--energy.
3. Fewster--Verch dynamical locality already compares kinematic and response-defined local
   subtheories.
4. Kurylev--Lassas--Oksanen--Uhlmann already prove that controlled nonlinear
   Einstein--scalar measurements can determine topology, differentiable structure, and conformal
   geometry of a causal diamond, and the metric in a vacuum region.
5. Integer-\(\nu\) holographic scalar correlators are already known to acquire logarithmic
   terms after local counterterm subtraction.

Therefore a paper that merely renames commutator support, relative Cauchy evolution, inverse
geometry, or conformal logarithms as “gravity from clocks” fails novelty.

Candidate-new intersection:

1. one **finite operational clock-compass reporter net**, rather than direct observation of
   \((g,\Phi)\), reconstructs causal orientation, full metric scale, nonlinear source response,
   and noncommutative curvature products;
2. equality of complete clock intervention functors is equivalent to diffeomorphism plus physical
   field redefinition, not merely equality of one background metric;
3. source response carries a formal differential-Galois filtration preserved by complete
   reporting and nondegenerate exterior observation;
4. the first exact gravitational sector in that filtration obeys the odd-DA/even-HT/noninteger-HT
   law `(7)`.

## Nature editorial gate

Nature requires original research of outstanding importance and interdisciplinary interest; desk
review additionally asks for novel, arresting results with immediate and far-reaching
implications. The current package does not yet pass that gate. A submission needs all of:

1. a clock-only reconstruction theorem for `(5)`, not a composition hidden behind direct field
   observations;
2. an observable consequence of \(\chi\) that separates gravitational theories;
3. a finite-resolution inference protocol or analogue/astrophysical observable for `(7)`;
4. a collision-complete priority audit across AQFT, Lorentzian inverse problems, quantum reference
   frames, black-hole response, holographic renormalization, and modified-gravity ringdown;
5. a schematic readable without differential algebra.

## Kill conditions

Retire or narrow the universal claim if any survives:

1. two inequivalent gravitational theories have identical complete clock intervention functors;
2. proper-time and clock-product data do not remove residual conformal or field-redefinition
   ambiguity;
3. conservation constraints prevent source completeness needed for inverse reconstruction;
4. reporter backreaction makes `(5)` non-identifiable without direct field access;
5. \(\chi\) is exactly equivalent to already known relative Cauchy evolution with no new
   operational content;
6. DA/HT species cannot produce any finite-resolution falsifiable statistic;
7. exact exterior propagation erases or contaminates the throat species law beyond recoverability.

## Next mathematical obligations

1. State precise category and equivalence relation for the intervention functor `(5)`.
2. Construct analytic retarded/advanced reporter Green operators and prove the Lean algebraic
   identities apply on the correct support domains.
3. Build the clock-only bridge to the nonlinear Einstein--scalar inverse theorem.
4. Derive a finite-order falsification hierarchy for bounded DA order/degree without pretending
   finite data can certify unrestricted HT.
5. Extend `(7)` beyond the scalaron to the maximal class of neutral AdS₂ gravitational modes and
   find the first counterexample.

## Primary collisions and inputs

- R. Brunetti, K. Fredenhagen, and R. Verch,
  *The generally covariant locality principle -- A new paradigm for local quantum physics*,
  <https://arxiv.org/abs/math-ph/0112041>.
- C. J. Fewster and R. Verch,
  *Dynamical locality and covariance: What makes a physical theory the same in all spacetimes?*,
  <https://arxiv.org/abs/1106.4785>.
- Y. Kurylev, M. Lassas, L. Oksanen, and G. Uhlmann,
  *Inverse problem for Einstein-scalar field equations*,
  <https://arxiv.org/abs/1406.4776>.
- T. Faulkner, H. Liu, J. McGreevy, and D. Vegh,
  *Emergent quantum criticality, Fermi surfaces, and AdS2*,
  <https://arxiv.org/abs/0907.2694>.
- K. Skenderis, *Lecture Notes on Holographic Renormalization*,
  <https://arxiv.org/abs/hep-th/0209067>.

## Log

- 2026-07-28 — rejected “gravity is clock disagreement” as a novelty claim by itself after
  collisions with causal commutators, relative Cauchy evolution, and nonlinear inverse geometry.
- 2026-07-28 — retained stronger operational apex `(2)` and made clock-only completeness plus
  theory-identifying causal susceptibility explicit open core.
- 2026-07-28 — closed exact black-hole response species law `(7)` in Lean as first sharp
  strong-field corollary.
- 2026-07-28 — formalized exact causal fracture/operator recovery plus complete finite
  clock-intervention packet and ordered-word reconstruction.
