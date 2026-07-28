# Black holes split gravitational time into two mathematical species

- **ID:** `scalaron-horizon-clock-complexity-phase-law`
- **Stage:** 1-in-progress
- **Type:** PHYSICS LAW / MODIFIED GRAVITY / BLACK HOLES / CLOCK RESPONSE /
  HYPERTRANSCENDENCE
- **Status:** exact throat law, normalized-core boundary, and even-resonance HT survivor derived;
  full Laurent finite-part formalization, asymptotic clock-compass protocol, and unrestricted
  exterior matching remain open
- **Formal core:**
  `formal/GaloisForLFunctions/HTGeometry/NearHorizonScalaronClockBoundary.lean`;
  `formal/GaloisForLFunctions/HTGeometry/AdS2RenormalizedScalarClockParity.lean`

## Public claim

> **A black hole can change the mathematical species of time.**

More precise:

> **As hidden gravitational mass is tuned, a black-hole clock alternates between finite-law odd
> resonances and irreducibly hypertranscendental even resonances; away from every resonance it is
> hypertranscendental again.**

This is a strong-field prediction inside the broader chronometric-intervention program. It is not
yet the ontology-level headline “gravity is the response law of the clock algebra,” but it supplies
the first source-selected HT gravitational channel that survives a nondegenerate projective
readout.

## Physical derivation

Consider four-dimensional

\[
  f(R)=R+\alpha R^2
\]

gravity coupled to Maxwell theory. Maxwell stress is traceless, and every Einstein--Maxwell
solution with \(R=0\), including Reissner--Nordström, remains an exact background. The trace of the
modified field equation gives, in a trace-free region,

\[
  (6\alpha\,\Box-1)R=0.
\]

Linearizing about \(R=0\) therefore makes the gauge-invariant curvature scalar
\(\delta R\) a propagating scalaron:

\[
  (\Box-m_s^2)\delta R=0,\qquad m_s^2=\frac{1}{6\alpha}.       \tag{1}
\]

For an extremal Reissner--Nordström throat
\(\mathrm{AdS}_2(Q)\times S^2(Q)\), expand

\[
  \delta R=\sum_{\ell m}\phi_{\ell m}(x_{\mathrm{AdS}_2})Y_{\ell m}.
\]

Each mode is a neutral massive scalar on \(\mathrm{AdS}_2\) with

\[
  M_\ell^2=m_s^2+\frac{\ell(\ell+1)}{Q^2}.                   \tag{2}
\]

Its conformal half-gap and full gap are

\[
  \nu_\ell
    =\sqrt{\frac14+Q^2M_\ell^2},\qquad
  g_\ell=2\nu_\ell
    =\sqrt{(2\ell+1)^2+\frac{2Q^2}{3\alpha}}.                \tag{3}
\]

At finite throat temperature, define the normalized frequency-dependent retarded core

\[
  {\cal G}_{\ell}^{\rm IR}(z)
  =
  \frac{\Gamma\!\left(z+\frac{1+g_\ell}{2}\right)}
       {\Gamma\!\left(z+\frac{1-g_\ell}{2}\right)},
  \qquad z=-\frac{i\omega}{2\pi T}.                          \tag{4}
\]

The corpus Gamma-orbit theorem gives the exact **normalized-core** dichotomy:

\[
\begin{aligned}
  {\cal G}_{\ell}^{\rm IR}\text{ is DA over }\mathbb C(z)
  &\Longleftrightarrow g_\ell\in\mathbb Z,\\
  {\cal G}_{\ell}^{\rm IR}\text{ is HT over }\mathbb C(z)
  &\Longleftrightarrow g_\ell\notin\mathbb Z.                \tag{5}
\end{aligned}
\]

Thus every integer candidate obeys the discrete resonance equation

\[
  3\alpha\left[k^2-(2\ell+1)^2\right]=2Q^2,
  \qquad k\in\mathbb Z.                                     \tag{6}
\]

For nonzero \(Q\), \(k=2\ell+1\) is impossible. Generic stable \(\alpha>0\) lies off every
resonance and produces an HT curvature response.

### Physical normalization changes the integer branch

Equation (D27) of Faulkner--Liu--McGreevy--Vegh contains the factor omitted by the normalized
core:

\[
  {\cal A}(g)
  =
  (4\pi T)^g
  \frac{\Gamma(-g)}{\Gamma(g)}
  \frac{\Gamma\!\left(\frac{1+g}{2}\right)}
       {\Gamma\!\left(\frac{1-g}{2}\right)}.                 \tag{7}
\]

This factor creates a parity law.

For \(g=2n+1\), the pole of \(\Gamma(-g)\) is cancelled by the pole of
\(\Gamma((1-g)/2)=\Gamma(-n)\). The finite coefficient is nonzero, and the quotient in `(4)` is
a polynomial of degree \(2n+1\). The complete response is therefore DA.

For \(g=2n>0\), \(\Gamma((1-g)/2)=\Gamma(1/2-n)\) is finite and nonzero, so \({\cal A}\) has a
simple pole. Its residue multiplies the degree-\(2n\) polynomial

\[
  P_{2n}(z)=
  \frac{\Gamma(z+n+1/2)}{\Gamma(z-n+1/2)}.
\]

That divergence is local and removable by a local counterterm. The finite part necessarily
contains

\[
  P_{2n}(z)
  \left[
    \psi\!\left(z+\frac12-n\right)
    +
    \psi\!\left(z+\frac12+n\right)
  \right].                                                   \tag{8}
\]

The digamma terms have integer separation \(2n\) and total orbit charge \(2\), not zero. Their
sum is HT. Its polynomial coefficient is nonzero, and adding any local polynomial or rational
counterterm cannot erase HT. The resulting candidate physical boundary is therefore

\[
\boxed{
\begin{aligned}
  {\cal G}^{\rm ren}_\ell \text{ is DA}
    &\Longleftrightarrow g_\ell\in 2\mathbb Z+1,\quad g_\ell>0,\\
  {\cal G}^{\rm ren}_\ell \text{ is HT}
    &\Longleftrightarrow g_\ell>0\ \text{and}\ 
      g_\ell\notin 2\mathbb Z+1.                             \tag{9}
\end{aligned}}
\]

`(9)` is the stronger target, not yet the fully formalized physical theorem. Lean now proves the
static Gamma parity selector, HT of the even-resonance digamma carrier, and invariance under every
nonzero DA normalization and DA local counterterm. Formal Laurent identification of `(8)` remains
open.

## Exterior matching and observable clock

Low-frequency throat matching has projective form

\[
  G_{\rm full}
  =
  K\,
  \frac{B_+(\omega)+B_-(\omega){\cal G}^{\rm IR}_\ell(\omega)}
       {A_+(\omega)+A_-(\omega){\cal G}^{\rm IR}_\ell(\omega)}. \tag{10}
\]

New unconditional Lean machinery proves that every nondegenerate Möbius matching whose
coefficients lie in the declared rational differential base preserves `(5)` exactly. The same
boundary survives the Wigner--Smith/logarithmic response clock

\[
  \tau_\ell(z)=\partial_z\log G_{\rm full}(z).               \tag{11}
\]

This closes constant matching and rational frequency-dependent matching. It does **not** classify
the exact unknown analytic connection coefficients of a generic asymptotically flat exterior.
Two honest observables remain available:

1. the universal IR scaling function extracted after analytic-background subtraction;
2. a full exterior response once the connection coefficients are proved DA and nondegenerate.

## Relation to Einstein gravity

Do not say that Einstein gravity is the \(\alpha=0\) integer point of `(6)`. At \(\alpha=0\) the
scalaron channel disappears rather than becoming a finite-mass integer-gap mode. Correct
comparison is:

- Einstein gravity has no propagating Ricci-scalar channel in trace-free vacuum;
- \(R+\alpha R^2\) gravity adds one;
- when present, its normalized core is DA at `(6)`;
- after physical renormalization, current evidence gives DA only on the positive odd subset of
  `(6)`, while positive even resonances retain HT memory.

Separate literature shows integer conformal weights for broad symmetry-preserving massless
gravitational/electromagnetic sectors of near-extreme horizons. That supports a possible larger
“Einstein integer orbit versus extra-mode generic HT” classifier, but no universal theorem over
all Einstein perturbations is claimed here.

## Why this is not the earlier charged-probe result

The corpus already classified a charged scalar probe of Kerr--Newman. The present carrier is
different:

1. \(\delta R\) is a gravitational degree of freedom of the modified field equations;
2. it is gauge invariant on the \(R=0\) background;
3. a complete clock compass reconstructs Ricci scalar from its Riemann reporters;
4. independently controlled trace-matter interventions can source the channel;
5. the projective matching and directly observable logarithmic delay preserve its HT phase.

The remaining gap is experimental synthesis of `(8)` from the same finite clock-compass reporter
net used for geometry and quantum-product tomography.

## Novelty audit

Primary literature separately supplies:

- scalaron dynamics and mass in \(f(R)\) black-hole perturbation theory;
- finite-temperature \(\mathrm{AdS}_2\) Gamma response and inner/outer Möbius matching;
- exact near-horizon Einstein--Maxwell scattering;
- integer conformal weights in important symmetry-preserving Einstein sectors.

Searches for “hypertranscendental black hole response,” “differentially algebraic black hole Green
function,” “differential Galois black hole response conformal weight,” and “AdS2 integer gap
digamma parity” found no prior differential-algebraic phase classification matching
`(5)`--`(11)`. This is an absence-of-hit
verdict, not proof of priority.

## Kill conditions

Retire or narrow the physics claim if:

1. the scalaron is not independently sourceable or reconstructible by the declared clocks;
2. the even-resonance Laurent residue or its gap derivative vanishes after physical
   normalization;
3. exact exterior coefficients are neither DA nor removable by scaling-background subtraction;
4. the near-extremal scaling window has no operational frequency range;
5. finite bandwidth makes the DA/HT distinction non-identifiable even in principle;
6. a prior source already proves the same differential-complexity classifier.

## Formal status

Unconditionally checked in Lean:

- scalaron mass/gap algebra and integer-resonance equation;
- base resonance exclusion at nonzero throat radius;
- exact Gamma quotient;
- DA iff integer gap and HT iff noninteger gap;
- no-resonance implies HT;
- nondegenerate rational Möbius matching preserves the boundary;
- matched Wigner--Smith clock preserves the boundary.
- odd gaps and only odd gaps send the static normalization denominator to a Gamma pole;
- the exact gap derivative of the normalized quotient exposes the endpoint-digamma sum, and at
  even gap it is exactly one half of the displayed even-resonance carrier;
- the finite part of any simple-pole normalization times a differentiable response contains
  exactly residue times gap derivative plus a regular local multiple of the response;
- the exact AdS₂ normalization has the declared nonzero simple-pole residue at every positive even
  gap;
- every even-resonance digamma finite-part carrier is HT;
- nonzero DA normalization and arbitrary DA local counterterms preserve that HT carrier.

Physical identifications `(1)`--`(4)`, exact normalization `(7)`, and Laurent identification `(8)`
remain source-derived mathematics outside Lean; they are not encoded as axioms.

## Primary sources

- Y. S. Myung, T. Moon, and E. J. Son, *Stability of f(R) black holes*,
  <https://arxiv.org/abs/1103.0343>.
- T. Moon, Y. S. Myung, and E. J. Son, *f(R) Black holes*,
  <https://arxiv.org/abs/1101.1153>.
- T. Faulkner, H. Liu, J. McGreevy, and D. Vegh,
  *Emergent quantum criticality, Fermi surfaces, and AdS2*,
  <https://arxiv.org/abs/0907.2694>.
- A. P. Porfyriadis,
  *Scattering of gravitational and electromagnetic waves off AdS2 × S2 in extreme
  Reissner--Nordström*, <https://arxiv.org/abs/1805.12409>.
- A. P. Porfyriadis,
  *Near-AdS2 perturbations and the connection with near-extreme Reissner--Nordström*,
  <https://arxiv.org/abs/1806.07097>.
- K. Murata, *Conformal weights in the Kerr/CFT correspondence*,
  <https://arxiv.org/abs/1103.5635>.

## Next proof obligations

1. Derive the sourced scalaron equation including a compactly supported trace intervention.
2. Derive the clock-compass Ricci-scalar transfer and physical normalization.
3. Formalize existence of the regular Laurent coefficient of `(7)` at positive even gaps.
4. Prove scaling-background subtraction identifies `(4)` without assuming unknown outer data DA.
5. Extend from \(R+\alpha R^2\) to a mode-by-mode theorem for general near-\(\mathrm{AdS}_2\)
   gravitational effective field theories.
6. Determine whether all propagating Einstein throat modes occupy integer Gamma orbits, or record
   the exact counterexample.
