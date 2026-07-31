# Rewrite blueprint: localization versus recurrence

**Status:** superseded after coherence failure; retained for provenance only
**Replacement:** `rewrite-blueprint-recurrence-clock.md`
**Target:** one theoretical physics paper assessed against Nature editorial
criteria  
**Central question:** Does spatial localization simplify the long-term
future of quantum matter?

## Editorial answer

Within exactly diagonal l-bit Hamiltonians, zero configuration-basis
transport is compatible with the largest possible number of independent
projective spectral phases. Finite-range commuting support geometry limits
this number, but absolutely summable all-range tails can restore the
finite-window maximum in one infinite constructed field.

Popular-language form:

> A quantum system can remain frozen in its configuration basis yet require
> exponentially many independent phases to return.

This is the only public-facing claim presently earned. It must not be
expanded to spacetime dimensionality, free will, black-hole information or
cosmology.

## Proposed title

**Exponential quasi-locality permits maximal quantum recurrence rank**

Alternative:

**Exactly diagonal l-bit dynamics can have maximal projective recurrence
rank**

Do not use “Anderson localization” in the title until a standard
microscopic disordered-chain transfer is proved.

## Master law

For a finite exact l-bit Hamiltonian
\[
  H_J=\sum_{S\subseteq I}J_S Z_S,
\]
define \(\tau(H_J)\) as the rational dimension of its projective gap span
and \(L_{E_J}^{\mathrm{proj}}\) as its balanced rational spectral-relation
space. Then
\[
  \boxed{
  \tau(H_J)=
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
  \{J_S:S\ne\varnothing\},}
\]
\[
  \boxed{
  \tau(H_J)+
  \operatorname{rank}_{\mathbb Q}L_{E_J}^{\mathrm{proj}}
  =2^{|I|}-1.}
\]

This is the theorem spine. All other main-text results must be consequences,
sharp boundaries or operational resolutions of these equations.

## The result sequence

### Result 1: noninteracting diagonal/Fock endpoint

If all genuine interaction coefficients vanish and the one-body
coefficients are rationally independent,
\[
  \tau=|I|,\qquad
  \operatorname{rank}_{\mathbb Q}L_{E_J}^{\mathrm{proj}}
  =2^{|I|}-1-|I|.
\]
This is the noninteracting diagonal endpoint. Anderson localization is not
used in its proof.

### Result 2: interaction singularity without transport

For every finite-order l-bit Hamiltonian and every \(\varepsilon>0\), there
is a full-rank Hamiltonian within coefficient \(L^1\) distance
\(\varepsilon\), with every energy uniformly \(\varepsilon\)-close,
satisfying
\[
  \tau=2^{|I|}-1.
\]
The two Hamiltonians are diagonal in the same product basis, every
l-bit charge remains conserved, and all off-diagonal configuration
transitions remain zero. Within this diagonal class, recurrence rank is
discontinuous in coefficient norm and is not bounded by off-diagonal
configuration transport.

### Result 3: geometric-locality boundary

For a commuting l-bit Hamiltonian whose nonzero supports have diameter at
most \(R\),
\[
  \tau\le|\mathcal S_{n,R}|\le n\,2^{R+1}.
\]
The intrinsic support-count ceiling is sharp inside the allowed support
class under rational independence. This is a commuting finite-range law,
not a universal ceiling for noncommuting local Hamiltonians.

Maximal rank is equivalent to rational independence of the complete
nonempty-support coefficient packet. Therefore any exact
coefficient-preserving site permutation that moves one support forces
strict rank loss. This explains why the maximal infinite quasi-local
construction is inhomogeneous and why Anderson-type disorder is naturally
compatible with, rather than opposed to, maximal recurrence complexity.

### Result 4: infinite quasi-local escape

One coefficient field on all finite supports of the countable chain
satisfies
\[
  \sum_S|J_S|<\infty,\qquad
  |J_S|\le
  2^{-(|S|+\max S+\operatorname{diam}S)}
\]
and has
\[
  \tau(J|_\Lambda)=2^{|\Lambda|}-1
\]
for every finite embedded window \(\Lambda\). It defines a bounded
continuous infinite-configuration energy, uniformly approximated by the
nested first-\(n\)-site truncations. It generates a reversible strongly
continuous Banach-space multiplication group of complex-linear isometries
on continuous amplitudes; this is not a Hilbert-space unitary construction.
Therefore the explicit origin-dependent summable envelope does not imply
the finite-range ceiling.

### Result 5: exact full-cube coefficient isolation

For the full Boolean-cube character,
\[
  \sum_x(-1)^{|x|}E_J(x)=2^{|I|}J_I.
\]
The corresponding recurrence relation survives exactly when \(J_I=0\), and
its minimum replica height is \(2^{|I|-1}\). Its symmetric finite-window
response is
\[
  \mathcal W_I(A)=\operatorname{sinc}(A\,2^{|I|}J_I),
\]
with an exact zero at
\[
  A_*=\pi/|2^{|I|}J_I|
\]
when \(J_I\ne0\).

More generally, every nonempty support \(S\) has a balanced integer Walsh
character on the complete configuration cube that extracts \(2^{|I|}J_S\).
For the exactly scaled family
\[
  J_S(g)=g^{w(S)}J_S,
\]
its centered finite-time Fourier response at elapsed horizon
\(T=\tau g^{-w(S)}\) is exactly
\[
  \operatorname{sinc}(\tau\,2^{|I|}J_S),
\]
independent of \(g\ne0\). Shorter inverse-power horizons converge to one
and longer horizons converge to zero. This is an exact elapsed-time
realization in the ideal scaled diagonal family, not yet a noisy or
support-local device protocol.

### Result 6: resolution and elapsed-time dimension cascade

For a pure-birth scaled l-bit spectral family, the spectral-jet dimension
resolved through order \(r\) is exactly
\[
  \tau_r=
  \sum_{m<r}
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
  \{J_S:w(S)=m\}.
\]
No rational independence across distinct birth layers is required. Under
independence within each layer, this equals the number of nonempty supports
born below \(r\). For diameter birth order,
\[
  \tau_r\le |I|\,2^{r+1}.
\]
The exact theorem is a spectral-jet resolution law. It does not identify
\(r\) with physical elapsed time. For a general analytic family with
overlapping orders, the correct target remains the cumulative
associated-graded rank of stacked spectral jets.

For an active projective character \(k\) whose detuning has birth order
\(b(k)\), the centered inverse-power observation horizon
\(T=\tau g^{-r}\) should give the exact asymptotic wall crossing
\[
  \widehat\mu_r(k)=
  \begin{cases}
    1,&r<b(k),\\
    \operatorname{sinc}(\tau c_k),&r=b(k),\\
    0,&r>b(k),
  \end{cases}
\]
where \(c_k\ne0\) is the leading detuning coefficient. The global Walsh
character isolating support \(S\) has detuning \(2^{|I|}J_S(g)\), so its
birth equals the coefficient birth. It uses the full configuration cube and
has replica height \(2^{|I|-1}\); support-local isolation in the presence of
outside interactions is not proved.

The ideal scaled l-bit family now has the physical-time wall crossing above.
A general analytic family still needs uniform finite-\(g\) remainder bounds,
and a noisy experiment needs a bounded-height margin classifier.
Vasseur--Parameswaran--Moore, Serbyn et al. and logarithmic-light-cone
literature already own the qualitative \(Jt\sim1\) threshold and growth of
effective frequency count. Candidate novelty is only the simultaneous exact
relation-lattice annihilator, layer-additive spectral-jet staircase and
per-character phase-law trichotomy.

### Result 7: one state sees the complete law

The normalized uniform l-bit product state
\[
  \lvert+\rangle^{\otimes |I|}
\]
has nonzero weight on every configuration. Its visible rational gap span is
therefore the full l-bit gap span, and its visible temporal rank is
\(\tau(H_J)\). Moreover, maximal rank is equivalent to every completed
survival-fidelity moment of this single state attaining the unavoidable
permutation collision floor. This removes the abstract-state-support
objection inside the exact l-bit basis. It does not prove preparation in
microscopic physical-spin coordinates when the l-bit dressing is unknown.

## Anderson/MBL interpretation

The paper may state:

- finite noninteracting diagonal/Fock spectra generated by \(N\) one-body
  energies have projective rank at most \(N\);
- interacting exact l-bit fixed points can remain diagonal in the same
  product basis and occupy \(2^N-1\);
- fixed commuting range gives a linear-in-\(N\) ceiling;
- all-range summable tails can saturate every finite-window capacity;
- the arithmetic law explains, but does not first discover,
  interaction-induced suppression of localized revivals.

The paper may not state:

- every microscopic MBL system has full rank;
- rank diagnoses the MBL transition;
- maximal rank implies chaos or thermalization;
- the construction proves stability of MBL;
- the infinite energy has a global exact recurrence.

## Prior-paper subsumption

Main text retains only prior results with a direct arrow from the master law:

| Prior result | New role |
|---|---|
| projective recurrence deadlines and rate--distortion target volume | quantitative geometry on a fixed recurrence torus; one concise corollary or Supplement |
| observer coherence graph | quotient of the master projective gap space |
| collision hierarchy | scalar moment projection of the completed recurrence law |
| exact tensor composition | free/Fock additive endpoint and interaction-induced dimension multiplication |
| weak-interaction finite-horizon continuity | operational contrast to exact-rank discontinuity |
| countable pure-point recurrence | comparison boundary; not the new infinite l-bit theorem |
| atomless/contractive classifications | Supplement unless they become necessary to state the domain boundary |
| local/global completion no-go | Discussion boundary; not a coequal headline |

Contractive dynamics, arbitrary probability spectra, black-hole SFF
discussion and Gaussian compression cannot remain parallel main-text
headlines. That recreates the rejected collage.

## Required main figure

One two-axis capacity diagram:

- horizontal axis: spatial interaction structure
  (one-body \(\rightarrow\) bounded range \(\rightarrow\) quasi-local tails);
- vertical axis: attainable recurrence-rank ceiling under rational
  independence
  (\(N\rightarrow O(N2^R)\rightarrow 2^N-1\));
- all constructed points remain on the zero configuration-transport
  diagonal manifold;
- inset: observer scale unlocks successively weaker interaction layers.

## Current hostile verdict

The finite exact law plus infinite continuous-energy construction is a
strong mathematical-physics result. It is not yet a Nature paper because:

1. the 2015 revival-suppression literature owns the qualitative effect;
2. exact rational rank is discontinuous and naturally asymptotic;
3. no standard microscopic localized ensemble is covered;
4. the finite-time observable is exponentially nonlocal in replica height;
5. no experimental advantage over known dephasing probes is proved.

Promotion requires a physical elapsed-time realization with explicit
finite-parameter and noise errors beyond the ideal scaled family, plus
either a microscopic localized-chain transfer or a compelling
experimentally accessible exact prediction. The exact wall crossing still
uses a full-configuration character and does not cross that gate alone.
