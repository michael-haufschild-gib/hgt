# Projective amplitude, Fisher--phase coupling, and hidden-history law

- **ID:** ULF-PAFP-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** phase-genesis attack on modular path-law geometry
- **Statement:** A full-support projective complex amplitude is exactly probability plus relative phase, and its Fubini--Study metric couples Fisher information to weighted phase variance; probability can remain constant along a closed projective loop with nonzero length, winding, and Berry holonomy.
- **Status:** [PAPER-PROVED] [FIELD-LEVEL SINGLE PRODUCER] [CLASSICAL QUANTUM INFORMATION GEOMETRY] [NOT RH] [LEAN CERTIFIED]

## 1. Polar projective chart

Let \(\Omega=\{1,\ldots,N\}\), (N\ge2), and let

\[
\mathbb P^\times(\mathbb C^\Omega)
=\{[z]\in\mathbb{CP}^{N-1}:z_i\ne0\text{ for all }i\}.
\]

For a representative (z), put

\[
p_i=\frac{|z_i|^2}{\sum_j|z_j|^2}
\]

and let ([u]\in U(1)^N/U(1)) be the relative-phase class of

\[
u_i=z_i/|z_i|.
\]

### Theorem 1.1

The polar map is a bijection

\[
\boxed{
\mathbb P^\times(\mathbb C^\Omega)
\cong
\Delta_{N-1}^\circ\times\bigl(U(1)^N/U(1)\bigr),}
\tag{1}
\]

where \(\Delta_{N-1}^\circ\) is the open probability simplex.

### Proof

Projective scaling changes neither normalized magnitudes nor relative phases. Conversely, from
((p,[u])), choose a phase representative (u) and set (z_i=\sqrt{p_i}u_i). Changing the phase
representative multiplies every coordinate by one common scalar, hence gives the same projective
point. The constructions are inverse. QED.

Thus the positive-probability observer

\[
\pi_+:[z]\longmapsto p
\]

has fibre (U(1)^{N-1}). Probability alone cannot reconstruct amplitude even locally when
(N\ge2).

## 2. Exact Fubini--Study decomposition

Choose a normalized representative

\[
\psi_i=\sqrt{p_i}e^{i\phi_i},
\qquad
\sum_i p_i=1.
\]

### Theorem 2.1

The Fubini--Study line element is

\[
\boxed{
ds_{FS}^2
=\frac14\sum_i\frac{dp_i^2}{p_i}
+\sum_i p_i\,d\phi_i^2
-\left(\sum_i p_i\,d\phi_i\right)^2.}
\tag{2}
\]

The first term is one quarter of the Fisher--Rao metric. The last two terms are the weighted variance
of phase velocity and vanish exactly for a common projective-gauge phase change.

### Proof

Direct differentiation gives

\[
\sum_i|d\psi_i|^2
=\frac14\sum_i\frac{dp_i^2}{p_i}
+\sum_i p_i\,d\phi_i^2.
\]

Since \(\sum_i dp_i=0\),

\[
\langle\psi,d\psi\rangle
=i\sum_i p_i\,d\phi_i.
\]

Now use

\[
ds_{FS}^2=\langle d\psi,d\psi\rangle
-|\langle\psi,d\psi\rangle|^2.
\]

QED.

Equation (2) is a single-producer coupling law. Positive information and phase history are not
independent coordinates, but neither determines the other.

## 3. Constant positive shadow with nontrivial projective history

Fix (p\in\Delta_{N-1}^\circ) and integers (k_i\). Consider

\[
\psi_i(t)=\sqrt{p_i}e^{ik_it},
\qquad0\le t\le2\pi.
\tag{3}
\]

The probability observer is constant, and the projective path closes at (2\pi). Nevertheless,

\[
\boxed{
\|\dot\psi(t)\|_{FS}^2
=\operatorname{Var}_p(k),}
\tag{4}
\]

so its length is

\[
\boxed{L_{FS}=2\pi\sqrt{\operatorname{Var}_p(k)}.}
\tag{5}
\]

It is nonzero exactly when the integer velocities are not all equal. The Berry connection in this
chart is

\[
\mathcal A=-i\langle\psi,d\psi\rangle
=\sum_i p_i\,d\phi_i,
\]

and the loop holonomy is

\[
\boxed{
\operatorname{Hol}(\psi)
=\exp\!\left(i2\pi\sum_i p_i k_i\right).}
\tag{6}
\]

For (N=2), (p=(1/2,1/2)), and (k=(0,1)), the positive observer is stationary, the projective
loop has length \(\pi\), the lifted relative phase advances by (2\pi), and the Berry holonomy is
(-1).

## 4. Phase-genesis no-go and positive survivor

A probability law (p) determines neither relative phase nor projective history: its exact fibre is
the torus in (1). Conversely, a full-support projective amplitude determines both probability and
relative phase. Therefore modular path-law geometry cannot obtain phase from its positive law by
functorial inference. The smallest finite single producer is projective complex amplitude.

With a reversal involution on histories, normalized squared magnitude supplies a path probability
and hence the likelihood-production laws of
`time-reversal-likelihood-cocycle-observer-contraction-and-open-history-law.md`; relative phase
supplies the independent orientation needed for interference. Equation (2) is the exact local weld
between those two polar shadows.

## 5. Hostile scope

- Projective Hilbert geometry, Fisher--Rao geometry, and Berry phase are classical.
- The basis/history labels are marked. A change of measurement context changes the probability
  projection and can convert phase into observable interference.
- Positivity does not universally erase phase: informationally complete positive measurements can
  reconstruct a finite density matrix.
- A projective vector does not by itself supply concatenation, interventions, or a source history
  category.
- Infinite-dimensional projective space does not imply differential hypertranscendence.
- The theorem identifies a better single producer; it does not establish a universal field or RH.

## Log

- 2026-08-09 — finite polar-amplitude chart and hidden-history loop proved.

## Lean certification status (2026-08-10) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutivePolarAmplitudeFisherPhase`
(wired into `HTGeometry.UniversalLawField`).

**§1, Theorem 1.1.**  `FullAmp N` are the full-support amplitude vectors, `projSetoid` is
projective equivalence and `ProjAmp N` the quotient; `OpenSimplex N` is the open probability simplex
and `PhaseClass N = (U(1)^N)/U(1)` the relative-phase classes.  `ampProb`, `ampProb_pos`,
`ampProb_sum` and `ampPhase` give the polar data; `ampProb_of_equiv` and `ampPhase_of_equiv` prove
both are projective invariants; `ofPolarData` reconstructs an amplitude with
`ampNormSq_ofPolarData`, `ampProb_ofPolarData`, `ampPhase_ofPolarData`.  **`polarEquiv` is
equation (1)** — a genuine `Equiv ProjAmp (OpenSimplex × PhaseClass)`, not merely the two maps.
`polarEquiv_fst` records that the probability observer is the first projection, so its fibre is the
whole relative-phase torus.

**§2, Theorem 2.1.**  `ampNormSq`, `ampInner` and `fsSpeedSq ψ dψ = ‖dψ‖² − |⟨ψ,dψ⟩|²`;
`polarAmp` and `polarTangent` are the polar chart and its tangent.  `normSq_polarTangent` and
`ampNormSq_polarTangent` give the magnitude half, `ampInner_polarAmp_polarTangent` proves the Berry
connection value `⟨ψ,dψ⟩ = i ∑ pᵢ dφᵢ` (using `∑ dpᵢ = 0`), and **`fsSpeedSq_polar` is
equation (2)**.  `hasDerivAt_polarAmp` certifies that `polarTangent` really is the derivative of the
polar curve, so (2) is a statement about an actual line element rather than a chosen algebraic
expression.

**§3.**  `phaseLoop` is (3); `normSq_phaseLoop` shows the probability observer is constant and
`phaseLoop_two_pi` that the loop closes.  `hasDerivAt_phaseLoop` identifies its velocity.
`velMean`, `velVar`, and **`fsSpeedSq_phaseLoop` is equation (4)**; **`length_phaseLoop` is (5)**;
**`berryConnection_phaseLoop` with `berryHolonomy` and `berryHolonomy_eq_exp_integral` is (6)**.
`velVar_eq_sum` and `velVar_eq_zero_iff` prove the length is nonzero exactly when the integer
velocities are not all equal.  `twoLevel_example` certifies the card's `N = 2` instance: stationary
observer, projective length `π`, Berry holonomy `−1`.

**§4.**  `probObserver` and `probObserver_not_injective`: the amplitudes `(1,1)` and `(1,−1)` have
the same probability vector and are not proportional, so probability determines neither relative
phase nor projective class.  Together with `polarEquiv` this is the exact fibre statement.

`polar_amplitude_fisher_phase_law` bundles §3.

`#print axioms` on `polarEquiv`, `fsSpeedSq_polar`, `hasDerivAt_polarAmp`,
`ampInner_polarAmp_polarTangent`, `fsSpeedSq_phaseLoop`, `length_phaseLoop`, `velVar_eq_zero_iff`,
`berryConnection_phaseLoop`, `probObserver_not_injective`, `twoLevel_example`, and
`polar_amplitude_fisher_phase_law` reports only `propext`, `Classical.choice`, and `Quot.sound`.
