# Universal spectral-semigroup wall crossing

- **ID:** `universal-spectral-semigroup-wall-crossing`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / OPEN-AND-CLOSED LINEAR DYNAMICS /
  FINITE OBSERVATION
- **Source:** failure-driven extension of
  `valued-spectral-constraint-quantum-time-cascade.md`
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Exact frontier

- `[CORPUS]` `ObserverTemporalBirthValuationLaw.lean` proves that every
  active scalar analytic spectral response is exactly
  \(g^bU(g)\), where \(b\in\mathbb N_0\) and \(U(0)\ne0\).
- `[CORPUS]` `TemporalCharacterWallCrossingLaw.lean` proves the symmetric
  unitary sinc crossover for positive detuning magnitude.
- `[CORPUS]` `ArbitrarySpectrumTemporalWallCrossingLaw.lean` proves that
  every finite projective character of an arbitrary analytic spectrum has
  this crossover.
- `[LITERATURE]` Mark et al., *Phys. Rev. X* **14**, 041051 (2024),
  <https://doi.org/10.1103/PhysRevX.14.041051>, characterize infinite-time
  temporal ensembles by all-order no-resonance and study finite-time sinc
  convergence.
- `[LITERATURE]` Stroschein and Reiher, *J. Chem. Theory Comput.* **22**,
  6268--6274 (2026), <https://doi.org/10.1021/acs.jctc.6c00709>, make finite
  observation time primary and prove a sharp spectral-resolution
  transition.
- `[LITERATURE]` finite-dimensional open quantum dynamics is represented by
  contraction semigroups/Lindblad generators; stability and mixing results
  usually assume or bound a gap rather than classify the analytic birth
  order of every observed mode.

The closed-system sinc theorem does not yet explain dissipative modes.
Replacing symmetric phase averaging by a forward time window exposes the
same three-regime law for unitary and contractive evolution.

## Exact theorem

Define the entire removable-singularity kernel
\[
 \Phi(z)=
 \begin{cases}
  (e^z-1)/z,&z\ne0,\\
  1,&z=0.
 \end{cases}                                           \tag{1}
\]

Let \(\lambda:(0,\varepsilon)\to\mathbb C\) obey
\[
 \lambda(g)=g^b u(g),\qquad
 \lim_{g\downarrow0}u(g)=c\ne0,\qquad
 \operatorname{Re}\lambda(g)\le0.                     \tag{2}
\]
For \(\tau>0\), \(r\in\mathbb N_0\), put
\[
 T_r(g)=\tau g^{-r},\qquad
 A_r(g)=\frac1{T_r(g)}
   \int_0^{T_r(g)}e^{t\lambda(g)}\,dt.                \tag{3}
\]
Then
\[
 \boxed{
 \lim_{g\downarrow0}A_r(g)=
 \begin{cases}
  1,&r<b,\\
  \Phi(\tau c),&r=b,\\
  0,&r>b.
 \end{cases}}
                                                               \tag{4}
\]

The hypotheses are properties of the mode, not unproved premises about a
physical model. The theorem is unconditional for every mode satisfying the
displayed, checkable conditions. Every active analytic mode with
nonpositive real part has `(2)` by its exact order of vanishing.

## Dependency-closed proof

For \(T>0\), direct integration gives
\[
 \frac1T\int_0^T e^{t\lambda}\,dt=\Phi(T\lambda),      \tag{5}
\]
including \(\lambda=0\) by continuity. Here
\[
 T_r(g)\lambda(g)=\tau g^{b-r}u(g).                   \tag{6}
\]

If \(r<b\), then \(g^{b-r}\to0\), so `(6)` tends to zero.
Continuity of \(\Phi\) at zero gives \(A_r(g)\to1\).

If \(r=b\), `(6)` tends to \(\tau c\), so continuity gives
\(A_b(g)\to\Phi(\tau c)\).

If \(r>b\), then
\[
 |T_r(g)\lambda(g)|
 =\tau g^{-(r-b)}|u(g)|\longrightarrow\infty          \tag{7}
\]
because \(u(g)\to c\ne0\). Moreover,
\(\operatorname{Re}(T_r(g)\lambda(g))\le0\), hence
\[
 |e^{T_r(g)\lambda(g)}|\le1,\qquad
 |\Phi(T_r(g)\lambda(g))|
 \le\frac2{|T_r(g)\lambda(g)|}\longrightarrow0.       \tag{8}
\]
This proves `(4)`. \(\square\)

## Exact specializations

1. **Closed unitary mode.** For \(\lambda(g)=-i\delta(g)\), the forward
   kernel is
   \(e^{-iT\delta/2}\operatorname{sinc}(T\delta/2)\). Symmetric observation
   removes the phase factor and recovers the exact sinc law.
2. **Open contractive mode.** For a Lindbladian or any contraction
   semigroup eigenmode, \(\operatorname{Re}\lambda(g)\le0\). A decay mode
   born at order \(b\) is unresolved below \(g^{-b}\), has the universal
   \(\Phi\)-profile at \(g^{-b}\), and is fully averaged away above it.
3. **Persistent mode.** If \(\lambda\equiv0\), its average is exactly one
   at every horizon. This is the \(b=\infty\) relation sector and is kept
   separate from active modes.

## Hostile attack

### “This is the elementary \(\varphi_1\) function.”

`[BRIDGE]` Correct for `(1)` and `(5)`. The scalar kernel is standard.
Novelty cannot rest on integrating an exponential. Candidate novelty is the
single valuation filtration whose same birth integers govern:

- Hamiltonian phase relations;
- dissipative spectral modes;
- temporal-dimension rank loss;
- local interaction-packet depth; and
- exact finite-observation wall crossings.

Without the filtration and local generator theorem, this card is
`INSIGNIFICANT`.

### “It does not prove a law of open quantum systems.”

The theorem covers every analytic contractive spectral mode. It does not
claim diagonalizability, completeness of modes, uniform thermodynamic
mixing, non-Markovian dynamics, or exceptional-point branches. A manuscript
must either prove the finite-dimensional generator-level decomposition or
state the theorem per observed mode.

### “Unitary and dissipative modes are not the same physical thing.”

Correct; they share the same valuation-controlled scale law, not the same
kernel value or physical interpretation. Unitary evolution lies on the
boundary \(\operatorname{Re}\lambda=0\); dissipation lies in the left
half-plane.

## Verdict

`SURVIVES PRELIMINARY ATTACK` as a universal extension theorem.
`INSIGNIFICANT` as a stand-alone paper.

## Stronger conjecture forced by the attack

`[CONJECTURE]` For every finite analytic family of contraction generators,
the rational relation filtration of all observer-accessible spectral modes,
its rank-nullity dimension cascade, and the forward-window wall crossings
form one exact functorial object under observer restriction. Local generator
support gives lower bounds on every finite birth valuation.

`[OPEN CORE]` Prove the generator-level observer restriction and local
support theorem without assuming a complete eigenbasis. Until then,
open-system scope remains a per-mode corollary.

## Formalization status

`[LEAN-PROVED]` `UniversalSpectralSemigroupWallCrossingLaw.lean` proves:

1. continuity and the removable value of \(\Phi\);
2. the exact forward-time integral identity `(5)`;
3. all three scaled-mode limits;
4. decay of \(\Phi\) on every unbounded path in the closed left half-plane;
5. the full wall-crossing theorem `(4)`.

Direct verification:
`lake env lean GaloisForLFunctions/HTGeometry/UniversalSpectralSemigroupWallCrossingLaw.lean`
passes without warnings. The analytic-birth instantiation remains a bridge
task, not an assumption in the theorem above. Do not formalize the stronger
generator-level conjecture until its paper proof closes.
