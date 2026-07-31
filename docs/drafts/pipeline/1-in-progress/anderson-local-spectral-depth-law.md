# Anderson local spectral-depth law

- **ID:** `anderson-local-spectral-depth-law`
- **Stage:** 1-in-progress
- **Type:** NAMED-MODEL ANDERSON SPECTRAL LAW
- **Labels:** `[FROZEN CONJECTURE] [NOVELTY TARGET] [LEAN-OPEN]`
- **Parent:** `local-spectral-dimension-recurrence-law`
- **Date opened:** 2026-07-31

## Public sentence

> In localized matter, distance from an observer is encoded as logarithmic
> depth in the spectrum they can see.

## Frozen conjecture

Let
\[
 (H_\omega\psi)(n)=\psi(n+1)+\psi(n-1)+V_\omega(n)\psi(n)
\]
be the one-dimensional discrete iid Anderson Hamiltonian on
\(\ell^2(\mathbb Z)\), with nonzero hopping and a compactly supported
single-site law having a bounded density.  Restrict to a compact energy
interval \(I\) in the localized regime.  Almost surely choose normalized
eigenfunctions \(\psi_j\), eigenvalues \(E_j\in I\), and localization
centres \(c_j\).  For a fixed observation site \(x\), define
\[
 p_j(x)=|\psi_j(x)|^2,\qquad
 N_x(L;I)=\#\{j:E_j\in I,\ -\log p_j(x)\le L\}.
 \tag{1}
\]

Then almost surely
\[
 \boxed{
 N_x(L;I)\sim
 L\int_I\frac{1}{\gamma(E)}\,dN(E)}
 \qquad(L\to\infty),
 \tag{2}
\]
where \(\gamma(E)>0\) is the Lyapunov exponent and \(N\) is the integrated
density of states.

The convention in (2) uses two spatial directions and squared amplitudes:
centres at distance \(r\) have logarithmic weight \(2\gamma(E)r\), while
the one-dimensional ball contains asymptotically \(2r\) centres per unit
integrated density of states.  The two factors cancel.

## Stronger geometric conjecture

For an ergodic Anderson model on a graph or lattice of volume-growth
dimension \(D\), with an energy-dependent homogeneous localization metric
\(\tau_E\), the expected universal form is
\[
 \boxed{
 N_x(L;I)\sim
 2^{-D}L^D
 \int_I
 \operatorname{vol}\{z:\tau_E(z)\le1\}\,dN(E).}
 \tag{3}
\]

Equation (3) is a truth-hunch, not a paper claim.  It predicts that
noninteger graph/fractal volume dimension and anisotropic localization
geometry are visible in the threshold count of one local spectral measure.

## Why this is the missing Anderson theorem

Existing localization theory controls how large a remote amplitude can be.
The count (1) also needs to know that a positive-density set of remote
eigenfunctions is not anomalously dark at the fixed site \(x\).  This is a
triangular-array problem: as the centre recedes, the eigenfunction itself
changes.  Oseledec decay of one fixed eigenfunction along its own tail does
not directly give uniform fixed-site control across all receding centres.

If (2) is proved, the externally known small-deviation law and the local
recurrence minimax bridge give
\[
 \log T_x(\eta)\sim
 \frac14
 \left(\int_I\frac{1}{\gamma(E)}\,dN(E)\right)
 \bigl(\log(1/\eta)\bigr)^2
 \tag{4}
\]
for the universal local spectral packet clock and the corresponding
independent-Haar phase quantiles.  Equation (4) is not an actual
deterministic first-return law for one fixed spectrum; torus-flow hitting
times retain arithmetic dependence.

## Strictly local Floquet target

Vakulchyk--Flach, *Chaos* **33**, 083134 (2023), construct a
one-dimensional random Floquet map with two internal states per unit cell,
strictly nearest-neighbour coupling, full-circle quasienergy spectrum, and a
quasienergy-independent localization length
\[
 \xi(\theta)=\frac1{-\log|\sin\theta|}.
 \tag{4a}
\]
This is a stronger Nature target than the Blaschke-dressed atomic ensemble:
disorder creates the localized eigenvectors of a banded unitary instead of
only randomizing eigenvalues in a prescribed localized basis.

For a local spinor basis state \(e_{x,\sigma}\), put
\[
 p_j(x,\sigma)=|\langle e_{x,\sigma},\psi_j\rangle|^2,\qquad
 N_{x,\sigma}(L)=\#\{j:-\log p_j(x,\sigma)\le L\}.
 \tag{4b}
\]
The named-model conjecture is
\[
 \boxed{N_{x,\sigma}(L)\sim2\xi(\theta)L}
 \tag{4c}
\]
almost surely.  The factor \(2\) is the two-state integrated density per
unit cell; two spatial directions cancel the factor \(2\) from squared
amplitude decay.

Spectral depth alone is insufficient for an actual first-return law because
the weights, active set, and quasienergies are correlated.  Let
\({\cal R}_L\) be the event that the depth count and reverse-water entropy
have their predicted asymptotics at scale \(L\).  The missing
anti-concentration theorem is the annealed bound, uniformly for every
positive integer \(n\),
\[
 \begin{aligned}
 &{\mathbb P}\left(
 {\cal R}_L\ \text{and}\
 \left|\sum_jp_j(x,\sigma)e^{-inE_j}\right|\ge1-e^{-L}
 \right)\\
 &\qquad\le
 K_x(L)\,M_x(L)
 \exp\left[\frac\pi4-H_x(L)+\frac L2\right],
 \qquad
 \log K_x(L)=o(L^2),
 \tag{4d}
 \end{aligned}
\]
where \(M_x(L)=O(L)\), \(H_x(L)\sim\xi(\theta)L^2/2\), and
\(\sum_L{\mathbb P}({\cal R}_L^c)<\infty\).
A conditional finite-head density bound implies (4d), but is not assumed:
conditioning on the exact random weights may itself produce a singular
law.  Equations (4c)--(4d), combined with the bounded-density recurrence
argument, would give the exit-conditioned trace-distance law
\[
 \boxed{
 \log\tau^{\rm tr}_{x,\sigma}(\varepsilon)
 \sim2\xi(\theta)\bigl(\log(1/\varepsilon)\bigr)^2.}
 \tag{4e}
\]

The plausible mechanism for (4d) is localized spectral averaging:
Hellmann--Feynman derivatives of an eigenphase with respect to a disorder
phase equal local eigenstate intensities.  For separated localization
centres, the resulting Jacobian is approximately diagonal.  A direct
averaged target estimate may survive even when the conditional joint law is
singular.  A cost \(\log K_x(L)=O(L\log L)\) would already suffice.  This is
a research route, not a proved claim.

## Existing exact deterministic bridge

Let \(r_j=d(x,c_j)\), \(M_x(R)=\#\{j:r_j\le R\}\), and suppose
\[
 c_-e^{-\beta_-r_j}\le p_j(x)\le c_+e^{-\beta_+r_j}.
 \tag{5}
\]
Then, for large \(L\),
\[
 M_x\!\left(\frac{L+\log c_-}{\beta_-}\right)
 \le N_x(L)
 \le
 M_x\!\left(\frac{L+\log c_+}{\beta_+}\right).
 \tag{6}
\]
Thus polynomial centre growth and a two-sided exponential profile imply
\(N_x(L)=\Theta(L^D)\).  If
\[
 M_x(R)\sim\kappa_xR^D,\qquad
 \sup_{r_j\ge R}
 \left|\frac{-\log p_j(x)}{r_j}-\beta_x\right|\to0,
\]
then
\[
 N_x(L)\sim\kappa_x\beta_x^{-D}L^D.
 \tag{7}
\]
This geometry-to-visibility implication is dependency-closed on paper.
Its hypotheses are not currently derived for the named model in (1).

## External frontier

- `[LITERATURE]` Bucaj et al., arXiv:1706.06135, prove spectral and
  dynamical localization for the one-dimensional iid Anderson model and
  Lyapunov behaviour for generalized eigenfunctions.
- `[LITERATURE]` Goldsheid--Sodin, arXiv:2012.03017, prove nearby lower
  bounds on Anderson-localized eigenfunctions, but only subsequential
  decay-rate control.
- `[LITERATURE]` Germinet--Klopp, arXiv:1011.1832, prove joint eigenvalue
  and localization-centre statistics in the localized regime.
- `[LITERATURE]` Elgart--Klein, arXiv:1509.08521, label high-disorder
  finite-volume eigenpairs by lattice sites and prove exponential
  localization with high probability.
- `[LITERATURE]` Klopp--Schenker, arXiv:2105.13215, control spatial extent
  and onset of localized eigenfunction decay.
- `[LITERATURE]` Vakulchyk--Flach, *Chaos* 33, 083134 (2023), prove a
  quasienergy-independent localization length for a strictly
  nearest-neighbour random one-dimensional Floquet map.
- `[LITERATURE]` Kotowski--Oszmaniec, arXiv:2601.10409, prove tight
  finite-dimensional recurrence bounds and explicitly leave tight
  recurrence for physical local noncommuting dynamics open.
- `[PRIORITY BOUNDARY]` None of these results, as audited, proves (2).
  Absence from this list is not evidence of novelty; full priority audit
  remains open.

## Counterexamples to weaker statements

1. At the atomic limit \(H=\operatorname{diag}(V_y)\),
   \(p_j(x)=\mathbf1_{\{j=x\}}\) and \(N_x(L)=1\), despite complete
   dynamical localization.
2. Superexponential Wannier--Stark/Bessel tails give
   \(N_x(L)\asymp L/\log L\) in one dimension, not \(L\).
3. A one-sided exponential envelope permits exact nodes, near-nodes, or
   superexponentially dark modes.  It supplies only the upper count.

Therefore “Anderson localization alone implies (2)” is false.

## Proof attack

Required bricks:

1. a stationary marked point process of eigenvalue--centre--amplitude
   triples;
2. centre intensity \(dN(E)\,dc\);
3. a uniform large-deviation law for transfer matrices evaluated at the
   random eigenvalue belonging to a receding centre;
4. negligible density of nodes, resonant cancellations, and anomalously
   dark modes at \(x\);
5. an ergodic counting theorem for the moving threshold
   \(2\gamma(E)|c-x|\le L\);
6. boundary and finite-volume-to-infinite-volume control.

Potential proof route in \(D=1\):

- label finite-volume eigenpairs by centres;
- express the fixed-site amplitude ratio through the transfer-matrix
  cocycle between \(x\) and \(c_j\);
- prove a uniform-in-energy large-deviation estimate strong enough for a
  Borel--Cantelli argument over all centres at distance \(r\);
- combine with joint centre--energy statistics and pass to infinite volume.

Fatal risk: resonant normalization or cancellation may leave a
positive-density family whose fixed-site amplitude exponent differs from
\(2\gamma(E)\).  Finding such a family kills (2) and requires replacing the
constant by a variational large-deviation rate.

## Formal status

- (6) and (7): paper-proved, Lean-open.
- abstract recurrence squeeze: paper-proof candidate, external priority
  collision, Lean-open.
- named-model law (2): conjecture, unproved.
- geometric law (3): conjecture, unproved.

No statement from this card is manuscript-authorized until its exact
mathematical content is proved in Lean.  The manuscript must not mention
formalization.
