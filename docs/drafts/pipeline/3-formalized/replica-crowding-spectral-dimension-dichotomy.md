# Replica-crowding spectral-dimension dichotomy

- **ID:** `replica-crowding-spectral-dimension-dichotomy`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / finite-time spectral-structure law
- **Status:** `[FORMALIZED] [FRONTIER] [NOVELTY UNVERIFIED]`
- **Parent:** `replica-action-crowding-shortcut-law.md`
- **Date:** 2026-08-06

## Question

The parent shortcut law replaces the smallest nonzero replica action by the
local crowding degree `kappa_r(E;delta)`.  What does large crowding mean
structurally?  The answer is exact: it cannot occur without many independent
integer spectral characters that remain slow throughout the observation
window.

## Definitions

Let `I` be a finite spectral label set and

\[
 \mathcal P_r=\{p:I\to\mathbb N:\sum_i p_i=r\},\qquad
 \Omega_p=\sum_i p_iE_i.
\]

For `p in P_r`, define its nonzero `delta`-crowding fibre

\[
 Q_p(\delta)=\{q\in\mathcal P_r:
   0<|\Omega_q-\Omega_p|<\delta\}.
\]

Associate to every `q in Q_p(delta)` the balanced integer character

\[
 k_q=q-p\in\mathbb Z^I,
 \qquad \sum_i(k_q)_i=0,
 \qquad |(k_q)_i|\le r.                                  \tag{1}
\]

Let

\[
 s_p(\delta)=\dim_{\mathbb Q}
   \operatorname{span}_{\mathbb Q}\{k_q:q\in Q_p(\delta)\},
 \qquad
 s_r(E;\delta)=\max_{p\in\mathcal P_r}s_p(\delta).       \tag{2}
\]

## The law

For every finite real spectrum, every replica order and every positive
resolution,

\[
 \boxed{
   |Q_p(\delta)|\le(2r+1)^{s_p(\delta)},\qquad
   \kappa_r(E;\delta)\le(2r+1)^{s_r(E;\delta)}.}          \tag{3}
\]

Moreover, if `s=s_p(delta)`, there exist `s` rationally independent balanced
integer characters `k_1,...,k_s`, each with coordinate size at most `r`, such
that

\[
 0<\left|\sum_i(k_j)_iE_i\right|<\delta                 \tag{4}
\]

and, for every real time `t`,

\[
 \boxed{
 \left|\exp\!\left(it\sum_i(k_j)_iE_i\right)-1\right|
 \le |t|\delta.}                                         \tag{5}
\]

Consequently the whole phase orbit up to `|t|<=T` lies in the common
`T delta`-tube of `s` independent character kernels.  Large crowding is thus
not an unclassified failure of anti-concentration: it is a certificate of
finite-time spectral-dimension loss.

For a static Hamiltonian with maximal projective spectral rank, a normalized
full-Choi target assigned to every padded word of length at most `s`, and a
gate alphabet of size `g`, combining `(3)` with the parent adaptive circuit
theorem gives

\[
 \boxed{
 P_{\rm shortcut}
 \le g^{s+1}\left[
   \bigl(1+(2r+1)^{s_r(E;\delta)}\bigr)r!d^{-r}
   +e^{-(T\delta)^2/2}\right]}                            \tag{6}
\]

for Gaussian observation, with the uniform-window sinc remainder in place
of the Gaussian remainder.

The uniform law also gives a deterministic forward-time certificate.  If

\[
 g^{s+1}\left[
   \bigl(1+(2r+1)^{s_r(E;\delta)}\bigr)r!d^{-r}
   +\min\{1,(T\delta)^{-1}\}\right]
 <(1-\epsilon^2)^r,                                  \tag{7}
\]

then some `t in (0,2T]` is farther than `epsilon` in pure-state trace
distance from every supplied padded-word Choi target.  No closure of the gate
set under inverses is needed: exact diagonal spectral phase translation moves
the centered window to positive time while preserving target norms and trace
distance.

For the ordinary time-independent bounded-weight Pauli family, generic
coefficients supply maximal projective spectrum.  Under `(7)`, the same
Hamiltonian simultaneously satisfies

\[
 \boxed{\begin{gathered}
 \exists t\in(0,2T]\text{ outside every depth-}s\text{ circuit target},\\
 \forall u\in\mathbb R:\quad
 S_{\rm local}(u)>S_{\rm Haar}.
 \end{gathered}}                                      \tag{8}
\]

Here the second line is the corpus's exact product-stabilizer two-query
signal for that Hamiltonian.  Thus circuit hardness at the certified future
endpoint does not erase its permanent operational locality witness.

## Proof

Fix `p`.  Translation by `-p` is injective, so `q -> k_q` identifies the
crowding fibre with a finite subset `K_p` of the rational vector space
`V_p=span_Q K_p`.  Let `s=dim_Q V_p`.

The coordinate functionals on `Q^I` separate points of `V_p`, hence their
restrictions span `V_p^*`.  Choose `s` coordinate functionals forming a basis
of `V_p^*`; equivalently, there is a coordinate set `J subset I`, `|J|=s`,
for which the projection

\[
 \pi_J:V_p\longrightarrow\mathbb Q^J
\]

is injective.  By `(1)`, each projected integer coordinate has one of exactly
`2r+1` values `-r,-r+1,...,r`.  Therefore

\[
 |Q_p(\delta)|=|K_p|=|\pi_J(K_p)|\le(2r+1)^s,
\]

proving the first part of `(3)`.  Maximizing over `p` proves its second part.

A basis extracted from `K_p` supplies the independent characters in `(4)`.
Balancedness and coordinate bounds are inherited from `(1)`.  Finally the
unit-circle chord inequality `|e^{ix}-1|<=|x|` gives

\[
 \left|e^{it\langle k_j,E\rangle}-1\right|
 \le |t|\,|\langle k_j,E\rangle|\le|t|\delta,
\]

which proves `(5)`.  Substitution of `(3)` into the already proved parent
shortcut law proves `(6)`.

## Interpretation

Replica action crowding and finite-time temporal dimension are dual views of
one obstruction.  Sparse crowding gives circuit anti-concentration directly.
Dense crowding forces independent phase coordinates to remain effectively
frozen during the same window.  The observation time therefore resolves only
the quotient by slow characters; its effective spectral dimension grows as
those characters cross their inverse-action times.

This supplies a precise mathematical version of “time has an
observer-dependent dimension”: dimension here is neither subjective nor a
new spacetime postulate.  It is the number of independent spectral characters
resolved at a stated temporal resolution.

## Hostile audit

1. Coordinate-projection counting and the unit-circle chord inequality are
   classical; novelty can only lie in the replica-crowding/shortcut/temporal-
   dimension synthesis.
2. Equation `(5)` proves confinement near a spectral subtorus, not low circuit
   complexity of that subtorus.  No Brown--Susskind growth law follows from it
   alone.
3. The rank `s_r(E;delta)` may be large.  Then `(6)` can be too weak to survive
   circuit entropy; the structural branch, not the probability branch, is the
   content.
4. Equation `(7)` is an explicit first-forward-hard-time certificate, but it
   does not bound `s_r(E;delta)` for a local-Hamiltonian ensemble.  Without
   that input it is not a Brown--Susskind cut-time scale.
5. Low resolved spectral dimension does not imply low circuit complexity; a
   one-parameter orbit may contain hard endpoints.  No such inference is made.
6. Priority remains unverified against quantitative Kronecker theory,
   additive-energy inverse theorems and higher spectral-form-factor work.

## Formalization inventory

All displayed mathematical claims are theorem-backed in:

- `HTGeometry/ReplicaCrowdingSpectralDimensionLaw.lean`: balanced integer
  differences, coordinate bound, injective coordinate projection, fibre and
  global rank bounds, existence of an independent generating set with
  cardinal exactly the rank, slow-character inequality, and Gaussian/uniform
  rank-form moment and capture laws.
- `RHTower/DirectAdaptiveStaticChoiSpectralDimensionLaw.lean`: invariance of
  crowding rank under spectral sign reversal and Gaussian/uniform adaptive
  padded-circuit shortcut bounds under maximal projective spectral rank,
  together with the centered-window hard-time certificate.
- `RHTower/StaticChoiForwardSpectralDimensionLaw.lean`: diagonal spectral
  phase isometry, exact time-shift covariance of Choi capture, and the
  forward hard-time theorem `(7)`.
- `RHTower/StaticQLocalForwardComplexityHaarSeparationLaw.lean`: same-system
  bounded-weight Pauli specialization `(8)`, combining future circuit
  hardness with all-time strict separation from the exact Haar benchmark.

No `sorry`, `admit`, new axiom, `opaque`, or `unsafe` declaration is used.
