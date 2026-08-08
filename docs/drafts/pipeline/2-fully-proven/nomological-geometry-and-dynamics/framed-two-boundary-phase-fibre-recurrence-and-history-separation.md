# Framed two-boundary phase fibre, recurrence, and history separation

- **ID:** `ngd-framed-phase-fibre-history-separation`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM (paper)
- **Status:** `[PAPER-PROVED] [EXACT NGD PHYSICS CHART] [NOT A WORMHOLE THEOREM]`
  `[NOT RH] [NO LEAN WRITTEN]`
- **Statement:** Fixed two-boundary reductions of framed GHZ states have a torus phase fibre whose
  radial QEC defect, Fubini--Study action, winding class, Berry holonomy, and finite Krylov
  displacement are pairwise non-equivalent shadows.

## Goal

Give NGD's time/interior sector one dependency-closed finite theorem. Determine exactly what two
boundary reductions forget, what extra geometry their common fibre carries, and which recurrence
quantities cannot represent accumulated history.

## Setup

Fix an integer `d >= 2`. In
`H_R tensor H_A tensor H_B`, with every factor isomorphic to `C^d`, set

\[
 e_j=|j\rangle_R|j\rangle_A|j\rangle_B,
 \qquad
 |\Psi_\phi\rangle
 =\frac1{\sqrt d}\sum_{j=0}^{d-1}e^{i\phi_j}e_j,
 \qquad
 \Omega_\phi=|\Psi_\phi\rangle\langle\Psi_\phi|.
 \tag{1}
\]

Let `pi_A=Tr_B` and `pi_B=Tr_A`. Let `P=I-d^(-1)11^T` be orthogonal projection onto
`1^perp` in `R^d`.

## Theorem 1 — boundary fibre and radial QEC invariant

Both reductions are independent of `phi`:

\[
 \pi_A(\Omega_\phi)=\frac1d\sum_j|jj\rangle\langle jj|_{RA},
 \qquad
 \pi_B(\Omega_\phi)=\frac1d\sum_j|jj\rangle\langle jj|_{RB}.
 \tag{2}
\]

Among pure states in `span{e_0,...,e_(d-1)}` with these fixed reductions, the common fibre is

\[
 \mathcal F_d\cong\mathbb T^d/\mathbb T_{\rm diag}
 \cong\mathbb T^{d-1}.
 \tag{3}
\]

Define the dephased state and off-diagonal part

\[
 \Delta=\frac1d\sum_j|e_j\rangle\langle e_j|,
 \qquad \kappa_\phi=\Omega_\phi-\Delta.
\]

Then

\[
 \operatorname{Tr}(\kappa_\phi^2)
 =1-\frac1d
 =1-F_e^{\rm opt}(A)
 =1-F_e^{\rm opt}(B)
 =1-e^{-I(R:B\mid A)}.
 \tag{4}
\]

Here `F_e^opt(A)` and `F_e^opt(B)` are optimal entanglement fidelities after losing the opposite
share and recovering from the retained classical label. Consequently `(4)` is constant on the
whole phase fibre.

### Proof

In either partial trace, an off-diagonal term `|e_i><e_j|`, `i != j`, contains the orthogonal
factor `|i><j|` in the traced system and vanishes. This proves `(2)`. Conversely, write a pure
state in the framed support as `sum_j c_j e_j`. Either fixed reduction forces
`|c_j|^2=1/d`. Thus `c_j=d^(-1/2)e^(i phi_j)`, modulo one common projective phase, proving `(3)`.

Directly,

\[
 \operatorname{Tr}\Omega_\phi^2=1,\qquad
 \operatorname{Tr}\Delta^2=d^{-1},\qquad
 \operatorname{Tr}(\Omega_\phi\Delta)=d^{-1},
\]

which gives `Tr(kappa_phi^2)=1-d^(-1)`. After one share is lost, the reference--retained state is
classical on the Schmidt label, hence every recovery remains entanglement breaking from the
reference viewpoint. The overlap of any separable state with a rank-`d` maximally entangled state
is at most `1/d`; reading the label and re-preparing its framed partner attains `1/d`. Thus both
optimal entanglement fidelities equal `1/d`.

Every proper GHZ marginal has entropy `log d`, while the full state is pure. Therefore

\[
 I(R:B\mid A)=S(RA)+S(AB)-S(A)-S(RAB)=\log d,
\]

and `e^(-I)=1/d`. This proves `(4)`. `square`

## Theorem 2 — phase metric, minimum action, and winding

The Fubini--Study metric induced on `F_d` is

\[
 ds_{\rm FS}^2
 =\frac1d\sum_jd\phi_j^2
  -\frac1{d^2}\left(\sum_jd\phi_j\right)^2
 =\frac1d\|P\,d\phi\|^2.
 \tag{5}
\]

For an absolutely continuous history `phi:[0,T]->R^d`, define

\[
 \mathcal A_{\rm FS}[\phi]
 =\frac12\int_0^T\|\dot\Psi_\phi\|_{\rm FS}^2dt.
\]

Then

\[
 \mathcal A_{\rm FS}[\phi]=\frac18\int_0^T F_Q(t)dt,
 \tag{6}
\]

where `F_Q` is pure-state quantum Fisher information. If the endpoint phase difference is `delta`,
the minimum over all lifts is

\[
 \mathcal A_{\min}(\delta;T)
 =\frac1{2dT}\min_{n\in\mathbb Z^d}
   \|P(\delta+2\pi n)\|^2.
 \tag{7}
\]

A closed history has class

\[
 [m]\in\pi_1(\mathcal F_d)
 \cong\mathbb Z^d/\mathbb Z\mathbf1.
\]

Within a fixed class,

\[
 \boxed{
 \mathcal A_{\min}^{[m]}(T)
 =\frac{2\pi^2}{dT}\|Pm\|^2,
 \qquad
 L_{\min}^{[m]}=\frac{2\pi}{\sqrt d}\|Pm\|.}
 \tag{8}
\]

The Berry holonomy is

\[
 \operatorname{Hol}_{\rm B}([m])
 =\exp\!\left(-\frac{2\pi i}{d}\sum_jm_j\right).
 \tag{9}
\]

It factors through a proper quotient of the winding lattice and therefore does not determine
`(8)`.

### Proof

Differentiating `(1)` gives

\[
 \langle d\Psi,d\Psi\rangle=d^{-1}\sum_jd\phi_j^2,
 \qquad
 |\langle\Psi,d\Psi\rangle|^2=d^{-2}(\sum_jd\phi_j)^2,
\]

which is `(5)`. Pure-state quantum Fisher information is four times squared Fubini--Study speed,
proving `(6)`. On the flat universal cover `1^perp`, Cauchy--Schwarz gives

\[
 \int_0^T\|P\dot\phi\|^2dt
 \ge T^{-1}\|P(\phi(T)-\phi(0))\|^2,
\]

with equality for constant-speed segments. Minimizing over integral lifts proves `(7)`; setting
`delta=0` and fixing the lift `2*pi*m` proves `(8)`.

The Berry connection in this frame is

\[
 i\langle\Psi,d\Psi\rangle=-d^{-1}\sum_jd\phi_j.
\]

Integration around the lift `2*pi*m` proves `(9)`. Classes with the same coordinate sum modulo
`d` can have different `||Pm||`, so holonomy does not determine action. `square`

## Theorem 3 — constant source generator and exact recurrence

For `phi_j(t)=-tE_j` with fixed real energies `E_j`,

\[
 F_Q=4\operatorname{Var}_{\rm unif}(E),\qquad
 L_{\rm FS}(T)=T\sqrt{\operatorname{Var}_{\rm unif}(E)},\qquad
 \mathcal A_{\rm FS}(T)=\frac T2\operatorname{Var}_{\rm unif}(E).
 \tag{10}
\]

The witness returns projectively exactly when

\[
 T(E_j-E_0)\in2\pi\mathbb Z\quad\text{for every }j,
 \tag{11}
\]

although both boundary reductions are constant for all time.

### Proof

Substitution of `dot phi=-E` into `(5)` yields squared speed
`Var_unif(E)`, hence `(10)`. Projective return means all relative phases are integral multiples of
`2*pi`, which is `(11)`. `square`

## Theorem 4 — two-level finite Krylov collision

For `d=2`, take

\[
 H=\operatorname{diag}(-\omega/2,\omega/2),
 \qquad |\Psi_0\rangle=(e_0+e_1)/\sqrt2.
\]

The two-site Krylov complexity is

\[
 \boxed{C_K(t)=\sin^2(\omega t/2)
 =1-|\langle\Psi_0|\Psi_t\rangle|^2,}
 \tag{12}
\]

while executed Fubini--Study length is `|omega*t|/2`. At
`t=2*pi/|omega|`, state and `C_K` return to their initial values but executed length equals `pi`.
More generally, for a fixed Krylov space of dimension `D_K`,

\[
 0\le C_K(t)\le D_K-1.
 \tag{13}
\]

### Proof

Lanczos reduction of `(H,Psi_0)` has two sites and transition probability
`sin^2(omega*t/2)` to the site of Krylov index one, proving `(12)`. Formula `(5)` gives constant
speed `|omega|/2`. Bound `(13)` follows because Krylov complexity is the expectation of the site
index supported on `{0,...,D_K-1}`. `square`

## Corollary — exact no-go and positive survivor

No functional of the two boundary reductions, conditional mutual information, optimal recovery
defect, exact regional algebras, or initial/final witness alone determines phase action or winding.
No fixed finite-code recovery defect, endpoint distance, or finite Krylov complexity can equal an
unbounded history length for all time.

The strongest positive survivor is the typed decomposition

\[
 \text{radial QEC defect}
 \quad\perp\quad
 \text{phase tangent metric}
 \quad\perp\quad
 \text{winding history}
 \quad\perp\quad
 \text{Berry quotient}.
 \tag{14}
\]

A physical interior geometry therefore requires, beyond a marginal fibre, a thin path groupoid for
holonomy, a Moore path category or universal cover for executed history, source generator or
connection, cost/metric, cotangent charge, and reconstruction map. This conclusion is unconditional for the finite model; it does not identify that geometry
with a black-hole interior.

## NGD consequence

This chart realizes one exact noncommuting reduction phenomenon: boundary reduction erases all
phase histories, while path lifting retains metric and topological data. It also falsifies any NGD
law that compresses recovery defect, holonomy, action, and complexity into one scalar curvature.

## Literature boundary

- Finite-dimensional Krylov saturation is consistent with `(13)`:
  <https://arxiv.org/abs/2607.14220>.
- DSSYK obtains a model-specific length/Krylov operator dictionary, not a consequence of fibre
  geometry alone: <https://arxiv.org/abs/2305.04355> and <https://arxiv.org/abs/2606.20220>.
- Long-wormhole code results concern code families and mutual information rather than a universal
  equality `CMI = length`: <https://arxiv.org/abs/2310.07770>.

## Gates

- [x] source and boundary reductions explicit
- [x] common fibre classified
- [x] QEC/recovery equality proved
- [x] metric, action, winding, and holonomy formulas proved
- [x] finite Krylov collision proved
- [x] sharp no-go and positive survivor recorded
- [ ] formalized in Lean 4
- [ ] identified with a literal gravitational bulk operator

## Lean-return note

No Lean code was written or built. A later formalization can split into finite-dimensional complex
linear algebra, torus/lattice minimization, entropy identities, and the two-site unitary calculation.
No existing repository file is nominated until corpus search identifies a compatible module.

## Log

- 2026-08-08 — paper proof closed; exact finite physics chart added to NGD.
