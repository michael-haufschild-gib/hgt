# Banach two-boundary observer radical and horizon-layer duality

- **ID:** `banach-two-boundary-observer-radical-and-horizon-layer-duality`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / CONTINUOUS CONSTRAINT-RELATIVITY CHART
- **Status:** `[PAPER-PROVED] [BANACH COMPLETION RADICAL] [VON NEUMANN HORIZON LAYER]`
  `[MODULAR PAIRING COVARIANCE] [CLASSICAL FUNCTIONAL ANALYSIS] [BRIDGE]`
  `[CONDITIONAL ON STANDARD HSMI INPUT] [NOT WORMHOLE] [LEAN COMPLETE]`
- **Statement:** Continuous two-boundary exactification has weak-star observer-descent radical absent
  in finite vector spaces. For nested weak-star closed horizon cuts, relative layer is canonically
  predual to normal observer quotient and modular flow preserves pairing.
- **Parents:** `relative-law-observer-descent-duality.md`,
  `half-sided-modular-conormal-persistence-and-bounded-dilation-no-go.md`.

## Goal

Extend relative-law/observer duality beyond algebraic vector spaces without assuming continuous
complements. Determine exactly what completion adds, then instantiate on half-sided modular
horizon filtration.

## 1. Two-boundary Banach exactification

Let `E` be complex Banach space and `Y_L,Y_R subset E` closed linear subspaces. Define

\[
 q:E\longrightarrow (E/Y_L)\oplus_\infty(E/Y_R),
 \qquad
 q(x)=([x]_L,[x]_R).
 \tag{BHR.1}
\]

Then

\[
 K=\ker q=Y_L\cap Y_R.
 \tag{BHR.2}
\]

Concentrate source and target in degree zero and use cone convention

\[
 \operatorname{Cone}(q)^n
 =(E/Y_L\oplus E/Y_R)^n\oplus E^{n+1}.
 \tag{BHR.3}
\]

Therefore

\[
 \boxed{
 H^{-1}(\operatorname{Cone}q)\cong K.}
 \tag{BHR.4}
\]

### Proof

Cone degree `-1` is `E`, cone degree zero is `E/Y_L direct-sum E/Y_R`, and differential is
`-q`. There is no degree `-2` term. Thus degree-minus-one cohomology is `ker q`. `[PROVED HERE]`

## 2. Continuous observer-descent exact sequence

For closed `Y subset E`, let annihilator

\[
 Y^\perp=\{\lambda\in E^*: \lambda|_Y=0\}.
 \tag{BHR.5}
\]

Continuous observers descending through two boundary quotients are exactly sums
`Y_L^perp+Y_R^perp`. Define algebraic quotient of continuous observers

\[
 \mathcal O_q
 =E^*/(Y_L^\perp+Y_R^\perp).
 \tag{BHR.6}
\]

Restriction to `K` yields exact sequence

\[
 \boxed{
 0\longrightarrow
 \frac{K^\perp}{Y_L^\perp+Y_R^\perp}
 \longrightarrow\mathcal O_q
 \xrightarrow{\mathrm{res}}K^*
 \longrightarrow0.}
 \tag{BHR.7}
\]

### Proof

Every element of `Y_L^perp+Y_R^perp` vanishes on `K`, so restriction descends to `O_q`. Kernel
is exactly functionals vanishing on `K`, namely `K^perp`, modulo already descending sum. Every
continuous functional on closed `K` extends to `E` by Hahn--Banach, so restriction is surjective.
`[PROVED HERE]`

The first term is **topological descent radical**. Standard annihilator identity gives

\[
 \boxed{
 K^\perp
 =\overline{Y_L^\perp+Y_R^\perp}^{\,w^*}.}
 \tag{BHR.8}
\]

Indeed annihilator of `Y_L^perp+Y_R^perp` in `E` is `Y_L intersection Y_R=K`; bipolar theorem
gives weak-star closure `(BHR.8)`. `[PROVED HERE]`

All quotients in `(BHR.6)`--`(BHR.8)` are algebraic unless explicitly normed. If
`Y_L^perp+Y_R^perp` is not weak-star closed, the radical quotient is generally non-Hausdorff in
the quotient topology.

Consequences:

1. if sum of annihilators is weak-star closed, `O_q≈K*`;
2. in finite dimension this always holds, recovering algebraic relative-observer duality;
3. if sum is not weak-star closed, nonzero observer classes may vanish on every retained law yet
   still fail exact boundary descent.

This radical is missing completion carrier. It is not new functional analysis.

## 3. Locality no-go

A strict left-boundary observer is pullback of functional on `E/Y_L`, hence belongs to
`Y_L^perp`; similarly on right. Both vanish on `K`. More generally, every observer descending
through `q` lies in `Y_L^perp+Y_R^perp` and vanishes on `K`. If `k in K` is nonzero, any continuous
functional detecting it has nonzero restriction to `K` and therefore cannot descend through `q`.

The topological descent radical has a different role: it records non-descending observer classes
that remain invisible on every element of `K`. `[PROVED HERE]`

## 4. Nested horizon-cut exact layer

Let `M` be von Neumann algebra with predual `M_*`, and let

\[
 M(b)\subset M(a)\subset M
 \tag{BHR.9}
\]

be weak-star closed cut algebras. Put

\[
 C_c=M/M(c),
 \qquad
 L_{a,b}=M(a)/M(b).
 \tag{BHR.10}
\]

Canonical quotient map

\[
 \pi_{b,a}:C_b\to C_a,
 \qquad [x]_{M(b)}\mapsto[x]_{M(a)}
 \tag{BHR.11}
\]

has

\[
 \boxed{\ker\pi_{b,a}=L_{a,b}.}
 \tag{BHR.12}
\]

Thus layer is literal relative law/mapping-cone kernel between cuts. `[PROVED HERE]`

For normal annihilator

\[
 M(c)^\perp
 =\{\omega\in M_*:\omega|_{M(c)}=0\},
 \tag{BHR.13}
\]

Equip `M(a)/M(b)` with its quotient weak-star topology as a dual operator space.

there is canonical isometric predual identification

\[
 \boxed{
 M(b)^\perp/M(a)^\perp
 \cong (M(a)/M(b))_*.}
 \tag{BHR.14}
\]

Pairing is

\[
 \langle[\omega],[x]\rangle=\omega(x).
 \tag{BHR.15}
\]

### Proof

Since `M(a)^perp subset M(b)^perp`, right side of `(BHR.15)` is unchanged if `omega` changes by
`M(a)^perp`. It is unchanged if `x` changes by `M(b)` because `omega` annihilates `M(b)`.
Standard predual quotient theorem for weak-star closed subspaces identifies all normal
functionals on `M(a)/M(b)` this way, isometrically. `[PROVED HERE]`

No continuous complement or `Ext^1` is used.

## 5. Modular covariance

Define co-moving modular flow

\[
 \tau_t=\operatorname{Ad}(\Delta_\Omega^{-it}).
 \tag{BHR.16a}
\]

Assume, with parent card's convention, that it transports cuts by

\[
 \tau_tM(a)=M(e^{2\pi t}a).
 \tag{BHR.16}
\]

For `x in M(a)` and `omega in M(b)^perp`, put

\[
 x_t=\tau_t(x),
 \qquad
 \omega_t=\omega\circ\tau_{-t}.
 \tag{BHR.17}
\]

Then `x_t in M(e^(2 pi t)a)` and `omega_t in M(e^(2 pi t)b)^perp`: if
`z=tau_t(y)` with `y in M(b)`, then `omega_t(z)=omega(y)=0`. Thus transported pairing is between

\[
 M(e^{2\pi t}a)/M(e^{2\pi t}b)
 \quad\text{and}\quad
 M(e^{2\pi t}b)^\perp/M(e^{2\pi t}a)^\perp.
 \tag{BHR.17a}
\]

Then `x_t` belongs transported layer and `omega_t` transported observer quotient. Pairing obeys

\[
 \boxed{
 \langle[\omega_t],[x_t]\rangle
 =\langle[\omega],[x]\rangle.}
 \tag{BHR.18}
\]

Proof is `omega_t(x_t)=omega(tau_(-t)(tau_t x))=omega(x)`. `[PROVED HERE]`

Thus modular time transports relative law, observer topology, and evaluation simultaneously.
Co-moving pairing is invariant; fixed frame may see hyperbolic scaling.

## 6. Phase-time classification

Half-sided modular inclusion supplies positive generator `P` with

\[
 \Delta^{-it}P\Delta^{it}=e^{2\pi t}P.
 \tag{BHR.19}
\]

Together with translations `U(a)=e^{iaP}`, covariance relations define a unitary representation,
not necessarily faithful, of orientation-preserving affine group

\[
 \mathbb R_{\mathrm{boost}}\ltimes\mathbb R_{\mathrm{translation}},
 \tag{BHR.20}
\]

with `t` acting on `a` by `a mapsto e^(2 pi t)a`, not compact phase circle. Translation characters gain phases, boosts rescale frequencies. This
separates finite Gibbs recurrence (elliptic phase) from horizon modular time (hyperbolic
phase-scale). Equation `(BHR.18)` is exact bridge.

## 7. Finite thermofield countermodel to wormhole inference

Let faithful finite density matrix `rho=diag(r_i)` on `H`, with standard-form space
`H tensor conjugate(H)` and modular operator

\[
 \Delta_\rho=\rho\otimes\overline{\rho^{-1}}.
 \tag{BHR.21}
\]

Set

\[
 Y_L^i=\mathbb Ce_i\otimes\overline H,
 \qquad
 Y_R^j=H\otimes\mathbb C\overline e_j.
 \tag{BHR.22}
\]

Then

\[
 Y_L^i\cap Y_R^j=\mathbb C(e_i\otimes\overline e_j).
 \tag{BHR.23}
\]

Both boundary quotients kill this line; cone retains it; covector `bra(e_i tensor conjugate(e_j))` detects
it; modular time acts by

\[
 \Delta_\rho^{it}(e_i\otimes\overline e_j)
 =e^{it(\log r_i-\log r_j)}e_i\otimes\overline e_j.
 \tag{BHR.24}
\]

Thus boundary-erased relative class, detecting observer, and modular phase exist in every faithful
finite thermal system—without gravity, nonfactorization, interior, or wormhole. These incidence
properties cannot diagnose wormhole. For prime Gibbs weights, frequency is
`beta log(p_j/p_i)` when `r_i=Z^(-1)p_i^(-beta)`. This finite model is not an HSMI model; it is
only a counterexample to inferring gravity from boundary-erased relative class, detecting observer,
and modular phase. `[PROVED HERE]`

## 8. Hostile limits and positive survivor

1. Finite-dimensional perfect duality misses radical `(BHR.7)`.
2. Relative class plus modular phase does not imply gravitational interior by `(BHR.21)`--`(BHR.24)`.
3. Horizon layer theorem does not identify arithmetic Route-R class.
4. HSMI supplies affine transport, not periodic recurrence.
5. No wormhole length, Brown--Susskind complexity, or two-asymptotic-boundary theorem follows.

Strongest positive survivor is exact horizon-cut quartet

\[
 (L_{a,b},M(b)^\perp/M(a)^\perp,\langle-,-\rangle,\tau_t),
 \tag{BHR.25}
\]

plus continuous descent radical `(BHR.7)`--`(BHR.8)`.

## 9. Novelty boundary

Hahn--Banach, annihilator identities, predual quotients, modular automorphisms, and thermofield
standard form are classical. Candidate new-to-corpus content is packaging them as exact continuous
Constraint Relativity chart and isolating topological descent radical omitted by algebraic theorem.
Label `[BRIDGE]`, no priority claim.

## Lean formalization

Formalized in `BanachTwoBoundaryDuality.lean`. The implementation proves the Banach cone kernel,
Hahn--Banach observer exact sequence, weak-star annihilator closure, nested-cut kernel, exact
selected-normal-predual quotient, Hahn--Banach recovery of closed predual subspaces from their
weak-star cuts, the quotient-norm isometry in `(BHR.14)`, contragredient pairing covariance, and
finite thermofield countermodel. See the same-directory `-formalized.md` companion for
declaration-level mapping and verification.

## Gates

- [x] Banach relative cone kernel
- [x] continuous observer exact sequence
- [x] weak-star descent radical
- [x] horizon-cut relative layer/predual duality
- [x] modular covariance
- [x] finite TFD wormhole countermodel
- [x] Lean formalization
- [ ] independent hostile audit
- [ ] literal gravity cut hypotheses
- [ ] arithmetic comparison
- [ ] wormhole length/interior theorem

## Log

- 2026-08-08 — continuous observer radical and exact nested-horizon modular pairing proved;
  finite thermofield countermodel closed wormhole inference.
