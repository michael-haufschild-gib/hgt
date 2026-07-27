# Cofinite-base reduction for Deninger direct-image amplitude

- **ID:** `deninger-cofinite-base-direct-image-amplitude-reduction`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_COFINITE_BASE_DIRECT_IMAGE_AMPLITUDE_REDUCTION`
- **Parent:**
  `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Statement:** amplitude of Deninger's derived arithmetic projection
  is determined on preimages of the cofinite affine basis
  \(\operatorname{Spec}\mathbb Z[1/N]\).

## Goal

Reduce the first source analytic gate to explicit cofinite arithmetic
opens without assuming a local slice, proper action, or Stein basis on
Deninger's coarse quotient.

## Setup

Let
\[
 S=\operatorname{Spec}\mathbb Z
\]
with Zariski basis
\[
 \mathcal B
 =
 \{U_N=\operatorname{Spec}\mathbb Z[1/N]:0\ne N\in\mathbb Z\}.
\]
Let \(a:X\to S\) be a continuous map and let
\(\mathscr E\) be a bounded-below derived sheaf of \(R\)-modules on
\(X\).

## Theorem

`[PROVED HERE]
[DAC_COFINITE_BASE_DIRECT_IMAGE_AMPLITUDE_REDUCTION]`

Fix integers \(r\le s\).  If
\[
 H^qR\Gamma(a^{-1}U_N,\mathscr E)=0
 \qquad
 (q\notin[r,s])                                                    \tag{1}
\]
for every \(U_N\in\mathcal B\), then
\[
 \mathcal H^q(Ra_*\mathscr E)=0
 \qquad
 (q\notin[r,s]).                                                   \tag{2}
\]

The assertion remains true in a complete locally convex derived
category once `(1)` is interpreted in its exact category and the
chosen derived direct image is computed by a resolution whose
restriction maps remain strict.

## Proof

Choose a \(K\)-injective representative \(I^\bullet\) of
\(\mathscr E\).  The complex \(a_*I^\bullet\) represents
\(Ra_*\mathscr E\).  For every open \(U\subseteq S\),
\[
 \Gamma(U,a_*I^\bullet)
 =
 \Gamma(a^{-1}U,I^\bullet),
\]
so the cohomology sheaf
\(\mathcal H^q(Ra_*\mathscr E)\) is the sheaf associated to the
presheaf
\[
 U\longmapsto
 H^qR\Gamma(a^{-1}U,\mathscr E).                                  \tag{3}
\]

Every point of \(S\) has a neighborhood basis inside \(\mathcal B\):
the generic point lies in every nonempty \(U_N\), and a closed point
\((p)\) lies in those \(U_N\) with \(p\nmid N\).  Assumption `(1)`
therefore makes every germ of `(3)` zero for \(q\notin[r,s]\).
Its sheafification is zero, proving `(2)`.

For the locally convex refinement, the same argument is applied to
the fixed strict resolution.  Strictness is not automatic; it is an
explicit hypothesis ensuring that cohomology in the exact category
and restriction to basis opens calculate the intended derived object.

## Deninger consequence

For
\[
 \mathscr E=\mathscr E_{\mathrm{Den}}
 =
 (\pi_*\widetilde{\mathscr A})^{\mathbb Q_{>0}},
\]
one need not construct local slices for the nonproper
\(\mathbb Q_{>0}\)-action.  It suffices to prove compatible strict
two-term contractions for
\[
 R\Gamma(a^{-1}U_N,\mathscr E_{\mathrm{Den}})
\]
for every nonzero \(N\).  Taking \([r,s]=[0,1]\) then gives the two
analytic rows required by
`DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`.

## Hostile audit

- A calculation only on the generic fibre is insufficient; every
  cofinite \(U_N\) is required.
- Vanishing of algebraic cohomology after a non-strict completion does
  not imply locally convex derived vanishing.
- The theorem does not prove `(1)` and does not commute invariants with
  cohomology.
- No quotient-stack object, CCM model, Xi zero, RH premise, or
  numerical computation occurs.

## Gates

- [x] 0 → 1 in-progress: source-pure and explicit
- [x] 1 → 2 fully-proven: basis/stalk proof complete
- [ ] 2 → 3 formalized: sheafification-on-basis theorem in Lean
- [ ] 3 → 4 publication-ready: standalone proof and Lean audit

## Novelty audit

The basis criterion for vanishing higher direct images is standard.
Its new role is to replace an invalid local-slice attack by the exact
cofinite arithmetic sections supplied by Deninger's projection.

## Log

- 2026-07-27 — proved and applied to isolate the finite-\(N\) analytic
  contraction as the first source gate.
