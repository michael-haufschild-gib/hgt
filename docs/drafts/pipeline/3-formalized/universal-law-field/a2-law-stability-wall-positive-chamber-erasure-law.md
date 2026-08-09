# A2 law-stability wall and positive chamber-erasure law

- **ID:** ULF-LSW-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveStabilityWall`
- **Source:** universal-law-field speculative tournament
- **Statement:** One fixed exact law changes from stable to unstable across a phase wall while every natural modulus-only observer remains unchanged.

## Goal

Test a stronger reinterpretation than observer loss: constitutive phase data may change which proof
composites are admitted even when the underlying algebra, exact sequence, dimensions, and positive
sizes are fixed.

## Gates

- [x] 0 → 1: finite quiver model and explicit wall
- [x] 1 → 2: complete classification proof below
- [x] 2 → 3: Lean-certified in `GaloisForLFunctions.HTGeometry.ConstitutiveStabilityWall`
- [ ] 3 → 4: no publication/priority claim

## 1. Fixed exact law

Let (Q) be the quiver (1\to2) over (\mathbb C). Write

\[
S_1=(\mathbb C\to0),\qquad
S_2=(0\to\mathbb C),\qquad
E=(\mathbb C\xrightarrow{1}\mathbb C).
\]

There is a nonsplit exact sequence

\[
0\longrightarrow S_2\longrightarrow E\longrightarrow S_1\longrightarrow0.
\tag{1}
\]

Choose a stability function (Z:K_0(\operatorname{Rep}Q)\to\mathbb C) with
(z_i=Z(S_i)) in the open upper half-plane. The phase of a nonzero object is
(\phi(X)=\arg Z(X)\in(0,\pi)). An object is stable when every nonzero proper subobject has
strictly smaller phase.

## Theorem 1 — complete wall classification

The representation (E) has exactly one nonzero proper subobject, namely (S_2). If
(\arg z_1\ne\arg z_2), then

\[
E\text{ is stable}\quad\Longleftrightarrow\quad
\arg z_2<\arg z_1.
\tag{2}
\]

When (\arg z_1=\arg z_2), (E) is strictly semistable.

### Proof

A subrepresentation of (E) is a pair (U_1,U_2\subseteq\mathbb C) satisfying
(U_1\subseteq U_2). The only possibilities are (0,S_2,E). Hence stability is exactly
(\arg z_2<\arg(z_1+z_2)). For two non-collinear vectors in the upper half-plane, the
argument of their sum lies strictly between their arguments. This proves (2); equality gives the
semistable wall. ∎

## Theorem 2 — positivity identifies opposite law chambers

For (0<|\theta|<\pi/2), set

\[
z_1(\theta)=e^{i(\pi/2+\theta)},\qquad
z_2(\theta)=e^{i(\pi/2-\theta)}.
\tag{3}
\]

Then (E) is stable for (\theta>0), unstable for (\theta<0), and semistable at
(\theta=0). Nevertheless the entire modulus packet

\[
\bigl(|z_1|,|z_2|,|Z(E)|\bigr)
=\bigl(1,1,2|\cos\theta|\bigr)
\tag{4}
\]

is identical at (\theta) and (-\theta).

Therefore no rule factoring only through the three positive moduli in (4) can determine whether
the fixed extension law (E) is stable.

### Proof

The phase order in (3) reverses under (\theta\mapsto-\theta), so Theorem 1 gives the
stability statements. Also

\[
z_1(\theta)+z_2(\theta)=2i\cos\theta,
\]

which proves (4). ∎

## 2. Interpretation and falsifier

This model separates three levels:

1. the algebraic exact law (1), which never changes;
2. the constitutive phase order, which changes the admitted stable composite;
3. its positive modulus quotient, which identifies opposite chambers.

Thus observer change need not merely erase information about a fixed theorem. It can change the
effective factorization doctrine of the theorem category itself.

The result does **not** say every proof system carries a Bridgeland stability condition. The
field-level hypothesis dies unless source data canonically supply:

- a Grothendieck-type charge group;
- a complex central charge or ordered phase object;
- a source-native class of sublaws/factorizations;
- a wall-crossing rule compatible with proof composition.

Absent those, "law stability" is fitted language.

## 3. Literature scope

Stability conditions and wall crossing are established mathematics. This card claims only a sharp
finite calibration for the universal-law-field programme: positivity can erase the side of a
constitutive wall even while the underlying exact law stays fixed.

## Log

- 2026-08-09 — complete (A_2) classification and positive chamber countermodel recorded; no Lean.

## Lean certification status (2026-08-09) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveStabilityWall`
(wired into `HTGeometry.UniversalLawField`).

Theorem 1: `subrep_classification` and `subrep_proper_nonzero` — a subrepresentation of
`E = (ℂ →id ℂ)` is a pair of subspaces with `U₁ ≤ U₂`, and there are exactly three, so the unique
nonzero proper subobject is `S₂`. `stability_iff` proves the wall criterion
`arg z₂ < arg (z₁ + z₂) ↔ arg z₂ < arg z₁` for charges in the open upper half-plane, and
`arg_eq_of_arg_eq` proves strict semistability on the wall `arg z₁ = arg z₂`.

The phase-order engine is `arg_lt_arg_iff_cross_pos`: in the open upper half-plane
`arg w < arg z ↔ 0 < Im(z · conj w)`, proved through `arg_div_eq_sub`
(`arg (z/w) = arg z − arg w` there). Since `Im(z₂ · conj z₂) = 0`, the criterion for the sum
collapses to the criterion for `z₁`, which is exactly the card's "the argument of the sum of two
non-collinear upper half-plane vectors lies strictly between their arguments".

Theorem 2: `wallCharge₁`, `wallCharge₂`, `wallCharge_im_pos`, `wallCharge_cross`
(`Im(z₁ conj z₂) = sin 2θ`), `wallFamily_stable_iff_pos` (stable exactly for `θ > 0`),
`wallCharge_sum` (`z₁ + z₂ = 2i cos θ`), `wallFamily_modulus_packet` (`(1, 1, 2|cos θ|)`),
`wallFamily_modulus_packet_symm` and the capstone `positive_chamber_erasure`.

`#print axioms` on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
