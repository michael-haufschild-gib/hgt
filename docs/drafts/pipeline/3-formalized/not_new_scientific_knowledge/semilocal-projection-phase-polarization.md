# Semilocal projection phase polarization

- **ID:** `semilocal-projection-phase-polarization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[TOP-DOWN GAP REDUCTION]`, `[NOT AN RH PROOF]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/sonin-prime-seam-exterior-factorization.md`
- **Statement:** Canonically phase-rotating one self-adjoint projection tangent converts the
  symmetric mixed-curvature identity into the antisymmetric normal Gram exactly; compactness of
  only the base-compressed mixed derivative therefore forces compactness of the orientation
  sector, and exact real--imaginary polarization wires that sector to the finite Euler Gram.

## Goal

The semilocal Euler chart already produces actual Sonin prime normals, but the existing mixed
derivative theorem sees their symmetric Gram while the RH-facing prime seam is antisymmetric.
Close that algebraic mismatch without assuming a separate connection-curvature identity from the
source.

## Theorem

For a self-adjoint idempotent `P` and a self-adjoint operator `D`, define

\[
J_P(D)=i\big((1-P)DP-PD(1-P)\big).
\]

Lean proves:

\[
J_P(D)^*=J_P(D),\qquad
J_P(D)P+PJ_P(D)=J_P(D),
\]

and

\[
(1-P)J_P(D)P=i(1-P)DP.
\]

Let `F(s,t)` be a two-parameter idempotent family based at `P`, with `t`-tangent `D_t`,
`s`-tangent `J_P(D)`, and mixed derivative `D_{st}`. Then

\[
P D_{st} P
=-i\left(B_t^*B_D-B_D^*B_t\right),
\qquad B_X=(1-P)XP.
\]

When `D` is itself tangent, the bracket is exactly the connection curvature:

\[
P D_{st}P=-i\,P(D_tD-DD_t)P.
\]

Consequently,

\[
P D_{st}P\text{ compact}
\Longrightarrow
B_t^*B_D-B_D^*B_t\text{ compact}.
\]

The hypothesis is strictly localized: compactness of the full mixed derivative and compactness of
the entire projection family relative to `P` are not required.

## Top-down consequence

The finite Sonin extraction problem no longer needs two independently supplied curvature sectors.
It is enough to construct a completed prime--Gamma two-parameter projection family whose first
directions are:

1. a real seam-weighted Euler `t`-tangent;
2. the canonical phase rotation of the unweighted universal Euler `s`-tangent;

and prove that its **base-compressed** mixed derivative is compact on each Xi zero fibre. Splitting
the complex seam packet into real and imaginary parts then gives two such real phase-polarized
families. Their compact skew Grams recombine into the complex finite seam orientation Gram already
proved Calkin-faithful in Lean.

This is a constraint formulation. The phase rotation is algebraic at the fixed base projection;
no projection flow, zero enumeration, or limiting divisor measure is introduced.

Lean also proves the exact source wiring. For every complex packet `u`,

\[
G(u)=G(\operatorname{Re}u)+iG(\operatorname{Im}u),
\]

and for a real packet `v`,

\[
G(v)=B_v^*B_1-B_1^*B_v.
\]

Thus two phase-polarized families with compact compressed mixed derivatives, one for
`Re u` and one for `Im u`, make the complete complex finite Euler orientation Gram compact. This
is the operator to which the existing finite Calkin-faithfulness theorem applies.

## Open core

`[OPEN CORE]` Construct the two completed semilocal prime--Gamma families and prove compactness of
their base-compressed mixed derivatives on actual Xi zero fibres. The theorem does not manufacture
that source--divisor value relation. Finite quasi-innerness alone is insufficient because an
individual prime ratio is not quasi-inner; the phase rotation and the compact cancellation must be
performed inside the completed finite product.

## Lean certificate

Modules:

- `formal/GaloisForLFunctions/RHTower/SemilocalProjectionPhasePolarization.lean`
- `formal/GaloisForLFunctions/RHTower/SemilocalEulerPhasePolarization.lean`

Main declarations:

- `projectionPhaseRotation`
- `projectionNormalCorner_phaseRotation`
- `adjoint_projectionPhaseRotation`
- `projectionPhaseRotation_tangent`
- `selfAdjointIdempotentFamily_phaseRotated_mixed_identity`
- `selfAdjointIdempotentFamily_phaseRotated_mixed_eq_connectionCurvature`
- `selfAdjointIdempotentFamily_phaseRotated_normalSkewGram_isCompact`
- `finiteEulerOrientationMatrix_re_im`
- `finiteArchimedeanEulerOrientationGram_re_im`
- `finiteArchimedeanEulerOrientationGram_ofReal_eq_boundarySkew`
- `finiteArchimedeanEulerOrientationGram_isCompact_of_re_im_boundarySkew`
- `finiteArchimedeanEulerOrientationGram_isCompact_of_phaseRotatedFamily`

## Gates

- [x] canonical phase rotation constructed
- [x] self-adjointness and tangent constraint proved
- [x] exact normal-corner quarter-turn proved
- [x] exact phase-polarized mixed-curvature identity proved
- [x] connection-curvature reformulation proved
- [x] compressed-mixed compactness transfer proved
- [x] exact real--imaginary finite Euler orientation decomposition proved
- [x] real finite Euler orientation identified with the literal boundary skew Gram
- [x] phase-rotated family compactness wired to the finite Euler Calkin operator
- [x] module imported by the `RHTower` umbrella
- [ ] completed prime--Gamma phase families constructed
- [ ] Xi-zero-fibre compressed mixed derivative proved compact
