# Semilocal projection phase polarization

- **ID:** `semilocal-projection-phase-polarization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[TOP-DOWN GAP REDUCTION]`, `[NOT AN RH PROOF]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/sonin-prime-seam-exterior-factorization.md`
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

## Literature audit — 2026-08-20

`[LITERATURE]` This card's fixed-base projection algebra is standard operator geometry, not a
new analytic construction.  Kato's perturbation theory covers differentiable spectral-projection
calculus when a suitable isolated spectral subspace is available.

`[LITERATURE]` Connes--Consani, *Quasi-inner functions and local factors*, J. Number Theory 226
(2021), 139--167, prove compact Hardy off-diagonal blocks for a **completed finite product** of
local factors and prove that individual non-archimedean local ratios are not quasi-inner.  That is
the correct literature antecedent for the completed, rather than one-prime, compact cancellation
required here; it contains neither a two-parameter projection jet nor an Xi-fibre mixed-curvature
identity.

`[LITERATURE]` Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators: semilocal
adelic operators*, Ann. Funct. Anal. 15 (2024), Art. 87, prove stability of semilocal Sonin spaces
and propose a semilocal prolate operator.  They explicitly leave a further candidate to future
work.  Their result supplies an operator setting, not the completed differentiable family in this
card.

`[LITERATURE]` Their subsequent preprint *Zeta Spectral Triples* (arXiv:2511.22755, 2025)
constructs a different finite-Euler-product rank-one-perturbation model.  Its Section 8 explicitly
lists two missing convergence steps.  Connes' 2026 survey (arXiv:2602.04022, §7.4) recalls
semilocal sharp time/frequency projections `P_T^S` and `P_hat_W^S`, but does not state a
norm-differentiable two-parameter prime--Gamma family or the compact compressed mixed derivative
required above.

`[CORPUS]` The sharp cutoff family cannot itself fill the Lean hypothesis: for distinct cutoffs,
the corresponding multiplication projections differ by norm one on a non-null annulus.  Hence it
is not norm-continuous, let alone norm-differentiable.  The formal endpoint's `HasDerivAt`
assumptions demand a genuinely new smooth source, not a restatement of the standard cutoff
projections.

`[OPEN CORE]` Limited primary-source audit found no paper asserting the exact source theorem:
a norm-differentiable completed semilocal two-parameter projection family whose normal corners are
the actual prime--Gamma/Sonin directions and whose base-compressed mixed derivative is compact on
Xi fibres.  This is a project-local open core, **not** a claim that the question is a named or
globally unproved problem.  Any proposed construction must first prove its source-to-operator
identification before zero-fibre specialization; otherwise the existing Calkin equivalence makes
the assertion circular with RH.
