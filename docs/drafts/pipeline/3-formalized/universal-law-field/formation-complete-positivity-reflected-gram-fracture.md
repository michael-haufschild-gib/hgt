# Formation-complete positivity and reflected Gram fracture

- **ID:** ULF-FCP-RGF
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Lean-corpus synthesis: `SourceHorizontalSharedReservoirAmplification`,
  `HedenmalmThetaSourceShellReplicaWardDoubleProperness`,
  `ConstitutiveFunctionalEquationPacketLift`
- **Statement:** Weighted codiagonal recovery, shared-reservoir inertia, and reflected
  three-slot positivity are one Gram identity; simultaneous positive completion of both
  orientations forces neutral horizontal grade.

## 1. Higher-law interpretation

Positivity is not a scalar sign. It is stability of one source response under arbitrary finite
formation amplification. Local energy, fused recovery energy, and the Krein reservoir are the
diagonal, rank-one, and cross terms of one Gram law. Functional-equation reflection reverses only
the cross term. A source phase quotient that is positive in both orientations must therefore kill
the oriented class. Nonclosable infinite codiagonals and unbounded negative index are infinite and
finite shadows of the same failure of formation-complete positivity.

## 2. Corpus audit before statement

Fresh `scripts/formal_tools.py research` searches established:

- `sourceSharedReservoirMatrix w = diagonal(w) - vv^T`, where `v_i = sqrt(w_i)`;
- its quadratic form has inertia `(m-1,1,0)` for positive weights and `m >= 2`;
- Xi reflection negates the oriented reservoir and preserves its absolute weights;
- high-shell formation supplies disjoint provenance and a constant-weight codiagonal whose
  recovery is nonclosable exactly off the wall;
- functional-equation packet lift through common recovery is information-neutral;
- no declaration identifies the reservoir with the weighted codiagonal Gram defect or classifies
  both reflected diagonal completions.

Big-Witt Frobenius/reflection, ABHN trace-zero globalization, multiplicative recovery, and Fock
scalarization were audited and rejected: respectively exact compensator cancellation, failure to
preserve quadratic form, wrong reporter type, and phase-blind/nonclosable scalarization.

## 3. Exact RH closure

For an Xi copy `q`, let `B_q` be its oriented shared-reservoir form and `D_q` the diagonal absolute
prime energy. Corpus proves `B_reflect(q) = -B_q` and all weights are positive off wall. If one
source-derived functional-equation recovery proves both completed forms `D_q + B_q` and
`D_q + B_reflect(q)` nonnegative on every three-prime packet, Theorem 3 below forces
`Re(q)=1/2`. Quantifying over Xi support closes RH through the existing
`riemannHypothesis_iff_xi_zero_re_eq_half` endpoint. The missing theorem is exactly
that source-derived simultaneous positive landing; it is not asserted here.

## Definitions

Fix `m >= 1` and positive weights `w_i > 0`. Put

`v_i = sqrt(w_i)`,

`D_w(x) = sum_i w_i x_i^2`,

`T_w(x) = sum_i v_i x_i`,

`R_w(x) = D_w(x) - T_w(x)^2`.

`R_w` is the corpus shared-reservoir quadratic form. Define reflected diagonal completions

`K_w^+(x) = D_w(x) + R_w(x)`,

`K_w^-(x) = D_w(x) - R_w(x)`.

## Theorem 1 — exact fusion identity `[PROVED HERE]`

For every `x`,

`R_w(x) = D_w(x) - T_w(x)^2`,

`K_w^-(x) = T_w(x)^2 >= 0`,

`K_w^+(x) = 2 D_w(x) - T_w(x)^2`.

Consequently the two orientations jointly reconstruct both constituents:

`K_w^+(x) + K_w^-(x) = 2 D_w(x)`,

`K_w^+(x) - K_w^-(x) = 2 R_w(x)`.

### Proof

The first equality is the definition of the weighted reservoir form, equivalently expansion of
`diagonal(w) - vv^T`. Subtracting it from `D_w` gives `T_w^2`; adding it gives
`2D_w-T_w^2`. A square is nonnegative. ∎

## Theorem 2 — sharp formation-depth threshold `[PROVED HERE]`

For `m >= 1`, `K_w^+` is nonnegative on all vectors iff `m <= 2`. More precisely:

- if `m=1`, `K_w^+=D_w`;
- if `m=2`, `K_w^+(x)=(v_1x_1-v_2x_2)^2`;
- if `m>=3`, `K_w^+` is negative at `x_i=1/v_i`.

### Proof

For `m=1`, `T_w^2=D_w`. For `m=2`, expansion gives
`2D_w-T_w^2=(v_1x_1-v_2x_2)^2`. If `m>=3`, positivity of `w_i` makes every `v_i` nonzero. At
`x_i=1/v_i`, one has `D_w(x)=m` and `T_w(x)=m`; hence

`K_w^+(x)=2m-m^2=m(2-m)<0`.

This proves both directions. ∎

## Theorem 3 — reflected complete-positivity selector `[PROVED HERE]`

Let `B` be either `R_w` or `-R_w`, with `m>=3` and all weights positive. The two reflected
completions `D_w+B` and `D_w-B` cannot both be nonnegative. Equivalently, if both are nonnegative,
then at least one weight is zero or formation depth is at most two.

### Proof

The unordered pair `{D_w+B,D_w-B}` equals `{K_w^+,K_w^-}`. Theorem 1 makes `K_w^-`
nonnegative; Theorem 2 makes `K_w^+` negative when `m>=3` and all weights are positive. ∎

## Corollary 4 — Xi three-prime selector `[PROVED HERE]`

Fix an Xi divisor copy and three prime labels. If its absolute source weights and those of its
functional-equation reflection give nonnegative diagonal completions for both oriented
shared-reservoir forms, then the copy lies on the critical line.

### Proof

If the copy were off wall, corpus coefficient faithfulness makes all three weights positive and
reflection negates the reservoir while preserving those weights. Theorem 3 contradicts the two
nonnegativity assumptions. Therefore it is on wall. ∎

## Fourth-organ prediction

The finite three-slot obstruction predicts the infinite shell theorem: repeated equal-weight
label-forgetting recovery has Gram defect `R_w`; its positive reflected completion fails already
on three labels, while normalized growing packets expose the same defect as a vertical limit and
destroy closability. Thus any source-positive recovery that survives reflection must retain
provenance or annihilate the horizontal response. This prediction agrees with the independently
proved shell-replica graph-null theorem; it was not used in Theorems 1–3.

## Hostile audit

- The algebraic theorem is not RH and does not claim simultaneous source positivity.
- Declaring both completions positive would be an RH-equivalent receiver unless realized as the
  Gram matrices of one fixed pre-divisor source recovery and its already-constructed FE lift.
- Positivity of one orientation is insufficient; one completion is always the rank-one square.
- Two labels are insufficient; depth three is the first separating formation.
- No scalar trace, total Ward cancellation, Fock norm, or divisor replication supplies the open
  source landing.

## Gates

- [x] 0 → 1: source-pure statement, corpus audit, exact RH chain, hostile audit
- [x] 1 → 2: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3: `FormationCompletePositivityReflectedGramFracture.lean`; direct check,
  leaf build, closed axiom audit, and `UniversalLawField` umbrella wiring passed
- [ ] 3 → 4: publication-ready synthesis

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.FormationCompletePositivityReflectedGramFracture`
- Closed theorem: `formationCompletePositivityReflectedGramFractureLaw`
- Axioms: `[propext, Classical.choice, Quot.sound]` only; no project axiom, `sorry`, `admit`,
  `opaque`, or `unsafe`
