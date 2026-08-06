# Scalar recurrence / traceless circuit split

- **ID:** `scalar-recurrence-traceless-circuit-split`
- **Stage:** 3 — formalized
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [NEW MECHANISM]`
- **Parent:** `../1-in-progress/scalar-recurrence-traceless-replica-decoupling-law.md`
- **Statement:** Every static-Choi circuit-target union is contained in one
  common identity-recurrence event plus the union of orthogonal traceless
  target events.

## Exact law

Let

\[
 a(t)=|\operatorname{Choi}(e^{-itH})\rangle,
 \qquad e=a(0),\qquad \|a(t)\|=\|e\|=1.
\]

For every normalized target `u`, define

\[
 \alpha_u=\langle e,u\rangle,
 \qquad u^\circ=u-\alpha_ue.                                 \tag{1}
\]

Then

\[
 \langle e,u^\circ\rangle=0,qquad |\alpha_u|\le1,           \tag{2}
\]

and for every time `t`,

\[
 \langle a(t),u\rangle
 =\alpha_u\langle a(t),e\rangle+
   \langle a(t),u^\circ\rangle.                              \tag{3}
\]

More sharply, for every pair of real thresholds `theta,eta` and arbitrary
target family `A`,

\[
 \boxed{
 \bigcup_{u\in A}\{|\langle a(t),u\rangle|\ge\theta\}
 \subseteq
 \{|\langle a(t),e\rangle|\ge\eta\}
 \cup
 \bigcup_{u\in A}
   \{|\langle a(t),u^\circ\rangle|\ge\theta-\eta\}.}        \tag{4}
\]

No finiteness, measurability, spectral-genericity, or ensemble assumption is
used.  Equation `(4)` is deterministic for every finite static Hamiltonian.
The symmetric half-threshold split is the specialization `eta=theta/2`.

## Why it changes the frontier

The identity target lies in every ordinary circuit dictionary and has a
non-Haar positive replica-crowding floor.  Previous bounds paid that same
return channel once for every circuit word.  Equation `(4)` proves that this
loss is artificial: identity recurrence is one common event.  Circuit entropy
is charged only to target-specific directions orthogonal to identity.

This does not itself prove their anti-concentration.  It changes the missing
theorem from an impossible exponential upper bound on positive `Z_r` to the
signed traceless replica-decoupling conjecture in the parent card.

## Lean certificate

Module:
`RHTower/ScalarRecurrenceTracelessCircuitSplit.lean`

Declarations:

- `norm_common_or_residual_of_norm_linear_split_ge`
- `norm_common_or_residual_of_norm_linear_split_ge_budget`
- `staticChoiScalarComponent`
- `staticChoiTracelessResidual`
- `staticChoiTarget_eq_scalar_add_traceless`
- `inner_staticChoiTracelessResidual_zero`
- `norm_staticChoiScalarComponent_le_one`
- `inner_staticChoiTarget_scalar_traceless_decomposition`
- `staticChoiTarget_capture_scalar_or_traceless`
- `staticChoiTarget_capture_scalar_or_traceless_budget`
- `iUnion_staticChoiOverlapCaptureSet_subset_scalar_union_traceless`
- `iUnion_staticChoiOverlapCaptureSet_subset_scalar_union_traceless_budget`
- `sum_staticChoiTracelessSpectralCoefficient_eq_zero`
- `staticChoiTracelessReplicaSectorMass_eq_neg_complement`

Verification:

- `lake env lean GaloisForLFunctions/RHTower/ScalarRecurrenceTracelessCircuitSplit.lean` — pass
- axiom audit of core declarations — only `propext`, `Classical.choice`, and
  `Quot.sound`
- umbrella import added to `RHTower.lean`

## Hostile audit

- Orthogonal decomposition is elementary; novelty cannot be claimed for the
  Hilbert-space identity alone.
- Scientific delta is identifying it as the mandatory quotient before the
  growing-replica circuit union, proved necessary by the separate crowding
  floor.
- No anti-concentration, complexity growth, plateau, or recurrence rate is
  inferred from `(4)`.
- Final-paper use requires the central-limit floor and traceless decoupling
  bound also to be formalized; otherwise this remains infrastructure.

## Gates

- [x] 0 -> 1: exact statement and role fixed
- [x] 1 -> 2: complete proof
- [x] 2 -> 3: Lean proof and axiom audit
- [ ] 3 -> 4: only after parent conjecture closes

## Log

- 2026-08-06 — Exact scalar/traceless decomposition and arbitrary-union
  inclusion proved and wired into RHTower umbrella.
