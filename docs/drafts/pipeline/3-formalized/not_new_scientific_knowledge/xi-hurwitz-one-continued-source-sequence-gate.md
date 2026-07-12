# Xi--Hurwitz one continued-source sequence gate

- **ID:** xi-hurwitz-one-continued-source-sequence-gate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** top-down exact-value synthesis from the Xi--Hurwitz orientation closure
- **Statement:** One unconditional sequence of finite continued prime--Gamma Cauchy-source vectors has eventual nonnegative Weil values if and only if RH.

## Goal

Shrink the remaining source-positivity interface after the Xi--Hurwitz orientation closure theorem.
The input is no longer positivity on all regular Cauchy points or on the whole algebraic source
span.  It is eventual positivity along one countable sequence whose poles remain in the exact
domain of the analytically continued prime--Gamma source formula.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-domain sequence isolated
- [x] 1 → 2  fully-proven: complete proof by closure, continuity, and the orientation-energy identity
- [x] 2 → 3  formalized: Lean theorem `exists_continuedCauchyCore_sequence_eventually_nonnegative_iff_riemannHypothesis`
- [ ] 3 → 4  publication-ready: not independently publication-sized

## Theorem

There exists a sequence `V_n` in the finite algebraic span of Cauchy vectors based at continued
prime--Gamma source points such that

\[
  V_n\longrightarrow v_\Xi,
  \qquad
  \mathcal W(V_n)\longrightarrow-\mathcal E_\Xi,
\]

and

\[
  \mathrm{RH}
  \iff
  \mathcal W(V_n)\ge 0\quad\text{eventually}.
\]

The reverse implication is the exact value argument: an eventually nonnegative real sequence
cannot converge to a strictly negative value.  Thus `E_Xi = 0`, which is equivalent to RH.
Under RH, critical-line reflection fixes every divisor-multiplicity copy, so
the Weil quadratic value equals the squared norm on the entire Hilbert carrier.

## Research consequence

The remaining positive problem is now specific: identify or bound the finite source values
`W(V_n)` for this sequence using an independently positive prime--Gamma value family.
Proving an all-point anti-Herglotz condition, full Cauchy-core positivity, or an arbitrary Weil
criterion is unnecessary and would merely reintroduce an RH-equivalent universal hypothesis.

## Lean certificate

- `formal/GaloisForLFunctions/RHTower/XiHurwitzOrientationSourceSequenceGate.lean`
- `xiZeroCopyLineConjEquiv_eq_of_riemannHypothesis`
- `xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis`
- `exists_continuedCauchyCore_sequence_eventually_nonnegative_iff_riemannHypothesis`

## Log

- 2026-07-12 — formalized the one-sequence continued-source RH gate.
