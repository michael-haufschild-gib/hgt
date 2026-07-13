# Nonzero orbit degree cannot be zero-class

- **ID:** orbit-degree-nonzero-not-zero-class
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/seam-two-lattices-archimedean-residue.md` section "The two
  lattices", using the orbit-degree algebra of `../2-fully-proven/two-sources-of-hypertranscendence.md`.
- **Statement:** In the finite orbit-degree model, a divisor whose orbit degree is nonzero cannot equal any
  divisor of orbit degree zero; in particular, a nonzero point-mass cannot lie in the zero-degree class.

## Goal

This banks the exact group-invariant core behind the seam card's statement that a non-CC archimedean orbit
class cannot be in the CC/prime zero-degree span. It does not formalize rational-function divisors,
multiplier classes in `C(z)^*`, the full CC equivalence, the digamma residue, or the tensor decomposition of
`M_Lambda`.

## Paper Proof

Define the orbit degree of a finite integer divisor as the sum of its coefficients. If two finite divisors are
equal, then applying the orbit-degree map gives equal degrees. Therefore, if `deg(D) != 0` and `deg(E)=0`,
then `D=E` would imply `deg(D)=0`, a contradiction.

For a point-mass `n[a]`, the orbit degree is `n`; hence if `n != 0`, `n[a]` cannot equal any degree-zero
divisor. This is the finite algebraic witness for the paper phrase "non-CC is not in the CC subgroup" after
passing through the orbit-degree classifier.

## Gates

- [x] 0 -> 1  in-progress: exact invariant separation extracted from the seam/two-lattices card.
- [x] 1 -> 2  fully-proven: paper proof above by applying the orbit-degree homomorphism to a hypothetical
  equality.
- [x] 2 -> 3  formalized: Lean theorems `orbitDegree_ne_zero_ne_of_orbitDegree_zero` and
  `orbitDegree_single_ne_zero_ne_of_orbitDegree_zero` in
  `formal/GaloisForLFunctions/HTGeometry/OrbitBalance.lean`; names checked by scratch file; `#print axioms` uses only the
  allowed standard subset `[propext, Classical.choice, Quot.sound]`; `lake build` green; `check_axioms.sh`
  PASS.
- [ ] 3 -> 4  publication-ready: include as the finite orbit-degree separation lemma in the seam/two-lattices
  note.

## Door Passport

Door-2 strips this to a finite abelian-group/invariant argument, so it is BRIDGE. Its value is as the
Lean-certified finite algebraic floor for the CC-class non-lift obstruction.

## Log

- 2026-06-19 - Leaner added the Lean theorem and this synced paper-proof ticket while formalizing the
  two-lattices seam card. The parent card remains in `2-fully-proven` because its analytic digamma residue,
  multiplier-class, and tensor-product claims are not fully Lean-formalized.
