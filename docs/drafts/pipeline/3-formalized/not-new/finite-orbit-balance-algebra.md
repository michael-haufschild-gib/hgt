# Finite orbit-balance algebra

- **ID:** finite-orbit-balance-algebra
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/two-sources-of-hypertranscendence.md`, orbit-balance criterion core
- **Statement:** For finite integer divisors on an orbit, orbit degree is additive, nonzero orbit degree separates a divisor from every degree-zero divisor, balanced point-masses have degree zero, every degree-zero divisor decomposes into balanced point-masses against a base point, and finite shift coboundaries have degree zero.

## Goal
This banks the finite augmentation-kernel algebra behind the sigma-orbit-balance criterion. It does not formalize rational-function divisors, the full constant-up-to-coboundary equivalence in `C(z)^*`, the `q`-orbit analog, or the Holder/ADH hypertranscendence import.

## Paper Proof
Model a finite divisor on an orbit by a finitely supported function `D : alpha ->_fin Z`, and define its orbit degree as the sum of its coefficients.

The zero divisor, single point-mass, additivity, and subtraction rules follow immediately from finite sums. A balanced point-mass `n[a]-n[b]` has degree `n-n=0`.

If `deg(D) ≠ 0` and `deg(E)=0`, then `D ≠ E`, because equality would force `deg(D)=deg(E)=0`. In particular,
a nonzero point-mass cannot equal any degree-zero divisor. This is the finite orbit-degree core of the
"non-CC is not in the CC subgroup" separation after the multiplier classes have been mapped to orbit degrees.

If `deg(D)=0` and `base` is fixed, then
`D = sum_{a in supp D} D(a)[a]`. Since `sum_a D(a)=0`, the base terms also sum to zero:
`sum_a D(a)[base]=0`. Hence
`D = sum_a (D(a)[a] - D(a)[base])`, a finite sum of balanced point-masses.

On the integer orbit, each consecutive shift term `[z-1]-[z]` has degree zero, so any finite sum of such terms has degree zero. The explicit rightward telescoping identity follows by summing consecutive differences along the path from `base` to `base+k`.

## Gates
- [x] 0 -> 1  in-progress: finite orbit-degree algebra extracted.
- [x] 1 -> 2  fully-proven: paper proof above, using only finite sums and telescoping.
- [x] 2 -> 3  formalized: Lean theorems `orbitDegree_zero`, `orbitDegree_single`, `orbitDegree_add`, `orbitDegree_sub`, `orbitDegree_ne_zero_ne_of_orbitDegree_zero`, `orbitDegree_single_ne_zero_ne_of_orbitDegree_zero`, `orbitDegree_single_sub_single`, `eq_sum_single_sub_base_of_orbitDegree_zero`, `orbitDegree_intShiftCoboundary`, and `sum_intShiftTerm_right` in `formal/GaloisForLFunctions/OrbitBalance.lean`; `lake build` green; `check_axioms.sh` PASS.
- [ ] 3 -> 4  publication-ready: include as the finite algebra lemma in the orbit-balance invariant note.

## Log
- 2026-06-19 — Leaner split this exact finite augmentation-kernel algebra from `two-sources-of-hypertranscendence`. The parent card remains in `2-fully-proven` because the rational divisor layer, full CC equivalence, `q`-orbit analog, and hypertranscendence import are not fully Lean-formalized.
- 2026-06-19 — Leaner corrected the certificate to include the already-audited degree-separation theorems `orbitDegree_ne_zero_ne_of_orbitDegree_zero` and `orbitDegree_single_ne_zero_ne_of_orbitDegree_zero`.
