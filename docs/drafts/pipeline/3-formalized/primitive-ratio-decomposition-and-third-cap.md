# The primitive-ratio decomposition of the mean square, and the third cap

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## What was asked

The route triage of `coefficient-free-cap-law.md` concluded: a surviving route must use the coefficient
signs at essentially every frequency and may not majorise through `‖a_n‖`; the only objects in
`RHTower/Sieve` with that shape are the exact off-diagonal identities. This card attacks the first of
them, `DirichletDiagonal.integral_normSq_dirPoly_sub_diag`.

## What was proved

**1. The index bijection.** `RHTower/Sieve/PrimitiveRatioDecomposition.lean`. Grouping the off-diagonal
pairs of `[1,N]²` by `d = gcd(m,n)` is a bijection onto triples `(d, m', n')` with `m' ⊥ n'`, `m' ≠ n'`,
`dm', dn' ≤ N`:

* `sum_offDiagPairs_eq_sum_primitiveTriples` — the bijection, for an arbitrary summand;
* `sum_fin_erase_eq_sum_filter`, `sum_fin_offDiag_eq_sum_offDiagPairs` — the `Fin N` off-diagonal double
  sum in single-`Finset` form and shifted to `[1,N]`;
* `ratioScales_eq_Icc` (in the sibling file) — the scales are the initial segment `d ≤ N / max(m,n)`;
* `sum_fin_offDiag_eq_sum_ratio` — the combined statement: `∑_{m≠n} f(m,n) = ∑_{m ⊥ n} ∑_d f(dm, dn)`.

**2. The identity.** `RHTower/Sieve/DirichletOffDiagonalCorrelation.lean`. Since the kernel sees only the
ratio (`ratioKernel_mul_left`),

`∫_0^T |F|² − T ∑_n |a_n|² = ∑_{m ⊥ n, m ≠ n} C(m,n) · K_T(m,n)`,
`C(m,n) = ∑_{d ≤ N/max(m,n)} a_{dm} conj(a_{dn})`

(`integral_normSq_dirPoly_sub_diag_ratio`), together with `norm_ratioKernel_le` and
`norm_le_sum_norm_correlation_mul` showing the form is never weaker than the classical mean value theorem
(one term per *coprime* pair instead of one per pair).

**3. The third cap.** `RHTower/Sieve/DirichletCorrelationMultiplicative.lean`. For a completely
multiplicative unimodular `g` the scale sum evaluates exactly, because
`g(dm) conj(g(dn)) = ‖g(d)‖² g(m) conj(g(n))`:

* `dirCorrelation_completelyMultiplicative` — `C(m,n) = g(m) conj(g(n)) · ⌊N/max(m,n)⌋`;
* `integral_normSq_dirPoly_completelyMultiplicative` —
  `∫_0^T |F|² = TN + ∑_{m ⊥ n, m ≠ n} g(m) conj(g(n)) ⌊N/max(m,n)⌋ K_T(m,n)`;
* `norm_dirCorrelation_eq_norm_one` — `‖C(m,n)‖` is **the same for every** unimodular completely
  multiplicative `g`, so it cannot distinguish `μ` or `λ` from `1`;
* `le_bound_of_norm_dirCorrelation` — hence, via `RHTower.le_bound_of_invariant_collision`, any bound
  routed through the correlation moduli is capped at its value on the constant sequence.

All `#print axioms` checks give `[propext, Classical.choice, Quot.sound]`.

## What this means for the route

Two readings, and both are informative.

*Negative.* The scale sum carries **no** cancellation for the sequences of interest — every term in
`C(m,n)` has the same phase. So the inner sum of the primitive-ratio decomposition is not a place where
anything can be won, and passing to `‖C‖` at any point reinstates the cap of
`CoefficientFreeCap.le_of_coefficientFree_bound` one level deeper. This is the third member of the family
(`modulus-first-vertical-integral-no-go`, `ghs-prime-saving-master-bound-is-trivial`, this).

*Positive.* The identity is exact and its right-hand side is an explicit Hermitian form: the weight
`⌊N/max(m,n)⌋` is real and positive, the kernel satisfies `K_T(n,m) = conj K_T(m,n)`, and all of the
arithmetic is the phase vector `(g(m))_{m ≤ N}` tested against a **fixed** matrix supported on the coprime
off-diagonal. Non-negativity of `∫|F|²` is exactly the statement that this matrix is `⪰ −T·I` on the
unimodular vectors. That is a spectral question about an explicit arithmetic matrix, in the same family as
the Hilbert-matrix layer the corpus already owns (`hilbert-matrix-operator-theory-corpus`), and it is the
first formulation in this folder in which the coefficients appear *only* as a unit vector — no moduli, no
majorisation, hence no cap applies to it by construction.

## Next

The live question is the smallest eigenvalue of `M_{mn} = [m ⊥ n, m ≠ n] ⌊N/max(m,n)⌋ K_T(m,n)` on
unimodular vectors, and whether the corpus's Hilbert-matrix norm bound (`‖H‖ ≤ π`) transfers to it after
the dyadic decomposition of `⌊N/max⌋`.
