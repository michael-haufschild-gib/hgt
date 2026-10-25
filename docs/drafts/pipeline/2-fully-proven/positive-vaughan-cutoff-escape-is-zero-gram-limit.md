# Positive cutoff escape is exactly the zero subcritical Gram limit

- **ID:** positive-vaughan-cutoff-escape-is-zero-gram-limit
- **Stage:** 2-fully-proven
- **Type:** CLAIM (Lean verification pending)
- **Verification:** UNPROVED. The argument below is not a certified result until its Lean proof and transitive axiom audit pass; checked component lemmas are identified separately.
- **Source:** ../2-fully-proven/vaughan-subcritical-gram-limit-classification.md
- **Statement:** With positive cutoffs and a divergent horizon, the normalized subcritical centered Gram tends to zero exactly when the cutoff product diverges.

## Statement

For positive natural cutoff schedules `U(t),V(t)` and `H(t)→∞`,

`G^c(H(t);U(t),V(t))/H(t)^(1-2ε) → 0  iff  U(t)V(t)→∞`

for every `0<ε<1/2`.

## Dependency-closed paper proof

[LEAN VERIFICATION PENDING] Write `a_t=H_(U(t))²H_(V(t))²` and `β=1-2ε`. The uniform Gram law
and `subHalfZetaCoeff(ε)≠0` show that the normalized `(2,2)` entry tends to zero
if and only if `a_t→0`. If this holds, the same uniform law makes every matrix
entry tend to zero. Thus it suffices to characterize `a_t→0`.

If `U(t)V(t)→∞`, the checked bounded-product-index lemma applies to the bounded
sequence `H_N→0`, giving `H_(U(t))H_(V(t))→0`, hence `a_t→0`.

Conversely suppose `a_t→0` but the cutoff product does not diverge. There is a
finite bound `B` for which `U(t)V(t)≤B` occurs arbitrarily far out. Positivity of
both cutoffs gives `1≤U(t),V(t)≤B` on those indices. Every amplitude in the
finite rectangle `1≤U,V≤B` is strictly positive by finite harmonic nonvanishing.
Its finite set of values therefore has a positive minimum `m_B`. The assumed
convergence gives `a_t<m_B` eventually, contradicting those arbitrarily late
bounded-product indices. This proves the converse.

## Exact convergence dichotomy

With positive cutoffs, the normalized centered Gram has a finite entrywise limit
if and only if one of the following mutually exclusive alternatives holds:

1. `U(t)V(t)→∞`; its limit is zero.
2. There is a positive real `a` such that `a_t=a` eventually; its limit is
   `(subHalfZetaCoeff(ε)²/β)a ssᵀ`, with `s=(0,0,-1,1,0)`.

For necessity, the subcritical limit classification gives an amplitude `a∈S`.
If `a=0`, the preceding equivalence applies. If `a>0`, finite-fiber rigidity
makes `a_t` eventually exactly equal to `a`. For sufficiency, each alternative
and the uniform Gram error directly give the asserted matrix limit. The second
alternative automatically uses an amplitude realized by fixed positive cutoffs,
and confines the cutoff pair to one finite fiber.

Zero cutoffs cannot be admitted to the converse: a permanently zero cutoff has
zero smooth amplitude at a bounded product. The uniform Gram paper itself still
includes zero cutoffs; only the escape equivalence needs positivity.

## Status

Corpus search found logarithmic harmonic limits and the known sufficient
product-divergence mechanism, without an indexed exact converse for positive
Vaughan cutoffs. This is an internal audit, not an external novelty claim.
The finite harmonic nonvanishing and uniform Gram leaves are checked. The
harmonic amplitude escape equivalence passed producing and final direct checks
in `TheCompactArithmeticAmplitudesOfVaughanGrams.lean`, with only standard
transitive axioms. The matrix converse, convergence dichotomy,
and exact attained matrix limit set are drafted in
`/tmp/QIVaughanGramLimitClassificationTools.lean`; that leaf is under verification.
No quantitative rate for escaping cutoffs or fixed zero-free strip follows.
