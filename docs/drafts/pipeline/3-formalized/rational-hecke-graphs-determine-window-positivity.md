# Rational Hecke graphs determine window positivity

- **ID:** rational-hecke-graphs-determine-window-positivity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6; WTZ README §4C.

## Target

For every aperture `A`, truncation `N` and real coefficients `c_n`, prove equivalence of

`∫H² + Σ_{2≤n≤N} c_n ∫H(u)H(u+log n) ≥ 0`

for all `C²` tests supported in `[-A,0]`, and positivity of every finite rational Hecke
graph of logarithmic spread `< A` with the same coefficients. The existing theorem
`exists_windowTest_eq_heckeForm` proves the implication from windows to graphs.

## Proof of the converse

For `S={log n:2≤n≤N}`, the existing abelian Følner lemma gives a nonempty
finite `F` of logarithms of positive rationals, with
`(1−η)|F|≤#{v∈F:v+log n∈F}≤|F|` for every active `n` and every `η>0`.
It uses a slow-growth step of the finite sets of nonnegative sums of elements of `S`;
no multiplicative independence is needed.

At each real `x`, restrict `F` to the nodes where `H(x+v)≠0`. Continuity and
support force strict spread `<A`. Exponentiation identifies this finite graph with
a graph of positive rationals. Graph positivity, integrated in `x`, gives

`|F|∫H² + Σ_n c_n #{v∈F:v+log n∈F} ∫H(u)H(u+log n) ≥ 0`.

Put `Q=∫H²+Σ_n c_n∫H(u)H(u+log n)` and
`B=Σ_n |c_n∫H(u)H(u+log n)|`. Each edge count differs from `|F|` by a number
between zero and `η|F|`. Thus the integrated graph form is at most
`|F|(Q+ηB)`, giving `Q+ηB≥0`. If `Q<0`, choose
`η=−Q/(2(B+1))`; then `Q+ηB<0`, a contradiction.
Each sum is finite; the integrands are continuous with compact support.
No spectral positivity input is assumed.

## Exact scope

This supplies the missing graph-to-window implication. Explicit later-stage horizon
values and a bounded positive balancing weight at a critical horizon remain separate
obligations. `MultiplicativePositivityGeometry.AbelianZeroMass` supplies
`exists_abFolner_step`, `card_abShift_mem_ge` and nonemptiness.

## Lean theorem

`WindowTowerOfSpecZ.windowForm_nonneg_iff_rationalHeckePositive` in
`RationalHeckeGraphsDetermineWindowPositivity.lean` proves the exact equivalence.
Direct source check passed; transitive axioms are only `propext`, `Classical.choice`
and `Quot.sound`. The owning umbrella imports the module.
