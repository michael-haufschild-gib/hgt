# Countable Gauss words and exact Mayer power traces

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [three approaches, A](../1-in-progress/argon-three-orthogonal-rh-approaches.md).
- **Input:** [actual source determinant](gauss-mayer-source-fredholm-determinant.md).

## Theorem

For a positive-integer Gauss word `a` of length `k≥1`, let
`M_a=[[A,B],[C,D]]` be the ordered product of its actual branch matrices
`[[0,1],[1,n]]`. Its unique fixed point is real, `0<p_a<1`. The multiplier
`λ_a=Cp_a+D` satisfies

`λ_a>1`, `det M_a=(-1)^k`, `λ_a²−(A+D)λ_a+(-1)^k=0`.

For `Re w>1`, the actual Hilbert realization `T(w)=QJ` of the Banach
Mayer operator `L(w)=JQ` obeys

`Tr(T(w)^k)=Σ_a λ_a^(−w)/(1−(-1)^k λ_a^(−2))`,

`Tr(T(w)^k)−(-1)^k Tr(T(w+2)^k)=Σ_a λ_a^(−w)`.

Both word sums converge absolutely. All branch maps, weights, fixed points,
matrices and operators are constructed from the actual Gauss branches.

## Proof

1. Every branch maps the closed outer disc `|z−1|≤3/2` into
   `|z−1|≤1`. Each nonempty composed word therefore has a unique attracting
   fixed point in the coefficient disc of radius `R=32/25`. The existing
   weighted-composition trace theorem evaluates its Cauchy diagonal as
   `W_a(w,p_a)/(1−Φ_a′(p_a))`.
2. Put `B(w,n)=2^(Re w) exp(π|Im w|) n^(−Re w)`. The composed weight
   is bounded by `∏_j B(w,a_j)` on the outer disc. Since the final image
   lies in the unit inner disc, this bounds the image of every Cauchy
   monomial independently of its degree. The `i`th diagonal is bounded
   by `R^(−i)∏_j B(w,a_j)`. The digit product is summable at fixed length
   for `Re w>1`, and the diagonal factor is geometric. Thus the double
   series is absolutely summable before exchanging its indices.
3. The countable head/tail decomposition and absolute operator convergence
   expand the genuine `L(w)^k` into exactly those word operators. The
   source factorization gives `T(w)^k=Q L(w)^(k−1)J`. Its Cauchy rescalings
   cancel in every diagonal entry, identifying the resulting sum with
   the actual Hilbert power trace.
4. Integral matrix multiplication recovers each fractional-linear word
   and its determinant sign. The denominator row satisfies `0≤C≤D`,
   `D≥1`, and `C>0` for nonempty words. Uniqueness under conjugation
   forces the fixed point to be real; real inverse branches put it in
   `(0,1)`. The fixed-point equation yields the stated quadratic for
   `λ=Cp+D>1`.
5. Positive real denominator factors telescope. Multiplicativity of
   principal powers on positive real numbers gives `W_a(w,p_a)=λ_a^(−w)`.
   The chain rule gives `Φ_a′=(-1)^k W_a(2,·)`. Since
   `W_a(w+2,·)=W_a(w,·)W_a(2,·)`, the difference of the two word traces
   cancels their common denominator. Absolute summability permits
   summation, giving the exact shift identity.

## Lean certificate

Module: `RenormalizedIntersectionTheory/GaussMayerCountableWordTraces.lean`.
Namespace: `GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords`.

- `hasSum_wordOperator`, `summable_norm_wordDiagonal`.
- `opTrace_power_eq_wordTrace`, `opTrace_power_shift`.
- `wordMatrix_unimodular`, `wordMap_eq_fraction`.
- `fixedPoint_real_interval`, `one_lt_wordMultiplier`, `wordMultiplier_quadratic`.
- `fixedPoint_weight_eq`, `fixedPoint_deriv_eq`, `summable_fixedPoint_weight`.
- `opTrace_power_eq_multipliers`, `opTrace_power_shift_multipliers`.

Direct production check passed. Eleven transitive axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import wired.

## Scope and modular normalization

The new source bridge is the countable word expansion, absolute trace
interchange, and identification of every actual power trace with its integral
word multipliers. The single-map trace and disc fixed-point theorems are
existing inputs. No literature-priority claim is made.

A single branch has determinant `−1`; the direct `PSL₂(ℤ)` comparison
uses even words. Dropping parity changes both displayed identities.
The word sums here are proved on `Re w>1`. [Source-parameter holomorphy](gauss-mayer-source-parameter-holomorphy.md)
of the actual determinant is now certified on `Re w>0`, away from one.
Primitive geodesic coding, the Selberg/scattering comparison, and resonance
exclusion remain open. No RH conclusion follows.
