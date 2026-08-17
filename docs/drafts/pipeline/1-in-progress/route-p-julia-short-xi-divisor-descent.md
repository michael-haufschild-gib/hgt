# Route P Julia-short completed Xi-divisor descent

- **ID:** `P-G207`
- **Stage:** `1-in-progress`
- **Type:** completed Gamma/polar transport / multiplicity-copy Schur descent
- **Status:** `[CONJECTURE] [OPEN CORE] [NOT RH]`
- **Parent:** `../3-formalized/new_scientific_knowledge/gamma/route-p-julia-ward-precompression-shorting.md`

## Exact target

Transport P-G206's literal rank-one Julia environment short through the already formalized
rectangular Gamma/polar completion. Target must retain:

1. the nonzero rectangular source coefficient at each detected right-Xi support;
2. every analytic-multiplicity copy, not a quadratic raw residue;
3. a literal Hermitian environment block whose Schur short is zero;
4. cutoff independence of the completed residue.

## Internal frontier

- `[CORPUS]` `routePPrimitiveGammaJuliaWard_precompressionShorting` realizes the source block
  `[[C_x^2,C_x],[C_x,1]]` and proves its short is zero.
- `[CORPUS]` `gammaSewnMobiusJuliaCriticalCompletedTail_divisorComplete` transports the singular
  Julia coefficient through canonical polar/Gamma completion to a meromorphic source tail.
- `[CORPUS]` `meromorphicTrailingCoeffAt_xiRectangularPrimeGammaTailContinuation` identifies its
  residue at `q` as `2 m(q) a_L(q)` with `a_L(q) != 0`.
- `[CORPUS]` `xiRightSupportFiberEquiv` identifies the support fibre with exactly `m(q)` copies.
- `[CORPUS]` `routePXiConormalMultiplicitySplit_*` proves equal copy splitting is the unique
  minimum-energy, coefficient-faithful cure for quadratic multiplicity.

## Heavy-conjecture loop

1. **Ordinary trace-class spectral transport. — `[FALSIFIED]`.**
   `not_routePPrimitiveGammaJuliaStokesTraceClassXiDivisorLanding` excludes every nonzero scalar
   multiplicity-exact reciprocal-Xi landing because the divisor is genus one, not trace class.
2. **Direct genus-one determinant/scalar weld. — `[FALSIFIED]`.**
   The source `det2` has a forced zero at `1`, while `XiC(1) != 0`; even an arbitrary pointwise
   scalar multiplier cannot repair it.
3. **Transport the rank-one Schur functor before spectral scalarization. — active.**
   Split the completed raw residue `2 m(q) a_L(q)` over the canonical `m(q)`-copy support fibre.
   Each copy receives `2 a_L(q)`. Apply the same Hermitian environment block
   `B(c)=[[|c|^2,c],[conj(c),1]]` used by P-G206. Then every copy has zero Schur short and the
   aggregate source corner is exactly `m(q)|2a_L(q)|^2`.

## Frozen conjecture candidate

`[CONJECTURE]` For every positive rectangular width, admissible completed tail, detected right-Xi
divisor copy `q`, and member of its canonical support fibre, the completed Gamma/polar residue
admits a cutoff-independent copy coordinate `c_q=2a_L(q)`. The P-G206 source block and every
completed copy block are instances of one Hermitian rank-one Schur functor; hence shorting commutes
with this coefficient transport, while direct-sum corner energy preserves analytic multiplicity
linearly.

`[OPEN CORE]` Complete hostile literature audit, then prove that every coordinate is derived from
the actual meromorphic residue (not fitted from the target coefficient), prove codiagonal residue
conservation and aggregate energy, and prove the source-block identification with P-G206 literally.

## Honest boundary

Even if proved, this transport alone cannot imply RH: the copywise short vanishes at every detected
off-line divisor. Its value is to close the requested completed-source compatibility and show that
the next RH producer must constrain the positive compressed corner, not ask whether the Schur short
survives divisor descent.
