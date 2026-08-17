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
3. **Split a scalar residue and wrap each copy in a rank-one block. — `[FALSIFIED]`.**
   Although this preserves the target coefficient and linear multiplicity, it is target fitting:
   no pre-divisor object has the wrapped matrix as its residue. In particular it never transports
   P-G206's pairwise Julia exterior coupling.
4. **Polarize before residues and retain the environment pivot. — active.**
   Put `B(a,b)=[[ab,a],[b,1]]`. P-G206 is the real diagonal specialization `a=b=C_x` because
   `C_x^2=W_x`. Tensor the literal Julia coupling `C_x` into the two actual completed
   Gamma/polar source columns `R(z,r)` and `F(w,r)`. Before either divisor limit, gauge the two
   pole legs separately:

       a_rho(z)=C_x (z-p_rho) R(z,r),
       b_tau(w)=C_x (w-p_tau) F(w,r).

   The matrix `B(a_rho(z),b_tau(w))` is rank one and has pivot `1` and Schur short `0` for every
   punctured source pair. Its upper-left entry is literally the two-sided pole gauge of the
   pre-divisor quadratic source current, multiplied by P-G206's exact Julia coefficient squared.
   Existing residue theorems give

       a_rho -> C_x m_rho R_rho,   b_tau -> C_x m_tau F_tau.

   Thus the iterated matrix residue retains the exact coefficient and the full multiplicity
   product. Dividing each leg by its own analytic multiplicity before the limit gives the canonical
   copy block `B(C_x R_rho,C_x F_rho)` on every member of the actual multiplicity fibre; its
   codiagonal recovers each raw residue leg and its corner energy is linear in multiplicity.

## Frozen conjecture candidate

`[CONJECTURE]` For every P-G206 Julia aperture pair, every retained Xi divisor support, every radial
coordinate, and every member of its analytic-multiplicity fibre, the two-sided residue-gauged
completed Gamma/polar quadratic source block converges entrywise to the coefficient-faithful Xi
environment block. The raw landing retains the analytic multiplicity product; canonical
leg-by-leg splitting retains one exact coefficient on each divisor copy. Both source and divisor
blocks are literal specializations of `B(a,b)`, so the environment pivot remains `1` and Schur
shorting commutes with descent.

`[NOVELTY UNVERIFIED]` Anderson--Trapp shorting is classical; completed zeta spectral realizations
and reflection pairings are classical. Bounded literature audit found no construction combining a
Gamma-sewn Julia prime coupling, a two-variable completed Xi source current, two-sided residue
gauges that leave the pivot unscaled, and canonical multiplicity-copy splitting. This is not proof
of novelty.

`[OPEN CORE]` Prove the matrix-valued one-leg and iterated residue limits, the literal P-G206
source-block specialization, the same-support Hermitian/PSD landing, and codiagonal plus aggregate
energy conservation. Hostile check must then determine whether this is only a kinematic transport
or supplies an RH-bearing inequality.

## Honest boundary

Even if proved, this transport alone cannot imply RH: the copywise short vanishes at every detected
off-line divisor. Its value is to close the requested completed-source compatibility and show that
the next RH producer must constrain the positive compressed corner, not ask whether the Schur short
survives divisor descent.
