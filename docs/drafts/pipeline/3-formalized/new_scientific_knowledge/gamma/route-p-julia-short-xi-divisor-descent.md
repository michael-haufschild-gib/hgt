# Route P Julia-short completed Xi-divisor descent

- **ID:** `P-G207`
- **Stage:** `3-formalized`
- **Type:** completed Gamma/polar transport / multiplicity-copy Schur descent
- **Status:** `[FORMALIZED] [LEAN BUILT] [UNCONDITIONAL] [NOT RH]`
- **Parent:** `route-p-julia-ward-precompression-shorting.md`

## Exact target

Transport P-G206's literal rank-one Julia environment short through the already formalized
primitive-depth/CCM Gamma/polar completion. Target must retain:

1. P-G206's exact Julia exterior coefficient on the actual pre-divisor quadratic source current;
2. every analytic-multiplicity copy, not a quadratic raw residue;
3. a literal Hermitian environment block whose Schur short is zero;
4. both source legs and the environment pivot throughout iterated Xi residues.

## Internal frontier

- `[CORPUS]` `routePPrimitiveGammaJuliaWard_precompressionShorting` realizes the source block
  `[[C_x^2,C_x],[C_x,1]]` and proves its short is zero.
- `[CORPUS]` `frankensteinKreinCCMRoutePQuadraticSourceCurrent` is the actual two-variable
  primitive-depth/CCM completed Gamma/polar current, formed before either Xi residue.
- `[CORPUS]` its forward and reflected residue theorems retain the exact radial coefficient and
  full analytic multiplicity on each source leg.
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
4. **Polarize before residues and retain the environment pivot. — `[PROVED]`.**
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

`[PROVED]` For every P-G206 Julia aperture pair, every retained Xi divisor support, every radial
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

## Dependency-closed proof

Write `kappa_x` for P-G206's literal normalized two-prime exterior coupling and
`B(a,b)=[[ab,a],[b,1]]`.

1. Direct multiplication gives `det B(a,b)=0` and
   `ab-a*1^(-1)*b=0`. For `b=c` and `a=conj(c)`, `B(a,b)=[c,1]^*[c,1]`, so it is Hermitian PSD.
2. P-G206 proves `kappa_x^2=W_x`. Therefore its real precompression block, after coefficient
   extension to `C`, is literally `B(kappa_x,kappa_x)`, not merely isomorphic to it.
3. Let `R(z,r)` and `F(w,r)` be the reflected and forward completed primitive-depth/CCM source
   columns. Their product is the existing pre-divisor quadratic source current. The upper-left
   entry of the gauged block is exactly

       (z-p_rho)(w-p_tau) kappa_x^2 R(z,r)F(w,r).

   Hence the matrix is formed before divisor evaluation and cannot be target fitting.
4. Existing unconditional completed Gamma/polar residue laws give

       (z-p_rho)R(z,r) -> m_rho R_rho(r),
       (w-p_tau)F(w,r) -> m_tau F_tau(r).

   Multiplication and pointwise matrix topology give first the right-leg limit, then the left-leg
   limit, landing in `B(kappa_x m_rho R_rho, kappa_x m_tau F_tau)`. Every matrix entry therefore
   retains its exact coefficient and the full analytic multiplicity product.
5. Apply the already proved canonical equal split separately to each gauged leg before taking its
   limit. Since `m_rho>0`, every copy coordinate converges to `kappa_x R_rho` or
   `kappa_x F_rho`. The same matrix-limit argument lands each pair of copies in
   `B(kappa_x R_rho,kappa_x F_rho)`.
6. On one support, the completed reflection law gives `R_rho=conj(F_rho)`, while `kappa_x` is real.
   The raw and copywise landings are therefore Hermitian PSD rank-one blocks with literal pivot
   `1` and zero short.
7. Codiagonal conservation follows from equal splitting:
   `sum_j kappa_x F_rho = m_rho kappa_x F_rho`. Squared corner energy is exactly
   `m_rho |kappa_x F_rho|^2`, so analytic multiplicity is linear after copy resolution.

All steps are algebraic, topological, or invoke existing unconditional residue/multiplicity laws.
No RH premise, simple-zero premise, numerical computation, or trace-class assumption occurs.

## Lean status

Formalized in
`formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaCompletedXiDivisorShorting.lean`.
Direct `lake env lean` and exact leaf build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean`; umbrella build was not
run.

## Hostile verdict

`[PROVED, NOT RH]` Exact transport exists. It does **not** kill an off-line divisor: the same
rank-one block and zero short land at every retained Xi support, and its compressed corner can be
strictly positive. Thus “does shorting survive Gamma/polar descent?” is closed. Remaining hard
producer is an independent completed-source budget/order law that compares this positive corner
with a quantity not erased by the environment pivot. Repeating Schur transport alone is retired.

## Honest boundary

This transport alone cannot imply RH: the copywise short vanishes at every detected
off-line divisor. Its value is to close the requested completed-source compatibility and show that
the next RH producer must constrain the positive compressed corner, not ask whether the Schur short
survives divisor descent.
