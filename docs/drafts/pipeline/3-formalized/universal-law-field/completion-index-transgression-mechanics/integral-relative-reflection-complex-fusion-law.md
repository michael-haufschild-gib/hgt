# Integral relative-reflection complex fusion law

- **ID:** `ULF-IRRCF-1`
- **Stage:** 3-formalized
- **Type:** unconditional source/Gamma/reflection fusion law
- **Status:** dependency-closed paper proof; Lean-certified in
  `GaloisForLFunctions.RHTower.IntegralRelativeReflectionComplexFusion`

## Statement

In the integral Laurent source `R=Z[T,T^-1]`, put

`g=T-1`, `g*=T^-1-1`,

and define the odd relative-reflection differential

`C_T=[[0,g],[g*,0]]`.

Let `kappa=g g*`. Then:

1. `C_T^2=kappa I`;
2. `det C_T=-kappa`;
3. Laurent inversion exchanges the two arrows and fixes `kappa`;
4. physical Gamma evaluation `T -> exp(a)` sends `C_T` exactly to the curved suspension
   `R_a-R`;
5. evaluation sends `det C_T` to `2(cosh a-1)`, the paired Gamma curvature.

Thus integral Laurent formation, functional-equation reflection, and Gamma relative framing are
literal realizations of one two-periodic complex.

## Proof

Matrix multiplication gives

`C_T^2=[[g g*,0],[0,g* g]]=kappa I`

because `R` is commutative. The two-by-two determinant is `-g g*=-kappa`. Laurent inversion sends
`g` to `g*` and `g*` back to `g`, so it transposes `C_T` and fixes `kappa`.

Under `T -> exp(a)`, the two arrows become

`exp(a)-1`, `exp(-a)-1`.

These are exactly the forward and reflected Gamma-six suspension legs, so the evaluated matrix is
`R_a-R`. Finally,

`-kappa(a)=-(exp(a)-1)(exp(-a)-1)=2(cosh a-1)`.

## Exact conservation identity

The relation `C_T^2=kappa I` is the source Clifford law. Every scalar shadow in this branch is a
functorial readout of it:

- determinant reads `-kappa`;
- trace of the square reads `2 kappa`;
- Gamma evaluation reads negative curvature in `kappa` and positive curvature in `det C_T`;
- inversion exchanges odd arrows while preserving the even quadratic class.

## Fourth-organ prediction

On each canonical Xi jet associated-grade layer, a proper integral realization of `C_T` must give
the evaluated curved suspension integer coordinates. `ULF-DRRIF-1` proves that at prime two this
is possible in the open strip only at neutral grade. Therefore the fusion law predicts the exact
global properness theorem needed for RH: integral landing of this one complex on every Xi source
jet layer.

## Dependency audit

- Laurent inversion and the existing integral Cartier generator.
- Elementary two-by-two matrix multiplication and determinant.
- Existing exact Gamma evaluation of forward/inverse Laurent generators.
- Existing definition of the Gamma-six curved suspension and paired curvature.
- No RH, Xi zero, positivity, numerical computation, added axiom, or lattice-existence premise.
