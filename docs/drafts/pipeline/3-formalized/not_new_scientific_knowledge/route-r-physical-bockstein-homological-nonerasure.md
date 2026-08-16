# Route R physical Bockstein homological non-erasure

- **Stage:** 3-formalized
- **Status:** `[BRIDGE] [PAPER-PROVED]`
- **Route:** R

## Exact theorem

Let `H_p` be the signed cyclic/Hochschild quotient of the actual rational-adelic source, let
`e_p : H_p` be its retained ordinary-prime class, and let

\[
  r(e_p)=-\log p\ne0
\]

be the descended Kummer regulator.  For an actual Xi divisor copy `rho`, put

\[
  c_\rho=\Xi_C^{(m_\rho)}(w_\rho)\ne0,
  \qquad g_{p,\rho}=p^{2\Re\rho-1}>0,
\]

and define the source physical Bockstein class

\[
  \beta_{p,\rho}=(1-g_{p,\rho})c_\rho e_p\in H_p.
\]

Then:

1. `r(beta_{p,rho})` is exactly the signed-Kummer physical dilation defect;
2. `beta_{p,rho}=0` iff `g_{p,rho}=1` iff `Re rho=1/2`;
3. its literal chain representative belongs to the signed cyclic/Hochschild boundary submodule
   iff `Re rho=1/2`;
4. for every complex-linear target map `F : H_p -> V` retaining the prime atom
   (`F(e_p) != 0`), `F(beta_{p,rho})=0` iff `Re rho=1/2`.
5. the Kunneth self-product `beta_{p,rho} tensor beta_{p,rho}` is zero iff
   `Re rho=1/2`.

Thus no complex-linear homological enlargement can both retain the ordinary-prime class and
annihilate the physical Bockstein class at an off-line fibre.  Any surviving relative-index
producer must be nonlinear/non-Kunneth, or must add a relation that erases the coefficient-faithful
prime direction.

## Proof

The corpus proves `e_p != 0`, `c_rho != 0`, and `r(e_p)=-log p != 0`.  Linearity gives

\[
  r(\beta_{p,\rho})
   =(1-g_{p,\rho})c_\rho(-\log p),
\]

which is the previously formalized signed-Kummer physical defect.  Since the coefficient field is
`C`, scalar multiplication is torsion-free.  Hence `beta=0` iff
`(1-g)c=0`; nonvanishing of `c` reduces this to `g=1`.  The existing half-density character
rigidity gives `g=1` iff `Re rho=1/2`.

The quotient class of the literal representative is `beta`, so quotient membership is equivalent
to `beta=0`.  Finally, for a complex-linear `F`,

\[
  F(\beta)=(1-g)cF(e_p).
\]

If `F(e_p)` is nonzero, torsion-freeness again gives the same zero criterion.
For the self-product, apply `r tensor r` followed by the canonical multiplication
`C tensor_C C -> C`.  Its value is `r(beta)^2`, which is nonzero whenever `r(beta)` is nonzero.
The converse follows from `beta=0` on the critical fibre.

## Hostile audit

- No critical-line or RH premise occurs.
- The class is defined from the actual retained source atom, actual Xi leading jet, and literal
  physical half-density character.
- Non-erasure is a conclusion from the existing Kummer regulator, not an assumed injectivity field.
- This does not prove RH.  It proves that linear source homology cannot be the missing annihilator.
- It also excludes the ordinary Kunneth self-product as a source-exact quadratic relative index.
  A surviving index must introduce a genuinely additional relation, not tensor existing homology.
- This is a bridge/classification, not new scientific knowledge; it is forced by vector-space
  torsion-freeness once the corpus's coefficient-faithful source landing is assembled.

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/RouteRPhysicalBocksteinHomologicalNonErasure.lean`
(namespace `RHTower`), wired into the `GaloisForLFunctions.RHTower` umbrella.

| Paper statement | Lean declaration |
|---|---|
| the source physical Bockstein class `beta_{p,rho}` | `ccmRationalAdelicPrimeXiPhysicalBocksteinScalar`, `…HomologyClass`, `…Representative` |
| item 1, `r(beta)` is the signed-Kummer dilation defect | `ccmRationalAdelicSignedKummerRegulator_physicalBocksteinClass` |
| item 2, `beta = 0` iff `g = 1` iff `Re rho = 1/2` | `…HomologyClass_eq_zero_iff_gain_eq_one`, `…HomologyClass_eq_zero_iff_re_eq_half` |
| item 3, boundary-submodule membership | `…Representative_class`, `…Representative_mem_boundary_iff` |
| item 4, every complex-linear retaining target | `…Class_map_eq_zero_iff_gain_eq_one`, `…Class_map_eq_zero_iff_re_eq_half` |
| item 5, the Kunneth self-product | `…TensorSquare`, `ccmRationalAdelicSignedKummerTensorSquareRegulator_bockstein`, `…TensorSquare_eq_zero_iff_re_eq_half` |
| every Kunneth tensor power (strengthening) | `…TensorPower`, `…TensorPowerRegulator_bockstein`, `…TensorPower_ne_zero_of_offLine`, `…TensorPower_eq_zero_iff_re_eq_half` |

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
