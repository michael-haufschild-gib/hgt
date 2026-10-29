# Global Hecke continuation from actual ordinary-class theta transforms

- **ID:** hecke-global-continuation-from-ordinary-classes
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Lean:** `HeckeLFunctions/HeckeLFunctionsHaveGlobalContinuation.lean`
- **Statement:** Every finite-order ray class Hecke L-series has a meromorphic continuation to the complex plane. It is entire for every nontrivial character. The trivial character has exactly a simple pole at one, with residue `heckeDensity`.

## Actual global construction

The [finite-class recombination](hecke-l-series-as-finite-class-theta-sums.md)
uses actual nonzero integral inverse-class representatives prime to the
modulus. Its normalized sum of actual unit-theta Mellin transforms agrees
with `GammaFactor * heckeL` on `Re s>1`. Multiplication by the entire
reciprocal Gamma product yields the raw L-continuation.

Write `n=[K:Q]`, `k=parityDegree`, `a(s)=(n*s+k)/2`, and
`kappa=n/2+k`. The exact zero-mode decomposition is

`rawL(s) = R(s) - A(s)/a(s) - B(s)/(kappa-a(s))`,

where `R`, `A`, and `B` are the actual finite normalized class sums,
multiplied by the reciprocal Gamma product. All three are entire.
This identity comes directly from the proved weak Mellin-pair formula;
no continuation or zero-mode input is assumed.

If `k` is nonzero, both theta zero modes vanish and `rawL=R` is entire.
If `k=0`, the Gamma product is zero at zero: at least one infinite place
exists, and every real and complex Gamma factor has its prescribed zero
value there. Hence `A(0)=0`. Define

`H(s) = R(s) - (2/n)*dslope A 0 s + (2/n)*dslope B 1 s`.

The existing analytic divided-difference theorem proves that `H` is
entire, including both filled points. Away from zero and one,

`rawL(s) = H(s) + r/(s-1)`, where `r=(2/n)*B(1)`.

For nonzero parity use `H=R` and `r=0`. In all cases the original Hecke
series agrees with this expression on `Re s>1`.

## Residue identification and absence of circularity

Along real `s` tending to one from above, the new expression gives
`(s-1)*L(s) -> r`. The previously proved ideal-counting continuation is
holomorphic at one for every nontrivial character, so the same limit is
zero. For the trivial character the previously proved residue theorem
gives `heckeDensity`. Uniqueness of limits therefore identifies `r`
exactly. This uses only the older continuation near one, not the new
global continuation.

Define the actual global `heckeLFunction(s)=H(s)+r/(s-1)`. It is
meromorphic everywhere and entire when the character is nontrivial.
For the trivial character, the local numerator
`heckeDensity+(s-1)*H(s)` is analytic and nonzero at one because
`heckeDensity_pos` is already proved. Thus the meromorphic order is exactly
`-1`; differentiability away from one excludes every other pole.
The complex residue limit is also proved directly.

The identity theorem on the connected common half-plane identifies this
global function with `heckeLCont`. In particular it inherits the already
proved nonquadratic nonvanishing on `Re s >= 1`.

## Main declarations

- `heckeThetaLContinuation_eq_regular_sub_poles`
- `differentiable_heckeEntireRegularPart`
- `heckeThetaPoleCoefficient_eq_zero`
- `heckeThetaPoleCoefficient_one`
- `heckeLFunction_eq_heckeL`
- `meromorphic_heckeLFunction`
- `differentiable_heckeLFunction`
- `differentiableAt_heckeLFunction`
- `tendsto_sub_one_mul_heckeLFunction`
- `meromorphicOrderAt_heckeLFunction_one`
- `heckeLFunction_eq_heckeLCont`
- `heckeLFunction_ne_zero_of_sq_ne_one`

## Verification and remaining scope

Seven main transitive axiom audits report only `propext`, `Classical.choice`,
and `Quot.sound`. Final direct source audit with `lake --old env lean`
passes without warnings. The module is wired into the Hecke umbrella;
no umbrella was compiled. Its olean is built for the written real-character
nonvanishing consumer.

Primitive Gauss/conductor normalization and the primitive completed
functional equation remain open. Real-character nonvanishing is being
formalized through the separate positive-occupation Landau argument.
Class field theory remains later in the programme.
