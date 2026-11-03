# Ninth theta section

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** For every `0<a<1/2`, the actual signed center-mixed theta Hankel matrix of size nine is positive definite.

The strict eighth section supplies the head. The remaining scalar is the native successor integral `I₈(a)`, beginning with the sixteenth reflection derivative. Parity reduces the new sign to the even five-dimensional block.

Investigate matrix-valued zero-boundary flux corrections extending the corrected even four-dimensional source. The correction must preserve every mixed entry after integration. Positivity of an abstract corrected matrix, an assumed successor sign, or a tail estimate alone does not discharge the target.

**Open:** An unconditional integrated sign for the literal even five-dimensional block. No rank-nine proof is claimed.

## Formalized source correction

The fixed correction `10¹²G e₃e₃ᵀ+D G e₄e₄ᵀ`, where
`G=3Φ²+2xΦΦ′` and `D` is selected from the actual fifth Schur coordinate at
zero, repairs a neighborhood of zero and a cofinal ray. Its weighted flux
derivatives preserve every mixed entry. A fifth-diagonal correction alone
cannot repair the negative fourth principal determinant at zero.

[Proof and Lean declarations](../3-formalized/theta-cusp-fifth-even-source-origin-tail-repair.md)
pass the canonical check and standard-only axiom audit. A sufficient
remaining source comparison is `S(x)+D G(x)>0` on the compact gap, where
`S` is the Schur coordinate of the native fifth border over the fixed
corrected fourth head. No integrated rank-nine sign follows yet.

## Inherited-load obstruction to test

At `q=πe^(2x)=7`, consider the even coefficient vector
`v=(-658560,47040,-420,1,-1/1568)`. Its native energy is determined exactly
by the existing atom-pair radial recurrence through order sixteen; the
all-order two-atom Cauchy estimate controls the omitted source.
Conjecture: `vᵀ H₅(x) v + 10¹²G(x) < 0`. Since `G(x)<0` at this center,
that inequality would rule out every nonnegative fifth-diagonal coefficient
while retaining the fixed fourth correction. No such inequality is yet
proved. The earlier odd-rank obstruction motivates this test but does not
prove it for the even fifth block.

The corresponding positive survivor is the exact directional load region
`C+D/1568² < B`, where `B=(vᵀH₅v)/(-G)` at this center. The proposed
complete-source bounds give `0<B<10¹²`; their finite radial certificates
and all-order Cauchy error estimate still require kernel verification.
