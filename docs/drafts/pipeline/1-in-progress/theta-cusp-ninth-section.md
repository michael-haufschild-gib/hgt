# Ninth theta section

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** For every `0<a<1/2`, the actual signed center-mixed theta Hankel matrix of size nine is positive definite.

The strict eighth section supplies the head. The remaining scalar is the native successor integral `I₈(a)`, beginning with the sixteenth reflection derivative. Parity reduces the new sign to the even five-dimensional block.

Investigate matrix-valued zero-boundary flux corrections extending the corrected even four-dimensional source. The correction must preserve every mixed entry after integration. Positivity of an abstract corrected matrix, an assumed successor sign, or a tail estimate alone does not discharge the target.

**Open:** An unconditional integrated sign for the literal even five-dimensional block. No rank-nine proof is claimed.

## Exact source correction under formalization

Write `m_k(x)=(-1)^k D_t^(2k)[Φ(x+t)Φ(x−t)]|_(t=0)` and
`G(x)=3Φ(x)²+2xΦ(x)Φ′(x)`. The native four-dimensional even determinant at
zero is negative. A fifth-diagonal correction leaves that principal block
unchanged and therefore cannot make the fifth block positive semidefinite.

Retain `A(x)=[m_(i+j)(x)]_(i,j<4)+10¹²G(x)e₃e₃ᵀ`, already strictly positive
for `x≥0`. Let `b=(m₄,m₅,m₆,m₇)`, `S=m₈−bᵀA⁻¹b`, and
`D=(|S(0)|+Φ(0)²)/Φ(0)²>0`. Adding `10¹²G e₃e₃ᵀ+D G e₄e₄ᵀ` to the fifth
native block gives Schur value `S(0)+3|S(0)|+3Φ(0)²>0` at zero.
Continuity gives a nontrivial positive interval. Both corrections vanish
under Gaussian balancing at infinity (orders six and eight), so the
corrected block is also strictly positive on a cofinal ray.

Replace each weighted `G(r/2)` correction by the derivative of the existing
zero-boundary center flux. The extra diagonal is nonnegative for positive
aperture. Every matrix entry remains integrable and retains its exact mixed
moment after integration. This constructs a single aperture-independent
repair near zero and at infinity; it does not prove positivity in between.

Lean source: `ThetaCuspSections/FifthEvenSourceRepair.lean`; checks pending.
The rank-nine statement remains unproved. A sufficient source obligation for this correction is
`S(x)+D G(x)>0` on the intervening compact interval.
