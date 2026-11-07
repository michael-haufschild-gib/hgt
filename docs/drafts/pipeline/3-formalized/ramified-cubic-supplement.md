# The ramified cubic supplementary law

- **ID:** ramified-cubic-supplement
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For a primary prime `p=1+3A+3Bω`, `(ω/p)₃=ω^(2A−B)` and `(ω−1/p)₃=ω^A`.

Euler's residue exponent evaluates the symbol of `ω`. The exact norm
`N(p)=1+9(A²−AB+B²)+3(2A−B)` then gives its exponent modulo three.

Put `λ=ω−1`. If primary primes satisfy `p−q=λ²ur`, with unit `u` and
primary `r`, composite reciprocity gives `(r/p)₃=(r/q)₃`: modulo `r`, `p=q`.
The common value is nonzero, since otherwise `q` belongs to `(p)`.
Comparing the symbols of `p−q` and cancelling yields
`(λ/p)₃²(u/p)₃=(λ/q)₃²(u/q)₃`. Squaring is injective on cubic roots.

The comparison primes are `q=−2` and `q=1+3ω`, of norms four and seven.
Their `λ` symbols are `ω²` and `1`. For `A=3k+i`, `B=3l+j`, the following
factorizations `p−q=λ²u(1+3C+3Dω)` cover every case:

| `(i,j)` | `q` | `u` | `(C,D)` |
|---|---|---|---|
| `(0,0)` | `−2` | `−ω²` | `(k,l)` |
| `(0,1)` | `−2` | `ω` | `(l,−k+l)` |
| `(0,2)` | `1+3ω` | `−1` | `(−k+l,−k)` |
| `(1,0)` | `−2` | `ω²` | `(−k−1,−l)` |
| `(1,1)` | `1+3ω` | `−ω²` | `(k,l)` |
| `(1,2)` | `−2` | `−ω` | `(−l−1,k−l)` |
| `(2,0)` | `1+3ω` | `−ω` | `(−l,k−l+1)` |
| `(2,1)` | `−2` | `−1` | `(−k+l−1,−k−1)` |
| `(2,2)` | `−2` | `1` | `(k−l,k+1)` |

Substitute the unit symbols into the comparison identity. The result is
`(λ/p)₃=ω^i` in every row. Each row follows from a polynomial identity.

Module: `MetaplecticMobiusDescent/TheRamifiedCubicSupplement.lean`.
Audited endpoints: `cubicChar_omega`, `ramified_comparison`,
`cubicValue_omega_primary`, `cubicValue_lambda_primary`.
Direct Lean audit passed. All four transitive axiom lists contain only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.

Adapted from external OpenAI `Reciprocity/CubicJacobi.lean`; source and
license are recorded in `NOTICE`. Composite ray phases and the Kubota multiplier are formalized in
[ray phases](ramified-cubic-ray-phase.md) and
[the multiplier](cubic-jacobi-symbol-and-kubota-character.md).
