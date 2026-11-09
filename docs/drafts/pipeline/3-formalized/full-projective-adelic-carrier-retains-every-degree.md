# A projective adelic carrier retaining every original degree

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133, global carrier geometry.
- **Statement:** A discrete subgroup of `SL₂(ℂ)×Π'_p PGL₂(ℚ_p)` retains all
  original positive-integer degree points in its vertex quotient.

## Construction

Let `K_p` be the image of `GL₂(ℤ_p)` in `PGL₂(ℚ_p)`, and let `V` be the
finite-support restricted product of `PGL₂(ℚ_p)/K_p`. The rational diagonal
embedding of `SL₂(ℚ)` into `SL₂(ℂ)×Π'_p PGL₂(ℚ_p)` is faithful and discrete.
Set `J=(1,(w)_p)` for `w=[[0,-1],[1,0]]` and `Γ=J⁻¹SL₂(ℚ)J`.
The quotient uses the ordinary adelic action of this actual subgroup on `ℍ³×V`.
The original configuration

`n ↦ [x_n]`, where `x_n=(z_n,(diag(n,1)K_p)_p)`,

is injective for all positive integers `n`. Both local parity classes occur;
the square-degree restriction of the
[determinant-one construction](finite-weyl-conjugation-retains-the-global-degree-configuration.md)
is removed.

## Arithmetic mechanism

A local projectively integral matrix satisfies `‖Mᵢⱼ‖²≤‖det M‖`:
factor off its scalar and use integrality of the remaining matrix and inverse.
Thus a rational matrix projectively integral at every prime has integer
quotients `Mᵢⱼ²/det M`. For an orbit between opposite degree points, with
bottom row `(c,d)`, this gives integers `C=c²/(mn)` and `D=d²m/n`.
The hyperbolic height equation gives

`(m/n)² = C m⁴ + D ∈ ℤ`.

The inverse orbit makes the reciprocal square an integer, forcing `m=n`.
Finite Weyl reversal transfers this result to the original degree points.
For discreteness, projective integrality of a determinant-one rational matrix
forces all entries to be integers; an archimedean unit neighbourhood isolates
the identity. The integral projective stabilizers are proved open.

## Verification and remaining scope

[TheFullAdelicDegreeConfiguration.lean](../../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/TheFullAdelicDegreeConfiguration.lean)
formalizes the construction in namespace
`GaloisForLFunctions.HyperbolicArakelovTheory.FullAdelic`.
Capstones include `quadratic_entry_bound`, `orbit_square_ratio_integer`,
`conjugateArithmeticGroup_discrete`, and `originalDegreeClass_injective`.
Direct source audit passed; all eleven capstone audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import added.

This proves vertex-level orbit injectivity. Local finiteness of the degree
image, tree adjacency on the quotient, the global Green operator and
off-diagonal identity, and Weil's Robin diagonal remain unproved here.
One contribution: the full projective carrier and all-degree rigidity.
