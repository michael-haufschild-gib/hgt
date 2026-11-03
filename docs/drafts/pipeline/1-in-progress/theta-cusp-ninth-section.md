# Ninth theta section

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** For every `0<a<1/2`, the actual signed center-mixed theta Hankel matrix of size nine is positive definite.

The strict eighth section supplies the head. The remaining scalar is the
native successor integral `I₈(a)`, beginning with the sixteenth reflection
derivative. Parity reduces the new sign to the even five-dimensional block.
An unconditional integrated sign for that literal block remains open.

## Established source boundary

The [origin-and-tail repair](../3-formalized/theta-cusp-fifth-even-source-origin-tail-repair.md)
adds `10¹²G e₃e₃ᵀ+D G e₄e₄ᵀ`, with `D>0` selected from the actual
fifth Schur coordinate and `G=3Φ²+2xΦΦ′`. Its weighted flux derivatives
preserve every mixed entry. It is positive near zero and cofinally.

The [inherited-load boundary](../5-failed/theta-cusp-fifth-even-inherited-load-boundary.md)
refutes its global pointwise positivity. At `q=7`, the explicit even vector
`(-658560,47040,-420,1,-1/1568)` has native energy `E>0`, but the inherited
fourth correction makes it negative for every nonnegative fifth load,
including in the actual weighted representative at every critical aperture.
The origin-selected fifth Schur comparison is therefore nonpositive there.

Its exact native directional capacity is `B=E/(-G)`, with `0<B<10¹²`.
For independent loads, positivity in that direction at every critical
aperture is equivalent to `C+D/1568²≤B`. This classifies the witness
direction; it does not assert positivity of the whole matrix.

The [constant-load separation](../5-failed/theta-cusp-fifth-even-constant-load-separation.md)
excludes every real fourth load with nonnegative fifth load. The origin
requires `C≥C₀>660·10⁹`; scale seven allows `C+D/1568²≤B<330·10⁹`.
For each critical aperture, weighted positivity still forces the origin
condition, while its scale-seven capacity satisfies `B_a<450·10⁹`.
All these bounds are formalized.

The exact surviving boundary region is `C>C₀`,
`D≤1568²(B−C)`. It is nonempty and forces `D<0`; it asserts only the
origin fourth head and the specified scale-seven direction.

## Next conjecture

Signed constant loads also fail global positivity of the full fifth block.
First decide whether the surviving boundary region intersects full fifth
positivity at zero. Eliminate the native positive three-dimensional head,
leaving `[[α+C G₀, β],[β, γ+D G₀]]`, where `G₀=3Φ(0)²` and
`α=S₄(0)`. The infimum of `C+D/1568²` over strict origin positivity is
`(−α−γ/1568²+2|β|/1568)/G₀`. Its comparison with `B` is unproved;
it requires the actual theta moments through order sixteen.

The integrated rank-nine sign remains open. A source certificate must pay
the negative region while preserving the actual mixed entries.
