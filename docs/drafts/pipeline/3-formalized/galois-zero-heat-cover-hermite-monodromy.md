# The heat cover of the zeros and the Hermite monodromy of a collision

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** review-1211 §2.19 Q5 (monodromy of the zeros of the heat family around a
  collision, relation to conjugation); milestone M4.

`H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx` for complex `τ` (`complexHeat`); for real `τ` it is the
de Bruijn–Newman family. The heat cover is `{(τ, z) : H_τ(z) = 0} ⊂ ℂ²`. A collision of order
`m` is a point `(τ₀, z₀)` with `z₀` a zero of exact order `m` of `H_τ₀`; `a = H_τ₀^{(m)}(z₀)`.
`Q_m = e^{−D²}y^m` is the Hermite profile; it has `m` simple real roots, symmetric under
`ρ ↦ −ρ`, and `0` is a root iff `m` is odd.

## Theorems

1. `H` is analytic on `ℂ²`, `H_τ` is even, `conj H_τ(z) = H_τ̄(z̄)`, and no `H_τ` vanishes
   identically. Every point of the cover is a collision of some finite order `m ≥ 1`.
2. **Blow-up.** There is an analytic `G` on `ℂ²` with
   `H_{τ₀+s²}(z₀ + s y) = s^m G(s, y)` and `G(0, y) = (a/m!) Q_m(y)`.
3. **Sheets.** Through each root `ρ` of `Q_m` passes a unique analytic branch `y_ρ` of `G = 0`;
   `Z_ρ(s) = z₀ + s y_ρ(s)` is a zero of `H_{τ₀+s²}`, and different roots give different zeros
   for small `s ≠ 0`.
4. **Monodromy.** `Z_ρ(−s) = Z_{−ρ}(s)`.
5. **Involutions.** `conj Z^{(τ₀,z₀)}_ρ(s) = Z^{(τ̄₀,z̄₀)}_ρ(s̄)` and
   `−Z^{(τ₀,z₀)}_ρ(s) = Z^{(τ₀,−z₀)}_{−ρ}(s)`. At a collision at the centre `z₀ = 0` the order
   is even and `−Z_ρ(s) = Z_ρ(−s)`. At a real collision (`τ₀`, `z₀` real): `Z_ρ(s)` is real for
   real `s`; `conj Z_ρ(iσ) = Z_{−ρ}(iσ)`, and `Z_ρ(iσ)` is not real for `ρ ≠ 0`, small `σ ≠ 0`.
6. **Exhaustion.** There is `r > 0` such that `z₀` is the only zero of `H_τ₀` in the disc
   `|z − z₀| < r`, and for all small `s ≠ 0` the zeros of `H_{τ₀+s²}` in that disc are exactly
   the `m` points `Z_ρ(s)`, all simple. For `τ ≠ τ₀` near `τ₀` there are exactly `m` zeros in
   the disc, all simple.
7. **Branch points.** The set of multiple zeros `{(τ, z) : H_τ(z) = H_τ'(z) = 0}` is discrete
   in `ℂ²` and countable; the set of branch times is countable.

## Proof

*Analyticity.* The kernel `Φ(x)e^{τx²}e^{izx}` is entire in `(τ, z)` and dominated on bounded
sets by `Φ(x)e^{Rx²}e^{R|x|}`, which is integrable. The integral is continuous and holomorphic
on complex lines, hence analytic. `H_τ` is the Fourier transform of the nonzero integrable
function `Φe^{τx²}`, so it is not identically zero and its zeros have finite order.

*Blow-up.* Put `X = ix`, `W = Φ e^{τ₀x²}e^{iz₀x}`, `u = sX(y − sX)`. Then
`H_{τ₀+s²}(z₀+sy) = ∫ W e^u`. Write `e^u = Σ_{n<m} u^n/n! + u^m e_m(u)` with `e_m` entire,
`|e_m(u)| ≤ e^{|u|}`. Expanding `u^n` and using `∫ W X^k = H_τ₀^{(k)}(z₀) = 0` for `k < m`
leaves `s^m` times a polynomial in `(s, y)` plus `s^m ∫ W X^m (y − sX)^m e_m(u)`; the integral
is analytic by the same domination. At `s = 0` only the terms with total degree `m` survive
and give `(a/m!) Q_m(y)`.

*Sheets.* `∂_y G(0, ρ) = (a/m!) Q_m'(ρ) ≠ 0`. The analytic implicit function theorem gives
`y_ρ`, unique among continuous branches through `ρ`.

*Monodromy and involutions.* `G(−s, −y) = (−1)^m G(s, y)`, `conj G_{τ₀,z₀}(s, y) =
G_{τ̄₀,z̄₀}(s̄, ȳ)` and `G_{τ₀,−z₀}(s, y) = G_{τ₀,z₀}(s, −y)` hold for `s ≠ 0` by the
symmetries of `H` and extend by continuity. The first turns the branch through `ρ` into a
branch through `−ρ`, the second into a branch of the conjugate collision through `ρ`, the
third into a branch of the reflected collision through `−ρ`; uniqueness identifies each.

*Exhaustion.* `z₀` is an isolated zero of `H_τ₀`; on a small circle `|H_τ₀| ≥ ε`, and
`H_τ → H_τ₀` uniformly there, so the zero count with multiplicity in the disc is `m` for
nearby `τ`. The `m` sheets are distinct zeros in the disc, hence all of them, each simple.

*Branch points.* By exhaustion a multiple zero has a neighbourhood in `ℂ²` without another
multiple zero; a discrete subset of `ℂ²` is countable.

## Formalization

`GaloisTheoryOfZeros/TheHeatCoverOfTheZeros.lean`: `analyticAt_complexHeat`,
`complexHeat_ofReal`, `complexHeat_neg`, `complexHeat_conj`, `exists_complexHeat_ne_zero`,
`complexHeat_blowup`, `collisionBlowup_zero`, `collisionBlowup_neg`, `collisionBlowup_conj`,
`collisionBlowup_reflect`.

`GaloisTheoryOfZeros/TheHermiteMonodromyOfACollision.lean`: `IsCollision`,
`exists_isCollision`, `isCollision_ofReal_iff`, `IsCollision.even_of_center`,
`exists_collisionBranch`, `complexHeat_collisionZero`, `collisionZero_ne`, `collisionZero_neg`,
`collisionZero_conj`, `collisionZero_reflect`, `neg_collisionZero_center`,
`collisionZero_ofReal_im`, `conj_collisionZero_I_mul`, `collisionZero_I_mul_im_ne_zero`,
`collisionZero_center_I_mul_re`.

`GaloisTheoryOfZeros/TheSheetsOfACollisionAreAllItsZeros.lean`: `exists_ball_zeros_eq_sheets`,
`exists_ball_simple_zeros`, `discreteTopology_multipleZeros`, `countable_multipleZeros`,
`countable_branchTimes`.

Each module checked with `lake --old env lean`; umbrella import wired.
