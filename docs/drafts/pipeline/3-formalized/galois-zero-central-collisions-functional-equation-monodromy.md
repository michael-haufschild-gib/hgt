# Central collisions: the functional equation is a monodromy of the heat cover

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** review-1211 §2.19 Q5 (existence of branch points; the reflection `r` as a
  monodromy); T3g (class of `r`).

`H_τ(z) = ∫ Φ(x) e^{τx²} e^{izx} dx`, `c(τ) = H_τ(0) = ∫ Φ(x) e^{τx²} dx` the centre value.

## Theorems

1. `c` is entire and `|c(τ)| ≤ exp(C (1 + |τ|)^{3/2})`.
2. For every `A` there is a real `σ ≥ 1` with `log c(σ) > Aσ`.
3. `c(t) > 0` for real `t`.
4. `{τ : c(τ) = 0}` is infinite, and none of its points is real.
5. At each zero `τ₀` of `c` an even number `m ≥ 2` of zeros of the family collide at the
   centre, and the turn of the time around `τ₀` carries the zero on each sheet to its
   negative: `−Z_ρ(s) = Z_ρ(−s)`.
6. The heat cover has infinitely many branch times.

## Proof

*Growth.* `Φ(x) ≤ A exp(−B e^{b|x|} + c x²)`. For `T, u ≥ 0`,
`T u² ≤ (B/2) e^{bu} + K (1+T)^{3/2}`: with `κ = (B/2) b⁶/720`, `κ u⁶ ≤ (B/2)e^{bu}`; put
`w = u²`, `λ = √(1+T)(1 + 1/κ)`. If `w ≤ λ` then `T w ≤ T λ`; otherwise `κ w² ≥ κ λ² ≥ T`, so
`T w ≤ κ w³`. Hence `|Φ(x) e^{τx²}| ≤ A e^{K(1+c+|τ|)^{3/2}} e^{−(B/2)e^{b|x|}}`, and the last
factor is below a Gaussian. Integrate.

*Ray.* `c(σ) ≥ ∫_R^{R+1} Φ e^{σx²} ≥ μ e^{σR²}` with `μ = min_{[R,R+1]} Φ > 0`. Take
`R² ≥ A + 1` and `σ ≥ 1 + |log μ|`.

*Zeros.* An entire function of order below two with finitely many zeros is `P(τ) e^{aτ+b}`,
which grows at most exponentially on the real axis. This contradicts the ray growth. A real
zero is excluded by positivity.

*Collision.* `H_τ₀` is even and not identically zero, so `0` is a zero of finite even order
`m ≥ 2`. The reflection law `−Z^{z₀}_ρ(s) = Z^{−z₀}_{−ρ}(s)` at `z₀ = 0` and the monodromy law
`Z_{−ρ}(s) = Z_ρ(−s)` give `−Z_ρ(s) = Z_ρ(−s)`.

## Formalization

`GaloisTheoryOfZeros/TheFunctionalEquationIsAMonodromyOfTheHeatCover.lean`:
`exists_norm_complexHeat_center_le`, `exists_lt_log_norm_complexHeat_center`,
`integral_riemannKernelReal_mul_exp_pos`, `im_ne_zero_of_complexHeat_center_eq_zero`,
`infinite_centerTimes`, `exists_isCollision_center`, `infinite_branchTimes`,
`infinite_setOf_center_monodromy`. The zero-set input is
`RHTower.zeroSet_infinite_of_subquadratic_superlinear_ray`.

Checked with `lake --old env lean`; umbrella import wired.
