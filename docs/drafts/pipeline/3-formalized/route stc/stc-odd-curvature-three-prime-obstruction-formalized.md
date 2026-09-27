# Three-prime obstruction to direct all-pair Stokes-curvature gluing — Lean certificate

- **Paper card:** `stc-odd-curvature-three-prime-obstruction.md`
- **Lean module:** `GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesFourChannelObstruction`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build` of the module; `lake --old env lean` clean (no warnings);
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`c_pq(g) = routeRCrossPrimeStokesOddCurvature p q g`.

| Card item | Lean theorem |
|-|-|
| (3) neutral-grade slope `c_pq(g)/g → -(x+y)(y/x+x/y)` | `tendsto_stokesOddCurvature_div_grade` |
| (2) `lim Ω(g)/g` exists and is `< -(log 3)/2` | `exists_tendsto_stokes_triangle_357_slope` |
| `Ω(g) ≠ 0` near `g = 0` | `stokes_triangle_ne_zero_near_zero` |
| sign of `Ω(g)` opposite to `g` | `stokes_triangle_357_sign_opposite` |
| no prime potential on `(3,5,7)` | `no_direct_stokes_three_prime_potential` |
| gauge invariance of the triangle charge | `triangle_charge_gauge_invariant` |
| (4) compensation law `B_35+B_57-B_37 = -Ω` | `stokes_triangle_357_compensation` |
| the correction is not itself a potential difference | `stokes_triangle_357_correction_not_potential` |
