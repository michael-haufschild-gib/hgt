# Route P Julia--Ward precompression shorting

- **ID:** `P-G206`
- **Stage:** `1-in-progress`
- **Type:** nonlocal source coupling / compression-order theorem
- **Status:** `[CONJECTURE] [NOVELTY-UNVERIFIED]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaWardPrecompressionShorting.lean`

## Hard target

Construct coupling before finite prime-cell compression which is forced by literal Julia source
transport and reciprocal-promotion co-source, then prove shorting is not compression-monotone on
depth-zero primes two and three.

## Heavy-conjecture loop

1. **Copy Ward current into auxiliary channel. -- REJECTED.** Any quadratic energy can be killed by
   adjoining its own square root. This is tautological and supplies no independent source law.
2. **Use covariant Pluecker inverse incidence alone. -- FAIL.** It restores global covariance, but
   existing theorem contains no Gamma--Julia coefficient identifying its current with literal
   two-prime Ward cross term.
3. **Use normalized environment coordinate of canonical Gamma-sewn Julia lift. -- SURVIVES PAPER
   AUDIT.** Existing source theorem produces prime-log coordinate before scalar recombination and
   converges coefficientwise to literal `log p`. Weight it by exact reciprocal-promotion
   amplitudes before selecting prime cells.

## Frozen construction

For literal normalized two-prime co-source weights `w_i(u)` and Julia environment clock

```text
E_x(i) = c_J gammaSewnMobiusJuliaNormalizedPrimeLog(x,p_i),
```

define finite-aperture Ward energy and nonlocal cross coupling

```text
W_x(u) = 2 w_0(u) w_1(u) (E_x(0)-E_x(1))^2,
C_x(u) = sqrt(2) a_0(u)a_1(u)/M(u) (E_x(0)-E_x(1)),
```

where `a_i` are literal reciprocal-promotion amplitudes and `M=a_0^2+a_1^2`. Thus no fitted
scalar, determinant correction, or prime-local ghost is introduced.

Put the resolved source and Julia environment in positive block

```text
B_x(u) = [[W_x(u), C_x(u)], [C_x(u), 1]].
```

Target identities:

```text
C_x(u)^2 = W_x(u),
B_x(u) >= 0,
Schur_1(B_x(u)) = W_x(u)-C_x(u)^2 = 0.
```

As `x -> 0+`, `E_x(i) -> c_J log p_i`, so `W_x(u)` tends literal two-prime source-state Ward
energy and `C_x(u)` tends its coefficient-faithful cross square root. At boundary:

```text
short before compression = 0 < literal compressed Ward energy.
```

This is exact failure of compression monotonicity required to evade P-G205.

## Hostile boundary

The construction closes order/coupling geometry only. It does not identify shorted source block
with completed Xi divisor, preserve Xi multiplicity automatically, or prove RH. Next producer must
transport this exact Julia environment short through completed Gamma/polar source regulator; an
abstract auxiliary copy is invalid.

## Literature audit

Anderson--Trapp shorting gives the positive block formula `A-BD^{-1}B*`; Julia operator theory
supplies unitary defect channels. No checked source identifies this arithmetic reciprocal-promotion
cross with a completed zeta/Xi divisor law. Classification is classical; arithmetic coefficient
identity is corpus-derived. Novelty remains unverified until formal theorem survives.
