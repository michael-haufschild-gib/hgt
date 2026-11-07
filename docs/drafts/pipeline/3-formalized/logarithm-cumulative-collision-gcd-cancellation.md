# Cumulative collision bounds and the exact diagonal regime

- **ID:** SPL-cumulative-collision-gcd-cancellation
- **Stage:** 3-formalized
- **Type:** THEOREM

For actual balanced smooth rows `A` and prime columns `P`, all in `(X,2X]`,
let `E(δ)` count ordered product pairs with logarithmic distance at most `δ`.
The proposed uniform envelope is

`E(1/T)≤#A #P+2 floor(4X²/T) #A²`,

with exact equality `E(1/T)=#A #P` when `T>4X²`.
The exact gcd-class bound also admits the floor cutoff.

## Paper argument

Fix rows `m,m'` and let `g=gcd(m,m')`. The corpus fixed-difference bound
is `g` when `g∣h` and zero otherwise. Exactly `floor(H/g)` positive
multiples of `g` lie at most `H`. Thus the full column-pair census over
all differences `1≤h≤H` is at most `g floor(H/g)≤H`.
Restriction to actual prime columns preserves this inequality. Summing over
smooth row pairs gives `Σ_(1≤h≤H) C(h)≤H #A²`.

If products `a<b≤4X²` have `log b−log a≤δ`, the inequality
`1−a/b≤log(b/a)` gives `b−a≤4X²δ`. Its integer difference therefore lies
in `[1,floor(4X²δ)]`. Covering by the actual difference fibres and applying
the cumulative bound gives `E₊(δ)≤floor(4X²δ)#A²`.
Smooth/rough coprimality gives a unique factorization into row and column,
so `E(δ)=#A #P+2E₊(δ)`. For `T>4X²`, the floor is zero.
Replacing the cumulative estimate by the existing fixed-difference gcd-class
estimate retains the sharper arithmetic partition with the same floor cutoff.

## Inputs and scope

Inputs: `Goldbach.card_balancedProductCollisionFiber_le_gcd_gate`,
`Nat.Ioc_filter_dvd_card_eq_div`, and this programme's exact smooth/prime
diagonal. The production module passes its direct Lean check and is wired into the umbrella.

This gives a uniform incidence envelope and exact diagonal regime.
It does not supply the prime-density factors required for random energy.
The corpus's stronger affine prime-pair sieve uses a Selberg quadratic
majorant. It is available for broader RH research, outside this programme's
restricted method.

## Lean declarations

Module `SumProductArithmeticOfTheLogarithm/CumulativeSmoothPrimeEnergy.lean`:
- `cumulative_balanced_collision_fiber_le`
- `cumulative_smooth_prime_collision_le`
- `smoothPrimeUpperLogFiber_le_floor`
- `smoothPrimeUpperLogCount_le_floor_sum`
- `smoothPrimeLogEnergy_le_floor_gcd_classes`
- `smoothPrimeLogEnergy_le_floor_envelope`
- `smoothPrimeLogEnergy_le_floor_at_height`
- `smoothPrimeLogEnergy_eq_diagonal_of_height`

All eight capstones pass transitive axiom audits with only `propext`,
`Classical.choice`, and `Quot.sound`.
