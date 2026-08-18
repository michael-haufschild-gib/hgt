# Source-horizontal BV complete-split primitive-budget firewall

- **ID:** `source-horizontal-bv-complete-split-primitive-budget-firewall`
- **Stage:** 5 — failed / scoped route retired
- **Status:** `[SCOPED NO-GO PROVED] [LEAN FORMALIZED] [POSITIVE SURVIVORS EXTRACTED] [NOT RH]`
- **Route:** Frankenstein P / BV Green--Stokes / selected Krein residue / completed Euler budget

## Scoped question

Can proved BV Green--Stokes conservation, its canonical Krein sign, or Route O's exact matched
Gamma/Suzuki current provide an unconditional primitive-budget law controlling the positive
Xi-selected Wold--Julia corner? Generic Loewner descent is already RH-equivalent.

## Conjecture loop

### C1 — complete BV split is contractive after selected positivity

Let

```text
epsilon_N = endpoint third jet,
iota_N    = interior third jet.
```

Finite BV Green--Stokes conservation predicts the exact complementary identity

```text
iota_N + epsilon_N = 1.
```

Both terms should be positive: `iota_N` is the normalized positive Wold cubic moment, while
`epsilon_N` is eventually positive and tends to `2/3`. The four-orientation coefficient lift then
has complete positive energy

```text
8 ||c||^2 iota_N + 8 ||c||^2 epsilon_N = 8 ||c||^2.
```

Attack: compare this complete source-preserving energy with the literal primitive Euler budget.

### C1 verdict — falsified

Write `H_N=log p_N` and

```text
M_N = sum_(n<=N) woldCoeff(1,p_n) (log p_n)^2.
```

The literal interior third jet is `iota_N=M_N/H_N^3`. The already-proved residual identity gives
`epsilon_N=-(M_N-H_N^3)/H_N^3`; hence

```text
iota_N + epsilon_N = 1                                             (1)
```

at every finite clock. `iota_N>0` because every summand is positive and the range contains the
first prime. Therefore the complete coefficient-energy split is

```text
8||c||^2 iota_N + 8||c||^2 epsilon_N = 8||c||^2.                   (2)
```

The primitive source budget satisfies

```text
B_P(c) < (16/3)||c||^2 < 8||c||^2                                 (3)
```

for `c != 0`. Thus complete positive descent is noncontractive at every finite clock, not merely
cofinally. Positivity of the endpoint corner can be obtained only by making the interior BV
channel negative, null, or invisible. Such an operation is not a positive source-conservation
descent.

### C2 — signed interior compensation

After C1, test the only surviving possibility: retain endpoint positivity while the interior
channel remains Krein-negative, and derive an independent arithmetic bound on its signed trace.
This must be a literal source identity; defining it as budget minus endpoint is forbidden.

### C2 verdict — falsified

The coefficient arithmetic is sharper than the old `<2` quantum estimate. Isolate prime terms
`2,3,5`; monotonicity of `1/(x log^2 x)` bounds every later ordered-prime term by the integer tail
from `7`, whose integral is `1/log 6`. Certified logarithm bounds give

```text
sum_p 1/(p log(p)^2) < 2,
primitive base budget B_P < 1.                                  (4)
```

The canonical Krein trace is

```text
K_N(c) = 8||c||^2 (epsilon_N-iota_N)
       = 8||c||^2 (2 epsilon_N-1) -> (8/3)||c||^2.              (5)
```

But literal normalized source budget is `(8/3)||c||^2 B_P`, strictly below the limit in (5) for
`c != 0`. Thus canonical signed compensation overspends cofinally. This fails because of exact
source coefficients, not because abstract Krein/J-inner theory is missing.

### C3 — Route-O/Gamma compensation

If C2 has no coefficient-faithful source law, test whether the actual-head quantile Gamma current
can supply the negative channel after the Route-P cubic filter. Raw quantile transport and raw Wold
moments have incompatible weights; any claimed bridge must prove the coefficient transform before
using Cauchy--Schwarz.

### C3 verdict — falsified for exact matched-current producer

Route O's strongest exact coefficient-retaining signed term is
`ccmActualHeadMatchedSuzukiCurrent n f`. Existing Lean proves absolute summability over every
natural/prime-power label. Retain all labels below the open `N`th-prime cutoff:

```text
S_N(f) = sum_(n<p_N) ccmActualHeadMatchedSuzukiCurrent(n,f).
```

Then `S_N(f)` converges to its source total, while `H_N^3=(log p_N)^3 -> infinity`; hence

```text
S_N(f)/H_N^3 -> 0.                                              (6)
```

For every fixed source scaling `k`, the compensated trace

```text
K_N(c) - k S_N(f)/H_N^3
```

still tends to `(8/3)||c||^2` and still overspends primitive budget eventually. This preserves the
actual Route-O current rather than replacing it by a scalar majorant.

## Scoped retirement verdict

No primitive-budget control can be obtained from:

1. complete positive BV conservation;
2. canonical endpoint-positive/interior-negative Krein conservation; or
3. any fixed coefficient-faithful scaling of Route O's exact matched Suzuki current.

A surviving producer must introduce a genuinely new **cubic-order, non-summable but
source-renormalized negative channel** before selected positivity. Clock-dependent rescaling of a
summable Route-O current is not source naturality and is excluded from this scoped route. This card
does not rule out every nonlinear completed-source mechanism and does not prove RH.

## Strongest positive survivors

- exact finite complementary jet law `iota_N + epsilon_N = 1`;
- strict positivity `iota_N>0` at every clock;
- new symbolic arithmetic bound `sum_p 1/(p log(p)^2)<2`;
- sharpened literal primitive base budget `B_P<1`;
- cubic-scale nullity of exact Route-O matched signed current under prime-clock normalization.

All are formalized unconditionally in
`SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall.lean`.

## Gates

- [x] internal corpus audit
- [x] bounded primary-literature audit
- [x] refute C1 exactly on paper
- [x] refute C2 with sharper coefficient arithmetic
- [x] refute C3 on exact matched Route-O current
- [x] formalize every dependency-closed survivor
- [x] update RH frontier map
