# Prime-depth BV--Wold Schatten wall

- **ID:** prime-depth-bv-wold-schatten-wall
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CROSS-ROUTE CLASSIFICATION
- **Source:** `../../1-in-progress/rh-current-frontier-map.md` §1
- **Statement:** All-prime BV--Wold log anomaly is summable exactly from depth two onward; adding physical/unit-double trace-class remainder does not change this threshold.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: `RHTower/PrimeDepthWoldWall.lean`, unconditional
      (`[propext, Classical.choice, Quot.sound]`)
- [ ] 3 → 4 publication-ready

## Definitions

For ordinary prime `p`, depth `e`, and scalar `a`, put

```text
c_e(p)=(1-p^(-1))^3 p^(-e) log p,
w_(a,e)(p)=a c_e(p),
r(p)=2 log p/p^2.
```

Existing atlas transition proves `log A_(p,e)(s)=(2 Re(s)-1)c_e(p)` and existing physical/unit-double seam proves `r` summable.

## Theorem `[PROVED HERE]`

For every `e : Nat` and `a : Real`,

```text
Summable c_e                    iff 2<=e,
Summable w_(a,e)                iff a=0 or 2<=e,
Summable (w_(a,e)+r)            iff a=0 or 2<=e.
```

Thus at depth one,

```text
Summable_p (log A_(p,1)(s)+r(p)) iff Re(s)=1/2.
```

## Proof

Every prime satisfies `p≥2`, so `1/2≤1-p⁻¹<1`.

At depth one,

```text
c_1(p) ≥ (1/8) log(p)/p.
```

The prime sum of `log(p)/p` diverges.  Indeed, `log p≥log 2>0`; convergence would imply convergence of `(log 2) sum_p 1/p`, contradicting Euler's divergence.  Hence `c_1` is not summable.  Since `p⁻¹≤1`, `c_0≥c_1`, so `c_0` is not summable.

For `e≥2`, `0<p⁻¹≤1` gives

```text
0≤c_e(p)≤log(p)/p².
```

Right side is summable, proving first equivalence.  Multiplication by nonzero scalar preserves and reflects summability, proving second.  Since `r` is summable, a family is summable exactly when its sum with `r` is summable, proving third.  Substitute `a=2 Re(s)-1` for depth-one conclusion.  No RH or zero-location premise occurs.

## New knowledge

Wold depth crosses global operator-ideal wall:

```text
depth 0,1 : local orientation anomaly is globally nonsummable;
depth ≥2  : same nonzero anomaly is globally trace-class.
```

Depth therefore adds Kummer roots while regularizing away global orientation obstruction.  Useful Frankenstein atlas is polarized across transition `1→2`, not cofinal in depth.  Any fixed trace-class physical correction is incapable of hiding depth-one anomaly; if merged relative determinant is Schatten-1, centered Xi rate must vanish.

## Lean

`GaloisForLFunctions/RHTower/PrimeDepthWoldWall.lean`, indexed over `Nat.Primes`:

- `woldCoeff e p = (1 − 1/p)³ · log p / p^e`, `woldRemainder p = 2 log p / p²`;
- `woldFactor_mem` — the Euler factor is trapped: `1/8 ≤ (1 − 1/p)³ ≤ 1`, from `p ≥ 2`;
- `summable_log_div_sq` — `∑_p log p/p²` converges, by `log p ≤ 2√p`
  (`Sieve.log_le_two_mul_sqrt`) against `Nat.Primes.summable_rpow` at `−3/2`;
- `summable_woldCoeff_of_two_le` — above the wall `c_e(p) ≤ log p/p²`;
- `not_summable_woldCoeff_of_lt_two` — below it `c_e(p) ≥ (log 2/8)·(1/p)`, and
  `Nat.Primes.not_summable_one_div` closes it;
- **`summable_woldCoeff_iff`** — `Summable c_e ↔ 2 ≤ e`;
- **`summable_smul_woldCoeff_iff`** — `Summable w_{a,e} ↔ a = 0 ∨ 2 ≤ e`;
- **`summable_smul_woldCoeff_add_remainder_iff`** — `Summable (w_{a,e} + r) ↔ a = 0 ∨ 2 ≤ e`.

The three equivalences of the theorem statement are machine-checked exactly as stated.  No RH or
zero-location premise enters, matching the paper proof.

## Log

- 2026-08-04 — paper proof completed; moved directly from Stage 1 to Stage 2.
- 2026-08-04 — formalized in Lean, unconditionally; gate 2 → 3 closed.
