# Mass–Xi high-prime-power vertical ideal

## Status

- Lane: `3-formalized`
- Conjecture: `C31` — proved
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- Lean: `formal/GaloisForLFunctions/RHTower/XiMassPrimePowerVerticalIdeal.lean`

## Exact theorem

For the depth-erased mass source, the critical coefficient at prime power `p^(k+1)` is

```text
xiMassPrimePowerCriticalWeight p k
  = log(p) · p^(-(k+1)/2).
```

All valuation depths at least three are absolutely summable:

```text
Summable (fun (p,k) => xiMassPrimePowerCriticalWeight p (k+2)).
```

Let

```text
H_a(τ) = ∑' (p,k), xiMassCenteredPrimeAtom a τ (p^(k+3)).
```

For `a>0`, `σ>0`, and every `u : ℝ`, Lean proves the uniform vertical bound

```text
‖H_a(σ+iu)‖
  ≤ (∑' (p,k), xiMassPrimePowerCriticalWeight p (k+2))
      · ∫_ℝ exp(-σ|x|) dx.
```

The right side is finite and independent of `u`. For every legal Euler depth `1/2<c<a` and
`Re τ>0`, the literal bottom source splits exactly as

```text
∫_ℝ xiMassBottomPrimeIntegrand a c τ x dx
  = ∑' p, centeredAtom(a,τ,p)
    + ∑' p, centeredAtom(a,τ,p^2)
    + H_a(τ).
```

All rearrangements are justified by absolute summability.

## Proof

The uniform strip-Fourier estimate

```text
‖stripFourier (xiMassAnalyticTest a (σ+iu)) w‖
  ≤ ∫_ℝ exp(-σ|x|) dx
```

removes both vertical time `u` and frequency `w` from each atom norm. The exact von-Mangoldt
coefficient then leaves `log(p) p^{-r/2}` at valuation depth `r`.

For `r=k+3`, split `k` by parity. The even subsequence is a geometric depth series over the prime
base weight `log(p)p^{-3/2}`; the odd subsequence has base weight `log(p)p^{-2}`. Both prime sums
converge because their exponents exceed one, and the remaining depth ratio is at most `p^{-1}`.
The proof formalizes a more general theorem summing

```text
log(p) · (p⁻¹)^(k+β)
```

for every `β>1`.

Von-Mangoldt support is then reindexed by unique prime powers. Two exact `tsum_eq_zero_add` splits
extract depths one and two; Fubini/reindexing for the remaining absolutely summable product gives
the displayed source decomposition.

## New scientific knowledge

Valuation depth defines a sharp vertical ideal filtration. Depths `r≥3` form a bounded ideal and
cannot carry RH-strength vertical growth. Only the prime layer `r=1` and prime-square layer `r=2`
survive in the quotient seen by §9.3.

The threshold is structural, not a proof artifact: at the critical line the first omitted base
weight is `log(p)p^{-3/2}`, while the square layer has `log(p)p^{-1}` and is not absolutely
summable. C30 showed contour depth is a gauge; C31 shows Euler valuation depth, not contour depth,
is the first genuine source filtration. Any next cancellation invariant only needs to act on
primes and squares. Higher powers are rigorously harmless.

## Lean declarations

- `RHTower.norm_stripFourier_xiMassAnalyticTest_vertical_le`
- `RHTower.xiMassPrimePowerCriticalWeight_eq`
- `RHTower.summable_primeLog_mul_inv_rpow_add`
- `RHTower.summable_xiMassPrimePowerCriticalWeight_high`
- `RHTower.summable_norm_xiMassHighPrimePowerAtom`
- `RHTower.norm_xiMassHighPrimePowerTail_vertical_le`
- `RHTower.tsum_xiMassCenteredPrimeAtom_eq_prime_add_square_add_high`
- `RHTower.integral_xiMassBottomPrimeIntegrand_eq_prime_add_square_add_high`

## Verification

- `lake env lean GaloisForLFunctions/RHTower/XiMassPrimePowerVerticalIdeal.lean`: PASS
- `lake build GaloisForLFunctions.RHTower.XiMassPrimePowerVerticalIdeal`: PASS (`9379/9379`)
- Axiom audit of five key declarations: only `propext`, `Classical.choice`, `Quot.sound`
- No `sorry`, `admit`, local axiom, `opaque`, `unsafe`, computation proof, or RH hypothesis
- Wired into `GaloisForLFunctions.RHTower`
- Repository-wide lint reached this module and found it reachable; its final nonzero status came
  solely from two concurrently added, unrelated unwired modules in `RHTower` and `HTGeometry`

## Novelty audit

`[LOCAL-RESEARCH] [LEAN-PROVED] [NOVELTY UNVERIFIED]`.

Prime-power absolute convergence above exponent one is classical. The exact valuation-ideal
classification for the depth-erased mass–Xi source, its vertical-uniform high-power bound, and the
conclusion that §9.3 factors through the prime-plus-square quotient were not found in the audited
route corpus. External priority remains unverified.
