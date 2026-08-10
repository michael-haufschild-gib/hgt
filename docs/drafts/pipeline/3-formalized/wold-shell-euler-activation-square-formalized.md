# Wold–shell Euler activation square — formalized closure

- **ID:** `wold-shell-euler-activation-square-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./wold-shell-euler-activation-square.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [OPEN CORE REMAINS]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.RHTower.WoldEulerActivationSquare` — the finite-depth activation series, its
  Euler product `(4)` and all four faces `(5)`.
- `GaloisForLFunctions.RHTower.WoldShellTangentTransfer` — the shell tangent `(14)` and the whole
  transfer spectrum `(15)`–`(18)`.

Pre-existing and reused:

- `WoldEulerActivationHolonomy` (zero face, cocycle `(6)`, first von-Mangoldt jet `(10)`–`(11)`,
  infinite-activation limit);
- `WoldActivationDivisorBlowup` (the local factorization `(20)`, the two incompatible faces `(22)`
  and the blow-up chart limit `(23)`) — already complete before this closure;
- `SuzukiPacketCoefficientSeries` (`suzukiRadicalFactor`, the packet L-series);
- `MFreeLadder` (`MFree`, `mFreeIndicator`, `LSeries_mFree_eq_riemannZeta_div`);
- `XiSourceNormalConeDivisorConservation` (`tendsto_riemannZeta_of_re_atTop`, generalized here to
  arbitrary filters as `tendsto_riemannZeta_of_re_atTop_filter`);
- mathlib `LSeriesSummable_vonMangoldt`, `ArithmeticFunction.IsMultiplicative.eulerProduct_tprod`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Formal theorem chain

1. **The activation coefficient.**  `activationFactor h = suzukiRadicalFactor (h/2)` reuses the
   corpus radical factor rather than rebuilding it; `activationFactor_apply` is `(1)` and
   `norm_activationFactor_le_one` the `0 ≤ a_h ≤ 1` bound used throughout.
2. **The depth truncation.**  `activationDepthFactor h m` is the activation coefficient times the
   `(m+1)`-free indicator, which is exactly `M(n) ≤ m`; multiplicativity comes from
   `isMultiplicative_mFreeIndicator` and the radical factor.
3. **The Euler activation square `(4)`.**  `activationCpow_prime_pow` computes the local factor as
   `1 + (1 - p^{-h}) ∑_{k=1}^m p^{-ks}` and `activationSeries_eq_tprod` is the product formula.
4. **The four faces `(5)`.**  `activationSeries_zero_activation` (zero activation),
   `tendsto_activationSeries_depth` (infinite depth, `ζ(s)/ζ(s+h)`),
   `tendsto_activationSeries_activation` (full activation, `ζ(s)/ζ((m+1)s)`), and
   `tendsto_zetaRatio_depth`, `tendsto_zetaRatio_activation` (the corner, in both orders).  Both
   limit faces are dominated-convergence arguments over the same `n^{-σ}` bound.
5. **The shell tangent `(14)` and its spectrum `(15)`–`(18)`.**  `tendsto_normalizedPrimeTail` is
   the tail estimate; `normalizedShellTangent_sub_atoms` strips atoms;
   `tendsto_normalized_shellTangent_two` and `tendsto_normalized_shellTangent_three` are `(15)` and
   `(16)`; `tendsto_ratio_of_normalized` yields `(17)` and its residual form; and the half-density
   statements `(18)` follow with the real masses `shellTangentMass`, `shellTangentMassThree`.
6. **The divisor blow-up `(19)`–`(23)`.**  Already formalized in `WoldActivationDivisorBlowup`:
   `woldActivationInfiniteDepth_zero_activation` and `woldActivationInfiniteDepth_on_divisor` are
   the two incompatible faces `(22)`, and
   `exists_tendsto_woldActivationInfiniteDepth_blowupChart` is `(23)`.

## New reusable assets

- `tendsto_riemannZeta_of_re_atTop_filter` — zeta tends to one along *any* filter escaping through
  the right half-plane; the corpus previously had only the sequential form.
- `tendsto_ratio_of_normalized` and `tendsto_ratio_of_normalized_real` — adjacent-ratio limits from
  a normalization, complex and real.
- `summable_logPrime_rpow` — `∑_p (log p) p^{-σ} < ∞` for `σ > 1`, extracted from the von Mangoldt
  L-series.

## Verification

- `lake env lean` clean, with no warnings, on both new modules.
- `lake build GaloisForLFunctions.RHTower.WoldShellTangentTransfer` — green, with both modules
  wired into the area umbrella.
- `#print axioms` on the seventeen capstones of items 3–6: `propext`, `Classical.choice`,
  `Quot.sound` only.

## Scope boundary

The activation parameter is real and nonnegative in the series statements — exactly the range in
which `(3)` converges absolutely and `a_h` is bounded by one — while the blow-up statements use the
continued ratio `ζ(s)/ζ(s+h)` in the complex variable `h`, as on the paper card.  Equation `(7)`
(the connection at general `h`) and `(8)` (the holonomy integral) are not restated; the `h = 0` jet
`(10)`–`(11)`, which is what the card consumes, is in `WoldEulerActivationHolonomy`.

The card's remaining gate is its own open core, the exceptional Gamma/co-Poisson transport, plus a
broader literature audit; neither is a Lean gate.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
