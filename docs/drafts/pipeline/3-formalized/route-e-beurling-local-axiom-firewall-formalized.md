# Route E Beurling local-axiom firewall — formalized closure

- **ID:** `route-e-beurling-local-axiom-firewall-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-CLASSIFICATION FIREWALL (Lean)
- **Paper proof:** `./route-e-beurling-local-axiom-firewall.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED]`

## Lean modules

The abstract layer, in dependency order:

- `GaloisForLFunctions.RHTower.BeurlingSystemGibbsGauge` — `structure BeurlingSystem`, the
  generalized integers `Multiset Label`, `intNorm`, the generalized Möbius function and its divisor
  identity, the Rayleigh law `(BF2)` and the divided-log gauge `(BF10)`–`(BF11)`.
- `.../BeurlingSystemCounting` — `IsDiscrete`, `countBall`, `HasLinearCounting`, and absolute
  convergence of the exponential Gibbs sums.
- `.../BeurlingSystemDecomposition` — the three-sector split `(BF3)`–`(BF4)`.
- `.../BeurlingSystemTailBound` — the window estimate `(BF15)` and the remainder bound `(BF6)`.
- `.../BeurlingSystemTransitionKernel` — the kernel `(BF7)`, its strict antitonicity and the unique
  sign transition.
- `.../BeurlingSystemZetaSeries` — the two Dirichlet series and the real Möbius inversion.
- `.../BeurlingSystemMellin` — the Mellin identity `(BF16)`, the strict-half failure `(BF13)` and
  the aperture failure `(BF14)`.
- `.../BeurlingSystemPrefixFirewall` — the local-prefix nonrobustness law `(BF22)`.
- `.../BeurlingSystemPartialSummation` — the prime counting functions, the generalized prime number
  theorem `HasPrimePNT`, and Abel summation over generalized primes.
- `.../BeurlingSystemPrimeSumAsymptotic` — the power form of `(BF9)`.
- `.../BeurlingSystemMertensWindow` — the Mertens form of `(BF9)`.
- `.../BeurlingSystemTransitionAsymptotic` — the transition asymptotic `(BF8)`.

Reused from the general analytic layer:

- `GaloisForLFunctions.HTGeometry.LogWeightedRpowIntegral` — the logarithmic power integral, its
  asymptotic, and (new in this closure) `tendsto_logKernelRemainder`, the general statement that a
  vanishing weight against a kernel dominated by `C·t^(a-1)/log t` contributes `o(x^a/log x)`.
  The private Abel remainder of `RHTower.PrimeRpowSumAsymptotic` is now a one-line consequence.
- mathlib `hasSum_mellin`, `intervalIntegral.integral_indicator`,
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `Real.tsum_le_of_sum_le`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Formal theorem chain

1. **The system.**  `BeurlingSystem` carries prime labels with norms above one; the generalized
   integers are the free commutative monoid `Multiset Label` and `intNorm` is multiplicative.  Every
   statement below is a theorem about an arbitrary such system, so nothing is assumed about the
   existence of exotic systems: the Diamond–Montgomery–Vorhauer and Zhang constructions enter only
   as hypotheses when a card statement needs them.
2. **Item 3, `(BF2)`.**  `gibbsWeight_mul_le` / `gibbsWeight_mul_lt`.
3. **Item 4, `(BF3)`–`(BF4)`.**  `phi_eq_apertureSum_sub_tsum_add`, through the reindexing
   `oneLargeSum_eq_neg_tsum` of the one-large-prime sector.
4. **Item 5.**  `exists_unique_transition` and `transitionKernel_sign` are `(BF7)`;
   `tendsto_transition_ratio` is `(BF8)`; `tendsto_primeRpowSum` and `tendsto_primeInvWindowSum`
   are the two halves of `(BF9)`.
5. **Item 6, `(BF10)`–`(BF11)`.**  `log_labelNorm_div_log_intNorm_replicate` and
   `gammaGauge_mem_Icc_of_truncate`.
6. **Item 7, `(BF13)`–`(BF16)`.**  `mellin_phi_eq_gamma_div`,
   `not_isBigO_rpow_of_continuation_eq_zero`, `not_aperture_decay_of_continuation_eq_zero`.
7. **`(BF22)`.**  `not_isPrefixNeighborhood_of_isSoundCertificate`.

## Partial summation over generalized primes

The reusable core of this closure is `sum_primeWindow_eq_sub_sub_integral`:

```text
∑_{Y < |p| ≤ X} f(|p|) = π_P(X) f(X) - π_P(Y) f(Y) - ∫_Y^X f'(t) π_P(t) dt
```

for a discrete system and any `f` differentiable on `[Y,X]` with interval-integrable derivative.
Three steps: `f(|p|) - f(Y)` is the integral of `f'` against the indicator of `{t ≤ |p|}`; the
finite sum and the integral are exchanged; the resulting weight is identified with
`π_P(X) - π_P^<(t)`, and the strict counting function is replaced by the non-strict one because
they differ only on the finite set of prime norms below `X`.

The same identity drives all three PNT-consuming statements: the power sum `(BF9a)` with
`f(t) = t^{a-1}`, the Mertens window `(BF9b)` with `f(t) = t^{-1}`, and the exponential tail of
`(BF8)` with `f(t) = e^{-(t-1)τ}`.

## Axioms

`#print axioms` on every theorem above: `propext`, `Classical.choice`, `Quot.sound`.

## What is not formalized

The existence of Beurling systems with the pathologies the card uses — the Diamond–Montgomery–
Vorhauer error term and Zhang's prime distribution — is an external construction.  Formalizing it
is a separate long project; the firewall itself is unconditional.
