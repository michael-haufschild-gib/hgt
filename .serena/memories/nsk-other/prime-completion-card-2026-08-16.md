# Prime-completion card — CLOSED and promoted to stage 3 (2026-08-16)

Card now at
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/prime-completion-annihilates-hypertranscendence-at-even-temperature.md`

## Why it closed fast

The corpus already owned BOTH hard halves and nobody had connected them:
- `HTGeometry/PrimeLinearOccupationHypertranscendence.lean` — HT of finite prime packets at LINEAR
  temperature, via `PrimeNomePeriod.lean` and `MultipleEllipticGammaPeriodRankDichotomy.lean`;
- `HTGeometry/EvenPowerCanonicalProductDA.lean` — even-exponent canonical products factor into
  Euler sine products, hence are differentially algebraic.

Also reused: `Core.primeProduct` / `primeProduct_injective`, `HTGeometry/SmoothNumbers.lean`
(`primeExponentVector`, `primeProduct_primeExponentVector`) for unique factorization;
`HTGeometry/OccupationEulerProduct.lean` (`hasSum_supported_nomeMonomial`) for the packet Euler
factorization; `HTGeometry/PrimeOccupationCofinalLimit.lean` (`occupationSupported`,
`cofinal_occupationSupported`, `smoothPowerSum`, `tendsto_smoothPowerSum`,
`tendsto_tsum_subtype_of_cofinal`) for the cofinal machinery.

## New modules (all unconditional, axiom-clean, umbrella-wired)

- `HTGeometry/PrimeOccupationCompletionProduct.lean` — `occupationProduct r x = ∏_{n≥1}(1-x/n^r)`;
  `differentiallyAlgebraic_occupationProduct_of_even`; `pi_mul_occupationProduct_two`;
  `ode_of_sin_square_law` + `occupationProduct_two_ode` (`4xΦ''+6Φ'+π²Φ=0`); the smooth-number
  packet product and `tendsto_smoothOccupationProduct`; `natPowInvHom`, `smoothZetaSum`,
  `prod_primesBelow_eq_smoothZetaSum`, `tendsto_smoothZetaSum`; `occupationEquivPNat`.
- `HTGeometry/PrimePowerOccupationHypertranscendence.lean` — `primePowerNomePeriod r q`,
  `periodsIntegrallyIndependent_natCast_mul`, `primeOccupationFacePow r S`,
  `multipleEllipticGammaBackwardProduct_primePowerNomePeriod`,
  `hypertranscendental_primeOccupationFacePow`.
- `HTGeometry/PrimeOccupationCompletionLimit.lean` — `occupationEquivNatPos`,
  `hasProd_occupationProduct_occ`, `occupationSupportedEquiv`,
  `primeOccupationFacePow_eq_tprod_occ`, `tendsto_primeOccupationFacePow`,
  `tsum_occupationRecip_pow_eq_riemannZeta`, `tendsto_smoothPowerSum_riemannZeta`,
  `smoothPowerSum_eq_prod`, `tendsto_prod_primePowerNome_riemannZeta`,
  `hasDerivAt_primeOccupationFacePow_zero`, `deriv_primeOccupationFacePow_zero`,
  `tendsto_deriv_primeOccupationFacePow_zero`,
  `cexp_neg_logSeries_eq_primeOccupationFacePow` (needs `maxHeartbeats 1000000`).
- `HTGeometry/InfiniteProductNearOne.lean` extended: `norm_prod_one_add_sub_prod_one_add_le`,
  `norm_tprod_one_add_sub_tprod_one_add_le`, `norm_prod_one_add_sub_one_sub_sum_le`,
  `norm_tprod_one_add_sub_one_sub_tsum_le`, `hasDerivAt_tprod_one_add_mul`.

## Reusable techniques that worked

- Two-product comparison `‖∏(1+a) − ∏(1+b)‖ ≤ (∑‖a−b‖)·exp(∑(‖a‖+‖b‖))` + the smooth/occupation
  tail estimate is the standard way to turn a cofinal exhaustion into product convergence.
- The log expansion of a product is branch-free if stated as
  `exp(−∑_n x^n/n · P(rn)) = Φ(x)`: use `Complex.hasSum_taylorSeries_neg_log`,
  `HasSum.prod_fiberwise` in both directions over `T × ℕ` (swap with `Equiv.prodComm`), and
  `Complex.cexp_tsum_eq_tprod`.
- `e^t − 1 − t ≤ t²e^t` for `t ≥ 0`: split at `t = 1`; below use `1 − t ≤ e^{−t}`.
- Namespace trap: `EvenPowerCanonicalProductDA` lives in ROOT `HTGeometry`, most other modules in
  `GaloisForLFunctions.HTGeometry`.  `open HTGeometry` inside `namespace GaloisForLFunctions.HTGeometry`
  resolves to the current namespace, not the root one.
