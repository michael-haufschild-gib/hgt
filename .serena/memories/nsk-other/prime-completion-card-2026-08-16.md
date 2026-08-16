# Prime-completion card: from no Lean to one reindexing short

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/prime-completion-annihilates-hypertranscendence-at-even-temperature.md`

## Why this card is nearly closable

The corpus already owned BOTH hard halves; nobody had connected them.
- HT of finite prime packets: `HTGeometry/PrimeLinearOccupationHypertranscendence.lean`
  (`hypertranscendental_primeOccupationFaceA`), built on `PrimeNomePeriod.lean` and the
  period-rank dichotomy `MultipleEllipticGammaPeriodRankDichotomy.lean`.
- DA of the even-temperature completion: `HTGeometry/EvenPowerCanonicalProductDA.lean`
  (`differentiallyAlgebraic_powerCanonicalProduct_of_even`, `pi_mul_sincProduct`,
  `powerCanonicalProduct_even_eq_prod_sinc`).

## Built 2026-08-16 (unconditional, axiom-clean, umbrella-wired)

`HTGeometry/PrimeOccupationCompletionProduct.lean` (430 lines)
- `occupationProduct r x := powerCanonicalProduct r (-x)` = `∏_{n≥1}(1 - x/n^r)`;
  `hasProd_occupationProduct`, `analyticOnNhd_occupationProduct`
- `differentiallyAlgebraic_occupationProduct_of_even`  (card (7))
- `occupationProduct_two_sq`, `pi_mul_occupationProduct_two` : `π c Φ₂(c²) = sin(πc)`
- `ode_of_sin_square_law` (generic!) and `occupationProduct_two_ode` : `4xΦ'' + 6Φ' + π²Φ = 0`
  (card (8)).  Proof: `G(c) = cΦ(c²) = sin(πc)/π` gives `G'' = -π²G`, i.e. `c·E(c²) = 0`;
  every nonzero `x` is a square, and continuity closes `x = 0`.
- Euler jet (card (4)-(6)): `natPowInvHom k`, `smoothZetaSum N k`,
  `prod_primesBelow_eq_smoothZetaSum` (mathlib `EulerProduct`),
  `tendsto_smoothZetaSum`, `tendsto_prod_primesBelow_riemannZeta`
- packet product + cofinal completion (card (3)): `occFull`, `occSmooth`,
  `smoothOccupationProduct`, `hasProd_occFull`, `tendsto_smoothOccupationProduct`
- unique factorization (card (11)): `occupationEquivPrimeSupported`, `occupationEquivPNat`,
  `occupationEquivPNat_coe`

`HTGeometry/InfiniteProductNearOne.lean` — added `norm_prod_one_add_sub_prod_one_add_le` and
`norm_tprod_one_add_sub_tprod_one_add_le` (two-product comparison; an RHTower copy existed but
importing RHTower from HTGeometry would invert the layering).

`HTGeometry/PrimePowerOccupationHypertranscendence.lean` (card (2))
- `primePowerNomePeriod r q := r · primeNomePeriod q`, `..._im_pos`,
  `ellipticNome_primePowerNomePeriod`, `periodsIntegrallyIndependent_natCast_mul`,
  `periodsIntegrallyIndependent_primePowerNomePeriod`
- `primePowerNome`, `primeOccupationFacePow r S` (= the card's `Φ_{S,r}`),
  `multipleEllipticGammaBackwardProduct_primePowerNomePeriod`,
  `hypertranscendental_primeOccupationFacePow` (r ≥ 1, |S| ≥ 2),
  `hypertranscendental_primeOccupationFacePow_neg`

## The single remaining step

Transport `primeOccupationFacePow r S` (indexed by `ν : S →₀ ℕ`) to `smoothOccupationProduct N r`
(indexed by the `S`-smooth positive integers) along the restriction of `occupationEquivPNat` to a
packet — i.e. `nomeMonomial (fun p : S => (1/p)^r) ν = 1/(∏ p^{ν_p})^r` plus the reindexing
`Equiv.tprod_eq`.  After that every item of the card refers to one object and the card is complete.

Watch out: `Nat.Primes` and `{p // Nat.Prime p}` are defeq but elaborate to different coercions;
state value lemmas through `Finsupp.extendDomain`/`Subtype.val` rather than `↑`.
