# Annihilator quotient signs have bounded logarithmic gaps

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; positivity after finite annihilator division.
- **Statement:** For a normalized positive two-prime polynomial vanishing at
  `ρ`, `β=Re ρ>0`, the canonical quotient coefficients have uniformly positive
  weighted mass of each sign in every sufficiently high logarithmic band of
  a fixed width. Weight is `exp(−β log n)`. Width `2B` suffices whenever
  `B>0` bounds all logarithmic frequencies in the annihilator.
- **Contribution count:** One (#12), including absolute boundary mass,
  positive-kernel sign transfer, and the actual finite xi-divisor application.
- **Novelty boundary:** Existing two-sided excursions and endpoint divergence
  allow sparse exceptional indices. A fixed-band lower bound would forbid
  arbitrarily long logarithmic gaps in either sign.

## Proof

Write `L_d=d₀ log 2+d₁ log 3`, `b_d` for the canonical quotient coefficient,
`F(T)=Σ_(L_d≤T) b_d exp(−ρL_d)`, and
`G(T)=Σ_(L_d≤T) exp(−ρL_d)`. These are finite sums. Choose `B>0` bounding
every frequency in `P.support`, and put `H=Σ_(e≠0)c_e exp(−βL_e)`.

1. The exact formal convolution gives
   `Σ_e c_e exp(−ρL_e) F(T−L_e)=G(T)`. Since `P(ρ)=0`, subtracting this from
   `P(ρ)F(T)=0` leaves only `T−B<L_d≤T`. Thus
   `|G(T)|≤(1+H) Σ_(T−B<L_d≤T)|b_d|exp(−βL_d)`.
2. The geometric numerator converges to
   `G=1/((1−2^(−ρ))(1−3^(−ρ)))≠0`. Hence the absolute band mass is eventually
   at least some `c₀>0`, at the exact exponent `β`.
3. Put `u_d=b_d exp(−βL_d)`. Positivity of the convolution kernel gives
   `u_d⁺≤exp(−βL_d)+Σ_(e≠0)c_e exp(−βL_e)u_(d−e)⁻` and
   `u_d⁻≤Σ_(e≠0)c_e exp(−βL_e)u_(d−e)⁺`, omitting indices with `e≰d`.
4. Translation by `e` maps the narrow band injectively into
   `T−2B<L_d≤T`. If `M` is the narrow absolute mass and `P₂,N₂` are the
   wider positive and negative masses, summing gives
   `M≤(H+1)P₂` and `M≤G_abs(T)+(H+1)N₂`.
5. The geometric forcing `G_abs(T)` in the narrow band tends to zero by
   absolute summability. Eventually it is below `c₀/2`, forcing both wider
   sign masses above `c₀/(2(H+1))`. Translating the cutoff gives the claimed
   fixed-width forward bands.
6. Apply this theorem to the corpus's positive annihilators of arbitrary
   finite actual xi divisors with prescribed multiplicities and arbitrary
   accuracy in `Re s≥1`. No analytic continuation of the quotient is assumed.

## Lean certificate

Paths are relative to `formal/GaloisForLFunctions/ArithmeticPositiveDuality/`.

| Module | Capstone |
|---|---|
| `QuotientMassCannotSkipLogarithmicBands.lean` | `quotient_band_mass_eventually_lower` |
| `QuotientSignsHaveBoundedLogarithmicGaps.lean` | `quotient_sign_band_mass_eventually_lower` |
| `QuotientSignsHaveBoundedLogarithmicGaps.lean` | `quotient_signs_have_bounded_logarithmic_gaps` |
| `QuotientSignsHaveBoundedLogarithmicGaps.lean` | `exists_xi_annihilator_with_quotient_band_oscillation` |

Both new modules and the reused recurrence module
`AnnihilatorDivisionForcesCoefficientOscillation.lean` pass direct
`lake --old env lean` audits without warnings. All capstones have only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. New
modules are umbrella-wired. Existing recurrence proofs are reused through
public declarations.

The width and lower mass depend on the annihilator. The result excludes
sparse sign defects in its canonical quotient; it does not exclude finite
off-line xi divisors or prove RH.
