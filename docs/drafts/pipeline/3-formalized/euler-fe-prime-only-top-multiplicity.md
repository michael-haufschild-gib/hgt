# The raw Gaussian prime current at a rightmost zero

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport theory: resonance of the full prime discrepancy.

## Theorem

Let `ρ` be an actual rightmost Xi zero, of divisor multiplicity `mρ`. For

`Gρ(y)=ΣₙΛ(n)n^(−ρ)e^(−yn²)−∫₁∞v^(−ρ)e^(−yv²)dv`,

Then `Gρ(e^(−u))/u → −mρ/2` as `u→∞`.

The observable contains only the actual prime current and its continuum. It
contains no divisor-defined counterterm. Rightmostness need not be isolated:
equal-abscissa zeros and zeros approaching that abscissa remain in the full sum.
The actual finite-top theorem under `¬AAL` produces such a zero with
`Re ρ>½`, without an additional analytic premise.

## Mechanism

The resonant finite-part identity gives
`Gρ(y)+Bρ(y)−(mρ/2)log y → Kρ` with the complete nonresonant Gamma field.
At a rightmost zero, every exponent in `Bρ(y)` has nonnegative real part.
For `0<y≤1`, each mode is bounded by its absolute value at `y=1`; those
amplitudes are summable. Thus `Bρ(e^(−u))` is uniformly bounded and vanishes
after division by `u`. The finite-part error does too, while
`log(e^(−u))/u=−1`.

More explicitly, set `Aρ=Σoff |½Γ((ρq−ρ)/2)|`. Absolute admission at `y=1`
makes `Aρ` finite. Rightmostness gives
`|y^(−(ρq−ρ)/2)|=y^((Re ρ−Re ρq)/2)≤1`, so `|Bρ(y)|≤Aρ`.
The finite-part expression divided by `u` tends to zero; subtracting
`Bρ(e^(−u))/u` and `mρ/2` proves the raw-current limit.

Under `¬AAL`, the proved finite-top theorem supplies a nonempty set `F`,
`β>½`, and `θ<β`, with all zeros in `F` at abscissa `β` and every
complementary zero at abscissa at most `θ`. Any zero copy in `F` therefore
supplies the required actual rightmost support point. No new analytic
assumption enters this specialization.

## Formalization and scope

`EulerFETransportTheory/ThePrimeCurrentReadsTopMultiplicity.lean` proves:

- `norm_nonresonantGaussianModes_le_of_rightmost`: full-field uniform bound.
- `tendsto_gaussianPrimeGap_div_logScale_of_rightmost`: raw-current limit.
- `not_asymptoticAbscissaLaw_has_primeMultiplicityLimit`: actual off-line
  specialization under `¬AAL`.

Direct Lean checking succeeds without warnings. Both terminal transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The prerequisite renormalization is proved in
`../3-formalized/euler-fe-two-scale-zero-multiplicity.md`.

The observable contains no divisor counterterm, but its observation point is
an existing rightmost zero. The law supplies neither a contradiction to a
finite top nor a new zero height. Same-depth replication remains open.
