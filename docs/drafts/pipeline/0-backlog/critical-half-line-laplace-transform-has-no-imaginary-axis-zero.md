# Critical half-line Laplace transforms have no imaginary-axis zero

- **ID:** critical-state-boundary-laplace
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** B104; actual weak equation and weighted causal resolvents.
- **Statement:** Every actual critical half-line state at a finite global window threshold has `∫ F(u) exp(iτu) du ≠ 0` for every real τ.
- **Status:** Unproved. The open-right-half-plane extension is also awaiting its final Lean check.

## Goal

Determine whether the actual critical-state line has any real Fourier zero.
This is a boundary claim beyond open-half-plane Laplace nonvanishing; it
does not establish the polar charge or an outer-factor theorem.

## Approach

At an imaginary-axis zero, the undamped oscillatory causal resolvent has
zero positive tail. Exponential weighting shifts its kernel into the
decaying half-plane, so the verified weighted L² closure still applies.
Half-line support should then supply unweighted L² and L¹ admission.

Use the real sum of the two conjugate undamped resolvents as a test in the
verified actual weak equation. Their Fourier multipliers are purely
imaginary away from the cancelled poles; the symmetric prime/Gamma mixed
forms should vanish. The opposite pole-moment factors are odd, giving zero
mixed pole term. The exponentially weighted mixed term should instead be
a positive multiple of the sum of the two resolvent norms.

## Exact missing inputs

- Full Gamma admission of the actual undamped resolvent near its cancelled Fourier pole.
- The neutral complex moment law with integrability of the actual resolvent derived from the weighted domain.
- Exact vanishing of the symmetric prime/Gamma and pole mixed terms.
- The positive weighted mixed identity and its use in the actual weak equation.

## Corpus inputs

- `criticalHalfLineMixedEnergy_groundState_eq_zero`: the actual finite-energy weak equation, without polar-threshold equality.
- `memLp_weighted_modulatedCausalConvolution`: the shifted decay condition permits an undamped kernel with a positive exponential weight.
- `RHTower.WeilHerglotz.continuous_gammaBracket`: local Gamma control near each cancelled Fourier pole.
- `RHTower.integrable_expWeight_of_memLp_two`: reflected weighted L² data admit L¹ after removing part of the exponential weight.
- `RHTower.WeilSpectral.abs_gammaBracket_le_sqrt`: linear Fourier decay makes the Gamma density integrable with a `(1+|r|)^(-3/2)` majorant; the domination proof occurs in `tendsto_archPoleEnergy_truncTest`.

The neutral moment proof can use actual resolvent L¹ admission: approach
the imaginary axis through positive real parts and apply the verified
anti-causal moment formula. Away from the cancelled Fourier pole this gives
the multiplier bound; near the pole, resolvent L¹ bounds its Fourier
transform. Combining both bounds gives `O((1+|r|)^(-1))` decay and hence
Gamma admission directly from the square-root Gamma bound.

No proof or contribution is counted.

Written, unchecked support: `ArithmeticHodgeTheoryOfDegenerations/CausalReflection/GammaIntegrabilityFromLinearFourierDecay`.
