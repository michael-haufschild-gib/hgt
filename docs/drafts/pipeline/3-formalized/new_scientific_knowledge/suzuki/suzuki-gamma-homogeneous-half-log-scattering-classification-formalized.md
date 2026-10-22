# Gamma transport forces a complete half-log scattering classification, formalized

- **ID:** `suzuki-gamma-homogeneous-half-log-scattering-classification`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-gamma-homogeneous-half-log-scattering-classification.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaDistributionalHalfLine.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaHalfLineClassification.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiHalfLogScatteringKernel.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaCoronaSequence.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripBranch.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripGluing.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripCarrierIntegrability.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripSquareIntegrable.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripUniformBound.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripContourPairing.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaStripFourierWeight.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PointSupportGammaForm.lean`
  - `formal/GaloisForLFunctions/HTGeometry/HalfLogTraceNonIntegrable.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialTwist.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialTwistInversion.lean`
  - `formal/GaloisForLFunctions/HTGeometry/DistributionalLinearODE.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ConjugatedTransportRepresentation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/IntervalCutoff.lean`
  - `formal/GaloisForLFunctions/HTGeometry/HalfLineIntegratingFactor.lean`
  - `formal/GaloisForLFunctions/HTGeometry/IntervalTestSeparation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/HolomorphicBranch.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExpSelfAdjointNormBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GammaVerticalRatioBetaBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/GammaVerticalSubstripBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/StripContourShift.lean`
  - `formal/GaloisForLFunctions/HTGeometry/CompactTestTransform.lean`

## Formal content

| Card | Lean |
|---|---|
| `(6)`, `(7)` the unitary real-frequency transport `Q(η)` | `gammaTransport`, `gammaTransportInv`, `continuous_gammaTransport` |
| Theorem 1, `(8)`: `f = \|η\|^{-1/2}Q(η)c_±` on each open half-line | `gamma_tempered_classification`, `exists_channel_vector_positive`, `exists_channel_vector_negative` |
| Theorem 1: the channel vectors are unique | `channel_vector_unique_distributional` |
| Theorem 1: no additional distribution at `η = 0` | `eq_zero_of_pointSupport_gammaForm` |
| `(11)` the half-log scattering map `β(c₊,c₋)` | `halfLogScatter`, `halfLogScatter_surjective` |
| Theorem 2, `(12)`: `F(L) = L^{-1/2}β + O(L^{-1})` | `norm_gammaProfile_sub_halfLog_le` |
| Theorem 2, `(13)`: `β = 0 ⟹ F ∈ L²` on a terminal ray | `halfLog_trace_zero_iff_integrableOn_sq` |
| `(12)` reverse-triangle lower bound behind the converse | `norm_ge_of_halfLog_asymptotic` |
| nonzero trace destroys square integrability | `not_integrableOn_sq_of_halfLog_trace` |
| `(21)`, `(26)`, `(27)`: the branch of `z^{-1/2}` and its boundary values | `cpow_neg_half_ofReal_pos`, `cpow_neg_half_ofReal_neg`, `stripSolution_ofReal_pos`, `stripSolution_ofReal_neg` |
| the holomorphic square root of the Gamma quotient on the strip | `isSimplyConnected_imStrip`, `exists_differentiableOn_sq_eq`, `exists_gammaRatioSqrt` |
| `(28)` the strip solution is holomorphic on `0 < Im z < 1` | `stripSolution`, `differentiableOn_stripSolution` |
| Theorem 3, `(23)`: zero trace ⟺ `c₋ = -i c₊` ⟺ one holomorphic solution | `stripSolution_glue_iff`, `halfLogScatter_eq_zero_iff_glue` |
| `(29)` the vertical Gamma-quotient bound, uniform in the height | `norm_Gamma_vertical_le`, `exists_bound_gammaRatio_substrip` |
| `(30)` the operator factor `‖e^{-izT/2}‖ ≤ e^{σ‖T‖/2}` | `norm_exp_smul_le`, `norm_exp_imaginary_smul_eq_one` |
| `(31)` the pointwise modulus on the shifted line | `norm_sq_stripSolution_shift_le`, `norm_gammaRatio_shift` |
| Theorem 3, `(24)`: `f(·+iσ) ∈ L²(ℝ;X)` for every `0 < σ < 1` | `integrable_norm_sq_stripSolution`, `memLp_stripLine` |
| the strip solution is bounded on every closed substrip | `exists_bound_norm_stripSolution` |
| the entire Fourier extension of a test function and its `\|z\|^{-2}` decay | `testTransform`, `differentiable_testTransform`, `testTransform_ibp_two`, `exists_testTransform_decay`, `exists_testTransformTwoPi_decay` |
| the horizontal contour shift | `integral_line_shift`, `pairedIntegrand_line_shift` |
| the multiplication formula for the boundary pairing | `integral_weightedTest_smul_fourierInv` |
| `(32)` the Fourier translation identity | `stripFourier_weight_eq` |
| Theorem 3, `(25)`: `e^{2πσL}F(L) ∈ L²(ℝ;X)` for every `0 < σ < 1` | `exists_memLp_exp_smul_stripFourier` |
| `(33)` zero half-log trace forces exponential decay for every `σ < 1` | Theorems 1 and 3 together |

## What the card actually closes

Three theorems, all unconditional.

**Theorem 1** classifies the homogeneous sector.  An `X`-valued tempered distribution satisfying the
Gamma frequency equation is, on each open frequency half-line, exactly `|η|^{-1/2}Q(η)c_±` for one
channel vector; that vector is unique; and no nonzero solution is carried by the origin.  The proof
route is new, because an `X`-valued tempered distribution cannot be multiplied by an
operator-valued function and the classical integrating factor `η^{1/2}Q(η)^{-1}` therefore has no
distributional meaning.  It is replaced by the **exponential twist**

```text
(E_A u)(φ) = ∑_n (-A)^n u(η^n φ)/n!,
```

which converges because the values of a tempered distribution along the coordinate powers of a
compactly supported test function grow at most geometrically.  The twist of a solution of `u' = Au`
has vanishing derivative, so the du Bois-Reymond lemma makes it a constant multiple of Lebesgue
measure; the opposite twist inverts it by Fubini for the double family indexed by `(k,n)`,
regrouped by total degree, where the coefficient collapses to the alternating binomial sum.

**Theorem 2** is the half-log scattering asymptotic and its converse.  The endpoint trace `β` is
onto, the remainder is `O(L^{-1})`, and a nonzero trace forces `‖F(L)‖ ≥ ‖β‖L^{-1/2}/2` on a
terminal ray, so `∫‖F‖² ≥ (‖β‖²/4)∫dL/L` diverges: the kernel of the trace is exactly the physical
`L²` sector.

**Theorem 3** is the upper-strip gluing and its two analytic consequences.  Zero trace, `c₋ = -ic₊`,
and gluing of the two real-frequency channels into a single holomorphic solution on `0 < Im z < 1`
are equivalent; that solution is square integrable on every interior line; and its `L²` inverse
Fourier transforms on the different lines differ exactly by the exponential weights, so a single
frequency profile `F` satisfies `e^{2πσL}F ∈ L²(ℝ;X)` for every `0 < σ < 1`.

The last step is the substantive Paley–Wiener content and it is proved without Stirling
asymptotics.  The uniform-in-height Gamma bound comes from the Beta integral: `Γ(u)Γ(v) =
Γ(u+v)B(u,v)` and `‖B(u,v)‖ ≤ B(Re u, Re v)`, so `‖Γ(1+iz)/Γ(1-iz)‖ ≤ Γ(1-σ)/Γ(1+σ)` on the line
`Im z = σ`, a bound continuous in `σ` and hence bounded on every closed substrip.  Together with
`|z| ≥ Im z` and self-adjointness of `T` this makes the strip solution bounded across a closed
substrip.  Multiplying it by the entire extension

```text
Ψ(z) = ∫ ψ(L) e^{2πizL} dL
```

of a compactly supported smooth test function — entire by differentiation under the integral sign,
and `O(|z|^{-2})` on every horizontal strip by two integrations by parts — produces a holomorphic
integrand whose vertical segments vanish, so Cauchy's theorem on rectangles moves the line of
integration freely.  The multiplication formula for tempered distributions turns that shift into an
identity between the `L²` transforms: pairing `𝓕⁻(f_σ)` with `ψ·e^{-2πσL}` (compactly supported,
hence Schwartz) is the same as pairing `f_σ` with `Ψ(·+iσ)`.  Since the latter does not depend on
`σ`, the du Bois-Reymond lemma for locally integrable functions gives
`e^{-2πσL}𝓕⁻(f_σ)(L) = e^{-2πσ'L}𝓕⁻(f_{σ'})(L)` almost everywhere.

## Hypotheses

Object data only: `X` a complex Hilbert space, `T` bounded and self-adjoint, `E` a holomorphic
branch of the square root of the Gamma quotient on the strip, `c` a channel vector, and the
frequency remainder `r` continuous, nonnegative and even-monotone with `Rint 0 = 0`.  These are the
literal properties of the Suzuki Gamma remainder.  No RH, no spectral premise, no `sorry`, `axiom`,
`opaque`, or `unsafe`.  Every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

What stays open is what the card itself declares open: the completed-domain cutoff/forcing
decomposition, the proof that its particular forcing has the corresponding upper-strip Hardy
regularity, the identification of the two-ended corona packet with the raw Evans packet, and RH or
a whole-program no-go.  The homogeneous Gamma-strip gate is closed.
