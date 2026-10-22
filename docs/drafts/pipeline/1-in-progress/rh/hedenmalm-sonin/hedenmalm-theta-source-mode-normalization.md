# Theta source-mode normalization and hypothesis-free eigenvector

- **ID:** HED-THETA-SOURCE-MODE-NORMALIZATION
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** corpus conjunction: `HedenmalmPrimeTranslationAnomaly` +
  `HedenmalmThetaRootModeDecay`
- **Statement:** At every theta-source divisor `z` with `|Im z| < 1`, the explicit mode
  `f_z = -z u_z` is integrable, has total mass exactly `M`, and the source inverse satisfies
  `B f_z = -z⁻¹ f_z` without the previously assumed integrability or mass-normalization data.

## Goal

Remove the two unproved analytic inputs `Integrable (sourceModeF thetaSource z)` and
`∫ sourceModeF thetaSource z = thetaSource.mass` from the corpus's divisor-to-eigenvector map.
This is non-circular: it uses only explicit theta-source decay, the first-order source ODE, and the
fundamental theorem of calculus. It does not assume a zero-location statement or any RH-equivalent
positivity certificate.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus and literature audit

- `[CORPUS]` `norm_sourceModeU_le` gives
  `‖u_z(x)‖ ≤ C_z exp(-|x|)` at every theta-source zero in the strip.
- `[CORPUS]` `hasDerivAt_sourceModeU`, `sourceModeF_eq_neg_I_mul_D`, and
  `sourceInverse_sourceModeF_eq_smul` contain the differential and operator identities, but the
  last theorem still takes mode integrability and total mass as hypotheses.
- `[CORPUS]` no theorem named by searches for `integrable_sourceModeF`,
  `integral_sourceModeF`, or `sourceModeF ... mass` discharges those hypotheses.
- `[LITERATURE]` Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494,
  Theorem 3.3.3 and Remark 3.3.4, identifies complex zeros with two-ended rapidly decaying
  eigenfunctions. The paper's displayed spectral problem is second order; this card records the
  distinct first-order source-inverse normalization needed by the Lean corpus.
- `[INFERENCE]` literature search found no explicit statement of the fixed source mass identity
  below. External novelty remains unclaimed pending a broader expert audit.

## Conjecture/failure/proof chain

1. **C24a (failed):** endpoint vanishing forces zero root-mode mean.
   The root ODE is `h' = g - 1`; two zero endpoints force mean `1`, not `0`.
2. **C24b (proved):** the nonzero mean is not an extra hypothesis. For the theta source it follows
   from exponential localization and the source ODE, equivalently from a fixed total source mass.
3. **Next conjecture after formalization:** transport this canonical normalization through the
   quantile unitary and reduce the universal rank-two boundary defect on every actual divisor mode
   to its single centered moment.

## Complete paper proof

Let `u = sourceModeU thetaSource z`, `f = sourceModeF thetaSource z = -z u`, and
`D = sourceModeD thetaSource z`. Assume `|Im z| < 1` and `XiC thetaSource z = 0`.

1. `[PROVED HERE]` Existing decay gives
   `‖u(x)‖ ≤ C_z exp(-|x|)`, where `C_z ≥ 0`. Since `exp(-|x|)` is integrable on `ℝ` and `u` is
   continuous, domination proves `u ∈ L¹(ℝ)`. Therefore `f = -z u ∈ L¹(ℝ)`.
2. `[PROVED HERE]` The pointwise algebraic identity
   `D = i(f-k)` and integrability of `f` and `k` prove `D ∈ L¹(ℝ)`.
3. `[PROVED HERE]` The same exponential majorant tends to zero at both infinities, hence
   `u(-∞)=u(+∞)=0`.
4. `[PROVED HERE]` The source ODE gives `u'=D` everywhere. The whole-line fundamental theorem of
   calculus yields
   `∫_ℝ D = u(+∞)-u(-∞)=0`.
5. `[PROVED HERE]` From `f = -iD+k`, integrate to obtain
   `∫_ℝ f = -i∫_ℝD + ∫_ℝk = M`.
6. `[PROVED HERE]` Substitute mode integrability, left endpoint limit, and the mass identity into
   `sourceInverse_sourceModeF_eq_smul`. For `z ≠ 0`,
   `B f_z = -z⁻¹ f_z` pointwise. For a theta-source zero, `z ≠ 0` also follows independently from
   positivity of `XiC thetaSource 0 = M`; this last convenience lemma may be formalized separately
   if not already exported.

Every dependency in steps 1–5 is already unconditional in the corpus or mathlib. Step 6's displayed
eigenvalue requires only the algebraically necessary `z ≠ 0`; the normalization theorem itself does
not.

## Door passport

- **Source purity:** explicit theta source, its completed transform, and proved exponential bound.
- **No RH import:** no zero-location, prime positivity, Weil positivity, or equivalent endpoint.
- **Output:** eliminates assumed analytic data from the divisor-to-eigenvector chain.
- **Open core after output:** prove fixed-mean quantile transport and analyze the remaining centered
  moment; no claim that normalization alone implies RH.

## Log

- 2026-08-07 — C24a falsified; fixed nonzero mean recognized.
- 2026-08-07 — C24b dependency-closed paper proof completed; moved directly to Lean attack.
