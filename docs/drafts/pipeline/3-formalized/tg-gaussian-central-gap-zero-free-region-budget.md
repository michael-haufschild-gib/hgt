# TG — Unconditional central Gaussian budgets from zero-free regions (producer frontier)

- **ID:** TG-UNC-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Statement:** G(u) = P_½(e^{-u}) − C_½(e^{-u}).
  (a) Transfer: zeros with |γ| ≥ t₀ satisfy β ≤ 1 − η(|γ|), η antitone ⇒ ∃C,δ>0 ∀u≥0 ∀T≥t₀:
      |G(u)| ≤ C(1 + e^{u/4}(e^{-uη(T)/2} + e^{-πT/8} + e^{-uδ/2})).
  (b) η antitone, η → 0 ⇒ |G(u)| ≤ C exp(u/4 − uη(u)/2) for large u.
  (c) dLVP (corpus explicit region 1/(58 log|γ|), |γ| ≥ 4): |G(u)| ≤ C exp(u/4 − u/(116 log u)).
  (d) Vinogradov–Korobov (corpus): |G(u)| ≤ C exp(u/4 − u(log u)^{-2/3}(log log u)^{-5/3}/(2·10⁸)).

## Proof
Unconditional zero expansion G = MB − Σ_ρ ½Γ((ρ−½)/2)e^{(ρ−½)u/2} − Σ_ρ R_ρ (cycle 19). Amplitudes:
‖amp‖ ≤ W|ρ−½|^{-2} (germ at y=1) and, off |γ|<2, ‖amp‖e^{π|γ|/8} ≤ D|ρ−½|^{-2} (sharp strip bound
|Γ(x+it)| ≤ C|t|^N e^{-π|t|/2}, HTGeometry/GammaStripSharpDecay, + t^k ≤ (8/π)^k k! e^{πt/8}). Low zeros:
compactness gives β ≤ 1−δ. Split zeros into |γ|<t₀, t₀≤|γ|≤T, |γ|>T; sum with Σ|ρ−½|^{-2} < ∞.

## Lean
`RHTower/GaussianCentralGapZeroFreeRegionBudget.lean` (489 lines), wired after GaussianBudgetSignedMixtureLaw.
`exists_norm_zeroBohrAmplitude_le_inv_sq`, `exists_norm_zeroBohrAmplitude_mul_exp_le`,
`exists_xi_zero_re_le_of_abs_im_le`, `norm_zeroBohrTerm_le`, `norm_gaussianCentralGap_le_of_zeroFree`,
`exists_norm_gaussianCentralGap_le_exp_of_zeroFree`, `exists_norm_gaussianCentralGap_le_dlvp`,
`exists_xiZero_re_le_vinogradovKorobov`, `exists_norm_gaussianCentralGap_le_vinogradovKorobov`.
Axioms [propext, Classical.choice, Quot.sound].

## Reading
This is the current unconditional state of the TG producer: the central budget is known with exponent
1/4 and a sub-exponential VK saving; RH needs exponent 0. Because of Γ-damping the budget at scale u
is decided by zeros of height ≲ u (cutoff T = u), so the dLVP saving becomes u/log u (vs √(log x) for
sharp ψ). Any saving in the exponent itself is a zero-free strip Re s > 1 − ε (open since 1896).
Producer milestone ladder: exponent 1/4 → 1/4 − ε (zero-free strip) → 0 (RH).
