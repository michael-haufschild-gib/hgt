# TG — reflected Gaussian formation: Hermite–Biehler dominance above a height

- **ID:** TG-RGF-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** frontier map TG (pre-divisor Gaussian Euler source; faithful source-to-Hardy identification)
- **Statement:** For every x>0 there is T₀(x) with Re(Φₓ'/Φₓ)(s)>0 on {Re s>0, |Im s|≥T₀}. Hence
  σ↦|Φₓ(σ+it)| is strictly increasing on (0,∞), and Ξₓ(s)=Φₓ(s)+Φₓ(1−s) has no zero with
  0<Re s<1, Re s≠½, |Im s|≥T₀; its critical-line zeros there are simple.

## Goal
A source-built (Gaussian Euler log + continuum + Γ) function with the exact functional equation of ξ
that satisfies the TG sub-unit gate (index 0 on every right disc) above T₀(x). This isolates the TG gap
as the comparison ξ ↔ Ξₓ, not the construction of an RH-true source model.

## Paper proof
- logDeriv Φₓ = logDeriv h∞ − Jₓ + Mₓ on Re s>0 [L].
- |Jₓ(s)| ≤ Kₓ := Σ Λ(n)e^{−πxn²}, |Mₓ(s)| ≤ ∫₁^∞e^{−πxu²}du on Re s≥0 (|n^{−s}|≤1).
- logDeriv h∞(s) = 1/s − ½log π + ½ψ(s/2); Re(1/s)≥0; Re ψ(z) ≥ log|z| − 3/|z| for Re z>0, |z|≥2 [L].
- So Re logDeriv Φₓ ≥ ½log(|t|/2π) − 3/|t|·2 − Kₓ − M₀ > 0 for |t| large.
- d/dσ|Φₓ(σ+it)|² = 2|Φₓ|² Re(Φₓ'/Φₓ) > 0 ⇒ strict monotonicity.
- |Φₓ(1−s)| = |Φₓ(1−σ+it)| (real structure) < |Φₓ(σ+it)| for ½<σ<1 ⇒ Ξₓ(s)≠0; symmetric for σ<½.
- On the line Ξₓ = 2 Re Φₓ; Ξₓ'(½+it) = 2i Im Φₓ'(½+it) and at a zero Φₓ = ib, Im Φₓ' = b Re(Φₓ'/Φₓ) ≠ 0.

## Log
- 2026-10-09 — opened; paper proof complete; Lean leaf `GaussianFormationReflectedHermiteBiehler` started.
- 2026-10-09 — formalized: `RHTower/GaussianFormationReflectedHermiteBiehler.lean` (478 lines), wired in
  `RHTower.lean`. `lake build --old` of the leaf exit 0, no warnings; axioms of all six headline theorems =
  [propext, Classical.choice, Quot.sound]. Headline: `re_logDeriv_gaussianFormation_pos`,
  `strictMonoOn_norm_gaussianFormation_horizontal`, `gaussianReflectedFormation_ne_zero`,
  `deriv_gaussianReflectedFormation_ne_zero_of_line`, `gaussianReflectedFormation_relativeIndex_eq_zero`,
  `exists_gaussianReflectedDiscDatum`.

## Reading
- Gonek-type mechanism (archimedean ½log|t| beats every bounded Gaussian prime datum); not new to the
  literature, new to the corpus. It is the first source-built function with ξ's functional equation proved to
  pass the TG gate (index 0 on right discs) in a full half-strip above a height.
- Window law: T₀(x) = 2π·exp(2+2Kₓ+2M⁰ₓ), Kₓ ≈ x^{−1/2}/2, so at height T the model is RH-true only for
  Gaussian length X = x^{−1/2} ≲ log T. Rouché-closeness of Φₓ to ξ needs (under RH) X ≥ (log T)^{1/δ} at
  distance δ from the line. The two windows do not meet near the line: this is the TG gap, quantified.
- Consistent with CANNOT-461 (holomorphic source readers: budget idle); Ξₓ is not a zero-free approximant of ξ.
- 2026-10-09 — all heights. Generic module `RHTower/HorizontalLogDerivReflectionDominance.lean`
  (namespace `ReflectionDominance`: any conj-real F, zero-free on Re s>0, Re F'/F>0 above T₀ ⇒ monotone
  modulus, reflection RH, simple line zeros, TG index 0). Paley–Wiener tilt: Re h∞'/h∞ > −2 on all of
  Re s>0 (`neg_two_lt_re_logDeriv_gaussianArchimedeanHalfFactor`, the factor s cancels ψ's pole), so for
  λ ≥ λₓ = 2+Kₓ+M⁰ₓ the tilted reflection e^{λ(s−½)}Φₓ(s)+e^{λ(½−s)}Φₓ(1−s) is RH-true at every height
  with simple line zeros (`tiltedGaussianReflectedFormation_ne_zero`, `..._relativeIndex_eq_zero`).
  Cost law: the tilt adds zero density λ/π ≥ λₓ/π ≈ x^{−1/2}/(2π). Leaf builds exit 0, axioms standard.
