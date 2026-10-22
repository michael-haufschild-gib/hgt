# Producer explicit formula and Soundararajan's inequality on the Weil cone

- **ID:** MC-PRODUCER-SOUND
- **Stage:** 1-in-progress
- **Type:** THEOREM [P] → Lean
- **Source:** MC/Bohr loop cycles 243–244 (card `bohr-route-detection.md`, rows 22–23)

## Statement
Let `lam` be full-cone Weil-positive. Put `A_lam(s) = Σ_{n≥2} lam(n) n^{-s} = U(s) − Φ_lam(s)`, with `U = ½ψ(s/2) − ½log π + 1/s + 1/(s−1)` and `Φ_lam(s) = H(s−½) + iC`, where `H(z) = ∫ (1/(z−ir) − ir/(1+r²)) dμ_lam(r)` (corpus `herglotzFunction`).

1. **Producer explicit formula.** For `Re z > ½` and `x > 1`:
   `Σ_{n≤x} lam(n) n^{-z} log(x/n) = A_lam(z) log x + A_lam'(z) + x^{1−z}/(1−z)² − ∫ x^{½+ir−z}/(½+ir−z)² dμ_lam(r) + T_x(z)`.
   Here `T_x(z) = Σ_{k≥1} x^{−2k−z}/(2k+z)²` comes from the trivial points of `ψ`, plus an archimedean correction of size `O(x^{−z}/|z|²)`.
2. **Producer Soundararajan inequality.** For `T ≤ t ≤ 2T`, `2 ≤ x ≤ T²`, `λ ≥ λ₀ ≈ 0.567` (with `e^{−λ}/λ ≤ 1`) and `½ < σ ≤ σ₀ = ½ + λ/log x`:
   `log|F_lam(σ+it)| ≤ Re Σ_{n≤x} lam(n) log(x/n)/(n^{σ₀+it} log n · log x) + ((1+λ)/2)·log T/log x + O(1/log x)`.

## Proof (paper)
- **(1)** Perron's formula with weight `x^w/w²` gives `Σ_{n≤x} a(n)n^{-z}log(x/n) = (1/2πi)∫_{(c)} A_lam(z+w)x^w/w² dw` for `c > 1 − Re z`.
  - Split `A_lam = U − iC − H(·−½)`. For `U` and `iC` the contour moves to `Re w = −∞`, picking up residues at `w = 0`, at `w = 1−z`, and at the trivial points.
  - For `H` use Fubini. With the combined kernel, `∫|kernel(z+w−½, r)| dμ(r) ≪ log²(2+|w|)/Re z`, integrable against `|dw|/|w|²`.
  - Close each kernel's contour to the left. Residues: at `w = 0`, `−1/(z−½−ir)² + (1/(z−½−ir) − ir/(1+r²))log x`; at `w = ½+ir−z`, `x^{½+ir−z}/(½+ir−z)²`.
  - Integrating in `r` gives `−H'(z−½) + H(z−½)log x + ∫ x^{½+ir−z}/(½+ir−z)² dμ`. No continuation of `Φ_lam` past the line is used.
- **(2)** Soundararajan's argument (Moments of ζ, Prop. 1), with RH replaced by positivity.
  - Divide (1) by `log x` and integrate over `σ ∈ [σ₀, ∞)`.
  - The spectral term obeys `|∫_{σ₀}^∞∫ x^{½+ir−s}/(½+ir−s)² dμ dσ| ≤ x^{½−σ₀} ∫ dμ/|s₀−½−ir|² / log x = x^{½−σ₀} Re Φ_lam(s₀)/((σ₀−½) log x)`, by the corpus Poisson representation.
  - `−Re A_lam(s₀) = Re Φ_lam(s₀) − Re U(s₀)` and `Re U(s₀) = ½log(t/2π) + O(1)`. Choosing `λ ≥ λ₀` makes the `Re Φ` terms non-positive.
  - Going left from `σ₀` to `σ` costs `∫_σ^{σ₀} Re A_lam ≤ ∫ Re U = (σ₀−σ)(½log T + O(1))`, because `Re Φ_lam ≥ 0`.

## Uses
- **Step A without the sharp constant.** Via Soundararajan or Harper large deviations for short sums, `∫|F_lam(½+it)|² ≪ T(log T)^{1+o(1)}` for producers whose short sums have Λ-like moments.
- **Settled-phase kill of slowly decaying evaporation** (bohr card row 23). The mean-square input there is also available from `exists_zetaBlock_meanSquare_le` on `σ = ½ + R/log T` together with horizontal monotonicity.
- **Producer Littlewood bound:** `|F_lam(½+it)| ≤ exp(C log t/log log t)`.

## Novelty audit
- `research` (2026-10-03): the corpus has no Soundararajan inequality, either for ζ or for producers. HF uses only Soundararajan's resonator (L208/L209). The `log`-weighted explicit formula is in the corpus for `ξ'/ξ` only pointwise (`xi_explicitFormula_logDeriv`), not in Soundararajan's form.
- Literature: Soundararajan 2009 is for ζ under RH; Chandee 2009 covers GRH L-functions. The transfer to Herglotz producers is new in framework but classical in mechanism: BRIDGE.

## Log
- 2026-10-03 — created; paper proof complete for (1) and (2). Lean next: (1) is the main brick.
- 2026-10-03 — **(1) closed in Lean.** All four modules compile with standard axioms and are wired into `RHTower.lean`.
  - **Modules.**
    - `PerronLaplacePoleKernel`: pole integrals at orders one and two, and Perron formulas for general Dirichlet series at weights `(L−log n)⁺` and `((L−log n)⁺)²/2`.
    - `PerronDigammaSeriesKernel`: the Gauss series of `ψ`, done termwise.
    - `WeilHerglotzPerronIntegral`: the Fubini step for `H`.
    - `WeilProducerPerronExplicitFormula`: `tsum_lamC_mul_max_eq`.
  - **Fubini input.** A pointwise kernel comparison: `|1/(a+iτ−ir) − 1/(a−ir)| ≤ (4b/a)(P_b(r−τ) + P_b(r))` whenever `aτ ≤ 2b²`. Combined with `Re H(b+iτ) ≤ ½log(|b+iτ|+1) + K` for `b ≥ 4` (digamma asymptotic), this gives kernel mass `O((1+|w|)^{3/4})`. No local mass bound is needed.
  - **Next.** (S1) split `Q = e^{bL}/b² − 1/b² − L/b`. (S2) identify the `L`-coefficient with `A_lam(z)`. (S3) identify the `1/b²` part with `A_lam'(z)` (trigamma series plus `hasDerivAt_herglotzFunction`). (S4) integrate over `u ∈ [σ₀, ∞)` and bound the `μ` term via Poisson.
- 2026-10-03 — **(2) closed in Lean** (MUST-671).
  - **Modules.** `WeilProducerExplicitFormulaResidues` (residue form, and `A_lam' ` identified through the trigamma series) and `WeilProducerSoundararajanInequality` (`re_producerLogZeta_le`, plus the consistency lemma `producerLogZeta_eq_LSeries`).
  - **Normalisation.** `log F` is normalised at abscissa `2` and integrated horizontally, so no improper integrals are needed. The `μ`-term is absorbed through Poisson and `e^{−λ} ≤ λ`.
  - **Open.** The `ζ` specialization under RH (`weilPositiveFull_vonMangoldt_of_riemannHypothesis` together with the identification `producerLogZeta = log ζ`). Moment corollaries need prime-side statistics of `lam`.
- 2026-10-03 — **Littlewood corollary and ζ specialization closed in Lean** (MUST-672).
  - `WeilProducerLittlewoodBound`: `|lam(n)| ≤ κ log n` gives `log|F_lam| ≪ log t/log log t` up to the line.
  - `RiemannHypothesisLittlewoodBound`: under RH, `producerLogZeta(Λ) = log ζ` (identity theorem on the quadrants `{Re > ½, ±Im > 0}`, Euler logarithm at `σ = 2`). This gives Littlewood for `ζ` on `½ ≤ σ ≤ 2` (critical line by continuity) and Soundararajan for `ζ`.
