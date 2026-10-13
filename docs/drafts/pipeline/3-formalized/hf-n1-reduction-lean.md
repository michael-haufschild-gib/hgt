# HF reduction in Lean: RH ⟸ PBAP + (N1)

- **ID:** hf-n1-reduction-lean
- **Stage:** 3-formalized
- **Type:** THEOREM (formalization of a paper reduction)
- **Source:** route-candidates loop row 715 (REDUCTION [paper]); MUST-718 (critical-zero-carried rigidity [L]); `exists_weilPositiveFull_iff_primeBlindPositive` (PBAP ⟺ Weil cone nonempty [L]).
- **Statement.** Let `F : ℝ → ℝ` be `C²` with `|F|, |F'| ≤ C e^{−|x|/2}(1+x²)^{−1}`, with prime-blind autocorrelation `(F⋆F̃)(log n) = 0` (`n ≥ 2`), with `F̂` vanishing at every zero of `ξ` (spectral coordinates, off-line zeros included), and with `F̂(r) ≠ 0` at every real `r` where `ζ(½+ir) ≠ 0`. Then every full-cone Weil-positive `λ` equals `Λ`. With PBAP (the cone is nonempty) RH follows.

## Proof plan
1. Truncate: `F_L = Fχ_L` is `C²` with compact support, so the corpus identity gives `∫|F̂_L|² dμ_λ = Re W_ζ(F_L,F_L) − T_{λ−Λ}(F_L⋆F̃_L)`.
2. Zero side: `(1+|Re z|)|(F_L − F)^(z)| ≤ ∫|F_L−F|e^{|u|/2} + ∫|(F_L−F)'|e^{|u|/2} → 0` uniformly on `|Im z| ≤ ½` (integration by parts under half-exponential decay). With `F̂ = 0` at the zeros, `norm_W_le_of_zero_bound` gives `W_ζ(F_L,F_L) → 0`.
3. Prime side: summation by parts with `|Σ_{n≤N}(λ−Λ)| = O(N)` (`exists_sharp_source_sum_le` + Chebyshev). Use uniform bounds `|k_L|, |k_L'| ≤ C e^{−|y|/2}(1+y²)^{−1}` and blindness `k(±log n) = 0`; dominated convergence gives `T → 0`.
4. Fatou: `∫|F̂|² dμ_λ = 0`, so `μ_λ` is carried by the critical zeros; MUST-718 gives `λ = Λ`.

## Log
- 2026-10-12 — card opened (Opus loop row 1035). Value: makes the HF route's reduction an exact Lean theorem; its two premises (PBAP, N1) become named Props.
- 2026-10-12 — **[L] for decay rate > 1** (loop row 1035): `formal/GaloisForLFunctions/RHTower/WeilConeXiDivisibleBlindTest.lean`. Class `ExpDecayTest`: `|F|, |F'| ≤ C e^{−(1+δ)|x|}`. Prime side by Tannery with the box bound `|λ(n) − Λ(n)| ≤ √n(2 log n + C₀)` (no summation by parts needed at this rate). Main theorems: `eq_vonMangoldt_of_xiDivisibleBlindTest`, `riemannHypothesis_of_primeBlindPositive_of_xiDivisibleBlindTest`, `riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindTest`. Standard axioms. Models: `F̂ = Ξ g` with `g = cosh(πz/4)(a² + z²)^{−k}`, `a > 1`, has the decay shape (prime-blindness is the open (N1) condition, not a decay issue).
- Next: extend to rate `> ½` (the card's original class; the explicit formula needs analyticity on `|Im z| ≤ ½` only). Plan: discrete Abel summation `Σ c(n)φ_L(n) = Σ S(n)(φ_L(n) − φ_L(n+1))`, `|S(N)| ≤ A(N+1)` from `exists_sharp_source_sum_le` and Chebyshev, `|φ_L(n) − φ_L(n+1)| ≤ C n^{−2−δ/2}` uniformly in `L` by the mean value theorem inside the autocorrelation; Tannery; the limit is `0` termwise by blindness.
- 2026-10-12 — **[L] for decay rate > ½, MUST-1332** (loop row 1036). `ExpDecayTest` is now `|F|, |F'| ≤ C e^{−(1/2+δ)|x|}`: the card's class, with the weight `(1+x²)^{−1}` replaced by any exponential margin `δ > 0`. Prime side by summation by parts against the partial-sum bound `|Σ_{n≤N}(λ − Λ)| ≤ A(N+1)` (`exists_abs_primeWeightPartialSum_sub_vonMangoldt_le`), with uniform profile increments (`abs_primeLogProfile_truncTest_sub_le`). Card closed at stage 3. The open inputs are exactly the two Props PBAP (`WeilOneSided.PrimeBlindPositive`) and the existence of an `F` meeting the hypotheses ((N1)).
- 2026-10-12 — Factorized (N1) Prop `XiDivisibleBlindTest` (`F̂ = Ξg` on the critical strip, `g ≠ 0` on ℝ) with `riemannHypothesis_iff_primeBlindPositive_of_exists_xiDivisibleBlindTest` (MUST-1332 addendum). NULL law: `archPoleEnergy_eq_zero_of_xiDivisibleBlindTest` (loop row 1038). An (N1) test makes the zeta-free pole and archimedean energy vanish, so PBAP is attained on it.
- 2026-10-12 — Follow-on modules (loop rows 1039–1046):
  - `RHTower/WeilConeNullEnergyBlindTestCarrier` (MUST-1336/1337): null carrier law, zeta-free spectral identity, PBAP extends to the decay class, zeta-free localization of the zeros under RH.
  - `RHTower/WeilPrimeBlindZeroSideIdentity` (MUST-1338/1339): explicit formula on the decay class with the Abel prime side; PBAP ⟹ zero side ≥ 0 on prime-blind tests; detection receiver.
  - `RHTower/WeilDecayClassRHCriterion` (MUST-1341): real tests suffice; RH ⟺ decay-class Weil positivity.
