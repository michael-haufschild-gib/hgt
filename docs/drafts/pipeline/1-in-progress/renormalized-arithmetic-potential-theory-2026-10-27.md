# Renormalized arithmetic potential theory of the characteristic circle (RAPT)

- **ID:** rapt
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2710/obstacles-summary.md §4 (Q2, B3.25, B3.26, W11, W12; Q3 gauge face)
- **Statement:** Regulators, counterterms, anomalies and couplings of the places of the explicit formula; programme folder `formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/` (README there).

## Goal
Answer Q2 of the report (coupled renormalization) and its gauge face with theorems.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proofs of RP1–RP21 (all carried out directly in Lean)
- [x] 2 → 3  Lean: `renormalized_arithmetic_potential_theory_laws` and the module pillars, all
      axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), wired into
      `RenormalizedArithmeticPotentialTheory.lean`
- [ ] open topics (README §9): the overlap regime beyond the spacing; finite parts on
      residue-class profiles; non-abelian Chebotarev gauges; passage to all primes

## Results (Lean)
- RP1 coupled survival law; RP2 the archimedean place pays the arithmetic point.
- RP3 covariance ⇒ scalar, `κ_cov(N) = log N + O(1)`; RP4 `κ_tor(N) ≥ (3/2) log N − C`.
- RP5 horizon polarity; RP6 unbounded rank on `p`-adic classes; RP7 tensor law
  `Σ_j δ_j^{−1} ℓ_j²`, `δ_j = φ(p^{J+1−j})/p^{J+1}`; RP9 no anomaly under `[p]`.
- RP10 finite part `−2γ`; RP12 on the classes the finite part is the tower form of `p` with
  `γ_p = γ + log p/(p − 1)`; RP13 matched stability law at widths `δ_N N^{−e^{1/2}}`.
- RP8 spectral ends `±log N`, Liouville flip; RP11 matching law for sign gauges, finite flips
  invisible; RP14 Gårding ⇔ finite-rank survival (report milestone W18(xi)).
- RP15 `κ_tor(N) ≤ 2 log N + C`: torsion window `[3/2, 2]`, anomaly cost in `[½, 1]·log N`.
- RP16 tower finite part ≥ 0 on the classes of `p` iff `√p log p ≤ γ(p − 1)`; deficit `2d_p`
  sharp; fails at `p = 2`, holds for `p ≥ 2^16`.
- RP17 Lévy gain with constant `1 − O(1/N)`; matched width `c δ_N/N`.
- RP18 Markov form ≥ 0 on atomic tests at width `δ_N/(C log N)`, archimedean interaction of the
  atoms included (superseded at the spacing by SSHA `markovEnergy_atomicTest_nonneg_spacing`,
  width `c₀δ_N`).
- RP19 Mertens for characters, `A_χ = O(1)`; RP20 real character gauges mod a prime have matching
  coefficient `0`; RP21 Mertens in residue classes.
- RP24 unit residue classes mod `q`: counterterm `(q/φ(q)) ℓ²`, rank one for every `q`;
  RP25 class functions seen only through their mean, every character `χ ≠ 1` invisible;
  RP26 transfer law (remainder = harmonic convolution of the Mertens error), soft law under
  `A_ε(y)/log y → κ`, diagonal criterion.
- RP27 the horizon laws (polarity, `−2γ`, tensor law) for every profile, error by the horizon
  variation; bounded-variation (smooth) signed and class profiles up to `o(mass)` (W23).
- RP28 `d_p = u/sinh u − γ` strictly decreasing; `d_p > 0` iff `p ≤ 43`; tower finite part
  nonnegative iff `p ≥ 47` (W25 sign table).
- RP30 finite part `= 2 lim (A_ε − κ log)` for every gauge with convergent Mertens error (RP10 is
  `α = −γ`); RP31 `A_χ(y) → −L′/L(1, χ)` from the corpus PNT for characters; finite part of
  real character gauges.
- RP33 Liouville finite part `2(γ + τ)`; on `ℓ = 0`, `P_N(λx) − P_N(x) = 2(2γ + τ)|x|² + o(mass)`.
- RP34 class Mertens constants `c_r` with `φ(q) c_r = −γ − Q_q + Re Σ_{χ≠1} χ(r⁻¹)(−L′/L(1, χ))`.

## RP35 route (residue finite part)
- Target: for units `a, b`, `1 ≤ M ≤ M'`: `G_ab(M, M') = (q/φ) S_a(M) S_b(M') + c_{a⁻¹b} S_a(M) +
  c_{b⁻¹a} S_b(M) + o(H_M) + O(1)`; finite-part matrix `F_ab = c_{a⁻¹b} + c_{b⁻¹a}` with character
  eigenvalues `2 Re β_χ`, `β_χ = −L′/L(1, χ)` (`χ ≠ 1`), `β_1 = −γ − Q_q`.
- Inputs: class harmonic constant with rate, `|q S_a(M) − log M − q d_a| ≤ K/M` (shift identity
  gives Cauchy rate for `S_{a+1} − S_a`, plus `H_M − log M − γ ∈ [0, 1/M]`); `L_a(M) = (log M)²/(2q)
  + d_a log M + O(1)` (telescoping, `Σ 1/M²`); floor error `Σ_{m ≤ M} (log(M'/m) − log⌊M'/m⌋)/m ≤ 2`;
  class-restricted convergent convolution of `A(·; r) − log/φ − c_r → 0` (RP30 lemma on `|D|`).
- Algebra: `L_a + L_b − S_a(log M + q d_b) = O(1)` closes the log-part.

## No-go closure
- **Killing theorem:** condition (i) of the central conjecture (bounded counterterm rank on Hecke
  orbits) fails under the Abel radius (`coupled_torsion_survival`) and at the horizon
  (`horizonCounterterm_rank_unbounded`).
- **Positive survivor:** the tensor law (RP7) with Hecke-covariant finite part (RP9) and computed
  prime finite part (RP10); Lean: `abs_atomicWeilForm_classProfile_sub_le`,
  `finitePart_heckeShift`, `exists_abs_atomicWeilForm_stepProfile_finitePart_le`.
- **New insight:** counterterm rank and anomaly belong to the regulator; at the horizon the degree
  of `[p]` scales orbit densities and cancels.

## Log
- 2026-10-27 — created; README first draft; RP1–RP21 formalized; laws module.
