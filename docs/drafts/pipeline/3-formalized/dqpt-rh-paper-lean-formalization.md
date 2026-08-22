# DQPT–RH paper: full Lean formalization of its mathematical content

- **ID:** `dqpt-rh-paper-lean-formalization`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ShiJie Wei, Yue Zhai, Quanfeng Lu, Wentao Yang, Pan Gao, Chao Wei, Junda Song,
  Franco Nori, Tao Xin, GuiLu Long, *The Riemann Hypothesis Emerges in Dynamical Quantum Phase
  Transitions*, arXiv:2511.11199v1 (14 Nov 2025); published as Nature Communications,
  DOI `10.1038/s41467-026-74935-8` (local: `docs/s41467-026-74935-8_reference.pdf`,
  `docs/s41467-026-74935-8_supplementary.pdf`).
- **Statement:** Every determinate mathematical proposition of the paper (both the arXiv and the
  published supplementary) is an unconditional, hypothesis-free Lean 4 theorem in this corpus.

## Relation to the closed RH-route card

`docs/drafts/pipeline/5-failed/nature-dqpt-alternating-tail-rh-route.md` audits the same paper and
closes it **as an RH proof route**. That card explicitly records "no Lean theorem". This card is a
different task: formalize the paper's mathematics. Nothing here re-attempts the dead route
(DQPT-occurrence ⇒ RH); the RH-facing claim is not among the paper's theorems.

## Target inventory (paper → Lean)

Numbering: `A` = arXiv supplementary note, `P` = published supplementary note.

### Group 1 — analytic number theory (fully determinate)

| Paper item | Content | Lean module |
|---|---|---|
| A1(1.1)–(1.8) / P1(1)–(7) | `S_N(s)`, tail `R_N(s)`, `η = S_N + R_N` | `RHTower/DQPTAltPartialSum` |
| A1(1.9)–(1.17) / P1(12)–(13) | `¼(N+1)^{-β} ≤ |R_N(s)| ≤ ¾(N+1)^{-β}` for large `N` | `RHTower/DQPTTailNormal` |
| A1(1.18)–(1.21) / P1(14)–(17) | `−ln|S_N|/log₂N → β ln2` at η-zeros, `→ 0` otherwise | `RHTower/DQPTPartialSumRate` |
| A2 / P2 | `Z_N(β)` two-sided integral bounds and `−ln Z_N/log₂N → (β−1)ln2 / 0` | `RHTower/DQPTPartitionRate` |
| Methods (19) / P3 | free-energy density `F₁` trichotomy; entropy density `𝒮 = −ln2 / 0` | `RHTower/DQPTFreeEnergy` |
| A6 / P8 | `|η(s)| ≤ |s|/β`, `|η'(s)| ≤ |s|/β² + 1/β`, `|2^{1−β}−1| ≥ ln2·|1−β|`, `ζ'` bound | `RHTower/DQPTEtaDerivBound` |
| A7 / P7 | `|sin(πs/2)|² = sinh²(πt/2)+sin²(πβ/2)`; `|χ(β+it)| = Θ(|t|^{1/2−β})` | `RHTower/DQPTChiOrder` |
| Main text (2),(3),(5); Methods (22) | `L(β,t)` and `S(t)` closed forms and their limits | `RHTower/DQPTObservables` |
| 5-failed card (1),(3) | reflected tail-slope law and spike contrast | `RHTower/DQPTReflectedSlope` |

### Group 2 — determinate cores of the algorithm notes

| Paper item | Content | Lean module |
|---|---|---|
| A4(4.5)–(4.6) / P5 | amplitude split `c_{w0}² + c_{w1}² = c_w²` | `RHTower/DQPTAmplitudeSplit` |
| A4(4.10)–(4.12) | `θ = arctan√(S₁/S₀) = arcsin√(S₁/(S₀+S₁))` well-posedness | `RHTower/DQPTAmplitudeSplit` |
| A4(4.13) | state-distance bound `≤ maxᵂ |θ̃−θ|` | `RHTower/DQPTAmplitudeSplit` |
| A4(4.76) | `‖(ψ₀+γ̃ψ₁)/√(1+γ̃²) − (ψ₀+γψ₁)/√(1+γ²)‖ ≤ √2|γ−γ̃|` | `RHTower/DQPTAmplitudeSplit` |
| A4(4.84) | post-selection success probability `> 1/2` | `RHTower/DQPTAmplitudeSplit` |
| A4(4.86)–(4.91) | normalized-projection perturbation bound and success probability | `RHTower/DQPTAmplitudeSplit` |
| A3(3.6)–(3.12) | dyadic partition, `d ∈ [−¼,½)`, `log₂ n = (ν+1) + log₂(1+d)` | `RHTower/DQPTOracleNumerics` |
| A3(3.10)–(3.11) | `|∑_{j>l} (−1)^{j+1}dʲ/j| ≤ 2^{−l}`; rounding geometric bound | `RHTower/DQPTOracleNumerics` |
| A4(4.19)–(4.20) | `sin²θ` power series and its truncation error | `RHTower/DQPTOracleNumerics` |
| A4(4.50) | `|1 − 2ˣ| ≤ |x|` for `x ≤ 1` | `RHTower/DQPTOracleNumerics` |
| A4(4.54),(4.57) | `2ˣ` series and truncation bound on `[−½,½]` | `RHTower/DQPTOracleNumerics` |
| A4(4.33) / P5 | `2(2l)!/(2π)^{2l}·(1−2^{−2l})^{-1} < |B_{2l}| < 2(2l)!/(2π)^{2l}·(1−2^{1−2l})^{-1}` | `RHTower/DQPTBernoulliBound` |
| A4 Cor 4.6 / P5 Cor 5.6 | `∑_{p≤q} C(q+1,p) B_p = 0` | `RHTower/DQPTBernoulliBound` |
| A4 Prop 4.5 / P5 Prop 5.5 | Euler–Maclaurin approximation of `S(a,b,β)` with remainder `< ϵ/2` | `RHTower/DQPTEulerMaclaurinPartialSum` |
| A5(5.8) / P6 | `‖∑ αₙ(e^{−iãₙ} − e^{−iaₙ})|n⟩‖ ≤ 2 sin(ξ/2) < ξ` | `RHTower/DQPTPhaseError` |
| Methods IV C (20)–(22) | probe reduced density matrix and `Re S(t) = G(½,t)` | `RHTower/DQPTObservables` |

### Group 3 — out of scope, with reason

The gate-count and ancilla-count statements (A3 Lemma 3.1/3.2, A4 Thm 4.2/4.4/4.11 and
Props 4.8/4.9, A5 Thm 5.1, Methods IV E and its `R_c`, `R_s`, `R_o` bounds; published
Cor 4.2/Prop 5.7/Prop 5.8/Lemma 5.9) are resource estimates in an unspecified gate-cost model.
Their proofs invoke costs of primitives the paper does not define or prove (schoolbook reversible
multiplication [46], Grover recursive amplitude splitting [43], LCU, amplitude amplification), and
the conclusions are stated as `Poly(...)` without naming the polynomial or the uniformity. They
have no determinate formal content to certify. Every *mathematical* step inside those proofs is
listed in Group 2 and is formalized.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper (paper supplies the proofs; corrections recorded below)
- [x] 2 → 3  formalized: 19 Lean modules, all `lake build` green, all 62 capstones
  `#print axioms`-clean (`propext, Classical.choice, Quot.sound` only)
- [ ] 3 → 4  n/a (formalization of an external paper, not a new preprint)

## Corrections to the source found while formalizing

1. **A1 / P1 Case 2 dichotomy is on `η`, not on `ζ`.** The rate is `β ln2` exactly when
   `η(s) = (1−2^{1−s})ζ(s) = 0`. On the line `Re s = 1` the extra zeros `s = 1 + 2πik/ln2` of the
   eta multiplier also give rate `β ln2` while `ζ(s) ≠ 0`. In the open strip `0 < β < 1` the two
   formulations agree, so the paper's use is sound there.
2. **A6(6.8) has a typo.** With `|η(s)| ≤ |s|/β` and `|η'(s)| ≤ |s|/β² + 1/β`, the correct
   consequence is
   `|ζ'(s)| ≤ (|s|/β² + 1/β)/|2^{1−β}−1| + 2^{1−β} ln2 (|s|/β)/|2^{1−β}−1|²`.
   The displayed first denominator `|2^{1−β}−1|β` should be `|2^{1−β}−1|β²`.
3. **A3(3.11) rounding bound.** `η/2·(1 + ½ + ¼ + ⋯) = η`, not `≤ η/2`; the stated total error
   `< η` holds with the truncation half replaced by `η/2` only if the coefficient rounding is
   charged `η/2` in total (i.e. per-coefficient `η/4`). Formalized with the corrected constant.
4. **A1 route replaced.** The Gamma/`tanh` splitting of `J` (A1(1.5)–(1.16)) is replaced by an
   equivalent, sharper and fully elementary second-difference argument: pairing the tail gives
   `A_N := ∑_j ((N+1+2j)^{-s} − (N+2+2j)^{-s})` with `R_N = (−1)^N A_N`, and the half-sum identity
   `A_N = ½(N+1)^{-s} + ½∑_j (g_{2j} − 2g_{2j+1} + g_{2j+2})` yields
   `|A_N − ½(N+1)^{-s}| ≤ |s||s+1|(N+1)^{−β−1}`, hence A1(1.17) for `N+1 ≥ 4|s||s+1|`.
   This avoids the paper's non-effective constant `A = A(s)` and gives the explicit threshold.

## Log
- 2026-08-22 — card created; paper read (arXiv v1 + published supplementary); target inventory
  frozen; corpus audit found `RHTower.ZetaRealStrip.etaPair_eq`,
  `RHTower.GammaVerticalRatioAsymptotic.gamma_vertical_ratio_norm_rpow_tendsto`,
  `HTGeometry.GammaVerticalModulus`, `RHTower.ZetaCarrier.zetaChi` as the load-bearing reusable
  assets.

## Lean progress ledger (2026-08-22)

All modules live in `formal/GaloisForLFunctions/RHTower/` and are wired into
`GaloisForLFunctions/RHTower.lean`.  Each was checked with `lake env lean <file>` (clean, no
warnings) and its olean built with `lake build <module>` where a later module imports it.

| Module | Paper items | Status |
|---|---|---|
| `DQPTAltPartialSum` | A1 (1.1)–(1.8) | clean |
| `DQPTTailNormal` | A1 (1.9)–(1.17) | clean |
| `DQPTPartialSumRate` | A1 (1.18)–(1.21) | clean |
| `DQPTPartitionRate` | A2 (2.1)–(2.7) | clean |
| `DQPTFreeEnergy` | Methods (19); P3 (25)–(28) | clean |
| `DQPTEtaBound` | A6 (6.3) | clean |
| `DQPTEtaDeriv` | A6 (6.4)–(6.5) | clean |
| `DQPTZetaDerivBound` | A6 (6.6)–(6.8) | clean |
| `DQPTChiOrder` | A7 (7.1)–(7.14) | clean |
| `DQPTObservables` | main text (2),(3),(4),(5); Methods (22) | clean |
| `DQPTReflectedSlope` | 5-failed card (1),(2),(3) | clean |
| `DQPTOracleNumerics` | A3 (3.6)–(3.12); A4 (4.22),(4.50),(4.54),(4.57),(4.64) | clean |
| `DQPTAngleNumerics` | A4 (4.18),(4.19),(4.20) | clean |
| `DQPTBernoulliBound` | A4 Cor 4.6, (4.33),(4.39) | clean |
| `DQPTStateError` | A4 (4.13),(4.76),(4.86)–(4.91); A5 (5.8) | clean |
| `DQPTAmplitudeSplit` | A4 (4.5),(4.6),(4.10)–(4.12),(4.84) | clean |

| `DQPTEulerMaclaurin` | **new mathlib gap**: Euler–Maclaurin to arbitrary order | clean |
| `DQPTEulerMaclaurinPartialSum` | A4 Prop 4.5 / P5 Prop 5.5, (4.28),(4.31),(4.34) | clean |
| `DQPTProbeDensityMatrix` | Methods (20)–(21) | clean |

All 19 modules are wired into `GaloisForLFunctions/RHTower.lean`.
`scripts/formal_tools.py lint` reports no `sorry`/`admit`/`axiom`/`opaque`/`unsafe` in them and
no unreachable DQPT module (the 16 remaining lint errors are pre-existing unwired modules owned by
other agents, untouched by this card).

## New mathlib gap closed

`RHTower/DQPTEulerMaclaurin.lean` proves **Euler–Maclaurin summation to arbitrary order `2m+2`**
with the Bernoulli-polynomial cell remainder, for any *derivative tower* `F : ℕ → ℝ → ℝ` on the
interval (so no global smoothness hypothesis is needed).  Neither mathlib nor this corpus had it:
`HTGeometry.EulerMaclaurinSecondOrder` only covers order two.  The module also proves
`|B_{2k}(x)| ≤ |B_{2k}|` on `[0,1]` from mathlib's Fourier expansion of the periodised Bernoulli
polynomials — the sharp input for every Euler–Maclaurin remainder bound.

## Out of scope, restated

The gate- and ancilla-count conclusions (A3 Lemma 3.1/3.2, A4 Thm 4.2/4.4/4.11, Prop 4.8/4.9,
A5 Thm 5.1, Methods IV E; published Cor 4.2, Prop 5.7/5.8, Lemma 5.9) quantify over an
unspecified circuit-cost model, cite unproved primitive costs, and state their conclusions as
`Poly(...)` without naming the polynomial or its uniformity.  They have no determinate formal
content.  Every mathematical step used inside their proofs is formalized above.

## Log
- 2026-08-22 — all determinate mathematics of the paper formalized in 19 Lean modules
  (`RHTower/DQPT*.lean`), wired into the RHTower umbrella, every capstone `#print axioms`-clean.
  Moved 1-in-progress → 3-formalized.
