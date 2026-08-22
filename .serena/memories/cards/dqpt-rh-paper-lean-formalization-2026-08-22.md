# DQPT–RH paper (arXiv:2511.11199) — fully Lean-closed

Card: `docs/drafts/pipeline/3-formalized/dqpt-rh-paper-lean-formalization.md` (stage 3).
Related no-go: `docs/drafts/pipeline/5-failed/nature-dqpt-alternating-tail-rh-route.md`
(unchanged as an RH route; its survivor laws are now Lean theorems).

## What is closed

19 modules `formal/GaloisForLFunctions/RHTower/DQPT*.lean`, namespace `RHTower.DQPT`, all wired
into `GaloisForLFunctions/RHTower.lean`, all 62 capstones `#print axioms`-clean.

| Module | Content |
|---|---|
| `DQPTAltPartialSum` | `dqptRp`, MVT + second-difference bounds, paired tail `A_N`, telescoping, `dqptEta_eq_altPartialSum_add_tail` |
| `DQPTTailNormal` | `¼(N+1)^{-β} ≤ ‖A_N‖ ≤ ¾(N+1)^{-β}` with the **explicit** threshold `N+1 ≥ 3‖s‖‖s+1‖` |
| `DQPTPartialSumRate` | `dqpt_tendsto_neg_log_div_logb` power sandwich; the `β ln2 / 0` dichotomy on `η` and on `ζ` |
| `DQPTPartitionRate` | `Z_N(β)` integral bounds, `→ ζ(β)`, rate `(β−1)ln2 / 0` |
| `DQPTFreeEnergy` | free-energy trichotomy + entropy density `−ln2 / 0` |
| `DQPTEtaBound` | fencing MVT (`dqpt_norm_sub_le_of_deriv_le`), gap telescope, `‖η(s)‖ ≤ ‖s‖/β` |
| `DQPTEtaDeriv` | term-by-term `η′` via `hasDerivAt_tsum_of_isPreconnected`, `‖η′‖ ≤ ‖s‖/β²+1/β` |
| `DQPTZetaDerivBound` | `(1−2^{1−s})²ζ′ = η′(1−2^{1−s}) − 2^{1−s}ln2·η`; explicit `ζ′` bound |
| `DQPTChiOrder` | `‖sin(πs/2)‖² = sin²+sinh²`; **`|χ(β+it)|·(t/2π)^{β−1/2} → 1`** |
| `DQPTObservables` | `L(β,t) = −S_N/Z_N`, `Z·L → (2^{1−s}−1)ζ`, Choi–Jamiołkowski inner product |
| `DQPTReflectedSlope` | first normal `(N+1)^s A_N → ½`; reflected ratio bounds |
| `DQPTOracleNumerics` | dyadic partition, `log(1+d)` remainder, geometric bounds, `|2^x−1| ≤ |x|`, `2^x` series |
| `DQPTAngleNumerics` | cosine Taylor remainder via `alternating_series_error_bound`; `sin²` separation |
| `DQPTBernoulliBound` | `ζ(2k)` even/odd split bounds; `|B_{2k}| = 2(2k)!ζ(2k)/(2π)^{2k}` |
| `DQPTStateError` | chord identity, angle perturbation, arctan Lipschitz, normalisation Lipschitz, phase error |
| `DQPTAmplitudeSplit` | block split `c_w² = c_{w0}²+c_{w1}²`, split angle, post-selection `> 1/2` |
| `DQPTEulerMaclaurin` | **new mathlib gap**: EM to arbitrary order + `|B_{2k}(x)| ≤ |B_{2k}|` |
| `DQPTEulerMaclaurinPartialSum` | Prop 4.5: EM approximation of `S(a,b,β)` and its remainder bound |
| `DQPTProbeDensityMatrix` | `exp(−(ia/2)σx)`, joint evolution as a matrix exponential, `ρ_probe` |

## Reusable assets this left behind

* `DqptDerivTower` + `dqpt_euler_maclaurin`: Euler–Maclaurin to order `2m+2` for **any** derivative
  tower on an interval — no global `ContDiff`. Use this instead of re-deriving EM.
* `dqpt_abs_bernoulliFun_le`: `|B_{2k}(x)| ≤ |B_{2k}|` on `[0,1]`, from mathlib's
  `hasSum_one_div_nat_pow_mul_cos`. The sharp input for every EM remainder.
* `dqpt_norm_sub_le_of_deriv_le`: fencing MVT in increment form (`‖f b − f a‖ ≤ B b − B a`),
  and `dqpt_gap_telescope` for summing increments over non-overlapping intervals. This pair
  replaces integral comparison in every `∑ n^{-s}`-style tail estimate.
* `dqpt_tendsto_neg_log_div_logb`: two-sided power sandwich ⇒ logarithmic rate.
* `dqpt_gamma_ratio_tendsto`: two-sided vertical Gamma-ratio law (both signs of `b−a`), built on
  `RHTower.gamma_vertical_ratio_norm_rpow_tendsto`.
* `dqpt_normalize_dist_le`: `‖x/‖x‖ − y/‖y‖‖ ≤ 2‖x−y‖/‖x‖` in any normed space.

## Traps hit

* mathlib has **no** `NormedRing (Matrix …)` instance, so `Pi.coe_exp` does **not** apply to a
  matrix-valued family. Do not try `Matrix.exp_blockDiagonal` + `Pi.coe_exp`. Instead conjugate
  the block matrix to a **ℂ-valued diagonal** (Hadamard ⊗ 1) and use `Matrix.exp_units_conj`
  + `Matrix.exp_diagonal` + `Pi.coe_exp` at `𝔸 = ℂ`.
* `simp` rewrites `↑(Real.cos x) → Complex.cos ↑x` and then cannot discharge
  `conj (Complex.cos (↑a * 2⁻¹))`. Fix: `simp [-Complex.ofReal_cos, -Complex.ofReal_sin]`.
* `Real.tsum_le_of_sum_range_le` (not `tsum_le_of_sum_range_le`).
* Renames in this toolchain: `div_le_div_iff → div_le_div_iff₀`,
  `le_or_lt → le_total`, `Nat.Ico_succ_right → Finset.Ico_add_one_right_eq_Icc`,
  `Nat.cast_sub (α := ℝ) → (R := ℝ)`, `Complex.cos_ofReal → ← Complex.ofReal_cos`,
  `Complex.sq_abs`/`Complex.norm_eq_abs` gone (use `Complex.norm_def` + `Complex.normSq_apply`).

## Deliberately out of scope

All gate-/ancilla-count statements (Lemma 3.1/3.2, Thm 4.2/4.4/4.11, Prop 4.8/4.9, Thm 5.1,
Methods IV E; published Cor 4.2, Prop 5.7/5.8, Lemma 5.9). They quantify over an unspecified
circuit-cost model, cite unproved primitive costs, and conclude `Poly(...)` without naming the
polynomial or its uniformity. Every mathematical step *inside* those proofs is formalized.

## Corrections to the source found while formalizing

1. The `S_N` rate dichotomy is on `η(s) = (1−2^{1−s})ζ(s)`, not on `ζ(s)` (they differ only on
   `Re s = 1`).
2. Eq. (6.8)'s first denominator should be `|2^{1−β}−1|β²`, not `|2^{1−β}−1|β`.
3. Eq. (3.11)'s geometric cascade sums to `η`, not `η/2`.
4. Supplementary Note 1's `A = A(s)` threshold is non-effective; the second-difference route used
   here gives the explicit threshold `N+1 ≥ 3‖s‖‖s+1‖`.
