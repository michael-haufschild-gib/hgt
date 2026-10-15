import GaloisForLFunctions.RHTower.CHMDStage7HyperbolicCoshFactorizationAndEvenSubblindDecomposition

/-!
# CHMD Stage 8: Even Window Positive-Part Control and Uniform Two-Bump Midpoint Convexity on `WeilPositiveEvenPolar`

This module establishes the **Stage 8** window and two-bump midpoint convexity theorems on the
pole-free even cone `WeilPositiveEvenPolar`:

1. **Unconditional Even Window Positive-Part Bound (`even_window_posPart_le_of_weilPositiveEvenPolar`)**:
   Using the unconditional dyadic `ℓ¹` positive-part bound
   `even_sum_posPart_Ioc_le_of_weilPositiveEvenPolar` from Stage 7, we prove that for every
   `lam` satisfying `WeilPositiveEvenPolar lam`, every `M ≥ 1`, and every window center `2a ≥ log(2M)`,
   the positive-part window sum over `[2, 8M]` is bounded by three dyadic blocks:
   `∑ n ∈ Icc 2 (8 * M), max (lam n) 0 / √n * farKernel (log n - 2 * a) ≤ farMass * (√M)⁻¹ * (21 / 2 * M * (log (8 * M) + evenToeplitzConst + 1))`.

2. **Exact Cross-Kernel and Cross-Sum Evaluation for Pairs of Even Far Bumps
   (`farCrossKernel_evenFarBump`, `summable_farSum_term`, `farCrossSum_evenFarBump`,
   `farCoeff_evenFarBump`, `farCoeff_evenFarBump_eq_cosh_div_cosh`)**:
   We evaluate the cross-correlation and cross-sum when the inner test `g` in
   `EvenSectorFarBumpPoleFreeCombination` is itself an even far bump `evenFarBump b`:
   - `farCrossKernel (evenFarBump b) y = farKernel (y - b) + farKernel (y + b)`;
   - `farCrossSum lam (evenFarBump b) a = farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2)` for all `b, a : ℝ`;
   - `farCoeff (evenFarBump b) a = Real.cosh (b / 2) / Real.cosh (a / 2) ∈ (0, 1]` for `0 ≤ b ≤ a`.

3. **Uniform Two-Bump Archimedean Bound and Midpoint Convexity Law on `WeilPositiveEvenPolar`
   (`abs_farArch_evenFarBump_add_evenFarBump_le`, `farArch_evenFarBump_sub_smul_le`,
   `two_bump_farSum_midpoint_le_of_weilPositiveEvenPolar`,
   `two_bump_cosh_normalized_midpoint_le_of_weilPositiveEvenPolar`)**:
   Because `‖paperFT (evenFarBump b) r‖ ≤ 4 ‖paperFT (nodeBump 2) r‖` uniformly in `b`, the
   archimedean energy of the pole-free two-bump combination
   `G_{b, a}(x) = evenFarBump b x - (cosh(b/2) / cosh(a/2)) * evenFarBump a x`
   is bounded uniformly for all `0 ≤ b ≤ a` by `(4 / π) * farBumpArchMass` (independent of both
   `a` and `b`). Evaluating the Weil functional on `G_{b, a}` for `0 ≤ b` and `b + 2 ≤ a` yields
   the exact uniform midpoint convexity inequality for `farSum lam`:
   `2 * farSum lam b + 2 * (cosh(b/2) / cosh(a/2))^2 * farSum lam a - 4 * (cosh(b/2) / cosh(a/2)) * (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2)) ≤ (4 / π) * farBumpArchMass`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.CHMDStage8

open EvenSector OddSector WeilOneSided WeilPoleWeight WeilSpectral WeilMeanSquare ResonatorProfile
open CHMDStage6 CHMDStage7

/-! ## Section 1: Unconditional Even Window Positive-Part Bound on `WeilPositiveEvenPolar` -/

/-- **Unconditional Even Window Positive-Part Bound**:
for any `lam` satisfying `WeilPositiveEvenPolar lam`, any `M ≥ 1`, and any `2a ≥ log(2M)`,
the positive part of `lam` seen through the window `farKernel (log n - 2a)` on `[2, 8M]` is
controlled by three dyadic blocks. -/
theorem even_window_posPart_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {M : ℕ} (hM : 1 ≤ M) {a : ℝ}
    (ha : Real.log (2 * M : ℕ) ≤ 2 * a) :
    ∑ n ∈ Finset.Icc 2 (8 * M), max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) ≤
      farMass * (Real.sqrt M)⁻¹ *
        (21 / 2 * M * (Real.log (8 * M) + evenToeplitzConst + 1)) := by
  have hK0 : 0 ≤ farMass := (farKernel_nonneg 0).trans (farKernel_le 0)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog2 := Real.log_two_gt_d9
  have hrO := nodeBump_rOut_le 2
  have hg0 : ∀ n, 0 ≤ max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) := fun n =>
    mul_nonneg (div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) (farKernel_nonneg _)
  have hzero : ∀ n ∈ Finset.Ioc 0 M,
      max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) = 0 := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hl : Real.log n ≤ Real.log M := Real.log_le_log hn0 (by exact_mod_cast hn2)
    have h2M : Real.log (2 * M : ℕ) = Real.log 2 + Real.log M := by
      push_cast; exact Real.log_mul (by norm_num) hM0.ne'
    have hk : farKernel (Real.log n - 2 * a) = 0 :=
      farKernel_eq_zero (by rw [abs_of_nonpos (by linarith)]; linarith)
    rw [hk, mul_zero]
  have hbound : ∀ n ∈ Finset.Ioc M (8 * M),
      max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) ≤
        farMass * (Real.sqrt M)⁻¹ * max (lam n) 0 := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : (Real.sqrt n)⁻¹ ≤ (Real.sqrt M)⁻¹ := by
      rw [inv_le_inv₀ (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hM0)]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn1.le)
    have hlp := le_max_right (lam n) 0
    calc max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a)
        ≤ max (lam n) 0 / Real.sqrt n * farMass :=
          mul_le_mul_of_nonneg_left (farKernel_le _) (div_nonneg hlp (Real.sqrt_nonneg _))
      _ = farMass * (Real.sqrt n)⁻¹ * max (lam n) 0 := by ring
      _ ≤ farMass * (Real.sqrt M)⁻¹ * max (lam n) 0 := by gcongr
  have hblocks : ∑ n ∈ Finset.Ioc M (8 * M), max (lam n) 0 ≤
      21 / 2 * M * (Real.log (8 * M) + evenToeplitzConst + 1) := by
    have hlog : ∀ k : ℕ, 1 ≤ k → k ≤ 4 * M →
        Real.log (2 * k : ℕ) + evenToeplitzConst + 1 ≤
          Real.log (8 * M) + evenToeplitzConst + 1 := by
      intro k hk1 hk
      have h8 : ((2 * k : ℕ) : ℝ) ≤ 8 * M := by
        have : (k : ℝ) ≤ 4 * M := by exact_mod_cast hk
        push_cast; linarith
      have := Real.log_le_log (by exact_mod_cast (show 0 < 2 * k by omega)) h8
      linarith
    have P1 := even_sum_posPart_Ioc_le_of_weilPositiveEvenPolar hpf hM
    have P2 := even_sum_posPart_Ioc_le_of_weilPositiveEvenPolar hpf (N := 2 * M) (by omega)
    have P3 := even_sum_posPart_Ioc_le_of_weilPositiveEvenPolar hpf (N := 2 * (2 * M)) (by omega)
    have Q1 := mul_le_mul_of_nonneg_left (hlog M hM (by omega))
      (show (0 : ℝ) ≤ 3 / 2 * M by positivity)
    have Q2 := mul_le_mul_of_nonneg_left (hlog (2 * M) (by omega) (by omega))
      (show (0 : ℝ) ≤ 3 / 2 * ((2 * M : ℕ) : ℝ) by positivity)
    have Q3 := mul_le_mul_of_nonneg_left (hlog (2 * (2 * M)) (by omega) (by omega))
      (show (0 : ℝ) ≤ 3 / 2 * ((2 * (2 * M) : ℕ) : ℝ) by positivity)
    rw [show 8 * M = 2 * (2 * (2 * M)) by ring,
      ← Finset.sum_Ioc_consecutive _ (show M ≤ 2 * M by omega)
        (show 2 * M ≤ 2 * (2 * (2 * M)) by omega),
      ← Finset.sum_Ioc_consecutive _ (show 2 * M ≤ 2 * (2 * M) by omega)
        (show 2 * (2 * M) ≤ 2 * (2 * (2 * M)) by omega)]
    calc _ ≤ _ := add_le_add (P1.trans Q1) (add_le_add (P2.trans Q2) (P3.trans Q3))
      _ = _ := by push_cast; ring
  calc ∑ n ∈ Finset.Icc 2 (8 * M), max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a)
      ≤ ∑ n ∈ Finset.Ioc 0 (8 * M),
          max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
          rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ioc]; omega) fun n _ _ => hg0 n
    _ = ∑ n ∈ Finset.Ioc M (8 * M),
          max (lam n) 0 / Real.sqrt n * farKernel (Real.log n - 2 * a) := by
        rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) (show M ≤ 8 * M by omega),
          Finset.sum_eq_zero hzero, zero_add]
    _ ≤ ∑ n ∈ Finset.Ioc M (8 * M), farMass * (Real.sqrt M)⁻¹ * max (lam n) 0 :=
        Finset.sum_le_sum hbound
    _ = farMass * (Real.sqrt M)⁻¹ * ∑ n ∈ Finset.Ioc M (8 * M), max (lam n) 0 := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hblocks (by positivity)

/-! ## Section 2: Exact Cross-Kernel and Cross-Sum Evaluation for Pairs of Even Far Bumps -/

/-- **Cross-Kernel of an Even Far Bump**:
`farCrossKernel (evenFarBump b) y = farKernel (y - b) + farKernel (y + b)`. -/
theorem farCrossKernel_evenFarBump (b y : ℝ) :
    farCrossKernel (evenFarBump b) y = farKernel (y - b) + farKernel (y + b) := by
  unfold farCrossKernel evenFarBump farKernel crossCorr
  have i1 : Integrable fun t => farBump (t - b) * farBump (t - y) := by
    have := (integrable_farBump_mul (y - b)).comp_sub_right b
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t - b) * farBump (t - b - (y - b)) = _
    rw [show t - b - (y - b) = t - y by ring]
  have i2 : Integrable fun t => farBump (t + b) * farBump (t - y) := by
    have := (integrable_farBump_mul (y + b)).comp_add_right b
    refine this.congr (Eventually.of_forall fun t => ?_)
    show farBump (t + b) * farBump (t + b - (y + b)) = _
    rw [show t + b - (y + b) = t - y by ring]
  have e : (fun t => (farBump (t - b) + farBump (t + b)) * farBump (t - y)) =
      fun t => farBump (t - b) * farBump (t - y) + farBump (t + b) * farBump (t - y) := by
    funext t; ring
  rw [e, integral_add i1 i2]
  have j1 : ∫ t, farBump (t - b) * farBump (t - y) =
      ∫ s, farBump s * farBump (s - (y - b)) := by
    rw [← integral_sub_right_eq_self (fun s => farBump s * farBump (s - (y - b))) b]
    congr 1; funext t; congr 2; ring
  have j2 : ∫ t, farBump (t + b) * farBump (t - y) =
      ∫ s, farBump s * farBump (s - (y + b)) := by
    rw [← integral_add_right_eq_self (fun s => farBump s * farBump (s - (y + b))) b]
    congr 1; funext t; congr 2; ring
  rw [j1, j2]

/-- Every `farSum` series has finite support in `n : ℕ` and is therefore unconditionally summable
for any sequence `lam : ℕ → ℝ` and any `a : ℝ`. -/
theorem summable_farSum_term (lam : ℕ → ℝ) (a : ℝ) :
    Summable (fun n : ℕ =>
      (if 2 ≤ n then lam n / Real.sqrt n else 0) * farKernel (Real.log n - 2 * a)) := by
  set N : ℕ := ⌈Real.exp (2 * |a|)⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha2 : 2 * a ≤ Real.log N + Real.log 2 + 1 / 12 := by
    have h1 : Real.exp (2 * |a|) ≤ N := by
      have := Nat.le_ceil (Real.exp (2 * |a|))
      have : (⌈Real.exp (2 * |a|)⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈Real.exp (2 * |a|)⌉₊ ≤ N by omega)
      linarith
    have h2 : 2 * |a| ≤ Real.log N := (Real.le_log_iff_exp_le hN0).mpr h1
    have h3 : a ≤ |a| := le_abs_self a
    have hlog2 := Real.log_two_gt_d9
    linarith
  refine summable_of_ne_finset_zero (s := Finset.Icc 2 (4 * N)) fun n hn => ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with h1 | h1
  · rw [if_neg (by omega), zero_mul]
  · have hr := nodeBump_rOut_le 2
    have hlog2 := Real.log_two_gt_d9
    have hn4 : (4 * N : ℝ) ≤ n := by exact_mod_cast h1.le
    have hlog : Real.log (4 * N) ≤ Real.log n := Real.log_le_log (by positivity) hn4
    rw [Real.log_mul (by norm_num) hN0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      at hlog
    push_cast at hlog
    rw [farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith), mul_zero]

/-- **Cross-Sum of an Even Far Bump**:
for any `lam : ℕ → ℝ` and any `b, a : ℝ`,
`farCrossSum lam (evenFarBump b) a = farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2)`. -/
theorem farCrossSum_evenFarBump (lam : ℕ → ℝ) (b a : ℝ) :
    farCrossSum lam (evenFarBump b) a =
      farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2) := by
  unfold farCrossSum farSum
  have hs1 := summable_farSum_term lam ((a + b) / 2)
  have hs2 := summable_farSum_term lam ((a - b) / 2)
  rw [← hs1.tsum_add hs2]
  refine tsum_congr fun n => ?_
  rw [farCrossKernel_evenFarBump b (Real.log n - a),
    show Real.log n - a - b = Real.log n - 2 * ((a + b) / 2) by ring,
    show Real.log n - a + b = Real.log n - 2 * ((a - b) / 2) by ring]
  ring

/-- **Pole-Free Coefficient of an Even Far Bump**:
`farCoeff (evenFarBump b) a = (Real.exp (-b / 2) + Real.exp (b / 2)) / (Real.exp (-a / 2) + Real.exp (a / 2))`. -/
theorem farCoeff_evenFarBump (b a : ℝ) :
    farCoeff (evenFarBump b) a =
      (Real.exp (-b / 2) + Real.exp (b / 2)) / (Real.exp (-a / 2) + Real.exp (a / 2)) := by
  unfold farCoeff
  rw [integral_evenFarBump_mul_exp]
  have hJ : farJ ≠ 0 := farJ_pos.ne'
  exact mul_div_mul_right _ _ hJ

/-- **Hyperbolic Cosine Form of `farCoeff (evenFarBump b) a`**:
`farCoeff (evenFarBump b) a = Real.cosh (b / 2) / Real.cosh (a / 2)`. -/
theorem farCoeff_evenFarBump_eq_cosh_div_cosh (b a : ℝ) :
    farCoeff (evenFarBump b) a = Real.cosh (b / 2) / Real.cosh (a / 2) := by
  have hb : Real.exp (-b / 2) + Real.exp (b / 2) = 2 * Real.cosh (b / 2) := by
    rw [Real.cosh_eq, show -(b / 2) = -b / 2 by ring]; ring
  have ha : Real.exp (-a / 2) + Real.exp (a / 2) = 2 * Real.cosh (a / 2) := by
    rw [Real.cosh_eq, show -(a / 2) = -a / 2 by ring]; ring
  rw [farCoeff_evenFarBump, hb, ha]
  exact mul_div_mul_left _ _ two_ne_zero

theorem farCoeff_evenFarBump_nonneg (b a : ℝ) :
    0 ≤ farCoeff (evenFarBump b) a := by
  rw [farCoeff_evenFarBump_eq_cosh_div_cosh]
  exact div_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le

theorem farCoeff_evenFarBump_le_one {b a : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    farCoeff (evenFarBump b) a ≤ 1 := by
  rw [farCoeff_evenFarBump_eq_cosh_div_cosh, div_le_one (Real.cosh_pos _)]
  have h1 : |b / 2| ≤ |a / 2| := by
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  exact Real.cosh_le_cosh.mpr h1

/-! ## Section 3: Uniform Two-Bump Archimedean Bound and Midpoint Convexity Law on `WeilPositiveEvenPolar` -/

/-- **Uniform Archimedean Bound for the Sum of Two Even Far Bumps**:
`|farArch (evenFarBump b + evenFarBump a)| ≤ (2 / π) * farBumpArchMass` for all `0 ≤ b ≤ a`. -/
theorem abs_farArch_evenFarBump_add_evenFarBump_le {b a : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    |farArch (fun x => evenFarBump b x + evenFarBump a x)| ≤
      2 / Real.pi * farBumpArchMass := by
  have hbs : ∀ x, b + 1 < |x| → evenFarBump b x = 0 := fun x hx => evenFarBump_eq_zero hb hx
  have ha0 : 0 ≤ a := hb.trans hba
  have has : ∀ x, a + 1 < |x| → evenFarBump a x = 0 := fun x hx => evenFarBump_eq_zero ha0 hx
  have hbs' : ∀ x, a + 1 < |x| → evenFarBump b x = 0 := fun x hx => hbs x (by linarith)
  have hs : ∀ x, a + 1 < |x| → evenFarBump b x + evenFarBump a x = 0 := fun x hx => by
    rw [hbs' x hx, has x hx, add_zero]
  have hbc := hasCompactSupport_evenFarBump b
  have hac := hasCompactSupport_evenFarBump a
  have hIb := integrable_normSq_paperFT_mul_abs_gammaBracket (contDiff_evenFarBump b) hbs'
  have hIa := integrable_normSq_paperFT_mul_abs_gammaBracket (contDiff_evenFarBump a) has
  have hIs := integrable_normSq_paperFT_mul_abs_gammaBracket
    ((contDiff_evenFarBump b).add (contDiff_evenFarBump a)) hs
  have hpt : ∀ r : ℝ, ‖paperFT (fun u => ((evenFarBump b u + evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
      |EF.gammaBracket r| ≤
      2 * (‖paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
        2 * (‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) := by
    intro r
    have e : paperFT (fun u => ((evenFarBump b u + evenFarBump a u : ℝ) : ℂ)) r =
        paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r +
          paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r := by
      have := paperFT_ofReal_add_smul (continuous_evenFarBump b) hbc (continuous_evenFarBump a)
        hac 1 1 r
      rw [show (fun u => ((evenFarBump b u + evenFarBump a u : ℝ) : ℂ)) =
        fun u => ((1 * evenFarBump b u + 1 * evenFarBump a u : ℝ) : ℂ) by
          funext u; push_cast; ring, this]
      push_cast; ring
    rw [e]
    have hsq : ‖paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r +
        paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 ≤
        2 * ‖paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r‖ ^ 2 +
          2 * ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _)
        (norm_add_le (paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r)
          (paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r)) 2
      nlinarith [sq_nonneg (‖paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r‖ -
        ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖)]
    have hG := abs_nonneg (EF.gammaBracket r)
    nlinarith
  have hint : ∫ r : ℝ, ‖paperFT (fun u => ((evenFarBump b u + evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
      |EF.gammaBracket r| ≤ 4 * farBumpArchMass := by
    calc ∫ r : ℝ, ‖paperFT (fun u => ((evenFarBump b u + evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
          |EF.gammaBracket r|
        ≤ ∫ r : ℝ, (2 * (‖paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
          2 * (‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|)) :=
          integral_mono hIs ((hIb.const_mul 2).add (hIa.const_mul 2)) hpt
      _ = 2 * (∫ r : ℝ, ‖paperFT (fun u => ((evenFarBump b u : ℝ) : ℂ)) r‖ ^ 2 * |EF.gammaBracket r|) +
          2 * ∫ r : ℝ, ‖paperFT (fun u => ((evenFarBump a u : ℝ) : ℂ)) r‖ ^ 2 *
            |EF.gammaBracket r| := by
          rw [integral_add (hIb.const_mul 2) (hIa.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 4 * farBumpArchMass := by
          linarith [integral_evenFarBump_arch_le b, integral_evenFarBump_arch_le a]
  calc |farArch (fun x => evenFarBump b x + evenFarBump a x)|
      ≤ 1 / (2 * Real.pi) * (4 * farBumpArchMass) :=
        (abs_farArch_le _).trans (mul_le_mul_of_nonneg_left hint (by positivity))
    _ = 2 / Real.pi * farBumpArchMass := by ring

/-- **Uniform Archimedean Bound for Two-Bump Linear Combinations**:
for all `0 ≤ b ≤ a` and `0 ≤ c ≤ 1`,
`farArch (fun x => evenFarBump b x - c * evenFarBump a x) ≤ (4 / π) * farBumpArchMass`. -/
theorem farArch_evenFarBump_sub_smul_le {b a c : ℝ} (hb : 0 ≤ b) (hba : b ≤ a)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    farArch (fun x => evenFarBump b x - c * evenFarBump a x) ≤
      4 / Real.pi * farBumpArchMass := by
  have ha0 : 0 ≤ a := hb.trans hba
  have hbs : ∀ x, a + 1 < |x| → evenFarBump b x = 0 := fun x hx =>
    evenFarBump_eq_zero hb (by linarith)
  have has : ∀ x, a + 1 < |x| → evenFarBump a x = 0 := fun x hx =>
    evenFarBump_eq_zero ha0 hx
  rw [farArch_sub_smul (contDiff_evenFarBump b) (contDiff_evenFarBump a) hbs has c]
  have hAb := (le_abs_self _).trans (abs_farArch_evenFarBump_le b)
  have hAa := (le_abs_self _).trans (abs_farArch_evenFarBump_le a)
  have hAs := (neg_le_abs _).trans (abs_farArch_evenFarBump_add_evenFarBump_le hb hba)
  have hM0 : 0 ≤ 1 / (2 * Real.pi) * farBumpArchMass :=
    (abs_nonneg _).trans (abs_farArch_evenFarBump_le 0)
  have h1 : (1 + c) * farArch (evenFarBump b) ≤ 2 * (1 / (2 * Real.pi) * farBumpArchMass) := by
    calc (1 + c) * farArch (evenFarBump b)
        ≤ (1 + c) * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_left hAb (by linarith)
      _ ≤ 2 * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_right (by linarith) hM0
  have h2 : -c * farArch (fun x => evenFarBump b x + evenFarBump a x) ≤
      2 / Real.pi * farBumpArchMass := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hMpos : 0 ≤ farBumpArchMass := nonneg_of_mul_nonneg_right hM0 (by positivity)
    calc -c * farArch (fun x => evenFarBump b x + evenFarBump a x)
        = c * (-farArch (fun x => evenFarBump b x + evenFarBump a x)) := by ring
      _ ≤ c * (2 / Real.pi * farBumpArchMass) :=
          mul_le_mul_of_nonneg_left hAs hc0
      _ ≤ 1 * (2 / Real.pi * farBumpArchMass) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ = 2 / Real.pi * farBumpArchMass := one_mul _
  have h3 : (c + c ^ 2) * farArch (evenFarBump a) ≤
      2 * (1 / (2 * Real.pi) * farBumpArchMass) := by
    have hc2 : c + c ^ 2 ≤ 2 := by nlinarith
    calc (c + c ^ 2) * farArch (evenFarBump a)
        ≤ (c + c ^ 2) * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_left hAa (by positivity)
      _ ≤ 2 * (1 / (2 * Real.pi) * farBumpArchMass) :=
          mul_le_mul_of_nonneg_right hc2 hM0
  have he : 2 * (1 / (2 * Real.pi) * farBumpArchMass) + 2 / Real.pi * farBumpArchMass +
      2 * (1 / (2 * Real.pi) * farBumpArchMass) = 4 / Real.pi * farBumpArchMass := by ring
  linarith

/-- **Uniform Two-Bump Midpoint Convexity Inequality on `WeilPositiveEvenPolar`**:
for every `lam` satisfying `WeilPositiveEvenPolar lam` and all `0 ≤ b` and `b + 2 ≤ a`,
with `c = farCoeff (evenFarBump b) a = cosh(b/2) / cosh(a/2)`,
`2 * farSum lam b + 2 * c^2 * farSum lam a - 4 * c * (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2)) ≤ (4 / π) * farBumpArchMass`. -/
theorem two_bump_farSum_midpoint_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    2 * farSum lam b + 2 * farCoeff (evenFarBump b) a ^ 2 * farSum lam a -
      4 * farCoeff (evenFarBump b) a *
        (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2)) ≤
      4 / Real.pi * farBumpArchMass := by
  have ha0 : 0 ≤ a := by linarith
  have hba' : b ≤ a := by linarith
  set c := farCoeff (evenFarBump b) a with hc
  have hc0 : 0 ≤ c := farCoeff_evenFarBump_nonneg b a
  have hc1 : c ≤ 1 := farCoeff_evenFarBump_le_one hb hba'
  set G : ℝ → ℝ := fun x => evenFarBump b x - c * evenFarBump a x with hG
  have hGd : ContDiff ℝ 2 G :=
    (contDiff_evenFarBump b).sub (contDiff_const.mul (contDiff_evenFarBump a))
  have hbs : ∀ x, b + 1 < |x| → evenFarBump b x = 0 := fun x hx => evenFarBump_eq_zero hb hx
  have has : ∀ x, a + 1 < |x| → evenFarBump a x = 0 := fun x hx => evenFarBump_eq_zero ha0 hx
  have hGs : ∀ x, a + 1 < |x| → G x = 0 := fun x hx => by
    simp only [hG, hbs x (by linarith), has x hx, mul_zero, sub_zero]
  have hGc := hasCompactSupport_of_abs_gt_eq_zero hGs
  have hGe : ∀ x, G (-x) = G x := fun x => by simp only [hG, evenFarBump_neg]
  have hP0 : ∫ u, G u * Real.exp (-u / 2) = 0 :=
    integral_sub_farCoeff_mul_exp (continuous_evenFarBump b) (hasCompactSupport_evenFarBump b) a
  have hpos := hpf (fun u => (G u : ℂ)) (contDiff_ofReal_comp hGd)
    (hGc.comp_left Complex.ofReal_zero) (fun x => by simp only [hGe])
    (by rw [paperFT_ofRealFun_I_div_two, hP0, Complex.ofReal_zero])
  rw [re_weilFullFunctional_ofReal_eq lam hGd.continuous hGc,
    re_weilPoleTerm_ofReal_even hGd.continuous hGc hGe, hP0] at hpos
  have hG' : G = fun u => evenFarBump b u + -c * evenFarBump a u := by
    funext u; simp only [hG]; ring
  have hatoms : atomPairing lam (crossCorr G G) =
      2 * farSum lam b - 4 * c * (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2)) +
        2 * c ^ 2 * farSum lam a := by
    rw [hG', atomPairing_add_smul_expand lam (continuous_evenFarBump b)
      (hasCompactSupport_evenFarBump b) (continuous_evenFarBump a)
      (hasCompactSupport_evenFarBump a) (-c),
      atomPairing_evenFarBump lam hb,
      atomPairing_crossCorr_evenFarBump lam (continuous_evenFarBump b)
        (hasCompactSupport_evenFarBump b) (evenFarBump_neg b) (R := b + 1) (by linarith) hbs
        (by linarith),
      farCrossSum_evenFarBump lam b a,
      atomPairing_evenFarBump lam ha0]
    ring
  have harch := farArch_evenFarBump_sub_smul_le hb hba' hc0 hc1
  rw [← hG] at harch
  linarith

/-- **Hyperbolic Cosine Normalized Two-Bump Midpoint Inequality on `WeilPositiveEvenPolar`**:
rewrites `two_bump_farSum_midpoint_le_of_weilPositiveEvenPolar` explicitly in terms of
`Real.cosh (b / 2) / Real.cosh (a / 2)`. -/
theorem two_bump_cosh_normalized_midpoint_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    2 * farSum lam b + 2 * (Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 * farSum lam a -
      4 * (Real.cosh (b / 2) / Real.cosh (a / 2)) *
        (farSum lam ((a + b) / 2) + farSum lam ((a - b) / 2)) ≤
      4 / Real.pi * farBumpArchMass := by
  rw [← farCoeff_evenFarBump_eq_cosh_div_cosh]
  exact two_bump_farSum_midpoint_le_of_weilPositiveEvenPolar hpf hb hba

end RHTower.CHMDStage8

end
