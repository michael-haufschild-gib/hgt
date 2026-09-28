import GaloisForLFunctions.RHTower.WeilPositivitySummableWeightsObstruction
import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound

/-!
# Weil positivity is rigid under summable perturbations of the prime weights

Replace the von Mangoldt weights of the finite-atom Weil symbol of `ζ` by `Λ(n) + w(n)` with
`Σ_{n ≥ 2} |w(n)| n^{-1/2} < ∞`, keeping the archimedean term of `ζ`.

**Theorem** (`vonMangoldt_add_summable_not_weilPositive`).  If `w(n₀) ≠ 0` for some `n₀ ≥ 2`, then
`Λ + w` is not Weil-positive: some polar-constrained `C²` test at some level has negative symbol
energy.

**Corollaries.**
* `eq_vonMangoldt_of_weilPositive_of_summable_sub`: a Weil-positive `lam` with
  `Σ |lam(n) - Λ(n)| n^{-1/2} < ∞` equals `Λ` on `n ≥ 2`.
* `vonMangoldt_update_not_weilPositive`: changing the weight of a single integer `n₀ ≥ 2`, for
  instance a single prime, by any `c ≠ 0` destroys Weil positivity.
* `abs_le_of_weilPositive`: every Weil-positive weight system satisfies
  `|lam(n)| ≤ √n (log n + C₀)`, so the Weil-positive weights form a compact convex set in the
  product topology.

Together with `summable_weights_weilAtomSymbol_not_nonneg` (no summable weights are Weil-positive),
the Weil-positive weights meet `Λ + ℓ¹(n^{-1/2})` at most in `Λ` and miss `ℓ¹(n^{-1/2})` entirely.

## Mechanism

* **Energy decomposition** (`integral_weilAtomSymbol_vonMangoldt_add_le`).  For a polar-constrained
  test, `∫ |h|² S_{Λ+w} ≤ 2π ‖W(f)‖ - ∫ |h|² P_w + ε_N ∫ |h|²`, where `W` is the zero side of `ζ`,
  `P_w(τ) = Σ 2w(n) n^{-1/2} cos(τ log n)` is the perturbation symbol and `ε_N` the atom tail.
* **Coefficient extraction** (`eq_zero_of_perturbationSymbol_nonpos`).  `∫ |h_F|² P_w` is the
  cosine-moment series `Σ 2π w(n) n^{-1/2} Re(k(log n) + k(-log n))`.  For the two-point resonator
  `F = g(x - log 1) ± g(x - log n₀)` with a narrow polar-free bump `g`, only the atom `n₀` is seen, with
  sign `±`.  So `P_w ≤ 0` everywhere forces `w = 0`.
* **Concentration** (`vonMangoldt_add_violation_of_concentration`).  Where `P_w > 0`, spread
  radical tests concentrated at a nearby point have zero side `O(S^{10} e^{-S})`.  Their energy is
  `≤ -c S`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section
namespace RHTower

open Zeta23 ResonatorProfile

local notation "Φ" => riemannPhiKernel

variable {w : ℕ → ℝ}

/-- The perturbation symbol `P_w(τ) = Σ_{n ≥ 2} 2 w(n) n^{-1/2} cos(τ log n)`. -/
def perturbationSymbol (w : ℕ → ℝ) (τ : ℝ) : ℝ := ∑' n : ℕ, weightAtom w n (τ / (2 * π))

theorem continuous_perturbationSymbol (hsum : Summable fun n => |w n| / Real.sqrt n) :
    Continuous (perturbationSymbol w) :=
  (continuous_tsum (fun n => by unfold weightAtom; split_ifs <;> fun_prop) (hsum.mul_left 2)
    fun n ξ => by rw [Real.norm_eq_abs]; exact abs_weightAtom_le w n ξ).comp (by fun_prop)

theorem abs_perturbationSymbol_le (hsum : Summable fun n => |w n| / Real.sqrt n) (τ : ℝ) :
    |perturbationSymbol w τ| ≤ ∑' n : ℕ, 2 * (|w n| / Real.sqrt n) := by
  have hs := summable_weightAtom hsum (τ / (2 * π))
  calc |perturbationSymbol w τ| ≤ ∑' n : ℕ, |weightAtom w n (τ / (2 * π))| := by
        have h := norm_tsum_le_tsum_norm (f := fun n => weightAtom w n (τ / (2 * π)))
          (by simpa [Real.norm_eq_abs] using hs.abs)
        simpa [Real.norm_eq_abs, perturbationSymbol] using h
    _ ≤ _ := Summable.tsum_le_tsum (fun n => abs_weightAtom_le w n _) hs.abs (hsum.mul_left 2)

theorem fullAtomSymbol_eq_sub (w : ℕ → ℝ) (τ : ℝ) :
    fullAtomSymbol w (τ / (2 * π)) = archimedeanWeilSymbol (τ / (2 * π)) - perturbationSymbol w τ :=
  rfl

theorem weilAtomSymbol_add (w : ℕ → ℝ) (N : ℕ) (ξ : ℝ) :
    weilAtomSymbol (fun n => (Λ n : ℝ) + w n) N ξ =
      weilAtomSymbol (fun n => (Λ n : ℝ)) N ξ + weilAtomSymbol w N ξ - archimedeanWeilSymbol ξ := by
  unfold weilAtomSymbol
  rw [← add_sub_assoc]
  have : ∑ n ∈ Finset.Icc 2 N, ((Λ n : ℝ) + w n) * (1 / Real.sqrt n) *
      (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) =
      ∑ n ∈ Finset.Icc 2 N, (Λ n : ℝ) * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) +
      ∑ n ∈ Finset.Icc 2 N, w n * (1 / Real.sqrt n) *
        (2 * Real.cos (2 * Real.pi * Real.log n * ξ)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun n _ => ?_; ring
  rw [this]; ring

/-- **Energy of a summable perturbation of `Λ`.**  For a polar-constrained `C²` test on `[-a, a]`,
`∫ |h|² S_{Λ+w} ≤ 2π ‖W(f)‖ - ∫ |h|² P_w + ε_N ∫ |h|²`, with `ε_N` the atom tail of `w` beyond
`N = ⌊e^{2a}⌋`. -/
theorem integral_weilAtomSymbol_vonMangoldt_add_le (hsum : Summable fun n => |w n| / Real.sqrt n)
    {a : ℝ} {f : ℝ → ℂ} (hfd : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) ≤
      2 * π * ‖zetaZeroConfig.W f f‖ -
        (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * perturbationSymbol w τ) +
        (2 * ∑' k : ℕ, |w (k + (⌊Real.exp (2 * a)⌋₊ + 1))| /
          Real.sqrt (k + (⌊Real.exp (2 * a)⌋₊ + 1) : ℕ)) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 := by
  have hF := integrable_normSq_paperFT hfd hfs
  have hFA := integrable_normSq_paperFT_mul_arch hfd hfs
  have hΛi := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs (fun n => (Λ n : ℝ))
  have hwi := integrable_normSq_paperFT_mul_weilAtomSymbol_of hfd hfs w
  obtain ⟨hfc, -, -, -, -⟩ := weilTest_self_data hfd hfs
  have hHc : Continuous fun τ : ℝ => ‖paperFT f τ‖ ^ 2 :=
    (continuous_paperFT_real_of_integrable (hfd.continuous.integrable_of_hasCompactSupport
      hfc)).norm.pow 2
  set Mw := ∑' n : ℕ, 2 * (|w n| / Real.sqrt n) with hMw
  have hPi : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * perturbationSymbol w τ := by
    refine (hF.mul_const Mw).mono' (hHc.mul (continuous_perturbationSymbol hsum)).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_perturbationSymbol_le hsum τ) (sq_nonneg _)
  have hfull : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * fullAtomSymbol w (τ / (2 * π)) := by
    refine (hFA.sub hPi).congr (Eventually.of_forall fun τ => ?_)
    simp only [Pi.sub_apply, fullAtomSymbol_eq_sub]; ring
  have hle := integral_weilAtomSymbol_le_full hsum hfd hfs hfull
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hfd hfs hp hm
  have hWre : (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) =
      2 * π * (zetaZeroConfig.W f f).re := by
    rw [hW, Complex.ofReal_re]; field_simp
  have hsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) +
        (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) -
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) := by
    have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) =
        fun τ : ℝ => (‖paperFT f τ‖ ^ 2 *
          weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
          ‖paperFT f τ‖ ^ 2 * weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) -
          ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π)) := by
      funext τ; rw [weilAtomSymbol_add]; ring
    have hsi : Integrable (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) +
        ‖paperFT f τ‖ ^ 2 * weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) := hΛi.add hwi
    rw [e, integral_sub hsi hFA, integral_add hΛi hwi]
  have hfullsplit : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * fullAtomSymbol w (τ / (2 * π)) =
      (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * archimedeanWeilSymbol (τ / (2 * π))) -
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * perturbationSymbol w τ := by
    rw [← integral_sub hFA hPi]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [fullAtomSymbol_eq_sub]; ring
  have hre := Complex.re_le_norm (zetaZeroConfig.W f f)
  rw [hsplit, hWre]
  rw [hfullsplit] at hle
  have hπ : 0 < π := Real.pi_pos
  nlinarith


/-- The perturbation symbol against `|h_f|²` is the cosine-moment series of the weights:
`∫ |h_f|² P_w = Σ_{n ≥ 2} 2π w(n) n^{-1/2} Re(k(log n) + k(-log n))`, `k = f ⋆ f̃`. -/
theorem integral_normSq_mul_perturbationSymbol (hsum : Summable fun n => |w n| / Real.sqrt n)
    {a : ℝ} {f : ℝ → ℂ} (hfd : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * perturbationSymbol w τ =
      ∑' n : ℕ, (if 2 ≤ n then 2 * π * (w n / Real.sqrt n) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re else 0) := by
  have hF := integrable_normSq_paperFT hfd hfs
  have hterm : ∀ n : ℕ, Integrable fun τ : ℝ =>
      ‖paperFT f τ‖ ^ 2 * weightAtom w n (τ / (2 * π)) := by
    intro n
    unfold weightAtom
    split_ifs
    · have hc := integrable_normSq_paperFT_mul_cos hfd hfs (Real.log n)
      refine (hc.const_mul (w n * (1 / Real.sqrt n) * 2)).congr (Eventually.of_forall fun τ => ?_)
      simp only
      rw [show 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n by field_simp]; ring
    · simp
  have hval : ∀ n : ℕ, ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weightAtom w n (τ / (2 * π)) =
      if 2 ≤ n then 2 * π * (w n / Real.sqrt n) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re else 0 := by
    intro n
    unfold weightAtom
    split_ifs with hn
    · have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 *
          (w n * (1 / Real.sqrt n) * (2 * Real.cos (2 * π * Real.log n * (τ / (2 * π)))))) =
          fun τ : ℝ => (w n * (1 / Real.sqrt n) * 2) *
            (‖paperFT f τ‖ ^ 2 * Real.cos (τ * Real.log n)) := by
        funext τ
        rw [show 2 * π * Real.log n * (τ / (2 * π)) = τ * Real.log n by field_simp]; ring
      rw [e, integral_const_mul, integral_normSq_paperFT_mul_cos_eq hfd hfs]
      ring
    · simp
  have hnorm : Summable fun n : ℕ => ∫ τ : ℝ,
      ‖‖paperFT f τ‖ ^ 2 * weightAtom w n (τ / (2 * π))‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((hsum.mul_left 2).mul_right (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2))
    calc ∫ τ : ℝ, ‖‖paperFT f τ‖ ^ 2 * weightAtom w n (τ / (2 * π))‖
        ≤ ∫ τ : ℝ, 2 * (|w n| / Real.sqrt n) * ‖paperFT f τ‖ ^ 2 :=
          integral_mono (hterm n).norm (hF.const_mul _) fun τ => by
            rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, mul_comm]
            exact mul_le_mul_of_nonneg_right (abs_weightAtom_le w n _) (sq_nonneg _)
      _ = 2 * (|w n| / Real.sqrt n) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 := integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hterm hnorm
  have e : (fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * perturbationSymbol w τ) =
      fun τ : ℝ => ∑' n : ℕ, ‖paperFT f τ‖ ^ 2 * weightAtom w n (τ / (2 * π)) := by
    funext τ; unfold perturbationSymbol; rw [tsum_mul_left]
  rw [e, ← hswap]
  exact tsum_congr hval

/-- The two-point resonator coefficients `1_{m = 1} + s 1_{m = n₀}`. -/
def twoPointCoeff (n₀ : ℕ) (s : ℂ) (m : ℕ) : ℂ := if m = 1 then 1 else if m = n₀ then s else 0

theorem twoPointCoeff_diag {n₀ n : ℕ} (hn₀ : 2 ≤ n₀) (s : ℂ) (hn : 2 ≤ n) :
    ∑ m ∈ Finset.Icc 1 n₀, twoPointCoeff n₀ s (n * m) * conj (twoPointCoeff n₀ s m) =
      if n = n₀ then s else 0 := by
  have hpt : ∀ m ∈ Finset.Icc 1 n₀, twoPointCoeff n₀ s (n * m) * conj (twoPointCoeff n₀ s m) =
      if m = 1 then (if n = n₀ then s else 0) else 0 := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    by_cases h1 : m = 1
    · subst h1
      simp only [twoPointCoeff, mul_one, if_true, map_one]
      rw [if_neg (by omega)]
    · rw [if_neg h1]
      by_cases h2 : m = n₀
      · subst h2
        have : twoPointCoeff m s (n * m) = 0 := by
          unfold twoPointCoeff
          rw [if_neg (by nlinarith), if_neg (by nlinarith)]
        rw [this, zero_mul]
      · have : twoPointCoeff n₀ s m = 0 := by unfold twoPointCoeff; rw [if_neg h1, if_neg h2]
        rw [this, map_zero, mul_zero]
  rw [Finset.sum_congr rfl hpt, Finset.sum_ite_eq']
  simp [Finset.mem_Icc]; omega

/-- **Coefficient extraction.**  If the perturbation symbol of summable weights is nonpositive
everywhere, the weights vanish.  The two-point resonators `g(x - log 1) ± g(x - log n₀)` with
narrow polar-free bumps `g` see the atom `log n₀` alone, with sign `±`. -/
theorem eq_zero_of_perturbationSymbol_nonpos (hsum : Summable fun n => |w n| / Real.sqrt n)
    (hP : ∀ τ, perturbationSymbol w τ ≤ 0) {n₀ : ℕ} (hn₀ : 2 ≤ n₀) : w n₀ = 0 := by
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * w n₀ ≤ 0 := by
    intro s hs
    set N := n₀ with hNdef
    set c := twoPointCoeff n₀ (s : ℂ) with hcdef
    have hN : 1 ≤ N := by omega
    have hN1 : (0 : ℝ) < N + 1 := by positivity
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    set ω : ℝ := 1 / ((N : ℝ) + 1) with hωdef
    have hω : 0 < ω := by positivity
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNr
    set a : ℝ := Real.log N / 2 + ω / 4 with hadef
    set F := resonator N c ω with hFdef
    have hc : ∀ m, N < m → c m = 0 := by
      intro m hm; simp only [hcdef, twoPointCoeff]; rw [if_neg (by omega), if_neg (by omega)]
    have hFvan : ∀ u, a < |u| → F u = 0 := fun u hu =>
      sum_translates_eq_zero (fun v hv => gC_eq_zero hω hv) hu
    have hFs : tsupport F ⊆ Icc (-a) a := tsupport_subset_of_vanish hFvan
    have hF2 : ContDiff ℝ 2 F := contDiff_resonator N c ω 2
    set k0r : ℝ := ∫ t, gR ω t ^ 2 with hk0r
    have hk0 : EF.weilTest (gC ω) (gC ω) 0 = (k0r : ℂ) := weilTest_self_zero_ofReal (g := gR ω)
    have hk0pos : 0 < k0r := lt_of_lt_of_le (div_pos integral_d2_sq_pos (by positivity))
      (integral_gR_sq_ge hω)
    have hgap : 2 * (ω / 4) < 1 / ((N : ℝ) + 1) := by rw [← hωdef]; linarith
    have hvan0 : ∀ Y, 1 / ((N : ℝ) + 1) ≤ |Y| → EF.weilTest (gC ω) (gC ω) Y = 0 :=
      fun Y hY => weilTest_self_eq_zero (fun u hu => gC_eq_zero hω hu) (by linarith)
    have hgc0 : Continuous (gC ω) := (contDiff_gC ω 0).continuous
    have hgs0 := hasCompactSupport_gC hω
    have hsel : ∀ n : ℕ, 2 ≤ n →
        (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re =
          2 * k0r * (if n = n₀ then s else 0) := by
      intro n hn
      have h1 := weilTest_translates_log hgc0 hgs0 hvan0 hc (show 1 ≤ n by omega)
      have h2 := weilTest_translates_neg_log hgc0 hgs0 hvan0 hc (show 1 ≤ n by omega)
      rw [sum_conj_swap] at h2
      rw [show F = fun u => ∑ m ∈ Finset.Icc 1 N, c m * gC ω (u - resPt N m) from rfl, h1, h2, hk0,
        hcdef, twoPointCoeff_diag hn₀ _ hn]
      split_ifs <;> simp [Complex.add_re]; ring
    have hI := integral_normSq_mul_perturbationSymbol hsum hF2 hFs
    have hsum1 : ∑' n : ℕ, (if 2 ≤ n then 2 * π * (w n / Real.sqrt n) *
        (EF.weilTest F F (Real.log n) + EF.weilTest F F (-Real.log n)).re else 0) =
        2 * π * (w n₀ / Real.sqrt n₀) * (2 * k0r * s) := by
      rw [tsum_eq_single n₀]
      · rw [if_pos hn₀, hsel n₀ hn₀, if_pos rfl]
      · intro n hn
        split_ifs with h2
        · rw [hsel n h2, if_neg hn]; ring
        · rfl
    rw [hsum1] at hI
    have hnonpos : ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 * perturbationSymbol w τ ≤ 0 :=
      integral_nonpos fun τ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hP τ)
    rw [hI] at hnonpos
    have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
    have hπ : 0 < π := Real.pi_pos
    have : 0 < 4 * π * k0r / Real.sqrt n₀ := by positivity
    have heq : 2 * π * (w n₀ / Real.sqrt n₀) * (2 * k0r * s) =
        (4 * π * k0r / Real.sqrt n₀) * (s * w n₀) := by field_simp; ring
    rw [heq] at hnonpos
    by_contra hcon
    push Not at hcon
    linarith [mul_pos this hcon]
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  linarith

/-- The concentration stage for a summable perturbation of `Λ`: if the perturbation symbol is
`≥ d₁/2` near `τ₀` and the radical limit has size `≥ m/2` there, the spread radical tests violate
Weil positivity of `Λ + w`.  Their zero side for `ζ` is `O(S^{10} e^{-S})`. -/
theorem vonMangoldt_add_violation_of_concentration
    (hsum : Summable fun n => |w n| / Real.sqrt n)
    {τ₀ η m d₁ : ℝ} (hη0 : 0 < η) (hm0 : 0 < m) (hd₁0 : 0 < d₁)
    (hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η →
      d₁ / 2 ≤ perturbationSymbol w τ ∧ m / 2 ≤ ‖twistLimit 0 τ‖) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  set D : ℝ → ℝ := fun τ => -perturbationSymbol w τ with hDdef
  obtain ⟨Cκ, hCκ0, hCκ⟩ := exists_norm_paperFT_weilBumpC_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set Aκ := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hAκ
  have hAκ0 : 0 ≤ Aκ := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set B := (∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|)) * Aκ with hB
  have hB0 : 0 ≤ B := mul_nonneg (integral_nonneg fun _ => by positivity) hAκ0
  set Mlam := ∑' n : ℕ, 2 * (|w n| / Real.sqrt n) with hMlam
  have hMlam0 : 0 ≤ Mlam := tsum_nonneg fun n => by positivity
  set CD := Mlam with hCD
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_twistTest_log_le 0 τ₀
  have hCD0 : 0 ≤ CD := by positivity
  have hcos : 0 < Real.cos (1 / 4) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],
    by linarith [Real.pi_gt_three]⟩
  set c := (Real.cos (1 / 4) / 4) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set I₃ := ∫ τ : ℝ, 1 / (1 + |τ - τ₀|) ^ 3 with hI₃
  have hI₃0 : 0 ≤ I₃ := integral_nonneg fun _ => by positivity
  set L₀ := m / 4 * c with hL₀
  have hL₀0 : 0 < L₀ := by positivity
  set Ctail := |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / η ^ 4) * I₃ with hCtail
  have hCtail0 : 0 ≤ Ctail := by positivity
  set goal := d₁ / 2 * L₀ ^ 2 with hgoal
  have hgoal0 : 0 < goal := by positivity
  have t1 : Tendsto (fun S : ℝ => 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have t3 : Tendsto (fun S : ℝ => Ctail / S ^ 3) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have t4 : Tendsto (fun S : ℝ => 2 * π * KW * (S ^ 9 * Real.exp (-S))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 9).const_mul (2 * π * KW)
  obtain ⟨S, ⟨⟨⟨hE2, hE4⟩, hE5⟩, hE1⟩⟩ := (((t1.eventually (ge_mem_nhds (by linarith :
    (0 : ℝ) < m / 4))).and (t3.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 2)))).and
    (t4.eventually (ge_mem_nhds (by linarith : (0 : ℝ) < goal / 4)))).and
    (eventually_ge_atTop (max (max (Real.exp 1) (1 / η)) 1)) |>.exists
  have hSe : Real.exp 1 ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE1
  have hSη : 1 / η ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE1
  have hS1 : 1 ≤ S := le_trans (le_max_right _ _) hE1
  have hS0 : 0 < S := by linarith
  have h1S : 1 / S ≤ η := by
    rw [div_le_iff₀ hS0]; rw [div_le_iff₀ hη0] at hSη; linarith
  set R := Real.log S with hR
  have hR1 : 1 ≤ R := by rw [hR, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hSe
  have hR0 : 0 ≤ R := by linarith
  set f := twistTest 0 τ₀ R S with hf
  have hfd : ContDiff ℝ 2 f := contDiff_twistTest 0 τ₀ R S
  have hfs : tsupport f ⊆ Icc (-(3 * R + S)) (3 * R + S) := tsupport_twistTest hS0
  have hzero : ∀ z : ℂ, paperFT (weilRadicalTest R) z = 0 → paperFT f z = 0 := fun z hz => by
    rw [paperFT_twistTest_factor hS0, hz, zero_mul]
  have hp := hzero _ (paperFT_weilRadicalTest_half_I R)
  have hm' := hzero _ (paperFT_weilRadicalTest_neg_half_I R)
  have hεR : (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) ≤
      E₀ * C₆ * Real.exp (1 / 4) / S := by
    refine (riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR1 (by norm_num)).trans (le_of_eq ?_)
    rw [show -(R - 1 / 4) = 1 / 4 + -R by ring, Real.exp_add, Real.exp_neg, hR,
      Real.exp_log hS0]
    field_simp
  have happrox : 3 * B ^ 2 * ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ) ≤
      m / 4 := by
    refine le_trans ?_ hE2
    have : (∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ ≤
        E₀ * C₆ * Real.exp (1 / 4) / S * Aκ := mul_le_mul_of_nonneg_right hεR hAκ0
    calc 3 * B ^ 2 * ((∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|)) * Aκ)
        ≤ 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) / S * Aκ) := by gcongr
      _ = 3 * B ^ 2 * (E₀ * C₆ * Real.exp (1 / 4) * Aκ) / S := by ring
  have hsed : SuperExpDecay f := ⟨hfd.continuous, fun c' =>
    (hfd.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (a := 3 * R + S) fun u hu =>
        twistTest_eq_zero hS0 hu).norm.mul_right⟩
  have hHc : Continuous fun τ : ℝ => paperFT f τ :=
    hsed.differentiable_paperFT.continuous.comp Complex.continuous_ofReal
  have hHm : AEStronglyMeasurable (fun τ : ℝ => paperFT f τ) volume := hHc.aestronglyMeasurable
  have hF := integrable_normSq_paperFT hfd hfs
  have hDc : Continuous D := (continuous_perturbationSymbol hsum).neg
  have hDbd : ∀ τ, |D τ| ≤ CD * (1 + |τ - τ₀|) := fun τ => by
    rw [hDdef, abs_neg]
    have h1 := abs_perturbationSymbol_le hsum τ
    have h2 : 0 ≤ |τ - τ₀| := abs_nonneg _
    nlinarith
  have hint : Integrable fun τ : ℝ => ‖paperFT f τ‖ ^ 2 * D τ := by
    refine (hF.mul_const CD).mono' ((hHc.norm.pow 2).mul hDc).aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [hDdef, abs_neg]; exact abs_perturbationSymbol_le hsum τ
  have hconc := concentrated_integral_lower (H := fun τ : ℝ => paperFT f τ) (D := D)
    (t := -1) (τ₀ := τ₀) (η := η) (S := S) (d₁ := d₁) (L := L₀ * S) (K₁ := B ^ 3) (Cκ := Cκ)
    (CD := CD) hS1 hη0 h1S hd₁0 (by positivity) hCD0 (by positivity) hCκ0 hHm hint
    (fun τ hτ => by rw [hDdef]; simp only [neg_mul, one_mul, neg_neg]; exact (hnear τ hτ).1)
    (fun τ hτ => by
      have := norm_paperFT_twistTest_real_ge (α := 0) (R := R) hS0 hτ
        (hnear τ (hτ.trans h1S)).2 happrox
      rw [hL₀]; convert this using 1; ring)
    (fun τ => norm_paperFT_twistTest_real_le hS0 hCκ τ)
    hDbd
  have hmain : d₁ / 2 * (2 / S * (L₀ * S) ^ 2) -
      |(-1 : ℝ)| * ((B ^ 3) ^ 2 * Cκ ^ 4 * CD / (S ^ 2 * η ^ 4)) * I₃ =
      2 * goal * S - Ctail / S ^ 2 := by
    rw [hgoal, hCtail]; field_simp
  rw [hmain] at hconc
  have hE4' : Ctail / S ^ 2 ≤ goal / 2 * S := by
    have := mul_le_mul_of_nonneg_right hE4 hS0.le
    calc Ctail / S ^ 2 = Ctail / S ^ 3 * S := by field_simp
      _ ≤ goal / 2 * S := this
  have hDneg : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ ≤ -(3 / 2 * goal * S) := by linarith
  have hWS : 2 * π * ‖zetaZeroConfig.W f f‖ ≤ goal / 4 * S := by
    have h := (hKW S hSe).1
    have hπ : 0 < π := Real.pi_pos
    calc 2 * π * ‖zetaZeroConfig.W f f‖ ≤ 2 * π * (KW * S ^ 10 * Real.exp (-S)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * π * KW * (S ^ 9 * Real.exp (-S)) * S := by ring
      _ ≤ goal / 4 * S := mul_le_mul_of_nonneg_right hE5 hS0.le
  -- choosing the level
  set MH := ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 with hMH
  have hMH0 : 0 ≤ MH := integral_nonneg fun _ => sq_nonneg _
  have hlev : Tendsto (fun a : ℝ => ⌊Real.exp (2 * a)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have htail := (tendsto_weight_tail w).comp hlev
  have hgS : 0 < goal * S := by positivity
  have hev : ∀ᶠ a : ℝ in atTop,
      (2 * ∑' k : ℕ, |w (k + (⌊Real.exp (2 * a)⌋₊ + 1))| /
        Real.sqrt (k + (⌊Real.exp (2 * a)⌋₊ + 1) : ℕ)) * MH ≤ goal / 4 * S := by
    have := (htail.mul_const MH)
    simp only [zero_mul] at this
    exact this.eventually (ge_mem_nhds (by positivity))
  obtain ⟨a, haS, ha⟩ := (hev.and (eventually_ge_atTop (3 * R + S))).exists
  have hfsa : tsupport f ⊆ Icc (-a) a := hfs.trans (Icc_subset_Icc (by linarith) ha)
  refine ⟨a, by linarith, f, hfd, hfsa, hp, hm', ?_⟩
  have hbound := integral_weilAtomSymbol_vonMangoldt_add_le hsum hfd hfsa hp hm'
  have hPD : ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * perturbationSymbol w τ =
      -∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * D τ := by
    rw [← integral_neg]; congr 1; funext τ; simp only [hDdef]; ring
  rw [hPD] at hbound
  linarith


/-- **Weil positivity is rigid under summable perturbations of `Λ`.**  If
`Σ_{n ≥ 2} |w(n)| n^{-1/2} < ∞` and `w(n₀) ≠ 0` for some `n₀ ≥ 2`, then the weights `Λ(n) + w(n)`
are not Weil-positive: some polar-constrained `C²` test at some level has negative symbol energy.

The perturbation symbol `P_w(τ) = Σ 2w(n) n^{-1/2} cos(τ log n)` is positive somewhere
(`eq_zero_of_perturbationSymbol_nonpos`).  Spread radical tests concentrated there have zero side
`O(S^{10} e^{-S})` for `ζ`, so the energy is `-∫ |h|² P_w + o(S) < 0`. -/
theorem vonMangoldt_add_summable_not_weilPositive (hsum : Summable fun n => |w n| / Real.sqrt n)
    {n₀ : ℕ} (hn₀ : 2 ≤ n₀) (hw : w n₀ ≠ 0) :
    ¬ (∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + w n) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) := by
  intro hpos
  have hex : ∃ τ₁, 0 < perturbationSymbol w τ₁ := by
    by_contra h
    push Not at h
    exact hw (eq_zero_of_perturbationSymbol_nonpos hsum h hn₀)
  obtain ⟨τ₁, hτ₁⟩ := hex
  have hPc := continuous_perturbationSymbol hsum
  set d₁ := perturbationSymbol w τ₁ with hd₁
  obtain ⟨η₁, hη₁0, hη₁⟩ := Metric.continuousAt_iff.mp
    (hPc.continuousAt (x := τ₁)) (d₁ / 2) (by linarith)
  have hnear₁ : ∀ τ : ℝ, |τ - τ₁| < η₁ → d₁ / 2 ≤ perturbationSymbol w τ := by
    intro τ hτ
    have := hη₁ (show dist τ τ₁ < η₁ by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).1
    linarith
  have hev := ((eventually_radicalLimit_shift_ne_zero 0 τ₁).and
    (nhdsWithin_le_nhds (Metric.ball_mem_nhds τ₁ (half_pos hη₁0))))
  obtain ⟨τ₀, h0, hball⟩ := hev.exists
  have hτ₀ : |τ₀ - τ₁| < η₁ / 2 := by rw [Real.dist_eq] at hball; exact hball
  have hlim0 : twistLimit 0 τ₀ ≠ 0 := by
    unfold twistLimit
    simp only [Complex.ofReal_zero, add_zero, neg_zero] at h0 ⊢
    exact mul_ne_zero (mul_ne_zero h0 h0) h0
  set m := ‖twistLimit 0 τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hlim0
  obtain ⟨η₂, hη₂0, hη₂⟩ := Metric.continuousAt_iff.mp
    ((continuous_twistLimit_real 0).continuousAt (x := τ₀)) (m / 2) (by linarith)
  set η := min (η₁ / 2) (η₂ / 2) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hnear : ∀ τ : ℝ, |τ - τ₀| ≤ η →
      d₁ / 2 ≤ perturbationSymbol w τ ∧ m / 2 ≤ ‖twistLimit 0 τ‖ := by
    intro τ hτ
    constructor
    · refine hnear₁ τ ?_
      have : |τ - τ₁| ≤ |τ - τ₀| + |τ₀ - τ₁| := by
        calc |τ - τ₁| = |(τ - τ₀) + (τ₀ - τ₁)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have := min_le_left (η₁ / 2) (η₂ / 2)
      linarith
    · have hd : dist τ τ₀ < η₂ := by
        rw [Real.dist_eq]; have := min_le_right (η₁ / 2) (η₂ / 2); linarith
      have := hη₂ hd
      rw [dist_eq_norm] at this
      have := norm_sub_norm_le (twistLimit 0 τ₀) (twistLimit 0 τ)
      rw [norm_sub_rev] at this
      linarith
  obtain ⟨a, ha, f, hfd, hfs, hp, hm', hneg⟩ :=
    vonMangoldt_add_violation_of_concentration hsum hη0 hm0 hτ₁ hnear
  linarith [hpos a ha f hfd hfs hp hm']

/-- **Weil positivity determines the prime weights within `Λ + ℓ¹(n^{-1/2})`.**  If `lam` is
Weil-positive and `Σ_{n ≥ 2} |lam(n) - Λ(n)| n^{-1/2} < ∞`, then `lam(n) = Λ(n)` for all `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositive_of_summable_sub {lam : ℕ → ℝ}
    (hsum : Summable fun n => |lam n - Λ n| / Real.sqrt n)
    (hpos : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {n : ℕ} (hn : 2 ≤ n) : lam n = Λ n := by
  by_contra hne
  have hlam : (fun k => (Λ k : ℝ) + (lam k - Λ k)) = lam := by funext k; ring
  refine vonMangoldt_add_summable_not_weilPositive (w := fun k => lam k - Λ k) hsum hn
    (sub_ne_zero.mpr hne) ?_
  rw [hlam]; exact hpos

/-- **A single prime weight cannot be changed.**  For `n₀ ≥ 2` and `c ≠ 0`, the weights equal to
`Λ(n)` for `n ≠ n₀` and to `Λ(n₀) + c` at `n₀` are not Weil-positive. -/
theorem vonMangoldt_update_not_weilPositive {n₀ : ℕ} (hn₀ : 2 ≤ n₀) {c : ℝ} (hc : c ≠ 0) :
    ¬ (∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (Λ n : ℝ) + if n = n₀ then c else 0)
          ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) := by
  have hsum : Summable fun n : ℕ => |(if n = n₀ then c else 0)| / Real.sqrt n := by
    refine summable_of_ne_finset_zero (s := {n₀}) fun n hn => ?_
    rw [Finset.mem_singleton] at hn
    simp [hn]
  exact vonMangoldt_add_summable_not_weilPositive (w := fun n => if n = n₀ then c else 0) hsum hn₀
    (by simp [hc])

/-- **Weil-positive weights lie in a box.**  There is `C₀` such that every Weil-positive weight
system satisfies `|lam(n)| ≤ √n (log n + C₀)` for all `n ≥ 2`.  The two-point resonator vectors
`1_{m = 1} ± 1_{m = n}` have multiplicative diagonal `±1_{· = n}`, so the Weil–Toeplitz bound reads
`± 2 lam(n) n^{-1/2} ≤ 2(log n + C₀)`. -/
theorem abs_le_of_weilPositive {lam : ℕ → ℝ}
    (hW : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) :
    ∃ C₀ : ℝ, ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Real.sqrt n * (Real.log n + C₀) := by
  obtain ⟨C₀, hC₀⟩ := weil_multiplicativeToeplitz_bound hW
  refine ⟨C₀, fun n₀ hn₀ => ?_⟩
  have hsq : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * lam n₀ ≤ Real.sqrt n₀ * (Real.log n₀ + C₀) := by
    intro s hs
    have hc : ∀ m, n₀ < m → twoPointCoeff n₀ (s : ℂ) m = 0 := by
      intro m hm; unfold twoPointCoeff; rw [if_neg (by omega), if_neg (by omega)]
    have h := hC₀ n₀ (by omega) (twoPointCoeff n₀ (s : ℂ)) hc
    have hdiag : ∀ n ∈ Finset.Icc 2 n₀, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 n₀, twoPointCoeff n₀ (s : ℂ) (n * m) *
          conj (twoPointCoeff n₀ (s : ℂ) m)).re = if n = n₀ then lam n₀ / Real.sqrt n₀ * s else 0 := by
      intro n hn
      rw [twoPointCoeff_diag hn₀ _ (Finset.mem_Icc.mp hn).1]
      split_ifs with h' <;> simp [h']
    rw [Finset.sum_congr rfl hdiag, Finset.sum_ite_eq'] at h
    rw [if_pos (Finset.mem_Icc.mpr ⟨hn₀, le_rfl⟩)] at h
    have hnorm : ∑ m ∈ Finset.Icc 1 n₀, ‖twoPointCoeff n₀ (s : ℂ) m‖ ^ 2 = 2 := by
      have hpt : ∀ m ∈ Finset.Icc 1 n₀, ‖twoPointCoeff n₀ (s : ℂ) m‖ ^ 2 =
          (if m = 1 then 1 else 0) + (if m = n₀ then 1 else 0) := by
        intro m _
        unfold twoPointCoeff
        by_cases h1 : m = 1
        · subst h1; simp; omega
        · by_cases h2 : m = n₀
          · subst h2; rcases hs with rfl | rfl <;> simp [h1]
          · simp [h1, h2]
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.sum_ite_eq']
      rw [if_pos (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩),
        if_pos (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]; norm_num
    rw [hnorm] at h
    have : s * lam n₀ = Real.sqrt n₀ * (lam n₀ / Real.sqrt n₀ * s) := by field_simp
    rw [this]
    have h' : lam n₀ / Real.sqrt n₀ * s ≤ Real.log n₀ + C₀ := by linarith
    exact mul_le_mul_of_nonneg_left h' hsq.le
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

end RHTower
