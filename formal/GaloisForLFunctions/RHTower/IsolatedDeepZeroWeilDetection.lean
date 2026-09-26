import Zeta23.WeilEF.ZeroSummability
import Zeta23.ExplicitFormula
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# An isolated deep zero violates level-`a` Weil positivity

Let `Z` be a zero configuration whose local count satisfies `N(t, t+1] ≤ A₀ log(|t| + 3)`, and let
`ρ₀ = ½ + δ + iγ₀` be a zero of depth `δ > 0`.  Test the Weil form
`W(f, f) = Σ_ρ m_ρ h_f(γ_ρ) conj(h_f(conj γ_ρ))` with `f(u) = e^{-iγ₀u} s(u)`, where `s` is real,
odd, `C²` and supported in `[-a, a]`.

* **The deep pair.**  Since `s` is odd, `ŝ(∓iδ) = ±P` with `P = ∫ s(u) sinh(δu)`, and `ρ₀`, `1 - ρ̄₀`
  each contribute `-m_{ρ₀}P²`.
* **Every other zero.**  Uniform decay of `ŝ` gives `|m_ρ ŝ(x)ŝ(x̄)| ≤ 16 m_ρ e^{2|β-½|a} N²/(1 + |γ - γ₀|)⁴`
  with `N = ‖s‖₁ + ‖s''‖₁`.  On-line zeros within distance `R` carry no exponential factor, and
  far zeros carry at most `e^a/(1 + R)` after trading one power of the distance.
* **Summation.**  Unit windows of the local count give `Σ_ρ m_ρ(1 + |γ - γ₀|)^{-3} ≤ 24 A₀ log(|γ₀| + 3)`.

The **isolation inequality** is
`Re W ≤ -2 m_{ρ₀} P² + 384 A₀ log(|γ₀| + 3) N² (1 + e^a/(1 + R))`.  With the explicit test
`s(u) = sinh(δu)(a² - u²)₊^{5/2}`, bounds on `N` and `P` turn it into an elementary sufficient
condition for negativity.  Contrapositively, Weil positivity at level `a` forces every
sufficiently deep zero to have another off-line zero within ordinate distance `R`.  This is
stated for `ζ` with the unconditional local zero count.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-- Modulation by `e^{-iγ₀u}` translates the Fourier variable by `γ₀`. -/
theorem paperFT_modulate (c : ℝ → ℂ) (γ₀ : ℝ) (z : ℂ) :
    paperFT (fun u => cexp (-(I * γ₀ * u)) * c u) z = paperFT c (z - γ₀) := by
  rw [paperFT_def, paperFT_def]
  congr 1 with u
  rw [mul_comm (cexp _) (c u), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem integral_odd_mul_cosh {s : ℝ → ℝ} (hodd : ∀ u, s (-u) = -s u) (δ : ℝ) :
    ∫ u, s u * Real.cosh (δ * u) = 0 := by
  have h := integral_neg_eq_self (fun u => s u * Real.cosh (δ * u)) volume
  simp only [hodd, mul_neg, Real.cosh_neg, neg_mul] at h
  rw [integral_neg] at h
  linarith

/-- For an odd real test, `∫ s(u) e^{δu} = ∫ s(u) sinh(δu)`. -/
theorem integral_odd_mul_exp {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) (δ : ℝ) :
    ∫ u, s u * Real.exp (δ * u) = ∫ u, s u * Real.sinh (δ * u) := by
  have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hsupp
  have hi1 : Integrable (fun u => s u * Real.cosh (δ * u)) :=
    (hs.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have hi2 : Integrable (fun u => s u * Real.sinh (δ * u)) :=
    (hs.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have h : (fun u => s u * Real.exp (δ * u)) =
      fun u => s u * Real.cosh (δ * u) + s u * Real.sinh (δ * u) := by
    funext u; rw [← mul_add, Real.cosh_add_sinh]
  rw [h, integral_add hi1 hi2, integral_odd_mul_cosh hodd, zero_add]

theorem integral_odd_mul_exp_neg {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) (δ : ℝ) :
    ∫ u, s u * Real.exp (-(δ * u)) = -∫ u, s u * Real.sinh (δ * u) := by
  have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hsupp
  have hi1 : Integrable (fun u => s u * Real.cosh (δ * u)) :=
    (hs.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have hi2 : Integrable (fun u => s u * Real.sinh (δ * u)) :=
    (hs.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hcs.mul_right
  have h : (fun u => s u * Real.exp (-(δ * u))) =
      fun u => s u * Real.cosh (δ * u) - s u * Real.sinh (δ * u) := by
    funext u; rw [← mul_sub, Real.cosh_sub_sinh]
  rw [h, integral_sub hi1 hi2, integral_odd_mul_cosh hodd, zero_sub]

/-- The transform of an odd real test at `-iδ` is `P = ∫ s(u) sinh(δu)`. -/
theorem paperFT_odd_neg_I_mul {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) (δ : ℝ) :
    paperFT (fun u => (s u : ℂ)) (-(I * δ)) = ((∫ u, s u * Real.sinh (δ * u) : ℝ) : ℂ) := by
  rw [paperFT_def, ← integral_odd_mul_exp hs hsupp hodd δ, ← integral_complex_ofReal]
  congr 1 with u
  have hI : I * I = -1 := Complex.I_mul_I
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  linear_combination (-(δ : ℂ) * u) * hI

/-- The transform of an odd real test at `iδ` is `-P`. -/
theorem paperFT_odd_I_mul {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) (δ : ℝ) :
    paperFT (fun u => (s u : ℂ)) (I * δ) = -((∫ u, s u * Real.sinh (δ * u) : ℝ) : ℂ) := by
  rw [paperFT_def, ← Complex.ofReal_neg, ← integral_odd_mul_exp_neg hs hsupp hodd δ,
    ← integral_complex_ofReal]
  congr 1 with u
  have hI : I * I = -1 := Complex.I_mul_I
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  linear_combination ((δ : ℂ) * u) * hI

/-- Uniform decay of a compactly supported `C²` transform:
`‖ĉ(x)‖ ≤ e^{|Im x| a} · 4(‖c‖₁ + ‖c''‖₁) / (1 + |Re x|)²`. -/
theorem norm_paperFT_le_decay {c : ℝ → ℂ} {a : ℝ} (hc : ContDiff ℝ 2 c)
    (hsupp : ∀ u, c u ≠ 0 → |u| ≤ a) (x : ℂ) :
    ‖paperFT c x‖ ≤ Real.exp (|x.im| * a) *
      (4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖)) / (1 + |x.re|) ^ 2 := by
  have hcs := hasCompactSupport_of_support_subset_abs hsupp
  have h0 := norm_paperFT_le (hc.continuous.integrable_of_hasCompactSupport hcs) hsupp x
  have h2 := norm_paperFT_mul_sq_le hc hsupp x
  set E := Real.exp (|x.im| * a) with hE
  set N₁ := ∫ u, ‖c u‖ with hN₁
  set N₂ := ∫ u, ‖deriv (deriv c) u‖ with hN₂
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun _ => norm_nonneg _
  have hN₂0 : 0 ≤ N₂ := integral_nonneg fun _ => norm_nonneg _
  have hE0 : 0 < E := Real.exp_pos _
  rw [le_div_iff₀ (by positivity)]
  have hre : |x.re| ≤ ‖x‖ := Complex.abs_re_le_norm x
  have hF0 := norm_nonneg (paperFT c x)
  rcases le_or_gt |x.re| 1 with h | h
  · have h4 : (1 + |x.re|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg x.re]
    calc ‖paperFT c x‖ * (1 + |x.re|) ^ 2 ≤ ‖paperFT c x‖ * 4 :=
          mul_le_mul_of_nonneg_left h4 hF0
      _ ≤ E * N₁ * 4 := by nlinarith
      _ ≤ E * (4 * (N₁ + N₂)) := by nlinarith
  · have h4 : (1 + |x.re|) ^ 2 ≤ 4 * ‖x‖ ^ 2 := by nlinarith
    calc ‖paperFT c x‖ * (1 + |x.re|) ^ 2 ≤ ‖paperFT c x‖ * (4 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 hF0
      _ = 4 * (‖paperFT c x‖ * ‖x‖ ^ 2) := by ring
      _ ≤ 4 * (E * N₂) := by linarith
      _ ≤ E * (4 * (N₁ + N₂)) := by nlinarith

theorem hasSum_inv_one_add_abs_sq :
    HasSum (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ 2) (π ^ 2 / 3 - 1) := by
  have h1 : HasSum (fun k : ℕ => 1 / (1 + |((k : ℤ) : ℝ)|) ^ 2) (π ^ 2 / 6) := by
    have e1 : (fun k : ℕ => 1 / (1 + |((k : ℤ) : ℝ)|) ^ 2) =
        fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
      funext k
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg k)]
      push_cast
      ring
    have e2 : π ^ 2 / 6 - ∑ i ∈ Finset.range 1, 1 / (i : ℝ) ^ 2 = π ^ 2 / 6 := by simp
    rw [e1, ← e2]
    exact (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have h2 : HasSum (fun k : ℕ => 1 / (1 + |((-((k : ℤ) + 1) : ℤ) : ℝ)|) ^ 2)
      (π ^ 2 / 6 - 1) := by
    have e1 : (fun k : ℕ => 1 / (1 + |((-((k : ℤ) + 1) : ℤ) : ℝ)|) ^ 2) =
        fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ) ^ 2 := by
      funext k
      have hk : |((-((k : ℤ) + 1) : ℤ) : ℝ)| = (k : ℝ) + 1 := by
        rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg,
          abs_of_nonneg (by positivity)]
      rw [hk]
      push_cast
      ring
    have e2 : π ^ 2 / 6 - ∑ i ∈ Finset.range 2, 1 / (i : ℝ) ^ 2 = π ^ 2 / 6 - 1 := by
      simp [Finset.sum_range_succ]
    rw [e1, ← e2]
    exact (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  have h := HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ 2) h1 h2
  rwa [show π ^ 2 / 6 + (π ^ 2 / 6 - 1) = π ^ 2 / 3 - 1 by ring] at h

theorem one_le_log_abs_add_three (x : ℝ) : 1 ≤ Real.log (|x| + 3) := by
  rw [← Real.log_exp 1]
  apply Real.log_le_log (Real.exp_pos 1)
  have := Real.exp_one_lt_d9
  linarith [abs_nonneg x]

/-- Unit-window summation of a local zero count against the weight `(1 + |γ - γ₀|)^{-3}`. -/
theorem window_tsum_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (γ₀ : ℝ) :
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3) ∧
      ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 ≤
        24 * A₀ * Real.log (|γ₀| + 3) := by
  classical
  have hLC := Tail.LocalCount.ofWindowCount Z hA₀ hloc
  set L₀ := Real.log (|γ₀| + 3) with hL₀
  have hL₀1 : 1 ≤ L₀ := one_le_log_abs_add_three γ₀
  have hS := hasSum_inv_one_add_abs_sq
  have hpi : π ^ 2 / 3 - 1 ≤ 3 := by
    have := Real.pi_lt_d2
    have hp : 0 < π := Real.pi_pos
    nlinarith
  have hnonneg : 0 ≤ fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hfin : ∀ s : Finset Z.carrier,
      ∑ ρ ∈ s, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 ≤ 8 * A₀ * L₀ * (π ^ 2 / 3 - 1) := by
    intro s
    set κ : Z.carrier → ℤ := fun ρ => WeilEF.key ((ρ : ℂ).im - γ₀) with hκ
    rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
      (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
    have hfiber : ∀ n ∈ s.image κ,
        ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 ≤
          8 * A₀ * L₀ * (1 / (1 + |(n : ℝ)|) ^ 2) := by
      intro n _
      have hwin := hLC.window (γ₀ + n) (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        have h1 := WeilEF.key_lt ((ρ : ℂ).im - γ₀)
        have h2 := WeilEF.le_key_add_one ((ρ : ℂ).im - γ₀)
        rw [show WeilEF.key ((ρ : ℂ).im - γ₀) = n from hρ.2] at h1 h2
        constructor <;> linarith)
      have hlog : Real.log (|γ₀ + n| + 3) ≤ L₀ * (1 + |(n : ℝ)|) := by
        have hpos : 0 < |γ₀| + 3 := by positivity
        have h1 : |γ₀ + n| + 3 ≤ (|γ₀| + 3) * (1 + |(n : ℝ)|) := by
          have := abs_add_le γ₀ (n : ℝ)
          nlinarith [abs_nonneg γ₀, abs_nonneg (n : ℝ)]
        have h2 : Real.log (|γ₀ + n| + 3) ≤ L₀ + Real.log (1 + |(n : ℝ)|) := by
          rw [hL₀, ← Real.log_mul hpos.ne' (by positivity)]
          exact Real.log_le_log (by positivity) h1
        have h3 : Real.log (1 + |(n : ℝ)|) ≤ |(n : ℝ)| := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + |(n : ℝ)| by positivity)
          linarith
        nlinarith [abs_nonneg (n : ℝ)]
      have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
          (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3 ≤
            (8 / (1 + |(n : ℝ)|) ^ 3) * (Z.mult ρ : ℝ) := by
        intro ρ hρ
        simp only [Finset.mem_filter] at hρ
        have h1 := WeilEF.key_lt ((ρ : ℂ).im - γ₀)
        have h2 := WeilEF.le_key_add_one ((ρ : ℂ).im - γ₀)
        rw [show WeilEF.key ((ρ : ℂ).im - γ₀) = n from hρ.2] at h1 h2
        set y := (ρ : ℂ).im - γ₀
        have hcmp : 1 + |(n : ℝ)| ≤ 2 * (1 + |y|) := by
          rcases le_or_gt 0 (n : ℝ) with hn | hn
          · rw [abs_of_nonneg hn]
            have : (n : ℝ) ≤ |y| := by
              rw [abs_of_pos (by linarith)]; linarith
            linarith
          · have hn' : (n : ℝ) ≤ -1 := by
              have : n < 0 := by exact_mod_cast hn
              exact_mod_cast (show n ≤ -1 by omega)
            rw [abs_of_neg hn]
            have : -(n : ℝ) - 1 ≤ |y| := by
              have := neg_abs_le y
              linarith
            linarith
        have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
        have hD : 0 < 1 + |y| := by positivity
        have hcube : (1 + |(n : ℝ)|) ^ 3 ≤ 8 * (1 + |y|) ^ 3 := by
          have h0 : 0 ≤ 1 + |(n : ℝ)| := by positivity
          calc (1 + |(n : ℝ)|) ^ 3 ≤ (2 * (1 + |y|)) ^ 3 := pow_le_pow_left₀ h0 hcmp 3
            _ = 8 * (1 + |y|) ^ 3 := by ring
        rw [div_le_iff₀ (by positivity)]
        calc (Z.mult ρ : ℝ) = (Z.mult ρ : ℝ) * (1 + |(n : ℝ)|) ^ 3 / (1 + |(n : ℝ)|) ^ 3 := by
              field_simp
          _ ≤ (Z.mult ρ : ℝ) * (8 * (1 + |y|) ^ 3) / (1 + |(n : ℝ)|) ^ 3 := by
              gcongr
          _ = 8 / (1 + |(n : ℝ)|) ^ 3 * (Z.mult ρ : ℝ) * (1 + |y|) ^ 3 := by ring
      calc ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3
          ≤ ∑ ρ ∈ s with κ ρ = n, (8 / (1 + |(n : ℝ)|) ^ 3) * (Z.mult ρ : ℝ) :=
            Finset.sum_le_sum hpt
        _ = (8 / (1 + |(n : ℝ)|) ^ 3) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (8 / (1 + |(n : ℝ)|) ^ 3) * (A₀ * Real.log (|γ₀ + n| + 3)) :=
            mul_le_mul_of_nonneg_left hwin (by positivity)
        _ ≤ (8 / (1 + |(n : ℝ)|) ^ 3) * (A₀ * (L₀ * (1 + |(n : ℝ)|))) := by
            gcongr
        _ = 8 * A₀ * L₀ * (1 / (1 + |(n : ℝ)|) ^ 2) := by
            have : (0 : ℝ) < 1 + |(n : ℝ)| := by positivity
            field_simp
    calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n,
          (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3
        ≤ ∑ n ∈ s.image κ, 8 * A₀ * L₀ * (1 / (1 + |(n : ℝ)|) ^ 2) := Finset.sum_le_sum hfiber
      _ = 8 * A₀ * L₀ * ∑ n ∈ s.image κ, 1 / (1 + |(n : ℝ)|) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 8 * A₀ * L₀ * (π ^ 2 / 3 - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_le_hasSum _ (fun n _ => by positivity) hS
  have hsum := summable_of_sum_le hnonneg hfin
  refine ⟨hsum, ?_⟩
  calc ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₀|) ^ 3
      ≤ 8 * A₀ * L₀ * (π ^ 2 / 3 - 1) := hsum.tsum_le_of_sum_le hfin
    _ ≤ 8 * A₀ * L₀ * 3 := by
        apply mul_le_mul_of_nonneg_left hpi
        positivity
    _ = 24 * A₀ * L₀ := by ring

theorem gammaOf_sub_of_re_im {ρ : ℂ} {γ₀ ε : ℝ} (him : ρ.im = γ₀) (hre : ρ.re = 1 / 2 + ε) :
    gammaOf ρ - γ₀ = -(I * ε) ∧ conj (gammaOf ρ) - γ₀ = I * ε := by
  constructor
  · apply Complex.ext
    · simp [WeilEF.gammaOf_re, him]
    · simp [WeilEF.gammaOf_im, hre]
  · apply Complex.ext
    · simp [WeilEF.gammaOf_re, him]
    · simp [WeilEF.gammaOf_im, hre]

/-- The test `e^{-iγ₀u} s(u)`, localizing the Weil form at the ordinate `γ₀`. -/
def modulatedTest (γ₀ : ℝ) (s : ℝ → ℝ) : ℝ → ℂ := fun u => cexp (-(I * γ₀ * u)) * (s u : ℂ)

/-- `‖s‖₁ + ‖s''‖₁`. -/
def testNorm (s : ℝ → ℝ) : ℝ :=
  (∫ u, ‖(s u : ℂ)‖) + ∫ u, ‖deriv (deriv (fun u => (s u : ℂ))) u‖

theorem testNorm_nonneg (s : ℝ → ℝ) : 0 ≤ testNorm s :=
  add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

theorem Wsummand_modulatedTest (Z : ZeroConfig) (γ₀ : ℝ) (s : ℝ → ℝ) (ρ : ℂ) :
    Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ =
      (Z.mult ρ : ℂ) * paperFT (fun u => (s u : ℂ)) (gammaOf ρ - γ₀) *
        conj (paperFT (fun u => (s u : ℂ)) (conj (gammaOf ρ) - γ₀)) := by
  rw [ZeroConfig.Wsummand]
  unfold modulatedTest
  rw [paperFT_modulate, paperFT_modulate]

theorem norm_Wsummand_modulatedTest_le (Z : ZeroConfig) (γ₀ : ℝ) {s : ℝ → ℝ} {a : ℝ}
    (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (ρ : ℂ) :
    ‖Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ‖ ≤
      (Z.mult ρ : ℝ) * (Real.exp (|1 / 2 - ρ.re| * a) ^ 2 * (16 * testNorm s ^ 2)) /
        (1 + |ρ.im - γ₀|) ^ 4 := by
  have hS : ContDiff ℝ 2 (fun u => (s u : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  have hSsupp : ∀ u, (fun u => (s u : ℂ)) u ≠ 0 → |u| ≤ a := fun u hu =>
    hsupp u (fun h => hu (by simp [h]))
  have hN := testNorm_nonneg s
  rw [Wsummand_modulatedTest, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast]
  have h1 := norm_paperFT_le_decay hS hSsupp (gammaOf ρ - γ₀)
  have h2 := norm_paperFT_le_decay hS hSsupp (conj (gammaOf ρ) - γ₀)
  have e1 : (gammaOf ρ - γ₀).re = ρ.im - γ₀ := by simp [WeilEF.gammaOf_re]
  have e2 : (gammaOf ρ - γ₀).im = 1 / 2 - ρ.re := by simp [WeilEF.gammaOf_im]
  have e3 : (conj (gammaOf ρ) - γ₀).re = ρ.im - γ₀ := by simp [WeilEF.gammaOf_re]
  have e4 : |(conj (gammaOf ρ) - γ₀).im| = |1 / 2 - ρ.re| := by
    simp only [Complex.sub_im, Complex.conj_im, Complex.ofReal_im, sub_zero, WeilEF.gammaOf_im,
      abs_neg]
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  change _ ≤ Real.exp _ * (4 * testNorm s) / _ at h1 h2
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hD : 0 < 1 + |ρ.im - γ₀| := by positivity
  calc (Z.mult ρ : ℝ) * ‖paperFT (fun u => (s u : ℂ)) (gammaOf ρ - γ₀)‖ *
        ‖paperFT (fun u => (s u : ℂ)) (conj (gammaOf ρ) - γ₀)‖
      ≤ (Z.mult ρ : ℝ) *
          (Real.exp (|1 / 2 - ρ.re| * a) * (4 * testNorm s) / (1 + |ρ.im - γ₀|) ^ 2) *
          (Real.exp (|1 / 2 - ρ.re| * a) * (4 * testNorm s) / (1 + |ρ.im - γ₀|) ^ 2) := by
        gcongr
    _ = (Z.mult ρ : ℝ) * (Real.exp (|1 / 2 - ρ.re| * a) ^ 2 * (16 * testNorm s ^ 2)) /
        (1 + |ρ.im - γ₀|) ^ 4 := by
        field_simp
        ring

theorem exp_abs_half_sub_sq_le {x a : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (ha : 0 ≤ a) :
    Real.exp (|1 / 2 - x| * a) ^ 2 ≤ Real.exp a := by
  rw [sq, ← Real.exp_add, Real.exp_le_exp]
  have : |1 / 2 - x| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  nlinarith

/-- Uniform weight bound for every zero of the strip. -/
theorem norm_Wsummand_modulatedTest_le_weight (Z : ZeroConfig) (γ₀ : ℝ) {s : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) :
    ‖Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ‖ ≤
      (16 * testNorm s ^ 2 * Real.exp a) * ((Z.mult ρ : ℝ) / (1 + |ρ.im - γ₀|) ^ 3) := by
  have hE := exp_abs_half_sub_sq_le (Z.strip ρ hρ) ha
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hN := testNorm_nonneg s
  set D := 1 + |ρ.im - γ₀| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg (ρ.im - γ₀)]
  refine (norm_Wsummand_modulatedTest_le Z γ₀ hs hsupp ρ).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have hD3 : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
  have hD0 : 0 < D ^ 3 := by positivity
  calc (Z.mult ρ : ℝ) * (Real.exp (|1 / 2 - ρ.re| * a) ^ 2 * (16 * testNorm s ^ 2))
      ≤ (Z.mult ρ : ℝ) * (Real.exp a * (16 * testNorm s ^ 2)) := by gcongr
    _ = 16 * testNorm s ^ 2 * Real.exp a * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 3 := by
        field_simp
    _ ≤ 16 * testNorm s ^ 2 * Real.exp a * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 4 := by gcongr

/-- Weight bound for the zeros other than the deep pair, under isolation. -/
theorem norm_Wsummand_modulatedTest_le_isolated (Z : ZeroConfig) (γ₀ : ℝ) {s : ℝ → ℝ}
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R) (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hon : |ρ.im - γ₀| ≤ R → ρ.re = 1 / 2) :
    ‖Z.Wsummand (modulatedTest γ₀ s) (modulatedTest γ₀ s) ρ‖ ≤
      16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) *
        ((Z.mult ρ : ℝ) / (1 + |ρ.im - γ₀|) ^ 3) := by
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hN := testNorm_nonneg s
  set K := 1 + Real.exp a / (1 + R) with hK
  have hR0 : 0 < 1 + R := by linarith
  have hK1 : 1 ≤ K := by
    have : 0 ≤ Real.exp a / (1 + R) := by positivity
    linarith
  set D := 1 + |ρ.im - γ₀| with hD
  have hD1 : 1 ≤ D := by linarith [abs_nonneg (ρ.im - γ₀)]
  have hD0 : 0 < D := by linarith
  refine (norm_Wsummand_modulatedTest_le Z γ₀ hs hsupp ρ).trans ?_
  rw [div_le_iff₀ (by positivity)]
  rcases le_or_gt |ρ.im - γ₀| R with hnear | hfar
  · rw [hon hnear, sub_self, abs_zero, zero_mul, Real.exp_zero, one_pow, one_mul]
    have hD34 : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
    calc (Z.mult ρ : ℝ) * (16 * testNorm s ^ 2)
        ≤ (Z.mult ρ : ℝ) * (16 * testNorm s ^ 2) * K := by
          nlinarith [mul_nonneg hm (by positivity : (0 : ℝ) ≤ 16 * testNorm s ^ 2)]
      _ = 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 3 := by
          field_simp
      _ ≤ 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 4 := by gcongr
  · have hE := exp_abs_half_sub_sq_le (Z.strip ρ hρ) ha
    have hDR : 1 + R ≤ D := by rw [hD]; linarith
    have h1' : Real.exp a / (1 + R) ≤ K := by rw [hK]; linarith
    have h3' : 0 ≤ (Z.mult ρ : ℝ) / D ^ 3 := by positivity
    calc (Z.mult ρ : ℝ) * (Real.exp (|1 / 2 - ρ.re| * a) ^ 2 * (16 * testNorm s ^ 2))
        ≤ (Z.mult ρ : ℝ) * (Real.exp a * (16 * testNorm s ^ 2)) := by gcongr
      _ = 16 * testNorm s ^ 2 * (Real.exp a / (1 + R)) * ((Z.mult ρ : ℝ) / D ^ 3) *
            ((1 + R) * D ^ 3) := by
          field_simp
      _ ≤ 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * ((1 + R) * D ^ 3) := by
          gcongr
      _ ≤ 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * (D * D ^ 3) := by
          gcongr
      _ = 16 * testNorm s ^ 2 * K * ((Z.mult ρ : ℝ) / D ^ 3) * D ^ 4 := by ring

/-- The deep pair `ρ₀ = ½ + δ + iγ₀`, `1 - ρ̄₀` contributes `-m_{ρ₀} P²` each. -/
theorem Wsummand_modulatedTest_deep_pair (Z : ZeroConfig) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    {δ : ℝ} (hre : ρ₀.re = 1 / 2 + δ) {s : ℝ → ℝ} {a : ℝ} (hs : Continuous s)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) (hodd : ∀ u, s (-u) = -s u) :
    Z.Wsummand (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s) ρ₀ =
        ((-((Z.mult ρ₀ : ℝ) * (∫ u, s u * Real.sinh (δ * u)) ^ 2) : ℝ) : ℂ) ∧
      Z.Wsummand (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s) (reflect ρ₀) =
        ((-((Z.mult ρ₀ : ℝ) * (∫ u, s u * Real.sinh (δ * u)) ^ 2) : ℝ) : ℂ) := by
  obtain ⟨g0, g0c⟩ := gammaOf_sub_of_re_im (ρ := ρ₀) (γ₀ := ρ₀.im) rfl hre
  have hre1 : (reflect ρ₀).re = 1 / 2 + -δ := by
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, hre]; ring
  have him1 : (reflect ρ₀).im = ρ₀.im := by
    simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]; ring
  obtain ⟨g1, g1c⟩ := gammaOf_sub_of_re_im him1 hre1
  rw [Complex.ofReal_neg, mul_neg, neg_neg] at g1
  rw [Complex.ofReal_neg, mul_neg] at g1c
  have hPpos := paperFT_odd_neg_I_mul hs hsupp hodd δ
  have hPneg := paperFT_odd_I_mul hs hsupp hodd δ
  constructor
  · rw [Wsummand_modulatedTest, g0, g0c, hPpos, hPneg]
    simp only [map_neg, Complex.conj_ofReal]
    push_cast
    ring
  · rw [Wsummand_modulatedTest, g1, g1c, hPpos, hPneg, Z.mult_reflect ρ₀ hρ₀]
    simp only [Complex.conj_ofReal]
    push_cast
    ring

/-- **Isolation inequality.**  Let `ρ₀ = ½ + δ + iγ₀` be a zero of a configuration with local
count `N(t, t+1] ≤ A₀ log(|t| + 3)`, and suppose every other zero with `|γ - γ₀| ≤ R` lies on the
critical line.  For every real odd `C²` test `s` supported in `[-a, a]`, the modulated test
`e^{-iγ₀u} s(u)` satisfies
`Re W ≤ -2 m_{ρ₀} P² + 384 A₀ log(|γ₀| + 3) N² (1 + e^a/(1 + R))`,
with `P = ∫ s(u) sinh(δu)` and `N = ‖s‖₁ + ‖s''‖₁`. -/
theorem re_W_modulatedTest_le_of_isolated (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R : ℝ} (ha : 0 ≤ a) (hR : 0 ≤ R)
    (hiso : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R → ρ.re = 1 / 2)
    {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s) (hodd : ∀ u, s (-u) = -s u)
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) :
    (Z.W (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s)).re ≤
      -2 * Z.mult ρ₀ * (∫ u, s u * Real.sinh (δ * u)) ^ 2 +
        384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) := by
  classical
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc ρ₀.im
  have hsumm : Summable (fun ρ : Z.carrier =>
      Z.Wsummand (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s) ρ) :=
    Summable.of_norm_bounded (hwsum.mul_left _) fun ρ =>
      norm_Wsummand_modulatedTest_le_weight Z ρ₀.im ha hs hsupp ρ.2
  obtain ⟨hval0, hval1⟩ := Wsummand_modulatedTest_deep_pair Z hρ₀ hre hs.continuous hsupp hodd
  set Q : ℝ := (Z.mult ρ₀ : ℝ) * (∫ u, s u * Real.sinh (δ * u)) ^ 2 with hQ
  set ρ₀ₛ : Z.carrier := ⟨ρ₀, hρ₀⟩ with hρ₀ₛ
  set ρ₁ₛ : Z.carrier := ⟨reflect ρ₀, Z.reflect_mem ρ₀ hρ₀⟩ with hρ₁ₛ
  have hne : ρ₁ₛ ≠ ρ₀ₛ := by
    intro h
    have := congrArg (fun x : Z.carrier => (x : ℂ).re) h
    simp only [hρ₀ₛ, hρ₁ₛ, reflect, Complex.sub_re, Complex.one_re, Complex.conj_re, hre] at this
    linarith
  set F : Z.carrier → ℝ := fun ρ =>
    (Z.Wsummand (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s) ρ).re with hF
  set c : Z.carrier → ℝ := fun ρ =>
    16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) *
      ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - ρ₀.im|) ^ 3) with hc
  have hN := testNorm_nonneg s
  have hR0 : 0 < 1 + R := by linarith
  have hc0 : ∀ ρ, 0 ≤ c ρ := fun ρ => by
    have : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    simp only [hc]
    positivity
  have hgc : ∀ ρ, F ρ + (if ρ = ρ₀ₛ then Q else 0) + (if ρ = ρ₁ₛ then Q else 0) ≤ c ρ := by
    intro ρ
    by_cases h0 : ρ = ρ₀ₛ
    · rw [h0, if_pos rfl, if_neg hne.symm]
      simp only [hF]
      rw [show ((ρ₀ₛ : Z.carrier) : ℂ) = ρ₀ from rfl, hval0, Complex.ofReal_re]
      linarith [hc0 ρ₀ₛ]
    by_cases h1 : ρ = ρ₁ₛ
    · rw [h1, if_neg hne, if_pos rfl]
      simp only [hF]
      rw [show ((ρ₁ₛ : Z.carrier) : ℂ) = reflect ρ₀ from rfl, hval1, Complex.ofReal_re]
      linarith [hc0 ρ₁ₛ]
    rw [if_neg h0, if_neg h1, add_zero, add_zero]
    have hρ0 : (ρ : ℂ) ≠ ρ₀ := fun h => h0 (Subtype.ext h)
    have hρ1 : (ρ : ℂ) ≠ reflect ρ₀ := fun h => h1 (Subtype.ext h)
    exact (Complex.re_le_norm _).trans (norm_Wsummand_modulatedTest_le_isolated Z ρ₀.im ha hR
      hs hsupp ρ.2 (hiso ρ ρ.2 hρ0 hρ1))
  have hre_sum : Summable F := (Complex.hasSum_re hsumm.hasSum).summable
  have hi0 := hasSum_ite_eq ρ₀ₛ Q
  have hi1 := hasSum_ite_eq ρ₁ₛ Q
  have hgsum : Summable (fun ρ => F ρ + (if ρ = ρ₀ₛ then Q else 0) +
      (if ρ = ρ₁ₛ then Q else 0)) := (hre_sum.add hi0.summable).add hi1.summable
  have hcsum : Summable c := hwsum.mul_left _
  have htg : ∑' ρ, (F ρ + (if ρ = ρ₀ₛ then Q else 0) + (if ρ = ρ₁ₛ then Q else 0)) =
      (∑' ρ, F ρ) + Q + Q := by
    rw [Summable.tsum_add (hre_sum.add hi0.summable) hi1.summable,
      Summable.tsum_add hre_sum hi0.summable, hi0.tsum_eq, hi1.tsum_eq]
  have htc : ∑' ρ, c ρ ≤ 16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) *
      (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by
    rw [hc, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hwle (by positivity)
  have hle := Summable.tsum_le_tsum hgc hgsum hcsum
  have hW : (Z.W (modulatedTest ρ₀.im s) (modulatedTest ρ₀.im s)).re = ∑' ρ, F ρ := by
    rw [ZeroConfig.W, Complex.re_tsum hsumm]
  rw [hW]
  have : ∑' ρ, F ρ ≤ -2 * Q + 16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) *
      (24 * A₀ * Real.log (|ρ₀.im| + 3)) := by linarith
  calc ∑' ρ, F ρ ≤ -2 * Q + 16 * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) *
        (24 * A₀ * Real.log (|ρ₀.im| + 3)) := this
    _ = -2 * Z.mult ρ₀ * (∫ u, s u * Real.sinh (δ * u)) ^ 2 +
        384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm s ^ 2 * (1 + Real.exp a / (1 + R)) := by
        rw [hQ]; ring

/-! ### An explicit odd test -/

theorem rpow_five_halves_of_neg {x : ℝ} (hx : x < 0) : x ^ (5 / 2 : ℝ) = 0 := by
  rw [Real.rpow_def_of_neg hx]
  have : Real.cos (5 / 2 * π) = 0 := by
    rw [show 5 / 2 * π = π / 2 + 2 * π by ring, Real.cos_add_two_pi, Real.cos_pi_div_two]
  rw [this, mul_zero]

/-- `(a² - u²)₊^{5/2}`, realised as a real power, which vanishes for negative base. -/
def sinhTestWeight (a u : ℝ) : ℝ := (a ^ 2 - u ^ 2) ^ (5 / 2 : ℝ)

/-- The odd test `sinh(δu)(a² - u²)₊^{5/2}`, of class `C²` and supported in `[-a, a]`. -/
def sinhTest (a δ u : ℝ) : ℝ := Real.sinh (δ * u) * sinhTestWeight a u

theorem sinhTest_contDiff (a δ : ℝ) : ContDiff ℝ 2 (sinhTest a δ) := by
  have h52 : ContDiff ℝ 2 (fun x : ℝ => x ^ (5 / 2 : ℝ)) := by
    have := Real.contDiff_rpow_const_of_le (n := 2) (p := 5 / 2) (by norm_num)
    exact_mod_cast this
  have hw : ContDiff ℝ 2 (sinhTestWeight a) :=
    h52.comp (contDiff_const.sub (contDiff_id.pow 2))
  exact ((Real.contDiff_sinh (n := 2)).comp (contDiff_const.mul contDiff_id)).mul hw

theorem sinhTest_odd (a δ u : ℝ) : sinhTest a δ (-u) = -sinhTest a δ u := by
  simp only [sinhTest, sinhTestWeight, mul_neg, Real.sinh_neg, neg_sq, neg_mul]

theorem sinhTest_eq_zero {a δ u : ℝ} (ha : 0 ≤ a) (hu : a < |u|) : sinhTest a δ u = 0 := by
  have h : a ^ 2 - u ^ 2 < 0 := by nlinarith [abs_nonneg u, sq_abs u]
  simp only [sinhTest, sinhTestWeight, rpow_five_halves_of_neg h, mul_zero]

theorem sinhTest_supp {a δ : ℝ} (ha : 0 ≤ a) : ∀ u, sinhTest a δ u ≠ 0 → |u| ≤ a := by
  intro u hu
  by_contra h
  exact hu (sinhTest_eq_zero ha (lt_of_not_ge h))

theorem rpow_sub_sq_le {a u r : ℝ} (ha : 0 ≤ a) (hu : |u| ≤ a) (hr : 0 ≤ r) :
    0 ≤ (a ^ 2 - u ^ 2) ^ r ∧ (a ^ 2 - u ^ 2) ^ r ≤ a ^ (2 * r) := by
  have hp : 0 ≤ a ^ 2 - u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  refine ⟨Real.rpow_nonneg hp r, ?_⟩
  calc (a ^ 2 - u ^ 2) ^ r ≤ (a ^ 2) ^ r :=
        Real.rpow_le_rpow hp (by nlinarith [sq_nonneg u]) hr
    _ = a ^ (2 * r) := by
        rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
        norm_num

theorem abs_sinh_le_cosh_of_abs_le {δ u a : ℝ} (hδ : 0 ≤ δ) (hu : |u| ≤ a) :
    |Real.sinh (δ * u)| ≤ Real.cosh (δ * a) := by
  rw [Real.abs_sinh]
  have h1 : Real.sinh |δ * u| ≤ Real.cosh |δ * u| := (Real.sinh_lt_cosh _).le
  have h2 : Real.cosh |δ * u| ≤ Real.cosh (δ * a) := by
    rw [Real.cosh_abs, Real.cosh_le_cosh, abs_mul, abs_of_nonneg hδ]
    have ha : 0 ≤ a := (abs_nonneg u).trans hu
    rw [abs_mul, abs_of_nonneg hδ, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left hu hδ
  exact h1.trans h2

theorem cosh_mul_le_cosh_mul_of_abs_le {δ u a : ℝ} (hδ : 0 ≤ δ) (hu : |u| ≤ a) :
    Real.cosh (δ * u) ≤ Real.cosh (δ * a) := by
  have ha : 0 ≤ a := (abs_nonneg u).trans hu
  rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_nonneg hδ, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left hu hδ

/-- An integrand bounded by `M` on `[-a, a]` and vanishing outside has integral at most `2aM`. -/
theorem integral_le_of_bound_on_Icc {g : ℝ → ℝ} {a M : ℝ} (ha : 0 ≤ a) (hg0 : ∀ u, 0 ≤ g u)
    (hin : ∀ u, |u| ≤ a → g u ≤ M) (hout : ∀ u, a < |u| → g u = 0) :
    ∫ u, g u ≤ 2 * a * M := by
  have hint : Integrable ((Icc (-a) a).indicator (fun _ => M)) :=
    (integrableOn_const (C := M) (s := Icc (-a) a) (μ := volume) measure_Icc_lt_top.ne
      (by simp)).integrable_indicator
      measurableSet_Icc
  calc ∫ u, g u ≤ ∫ u, (Icc (-a) a).indicator (fun _ => M) u := by
        refine integral_mono_of_nonneg (Eventually.of_forall hg0) hint
          (Eventually.of_forall fun u => ?_)
        by_cases hu : u ∈ Icc (-a) a
        · rw [Set.indicator_of_mem hu]
          exact hin u (abs_le.mpr hu)
        · rw [Set.indicator_of_notMem hu, hout u]
          by_contra h
          exact hu (abs_le.mp (le_of_not_gt h))
    _ = 2 * a * M := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc,
          smul_eq_mul]
        rw [max_eq_left (by linarith)]
        ring

theorem sinhTestWeight_nonneg (a u : ℝ) : 0 ≤ sinhTestWeight a u := by
  rcases le_or_gt 0 (a ^ 2 - u ^ 2) with h | h
  · exact Real.rpow_nonneg h _
  · rw [sinhTestWeight, rpow_five_halves_of_neg h]

theorem hasDerivAt_sub_sq_rpow (a r : ℝ) (hr : 1 ≤ r) (u : ℝ) :
    HasDerivAt (fun u : ℝ => (a ^ 2 - u ^ 2) ^ r) (-(2 * u) * r * (a ^ 2 - u ^ 2) ^ (r - 1)) u := by
  have hp : HasDerivAt (fun u : ℝ => a ^ 2 - u ^ 2) (-(2 * u)) u :=
    ((hasDerivAt_pow 2 u).const_sub (a ^ 2)).congr_deriv (by norm_num)
  exact hp.rpow_const (Or.inr hr)

theorem hasDerivAt_sinh_const_mul (δ u : ℝ) :
    HasDerivAt (fun u => Real.sinh (δ * u)) (Real.cosh (δ * u) * δ) u := by
  exact (((hasDerivAt_id' u).const_mul δ).sinh).congr_deriv (by ring)

theorem hasDerivAt_cosh_const_mul (δ u : ℝ) :
    HasDerivAt (fun u => Real.cosh (δ * u)) (Real.sinh (δ * u) * δ) u := by
  exact (((hasDerivAt_id' u).const_mul δ).cosh).congr_deriv (by ring)

theorem hasDerivAt_sinhTest (a δ u : ℝ) :
    HasDerivAt (sinhTest a δ) (Real.cosh (δ * u) * δ * sinhTestWeight a u +
      Real.sinh (δ * u) * (-(2 * u) * (5 / 2) * (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ))) u := by
  have h1 := hasDerivAt_sinh_const_mul δ u
  have h2 := hasDerivAt_sub_sq_rpow a (5 / 2) (by norm_num) u
  rw [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at h2
  exact h1.mul h2

/-- The second derivative of the explicit test. -/
def sinhTestDeriv2 (a δ u : ℝ) : ℝ :=
  δ ^ 2 * Real.sinh (δ * u) * sinhTestWeight a u +
    2 * δ * Real.cosh (δ * u) * (-(5 * u) * (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ)) +
    Real.sinh (δ * u) *
      (-5 * (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ) + 15 * u ^ 2 * (a ^ 2 - u ^ 2) ^ (1 / 2 : ℝ))

theorem deriv_sinhTest (a δ : ℝ) :
    deriv (sinhTest a δ) = fun u => Real.cosh (δ * u) * δ * sinhTestWeight a u +
      Real.sinh (δ * u) * (-(2 * u) * (5 / 2) * (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ)) :=
  funext fun u => (hasDerivAt_sinhTest a δ u).deriv

theorem hasDerivAt_deriv_sinhTest (a δ u : ℝ) :
    HasDerivAt (deriv (sinhTest a δ)) (sinhTestDeriv2 a δ u) u := by
  rw [deriv_sinhTest]
  have hc := hasDerivAt_cosh_const_mul δ u
  have hs := hasDerivAt_sinh_const_mul δ u
  have hw := hasDerivAt_sub_sq_rpow a (5 / 2) (by norm_num) u
  rw [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at hw
  have h3 := hasDerivAt_sub_sq_rpow a (3 / 2) (by norm_num) u
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at h3
  have hq : HasDerivAt (fun u : ℝ => -(2 * u) * (5 / 2)) (-(2 * 1) * (5 / 2)) u :=
    (((hasDerivAt_id u).const_mul 2).neg).mul_const (5 / 2 : ℝ)
  have hA := (hc.mul_const δ).mul hw
  have hB := hs.mul (hq.mul h3)
  refine (hA.add hB).congr_deriv ?_
  simp only [sinhTestDeriv2, sinhTestWeight, Pi.mul_apply]
  ring

theorem deriv_deriv_sinhTest (a δ : ℝ) :
    deriv (deriv (sinhTest a δ)) = sinhTestDeriv2 a δ :=
  funext fun u => (hasDerivAt_deriv_sinhTest a δ u).deriv

theorem deriv_deriv_ofReal_sinhTest (a δ : ℝ) :
    deriv (deriv (fun u => (sinhTest a δ u : ℂ))) = fun u => ((sinhTestDeriv2 a δ u : ℝ) : ℂ) := by
  have h1 : deriv (fun u => (sinhTest a δ u : ℂ)) = fun u => ((deriv (sinhTest a δ) u : ℝ) : ℂ) :=
    funext fun u => ((hasDerivAt_sinhTest a δ u).ofReal_comp).deriv.trans
      (by rw [(hasDerivAt_sinhTest a δ u).deriv])
  rw [h1]
  funext u
  rw [← deriv_deriv_sinhTest]
  exact ((hasDerivAt_deriv_sinhTest a δ u).ofReal_comp).deriv.trans
    (by rw [deriv_deriv_sinhTest])

theorem abs_sinhTest_le {a δ u : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hu : |u| ≤ a) :
    |sinhTest a δ u| ≤ Real.cosh (δ * a) * a ^ 5 := by
  have hS := abs_sinh_le_cosh_of_abs_le hδ hu
  obtain ⟨hψ0, hψ⟩ := rpow_sub_sq_le ha hu (show (0 : ℝ) ≤ 5 / 2 by norm_num)
  rw [show (2 * (5 / 2) : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hψ
  rw [sinhTest, abs_mul, abs_of_nonneg (sinhTestWeight_nonneg a u)]
  exact mul_le_mul hS hψ hψ0 (Real.cosh_pos _).le

theorem abs_sinhTestDeriv2_le {a δ u : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hu : |u| ≤ a) :
    |sinhTestDeriv2 a δ u| ≤
      Real.cosh (δ * a) * (δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3) := by
  set C := Real.cosh (δ * a) with hC
  have hC0 : 0 < C := Real.cosh_pos _
  have hS := abs_sinh_le_cosh_of_abs_le hδ hu
  have hCo := cosh_mul_le_cosh_mul_of_abs_le hδ hu
  have hco0 := Real.cosh_pos (δ * u)
  obtain ⟨p5a, p5b⟩ := rpow_sub_sq_le ha hu (show (0 : ℝ) ≤ 5 / 2 by norm_num)
  obtain ⟨p3a, p3b⟩ := rpow_sub_sq_le ha hu (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  obtain ⟨p1a, p1b⟩ := rpow_sub_sq_le ha hu (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [show (2 * (5 / 2) : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at p5b
  rw [show (2 * (3 / 2) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at p3b
  rw [show (2 * (1 / 2) : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_one] at p1b
  set ψ := sinhTestWeight a u with hψ
  set p3 := (a ^ 2 - u ^ 2) ^ (3 / 2 : ℝ)
  set p1 := (a ^ 2 - u ^ 2) ^ (1 / 2 : ℝ)
  have hψ5 : ψ ≤ a ^ 5 := p5b
  have hψ0 : 0 ≤ ψ := sinhTestWeight_nonneg a u
  have hu2 : u ^ 2 ≤ a ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  have hua : |u| ≤ a := hu
  have e1 : |δ ^ 2 * Real.sinh (δ * u) * ψ| ≤ δ ^ 2 * C * a ^ 5 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg δ), abs_of_nonneg hψ0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hS (sq_nonneg δ)) hψ5 hψ0 (by positivity)
  have e2 : |2 * δ * Real.cosh (δ * u) * (-(5 * u) * p3)| ≤ 10 * δ * C * a ^ 4 := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg, abs_mul, abs_of_nonneg hδ,
      abs_of_pos hco0, abs_of_nonneg p3a]
    norm_num
    have h5 : |u| * p3 ≤ a * a ^ 3 := mul_le_mul hua p3b p3a ha
    calc 2 * δ * Real.cosh (δ * u) * (5 * |u| * p3)
        = 10 * δ * Real.cosh (δ * u) * (|u| * p3) := by ring
      _ ≤ 10 * δ * C * (a * a ^ 3) := by gcongr
      _ = 10 * δ * C * a ^ 4 := by ring
  have e3 : |Real.sinh (δ * u) * (-5 * p3 + 15 * u ^ 2 * p1)| ≤ C * (20 * a ^ 3) := by
    rw [abs_mul]
    have h1 : |-5 * p3 + 15 * u ^ 2 * p1| ≤ 20 * a ^ 3 := by
      have h2 : |-5 * p3 + 15 * u ^ 2 * p1| ≤ 5 * p3 + 15 * u ^ 2 * p1 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg u]
      have h3 : u ^ 2 * p1 ≤ a ^ 2 * a := mul_le_mul hu2 p1b p1a (sq_nonneg a)
      nlinarith
    exact mul_le_mul hS h1 (abs_nonneg _) hC0.le
  unfold sinhTestDeriv2
  calc |δ ^ 2 * Real.sinh (δ * u) * ψ + 2 * δ * Real.cosh (δ * u) * (-(5 * u) * p3) +
        Real.sinh (δ * u) * (-5 * p3 + 15 * u ^ 2 * p1)|
      ≤ |δ ^ 2 * Real.sinh (δ * u) * ψ + 2 * δ * Real.cosh (δ * u) * (-(5 * u) * p3)| +
          |Real.sinh (δ * u) * (-5 * p3 + 15 * u ^ 2 * p1)| := abs_add_le _ _
    _ ≤ |δ ^ 2 * Real.sinh (δ * u) * ψ| + |2 * δ * Real.cosh (δ * u) * (-(5 * u) * p3)| +
          |Real.sinh (δ * u) * (-5 * p3 + 15 * u ^ 2 * p1)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ δ ^ 2 * C * a ^ 5 + 10 * δ * C * a ^ 4 + C * (20 * a ^ 3) := by gcongr
    _ = C * (δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3) := by ring

theorem sinhTestDeriv2_eq_zero {a δ u : ℝ} (ha : 0 ≤ a) (hu : a < |u|) :
    sinhTestDeriv2 a δ u = 0 := by
  have hopen : IsOpen {v : ℝ | a < |v|} := isOpen_lt continuous_const continuous_abs
  have hev : sinhTest a δ =ᶠ[nhds u] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hopen.mem_nhds hu) fun v hv => sinhTest_eq_zero ha hv
  rw [← deriv_deriv_sinhTest, hev.deriv.deriv_eq]
  simp

/-- `‖s‖₁ + ‖s''‖₁ ≤ 2a cosh(δa)(a⁵ + δ²a⁵ + 10δa⁴ + 20a³)` for the explicit test. -/
theorem testNorm_sinhTest_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    testNorm (sinhTest a δ) ≤
      2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3) := by
  unfold testNorm
  rw [deriv_deriv_ofReal_sinhTest]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have h1 : ∫ u, |sinhTest a δ u| ≤ 2 * a * (Real.cosh (δ * a) * a ^ 5) :=
    integral_le_of_bound_on_Icc ha (fun _ => abs_nonneg _)
      (fun u hu => abs_sinhTest_le ha hδ hu)
      (fun u hu => by rw [sinhTest_eq_zero ha hu, abs_zero])
  have h2 : ∫ u, |sinhTestDeriv2 a δ u| ≤
      2 * a * (Real.cosh (δ * a) * (δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) :=
    integral_le_of_bound_on_Icc ha (fun _ => abs_nonneg _)
      (fun u hu => abs_sinhTestDeriv2_le ha hδ hu)
      (fun u hu => by rw [sinhTestDeriv2_eq_zero ha hu, abs_zero])
  linarith

/-- `∫ s(u) sinh(δu) ≥ w (wa)^{5/2} sinh(δ(a - 2w))²` for `0 < w ≤ a/4`. -/
theorem sinhTest_energy_ge {a δ w : ℝ} (hδ : 0 < δ) (hw : 0 < w) (hwa : w ≤ a / 4) :
    w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 ≤
      ∫ u, sinhTest a δ u * Real.sinh (δ * u) := by
  have ha : 0 < a := by linarith
  set c := (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 with hc
  have hg0 : ∀ u, 0 ≤ sinhTest a δ u * Real.sinh (δ * u) := by
    intro u
    have : sinhTest a δ u * Real.sinh (δ * u) = Real.sinh (δ * u) ^ 2 * sinhTestWeight a u := by
      rw [sinhTest]; ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) (sinhTestWeight_nonneg a u)
  have hcont : Continuous (fun u => sinhTest a δ u * Real.sinh (δ * u)) :=
    (sinhTest_contDiff a δ).continuous.mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hint : Integrable (fun u => sinhTest a δ u * Real.sinh (δ * u)) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    exact (hasCompactSupport_of_support_subset_abs (sinhTest_supp ha.le)).mul_right
  have hsub : ∫ u in Icc (a - 2 * w) (a - w), c ≤
      ∫ u in Icc (a - 2 * w) (a - w), sinhTest a δ u * Real.sinh (δ * u) := by
    refine setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne (by simp))
      hcont.integrableOn_Icc measurableSet_Icc fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := hu
    have hu0 : 0 ≤ u := by linarith
    have hp : w * a ≤ a ^ 2 - u ^ 2 := by nlinarith
    have hψ : (w * a) ^ (5 / 2 : ℝ) ≤ sinhTestWeight a u :=
      Real.rpow_le_rpow (by positivity) hp (by norm_num)
    have hsh0 : 0 ≤ Real.sinh (δ * (a - 2 * w)) :=
      Real.sinh_nonneg_iff.mpr (mul_nonneg hδ.le (by linarith))
    have hsh : Real.sinh (δ * (a - 2 * w)) ≤ Real.sinh (δ * u) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hu1 hδ.le)
    have hsq : Real.sinh (δ * (a - 2 * w)) ^ 2 ≤ Real.sinh (δ * u) ^ 2 :=
      pow_le_pow_left₀ hsh0 hsh 2
    have : sinhTest a δ u * Real.sinh (δ * u) = sinhTestWeight a u * Real.sinh (δ * u) ^ 2 := by
      rw [sinhTest]; ring
    rw [this, hc]
    exact mul_le_mul hψ hsq (sq_nonneg _) (sinhTestWeight_nonneg a u)
  have hle : ∫ u in Icc (a - 2 * w) (a - w), sinhTest a δ u * Real.sinh (δ * u) ≤
      ∫ u, sinhTest a δ u * Real.sinh (δ * u) :=
    setIntegral_le_integral hint (Eventually.of_forall hg0)
  rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
    max_eq_left (by linarith)] at hsub
  have : a - w - (a - 2 * w) = w := by ring
  rw [this] at hsub
  calc w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 = w * c := by rw [hc]; ring
    _ ≤ _ := hsub.trans hle

/-! ### Detection of an isolated deep zero -/

theorem modulatedTest_contDiff (γ₀ : ℝ) {s : ℝ → ℝ} (hs : ContDiff ℝ 2 s) :
    ContDiff ℝ 2 (modulatedTest γ₀ s) := by
  unfold modulatedTest
  have h1 : ContDiff ℝ 2 (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
  have h2 : ContDiff ℝ 2 (fun u : ℝ => -(I * (γ₀ : ℂ) * (u : ℂ))) := (contDiff_const.mul h1).neg
  exact (Complex.contDiff_exp.comp h2).mul (Complex.ofRealCLM.contDiff.comp hs)

theorem tsupport_modulatedTest_subset (γ₀ : ℝ) {s : ℝ → ℝ} {a : ℝ}
    (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) : tsupport (modulatedTest γ₀ s) ⊆ Icc (-a) a :=
  tsupport_subset_of_support_subset_abs fun u hu =>
    hsupp u fun h => hu (by simp [modulatedTest, h])

/-- **An isolated deep zero violates Weil positivity at level `a`.**  Let `ρ₀ = ½ + δ + iγ₀` be a
zero of a configuration with local count `N(t, t+1] ≤ A₀ log(|t| + 3)`, all of whose other zeros
with `|γ - γ₀| ≤ R` lie on the critical line.  If, for some `0 < w ≤ a/4`,
`384 A₀ log(|γ₀| + 3) N_b² (1 + e^a/(1 + R)) < 2 P_b²` with
`N_b = 2a cosh(δa)(a⁵ + δ²a⁵ + 10δa⁴ + 20a³)` and `P_b = w (wa)^{5/2} sinh²(δ(a - 2w))`, then a
`C²` test supported in `[-a, a]` has negative Weil form.  The test is
`e^{-iγ₀u} sinh(δu)(a² - u²)₊^{5/2}`. -/
theorem exists_re_W_neg_of_isolated_deep_zero (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {a R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hiso : ∀ ρ ∈ Z.carrier, ρ ≠ ρ₀ → ρ ≠ reflect ρ₀ → |ρ.im - ρ₀.im| ≤ R → ρ.re = 1 / 2)
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + R)) <
      2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0 := by
  have ha : 0 < a := by linarith
  refine ⟨modulatedTest ρ₀.im (sinhTest a δ), modulatedTest_contDiff _ (sinhTest_contDiff a δ),
    tsupport_modulatedTest_subset _ (sinhTest_supp ha.le), ?_⟩
  have hmaster := re_W_modulatedTest_le_of_isolated Z hA₀ hloc hρ₀ hδ hre ha.le hR hiso
    (sinhTest_contDiff a δ) (sinhTest_odd a δ) (sinhTest_supp ha.le)
  have hP := sinhTest_energy_ge (a := a) hδ hw hwa
  have hN := testNorm_sinhTest_le ha.le hδ.le
  have hN0 := testNorm_nonneg (sinhTest a δ)
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have hPl0 : 0 ≤ w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2 := by positivity
  have hL : 0 ≤ 384 * A₀ * Real.log (|ρ₀.im| + 3) := by
    have := one_le_log_abs_add_three ρ₀.im
    positivity
  have hK : 0 ≤ 1 + Real.exp a / (1 + R) := by positivity
  have hP2 := pow_le_pow_left₀ hPl0 hP 2
  have hN2 := pow_le_pow_left₀ hN0 hN 2
  have h1 : -2 * (Z.mult ρ₀ : ℝ) * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 ≤
      -2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (∫ u, sinhTest a δ u * Real.sinh (δ * u))]
  have h2 : 384 * A₀ * Real.log (|ρ₀.im| + 3) * testNorm (sinhTest a δ) ^ 2 *
        (1 + Real.exp a / (1 + R)) ≤
      384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + R)) := by
    gcongr
  linarith

/-- **Weil positivity forces off-line companions.**  If the Weil form of a configuration with
local count `A₀` is nonnegative on all `C²` tests supported in `[-a, a]`, then every zero
`ρ₀ = ½ + δ + iγ₀` satisfying the size condition of `exists_re_W_neg_of_isolated_deep_zero` has
another off-line zero, different from `1 - ρ̄₀`, within ordinate distance `R`. -/
theorem exists_offLine_companion_of_weil_positive (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a : ℝ}
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    {R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w) (hwa : w ≤ a / 4)
    (hbig : 384 * A₀ * Real.log (|ρ₀.im| + 3) *
        (2 * a * Real.cosh (δ * a) * (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
        (1 + Real.exp a / (1 + R)) <
      2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2) :
    ∃ ρ ∈ Z.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧ ρ.re ≠ 1 / 2 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨f, hf, hfs, hneg⟩ :=
    exists_re_W_neg_of_isolated_deep_zero Z hA₀ hloc hρ₀ hδ hre hR hw hwa h hbig
  exact absurd (hpos f hf hfs) (not_le.mpr hneg)

/-- The companion law for the nontrivial zeros of `ζ`, with the unconditional local count. -/
theorem zeta_weil_positive_forces_offLine_companion :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a : ℝ,
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ (zetaZeroConfig.W f f).re) →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, ∀ δ : ℝ, 0 < δ → ρ₀.re = 1 / 2 + δ →
      ∀ R w : ℝ, 0 ≤ R → 0 < w → w ≤ a / 4 →
        384 * A₀ * Real.log (|ρ₀.im| + 3) *
            (2 * a * Real.cosh (δ * a) *
              (a ^ 5 + δ ^ 2 * a ^ 5 + 10 * δ * a ^ 4 + 20 * a ^ 3)) ^ 2 *
            (1 + Real.exp a / (1 + R)) <
          2 * (w * (w * a) ^ (5 / 2 : ℝ) * Real.sinh (δ * (a - 2 * w)) ^ 2) ^ 2 →
        ∃ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ ∧ ρ ≠ reflect ρ₀ ∧ |ρ.im - ρ₀.im| ≤ R ∧
          ρ.re ≠ 1 / 2 := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun a hpos ρ₀ hρ₀ δ hδ hre R w hR hw hwa hbig =>
    exists_offLine_companion_of_weil_positive zetaZeroConfig hA₀ hloc hpos hρ₀ hδ hre hR hw hwa
      hbig⟩

end RHTower
