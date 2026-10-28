import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheSharpMultiplicativeHardyInequality

/-!
# The stability regime reaches a fixed fraction of the Robin–Euler threshold

With the one-sided cross penalty (`TheArchimedeanCrossEnergyIsOneSided`) and the sharp Hardy
inequality (`TheSharpMultiplicativeHardyInequality`), the argument of `ThePoleDefectPaysThePole`
runs with constants of order ten instead of a thousand.

* **The pole rows of a window test** (`abs_poleRows_windowTest_le`):
  `|A| ≤ √w Σ y_n n^{−1/2}` and `|B| ≤ e^{w/2} √w Σ y_n √n`.
* **The sharp pole bound** (`two_mul_abs_poleMoments_windowTest_le_split`): for every `ρ' > 0`,
  `2|AB| ≤ w e^{w/2} (ρ'(1 + log N)|y|² + ((1 + θ)E_N D_N(y) + (1 + 1/θ)((1 + ζ)U_N + 1 + 1/ζ)|y|²)/ρ')`.
* **The weights are asymptotically sharp** (`eventually_edgeWeight_le`, `eventually_upWeight_le`):
  `E_N ≤ (1/(2b) + η) N²/log N` and `(1 + ζ)U_N + 1 + 1/ζ ≤ ((1 + ζ)B_ψ²/b² + η) N²/log N`,
  eventually in `N`, for every fixed `0 < b < 1`.
* **Weil positivity at a fixed fraction of the Robin–Euler threshold**
  (`eventually_weilQuad_windowTest_nonneg_sharp`): with `λ = 1/2`, `κ = 1/10`, `b = 9/10`, `θ = 4`,
  `ζ = 1/10`, `ρ = 4`, eventually in `N`, Weil's form is nonnegative on every window test of shape
  `β(G_n) ≥ β‖G_n‖²` at every width `w ≤ K★_sharp(β, ε, a) δ_N`,
  `K★_sharp = min(1/10, a/C_X, exp(2θ′(0) + 2c_∞ + β + γ − ε − a − 1/100))`, `C_X ≈ 24`.
  For plateau profiles (`β → 1`) and `a = 3/2` this is `≈ 0.06` of the spacing; for arbitrary
  profiles (`β = 0`) it is `≈ 0.03`. The threshold `K★ ≈ 6·10⁻⁴` of `ThePoleDefectPaysThePole` came
  from constants `1517` and `107`, which are now `16` and `8`.
-/

noncomputable section

open MeasureTheory Finset Filter Asymptotics RHTower
open scoped Topology

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {G : ℕ → ℝ → ℝ} {w : ℝ}

/-! ### The pole rows -/

/-- **The pole rows of a window test**: `|A| ≤ √w Σ y_n n^{−1/2}`, `|B| ≤ e^{w/2} √w Σ y_n √n`. -/
theorem abs_poleRows_windowTest_le (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) (N : ℕ) :
    |∫ u, windowTest N G u * Real.exp (-(u / 2))| ≤
        Real.sqrt w * ∑ n ∈ Icc 1 N, windowNorm G n * Real.exp (-(Real.log n / 2)) ∧
      |∫ u, windowTest N G u * Real.exp (u / 2)| ≤
        Real.exp (w / 2) * Real.sqrt w * ∑ n ∈ Icc 1 N, windowNorm G n * Real.sqrt n := by
  set y := windowNorm G
  set sw := Real.sqrt w
  constructor
  · rw [integral_windowTest_mul hG hGsupp (by fun_prop), mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    have h := abs_integral_shift_mul_le (hG n).continuous (hasCompactSupport_profile hGsupp n)
      (hGsupp n) (φ := fun u => Real.exp (-(u / 2))) (by fun_prop) (c := Real.log n)
      (M := Real.exp (-(Real.log n / 2))) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by linarith [hu.1])
    have h2 := integral_abs_profile_le hG hGsupp hw0 n
    calc _ ≤ Real.exp (-(Real.log n / 2)) * ∫ u, |G n u| := h
      _ ≤ Real.exp (-(Real.log n / 2)) * (sw * y n) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = sw * (y n * Real.exp (-(Real.log n / 2))) := by ring
  · rw [integral_windowTest_mul hG hGsupp (by fun_prop), mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hsq : Real.exp (Real.log n / 2) = Real.sqrt n := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, exp_half_log_sq hn1]
    have h := abs_integral_shift_mul_le (hG n).continuous (hasCompactSupport_profile hGsupp n)
      (hGsupp n) (φ := fun u => Real.exp (u / 2)) (by fun_prop) (c := Real.log n)
      (M := Real.exp (Real.log n / 2) * Real.exp (w / 2)) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [hu.2])
    rw [hsq] at h
    have h2 := integral_abs_profile_le hG hGsupp hw0 n
    calc _ ≤ Real.sqrt n * Real.exp (w / 2) * ∫ u, |G n u| := h
      _ ≤ Real.sqrt n * Real.exp (w / 2) * (sw * y n) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp (w / 2) * sw * (y n * Real.sqrt n) := by ring

/-- **The sharp pole bound.** For `N ≥ 2` and `b, θ, ζ, ρ' > 0`,
`2|AB| ≤ w e^{w/2} (ρ'(1 + log N)|y|² + ((1 + θ)E_N D + (1 + 1/θ)((1 + ζ)U_N + 1 + 1/ζ)|y|²)/ρ')`. -/
theorem two_mul_abs_poleMoments_windowTest_le_split (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) {N : ℕ} (hN : 2 ≤ N) {b θ ζ ρ' : ℝ}
    (hb0 : 0 < b) (hθ : 0 < θ) (hζ : 0 < ζ) (hρ : 0 < ρ') :
    2 * |(∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)| ≤
      w * Real.exp (w / 2) * (ρ' * (1 + Real.log N) * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 +
        ((1 + θ) * edgeWeight N b * poleDefect N (windowNorm G) +
          (1 + 1 / θ) * ((1 + ζ) * upWeight N b + (1 + 1 / ζ)) *
            ∑ n ∈ Icc 1 N, windowNorm G n ^ 2) / ρ') := by
  set y := windowNorm G
  set X := ∑ n ∈ Icc 1 N, y n ^ 2
  set S₁ := ∑ n ∈ Icc 1 N, y n * Real.exp (-(Real.log n / 2))
  set S₂ := ∑ n ∈ Icc 1 N, y n * Real.sqrt n
  obtain ⟨hA, hB⟩ := abs_poleRows_windowTest_le hG hGsupp hw0 N
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hy0 : ∀ n, 0 ≤ y n := windowNorm_nonneg G
  have hS₁0 : 0 ≤ S₁ := sum_nonneg fun n _ => mul_nonneg (hy0 n) (Real.exp_pos _).le
  have hS₂0 : 0 ≤ S₂ := sum_nonneg fun n _ => mul_nonneg (hy0 n) (Real.sqrt_nonneg _)
  have hsw : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw0.le
  -- the `H`-row by Cauchy–Schwarz
  have hS₁ : S₁ ^ 2 ≤ (1 + Real.log N) * X := by
    have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) y (fun n => Real.exp (-(Real.log n / 2)))
    have hharm : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
      have h := harmonic_le_one_add_log N
      simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
      simpa only [one_div] using h
    have e2 : ∑ n ∈ Icc 1 N, Real.exp (-(Real.log n / 2)) ^ 2 = ∑ n ∈ Icc 1 N, (1 : ℝ) / n :=
      sum_congr rfl fun n hn => exp_neg_half_log_sq (Finset.mem_Icc.mp hn).1
    rw [e2] at h
    nlinarith [mul_le_mul_of_nonneg_left hharm hX]
  -- the `V`-row by the sharp Hardy inequality
  have hS₂ : S₂ ^ 2 ≤ (1 + θ) * edgeWeight N b * poleDefect N y +
      (1 + 1 / θ) * ((1 + ζ) * upWeight N b + (1 + 1 / ζ)) * X := by
    have h := sq_vRow_le_split hN hb0 hθ hζ y
    have e1 : ∑ n ∈ Icc 1 N, Real.sqrt n * y n = S₂ := sum_congr rfl fun n _ => mul_comm _ _
    rwa [e1] at h
  -- `2|AB| ≤ 2 w e^{w/2} S₁ S₂ ≤ w e^{w/2} (ρ' S₁² + S₂²/ρ')`
  have hAB : 2 * |(∫ u, windowTest N G u * Real.exp (-(u / 2))) *
      ∫ u, windowTest N G u * Real.exp (u / 2)| ≤ 2 * (w * Real.exp (w / 2)) * (S₁ * S₂) := by
    rw [abs_mul]
    have := mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have e : Real.sqrt w * S₁ * (Real.exp (w / 2) * Real.sqrt w * S₂) =
        w * Real.exp (w / 2) * (S₁ * S₂) := by
      calc Real.sqrt w * S₁ * (Real.exp (w / 2) * Real.sqrt w * S₂) =
          (Real.sqrt w * Real.sqrt w) * (Real.exp (w / 2) * (S₁ * S₂)) := by ring
        _ = w * Real.exp (w / 2) * (S₁ * S₂) := by rw [hsw]; ring
    linarith
  have hamgm : 2 * (S₁ * S₂) ≤ ρ' * S₁ ^ 2 + S₂ ^ 2 / ρ' := by
    have h : ρ' * S₁ ^ 2 + S₂ ^ 2 / ρ' - 2 * (S₁ * S₂) = (ρ' * S₁ - S₂) ^ 2 / ρ' := by
      field_simp; ring
    have : 0 ≤ (ρ' * S₁ - S₂) ^ 2 / ρ' := div_nonneg (sq_nonneg _) hρ.le
    linarith
  have hwe : 0 ≤ w * Real.exp (w / 2) := by positivity
  have h1 : ρ' * S₁ ^ 2 + S₂ ^ 2 / ρ' ≤ ρ' * ((1 + Real.log N) * X) +
      ((1 + θ) * edgeWeight N b * poleDefect N y +
        (1 + 1 / θ) * ((1 + ζ) * upWeight N b + (1 + 1 / ζ)) * X) / ρ' := by
    gcongr
  calc _ ≤ 2 * (w * Real.exp (w / 2)) * (S₁ * S₂) := hAB
    _ = w * Real.exp (w / 2) * (2 * (S₁ * S₂)) := by ring
    _ ≤ w * Real.exp (w / 2) * (ρ' * S₁ ^ 2 + S₂ ^ 2 / ρ') :=
        mul_le_mul_of_nonneg_left hamgm hwe
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (h1.trans (le_of_eq ?_)) hwe
        ring

/-! ### The weights are asymptotically sharp -/

/-- `N^b log N ≤ c N` eventually, for `b < 1` and `c > 0`. -/
theorem eventually_rpow_mul_log_le {b c : ℝ} (hb : b < 1) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ b * Real.log N ≤ c * N := by
  have h := (isLittleO_log_rpow_atTop (show 0 < 1 - b by linarith)).bound hc
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
    eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  rw [Real.norm_of_nonneg hL, Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _)] at hN
  have hb0 : 0 ≤ (N : ℝ) ^ b := Real.rpow_nonneg hN0.le b
  calc (N : ℝ) ^ b * Real.log N ≤ (N : ℝ) ^ b * (c * (N : ℝ) ^ (1 - b)) :=
        mul_le_mul_of_nonneg_left hN hb0
    _ = c * ((N : ℝ) ^ b * (N : ℝ) ^ (1 - b)) := by ring
    _ = c * N := by rw [← Real.rpow_add hN0, add_sub_cancel, Real.rpow_one]

/-- **The edge weight is asymptotically sharp**: `E_N ≤ (1/(2b) + η) N²/log N` eventually. -/
theorem eventually_edgeWeight_le {b η : ℝ} (hb0 : 0 < b) (hb : b < 1) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, edgeWeight N b ≤ (1 / (2 * b) + η) * ((N : ℝ) ^ 2 / Real.log N) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_rpow_mul_log_le hb (show 0 < η * Real.log 2 / 2 by positivity),
    eventually_ge_atTop (⌈1 / (b * η)⌉₊ + 2)] with N h1 h2
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hNbη : 1 ≤ b * η * N := by
    have h := Nat.le_ceil (1 / (b * η))
    have : (⌈1 / (b * η)⌉₊ : ℝ) ≤ N := by exact_mod_cast (show ⌈1 / (b * η)⌉₊ ≤ N by omega)
    rw [div_le_iff₀ (by positivity)] at h
    nlinarith [mul_le_mul_of_nonneg_right this (mul_pos hb0 hη).le]
  unfold edgeWeight
  -- the two parts
  have e1 : (N : ℝ) * (N + 1) / (2 * b * Real.log N) ≤
      (1 / (2 * b) + η / 2) * ((N : ℝ) ^ 2 / Real.log N) := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 / (2 * b) + η / 2) * ((N : ℝ) ^ 2 / Real.log N) * (2 * b * Real.log N) =
        (1 + b * η) * N ^ 2 := by field_simp
    rw [this]
    nlinarith
  have e2 : (N : ℝ) * ((N : ℝ) ^ b / Real.log 2) ≤ η / 2 * ((N : ℝ) ^ 2 / Real.log N) := by
    rw [show (N : ℝ) * ((N : ℝ) ^ b / Real.log 2) = N * (N : ℝ) ^ b / Real.log 2 by ring,
      div_le_iff₀ hl2, show η / 2 * ((N : ℝ) ^ 2 / Real.log N) * Real.log 2 =
        N * (η * Real.log 2 / 2 * N) / Real.log N by ring, le_div_iff₀ hL]
    nlinarith [mul_le_mul_of_nonneg_left h1 hN0.le]
  nlinarith

/-- `(c + q)²(1 + δ) ≤ c² + δ(c² + 4c + 2)` for `0 ≤ q ≤ δ ≤ 1`, `c ≥ 0`. -/
theorem sq_add_mul_le {c q δ : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) (hqδ : q ≤ δ) (hδ1 : δ ≤ 1) :
    (c + q) ^ 2 * (1 + δ) ≤ c ^ 2 + δ * (c ^ 2 + 4 * c + 2) := by
  have hδ0 : 0 ≤ δ := hq.trans hqδ
  have h1 : (c + q) ^ 2 ≤ (c + δ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 + δ), mul_nonneg hδ0 hδ0,
    mul_nonneg (mul_nonneg hδ0 hδ0) hδ0, mul_nonneg hc hδ0, mul_nonneg (mul_nonneg hc hδ0) hδ0]

/-- **The up-row weight is asymptotically sharp**:
`(1 + ζ)U_N + 1 + 1/ζ ≤ ((1 + ζ) B_ψ²/b² + η) N²/log N` eventually. -/
theorem eventually_upWeight_le {b ζ η : ℝ} (hb0 : 0 < b) (hb : b < 1) (hζ : 0 < ζ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (1 + ζ) * upWeight N b + (1 + 1 / ζ) ≤
      ((1 + ζ) * (psiConstant / b) ^ 2 + η) * ((N : ℝ) ^ 2 / Real.log N) := by
  set c := psiConstant / b
  have hc : 0 ≤ c := div_nonneg psiConstant_pos.le hb0.le
  set K := (1 + ζ) * (c ^ 2 + 4 * c + 2) + 1
  have hK : 0 < K := by positivity
  set δ := min 1 (η / K)
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδK : δ * K ≤ η := by
    have := min_le_right 1 (η / K)
    rw [le_div_iff₀ hK] at this; exact this
  filter_upwards [eventually_rpow_mul_log_le hb hδ0,
    eventually_ge_atTop (⌈Real.exp (1 / δ)⌉₊ + ⌈(1 + 1 / ζ) / δ⌉₊ + 2)] with N h1 h2
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  -- `1/log N ≤ δ`
  have hLδ : 1 / Real.log N ≤ δ := by
    have hexp : Real.exp (1 / δ) ≤ N := by
      have := Nat.le_ceil (Real.exp (1 / δ))
      have : (⌈Real.exp (1 / δ)⌉₊ : ℝ) ≤ N := by exact_mod_cast (show _ ≤ N by omega)
      linarith
    have : 1 / δ ≤ Real.log N := by
      rw [← Real.log_exp (1 / δ)]; exact Real.log_le_log (Real.exp_pos _) hexp
    rw [div_le_iff₀ hL]; rw [div_le_iff₀ hδ0] at this; linarith
  -- `(1 + 1/ζ) log N/N² ≤ δ`
  have hcst : (1 + 1 / ζ) * Real.log N / N ^ 2 ≤ δ := by
    have hN : (1 + 1 / ζ) / δ ≤ N := by
      have := Nat.le_ceil ((1 + 1 / ζ) / δ)
      have : (⌈(1 + 1 / ζ) / δ⌉₊ : ℝ) ≤ N := by exact_mod_cast (show _ ≤ N by omega)
      linarith
    have hlogN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hδ0] at hN
    have hζ' : 0 ≤ 1 + 1 / ζ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogN hζ']
  -- `q = N^b log N/N ≤ δ`
  set q := (N : ℝ) ^ b * Real.log N / N
  have hq0 : 0 ≤ q := by positivity
  have hqδ : q ≤ δ := by simp only [q]; rw [div_le_iff₀ hN0]; exact h1
  -- `U_N = (N²/log N)(c + q)²(1 + 1/log N)`
  have hU : upWeight N b = (N ^ 2 / Real.log N) * ((c + q) ^ 2 * (1 + 1 / Real.log N)) := by
    simp only [upWeight, c, q]
    field_simp
    ring
  have hmain := sq_add_mul_le hc hq0 hqδ hδ1
  have hmono : (c + q) ^ 2 * (1 + 1 / Real.log N) ≤ (c + q) ^ 2 * (1 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  set Q := (N : ℝ) ^ 2 / Real.log N
  have hQ : 0 < Q := by positivity
  have hcQ : 1 + 1 / ζ ≤ δ * Q := by
    simp only [Q]
    rw [mul_div_assoc', le_div_iff₀ hL]
    rw [div_le_iff₀ (by positivity)] at hcst
    linarith
  rw [hU]
  have h3 : (1 + ζ) * (Q * ((c + q) ^ 2 * (1 + 1 / Real.log N))) ≤
      (1 + ζ) * (Q * (c ^ 2 + δ * (c ^ 2 + 4 * c + 2))) := by
    gcongr; linarith
  have h4 : (1 + ζ) * (Q * (c ^ 2 + δ * (c ^ 2 + 4 * c + 2))) + δ * Q =
      Q * ((1 + ζ) * c ^ 2 + δ * K) := by simp only [K]; ring
  nlinarith [mul_le_mul_of_nonneg_left hδK hQ.le]

/-! ### Weil positivity at a fixed fraction of the Robin–Euler threshold -/

/-- The edge constant `1/(2b) + η` at `b = 9/10`, `η = 1/100`. -/
def sharpCE : ℝ := 1 / (2 * (9 / 10)) + 1 / 100

/-- The up-row constant `(1 + ζ)B_ψ²/b² + η` at `b = 9/10`, `ζ = 1/10`, `η = 1/100`. -/
def sharpCU : ℝ := (1 + 1 / 10) * (psiConstant / (9 / 10)) ^ 2 + 1 / 100

/-- The pole cost on `|y|²`, `e^{1/100}(ρ(1 + η) + (1 + 1/θ) C_U/ρ)` at `θ = 4`, `ρ = 4`. -/
def sharpPoleX : ℝ := Real.exp (1 / 100) * (4 * (1 + 1 / 100) + (1 + 1 / 4) * sharpCU / 4)

/-- The pole cost on the defect, `e^{1/100}(1 + θ) C_E/ρ`. -/
def sharpPoleD : ℝ := Real.exp (1 / 100) * ((1 + 4) * sharpCE / 4)

/-- The linear cost on `|y|²`: cross penalty at `λ = 1/2`, `κ = 1/10`, plus the pole. -/
def sharpCostX : ℝ := crossConstant (1 / 2) (1 / 10) + sharpPoleX

/-- The linear cost on the defect. -/
def sharpCostD : ℝ := 2 * (1 + 1 / (1 / 2)) / (1 - 1 / 10) + sharpPoleD

/-- The fraction `K★_sharp(β, ε, a)` of the spacing. -/
def sharpFraction (β ε a : ℝ) : ℝ :=
  min (min (1 / 10) (1 / (2 * sharpCostD)))
    (min (a / sharpCostX)
      (Real.exp (2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25)))

theorem sharpCE_pos : 0 < sharpCE := by unfold sharpCE; norm_num

theorem sharpCU_pos : 0 < sharpCU := by unfold sharpCU; positivity

theorem sharpCostX_pos : 0 < sharpCostX := by
  unfold sharpCostX sharpPoleX crossConstant
  have := psiConstant_pos
  have := sharpCU_pos
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  positivity

theorem sharpCostD_pos : 0 < sharpCostD := by
  unfold sharpCostD sharpPoleD; have := sharpCE_pos; positivity

theorem sharpFraction_pos (β ε a : ℝ) (ha : 0 < a) : 0 < sharpFraction β ε a := by
  have := sharpCostX_pos
  have := sharpCostD_pos
  unfold sharpFraction
  exact lt_min (lt_min (by norm_num) (by positivity)) (lt_min (by positivity) (Real.exp_pos _))

/-- **The pole bound at the sharp constants**: if `log N ≥ 100`, the two weights obey their
asymptotic bounds and `w ≤ 1/50`, then `2|AB| ≤ wN (sharpPoleX |y|² + sharpPoleD D_N(y))`. -/
theorem two_mul_abs_poleMoments_windowTest_le_sharp (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) (hw : w ≤ 1 / 50) {N : ℕ}
    (hN : 2 ≤ N) (hLN : 100 ≤ Real.log N)
    (hEN : edgeWeight N (9 / 10) ≤ sharpCE * ((N : ℝ) ^ 2 / Real.log N))
    (hUN : (1 + 1 / 10) * upWeight N (9 / 10) + (1 + 1 / (1 / 10)) ≤
      sharpCU * ((N : ℝ) ^ 2 / Real.log N)) :
    2 * |(∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)| ≤
      w * N * (sharpPoleX * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 +
        sharpPoleD * poleDefect N (windowNorm G)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := by linarith
  have hP := two_mul_abs_poleMoments_windowTest_le_split hG hGsupp hw0 hN
    (b := 9 / 10) (θ := 4) (ζ := 1 / 10) (ρ' := 4 * N / Real.log N) (by norm_num) (by norm_num)
    (by norm_num) (by positivity)
  set X := ∑ n ∈ Icc 1 N, windowNorm G n ^ 2
  set D := poleDefect N (windowNorm G)
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N _
  set Q := (N : ℝ) ^ 2 / Real.log N
  have hρ : 0 < 4 * N / Real.log N := by positivity
  have hstuff : (1 + 4) * edgeWeight N (9 / 10) * D +
      (1 + 1 / 4) * ((1 + 1 / 10) * upWeight N (9 / 10) + (1 + 1 / (1 / 10))) * X ≤
      ((1 + 4) * sharpCE * D + (1 + 1 / 4) * sharpCU * X) * Q := by
    have h1 : (1 + 4) * edgeWeight N (9 / 10) * D ≤ (1 + 4) * (sharpCE * Q) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEN (by norm_num)) hD
    have h2 : (1 + 1 / 4) * ((1 + 1 / 10) * upWeight N (9 / 10) + (1 + 1 / (1 / 10))) * X ≤
        (1 + 1 / 4) * (sharpCU * Q) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUN (by norm_num)) hX
    linarith
  have hdiv : ((1 + 4) * edgeWeight N (9 / 10) * D +
      (1 + 1 / 4) * ((1 + 1 / 10) * upWeight N (9 / 10) + (1 + 1 / (1 / 10))) * X) /
        (4 * N / Real.log N) ≤ ((1 + 4) * sharpCE * D + (1 + 1 / 4) * sharpCU * X) * N / 4 := by
    rw [div_le_iff₀ hρ]
    have e : ((1 + 4) * sharpCE * D + (1 + 1 / 4) * sharpCU * X) * N / 4 * (4 * N / Real.log N) =
        ((1 + 4) * sharpCE * D + (1 + 1 / 4) * sharpCU * X) * Q := by
      simp only [Q]; field_simp
    rw [e]; exact hstuff
  have hfirst : 4 * N / Real.log N * (1 + Real.log N) * X ≤ 4 * (1 + 1 / 100) * N * X := by
    refine mul_le_mul_of_nonneg_right ?_ hX
    rw [div_mul_eq_mul_div, div_le_iff₀ hlogN]; nlinarith
  have hexp : Real.exp (w / 2) ≤ Real.exp (1 / 100) := Real.exp_le_exp.mpr (by linarith)
  have hd0 : 0 ≤ N * (4 * (1 + 1 / 100) * X + ((1 + 4) * sharpCE * D +
      (1 + 1 / 4) * sharpCU * X) / 4) := by
    have := sharpCE_pos; have := sharpCU_pos; positivity
  refine hP.trans ?_
  calc w * Real.exp (w / 2) * (4 * N / Real.log N * (1 + Real.log N) * X +
        ((1 + 4) * edgeWeight N (9 / 10) * D +
          (1 + 1 / 4) * ((1 + 1 / 10) * upWeight N (9 / 10) + (1 + 1 / (1 / 10))) * X) /
            (4 * N / Real.log N))
      ≤ w * Real.exp (w / 2) * (N * (4 * (1 + 1 / 100) * X +
          ((1 + 4) * sharpCE * D + (1 + 1 / 4) * sharpCU * X) / 4)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ ≤ w * Real.exp (1 / 100) * (N * (4 * (1 + 1 / 100) * X +
          ((1 + 4) * sharpCE * D + (1 + 1 / 4) * sharpCU * X) / 4)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hw0.le) hd0
    _ = w * N * (sharpPoleX * X + sharpPoleD * D) := by
        simp only [sharpPoleX, sharpPoleD]; ring

/-- **Weil positivity at a fixed fraction of the Robin–Euler threshold.** For `0 < ε ≤ 1/2` and
`a > 0`, eventually in `N`: for every `β`, every width `0 < w ≤ K★_sharp(β, ε, a) δ_N` and every
window test whose profiles have shape term `β(G_n) ≥ β‖G_n‖²`, Weil's form is nonnegative. -/
theorem eventually_weilQuad_windowTest_nonneg_sharp {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {a : ℝ} (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ β w : ℝ, 0 < w → w ≤ sharpFraction β ε a * atomSpacing N →
      ∀ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) → (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) →
      (∀ n, β * ∫ u, G n u ^ 2 ≤ bumpRobin (G n) w) → 0 ≤ weilQuad (windowTest N G) := by
  obtain ⟨N₁, hN₁⟩ := eventually_markovEnergy_windowTest_ge_sharp hε (κ := 1 / 10) (by norm_num)
    (by norm_num) (lam := 1 / 2) (by norm_num)
  have hE := eventually_edgeWeight_le (b := 9 / 10) (η := 1 / 100) (by norm_num) (by norm_num)
    (by norm_num)
  have hU := eventually_upWeight_le (b := 9 / 10) (ζ := 1 / 10) (η := 1 / 100) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hL : ∀ᶠ N : ℕ in atTop, (100 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 100
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hE.and (hU.and (hL.and (eventually_ge_atTop 50))))
  refine ⟨max N₁ N₂, fun N hN β w hw0 hw G hG hGsupp hβ => ?_⟩
  obtain ⟨hEN, hUN, hLN, hN50⟩ := hN₂ N (le_trans (le_max_right _ _) hN)
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδ := atomSpacing_pos hN1
  have hδN : atomSpacing N * N ≤ 1 := by
    have h := atomSpacing_le_inv hN1
    calc atomSpacing N * N ≤ 1 / N * N := mul_le_mul_of_nonneg_right h hN0.le
      _ = 1 := by field_simp
  have hKs := sharpFraction_pos β ε a ha
  have hK1 : sharpFraction β ε a ≤ 1 / 10 := (min_le_left _ _).trans (min_le_left _ _)
  have hK2 : sharpFraction β ε a ≤ 1 / (2 * sharpCostD) := (min_le_left _ _).trans (min_le_right _ _)
  have hK3 : sharpFraction β ε a ≤ a / sharpCostX := (min_le_right _ _).trans (min_le_left _ _)
  have hK4 : sharpFraction β ε a ≤
      Real.exp (2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hKK : w * N ≤ sharpFraction β ε a := by
    calc w * N ≤ sharpFraction β ε a * atomSpacing N * N := mul_le_mul_of_nonneg_right hw hN0.le
      _ = sharpFraction β ε a * (atomSpacing N * N) := by ring
      _ ≤ sharpFraction β ε a * 1 := mul_le_mul_of_nonneg_left hδN hKs.le
      _ = sharpFraction β ε a := mul_one _
  have hK0 : 0 < w * N := by positivity
  have hw10 : w ≤ 1 / 10 * atomSpacing N := hw.trans (mul_le_mul_of_nonneg_right hK1 hδ.le)
  have hwsmall : w ≤ 1 / 500 := by
    have h1 : w * N ≤ 1 / 10 := hKK.trans hK1
    have h2 : (50 : ℝ) ≤ N := by exact_mod_cast hN50
    nlinarith
  have hM := hN₁ N (le_trans (le_max_left _ _) hN) w hw0 hw10 G hG hGsupp β hβ
  have hP := two_mul_abs_poleMoments_windowTest_le_sharp hG hGsupp hw0 (by linarith) (by omega)
    hLN hEN hUN
  -- Weil's form is the Markov form plus the pole term
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  have hW : weilQuad (windowTest N G) = markovEnergy (fun u => (windowTest N G u : ℂ)) +
      2 * ((∫ u, windowTest N G u * Real.exp (-(u / 2))) *
        ∫ u, windowTest N G u * Real.exp (u / 2)) := by
    rw [weilQuad_eq hf hfc, add_sub_assoc, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc,
      markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
    ring
  rw [hW]
  -- the two coefficients beat the pole costs
  have hc₀ : sharpPoleD * (w * N) ≤ 1 - ε - 2 * (1 + 1 / (1 / 2)) / (1 - 1 / 10) * (w * N) := by
    have h := mul_le_mul_of_nonneg_left (hKK.trans hK2) sharpCostD_pos.le
    have e : sharpCostD * (1 / (2 * sharpCostD)) = 1 / 2 := by
      have := sharpCostD_pos; field_simp
    rw [e] at h
    unfold sharpCostD at h
    linarith
  have hφ₀ : sharpPoleX * (w * N) ≤ 2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) +
      archRobinConstant + β + γ - ε - Real.exp (1 / 2) / 2 * w -
      crossConstant (1 / 2) (1 / 10) * (w * N) := by
    have hlog : -(2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25) ≤
        Real.log (1 / (w * N)) := by
      have h6 : Real.log (w * N) ≤
          2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25 := by
        have := Real.log_le_log hK0 (hKK.trans hK4)
        rwa [Real.log_exp] at this
      have e : Real.log (1 / (w * N)) = -Real.log (w * N) := by
        rw [one_div (w * (N : ℝ)), Real.log_inv]
      rw [e]
      linarith
    have hcost : sharpCostX * (w * N) ≤ a := by
      have h := mul_le_mul_of_nonneg_left (hKK.trans hK3) sharpCostX_pos.le
      have e : sharpCostX * (a / sharpCostX) = a := by
        have := sharpCostX_pos; field_simp
      rwa [e] at h
    have hew : Real.exp (1 / 2) / 2 * w ≤ 1 / 25 := by
      have := exp_half_lt_two
      nlinarith
    unfold sharpCostX at hcost
    linarith
  set X := ∑ n ∈ Icc 1 N, windowNorm G n ^ 2
  set D := poleDefect N (windowNorm G)
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N _
  set P := (∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)
  have hPabs := neg_abs_le P
  have h1 := mul_nonneg hX (sub_nonneg.mpr hφ₀)
  have h2 := mul_nonneg hD (sub_nonneg.mpr hc₀)
  linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms eventually_weilQuad_windowTest_nonneg_sharp
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms two_mul_abs_poleMoments_windowTest_le_sharp
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms eventually_upWeight_le
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms eventually_edgeWeight_le
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms levyEnergy_windowTest_ge_sharp
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms sq_vRow_le_split
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms eventually_markovEnergy_windowTest_ge_sharp
