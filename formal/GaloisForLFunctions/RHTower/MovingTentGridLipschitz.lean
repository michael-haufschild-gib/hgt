import GaloisForLFunctions.RHTower.TentMellinFactor
import GaloisForLFunctions.HTGeometry.RiemannSumCell

/-!
# Global Lipschitz bound for the truncated moving-tent integrand

The discretization input of `prime-polar-moving-tent-divisor-tomography` §3 (eq. 14–15): the truncated
moving-tent-of-log integrand `g_s(u) = τ_L(log u)·u^{-s}` (with the *truncated* tent `τ_L = tentPos`,
so `g_s ≡ 0` off the support `[1, e^{2L}]`) is Lipschitz on `[0, ∞)`.

The bound is assembled by gluing three pieces at `u = 1` and `u = e^{2L}`: `g_s ≡ 0` on `[0,1]`
(where `log u ≤ 0`), `g_s = gTent` on the support `[1, e^{2L}]` (`gTent_lipschitzOnWith`), and
`g_s ≡ 0` on `[e^{2L}, ∞)` (where `log u ≥ 2L`).  The gluing uses `lipschitzOnWith_of_glue`.  This
global bound feeds `norm_sum_smul_sub_integral_le`, producing the uniform Riemann-sum estimate `(15)`.
-/

open HTGeometry MeasureTheory

namespace RHTower

/-- The truncated moving-tent-of-log integrand `τ_L(log u)·e^{-s·log u}` (`= τ_L(log u)·u^{-s}` for
`u > 0`), using the truncated tent so that it vanishes off `[1, e^{2L}]`. -/
noncomputable def gGridPos (L : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  (tentPos L (Real.log u) : ℂ) * Complex.exp (-s * (Real.log u : ℂ))

/-- The truncated tent vanishes for nonpositive argument. -/
theorem tentPos_eq_zero_of_nonpos (L : ℝ) {x : ℝ} (hx : x ≤ 0) : tentPos L x = 0 := by
  rw [tentPos, tentFn_eq_min, max_eq_left]
  exact le_trans (min_le_left _ _) hx

/-- The truncated tent vanishes past `2L`. -/
theorem tentPos_eq_zero_of_ge (L : ℝ) {x : ℝ} (hx : 2 * L ≤ x) : tentPos L x = 0 := by
  rw [tentPos, tentFn_eq_min, max_eq_left]
  exact le_trans (min_le_right _ _) (by linarith)

/-- `g_s ≡ 0` on `[0, 1]` (there `log u ≤ 0`). -/
theorem gGridPos_eq_zero_of_mem_Icc (L : ℝ) (s : ℂ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    gGridPos L s u = 0 := by
  rw [gGridPos, tentPos_eq_zero_of_nonpos L (Real.log_nonpos hu0 hu1), Complex.ofReal_zero, zero_mul]

/-- `g_s ≡ 0` on `[e^{2L}, ∞)` (there `log u ≥ 2L`). -/
theorem gGridPos_eq_zero_of_ge (L : ℝ) (s : ℂ) {u : ℝ} (hu : Real.exp (2 * L) ≤ u) :
    gGridPos L s u = 0 := by
  have hlu : 2 * L ≤ Real.log u := by
    rw [← Real.log_exp (2 * L)]; exact Real.log_le_log (Real.exp_pos _) hu
  rw [gGridPos, tentPos_eq_zero_of_ge L hlu, Complex.ofReal_zero, zero_mul]

/-- On the support `[1, e^{2L}]` the truncated integrand equals `gTent`. -/
theorem gGridPos_eq_gTent (L : ℝ) (s : ℂ) {u : ℝ} (hu : u ∈ Set.Icc 1 (Real.exp (2 * L))) :
    gGridPos L s u = gTent L s u := by
  have hlog : Real.log u ∈ Set.Icc 0 (2 * L) := by
    refine ⟨Real.log_nonneg hu.1, ?_⟩
    rw [← Real.log_exp (2 * L)]; exact Real.log_le_log (by linarith [hu.1]) hu.2
  rw [gGridPos, gTent, tentPos_eq_tentFn_of_mem L hlog]

/-- **The truncated moving-tent integrand is Lipschitz on `[0, ∞)`** (§3, eq. 14–15).  Assembled by
gluing the two flat pieces `[0,1]`, `[e^{2L}, ∞)` to the support piece `[1, e^{2L}]` (where it equals
`gTent`), with the common constant supplied by `gTent_lipschitzOnWith`.  This is the modulus of
continuity that feeds the uniform Riemann-sum estimate for the moving-prime sum. -/
theorem gGridPos_lipschitzOnWith (L : ℝ) (hL : 0 ≤ L) (s : ℂ) :
    ∃ C : NNReal, LipschitzOnWith C (gGridPos L s) (Set.Ici 0) := by
  obtain ⟨C, hC⟩ := gTent_lipschitzOnWith L hL s
  refine ⟨C, ?_⟩
  have hP2 : LipschitzOnWith C (gGridPos L s) (Set.Icc 1 (Real.exp (2 * L))) := by
    rw [lipschitzOnWith_iff_dist_le_mul] at hC ⊢
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm, gGridPos_eq_gTent L s hx, gGridPos_eq_gTent L s hy,
      ← dist_eq_norm, ← dist_eq_norm]
    exact hC x hx y hy
  have hP3 : LipschitzOnWith C (gGridPos L s) (Set.Ici (Real.exp (2 * L))) := by
    rw [lipschitzOnWith_iff_dist_le_mul]; intro x hx y hy
    rw [gGridPos_eq_zero_of_ge L s hx, gGridPos_eq_zero_of_ge L s hy, dist_self]; positivity
  have hP1 : LipschitzOnWith C (gGridPos L s) (Set.Icc 0 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]; intro x hx y hy
    rw [gGridPos_eq_zero_of_mem_Icc L s hx.1 hx.2, gGridPos_eq_zero_of_mem_Icc L s hy.1 hy.2,
      dist_self]; positivity
  have hIci1 : LipschitzOnWith C (gGridPos L s) (Set.Ici 1) :=
    lipschitzOnWith_of_glue (c := Real.exp (2 * L)) Set.ordConnected_Ici
      (hP2.mono Set.Ici_inter_Iic.le) (hP3.mono Set.inter_subset_right)
  exact lipschitzOnWith_of_glue (c := 1) Set.ordConnected_Ici
    (hP1.mono Set.Ici_inter_Iic.le) (hIci1.mono Set.inter_subset_right)

/-- `g_s` is continuous on `[0, ∞)` (from the Lipschitz bound). -/
theorem gGridPos_continuousOn (L : ℝ) (hL : 0 ≤ L) (s : ℂ) :
    ContinuousOn (gGridPos L s) (Set.Ici 0) :=
  (gGridPos_lipschitzOnWith L hL s).choose_spec.continuousOn

/-- **The integral of the truncated integrand equals the tent Mellin factor** (§3, the integral half of
the comparison `(15)`--`(16)`).  For any cutoff `T ≥ e^{2L}` past the support, `∫₀ᵀ g_s(u) du = A_L(s-1)²
= I_L(s)`, since `g_s ≡ 0` off `[1, e^{2L}]` and equals `gTent` on it.  So the improper `∫₀^∞ g_s` of
`(8)` is `I_L(s)`, and any finite cutoff past the support already sees the whole value. -/
theorem gGridPos_integral_eq (L : ℝ) (hL : 0 ≤ L) (s : ℂ) (hs : s ≠ 1)
    {T : ℝ} (hT : Real.exp (2 * L) ≤ T) :
    (∫ u in (0 : ℝ)..T, gGridPos L s u) = (rectangularWindowAmplitude L (s - 1)) ^ 2 := by
  have h1e : (1 : ℝ) ≤ Real.exp (2 * L) := Real.one_le_exp (by linarith)
  have hcont := gGridPos_continuousOn L hL s
  have hsub01 : Set.uIcc (0 : ℝ) 1 ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le zero_le_one]; intro z hz; exact hz.1
  have hsub1e : Set.uIcc (1 : ℝ) (Real.exp (2 * L)) ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le h1e]; intro z hz; exact le_trans zero_le_one hz.1
  have hsubeT : Set.uIcc (Real.exp (2 * L)) T ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hT]; intro z hz; exact le_trans (le_trans zero_le_one h1e) hz.1
  have hint01 : IntervalIntegrable (gGridPos L s) MeasureTheory.volume 0 1 :=
    (hcont.mono hsub01).intervalIntegrable
  have hint1e : IntervalIntegrable (gGridPos L s) MeasureTheory.volume 1 (Real.exp (2 * L)) :=
    (hcont.mono hsub1e).intervalIntegrable
  have hinteT : IntervalIntegrable (gGridPos L s) MeasureTheory.volume (Real.exp (2 * L)) T :=
    (hcont.mono hsubeT).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hint01 (hint1e.trans hinteT),
    ← intervalIntegral.integral_add_adjacent_intervals hint1e hinteT]
  have z01 : (∫ u in (0 : ℝ)..1, gGridPos L s u) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_, intervalIntegral.integral_zero]
    intro u hu; rw [Set.uIcc_of_le zero_le_one] at hu
    exact gGridPos_eq_zero_of_mem_Icc L s hu.1 hu.2
  have zeT : (∫ u in (Real.exp (2 * L))..T, gGridPos L s u) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) ?_, intervalIntegral.integral_zero]
    intro u hu; rw [Set.uIcc_of_le hT] at hu
    exact gGridPos_eq_zero_of_ge L s hu.1
  have mid : (∫ u in (1 : ℝ)..(Real.exp (2 * L)), gGridPos L s u)
      = (rectangularWindowAmplitude L (s - 1)) ^ 2 := by
    rw [← gTent_integral_eq_amplitude_sq L hL s hs]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le h1e] at hu
    exact gGridPos_eq_gTent L s hu
  rw [z01, mid, zeT]; ring

/-- **The uniform Riemann-sum estimate** (§3, eq. 15).  For each scale `k ≥ 1` and cutoff `N` with
`N/k ≥ e^{2L}` (so the grid covers the whole support), the left-endpoint moving sum at step `1/k`
differs from the tent Mellin factor `I_L(s) = A_L(s-1)²` by at most `N·C/(2k²)`, with `C` the Lipschitz
constant of `g_s` — a single constant uniform in `k, N`.  With `N ≈ k·e^{2L}` this is the `O(1/k)`
bound of `(15)`.  Combines `gGridPos_lipschitzOnWith` (per-cell modulus) with `gGridPos_integral_eq`
(the integral value) through `norm_sum_smul_sub_integral_le`. -/
theorem gGridPos_riemann_bound (L : ℝ) (hL : 0 ≤ L) (s : ℂ) (hs : s ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k N : ℕ), 0 < k → Real.exp (2 * L) ≤ (N : ℝ) / (k : ℝ) →
      ‖(∑ j ∈ Finset.range N, (1 / (k : ℝ)) • gGridPos L s ((j : ℝ) / (k : ℝ)))
          - (rectangularWindowAmplitude L (s - 1)) ^ 2‖ ≤ (N : ℝ) * C / (2 * (k : ℝ) ^ 2) := by
  obtain ⟨C, hC⟩ := gGridPos_lipschitzOnWith L hL s
  rw [lipschitzOnWith_iff_dist_le_mul] at hC
  refine ⟨(C : ℝ), C.2, fun k N hk hN => ?_⟩
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hh : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hcont := gGridPos_continuousOn L hL s
  have hNk : Real.exp (2 * L) ≤ (0 : ℝ) + (N : ℝ) * (1 / (k : ℝ)) := by
    rw [zero_add, mul_one_div]; exact hN
  have hsubI : Set.uIcc (0 : ℝ) (0 + (N : ℝ) * (1 / (k : ℝ))) ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le (by positivity)]; intro z hz; exact hz.1
  have hint : IntervalIntegrable (gGridPos L s) volume 0 (0 + (N : ℝ) * (1 / (k : ℝ))) :=
    (hcont.mono hsubI).intervalIntegrable
  have hbound : ∀ j : ℕ, j < N → ∀ x ∈ Set.Icc ((0 : ℝ) + (j : ℝ) * (1 / (k : ℝ)))
      ((0 : ℝ) + (j : ℝ) * (1 / (k : ℝ)) + 1 / (k : ℝ)),
      ‖gGridPos L s x - gGridPos L s ((0 : ℝ) + (j : ℝ) * (1 / (k : ℝ)))‖
        ≤ (C : ℝ) * (x - ((0 : ℝ) + (j : ℝ) * (1 / (k : ℝ)))) := by
    intro j _ x hx
    have hcpos : (0 : ℝ) ≤ (0 : ℝ) + (j : ℝ) * (1 / (k : ℝ)) := by positivity
    have hxc : (0 : ℝ) + (j : ℝ) * (1 / (k : ℝ)) ≤ x := hx.1
    have hxpos : (0 : ℝ) ≤ x := le_trans hcpos hxc
    have hd := hC x hxpos ((0 : ℝ) + (j : ℝ) * (1 / (k : ℝ))) hcpos
    rwa [dist_eq_norm, Real.dist_eq, abs_of_nonneg (by linarith)] at hd
  have hmain := norm_sum_smul_sub_integral_le hh hint hbound
  rw [gGridPos_integral_eq L hL s hs hNk] at hmain
  have hgridpt : ∀ j : ℕ, (0 : ℝ) + (j : ℝ) * (1 / (k : ℝ)) = (j : ℝ) / (k : ℝ) :=
    fun j => by rw [zero_add, mul_one_div]
  simp only [hgridpt] at hmain
  calc ‖(∑ j ∈ Finset.range N, (1 / (k : ℝ)) • gGridPos L s ((j : ℝ) / (k : ℝ)))
        - (rectangularWindowAmplitude L (s - 1)) ^ 2‖
      ≤ (N : ℝ) * (C : ℝ) * (1 / (k : ℝ)) ^ 2 / 2 := hmain
    _ = (N : ℝ) * C / (2 * (k : ℝ) ^ 2) := by field_simp

end RHTower
