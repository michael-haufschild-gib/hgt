import GaloisForLFunctions.RHTower.XiSliceHeatRateSubconvex
import GaloisForLFunctions.RHTower.ZetaStripInterpolation
import GaloisForLFunctions.RHTower.ZetaFiveSeventhsLineBound

/-!
# An interior Lindelöf point lowers the WD heat rate to `(17/25)/log t`

Let `S(t, x) = ξ(½+x+it) ξ(½−x+it)` and let `T_n(λ, 0, t)` be the Taylor coefficients at `0` of the
heated slice `e^{(λ/2)∂_x²} S(t, ·)`.

**Theorem** (`DeBruijn.exists_xiSliceHeatTransfer_pos_heat_interior`).  There is `t₀` such that for
`|t| ≥ t₀`, every heat `λ ≥ (17/25)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`.

The previous rate `(19/25)/log t` (`exists_xiSliceHeatTransfer_pos_heat_subconvex`) used one linear
size profile, the Phragmén–Lindelöf chord between Weyl's `μ(½) ≤ 1/6` and `μ(1) = 0`.  With the
fourth-derivative point `μ(5/7) ≤ 1/14` (`norm_riemannZeta_fiveSevenths_le`) the profile of
`log ζ(σ+it)/log t` on `[½, 1+η]` has two pieces:

* `σ ∈ [½, 5/7]`: `1/6 + η − (4/9)(σ − ½)` (`exists_norm_riemannZeta_le_profile_one`);
* `σ ∈ [5/7, 1+η]`: `(1/14 + η)(1 + η − σ)/(2/7 + η)` (`exists_norm_riemannZeta_le_profile_two`).

For the slice this gives `|S(t, a + ic)| ≤ C S(½+2η)(t^{−(1/9 + (1/9)(½−|a|))} + t^{−(η + c₂(½+η−|a|))})`,
`c₂ = 1 − 2(1/14+η)/(2/7+η)` (`exists_norm_xiSliceProduct_le_two_profiles`).  Each linear piece
contributes an inner exponent `bᵢ = ηᵢ + cᵢ/2 − cᵢ²κ/2` against the Gaussian of variance `κ/log t`.
The window `[κ, κ + 1/100]` contributes `a = κ/2 − ½ − 2η − 1/12000`, using the Euler-point lower bound
from `x₀ = 2/3` (`exists_iteratedDeriv_xiSliceProduct_ge_euler_from`).  At `η = 1/1000`,
`κ = 17/25` both gaps `a + bᵢ` are positive (`interior_gap_pos_one`, `interior_gap_pos_two`).

In the limit `η → 0` the size-only rate is the parabola envelope of the Lindelöf profile,
`κ > max over x of (the κ with (κ − x)²/(2κ) = 2μ(½ + x))`.  Here that gives `27/40`.  With Weyl's
exponent at `½` the floor is `4μ(½) = 2/3`.
-/

open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Edge bounds and the two Phragmén–Lindelöf profiles -/

/-- `‖(s−1)ζ(s)‖ ≤ (20600/η)|t|^{15/14+η}` on `Re s = 5/7`, `|t| ≥ 8`. -/
theorem norm_zetaEntire_fiveSevenths_edge_le {η y : ℝ} (hη : 0 < η) (hy : 8 ≤ |y|) :
    ‖zetaEntire (((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 20600 / η * |y| ^ (15 / 14 + η) := by
  have key : ∀ u : ℝ, 8 ≤ u →
      ‖riemannZeta (((5 / 7 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ 10300 / η * u ^ (1 / 14 + η) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have h0 := norm_riemannZeta_fiveSevenths_le hu
    rw [show (5 / 7 : ℂ) = ((5 / 7 : ℝ) : ℂ) by push_cast; ring] at h0
    refine h0.trans ?_
    have hlog := Real.log_le_rpow_div hu0.le hη
    calc 10300 * u ^ (1 / 14 : ℝ) * Real.log u ≤ 10300 * u ^ (1 / 14 : ℝ) * (u ^ η / η) := by
          gcongr
      _ = 10300 / η * (u ^ (1 / 14 : ℝ) * u ^ η) := by ring
      _ = 10300 / η * u ^ (1 / 14 + η) := by rw [← Real.rpow_add hu0]
  have hζ : ‖riemannZeta (((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 10300 / η * |y| ^ (1 / 14 + η) := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h] at hy ⊢; exact key y hy
    · rw [abs_of_neg h] at hy ⊢
      have hc : ((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I
          = starRingEnd ℂ (((5 / 7 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) := by
        rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
        push_cast; ring
      rw [hc, riemannZeta_conj, Complex.norm_conj]
      exact key (-y) hy
  have hz1 : ((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; norm_num at this
  rw [zetaEntire_eq hz1, norm_mul]
  have hn : ‖((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I - 1‖ ≤ 2 * |y| := by
    have e : ((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I - 1 = ((-2 / 7 : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [e]; refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs]
    norm_num; linarith
  have hy0 : 0 < |y| := by linarith
  have hpow : |y| ^ (15 / 14 + η) = |y| * |y| ^ (1 / 14 + η) := by
    rw [show (15 / 14 : ℝ) + η = 1 + (1 / 14 + η) by ring, Real.rpow_add hy0, Real.rpow_one]
  calc ‖((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I - 1‖ * ‖riemannZeta (((5 / 7 : ℝ) : ℂ) + (y : ℂ) * I)‖
      ≤ (2 * |y|) * (10300 / η * |y| ^ (1 / 14 + η)) := by gcongr
    _ = 20600 / η * (|y| * |y| ^ (1 / 14 + η)) := by ring
    _ = 20600 / η * |y| ^ (15 / 14 + η) := by rw [hpow]

/-- `‖(s−1)ζ(s)‖ ≤ 2(1 + 1/η)|t|` on `Re s = 1 + η`, `|t| ≥ 8`. -/
theorem norm_zetaEntire_right_edge_le_abs {η y : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hy : 8 ≤ |y|) :
    ‖zetaEntire (((1 + η : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ 2 * (1 + 1 / η) * |y| ^ (1 : ℝ) := by
  rw [Real.rpow_one]
  refine (norm_zetaEntire_right_edge_le hη hη1).trans ?_
  have : 0 ≤ 1 + 1 / η := by positivity
  nlinarith

/-- **First profile.**  `‖ζ(σ + it)‖ ≤ C t^{1/6 + η − (4/9)(σ − ½)}` for `½ ≤ σ ≤ 5/7`, `t ≥ 8`. -/
theorem exists_norm_riemannZeta_le_profile_one {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 5 / 7 → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * t ^ (1 / 6 + η - 4 / 9 * (σ - 1 / 2)) := by
  obtain ⟨C, hC, h⟩ := exists_norm_riemannZeta_le_interp (a := 1 / 2) (b := 5 / 7)
    (pa := 7 / 6 + η) (pb := 15 / 14 + η) (Ma := 8400 / η) (Mb := 20600 / η)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
    (by positivity) (by positivity)
    (fun y hy => by simpa using norm_zetaEntire_half_edge_le hη hy)
    (fun y hy => norm_zetaEntire_fiveSevenths_edge_le hη hy)
  refine ⟨C, hC, fun σ t h1 h2 ht => (h σ t h1 h2 ht).trans (le_of_eq ?_)⟩
  congr 2; ring

/-- **Second profile.**  `‖ζ(σ + it)‖ ≤ C t^{(1/14 + η)(1 + η − σ)/(2/7 + η)}` for `5/7 ≤ σ ≤ 1 + η`,
`t ≥ 8`. -/
theorem exists_norm_riemannZeta_le_profile_two {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 5 / 7 ≤ σ → σ ≤ 1 + η → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ C * t ^ ((1 / 14 + η) * (1 + η - σ) / (2 / 7 + η)) := by
  obtain ⟨C, hC, h⟩ := exists_norm_riemannZeta_le_interp (a := 5 / 7) (b := 1 + η)
    (pa := 15 / 14 + η) (pb := 1) (Ma := 20600 / η) (Mb := 2 * (1 + 1 / η))
    (by norm_num) (by linarith) (by linarith) le_rfl (by linarith) (by linarith)
    (by positivity) (by positivity)
    (fun y hy => norm_zetaEntire_fiveSevenths_edge_le hη hy)
    (fun y hy => by simpa using norm_zetaEntire_right_edge_le_abs hη (by linarith) hy)
  refine ⟨C, hC, fun σ t h1 h2 ht => (h σ t h1 h2 ht).trans (le_of_eq ?_)⟩
  have h27 : (0 : ℝ) < 2 / 7 + η := by linarith
  rw [show (1 + η - 5 / 7 : ℝ) = 2 / 7 + η by ring]
  congr 2; field_simp; ring

/-! ## The slice with two size profiles -/

/-- **The slice from a `ζ` exponent.**  If `‖ζ(½ + |a| + i(t + c'))‖ ≤ C_ζ (2t)^e` for `|c'| ≤ R₁`, with
`2e ≤ 1`, then `|S(t, a + ic)| ≤ K S(t, ½+2η) t^{2e − (½ + 2η − |a|)}`. -/
theorem norm_xiSliceProduct_le_of_zeta_exponent {η R₁ Cz e : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hR₁ : 1 ≤ R₁) (he1 : 2 * e ≤ 1) {t a c : ℝ} (ht : 32 * R₁ + 16 ≤ t) (hc : |c| ≤ R₁)
    (ha : |a| ≤ 1 / 2 + 2 * η)
    (hz : ∀ c' : ℝ, |c'| ≤ R₁ →
      ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t + c' : ℝ) : ℂ) * I)‖ ≤ Cz * (2 * t) ^ e) :
    ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
      ≤ Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (Cz * (1 + 1 / (2 * η))) ^ 2
        * xiSliceReal t (1 / 2 + 2 * η) * t ^ (2 * e - (1 / 2 + 2 * η - |a|)) := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = 1 / (1 + 1 / (2 * η)) := ⟨_, rfl⟩
  have hm₀0 : 0 < m₀ := by rw [hm₀]; positivity
  have ht0 : 0 < t := by linarith
  have hct : |c| ≤ t / 2 := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 / 2 + 2 * η := ⟨_, rfl⟩
  rw [← hR] at ha ⊢
  have hz₀ := inv_le_norm_riemannZeta_saddle t hη (le_refl (1 / 2 + 2 * η))
  rw [← hm₀, ← hR] at hz₀
  have hB2 : ‖riemannZeta (((1 / 2 + |a| : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖ ≤ Cz * (2 * t) ^ e := by
    have := hz (-c) (by rwa [abs_neg]); rwa [← sub_eq_add_neg] at this
  have h := norm_xiSliceProduct_le_of_ref (by linarith) ha hct hm₀0 hz₀ (hz c hc) hB2
  have hpow : (Cz * (2 * t) ^ e / m₀) ^ 2 = (Cz * (1 + 1 / (2 * η))) ^ 2 * (2 * t) ^ (2 * e) := by
    rw [hm₀, div_pow, mul_pow, ← Real.rpow_natCast ((2 * t) ^ e), ← Real.rpow_mul (by positivity)]
    push_cast
    field_simp
  have hexpX := exp_shift_decay_le (d := R - |a|) (c := c) (a := |a|) ht le_rfl
    (by linarith) (by rw [hR]; linarith [abs_nonneg a]) hc (by rw [hR] at ha; linarith)
  have hkey : (2 * t) ^ (2 * e) * t ^ (-(R - |a|)) ≤ 2 * t ^ (2 * e - (R - |a|)) := by
    rw [Real.mul_rpow (by norm_num) ht0.le, mul_assoc, ← Real.rpow_add ht0,
      show 2 * e + -(R - |a|) = 2 * e - (R - |a|) by ring]
    have h2 : (2 : ℝ) ^ (2 * e) ≤ 2 := by
      calc (2 : ℝ) ^ (2 * e) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have hS := xiSliceReal_nonneg t R
  rw [hpow] at h
  calc ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
      ≤ xiSliceReal t R * ((Cz * (1 + 1 / (2 * η))) ^ 2 * (2 * t) ^ (2 * e))
        * Real.exp (-(R - |a|) * Real.log (t / (2 * Real.pi))
          + 12 * (R - |a| + |c|) / t + 4 * (1 / 2 + |a|) / t) := h
    _ ≤ xiSliceReal t R * ((Cz * (1 + 1 / (2 * η))) ^ 2 * (2 * t) ^ (2 * e))
        * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(R - |a|)))) :=
        mul_le_mul_of_nonneg_left hexpX (by positivity)
    _ = xiSliceReal t R * (Cz * (1 + 1 / (2 * η))) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * ((2 * t) ^ (2 * e) * t ^ (-(R - |a|))) := by ring
    _ ≤ xiSliceReal t R * (Cz * (1 + 1 / (2 * η))) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * (2 * t ^ (2 * e - (R - |a|))) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (Cz * (1 + 1 / (2 * η))) ^ 2 * xiSliceReal t R
        * t ^ (2 * e - (R - |a|)) := by ring

/-- The slope of the second profile, `c₂ = 1 − 2(1/14+η)/(2/7+η)`. -/
def interiorGain (η : ℝ) : ℝ := 1 - 2 * (1 / 14 + η) / (2 / 7 + η)

theorem interiorGain_nonneg {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 10) : 0 ≤ interiorGain η := by
  unfold interiorGain
  rw [sub_nonneg, div_le_one (by linarith)]
  linarith

theorem interiorGain_le_one {η : ℝ} (hη : 0 < η) : interiorGain η ≤ 1 := by
  unfold interiorGain
  have : 0 ≤ 2 * (1 / 14 + η) / (2 / 7 + η) := by positivity
  linarith

/-- **The slice inside the strip, two profiles.**  For `|a| < ½ + η`,
`|S(t, a + ic)| ≤ C S(t, ½+2η) (t^{−(1/9 + (1/9)(½ − |a|))} + t^{−(η + c₂(½ + η − |a|))})`. -/
theorem exists_norm_xiSliceProduct_le_two_profiles {η R₁ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 10)
    (hR₁ : 1 ≤ R₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ t a c : ℝ, 32 * R₁ + 16 ≤ t → |c| ≤ R₁ → |a| < 1 / 2 + η →
      ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
        ≤ C * xiSliceReal t (1 / 2 + 2 * η)
          * (t ^ (-(1 / 9 + 1 / 9 * (1 / 2 - |a|)))
            + t ^ (-(η + interiorGain η * (1 / 2 + η - |a|)))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_riemannZeta_le_profile_one hη (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_riemannZeta_le_profile_two hη (by linarith)
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₁ * (1 + 1 / (2 * η))) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨K₂, hK₂⟩ : ∃ K₂, K₂ = Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * (C₂ * (1 + 1 / (2 * η))) ^ 2 :=
    ⟨_, rfl⟩
  refine ⟨K₁ + K₂, by rw [hK₁, hK₂]; positivity, fun t a c ht hc ha => ?_⟩
  have ht0 : 0 < t := by linarith
  have hS := xiSliceReal_nonneg t (1 / 2 + 2 * η)
  have hp1 : 0 ≤ t ^ (-(1 / 9 + 1 / 9 * (1 / 2 - |a|))) := by positivity
  have hp2 : 0 ≤ t ^ (-(η + interiorGain η * (1 / 2 + η - |a|))) := by positivity
  have hzt : ∀ c' : ℝ, |c'| ≤ R₁ → 8 ≤ t + c' ∧ t + c' ≤ 2 * t := by
    intro c' hc'
    have := abs_le.mp hc'
    constructor <;> linarith
  rcases le_or_gt |a| (3 / 14) with hsmall | hbig
  · -- first profile, `e = 1/6 + η − (4/9)|a|`
    have he0 : 0 ≤ 1 / 6 + η - 4 / 9 * |a| := by linarith
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₁) (e := 1 / 6 + η - 4 / 9 * |a|)
      (t := t) (a := a) (c := c) hη (by linarith) hR₁ (by linarith [abs_nonneg a]) ht hc
      (by linarith) (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₁ _ _ (by linarith [abs_nonneg a]) (by linarith) h8).trans ?_
        rw [show 1 / 6 + η - 4 / 9 * (1 / 2 + |a| - 1 / 2) = 1 / 6 + η - 4 / 9 * |a| by ring]
        gcongr)
    rw [← hK₁] at hb
    have hex : 2 * (1 / 6 + η - 4 / 9 * |a|) - (1 / 2 + 2 * η - |a|)
        = -(1 / 9 + 1 / 9 * (1 / 2 - |a|)) := by ring
    rw [hex] at hb
    calc ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
        ≤ K₁ * xiSliceReal t (1 / 2 + 2 * η) * t ^ (-(1 / 9 + 1 / 9 * (1 / 2 - |a|))) := hb
      _ ≤ (K₁ + K₂) * xiSliceReal t (1 / 2 + 2 * η)
          * (t ^ (-(1 / 9 + 1 / 9 * (1 / 2 - |a|)))
            + t ^ (-(η + interiorGain η * (1 / 2 + η - |a|)))) := by
          have hK0 : 0 ≤ K₂ := by rw [hK₂]; positivity
          have hK10 : 0 ≤ K₁ := by rw [hK₁]; positivity
          have : K₁ * xiSliceReal t (1 / 2 + 2 * η) ≤ (K₁ + K₂) * xiSliceReal t (1 / 2 + 2 * η) :=
            mul_le_mul_of_nonneg_right (by linarith) hS
          calc K₁ * xiSliceReal t (1 / 2 + 2 * η) * t ^ (-(1 / 9 + 1 / 9 * (1 / 2 - |a|)))
              ≤ (K₁ + K₂) * xiSliceReal t (1 / 2 + 2 * η) * t ^ (-(1 / 9 + 1 / 9 * (1 / 2 - |a|))) :=
                mul_le_mul_of_nonneg_right this hp1
            _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hS)
  · -- second profile, `e = (1/14 + η)(½ + η − |a|)/(2/7 + η)`
    have h27 : (0 : ℝ) < 2 / 7 + η := by linarith
    have he0 : 0 ≤ (1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) h27.le
    have he1 : 2 * ((1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η)) ≤ 1 := by
      rw [mul_div_assoc', div_le_one h27]
      nlinarith
    have hb := norm_xiSliceProduct_le_of_zeta_exponent (Cz := C₂)
      (e := (1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η)) (t := t) (a := a) (c := c) hη
      (by linarith) hR₁ he1 ht hc
      (by linarith) (fun c' hc' => by
        obtain ⟨h8, h2t⟩ := hzt c' hc'
        refine (h₂ _ _ (by linarith) (by linarith) h8).trans ?_
        rw [show 1 + η - (1 / 2 + |a|) = 1 / 2 + η - |a| by ring]
        gcongr)
    rw [← hK₂] at hb
    have hex : 2 * ((1 / 14 + η) * (1 / 2 + η - |a|) / (2 / 7 + η)) - (1 / 2 + 2 * η - |a|)
        = -(η + interiorGain η * (1 / 2 + η - |a|)) := by
      unfold interiorGain; field_simp; ring
    rw [hex] at hb
    have hK0 : 0 ≤ K₁ := by rw [hK₁]; positivity
    have hK0' : 0 ≤ K₂ := by rw [hK₂]; positivity
    calc ‖xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)‖
        ≤ K₂ * xiSliceReal t (1 / 2 + 2 * η) * t ^ (-(η + interiorGain η * (1 / 2 + η - |a|))) := hb
      _ ≤ (K₁ + K₂) * xiSliceReal t (1 / 2 + 2 * η)
          * t ^ (-(η + interiorGain η * (1 / 2 + η - |a|))) := by
          gcongr; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hS)

/-- **Inner Cauchy bound, two profiles.**  For `|x| < ½` and `1 ≤ N ≤ log t`, with `c₂ = interiorGain η`
and `E = C_η`,
`|S^{(N)}(x)|/N! ≤ C S(½+2η) (e^{N − u/9 − (u/9)(½−|x|)} + e^{N − ηu − c₂u(½−|x|)}) ((u + 2E)/N)ᴺ`,
`u = log t`. -/
theorem exists_norm_iteratedDeriv_xiSliceProduct_le_inner_two_profiles {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 80 ≤ t → ∀ x : ℝ, |x| < 1 / 2 → ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ≤ Real.log t →
      ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ / N.factorial ≤
        C * xiSliceReal t (1 / 2 + 2 * η)
          * ((Real.exp (N - Real.log t / 9 - Real.log t / 9 * (1 / 2 - |x|))
            + Real.exp (N - η * Real.log t - interiorGain η * Real.log t * (1 / 2 - |x|)))
          * ((Real.log t + 2 * xiEulerConstant η) / N) ^ N) := by
  obtain ⟨C₁, hC₁, hS₁⟩ := exists_norm_xiSliceProduct_le_two_profiles (R₁ := 2) hη hη1 (by norm_num)
  obtain ⟨C₂, hC₂, hS₂⟩ := exists_norm_xiSliceProduct_le_strip (R₁ := 2) hη (by linarith)
    (by norm_num)
  have hc0 := interiorGain_nonneg hη hη1
  have hc1 := interiorGain_le_one hη
  refine ⟨C₁ + C₂, by linarith, fun t ht x hx N hN1 hNu => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = interiorGain η := ⟨_, rfl⟩
  rw [← hudef] at hNu ⊢
  rw [← hEdef, ← hcdef]
  rw [← hcdef] at hc0 hc1
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hu0 : 0 < u := by linarith
  have hu2E : 0 < u + 2 * E := by linarith
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = xiSliceReal t (1 / 2 + 2 * η) := ⟨_, rfl⟩
  have hS₀0 : 0 ≤ S₀ := hS₀ ▸ xiSliceReal_nonneg t _
  obtain ⟨r, hrdef⟩ : ∃ r, r = N / (u + 2 * E) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hu2E]; linarith
  have hrN : (u + 2 * E) * r = N := by rw [hrdef]; field_simp
  have hxa : 0 < 1 / 2 - |x| := by linarith
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = (u + 2 * E) * r - u / 9 - u / 9 * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (C₁ + C₂) * S₀ * (Real.exp A₁ + Real.exp A₂) := ⟨_, rfl⟩
  have hMb : ∀ z ∈ sphere (x : ℂ) r, ‖xiSliceProduct t z‖ ≤ M := by
    intro z hz
    have hzr : ‖z - x‖ = r := mem_sphere_iff_norm.mp hz
    have hza : |z.re - x| ≤ r := by
      have := Complex.abs_re_le_norm (z - x)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    have hzc : |z.im| ≤ r := by
      have := Complex.abs_im_le_norm (z - x)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith
    have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have habs : |z.re| ≤ |x| + r := by
      have := abs_add_le (z.re - x) x
      rw [sub_add_cancel] at this
      linarith
    have hE1 : 0 ≤ Real.exp A₁ := (Real.exp_pos _).le
    have hE2 : 0 ≤ Real.exp A₂ := (Real.exp_pos _).le
    rw [hz']
    by_cases ha : |z.re| < 1 / 2 + η
    · have h := hS₁ t z.re z.im (by linarith) (by linarith) ha
      rw [← hS₀, ← hcdef] at h
      refine h.trans ?_
      rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0, ← hudef, hM]
      have hexp1 : u * -(1 / 9 + 1 / 9 * (1 / 2 - |z.re|)) ≤ A₁ := by
        rw [hA₁]
        have h2 : |z.re| - |x| ≤ r := by linarith only [habs]
        have h3 : u / 9 * (|z.re| - |x|) ≤ u / 9 * r := mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : u / 9 * r ≤ u * r := by nlinarith [hr0]
        have h5 : 0 ≤ 2 * E * r := by positivity
        nlinarith only [h3, h4, h5]
      have hexp2 : u * -(η + c * (1 / 2 + η - |z.re|)) ≤ A₂ := by
        rw [hA₂]
        have h2 : |z.re| - |x| - η ≤ r := by linarith only [habs, hη]
        have h3 : c * u * (|z.re| - |x| - η) ≤ c * u * r :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have h4 : c * (u * r) ≤ 1 * (u * r) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
        have h5 : 0 ≤ 2 * E * r := by positivity
        have e1 : c * u * r = c * (u * r) := by ring
        have e2 : (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|) - u * -(η + c * (1 / 2 + η - |z.re|))
            = (u + 2 * E) * r - c * u * (|z.re| - |x| - η) := by ring
        have e3 : (u + 2 * E) * r = 1 * (u * r) + 2 * E * r := by ring
        linarith only [h3, h4, h5, e1, e2, e3]
      have hCC : C₁ * S₀ ≤ (C₁ + C₂) * S₀ := mul_le_mul_of_nonneg_right (by linarith) hS₀0
      exact mul_le_mul hCC (add_le_add (Real.exp_le_exp.mpr hexp1) (Real.exp_le_exp.mpr hexp2))
        (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (mul_nonneg (by linarith) hS₀0)
    · push Not at ha
      obtain ⟨-, hout⟩ := hS₂ t z.re z.im (by linarith) (by linarith)
      refine le_trans (hout ha (by linarith)) ?_
      set y := max |z.re| (1 / 2 + 2 * η) with hy
      have hy1 : 1 / 2 + 2 * η ≤ y := le_max_right _ _
      have hy2 : y ≤ t / 2 := max_le (by linarith) (by linarith)
      have hgrow := (xiSliceReal_growth_euler (t := t) hη (by linarith) (y₁ := 1 / 2 + 2 * η)
        (y₂ := y) (by linarith) hy1 hy2).2
      rw [← hudef, ← hEdef, ← hS₀] at hgrow
      have hexp : (u + 2 * E) * (y - (1 / 2 + 2 * η)) ≤ A₂ := by
        rw [hA₂]
        have hcu : c * u * (1 / 2 - |x|) ≤ u * (1 / 2 - |x|) := by
          have := mul_le_mul_of_nonneg_right hc1 (by positivity : (0 : ℝ) ≤ u * (1 / 2 - |x|))
          linarith
        have e0 : u * (1 / 2 - |x|) - c * u * (1 / 2 - |x|) = (1 - c) * (u * (1 / 2 - |x|)) := by
          ring
        have hcu' : 0 ≤ (1 - c) * (u * (1 / 2 - |x|)) :=
          mul_nonneg (by linarith only [hc1]) (by positivity)
        rcases le_total |z.re| (1 / 2 + 2 * η) with h | h
        · rw [hy, max_eq_right h, sub_self, mul_zero]
          have h1 : 1 / 2 + η - |x| ≤ r := by linarith only [ha, habs]
          have h2 : u * (1 / 2 + η - |x|) ≤ u * r := mul_le_mul_of_nonneg_left h1 hu0.le
          have h3 : 0 ≤ E * r := mul_nonneg hE0.le hr0.le
          have e1 : (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|)
              = (u * r - u * (1 / 2 + η - |x|)) + 2 * (E * r)
                + (u * (1 / 2 - |x|) - c * u * (1 / 2 - |x|)) := by ring
          linarith only [h2, h3, e0, e1, hcu']
        · rw [hy, max_eq_left h]
          have h1 : |z.re| - (1 / 2 + 2 * η) ≤ r + |x| - 1 / 2 - 2 * η := by linarith only [habs]
          have h2 := mul_le_mul_of_nonneg_left h1 hu2E.le
          have hneg : |x| - 1 / 2 - 2 * η ≤ 0 := by linarith only [hx, hη]
          have h3 : 2 * E * (|x| - 1 / 2 - 2 * η) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
          have e1 : (u + 2 * E) * (r + |x| - 1 / 2 - 2 * η)
              = (u + 2 * E) * r + u * (|x| - 1 / 2 - 2 * η) + 2 * E * (|x| - 1 / 2 - 2 * η) := by
            ring
          have e2 : u * (|x| - 1 / 2 - 2 * η) = -(u * (1 / 2 - |x|)) - 2 * (η * u) := by ring
          have hηu : 0 ≤ η * u := by positivity
          linarith only [h2, h3, e0, e1, e2, hcu', hηu]
      calc C₂ * xiSliceReal t y
          ≤ C₂ * (S₀ * Real.exp ((u + 2 * E) * (y - (1 / 2 + 2 * η)))) :=
            mul_le_mul_of_nonneg_left hgrow hC₂.le
        _ ≤ (C₁ + C₂) * (S₀ * Real.exp A₂) := by
            gcongr; linarith
        _ ≤ (C₁ + C₂) * (S₀ * (Real.exp A₁ + Real.exp A₂)) := by
            gcongr; linarith [Real.exp_pos A₁]
        _ = M := by rw [hM]; ring
  have hcauchy := norm_iteratedDeriv_xiSliceProduct_le t N hr0 hMb
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hfact, ← hS₀]
  have hA₁' : A₁ = N - u / 9 - u / 9 * (1 / 2 - |x|) := by rw [hA₁, hrN]
  have hA₂' : A₂ = N - η * u - c * u * (1 / 2 - |x|) := by rw [hA₂, hrN]
  calc ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ ≤ N.factorial * M / r ^ N := hcauchy
    _ = (C₁ + C₂) * S₀ * ((Real.exp (N - u / 9 - u / 9 * (1 / 2 - |x|))
          + Real.exp (N - η * u - c * u * (1 / 2 - |x|))) * ((u + 2 * E) / N) ^ N)
          * N.factorial := by
        rw [hM, ← hA₁', ← hA₂', hrdef, div_pow, div_pow]
        field_simp

/-! ## The window, the gaps and the low orders -/

/-- **Weighted window bound at the saddle** for `max(½ + 2η, 3/5) ≤ κ ≤ 1`, `x ∈ [κ, κ + 1/100]`:
`S(½+2η) e^{u(κ/2 − ½ − 2η − 1/12000) − 2(log 2 + 2E)} ≤ S(x) e^{−x²u/(2κ)}`. -/
theorem xiSliceReal_mul_gauss_ge_window_interior {η κ t x : ℝ} (hη : 0 < η)
    (hκη : 1 / 2 + 2 * η ≤ κ) (hκ6 : 3 / 5 ≤ κ) (hκ1 : κ ≤ 1) (ht : 8 ≤ t) (hx1 : κ ≤ x)
    (hx2 : x ≤ κ + 1 / 100) (hxt : x ≤ t / 2) :
    xiSliceReal t (1 / 2 + 2 * η) * Real.exp (Real.log t * (κ / 2 - 1 / 2 - 2 * η - 1 / 12000)
        - 2 * (Real.log 2 + 2 * xiEulerConstant η))
      ≤ xiSliceReal t x * Real.exp (-(x ^ 2 * Real.log t / (2 * κ))) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  rw [← hudef, ← hEdef]
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hu0 : 0 ≤ u := by rw [hudef]; exact Real.log_nonneg (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ0 : 0 < κ := by linarith
  have hgrow := (xiSliceReal_growth_euler (t := t) (η := η) hη ht
    (y₁ := 1 / 2 + 2 * η) (y₂ := x) (by linarith) (by linarith) hxt).1
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef] at hgrow
  have hQ : κ / 2 - 1 / 2 - 2 * η - 1 / 12000 ≤ x - (1 / 2 + 2 * η) - x ^ 2 / (2 * κ) := by
    have e : x - x ^ 2 / (2 * κ) = κ / 2 - (x - κ) ^ 2 / (2 * κ) := by field_simp; ring
    have h1 : (x - κ) ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (x - κ) ^ 2 / (2 * κ) ≤ 1 / 12000 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hexp : u * (κ / 2 - 1 / 2 - 2 * η - 1 / 12000) - 2 * (Real.log 2 + 2 * E)
      ≤ (u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η)) - x ^ 2 * u / (2 * κ) := by
    have h1 := mul_le_mul_of_nonneg_left hQ hu0
    have h2 : x - (1 / 2 + 2 * η) ≤ 2 := by linarith
    have h3 : 0 ≤ x - (1 / 2 + 2 * η) := by linarith
    have hc : 0 ≤ Real.log 2 + 2 * E := by linarith
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    have e : x ^ 2 * u / (2 * κ) = u * (x ^ 2 / (2 * κ)) := by ring
    rw [e]
    nlinarith
  have hS := xiSliceReal_nonneg t (1 / 2 + 2 * η)
  calc xiSliceReal t (1 / 2 + 2 * η)
        * Real.exp (u * (κ / 2 - 1 / 2 - 2 * η - 1 / 12000) - 2 * (Real.log 2 + 2 * E))
      ≤ xiSliceReal t (1 / 2 + 2 * η) * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η))
          - x ^ 2 * u / (2 * κ)) := by gcongr
    _ = xiSliceReal t (1 / 2 + 2 * η)
          * Real.exp ((u - Real.log 2 - 2 * E) * (x - (1 / 2 + 2 * η)))
          * Real.exp (-(x ^ 2 * u / (2 * κ))) := by
        rw [mul_assoc (xiSliceReal t (1 / 2 + 2 * η)), ← Real.exp_add]; ring_nf
    _ ≤ xiSliceReal t x * Real.exp (-(x ^ 2 * u / (2 * κ))) := by gcongr

/-- The inner exponent of the first profile, `b₁ = 1/9 + 1/18 − κ/162`. -/
def interiorRateOne (κ : ℝ) : ℝ := 1 / 9 + 1 / 18 - (1 / 9) ^ 2 * κ / 2

/-- The inner exponent of the second profile, `b₂ = η + c₂/2 − c₂²κ/2`. -/
def interiorRateTwo (η κ : ℝ) : ℝ := η + interiorGain η / 2 - interiorGain η ^ 2 * κ / 2

theorem interior_gap_pos_one :
    0 < ((17 / 25 : ℝ) / 2 - 1 / 2 - 2 * (1 / 1000) - 1 / 12000) + interiorRateOne (17 / 25) := by
  unfold interiorRateOne; norm_num

theorem interior_gap_pos_two :
    0 < ((17 / 25 : ℝ) / 2 - 1 / 2 - 2 * (1 / 1000) - 1 / 12000)
      + interiorRateTwo (1 / 1000) (17 / 25) := by
  unfold interiorRateTwo interiorGain; norm_num

/-- **Low orders at heat `κ/log t` with two size profiles.**  If `2/3 ≤ κ ≤ 1` and both gaps
`κ/2 − ½ − 2η − 1/12000 + bᵢ` are positive at `η = 1/1000`, then for `1 ≤ m` and `2m ≤ log t`,
`T_{2m}(κ/log t, 0, t)` is positive once `t` is large. -/
theorem exists_xiSliceHeatTransfer_pos_low_order_interior {κ : ℝ} (hκ : 2 / 3 ≤ κ) (hκ1 : κ ≤ 1)
    (hgap₁ : 0 < (κ / 2 - 1 / 2 - 2 * (1 / 1000) - 1 / 12000) + interiorRateOne κ)
    (hgap₂ : 0 < (κ / 2 - 1 / 2 - 2 * (1 / 1000) - 1 / 12000) + interiorRateTwo (1 / 1000) κ) :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ, 1 ≤ m → (2 * m : ℝ) ≤ Real.log t →
      0 < DeBruijn.xiSliceHeatTransfer (κ / Real.log t) 0 t (2 * m) := by
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = 1 / 1000 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; norm_num
  have hη1 : η ≤ 1 / 10 := by rw [hηdef]; norm_num
  obtain ⟨C, hC, hinner⟩ := exists_norm_iteratedDeriv_xiSliceProduct_le_inner_two_profiles hη hη1
  obtain ⟨t₄, -, hM4⟩ := exists_iteratedDeriv_xiSliceProduct_ge_euler_from (η := 1 / 12)
    (by norm_num) (by norm_num)
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨E₈, hE₈def⟩ : ∃ E₈, E₈ = xiEulerConstant (1 / 12) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hE₈0 : 0 < E₈ := hE₈def ▸ xiEulerConstant_pos (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ0 : 0 < κ := by linarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = interiorGain η := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = κ / 2 - 1 / 2 - 2 * η - 1 / 12000 := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = min (interiorRateOne κ) (interiorRateTwo η κ) := ⟨_, rfl⟩
  have hb₁ : b ≤ 1 / 9 + 1 / 18 - (1 / 9) ^ 2 * κ / 2 := by
    rw [hbdef]; exact min_le_left _ _
  have hb₂ : b ≤ η + c / 2 - c ^ 2 * κ / 2 := by
    rw [hbdef, hcdef]; exact min_le_right _ _
  have hgap : 0 < a + b := by
    rw [hadef, hbdef, hηdef]
    rcases min_choice (interiorRateOne κ) (interiorRateTwo (1 / 1000) κ) with h | h <;> rw [h]
    · exact hgap₁
    · exact hgap₂
  obtain ⟨K, hKdef⟩ : ∃ K, K = 80 * Real.pi * Real.sqrt 2 * (2 * C)
      * Real.exp (2 * (2 * E + Real.log 2 + 2 * E₈) + (2 * (Real.log 2 + 2 * E) + 1)) / (1 / 100) :=
    ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (a + b)
    hgap)).2 (1 / K) (by positivity)
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp e5
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = max (max (Real.log 80) (Real.log t₄))
      (max (2 * (Real.log 2 + 2 * E₈)) (max U 1)) := ⟨_, rfl⟩
  refine ⟨max 80 (max t₄ (Real.exp L₀)), le_max_left _ _, ?_⟩
  intro t ht m hm1 hmu
  have ht80 : 80 ≤ t := le_trans (le_max_left _ _) ht
  have ht4 : t₄ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htL : Real.exp L₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have ht0 : 0 < t := by linarith
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  have hLu : L₀ ≤ u := by
    rw [hudef, ← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) htL
  rw [hL₀] at hLu
  have hu2 : 2 * (Real.log 2 + 2 * E₈) ≤ u :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLu
  have huU : U ≤ u :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu1 : 1 ≤ u :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hLu
  have hu0 : 0 < u := by linarith
  have hKu : u * K < Real.exp ((a + b) * u) := by
    have h := hU u huU
    rw [Real.rpow_one, show -(a + b) * u = -((a + b) * u) by ring, Real.exp_neg] at h
    have hx := Real.exp_pos ((a + b) * u)
    rw [lt_div_iff₀ hK0] at h
    calc u * K = u * (Real.exp ((a + b) * u))⁻¹ * K * Real.exp ((a + b) * u) := by field_simp
      _ < 1 * Real.exp ((a + b) * u) := mul_lt_mul_of_pos_right h hx
      _ = Real.exp ((a + b) * u) := one_mul _
  -- the order and the heat
  obtain ⟨N, hNdef⟩ : ∃ N, N = 2 * m := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by omega
  have hNu : (N : ℝ) ≤ u := by rw [hNdef, hudef]; push_cast; exact hmu
  rw [← hudef]
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = κ / u := ⟨_, rfl⟩
  rw [← hlamdef, ← hNdef]
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt lam := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hlam0
  have hs2 : s ^ 2 = lam := by rw [hsdef]; exact Real.sq_sqrt hlam0.le
  -- the representation and its real part
  have hrep := DeBruijn.xiSliceHeatTransfer_eq_integral_iteratedDeriv hlam0.le t N
  have hint := DeBruijn.integrable_gauss_mul_iteratedDeriv_xiSliceProduct hlam0.le t N
  rw [← hsdef] at hrep hint
  set F : ℝ → ℂ := fun w => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
    * (iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ) / N.factorial) with hF
  have hre : ∫ w, (F w).re = (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)
      * DeBruijn.xiSliceHeatTransfer lam 0 t N).re := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [hrep]; exact this
  have hfact0 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hFre : ∀ w, (F w).re = Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial) := by
    intro w
    simp only [hF]
    rw [Complex.re_ofReal_mul, Complex.div_natCast_re]
  -- constants of the window argument
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = xiSliceReal t (1 / 2 + 2 * η) := ⟨_, rfl⟩
  have hS₀0 : 0 < S₀ := by rw [hS₀]; exact xiSliceReal_pos t (by linarith)
  have hlogt2 : Real.log (t / 2) = u - Real.log 2 := by
    rw [Real.log_div ht0.ne' (by norm_num), hudef]
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
      * (1 / (40 * Real.pi * Real.sqrt (2 * u))) := ⟨_, rfl⟩
  have hL'0 : 0 < u - Real.log 2 - 2 * E₈ := by linarith
  have hQ0 : 0 ≤ Q := by
    rw [hQ]; exact mul_nonneg (div_nonneg (pow_pos hL'0 N).le hfact0.le) (by positivity)
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, P₀ = S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = 2 * C * S₀ * (Real.exp (N - b * u)
      * ((u + 2 * E) / N) ^ N) := ⟨_, rfl⟩
  have hwin := DeBruijn.integral_ge_of_window (h := fun w => (F w).re) hint.re
    (a := κ / s) (b := (κ + 1 / 100) / s) (c := 1 / 2 / s) (P := P₀) (B := B₀)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hs0.le) ?_ ?_ ?_
  rotate_left
  · -- the window
    intro w hw
    have hx1 : κ ≤ s * w := by
      have := hw.1; rw [div_le_iff₀ hs0] at this; linarith
    have hx2 : s * w ≤ κ + 1 / 100 := by
      have := hw.2; rw [le_div_iff₀ hs0] at this; linarith
    have hM := hM4 t ht4 (s * w) (by linarith) (by linarith) N hN1 (by rw [← hudef]; exact hNu)
    rw [← div_eq_inv_mul, Complex.div_natCast_re, hlogt2, ← hE₈def, ← hudef] at hM
    have hF' := xiSliceReal_mul_gauss_ge_window_interior (t := t) hη (by linarith) (by linarith)
      hκ1 (by linarith) hx1 hx2 (by linarith)
    rw [← hudef, ← hEdef, ← hS₀,
      show u * (κ / 2 - 1 / 2 - 2 * η - 1 / 12000) = u * a by rw [hadef]] at hF'
    have hg : Real.exp (-(w ^ 2 / 2)) = Real.exp (-((s * w) ^ 2 * u / (2 * κ))) := by
      congr 2
      rw [mul_pow, hs2, hlamdef]
      field_simp
    rw [hFre, hg, hP₀]
    calc S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q
        ≤ xiSliceReal t (s * w) * Real.exp (-((s * w) ^ 2 * u / (2 * κ))) * Q :=
          mul_le_mul_of_nonneg_right hF' hQ0
      _ = Real.exp (-((s * w) ^ 2 * u / (2 * κ)))
          * (xiSliceReal t (s * w) * (u - Real.log 2 - 2 * E₈) ^ N / N.factorial
            * (1 / (40 * Real.pi * Real.sqrt (2 * u)))) := by rw [hQ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
  · -- the inner region
    intro w hw
    have hx : |s * w| < 1 / 2 := by
      rw [abs_mul, abs_of_pos hs0, ← lt_div_iff₀' hs0]
      exact abs_lt.mpr ⟨hw.1, hw.2⟩
    have hb := hinner t ht80 (s * w) hx N hN1 (by rw [← hudef]; exact hNu)
    rw [← hudef, ← hEdef, ← hS₀, ← hcdef] at hb
    rw [hFre]
    have hg0 := Real.exp_pos (-(w ^ 2 / 2))
    have hsw : |s * w| = s * |w| := by rw [abs_mul, abs_of_pos hs0]
    have hus : u ^ 2 * s ^ 2 = κ * u := by
      rw [hs2, hlamdef]; field_simp
    have h2 : |w| ^ 2 = w ^ 2 := sq_abs w
    have hsq₁ : -(w ^ 2 / 2) + (N - u / 9 - u / 9 * (1 / 2 - |s * w|)) ≤ N - b * u := by
      have h1 : 0 ≤ (|w| - u / 9 * s) ^ 2 := sq_nonneg _
      have key : -(w ^ 2 / 2) + u / 9 * s * |w| ≤ (1 / 9) ^ 2 * κ * u / 2 := by
        nlinarith only [h1, h2, hus]
      have hbu : b * u ≤ (1 / 9 + 1 / 18 - (1 / 9) ^ 2 * κ / 2) * u :=
        mul_le_mul_of_nonneg_right hb₁ hu0.le
      rw [hsw]
      linarith only [key, hbu]
    have hsq₂ : -(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|)) ≤ N - b * u := by
      have h1 : 0 ≤ (|w| - c * u * s) ^ 2 := sq_nonneg _
      have key : -(w ^ 2 / 2) + c * u * s * |w| ≤ c ^ 2 * κ * u / 2 := by
        nlinarith only [h1, h2, hus]
      have hbu : b * u ≤ (η + c / 2 - c ^ 2 * κ / 2) * u :=
        mul_le_mul_of_nonneg_right hb₂ hu0.le
      rw [hsw]
      linarith only [key, hbu]
    have hre1 : |(iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re| / N.factorial
        ≤ C * S₀ * ((Real.exp (N - u / 9 - u / 9 * (1 / 2 - |s * w|))
          + Real.exp (N - η * u - c * u * (1 / 2 - |s * w|))) * ((u + 2 * E) / N) ^ N) :=
      le_trans (div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) hfact0.le) hb
    have hX0 : 0 ≤ ((u + 2 * E) / N) ^ N := by positivity
    have habs : |Real.exp (-(w ^ 2 / 2))
        * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial)| ≤ B₀ := by
      rw [abs_mul, abs_of_pos hg0, abs_div, abs_of_pos hfact0]
      calc Real.exp (-(w ^ 2 / 2)) * (|(iteratedDeriv N (xiSliceProduct t)
            ((s * w : ℝ) : ℂ)).re| / N.factorial)
          ≤ Real.exp (-(w ^ 2 / 2)) * (C * S₀ * ((Real.exp (N - u / 9 - u / 9 * (1 / 2 - |s * w|))
            + Real.exp (N - η * u - c * u * (1 / 2 - |s * w|))) * ((u + 2 * E) / N) ^ N)) :=
            mul_le_mul_of_nonneg_left hre1 hg0.le
        _ = C * S₀ * ((Real.exp (-(w ^ 2 / 2) + (N - u / 9 - u / 9 * (1 / 2 - |s * w|)))
            + Real.exp (-(w ^ 2 / 2) + (N - η * u - c * u * (1 / 2 - |s * w|))))
            * ((u + 2 * E) / N) ^ N) := by rw [Real.exp_add, Real.exp_add]; ring
        _ ≤ C * S₀ * ((Real.exp (N - b * u) + Real.exp (N - b * u)) * ((u + 2 * E) / N) ^ N) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (add_le_add (Real.exp_le_exp.mpr hsq₁) (Real.exp_le_exp.mpr hsq₂)) hX0)
              (mul_nonneg hC.le hS₀0.le)
        _ = B₀ := by rw [hB₀]; ring
    linarith [neg_abs_le (Real.exp (-(w ^ 2 / 2))
      * ((iteratedDeriv N (xiSliceProduct t) ((s * w : ℝ) : ℂ)).re / N.factorial))]
  · -- outside the inner region
    intro w hw
    have hx : 1 / 2 ≤ |s * w| := by
      rw [abs_mul, abs_of_pos hs0, ← div_le_iff₀' hs0]
      by_contra hcon
      push Not at hcon
      exact hw (abs_lt.mp hcon)
    rw [hFre]
    have h0 := DeBruijn.re_iteratedDeriv_xiSliceProduct_even_nonneg t m hx
    rw [← hNdef] at h0
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg h0 hfact0.le)
  -- the comparison
  have hcmp := heat_window_comparison_gen (a := a) (b := b) (w := 1 / 100) (C := 2 * C)
    (by norm_num) (by linarith) hE0.le hE₈0.le hu0 hu2 (by rw [← hKdef]; exact hKu) hN1 hNu
  have hpos : 0 < ((κ + 1 / 100) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀ := by
    have e : ((κ + 1 / 100) / s - κ / s) * P₀ - 2 * (1 / 2 / s) * B₀
        = (1 / 100 * P₀ - B₀) / s := by field_simp; ring
    rw [e]
    refine div_pos ?_ hs0
    rw [hP₀, hB₀]
    rw [← hQ] at hcmp
    have h := mul_lt_mul_of_pos_left hcmp hS₀0
    rw [sub_pos]
    calc 2 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)
        < 2 * (2 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N)) := by
          have : 0 < 2 * C * S₀ * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N) := by positivity
          linarith
      _ = S₀ * (2 * (2 * C * (Real.exp (N - b * u) * ((u + 2 * E) / N) ^ N))) := by ring
      _ < S₀ * (1 / 100 * (Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q)) := h
      _ = 1 / 100 * (S₀ * Real.exp (u * a - 2 * (Real.log 2 + 2 * E)) * Q) := by ring
  have hT := lt_of_lt_of_le hpos (le_of_le_of_eq hwin hre)
  rw [Complex.re_ofReal_mul] at hT
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hTre : 0 < (DeBruijn.xiSliceHeatTransfer lam 0 t N).re := pos_of_mul_pos_right hT hsq.le
  exact Complex.lt_def.mpr ⟨hTre, (DeBruijn.xiSliceHeatTransfer_im_eq_zero hlam0.le t N).symm⟩

namespace DeBruijn

/-- **Every even order at heat `(17/25)/log t`.** -/
theorem exists_xiSliceHeatTransfer_pos_at_heat_interior :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ m : ℕ,
      0 < xiSliceHeatTransfer ((17 / 25) / Real.log t) 0 t (2 * m) := by
  obtain ⟨t₁, ht₁, hlow⟩ := exists_xiSliceHeatTransfer_pos_low_order_interior (by norm_num)
    (by norm_num) interior_gap_pos_one interior_gap_pos_two
  obtain ⟨K₁, hK₁⟩ := exists_xiSliceCoeff_pos_above_quarter_log (ε := 1 / 4) (by norm_num)
  refine ⟨max t₁ (Real.exp (2 * |K₁| + 2)), le_trans ht₁ (le_max_left _ _), fun t ht m => ?_⟩
  have ht1 : t₁ ≤ t := le_trans (le_max_left _ _) ht
  have htK : Real.exp (2 * |K₁| + 2) ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = Real.log t := ⟨_, rfl⟩
  have hℓK : 2 * |K₁| + 2 ≤ ℓ := by
    rw [hℓ, ← Real.log_exp (2 * |K₁| + 2)]; exact Real.log_le_log (Real.exp_pos _) htK
  have hℓ0 : 0 < ℓ := by linarith [abs_nonneg K₁]
  rw [← hℓ]
  have hlam0 : 0 < (17 / 25) / ℓ := by positivity
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    rw [mul_zero]
    exact xiSliceHeatTransfer_zero_order_pos hlam0 t
  by_cases hm : (2 * m : ℝ) ≤ ℓ
  · rw [hℓ] at hm ⊢
    exact hlow t ht1 m hm0 hm
  push Not at hm
  -- high orders: every slice coefficient involved is positive
  have hcoef : ∀ k : ℕ, m ≤ k → 0 < xiSliceCoeff t (2 * k) := by
    intro k hk
    have hk' : (m : ℝ) ≤ k := by exact_mod_cast hk
    refine hK₁ t ht0.le k (max_le ?_ ?_)
    · have : (K₁ : ℝ) ≤ |K₁| := le_abs_self K₁
      linarith
    · rw [← hℓ]; linarith
  have hT := hasSum_xiSliceHeatTransfer_kernelSliceMoment hlam0.le 0 t (2 * m)
  simp only [kernelSliceMoment_riemannKernel_eq_xiSliceCoeff] at hT
  have hterm : ∀ k : ℕ, 0 ≤ ((((((17 / 25) / ℓ) / 2) ^ k / k.factorial *
      ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
        xiSliceCoeff t (2 * m + 2 * k)) := by
    intro k
    refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
    rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
    exact (hcoef (m + k) (by omega)).le
  have h0 := le_hasSum hT 0 fun j _ => hterm j
  have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
    div_self hfac, one_mul, Complex.ofReal_one] at h0
  exact lt_of_lt_of_le (hcoef m le_rfl) h0

/-- **Heat `(17/25)/log |t|` makes every heated slice coefficient positive.**  There is `t₀` such that
for `|t| ≥ t₀`, every heat `λ ≥ (17/25)/log |t|` and every `m`, `T_{2m}(λ, 0, t) > 0`. -/
theorem exists_xiSliceHeatTransfer_pos_heat_interior :
    ∃ t₀ : ℝ, 80 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ |t| → ∀ lam : ℝ, (17 / 25) / Real.log |t| ≤ lam →
      ∀ m : ℕ, 0 < xiSliceHeatTransfer lam 0 t (2 * m) := by
  obtain ⟨t₀, ht₀, h⟩ := exists_xiSliceHeatTransfer_pos_at_heat_interior
  refine ⟨t₀, ht₀, fun t ht lam hlam m => ?_⟩
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlam
  have key : 0 < xiSliceHeatTransfer lam 0 |t| (2 * m) := by
    have hshift := hasSum_xiSliceHeatTransfer_shift hlam 0 |t| (2 * m)
    have hterm : ∀ k : ℕ, 0 ≤ ((((lam - (17 / 25) / Real.log |t|) / 2) ^ k / k.factorial *
        ((2 * m + 2 * k).factorial / (2 * m).factorial) : ℝ) : ℂ) *
          xiSliceHeatTransfer ((17 / 25) / Real.log |t|) 0 |t| (2 * m + 2 * k) := by
      intro k
      have hd : 0 ≤ (lam - (17 / 25) / Real.log |t|) / 2 := by linarith
      refine mul_nonneg (Complex.zero_le_real.mpr (by positivity)) ?_
      rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
      exact (h |t| ht (m + k)).le
    have h0 := le_hasSum hshift 0 fun j _ => hterm j
    have hfac : ((2 * m).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero,
      div_self hfac, one_mul, Complex.ofReal_one] at h0
    exact lt_of_lt_of_le (h |t| ht m) h0
  rcases le_total 0 t with htn | htn
  · rwa [abs_of_nonneg htn] at key
  · rw [abs_of_nonpos htn] at key
    rw [← neg_neg t, xiSliceHeatTransfer_neg_height hlam0]
    exact key

end DeBruijn

end

end RHTower
