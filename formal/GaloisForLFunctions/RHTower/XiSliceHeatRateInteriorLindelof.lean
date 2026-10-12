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
      calc C₁ * S₀ * (Real.exp (u * -(1 / 9 + 1 / 9 * (1 / 2 - |z.re|)))
            + Real.exp (u * -(η + c * (1 / 2 + η - |z.re|))))
          ≤ (C₁ + C₂) * S₀ * (Real.exp A₁ + Real.exp A₂) :=
            mul_le_mul hCC (add_le_add (Real.exp_le_exp.mpr hexp1) (Real.exp_le_exp.mpr hexp2))
              (by positivity) (by positivity)
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

end

end RHTower
