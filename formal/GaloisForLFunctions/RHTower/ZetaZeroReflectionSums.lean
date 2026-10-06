import GaloisForLFunctions.RHTower.ZetaDerivZeroSumMainTerm
import GaloisForLFunctions.RHTower.BVPrimeWindowReciprocalReflection
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.ZetaOffLineWeightedDensity
import GaloisForLFunctions.RHTower.FiniteTypeDiscreteMomentAlgebra
import GaloisForLFunctions.RHTower.RouteBOfflineDomination

/-!
# Zero sums under `ρ ↦ 1 − ρ̄`, and the off-line weight

Over the zeros of `[−½, 11/10] × [t₀, Y]` (`t₀` the fixed bottom height):

* every such zero lies in `0 < Re ρ < 1`, and `ρ ↦ 1 − ρ̄` permutes them with multiplicity
  (`sum_rectZeros_reflect`);
* (`re_zeroSum_deriv_one_sub_eq`) `Re Σ m_ρ ζ'(1 − ρ) x^ρ g_T(ρ) = x Re Σ m_ρ ζ'(ρ) x^{−ρ} g_T(ρ)`;
* `χ(s) R(s) = 1` off the real axis (`ζ(s) = χ(s) ζ(1 − s)`, `ζ(1 − s) = R(s) ζ(s)`), so
  `ζ'(ρ) = −χ(ρ) ζ'(1 − ρ)` at a zero of the strip (`deriv_riemannZeta_eq_neg_zetaChi_mul`);
* (`exists_norm_zetaChi_le_strip`) `|χ(σ + it)| ≤ C |t|^{½−σ}` for `0 ≤ σ ≤ 1`, `|t| ≥ 1`;
* (`eventually_norm_zeroSum_le`) if `H` vanishes at the critical zeros and
  `|H(ρ)| ≤ K γ^{|β−½|}` at the others, then `|Σ m_ρ H(ρ) g_T(ρ)| ≤ 2eK ε T log² T` for every
  `ε > 0` and all large `T`: the zeros left of the line are reflected onto those right of it, and the
  latter carry the weight `γ^{β−½} e^{−γ²/T²}` of `eventually_offLineWeight_le`.
-/

open Complex Filter Topology Set

namespace RHTower.GaussZeroSum

noncomputable section

/-! ## The zeros of the rectangle -/

theorem riemannZeta_eq_zero_iff_zetaResidueUnit {s : ℂ} (hs : s ≠ 1) :
    zetaResidueUnit s = 0 ↔ riemannZeta s = 0 := by
  rw [(zetaResidueUnit_eventuallyEq hs).eq_of_nhds, mul_eq_zero, sub_eq_zero]
  simp [hs]

theorem rectZeros_facts {Y : ℝ} (hY : bottomHeight ≤ Y) {w : ℂ}
    (hw : w ∈ rectZeros bottomHeight Y) :
    riemannZeta w = 0 ∧ 0 < w.re ∧ w.re < 1 ∧ bottomHeight ≤ w.im ∧ w.im ≤ Y := by
  rw [rectZeros, Sieve.mem_zetaResidueUnitClosedRectangleZeros, Complex.mem_reProdIm] at hw
  obtain ⟨⟨-, him⟩, hz⟩ := hw
  have h1 : ((-1 / 2 : ℂ) + bottomHeight * I).im = bottomHeight := by simp
  have h2 : ((11 / 10 : ℂ) + Y * I).im = Y := by simp
  rw [h1, h2, uIcc_of_le hY] at him
  have hb := one_le_bottomHeight
  have hw1 : w ≠ 1 := ne_one_of_im_pos (by linarith [him.1])
  have hζ : riemannZeta w = 0 := (riemannZeta_eq_zero_iff_zetaResidueUnit hw1).mp hz
  have htriv : ∀ n : ℕ, w ≠ -(2 * ((n : ℂ) + 1)) := fun n h => by
    have := congrArg Complex.im h
    simp at this
    linarith [him.1]
  obtain ⟨h0, h1'⟩ := RHTower.riemannZeta_zero_re_mem_Ioo hζ htriv
  exact ⟨hζ, h0, h1', him.1, him.2⟩

/-- `ρ ↦ 1 − ρ̄`. -/
def reflectZero (w : ℂ) : ℂ := 1 - (starRingEnd ℂ) w

theorem reflectZero_re (w : ℂ) : (reflectZero w).re = 1 - w.re := by simp [reflectZero]

theorem reflectZero_im (w : ℂ) : (reflectZero w).im = w.im := by simp [reflectZero]

theorem reflectZero_reflectZero (w : ℂ) : reflectZero (reflectZero w) = w := by
  simp [reflectZero]

theorem riemannZeta_reflectZero {w : ℂ} (hz : riemannZeta w = 0) (h0 : 0 < w.re)
    (h1 : w.re < 1) : riemannZeta (reflectZero w) = 0 := by
  have hc : riemannZeta ((starRingEnd ℂ) w) = 0 := by rw [riemannZeta_conj, hz, map_zero]
  exact RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hc (by simpa using h0)
    (by simpa using h1)

theorem mult_reflectZero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    mult (reflectZero w) = mult w := by
  have h := RHTower.analyticOrderAt_regularizedRiemannZeta_one_sub_conj h0 h1
  have he : zetaResidueUnit = RHTower.regularizedRiemannZeta := rfl
  simp only [mult, reflectZero, he, h]

theorem reflectZero_mem {Y : ℝ} (hY : bottomHeight ≤ Y) {w : ℂ}
    (hw : w ∈ rectZeros bottomHeight Y) : reflectZero w ∈ rectZeros bottomHeight Y := by
  obtain ⟨hz, h0, h1, him1, him2⟩ := rectZeros_facts hY hw
  have hb := one_le_bottomHeight
  rw [rectZeros, Sieve.mem_zetaResidueUnitClosedRectangleZeros, Complex.mem_reProdIm]
  have r1 : ((-1 / 2 : ℂ) + bottomHeight * I).re = -1 / 2 := by simp
  have r2 : ((11 / 10 : ℂ) + Y * I).re = 11 / 10 := by simp
  have i1 : ((-1 / 2 : ℂ) + bottomHeight * I).im = bottomHeight := by simp
  have i2 : ((11 / 10 : ℂ) + Y * I).im = Y := by simp
  rw [r1, r2, i1, i2, uIcc_of_le (by norm_num), uIcc_of_le hY, reflectZero_re, reflectZero_im]
  refine ⟨⟨⟨by linarith, by linarith⟩, him1, him2⟩, ?_⟩
  have hne : reflectZero w ≠ 1 := ne_one_of_im_pos (by rw [reflectZero_im]; linarith)
  exact (riemannZeta_eq_zero_iff_zetaResidueUnit hne).mpr (riemannZeta_reflectZero hz h0 h1)

/-- **Reflection of a zero sum.** -/
theorem sum_rectZeros_reflect {Y : ℝ} (hY : bottomHeight ≤ Y) (h : ℂ → ℂ) :
    ∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * h (reflectZero w) =
      ∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * h w := by
  refine Finset.sum_nbij' reflectZero reflectZero (fun w hw => reflectZero_mem hY hw)
    (fun w hw => reflectZero_mem hY hw) (fun w _ => reflectZero_reflectZero w)
    (fun w _ => reflectZero_reflectZero w) (fun w hw => ?_)
  obtain ⟨-, h0, h1, -⟩ := rectZeros_facts hY hw
  rw [mult_reflectZero h0 h1]

theorem gaussWeight_one_sub (T : ℝ) (s : ℂ) : gaussWeight T (1 - s) = gaussWeight T s := by
  unfold gaussWeight
  congr 1
  ring

/-- **The reflected derivative sum.**
`Re Σ m_ρ ζ'(1 − ρ) x^ρ g_T(ρ) = x Re Σ m_ρ ζ'(ρ) (1/x)^ρ g_T(ρ)`. -/
theorem re_zeroSum_deriv_one_sub_eq {Y : ℝ} (hY : bottomHeight ≤ Y) {x : ℝ} (hx : 0 < x)
    (T : ℝ) :
    (∑ w ∈ rectZeros bottomHeight Y,
        (mult w : ℂ) * (deriv riemannZeta (1 - w) * (x : ℂ) ^ w * gaussWeight T w)).re =
      x * (∑ w ∈ rectZeros bottomHeight Y,
        (mult w : ℂ) * (deriv riemannZeta w * ((x⁻¹ : ℝ) : ℂ) ^ w * gaussWeight T w)).re := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hterm : ∀ w : ℂ, deriv riemannZeta (1 - reflectZero w) * (x : ℂ) ^ reflectZero w *
      gaussWeight T (reflectZero w) = (x : ℂ) * (starRingEnd ℂ)
        (deriv riemannZeta w * ((x⁻¹ : ℝ) : ℂ) ^ w * gaussWeight T w) := by
    intro w
    have e1 : 1 - reflectZero w = (starRingEnd ℂ) w := by simp [reflectZero]
    have e2 : (x : ℂ) ^ reflectZero w = (x : ℂ) * ((x⁻¹ : ℝ) : ℂ) ^ ((starRingEnd ℂ) w) := by
      rw [reflectZero, Complex.cpow_sub _ _ hx0, Complex.cpow_one, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm),
        div_eq_mul_inv]
    rw [e1, e2, reflectZero, gaussWeight_one_sub, deriv_riemannZeta_conj_eq,
      ofReal_cpow_conj (inv_pos.mpr hx), gaussWeight_conj, map_mul, map_mul]
    ring
  rw [← sum_rectZeros_reflect hY]
  simp_rw [hterm]
  have hsum : ∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * ((x : ℂ) * (starRingEnd ℂ)
      (deriv riemannZeta w * ((x⁻¹ : ℝ) : ℂ) ^ w * gaussWeight T w)) =
      (x : ℂ) * (starRingEnd ℂ) (∑ w ∈ rectZeros bottomHeight Y,
        (mult w : ℂ) * (deriv riemannZeta w * ((x⁻¹ : ℝ) : ℂ) ^ w * gaussWeight T w)) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [map_mul, map_natCast]
    ring
  rw [hsum, Complex.re_ofReal_mul, Complex.conj_re]

/-! ## `χ R = 1` and the derivative at a zero -/

theorem zetaReflectionFactor_eq_div {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n + 1)) :
    zetaReflectionFactor s = Complex.Gammaℝ s / Complex.Gammaℝ (1 - s) := by
  rw [Complex.Gammaℝ_div_Gammaℝ_one_sub hs, Complex.Gammaℂ_def, zetaReflectionFactor]

theorem zetaChi_mul_zetaReflectionFactor {s : ℂ} (hs : s.im ≠ 0) :
    zetaChi s * zetaReflectionFactor s = 1 := by
  have h1 := gammaR_ne_zero_of_im_ne_zero hs
  have h2 : Complex.Gammaℝ (1 - s) ≠ 0 := gammaR_ne_zero_of_im_ne_zero (by simpa using hs)
  rw [zetaReflectionFactor_eq_div fun n h => hs (by rw [h]; simp)]
  unfold zetaChi
  field_simp

/-- **`ζ'(ρ) = −χ(ρ) ζ'(1 − ρ)` at a zero of the strip.** -/
theorem deriv_riemannZeta_eq_neg_zetaChi_mul {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (him : ρ.im ≠ 0) :
    deriv riemannZeta ρ = -(zetaChi ρ * deriv riemannZeta (1 - ρ)) := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  rw [deriv_riemannZeta_one_sub_eq_of_zero h0 hρ1 hz, mul_neg, ← mul_assoc,
    zetaChi_mul_zetaReflectionFactor him, one_mul, neg_neg]

/-! ## `χ` in the strip -/

/-- `|χ(σ + it)| ≤ C |t|^{½−σ}` for `0 ≤ σ ≤ 1`, `|t| ≥ 2` (the vertical Gamma ratio). -/
theorem exists_norm_zetaChi_le_strip_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ (1 / 2 - σ) := by
  obtain ⟨c, C', hc, hC', hratio⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio (a₁ := 1 / 2) (δ₁ := 1 / 2)
      (by norm_num) (by norm_num)
  refine ⟨max (1 / c) (2 * Real.pi * C'), le_trans (by positivity) (le_max_left _ _),
    fun σ t h0 h1 ht => ?_⟩
  set τ : ℝ := |t| / 2 with hτ
  have hτ1 : 1 ≤ τ := by rw [hτ]; linarith
  have hτ0 : 0 < τ := by linarith
  have ht0 : 0 < |t| := by linarith
  have hnum : ‖Complex.Gamma ((1 - ((σ : ℂ) + (t : ℂ) * I)) / 2)‖ =
      ‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
    have e : (1 - ((σ : ℂ) + (t : ℂ) * I)) / 2 = (((1 - σ) / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e, ZetaGateProductAFE.norm_Gamma_re_add_abs_im, hτ, abs_div, abs_neg, abs_two]
  have hden : ‖Complex.Gamma (((σ : ℂ) + (t : ℂ) * I) / 2)‖ =
      ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
    have e : ((σ : ℂ) + (t : ℂ) * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e, ZetaGateProductAFE.norm_Gamma_re_add_abs_im, hτ, abs_div, abs_two]
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  rw [RHTower.norm_zetaChi_eq, hre, hnum, hden]
  have hGa : 0 < ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 _)
  have hGb : 0 < ‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    norm_pos_iff.mpr (_root_.RHTower.gammaArg_Gamma_ne_zero hτ0 _)
  set Ga := ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ with hGadef
  set Gb := ‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ with hGbdef
  have hπ0 : 0 < Real.pi ^ (σ - 1 / 2) := by positivity
  rcases le_total σ (1 / 2) with hσ | hσ
  · -- `Gb/Ga ≤ τ^{½−σ}/c`
    have hr := (hratio (σ / 2) (1 / 2 - σ) τ (by linarith) (by linarith) (by linarith)
      (by linarith) hτ1).1
    have heq : σ / 2 + (1 / 2 - σ) = (1 - σ) / 2 := by ring
    rw [heq] at hr
    have hq : Gb / Ga ≤ τ ^ (1 / 2 - σ) / c := by
      rw [div_le_div_iff₀ hGa hc]
      rw [le_div_iff₀ hGb] at hr
      have hτpow : τ ^ (-(1 / 2 - σ)) * τ ^ (1 / 2 - σ) = 1 := by
        rw [← Real.rpow_add hτ0]; simp
      calc Gb * c = c * τ ^ (-(1 / 2 - σ)) * Gb * τ ^ (1 / 2 - σ) := by
            rw [show c * τ ^ (-(1 / 2 - σ)) * Gb * τ ^ (1 / 2 - σ) =
              Gb * c * (τ ^ (-(1 / 2 - σ)) * τ ^ (1 / 2 - σ)) by ring, hτpow, mul_one]
        _ ≤ Ga * τ ^ (1 / 2 - σ) := mul_le_mul_of_nonneg_right hr (by positivity)
        _ = τ ^ (1 / 2 - σ) * Ga := by ring
    have hπ : Real.pi ^ (σ - 1 / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
    have hτt : τ ^ (1 / 2 - σ) ≤ |t| ^ (1 / 2 - σ) :=
      Real.rpow_le_rpow hτ0.le (by rw [hτ]; linarith) (by linarith)
    calc Real.pi ^ (σ - 1 / 2) * Gb / Ga = Real.pi ^ (σ - 1 / 2) * (Gb / Ga) := by ring
      _ ≤ 1 * (τ ^ (1 / 2 - σ) / c) := mul_le_mul hπ hq (by positivity) zero_le_one
      _ ≤ 1 / c * |t| ^ (1 / 2 - σ) := by
          rw [one_mul, show 1 / c * |t| ^ (1 / 2 - σ) = |t| ^ (1 / 2 - σ) / c by ring]
          exact div_le_div_of_nonneg_right hτt hc.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- `Gb/Ga ≤ C' τ^{−(σ−½)}`
    have hr := (hratio ((1 - σ) / 2) (σ - 1 / 2) τ (by linarith) (by linarith) (by linarith)
      (by linarith) hτ1).2
    have heq : (1 - σ) / 2 + (σ - 1 / 2) = σ / 2 := by ring
    rw [heq] at hr
    have hq : Gb / Ga ≤ C' * τ ^ (-(σ - 1 / 2)) := hr
    have hπ : Real.pi ^ (σ - 1 / 2) ≤ Real.pi := by
      calc Real.pi ^ (σ - 1 / 2) ≤ Real.pi ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
        _ = Real.pi := Real.rpow_one _
    have hτt : τ ^ (-(σ - 1 / 2)) ≤ 2 * |t| ^ (1 / 2 - σ) := by
      rw [hτ, Real.div_rpow ht0.le (by norm_num), show -(σ - 1 / 2) = 1 / 2 - σ by ring]
      have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 - σ) := by
        calc (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
          _ ≤ (2 : ℝ) ^ (1 / 2 - σ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [div_le_iff₀ (by positivity)]
      have hpos : 0 ≤ |t| ^ (1 / 2 - σ) := by positivity
      nlinarith
    calc Real.pi ^ (σ - 1 / 2) * Gb / Ga = Real.pi ^ (σ - 1 / 2) * (Gb / Ga) := by ring
      _ ≤ Real.pi * (C' * (2 * |t| ^ (1 / 2 - σ))) :=
          mul_le_mul hπ (hq.trans (mul_le_mul_of_nonneg_left hτt hC'.le)) (by positivity)
            (by positivity)
      _ = 2 * Real.pi * C' * |t| ^ (1 / 2 - σ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **`χ` in the strip**: `|χ(σ + it)| ≤ C |t|^{½−σ}` for `0 ≤ σ ≤ 1`, `|t| ≥ 1`. -/
theorem exists_norm_zetaChi_le_strip :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ (1 / 2 - σ) := by
  obtain ⟨C₁, hC₁, hhigh⟩ := exists_norm_zetaChi_le_strip_high
  let K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Icc (0 : ℝ) 1 ×ˢ (Icc (-2 : ℝ) (-1) ∪ Icc 1 2))
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)).image (by fun_prop)
  have hcont : ContinuousOn zetaChi K := by
    rintro z ⟨p, hp, rfl⟩
    refine (zetaChi_analyticAt_of_im_ne ?_).continuousAt.continuousWithinAt
    obtain ⟨-, hp2⟩ := hp
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add,
      add_zero]
    rcases hp2 with h | h <;> [linarith [h.2]; linarith [h.1]]
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ (2 * max M 0), le_trans hC₁ (le_max_left _ _), fun σ t h0 h1 ht => ?_⟩
  have hpos : 0 ≤ |t| ^ (1 / 2 - σ) := by positivity
  rcases le_or_gt 2 |t| with h2 | h2
  · exact (hhigh σ t h0 h1 h2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos)
  · have hmem : (σ : ℂ) + (t : ℂ) * I ∈ K := by
      refine ⟨(σ, t), ⟨⟨h0, h1⟩, ?_⟩, rfl⟩
      rcases le_or_gt 0 t with htt | htt
      · rw [abs_of_nonneg htt] at ht h2; exact Or.inr ⟨ht, h2.le⟩
      · rw [abs_of_neg htt] at ht h2; exact Or.inl ⟨by linarith, by linarith⟩
    have hb := hM _ hmem
    have hlow : (1 / 2 : ℝ) ≤ |t| ^ (1 / 2 - σ) := by
      have ht0 : 0 < |t| := by linarith
      calc (1 / 2 : ℝ) ≤ |t| ^ (-1 : ℝ) := by
            rw [Real.rpow_neg_one, ← one_div]
            exact div_le_div_of_nonneg_left zero_le_one ht0 h2.le
        _ ≤ |t| ^ (1 / 2 - σ) := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
    calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ max M 0 := hb.trans (le_max_left _ _)
      _ = 2 * max M 0 * (1 / 2) := by ring
      _ ≤ 2 * max M 0 * |t| ^ (1 / 2 - σ) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpos

/-! ## The zero side -/

theorem norm_gaussWeight_le_of_strip {T : ℝ} (hT : 1 ≤ T) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    ‖gaussWeight T w‖ ≤ Real.exp 1 * Real.exp (-(w.im ^ 2 / T ^ 2)) := by
  rw [norm_gaussWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hT2 : 1 ≤ T ^ 2 := by nlinarith
  have hsq : (w.re - 1 / 2) ^ 2 ≤ 1 := by nlinarith
  have : (w.re - 1 / 2) ^ 2 / T ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [sub_div]
  linarith

/-- **The zero side.** If `H` vanishes at the critical zeros and `|H(ρ)| ≤ K γ^{|β−½|}` at the other
zeros of the strip with `γ ≥ 1`, then for every `ε > 0` and all large `T`,
`|Σ m_ρ H(ρ) g_T(ρ)| ≤ 2eK ε T log² T`. -/
theorem eventually_norm_zeroSum_le {H : ℂ → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hcrit : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → 1 ≤ ρ.im → H ρ = 0)
    (hoff : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≠ 1 / 2 → 1 ≤ ρ.im →
      ‖H ρ‖ ≤ K * Real.exp (|ρ.re - 1 / 2| * Real.log ρ.im))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Y : ℝ, bottomHeight ≤ Y →
      ‖∑ w ∈ rectZeros bottomHeight Y, (mult w : ℂ) * (H w * gaussWeight T w)‖ ≤
        2 * Real.exp 1 * K * (ε * T * Real.log T ^ 2) := by
  classical
  filter_upwards [RHTower.eventually_offLineWeight_le hε, eventually_ge_atTop 1] with T hT hT1 Y hY
  have hb := one_le_bottomHeight
  have hY1 : 1 ≤ Y := hb.trans hY
  set Z := rectZeros bottomHeight Y with hZ
  set B := (RHTower.blockZeros 1 Y).filter (fun w => 1 / 2 < w.re) with hB
  set φ : ℂ → ℝ := fun w => RHTower.zeroMult w * (Real.exp ((w.re - 1 / 2) * Real.log w.im) *
    Real.exp (-(w.im ^ 2 / T ^ 2))) with hφ
  have hφ0 : ∀ w, 0 ≤ φ w := fun w => mul_nonneg (RHTower.zeroMult_nonneg w) (by positivity)
  have hBsum : ∑ w ∈ B, φ w ≤ ε * T * Real.log T ^ 2 := hT Y hY1
  set f : ℂ → ℝ := fun w => (mult w : ℝ) * (‖H w‖ * ‖gaussWeight T w‖) with hf
  have hnorm : ‖∑ w ∈ Z, (mult w : ℂ) * (H w * gaussWeight T w)‖ ≤ ∑ w ∈ Z, f w := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun w _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_natCast]
  -- pointwise bounds
  have hmemB : ∀ w : ℂ, riemannZeta w = 0 → 1 / 2 < w.re → w.re < 1 → 1 ≤ w.im → w.im ≤ Y →
      w ∈ B := by
    intro w hz h0 h1 him1 him2
    rw [hB, Finset.mem_filter, RHTower.mem_blockZeros_iff hY1]
    have hw1 : w ≠ 1 := ne_one_of_im_pos (by linarith)
    exact ⟨⟨⟨h0.le, by linarith⟩, ⟨him1, him2⟩, (riemannZeta_eq_zero_iff_zetaResidueUnit hw1).mpr hz⟩, h0⟩
  have hright : ∀ w ∈ Z.filter (fun w => 1 / 2 < w.re), f w ≤ Real.exp 1 * K * φ w := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hz, h0, h1, him1, -⟩ := rectZeros_facts hY hw.1
    have hH := hoff w hz h0 h1 (ne_of_gt hw.2) (hb.trans him1)
    rw [abs_of_pos (by linarith [hw.2])] at hH
    have hg := norm_gaussWeight_le_of_strip hT1 h0 h1
    simp only [hf, hφ, RHTower.zeroMult]
    calc (mult w : ℝ) * (‖H w‖ * ‖gaussWeight T w‖)
        ≤ (mult w : ℝ) * ((K * Real.exp ((w.re - 1 / 2) * Real.log w.im)) *
          (Real.exp 1 * Real.exp (-(w.im ^ 2 / T ^ 2)))) := by gcongr
      _ = _ := by simp only [mult]; ring
  have hleft : ∀ w ∈ Z.filter (fun w => w.re < 1 / 2), f w ≤ Real.exp 1 * K * φ (reflectZero w) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hz, h0, h1, him1, -⟩ := rectZeros_facts hY hw.1
    have hH := hoff w hz h0 h1 (ne_of_lt hw.2) (hb.trans him1)
    rw [abs_of_neg (by linarith [hw.2])] at hH
    have hg := norm_gaussWeight_le_of_strip hT1 h0 h1
    have hm : RHTower.zeroMult (reflectZero w) = (mult w : ℝ) := by
      have := mult_reflectZero h0 h1
      simp only [RHTower.zeroMult]
      exact_mod_cast this
    simp only [hf, hφ, hm, reflectZero_re, reflectZero_im]
    calc (mult w : ℝ) * (‖H w‖ * ‖gaussWeight T w‖)
        ≤ (mult w : ℝ) * ((K * Real.exp (-(w.re - 1 / 2) * Real.log w.im)) *
          (Real.exp 1 * Real.exp (-(w.im ^ 2 / T ^ 2)))) := by gcongr
      _ = _ := by ring_nf
  have hcrit' : ∀ w ∈ Z.filter (fun w => ¬ (w.re < 1 / 2)),
      w ∈ Z.filter (fun w => ¬ (1 / 2 < w.re)) → f w = 0 := by
    intro w hw hw'
    rw [Finset.mem_filter] at hw hw'
    obtain ⟨hz, -, -, him1, -⟩ := rectZeros_facts hY hw.1
    have hre : w.re = 1 / 2 := le_antisymm (not_lt.mp hw'.2) (not_lt.mp hw.2)
    simp only [hf, hcrit w hz hre (hb.trans him1), norm_zero, zero_mul, mul_zero]
  -- the split
  have hsplit : ∑ w ∈ Z, f w ≤ ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), f w +
      ∑ w ∈ Z.filter (fun w => w.re < 1 / 2), f w := by
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun w => w.re < 1 / 2)]
    have hrest : ∑ w ∈ Z.filter (fun w => ¬ (w.re < 1 / 2)), f w ≤
        ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), f w := by
      rw [← Finset.sum_filter_add_sum_filter_not (Z.filter (fun w => ¬ (w.re < 1 / 2)))
        (fun w => 1 / 2 < w.re)]
      have hz0 : ∑ w ∈ (Z.filter (fun w => ¬ (w.re < 1 / 2))).filter (fun w => ¬ (1 / 2 < w.re)),
          f w = 0 := by
        refine Finset.sum_eq_zero fun w hw => ?_
        rw [Finset.mem_filter] at hw
        exact hcrit' w hw.1 (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw.1).1, hw.2⟩)
      rw [hz0, add_zero]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_)
        (fun w _ _ => by simp only [hf]; positivity)
      rw [Finset.mem_filter] at hw ⊢
      exact ⟨(Finset.mem_filter.mp hw.1).1, hw.2⟩
    linarith
  have hR : ∑ w ∈ Z.filter (fun w => 1 / 2 < w.re), f w ≤ Real.exp 1 * K * ∑ w ∈ B, φ w := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hright).trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun w _ _ => mul_nonneg (by positivity) (hφ0 w)))
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hz, h0, h1, him1, him2⟩ := rectZeros_facts hY hw.1
    exact hmemB w hz hw.2 h1 (hb.trans him1) him2
  have hL : ∑ w ∈ Z.filter (fun w => w.re < 1 / 2), f w ≤ Real.exp 1 * K * ∑ w ∈ B, φ w := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hleft).trans ?_
    rw [← Finset.sum_image (f := fun w => Real.exp 1 * K * φ w)
      (fun x _ y _ hxy => by
        have := congrArg reflectZero hxy
        rwa [reflectZero_reflectZero, reflectZero_reflectZero] at this)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun w _ _ => mul_nonneg (by positivity) (hφ0 w))
    intro w' hw'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
    rw [Finset.mem_filter] at hw
    obtain ⟨hz, h0, h1, him1, him2⟩ := rectZeros_facts hY hw.1
    refine hmemB _ (riemannZeta_reflectZero hz h0 h1) (by rw [reflectZero_re]; linarith [hw.2])
      (by rw [reflectZero_re]; linarith) (by rw [reflectZero_im]; linarith) ?_
    rw [reflectZero_im]; exact him2
  calc ‖∑ w ∈ Z, (mult w : ℂ) * (H w * gaussWeight T w)‖ ≤ ∑ w ∈ Z, f w := hnorm
    _ ≤ Real.exp 1 * K * ∑ w ∈ B, φ w + Real.exp 1 * K * ∑ w ∈ B, φ w :=
        hsplit.trans (add_le_add hR hL)
    _ ≤ Real.exp 1 * K * (ε * T * Real.log T ^ 2) + Real.exp 1 * K * (ε * T * Real.log T ^ 2) := by
        gcongr
    _ = _ := by ring

end

end RHTower.GaussZeroSum
