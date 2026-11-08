import GaloisForLFunctions.BlackHoleRingdown.TheVerticalDecayOfTheRankinSelbergFunction
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound

/-!
# Polynomial growth of the Rankin–Selberg L-function

For a cusp form `g` let `φ_g = (s - 1) Λ_g / c` be the normalized Rankin–Selberg function of the mean-square
module, so that `φ_g(s)/(s - 1) = Σ_m (|ρ(m)|² + |ρ(-m)|²) m^{-s}` on `Re s > 1`, with
`c(s) = ξ(2s)/(2s(2s-1)) · (2π)^{-s} G(s)`.

**Theorem** (`exists_rsPhi_poly`). On every strip `a ≤ Re s ≤ 5/4`, `a > ½`,
`|φ_g(s)| ≤ C (1 + |Im s|)^N`.

**Proof.** `c(s) = π^{-s} ζ(2s) 2^{s-3} Γ(s/2+ν) Γ(s/2)² Γ(s/2-ν) (2π)^{-s}/2` (the `Γ(s)` cancels), so
`|1/c(s)| ≪ (1 + |t|)^4 e^{π|t|}` from `|Γ(σ+iy)|⁻¹ ≤ C|y|^{½-σ} e^{π|y|/2}` on `0 ≤ σ ≤ 1`, `|1/ζ(2s)| ≤ 1 + 1/(2a-1)`,
and `|t/2+t₀| + |t/2| + |t/2| + |t/2-t₀| ≤ 2|t| + 2|t₀|`. The completed function decays like
`(1+|t|)^N e^{-π|t|}` (vertical decay module), and the exponentials cancel. Near the real axis `φ_g` is
holomorphic, hence bounded on compact boxes.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspRSL

open HeckeCusp CuspL CuspRSC CuspMS CuspRSV

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-- `c(s) = π^{-s} ζ(2s) 2^{s-3} Γ(s/2+ν) Γ(s/2)² Γ(s/2-ν) (2π)^{-s}/2` for `Re s > 0`, `s ≠ ½`. -/
theorem rsFactor_eq_gamma {w : ℂ} (hw : 0 < w.re) (h1 : w ≠ 1 / 2) :
    rsFactor lamE w = (Real.pi : ℂ) ^ (-w) * riemannZeta (2 * w) * (2 : ℂ) ^ (w - 3) *
      (Gamma ((w + nu lamE + nu lamE) / 2) * Gamma ((w + nu lamE - nu lamE) / 2) *
        Gamma ((w - nu lamE + nu lamE) / 2) * Gamma ((w - nu lamE - nu lamE) / 2)) *
      (2 * Real.pi : ℂ) ^ (-w) / 2 := by
  have h := xi_mul_gammaFactor hw h1 (nu lamE)
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h2 : 2 * w - 1 ≠ 0 := fun h => h1 (by linear_combination h / 2)
  unfold rsFactor
  rw [show xi (2 * w) / (2 * w * (2 * w - 1)) * ((2 * Real.pi : ℂ) ^ (-w) * CuspRSI.gammaFactor (nu lamE) w) =
    (xi (2 * w) * CuspRSI.gammaFactor (nu lamE) w) * (2 * Real.pi : ℂ) ^ (-w) / (2 * w * (2 * w - 1)) by ring,
    h, div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hw0) h2) two_ne_zero]
  ring

/-- `‖Γ(z)⁻¹‖ ≤ C (1 + |Im z|) e^{π|Im z|/2}` for `0 ≤ Re z ≤ 1`, `|Im z| ≥ 1`. -/
theorem exists_norm_inv_Gamma_le_lin : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ |z.im| →
    ‖(Gamma z)⁻¹‖ ≤ C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) := by
  obtain ⟨C, hC, h⟩ := GaloisForLFunctions.HTGeometry.exists_norm_inv_Gamma_le_sharp
  refine ⟨C, hC.le, fun z h1 h2 ht => ?_⟩
  have hb := h z.re z.im h1 h2 ht
  rw [Complex.re_add_im] at hb
  have hp : |z.im| ^ (1 / 2 - z.re) ≤ 1 + |z.im| := by
    calc |z.im| ^ (1 / 2 - z.re) ≤ |z.im| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
      _ ≤ 1 + |z.im| := by rw [Real.rpow_one]; linarith
  calc _ ≤ C * |z.im| ^ (1 / 2 - z.re) * Real.exp (Real.pi * |z.im| / 2) := hb
    _ ≤ C * (1 + |z.im|) * Real.exp (Real.pi * |z.im| / 2) := by gcongr

/-- **`|1/c(s)| ≪ (1 + |t|)^4 e^{π|t|}`** on `a ≤ Re s ≤ 5/4`, `|t| ≥ T₀`. -/
theorem exists_norm_inv_rsFactor_le {a : ℝ} (ha : 1 / 2 < a) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 1 ≤ T₀ ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 5 / 4 → T₀ ≤ |w.im| →
      ‖(rsFactor lamE w)⁻¹‖ ≤ C * (1 + |w.im|) ^ 4 * Real.exp (Real.pi * |w.im|) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_norm_inv_Gamma_le_lin
  set t₀ := Real.sqrt (lamE - 1 / 4)
  have ht₀ : 0 ≤ |t₀| := abs_nonneg _
  set Kζ := 1 + 1 / (2 * a - 1)
  have hKζ : 0 ≤ Kζ := by have : 0 < 2 * a - 1 := by linarith
                          positivity
  refine ⟨2 * Real.pi ^ 2 * Kζ * 8 * (2 * Real.pi) ^ 2 * (CΓ ^ 4 * (1 + |t₀|) ^ 4 *
    Real.exp (Real.pi * |t₀|)), 2 * |t₀| + 2, by positivity, by linarith, fun w h1 h2 ht => ?_⟩
  set σ := w.re
  set T := w.im
  have hw0 : 0 < w.re := by linarith
  have hT1 : 1 ≤ |T| := by linarith
  have hw1 : w ≠ 1 / 2 := fun h => by
    have h' : w.im = 0 := by rw [h]; simp
    simp only [T] at hT1; rw [h'] at hT1; norm_num at hT1
  have hν : nu lamE = (t₀ : ℂ) * I := rfl
  have hseq : w = (σ : ℂ) + (T : ℂ) * I := (Complex.re_add_im w).symm
  have e1 : (w + nu lamE + nu lamE) / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 + t₀ : ℝ) : ℂ) * I := by
    rw [hseq, hν]; push_cast; ring
  have e2 : (w + nu lamE - nu lamE) / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by
    rw [show (w + nu lamE - nu lamE) / 2 = w / 2 by ring, hseq]; push_cast; ring
  have e3 : (w - nu lamE + nu lamE) / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by
    rw [show (w - nu lamE + nu lamE) / 2 = w / 2 by ring, hseq]; push_cast; ring
  have e4 : (w - nu lamE - nu lamE) / 2 = ((σ / 2 : ℝ) : ℂ) + ((T / 2 - t₀ : ℝ) : ℂ) * I := by
    rw [hseq, hν]; push_cast; ring
  set X := 1 + |T|
  have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg T]
  have hhalf : |T / 2| = |T| / 2 := by rw [abs_div, abs_two]
  have hy1 : 1 ≤ |T / 2 + t₀| := by
    have := abs_sub_abs_le_abs_sub (T / 2) (-t₀)
    rw [sub_neg_eq_add, abs_neg] at this
    rw [hhalf] at this; linarith
  have hy4 : 1 ≤ |T / 2 - t₀| := by
    have := abs_sub_abs_le_abs_sub (T / 2) t₀
    rw [hhalf] at this; linarith
  have hy2 : 1 ≤ |T / 2| := by rw [hhalf]; linarith
  have hσ1 : 0 ≤ σ / 2 := by linarith
  have hσ2 : σ / 2 ≤ 1 := by linarith
  have hg : ∀ y : ℝ, 1 ≤ |y| → ‖(Gamma (((σ / 2 : ℝ) : ℂ) + (y : ℂ) * I))⁻¹‖ ≤
      CΓ * (1 + |y|) * Real.exp (Real.pi * |y| / 2) := fun y hy => by
    have := hΓ (((σ / 2 : ℝ) : ℂ) + (y : ℂ) * I) (by simpa using hσ1) (by simpa using hσ2) (by simpa using hy)
    simpa using this
  have hp1 : 1 + |T / 2 + t₀| ≤ (1 + |t₀|) * X := by
    have := abs_add_le (T / 2) t₀; simp only [X]; rw [hhalf] at this; nlinarith [abs_nonneg T]
  have hp4 : 1 + |T / 2 - t₀| ≤ (1 + |t₀|) * X := by
    have := abs_sub (T / 2) t₀; simp only [X]; rw [hhalf] at this; nlinarith [abs_nonneg T]
  have hp2 : 1 + |T / 2| ≤ (1 + |t₀|) * X := by
    simp only [X]; rw [hhalf]; nlinarith [abs_nonneg T]
  have hsum : |T / 2 + t₀| + |T / 2| + |T / 2| + |T / 2 - t₀| ≤ 2 * |T| + 2 * |t₀| := by
    have := abs_add_le (T / 2) t₀; have := abs_sub (T / 2) t₀; rw [hhalf] at *; linarith
  have hGam : ‖(Gamma ((w + nu lamE + nu lamE) / 2) * Gamma ((w + nu lamE - nu lamE) / 2) *
      Gamma ((w - nu lamE + nu lamE) / 2) * Gamma ((w - nu lamE - nu lamE) / 2))⁻¹‖ ≤
      CΓ ^ 4 * (1 + |t₀|) ^ 4 * Real.exp (Real.pi * |t₀|) * (X ^ 4 * Real.exp (Real.pi * |T|)) := by
    rw [e1, e2, e3, e4, mul_inv, mul_inv, mul_inv, norm_mul, norm_mul, norm_mul]
    calc _ ≤ (CΓ * (1 + |T / 2 + t₀|) * Real.exp (Real.pi * |T / 2 + t₀| / 2)) *
          (CΓ * (1 + |T / 2|) * Real.exp (Real.pi * |T / 2| / 2)) *
          (CΓ * (1 + |T / 2|) * Real.exp (Real.pi * |T / 2| / 2)) *
          (CΓ * (1 + |T / 2 - t₀|) * Real.exp (Real.pi * |T / 2 - t₀| / 2)) := by
          gcongr
          · exact hg _ hy1
          · exact hg _ hy2
          · exact hg _ hy2
          · exact hg _ hy4
      _ ≤ (CΓ * ((1 + |t₀|) * X) * Real.exp (Real.pi * |T / 2 + t₀| / 2)) *
          (CΓ * ((1 + |t₀|) * X) * Real.exp (Real.pi * |T / 2| / 2)) *
          (CΓ * ((1 + |t₀|) * X) * Real.exp (Real.pi * |T / 2| / 2)) *
          (CΓ * ((1 + |t₀|) * X) * Real.exp (Real.pi * |T / 2 - t₀| / 2)) := by gcongr
      _ = CΓ ^ 4 * (1 + |t₀|) ^ 4 * X ^ 4 *
          Real.exp (Real.pi * (|T / 2 + t₀| + |T / 2| + |T / 2| + |T / 2 - t₀|) / 2) := by
          rw [show Real.pi * (|T / 2 + t₀| + |T / 2| + |T / 2| + |T / 2 - t₀|) / 2 =
            Real.pi * |T / 2 + t₀| / 2 + Real.pi * |T / 2| / 2 + Real.pi * |T / 2| / 2 +
              Real.pi * |T / 2 - t₀| / 2 by ring, Real.exp_add, Real.exp_add, Real.exp_add]
          ring
      _ ≤ CΓ ^ 4 * (1 + |t₀|) ^ 4 * X ^ 4 * Real.exp (Real.pi * |T| + Real.pi * |t₀|) := by
          gcongr; nlinarith [Real.pi_pos]
      _ = _ := by rw [Real.exp_add]; ring
  have hζ : ‖(riemannZeta (2 * w))⁻¹‖ ≤ Kζ := by
    have := _root_.RHTower.norm_inv_riemannZeta_le_of_le_re (σ₁ := 2 * a) (by linarith) (s := 2 * w)
      (by simp; linarith)
    simpa [Kζ, show 2 * a - 1 = 2 * a - 1 from rfl] using this
  have hpi : ‖((Real.pi : ℂ) ^ (-w))⁻¹‖ ≤ Real.pi ^ 2 := by
    rw [norm_inv, norm_cpow_eq_rpow_re_of_pos Real.pi_pos, neg_re, Real.rpow_neg Real.pi_pos.le, inv_inv]
    calc Real.pi ^ w.re ≤ Real.pi ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = Real.pi ^ 2 := by norm_num
  have h2pi : ‖((2 * Real.pi : ℂ) ^ (-w))⁻¹‖ ≤ (2 * Real.pi) ^ 2 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_inv,
      norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re, Real.rpow_neg (by positivity), inv_inv]
    calc (2 * Real.pi) ^ w.re ≤ (2 * Real.pi) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = (2 * Real.pi) ^ 2 := by norm_num
  have h8 : ‖((2 : ℂ) ^ (w - 3))⁻¹‖ ≤ 8 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_inv, norm_cpow_eq_rpow_re_of_pos (by norm_num),
      sub_re, show ((3 : ℂ)).re = 3 by norm_num, ← Real.rpow_neg (by norm_num), neg_sub]
    calc (2 : ℝ) ^ (3 - w.re) ≤ (2 : ℝ) ^ (3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by norm_num
  rw [norm_inv] at hpi hζ h8 h2pi hGam
  rw [rsFactor_eq_gamma hw0 hw1]
  generalize Gamma ((w + nu lamE + nu lamE) / 2) * Gamma ((w + nu lamE - nu lamE) / 2) *
      Gamma ((w - nu lamE + nu lamE) / 2) * Gamma ((w - nu lamE - nu lamE) / 2) = Gp at hGam ⊢
  rw [norm_inv, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  calc ‖(Real.pi : ℂ) ^ (-w)‖⁻¹ * ‖riemannZeta (2 * w)‖⁻¹ * ‖(2 : ℂ) ^ (w - 3)‖⁻¹ * ‖Gp‖⁻¹ *
        ‖(2 * Real.pi : ℂ) ^ (-w)‖⁻¹ * 2
      ≤ Real.pi ^ 2 * Kζ * 8 * (CΓ ^ 4 * (1 + |t₀|) ^ 4 * Real.exp (Real.pi * |t₀|) *
        (X ^ 4 * Real.exp (Real.pi * |T|))) * (2 * Real.pi) ^ 2 * 2 := by gcongr
    _ = _ := by ring

/-- **The normalized Rankin–Selberg function grows at most polynomially** on `a ≤ Re s ≤ 5/4`, `a > ½`. -/
theorem exists_rsPhi_poly (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {a : ℝ} (ha : 1 / 2 < a) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 5 / 4 →
      ‖rsPhi lamE g w‖ ≤ C * (1 + |w.im|) ^ N := by
  obtain ⟨Cr, T₀, hCr, hT₀, hr⟩ := exists_norm_inv_rsFactor_le (lamE := lamE) ha
  obtain ⟨CΛ, NΛ, hCΛ, hΛ⟩ := exists_norm_completedRS_le hg hρ0 hρ
  have hbox : IsCompact (Icc a (5 / 4) ×ℂ Icc (-T₀) T₀) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn (f := rsPhi lamE g) fun w hw =>
    (differentiableAt_rsPhi hg hρ0 hρ (by have := hw.1.1; linarith)).continuousAt.continuousWithinAt
  set B' := max B 0
  have hB0 : 0 ≤ B' := le_max_right _ _
  refine ⟨B' + Cr * CΛ, NΛ + 5, by positivity, fun w h1 h2 => ?_⟩
  set X := 1 + |w.im|
  have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg w.im]
  have hXp : 1 ≤ X ^ (NΛ + 5) := one_le_pow₀ hX
  rcases lt_or_ge |w.im| T₀ with ht | ht
  · have hmem : w ∈ Icc a (5 / 4) ×ℂ Icc (-T₀) T₀ := by
      rw [mem_reProdIm]
      exact ⟨⟨h1, h2⟩, ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩⟩
    calc ‖rsPhi lamE g w‖ ≤ B' := (hB w hmem).trans (le_max_left _ _)
      _ ≤ B' * X ^ (NΛ + 5) := le_mul_of_one_le_right hB0 hXp
      _ ≤ (B' + Cr * CΛ) * X ^ (NΛ + 5) := by
          gcongr; have : 0 ≤ Cr * CΛ := by positivity
          linarith
  · have ht1 : 1 ≤ |w.im| := le_trans hT₀ ht
    have him : w.im ≠ 0 := fun h => by rw [h] at ht1; norm_num at ht1
    have hw0 : w ≠ 0 := fun h => him (by rw [h]; simp)
    have hw1 : w ≠ 1 / 2 := fun h => him (by rw [h]; simp)
    have hw2 : w ≠ 1 := fun h => him (by rw [h]; simp)
    have hwn : ‖w - 1‖ ≤ X := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have hre : |(w - 1).re| ≤ 1 := by
        rw [sub_re, one_re, abs_le]; constructor <;> linarith
      have : (w - 1).im = w.im := by simp
      rw [this]; simp only [X]; linarith
    have hL := hΛ w (by linarith) h2 ht1
    have hR := hr w h1 h2 ht
    rw [rsPhi, residueRS_eq hw0 hw1 hw2, div_eq_mul_inv, norm_mul, norm_mul]
    have hE : Real.exp (-(Real.pi * |w.im|)) * Real.exp (Real.pi * |w.im|) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖w - 1‖ * ‖completedRS g w‖ * ‖(rsFactor lamE w)⁻¹‖
        ≤ X * (CΛ * X ^ NΛ * Real.exp (-(Real.pi * |w.im|))) *
          (Cr * X ^ 4 * Real.exp (Real.pi * |w.im|)) := by gcongr
      _ = Cr * CΛ * (X * X ^ NΛ * X ^ 4) *
          (Real.exp (-(Real.pi * |w.im|)) * Real.exp (Real.pi * |w.im|)) := by ring
      _ = Cr * CΛ * X ^ (NΛ + 5) := by rw [hE, mul_one]; ring
      _ ≤ (B' + Cr * CΛ) * X ^ (NΛ + 5) := by gcongr; linarith

end CuspRSL

end GaloisForLFunctions.BlackHoleRingdown
