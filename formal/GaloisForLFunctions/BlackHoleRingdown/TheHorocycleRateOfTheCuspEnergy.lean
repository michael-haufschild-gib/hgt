import GaloisForLFunctions.BlackHoleRingdown.TheVerticalDecayOfTheRankinSelbergFunction
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleEquidistributionOfTheCuspEnergy
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateOfTheCuspEnergyReadsTheZeros
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateIsTheZeroFreeRegion
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound

/-!
# The horocycle rate of the cusp energy

For a cusp form `g` of the modular horizon, the energy `m(y) = ∫_{-1/2}^{1/2} |g(x+iy)|² dx` along the
closed horocycle of height `y` equidistributes at a rate set by the zero-free region of `ζ`:

* unconditionally, `|m(y) - (3/π)‖g‖²| ≤ C y^{½ - ε}` on `(0, 1]` (`horocycle_energy_rate`);
* under the Riemann hypothesis, `|m(y) - (3/π)‖g‖²| ≤ C y^{¾ - ε}` (`horocycle_energy_rate_of_RH`);
* in general, a zero-free half-plane `Re z > θ` with polynomial bounds for `1/ζ` gives the rate
  `y^{1 - θ/2 - ε}` (`norm_mass_sub_le_of_zeroFree`).

Together with `CuspHR.not_rate_of_ne_zero` this is a quadratic Zagier dichotomy for the ringdown modes:
under RH every cusp energy reaches `y^{¾-ε}`, and a zero `ρ` off the line with `Λ_g(ρ/2) ≠ 0` keeps `g`
from reaching `y^{1 - Re ρ/2}`.

**Proof.** For `Re w > 0` the Mellin transform of `m - c e^{-y}` is
`Ψ(w) = N(w+1)/w`, `N(s) = 4P_g(s)/ξ(2s) - c Γ(s)`, `P_g = s(s-½)(s-1)Λ_g` entire, and `c = 4P_g(1)/ξ(2)` makes
`N(1) = 0`, so `Ψ = dslope N 1 (· + 1)` is holomorphic on `Re w > θ/2 - 1`. With `ξ(2s) = s(2s-1)π^{-s}Γ(s)ζ(2s)`,
the decay `|P_g| ≪ |t|^N e^{-π|t|}`, the lower bound `|Γ(s)| ≫ |t|^{-1} e^{-π|t|/2}` and the bound for
`1/ζ(2s)`, `Ψ` decays like `|t|^N e^{-π|t|/2}` on closed substrips. Mellin inversion on `Re w = 1/8` and the
contour shift to `Re w = θ/2 - 1 + ε` give `|m(y) - c e^{-y}| ≤ K y^{1 - θ/2 - ε}`. The constant is identified
by the equidistribution theorem: `c = (3/π)‖g‖²`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspHRate

open HeckeCusp CuspL CuspRSC CuspRSV CuspHR

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-! ### Gamma and `ξ(2s)` -/

/-- `ξ(2s) = s(2s-1) π^{-s} Γ(s) ζ(2s)` for `Re s > 0`, `s ≠ ½`. -/
theorem xi_two_mul_eq_gamma {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1 / 2) :
    xi (2 * s) = s * (2 * s - 1) * (Real.pi : ℂ) ^ (-s) * Gamma s * riemannZeta (2 * s) := by
  have h20 : 2 * s ≠ 0 := mul_ne_zero two_ne_zero fun h => by rw [h] at hs; simp at hs
  have h21 : 2 * s ≠ 1 := fun h => h1 (by linear_combination h / 2)
  have hΓ : Gammaℝ (2 * s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΛ : completedRiemannZeta (2 * s) = riemannZeta (2 * s) * Gammaℝ (2 * s) := by
    rw [riemannZeta_def_of_ne_zero h20, div_mul_cancel₀ _ hΓ]
  have hG : Gammaℝ (2 * s) = (Real.pi : ℂ) ^ (-s) * Gamma s := by
    rw [Gammaℝ_def, show -(2 * s) / 2 = -s by ring, show 2 * s / 2 = s by ring]
  rw [xi_eq_half_mul h20 h21, hΛ, hG]
  ring

/-- `|Γ(s)|⁻¹ ≤ C (1 + |t|) e^{π|t|/2}` on `a ≤ Re s ≤ 5/4`, `|t| ≥ 1`, for `a > 0`. -/
theorem exists_norm_inv_Gamma_le {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ 5 / 4 → 1 ≤ |s.im| →
      ‖(Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) * Real.exp (Real.pi * |s.im| / 2) := by
  obtain ⟨C, hC, h⟩ := GaloisForLFunctions.HTGeometry.exists_norm_inv_Gamma_le_sharp
  refine ⟨C, hC.le, fun s h1 h2 ht => ?_⟩
  have hpow : ∀ σ : ℝ, 0 ≤ σ → |s.im| ^ (1 / 2 - σ) ≤ 1 + |s.im| := fun σ hσ => by
    calc |s.im| ^ (1 / 2 - σ) ≤ |s.im| ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht (by linarith)
      _ ≤ 1 + |s.im| := by rw [Real.rpow_one]; linarith
  rcases le_or_gt s.re 1 with hs1 | hs1
  · have hb := h s.re s.im (by linarith) hs1 ht
    rw [Complex.re_add_im] at hb
    calc _ ≤ C * |s.im| ^ (1 / 2 - s.re) * Real.exp (Real.pi * |s.im| / 2) := hb
      _ ≤ C * (1 + |s.im|) * Real.exp (Real.pi * |s.im| / 2) := by
          gcongr; exact hpow _ (by linarith)
  · have hb := h (s.re - 1) s.im (by linarith) (by linarith) ht
    have hs' : ((s.re - 1 : ℝ) : ℂ) + (s.im : ℂ) * I = s - 1 := by
      apply Complex.ext <;> simp
    rw [hs'] at hb
    have hs0 : s - 1 ≠ 0 := fun h0 => by
      have := congrArg Complex.im h0; simp at this; rw [this] at ht; norm_num at ht
    have hΓ : Gamma s = (s - 1) * Gamma (s - 1) := by
      rw [← Complex.Gamma_add_one (s - 1) hs0, sub_add_cancel]
    have hn : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1); simp at this; linarith
    rw [hΓ, mul_inv, norm_mul, norm_inv]
    calc ‖s - 1‖⁻¹ * ‖(Gamma (s - 1))⁻¹‖ ≤ 1 * ‖(Gamma (s - 1))⁻¹‖ := by
          gcongr; exact inv_le_one_of_one_le₀ hn
      _ ≤ C * |s.im| ^ (1 / 2 - (s.re - 1)) * Real.exp (Real.pi * |s.im| / 2) := by rw [one_mul]; exact hb
      _ ≤ C * (1 + |s.im|) * Real.exp (Real.pi * |s.im| / 2) := by
          gcongr; exact hpow _ (by linarith)

/-! ### The regular part of the Mellin transform -/

/-- `c = 4 P_g(1)/ξ(2)`, the limit of the horocycle energy. -/
def rateConst (g : UpperHalfPlane → ℂ) : ℂ := 4 * entireRS g 1 / xi 2

/-- `N(s) = 4 P_g(s)/ξ(2s) - c Γ(s)`. -/
def poleNum (g : UpperHalfPlane → ℂ) (s : ℂ) : ℂ := 4 * entireRS g s / xi (2 * s) - rateConst g * Gamma s

/-- `Ψ(w) = N(w+1)/w`, regularised at `w = 0`. -/
def regPart (g : UpperHalfPlane → ℂ) (w : ℂ) : ℂ := dslope (poleNum g) 1 (w + 1)

theorem poleNum_one : poleNum g 1 = 0 := by
  simp [poleNum, rateConst, Complex.Gamma_one]

theorem regPart_eq {w : ℂ} (hw : w ≠ 0) : regPart g w = poleNum g (w + 1) / w := by
  rw [regPart, dslope_of_ne _ (by simpa using hw), slope_def_field, poleNum_one, sub_zero,
    add_sub_cancel_right]

theorem differentiableOn_poleNum (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {θ : ℝ} (hθ : 0 ≤ θ)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0) :
    DifferentiableOn ℂ (poleNum g) {s : ℂ | θ / 2 < s.re} := by
  intro s hs
  have hs' : θ / 2 < s.re := hs
  have hx : xi (2 * s) ≠ 0 := hZ _ (by simp; linarith)
  have hΓ : DifferentiableAt ℂ Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m hm => ?_
    have := congrArg Complex.re hm
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hxi : DifferentiableAt ℂ (fun s : ℂ => xi (2 * s)) s :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) s
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold poleNum
  exact (((differentiable_entireRS hg hρ0 hρ s).const_mul 4).div hxi hx).sub (hΓ.const_mul _)

theorem differentiableAt_regPart (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 2)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0) {w : ℂ} (hw : θ / 2 - 1 < w.re) :
    DifferentiableAt ℂ (regPart g) w := by
  have hU : IsOpen {s : ℂ | θ / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : {s : ℂ | θ / 2 < s.re} ∈ 𝓝 (1 : ℂ) := hU.mem_nhds (by simp; linarith)
  have hd := (Complex.differentiableOn_dslope h1).2 (differentiableOn_poleNum hg hρ0 hρ hθ0 hZ)
  have hw1 : w + 1 ∈ {s : ℂ | θ / 2 < s.re} := by simp; linarith
  have hdw := (hd _ hw1).differentiableAt (hU.mem_nhds hw1)
  exact hdw.comp w (differentiableAt_id.add_const 1)

/-- **The Mellin transform of `m - c e^{-y}` is `Ψ`** on `Re w > 0`, `Im w ≠ 0`. -/
theorem mellin_eq_regPart (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {w : ℂ} (hw : 0 < w.re)
    (him : w.im ≠ 0) :
    mellin (fun y => mass g y - rateConst g * ((Real.exp (-y) : ℝ) : ℂ)) w = regPart g w := by
  have hs : 1 < (w + 1).re := by simp; linarith
  have hsim : (w + 1).im ≠ 0 := by simpa using him
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hs0 : w + 1 ≠ 0 := fun h => hsim (by rw [h]; simp)
  have hs1 : w + 1 ≠ 1 / 2 := fun h => hsim (by rw [h]; simp)
  have hs2 : w + 1 ≠ 1 := fun h => hsim (by rw [h]; simp)
  have hA := mellinConvergent_mass hg hρ0 hρ hs
  rw [add_sub_cancel_right] at hA
  have hE := (mellinConvergent_exp_neg hw).const_smul (rateConst g)
  have hsplit : mellin (fun y => mass g y - rateConst g * ((Real.exp (-y) : ℝ) : ℂ)) w =
      mellin (mass g) w - rateConst g * mellin (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ)) w := by
    rw [mellin, mellin, mellin, ← integral_const_mul, ← integral_sub hA]
    · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [smul_eq_mul]
      ring
    · refine hE.congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [smul_eq_mul]
      ring
  have hM := mellin_mass hg hρ0 hρ hs
  rw [add_sub_cancel_right] at hM
  rw [hsplit, hM, mellin_exp_neg hw, regPart_eq hw0, poleNum, entireRS_eq hs0 hs1 hs2,
    completedRS_eq hg hρ0 hρ hs hsim, Complex.Gamma_add_one w hw0]
  have hx : xi (2 * (w + 1)) ≠ 0 := xi_ne_zero_of_one_lt_re (by simp; linarith)
  have hD : 2 * (w + 1) * (2 * (w + 1) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hs0) fun h => hs1 (by linear_combination h / 2)
  have hxi : xi (2 * (w + 1)) * (xi (2 * (w + 1)))⁻¹ = 1 := mul_inv_cancel₀ hx
  have hDi : 2 * (w + 1) * (2 * (w + 1) - 1) * (2 * (w + 1) * (2 * (w + 1) - 1))⁻¹ = 1 :=
    mul_inv_cancel₀ hD
  have hwi : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
  generalize (2 * Real.pi : ℂ) ^ (-(w + 1)) * CuspRSI.gammaFactor (nu lamE) (w + 1) *
    ∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-(w + 1)) = R at *
  generalize xi (2 * (w + 1)) = ξ at *
  generalize Gamma w = Γw at *
  generalize rateConst g = c at *
  simp only [div_eq_mul_inv]
  linear_combination (-R * (ξ * ξ⁻¹) * (w * w⁻¹)) * hDi + (-R * (w * w⁻¹)) * hxi + (-R + c * Γw) * hwi

/-! ### Regularity of `Ψ` -/

/-- **`Ψ` is regular** on `θ/2 - 1 < Re w < ¼`: holomorphic, and decaying faster than every power of
`|Im w|` on closed substrips. -/
theorem mellinRegularStrip_regPart (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0)
    (hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, θ + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N) :
    MellinRegularStrip (regPart g) (θ / 2 - 1) (1 / 4) := by
  refine ⟨fun w hw _ => differentiableAt_regPart hg hρ0 hρ hθ0 (by linarith) hZ hw,
    fun a' b' ha' hb' K => ?_⟩
  have hbox : IsCompact (Icc a' b' ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn (f := regPart g) (fun w hw => by
    have hw' : a' ≤ w.re := hw.1.1
    exact (differentiableAt_regPart hg hρ0 hρ hθ0 (by linarith) hZ (by linarith)).continuousAt
      |>.continuousWithinAt)
  obtain ⟨CP, NP, hCP, hPb⟩ := exists_norm_entireRS_le hg hρ0 hρ
  obtain ⟨CΓi, hCΓi, hΓi⟩ := exists_norm_inv_Gamma_le (a := a' + 1) (by linarith)
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip
    (a' + 1) (b' + 1)
  obtain ⟨Kz, Nz, hKz, hz⟩ := hP (2 * (a' + 1) - θ) (by linarith) (2 * (b' + 1))
  set c := rateConst g
  set N₁ := NP + 1 + Nz
  set C₁ := 4 * CP * Real.pi ^ 2 * CΓi * (Kz * 2 ^ Nz)
  set Nn := N₁ + NΓ
  set Cn := C₁ + ‖c‖ * CΓ
  obtain ⟨Ce, hCe, hCe'⟩ := exists_pow_mul_exp_le Nn K
  have hpi2 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  -- the pole numerator off the real axis
  have hN : ∀ s : ℂ, a' + 1 ≤ s.re → s.re ≤ b' + 1 → 1 ≤ |s.im| →
      ‖poleNum g s‖ ≤ Cn * (1 + |s.im|) ^ Nn * Real.exp (-(Real.pi * |s.im| / 2)) := by
    intro s h1 h2 ht
    have hs0 : 0 < s.re := by linarith
    have hs1 : s ≠ 1 / 2 := fun h => by rw [h] at ht; norm_num at ht
    set T := s.im
    set X := 1 + |T|
    have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg T]
    have hsn : 1 ≤ ‖s‖ := le_trans ht (Complex.abs_im_le_norm s)
    have h2sn : 1 ≤ ‖2 * s - 1‖ := by
      have := Complex.abs_im_le_norm (2 * s - 1)
      have him : (2 * s - 1).im = 2 * T := by simp [T]
      rw [him, abs_mul, abs_two] at this
      linarith
    have hpis : ‖(Real.pi : ℂ) ^ s‖ ≤ Real.pi ^ 2 := by
      rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      calc Real.pi ^ s.re ≤ Real.pi ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
        _ = Real.pi ^ 2 := by norm_num
    have hζ : ‖(riemannZeta (2 * s))⁻¹‖ ≤ Kz * 2 ^ Nz * X ^ Nz := by
      have h := hz (2 * s) (by simp; linarith) (by simp; linarith)
        (by simp [abs_mul]; linarith)
      have him : |(2 * s).im| = 2 * |T| := by simp [abs_mul, T]
      rw [him] at h
      calc _ ≤ Kz * (2 * |T|) ^ Nz := h
        _ ≤ Kz * (2 * X) ^ Nz := by gcongr; simp only [X]; linarith
        _ = Kz * 2 ^ Nz * X ^ Nz := by rw [mul_pow]; ring
    have hP' := hPb s (by linarith) (by linarith)
    have hΓi' := hΓi s h1 (by linarith) ht
    have hΓ' := hΓ s h1 h2 ht
    have hxi : ‖(xi (2 * s))⁻¹‖ ≤ Real.pi ^ 2 * (CΓi * X * Real.exp (Real.pi * |T| / 2)) *
        (Kz * 2 ^ Nz * X ^ Nz) := by
      rw [xi_two_mul_eq_gamma hs0 hs1, mul_inv, mul_inv, mul_inv, mul_inv, norm_mul, norm_mul, norm_mul,
        norm_mul, ← cpow_neg, neg_neg]
      have h1' : ‖s⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hsn
      have h2' : ‖(2 * s - 1)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h2sn
      calc ‖s⁻¹‖ * ‖(2 * s - 1)⁻¹‖ * ‖(Real.pi : ℂ) ^ s‖ * ‖(Gamma s)⁻¹‖ * ‖(riemannZeta (2 * s))⁻¹‖
          ≤ 1 * 1 * Real.pi ^ 2 * (CΓi * X * Real.exp (Real.pi * |T| / 2)) * (Kz * 2 ^ Nz * X ^ Nz) := by
            gcongr
        _ = _ := by ring
    have hT0 : |T| ^ NΓ ≤ X ^ NΓ := pow_le_pow_left₀ (abs_nonneg _) (by simp only [X]; linarith) _
    have hXN : ∀ k : ℕ, k ≤ Nn → X ^ k ≤ X ^ Nn := fun k hk => pow_le_pow_right₀ hX hk
    have he : Real.exp (-(Real.pi * |T|)) * Real.exp (Real.pi * |T| / 2) =
        Real.exp (-(Real.pi * |T| / 2)) := by rw [← Real.exp_add]; ring_nf
    unfold poleNum
    calc ‖4 * entireRS g s / xi (2 * s) - c * Gamma s‖
        ≤ ‖4 * entireRS g s / xi (2 * s)‖ + ‖c * Gamma s‖ := norm_sub_le _ _
      _ = 4 * ‖entireRS g s‖ * ‖(xi (2 * s))⁻¹‖ + ‖c‖ * ‖Gamma s‖ := by
          rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
      _ ≤ 4 * (CP * X ^ NP * Real.exp (-(Real.pi * |T|))) *
            (Real.pi ^ 2 * (CΓi * X * Real.exp (Real.pi * |T| / 2)) * (Kz * 2 ^ Nz * X ^ Nz)) +
          ‖c‖ * (CΓ * |T| ^ NΓ * Real.exp (-(Real.pi * |T| / 2))) := by gcongr
      _ = C₁ * X ^ N₁ * (Real.exp (-(Real.pi * |T|)) * Real.exp (Real.pi * |T| / 2)) +
          ‖c‖ * CΓ * |T| ^ NΓ * Real.exp (-(Real.pi * |T| / 2)) := by
          simp only [C₁, N₁]; ring
      _ ≤ C₁ * X ^ Nn * Real.exp (-(Real.pi * |T| / 2)) +
          ‖c‖ * CΓ * X ^ Nn * Real.exp (-(Real.pi * |T| / 2)) := by
          rw [he]
          gcongr
          · exact Nat.le_add_right _ _
          · exact hT0.trans (hXN NΓ (Nat.le_add_left _ _))
      _ = Cn * X ^ Nn * Real.exp (-(Real.pi * |T| / 2)) := by simp only [Cn]; ring
  refine ⟨max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce), fun w h1 h2 => ?_⟩
  have hden : 0 < (1 + w.im ^ 2) ^ K := by positivity
  rcases le_or_gt |w.im| 1 with ht | ht
  · have hmem : w ∈ Icc a' b' ×ℂ Icc (-1 : ℝ) 1 := by
      rw [mem_reProdIm]
      exact ⟨⟨h1, h2⟩, ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩⟩
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w hmem)
    have hpow : (1 + w.im ^ 2) ^ K ≤ 2 ^ K := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [abs_nonneg w.im, sq_abs w.im]
    rw [le_div_iff₀ hden]
    calc ‖regPart g w‖ * (1 + w.im ^ 2) ^ K ≤ B * 2 ^ K := by
          gcongr
          exact hB w hmem
      _ ≤ max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce) := le_max_left _ _
  · have hw0 : w ≠ 0 := fun h => by rw [h] at ht; simp at ht; linarith
    have hwn : 1 ≤ ‖w‖ := le_trans ht.le (Complex.abs_im_le_norm w)
    have hNb := hN (w + 1) (by simp; linarith) (by simp; linarith) (by simpa using ht.le)
    simp only [add_im, one_im, add_zero] at hNb
    have hX : 1 + |w.im| ≤ 2 * |w.im| := by linarith
    have hCn : 0 ≤ Cn := by positivity
    have hstep : (1 + |w.im|) ^ Nn ≤ 2 ^ Nn * |w.im| ^ Nn := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hX _
    have hfin := hCe' w.im ht.le
    rw [regPart_eq hw0, norm_div]
    calc ‖poleNum g (w + 1)‖ / ‖w‖ ≤ ‖poleNum g (w + 1)‖ := div_le_self (norm_nonneg _) hwn
      _ ≤ Cn * (1 + |w.im|) ^ Nn * Real.exp (-(Real.pi * |w.im| / 2)) := hNb
      _ ≤ Cn * (2 ^ Nn * |w.im| ^ Nn) * Real.exp (-(Real.pi * |w.im| / 2)) := by gcongr
      _ = Cn * 2 ^ Nn * (|w.im| ^ Nn * Real.exp (-(Real.pi * |w.im| / 2))) := by ring
      _ ≤ Cn * 2 ^ Nn * (Ce / (1 + w.im ^ 2) ^ K) := by gcongr
      _ = Cn * 2 ^ Nn * Ce / (1 + w.im ^ 2) ^ K := by ring
      _ ≤ max (B * 2 ^ K) (Cn * 2 ^ Nn * Ce) / (1 + w.im ^ 2) ^ K := by
          gcongr; exact le_max_right _ _

/-! ### Mellin inversion and the contour shift -/

/-- **The rate from a zero-free half-plane.** If `ξ` has no zeros right of `Re z = θ` and `1/ζ` grows at most
polynomially on every strip `Re z ≥ θ + δ`, then `|m(y) - c| ≤ C y^{1 - θ/2 - ε}` on `(0, 1]`. -/
theorem norm_mass_sub_le_of_zeroFree (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hZ : ∀ z : ℂ, θ < z.re → xi z ≠ 0)
    (hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, θ + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖mass g y - rateConst g‖ ≤ C * y ^ (1 - θ / 2 - ε) := by
  have hΨ := mellinRegularStrip_regPart hg hρ0 hρ hθ0 hθ1 hZ hP
  set c := rateConst g with hcdef
  set gf : ℝ → ℂ := fun y => mass g y - c * ((Real.exp (-y) : ℝ) : ℂ) with hgf
  set c' : ℝ := θ / 2 - 1 + ε with hc'
  have hc'1 : θ / 2 - 1 < c' := by linarith
  have hc'2 : c' < 1 / 4 := by linarith
  have h0a : θ / 2 - 1 < (1 / 8 : ℝ) := by linarith
  have h0b : (1 / 8 : ℝ) < 1 / 4 := by norm_num
  set K := (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖regPart g ((c' : ℂ) + t * I)‖ with hK
  have hK0 : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨K + ‖c‖, by positivity, fun y hy hy1 => ?_⟩
  have hconv : MellinConvergent gf ((1 / 8 : ℝ) : ℂ) := by
    have h1 := mellinConvergent_mass hg hρ0 hρ (s := ((1 / 8 : ℝ) : ℂ) + 1) (by norm_num)
    have h2 := (mellinConvergent_exp_neg (w := ((1 / 8 : ℝ) : ℂ)) (by simp)).const_smul c
    rw [add_sub_cancel_right] at h1
    refine (h1.sub h2).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hgf, smul_eq_mul]
    ring
  have hline : ∀ᵐ t : ℝ, mellin gf (((1 / 8 : ℝ) : ℂ) + t * I) = regPart g (((1 / 8 : ℝ) : ℂ) + t * I) := by
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with t ht
    have ht0 : t ≠ 0 := fun h => ht (by simp [h])
    exact mellin_eq_regPart hg hρ0 hρ (by simp) (by simpa using ht0)
  have hvert : Complex.VerticalIntegrable (mellin gf) (1 / 8 : ℝ) := by
    refine (hΨ.integrable_line h0a h0b).congr ?_
    filter_upwards [hline] with t ht using ht.symm
  have hcont : ContinuousAt gf y :=
    ((continuousOn_mass hg).continuousAt (Ioi_mem_nhds hy)).sub (continuousAt_const.mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousAt)
  have hinv := mellinInv_mellin_eq (1 / 8 : ℝ) gf hy hconv hvert hcont
  have hinv' : mellinInv (1 / 8 : ℝ) (mellin gf) y = mellinInv (1 / 8 : ℝ) (regPart g) y := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hline] with t ht
    rw [ht]
  have hshift := hΨ.mellinInv_eq h0a h0b hc'1 hc'2 hy
  have hbound := norm_mellinInv_le (Ψ := regPart g) c' hy
  have hgy : ‖gf y‖ ≤ K * y ^ (1 - θ / 2 - ε) := by
    rw [← hinv, hinv', hshift]
    refine hbound.trans (le_of_eq ?_)
    rw [hK, show -c' = 1 - θ / 2 - ε by rw [hc']; ring]
    ring
  have hexp : ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ ≤ y := by
    rw [show ((Real.exp (-y) : ℝ) : ℂ) - 1 = ((Real.exp (-y) - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
        have := Real.exp_le_one_iff.2 (by linarith : -y ≤ 0); linarith)]
    linarith [Real.add_one_le_exp (-y)]
  have hyp : y ≤ y ^ (1 - θ / 2 - ε) := by
    have := Real.rpow_le_rpow_of_exponent_ge hy hy1 (show 1 - θ / 2 - ε ≤ 1 by linarith)
    simpa using this
  have hsplit : mass g y - c = gf y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1) := by
    simp only [hgf]
    ring
  rw [hsplit]
  calc ‖gf y + c * (((Real.exp (-y) : ℝ) : ℂ) - 1)‖
      ≤ ‖gf y‖ + ‖c‖ * ‖((Real.exp (-y) : ℝ) : ℂ) - 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
    _ ≤ K * y ^ (1 - θ / 2 - ε) + ‖c‖ * y ^ (1 - θ / 2 - ε) := by
        gcongr
        exact hexp.trans hyp
    _ = (K + ‖c‖) * y ^ (1 - θ / 2 - ε) := by ring

/-! ### The constant and the two rates -/

/-- A rate `y^γ`, `γ > 0`, forces `c = (3/π)‖g‖²` by the equidistribution theorem. -/
theorem rateConst_eq (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {C γ : ℝ} (hγ : 0 < γ)
    (h : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖mass g y - rateConst g‖ ≤ C * y ^ γ) :
    rateConst g = ((3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : Tendsto (mass g) (𝓝[>] 0) (𝓝 (rateConst g)) := by
    have hlim : Tendsto (fun y : ℝ => C * y ^ γ) (𝓝[>] 0) (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).const_mul C
      simpa [Real.zero_rpow hγ.ne'] using this
    refine tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm' ?_ hlim)
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    exact h y hy.1 hy.2.le
  have h2 : Tendsto (mass g) (𝓝[>] 0)
      (𝓝 ((3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (CuspHE.tendsto_slice hg hρ0 hρ)
  exact tendsto_nhds_unique h1 h2

/-- **The horocycle rate of the cusp energy**: `|m(y) - (3/π)‖g‖²| ≤ C y^{½ - ε}` on `(0, 1]`. -/
theorem horocycle_energy_rate (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      |WeylUpper.slice g y - 3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2| ≤ C * y ^ (1 / 2 - ε) := by
  have hZ : ∀ z : ℂ, 1 < z.re → xi z ≠ 0 := fun z hz => xi_ne_zero_of_one_lt_re hz
  have hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, 1 + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := fun δ hδ d =>
    ⟨1 + 1 / δ, 0, by positivity, fun z hz _ _ => by
      simpa using _root_.RHTower.norm_inv_riemannZeta_le_of_le_re (by linarith : 1 < 1 + δ) hz⟩
  obtain ⟨C, hC, h⟩ := norm_mass_sub_le_of_zeroFree hg hρ0 hρ (θ := 1) zero_le_one le_rfl hZ hP hε hε1
  have hγ : (0 : ℝ) < 1 - 1 / 2 - ε := by linarith
  have hc := rateConst_eq hg hρ0 hρ hγ h
  refine ⟨C, hC, fun y hy hy1 => ?_⟩
  have := h y hy hy1
  rw [hc, mass, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    show (1 : ℝ) - 1 / 2 - ε = 1 / 2 - ε by ring] at this
  exact this

/-- **Under the Riemann hypothesis**: `|m(y) - (3/π)‖g‖²| ≤ C y^{¾ - ε}` on `(0, 1]`. -/
theorem horocycle_energy_rate_of_RH (hRH : RiemannHypothesis) (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      |WeylUpper.slice g y - 3 / Real.pi * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2| ≤ C * y ^ (3 / 4 - ε) := by
  have hZ : ∀ z : ℂ, 1 / 2 < z.re → xi z ≠ 0 := fun z hz h0 => by
    have := (riemannHypothesis_iff_xi_zero_re_eq_half.1 hRH) z h0
    linarith
  have hP : ∀ δ : ℝ, 0 < δ → ∀ d : ℝ, ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ z : ℂ, 1 / 2 + δ ≤ z.re →
      z.re ≤ d → 2 ≤ |z.im| → ‖(riemannZeta z)⁻¹‖ ≤ K * |z.im| ^ N := by
    intro δ hδ d
    obtain ⟨Kb, hKb, -, hbd⟩ := exists_invZeta_shift_data_of_rh hRH (δ := min δ (1 / 2))
      (lt_min hδ (by norm_num)) (by linarith [min_le_right δ (1 / 2)]) one_pos d
    refine ⟨2 * Kb, 1, by positivity, fun z hz1 hz2 hzt => ?_⟩
    have hmem : z ∈ GaloisForLFunctions.HTGeometry.verticalStrip (1 / 2 + min δ (1 / 2)) d :=
      ⟨by linarith [min_le_left δ (1 / 2)], hz2⟩
    have hz1' : z ≠ 1 := fun h => by rw [h] at hzt; simp at hzt; linarith
    have h := hbd z hmem
    rw [Sieve.invZeta_eq_inv hz1', Real.rpow_one] at h
    calc ‖(riemannZeta z)⁻¹‖ ≤ Kb * (2 + |z.im|) := h
      _ ≤ Kb * (2 * |z.im|) := by gcongr; linarith
      _ = 2 * Kb * |z.im| ^ 1 := by ring
  obtain ⟨C, hC, h⟩ := norm_mass_sub_le_of_zeroFree hg hρ0 hρ (θ := 1 / 2) (by norm_num) (by norm_num)
    hZ hP hε hε1
  have hγ : (0 : ℝ) < 1 - 1 / 2 / 2 - ε := by linarith
  have hc := rateConst_eq hg hρ0 hρ hγ h
  refine ⟨C, hC, fun y hy hy1 => ?_⟩
  have := h y hy hy1
  rw [hc, mass, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    show (1 : ℝ) - 1 / 2 / 2 - ε = 3 / 4 - ε by ring] at this
  exact this

end CuspHRate

end GaloisForLFunctions.BlackHoleRingdown
