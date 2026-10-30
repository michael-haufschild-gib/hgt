import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex
import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth

/-!
# The Steklov schedule reaches the whole Weil index

Finite negative spline families survive mollification in the logarithmic Denjoy–Carleman
class. Euler–Maclaurin synthesis then transports their Gram matrices to every sufficiently
large atomic horizon. Thus the single Steklov profile reaches the entire kernel index at
width `(log log N)(log log log N)^β/N`, for every `β > 2`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset Complex
open scoped Real ContDiff ComplexConjugate Convolution
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.TransMetzlerWeilPositivity
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (weilGram cx cx_contDiff cx_hasCompactSupport)
open GaloisForLFunctions.ArithmeticElectrostatics (atomicTest)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! The quadrature ratio controls both the sup error and its logarithmically weighted square. -/

private theorem dcSynthRatio_nonneg {b Bφ k : ℝ} (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ) (hk : 0 ≤ k)
    (n : ℕ) : 0 ≤ dcSynthRatio b Bφ k n := by
  unfold dcSynthRatio
  have hlog0 : 0 ≤ Real.log (((2 * gevOrder k + 2 : ℕ) : ℝ) + 3) ^ 2 := sq_nonneg _
  positivity

private theorem dcSynthRatio_le {b Bφ : ℝ} (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ) {k : ℝ} {n B : ℕ}
    (hk1 : 1 ≤ k) (hn : 1 ≤ n) (hℓ9 : 9 ≤ Real.log (Real.log k))
    (hll1 : 1 ≤ Real.log (Real.log (Real.log k)))
    (hK1 : 1 ≤ ((n * B : ℕ) : ℝ) / k /
      (Real.log (Real.log k) * Real.log (Real.log (Real.log k)) ^ 2)) :
    dcSynthRatio b Bφ k n ≤
      24 * b * (Real.log ((n * B : ℕ) : ℝ) ^ (3 : ℝ) / n) +
      144 * (Real.log ((n * B : ℕ) : ℝ) ^ (4 : ℝ) / n) +
      24 * Bφ * B * (((n * B : ℕ) : ℝ) / k /
        (Real.log (Real.log k) * Real.log (Real.log (Real.log k)) ^ 2))⁻¹ := by
  set ℓ := Real.log (Real.log k)
  set ℓ₂ := Real.log ℓ
  set W := ℓ * ℓ₂ ^ 2
  have hk0 : 0 < k := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hW1 : 1 ≤ W := by
    have : 1 ≤ ℓ₂ ^ 2 := by nlinarith only [hll1]
    nlinarith only [hℓ9, this]
  have hW0 : 0 < W := by linarith
  have hK'1 : 1 ≤ ((n * B : ℕ) : ℝ) / k := by
    have heq : ((n * B : ℕ) : ℝ) / k = (((n * B : ℕ) : ℝ) / k / W) * W := by field_simp [hW0.ne']
    nlinarith only [hK1, hW1, heq]
  have hkN : k ≤ ((n * B : ℕ) : ℝ) := by
    have := (le_div_iff₀ hk0).mp hK'1; linarith
  have hlogk : 1 < Real.log k := by
    by_contra h; push Not at h
    have : ℓ ≤ 0 := Real.log_nonpos (Real.log_nonneg hk1) h
    linarith
  set L := Real.log ((n * B : ℕ) : ℝ)
  have hℓL : ℓ ≤ L := by
    have h1 : ℓ ≤ Real.log k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact h1.trans (Real.log_le_log hk0 hkN)
  have hL0 : 0 < L := by linarith
  set p : ℝ := ((2 * gevOrder k + 2 : ℕ) : ℝ)
  have hp0 : 0 ≤ p := by positivity
  have hp6 : p ≤ 6 * ℓ := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ ℓ by linarith)
    simp only [p, gevOrder]; push_cast; linarith
  have hp3_sq : p + 3 ≤ ℓ ^ 2 := by nlinarith only [hp6, hℓ9]
  have hlogp : Real.log (p + 3) ≤ 2 * ℓ₂ := by
    calc Real.log (p + 3) ≤ Real.log (ℓ ^ 2) := Real.log_le_log (by positivity) hp3_sq
      _ = 2 * ℓ₂ := by rw [Real.log_pow]; push_cast; rfl
  have hlogp0 : 0 ≤ Real.log (p + 3) := (Real.log_pos (by linarith [hp0])).le
  have hlogp_sq : Real.log (p + 3) ^ 2 ≤ 4 * ℓ₂ ^ 2 := by
    calc Real.log (p + 3) ^ 2 ≤ (2 * ℓ₂) ^ 2 := pow_le_pow_left₀ hlogp0 hlogp 2
      _ = 4 * ℓ₂ ^ 2 := by ring
  have hpW : p * Real.log (p + 3) ^ 2 ≤ 24 * W := by
    calc p * Real.log (p + 3) ^ 2 ≤ (6 * ℓ) * (4 * ℓ₂ ^ 2) :=
          mul_le_mul hp6 hlogp_sq (sq_nonneg _) (by linarith)
      _ = 24 * W := by dsimp [W]; ring
  have hℓ₂L : ℓ₂ ≤ L := by
    have : ℓ₂ ≤ ℓ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    exact this.trans hℓL
  have hWL3 : W ≤ L ^ (3 : ℝ) := by
    have h3 : L ^ (3 : ℝ) = L * L ^ 2 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [h3]
    have hsq : ℓ₂ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hℓ₂L 2
    exact mul_le_mul hℓL hsq (sq_nonneg _) hL0.le
  have hL4 : L ^ (4 : ℝ) = L ^ (3 : ℝ) * L := by
    rw [show (4 : ℝ) = 3 + 1 by norm_num, Real.rpow_add_one hL0.ne']
  set Kq := ((n * B : ℕ) : ℝ) / k / W
  have hB0 : (0 : ℝ) < B := by
    rcases Nat.eq_zero_or_pos B with hBzero | hBpos
    · have hknonpos : k ≤ 0 := by
        simpa only [hBzero, Nat.mul_zero, Nat.cast_zero] using hkN
      exact False.elim ((not_le_of_gt hk0) hknonpos)
    · exact_mod_cast hBpos
  have hkn : k / n = B * Kq⁻¹ * W⁻¹ := by
    dsimp only [Kq]; push_cast; field_simp [hk0.ne', hn0.ne', hW0.ne', hB0.ne']
  have hρe : dcSynthRatio b Bφ k n =
      (p * Real.log (p + 3) ^ 2) * b / n + Bφ * ((p * Real.log (p + 3) ^ 2) * (k / n)) +
        (p * Real.log (p + 3) ^ 2) * p / n := by
    simp only [dcSynthRatio, p]; ring
  rw [hρe, hL4]
  have hpL3 : p * Real.log (p + 3) ^ 2 ≤ 24 * L ^ (3 : ℝ) :=
    hpW.trans (mul_le_mul_of_nonneg_left hWL3 (by norm_num))
  have t1 : (p * Real.log (p + 3) ^ 2) * b / n ≤ 24 * b * (L ^ (3 : ℝ) / n) := by
    rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
    nlinarith [mul_le_mul_of_nonneg_right hpL3 hb]
  have t2 : Bφ * ((p * Real.log (p + 3) ^ 2) * (k / n)) ≤ 24 * Bφ * B * Kq⁻¹ := by
    rw [hkn]
    have hKi : 0 ≤ Kq⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : (p * Real.log (p + 3) ^ 2) * (B * Kq⁻¹ * W⁻¹) ≤
        (24 * W) * (B * Kq⁻¹ * W⁻¹) :=
      mul_le_mul_of_nonneg_right hpW (by positivity)
    have h2 : (24 * W) * (B * Kq⁻¹ * W⁻¹) = 24 * B * Kq⁻¹ := by field_simp [hW0.ne']
    calc Bφ * ((p * Real.log (p + 3) ^ 2) * (B * Kq⁻¹ * W⁻¹))
        ≤ Bφ * ((24 * W) * (B * Kq⁻¹ * W⁻¹)) := mul_le_mul_of_nonneg_left h1 hBφ
      _ = 24 * Bφ * B * Kq⁻¹ := by rw [h2]; ring
  have t3 : (p * Real.log (p + 3) ^ 2) * p / n ≤ 144 * (L ^ (3 : ℝ) * L / n) := by
    rw [div_le_iff₀ hn0, mul_div_assoc', div_mul_cancel₀ _ hn0.ne']
    have hpL : p ≤ 6 * L := hp6.trans (by linarith)
    have hpW0 : 0 ≤ p * Real.log (p + 3) ^ 2 := mul_nonneg hp0 (sq_nonneg _)
    nlinarith [mul_le_mul hpL3 hpL hp0 (by positivity)]
  linarith

private theorem tendsto_dcLogSynthesis {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ) {B : ℕ}
    (hB : 1 ≤ B) {M b A Bφ A0 : ℝ} (hMA : 0 ≤ M * A) (hb : 0 ≤ b) (hBφ : 0 ≤ Bφ)
    (M' A' : ℕ → ℝ) (R' : ℝ) :
    Tendsto (fun n : ℕ => dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => synthLevy R'
      (dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n)
      (emLip M' A' (κ (n * B)) n) (κ (n * B))) atTop (𝓝 0) := by
  obtain ⟨hk, hkl⟩ := hκ
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  have hK : Tendsto (fun n => κ (n * B)) atTop atTop := hk.comp hNB
  have hlogK : Tendsto (fun n => Real.log (κ (n * B))) atTop atTop :=
    Real.tendsto_log_atTop.comp hK
  have hℓ : Tendsto (fun n => Real.log (Real.log (κ (n * B)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogK
  have hℓ₂ : Tendsto (fun n => Real.log (Real.log (Real.log (κ (n * B))))) atTop atTop :=
    Real.tendsto_log_atTop.comp hℓ
  have hKW : Tendsto (fun n : ℕ => ((n * B : ℕ) : ℝ) / κ (n * B) /
      (Real.log (Real.log (κ (n * B))) * Real.log (Real.log (Real.log (κ (n * B)))) ^ 2))
      atTop atTop := hkl.comp hNB
  have hev := (hK.eventually_ge_atTop 1).and ((eventually_ge_atTop 1).and
    ((hℓ.eventually_ge_atTop 9).and ((hℓ₂.eventually_ge_atTop 1).and
      (hKW.eventually_ge_atTop 1))))
  have hup : Tendsto (fun n : ℕ =>
      24 * b * (Real.log ((n * B : ℕ) : ℝ) ^ (3 : ℝ) / n) +
      144 * (Real.log ((n * B : ℕ) : ℝ) ^ (4 : ℝ) / n) +
      24 * Bφ * B * (((n * B : ℕ) : ℝ) / κ (n * B) /
        (Real.log (Real.log (κ (n * B))) *
          Real.log (Real.log (Real.log (κ (n * B)))) ^ 2))⁻¹) atTop (𝓝 0) := by
    have := (((tendsto_log_rpow_div (r := 3) hB).const_mul (24 * b)).add
      ((tendsto_log_rpow_div (r := 4) hB).const_mul 144)).add
      (hKW.inv_tendsto_atTop.const_mul (24 * Bφ * B))
    simp only [mul_zero, add_zero] at this
    exact this
  have hρ : Tendsto (fun n => dcSynthRatio b Bφ (κ (n * B)) n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (hev.mono fun n h => dcSynthRatio_nonneg hb hBφ (by linarith [h.1]) n)
      (hev.mono fun n ⟨hk1, hn, hℓ9, hll1, hK1⟩ => dcSynthRatio_le hb hBφ hk1 hn hℓ9 hll1 hK1)
  have hρ1 := hρ.eventually (Iic_mem_nhds (Real.exp_pos (-1)))
  have he₁ : ∀ᶠ n : ℕ in atTop,
      0 ≤ M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) ∧
      M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) ≤
        M * A * (1 / Real.log (κ (n * B)) ^ 2) := by
    filter_upwards [hev, hρ1] with n ⟨hk1, _, hℓ9, _, _⟩ hρn
    have hρ0 := dcSynthRatio_nonneg (k := κ (n * B)) hb hBφ
      (by linarith only [hk1]) n
    refine ⟨mul_nonneg hMA (pow_nonneg hρ0 _), mul_le_mul_of_nonneg_left ?_ hMA⟩
    have hlogk : 1 < Real.log (κ (n * B)) := by
      by_contra h; push Not at h
      have : Real.log (Real.log (κ (n * B))) ≤ 0 := Real.log_nonpos (Real.log_nonneg hk1) h
      linarith
    have h2p : 2 * Real.log (Real.log (κ (n * B))) ≤ ((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ) := by
      have := Nat.le_ceil (Real.log (Real.log (κ (n * B))))
      simp only [gevOrder]; push_cast; linarith
    have h1 := pow_le_pow_left₀ hρ0 hρn (2 * gevOrder (κ (n * B)) + 2)
    have h2 : Real.exp (-1) ^ (2 * gevOrder (κ (n * B)) + 2) =
        Real.exp (-((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h3 : Real.exp (-((2 * gevOrder (κ (n * B)) + 2 : ℕ) : ℝ)) ≤
        Real.exp (-(2 * Real.log (Real.log (κ (n * B))))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (-(2 * Real.log (Real.log (κ (n * B))))) =
        1 / Real.log (κ (n * B)) ^ 2 := by
      rw [Real.exp_neg,
        show (2 : ℝ) * Real.log (Real.log (κ (n * B))) =
          ((2 : ℕ) : ℝ) * Real.log (Real.log (κ (n * B))) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by linarith), one_div]
    linarith
  have hinvlog2 : Tendsto (fun n => 1 / Real.log (κ (n * B)) ^ 2) atTop (𝓝 0) := by
    simp only [one_div]
    exact ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlogK).inv_tendsto_atTop
  have hinv : Tendsto (fun n => 1 / κ (n * B)) atTop (𝓝 0) := by
    simp only [one_div]; exact hK.inv_tendsto_atTop
  have he₁t : Tendsto (fun n => M * A * dcSynthRatio b Bφ (κ (n * B)) n ^
      (2 * gevOrder (κ (n * B)) + 2)) atTop (𝓝 0) := by
    have hup' := hinvlog2.const_mul (M * A)
    rw [mul_zero] at hup'
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup'
      (he₁.mono fun n h => h.1) (he₁.mono fun n h => h.2)
  have herr_eq : ∀ n, dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n =
      M * A * dcSynthRatio b Bφ (κ (n * B)) n ^ (2 * gevOrder (κ (n * B)) + 2) +
        M * b * dcLogWeight 1 * (1 / κ (n * B)) * A0 := fun _ => rfl
  have he : Tendsto (fun n : ℕ => dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n)
      atTop (𝓝 0) := by
    simp_rw [herr_eq]
    simpa using he₁t.add ((hinv.const_mul (M * b * dcLogWeight 1)).mul_const A0)
  refine ⟨he, ?_⟩
  have hLE : Tendsto (fun n => Real.log (κ (n * B)) *
      dcSynthErr M b A Bφ (κ (n * B)) A0 (gevOrder (κ (n * B))) n ^ 2) atTop (𝓝 0) := by
    simp_rw [herr_eq]
    exact log_mul_sq_tendsto (k := fun n => κ (n * B)) hK he₁
  -- The logarithmic rate also controls the normalized Lipschitz error.
  have hK'ℓ1 : Tendsto (fun n : ℕ => ((n * B : ℕ) : ℝ) / κ (n * B) /
      Real.log (Real.log (κ (n * B))) ^ (1 : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hKW
    filter_upwards [hev] with n ⟨hk1, _, hℓ9, hll1, _⟩
    rw [Real.rpow_one]
    have hℓ_pos : 0 < Real.log (Real.log (κ (n * B))) := by linarith
    have hsq1 : 1 ≤ Real.log (Real.log (Real.log (κ (n * B)))) ^ 2 := by nlinarith only [hll1]
    have hnum0 : 0 ≤ ((n * B : ℕ) : ℝ) / κ (n * B) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith only [hk1])
    exact div_le_div_of_nonneg_left hnum0 hℓ_pos (le_mul_of_one_le_right hℓ_pos.le hsq1)
  have hev1 : ∀ᶠ n : ℕ in atTop, 1 ≤ κ (n * B) ∧ 1 ≤ n ∧
      1 ≤ Real.log (Real.log (κ (n * B))) ∧
      1 ≤ ((n * B : ℕ) : ℝ) / κ (n * B) / Real.log (Real.log (κ (n * B))) ^ (1 : ℝ) := by
    filter_upwards [hev, hK'ℓ1.eventually_ge_atTop 1] with n ⟨hk1, hn, hℓ9, _, _⟩ h1
    exact ⟨hk1, hn, by linarith, h1⟩
  exact tendsto_synthLevy_of he hLE (gevrey_lip_tendsto zero_le_one hK hK'ℓ1 hev1 M' A')

private theorem abs_iteratedDeriv_mollify_le_dcLogWeight {φ g : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hg : Continuous g)
    {Mg : ℝ} (hgM : ∀ t, |g t| ≤ Mg) {m : ℝ} (hm : 0 < m) {A Bφ : ℝ}
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    (l : ℕ) (x : ℝ) :
    |iteratedDeriv l (mollify g φ m) x| ≤ Mg * A * (Bφ * m) ^ l * dcLogWeight l := by
  have hMg : 0 ≤ Mg := (abs_nonneg _).trans (hgM 0)
  have hψ : ContDiff ℝ ∞ (iteratedDeriv l (dilate m φ)) := by
    rw [iteratedDeriv_eq_iterate]; exact (contDiff_dilate_smooth hφ m).iterate_deriv l
  have hψc := hasCompactSupport_iteratedDeriv (hasCompactSupport_dilate_of hφ1 hm) l
  rw [iteratedDeriv_mollify hφ hφ1 hg hm l]
  refine (abs_integral_mul_le_sup_mul hgM
    (hψ.continuous.integrable_of_hasCompactSupport hψc) x).trans ?_
  rw [integral_abs_iteratedDeriv_dilate hφ hm l]
  have := mul_le_mul_of_nonneg_left (hA l) (mul_nonneg hMg (pow_nonneg hm.le l))
  calc Mg * (m ^ l * ∫ t, |iteratedDeriv l φ t|) = Mg * m ^ l * ∫ t, |iteratedDeriv l φ t| := by
        ring
    _ ≤ Mg * m ^ l * (A * Bφ ^ l * dcLogWeight l) := this
    _ = _ := by rw [mul_pow]; ring

variable {φ : ℝ → ℝ} {A Bφ : ℝ}

/-- Every finite part of the Weil index is carried by a logarithmic Denjoy–Carleman family. -/
theorem exists_dcLog_family (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ) (hφint : ∫ s, φ s = 1)
    (hBφ : 0 ≤ Bφ) (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {m : ℕ} (hm : (m : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel) :
    ∃ (n : ℕ) (G : Fin n → ℝ → ℝ) (R M b : ℝ), 0 ≤ R ∧ 0 ≤ M ∧ 0 ≤ b ∧
      (∀ i, ContDiff ℝ ∞ (G i)) ∧ (∀ i, SupportedIn R (G i)) ∧
      (∀ i l t, |iteratedDeriv l (G i) t| ≤ M * b ^ l * dcLogWeight l) ∧
      m ≤ hermNegIndex (weilGram Λw fun i => cx (G i)) := by
  obtain ⟨n, hn⟩ := exists_spline_family hm
  set B : Fin n → ℝ → ℝ := fun i u => cubicSpline (u - Real.log ((i : ℝ) + 1))
  have hB2 : ∀ i, ContDiff ℝ 2 (B i) := fun i =>
    contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const)
  have hBc : ∀ i, HasCompactSupport (B i) := fun i =>
    hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight _)
  -- Finite spline families admit common support, sup and Lipschitz bounds.
  choose Ri Mi Li hRi hRiB hMiB hLiB using fun i => exists_test_bounds (hB2 i) (hBc i)
  set R := ∑ i, Ri i
  set M := ∑ i, |Mi i|
  set L := ∑ i, |Li i|
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => hRi i
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBR : ∀ i, SupportedIn R (B i) := fun i => supportedIn_mono (hRiB i)
    (Finset.single_le_sum (fun j _ => hRi j) (Finset.mem_univ i))
  have hBM : ∀ i t, |B i t| ≤ M := fun i t => (hMiB i t).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |Mi j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
  have hBL : ∀ i u v, |B i u - B i v| ≤ L * |u - v| := fun i u v => (hLiB i u v).trans
    (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum
      (f := fun j => |Li j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))) (abs_nonneg _))
  -- Mollification preserves the finite negative subspace at sufficiently narrow width.
  set A0 := ∫ s, |φ s|
  set A1 := ∫ s, |deriv φ s|
  obtain ⟨he, hV, -, -⟩ := tendsto_mollifyErr L A0 M A1 (R + 1)
  have hconv := tendsto_weilGram_of_perturbation (F := B) (R' := R + 1) (by linarith) hB2 hBc
    (fun i => supportedIn_mono (hBR i) (by linarith)) (A := fun r i => mollify (B i) φ r)
    (Dn := fun r i x => mollify (B i) φ r x - B i x) (c := fun _ => 0)
    (e := fun r : ℕ => L * (1 / (r : ℝ)) * A0) (LD := fun r : ℕ => M * ((r : ℝ) * A1) + L)
    (k := fun r : ℕ => (r : ℝ))
    (Eventually.of_forall fun r i => by funext u; simp only [sub_zero]; ring)
    (by
      filter_upwards [eventually_ge_atTop 1] with r hr i
      have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
      obtain ⟨h2, hR, hsup, hlip⟩ := mollify_perturbation hφ hφ1 hφint (hB2 i) (hBR i) (hBM i)
        (hBL i) hr'
      exact ⟨h2, hR, hsup, hlip, hr'⟩)
    he hV
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex (weilGram_cx_isHermitian hB2 hBc)
    hconv
  obtain ⟨r, hr, hr1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa only [pow_zero, mul_one, dcLogWeight_zero] using this
  refine ⟨n, fun i => mollify (B i) φ r, R + 1, M * A, Bφ * r, by linarith, mul_nonneg hM0 hA0,
    mul_nonneg hBφ hr0.le, fun i => contDiff_mollify hφ hφ1 (hB2 i).continuous hr0,
    fun i => mollify_supportedIn hφ1 (hBR i) hr1', fun i l t => ?_, hn.trans hr⟩
  have := abs_iteratedDeriv_mollify_le_dcLogWeight hφ hφ1 (hB2 i).continuous (hBM i) hr0 hA l t
  simpa only [mul_assoc] using this

/-- Fixed integer shifts preserve the super-Gevrey overlap law. -/
theorem overlapGrowthSuperGevrey_shift {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ)
    (ρ : ℕ) : OverlapGrowthSuperGevrey fun N => κ (N + ρ) := by
  have hsh : Tendsto (fun N : ℕ => N + ρ) atTop atTop := tendsto_add_atTop_nat ρ
  refine ⟨hκ.1.comp hsh, ?_⟩
  have hg := hκ.2.comp hsh
  refine tendsto_atTop_mono' atTop ?_ (hg.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
  filter_upwards [eventually_ge_atTop ρ, eventually_ge_atTop 1, hg.eventually_ge_atTop 0]
    with N hNρ hN1 hg0
  simp only [Function.comp] at hg0 ⊢
  have hN : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNρ' : (ρ : ℝ) ≤ N := by exact_mod_cast hNρ
  push_cast at hg0 ⊢
  have hfrac : 1 / 2 ≤ (N : ℝ) / (N + ρ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have heq : (N : ℝ) / κ (N + ρ) /
      (Real.log (Real.log (κ (N + ρ))) * Real.log (Real.log (Real.log (κ (N + ρ)))) ^ 2) =
      (N : ℝ) / (N + ρ) * (((N : ℝ) + ρ) / κ (N + ρ) /
        (Real.log (Real.log (κ (N + ρ))) * Real.log (Real.log (Real.log (κ (N + ρ)))) ^ 2)) := by
    field_simp
  rw [heq]
  nlinarith only [mul_le_mul_of_nonneg_right hfrac hg0]

/-- Synthesis transports each finite negative family along a fixed residue class. -/
theorem eventually_le_hermNegIndex_atomicGram_dcLog_residue (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ) {n : ℕ} {G : Fin n → ℝ → ℝ} {R M b : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hb : 0 ≤ b) (hG : ∀ i, ContDiff ℝ ∞ (G i))
    (hGR : ∀ i, SupportedIn R (G i))
    (hGM : ∀ i l t, |iteratedDeriv l (G i) t| ≤ M * b ^ l * dcLogWeight l) {m : ℕ}
    (hm : m ≤ hermNegIndex (weilGram Λw fun i => cx (G i))) (ρ : ℕ) :
    ∀ᶠ j in atTop, m ≤ hermNegIndex (atomicGram (dilate (κ (j * blockSize R + ρ)) φ)
      (j * blockSize R + ρ)) := by
  set B := blockSize R
  have hB : 1 ≤ B := SpacingScaleHarmonicAnalysis.one_le_blockSize R
  have hκρ := overlapGrowthSuperGevrey_shift hκ ρ
  set k : ℕ → ℝ := fun j => κ (j * B + ρ)
  have hA0 : 0 ≤ A := by
    have := (integral_nonneg fun t => abs_nonneg (iteratedDeriv 0 φ t)).trans (hA 0)
    simpa only [pow_zero, mul_one, dcLogWeight_zero] using this
  set A0 := ∫ s, |φ s|
  set Mseq : ℕ → ℝ := fun l => M * b ^ l * dcLogWeight l
  set Aseq : ℕ → ℝ := fun q => ∫ s, |iteratedDeriv q φ s|
  -- Synthesize the whole finite family with common error bounds.
  have hsyn : ∀ (j : ℕ) (i : Fin n), ∃ (x : ℕ → ℝ) (D : ℝ → ℝ), 2 ≤ j → 1 ≤ k j →
      atomicTest (j * B) x (dilate (k j) φ) =
          (fun u => G i (u - (Real.log j + R)) + D (u - (Real.log j + R))) ∧
        ContDiff ℝ 2 D ∧ SupportedIn (R + 1) D ∧
        (∀ u, |D u| ≤ dcSynthErr M b A Bφ (k j) A0 (gevOrder (k j)) j) ∧
        ∀ u v, |D u - D v| ≤ emLip Mseq Aseq (k j) j * |u - v| := fun j i => by
    by_cases hj : 2 ≤ j ∧ 1 ≤ k j
    · obtain ⟨x, D, h⟩ := exists_dcLogSynthesis hφ hφ1 hφint (hG i) (hGR i) hM hb hBφ
        (hGM i) hA hj.1 hj.2 (gevOrder (k j))
      exact ⟨x, D, fun _ _ => h⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose X Dn hXD using hsyn
  obtain ⟨he, hV⟩ := tendsto_dcLogSynthesis (A0 := A0) hκρ hB (mul_nonneg hM hA0) hb hBφ Mseq Aseq
    (R + 1)
  have hk : Tendsto k atTop atTop := hκρ.1.comp
    (tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hB) tendsto_id)
  refine eventually_le_hermNegIndex_of_synthesis (hφ.of_le (natCast_le_infty 2)) hφ1
    (R' := R + 1) (by linarith) (fun i => (hG i).of_le (natCast_le_infty 2))
    (fun i => supportedIn_mono (hGR i) (by linarith)) hm (H := fun j => j * B)
    (N := fun j => j * B + ρ) (fun j => Nat.le_add_right _ ρ) X Dn (fun j => Real.log j + R)
    (fun j => dcSynthErr M b A Bφ (k j) A0 (gevOrder (k j)) j) (fun j => emLip Mseq Aseq (k j) j)
    ?_ he hV
  filter_upwards [eventually_ge_atTop 2, hk.eventually_ge_atTop 1] with j hj2 hk1
  exact ⟨hk1, fun i => hXD j i hj2 hk1⟩

/-- Every finite part of the index occurs at all sufficiently large atomic horizons. -/
theorem eventually_le_hermNegIndex_atomicGram_dcLog (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ) {m : ℕ}
    (hm : (m : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel) :
    ∀ᶠ N in atTop, m ≤ hermNegIndex (atomicGram (dilate (κ N) φ) N) := by
  obtain ⟨n, G, R, M, b, hR, hM, hb, hG, hGR, hGM, hGm⟩ :=
    exists_dcLog_family hφ hφ1 hφint hBφ hA hm
  exact eventually_of_residues (SpacingScaleHarmonicAnalysis.one_le_blockSize R) fun ρ _ =>
    eventually_le_hermNegIndex_atomicGram_dcLog_residue hφ hφ1 hφint hBφ hA hκ hR hM hb hG hGR hGM
      hGm ρ

/-- **The indices converge to the index of the Weil kernel**, finite or infinite. -/
theorem tendsto_hermNegIndex_atomicGram_dcLog (hφ : ContDiff ℝ ∞ φ) (hφ1 : VanishesOff φ)
    (hφint : ∫ s, φ s = 1) (hBφ : 0 ≤ Bφ)
    (hA : ∀ q, ∫ t, |iteratedDeriv q φ t| ≤ A * Bφ ^ q * dcLogWeight q)
    {κ : ℕ → ℝ} (hκ : OverlapGrowthSuperGevrey κ) :
    Tendsto (fun N => (hermNegIndex (atomicGram (dilate (κ N) φ) N) : ℕ∞)) atTop
      (𝓝 (HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · lift a to ℕ using ha.ne_top
    have : ((a + 1 : ℕ) : ℕ∞) ≤ HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel := by
      exact_mod_cast Order.add_one_le_of_lt ha
    filter_upwards [eventually_le_hermNegIndex_atomicGram_dcLog hφ hφ1 hφint hBφ hA hκ this]
      with N hN
    exact_mod_cast Nat.lt_of_succ_le hN
  · filter_upwards [hκ.1.eventually_gt_atTop 0] with N hN
    exact lt_of_le_of_lt (hermNegIndex_atomicGram_le hφ2 hφ1 hN N) ha

/-- The fixed Steklov profile exhausts the entire Weil index at every super-Gevrey schedule. -/
theorem steklovDCProfile_atomicGram_reaches_index {β : ℝ} (hβ : 2 < β) :
    Tendsto (fun N : ℕ => (hermNegIndex (atomicGram
      (dilate ((N : ℝ) / superGevreyRatio β N) steklovDCProfile) N) : ℕ∞)) atTop
      (𝓝 (HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel)) :=
  tendsto_hermNegIndex_atomicGram_dcLog contDiff_steklovDCProfile
    steklovDCProfile_vanishesOff integral_steklovDCProfile (by norm_num)
    integral_abs_iteratedDeriv_steklovDCProfile_le (overlapGrowthSuperGevrey_of_two_lt hβ)

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory

#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.exists_dcLog_family
#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.tendsto_hermNegIndex_atomicGram_dcLog
#print axioms GaloisForLFunctions.EffectiveArithmeticHodgeTheory.steklovDCProfile_atomicGram_reaches_index
