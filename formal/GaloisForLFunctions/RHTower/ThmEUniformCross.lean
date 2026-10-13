import GaloisForLFunctions.RHTower.ThmEUniformArchimedean
import Zeta23.ThmE.CrossMuPChi
import Zeta23.Chebyshev

/-!
# The archimedean–prime cross term, uniformly in the modulus

For a `C¹` density `u` with `|u| ≤ B` and `|u'| ≤ D` on `[T, 2T]` and any coefficient sequence with
`|c(n)| ≤ 1`, double integration by parts in each frequency `log n` gives

`|𝓜[u, P_c]| ≤ 4 (4B + DT) C_c √X`                                       (`abs_Mform_PXc_le`)

where `Σ_{n ≤ X} Λ(n)/(√n log n) ≤ C_c √X / log X`.  For `u = μ_q` the shift `μ_q = μ_1 + (log q)/2π` gives
`B = (C + log q) l` and leaves `D` unchanged, so

`|𝓜[μ_q, P_c]| ≤ C (1 + log q) l √X`                                     (`prop_cross_uniform`)

with `C` and the threshold for `T` independent of `q` and of the coefficients.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

/-- **The cross term for a general density.** -/
theorem abs_Mform_PXc_le {Φ : ℝ → ℝ} {T L X : ℝ} (hT : 0 ≤ T) (hΦ : ContDiff ℝ 1 Φ)
    (hΦint : Integrable (fun x => Φ x ^ 2)) (hS : ∫ x, Φ x ^ 2 ≤ 2 * π * L) (hL : 0 < L)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {B D : ℝ} (hB0 : 0 ≤ B) (hD0 : 0 ≤ D)
    (hB : ∀ τ ∈ Icc T (2 * T), |u τ| ≤ B) (hD : ∀ τ ∈ Icc T (2 * T), |deriv u τ| ≤ D)
    {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ 1) (hX2 : 2 ≤ X) (hlogX : Real.log X = L) {Cc : ℝ}
    (hCc : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤ Cc * Real.sqrt X / Real.log X) :
    |Mform Φ T u (PXc c X)| ≤ 4 * (4 * B + D * T) * |Cc| * Real.sqrt X := by
  set S : ℝ := ∫ x, Φ x ^ 2 with hSdef
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  set K : ℝ := (4 * B + D * T) * S with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hosc : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      |(-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))
          * ((c n).re * Mform Φ T u (fun t => Real.cos (t * Real.log n))
             + (c n).im * Mform Φ T u (fun t => Real.sin (t * Real.log n)))|
        ≤ (1 / Real.pi) * (2 * K) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n) := by
    intro n hn
    have ha0 : (0:ℝ) ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by
        have : 0 < n := (Finset.mem_Ioc.mp hn).1
        omega
      subst hn1
      simp
    · have hy : 0 < Real.log n := Real.log_pos (by exact_mod_cast h2)
      have hMc := abs_Mform_cos_le hT hΦ hΦint hu hB hD hy.ne'
      rw [abs_of_pos hy] at hMc
      have hsin_eq : Mform Φ T u (fun t => Real.sin (t * Real.log n))
          = Mform Φ T u (fun t => Real.cos (t * Real.log n + -(π / 2))) := by
        unfold Mform
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only []
        rw [show z.2 * Real.log n + -(π / 2) = z.2 * Real.log n - π / 2 by ring,
          Real.cos_sub_pi_div_two]
      have hMs := abs_Mform_cos_phase_le hT hΦ hΦint hu hB hD hy.ne' (-(π / 2))
      rw [abs_of_pos hy, ← hsin_eq] at hMs
      have hre : |(c n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (hc n)
      have him : |(c n).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (hc n)
      rw [abs_mul]
      have h1 : |(c n).re * Mform Φ T u (fun t => Real.cos (t * Real.log n))
          + (c n).im * Mform Φ T u (fun t => Real.sin (t * Real.log n))| ≤ 2 * (K / Real.log n) := by
        calc |(c n).re * Mform Φ T u (fun t => Real.cos (t * Real.log n))
            + (c n).im * Mform Φ T u (fun t => Real.sin (t * Real.log n))|
            ≤ |(c n).re| * |Mform Φ T u (fun t => Real.cos (t * Real.log n))|
              + |(c n).im| * |Mform Φ T u (fun t => Real.sin (t * Real.log n))| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_mul, abs_mul]
          _ ≤ 1 * (K / Real.log n) + 1 * (K / Real.log n) :=
              add_le_add (mul_le_mul hre hMc (abs_nonneg _) zero_le_one)
                (mul_le_mul him hMs (abs_nonneg _) zero_le_one)
          _ = 2 * (K / Real.log n) := by ring
      calc |(-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))| * |_|
          ≤ (1 / Real.pi * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)))) * (2 * (K / Real.log n)) := by
            rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi),
              abs_of_nonneg ha0]
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 1 / Real.pi * (2 * K) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n) := by
            field_simp
  rw [Mform_mu_PXc_eq hΦ.continuous hu.continuous]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hosc).trans ?_)
  rw [← Finset.mul_sum]
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n
      ≤ |Cc| * Real.sqrt X / L := by
    rw [hlogX] at hCc
    have e : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n
        = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) / (Real.sqrt n * Real.log n) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
      rcases eq_or_lt_of_le hn1 with h1 | h2
      · rw [← h1]
        simp
      · have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
        have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
        have hlg : (0:ℝ) < Real.log n := Real.log_pos (by exact_mod_cast h2)
        rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
        field_simp
    rw [e]
    exact hCc.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Cc) (Real.sqrt_nonneg _)) hL.le)
  calc 1 / Real.pi * (2 * K) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) / Real.log n
      ≤ 1 / Real.pi * (2 * ((4 * B + D * T) * (2 * π * L))) * (|Cc| * Real.sqrt X / L) := by
        rw [hKdef]
        gcongr
    _ = 4 * (4 * B + D * T) * |Cc| * Real.sqrt X := by field_simp; ring

variable (cϱ : ℝ) in
/-- **[prop:cross] for `L(s, χ)`, uniformly in the modulus and the coefficients.** -/
theorem prop_cross_uniform {lam : ℝ} (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ c : ℕ → ℂ, CoeffOK q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F →
        |Mform F.Phi p.T (muq κ q) (PXc c p.X)|
          ≤ C * (1 + Real.log q) * (Zeta23.l p.T * Real.sqrt p.X) := by
  obtain ⟨Cμ₀, T₀₀, hCμ₀, hT₀₀⟩ := Zeta23.ThmE.muq_abs_le 0 1
    (GammaChi.gammaFactsChi (by norm_num) le_rfl) le_rfl
  obtain ⟨Cμ₁, T₀₁, hCμ₁, hT₀₁⟩ := Zeta23.ThmE.muq_abs_le 1 1
    (GammaChi.gammaFactsChi le_rfl le_rfl) le_rfl
  obtain ⟨Cd₀, hCd₀⟩ := (GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl).deriv_bound
  obtain ⟨Cd₁, hCd₁⟩ := (GammaChi.gammaFactsChi (κ := 1) (q := 1) le_rfl le_rfl).deriv_bound
  obtain ⟨Cc, hCc⟩ := Cheb.chebyshevMertens.cheb1c
  set Cμ := Cμ₀ + Cμ₁ with hCμ
  set Cd := |Cd₀| + |Cd₁| with hCd
  refine ⟨4 * (4 * (Cμ + 1) + Cd) * |Cc|,
    max (max T₀₀ T₀₁) (2 * π * Real.exp (|(2:ℝ)| / lam)), by positivity,
    fun κ q hκ hq c hc p F hp hT hF => ?_⟩
  have hT2 : 2 * π * Real.exp (|(2:ℝ)| / p.lam) ≤ p.T := by
    rw [hp]; exact (le_max_right _ _).trans hT
  have hlam0 : 0 < p.lam := hp ▸ hlam.1
  have hT1 : 1 ≤ p.T := Setting.one_le_T (div_nonneg (abs_nonneg _) hlam0.le) hT2
  have hT0 : 0 ≤ p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hL := hF.L_pos
  have hX2 : 2 ≤ p.X := Setting.le_X_of_T hlam0 hT2
  have hlogX : Real.log p.X = p.L := by simp [Setting.X]
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hΓ := GammaChi.gammaFactsChi hκ hq
  have hμ : ContDiff ℝ 1 (muq κ q) := hΓ.smooth.of_le (by exact_mod_cast le_top)
  -- the modulus-one bounds, shifted
  have hB1 : ∀ τ ∈ Set.Icc p.T (2 * p.T), |muq κ 1 τ| ≤ Cμ * p.l := by
    intro τ hτ
    interval_cases κ
    · exact (hT₀₀ p ((le_max_left _ _).trans ((le_max_left _ _).trans hT)) τ hτ).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    · exact (hT₀₁ p ((le_max_right _ _).trans ((le_max_left _ _).trans hT)) τ hτ).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hB : ∀ τ ∈ Set.Icc p.T (2 * p.T), |muq κ q τ| ≤ (Cμ + Real.log q) * p.l := by
    intro τ hτ
    rw [muq_eq_muq_one_add κ q hq]
    have hc2 : 0 ≤ Real.log q / (2 * π) := div_nonneg hlq (by positivity)
    have hc3 : Real.log q / (2 * π) ≤ Real.log q * p.l := by
      calc Real.log q / (2 * π) ≤ Real.log q := div_le_self hlq (by nlinarith [Real.pi_gt_three])
        _ ≤ Real.log q * p.l := le_mul_of_one_le_right hlq hl1
    calc |muq κ 1 τ + Real.log q / (2 * π)| ≤ |muq κ 1 τ| + |Real.log q / (2 * π)| := abs_add_le _ _
      _ ≤ Cμ * p.l + Real.log q * p.l := by rw [abs_of_nonneg hc2]; linarith [hB1 τ hτ]
      _ = (Cμ + Real.log q) * p.l := by ring
  have hD : ∀ τ ∈ Set.Icc p.T (2 * p.T), |deriv (muq κ q) τ| ≤ Cd / p.T := by
    intro τ hτ
    have hderiv : deriv (muq κ q) τ = deriv (muq κ 1) τ := by
      have e : muq κ q = fun x => muq κ 1 x + Real.log q / (2 * π) :=
        funext (muq_eq_muq_one_add κ q hq)
      rw [e, deriv_add_const]
    rw [hderiv]
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have h1 : |deriv (muq κ 1) τ| ≤ Cd / |τ| := by
      interval_cases κ
      · exact (hCd₀ τ hτ1).trans (div_le_div_of_nonneg_right
          (by linarith [le_abs_self Cd₀, abs_nonneg Cd₁]) (abs_nonneg _))
      · exact (hCd₁ τ hτ1).trans (div_le_div_of_nonneg_right
          (by linarith [le_abs_self Cd₁, abs_nonneg Cd₀]) (abs_nonneg _))
    refine h1.trans ?_
    rw [abs_of_pos hτ0]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) hτ.1
  have hBq0 : 0 ≤ (Cμ + Real.log q) * p.l := by
    have : 0 ≤ Cμ := by positivity
    positivity
  have h := abs_Mform_PXc_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hF.integral_Phi_sq_le hL hμ
    hBq0 (by positivity) hB hD hc.norm_le hX2 hlogX (hCc p.X hX2)
  refine h.trans ?_
  have hTne : p.T ≠ 0 := by linarith
  have e : 4 * (4 * ((Cμ + Real.log q) * p.l) + Cd / p.T * p.T) * |Cc| * Real.sqrt p.X
      = 4 * (4 * (Cμ + Real.log q) * p.l + Cd) * |Cc| * Real.sqrt p.X := by
    rw [div_mul_cancel₀ _ hTne]; ring
  rw [e]
  have hCμ0 : 0 ≤ Cμ := by positivity
  have hCd0 : 0 ≤ Cd := by positivity
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have key : 4 * (Cμ + Real.log q) * p.l + Cd ≤ (4 * (Cμ + 1) + Cd) * (1 + Real.log q) * p.l := by
    have h1 : Cd ≤ Cd * (1 + Real.log q) * p.l := by
      have : 1 ≤ (1 + Real.log q) * p.l := by nlinarith
      nlinarith
    nlinarith [mul_nonneg hCμ0 hlq, mul_nonneg (mul_nonneg hCμ0 hlq) (by linarith : (0:ℝ) ≤ p.l)]
  calc 4 * (4 * (Cμ + Real.log q) * p.l + Cd) * |Cc| * Real.sqrt p.X
      ≤ 4 * ((4 * (Cμ + 1) + Cd) * (1 + Real.log q) * p.l) * |Cc| * Real.sqrt p.X := by
        gcongr
    _ = 4 * (4 * (Cμ + 1) + Cd) * |Cc| * (1 + Real.log q) * (Zeta23.l p.T * Real.sqrt p.X) := by
        ring

end RHTower
