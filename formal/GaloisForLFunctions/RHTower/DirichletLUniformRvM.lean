import Zeta23.ThmE.MainTermChi
import GaloisForLFunctions.RHTower.DirichletLUniformBacklund
import GaloisForLFunctions.RHTower.DirichletLUniformLocalCount

/-!
# The Riemann–von Mangoldt formula for Dirichlet L-functions, uniformly in the modulus

There are absolute constants `C, T₀` such that for every modulus `q > 1`, every primitive character
`χ` modulo `q` and every `T ≥ T₀`,

`|N_χ(T, 2T) − (T/2π)(log(qT/2π) + 2 log 2 − 1)| ≤ C (log q + log T)`

(`mainChi_uniform`), and `N_χ(t, t + 1] ≤ A (log q + log(|t| + 3))` for all real `t`
(`localCountChi_uniform'`, from `uniform_localCount`).

The proof is the argument principle for the completed L-function on `[−1, 2] × [T₁, T₂]` with
`T₁ ∈ [T − 1, T]`, `T₂ ∈ [2T, 2T + 1]` zero-free ordinates; the archimedean side is `∫ μ_χ`, whose
Stirling constants do not depend on `q`; the horizontal sides are bounded by Backlund's argument with
the growth bound `|L(s, χ)| ≤ 8q(|Im s| + 3)`; the vertical side on `Re s = 2` is at most `π`; the two
end windows are bounded by the local count.  Every constant enters linearly in `log q`.
-/

open Complex Set DirichletCharacter MeasureTheory Zeta23 Zeta23.ThmE

noncomputable section

namespace RHTower

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The local count in the form `A (log q + log(|t| + 3))`. -/
theorem localCountChi_uniform' (hq : 1 < q) (hprim : χ.IsPrimitive) (t : ℝ) :
    (NcountL χ t (t + 1) : ℝ)
      ≤ 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) * (Real.log q + Real.log (|t| + 3)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  rw [← Real.log_mul hq0.ne' (by positivity)]
  exact uniform_localCount hq hprim t

/-- Backlund's horizontal bound in the form `C (log q + log|T|)`. -/
theorem backlund_horizontal_uniform' (hχ1 : χ ≠ 1) {T : ℝ} (hT : 4 ≤ |T|)
    (hord : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T) :
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv χ.LFunction (σ + T * I)).im|
      ≤ 2 * Real.pi * (1 / Real.log (0.9 / 0.8) * (Real.log 48 + 2) + 1)
          * (Real.log q + Real.log |T|) := by
  have h := backlund_horizontal_uniform hχ1 hT hord
  have hK : 0 < 1 / Real.log (0.9 / 0.8) := div_pos one_pos (Real.log_pos (by norm_num))
  have hLq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hlT : 1 ≤ Real.log |T| := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have h48 : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, x = 1 / Real.log (0.9 / 0.8) := ⟨_, rfl⟩
  rw [← hKdef] at h hK ⊢
  have hkey : K * (Real.log 48 + Real.log q + 2 * Real.log |T|) + 1
      ≤ (K * (Real.log 48 + 2) + 1) * (Real.log q + Real.log |T|) := by
    have a1 : 0 ≤ K * Real.log 48 * (Real.log |T| - 1) := by
      have : 0 ≤ Real.log |T| - 1 := by linarith
      positivity
    have a2 : 0 ≤ (K * Real.log 48 + K + 1) * Real.log q := by positivity
    nlinarith
  calc _ ≤ 2 * Real.pi * (K * (Real.log 48 + Real.log q + 2 * Real.log |T|) + 1) := h
    _ ≤ 2 * Real.pi * ((K * (Real.log 48 + 2) + 1) * (Real.log q + Real.log |T|)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-- The density of the archimedean factor, `|μ_χ(τ)| ≤ (C + 3)(log q + log(τ + 3))`. -/
theorem abs_muq_le {κ : ℕ} {C : ℝ} (hΓ : GammaFactsChiBounded κ q C) {τ : ℝ} (hτ : 1 ≤ τ) :
    |muq κ q τ| ≤ (|C| + 3) * (Real.log q + Real.log (τ + 3)) := by
  have hτ0 : 0 < τ := by linarith
  have hst := hΓ.stirling τ (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at hst
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hLq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  have hlτ : 0 ≤ Real.log τ := Real.log_nonneg hτ
  have hlτ3 : Real.log τ ≤ Real.log (τ + 3) := Real.log_le_log hτ0 (by linarith)
  have hl3 : 1 ≤ Real.log (τ + 3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have h2π : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have := Real.exp_one_gt_d9
    rw [he]
    nlinarith [Real.pi_lt_d2]
  have h2π0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hsplit : Real.log (q * τ / (2 * Real.pi))
      = Real.log q + Real.log τ - Real.log (2 * Real.pi) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hq0.ne' hτ0.ne']
  have hmain : |(1 / (2 * Real.pi)) * Real.log (q * τ / (2 * Real.pi))|
      ≤ Real.log q + Real.log τ + Real.log (2 * Real.pi) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), hsplit]
    have hfrac : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    calc 1 / (2 * Real.pi) * |Real.log q + Real.log τ - Real.log (2 * Real.pi)|
        ≤ 1 * |Real.log q + Real.log τ - Real.log (2 * Real.pi)| :=
          mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
      _ ≤ Real.log q + Real.log τ + Real.log (2 * Real.pi) := by
          rw [one_mul, abs_le]; constructor <;> linarith
  have hCτ : C / τ ^ 2 ≤ |C| := by
    calc C / τ ^ 2 ≤ |C| / τ ^ 2 := div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| := div_le_self (abs_nonneg C) (by nlinarith)
  have htri := abs_sub_abs_le_abs_sub (muq κ q τ) ((1 / (2 * Real.pi)) * Real.log (q * τ / (2 * Real.pi)))
  have hC1 : |C| ≤ |C| * Real.log (τ + 3) := le_mul_of_one_le_right (abs_nonneg C) hl3
  nlinarith [abs_nonneg C]

/-- **The main term, with explicit uniform hypotheses.** -/
theorem mainChi_aux_uniform (hq : 1 < q) (hprim : χ.IsPrimitive) {κ : ℕ}
    (hκdef : ∀ s, gammaFactor χ s = Complex.Gammaℝ (s + κ))
    {CB A₀ CΓ CM : ℝ} (hCB : 0 ≤ CB) (hA₀ : 0 ≤ A₀) (hCM : 0 ≤ CM)
    (hΓχ : GammaFactsChiBounded κ q CΓ)
    (hmu : ∀ τ : ℝ, 1 ≤ τ → |muq κ q τ| ≤ CM * (Real.log q + Real.log (τ + 3)))
    (hloc : ∀ t : ℝ, (NcountL χ t (t + 1) : ℝ) ≤ A₀ * (Real.log q + Real.log (|t| + 3)))
    (backlundχ : ∀ T : ℝ, 4 ≤ |T| → (∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv χ.LFunction (σ + T * I)).im|
        ≤ CB * (Real.log q + Real.log |T|))
    (verticalχ : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I) * I).im| ≤ Real.pi)
    {T : ℝ} (hT : max (CΓ + 1) 5 ≤ T) :
    |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T|
      ≤ (3 * CB + 4 + 4 * A₀ + 4 * CM + |CΓ|) * (Real.log q + Real.log T) := by
  have hT5 : 5 ≤ T := le_trans (le_max_right _ _) hT
  have hTΓ : CΓ ≤ T := by linarith [le_max_left (CΓ + 1) 5]
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hLq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
  obtain ⟨E, hE⟩ : ∃ x : ℝ, x = Real.log q + Real.log T := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; linarith
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeightL hq hprim (T - 1)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeightL hq hprim (2 * T)
  have hT₁a : T - 1 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ T := by have := hT₁mem.2; linarith
  have hT₂a : 2 * T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ 2 * T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ ≤ T₂ := by linarith
  have hN := NcountL_eq_im_halfContour hq hprim h12 hg1 hg2
  have hsplit := halfContourChi_split hq hprim hκdef h1T₁ h12 hg1 hg2
  have hgam := gammaSideChi q κ (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  have hadd : (NcountL χ T₁ T₂ : ℝ)
      = (NcountL χ T₁ T : ℝ) + (NcountL χ T (2*T) : ℝ) + (NcountL χ (2*T) T₂ : ℝ) := by
    have e1 := NcountL_add hq hprim (T₁ := T₁) (T := T) (T₂ := T₂) hT₁b (by linarith)
    have e2 := NcountL_add hq hprim (T₁ := T) (T := 2*T) (T₂ := T₂) (by linarith) hT₂a
    rw [e1, e2]
    push_cast
    ring
  have hlogsq : ∀ x : ℝ, 0 < x → x ≤ T ^ 2 → Real.log x ≤ 2 * Real.log T := by
    intro x hx hxT
    calc Real.log x ≤ Real.log (T ^ 2) := Real.log_le_log hx hxT
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  -- the end windows
  have hw1 : (NcountL χ T₁ T : ℝ) ≤ 2 * A₀ * E := by
    have hsub : NcountL χ T₁ T ≤ NcountL χ T₁ (T₁ + 1) :=
      NcountL_le_of_subset hq hprim (zerosInL_subset_of_le le_rfl (by linarith))
    have hl : Real.log (|T₁| + 3) ≤ 2 * Real.log T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < T₁)]
      exact hlogsq _ (by linarith) (by nlinarith)
    calc (NcountL χ T₁ T : ℝ) ≤ (NcountL χ T₁ (T₁ + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * (Real.log q + Real.log (|T₁| + 3)) := hloc T₁
      _ ≤ A₀ * (2 * E) := mul_le_mul_of_nonneg_left (by rw [hE]; linarith : _ ≤ 2 * E) hA₀
      _ = 2 * A₀ * E := by ring
  have hw2 : (NcountL χ (2*T) T₂ : ℝ) ≤ 2 * A₀ * E := by
    have hsub : NcountL χ (2*T) T₂ ≤ NcountL χ (2*T) (2*T + 1) :=
      NcountL_le_of_subset hq hprim (zerosInL_subset_of_le le_rfl hT₂b)
    have hl : Real.log (|2*T| + 3) ≤ 2 * Real.log T := by
      rw [abs_of_pos (by linarith : (0:ℝ) < 2*T)]
      exact hlogsq _ (by linarith) (by nlinarith)
    calc (NcountL χ (2*T) T₂ : ℝ) ≤ (NcountL χ (2*T) (2*T+1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * (Real.log q + Real.log (|2*T| + 3)) := hloc (2*T)
      _ ≤ A₀ * (2 * E) := mul_le_mul_of_nonneg_left (by rw [hE]; linarith : _ ≤ 2 * E) hA₀
      _ = 2 * A₀ * E := by ring
  -- the horizontal and vertical sides
  have habs₁ : |T₁| = T₁ := abs_of_pos (by linarith)
  have habs₂ : |T₂| = T₂ := abs_of_pos (by linarith)
  have hbk1 := backlundχ T₁ (by rw [habs₁]; linarith) hg1
  have hbk2 := backlundχ T₂ (by rw [habs₂]; linarith) hg2
  rw [habs₁] at hbk1
  rw [habs₂] at hbk2
  have hlogT₁ : Real.log T₁ ≤ Real.log T := Real.log_le_log (by linarith) hT₁b
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log T := hlogsq _ (by linarith) (by nlinarith)
  have hE₁ : Real.log q + Real.log T₁ ≤ E := by rw [hE]; linarith
  have hE₂ : Real.log q + Real.log T₂ ≤ 2 * E := by rw [hE]; linarith
  have hbk1' : |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im| ≤ CB * E :=
    hbk1.trans (mul_le_mul_of_nonneg_left hE₁ hCB)
  have hbk2' : |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im| ≤ 2 * CB * E := by
    refine hbk2.trans ?_
    calc CB * (Real.log q + Real.log T₂) ≤ CB * (2 * E) := mul_le_mul_of_nonneg_left hE₂ hCB
      _ = 2 * CB * E := by ring
  have hvert := verticalχ T₁ T₂
  have hLbound : |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
      ≤ CB * E + Real.pi + 2 * CB * E := by
    unfold RvM.halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im
          + (∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im := by
      rw [intervalIntegral.integral_mul_const]
      simp only [Complex.add_im, Complex.sub_im]
    rw [eim]
    calc _ ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im|
          + |(∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ CB * E + Real.pi + 2 * CB * E := by linarith
  -- the archimedean side
  have hμc : Continuous (muq κ q) := hΓχ.smooth.continuous
  have hμint : ∀ a b : ℝ, IntervalIntegrable (muq κ q) MeasureTheory.volume a b :=
    fun a b => hμc.intervalIntegrable a b
  have hμsplit : (∫ t in T₁..T₂, muq κ q t)
      = (∫ t in T₁..T, muq κ q t) + (∫ t in T..(2*T), muq κ q t)
        + ∫ t in (2*T)..T₂, muq κ q t := by
    have e1 : (∫ t in T₁..(2*T), muq κ q t)
        = (∫ t in T₁..T, muq κ q t) + ∫ t in T..(2*T), muq κ q t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ T) (hμint T (2*T))).symm
    have e2 : (∫ t in T₁..T₂, muq κ q t)
        = (∫ t in T₁..(2*T), muq κ q t) + ∫ t in (2*T)..T₂, muq κ q t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ (2*T)) (hμint (2*T) T₂)).symm
    rw [e2, e1]
  have hμwin : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2*T + 1 → b - a ≤ 1 →
      |∫ t in a..b, muq κ q t| ≤ 2 * CM * E := by
    intro a b ha hab hb hba
    have hbound : ∀ t ∈ Set.uIoc a b, ‖muq κ q t‖ ≤ CM * (2 * E) := by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht1 : 1 ≤ t := le_trans ha ht.1.le
      rw [Real.norm_eq_abs]
      refine (hmu t ht1).trans (mul_le_mul_of_nonneg_left ?_ hCM)
      have : Real.log (t + 3) ≤ 2 * Real.log T := hlogsq _ (by linarith) (by nlinarith [ht.2])
      rw [hE]; linarith
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at hnorm
    calc |∫ t in a..b, muq κ q t| ≤ CM * (2 * E) * (b - a) := hnorm
      _ ≤ CM * (2 * E) * 1 := mul_le_mul_of_nonneg_left hba (by positivity)
      _ = 2 * CM * E := by ring
  have hμ1 : |∫ t in T₁..T, muq κ q t| ≤ 2 * CM * E :=
    hμwin T₁ T h1T₁ hT₁b (by linarith) (by linarith)
  have hμ2 : |∫ t in (2*T)..T₂, muq κ q t| ≤ 2 * CM * E :=
    hμwin (2*T) T₂ (by linarith) hT₂a (by linarith) (by linarith)
  have hmid : |(∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)| ≤ |CΓ| * E := by
    refine (hΓχ.int_mu T hTΓ).trans ?_
    calc CΓ / T ≤ |CΓ| / T := div_le_div_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |CΓ| := div_le_self (abs_nonneg _) (by linarith)
      _ ≤ |CΓ| * E := le_mul_of_one_le_right (abs_nonneg _) hE1
  -- the identity
  have hkey : (NcountL χ T (2*T) : ℝ) - T / (2 * Real.pi) * ell1q q T
      = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
        + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
        - ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ)) := by
    have h5 : (NcountL χ T₁ T₂ : ℝ)
        = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
          + ∫ t in T₁..T₂, muq κ q t := by
      rw [hN, hsplit, Complex.add_im, mul_add, hgam]
    rw [hμsplit] at h5
    have hTell : T / (2 * Real.pi) * ell1q q T = T * ell1q q T / (2 * Real.pi) := by ring
    rw [hTell]
    linarith [hadd]
  have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hA : |(1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
      ≤ (3 * CB + 4) * E := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/Real.pi)]
    have hfrac : (1:ℝ)/Real.pi ≤ 1 := by rw [div_le_one Real.pi_pos]; exact hπ1
    have hπ4 : Real.pi ≤ 4 * E := by linarith [Real.pi_lt_d2]
    calc (1/Real.pi) * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
        ≤ 1 * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im| :=
          mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
      _ ≤ (3 * CB + 4) * E := by linarith
  rw [hkey]
  have hNc1 : (0:ℝ) ≤ (NcountL χ T₁ T : ℝ) := Nat.cast_nonneg _
  have hNc2 : (0:ℝ) ≤ (NcountL χ (2*T) T₂ : ℝ) := Nat.cast_nonneg _
  rw [← hE]
  have h1 := abs_add_le ((1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im)
    ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
      + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
  have h2 := abs_add_le (∫ t in T₁..T, muq κ q t) (∫ t in (2*T)..T₂, muq κ q t)
  have h3 := abs_add_le ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t))
    ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi))
  have h4 := abs_sub (((1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im)
      + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
      + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi))))
    ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ))
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ))] at h4
  have hsum : (3 * CB + 4) * E + (2 * CM * E + 2 * CM * E + |CΓ| * E) + (2 * A₀ * E + 2 * A₀ * E)
      = (3 * CB + 4 + 4 * A₀ + 4 * CM + |CΓ|) * E := by ring
  linarith

/-- **Riemann–von Mangoldt for primitive Dirichlet L-functions, uniformly in the modulus.** -/
theorem mainChi_uniform : ∃ C T₀ : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    1 < q → χ.IsPrimitive → ∀ T : ℝ, T₀ ≤ T →
      |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T|
        ≤ C * (Real.log q + Real.log T) := by
  obtain ⟨CΓ, hΓ⟩ := GammaChi.gammaFactsChi_uniform
  set CB : ℝ := 2 * Real.pi * (1 / Real.log (0.9 / 0.8) * (Real.log 48 + 2) + 1) with hCB
  set A₀ : ℝ := 2 * (Real.log 24 + 2) / Real.log (0.95 / 0.84) with hA₀
  set CM : ℝ := |CΓ| + 3 with hCM
  have hCB0 : 0 ≤ CB := by
    have : 0 < Real.log (0.9 / 0.8) := Real.log_pos (by norm_num)
    have : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
    positivity
  have hA₀0 : 0 ≤ A₀ := zero_le_one.trans one_le_uniformLocalCountConst
  have hCM0 : 0 ≤ CM := by positivity
  refine ⟨3 * CB + 4 + 4 * A₀ + 4 * CM + |CΓ|, max (CΓ + 1) 5, fun q _ χ hq hprim T hT => ?_⟩
  have hχ1 := ne_one_of_primitive hq hprim
  have hq1 : 1 ≤ q := hq.le
  rcases χ.even_or_odd with he | ho
  · have hΓ0 := hΓ 0 q (by norm_num) hq1
    exact mainChi_aux_uniform hq hprim (κ := 0)
      (fun s => by rw [he.gammaFactor_def]; norm_num) hCB0 hA₀0 hCM0 hΓ0
      (fun τ hτ => abs_muq_le hΓ0 hτ) (localCountChi_uniform' hq hprim)
      (fun T hT hord => backlund_horizontal_uniform' hχ1 hT hord) (vertical_twoChi hχ1) hT
  · have hΓ1 := hΓ 1 q le_rfl hq1
    exact mainChi_aux_uniform hq hprim (κ := 1)
      (fun s => by rw [ho.gammaFactor_def]; norm_num) hCB0 hA₀0 hCM0 hΓ1
      (fun τ hτ => abs_muq_le hΓ1 hτ) (localCountChi_uniform' hq hprim)
      (fun T hT hord => backlund_horizontal_uniform' hχ1 hT hord) (vertical_twoChi hχ1) hT

end RHTower
