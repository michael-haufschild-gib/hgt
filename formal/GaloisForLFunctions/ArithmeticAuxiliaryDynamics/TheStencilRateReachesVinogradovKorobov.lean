import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheRateIsTheMertensLevel
import GaloisForLFunctions.BezoutValuationIncidence.VinogradovKorobovCofinalMobiusDiscrepancy
import GaloisForLFunctions.BezoutValuationIncidence.UnconditionalEscapedMoebiusDecayAndCrossRouteBridge
import GaloisForLFunctions.HTGeometry.RpowExpAsymptotics

/-!
# The stencil rate reaches Vinogradov–Korobov

The Vinogradov–Korobov bounds for `M(N)` and `m(N)` make `exp(−(log T)^β)` a Mertens level for every
`β < 3/5`. So explicit integer producers on polynomial alphabets have rate
`exp(−(log K)^α)` for every `α < 3/5`.

This is the rung the programme asked about, reached and read exactly. A rate `α > 3/5` would give a
zero-free region past Vinogradov–Korobov, and a zero-free region past Vinogradov–Korobov would, through
the Mertens function, give that rate. The stencil does not know this by itself: its rate is certified
by the Möbius sums it contains.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The Vinogradov–Korobov saving beats every stretched exponential of exponent `< 3/5`. -/
theorem eventually_vk_le {κ' C β : ℝ} (hκ : 0 < κ') (hC : 0 < C) (hβ0 : 0 < β) (hβ : β < 3 / 5) :
    ∀ᶠ x : ℝ in atTop, C * Real.exp (-(κ' * vkScale x)) ≤ Real.exp (-(Real.log x ^ β)) := by
  set η : ℝ := (3 / 5 - β) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hlogo := (isLittleO_log_rpow_rpow_atTop (5 / 3 : ℝ) hη0).bound (zero_lt_one' ℝ)
  have hu1 : ∀ᶠ u : ℝ in atTop, 2 ≤ κ' * u ^ η :=
    ((tendsto_rpow_atTop hη0).const_mul_atTop hκ).eventually_ge_atTop 2
  have hu2 : ∀ᶠ u : ℝ in atTop, Real.log C ≤ u ^ β :=
    (tendsto_rpow_atTop hβ0).eventually_ge_atTop _
  have hu3 : ∀ᶠ u : ℝ in atTop, Real.exp 1 < u := eventually_gt_atTop _
  have hall : ∀ᶠ u : ℝ in atTop, C * Real.exp (-(κ' * (u ^ ((3 : ℝ) / 5) *
      Real.log u ^ (-((5 : ℝ) / 3))))) ≤ Real.exp (-(u ^ β)) := by
    filter_upwards [hlogo, hu1, hu2, hu3] with u h1 h2 h3 h4
    have hu0 : 0 < u := lt_trans (Real.exp_pos _) h4
    have hlog : 1 < Real.log u := by
      rw [Real.lt_log_iff_exp_lt hu0]
      exact h4
    have hlog0 : 0 < Real.log u := by linarith
    have hlp : 0 < Real.log u ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos hlog0 _
    have huη : 0 < u ^ η := Real.rpow_pos_of_pos hu0 _
    have hbound : Real.log u ^ ((5 : ℝ) / 3) ≤ u ^ η := by
      rw [Real.norm_of_nonneg hlp.le, Real.norm_of_nonneg huη.le, one_mul] at h1
      exact h1
    have hinv : (u ^ η)⁻¹ ≤ Real.log u ^ (-((5 : ℝ) / 3)) := by
      rw [Real.rpow_neg hlog0.le]
      exact inv_anti₀ hlp hbound
    have hsplit : u ^ ((3 : ℝ) / 5) = u ^ β * u ^ η * u ^ η := by
      rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]
      congr 1
      rw [hη]
      ring
    have hβp : 0 < u ^ β := Real.rpow_pos_of_pos hu0 _
    have hlow : u ^ β * u ^ η ≤ u ^ ((3 : ℝ) / 5) * Real.log u ^ (-((5 : ℝ) / 3)) := by
      calc u ^ β * u ^ η = u ^ ((3 : ℝ) / 5) * (u ^ η)⁻¹ := by
            rw [hsplit]
            field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
    have hmain : u ^ β + Real.log C ≤ κ' * (u ^ ((3 : ℝ) / 5) * Real.log u ^ (-((5 : ℝ) / 3))) := by
      have h5 : κ' * (u ^ β * u ^ η) ≤ κ' * (u ^ ((3 : ℝ) / 5) * Real.log u ^ (-((5 : ℝ) / 3))) :=
        mul_le_mul_of_nonneg_left hlow hκ.le
      have h6 : 2 * u ^ β ≤ κ' * u ^ η * u ^ β := mul_le_mul_of_nonneg_right h2 hβp.le
      nlinarith
    calc C * Real.exp (-(κ' * (u ^ ((3 : ℝ) / 5) * Real.log u ^ (-((5 : ℝ) / 3)))))
        = Real.exp (Real.log C + -(κ' * (u ^ ((3 : ℝ) / 5) * Real.log u ^ (-((5 : ℝ) / 3))))) := by
          rw [Real.exp_add, Real.exp_log hC]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact Real.tendsto_log_atTop.eventually hall

/-- **`exp(−(log T)^β)` is a Mertens level for every `β < 3/5`.** -/
theorem isMertensLevel_vk {β : ℝ} (hβ0 : 0 < β) (hβ : β < 3 / 5) :
    IsMertensLevel fun T => Real.exp (-(Real.log (T : ℝ) ^ β)) := by
  obtain ⟨C₁, hC₁, hM⟩ := BezoutValuationIncidence.exists_abs_mertensM_le_vk_rate
  obtain ⟨C₂, hC₂, M₀, _, hH⟩ := BezoutValuationIncidence.exists_abs_moebiusHarmonicTail_le_vk_rate
  have hκ24 : 0 < vkKappa / 24 := by have := vkKappa_pos; positivity
  have hκ48 : 0 < vkKappa / 48 := by have := vkKappa_pos; positivity
  have h1 := tendsto_natCast_atTop_atTop.eventually (eventually_vk_le (C := C₁ + 1) hκ24 (by linarith) hβ0 hβ)
  have h2 := tendsto_natCast_atTop_atTop.eventually (eventually_vk_le (C := C₂) hκ48 hC₂ hβ0 hβ)
  -- A pointwise bound on the Mertens function.
  have hMpt : ∀ᶠ N : ℕ in atTop, |mertens N| ≤ (N : ℝ) * Real.exp (-(Real.log (N : ℝ) ^ β)) := by
    filter_upwards [hM, h1] with N h3 h4
    rw [mertens_eq_mertensM]
    refine h3.trans ?_
    have hexp : Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) =
        Real.exp (-(vkKappa / 24 * vkScale (N : ℝ))) := by
      congr 2
      ring
    rw [hexp]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hE := (Real.exp_pos (-(vkKappa / 24 * vkScale (N : ℝ)))).le
    calc C₁ * (N : ℝ) * Real.exp (-(vkKappa / 24 * vkScale (N : ℝ)))
        ≤ (N : ℝ) * ((C₁ + 1) * Real.exp (-(vkKappa / 24 * vkScale (N : ℝ)))) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hN
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hMpt
  have hlogT : ∀ᶠ T : ℕ in atTop, 1 ≤ Real.log (T : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hpoly := HTGeometry.eventually_mul_rpow_le_exp_rpow (18 : ℝ) (c := 1) (δ := β) (p := 1) one_pos hβ0
  have hpolyT := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hpoly
  filter_upwards [eventually_ge_atTop N₁, eventually_ge_atTop M₀, eventually_ge_atTop 1, hlogT, h2,
    hpolyT] with T hT1 hT2 hT3 hT4 hT5 hT6
  simp only [Function.comp] at hT6
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT3
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT0 : (0 : ℝ) ≤ Real.log (T : ℝ) := by linarith
  have hpow0 : 0 ≤ Real.log (T : ℝ) ^ β := by positivity
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_, ?_, ?_, ?_⟩
  · -- `1/T ≤ δ`.
    have hle : Real.log (T : ℝ) ^ β ≤ Real.log (T : ℝ) := by
      calc Real.log (T : ℝ) ^ β ≤ Real.log (T : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT4 (by linarith)
        _ = Real.log (T : ℝ) := Real.rpow_one _
    have hval : 1 / (T : ℝ) = Real.exp (-Real.log (T : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log hT0, one_div]
    rw [hval]
    exact Real.exp_le_exp.mpr (by linarith)
  · intro y hy
    have hyR : (T : ℝ) ≤ y := by exact_mod_cast hy
    have hlogmono : Real.log (T : ℝ) ≤ Real.log (y : ℝ) := Real.log_le_log hT0 hyR
    have hpowmono : Real.log (T : ℝ) ^ β ≤ Real.log (y : ℝ) ^ β :=
      Real.rpow_le_rpow hlogT0 hlogmono hβ0.le
    have hexpmono : Real.exp (-(Real.log (y : ℝ) ^ β)) ≤ Real.exp (-(Real.log (T : ℝ) ^ β)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hy0 : (0 : ℝ) ≤ y := by linarith
    calc |mertens y| ≤ (y : ℝ) * Real.exp (-(Real.log (y : ℝ) ^ β)) := hN₁ y (hT1.trans hy)
      _ ≤ (y : ℝ) * Real.exp (-(Real.log (T : ℝ) ^ β)) := mul_le_mul_of_nonneg_left hexpmono hy0
      _ = _ := mul_comm _ _
  · have hval : |mobiusHarmonic T| = |SelectivePositivityAndThresholdLaws.moebiusHarmonicTail T| := by
      rw [mobiusHarmonic_eq_deninger, SelectivePositivityAndThresholdLaws.moebiusHarmonicTail,
        abs_neg, RHTower.deningerHarmonicPartial]
    rw [hval]
    refine (hH T hT2).trans ?_
    have hexp : Real.exp (-(vkKappa * vkScale (T : ℝ) / 48)) =
        Real.exp (-(vkKappa / 48 * vkScale (T : ℝ))) := by
      congr 2
      ring
    rw [hexp]
    exact hT5
  · -- The polylogarithm against the level.
    rw [Real.rpow_one, one_mul] at hT6
    have hE := Real.exp_pos (Real.log (T : ℝ) ^ β)
    rw [Real.exp_neg, inv_mul_le_iff₀ hE]
    nlinarith

/-- **A stretched exponential Mertens level gives the rate at every smaller exponent.** -/
theorem hasRate_of_level_exp {α β : ℝ} (hα0 : 0 < α) (hαβ : α < β)
    (hlevel : IsMertensLevel fun T => Real.exp (-(Real.log (T : ℝ) ^ β))) :
    HasRate fun K => Real.exp (-(Real.log (K : ℝ) ^ α)) := by
  have hβ0 : 0 < β := by linarith
  set c : ℝ := (1 / 5 : ℝ) ^ β with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hlogK : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp1 := hlogK.eventually (HTGeometry.eventually_mul_rpow_le_exp_rpow (360 : ℝ)
    (c := c / 2) (δ := β) (p := 2) (by positivity) hβ0)
  have hp2 : ∀ᶠ K : ℕ in atTop, 2 / c ≤ Real.log (K : ℝ) ^ (β - α) :=
    (hlogK.comp tendsto_id).eventually
      ((tendsto_rpow_atTop (by linarith : 0 < β - α)).eventually_ge_atTop (2 / c))
  filter_upwards [eventually_producer_of_level hlevel,
    tendsto_levelCutoff.eventually_ge_atTop 1, hp1, hp2, hlogK.eventually_ge_atTop 20,
    eventually_ge_atTop 1] with K hK hT1 h1 h2 h3 hK1
  obtain ⟨c', m, B, hP, ha, hr⟩ := hK
  refine ⟨c', m, B, hP, ha, hr.trans ?_⟩
  set T := levelCutoff K with hT
  set u := Real.log (K : ℝ) with hu
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hT0 : (0 : ℝ) < T := by linarith
  have hu0 : 0 < u := by linarith
  -- The logarithm of the cutoff is pinched between `u/5` and `u`.
  have hlow : u / 5 ≤ Real.log (T : ℝ) := by
    have h4 := half_rpow_le_levelCutoff hT1
    have h5 : Real.log ((K : ℝ) ^ (1 / 4 : ℝ) / 2) ≤ Real.log (T : ℝ) :=
      Real.log_le_log (by positivity) h4
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hK0] at h5
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hup : Real.log (T : ℝ) ≤ u := by
    have h4 : (T : ℝ) ≤ K := by
      have h5 := levelCutoff_pow_le K
      have h6 : (T : ℝ) ≤ (T : ℝ) ^ 4 := by
        calc (T : ℝ) = (T : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (T : ℝ) ^ 4 := pow_le_pow_right₀ hTR (by norm_num)
      linarith
    exact Real.log_le_log hT0 h4
  have hlogT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hTR
  -- The level at the cutoff.
  have hδ : Real.exp (-(Real.log (T : ℝ) ^ β)) ≤ Real.exp (-(c * u ^ β)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have h4 : (u / 5) ^ β ≤ Real.log (T : ℝ) ^ β := Real.rpow_le_rpow (by positivity) hlow hβ0.le
    have h5 : (u / 5) ^ β = c * u ^ β := by
      rw [hc, div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) hu0.le]
      norm_num
    linarith
  -- The polylogarithm.
  have hpolylog : (3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ)) ≤ 45 * u ^ 2 := by
    have h4 : 3 + 6 * Real.log (T : ℝ) ≤ 9 * u := by linarith
    have h5 : 1 + 4 * Real.log (T : ℝ) ≤ 5 * u := by linarith
    calc _ ≤ (9 * u) * (5 * u) := mul_le_mul h4 h5 (by linarith) (by linarith)
      _ = _ := by ring
  have hE0 := Real.exp_pos (-(Real.log (T : ℝ) ^ β))
  have hmain : 8 * (Real.exp (-(Real.log (T : ℝ) ^ β)) * (3 + 6 * Real.log (T : ℝ))) *
      (1 + 4 * Real.log (T : ℝ)) ≤ 360 * u ^ 2 * Real.exp (-(c * u ^ β)) := by
    have hprod : 0 ≤ (3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ)) := by positivity
    calc _ = 8 * (Real.exp (-(Real.log (T : ℝ) ^ β)) *
          ((3 + 6 * Real.log (T : ℝ)) * (1 + 4 * Real.log (T : ℝ)))) := by ring
      _ ≤ 8 * (Real.exp (-(c * u ^ β)) * (45 * u ^ 2)) := by gcongr
      _ = _ := by ring
  refine hmain.trans ?_
  -- The final comparison.
  have hrpow2 : u ^ (2 : ℝ) = u ^ 2 := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [hrpow2] at h1
  have huβ : 0 < u ^ β := Real.rpow_pos_of_pos hu0 _
  have hα2 : u ^ α ≤ c / 2 * u ^ β := by
    have hsplit : u ^ β = u ^ α * u ^ (β - α) := by
      rw [← Real.rpow_add hu0]
      congr 1
      ring
    have huα : 0 < u ^ α := Real.rpow_pos_of_pos hu0 _
    have h4 : 2 / c ≤ u ^ (β - α) := h2
    rw [div_le_iff₀ hc0] at h4
    rw [hsplit]
    nlinarith
  calc 360 * u ^ 2 * Real.exp (-(c * u ^ β))
      ≤ Real.exp (c / 2 * u ^ β) * Real.exp (-(c * u ^ β)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-(c / 2 * u ^ β)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- **Integer producers reach the Vinogradov–Korobov rate.** For every `0 < α < 3/5`, for all large
`K` there is an integer producer on an alphabet in `[1, K]` of rate at most `exp(−(log K)^α)`. -/
theorem hasRate_vk {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 5) :
    HasRate fun K => Real.exp (-(Real.log (K : ℝ) ^ α)) :=
  hasRate_of_level_exp hα0 (by linarith : α < (α + 3 / 5) / 2)
    (isMertensLevel_vk (by linarith) (by linarith))

/-- **The region the stencils read.** For every `0 < α < 3/5` the Möbius producers read back a
zero-free region `Re ρ ≤ 1 − c Λ^{1 − 1/α}`, `Λ = log (24 ‖ρ‖)`. This is the Vinogradov–Korobov shape,
through the rate law alone. -/
theorem exists_zeroFree_of_stencils {α : ℝ} (hα0 : 0 < α) (hα : α < 3 / 5) :
    ∃ T₀ : ℝ, ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ ‖ρ‖ →
      ρ.re ≤ 1 - (1 / (7 * (4 : ℝ) ^ (1 / α))) * Real.log (24 * ‖ρ‖) ^ (1 - 1 / α) :=
  exists_re_le_of_hasRate_exp hα0 (by linarith) (hasRate_vk hα0 hα)

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
