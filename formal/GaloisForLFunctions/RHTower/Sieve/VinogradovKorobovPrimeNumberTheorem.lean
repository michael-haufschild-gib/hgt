import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovChebyshevContour
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpSelfRateOne
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSmoothVsSharp
import GaloisForLFunctions.PNTPlus.MediumPNT

/-!
# The prime number theorem at Vinogradov–Korobov strength

Removing the scalar `2π` and the bracket from the smoothed contour bound, passing from the
smoothed sum to `ψ` at cost `(H + 1) log(N + H)`, and replacing the cutoff's mass by `N` at cost
`H`, every correction is at most `(log N)²(N + H + 1)e^{-s/6}`.  Since `s ≥ √(log N)`, the factor
`(log N)² ≤ s⁴` is absorbed by halving the exponent once more:

```text
|ψ(N) - N| ≤ B · N · exp(-c (log N)^{3/5} (log log N)^{-5/3}),      c = 1/(288·10⁸).
```

Against Littlewood's `exp(-c√(log N · log log N))` the exponent `1/2` becomes `3/5`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology Asymptotics ArithmeticFunction
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- `(log N)² e^{-s/6} ≤ 497664 e^{-s/12}` once `√(log N) ≤ s`. -/
theorem vk_log_sq_absorb {L s : ℝ} (hL : 0 ≤ L) (hs : Real.sqrt L ≤ s) :
    L ^ 2 * Real.exp (-(s / 6)) ≤ 497664 * Real.exp (-(s / 12)) := by
  have hs0 : 0 ≤ s := le_trans (Real.sqrt_nonneg L) hs
  have hL2 : L ^ 2 ≤ s ^ 4 := by
    have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg L) hs 4
    have h2 : Real.sqrt L ^ 4 = L ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hL]
    linarith
  have hfact := Real.pow_div_factorial_le_exp (s / 12) (by positivity) 4
  have hs4 : s ^ 4 ≤ 497664 * Real.exp (s / 12) := by
    rw [div_pow] at hfact
    norm_num [Nat.factorial] at hfact
    linarith
  have hsplit : Real.exp (s / 12) * Real.exp (-(s / 6)) = Real.exp (-(s / 12)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE := Real.exp_pos (-(s / 6))
  calc L ^ 2 * Real.exp (-(s / 6)) ≤ s ^ 4 * Real.exp (-(s / 6)) :=
        mul_le_mul_of_nonneg_right hL2 hE.le
    _ ≤ 497664 * Real.exp (s / 12) * Real.exp (-(s / 6)) :=
        mul_le_mul_of_nonneg_right hs4 hE.le
    _ = 497664 * Real.exp (-(s / 12)) := by rw [mul_assoc, hsplit]

/-- **The sharp Chebyshev sum against the cutoff, at Vinogradov–Korobov strength.** -/
theorem exists_norm_sum_vonMangoldt_sub_self_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ)‖
        ≤ B * Real.log N ^ 2 * (N + vkWidth N + 1) * Real.exp (-(vkSaving N / 6)) := by
  obtain ⟨δ, B₁, hδ, hB₁, hrate⟩ := exists_norm_tsum_vonMangoldt_vk_rate
  refine ⟨B₁ + 7, by linarith, ?_⟩
  filter_upwards [hrate, eventually_vk_conditions hδ 0] with N hcap hcond
  obtain ⟨hN3, hL3, -, hLg8, hLg2, hLgL, -, -, hu0, hu8, -, -⟩ := hcond
  have hsave : vkSaving N = Real.log (vkHeight N) / 2 := vkSaving_eq N
  have hH : vkWidth N = N * Real.exp (-(vkSaving N / 6)) := rfl
  have hT0 : 0 < vkHeight N := Real.exp_pos _
  set s := vkSaving N with hsdef
  set T := vkHeight N with hTdef
  set H := vkWidth N with hHdef
  set u := vkUniformRegWidth δ T with hudef
  clear_value s T H u
  set L := Real.log N with hLdef
  set A := ∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ)
    * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ) with hAdef
  set Mm := mellin (fun x : ℝ =>
    ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1 with hMmdef
  set P := ∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ) with hPdef
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hs0 : 0 ≤ s := by rw [hsave]; linarith
  have hHpos : 0 < H := by rw [hH]; positivity
  have hHN : H ≤ N := by
    rw [hH]
    exact mul_le_of_le_one_right hN0.le (Real.exp_le_one_iff.mpr (by linarith))
  have hHZ : H ≤ (N + H + 1) * Real.exp (-(s / 6)) := by
    rw [hH]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hZ0 : 0 < N + H + 1 := by linarith
  have hE0 := Real.exp_pos (-(s / 6))
  have hE23 : Real.exp (-(2 * s / 3)) ≤ Real.exp (-(s / 6)) := Real.exp_le_exp.mpr (by linarith)
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  -- the scalar and the bracket
  have hπ1 : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hcap' : ‖((2 * Real.pi : ℝ) : ℂ) * A
      - Mm * (((2 * Real.arctan (T / (chebRightTwo T - 1))
              - 2 * Real.arctan (T / ((1 - u) - 1)) : ℝ)) : ℂ)‖
      ≤ B₁ * L ^ 2 * (N + H + 1) * Real.exp (-(2 * s / 3)) := by
    rwa [← Complex.real_smul]
  have hT1 : 1 ≤ T := by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith
  have hd1 := one_lt_chebRightTwo hLg8
  have hbr := abs_bracket_sub_two_pi_le (c := 1 - u) (by linarith) hd1 hT0
  have hwd : chebRightTwo T - (1 - u) ≤ 1 := by
    have hinvLg : 1 / Real.log T ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    rw [chebRightTwo]; linarith
  have hTinv : 1 / T ≤ Real.exp (-(s / 6)) := by
    have h1 : Real.exp (-Real.log T) ≤ Real.exp (-(s / 6)) :=
      Real.exp_le_exp.mpr (by linarith only [hsave, hs0, hLg8])
    rw [Real.exp_neg, Real.exp_log hT0] at h1
    rwa [one_div]
  have hbr2 : 2 * ((chebRightTwo T - (1 - u)) / T) ≤ 2 * Real.exp (-(s / 6)) := by
    have h1 : (chebRightTwo T - (1 - u)) / T ≤ 1 / T :=
      div_le_div_of_nonneg_right hwd (by linarith)
    linarith
  have hMm := norm_mellin_smoothWeight_one_le hN0.le hHpos
  have hmain2 : ‖Mm * (((2 * Real.arctan (T / (chebRightTwo T - 1))
              - 2 * Real.arctan (T / ((1 - u) - 1)) : ℝ)) : ℂ)
      - Mm * (((2 * Real.pi : ℝ)) : ℂ)‖
      ≤ (N + H + 1) * (2 * Real.exp (-(s / 6))) := by
    rw [norm_mul_sub_mul_ofReal]
    exact mul_le_mul (by linarith) (hbr.trans hbr2) (abs_nonneg _) hZ0.le
  have hAM := norm_sub_le_of_scaled hπ1 hcap' hmain2
  -- the sharp transfer
  have htr : ‖A - P‖ ≤ (H + 1) * Real.log (N + H) :=
    norm_tsum_vonMangoldt_smoothWeight_sub_sum_le hN0 hHpos (by linarith)
  have hlogY : Real.log (N + H) ≤ 2 * L := by
    have h0 : 2 * N ≤ N ^ 2 := by nlinarith only [hN3]
    have h2 := Real.log_le_log (by linarith) (show N + H ≤ N ^ 2 by linarith only [h0, hHN])
    rw [Real.log_pow] at h2; push_cast at h2; linarith only [h2]
  have hcost : (H + 1) * Real.log (N + H) ≤ 4 * L * ((N + H + 1) * Real.exp (-(s / 6))) := by
    have hH1 : H + 1 ≤ 2 * ((N + H + 1) * Real.exp (-(s / 6))) := by
      have h1 : Real.exp (-L) ≤ Real.exp (-(s / 6)) :=
        Real.exp_le_exp.mpr (by linarith only [hsave, hLgL, hs0])
      rw [Real.exp_neg, hLdef, Real.exp_log hN0] at h1
      have h2 : 1 ≤ N * Real.exp (-(s / 6)) := by
        calc (1 : ℝ) = N * N⁻¹ := (mul_inv_cancel₀ hN0.ne').symm
          _ ≤ N * Real.exp (-(s / 6)) := mul_le_mul_of_nonneg_left h1 hN0.le
      have h3 : N * Real.exp (-(s / 6)) ≤ (N + H + 1) * Real.exp (-(s / 6)) :=
        mul_le_mul_of_nonneg_right (by linarith) hE0.le
      rw [← hH] at h2 h3
      linarith
    have hlog0 : 0 ≤ Real.log (N + H) := Real.log_nonneg (by linarith)
    calc (H + 1) * Real.log (N + H)
        ≤ (2 * ((N + H + 1) * Real.exp (-(s / 6)))) * (2 * L) :=
          mul_le_mul hH1 hlogY hlog0 (by positivity)
      _ = 4 * L * ((N + H + 1) * Real.exp (-(s / 6))) := by ring
  -- the mass
  have hmw : ‖Mm - ((N : ℝ) : ℂ)‖ ≤ H := norm_mellin_one_sub_ofReal_le hN0.le hHpos
  -- the triangle inequality
  have htri : ‖P - ((N : ℝ) : ℂ)‖ ≤ ‖A - P‖ + ‖A - Mm‖ + ‖Mm - ((N : ℝ) : ℂ)‖ := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub P Mm ((N : ℝ) : ℂ)
    have h2 := norm_sub_le_norm_sub_add_norm_sub P A Mm
    rw [norm_sub_rev P A] at h2
    linarith only [h1, h2]
  -- collect
  set Q := (N + H + 1) * Real.exp (-(s / 6)) with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  have hc1 : B₁ * L ^ 2 * (N + H + 1) * Real.exp (-(2 * s / 3)) ≤ B₁ * L ^ 2 * Q := by
    rw [hQdef, show B₁ * L ^ 2 * (N + H + 1) * Real.exp (-(2 * s / 3))
      = B₁ * L ^ 2 * ((N + H + 1) * Real.exp (-(2 * s / 3))) by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE23 hZ0.le) (by positivity)
  have hc2 : (N + H + 1) * (2 * Real.exp (-(s / 6))) = 2 * Q := by rw [hQdef]; ring
  have hc3 : 4 * L * Q ≤ 4 * L ^ 2 * Q :=
    mul_le_mul_of_nonneg_right (by linarith only [hLL]) hQ0
  have hc4 : 2 * Q ≤ 2 * L ^ 2 * Q := mul_le_mul_of_nonneg_right (by linarith only [hL2]) hQ0
  have hc5 : Q ≤ L ^ 2 * Q := by
    have := mul_le_mul_of_nonneg_right hL2 hQ0
    linarith only [this]
  have hgoal : (B₁ + 7) * L ^ 2 * (N + H + 1) * Real.exp (-(s / 6)) = (B₁ + 7) * L ^ 2 * Q := by
    rw [hQdef]; ring
  rw [hgoal]
  linarith only [htri, htr, hcost, hAM, hmw, hHZ, hc1, hc2, hc3, hc4, hc5]

/-- **The prime number theorem at Vinogradov–Korobov strength**, in Chebyshev form:

```text
|ψ(N) - N| ≤ B · N · exp(-κ·(log N)^{3/5}(log log N)^{-5/3}/24),      κ = 1/(12·10⁸).
``` -/
theorem exists_abs_sum_vonMangoldt_sub_self_vk_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      |(∑ n ∈ Finset.range (⌊N⌋₊ + 1), (vonMangoldt n : ℝ)) - N|
        ≤ B * N * Real.exp (-(vkKappa * vkScale N / 24)) := by
  obtain ⟨B, hB, hrate⟩ := exists_norm_sum_vonMangoldt_sub_self_vk_rate
  refine ⟨3 * 497664 * B, by positivity, ?_⟩
  filter_upwards [hrate, eventually_vk_conditions one_pos 0] with N hN hcond
  obtain ⟨hN3, hL3, -, -, hLg2, -, -, -, -, -, -, -⟩ := hcond
  have hN0 : 0 < N := by linarith
  have hsave : vkSaving N = Real.log (vkHeight N) / 2 := vkSaving_eq N
  have hsq : Real.sqrt (Real.log N) ≤ vkSaving N := by rw [hsave]; linarith
  have habs := vk_log_sq_absorb (by linarith : (0 : ℝ) ≤ Real.log N) hsq
  have hH0 : 0 ≤ vkWidth N := by unfold vkWidth; positivity
  have hHN : vkWidth N ≤ N := by
    unfold vkWidth
    have hs0 : 0 ≤ vkSaving N := le_trans (Real.sqrt_nonneg _) hsq
    exact mul_le_of_le_one_right hN0.le (Real.exp_le_one_iff.mpr (by linarith))
  have hZ3 : N + vkWidth N + 1 ≤ 3 * N := by linarith
  have hexp : Real.exp (-(vkSaving N / 12)) = Real.exp (-(vkKappa * vkScale N / 24)) := by
    rw [vkSaving]; congr 1; ring
  have hcast : ((∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ))
      = (((∑ n ∈ Finset.range (⌊N⌋₊ + 1), (vonMangoldt n : ℝ)) - N : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hN
  have hstep : B * Real.log N ^ 2 * (N + vkWidth N + 1) * Real.exp (-(vkSaving N / 6))
      ≤ B * (N + vkWidth N + 1) * (497664 * Real.exp (-(vkSaving N / 12))) := by
    have h1 := mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ B * (N + vkWidth N + 1))
    calc B * Real.log N ^ 2 * (N + vkWidth N + 1) * Real.exp (-(vkSaving N / 6))
        = B * (N + vkWidth N + 1) * (Real.log N ^ 2 * Real.exp (-(vkSaving N / 6))) := by ring
      _ ≤ _ := h1
  have hstep2 : B * (N + vkWidth N + 1) * (497664 * Real.exp (-(vkSaving N / 12)))
      ≤ 3 * 497664 * B * N * Real.exp (-(vkKappa * vkScale N / 24)) := by
    rw [hexp]
    have hE := Real.exp_pos (-(vkKappa * vkScale N / 24))
    have h1 := mul_le_mul_of_nonneg_left hZ3 hB
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 497664 * Real.exp
      (-(vkKappa * vkScale N / 24)))
    calc B * (N + vkWidth N + 1) * (497664 * Real.exp (-(vkKappa * vkScale N / 24)))
        ≤ B * (3 * N) * (497664 * Real.exp (-(vkKappa * vkScale N / 24))) := h2
      _ = 3 * 497664 * B * N * Real.exp (-(vkKappa * vkScale N / 24)) := by ring
  linarith [hN, hstep, hstep2]

/-- **The prime number theorem at Vinogradov–Korobov strength**, in the `IsBigO` shape of the
vendored `MediumPNT`:

```text
ψ - id  =O[atTop]  x · exp(-c·(log x)^{3/5}·(log log x)^{-5/3}).
``` -/
theorem chebyshevPsi_sub_id_isBigO_vinogradovKorobov :
    ∃ c > 0, (Chebyshev.psi - id) =O[atTop] fun x : ℝ =>
      x * Real.exp (-c * (Real.log x ^ ((3 : ℝ) / 5)
        * Real.log (Real.log x) ^ (-((5 : ℝ) / 3)))) := by
  obtain ⟨B, hB, hrate⟩ := exists_abs_sum_vonMangoldt_sub_self_vk_rate
  refine ⟨vkKappa / 24, by have := vkKappa_pos; positivity, Asymptotics.IsBigO.of_bound B ?_⟩
  filter_upwards [hrate, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have hcongr : Real.exp (-(vkKappa * vkScale N / 24))
      = Real.exp (-(vkKappa / 24) * (Real.log N ^ ((3 : ℝ) / 5)
          * Real.log (Real.log N) ^ (-((5 : ℝ) / 3)))) := by
    rw [vkScale]; congr 1; ring
  have hgnorm : ‖N * Real.exp (-(vkKappa / 24) * (Real.log N ^ ((3 : ℝ) / 5)
        * Real.log (Real.log N) ^ (-((5 : ℝ) / 3))))‖
      = N * Real.exp (-(vkKappa / 24) * (Real.log N ^ ((3 : ℝ) / 5)
        * Real.log (Real.log N) ^ (-((5 : ℝ) / 3)))) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Pi.sub_apply, id_eq, Chebyshev.psi_eq_sum_range, Real.norm_eq_abs, hgnorm]
  rw [hcongr] at hN
  linarith [hN]

end

end RHTower.Sieve
