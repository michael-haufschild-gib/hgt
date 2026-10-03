import GaloisForLFunctions.RHTower.XiLocalWindowDensity
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergUpper

/-!
# The off-line tail law in every window `[T, T + T^{24/25}]` with mollifiers of length `U^{21/50}`

The high-block bound in window form for coefficient length `U^{21/50}`
(`exists_highBlock_bound_of_mainTerm_upper_window`) loses only the taper `2a^{19/20}` on blocks
`a ≥ U^{49/50}`, and a window `[T, T + H]` with `H ≤ T` lies above `(T + H)^{49/50}` once
`T ≥ 2^{50}`.  So Selberg's twisted mollifier of length `U^{21/50}` has mean square
`c_R = e^{2R}/(1 − e^{−21R/25})` per unit length on every such window
(`eventually_window_meanSquare_selberg_upper`), and the window analysis of `ZetaLocalWindowTail`
gives, for every `η > 0`, all large `T` and every `T^{24/25} ≤ H ≤ T`,

* `4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½ − R/log(T+H−1))⁺ ≤ (log c_R − 2R + η) H`,
* `4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½)⁺ ≤ (log c_R − R + η) H`

(`eventually_windowTail_le_selberg_upper`).  At `R = 3/4` the window moment is at most `H/8`
(`eventually_windowTail_zero_le_eighth`), so on every window the first Laguerre inequality with
vertical monotonicity of `|Ξ|`, all-order slice positivity and the Speiser clean-height condition
hold on measure `≥ (3/4) H − 3`, and the Hadamard sign `Re(ξ'/ξ) ≥ 0` on area `≥ (3/8) H − 3/2`.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval ComplexOrder

namespace RHTower

noncomputable section

namespace ZetaGateProductAFE

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- **The mollified mean square on windows.**  With Selberg's twisted coefficients of length
`U^{21/50}`, for `U` large, every displacement `d` with `R ≤ d log U`, `d log(U − 1) ≤ R` and every
window `U^{49/50} ≤ a ≤ v ≤ 2a`, `v ≤ U`:
`∫_a^v ‖ζΨ(½ − d + iτ)‖² dτ ≤ (c_R + ε)(v − a + 2a^{19/20})`. -/
theorem eventually_window_meanSquare_selberg_upper {R : ℝ} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((selbergRealUpper R U n : ℝ) : ℂ)) (Finset.Icc 1 (mollUpper U))
                (displacedLinePt d τ)‖ ^ 2)
          ≤ (selbergBlockConstUpper R + ε) * (v - a + 2 * a ^ ((19 : ℝ) / 20)) := by
  have hN : ∀ᶠ U in atTop, (mollUpper U : ℝ) ≤ U ^ ((21 : ℝ) / 50) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with U hU
    exact mollUpper_le hU
  have hw : ∀ U, ∀ n ∈ Finset.Icc 1 (mollUpper U), |selbergRealUpper R U n| ≤ 1 := fun U n hn =>
    Sieve.abs_twistedWeight_le _ _ (Finset.mem_Icc.mp hn).1
  have hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (mollUpper U) (selbergRealUpper R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * selbergBlockFactorUpper R U := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 50)] with U hU
    intro d hd hd8 hRd hdU1 a v η hη h4 hav hvU hηa haη haU
    have hU3 : (3 : ℝ) ≤ U := le_trans (by norm_num) hU
    exact selberg_mainTerm_le_upper hR hd hd8 hRd hdU1 hU3 (two_le_mollUpper hU) hη h4 hav hvU hηa
      haη haU
  exact exists_highBlock_bound_of_mainTerm_upper_window hR (tendsto_selbergBlockFactorUpper hR)
    mollUpper (selbergRealUpper R) hN hw hmain ε hε

end ZetaGateProductAFE

/-! ## The tail law on windows -/

/-- `log c_R ≥ 2R`, since `c_R ≥ e^{2R}`. -/
theorem two_mul_le_log_selbergBlockConstUpper {R : ℝ} (hR : 0 < R) :
    2 * R ≤ Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) := by
  unfold ZetaGateProductAFE.selbergBlockConstUpper
  have h1 : 0 < Real.exp (-(21 * R / 25)) := Real.exp_pos _
  have h2 := ZetaGateProductAFE.exp_neg_lt_one (show 0 < 21 * R / 25 by positivity)
  rw [Real.log_div (Real.exp_pos _).ne' (by linarith), Real.log_exp]
  have : Real.log (1 - Real.exp (-(21 * R / 25))) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  linarith

/-- `U^{49/50} ≤ T` when `U ≤ 2T` and `T ≥ 2^{50}`. -/
theorem rpow_fortyNine_fiftieths_le_of_le_two_mul {T U : ℝ} (hT50 : (2 : ℝ) ^ 50 ≤ T)
    (hU0 : 0 ≤ U) (hU : U ≤ 2 * T) : U ^ ((49 : ℝ) / 50) ≤ T := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT50
  have h1 : U ^ ((49 : ℝ) / 50) ≤ (2 * T) ^ ((49 : ℝ) / 50) :=
    Real.rpow_le_rpow hU0 hU (by norm_num)
  have h2 : (2 * T) ^ ((49 : ℝ) / 50) = (2 : ℝ) ^ ((49 : ℝ) / 50) * T ^ ((49 : ℝ) / 50) :=
    Real.mul_rpow (by norm_num) hT0.le
  have h3 : (2 : ℝ) ^ ((49 : ℝ) / 50) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (49 : ℝ) / 50 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have h4 : 2 ≤ T ^ ((1 : ℝ) / 50) := by
    have e : ((2 : ℝ) ^ 50) ^ ((1 : ℝ) / 50) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hT50 (by norm_num)
  have hsplit : T = T ^ ((49 : ℝ) / 50) * T ^ ((1 : ℝ) / 50) := by
    rw [← Real.rpow_add hT0]; norm_num
  have h7 : 0 ≤ T ^ ((49 : ℝ) / 50) := Real.rpow_nonneg hT0.le _
  have h8 : 2 * T ^ ((49 : ℝ) / 50) ≤ T := by
    calc 2 * T ^ ((49 : ℝ) / 50) ≤ T ^ ((1 : ℝ) / 50) * T ^ ((49 : ℝ) / 50) :=
          mul_le_mul_of_nonneg_right h4 h7
      _ = T := by rw [mul_comm]; exact hsplit.symm
  have h9 : (2 : ℝ) ^ ((49 : ℝ) / 50) * T ^ ((49 : ℝ) / 50) ≤ 2 * T ^ ((49 : ℝ) / 50) :=
    mul_le_mul_of_nonneg_right h3 h7
  linarith

theorem exists_window_littlewood_upper {R c C K T H : ℝ} (hR : 0 < R)
    (hwide : ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc σ₀ (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb))
    (hT50 : (2 : ℝ) ^ 50 ≤ T) (hH4 : 4 ≤ H) (hHT : H ≤ T) (hlogT : 8 * R ≤ Real.log T)
    (hms : ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log (T + H) →
      d * Real.log (T + H - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → (T + H) ^ ((49 : ℝ) / 50) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ T + H →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (fun n => ((ZetaGateProductAFE.selbergRealUpper R (T + H) n : ℝ) : ℂ))
                (Finset.Icc 1 (ZetaGateProductAFE.mollUpper (T + H))) (displacedLinePt d τ)‖ ^ 2)
          ≤ c * (v - a + 2 * a ^ ((19 : ℝ) / 20))) :
    ∃ T₁ T₂ : ℝ, T < T₁ ∧ T₁ < T + 1 ∧ T + H - 1 < T₂ ∧ T₂ < T + H ∧
      2 * Real.pi * (R / Real.log T₂ * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
          + windowTail (R / Real.log T₂) T₁ T₂)
        ≤ (T₂ - T₁) / 2 * Real.log (c * (T₂ - T₁ + 2 * T₁ ^ ((19 : ℝ) / 20)) / (T₂ - T₁))
          + C + K * (Real.log T₂
            + Real.log ((ZetaGateProductAFE.mollUpper (T + H) : ℝ) ^ (5 : ℕ))) := by
  classical
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = T + H := ⟨_, rfl⟩
  rw [← hUdef] at hms ⊢
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT50
  have hU2T : U ≤ 2 * T := by linarith
  have hU50 : (2 : ℝ) ^ 50 ≤ U := by linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ZetaGateProductAFE.mollUpper U := ⟨_, rfl⟩
  rw [← hNdef] at hms ⊢
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℂ,
      b = fun n => ((ZetaGateProductAFE.selbergRealUpper R U n : ℝ) : ℂ) := ⟨_, rfl⟩
  rw [← hbdef] at hms
  have hN2 : 2 ≤ N := hNdef ▸ ZetaGateProductAFE.two_le_mollUpper hU50
  have hN1 : 1 ≤ N := by omega
  have hw : ∀ n ∈ Finset.Icc 1 N, |ZetaGateProductAFE.selbergRealUpper R U n| ≤ 1 :=
    fun n hn => Sieve.abs_twistedWeight_le _ _ (Finset.mem_Icc.mp hn).1
  have hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1 := by
    rw [hbdef]; exact ZetaGateProductAFE.norm_ofReal_coeff_le hw
  have hb1 : b 1 = 1 := by
    rw [hbdef]
    simp only [ZetaGateProductAFE.selbergRealUpper, Sieve.twistedWeight_one, Complex.ofReal_one]
  have hbreal : ∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n := fun n _ => by
    rw [hbdef]; exact Complex.conj_ofReal _
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩
  have hΨan : AnalyticOnNhd ℂ (edPoly b (Finset.Icc 1 N)) Set.univ := analyticOnNhd_edPoly b hs
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ,
      F = fun z => levinsonGEntire (((0 : ℝ) : ℝ) : ℂ) z * edPoly b (Finset.Icc 1 N) z :=
    ⟨_, rfl⟩
  have hFan : AnalyticOnNhd ℂ F Set.univ := by
    rw [hFdef]
    exact fun z hz => ((analyticOnNhd_levinsonGEntire _) z hz).mul (hΨan z hz)
  have hlamC : ‖(((0 : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hΨright : edPoly b (Finset.Icc 1 N) (((15 / 2 : ℝ) : ℂ)) ≠ 0 := by
    intro h0
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1mem hb1 hbn
      (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
    rw [h0] at h
    norm_num at h
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    refine ⟨((15 / 2 : ℝ) : ℂ), ?_⟩
    rw [hFdef]
    exact mul_ne_zero (levinsonGEntire_ne_zero_of_four_le hlamC (by simp; norm_num)) hΨright
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) (by linarith : T < T + 1) (by linarith : T + 1 < U - 1)
      (by linarith : U - 1 < U)
  obtain ⟨hT₁lo, hT₁hi⟩ := hT₁
  obtain ⟨hT₂lo, hT₂hi⟩ := hT₂
  have hT12 : T₁ < T₂ := by linarith
  have hT₁0 : 0 < T₁ := by linarith
  have hT₂0 : 0 < T₂ := by linarith
  have h20 : 20 ≤ T₁ := by linarith [show (20 : ℝ) ≤ 2 ^ 9 by norm_num]
  have hlogT₂ : Real.log T ≤ Real.log T₂ := Real.log_le_log hT0 (by linarith)
  have hlogT₂pos : 0 < Real.log T₂ := by
    have : 0 < Real.log T := Real.log_pos (by linarith [show (1 : ℝ) < 2 ^ 9 by norm_num])
    linarith
  -- the abscissa
  obtain ⟨d, hdR⟩ : ∃ d : ℝ, d = R / Real.log T₂ := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hdR]; positivity
  have hdlog : d * Real.log T₂ = R := by rw [hdR]; field_simp
  have hd8 : d ≤ 1 / 8 := by
    rw [hdR, div_le_iff₀ hlogT₂pos]
    linarith
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 1 / 2 - d := ⟨_, rfl⟩
  have hσ₀a : 1 / 4 ≤ σ₀ := by linarith
  have hσ₀b : σ₀ < 1 / 2 := by linarith
  have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log hT₂0 hT₂hi.le
  have hlogU1T₂ : Real.log (U - 1) ≤ Real.log T₂ := Real.log_le_log (by linarith) hT₂lo.le
  have hRd : R ≤ d * Real.log U := by
    have := mul_le_mul_of_nonneg_left hlogT₂U hd0.le
    linarith
  have hdU1 : d * Real.log (U - 1) ≤ R := by
    have := mul_le_mul_of_nonneg_left hlogU1T₂ hd0.le
    linarith
  have hU78 : U ^ ((49 : ℝ) / 50) ≤ T₁ :=
    (rpow_fortyNine_fiftieths_le_of_le_two_mul hT50 (by linarith) hU2T).trans hT₁lo.le
  have hT₂2 : T₂ ≤ 2 * T₁ := by linarith
  -- edges
  have hedge : ∀ Tz : ℝ, 20 ≤ Tz →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (Tz : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (Tz : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), edPoly b (Finset.Icc 1 N) ((x : ℂ) + (Tz : ℂ) * I) ≠ 0) := by
    intro Tz hTz hF
    have hmem : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2) := by
      intro x hx
      rw [uIcc_of_le (by norm_num)]
      exact ⟨le_trans hσ₀a hx.1, hx.2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · intro h0
      apply hF x (hmem x hx)
      have hne1 : ((x : ℂ) + (Tz : ℂ) * I) ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      rw [hFdef]
      show levinsonGEntire _ _ * _ = 0
      rw [levinsonGEntire_eq _ hne1]
      simp [levinsonG, h0]
    · intro h0
      apply hF x (hmem x hx)
      rw [hFdef]
      show _ * edPoly b (Finset.Icc 1 N) _ = 0
      rw [h0, mul_zero]
  obtain ⟨hG1, hP1⟩ := hedge T₁ h20 hF1
  obtain ⟨hG2, hP2⟩ := hedge T₂ (by linarith) hF2
  -- the mean square
  have hms' := hms d hd0 hd8 hRd hdU1 T₁ T₂ h20 hU78 hT12.le hT₂2 hT₂hi.le
  have hfun : (fun τ : ℝ => ‖riemannZeta (displacedLinePt d τ)
        * edPoly b (Finset.Icc 1 N) (displacedLinePt d τ)‖ ^ 2)
      = fun t : ℝ => ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I)
        * edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    funext t
    have hpt : displacedLinePt d t = (σ₀ : ℂ) + (t : ℂ) * I := by
      have := displacedLinePt_half_sub σ₀ t
      rw [hσ₀, show (1 / 2 : ℝ) - (1 / 2 - d) = d by ring] at this
      rw [this, hσ₀]
    rw [hpt]
  rw [hfun] at hms'
  have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ (5 : ℕ) := one_le_pow₀ (by exact_mod_cast hN1)
  obtain ⟨Z, hZ⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) h20 hT12
  have hc := hwide b N hN1 hb1 hbn hbreal ((N : ℝ) ^ (5 : ℕ)) hMb1
    (ZetaGateProductAFE.sum_norm_mul_rpow_four_le hbn) σ₀ T₁ T₂ _ hσ₀a hσ₀b h20 hT12
    hG1 hG2 hP1 hP2 hms' Z hZ
  have hZ' : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 - d) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
    rw [← hσ₀]; exact hZ
  have hbridge := window_count_add_tail_le_zetaWideSum hd0.le hT12.le Z hZ'
  rw [← hσ₀] at hbridge
  refine ⟨T₁, T₂, hT₁lo, hT₁hi, hT₂lo, hT₂hi, ?_⟩
  rw [← hdR]
  have hb2 := mul_le_mul_of_nonneg_left hbridge (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  unfold windowTail
  linarith only [hb2, hc]

/-- **The window analysis.**  The Littlewood bound on an admissible window `[T₁, T₂]`, the
Riemann–von Mangoldt lower bound and the size conditions give the two window bounds. -/
theorem window_bounds_of_littlewood_upper {R η c C K CR T H T₁ T₂ L₀ A : ℝ} {N : ℕ}
    (hR : 0 < R) (hη : 0 < η) (hc0 : 0 < c) (hlogc : 2 * R ≤ Real.log c) (hK : 0 < K)
    (hCR : 0 < CR) (hC : 0 < C) (hbb1 : 1 ≤ routeKRVMBase)
    (hL₀a : 8 * R ≤ L₀) (hL₀b : 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η ≤ L₀)
    (hA : A = 12 * Real.pi * R * CR + 2 * C + 14 * K * Real.log 2)
    (hT0 : 0 < T) (hlogTL : L₀ ≤ Real.log T)
    (hratio : 8 * T ^ (-((1 : ℝ) / 100)) ≤ η / 8)
    (hA' : A ≤ η / 32 * T ^ ((24 : ℝ) / 25))
    (hK' : 8 * K * Real.log T ≤ η / 32 * T ^ ((24 : ℝ) / 25))
    (hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25))
    (hH1 : T ^ ((24 : ℝ) / 25) ≤ H) (hH2 : H ≤ T)
    (hT₁lo : T < T₁) (hT₁hi : T₁ < T + 1) (hT₂lo : T + H - 1 < T₂) (hT₂hi : T₂ < T + H)
    (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ (T + H) ^ ((21 : ℝ) / 50))
    (hlit₀ : 2 * Real.pi * (R / Real.log T₂ * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
          + windowTail (R / Real.log T₂) T₁ T₂)
        ≤ (T₂ - T₁) / 2 * Real.log ((c + c * (η / 8))
            * (T₂ - T₁ + 2 * T₁ ^ ((19 : ℝ) / 20)) / (T₂ - T₁))
          + C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))))
    (hNlo : (T₂ - T₁) * (Real.log (T₁ / routeKRVMBase) + 1) / (2 * Real.pi)
          - CR * (Real.log T₁ + Real.log T₂)
        ≤ (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) :
    4 * Real.pi * windowTail (R / Real.log (T + H - 1)) (T + 1) (T + H - 1)
        ≤ (Real.log c - 2 * R + η) * H ∧
      4 * Real.pi * windowTail 0 (T + 1) (T + H - 1) ≤ (Real.log c - R + η) * H := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH4 : 4 ≤ H := le_trans hT2425 hH1
  have hT₁0 : 0 < T₁ := by linarith only [hT0, hT₁lo]
  have hT₂0 : 0 < T₂ := by linarith only [hT0, hT₁lo, hT₁hi, hT₂lo, hH4]
  have hT12 : T₁ < T₂ := by linarith only [hT₁hi, hT₂lo, hH4]
  have hT₂2 : T₂ ≤ 2 * T₁ := by linarith only [hT₂hi, hH2, hT₁lo]
  have hlogT₂L : L₀ ≤ Real.log T₂ :=
    le_trans hlogTL (Real.log_le_log hT0 (by linarith only [hT₁lo, hT12]))
  have hlogT₂pos : 0 < Real.log T₂ := by
    have : 0 < 8 * R := by positivity
    linarith only [this, hL₀a, hlogT₂L]
  obtain ⟨d, hdR⟩ : ∃ d : ℝ, d = R / Real.log T₂ := ⟨_, rfl⟩
  rw [← hdR] at hlit₀
  have hd0 : 0 < d := by rw [hdR]; positivity
  have hdlog : d * Real.log T₂ = R := by rw [hdR]; field_simp
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = T₂ - T₁ := ⟨_, rfl⟩
  rw [← hΔdef] at hlit₀ hNlo
  have hΔ0 : 0 < Δ := by rw [hΔdef]; linarith only [hT12]
  have hΔH : Δ ≤ H := by rw [hΔdef]; linarith only [hT₁lo, hT₂hi]
  have hΔlow : T ^ ((24 : ℝ) / 25) / 2 ≤ Δ := by
    rw [hΔdef]; linarith only [hT₁hi, hT₂lo, hH1, hT2425]
  -- the mean square per unit length
  have hτ0 : 0 ≤ 2 * T₁ ^ ((19 : ℝ) / 20) := by positivity
  have htaper := two_mul_rpow_taper_le hT0 hη hT₁0.le (by linarith only [hT₁hi, hT₂hi, hH2, hT12])
    hΔlow hratio
  have hlogMsq : Real.log ((c + c * (η / 8)) * (Δ + 2 * T₁ ^ ((19 : ℝ) / 20)) / Δ)
      ≤ Real.log c + η / 4 := by
    rw [show c + c * (η / 8) = c * (1 + η / 8) by ring]
    exact log_meanSquare_div_le hc0 hη hΔ0 hτ0 htaper
  -- Riemann–von Mangoldt on the window
  have hlogT₁ : Real.log T₂ - Real.log 2 ≤ Real.log T₁ := by
    have := Real.log_le_log hT₂0 hT₂2
    rw [Real.log_mul (by norm_num) hT₁0.ne'] at this
    linarith only [this]
  have hlogT₁T₂ : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log hT₁0 hT12.le
  have hdsmall : d * (Real.log 2 + Real.log routeKRVMBase) ≤ η / 16 := by
    rw [hdR, div_mul_eq_mul_div, div_le_iff₀ hlogT₂pos]
    have h1 := hL₀b.trans hlogT₂L
    rw [div_le_iff₀ hη] at h1
    linarith only [h1]
  have hlow := two_pi_mul_count_window_ge hd0.le hCR.le hΔ0.le hdlog hlogT₁ hlogT₁T₂
    (Real.log_div hT₁0.ne' (by linarith only [hbb1])) hdsmall hNlo
  -- the additive terms
  have hlogN : Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ 3 * (Real.log 2 + Real.log T₂) := by
    rw [Real.log_pow]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hTH0 : 0 < T + H := by linarith only [hT0, hH4]
    have h1 : Real.log (N : ℝ) ≤ Real.log ((T + H) ^ ((21 : ℝ) / 50)) :=
      Real.log_le_log hN0 hNle
    rw [Real.log_rpow hTH0] at h1
    have h2 : Real.log (T + H) ≤ Real.log 2 + Real.log T₂ := by
      have := Real.log_le_log hTH0 (show T + H ≤ 2 * T₂ by linarith only [hT₂lo, hT0, hH4])
      rwa [Real.log_mul (by norm_num) hT₂0.ne'] at this
    have h3 : 0 ≤ Real.log (T + H) := Real.log_nonneg (by linarith only [hT0, hH4])
    push_cast
    linarith only [h1, h2, h3, hlog2]
  have hlogT₂T : Real.log T₂ ≤ Real.log 2 + Real.log T := by
    have := Real.log_le_log hT₂0 (show T₂ ≤ 2 * T by linarith only [hT₂hi, hH2])
    rwa [Real.log_mul (by norm_num) hT0.ne'] at this
  have hlogMb0 : 0 ≤ Real.log ((N : ℝ) ^ (5 : ℕ)) :=
    Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hN1))
  have hL0 : 0 ≤ C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))) := by
    have : 0 ≤ Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)) := by
      linarith only [hlogT₂pos, hlogMb0]
    positivity
  have hE0 : 0 ≤ 4 * Real.pi * CR * R := by positivity
  have hadd : 2 * (C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ))))
      + 3 * (4 * Real.pi * CR * R) ≤ η / 8 * Δ := by
    have h3 : K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))
        ≤ 7 * K * Real.log 2 + 4 * K * Real.log T := by
      have : Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)) ≤ 7 * Real.log 2 + 4 * Real.log T := by
        linarith only [hlogN, hlogT₂T]
      have := mul_le_mul_of_nonneg_left this hK.le
      linarith only [this]
    have h4 := mul_le_mul_of_nonneg_left hΔlow (show (0 : ℝ) ≤ η / 8 by positivity)
    linarith only [h3, h4, hA, hA', hK']
  -- assembly
  have hlit : 2 * Real.pi * (d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
      + windowTail d T₁ T₂)
      ≤ Δ / 2 * (Real.log c + η / 4) + (C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))) := by
    have := mul_le_mul_of_nonneg_left hlogMsq (by positivity : (0 : ℝ) ≤ Δ / 2)
    linarith only [this, hlit₀]
  have hbridge' : 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (2 * Real.pi)
      + windowTail d T₁ T₂
      ≤ d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) + windowTail d T₁ T₂ := by
    rw [show 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (2 * Real.pi)
        = d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) by field_simp]
  have hW0 : windowTail 0 T₁ T₂ ≤ windowTail d T₁ T₂
      + 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (4 * Real.pi) := by
    have h := windowTail_zero_le hd0.le hT12.le
    rw [show 2 * Real.pi * d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) / (4 * Real.pi)
        = d / 2 * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁) by field_simp; ring]
    exact h
  have hlit' : 2 * Real.pi * (d * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)
      + windowTail d T₁ T₂)
      ≤ Δ / 2 * (Real.log c + η / 4) + (C + K * (Real.log T₂ + Real.log ((N : ℝ) ^ (5 : ℕ)))) :=
    hlit
  obtain ⟨htail, hmom⟩ := window_tail_moment_combine hΔ0.le hΔH hlogc hR.le hη hlit' hbridge'
    hlow hW0 hadd hL0 hE0
  -- monotonicity to the stated window
  have hlogU1pos : 0 < Real.log (T + H - 1) := Real.log_pos (by linarith only [hT0, hH4, hH2])
  have hdd : d ≤ R / Real.log (T + H - 1) := by
    rw [hdR]
    exact div_le_div_of_nonneg_left hR.le hlogU1pos
      (Real.log_le_log (by linarith only [hT0, hH4]) hT₂lo.le)
  have hwin : T + 1 ≤ T + H - 1 := by linarith only [hH4]
  have hmono1 : windowTail (R / Real.log (T + H - 1)) (T + 1) (T + H - 1) ≤ windowTail d T₁ T₂ :=
    (windowTail_anti hdd hwin).trans (windowTail_mono hT₁hi.le hT₂lo.le)
  have hmono0 : windowTail 0 (T + 1) (T + H - 1) ≤ windowTail 0 T₁ T₂ :=
    windowTail_mono hT₁hi.le hT₂lo.le
  constructor
  · have := mul_le_mul_of_nonneg_left hmono1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    linarith only [this, htail]
  · have := mul_le_mul_of_nonneg_left hmono0 (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
    linarith only [this, hmom]

/-- **The off-line tail law in every window `[T, T + H]`, `T^{24/25} ≤ H ≤ T`.**  With
`c_R = e^{2R}/(1 − e^{−21R/25})`, for every `η > 0` and all large `T`,
`4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½ − R/log(T+H−1))⁺ ≤ (log c_R − 2R + η) H` and
`4π Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½)⁺ ≤ (log c_R − R + η) H`. -/
theorem eventually_windowTail_le_selberg_upper {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      4 * Real.pi * windowTail (R / Real.log (T + H - 1)) (T + 1) (T + H - 1)
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - 2 * R + η) * H ∧
      4 * Real.pi * windowTail 0 (T + 1) (T + H - 1)
          ≤ (Real.log (ZetaGateProductAFE.selbergBlockConstUpper R) - R + η) * H := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = ZetaGateProductAFE.selbergBlockConstUpper R := ⟨_, rfl⟩
  rw [← hcdef]
  have hc1 : 1 ≤ c := hcdef ▸ ZetaGateProductAFE.one_le_selbergBlockConstUpper hR
  have hc0 : 0 < c := by linarith
  have hlogc : 2 * R ≤ Real.log c := hcdef ▸ two_mul_le_log_selbergBlockConstUpper hR
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_zetaWideMoment_le_of_mollified_meanSquare
  obtain ⟨CR, hCR, TR, hTR, hrvm⟩ := exists_xiPosZeroCount_window_bounds
  have hε : 0 < c * (η / 8) := by positivity
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp
    (ZetaGateProductAFE.eventually_window_meanSquare_selberg_upper hR hε)
  rw [← hcdef] at hU₀
  have hbb1 : 1 ≤ routeKRVMBase := by
    rw [routeKRVMBase]
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  have hlogbb : 0 ≤ Real.log routeKRVMBase := Real.log_nonneg hbb1
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ,
      L₀ = 8 * R + 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η := ⟨_, rfl⟩
  have hp1 : 0 ≤ 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hL₀a : 8 * R ≤ L₀ := by linarith
  have hL₀b : 16 * R * (Real.log 2 + Real.log routeKRVMBase) / η ≤ L₀ := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 12 * Real.pi * R * CR + 2 * C + 14 * K * Real.log 2 := ⟨_, rfl⟩
  have hη32 : 0 < η / 32 := by positivity
  filter_upwards [eventually_ge_atTop (max (max U₀ (TR + 1)) (max ((2 : ℝ) ^ 50) (Real.exp L₀))),
    eventually_const_mul_rpow_neg_le 8 ((1 : ℝ) / 100) (by norm_num) (show 0 < η / 8 by positivity),
    eventually_const_mul_rpow_neg_mul_log_pow_le A ((24 : ℝ) / 25) (by norm_num) 0 hη32,
    eventually_const_mul_rpow_neg_mul_log_pow_le (8 * K) ((24 : ℝ) / 25) (by norm_num) 1 hη32]
    with T hTbig hratio hadd1 hadd2
  intro H hH1 hH2
  have hTU₀ : U₀ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTTR : TR + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hT50 : (2 : ℝ) ^ 50 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTbig
  have hTL : Real.exp L₀ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTbig
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT50
  have hlogTL : L₀ ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos L₀) hTL
    rwa [Real.log_exp] at this
  have hT2425 : (4 : ℝ) ≤ T ^ ((24 : ℝ) / 25) :=
    four_le_rpow_twentyfour_div_twentyfive (le_trans (by norm_num) hT50)
  have hH4 : 4 ≤ H := le_trans hT2425 hH1
  have hpos2425 : 0 < T ^ ((24 : ℝ) / 25) := Real.rpow_pos_of_pos hT0 _
  have hA' : A ≤ η / 32 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd1
    rw [pow_zero, mul_one, Real.rpow_neg hT0.le, ← div_eq_mul_inv, div_le_iff₀ hpos2425] at h
    exact h
  have hK' : 8 * K * Real.log T ≤ η / 32 * T ^ ((24 : ℝ) / 25) := by
    have h := hadd2
    rw [pow_one, Real.rpow_neg hT0.le, ← mul_assoc, mul_comm (8 * K), mul_assoc,
      ← div_eq_inv_mul, div_le_iff₀ hpos2425] at h
    linarith only [h]
  have hms := hU₀ (T + H) (by linarith)
  obtain ⟨T₁, T₂, hT₁lo, hT₁hi, hT₂lo, hT₂hi, hlit₀⟩ :=
    exists_window_littlewood_upper hR hwide hT50 hH4
    hH2 (le_trans hL₀a hlogTL) hms
  obtain ⟨hNlo, -⟩ := hrvm T₁ T₂ (by linarith) (by linarith)
  have hN2 := ZetaGateProductAFE.two_le_mollUpper (show (2 : ℝ) ^ 50 ≤ T + H by linarith)
  exact window_bounds_of_littlewood_upper hR hη hc0 hlogc hK hCR hC hbb1 hL₀a hL₀b hA hT0
    hlogTL hratio hA' hK' hT2425 hH1 hH2 hT₁lo hT₁hi hT₂lo hT₂hi (by omega)
    (ZetaGateProductAFE.mollUpper_le (by linarith)) hlit₀ hNlo


/-! ## The window moment `1/8` -/

/-- `log c_{3/4} − 3/4 + 1/100 ≤ 4π · (1/8)`: `e^{−63/100} + e^{−4/5} ≤ 1` from the quartic
Taylor lower bounds of `e^{63/100}` and `e^{4/5}`. -/
theorem log_selbergBlockConstUpper_three_quarters_le :
    Real.log (ZetaGateProductAFE.selbergBlockConstUpper (3 / 4)) - 3 / 4 + 1 / 100
      ≤ 4 * Real.pi * (1 / 8) := by
  have hq : ∀ x : ℝ, 0 ≤ x → 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ Real.exp x := by
    intro x hx
    have h := Real.sum_le_exp_of_nonneg hx 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  have h63 := hq (63 / 100) (by norm_num)
  have h45 := hq (4 / 5) (by norm_num)
  have hy : Real.exp (-(63 / 100 : ℝ)) ≤ 1 / 1.8766 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h63 ⊢
    linarith
  have hz : Real.exp (-(4 / 5 : ℝ)) ≤ 1 / 2.2224 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h45 ⊢
    linarith
  have hc : ZetaGateProductAFE.selbergBlockConstUpper (3 / 4)
      = Real.exp (3 / 2) / (1 - Real.exp (-(63 / 100 : ℝ))) := by
    unfold ZetaGateProductAFE.selbergBlockConstUpper
    norm_num
  have h1y : Real.exp (-(4 / 5 : ℝ)) ≤ 1 - Real.exp (-(63 / 100 : ℝ)) := by
    norm_num at hy hz ⊢
    linarith
  have hpos : 0 < 1 - Real.exp (-(63 / 100 : ℝ)) := lt_of_lt_of_le (Real.exp_pos _) h1y
  rw [hc, Real.log_div (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  have hlog : -(4 / 5 : ℝ) ≤ Real.log (1 - Real.exp (-(63 / 100 : ℝ))) := by
    rw [Real.le_log_iff_exp_le hpos]
    exact h1y
  have hπ := Real.pi_gt_d2
  linarith

/-- **The window moment.**  For all large `T` and every `T^{24/25} ≤ H ≤ T`,
`Σ_{T+1 < Im ρ ≤ T+H−1} m_ρ (Re ρ − ½)⁺ ≤ H/8`. -/
theorem eventually_windowTail_zero_le_eighth :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      windowTail 0 (T + 1) (T + H - 1) ≤ 1 / 8 * H := by
  filter_upwards [eventually_windowTail_le_selberg_upper (R := 3 / 4) (η := 1 / 100)
    (by norm_num) (by norm_num), eventually_ge_atTop (0 : ℝ)] with T hT hT0
  intro H hH1 hH2
  have hH0 : 0 ≤ H := le_trans (Real.rpow_nonneg hT0 _) hH1
  have h := (hT H hH1 hH2).2
  have hc := log_selbergBlockConstUpper_three_quarters_le
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * windowTail 0 (T + 1) (T + H - 1) ≤ 4 * Real.pi * (1 / 8) * H :=
    h.trans (mul_le_mul_of_nonneg_right hc hH0)
  have h2 : 4 * Real.pi * (1 / 8) * H = 4 * Real.pi * (1 / 8 * H) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

/-! ## Signs on every window -/

/-- **Laguerre and vertical monotonicity on every window**, on measure `≥ (3/4) H − 3`. -/
theorem eventually_volume_laguerre_monotone_window_ge_upper :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (3 / 4 * H - 3) ≤
        volume {x ∈ Icc (T + 3 / 2) (T + H - 3 / 2) |
          MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((x : ℂ) + I * y)‖) (Ici 0) ∧
          0 ≤ (deriv (DeBruijn.riemannHeat 0) x ^ 2
            - DeBruijn.riemannHeat 0 x * deriv (deriv (DeBruijn.riemannHeat 0)) x).re} := by
  filter_upwards [eventually_windowTail_zero_le_eighth, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have h := DeBruijn.ofReal_window_le_volume_of_windowTail_le
    (fun x hx => DeBruijn.monotoneOn_laguerre_of_not_mem_xiShadow hx)
    (by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]) hH (hT H hH1 hH2)
  rwa [show (1 - 2 * (1 / 8 : ℝ)) * H - 3 = 3 / 4 * H - 3 by ring] at h

/-- **All-order slice positivity on every window**, on measure `≥ (3/4) H − 3`. -/
theorem eventually_volume_sliceCoeff_window_ge_upper :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (3 / 4 * H - 3) ≤
        volume {t ∈ Icc (T + 3 / 2) (T + H - 3 / 2) | ∀ n : ℕ, 0 ≤ xiSliceCoeff t n} := by
  filter_upwards [eventually_windowTail_zero_le_eighth, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have h := DeBruijn.ofReal_window_le_volume_of_windowTail_le
    (fun t ht => DeBruijn.xiSliceCoeff_nonneg_of_not_mem_xiShadow ht)
    (by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]) hH (hT H hH1 hH2)
  rwa [show (1 - 2 * (1 / 8 : ℝ)) * H - 3 = 3 / 4 * H - 3 by ring] at h

/-- **Speiser-clean heights on every window**, on measure `≥ (3/4) H − 3`. -/
theorem eventually_volume_speiserUnshadowed_window_ge_upper :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (3 / 4 * H - 3) ≤
        volume {t ∈ Icc (T + 3 / 2) (T + H - 3 / 2) | SpeiserUnshadowed t} := by
  filter_upwards [eventually_windowTail_zero_le_eighth, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have h := DeBruijn.ofReal_window_le_volume_of_windowTail_le
    (fun t ht => speiserUnshadowed_of_not_mem_xiShadow ht)
    (by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]) hH (hT H hH1 hH2)
  rwa [show (1 - 2 * (1 / 8 : ℝ)) * H - 3 = 3 / 4 * H - 3 by ring] at h

/-- **The Hadamard sign on every window**, on area `≥ (3/8) H − 3/2` of the window
`{½ < Re s < 1, T + 3/2 ≤ Im s ≤ T + H − 3/2}` of area `(H − 3)/2`. -/
theorem eventually_volume_hadamardSign_window_ge_upper :
    ∀ᶠ T in atTop, ∀ H : ℝ, T ^ ((24 : ℝ) / 25) ≤ H → H ≤ T →
      ENNReal.ofReal (3 / 8 * H - 3 / 2) ≤
        volume {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ T + 3 / 2 ≤ s.im ∧ s.im ≤ T + H - 3 / 2 ∧
          xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} := by
  filter_upwards [eventually_windowTail_zero_le_eighth, eventually_ge_atTop ((2 : ℝ) ^ 9)]
    with T hT hT9
  intro H hH1 hH2
  have hT0 : (0 : ℝ) ≤ T := by linarith [show (0 : ℝ) ≤ 2 ^ 9 by norm_num]
  have hH : 2 ≤ H := by linarith [four_le_rpow_twentyfour_div_twentyfive hT9]
  have hW := hT H hH1 hH2
  have hF := DeBruijn.volume_hadamardFail_window_le (a := T + 3 / 2) (b := T + H - 3 / 2)
    (by linarith)
  rw [show T + 3 / 2 - 1 / 2 = T + 1 by ring, show T + H - 3 / 2 + 1 / 2 = T + H - 1 by ring] at hF
  have hW0 : 0 ≤ windowTail 0 (T + 1) (T + H - 1) := by
    rw [windowTail_eq_sum (by linarith)]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  set Ω := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ T + 3 / 2 ≤ s.im ∧ s.im ≤ T + H - 3 / 2}
  set F := {s : ℂ | 1 / 2 < s.re ∧ T + 3 / 2 ≤ s.im ∧ s.im ≤ T + H - 3 / 2 ∧
    ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)}
  have hsub : Ω \ F ⊆ {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ T + 3 / 2 ≤ s.im ∧
      s.im ≤ T + H - 3 / 2 ∧ xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re} := by
    intro s ⟨⟨h1, h2, h3, h4⟩, hnF⟩
    have hg : xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re := by
      by_contra hc
      exact hnF ⟨h1, h3, h4, hc⟩
    exact ⟨h1, h2, h3, h4, hg.1, hg.2⟩
  calc ENNReal.ofReal (3 / 8 * H - 3 / 2)
      ≤ ENNReal.ofReal ((T + H - 3 / 2 - (T + 3 / 2)) / 2)
          - ENNReal.ofReal (windowTail 0 (T + 1) (T + H - 1)) := by
        rw [← ENNReal.ofReal_sub _ hW0]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ volume Ω - volume F := by
        rw [DeBruijn.volume_rightHalfStrip_window]
        exact tsub_le_tsub_left hF _
    _ ≤ volume (Ω \ F) := le_measure_sdiff
    _ ≤ _ := measure_mono hsub

end

end RHTower
