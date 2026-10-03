import GaloisForLFunctions.RHTower.ZetaGateUpperHighBlock
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergThreeTenths

/-!
# The off-line first moment with Selberg's twisted mollifier of length `U^{21/50}`

On the upper range `[U^{49/50}, U]` the high-block bound of `ZetaGateUpperHighBlock` accepts
mollifiers of length `N = ⌊U^{21/50}⌋`; the zeros below `U^{49/50}` are `o(U)` in number
(`ZetaGateUpperRange`).  With Selberg's twisted coefficients the main term per unit length tends to

  `c_R = e^{2R} / (1 − e^{−21R/25})`

(`tendsto_selbergBlockFactorUpper`), and at `R = 3/2` with `1 − e^{−63/50} ≥ e^{−17/50}`,

  `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½) ≤ (67/1000) V`   for all large `V`

(`eventually_offLineMoment_le_selberg_upper`), unconditionally.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The mollifier length `N = ⌊U^{21/50}⌋`. -/
def mollUpper (U : ℝ) : ℕ := ⌊U ^ ((21 : ℝ) / 50)⌋₊

theorem mollUpper_le {U : ℝ} (hU : 0 ≤ U) : (mollUpper U : ℝ) ≤ U ^ ((21 : ℝ) / 50) :=
  Nat.floor_le (by positivity)

theorem mollUpper_gt (U : ℝ) : U ^ ((21 : ℝ) / 50) - 1 < (mollUpper U : ℝ) := by
  have := Nat.lt_floor_add_one (U ^ ((21 : ℝ) / 50))
  unfold mollUpper
  linarith

theorem two_le_rpow_twentyOne_fiftieths {U : ℝ} (hU : (2 : ℝ) ^ 50 ≤ U) :
    (2 : ℝ) ≤ U ^ ((21 : ℝ) / 50) := by
  have e : ((2 : ℝ) ^ 50) ^ ((21 : ℝ) / 50) = 2 ^ 21 := by
    rw [← Real.rpow_natCast (2 : ℝ) 50, ← Real.rpow_mul (by norm_num),
      show ((50 : ℕ) : ℝ) * (21 / 50) = ((21 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  calc (2 : ℝ) ≤ 2 ^ 21 := by norm_num
    _ = ((2 : ℝ) ^ 50) ^ ((21 : ℝ) / 50) := e.symm
    _ ≤ U ^ ((21 : ℝ) / 50) := Real.rpow_le_rpow (by positivity) hU (by norm_num)

/-- `log N / log U → 21/50` for the mollifier length `N = ⌊U^{21/50}⌋`. -/
theorem tendsto_log_mollUpper_div_log :
    Tendsto (fun U : ℝ => Real.log (mollUpper U) / Real.log U) atTop (𝓝 (21 / 50)) := by
  have hlow : Tendsto (fun U : ℝ => 21 / 50 - Real.log 2 / Real.log U) atTop (𝓝 (21 / 50)) := by
    have := (tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop
    simpa using (tendsto_const_nhds (x := (21 / 50 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 50)] with U hU
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU)
    have h2 := two_le_rpow_twentyOne_fiftieths hU
    have hNhalf : U ^ ((21 : ℝ) / 50) / 2 ≤ mollUpper U := by
      linarith [mollUpper_gt U]
    have hlogN : 21 / 50 * Real.log U - Real.log 2 ≤ Real.log (mollUpper U) := by
      have h1 : Real.log (U ^ ((21 : ℝ) / 50) / 2) ≤ Real.log (mollUpper U) :=
        Real.log_le_log (by positivity) hNhalf
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hU0] at h1
      linarith
    have e : 21 / 50 - Real.log 2 / Real.log U
        = (21 / 50 * Real.log U - Real.log 2) / Real.log U := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hlogN hlogU.le
  · filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 50)] with U hU
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU)
    have hN1 : (1 : ℝ) ≤ mollUpper U := by
      linarith [mollUpper_gt U, two_le_rpow_twentyOne_fiftieths hU]
    have h : Real.log (mollUpper U) ≤ 21 / 50 * Real.log U := by
      have := Real.log_le_log (by linarith) (mollUpper_le hU0.le)
      rwa [Real.log_rpow hU0] at this
    rw [div_le_iff₀ hlogU]
    linarith

/-- Selberg's twisted coefficients of length `⌊U^{21/50}⌋`. -/
def selbergRealUpper (R U : ℝ) (n : ℕ) : ℝ :=
  Sieve.twistedWeight (selbergExponent R U) (mollUpper U) n

/-- **The gcd form of Selberg's twisted coefficients.**  For `d log(U − 1) ≤ R`,
`S₂ ≤ (2R/log(U − 1)) / (1 − e^{−2R log N/log(U − 1)})`. -/
theorem gcdSum₂_selbergRealUpper_le {R U d : ℝ} (hR : 0 < R) (hU : 3 ≤ U) (hd : 0 ≤ d)
    (hdU1 : d * Real.log (U - 1) ≤ R) (hN : 2 ≤ mollUpper U) :
    gcdSum₂ d (mollUpper U) (selbergRealUpper R U)
      ≤ (2 * R / Real.log (U - 1))
        / (1 - Real.exp (-(2 * R) * (Real.log (mollUpper U) / Real.log (U - 1)))) := by
  have hlog : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
  have hs := selbergExponent_gt_one hR (by linarith : 2 < U)
  have hss : 1 + 2 * d ≤ selbergExponent R U := by
    unfold selbergExponent
    have h1 : d ≤ R / Real.log (U - 1) := by rw [le_div_iff₀ hlog]; exact hdU1
    have h2 : 2 * d ≤ 2 * R / Real.log (U - 1) := by rw [mul_div_assoc]; linarith
    linarith
  have hN1 : 1 ≤ mollUpper U := by omega
  rw [gcdSum₂_eq_gcd_form]
  unfold selbergRealUpper
  refine (Sieve.gcdForm_twistedWeight_le hs.le (by linarith) hss hN1).trans ?_
  have hN0 : (1 : ℝ) < mollUpper U := by exact_mod_cast (by omega : 1 < mollUpper U)
  have hpow : (mollUpper U : ℝ) ^ (1 - selbergExponent R U)
      = Real.exp (-(2 * R) * (Real.log (mollUpper U) / Real.log (U - 1))) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    unfold selbergExponent
    ring
  have hlt : (mollUpper U : ℝ) ^ (1 - selbergExponent R U) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hN0 (by linarith)
  have hsum := sum_Icc_rpow_neg_ge hs hN1
  have hpos : 0 < (1 - (mollUpper U : ℝ) ^ (1 - selbergExponent R U))
      / (selbergExponent R U - 1) := div_pos (by linarith) (by linarith)
  calc 1 / ∑ m ∈ Finset.Icc 1 (mollUpper U), (m : ℝ) ^ (-selbergExponent R U)
      ≤ 1 / ((1 - (mollUpper U : ℝ) ^ (1 - selbergExponent R U))
          / (selbergExponent R U - 1)) := one_div_le_one_div_of_le hpos hsum
    _ = _ := by
        rw [one_div_div, ← hpow]
        congr 1
        unfold selbergExponent
        ring

/-! ## The main-term factor and its limit -/

/-- The main-term factor per unit window mass with Selberg's twisted coefficients. -/
def selbergBlockFactorUpper (R U : ℝ) : ℝ :=
  1 / (1 - Real.exp (-(2 * R) * (Real.log (mollUpper U) / Real.log (U - 1))))
    * (3 * R / Real.log (U - 1) + Real.log U / Real.log (U - 1))
    * Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
    * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))

/-- `c_R = e^{2R} / (1 − e^{−21R/25})`. -/
def selbergBlockConstUpper (R : ℝ) : ℝ := Real.exp (2 * R) / (1 - Real.exp (-(21 * R / 25)))

theorem selbergBlockConstUpper_pos {R : ℝ} (hR : 0 < R) :
    0 < selbergBlockConstUpper R := by
  unfold selbergBlockConstUpper
  have := exp_neg_lt_one (show 0 < 21 * R / 25 by positivity)
  exact div_pos (Real.exp_pos _) (by linarith)

/-- `log N / log(U − 1) → 21/50` for `N = ⌊U^{21/50}⌋`. -/
theorem tendsto_log_mollUpper_div_log_sub_one :
    Tendsto (fun U : ℝ => Real.log (mollUpper U) / Real.log (U - 1)) atTop (𝓝 (21 / 50)) := by
  have := tendsto_log_mollUpper_div_log.div tendsto_log_sub_one_div_log one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with U hU
  have h0 : Real.log U ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h1 : Real.log (U - 1) ≠ 0 := (Real.log_pos (by linarith)).ne'
  simp only [Pi.div_apply]
  field_simp

/-- **The Selberg main-term factor tends to `e^{2R}/(1 − e^{−21R/25})`.** -/
theorem tendsto_selbergBlockFactorUpper {R : ℝ} (hR : 0 < R) :
    Tendsto (selbergBlockFactorUpper R) atTop (𝓝 (selbergBlockConstUpper R)) := by
  have hT1 := tendsto_log_mollUpper_div_log_sub_one
  have hT4 := tendsto_log_div_log_sub_one
  have hlog1 : Tendsto (fun U : ℝ => Real.log (U - 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have hT0 : Tendsto (fun U : ℝ => 3 * R / Real.log (U - 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := 3 * R)).div_atTop hlog1
  have hden : 1 - Real.exp (-(2 * R) * (21 / 50)) ≠ 0 := by
    have := exp_neg_lt_one (show 0 < 21 * R / 25 by positivity)
    rw [show -(2 * R) * (21 / 50) = -(21 * R / 25) by ring]
    linarith
  have hA := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := -(2 * R))).mul hT1))
  have hA' := (tendsto_const_nhds (x := (1 : ℝ))).div hA hden
  have hB := hT0.add hT4
  have hE2 := (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := 2 * R)).mul hT4)
  have hT5 : Tendsto (fun U : ℝ => U ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hE3 := (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := (5 : ℝ))).mul hT5)
  have hprod := ((hA'.mul hB).mul hE2).mul hE3
  have hval : 1 / (1 - Real.exp (-(2 * R) * (21 / 50))) * (0 + 1) * Real.exp (2 * R * 1)
      * Real.exp (5 * 0) = selbergBlockConstUpper R := by
    unfold selbergBlockConstUpper
    rw [show -(2 * R) * (21 / 50) = -(21 * R / 25) by ring]
    simp only [mul_zero, Real.exp_zero, mul_one, zero_add]
    ring
  rw [hval] at hprod
  exact hprod

/-! ## The main term -/

/-- **The main term of a block with Selberg's twisted coefficients of length `⌊U^{21/50}⌋`.** -/
theorem selberg_mainTerm_le_upper {R U d a v η : ℝ} (hR : 0 < R) (hd : 0 < d)
    (hd8 : d ≤ 1 / 8) (hRd : R ≤ d * Real.log U) (hdU1 : d * Real.log (U - 1) ≤ R) (hU3 : 3 ≤ U)
    (hN2 : 2 ≤ mollUpper U) (hη : 0 < η) (h4 : 4 ≤ a - η) (hav : a ≤ v) (hvU : v ≤ U)
    (hηa : η ≤ a) (haη : a / 2 ≤ a - η) (haU : U ^ ((1 : ℝ) / 8) ≤ a) :
    gcdSum₂ d (mollUpper U) (selbergRealUpper R U)
      * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (v - a + 2 * η) * selbergBlockFactorUpper R U := by
  have hU0 : 0 < U := by linarith only [hU3]
  have hlogU0 : 0 < Real.log U := Real.log_pos (by linarith only [hU3])
  have hlogU1 : 0 < Real.log (U - 1) := Real.log_pos (by linarith only [hU3])
  have hd4 : d ≤ 1 / 4 := by linarith only [hd8]
  have hlen : 0 ≤ v - a + 2 * η := by linarith only [hav, hη]
  have hS := gcdSum₂_selbergRealUpper_le hR hU3 hd.le hdU1 hN2
  have hζ := norm_riemannZeta_one_add_le (by linarith only [hd] : 0 < 2 * d)
  have hχ := norm_integral_window_chiPairWeight_le_sharp hd hd4 hη h4 hav
  have h1d := inv_two_mul_le hd hR hRd
  have hF4 := chiWindowWeight_le hd.le hU0 hlogU0.le hlogU1 hdU1
    (y := v + η) (by linarith only [hav, h4, hη]) (by linarith only [hvU, hηa, hav])
  have hF5 := exp_chiWindowError_le hd8 haη h4 hU0 haU
  have hZ : ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ ≤ 3 / 2 + Real.log U / (2 * R) :=
    hζ.trans (by linarith only [h1d])
  have hX : ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖
      ≤ (v - a + 2 * η) * (Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
          * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))) := by
    refine hχ.trans (mul_le_mul_of_nonneg_left ?_ hlen)
    exact mul_le_mul hF4 hF5 (Real.exp_pos _).le (Real.exp_pos _).le
  have hZ0 : 0 ≤ 3 / 2 + Real.log U / (2 * R) := by positivity
  have hN1 : (1 : ℝ) < mollUpper U := by exact_mod_cast (by omega : 1 < mollUpper U)
  have hexp : Real.exp (-(2 * R) * (Real.log (mollUpper U) / Real.log (U - 1))) < 1 := by
    have h0 : 0 < Real.log (mollUpper U) / Real.log (U - 1) :=
      div_pos (Real.log_pos hN1) hlogU1
    rw [show -(2 * R) * (Real.log (mollUpper U) / Real.log (U - 1))
      = -(2 * R * (Real.log (mollUpper U) / Real.log (U - 1))) by ring]
    exact exp_neg_lt_one (by positivity)
  have hG0 : 0 ≤ (2 * R / Real.log (U - 1))
      / (1 - Real.exp (-(2 * R) * (Real.log (mollUpper U) / Real.log (U - 1)))) :=
    div_nonneg (by positivity) (by linarith)
  calc gcdSum₂ d (mollUpper U) (selbergRealUpper R U)
        * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ ((2 * R / Real.log (U - 1))
          / (1 - Real.exp (-(2 * R) * (Real.log (mollUpper U) / Real.log (U - 1)))))
        * ((3 / 2 + Real.log U / (2 * R))
          * ((v - a + 2 * η) * (Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
            * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))))) :=
        mul_le_mul hS (mul_le_mul hZ hX (norm_nonneg _) hZ0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hG0
    _ = (v - a + 2 * η) * selbergBlockFactorUpper R U := by
        unfold selbergBlockFactorUpper
        have hR0 : R ≠ 0 := hR.ne'
        have hl : Real.log (U - 1) ≠ 0 := hlogU1.ne'
        field_simp

/-! ## The dyadic law, the gate and the moment -/

theorem two_le_mollUpper {U : ℝ} (hU : (2 : ℝ) ^ 50 ≤ U) : 2 ≤ mollUpper U := by
  have h2 := two_le_rpow_twentyOne_fiftieths hU
  have h1 := mollUpper_gt U
  have : (1 : ℝ) < mollUpper U := by linarith
  have : 1 < mollUpper U := by exact_mod_cast this
  omega

/-- **The upper dyadic law with Selberg's twisted mollifier of length `⌊U^{21/50}⌋`**,
constant `e^{2R}/(1 − e^{−21R/25})`. -/
theorem zetaUpperDyadicMeanSquareLaw_selberg_upper {R : ℝ} (hR : 0 < R) :
    ZetaUpperDyadicMeanSquareLaw ((49 : ℝ) / 50) R (selbergBlockConstUpper R) := by
  have hN : ∀ᶠ U in atTop,
      1 ≤ mollUpper U ∧ (mollUpper U : ℝ) ≤ U ^ ((21 : ℝ) / 50) := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 50)] with U hU
    have h2 := two_le_mollUpper hU
    exact ⟨by omega, mollUpper_le (le_trans (by positivity) hU)⟩
  have hw : ∀ U, ∀ n ∈ Finset.Icc 1 (mollUpper U), |selbergRealUpper R U n| ≤ 1 :=
    fun U n hn => Sieve.abs_twistedWeight_le _ _ (Finset.mem_Icc.mp hn).1
  have hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (mollUpper U) (selbergRealUpper R U)
        * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * selbergBlockFactorUpper R U := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 50)] with U hU
    intro d hd hd8 hRd hdU1 a v η hη h4 hav hvU hηa haη haU
    have hU3 : (3 : ℝ) ≤ U := le_trans (by norm_num) hU
    exact selberg_mainTerm_le_upper hR hd hd8 hRd hdU1 hU3 (two_le_mollUpper hU) hη h4
      hav hvU hηa haη haU
  exact zetaUpperDyadicMeanSquareLaw_of_highBlock hR
    mollUpper (selbergRealUpper R) hN (fun U => Sieve.twistedWeight_one _ _) hw
    (exists_highBlock_bound_of_mainTerm_upper hR (tendsto_selbergBlockFactorUpper hR)
      mollUpper (selbergRealUpper R) (hN.mono fun _ h => h.2) hw hmain)

theorem one_le_selbergBlockConstUpper {R : ℝ} (hR : 0 < R) : 1 ≤ selbergBlockConstUpper R := by
  unfold selbergBlockConstUpper
  have h1 : 0 < Real.exp (-(21 * R / 25)) := Real.exp_pos _
  have h2 := exp_neg_lt_one (show 0 < 21 * R / 25 by positivity)
  rw [le_div_iff₀ (by linarith)]
  have h3 : 1 ≤ Real.exp (2 * R) := Real.one_le_exp (by positivity)
  linarith

/-- **The mean-square gate on the upper range with Selberg's twisted mollifier of length
`⌊U^{21/50}⌋`.** -/
theorem zetaMollifiedMeanSquareGateFrom_selberg_upper {R : ℝ} (hR : 0 < R) :
    ZetaMollifiedMeanSquareGateFrom ((49 : ℝ) / 50) R (selbergBlockConstUpper R) :=
  zetaMollifiedMeanSquareGateFrom_of_upperLaw (by norm_num) (by norm_num) hR
    (zetaUpperDyadicMeanSquareLaw_selberg_upper hR)

/-- `1 − e^{−63/50} ≥ e^{−17/50}`, from the degree-five Taylor lower bounds of `e^{63/50}` and
`e^{17/50}`. -/
theorem exp_neg_seventeen_fiftieths_le_one_sub_exp_neg_sixtyThree_fiftieths :
    Real.exp (-(17 / 50 : ℝ)) ≤ 1 - Real.exp (-(63 / 50 : ℝ)) := by
  have h1 : (43983508931 : ℝ) / 12500000000 ≤ Real.exp (63 / 50) := by
    have := Real.sum_le_exp_of_nonneg (x := (63 / 50 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have h2 : (52685450107 : ℝ) / 37500000000 ≤ Real.exp (17 / 50) := by
    have := Real.sum_le_exp_of_nonneg (x := (17 / 50 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have e1 : Real.exp (-(63 / 50 : ℝ)) ≤ 12500000000 / 43983508931 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith
  have e2 : Real.exp (-(17 / 50 : ℝ)) ≤ 37500000000 / 52685450107 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith
  linarith

/-- `log c_{3/2} − (5/3)(3/2) + 1/1000 ≤ 4π · 67/1000`. -/
theorem log_selbergBlockConstUpper_three_halves_le :
    Real.log (selbergBlockConstUpper (3 / 2)) - 5 / 3 * (3 / 2) + 1 / 1000
      ≤ 4 * Real.pi * (67 / 1000) := by
  set y : ℝ := Real.exp (-(63 / 50 : ℝ)) with hy
  have hden := exp_neg_seventeen_fiftieths_le_one_sub_exp_neg_sixtyThree_fiftieths
  rw [← hy] at hden
  have h1y : 0 < 1 - y := lt_of_lt_of_le (Real.exp_pos _) hden
  have hc : selbergBlockConstUpper (3 / 2) = Real.exp 3 / (1 - y) := by
    unfold selbergBlockConstUpper
    rw [hy]
    norm_num
  rw [hc, Real.log_div (Real.exp_pos _).ne' h1y.ne', Real.log_exp]
  have hlog : -(17 / 50) ≤ Real.log (1 - y) := by
    have := Real.log_le_log (Real.exp_pos _) hden
    rwa [Real.log_exp] at this
  have hπ := Real.pi_gt_d4
  norm_num at hπ ⊢
  linarith

/-- **The off-line first moment is at most `67/1000` of the height, unconditionally.** -/
theorem eventually_offLineMoment_le_selberg_upper :
    ∀ᶠ V in atTop, offLineMoment V ≤ 67 / 1000 * V := by
  have h := eventually_offLineMoment_le_of_zetaGateFrom_twoThirds (α := (49 : ℝ) / 50)
    (R := 3 / 2) (η := 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (one_le_selbergBlockConstUpper (by norm_num)) (by norm_num)
    (zetaMollifiedMeanSquareGateFrom_selberg_upper (by norm_num))
  filter_upwards [h, eventually_ge_atTop 0] with V hV hV0
  have hc := log_selbergBlockConstUpper_three_halves_le
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * offLineMoment V ≤ 4 * Real.pi * (67 / 1000) * V :=
    hV.trans (mul_le_mul_of_nonneg_right hc hV0)
  have h2 : 4 * Real.pi * (67 / 1000) * V = 4 * Real.pi * (67 / 1000 * V) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

end RHTower.ZetaGateProductAFE

end
