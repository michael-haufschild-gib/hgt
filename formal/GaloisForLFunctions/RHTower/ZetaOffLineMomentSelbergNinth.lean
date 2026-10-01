import GaloisForLFunctions.RHTower.ZetaGateDeepHighBlock
import GaloisForLFunctions.RHTower.ZetaOffLineMomentSelbergWeights

/-!
# The off-line first moment with Selberg's twisted mollifier of length `U^{1/9}`

The deep high-block bound (`exists_highBlock_bound_of_mainTerm_deep`) and the deep dyadic law
(`zetaDyadicMeanSquareLaw_of_highBlock_deep`) accept mollifiers of length `N = ⌊U^{1/9}⌋`.  With
Selberg's twisted coefficients `γ_n n^{1−s}`, `s = 1 + 2R/log(U − 1)`, the main term per unit length
tends to

  `c_R = e^{2R} / (1 − e^{−2R/9})`

(`tendsto_selbergBlockFactorNinth`), which gives the dyadic law, the mollified mean-square gate
and, at `R = 9/4` with `1 − e^{−1/2} ≥ e^{−1}`,

  `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½) ≤ (7/50) V`   for all large `V`

(`eventually_offLineMoment_le_selberg_ninth`), unconditionally.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The mollifier length `N = ⌊U^{1/9}⌋`. -/
def mollNinth (U : ℝ) : ℕ := ⌊U ^ ((1 : ℝ) / 9)⌋₊

theorem mollNinth_le {U : ℝ} (hU : 0 ≤ U) : (mollNinth U : ℝ) ≤ U ^ ((1 : ℝ) / 9) :=
  Nat.floor_le (by positivity)

theorem mollNinth_gt (U : ℝ) : U ^ ((1 : ℝ) / 9) - 1 < (mollNinth U : ℝ) := by
  have := Nat.lt_floor_add_one (U ^ ((1 : ℝ) / 9))
  unfold mollNinth
  linarith

theorem two_le_rpow_one_div_nine {U : ℝ} (hU : (2 : ℝ) ^ 9 ≤ U) :
    (2 : ℝ) ≤ U ^ ((1 : ℝ) / 9) := by
  have e : ((2 : ℝ) ^ 9) ^ ((1 : ℝ) / 9) = 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) 9, ← Real.rpow_mul (by norm_num),
      show ((9 : ℕ) : ℝ) * (1 / 9) = (1 : ℝ) by norm_num, Real.rpow_one]
  rw [← e]
  exact Real.rpow_le_rpow (by positivity) hU (by norm_num)

/-- `log N / log U → 1/9` for the mollifier length `N = ⌊U^{1/9}⌋`. -/
theorem tendsto_log_mollNinth_div_log :
    Tendsto (fun U : ℝ => Real.log (mollNinth U) / Real.log U) atTop (𝓝 (1 / 9)) := by
  have hlow : Tendsto (fun U : ℝ => 1 / 9 - Real.log 2 / Real.log U) atTop (𝓝 (1 / 9)) := by
    have := (tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop
    simpa using (tendsto_const_nhds (x := (1 / 9 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 9)] with U hU
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU)
    have h2 := two_le_rpow_one_div_nine hU
    have hNhalf : U ^ ((1 : ℝ) / 9) / 2 ≤ mollNinth U := by linarith [mollNinth_gt U]
    have hlogN : Real.log U / 9 - Real.log 2 ≤ Real.log (mollNinth U) := by
      have h1 : Real.log (U ^ ((1 : ℝ) / 9) / 2) ≤ Real.log (mollNinth U) :=
        Real.log_le_log (by positivity) hNhalf
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hU0] at h1
      linarith
    have e : 1 / 9 - Real.log 2 / Real.log U = (Real.log U / 9 - Real.log 2) / Real.log U := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hlogN hlogU.le
  · filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 9)] with U hU
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU)
    have hN1 : (1 : ℝ) ≤ mollNinth U := by
      linarith [mollNinth_gt U, two_le_rpow_one_div_nine hU]
    have h : Real.log (mollNinth U) ≤ Real.log U / 9 := by
      have := Real.log_le_log (by linarith) (mollNinth_le hU0.le)
      rwa [Real.log_rpow hU0, one_div_mul_eq_div] at this
    rw [div_le_iff₀ hlogU]
    linarith


/-- Selberg's twisted coefficients of length `⌊U^{1/9}⌋`. -/
def selbergRealNinth (R U : ℝ) (n : ℕ) : ℝ :=
  Sieve.twistedWeight (selbergExponent R U) (mollNinth U) n

/-- **The gcd form of Selberg's twisted coefficients.**  For `d log(U − 1) ≤ R`,
`S₂ ≤ (2R/log(U − 1)) / (1 − e^{−2R log N/log(U − 1)})`. -/
theorem gcdSum₂_selbergRealNinth_le {R U d : ℝ} (hR : 0 < R) (hU : 3 ≤ U) (hd : 0 ≤ d)
    (hdU1 : d * Real.log (U - 1) ≤ R) (hN : 2 ≤ mollNinth U) :
    gcdSum₂ d (mollNinth U) (selbergRealNinth R U)
      ≤ (2 * R / Real.log (U - 1))
        / (1 - Real.exp (-(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1)))) := by
  have hlog : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
  have hs := selbergExponent_gt_one hR (by linarith : 2 < U)
  have hss : 1 + 2 * d ≤ selbergExponent R U := by
    unfold selbergExponent
    have h1 : d ≤ R / Real.log (U - 1) := by rw [le_div_iff₀ hlog]; exact hdU1
    have h2 : 2 * d ≤ 2 * R / Real.log (U - 1) := by rw [mul_div_assoc]; linarith
    linarith
  have hN1 : 1 ≤ mollNinth U := by omega
  rw [gcdSum₂_eq_gcd_form]
  unfold selbergRealNinth
  refine (Sieve.gcdForm_twistedWeight_le hs.le (by linarith) hss hN1).trans ?_
  have hN0 : (1 : ℝ) < mollNinth U := by exact_mod_cast (by omega : 1 < mollNinth U)
  have hpow : (mollNinth U : ℝ) ^ (1 - selbergExponent R U)
      = Real.exp (-(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1))) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    unfold selbergExponent
    ring
  have hlt : (mollNinth U : ℝ) ^ (1 - selbergExponent R U) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hN0 (by linarith)
  have hsum := sum_Icc_rpow_neg_ge hs hN1
  have hpos : 0 < (1 - (mollNinth U : ℝ) ^ (1 - selbergExponent R U))
      / (selbergExponent R U - 1) := div_pos (by linarith) (by linarith)
  calc 1 / ∑ m ∈ Finset.Icc 1 (mollNinth U), (m : ℝ) ^ (-selbergExponent R U)
      ≤ 1 / ((1 - (mollNinth U : ℝ) ^ (1 - selbergExponent R U))
          / (selbergExponent R U - 1)) := one_div_le_one_div_of_le hpos hsum
    _ = _ := by
        rw [one_div_div, ← hpow]
        congr 1
        unfold selbergExponent
        ring

/-! ## The main-term factor and its limit -/

/-- The main-term factor per unit window mass with Selberg's twisted coefficients. -/
def selbergBlockFactorNinth (R U : ℝ) : ℝ :=
  1 / (1 - Real.exp (-(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1))))
    * (3 * R / Real.log (U - 1) + Real.log U / Real.log (U - 1))
    * Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
    * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))

/-- `c_R = e^{2R} / (1 − e^{−2R/9})`. -/
def selbergBlockConstNinth (R : ℝ) : ℝ := Real.exp (2 * R) / (1 - Real.exp (-(2 * R / 9)))

theorem selbergBlockConstNinth_pos {R : ℝ} (hR : 0 < R) : 0 < selbergBlockConstNinth R := by
  unfold selbergBlockConstNinth
  have := exp_neg_lt_one (show 0 < 2 * R / 9 by positivity)
  exact div_pos (Real.exp_pos _) (by linarith)

/-- `log N / log(U − 1) → 1/15` for `N = ⌊U^{1/15}⌋`. -/
theorem tendsto_log_mollNinth_div_log_sub_one :
    Tendsto (fun U : ℝ => Real.log (mollNinth U) / Real.log (U - 1)) atTop (𝓝 (1 / 9)) := by
  have := tendsto_log_mollNinth_div_log.div tendsto_log_sub_one_div_log one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with U hU
  have h0 : Real.log U ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h1 : Real.log (U - 1) ≠ 0 := (Real.log_pos (by linarith)).ne'
  simp only [Pi.div_apply]
  field_simp

/-- **The Selberg main-term factor tends to `e^{2R}/(1 − e^{−2R/9})`.** -/
theorem tendsto_selbergBlockFactorNinth {R : ℝ} (hR : 0 < R) :
    Tendsto (selbergBlockFactorNinth R) atTop (𝓝 (selbergBlockConstNinth R)) := by
  have hT1 := tendsto_log_mollNinth_div_log_sub_one
  have hT4 := tendsto_log_div_log_sub_one
  have hlog1 : Tendsto (fun U : ℝ => Real.log (U - 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have hT0 : Tendsto (fun U : ℝ => 3 * R / Real.log (U - 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := 3 * R)).div_atTop hlog1
  have hden : 1 - Real.exp (-(2 * R) * (1 / 9)) ≠ 0 := by
    have := exp_neg_lt_one (show 0 < 2 * R / 9 by positivity)
    rw [show -(2 * R) * (1 / 9) = -(2 * R / 9) by ring]
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
  have hval : 1 / (1 - Real.exp (-(2 * R) * (1 / 9))) * (0 + 1) * Real.exp (2 * R * 1)
      * Real.exp (5 * 0) = selbergBlockConstNinth R := by
    unfold selbergBlockConstNinth
    rw [show -(2 * R) * (1 / 9) = -(2 * R / 9) by ring]
    simp only [mul_zero, Real.exp_zero, mul_one, zero_add]
    ring
  rw [hval] at hprod
  exact hprod

/-! ## The main term -/

/-- **The main term of a block with Selberg's twisted coefficients.** -/
theorem selberg_mainTerm_le_ninth {R U d a v η : ℝ} (hR : 0 < R) (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hRd : R ≤ d * Real.log U) (hdU1 : d * Real.log (U - 1) ≤ R) (hU3 : 3 ≤ U)
    (hN2 : 2 ≤ mollNinth U) (hη : 0 < η) (h4 : 4 ≤ a - η) (hav : a ≤ v) (hvU : v ≤ U)
    (hηa : η ≤ a) (haη : a / 2 ≤ a - η) (haU : U ^ ((1 : ℝ) / 8) ≤ a) :
    gcdSum₂ d (mollNinth U) (selbergRealNinth R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (v - a + 2 * η) * selbergBlockFactorNinth R U := by
  have hU0 : 0 < U := by linarith only [hU3]
  have hlogU0 : 0 < Real.log U := Real.log_pos (by linarith only [hU3])
  have hlogU1 : 0 < Real.log (U - 1) := Real.log_pos (by linarith only [hU3])
  have hd4 : d ≤ 1 / 4 := by linarith only [hd8]
  have hlen : 0 ≤ v - a + 2 * η := by linarith only [hav, hη]
  have hS := gcdSum₂_selbergRealNinth_le hR hU3 hd.le hdU1 hN2
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
  have hN1 : (1 : ℝ) < mollNinth U := by exact_mod_cast (by omega : 1 < mollNinth U)
  have hexp : Real.exp (-(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1))) < 1 := by
    have h0 : 0 < Real.log (mollNinth U) / Real.log (U - 1) :=
      div_pos (Real.log_pos hN1) hlogU1
    rw [show -(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1))
      = -(2 * R * (Real.log (mollNinth U) / Real.log (U - 1))) by ring]
    exact exp_neg_lt_one (by positivity)
  have hE : 1 - Real.exp (-(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1))) ≠ 0 := by
    linarith
  have hG0 : 0 ≤ (2 * R / Real.log (U - 1))
      / (1 - Real.exp (-(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1)))) :=
    div_nonneg (by positivity) (by linarith)
  calc gcdSum₂ d (mollNinth U) (selbergRealNinth R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ ((2 * R / Real.log (U - 1))
          / (1 - Real.exp (-(2 * R) * (Real.log (mollNinth U) / Real.log (U - 1)))))
        * ((3 / 2 + Real.log U / (2 * R))
          * ((v - a + 2 * η) * (Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
            * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))))) :=
        mul_le_mul hS (mul_le_mul hZ hX (norm_nonneg _) hZ0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hG0
    _ = (v - a + 2 * η) * selbergBlockFactorNinth R U := by
        unfold selbergBlockFactorNinth
        have hR0 : R ≠ 0 := hR.ne'
        have hl : Real.log (U - 1) ≠ 0 := hlogU1.ne'
        field_simp

/-! ## The dyadic law, the gate and the moment -/

theorem two_le_mollNinth {U : ℝ} (hU : (2 : ℝ) ^ 9 ≤ U) : 2 ≤ mollNinth U := by
  have h2 := two_le_rpow_one_div_nine hU
  have h1 := mollNinth_gt U
  have : (1 : ℝ) < mollNinth U := by linarith
  have : 1 < mollNinth U := by exact_mod_cast this
  omega

/-- **The dyadic mean-square law with Selberg's twisted mollifier**, constant
`e^{2R}/(1 − e^{−2R/9})`. -/
theorem zetaDyadicMeanSquareLaw_selberg_ninth {R : ℝ} (hR : 0 < R) :
    ZetaDyadicMeanSquareLaw R (selbergBlockConstNinth R) := by
  have hN : ∀ᶠ U in atTop, 1 ≤ mollNinth U ∧ (mollNinth U : ℝ) ≤ U ^ ((1 : ℝ) / 9) := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 9)] with U hU
    have h2 := two_le_mollNinth hU
    exact ⟨by omega, mollNinth_le (le_trans (by positivity) hU)⟩
  have hw : ∀ U, ∀ n ∈ Finset.Icc 1 (mollNinth U), |selbergRealNinth R U n| ≤ 1 := fun U n hn =>
    Sieve.abs_twistedWeight_le _ _ (Finset.mem_Icc.mp hn).1
  have hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (mollNinth U) (selbergRealNinth R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * selbergBlockFactorNinth R U := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 9)] with U hU
    intro d hd hd8 hRd hdU1 a v η hη h4 hav hvU hηa haη haU
    have hU3 : (3 : ℝ) ≤ U := le_trans (by norm_num) hU
    exact selberg_mainTerm_le_ninth hR hd hd8 hRd hdU1 hU3 (two_le_mollNinth hU) hη h4 hav hvU hηa
      haη haU
  exact zetaDyadicMeanSquareLaw_of_highBlock_deep hR (selbergBlockConstNinth_pos hR).le mollNinth
    (selbergRealNinth R) hN (fun U => Sieve.twistedWeight_one _ _) hw
    (exists_highBlock_bound_of_mainTerm_deep hR (tendsto_selbergBlockFactorNinth hR) mollNinth
      (selbergRealNinth R)
      (hN.mono fun _ h => h.2) hw hmain)

/-- **The mollified mean-square gate with Selberg's twisted mollifier.** -/
theorem zetaMollifiedMeanSquareGate_selberg_ninth {R : ℝ} (hR : 0 < R) :
    ZetaMollifiedMeanSquareGate R (max (selbergBlockConstNinth R) 1) :=
  zetaMollifiedMeanSquareGate_of_dyadicLaw hR
    (zetaDyadicMeanSquareLaw_mono (le_max_left _ _) (zetaDyadicMeanSquareLaw_selberg_ninth hR))


/-- `log c_{9/4} − 15/4 + 1/200 ≤ 4π · 7/50`, from `1 − e^{−1/2} ≥ e^{−1}`. -/
theorem log_selbergBlockConstNinth_nine_quarters_le :
    Real.log (max (selbergBlockConstNinth (9 / 4)) 1) - 5 / 3 * (9 / 4) + 1 / 200
      ≤ 4 * Real.pi * (7 / 50) := by
  set y : ℝ := Real.exp (-(1 / 2 : ℝ)) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy8 : y ≤ 8 / 13 := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [hy, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h ⊢
    linarith
  have hyy : y ^ 2 = Real.exp (-1) := by
    rw [hy, ← Real.exp_nat_mul]
    norm_num
  have hden : Real.exp (-1) ≤ 1 - y := by
    rw [← hyy]
    nlinarith
  have hc : selbergBlockConstNinth (9 / 4) = Real.exp (9 / 2) / (1 - y) := by
    unfold selbergBlockConstNinth
    rw [hy]
    norm_num
  have h1y : 0 < 1 - y := by linarith
  have hc1 : 1 ≤ selbergBlockConstNinth (9 / 4) := by
    rw [hc, le_div_iff₀ h1y]
    have : 1 ≤ Real.exp (9 / 2) := Real.one_le_exp (by norm_num)
    linarith
  rw [max_eq_left hc1, hc, Real.log_div (Real.exp_pos _).ne' h1y.ne', Real.log_exp]
  have hlog : -1 ≤ Real.log (1 - y) := by
    have := Real.log_le_log (Real.exp_pos _) hden
    rwa [Real.log_exp] at this
  have hπ := Real.pi_gt_d2
  norm_num at hπ ⊢
  linarith

/-- **The off-line first moment is at most `7/50` of the height, unconditionally.** -/
theorem eventually_offLineMoment_le_selberg_ninth :
    ∀ᶠ V in atTop, offLineMoment V ≤ 7 / 50 * V := by
  have h := eventually_offLineMoment_le_of_zetaGate_twoThirds (R := 9 / 4) (η := 1 / 200)
    (by norm_num) (le_max_right _ _) (by norm_num)
    (zetaMollifiedMeanSquareGate_selberg_ninth (by norm_num))
  filter_upwards [h, eventually_ge_atTop 0] with V hV hV0
  have hc := log_selbergBlockConstNinth_nine_quarters_le
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * offLineMoment V ≤ 4 * Real.pi * (7 / 50) * V :=
    hV.trans (mul_le_mul_of_nonneg_right hc hV0)
  have h2 : 4 * Real.pi * (7 / 50) * V = 4 * Real.pi * (7 / 50 * V) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

end RHTower.ZetaGateProductAFE

end
