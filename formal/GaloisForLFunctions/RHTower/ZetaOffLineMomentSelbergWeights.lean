import GaloisForLFunctions.RHTower.ZetaGateProductAFEWeightedHighBlock
import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergMollifier
import GaloisForLFunctions.RHTower.FreeMonoidEulerBounds

/-!
# The off-line first moment with Selberg's twisted mollifier

On the Levinson line `Re s = ½ − d`, `R ≤ d log U`, `d log(U − 1) ≤ R`, take the mollifier of
length `N = ⌊U^{1/15}⌋` with coefficients `γ_n n^{1−s}`, where `γ` are Selberg's `Λ²` weights for
the density `n^{−s}` and `s = 1 + 2R/log(U − 1) ≥ 1 + 2d`.  The diagonal gcd form of the block main
term is at most `1/Σ_{m ≤ N} m^{−s} ≤ (s − 1)/(1 − N^{1−s})` (`gcdSum₂_selbergReal_le`), so the
main term per unit window mass tends to

  `c_R = e^{2R} / (1 − e^{−2R/15})`

(`tendsto_selbergBlockFactor`).  The weighted high-block bound gives the dyadic mean-square law and
the mollified mean-square gate with this constant, and the two-thirds ceiling at `R = 5/2` gives

  `Σ_{0 < Im ρ ≤ V} m(ρ) (Re ρ − ½) ≤ (17/100) V`   for all large `V`

(`eventually_offLineMoment_le_selberg`), unconditionally.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The Selberg exponent `s = 1 + 2R/log(U − 1)`. -/
def selbergExponent (R U : ℝ) : ℝ := 1 + 2 * R / Real.log (U - 1)

/-- Selberg's twisted coefficients `γ_n n^{1−s}`, `s = 1 + 2R/log(U − 1)`, of length
`⌊U^{1/15}⌋`. -/
def selbergReal (R U : ℝ) (n : ℕ) : ℝ :=
  Sieve.twistedWeight (selbergExponent R U) (mollLong U) n

theorem selbergExponent_gt_one {R U : ℝ} (hR : 0 < R) (hU : 2 < U) :
    1 < selbergExponent R U := by
  unfold selbergExponent
  have : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
  have : 0 < 2 * R / Real.log (U - 1) := by positivity
  linarith

/-- `Σ_{m ≤ N} m^{−s} ≥ (1 − N^{1−s})/(s − 1)` for `s > 1`. -/
theorem sum_Icc_rpow_neg_ge {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    (1 - (N : ℝ) ^ (1 - s)) / (s - 1) ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-s) := by
  have h := FreeMonoidEuler.sum_rpow_neg_ge N hs
  have e : ∑ i ∈ Finset.range N, ((1 : ℝ) + i) ^ (-s)
      = ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-s) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    push_cast
    rfl
  rw [e] at h
  refine le_trans ?_ h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ((N : ℝ) + 1) ^ (1 - s) ≤ (N : ℝ) ^ (1 - s) :=
    Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- **The gcd form of Selberg's twisted coefficients.**  For `d log(U − 1) ≤ R`,
`S₂ ≤ (2R/log(U − 1)) / (1 − e^{−2R log N/log(U − 1)})`. -/
theorem gcdSum₂_selbergReal_le {R U d : ℝ} (hR : 0 < R) (hU : 3 ≤ U) (hd : 0 ≤ d)
    (hdU1 : d * Real.log (U - 1) ≤ R) (hN : 2 ≤ mollLong U) :
    gcdSum₂ d (mollLong U) (selbergReal R U)
      ≤ (2 * R / Real.log (U - 1))
        / (1 - Real.exp (-(2 * R) * (Real.log (mollLong U) / Real.log (U - 1)))) := by
  have hlog : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
  have hs := selbergExponent_gt_one hR (by linarith : 2 < U)
  have hss : 1 + 2 * d ≤ selbergExponent R U := by
    unfold selbergExponent
    have h1 : d ≤ R / Real.log (U - 1) := by rw [le_div_iff₀ hlog]; exact hdU1
    have h2 : 2 * d ≤ 2 * R / Real.log (U - 1) := by rw [mul_div_assoc]; linarith
    linarith
  have hN1 : 1 ≤ mollLong U := by omega
  rw [gcdSum₂_eq_gcd_form]
  unfold selbergReal
  refine (Sieve.gcdForm_twistedWeight_le hs.le (by linarith) hss hN1).trans ?_
  have hN0 : (1 : ℝ) < mollLong U := by exact_mod_cast (by omega : 1 < mollLong U)
  have hpow : (mollLong U : ℝ) ^ (1 - selbergExponent R U)
      = Real.exp (-(2 * R) * (Real.log (mollLong U) / Real.log (U - 1))) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    unfold selbergExponent
    ring
  have hlt : (mollLong U : ℝ) ^ (1 - selbergExponent R U) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hN0 (by linarith)
  have hsum := sum_Icc_rpow_neg_ge hs hN1
  have hpos : 0 < (1 - (mollLong U : ℝ) ^ (1 - selbergExponent R U))
      / (selbergExponent R U - 1) := div_pos (by linarith) (by linarith)
  calc 1 / ∑ m ∈ Finset.Icc 1 (mollLong U), (m : ℝ) ^ (-selbergExponent R U)
      ≤ 1 / ((1 - (mollLong U : ℝ) ^ (1 - selbergExponent R U))
          / (selbergExponent R U - 1)) := one_div_le_one_div_of_le hpos hsum
    _ = _ := by
        rw [one_div_div, ← hpow]
        congr 1
        unfold selbergExponent
        ring

/-! ## The main-term factor and its limit -/

/-- The main-term factor per unit window mass with Selberg's twisted coefficients. -/
def selbergBlockFactor (R U : ℝ) : ℝ :=
  1 / (1 - Real.exp (-(2 * R) * (Real.log (mollLong U) / Real.log (U - 1))))
    * (3 * R / Real.log (U - 1) + Real.log U / Real.log (U - 1))
    * Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
    * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))

/-- `c_R = e^{2R} / (1 − e^{−2R/15})`. -/
def selbergBlockConst (R : ℝ) : ℝ := Real.exp (2 * R) / (1 - Real.exp (-(2 * R / 15)))

theorem exp_neg_lt_one {x : ℝ} (hx : 0 < x) : Real.exp (-x) < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

theorem selbergBlockConst_pos {R : ℝ} (hR : 0 < R) : 0 < selbergBlockConst R := by
  unfold selbergBlockConst
  have := exp_neg_lt_one (show 0 < 2 * R / 15 by positivity)
  exact div_pos (Real.exp_pos _) (by linarith)

/-- `log N / log(U − 1) → 1/15` for `N = ⌊U^{1/15}⌋`. -/
theorem tendsto_log_mollLong_div_log_sub_one :
    Tendsto (fun U : ℝ => Real.log (mollLong U) / Real.log (U - 1)) atTop (𝓝 (1 / 15)) := by
  have := tendsto_log_mollLong_div_log.div tendsto_log_sub_one_div_log one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with U hU
  have h0 : Real.log U ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h1 : Real.log (U - 1) ≠ 0 := (Real.log_pos (by linarith)).ne'
  simp only [Pi.div_apply]
  field_simp

/-- `log U / log(U − 1) → 1`. -/
theorem tendsto_log_div_log_sub_one :
    Tendsto (fun U : ℝ => Real.log U / Real.log (U - 1)) atTop (𝓝 1) := by
  have := (tendsto_const_nhds (x := (1 : ℝ))).div tendsto_log_sub_one_div_log one_ne_zero
  rw [div_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with U hU
  have h0 : Real.log U ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h1 : Real.log (U - 1) ≠ 0 := (Real.log_pos (by linarith)).ne'
  simp only [Pi.div_apply]
  field_simp

/-- **The Selberg main-term factor tends to `e^{2R}/(1 − e^{−2R/15})`.** -/
theorem tendsto_selbergBlockFactor {R : ℝ} (hR : 0 < R) :
    Tendsto (selbergBlockFactor R) atTop (𝓝 (selbergBlockConst R)) := by
  have hT1 := tendsto_log_mollLong_div_log_sub_one
  have hT4 := tendsto_log_div_log_sub_one
  have hlog1 : Tendsto (fun U : ℝ => Real.log (U - 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have hT0 : Tendsto (fun U : ℝ => 3 * R / Real.log (U - 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := 3 * R)).div_atTop hlog1
  have hden : 1 - Real.exp (-(2 * R) * (1 / 15)) ≠ 0 := by
    have := exp_neg_lt_one (show 0 < 2 * R / 15 by positivity)
    rw [show -(2 * R) * (1 / 15) = -(2 * R / 15) by ring]
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
  have hval : 1 / (1 - Real.exp (-(2 * R) * (1 / 15))) * (0 + 1) * Real.exp (2 * R * 1)
      * Real.exp (5 * 0) = selbergBlockConst R := by
    unfold selbergBlockConst
    rw [show -(2 * R) * (1 / 15) = -(2 * R / 15) by ring]
    simp only [mul_zero, Real.exp_zero, mul_one, zero_add]
    ring
  rw [hval] at hprod
  exact hprod

/-! ## The main term -/

/-- **The main term of a block with Selberg's twisted coefficients.** -/
theorem selberg_mainTerm_le {R U d a v η : ℝ} (hR : 0 < R) (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hRd : R ≤ d * Real.log U) (hdU1 : d * Real.log (U - 1) ≤ R) (hU3 : 3 ≤ U)
    (hN2 : 2 ≤ mollLong U) (hη : 0 < η) (h4 : 4 ≤ a - η) (hav : a ≤ v) (hvU : v ≤ U)
    (hηa : η ≤ a) (haη : a / 2 ≤ a - η) (haU : U ^ ((1 : ℝ) / 8) ≤ a) :
    gcdSum₂ d (mollLong U) (selbergReal R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (v - a + 2 * η) * selbergBlockFactor R U := by
  have hU0 : 0 < U := by linarith only [hU3]
  have hlogU0 : 0 < Real.log U := Real.log_pos (by linarith only [hU3])
  have hlogU1 : 0 < Real.log (U - 1) := Real.log_pos (by linarith only [hU3])
  have hd4 : d ≤ 1 / 4 := by linarith only [hd8]
  have hlen : 0 ≤ v - a + 2 * η := by linarith only [hav, hη]
  have hS := gcdSum₂_selbergReal_le hR hU3 hd.le hdU1 hN2
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
  have hN1 : (1 : ℝ) < mollLong U := by exact_mod_cast (by omega : 1 < mollLong U)
  have hexp : Real.exp (-(2 * R) * (Real.log (mollLong U) / Real.log (U - 1))) < 1 := by
    have h0 : 0 < Real.log (mollLong U) / Real.log (U - 1) :=
      div_pos (Real.log_pos hN1) hlogU1
    rw [show -(2 * R) * (Real.log (mollLong U) / Real.log (U - 1))
      = -(2 * R * (Real.log (mollLong U) / Real.log (U - 1))) by ring]
    exact exp_neg_lt_one (by positivity)
  have hE : 1 - Real.exp (-(2 * R) * (Real.log (mollLong U) / Real.log (U - 1))) ≠ 0 := by
    linarith
  have hG0 : 0 ≤ (2 * R / Real.log (U - 1))
      / (1 - Real.exp (-(2 * R) * (Real.log (mollLong U) / Real.log (U - 1)))) :=
    div_nonneg (by positivity) (by linarith)
  calc gcdSum₂ d (mollLong U) (selbergReal R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ ((2 * R / Real.log (U - 1))
          / (1 - Real.exp (-(2 * R) * (Real.log (mollLong U) / Real.log (U - 1)))))
        * ((3 / 2 + Real.log U / (2 * R))
          * ((v - a + 2 * η) * (Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
            * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))))) :=
        mul_le_mul hS (mul_le_mul hZ hX (norm_nonneg _) hZ0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hG0
    _ = (v - a + 2 * η) * selbergBlockFactor R U := by
        unfold selbergBlockFactor
        have hR0 : R ≠ 0 := hR.ne'
        have hl : Real.log (U - 1) ≠ 0 := hlogU1.ne'
        field_simp

/-! ## The dyadic law, the gate and the moment -/

theorem two_le_mollLong {U : ℝ} (hU : (2 : ℝ) ^ 15 ≤ U) : 2 ≤ mollLong U := by
  have h2 := two_le_rpow_one_div_fifteen hU
  have h1 := mollLong_gt U
  have : (1 : ℝ) < mollLong U := by linarith
  have : 1 < mollLong U := by exact_mod_cast this
  omega

/-- **The dyadic mean-square law with Selberg's twisted mollifier**, constant
`e^{2R}/(1 − e^{−2R/15})`. -/
theorem zetaDyadicMeanSquareLaw_selberg {R : ℝ} (hR : 0 < R) :
    ZetaDyadicMeanSquareLaw R (selbergBlockConst R) := by
  have hN : ∀ᶠ U in atTop, 1 ≤ mollLong U ∧ (mollLong U : ℝ) ≤ U ^ ((1 : ℝ) / 15) := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 15)] with U hU
    have h2 := two_le_mollLong hU
    exact ⟨by omega, mollLong_le (le_trans (by positivity) hU)⟩
  have hw : ∀ U, ∀ n ∈ Finset.Icc 1 (mollLong U), |selbergReal R U n| ≤ 1 := fun U n hn =>
    Sieve.abs_twistedWeight_le _ _ (Finset.mem_Icc.mp hn).1
  have hmain : ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U →
      d * Real.log (U - 1) ≤ R → ∀ a v η : ℝ, 0 < η → 4 ≤ a - η → a ≤ v → v ≤ U → η ≤ a →
      a / 2 ≤ a - η → U ^ ((1 : ℝ) / 8) ≤ a →
      gcdSum₂ d (mollLong U) (selbergReal R U) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
          * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
        ≤ (v - a + 2 * η) * selbergBlockFactor R U := by
    filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 15)] with U hU
    intro d hd hd8 hRd hdU1 a v η hη h4 hav hvU hηa haη haU
    have hU3 : (3 : ℝ) ≤ U := le_trans (by norm_num) hU
    exact selberg_mainTerm_le hR hd hd8 hRd hdU1 hU3 (two_le_mollLong hU) hη h4 hav hvU hηa
      haη haU
  exact zetaDyadicMeanSquareLaw_of_highBlock hR (selbergBlockConst_pos hR).le mollLong
    (selbergReal R) hN (fun U => Sieve.twistedWeight_one _ _) hw
    (exists_highBlock_bound_of_mainTerm (tendsto_selbergBlockFactor hR) mollLong (selbergReal R)
      (hN.mono fun _ h => h.2) hw hmain)

/-- **The mollified mean-square gate with Selberg's twisted mollifier.** -/
theorem zetaMollifiedMeanSquareGate_selberg {R : ℝ} (hR : 0 < R) :
    ZetaMollifiedMeanSquareGate R (max (selbergBlockConst R) 1) :=
  zetaMollifiedMeanSquareGate_of_dyadicLaw hR
    (zetaDyadicMeanSquareLaw_mono (le_max_left _ _) (zetaDyadicMeanSquareLaw_selberg hR))

/-- `log c_{5/2} − 25/6 + 1/100 ≤ 4π · 17/100`, from `e^{−1/3} ≤ 18/25` and `25/7 ≤ e^{9/7}`. -/
theorem log_selbergBlockConst_five_halves_le :
    Real.log (max (selbergBlockConst (5 / 2)) 1) - 5 / 3 * (5 / 2) + 1 / 100
      ≤ 4 * Real.pi * (17 / 100) := by
  have he3 : Real.exp (-(1 / 3 : ℝ)) ≤ 18 / 25 := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at h ⊢
    linarith
  have hden : 7 / 25 ≤ 1 - Real.exp (-(2 * (5 / 2) / 15)) := by
    rw [show -(2 * (5 / 2 : ℝ) / 15) = -(1 / 3) by norm_num]
    linarith
  have hc : selbergBlockConst (5 / 2) ≤ Real.exp 5 * (25 / 7) := by
    unfold selbergBlockConst
    rw [div_le_iff₀ (by linarith), show 2 * (5 / 2 : ℝ) = 5 by norm_num]
    have := mul_le_mul_of_nonneg_left hden (show 0 ≤ Real.exp 5 * (25 / 7) by positivity)
    linarith
  have hc1 : 1 ≤ selbergBlockConst (5 / 2) := by
    unfold selbergBlockConst
    rw [le_div_iff₀ (by linarith)]
    have h1 : 0 < Real.exp (-(2 * (5 / 2) / 15)) := Real.exp_pos _
    have h2 : 1 ≤ Real.exp (2 * (5 / 2)) := Real.one_le_exp (by norm_num)
    linarith
  rw [max_eq_left hc1]
  have h97 : 25 / 7 ≤ Real.exp (9 / 7) := by
    have h1 := Real.exp_one_gt_d9
    have h2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 / 7 by norm_num)
    have e : Real.exp (9 / 7) = Real.exp 1 * Real.exp (2 / 7) := by
      rw [← Real.exp_add]
      norm_num
    rw [e]
    have h3 := mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
    norm_num at h3 ⊢
    linarith
  have hlogc : Real.log (selbergBlockConst (5 / 2)) ≤ 5 + 9 / 7 := by
    have hpos : 0 < selbergBlockConst (5 / 2) := by linarith
    rw [Real.log_le_iff_le_exp hpos, Real.exp_add]
    calc selbergBlockConst (5 / 2) ≤ Real.exp 5 * (25 / 7) := hc
      _ ≤ Real.exp 5 * Real.exp (9 / 7) := mul_le_mul_of_nonneg_left h97 (Real.exp_pos _).le
  have hπ := Real.pi_gt_d2
  norm_num at hπ ⊢
  linarith

/-- **The off-line first moment is at most `17/100` of the height, unconditionally.** -/
theorem eventually_offLineMoment_le_selberg :
    ∀ᶠ V in atTop, offLineMoment V ≤ 17 / 100 * V := by
  have h := eventually_offLineMoment_le_of_zetaGate_twoThirds (R := 5 / 2) (η := 1 / 100)
    (by norm_num) (le_max_right _ _) (by norm_num)
    (zetaMollifiedMeanSquareGate_selberg (by norm_num))
  filter_upwards [h, eventually_ge_atTop 0] with V hV hV0
  have hc := log_selbergBlockConst_five_halves_le
  have hπ : 0 < 4 * Real.pi := by positivity
  have h1 : 4 * Real.pi * offLineMoment V ≤ 4 * Real.pi * (17 / 100) * V :=
    hV.trans (mul_le_mul_of_nonneg_right hc hV0)
  have h2 : 4 * Real.pi * (17 / 100) * V = 4 * Real.pi * (17 / 100 * V) := by ring
  rw [h2] at h1
  exact le_of_mul_le_mul_left h1 hπ

end RHTower.ZetaGateProductAFE

end
