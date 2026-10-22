import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomFourthLeadingRatio

/-!
# Sign of the three-atom fourth logarithmic numerator

The reduced theta head has two exponential variables `z = exp(-3q)` and
`w = exp(-8q)`. Its Euler jets give a quartic numerator. The exact expansion
below retains every mixed term. The coefficients subtracted from this
expansion are nonnegative for `q ≥ 3`; the remaining positive terms other
than the leading one contribute less than `3/100` of the constant term.

Combining that estimate with the leading `63/100` bound gives
`N₃ < -(17/50) A₀` for `q ≥ π`. Bounds on the denominator give
`N₃/G⁴ < -17/160` on the same half-line.
-/

open Set

namespace RHTower.ThetaCuspThreeAtomFourth

/-- Coefficient magnitudes in the exponential expansion of the fourth numerator. -/
noncomputable def coefficient (k : ℕ) (q : ℝ) : ℝ :=
  match k with
  | 0 => q * (16*q^4 - 96*q^3 + 240*q^2 - 72*q + 135)
  | 3 => 4*q*(5184*q^7 - 35640*q^6 + 106092*q^5 - 165418*q^4 +
      145257*q^3 - 64680*q^2 + 13113*q - 945)
  | 6 => 48*q*(27648*q^7 - 103680*q^6 + 159024*q^5 - 94480*q^4 -
      444*q^3 + 24780*q^2 - 9054*q + 675)
  | 8 => 108*q*(49152*q^7 - 266240*q^6 + 578816*q^5 - 627344*q^4 +
      345376*q^3 - 86000*q^2 + 7464*q - 135)
  | 9 => 64*q*(82944*q^7 - 51840*q^6 - 71568*q^5 + 79298*q^4 -
      5043*q^3 - 25260*q^2 + 15273*q - 1755)
  | 11 => 324*q*(132288*q^7 - 785320*q^6 + 1612004*q^5 - 1611870*q^4 +
      855491*q^3 - 239480*q^2 + 27171*q - 675)
  | 12 => 1024*q*(4096*q^4 - 6144*q^3 + 3840*q^2 - 288*q + 135)
  | 14 => 2592*q*(359424*q^7 - 1163520*q^6 + 1539952*q^5 - 1050512*q^4 +
      392532*q^3 - 85300*q^2 + 10938*q - 405)
  | 16 => 1458*q*(1179648*q^7 - 3932160*q^6 + 4588544*q^5 - 2076560*q^4 +
      245216*q^3 + 50960*q^2 - 10264*q + 225)
  | 17 => 1728*q*(1920000*q^7 - 4784000*q^6 + 5003600*q^5 - 2735162*q^4 +
      906703*q^3 - 160580*q^2 + 13971*q - 945)
  | 19 => 2916*q*(5573952*q^7 - 13522200*q^6 + 9971036*q^5 - 3061586*q^4 +
      150941*q^3 + 138680*q^2 - 31411*q + 1035)
  | 22 => 11664*q*(5760000*q^7 - 6240000*q^6 + 2563600*q^5 + 53456*q^4 -
      301844*q^3 + 85540*q^2 - 9578*q + 585)
  | 24 => 78732*q*(442368*q^7 - 552960*q^6 + 48384*q^5 + 76336*q^4 -
      19936*q^3 - 560*q^2 + 936*q - 35)
  | 27 => 78732*q*(1080000*q^7 + 351000*q^6 - 359100*q^5 - 11918*q^4 +
      56747*q^3 - 17720*q^2 + 1899*q - 155)
  | 32 => 1594323*q*(3888*q^4 - 2592*q^3 + 720*q^2 - 24*q + 5)
  | _ => 0

/-- Polynomial expressions for the reduced head and its first four Euler jets. -/
noncomputable def eulerJet (j : ℕ) (q z w : ℝ) : ℝ :=
  match j with
  | 0 => 2*q - 3 + (32*q - 12)*z + (162*q - 27)*w
  | 1 => 2*q + (-96*q^2 + 68*q)*z + (-1296*q^2 + 378*q)*w
  | 2 => 2*q + (288*q^3 - 396*q^2 + 68*q)*z +
      (10368*q^3 - 5616*q^2 + 378*q)*w
  | 3 => 2*q + (-864*q^4 + 2052*q^3 - 996*q^2 + 68*q)*z +
      (-82944*q^4 + 76032*q^3 - 14256*q^2 + 378*q)*w
  | 4 => 2*q + (2592*q^5 - 9612*q^4 + 9144*q^3 - 2196*q^2 + 68*q)*z +
      (663552*q^5 - 940032*q^4 + 342144*q^3 - 31536*q^2 + 378*q)*w
  | _ => 0

/-- Quartic numerator of `-q + (q d/dq)^4 log G`. -/
noncomputable def numerator (q z w : ℝ) : ℝ :=
  let g := eulerJet 0 q z w
  let g₁ := eulerJet 1 q z w
  let g₂ := eulerJet 2 q z w
  let g₃ := eulerJet 3 q z w
  let g₄ := eulerJet 4 q z w;
  -q*g^4 + g^3*g₄ - 4*g^2*g₁*g₃ - 3*g^2*g₂^2 + 12*g*g₁^2*g₂ - 6*g₁^4

/-- The complete expansion, including every mixed exponential coefficient. -/
theorem numerator_expansion (q z w : ℝ) :
    numerator q z w = -coefficient 0 q + coefficient 3 q*z - coefficient 6 q*z^2 +
      coefficient 8 q*w + coefficient 9 q*z^3 + coefficient 11 q*z*w -
      coefficient 12 q*z^4 + coefficient 14 q*z^2*w - coefficient 16 q*w^2 +
      coefficient 17 q*z^3*w - coefficient 19 q*z*w^2 - coefficient 22 q*z^2*w^2 +
      coefficient 24 q*w^3 + coefficient 27 q*z*w^3 - coefficient 32 q*w^4 := by
  simp only [numerator, eulerJet, coefficient]
  ring

theorem coefficient_zero_pos {q : ℝ} (hq : 3 ≤ q) : 0 < coefficient 0 q := by
  have hb := basePolynomial_pos (sub_nonneg.mpr hq)
  rw [basePolynomial_unshift] at hb
  exact mul_pos (by linarith) hb

theorem coefficient_leading_eq {q : ℝ} (hq : 3 ≤ q) :
    coefficient 3 q * Real.exp (-3*q) / coefficient 0 q = leadingRatio q := by
  simp only [coefficient, leadingRatio]
  rw [leadingPolynomial_unshift, basePolynomial_unshift]
  have hq0 : q ≠ 0 := ne_of_gt (by linarith)
  have hb := basePolynomial_pos (sub_nonneg.mpr hq)
  rw [basePolynomial_unshift] at hb
  field_simp [hq0, ne_of_gt hb]

theorem negative_coefficients_nonneg {q : ℝ} (hq : 3 ≤ q) :
    0 ≤ coefficient 6 q ∧ 0 ≤ coefficient 12 q ∧ 0 ≤ coefficient 16 q ∧
      0 ≤ coefficient 19 q ∧ 0 ≤ coefficient 22 q ∧ 0 ≤ coefficient 32 q := by
  obtain ⟨y, hy, hqy⟩ : ∃ y : ℝ, 0 ≤ y ∧ q = y + 3 :=
    ⟨q - 3, sub_nonneg.mpr hq, by ring⟩
  rw [hqy]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [coefficient]; ring_nf; positivity

/-- Polynomial majorants for the seven remaining positive exponential terms. -/
noncomputable def majorant (k : ℕ) : ℝ :=
  match k with
  | 8 => 70578972
  | 9 => 21310784/3
  | 11 => 568544292
  | 14 => 3976631712
  | 17 => 8942377536
  | 24 => 29957919660
  | 27 => 49300377516
  | _ => 0

theorem remaining_coefficients_le {q : ℝ} (hq : 3 ≤ q) :
    coefficient 8 q ≤ majorant 8 * q^3 * coefficient 0 q ∧
    coefficient 9 q ≤ majorant 9 * q^3 * coefficient 0 q ∧
    coefficient 11 q ≤ majorant 11 * q^3 * coefficient 0 q ∧
    coefficient 14 q ≤ majorant 14 * q^3 * coefficient 0 q ∧
    coefficient 17 q ≤ majorant 17 * q^3 * coefficient 0 q ∧
    coefficient 24 q ≤ majorant 24 * q^3 * coefficient 0 q ∧
    coefficient 27 q ≤ majorant 27 * q^3 * coefficient 0 q := by
  obtain ⟨y, hy, hqy⟩ : ∃ y : ℝ, 0 ≤ y ∧ q = y + 3 :=
    ⟨q - 3, sub_nonneg.mpr hq, by ring⟩
  rw [hqy]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    apply sub_nonneg.mp
    simp only [coefficient, majorant]
    ring_nf
    positivity

noncomputable def dampedCubic (k q : ℝ) : ℝ := q^3 * Real.exp (-k*q)

theorem hasDerivAt_dampedCubic (k q : ℝ) :
    HasDerivAt (dampedCubic k) (q^2 * Real.exp (-k*q) * (3-k*q)) q := by
  convert! ((hasDerivAt_id q).pow 3).mul (((hasDerivAt_id q).const_mul (-k)).exp)
    using 1
  dsimp
  ring

theorem dampedCubic_antitoneOn {k : ℝ} (hk : 1 ≤ k) :
    AntitoneOn (dampedCubic k) (Ici 3) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
  · intro q _
    exact (hasDerivAt_dampedCubic k q).continuousAt.continuousWithinAt
  · intro q _
    exact (hasDerivAt_dampedCubic k q).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : 3 ≤ q := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hq)
    rw [(hasDerivAt_dampedCubic k q).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ q by linarith)]

theorem dampedCubic_le {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq : Real.pi ≤ q) :
    dampedCubic k q ≤ (157/50:ℝ)^3 / 23^k := by
  have hpi : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : Real.exp (-((k:ℝ)*(157/50))) ≤ 1/(23:ℝ)^k := by
    rw [Real.exp_neg, Real.exp_nat_mul, one_div]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    gcongr
    exact twentyThree_lt_exp_lower_pi.le
  calc
    dampedCubic k q ≤ dampedCubic k (157/50) :=
      dampedCubic_antitoneOn hk' (by norm_num)
        (by change 3 ≤ q; linarith) (hpi.trans_le hq).le
    _ ≤ (157/50:ℝ)^3 / 23^k := by
      unfold dampedCubic
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [div_eq_mul_inv, one_mul, neg_mul] using he

noncomputable def remainingMajorant (q : ℝ) : ℝ :=
  majorant 8 * dampedCubic 8 q + majorant 9 * dampedCubic 9 q +
    majorant 11 * dampedCubic 11 q + majorant 14 * dampedCubic 14 q +
    majorant 17 * dampedCubic 17 q + majorant 24 * dampedCubic 24 q +
    majorant 27 * dampedCubic 27 q

theorem remainingMajorant_lt {q : ℝ} (hq : Real.pi ≤ q) :
    remainingMajorant q < 3/100 := by
  calc
    remainingMajorant q ≤
        majorant 8 * ((157/50:ℝ)^3/23^8) + majorant 9 * ((157/50:ℝ)^3/23^9) +
        majorant 11 * ((157/50:ℝ)^3/23^11) + majorant 14 * ((157/50:ℝ)^3/23^14) +
        majorant 17 * ((157/50:ℝ)^3/23^17) + majorant 24 * ((157/50:ℝ)^3/23^24) +
        majorant 27 * ((157/50:ℝ)^3/23^27) := by
      simp only [remainingMajorant, majorant]
      gcongr
      · exact dampedCubic_le (k := 8) (by norm_num) hq
      · exact dampedCubic_le (k := 9) (by norm_num) hq
      · exact dampedCubic_le (k := 11) (by norm_num) hq
      · exact dampedCubic_le (k := 14) (by norm_num) hq
      · exact dampedCubic_le (k := 17) (by norm_num) hq
      · exact dampedCubic_le (k := 24) (by norm_num) hq
      · exact dampedCubic_le (k := 27) (by norm_num) hq
    _ < 3/100 := by norm_num [majorant]

theorem numerator_expansion_exp (q : ℝ) :
    numerator q (Real.exp (-3*q)) (Real.exp (-8*q)) =
      -coefficient 0 q + coefficient 3 q*Real.exp (-3*q) - coefficient 6 q*Real.exp (-6*q) +
      coefficient 8 q*Real.exp (-8*q) + coefficient 9 q*Real.exp (-9*q) +
      coefficient 11 q*Real.exp (-11*q) - coefficient 12 q*Real.exp (-12*q) +
      coefficient 14 q*Real.exp (-14*q) - coefficient 16 q*Real.exp (-16*q) +
      coefficient 17 q*Real.exp (-17*q) - coefficient 19 q*Real.exp (-19*q) -
      coefficient 22 q*Real.exp (-22*q) + coefficient 24 q*Real.exp (-24*q) +
      coefficient 27 q*Real.exp (-27*q) - coefficient 32 q*Real.exp (-32*q) := by
  rw [numerator_expansion]
  simp only [mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  ring_nf

/-- Uniform strict negative margin for the complete reduced head numerator. -/
theorem numerator_lt {q : ℝ} (hq : Real.pi ≤ q) :
    numerator q (Real.exp (-3*q)) (Real.exp (-8*q)) < -(17/50) * coefficient 0 q := by
  have hq3 : 3 ≤ q := by linarith [Real.pi_gt_d2]
  have hbase := coefficient_zero_pos hq3
  have hlead : coefficient 3 q * Real.exp (-3*q) < (63/100) * coefficient 0 q := by
    apply (div_lt_iff₀ hbase).mp
    rw [coefficient_leading_eq hq3]
    exact leadingRatio_lt hq
  obtain ⟨h6, h12, h16, h19, h22, h32⟩ := negative_coefficients_nonneg hq3
  obtain ⟨h8, h9, h11, h14, h17, h24, h27⟩ := remaining_coefficients_le hq3
  have upper (k : ℕ) (hk : coefficient k q ≤ majorant k * q^3 * coefficient 0 q) :
      coefficient k q * Real.exp (-(k:ℝ)*q) ≤
        coefficient 0 q * (majorant k * dampedCubic k q) := by
    calc
      _ ≤ (majorant k * q^3 * coefficient 0 q) * Real.exp (-(k:ℝ)*q) :=
        mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
      _ = _ := by unfold dampedCubic; ring
  have hrem : coefficient 8 q*Real.exp (-8*q) + coefficient 9 q*Real.exp (-9*q) +
      coefficient 11 q*Real.exp (-11*q) + coefficient 14 q*Real.exp (-14*q) +
      coefficient 17 q*Real.exp (-17*q) + coefficient 24 q*Real.exp (-24*q) +
      coefficient 27 q*Real.exp (-27*q) ≤ coefficient 0 q * remainingMajorant q := by
    unfold remainingMajorant
    linear_combination upper 8 h8 + upper 9 h9 + upper 11 h11 + upper 14 h14 +
      upper 17 h17 + upper 24 h24 + upper 27 h27
  have hrem' := mul_lt_mul_of_pos_left (remainingMajorant_lt hq) hbase
  have hn6 := mul_nonneg h6 (Real.exp_pos (-6*q)).le
  have hn12 := mul_nonneg h12 (Real.exp_pos (-12*q)).le
  have hn16 := mul_nonneg h16 (Real.exp_pos (-16*q)).le
  have hn19 := mul_nonneg h19 (Real.exp_pos (-19*q)).le
  have hn22 := mul_nonneg h22 (Real.exp_pos (-22*q)).le
  have hn32 := mul_nonneg h32 (Real.exp_pos (-32*q)).le
  rw [numerator_expansion_exp]
  linarith

theorem expDecay_le (k : ℕ) {q : ℝ} (hq : Real.pi ≤ q) :
    Real.exp (-(k:ℝ)*q) ≤ 1/(23:ℝ)^k := by
  have hpi : (157 / 50 : ℝ) ≤ q := by linarith [Real.pi_gt_d2]
  have he : (23 : ℝ) ≤ Real.exp q :=
    twentyThree_lt_exp_lower_pi.le.trans (Real.exp_le_exp.mpr hpi)
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, one_div]
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  gcongr

theorem head_pos {q : ℝ} (hq : 3 ≤ q) :
    0 < eulerJet 0 q (Real.exp (-3*q)) (Real.exp (-8*q)) := by
  have h0 : 0 < 2*q-3 := by linarith
  have h2 : 0 < 32*q-12 := by linarith
  have h3 : 0 < 162*q-27 := by linarith
  simp only [eulerJet]
  positivity

theorem head_lt {q : ℝ} (hq : Real.pi ≤ q) :
    eulerJet 0 q (Real.exp (-3*q)) (Real.exp (-8*q)) < 2*(2*q-3) := by
  have hq3 : 3 ≤ q := by linarith [Real.pi_gt_d2]
  have hb : 0 < 2*q-3 := by linarith
  have h2 : 32*q-12 ≤ 28*(2*q-3) := by linarith
  have h3 : 162*q-27 ≤ 153*(2*q-3) := by linarith
  have ht2 := mul_le_mul h2 (expDecay_le 3 hq) (Real.exp_pos _).le
    (show 0 ≤ 28*(2*q-3) by positivity)
  have ht3 := mul_le_mul h3 (expDecay_le 8 hq) (Real.exp_pos _).le
    (show 0 ≤ 153*(2*q-3) by positivity)
  norm_num at ht2 ht3
  simp only [eulerJet, neg_mul]
  linarith

theorem coefficient_zero_ge {q : ℝ} (hq : 3 ≤ q) :
    5*(2*q-3)^4 ≤ coefficient 0 q := by
  obtain ⟨y, hy, hqy⟩ : ∃ y : ℝ, 0 ≤ y ∧ q = y + 3 :=
    ⟨q-3, sub_nonneg.mpr hq, by ring⟩
  apply sub_nonneg.mp
  rw [hqy]
  simp only [coefficient]
  ring_nf
  positivity

/-- A denominator-independent negative margin in Euler coordinates. -/
theorem normalized_numerator_lt {q : ℝ} (hq : Real.pi ≤ q) :
    numerator q (Real.exp (-3*q)) (Real.exp (-8*q)) /
      (eulerJet 0 q (Real.exp (-3*q)) (Real.exp (-8*q)))^4 < -(17/160) := by
  have hq3 : 3 ≤ q := by linarith [Real.pi_gt_d2]
  have hg := head_pos hq3
  have hgp := head_lt hq
  have hpow : (eulerJet 0 q (Real.exp (-3*q)) (Real.exp (-8*q)))^4 <
      (2*(2*q-3))^4 := by gcongr
  have hn := numerator_lt hq
  have hc := coefficient_zero_ge hq3
  apply (div_lt_iff₀ (pow_pos hg 4)).mpr
  nlinarith

end RHTower.ThetaCuspThreeAtomFourth
