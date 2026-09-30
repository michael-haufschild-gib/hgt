import GaloisForLFunctions.RHTower.ZetaGateProductAFEHighBlock
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovGcdFormSharp

/-!
# The high blocks of the mollified mean square with the sharp main-term constant

The main term of the block inequality is `S₂ · ‖ζ(1+2d)‖ · ‖∫ w χ(½−d+it)χ(½−d−it) dt‖`.  Replacing
the three crude estimates of `exists_highBlock_bound_productAFE` by

* `S₂ ≤ N^{4d} D(N)/log² N` with the Selberg diagonal `D(N) ~ log N`
  (`gcdSum₂_hbReal_le_diagonal`),
* `‖χ(½−d+it)‖² = (t/2π)^{2d} e^{e}`, `|e| ≤ 2d(π/t + 5/t²)` (`norm_chiPairWeight_le_sharp`),
* `d log(U−1) ≤ R` instead of `d log U ≤ 2R`,

with the mollifier length `N = ⌊U^{1/15}⌋` (`mollLong`) the main term per unit length tends to
`c_R = (15/(2R)) e^{2R + 4R/15}` (`tendsto_sharpBlockFactor`), and

  `∫_a^v ‖ζΨ(½−d+it)‖² dt ≤ (c_R + ε)(v − a) + ε a`

for every block with `U^{5/6} ≤ a ≤ v ≤ 2a ≤ 2U` once `U` is large (`exists_highBlock_bound_sharp`).
On such blocks `N ≤ a^{2/25} = u^8` with `u = a^{1/100}`, which is what the pair-error envelopes of the
product approximate functional equation need.
-/

noncomputable section

namespace RHTower.ZetaGateProductAFE

open Complex MeasureTheory Set Finset Filter Topology
open RHTower GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-! ## The gcd form against the Selberg diagonal -/

theorem barbanVehovSelbergDiagonal_nonneg (N : ℕ) : 0 ≤ Sieve.barbanVehovSelbergDiagonal N := by
  unfold Sieve.barbanVehovSelbergDiagonal
  exact Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- `S₂ ≤ N^{4d} D(N) / log² N`. -/
theorem gcdSum₂_hbReal_le_diagonal {d : ℝ} (hd0 : 0 ≤ d) {N : ℕ} (hN : 2 ≤ N) :
    gcdSum₂ d N (hbReal N)
      ≤ (N : ℝ) ^ (4 * d) * Sieve.barbanVehovSelbergDiagonal N / (Real.log N) ^ 2 := by
  rw [gcdSum₂_eq_gcd_form]
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h := Sieve.sum_barbanVehov_gcd_rpow_div_le_diagonal N (s := 1 + 2 * d) (by linarith)
  have e : ∑ P ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      hbReal N P.1 * hbReal N P.2 * (Nat.gcd P.1 P.2 : ℝ) ^ (1 + 2 * d) / ((P.1 : ℝ) * P.2)
      = (∑ P ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        Sieve.barbanVehovWeight N P.1 * Sieve.barbanVehovWeight N P.2
          * (Nat.gcd P.1 P.2 : ℝ) ^ (1 + 2 * d) / ((P.1 : ℝ) * P.2)) / (Real.log N) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun P _ => ?_
    unfold hbReal
    field_simp
  rw [e, div_le_div_iff_of_pos_right (by positivity)]
  rwa [show (2 * (1 + 2 * d - 1) : ℝ) = 4 * d by ring] at h

/-! ## The `χ`-pair weight -/

/-- `‖χ(½−d+it)χ(½−d−it)‖ ≤ (t/2π)^{2d} e^{2d(π/t + 5/t²)}`. -/
theorem norm_chiPairWeight_le_sharp {d t : ℝ} (hd0 : 0 ≤ d) (hd4 : d ≤ 1 / 4) (ht : 0 < t) :
    ‖chiPairWeight d t‖
      ≤ chiModulusWeight (2 * d) t * Real.exp (2 * d * (Real.pi / t + 5 / t ^ 2)) := by
  obtain ⟨e, he, heq⟩ := exists_norm_zetaChi_displacedLinePt_eq_weight_mul_exp hd0 hd4 ht
  unfold chiPairWeight
  rw [norm_mul, displacedLinePt_neg_eq_conj, zetaChi_conj, Complex.norm_conj, heq]
  have hw : chiModulusWeight d t * chiModulusWeight d t = chiModulusWeight (2 * d) t := by
    unfold chiModulusWeight
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have he1 : 2 * e ≤ 2 * d * (Real.pi / t + 5 / t ^ 2) := by
    have := (abs_le.mp he).2
    linarith
  have hw2 : 0 ≤ chiModulusWeight (2 * d) t := by unfold chiModulusWeight; positivity
  calc chiModulusWeight d t * Real.exp e * (chiModulusWeight d t * Real.exp e)
      = (chiModulusWeight d t * chiModulusWeight d t) * Real.exp (2 * e) := by
        rw [show (2 : ℝ) * e = e + e by ring, Real.exp_add]; ring
    _ ≤ chiModulusWeight (2 * d) t * Real.exp (2 * d * (Real.pi / t + 5 / t ^ 2)) := by
        rw [hw]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he1) hw2

/-- The window integral of the `χ`-pair weight with the sharp modulus. -/
theorem norm_integral_window_chiPairWeight_le_sharp {d p q η : ℝ} (hd : 0 < d) (hd4 : d ≤ 1 / 4)
    (hη : 0 < η) (hL : 4 ≤ p - η) (hpq : p ≤ q) :
    ‖∫ t, blockWindowC p q η t * chiPairWeight d t‖
      ≤ (q - p + 2 * η) * (((q + η) / (2 * Real.pi)) ^ (2 * d)
          * Real.exp (2 * d * (Real.pi / (p - η) + 5 / (p - η) ^ 2))) := by
  set M : ℝ := ((q + η) / (2 * Real.pi)) ^ (2 * d)
    * Real.exp (2 * d * (Real.pi / (p - η) + 5 / (p - η) ^ 2)) with hM
  have hqη : 0 ≤ (q + η) / (2 * Real.pi) := by
    have : 0 ≤ q + η := by linarith
    positivity
  have hM0 : 0 ≤ M := mul_nonneg (Real.rpow_nonneg hqη _) (Real.exp_pos _).le
  have hint : Integrable (fun t => blockWindowC p q η t * chiPairWeight d t) :=
    integrable_window_mul hη (continuous_chiPairWeight hd).continuousOn
  have hpt : ∀ t, ‖blockWindowC p q η t * chiPairWeight d t‖ ≤ ‖blockWindowC p q η t‖ * M := by
    intro t
    rw [norm_mul]
    by_cases ht : t ∈ Set.Icc (p - η) (q + η)
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have ht4 : 4 ≤ t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      have hpη : 0 < p - η := by linarith
      refine (norm_chiPairWeight_le_sharp hd.le hd4 ht0).trans ?_
      unfold chiModulusWeight
      rw [hM]
      refine mul_le_mul (Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right ht.2 (by positivity)) (by linarith))
        (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (Real.rpow_nonneg hqη _)
      have h1 : Real.pi / t ≤ Real.pi / (p - η) :=
        div_le_div_of_nonneg_left Real.pi_pos.le hpη ht.1
      have h2 : 5 / t ^ 2 ≤ 5 / (p - η) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ hpη.le ht.1 2)
      have h2d : 0 ≤ 2 * d := by linarith
      exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) h2d
    · rw [blockWindowC_eq_zero hη ht, norm_zero, zero_mul, zero_mul]
  calc ‖∫ t, blockWindowC p q η t * chiPairWeight d t‖
      ≤ ∫ t, ‖blockWindowC p q η t * chiPairWeight d t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖blockWindowC p q η t‖ * M :=
        integral_mono hint.norm ((integrable_blockWindowC hη).norm.mul_const _) hpt
    _ = (∫ t, ‖blockWindowC p q η t‖) * M := integral_mul_const _ _
    _ ≤ (q - p + 2 * η) * M :=
        mul_le_mul_of_nonneg_right (integral_norm_blockWindowC_le hη hpq) hM0

/-! ## The sharp main-term factor and its limit -/

/-- The mollifier length `N = ⌊U^{1/15}⌋`. -/
def mollLong (U : ℝ) : ℕ := ⌊U ^ ((1 : ℝ) / 15)⌋₊

theorem mollLong_le {U : ℝ} (hU : 0 ≤ U) : (mollLong U : ℝ) ≤ U ^ ((1 : ℝ) / 15) :=
  Nat.floor_le (by positivity)

theorem mollLong_gt (U : ℝ) : U ^ ((1 : ℝ) / 15) - 1 < (mollLong U : ℝ) := by
  have := Nat.lt_floor_add_one (U ^ ((1 : ℝ) / 15))
  unfold mollLong
  linarith

/-- `c_R = (15/(2R)) e^{2R + 4R/15}`. -/
def sharpBlockConst (R : ℝ) : ℝ := 15 / (2 * R) * Real.exp (2 * R + 4 * R / 15)

theorem sharpBlockConst_nonneg {R : ℝ} (hR : 0 < R) : 0 ≤ sharpBlockConst R := by
  unfold sharpBlockConst
  positivity

/-- The main-term factor per unit window mass at scale `U`. -/
def sharpBlockFactor (R U : ℝ) : ℝ :=
  Real.exp (4 * R * (Real.log (mollLong U) / Real.log (U - 1)))
    * (Sieve.barbanVehovSelbergDiagonal (mollLong U) / Real.log (mollLong U))
    * ((3 / 2 + Real.log U / (2 * R)) / Real.log (mollLong U))
    * Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
    * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))

theorem tendsto_mollLong : Tendsto (fun U : ℝ => mollLong U) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop (by norm_num))

/-- `log(U − 1)/log U → 1`. -/
theorem tendsto_log_sub_one_div_log :
    Tendsto (fun U : ℝ => Real.log (U - 1) / Real.log U) atTop (𝓝 1) := by
  have hlow : Tendsto (fun U : ℝ => 1 - Real.log 2 / Real.log U) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with U hU
    have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
    have h : Real.log U - Real.log 2 ≤ Real.log (U - 1) := by
      rw [← Real.log_div (by linarith) (by norm_num)]
      exact Real.log_le_log (by linarith) (by linarith)
    have e : 1 - Real.log 2 / Real.log U = (Real.log U - Real.log 2) / Real.log U := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right h hlogU.le
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with U hU
    have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
    rw [div_le_one hlogU]
    exact Real.log_le_log (by linarith) (by linarith)

theorem two_le_rpow_one_div_fifteen {U : ℝ} (hU : (2 : ℝ) ^ 15 ≤ U) :
    (2 : ℝ) ≤ U ^ ((1 : ℝ) / 15) := by
  have e : ((2 : ℝ) ^ 15) ^ ((1 : ℝ) / 15) = 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) 15, ← Real.rpow_mul (by norm_num),
      show ((15 : ℕ) : ℝ) * (1 / 15) = (1 : ℝ) by norm_num, Real.rpow_one]
  rw [← e]
  exact Real.rpow_le_rpow (by positivity) hU (by norm_num)

/-- `log N / log U → 1/15` for the mollifier length `N = ⌊U^{1/15}⌋`. -/
theorem tendsto_log_mollLong_div_log :
    Tendsto (fun U : ℝ => Real.log (mollLong U) / Real.log U) atTop (𝓝 (1 / 15)) := by
  have hlow : Tendsto (fun U : ℝ => 1 / 15 - Real.log 2 / Real.log U) atTop (𝓝 (1 / 15)) := by
    have := (tendsto_const_nhds (x := Real.log 2)).div_atTop Real.tendsto_log_atTop
    simpa using (tendsto_const_nhds (x := (1 / 15 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 15)] with U hU
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU)
    have h2 := two_le_rpow_one_div_fifteen hU
    have hNhalf : U ^ ((1 : ℝ) / 15) / 2 ≤ mollLong U := by linarith [mollLong_gt U]
    have hlogN : Real.log U / 15 - Real.log 2 ≤ Real.log (mollLong U) := by
      have h1 : Real.log (U ^ ((1 : ℝ) / 15) / 2) ≤ Real.log (mollLong U) :=
        Real.log_le_log (by positivity) hNhalf
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hU0] at h1
      linarith
    have e : 1 / 15 - Real.log 2 / Real.log U = (Real.log U / 15 - Real.log 2) / Real.log U := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right hlogN hlogU.le
  · filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 15)] with U hU
    have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU
    have hlogU : 0 < Real.log U := Real.log_pos (lt_of_lt_of_le (by norm_num) hU)
    have hN1 : (1 : ℝ) ≤ mollLong U := by
      linarith [mollLong_gt U, two_le_rpow_one_div_fifteen hU]
    have h : Real.log (mollLong U) ≤ Real.log U / 15 := by
      have := Real.log_le_log (by linarith) (mollLong_le hU0.le)
      rwa [Real.log_rpow hU0, one_div_mul_eq_div] at this
    rw [div_le_iff₀ hlogU]
    linarith

/-- **The sharp main-term factor tends to `c_R`.** -/
theorem tendsto_sharpBlockFactor {R : ℝ} (hR : 0 < R) :
    Tendsto (sharpBlockFactor R) atTop (𝓝 (sharpBlockConst R)) := by
  have hNlog := tendsto_log_mollLong_div_log
  have hsub := tendsto_log_sub_one_div_log
  have hlogN : Tendsto (fun U : ℝ => Real.log (mollLong U)) atTop atTop :=
    Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_iff (R := ℝ)).mpr tendsto_mollLong)
  have hevU : ∀ᶠ U : ℝ in atTop, 0 < Real.log U ∧ 0 < Real.log (U - 1) ∧ 0 < Real.log (mollLong U) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ), hlogN.eventually (eventually_gt_atTop 0)]
      with U hU hN
    exact ⟨Real.log_pos (by linarith), Real.log_pos (by linarith), hN⟩
  -- the four scalar limits
  have hT1 : Tendsto (fun U : ℝ => Real.log (mollLong U) / Real.log (U - 1)) atTop (𝓝 (1 / 15)) := by
    have := hNlog.div hsub one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [hevU] with U hU
    obtain ⟨h0, h1, -⟩ := hU
    have h0' := h0.ne'
    have h1' := h1.ne'
    simp only [Pi.div_apply]
    field_simp
  have hT4 : Tendsto (fun U : ℝ => Real.log U / Real.log (U - 1)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div hsub one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [hevU] with U hU
    obtain ⟨h0, h1, -⟩ := hU
    have h0' := h0.ne'
    have h1' := h1.ne'
    simp only [Pi.div_apply]
    field_simp
  have hT3 : Tendsto (fun U : ℝ => (3 / 2 + Real.log U / (2 * R)) / Real.log (mollLong U)) atTop
      (𝓝 (15 / (2 * R))) := by
    have h1 := (tendsto_const_nhds (x := (3 / 2 : ℝ))).div_atTop hlogN
    have h2 := (tendsto_const_nhds (x := 1 / (2 * R))).div hNlog (by norm_num)
    have h3 := h1.add h2
    have hval : (0 : ℝ) + 1 / (2 * R) / (1 / 15) = 15 / (2 * R) := by field_simp; ring
    rw [hval] at h3
    refine h3.congr' ?_
    filter_upwards [hevU] with U hU
    obtain ⟨h0, -, hN⟩ := hU
    have h0' := h0.ne'
    have hN' := hN.ne'
    simp only [Pi.div_apply]
    field_simp
  have hDiag : Tendsto (fun U : ℝ => Sieve.barbanVehovSelbergDiagonal (mollLong U)
      / Real.log (mollLong U)) atTop (𝓝 1) :=
    Sieve.tendsto_barbanVehovSelbergDiagonal_div_log_one.comp tendsto_mollLong
  have hT5 : Tendsto (fun U : ℝ => U ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hE1 := (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := 4 * R)).mul hT1)
  have hE2 := (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := 2 * R)).mul hT4)
  have hE3 := (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := (5 : ℝ))).mul hT5)
  have hprod := (((hE1.mul hDiag).mul hT3).mul hE2).mul hE3
  have hval : Real.exp (4 * R * (1 / 15)) * 1 * (15 / (2 * R)) * Real.exp (2 * R * 1)
      * Real.exp (5 * 0) = sharpBlockConst R := by
    unfold sharpBlockConst
    rw [mul_zero, Real.exp_zero, mul_one, mul_one, mul_one]
    rw [show 2 * R + 4 * R / 15 = 4 * R * (1 / 15) + 2 * R by ring, Real.exp_add]
    ring
  rw [hval] at hprod
  exact hprod

/-! ## The sharp main term -/

theorem mollN_rpow_four_le {d U R : ℝ} (hlogU1 : 0 < Real.log (U - 1))
    (hdU1 : d * Real.log (U - 1) ≤ R) (hN : 0 < Real.log (mollLong U)) :
    (mollLong U : ℝ) ^ (4 * d) ≤ Real.exp (4 * R * (Real.log (mollLong U) / Real.log (U - 1))) := by
  have hN0 : (0 : ℝ) < mollLong U := by
    by_contra h
    have h0 : (mollLong U : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, Real.log_zero] at hN
    exact lt_irrefl _ hN
  rw [Real.rpow_def_of_pos hN0]
  apply Real.exp_le_exp.mpr
  have hdle : d ≤ R / Real.log (U - 1) := by
    rw [le_div_iff₀ hlogU1]
    exact hdU1
  have := mul_le_mul_of_nonneg_left hdle (show 0 ≤ 4 * Real.log (mollLong U) by positivity)
  calc Real.log (mollLong U) * (4 * d) = 4 * Real.log (mollLong U) * d := by ring
    _ ≤ 4 * Real.log (mollLong U) * (R / Real.log (U - 1)) := this
    _ = 4 * R * (Real.log (mollLong U) / Real.log (U - 1)) := by ring

theorem chiWindowWeight_le {d U R y : ℝ} (hd : 0 ≤ d) (hU0 : 0 < U) (hlogU : 0 ≤ Real.log U)
    (hlogU1 : 0 < Real.log (U - 1)) (hdU1 : d * Real.log (U - 1) ≤ R) (hy0 : 0 ≤ y)
    (hy : y ≤ 2 * U) :
    (y / (2 * Real.pi)) ^ (2 * d) ≤ Real.exp (2 * R * (Real.log U / Real.log (U - 1))) := by
  have hbase : y / (2 * Real.pi) ≤ U := by
    have hπ : 2 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hπ hU0.le
    linarith only [this, hy]
  have hdle : d ≤ R / Real.log (U - 1) := by
    rw [le_div_iff₀ hlogU1]
    exact hdU1
  calc (y / (2 * Real.pi)) ^ (2 * d) ≤ U ^ (2 * d) :=
        Real.rpow_le_rpow (by positivity) hbase (by linarith only [hd])
    _ = Real.exp (Real.log U * (2 * d)) := Real.rpow_def_of_pos hU0 _
    _ ≤ Real.exp (2 * R * (Real.log U / Real.log (U - 1))) := by
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hdle (show 0 ≤ 2 * Real.log U by positivity)
        calc Real.log U * (2 * d) = 2 * Real.log U * d := by ring
          _ ≤ 2 * Real.log U * (R / Real.log (U - 1)) := this
          _ = 2 * R * (Real.log U / Real.log (U - 1)) := by ring

theorem exp_chiWindowError_le {d a η U : ℝ} (hd8 : d ≤ 1 / 8) (haη : a / 2 ≤ a - η)
    (h4 : 4 ≤ a - η) (hU0 : 0 < U) (haU : U ^ ((1 : ℝ) / 8) ≤ a) :
    Real.exp (2 * d * (Real.pi / (a - η) + 5 / (a - η) ^ 2))
      ≤ Real.exp (5 * U ^ (-(1 / 8 : ℝ))) := by
  apply Real.exp_le_exp.mpr
  have haη0 : 0 < a - η := by linarith only [h4]
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) haU
  have hsq : 4 * (a - η) ≤ (a - η) ^ 2 := by nlinarith
  have h5 : 5 / (a - η) ^ 2 ≤ (5 / 4) / (a - η) := by
    rw [div_le_div_iff₀ (by positivity) haη0]
    nlinarith
  have hπ : Real.pi / (a - η) ≤ 4 / (a - η) :=
    div_le_div_of_nonneg_right Real.pi_le_four haη0.le
  have hsum : Real.pi / (a - η) + 5 / (a - η) ^ 2 ≤ 11 / a := by
    have h2 : (21 / 4) / (a - η) ≤ (21 / 4) / (a / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) haη
    have h3 : (21 / 4) / (a / 2) ≤ 11 / a := by
      rw [div_le_div_iff₀ (by positivity) ha0]
      nlinarith
    have h4' : 4 / (a - η) + (5 / 4) / (a - η) = (21 / 4) / (a - η) := by ring
    linarith only [hπ, h5, h2, h3, h4']
  have hainv : 1 / a ≤ U ^ (-(1 / 8 : ℝ)) := by
    rw [Real.rpow_neg hU0.le, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) haU
  have hsum0 : 0 ≤ Real.pi / (a - η) + 5 / (a - η) ^ 2 := by positivity
  have h2d : 2 * d ≤ 1 / 4 := by linarith only [hd8]
  calc 2 * d * (Real.pi / (a - η) + 5 / (a - η) ^ 2)
      ≤ 1 / 4 * (11 / a) := mul_le_mul h2d hsum hsum0 (by norm_num)
    _ = 11 / 4 * (1 / a) := by ring
    _ ≤ 11 / 4 * U ^ (-(1 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hainv (by norm_num)
    _ ≤ 5 * U ^ (-(1 / 8 : ℝ)) := by
        have : 0 ≤ U ^ (-(1 / 8 : ℝ)) := by positivity
        linarith only [this]

/-- **The sharp main term of a block.** -/
theorem sharp_mainTerm_le {R U d a v η : ℝ} (hR : 0 < R) (hd : 0 < d) (hd8 : d ≤ 1 / 8)
    (hRd : R ≤ d * Real.log U) (hdU1 : d * Real.log (U - 1) ≤ R) (hU3 : 3 ≤ U)
    (hN2 : 2 ≤ mollLong U) (hlogN : 0 < Real.log (mollLong U)) (hη : 0 < η) (h4 : 4 ≤ a - η)
    (hav : a ≤ v) (hvU : v ≤ U) (hηa : η ≤ a) (haη : a / 2 ≤ a - η)
    (haU : U ^ ((1 : ℝ) / 8) ≤ a) :
    gcdSum₂ d (mollLong U) (hbReal (mollLong U)) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (v - a + 2 * η) * sharpBlockFactor R U := by
  have hU0 : 0 < U := by linarith only [hU3]
  have hlogU0 : 0 < Real.log U := Real.log_pos (by linarith only [hU3])
  have hlogU1 : 0 < Real.log (U - 1) := Real.log_pos (by linarith only [hU3])
  have hd4 : d ≤ 1 / 4 := by linarith only [hd8]
  have hlen : 0 ≤ v - a + 2 * η := by linarith only [hav, hη]
  have hS := gcdSum₂_hbReal_le_diagonal hd.le hN2
  have hζ := norm_riemannZeta_one_add_le (by linarith only [hd] : 0 < 2 * d)
  have hχ := norm_integral_window_chiPairWeight_le_sharp hd hd4 hη h4 hav
  have h1d := inv_two_mul_le hd hR hRd
  have hF1 := mollN_rpow_four_le hlogU1 hdU1 hlogN
  have hF4 := chiWindowWeight_le hd.le hU0 hlogU0.le hlogU1 hdU1
    (y := v + η) (by linarith only [hav, h4, hη]) (by linarith only [hvU, hηa, hav])
  have hF5 := exp_chiWindowError_le hd8 haη h4 hU0 haU
  have hD0 := barbanVehovSelbergDiagonal_nonneg (mollLong U)
  have hS' : gcdSum₂ d (mollLong U) (hbReal (mollLong U))
      ≤ Real.exp (4 * R * (Real.log (mollLong U) / Real.log (U - 1)))
        * (Sieve.barbanVehovSelbergDiagonal (mollLong U) / Real.log (mollLong U))
        * (1 / Real.log (mollLong U)) := by
    refine hS.trans ?_
    have e : (mollLong U : ℝ) ^ (4 * d) * Sieve.barbanVehovSelbergDiagonal (mollLong U)
        / (Real.log (mollLong U)) ^ 2
        = (mollLong U : ℝ) ^ (4 * d)
          * (Sieve.barbanVehovSelbergDiagonal (mollLong U) / Real.log (mollLong U))
          * (1 / Real.log (mollLong U)) := by
      field_simp
    rw [e]
    have hq0 : 0 ≤ Sieve.barbanVehovSelbergDiagonal (mollLong U) / Real.log (mollLong U) :=
      div_nonneg hD0 hlogN.le
    have hi0 : 0 ≤ 1 / Real.log (mollLong U) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hF1 hq0) hi0
  have hZ : ‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖ ≤ 3 / 2 + Real.log U / (2 * R) :=
    hζ.trans (by linarith only [h1d])
  have hX : ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖
      ≤ (v - a + 2 * η) * (Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
          * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))) := by
    refine hχ.trans (mul_le_mul_of_nonneg_left ?_ hlen)
    exact mul_le_mul hF4 hF5 (Real.exp_pos _).le (Real.exp_pos _).le
  have hZ0 : 0 ≤ 3 / 2 + Real.log U / (2 * R) := by positivity
  calc gcdSum₂ d (mollLong U) (hbReal (mollLong U)) * (‖riemannZeta ((1 + 2 * d : ℝ) : ℂ)‖
        * ‖∫ t, blockWindowC a v η t * chiPairWeight d t‖)
      ≤ (Real.exp (4 * R * (Real.log (mollLong U) / Real.log (U - 1)))
          * (Sieve.barbanVehovSelbergDiagonal (mollLong U) / Real.log (mollLong U))
          * (1 / Real.log (mollLong U)))
        * ((3 / 2 + Real.log U / (2 * R))
          * ((v - a + 2 * η) * (Real.exp (2 * R * (Real.log U / Real.log (U - 1)))
            * Real.exp (5 * U ^ (-(1 / 8 : ℝ)))))) :=
        mul_le_mul hS' (mul_le_mul hZ hX (norm_nonneg _) hZ0)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = (v - a + 2 * η) * sharpBlockFactor R U := by
        unfold sharpBlockFactor
        ring

/-! ## The sharp high-block bound -/

/-- **The sharp high-block bound.**  For `U` large, every displacement `d` with
`R ≤ d log U` and `d log(U − 1) ≤ R`, and every block `[a, v]` with `U^{5/6} ≤ a ≤ v ≤ 2a`, `v ≤ U`,
the mean square of `ζΨ` (mollifier length `⌊U^{1/15}⌋`) on the displaced line is at most
`(c_R + ε)(v − a) + ε a`, `c_R = (15/(2R)) e^{2R + 4R/15}`. -/
theorem exists_highBlock_bound_sharp {R : ℝ} (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∀ d : ℝ, 0 < d → d ≤ 1 / 8 → R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ ((5 : ℝ) / 6) ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
            * edPoly (hbCoeff (mollLong U)) (Finset.Icc 1 (mollLong U)) (displacedLinePt d τ)‖ ^ 2)
          ≤ (sharpBlockConst R + ε) * (v - a) + ε * a := by
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 20) (by norm_num)
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ :=
    exists_tsum_dualOffDiagTerm_le_split 20 (K'' := 40) (by norm_num)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_smoothDiagonal_left_le
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_norm_dualDiagonal_left_le
  have hC0 := sharpBlockConst_nonneg hR
  intro ε hε
  have hps := pairStar_nonneg hCA0 hC₁ hC₂ hK₁0
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ 800), eventually_ge_atTop (Real.exp 200),
    (tendsto_order.1 (tendsto_sharpBlockFactor hR)).2 _
      (show sharpBlockConst R < sharpBlockConst R + ε / 2 by linarith),
    eventually_const_mul_rpow_neg_le (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R))
      ((1 : ℝ) / 160) (by norm_num) (half_pos hε),
    eventually_const_mul_rpow_neg_le (4 * (sharpBlockConst R + ε) / ε) ((1 : ℝ) / 160)
      (by norm_num) one_pos]
    with U hU2 hUe hUA hUerr hUη
  intro d hd hd8 hRd hdU1 a v ha haU hav hv2 hvU
  -- consequences of `2^(800 : ℕ) ≤ U`; the hypothesis itself is cleared (its numeral is too large for
  -- the linear-arithmetic preprocessing)
  have hU1 : (1 : ℝ) ≤ U := le_trans (one_le_pow₀ (by norm_num)) hU2
  have h2100 : (2 : ℝ) ^ 100 ≤ a := by
    have e : ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 2) = (2 : ℝ) ^ 400 := by
      rw [← Real.rpow_natCast (2 : ℝ) 800, ← Real.rpow_mul (by norm_num),
        show ((800 : ℕ) : ℝ) * (1 / 2) = ((400 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (2 : ℝ) ^ 100 ≤ (2 : ℝ) ^ 400 := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ = ((2 : ℝ) ^ 800) ^ ((1 : ℝ) / 2) := e.symm
      _ ≤ U ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hU2 (by norm_num)
      _ ≤ U ^ ((5 : ℝ) / 6) := Real.rpow_le_rpow_of_exponent_le
          (le_trans (one_le_pow₀ (by norm_num)) hU2) (by norm_num)
      _ ≤ a := haU
  clear hU2
  have hd4 : d ≤ 1 / 4 := by linarith
  -- facts about `U`
  have hU0 : 0 < U := by linarith
  have hlogU : 200 ≤ Real.log U := by
    have := Real.log_le_log (Real.exp_pos 200) hUe
    rwa [Real.log_exp] at this
  have hlogU0 : 0 < Real.log U := by linarith
  have hU3 : (3 : ℝ) ≤ U := by
    have : (3 : ℝ) ≤ Real.exp 200 := by
      have := Real.add_one_le_exp (200 : ℝ)
      linarith
    linarith
  have hlogU1pos : 0 < Real.log (U - 1) := Real.log_pos (by linarith)
  have hdU : d * Real.log U ≤ 2 * R := by
    have hlog2U : Real.log U ≤ 2 * Real.log (U - 1) := by
      have h1 : U ≤ (U - 1) ^ 2 := by nlinarith
      have h2 : Real.log U ≤ Real.log ((U - 1) ^ 2) := Real.log_le_log hU0 h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith only [h2]
    have := mul_le_mul_of_nonneg_left hlog2U hd.le
    linarith only [this, hdU1]
  -- the mollifier length
  have hNle : (mollLong U : ℝ) ≤ U ^ ((1 : ℝ) / 15) := mollLong_le hU0.le
  have hNgt := mollLong_gt U
  have hNU : (256 : ℝ) ≤ U ^ ((1 : ℝ) / 15) := by
    have e : ((2 : ℝ) ^ 120) ^ ((1 : ℝ) / 15) = 256 := by
      rw [← Real.rpow_natCast (2 : ℝ) 120, ← Real.rpow_mul (by norm_num),
        show ((120 : ℕ) : ℝ) * (1 / 15) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    rw [← e]
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have : (2 : ℝ) ^ 120 ≤ Real.exp 200 := by
      rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have := Real.log_two_lt_d9
      norm_num at this ⊢
      linarith
    linarith
  have hN2 : 2 ≤ mollLong U := by
    have : (2 : ℝ) ≤ mollLong U := by linarith
    exact_mod_cast this
  have hNhalf : U ^ ((1 : ℝ) / 15) / 2 ≤ mollLong U := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log U / 30 ≤ Real.log (mollLong U) := by
    have h1 : Real.log (U ^ ((1 : ℝ) / 15) / 2) ≤ Real.log (mollLong U) :=
      Real.log_le_log (by positivity) hNhalf
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hU0] at h1
    linarith
  have hlogN1 : 1 ≤ Real.log (mollLong U) := by linarith
  -- the parameter `u = a^{1/100}`
  have ha0 : 0 < a := by linarith
  have haU8 : U ^ ((1 : ℝ) / 8) ≤ a :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) haU
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = a ^ ((1 : ℝ) / 100) := ⟨_, rfl⟩
  have hu2 : 2 ≤ u := by
    have e : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 100, ← Real.rpow_mul (by norm_num),
        show ((100 : ℕ) : ℝ) * (1 / 100) = (1 : ℝ) by norm_num, Real.rpow_one]
    rw [hudef, ← e]
    exact Real.rpow_le_rpow (by positivity) h2100 (by norm_num)
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hNu : (mollLong U : ℝ) ≤ u ^ 8 := by
    have hUa : U ≤ a ^ ((6 : ℝ) / 5) := by
      calc U = (U ^ ((5 : ℝ) / 6)) ^ ((6 : ℝ) / 5) := by
            rw [← Real.rpow_mul hU0.le]
            norm_num
        _ ≤ a ^ ((6 : ℝ) / 5) := Real.rpow_le_rpow (by positivity) haU (by norm_num)
    calc (mollLong U : ℝ) ≤ U ^ ((1 : ℝ) / 15) := hNle
      _ ≤ (a ^ ((6 : ℝ) / 5)) ^ ((1 : ℝ) / 15) := Real.rpow_le_rpow hU0.le hUa (by norm_num)
      _ = u ^ 8 := by
          rw [hudef, ← Real.rpow_mul ha0.le, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
          norm_num
  have hu5 : U ^ ((1 : ℝ) / 160) ≤ u ^ 5 := by
    calc U ^ ((1 : ℝ) / 160) = (U ^ ((1 : ℝ) / 8)) ^ ((1 : ℝ) / 100 * 5) := by
          rw [← Real.rpow_mul hU0.le]
          norm_num
      _ ≤ a ^ ((1 : ℝ) / 100 * 5) := Real.rpow_le_rpow (by positivity) haU8 (by norm_num)
      _ = u ^ 5 := by
          rw [hudef, Real.rpow_mul ha0.le, ← Real.rpow_natCast]
          norm_num
  -- the block parameters
  have hu100 : u ^ 100 = a := by
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num
  have hp : a = u ^ 100 := hu100.symm
  have h95 : u ^ 95 ≤ u ^ 100 / 2 := by
    have h5 : 2 ≤ u ^ 5 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hu2 5)
    have : u ^ 100 = u ^ 95 * u ^ 5 := by ring
    rw [this]
    nlinarith [pow_pos hu0 95]
  have hη : 0 < u ^ 95 := by positivity
  have hL : u ^ 100 / 2 ≤ a - u ^ 95 := by rw [hp]; linarith
  have h4 : (4 : ℝ) ≤ a - u ^ 95 := by
    have : (2 : ℝ) ^ 100 ≤ u ^ 100 := pow_le_pow_left₀ (by norm_num) hu2 100
    have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ 100 := by norm_num
    linarith
  have hq2 : v ≤ 2 * u ^ 100 := by rw [← hp]; exact hv2
  have hηa : u ^ 95 ≤ a := by
    rw [hp]
    linarith [pow_pos hu0 100]
  have hq3 : v + u ^ 95 ≤ 3 * U := by linarith
  have hlen : 0 ≤ v - a + 2 * u ^ 95 := by linarith
  -- Step A: window domination
  have hA := intervalIntegral_le_window_integral hη hav
    (continuousOn_normSq_zeta_mul_edPoly (d := d) (q := v) h4 (hbCoeff (mollLong U)) (mollLong U))
    (fun t => by positivity)
  -- Step B: the block inequality
  have hB := integral_window_normSq_le hd hd8 (x := u ^ 100) (by positivity) hη h4 hav
    (N := mollLong U) (b := hbCoeff (mollLong U)) (a := hbReal (mollLong U))
    (fun n _ => hbCoeff_eq_ofReal (mollLong U) n)
  -- Step C: the main term with the sharp constant
  have hlen' : 0 ≤ v - a + 2 * u ^ 95 := hlen
  have hmain := (sharp_mainTerm_le hR hd hd8 hRd hdU1 hU3 hN2 (by linarith) hη h4 hav hvU hηa
    (by rw [hp]; linarith only [h95]) haU8).trans (mul_le_mul_of_nonneg_left hUA.le hlen')
  -- Step D: the error
  have herr : ∑ h ∈ Finset.Icc 1 (mollLong U), ∑ k ∈ Finset.Icc 1 (mollLong U),
        ‖hbCoeff (mollLong U) h‖ * ‖hbCoeff (mollLong U) k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
      ≤ (v - a + 2 * u ^ 95) * (ε / 2) := by
    have hLf : (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * Real.exp (4 * R) :=
      rpow_two_mul_le_two_exp hd hd8 hU1 hdU (by linarith only [h4])
        (by linarith only [hav, hvU, hU1, hη])
    have hpair : ∀ h ∈ Finset.Icc 1 (mollLong U), ∀ k ∈ Finset.Icc 1 (mollLong U),
        ‖hbCoeff (mollLong U) h‖ * ‖hbCoeff (mollLong U) k‖
          * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
        ≤ (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
      intro h hh k hk
      have hb := norm_pairError_le_param hd hd8 hu2 hp hav hq2 hNu hh hk hCA0 hCA hC₁ hC₂ hsplit
        hK₁0 hK₂0 hK₁ hK₂
      have h1 : ‖hbCoeff (mollLong U) h‖ * ‖hbCoeff (mollLong U) k‖ ≤ 1 := by
        calc ‖hbCoeff (mollLong U) h‖ * ‖hbCoeff (mollLong U) k‖ ≤ 1 * 1 :=
              mul_le_mul (norm_hbCoeff_le hN2 hh) (norm_hbCoeff_le hN2 hk) (norm_nonneg _)
                zero_le_one
          _ = 1 := one_mul 1
      calc ‖hbCoeff (mollLong U) h‖ * ‖hbCoeff (mollLong U) k‖
            * ‖pairError d (u ^ 100) a v (u ^ 95) (h / Nat.gcd h k) (k / Nat.gcd h k) h k‖
          ≤ 1 * ((v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)) / u ^ 21)) :=
            mul_le_mul h1 hb (norm_nonneg _) zero_le_one
        _ ≤ (v - a + 2 * u ^ 95)
            * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21) := by
            rw [one_mul]
            have h2 : 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d) ≤ 2 * K₂ * (2 * Real.exp (4 * R)) :=
              mul_le_mul_of_nonneg_left hLf (by positivity)
            have : pairStar CA C₁ C₂ K₁ + 2 * K₂ * (1 + (a - u ^ 95)) ^ (2 * d)
                ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by linarith only [h2]
            gcongr
    have hsum := Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun k hk => hpair h hh k hk
    refine hsum.trans ?_
    rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul,
      Nat.add_sub_cancel]
    have hN16 : ((mollLong U : ℝ)) * (mollLong U : ℝ) ≤ u ^ 16 := by
      calc ((mollLong U : ℝ)) * (mollLong U : ℝ) ≤ u ^ 8 * u ^ 8 :=
            mul_le_mul hNu hNu (Nat.cast_nonneg _) (by positivity)
        _ = u ^ 16 := by ring
    have hK0 : 0 ≤ pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R) := by positivity
    have hfin : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 ≤ ε / 2 := by
      have h1 : (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5
          ≤ (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) * U ^ (-((1 : ℝ) / 160)) := by
        rw [div_eq_mul_inv, Real.rpow_neg hU0.le]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hu5) hK0
      exact h1.trans hUerr
    calc (mollLong U : ℝ) * ((mollLong U : ℝ) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)))
        = ((mollLong U : ℝ) * (mollLong U : ℝ)) * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) := by ring
      _ ≤ u ^ 16 * ((v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)) :=
          mul_le_mul_of_nonneg_right hN16 (mul_nonneg hlen (div_nonneg hK0 (by positivity)))
      _ = (v - a + 2 * u ^ 95)
          * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5) := by
          have e : u ^ 16 * ((pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 21)
              = (pairStar CA C₁ C₂ K₁ + 4 * K₂ * Real.exp (4 * R)) / u ^ 5 := by
            rw [mul_div_assoc', div_eq_div_iff (pow_ne_zero _ hu0.ne') (pow_ne_zero _ hu0.ne')]
            ring
          rw [← e]
          ring
      _ ≤ (v - a + 2 * u ^ 95) * (ε / 2) := mul_le_mul_of_nonneg_left hfin hlen
  -- Step E: combine
  have hη' : (sharpBlockConst R + ε) * (2 * u ^ 95) ≤ ε * a := by
    have h1 : 4 * (sharpBlockConst R + ε) / ε * U ^ (-((1 : ℝ) / 160)) ≤ 1 := hUη
    have hpos : 0 < 4 * (sharpBlockConst R + ε) / ε := by positivity
    have h2 : 4 * (sharpBlockConst R + ε) / ε ≤ U ^ ((1 : ℝ) / 160) := by
      rw [Real.rpow_neg hU0.le] at h1
      have hUp : 0 < U ^ ((1 : ℝ) / 160) := by positivity
      rwa [mul_inv_le_iff₀ hUp, one_mul] at h1
    have h3 : 4 * (sharpBlockConst R + ε) ≤ ε * u ^ 5 := by
      have := (div_le_iff₀ hε).mp (h2.trans hu5)
      linarith only [this]
    have h4' : (sharpBlockConst R + ε) * (2 * u ^ 95) ≤ (ε / 2) * (u ^ 95 * u ^ 5) := by
      have h5 := mul_le_mul_of_nonneg_right h3 (pow_pos hu0 95).le
      linarith only [h5]
    have hεa : 0 ≤ ε * a := mul_nonneg hε.le ha0.le
    calc (sharpBlockConst R + ε) * (2 * u ^ 95) ≤ (ε / 2) * (u ^ 95 * u ^ 5) := h4'
      _ = (ε / 2) * a := by rw [← hu100]; ring
      _ ≤ ε * a := by linarith only [hεa]
  calc (∫ τ in a..v, ‖riemannZeta (displacedLinePt d τ)
          * edPoly (hbCoeff (mollLong U)) (Finset.Icc 1 (mollLong U)) (displacedLinePt d τ)‖ ^ 2)
      ≤ ∫ t, blockWindow a v (u ^ 95) t * ‖riemannZeta (displacedLinePt d t)
          * edPoly (hbCoeff (mollLong U)) (Finset.Icc 1 (mollLong U)) (displacedLinePt d t)‖ ^ 2 := hA
    _ ≤ _ := hB
    _ ≤ (v - a + 2 * u ^ 95) * (sharpBlockConst R + ε / 2)
        + (v - a + 2 * u ^ 95) * (ε / 2) := add_le_add hmain herr
    _ = (sharpBlockConst R + ε) * (v - a) + (sharpBlockConst R + ε) * (2 * u ^ 95) := by
        ring
    _ ≤ (sharpBlockConst R + ε) * (v - a) + ε * a := by linarith only [hη']

end RHTower.ZetaGateProductAFE

end
