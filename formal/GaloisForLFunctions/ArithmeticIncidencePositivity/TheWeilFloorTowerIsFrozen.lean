import GaloisForLFunctions.ArithmeticIncidencePositivity.MultiPrimeDilationModulusAndIteratedWeilFloors

/-!
# The Weil floor tower is frozen at its base

The tower `weilFloorApertureTower` is strictly increasing, and its step is
`multiPrimeApertureStep R δ ≤ exp (-1 - 4 C(1.1 R) / δ)`, whose exponent carries the dilation
coefficient `C ≥ 226` over the halving floors `δ = (1/20000)/2^k`. Hence the steps decay doubly
exponentially from `exp (-18080000)` and sum to less than that first size:

* `weilFloorApertureTower_sub_lt`: `a_k - a₀ < exp (-18080000)` for every `k`;
* `exp_lt_ten_rpow`: `exp (-18080000) < 10 ^ (-7800000)`;
* `weilFloorApertureTower_lt`: `a_k < 0.3621`, so every stage stays below `½ log 3`
  (`weilFloorApertureTower_lt_half_log_three`) and only the prime `2` ever acts on the base window;
* `tendsto_weilFloorApertureTower`: the tower converges to `weilFloorApertureLimit`, which lies
  within `10 ^ (-7800000)` of the base.

So the tower is no aperture producer: its limit is `a₀` to seven million digits.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open ArithmeticCriticalityTheory RenormalizedArithmeticPotentialTheory BiScaleUncertainty
open SelectivePositivityAndThresholdLaws

/-- The base aperture is `(181/500)(1 + s)²` for the single step `s ≤ 1/(40000 (11 + 4e²))`. -/
theorem successorWeilFloorAperture_lt : successorWeilFloorAperture < 181 / 500 + 5 / 10 ^ 7 := by
  have hs0 := weilFloorApertureStep_pos
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hsmall : weilFloorApertureStep ≤ 1 / (40000 * (11 + 4 * Real.exp 2)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have he2 : (73 / 10 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith only [h]
  have hs : weilFloorApertureStep ≤ 1 / 1600000 := by
    refine hsmall.trans (one_div_le_one_div_of_le (by norm_num) ?_)
    linarith only [he2]
  unfold successorWeilFloorAperture enlargedWeilFloorAperture
  nlinarith only [hs0, hs, mul_nonneg hs0.le hs0.le]

/-- The dilation coefficient at every radius `R ≥ 0.3982` is at least `226`. -/
theorem le_multiPrimeDilationCoeff {R : ℝ} (hR : 3982 / 10000 ≤ R) :
    226 ≤ multiPrimeDilationCoeff R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hatom : (4901 / 10000 : ℝ) ≤ vonMangoldtAtom 2 := by
    unfold vonMangoldtAtom
    rw [if_pos le_rfl, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    have hs : Real.sqrt ((2 : ℕ) : ℝ) ≤ 14142136 / 10000000 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hs0 : 0 < Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    rw [le_div_iff₀ hs0]
    have h2 := Real.log_two_gt_d9
    push_cast at hs ⊢
    nlinarith only [hs, h2]
  have hexpR : 14774 / 10000 ≤ Real.exp R := by
    have h := Real.quadratic_le_exp_of_nonneg hR0
    nlinarith only [h, hR]
  have hfloor : 2 ≤ ⌊Real.exp (2 * R)⌋₊ := by
    apply Nat.le_floor
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * R by linarith only [hR])
    push_cast
    nlinarith only [h, hR]
  have hw : 2 * vonMangoldtAtom 2 ≤ multiPrimeWeightSum R := by
    unfold multiPrimeWeightSum
    exact Finset.single_le_sum (f := fun n => 2 * vonMangoldtAtom n)
      (fun n _ => mul_nonneg (by norm_num) (vonMangoldtAtom_nonneg n))
      (Finset.mem_Icc.mpr ⟨le_rfl, hfloor⟩)
  have hsqrt : (16487 / 10000 : ℝ) ≤ Real.exp (1 / 2) := by
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h := Real.exp_one_gt_d9
    have hpos := Real.exp_pos (1 / 2 : ℝ)
    nlinarith only [hsq, h, hpos]
  have hw' : (9802 / 10000 : ℝ) ≤ multiPrimeWeightSum R := by linarith only [hw, hatom]
  have hL : (4333 / 1000 : ℝ) ≤ multiPrimeLowEnergyConstant R := by
    unfold multiPrimeLowEnergyConstant
    have hprod : (3982 / 10000 : ℝ) * (14774 / 10000) ≤ R * Real.exp R :=
      mul_le_mul hR hexpR (by norm_num) hR0
    have habs := abs_nonneg (gammaHardyPhaseRate 0)
    nlinarith only [hprod, habs, hw']
  unfold multiPrimeDilationCoeff
  have hprod : (16487 / 10000 : ℝ) * (4333 / 1000) ≤
      Real.exp (1 / 2) * multiPrimeLowEnergyConstant R :=
    mul_le_mul hsqrt hL (by norm_num) (Real.exp_pos _).le
  have hinner : (228 + 6 / 10 : ℝ) + 2 ≤
      32 * Real.exp (1 / 2) * multiPrimeLowEnergyConstant R + 2 := by
    nlinarith only [hprod]
  calc (226 : ℝ) ≤ (9802 / 10000) * ((228 + 6 / 10) + 2) := by norm_num
    _ ≤ _ := mul_le_mul hw' hinner (by norm_num) (multiPrimeWeightSum_nonneg R)

/-- At stage `k` and any radius in `[181/500, 1/2]` the step is at most `q^(k+1)`, for
`q = exp (-18080000)`. -/
theorem multiPrimeApertureStep_le_pow (k : ℕ) {R : ℝ} (hR : 181 / 500 ≤ R) :
    multiPrimeApertureStep R (weilFloorTowerConst k) ≤ Real.exp (-18080000) ^ (k + 1) := by
  have hC := le_multiPrimeDilationCoeff (R := (11 / 10) * R) (by linarith only [hR])
  have hstep : multiPrimeApertureStep R (weilFloorTowerConst k) ≤
      Real.exp (-1 - 4 * multiPrimeDilationCoeff ((11 / 10) * R) / weilFloorTowerConst k) /
        max 1 (2 * ((11 / 10) * R)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmax : (1 : ℝ) ≤ max 1 (2 * ((11 / 10) * R)) := le_max_left _ _
  have hdiv := div_le_self (Real.exp_pos
    (-1 - 4 * multiPrimeDilationCoeff ((11 / 10) * R) / weilFloorTowerConst k)).le hmax
  refine hstep.trans (hdiv.trans ?_)
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  have hδ : 4 * multiPrimeDilationCoeff ((11 / 10) * R) / weilFloorTowerConst k =
      80000 * multiPrimeDilationCoeff ((11 / 10) * R) * (2 : ℝ) ^ k := by
    unfold weilFloorTowerConst
    field_simp
    ring
  have hpow : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
    have h : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    exact_mod_cast h
  rw [hδ]
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith only [mul_le_mul hC hpow (by positivity) (by linarith only [hC]), hk]

private theorem exp_neg_large_le : Real.exp (-18080000) ≤ 1 / 18080001 := by
  have h := Real.add_one_le_exp (18080000 : ℝ)
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [h])

/-- Every stage stays within the summed geometric series of the steps above the base. -/
theorem weilFloorApertureTower_le (k : ℕ) :
    weilFloorApertureTower k ≤ successorWeilFloorAperture +
      Real.exp (-18080000) * (1 - (1 / 2) ^ k) := by
  set q := Real.exp (-18080000) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq2 : q ≤ 1 / 18080001 := exp_neg_large_le
  have hbase := successorWeilFloorAperture_lt
  induction k with
  | zero => simp [weilFloorApertureTower_zero]
  | succ k ih =>
    simp only [weilFloorApertureTower]
    have hR : 181 / 500 ≤ weilFloorApertureTower k :=
      (enlargedWeilFloorAperture_bounds.1.trans
        (enlargedWeilFloorAperture_lt_weilFloorApertureTower k)).le
    have hd := multiPrimeApertureStep_le_pow k hR
    have hd0 := multiPrimeApertureStep_pos (weilFloorApertureTower_pos k)
      (weilFloorTowerConst_pos k)
    have hpow : q ^ (k + 1) ≤ q * (1 / 2) ^ k := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hq0.le (hq2.trans (by norm_num)) k) hq0.le
    have hhalf0 : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have hhalf1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hRle : weilFloorApertureTower k ≤ 1 / 2 := by
      have hbase' : successorWeilFloorAperture < 2 / 5 := hbase.trans (by norm_num)
      nlinarith only [ih, hbase', hq2, mul_pos hq0 hhalf0]
    have hmul : weilFloorApertureTower k * multiPrimeApertureStep (weilFloorApertureTower k)
        (weilFloorTowerConst k) ≤ (1 / 2) * (q * (1 / 2) ^ k) :=
      mul_le_mul hRle (hd.trans hpow) hd0.le (by norm_num)
    rw [pow_succ]
    nlinarith only [ih, hmul]

/-- **Frozen tower.** `a_k - a₀ < exp (-18080000)` at every stage. -/
theorem weilFloorApertureTower_sub_lt (k : ℕ) :
    weilFloorApertureTower k - successorWeilFloorAperture < Real.exp (-18080000) := by
  have h := weilFloorApertureTower_le k
  have hq0 := Real.exp_pos (-18080000 : ℝ)
  have hhalf0 : (0 : ℝ) < (1 / 2) ^ k := by positivity
  nlinarith only [h, hq0, mul_pos hq0 hhalf0]

/-- `exp (-18080000) < 10 ^ (-7800000)`, from `10³ < 2¹⁰` and `log 2 < 0.6931471808`. -/
theorem exp_lt_ten_rpow : Real.exp (-18080000) < (10 : ℝ) ^ (-7800000 : ℝ) := by
  rw [Real.rpow_def_of_pos (by norm_num), Real.exp_lt_exp]
  have hlog : 3 * Real.log 10 ≤ 10 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 10 ^ 3)
      (by norm_num : (10 : ℝ) ^ 3 ≤ 2 ^ 10)
    rw [Real.log_pow, Real.log_pow] at h
    exact_mod_cast h
  have h2 := Real.log_two_lt_d9
  linarith only [hlog, h2]

/-- Every stage of the tower lies within `exp (-18080000)` of the base. -/
theorem weilFloorApertureTower_lt (k : ℕ) : weilFloorApertureTower k < 3621 / 10000 := by
  have h := weilFloorApertureTower_sub_lt k
  have hbase := successorWeilFloorAperture_lt
  have hsmall := exp_neg_large_le
  norm_num at hbase hsmall ⊢
  linarith only [h, hbase, hsmall]

/-- No stage of the tower reaches the window `½ log 3`, where the prime `3` would first act. -/
theorem weilFloorApertureTower_lt_half_log_three (k : ℕ) :
    weilFloorApertureTower k < Real.log 3 / 2 := by
  have h := weilFloorApertureTower_lt k
  have hlog : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr (Real.exp_one_lt_d9.trans (by norm_num))
  linarith only [h, hlog]

/-- The tower is bounded above by `0.3621`. -/
theorem bddAbove_range_weilFloorApertureTower : BddAbove (Set.range weilFloorApertureTower) :=
  ⟨3621 / 10000, by rintro _ ⟨k, rfl⟩; exact (weilFloorApertureTower_lt k).le⟩

/-- The limit aperture `a_∞` of the floor tower. -/
def weilFloorApertureLimit : ℝ := ⨆ k, weilFloorApertureTower k

/-- The monotone tower converges to its limit aperture. -/
theorem tendsto_weilFloorApertureTower :
    Tendsto weilFloorApertureTower atTop (𝓝 weilFloorApertureLimit) :=
  tendsto_atTop_ciSup weilFloorApertureTower_strictMono.monotone
    bddAbove_range_weilFloorApertureTower

/-- **The limit aperture lies within `10 ^ (-7800000)` of the base**, and below `0.3621`. -/
theorem weilFloorApertureLimit_bounds :
    successorWeilFloorAperture < weilFloorApertureLimit ∧
      weilFloorApertureLimit - successorWeilFloorAperture < (10 : ℝ) ^ (-7800000 : ℝ) ∧
      weilFloorApertureLimit < 3621 / 10000 := by
  have hle : ∀ k, weilFloorApertureTower k ≤ weilFloorApertureLimit :=
    fun k => le_ciSup bddAbove_range_weilFloorApertureTower k
  have hsup : weilFloorApertureLimit ≤ successorWeilFloorAperture + Real.exp (-18080000) :=
    ciSup_le fun k => by linarith only [weilFloorApertureTower_sub_lt k]
  have hgap := exp_lt_ten_rpow
  refine ⟨?_, by linarith only [hsup, hgap], ?_⟩
  · exact (weilFloorApertureTower_lt_succ 0).trans_le (hle 1)
  · have hbase := successorWeilFloorAperture_lt
    have hsmall := exp_neg_large_le
    norm_num at hbase hsmall ⊢
    linarith only [hsup, hbase, hsmall]

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.weilFloorApertureLimit_bounds
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.weilFloorApertureTower_lt_half_log_three
