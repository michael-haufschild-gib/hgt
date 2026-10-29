import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.DisjointStepsHaveLogarithmicGammaCost
import GaloisForLFunctions.ArithmeticCriticalityTheory.QuarticGaugeWindowPotential
import GaloisForLFunctions.ArithmeticIncidencePositivity.OddPlateauFoldedWindowPositivity
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# Exact Gamma energy of an interval and its balanced split

The interval energy is its exterior tail plus its boundary moment. Keeping
both terms gives upper and lower finite parts with the same linear term.
That term cancels in the normalized energy of a balanced adjacent pair.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open RHTower RHTower.WeilLevyPoleGauss RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open MeanZeroIntervals ArithmeticCriticalityTheory BiarithmeticGaugeGeometry HTGeometry

/-- Gamma energy of an interval indicator, expressed through its width. -/
def intervalGammaCost (w : ℝ) : ℝ :=
  2 * w * archLevyAntideriv w + 2 * ∫ t in Ioc 0 w, t * archLevyDensity t

/-- A logarithmic cell has the exact interval energy at its actual width. -/
theorem rawCell_levyEnergy_eq_intervalGammaCost {a : ℕ} (ha : 1 ≤ a) :
    levyEnergy (rawCell a) = intervalGammaCost (logCellWidth a) := by
  have hw : 0 < logCellWidth a := logCellWidth_pos ha
  have hab : Real.log (a : ℝ) < Real.log ((a + 1 : ℕ) : ℝ) :=
    Real.log_lt_log (by exact_mod_cast (show 0 < a by omega))
      (by exact_mod_cast Nat.lt_succ_self a)
  have hwidth : Real.log ((a + 1 : ℕ) : ℝ) - Real.log (a : ℝ) = logCellWidth a := by
    simp only [logCellWidth, Nat.cast_add, Nat.cast_one]
  have hi : IntegrableOn (fun t => t * archLevyDensity t) (Ioc 0 (logCellWidth a)) :=
    RHTower.CHMDDoobGraph.integrable_archLevy_firstMoment.mono_set
      (fun _ ht => ht.1)
  have hn : 0 ≤ᵐ[volume.restrict (Ioc 0 (logCellWidth a))]
      fun t => t * archLevyDensity t :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ ht =>
      mul_nonneg ht.1.le (archLevyDensity_pos ht.1).le
  have hm : 0 ≤ ∫ t in Ioc 0 (logCellWidth a), t * archLevyDensity t := integral_nonneg_of_ae hn
  have ht : 0 ≤ archLevyAntideriv (logCellWidth a) := (archLevyAntideriv_pos hw).le
  have he := gamma_interval_exterior_kernel_eq hab
  rw [← rawCell_gamma_eq_exterior a, hwidth,
    show gammaTailMass (logCellWidth a) = archLevyAntideriv (logCellWidth a) from
      RHTower.WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hw,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hi hn] at he
  have hr : ENNReal.ofReal (intervalGammaCost (logCellWidth a)) =
      ENNReal.ofReal (2 * logCellWidth a * archLevyAntideriv (logCellWidth a)) +
        2 * ENNReal.ofReal (∫ t in Ioc 0 (logCellWidth a), t * archLevyDensity t) := by
    rw [intervalGammaCost, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
  have hcost : 0 ≤ intervalGammaCost (logCellWidth a) := by
    unfold intervalGammaCost
    positivity
  simpa only [ENNReal.toReal_ofReal (levyEnergy_nonneg_bv (rawCell_bv a) (rawCell_compact a)),
    ENNReal.toReal_ofReal hcost] using congrArg ENNReal.toReal (he.trans hr.symm)

private theorem firstMoment_bounds {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w / 2 + w ^ 2 / 8 - w ^ 3 / 48 ≤ ∫ t in Ioc 0 w, t * archLevyDensity t ∧
      (∫ t in Ioc 0 w, t * archLevyDensity t) ≤ w / 2 + w ^ 2 / 8 := by
  have hl := integral_pow_mul_archLevyDensity_ge (k := 1) (by omega)
    (a := 0) (by norm_num) hw.le hw1
  have hu := integral_pow_mul_archLevyDensity_le (k := 1) (by omega)
    (a := 0) (by norm_num) hw.le hw1
  norm_num only [pow_one, levyMomentPoly, levyMomentErr, Nat.cast_one,
    zero_pow (by decide : 1 ≠ 0), zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    zero_div, add_zero, sub_zero] at hl hu
  have h3 : 0 ≤ w ^ 3 := pow_nonneg hw.le 3
  have h4 : w ^ 4 ≤ w ^ 3 := by
    calc w ^ 4 = w ^ 3 * w := by ring
      _ ≤ w ^ 3 * 1 := mul_le_mul_of_nonneg_left hw1 h3
      _ = w ^ 3 := mul_one _
  constructor <;> nlinarith only [hl, hu, h3, h4]

/-- Lower finite part of the interval Gamma energy. -/
theorem intervalGammaCost_lower {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w * (1 - Real.log (w / 4) + Real.pi / 2 - w / 4 - w ^ 2 / 24) ≤
      intervalGammaCost w := by
  have ht := mul_le_mul_of_nonneg_left
    (ArithmeticIncidencePositivity.archLevyAntideriv_ge hw) (show 0 ≤ 2 * w by positivity)
  have hm := (firstMoment_bounds hw hw1).1
  unfold intervalGammaCost
  nlinarith only [ht, hm]

/-- Upper finite part with the same linear width term as the lower bound. -/
theorem intervalGammaCost_upper {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    intervalGammaCost w ≤
      w * (1 - Real.log (w / 4) + Real.pi / 2 - w / 4 + w ^ 2 / 48 + 5 * w ^ 3 / 192) := by
  have ht := mul_le_mul_of_nonneg_left
    (ArithmeticIncidencePositivity.archLevyAntideriv_le_expansion hw)
      (show 0 ≤ 2 * w by positivity)
  have hm := (firstMoment_bounds hw hw1).2
  unfold intervalGammaCost
  nlinarith only [ht, hm]

/-- Joining adjacent cells is an exact translation of the cell at half their index. -/
theorem levyEnergy_adjacent_pair {a : ℕ} (ha : 1 ≤ a) :
    levyEnergy (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) =
      levyEnergy (rawCell a) := by
  have he : (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) =
      fun x => rawCell a (x - Real.log 2) := by
    funext x
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero,
      Nat.mul_comm a 2, Nat.cast_ofNat] using (rawCell_hecke ha (by omega : 1 ≤ 2) x).symm
  rw [he]
  exact SpacingScaleHarmonicAnalysis.levyEnergy_translate (Real.log 2)

/-- Balanced polarization keeps the shared exterior energy with its exact coefficient. -/
theorem haarProfile_levyEnergy_eq {a : ℕ} (ha : 1 ≤ a) :
    levyEnergy (haarProfile a) =
      haarLeftCoeff a * levyEnergy (rawCell (2 * a)) +
        haarRightCoeff a * levyEnergy (rawCell (2 * a + 1)) -
        haarLeftCoeff a * haarRightCoeff a * levyEnergy (rawCell a) := by
  have hcv : BoundedVariationOn
      (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) univ := by
    simpa only [neg_one_mul, sub_neg_eq_add] using
      boundedVariationOn_sub (rawCell_bv (2 * a)) (bv_const_mul (-1) (rawCell_bv (2 * a + 1)))
  have hcc : HasCompactSupport (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) :=
    (rawCell_compact (2 * a)).add (rawCell_compact (2 * a + 1))
  have hi (n : ℕ) : Integrable (stationaryJump (rawCell n)) archBase :=
    (memLp_levyRoot (rawCell_bv n) (rawCell_compact n)).integrable_sq.congr
      (levyRoot_sq_ae (rawCell n))
  have hic : Integrable
      (stationaryJump (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x)) archBase :=
    (memLp_levyRoot hcv hcc).integrable_sq.congr (levyRoot_sq_ae _)
  have hil : Integrable (fun e => haarLeftCoeff a * stationaryJump (rawCell (2 * a)) e)
      archBase := (hi (2 * a)).const_mul _
  have hir : Integrable (fun e => haarRightCoeff a * stationaryJump (rawCell (2 * a + 1)) e)
      archBase := (hi (2 * a + 1)).const_mul _
  have his : Integrable (fun e => haarLeftCoeff a * stationaryJump (rawCell (2 * a)) e +
      haarRightCoeff a * stationaryJump (rawCell (2 * a + 1)) e) archBase := hil.add hir
  have hit : Integrable (fun e => (haarLeftCoeff a * haarRightCoeff a) *
      stationaryJump (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) e) archBase :=
    hic.const_mul _
  have hp (e : ℝ × ℝ) : stationaryJump (haarProfile a) e =
      haarLeftCoeff a * stationaryJump (rawCell (2 * a)) e +
        haarRightCoeff a * stationaryJump (rawCell (2 * a + 1)) e -
        (haarLeftCoeff a * haarRightCoeff a) *
          stationaryJump (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) e := by
    have h := haarCoeff_sum ha
    have hz : haarLeftCoeff a + haarRightCoeff a - 1 = 0 := by linarith only [h]
    simp only [stationaryJump, difference, left, right, haarProfile]
    calc
      _ = haarLeftCoeff a *
            (archLevyDensity e.1 * (rawCell (2 * a) e.2 - rawCell (2 * a) (e.2 + e.1)) ^ 2) +
          haarRightCoeff a *
            (archLevyDensity e.1 * (rawCell (2 * a + 1) e.2 - rawCell (2 * a + 1) (e.2 + e.1)) ^ 2) -
          (haarLeftCoeff a * haarRightCoeff a) *
            (archLevyDensity e.1 *
              (rawCell (2 * a) e.2 + rawCell (2 * a + 1) e.2 -
                (rawCell (2 * a) (e.2 + e.1) + rawCell (2 * a + 1) (e.2 + e.1))) ^ 2) +
          archLevyDensity e.1 * (haarLeftCoeff a + haarRightCoeff a - 1) *
            (haarLeftCoeff a * (rawCell (2 * a) e.2 - rawCell (2 * a) (e.2 + e.1)) ^ 2 +
              haarRightCoeff a *
                (rawCell (2 * a + 1) e.2 - rawCell (2 * a + 1) (e.2 + e.1)) ^ 2) := by ring
      _ = _ := by rw [hz]; ring
  calc
    _ = ∫ e, stationaryJump (haarProfile a) e ∂archBase :=
      (stationaryEnergy_eq_levyEnergy (haarProfile_bv a) (haarProfile_compact a)).symm
    _ = haarLeftCoeff a * levyEnergy (rawCell (2 * a)) +
        haarRightCoeff a * levyEnergy (rawCell (2 * a + 1)) -
        (haarLeftCoeff a * haarRightCoeff a) *
          levyEnergy (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) := by
      simp_rw [hp]
      rw [integral_sub his hit, integral_add hil hir]
      simp only [integral_const_mul]
      rw [show (∫ e, stationaryJump (rawCell (2 * a)) e ∂archBase) = levyEnergy (rawCell (2 * a)) from
        stationaryEnergy_eq_levyEnergy (rawCell_bv _) (rawCell_compact _),
        show (∫ e, stationaryJump (rawCell (2 * a + 1)) e ∂archBase) =
          levyEnergy (rawCell (2 * a + 1)) from
            stationaryEnergy_eq_levyEnergy (rawCell_bv _) (rawCell_compact _),
        show (∫ e, stationaryJump
          (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) e ∂archBase) =
            levyEnergy (fun x => rawCell (2 * a) x + rawCell (2 * a + 1) x) from
              stationaryEnergy_eq_levyEnergy hcv hcc]
    _ = _ := by rw [levyEnergy_adjacent_pair ha]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
