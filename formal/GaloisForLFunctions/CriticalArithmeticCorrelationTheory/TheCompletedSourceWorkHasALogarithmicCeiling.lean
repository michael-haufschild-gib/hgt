import GaloisForLFunctions.ArithmeticElectrostatics.TheSelbergWorkExhaustsTheTransverseEnergy
import GaloisForLFunctions.RHTower.LorentzianZeroMass

/-!
# A logarithmic ceiling for the completed arithmetic source work

Reflection bounds the full pair work by two damped Lorentzian rows. The
arithmetic mass bounds at unit width and at the damping width pay these rows
by `R (log R)²`. Multiplicities and all exterior interactions are retained.
-/

noncomputable section

open Filter RHTower
open GaloisForLFunctions.ArithmeticElectrostatics
open GaloisForLFunctions.ArithmeticCorrespondencePositivity

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The arithmetic logarithmic envelope at damping width `R`. -/
def sourceLogEnvelope (R : ℝ) : ℝ :=
  xiLineTwoLogDerivConstant + Real.log (R + 4)

theorem sourceLogEnvelope_nonneg {R : ℝ} (hR : 1 ≤ R) :
    0 ≤ sourceLogEnvelope R := by
  exact add_nonneg xiLineTwoLogDerivConstant_nonneg
    (Real.log_nonneg (by linarith only [hR]))

/-- A horizontal displacement in the critical strip is dominated by the unit Lorentzian. -/
theorem transverseAngular_le_lorentz {x : ℝ} (hx : x ^ 2 ≤ 1) (d : ℝ) :
    transverseAngular x d ≤ 1 / (1 + d ^ 2) := by
  by_cases hd : x ^ 2 + d ^ 2 = 0
  · simp only [transverseAngular, hd, div_zero]
    positivity
  have hdpos : 0 < x ^ 2 + d ^ 2 :=
    lt_of_le_of_ne (add_nonneg (sq_nonneg x) (sq_nonneg d)) (Ne.symm hd)
  unfold transverseAngular
  apply (div_le_div_iff₀ hdpos (by positivity)).mpr
  have h := mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg d)
  nlinarith only [h]

/-- Reflection preserves a summable height kernel even when the two points coalesce. -/
theorem reflectedEnergy_le_lorentz {x y : ℝ} (hxy : x ^ 2 + y ^ 2 ≤ 1) (d : ℝ) :
    reflectedEnergy x y d ≤ 2 / (1 + d ^ 2) := by
  have hx : x ^ 2 ≤ 1 := by linarith only [hxy, sq_nonneg y]
  have hy : y ^ 2 ≤ 1 := by linarith only [hxy, sq_nonneg x]
  have h := add_le_add (transverseAngular_le_lorentz hx d)
    (transverseAngular_le_lorentz hy d)
  simpa only [reflectedEnergy, ← add_div, one_add_one_eq_two] using h

/-- The logarithmic height cost is absorbed by the damping scale and one linear term. -/
theorem log_height_le_scale_add {R : ℝ} (hR : 0 < R) (t : ℝ) :
    Real.log (|t| + 4) ≤ Real.log (R + 4) + |t| / R := by
  have hu : 0 ≤ |t| / R := div_nonneg (abs_nonneg t) hR.le
  have hid : (|t| / R) * R = |t| := div_mul_cancel₀ _ hR.ne'
  have hinput : |t| + 4 ≤ (R + 4) * (1 + |t| / R) := by
    nlinarith only [hid, hu, hR.le]
  have hlog := Real.log_le_log (by positivity : 0 < |t| + 4) hinput
  rw [Real.log_mul (by linarith only [hR] : R + 4 ≠ 0)
    (by positivity : 1 + |t| / R ≠ 0)] at hlog
  have hlin := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |t| / R)
  linarith only [hlog, hlin]

/-- One width-adapted Lorentzian pays the damping and its logarithmic row cost. -/
theorem heightDamping_mul_log_le {R : ℝ} (hR : 1 ≤ R) (t : ℝ) :
    heightDamping R t * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) ≤
      R ^ 2 * (sourceLogEnvelope R + 1) / (R ^ 2 + t ^ 2) := by
  have hR0 : 0 < R := by linarith only [hR]
  have hden : 0 < R ^ 2 + t ^ 2 := by positivity
  have hL := sourceLogEnvelope_nonneg hR
  have hweight : R ^ 2 / (R ^ 2 + t ^ 2) ≤ 1 := by
    apply (div_le_one hden).mpr
    linarith only [sq_nonneg t]
  have hlinear : R * |t| / (R ^ 2 + t ^ 2) ≤ 1 := by
    apply (div_le_one hden).mpr
    nlinarith only [sq_nonneg (R - |t|), sq_abs t, sq_nonneg R, sq_nonneg t]
  have hlog : xiLineTwoLogDerivConstant + Real.log (|t| + 4) ≤
      sourceLogEnvelope R + |t| / R := by
    have h := log_height_le_scale_add hR0 t
    dsimp only [sourceLogEnvelope]
    linarith only [h]
  calc
    heightDamping R t * (xiLineTwoLogDerivConstant + Real.log (|t| + 4))
        ≤ heightDamping R t * (sourceLogEnvelope R + |t| / R) :=
      mul_le_mul_of_nonneg_left hlog (heightDamping_nonneg R t)
    _ = (R ^ 2 / (R ^ 2 + t ^ 2)) *
        ((R ^ 2 / (R ^ 2 + t ^ 2)) * sourceLogEnvelope R +
          R * |t| / (R ^ 2 + t ^ 2)) := by
      unfold heightDamping
      field_simp [hR0.ne', hden.ne']
    _ ≤ (R ^ 2 / (R ^ 2 + t ^ 2)) * (sourceLogEnvelope R + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hweight hL) hlinear
    _ = R ^ 2 * (sourceLogEnvelope R + 1) / (R ^ 2 + t ^ 2) := by ring

/-- A single damped Lorentzian row on the full multiplicity divisor. -/
def dampedLorentzRow (R : ℝ) (pq : XiZeroCopy × XiZeroCopy) : ℝ :=
  heightDamping R (xiZeroHeight pq.1) * lorentzMassTerm (xiZeroHeight pq.1) pq.2

theorem dampedLorentzRow_nonneg (R : ℝ) (pq : XiZeroCopy × XiZeroCopy) :
    0 ≤ dampedLorentzRow R pq :=
  mul_nonneg (heightDamping_nonneg R _) (lorentzMassTerm_nonneg _ _)

theorem lorentzMassTerm_height_comm (p q : XiZeroCopy) :
    lorentzMassTerm (xiZeroHeight p) q = lorentzMassTerm (xiZeroHeight q) p := by
  unfold lorentzMassTerm xiZeroHeight
  congr 2
  ring

/-- The old product majorant admits the rows; the sharper estimate will sum them by width. -/
theorem dampedLorentzRow_le_majorant {R : ℝ} (hR : 1 ≤ R)
    (pq : XiZeroCopy × XiZeroCopy) :
    dampedLorentzRow R pq ≤ xiWorkMajorant R pq := by
  have h := heightDamping_angular_bound hR 1 (xiZeroHeight pq.1) (xiZeroHeight pq.2)
    (by norm_num)
  have hrow : dampedLorentzRow R pq ≤
      2 * R ^ 4 / ((1 + xiZeroHeight pq.1 ^ 2) * (1 + xiZeroHeight pq.2 ^ 2)) := by
    simpa only [dampedLorentzRow, lorentzMassTerm, transverseAngular, one_pow,
      xiZeroHeight] using h
  calc
    dampedLorentzRow R pq ≤
        2 * R ^ 4 / ((1 + xiZeroHeight pq.1 ^ 2) * (1 + xiZeroHeight pq.2 ^ 2)) := hrow
    _ ≤ 16 * R ^ 4 / ((1 + xiZeroHeight pq.1 ^ 2) * (1 + xiZeroHeight pq.2 ^ 2)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith only [sq_nonneg (R ^ 2)]
    _ = xiWorkMajorant R pq := by
      unfold xiWorkMajorant
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem summable_dampedLorentzRow {R : ℝ} (hR : 1 ≤ R) :
    Summable (dampedLorentzRow R) :=
  Summable.of_nonneg_of_le (dampedLorentzRow_nonneg R)
    (dampedLorentzRow_le_majorant hR) (xiWorkMajorant_summable R)

/-- Sum a row at unit width before adapting the remaining height weight to width `R`. -/
theorem tsum_dampedLorentzRow_inner_le {R : ℝ} (hR : 1 ≤ R) (p : XiZeroCopy) :
    (∑' q : XiZeroCopy, dampedLorentzRow R (p, q)) ≤
      (8 * R ^ 2 * (sourceLogEnvelope R + 1)) * lorentzMassWTerm R 0 p := by
  have hmass := lorentzMass_le_log (xiZeroHeight p)
  have hweight := heightDamping_mul_log_le hR (xiZeroHeight p)
  calc
    (∑' q : XiZeroCopy, dampedLorentzRow R (p, q)) =
        heightDamping R (xiZeroHeight p) * lorentzMass (xiZeroHeight p) := by
      simp only [dampedLorentzRow, lorentzMass, tsum_mul_left]
    _ ≤ heightDamping R (xiZeroHeight p) *
        (8 * (xiLineTwoLogDerivConstant + Real.log (|xiZeroHeight p| + 4))) :=
      mul_le_mul_of_nonneg_left hmass (heightDamping_nonneg R _)
    _ = 8 * (heightDamping R (xiZeroHeight p) *
        (xiLineTwoLogDerivConstant + Real.log (|xiZeroHeight p| + 4))) := by ring
    _ ≤ 8 * (R ^ 2 * (sourceLogEnvelope R + 1) /
        (R ^ 2 + xiZeroHeight p ^ 2)) :=
      mul_le_mul_of_nonneg_left hweight (by norm_num)
    _ = (8 * R ^ 2 * (sourceLogEnvelope R + 1)) * lorentzMassWTerm R 0 p := by
      simp only [lorentzMassWTerm, xiZeroHeight, zero_sub, neg_sq]
      ring

/-- The full double row has a scale-sensitive arithmetic ceiling. -/
theorem tsum_dampedLorentzRow_le {R : ℝ} (hR : 1 ≤ R) :
    (∑' pq : XiZeroCopy × XiZeroCopy, dampedLorentzRow R pq) ≤
      64 * R * sourceLogEnvelope R * (sourceLogEnvelope R + 1) := by
  have hs := summable_dampedLorentzRow hR
  have hR0 : 0 < R := by linarith only [hR]
  have hL := sourceLogEnvelope_nonneg hR
  have hwidth : lorentzMassW R 0 ≤ (8 / R) * sourceLogEnvelope R := by
    simpa only [sourceLogEnvelope, abs_zero, add_zero] using lorentzMassW_le_log hR 0
  calc
    (∑' pq : XiZeroCopy × XiZeroCopy, dampedLorentzRow R pq) =
        ∑' p : XiZeroCopy, ∑' q : XiZeroCopy, dampedLorentzRow R (p, q) := hs.tsum_prod
    _ ≤ ∑' p : XiZeroCopy,
        (8 * R ^ 2 * (sourceLogEnvelope R + 1)) * lorentzMassWTerm R 0 p :=
      Summable.tsum_le_tsum (tsum_dampedLorentzRow_inner_le hR) hs.prod
        ((summable_lorentzMassWTerm hR 0).mul_left _)
    _ = (8 * R ^ 2 * (sourceLogEnvelope R + 1)) * lorentzMassW R 0 := by
      rw [tsum_mul_left]
      rfl
    _ ≤ (8 * R ^ 2 * (sourceLogEnvelope R + 1)) *
        ((8 / R) * sourceLogEnvelope R) :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = 64 * R * sourceLogEnvelope R * (sourceLogEnvelope R + 1) := by
      field_simp [hR0.ne']
      ring

/-- Both reflection rows use the same full-divisor sum. -/
theorem tsum_dampedLorentzRow_add_swap {R : ℝ} (hR : 1 ≤ R) :
    tsum (fun pq : XiZeroCopy × XiZeroCopy =>
      dampedLorentzRow R pq + dampedLorentzRow R (pq.2, pq.1)) =
      2 * tsum (dampedLorentzRow R) := by
  let e : (XiZeroCopy × XiZeroCopy) ≃ (XiZeroCopy × XiZeroCopy) := Equiv.prodComm _ _
  have hs := summable_dampedLorentzRow hR
  have he : Summable (fun pq => dampedLorentzRow R (e pq)) :=
    hs.comp_injective e.injective
  have hsum : (∑' pq, dampedLorentzRow R (e pq)) = ∑' pq, dampedLorentzRow R pq :=
    e.tsum_eq _
  change tsum (fun pq : XiZeroCopy × XiZeroCopy =>
    dampedLorentzRow R pq + dampedLorentzRow R (e pq)) = _
  rw [hs.tsum_add he, hsum]
  ring

/-- The complete reflected pair work is paid by two actual Lorentzian rows. -/
theorem xiDampedPairWork_le_rows {R : ℝ} (hR : 4 ≤ R) (p q : XiZeroCopy) :
    xiDampedPairWork R p q ≤
      2 * (dampedLorentzRow R (p, q) + dampedLorentzRow R (q, p)) := by
  have hwork := (heightDamping_work_bounds hR _ _ (xiZeroHeight p) (xiZeroHeight q)
    (xiSignedDepth_pair_bound p q)).2
  have henergy : xiReflectedPairEnergy p q ≤
      2 * lorentzMassTerm (xiZeroHeight p) q := by
    have h := reflectedEnergy_le_lorentz (xiSignedDepth_pair_bound p q)
      (xiZeroHeight p - xiZeroHeight q)
    simpa only [xiReflectedPairEnergy, lorentzMassTerm, xiZeroHeight, div_eq_mul_inv,
      one_mul] using h
  calc
    xiDampedPairWork R p q ≤
        (heightDamping R (xiZeroHeight p) + heightDamping R (xiZeroHeight q)) *
          xiReflectedPairEnergy p q := hwork
    _ ≤ (heightDamping R (xiZeroHeight p) + heightDamping R (xiZeroHeight q)) *
        (2 * lorentzMassTerm (xiZeroHeight p) q) :=
      mul_le_mul_of_nonneg_left henergy
        (add_nonneg (heightDamping_nonneg R _) (heightDamping_nonneg R _))
    _ = 2 * (dampedLorentzRow R (p, q) + dampedLorentzRow R (q, p)) := by
      unfold dampedLorentzRow
      rw [lorentzMassTerm_height_comm q p]
      ring

/-- The original completed source work is at most a fixed multiple of `R (log R)²`. -/
theorem xiDampedSourceWork_le_logarithmic_ceiling {R : ℝ} (hR : 4 ≤ R) :
    xiDampedSourceWork R ≤
      64 * R * sourceLogEnvelope R * (sourceLogEnvelope R + 1) := by
  have hR1 : 1 ≤ R := by linarith only [hR]
  have hs := summable_dampedLorentzRow hR1
  have hswap : Summable (fun pq : XiZeroCopy × XiZeroCopy =>
      dampedLorentzRow R (pq.2, pq.1)) :=
    hs.comp_injective (Equiv.prodComm XiZeroCopy XiZeroCopy).injective
  have hb := Summable.tsum_le_tsum
    (fun pq : XiZeroCopy × XiZeroCopy => xiDampedPairWork_le_rows hR pq.1 pq.2)
    (xiDampedPairWork_summable hR) ((hs.add hswap).mul_left 2)
  rw [tsum_mul_left, tsum_dampedLorentzRow_add_swap hR1] at hb
  have hrow := tsum_dampedLorentzRow_le hR1
  unfold xiDampedSourceWork
  linarith only [hb, hrow]

/-- Compact displacement tapers retain the same summable rows, uniformly in the taper index. -/
theorem abs_xiTaperedPairWork_le_rows {R : ℝ} (hR : 4 ≤ R) (N : ℕ)
    (p q : XiZeroCopy) :
    |xiTaperedPairWork R N p q| ≤
      4 * (dampedLorentzRow R (p, q) + dampedLorentzRow R (q, p)) := by
  have hwork := heightDamping_taper_work_bound hR _ _ (xiZeroHeight p) (xiZeroHeight q)
    (heightTaper N (xiZeroHeight p)) (heightTaper N (xiZeroHeight q))
    (xiSignedDepth_pair_bound p q) (heightTaper_bounds N _) (heightTaper_bounds N _)
    (heightTaper_lipschitz N _ _)
  have henergy : xiReflectedPairEnergy p q ≤
      2 * lorentzMassTerm (xiZeroHeight p) q := by
    have h := reflectedEnergy_le_lorentz (xiSignedDepth_pair_bound p q)
      (xiZeroHeight p - xiZeroHeight q)
    simpa only [xiReflectedPairEnergy, lorentzMassTerm, xiZeroHeight, div_eq_mul_inv,
      one_mul] using h
  calc
    |xiTaperedPairWork R N p q| ≤
        2 * (heightDamping R (xiZeroHeight p) + heightDamping R (xiZeroHeight q)) *
          xiReflectedPairEnergy p q := hwork
    _ ≤ 2 * (heightDamping R (xiZeroHeight p) + heightDamping R (xiZeroHeight q)) *
        (2 * lorentzMassTerm (xiZeroHeight p) q) :=
      mul_le_mul_of_nonneg_left henergy (by
        exact mul_nonneg (by norm_num)
          (add_nonneg (heightDamping_nonneg R _) (heightDamping_nonneg R _)))
    _ = 4 * (dampedLorentzRow R (p, q) + dampedLorentzRow R (q, p)) := by
      unfold dampedLorentzRow
      rw [lorentzMassTerm_height_comm q p]
      ring

/-- Every finite arithmetic Laurent-source reading obeys one ceiling, including its exterior rows. -/
theorem abs_xiTaperedSourceWork_le_logarithmic_ceiling {R : ℝ} (hR : 4 ≤ R) (N : ℕ) :
    |xiTaperedSourceWork R N| ≤
      128 * R * sourceLogEnvelope R * (sourceLogEnvelope R + 1) := by
  have hR1 : 1 ≤ R := by linarith only [hR]
  have hs := summable_dampedLorentzRow hR1
  have hswap : Summable (fun pq : XiZeroCopy × XiZeroCopy =>
      dampedLorentzRow R (pq.2, pq.1)) :=
    hs.comp_injective (Equiv.prodComm XiZeroCopy XiZeroCopy).injective
  have hpair := xiTaperedPairWork_summable hR N
  have hb := Summable.tsum_le_tsum
    (fun pq : XiZeroCopy × XiZeroCopy => show ‖xiTaperedPairWork R N pq.1 pq.2‖ ≤
        4 * (dampedLorentzRow R pq + dampedLorentzRow R (pq.2, pq.1)) from by
      simpa only [Real.norm_eq_abs] using abs_xiTaperedPairWork_le_rows hR N pq.1 pq.2)
    hpair.norm ((hs.add hswap).mul_left 4)
  rw [tsum_mul_left, tsum_dampedLorentzRow_add_swap hR1] at hb
  have htriangle : |∑' pq : XiZeroCopy × XiZeroCopy, xiTaperedPairWork R N pq.1 pq.2| ≤
      ∑' pq : XiZeroCopy × XiZeroCopy, ‖xiTaperedPairWork R N pq.1 pq.2‖ := by
    exact (Real.norm_eq_abs _).symm ▸ norm_tsum_le_tsum_norm hpair.norm
  have hrow := tsum_dampedLorentzRow_le hR1
  rw [xiTaperedSourceWork_eq_paired_tsum, abs_div,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  linarith only [hb, htriangle, hrow]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.xiDampedSourceWork_le_logarithmic_ceiling
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_xiTaperedSourceWork_le_logarithmic_ceiling
