import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurFarTail
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionMellin

/-!
# Terminal cusps of finite arithmetic theta shifts

The complete theta source has the exact first-atom envelope asymptotic.
Every finite arithmetic shift polynomial consequently has one terminal
negative-cusp coefficient, while its positive cusp retains only shift one.
The coefficients may have either sign; no source atom is discarded.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Exact first-atom correction to the double-exponential source envelope. -/
theorem thetaCuspSourceTerm_one_div_envelope (x : ℝ) :
    thetaCuspSourceTerm x 1 / thetaEnvelope x =
      4 * Real.pi ^ 2 - 6 * Real.pi * Real.exp (-2 * x) := by
  have h4 : Real.exp (4 * x) * Real.exp (x / 2) = Real.exp (9 * x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (2 * x) * Real.exp (x / 2) = Real.exp (5 * x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (-2 * x) * Real.exp (9 * x / 2) = Real.exp (5 * x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_eq_iff (thetaEnvelope_pos x).ne').2
  rw [thetaCuspSourceTerm_one_eq]
  calc
    2 * Real.pi * (2 * Real.pi * Real.exp (4 * x) - 3 * Real.exp (2 * x)) *
        (Real.exp (x / 2) * Real.exp (-Real.pi * Real.exp (2 * x))) =
      4 * Real.pi ^ 2 * (Real.exp (4 * x) * Real.exp (x / 2)) *
        Real.exp (-Real.pi * Real.exp (2 * x)) -
      6 * Real.pi * (Real.exp (2 * x) * Real.exp (x / 2)) *
        Real.exp (-Real.pi * Real.exp (2 * x)) := by ring
    _ = (4 * Real.pi ^ 2 - 6 * Real.pi * Real.exp (-2 * x)) * thetaEnvelope x := by
      rw [h4, h2, ← hn, thetaEnvelope]
      ring

/-- The first atom has its literal leading envelope coefficient. -/
theorem thetaCuspSourceTerm_one_div_envelope_tendsto :
    Tendsto (fun x : ℝ => thetaCuspSourceTerm x 1 / thetaEnvelope x)
      atTop (𝓝 (4 * Real.pi ^ 2)) := by
  have htwox : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  have hsmall : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp htwox
  have h := (tendsto_const_nhds (x := 4 * Real.pi ^ 2)).sub
    (hsmall.const_mul (6 * Real.pi))
  apply (show Tendsto _ atTop (𝓝 (4 * Real.pi ^ 2)) from by simpa using h).congr'
  exact Eventually.of_forall fun x => by
    simpa only [neg_mul] using (thetaCuspSourceTerm_one_div_envelope x).symm

/-- The complete source, including every later atom, has the same exact leading envelope. -/
theorem thetaCuspFullSource_div_envelope_tendsto :
    Tendsto (fun x : ℝ => thetaCuspFullSource x / thetaEnvelope x)
      atTop (𝓝 (4 * Real.pi ^ 2)) := by
  have h := thetaCuspFullSource_div_firstAtom_tendsto_one.mul
    thetaCuspSourceTerm_one_div_envelope_tendsto
  apply (show Tendsto _ atTop (𝓝 (4 * Real.pi ^ 2)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  field_simp [(thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))).ne',
    (thetaEnvelope_pos x).ne']

/-- Exact ratio of two logarithmically shifted source envelopes. -/
theorem thetaEnvelope_add_div_add (u v x : ℝ) :
    thetaEnvelope (x + u) / thetaEnvelope (x + v) =
      Real.exp (9 * (u - v) / 2) *
        Real.exp (-Real.pi * (Real.exp (2 * u) - Real.exp (2 * v)) * Real.exp (2 * x)) := by
  rw [thetaEnvelope, thetaEnvelope, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_sub, ← Real.exp_add]
  congr 1
  simp only [mul_add, Real.exp_add]
  ring

/-- A shift toward the positive cusp is negligible beside every strictly smaller shift. -/
theorem thetaEnvelope_add_div_add_tendsto_zero {u v : ℝ} (huv : v < u) :
    Tendsto (fun x : ℝ => thetaEnvelope (x + u) / thetaEnvelope (x + v))
      atTop (𝓝 0) := by
  have htwox : Tendsto (fun x : ℝ => 2 * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  have hdiff : 0 < Real.exp (2 * u) - Real.exp (2 * v) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  have hnegative : -Real.pi * (Real.exp (2 * u) - Real.exp (2 * v)) < 0 :=
    mul_neg_of_neg_of_pos (by linarith [Real.pi_pos]) hdiff
  have h := (Real.tendsto_exp_atBot.comp
    (Tendsto.const_mul_atTop_of_neg hnegative (Real.tendsto_exp_atTop.comp htwox))).const_mul
      (Real.exp (9 * (u - v) / 2))
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  exact Eventually.of_forall fun x => by
    simpa only [neg_mul] using (thetaEnvelope_add_div_add u v x).symm

/-- The exact complete-source shift ratio vanishes, without an envelope replacement. -/
theorem thetaCuspFullSource_add_div_add_tendsto_zero {u v : ℝ} (huv : v < u) :
    Tendsto (fun x : ℝ => thetaCuspFullSource (x + u) / thetaCuspFullSource (x + v))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun x : ℝ => x + u) atTop atTop :=
    tendsto_atTop_add_const_right atTop u tendsto_id
  have hv : Tendsto (fun x : ℝ => x + v) atTop atTop :=
    tendsto_atTop_add_const_right atTop v tendsto_id
  have h := ((thetaCuspFullSource_div_envelope_tendsto.comp hu).div
    (thetaCuspFullSource_div_envelope_tendsto.comp hv) (by positivity)).mul
      (thetaEnvelope_add_div_add_tendsto_zero huv)
  apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
  filter_upwards with x
  field_simp [(thetaEnvelope_pos (x + u)).ne', (thetaEnvelope_pos (x + v)).ne',
    (thetaCuspFullSource_pos_all (x + v)).ne']

/-- A literal finite arithmetic shift polynomial of the completed theta source. -/
def finiteArithmeticThetaShift (D : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ d ∈ D, c d * thetaCuspFullSource (x + Real.log (d : ℝ))

/-- The largest shift is the complete negative-cusp coefficient, even for signed coefficients. -/
theorem finiteArithmeticThetaShift_terminal_ratio
    (D : Finset ℕ) (c : ℕ → ℝ) (b : ℕ) (hb : b ∈ D)
    (hpositive : ∀ d ∈ D, 0 < d) (hmax : ∀ d ∈ D, d ≤ b) :
    Tendsto (fun x : ℝ => finiteArithmeticThetaShift D c (-x) /
      thetaCuspFullSource (x - Real.log (b : ℝ))) atTop (𝓝 (c b)) := by
  classical
  have hsum := tendsto_finsetSum D (f := fun d x =>
      c d * (thetaCuspFullSource (x - Real.log (d : ℝ)) /
        thetaCuspFullSource (x - Real.log (b : ℝ))))
    (a := fun d => if d = b then c d else 0) (fun d hd => by
      by_cases hdb : d = b
      · subst d
        simp only [ite_true]
        convert (tendsto_const_nhds (x := c b)) using 1
        funext x
        rw [div_self (thetaCuspFullSource_pos_all _).ne', mul_one]
      · have hlt : d < b := by have := hmax d hd; omega
        have hlog : Real.log (d : ℝ) < Real.log (b : ℝ) :=
          Real.log_lt_log (by exact_mod_cast hpositive d hd) (by exact_mod_cast hlt)
        have hs := (thetaCuspFullSource_add_div_add_tendsto_zero
          (u := -Real.log (d : ℝ)) (v := -Real.log (b : ℝ)) (by linarith)).const_mul (c d)
        simpa only [sub_eq_add_neg, if_neg hdb, mul_zero] using hs)
  have hlimit : (∑ d ∈ D, if d = b then c d else 0) = c b := by simp [hb]
  rw [hlimit] at hsum
  apply hsum.congr'
  filter_upwards with x
  simp only [finiteArithmeticThetaShift, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [show -x + Real.log (d : ℝ) = -(x - Real.log (d : ℝ)) by ring,
    thetaCuspFullSource_neg]
  ring

/-- Only arithmetic shift one survives at the positive cusp. -/
theorem finiteArithmeticThetaShift_positive_ratio
    (D : Finset ℕ) (c : ℕ → ℝ) (hpositive : ∀ d ∈ D, 0 < d) :
    Tendsto (fun x : ℝ => finiteArithmeticThetaShift D c x / thetaCuspFullSource x)
      atTop (𝓝 (if 1 ∈ D then c 1 else 0)) := by
  classical
  have hsum := tendsto_finsetSum D (f := fun d x =>
      c d * (thetaCuspFullSource (x + Real.log (d : ℝ)) / thetaCuspFullSource x))
    (a := fun d => if d = 1 then c d else 0) (fun d hd => by
      by_cases hd1 : d = 1
      · subst d
        simp only [ite_true, Nat.cast_one, Real.log_one, add_zero]
        convert (tendsto_const_nhds (x := c 1)) using 1
        funext x
        rw [div_self (thetaCuspFullSource_pos_all _).ne', mul_one]
      · have hgt : 1 < d := by have := hpositive d hd; omega
        have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast hgt)
        have hs := (thetaCuspFullSource_add_div_add_tendsto_zero
          (u := Real.log (d : ℝ)) (v := 0) hlog).const_mul (c d)
        simpa only [add_zero, if_neg hd1, mul_zero] using hs)
  have hlimit : (∑ d ∈ D, if d = 1 then c d else 0) =
      if 1 ∈ D then c 1 else 0 := by simp
  rw [hlimit] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun x => by
    simp only [finiteArithmeticThetaShift, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    ring

end

end RHTower
