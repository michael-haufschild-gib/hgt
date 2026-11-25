import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.ExactDistance.Tails
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.Uniform

/-! # Tail probabilities of the measured Gibbs energy gap -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GibbsTail

open Set Filter MeasureTheory Topology

/-- Weight of an unnormalized numerator row with denominator label n. -/
def weighted (h : Ioi (0:ℝ)) (n : ℕ+) (x : ℝ) := labelMass h n*(x/labelPartition h)

/-- The conditional event log(m/n) > u has an integer lower endpoint in each denominator row. -/
def tailRow (h : Ioi (0:ℝ)) (u : ℝ) (n : ℕ+) :=
  weighted h n (tail h ⌊Real.exp u*(n.val:ℝ)⌋₊)

theorem weighted_strictMono (h : Ioi (0:ℝ)) (n : ℕ+) : StrictMono (weighted h n) :=
  fun _ _ hab => mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hab (labelPartition_pos h)) (labelMass_pos h n)

theorem weighted_add (h : Ioi (0:ℝ)) (n : ℕ+) (x y : ℝ) :
    weighted h n (x+y) = weighted h n x+weighted h n y := by unfold weighted; ring

theorem weighted_mul (h : Ioi (0:ℝ)) (n : ℕ+) (x y : ℝ) :
    weighted h n (x*y) = weighted h n x*y := by unfold weighted; ring

theorem weighted_nonneg (h : Ioi (0:ℝ)) (n : ℕ+) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ weighted h n x :=
  mul_nonneg (labelMass_pos h n).le (div_nonneg hx (labelPartition_pos h).le)

theorem tailRow_summable (h : Ioi (0:ℝ)) (u : ℝ) : Summable (tailRow h u) := by
  have ht (k : ℕ) : 0 ≤ tail h k ∧ tail h k ≤ labelPartition h := by
    let f := fun m : ℕ+ => if k < m.val then thermalWeight (labelTemperature h) m else 0
    have H (m : ℕ+) : 0 ≤ f m ∧ f m ≤ thermalWeight (labelTemperature h) m := by
      dsimp [f]
      split <;> simp [(thermalWeight_pos (labelTemperature h) m).le]
    have hs := Summable.of_nonneg_of_le (fun m => (H m).1) (fun m => (H m).2) (thermalWeight_summable _)
    exact ⟨tsum_nonneg (fun m => (H m).1),hs.tsum_le_tsum (fun m => (H m).2) (thermalWeight_summable _)⟩
  apply Summable.of_nonneg_of_le (fun n => weighted_nonneg h n (ht _).1) _ (labelMass_hasSum h).summable
  intro n
  apply mul_le_of_le_one_right (labelMass_pos h n).le
  exact (div_le_one (labelPartition_pos h)).mpr (ht _).2

/-- The measured upper tail is the sum of its physical numerator rows. -/
theorem gap_tail_eq_tsum (h : Ioi (0:ℝ)) (u : ℝ) :
    1-gapCDF h (h.val*u) = ∑' n, tailRow h u n := by
  classical
  let μ : Measure ℝ := criticalGapLaw h
  let S := {q : ℕ+ × ℕ+ | ⌊Real.exp u*(q.2.val:ℝ)⌋₊ < q.1.val}
  have hh : 0 < h.val := h.property
  have he : (fun q => h.val/2*gapFrequency q) ⁻¹' Ioi (h.val*u) = S := by
    ext q
    have hm : 0 < (q.1.val:ℝ) := Nat.cast_pos.mpr q.1.pos
    have hn : 0 < (q.2.val:ℝ) := Nat.cast_pos.mpr q.2.pos
    change h.val*u < h.val/2*gapFrequency q ↔ ⌊Real.exp u*(q.2.val:ℝ)⌋₊ < q.1.val
    rw [show h.val/2*gapFrequency q = h.val*(energy q.1-energy q.2) by unfold gapFrequency; ring,
      mul_lt_mul_iff_right₀ hh,lt_sub_iff_add_lt,Nat.floor_lt (mul_nonneg (Real.exp_pos _).le hn.le)]
    change u+Real.log (q.2.val:ℝ) < Real.log (q.1.val:ℝ) ↔ _
    rw [← Real.exp_lt_exp,Real.exp_add,Real.exp_log hm,Real.exp_log hn]
  have hc := measureReal_add_measureReal_compl (μ := μ) (s := Iic (h.val*u)) measurableSet_Iic
  rw [compl_Iic,probReal_univ] at hc
  have hmass : 1-gapCDF h (h.val*u) = μ.real (Ioi (h.val*u)) := by
    change 1-μ.real (Iic (h.val*u)) = _
    linarith only [hc]
  rw [hmass]
  change ((Measure.map _ _) (Ioi (h.val*u))).toReal = _
  rw [Measure.map_apply Measurable.of_discrete measurableSet_Ioi,he]
  change (gibbsPairLaw (excessDamping h) (excessDamping_gt h) : Measure (ℕ+ × ℕ+)).real S = _
  rw [pair_event_rows]
  apply tsum_congr
  intro n
  unfold tailRow weighted tail
  rw [← tsum_div_const]
  apply congrArg (labelMass h n * ·)
  apply tsum_congr
  intro m
  by_cases hmn : ⌊Real.exp u*(n.val:ℝ)⌋₊ < m.val
  · simpa only [S,mem_setOf_eq,if_pos hmn] using labelMass_eq h m
  · simp only [S,mem_setOf_eq,if_neg hmn,zero_div]

theorem weighted_diagonal (h : Ioi (0:ℝ)) (n : ℕ+) :
    weighted h n (density h (n.val:ℝ)/2) = labelMass h n*labelMass h n/2 := by
  rw [weighted,density_label]
  have H := labelMass_eq h n
  calc
    _ = labelMass h n*(thermalWeight (labelTemperature h) n/labelPartition h)/2 := by ring
    _ = _ := by rw [← H]

theorem weighted_diagonal_hasSum (h : Ioi (0:ℝ)) :
    HasSum (fun n : ℕ+ => weighted h n (density h (n.val:ℝ)/2)) (collisionMass h/2) := by
  have H := labelMass_hasSum h
  have hs : Summable (fun n => labelMass h n*labelMass h n) := by
    apply Summable.of_nonneg_of_le (fun n => mul_self_nonneg _) _ H.summable
    intro n
    exact mul_le_of_le_one_right (labelMass_pos h n).le
      ((H.summable.le_tsum n fun i _ => (labelMass_pos h i).le).trans_eq H.tsum_eq)
  have he := hs.hasSum.div_const 2
  rw [← collisionMass_as_sum] at he
  exact he.congr_fun (weighted_diagonal h)

theorem weighted_integral_hasSum (h : Ioi (0:ℝ)) :
    HasSum (fun n : ℕ+ => weighted h n (primitive h (n.val:ℝ))) (rowIntegralFactor h) := by
  let b := fun n : ℕ+ => labelMass h n*(n.val:ℝ)^(-h.val)
  have hs : Summable b := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (labelMass_pos h n).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _ (labelMass_hasSum h).summable
    intro n
    exact mul_le_of_le_one_right (labelMass_pos h n).le
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos) (neg_nonpos.mpr h.property.le))
  have H := hs.hasSum.div_const (h.val*labelPartition h)
  apply H.congr_fun
  intro n
  dsimp [b,weighted,primitive]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem primitive_dilation (h : Ioi (0:ℝ)) (u : ℝ) (n : ℕ+) :
    primitive h (Real.exp u*(n.val:ℝ)) = primitive h (n.val:ℝ)*Real.exp (-h.val*u) := by
  rw [primitive,primitive,Real.mul_rpow (Real.exp_pos _).le (Nat.cast_nonneg _),
    Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,show u*(-h.val) = -h.val*u by ring]
  ring

#print axioms weighted_strictMono
#print axioms weighted_add
#print axioms weighted_mul
#print axioms weighted_nonneg
#print axioms tailRow_summable
#print axioms gap_tail_eq_tsum
#print axioms weighted_diagonal
#print axioms weighted_diagonal_hasSum
#print axioms weighted_integral_hasSum
#print axioms primitive_dilation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GibbsTail
