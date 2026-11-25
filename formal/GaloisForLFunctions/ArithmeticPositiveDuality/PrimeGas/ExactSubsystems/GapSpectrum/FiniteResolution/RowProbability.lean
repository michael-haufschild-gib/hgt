import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Continuum.GapLimit
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.Rows
import GaloisForLFunctions.HTGeometry.CountFormationSplit

/-! # Exact row sums for probabilities of arithmetic gap bands -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Set MeasureTheory

def labelTemperature (h : Ioi (0:ℝ)) : TraceTemperature := ⟨1+h.val,lt_add_of_pos_right _ h.property⟩

def labelPartition (h : Ioi (0:ℝ)) : ℝ := ∑' n, thermalWeight (labelTemperature h) n

theorem labelPartition_pos (h : Ioi (0:ℝ)) : 0 < labelPartition h :=
  (thermalWeight_pos _ 1).trans_le ((thermalWeight_summable _).le_tsum 1 fun i _ => (thermalWeight_pos _ i).le)

def labelMass (h : Ioi (0:ℝ)) (n : ℕ+) : ℝ :=
  (commonScaleWeight (excessDamping h/2) n).re

theorem labelMass_eq (h : Ioi (0:ℝ)) (n : ℕ+) :
    labelMass h n = thermalWeight (labelTemperature h) n / labelPartition h := by
  have ht : 4*(excessDamping h/2) = (labelTemperature h).val := by unfold excessDamping labelTemperature; ring
  have he : heat ((labelTemperature h).val:ℂ) n = (thermalWeight (labelTemperature h) n:ℂ) := by
    simp only [thermalWeight,heat,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  rw [labelMass,commonScaleWeight,ht,← thermalWeight_partition (labelTemperature h),he,Complex.div_ofReal_re,Complex.ofReal_re,labelPartition]

theorem labelMass_pos (h : Ioi (0:ℝ)) (n : ℕ+) : 0 < labelMass h n := by
  rw [labelMass_eq]
  exact div_pos (thermalWeight_pos _ _) (labelPartition_pos h)

theorem labelMass_hasSum (h : Ioi (0:ℝ)) : HasSum (labelMass h) 1 :=
  commonScaleReal_hasSum (by have := excessDamping_gt h; linarith)

private theorem pair_atom_real (h : Ioi (0:ℝ)) (q : ℕ+ × ℕ+) :
    (gibbsPairLaw (excessDamping h) (excessDamping_gt h) : Measure (ℕ+ × ℕ+)).real {q} =
      labelMass h q.1 * labelMass h q.2 := by
  have hx := excessDamping_gt h
  have hh : 1/4 < excessDamping h/2 := by linarith
  obtain ⟨a,ha,hea⟩ := commonScaleWeight_positive hh q.1
  obtain ⟨b,hb,heb⟩ := commonScaleWeight_positive hh q.2
  rw [measureReal_def,gibbsPairLaw_atom,gapAmplitude_product hx]
  simp only [labelMass,← hea,← heb,← Complex.ofReal_mul,Complex.ofReal_re,ENNReal.toReal_ofReal (mul_pos ha hb).le]

open scoped Classical in
/-- A test on both Gibbs samples is the sum of its conditional numerator rows. -/
theorem pair_event_rows (h : Ioi (0:ℝ)) (S : Set (ℕ+ × ℕ+)) :
    (gibbsPairLaw (excessDamping h) (excessDamping_gt h) : Measure (ℕ+ × ℕ+)).real S =
      ∑' n, labelMass h n * ∑' m, if (m,n) ∈ S then labelMass h m else 0 := by
  let μ : Measure (ℕ+ × ℕ+) := gibbsPairLaw (excessDamping h) (excessDamping_gt h)
  let f := S.indicator (fun q => μ.real {q})
  let e := Equiv.prodComm ℕ+ ℕ+
  have hf : Summable f := (HTGeometry.hasSum_measure_singleton_toReal μ).summable.indicator S
  have hswap := (e.summable_iff (f := f)).mpr hf
  have hs : MeasurableSet S := .of_discrete
  have hi := (integrable_const (μ := μ) (1:ℝ)).indicator hs
  change μ.real S = _
  calc
    _ = ∑' q, f q := by
      rw [← integral_indicator_one hs]
      change (∫ q, S.indicator (fun _ => (1:ℝ)) q ∂μ) = _
      rw [integral_countable hi]
      apply tsum_congr
      intro q
      by_cases hq : q ∈ S
      · simp only [f,indicator_of_mem hq,smul_eq_mul,mul_one]
      · simp only [f,indicator_of_notMem hq,smul_zero]
    _ = ∑' (n : ℕ+) (m : ℕ+), f (m,n) := (e.tsum_eq f).symm.trans hswap.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro n
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      by_cases hm : (m,n) ∈ S
      · simp only [f,indicator_of_mem hm,if_pos hm]
        exact (pair_atom_real h (m,n)).trans (mul_comm _ _)
      · simp only [f,indicator_of_notMem hm,if_neg hm,mul_zero]

private def rowIndex (n : ℕ+) : ℕ ↪ ℕ+ where
  toFun i := ⟨n.val+(i+1),by omega⟩
  inj' := by intro i j he; have hh := congrArg PNat.val he; change n.val+(i+1) = n.val+(j+1) at hh; omega

private theorem row_support {t : ℝ} (ht : 0 ≤ t) (n m : ℕ+) :
    m ∈ (Finset.range ⌊(Real.exp t-1)*(n.val:ℝ)⌋₊).map (rowIndex n) ↔
      energy m-energy n ∈ Ioc 0 t := by
  let R := (Real.exp t-1)*(n.val:ℝ)
  have hR : 0 ≤ R := mul_nonneg (sub_nonneg.mpr (Real.one_le_exp ht)) (Nat.cast_nonneg _)
  have hn : (0:ℝ) < n.val := Nat.cast_pos.mpr n.pos
  have hm : (0:ℝ) < m.val := Nat.cast_pos.mpr m.pos
  have hlog : energy m-energy n ∈ Ioc 0 t ↔ n.val < m.val ∧ (m.val:ℝ) ≤ Real.exp t*n.val := by
    change 0 < Real.log (m.val:ℝ)-Real.log (n.val:ℝ) ∧
      Real.log (m.val:ℝ)-Real.log (n.val:ℝ) ≤ t ↔ _
    rw [sub_pos,Real.log_lt_log_iff hn hm,sub_le_iff_le_add,← Real.exp_le_exp,Real.exp_add,Real.exp_log hm,Real.exp_log hn,Nat.cast_lt]
  rw [hlog,Finset.mem_map]
  constructor
  · rintro ⟨i,hi,rfl⟩
    have hd : i+1 ≤ ⌊R⌋₊ := Finset.mem_range.mp hi
    have hcast := (Nat.le_floor_iff hR).mp hd
    change n.val < n.val+(i+1) ∧ ((n.val+(i+1):ℕ):ℝ) ≤ Real.exp t*n.val
    refine ⟨by omega,?_⟩
    push_cast
    dsimp [R] at hcast
    push_cast at hcast
    linarith only [hcast]
  · rintro ⟨hmn,hupper⟩
    let i := m.val-n.val-1
    have he : m.val = n.val+(i+1) := by dsimp [i]; omega
    have heR : (m.val:ℝ) = n.val+((i+1:ℕ):ℝ) := by exact_mod_cast he
    have hd : i+1 ≤ ⌊R⌋₊ := (Nat.le_floor_iff hR).mpr (by dsimp [R]; linarith only [heR,hupper])
    exact ⟨i,Finset.mem_range.mpr hd,PNat.coe_injective he.symm⟩

/-- The probability of a positive log-gap band in one fixed denominator row. -/
theorem conditional_row_probability (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) (n : ℕ+) :
    (∑' m, if energy m-energy n ∈ Ioc 0 t then labelMass h m else 0) =
      positiveGapRow h.val t n / labelPartition h := by
  classical
  let F := (Finset.range ⌊(Real.exp t-1)*(n.val:ℝ)⌋₊).map (rowIndex n)
  rw [tsum_eq_sum (s := F) (fun m hm => if_neg (fun hmem => hm ((row_support ht n m).mpr hmem)))]
  calc
    _ = ∑ m ∈ F, labelMass h m := Finset.sum_congr rfl (fun m hm => if_pos ((row_support ht n m).mp hm))
    _ = _ := by
      dsimp only [F]
      rw [Finset.sum_map,positiveGapRow,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [labelMass_eq]
      change Real.exp (-(1+h.val)*Real.log ((n.val+(i+1):ℕ):ℝ)) / labelPartition h = _
      rw [Nat.cast_add]

/-- An actual rescaled Gibbs measurement, cut at h*t, equals the normalized row sum. -/
theorem positive_band_probability (h : Ioi (0:ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    (criticalGapLaw h : Measure ℝ).real (Ioc 0 (h.val*t)) =
      ∑' n, labelMass h n * (positiveGapRow h.val t n / labelPartition h) := by
  classical
  let x := excessDamping h
  let S := {q : ℕ+ × ℕ+ | energy q.1-energy q.2 ∈ Ioc 0 t}
  have hh : 0 < h.val := h.property
  have he : (fun q => h.val/2*gapFrequency q) ⁻¹' Ioc 0 (h.val*t) = S := by
    ext q
    have hf : h.val/2*gapFrequency q = h.val*(energy q.1-energy q.2) := by unfold gapFrequency; ring
    simp only [Set.mem_preimage,Set.mem_Ioc,Set.mem_setOf_eq,S,hf,mul_pos_iff_of_pos_left hh,
      mul_le_mul_iff_right₀ hh]
  have hm : (criticalGapLaw h : Measure ℝ).real (Ioc 0 (h.val*t)) =
      (gibbsPairLaw x (excessDamping_gt h) : Measure (ℕ+ × ℕ+)).real S := by
    change ((Measure.map _ _) (Ioc 0 (h.val*t))).toReal = _
    rw [Measure.map_apply Measurable.of_discrete measurableSet_Ioc,he]
    rfl
  rw [hm,pair_event_rows]
  apply tsum_congr
  intro n
  apply congrArg (labelMass h n * ·)
  refine Eq.trans (tsum_congr fun m => ?_) (conditional_row_probability h ht n)
  by_cases hm : energy m-energy n ∈ Ioc 0 t <;> simp only [S,mem_setOf_eq,hm,if_true,if_false]

#print axioms labelPartition_pos
#print axioms labelMass_eq
#print axioms labelMass_pos
#print axioms labelMass_hasSum
#print axioms pair_event_rows
#print axioms conditional_row_probability
#print axioms positive_band_probability

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
