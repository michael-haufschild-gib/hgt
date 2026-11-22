import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderCounting
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RefinementOperators
import GaloisForLFunctions.HTGeometry.LpDiagonalSchattenEnergy

/-!
# Exact count of the singular values above a square-shell threshold

Each scalar coordinate contributes one singular value. Strict thresholds
at successive square products separate all the possibly degenerate levels
of the heat-weighted error.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary MeasureTheory
open scoped Classical ENNReal

private theorem diagonal_count {ι : Type} [Countable ι] (a : ι → ℂ) {B : ℝ} (hB : 0 ≤ B) (ha : ∀ i, ‖a i‖ ≤ B)
    {z : ℝ} (hz : 0 < z) :
    Measure.count {n : ℕ | z < _root_.RHTower.approxNumber (lpDiagonalCLM a hB ha) n} =
      ∑' i, if z < ‖a i‖ then (1:ℝ≥0∞) else 0 := by
  let T (i : ι) := a i • ContinuousLinearMap.id ℂ ℂ
  have hb (i : ι) : ‖T i‖ ≤ B := by simpa only [T,norm_smul,ContinuousLinearMap.norm_id,mul_one] using ha i
  have he : _root_.RHTower.rectangularBlockOperator T hB hb = lpDiagonalCLM a hB ha := by ext f i; rfl
  have h := HTGeometry.count_lt_rectApproxNumber_rectangularBlockOperator T hB hb
    (fun _ => isCompactOperator_of_locallyCompactSpace_rng _) hz
  rw [he] at h
  refine h.trans (tsum_congr fun i => ?_)
  by_cases hi : z < ‖a i‖
  · have hs : {n : ℕ | z < _root_.RHTower.rectApproxNumber (T i) n} = {0} := by
      ext n
      by_cases hn : n = 0 <;> simp [T,HTGeometry.rectApproxNumber_complex_scalar,hn,hi,hz.not_gt]
    rw [hs,Measure.count_singleton,if_pos hi]
  · have hs : {n : ℕ | z < _root_.RHTower.rectApproxNumber (T i) n} = ∅ := by
      ext n
      by_cases hn : n = 0 <;> simp [T,HTGeometry.rectApproxNumber_complex_scalar,hn,hi,hz.not_gt]
    rw [hs,measure_empty,if_neg hi]

def squareThreshold (s : ℂ) (X : ℕ) := ‖heat s ((⟨X+1,Nat.succ_pos X⟩ : ℕ+)^2)‖

private theorem heat_strict {s : ℂ} (hs : 0 < s.re) (a b : ℕ+) :
    ‖heat s a‖ < ‖heat s b‖ ↔ b.val < a.val := by
  rw [norm_heat,norm_heat,Real.exp_lt_exp]
  have mono {c d : ℕ+} (h : c.val ≤ d.val) : energy c ≤ energy d :=
    Real.log_le_log (Nat.cast_pos.mpr c.pos) (by exact_mod_cast h)
  constructor
  · intro h
    by_contra! hn
    exact h.not_ge (mul_le_mul_of_nonpos_left (mono hn) (neg_nonpos.mpr hs.le))
  · intro h
    exact mul_lt_mul_of_neg_left (Real.log_lt_log (Nat.cast_pos.mpr b.pos) (by exact_mod_cast h)) (neg_lt_zero.mpr hs)

private theorem above_threshold (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) (X : ℕ) (y : Word) :
    squareThreshold s.val X < ‖tailMultiplier t j s.val y‖ ↔ remainder t j y ∧ (y false*y true).val ≤ X^2 := by
  have ht : 0 < squareThreshold s.val X := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  by_cases hy : remainder t j y
  · obtain ⟨x,hx⟩ := leastWords_nonempty t
    obtain ⟨p,rfl⟩ := (remainder_iff t j ⟨x,hx⟩ y).mp hy
    rw [tailMultiplier,if_pos hy,and_iff_right hy,wordHeat_total,Fintype.prod_bool,mul_comm _ (tailWord _ _ _ _ false),
      squareThreshold,heat_strict s.property,tail_square]
    let N := ((tailRadix t j)^(p.2.1+1)*p.2.2).val
    change N^2 < (X+1)^2 ↔ N^2 ≤ X^2
    rw [Nat.pow_lt_pow_iff_left (by norm_num : (2:ℕ) ≠ 0),Nat.pow_le_pow_iff_left (by norm_num : (2:ℕ) ≠ 0)]
    exact Nat.lt_succ_iff
  · simp [tailMultiplier,hy,ht.not_gt]

theorem singular_count (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) (X : ℕ) :
    Measure.count {n : ℕ | squareThreshold s.val X <
      _root_.RHTower.approxNumber (dampedRemainder t j ⟨s.val,s.property.le⟩) n} =
      (Nat.card (countingStates t j X) : ℝ≥0∞) := by
  let S := {y : Word | remainder t j y ∧ (y false*y true).val ≤ X^2}
  let e : S ≃ countingStates t j X :=
    ⟨fun y => ⟨⟨y.val,y.property.1⟩,y.property.2⟩,fun y => ⟨y.val.val,y.val.property,y.property⟩,
      fun _ => rfl,fun _ => rfl⟩
  have ht : 0 < squareThreshold s.val X := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  rw [damped_diagonal,diagonal_count _ _ _ ht]
  calc
    _ = ∑' y, S.indicator (fun _ => (1:ℝ≥0∞)) y := tsum_congr fun y => by
      simp only [Set.indicator_apply,above_threshold,S,Set.mem_setOf_eq]
    _ = ∑' _ : S, (1:ℝ≥0∞) := (tsum_subtype S _).symm
    _ = ∑' _ : countingStates t j X, (1:ℝ≥0∞) := e.tsum_eq (fun _ => (1:ℝ≥0∞))
    _ = _ := by
      letI := Fintype.ofFinite (countingStates t j X)
      simp [Nat.card_eq_fintype_card]

/-- The cumulative occupation count gives the exact index at which a singular value crosses the cutoff. -/
theorem threshold_lt_singular_iff (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 0 < z.re}) (X n : ℕ) :
    squareThreshold s.val X < _root_.RHTower.approxNumber (dampedRemainder t j ⟨s.val,s.property.le⟩) n ↔
      n < Nat.card (countingStates t j X) := by
  have h := singular_count t j s X
  have ha := _root_.RHTower.approxNumber_antitone (dampedRemainder t j ⟨s.val,s.property.le⟩)
  constructor
  · intro hn
    have hh := HTGeometry.le_count_lt_of_lt ha hn
    rw [h] at hh
    exact_mod_cast hh
  · intro hn
    by_contra! hle
    have hh := HTGeometry.count_lt_le_of_le ha hle
    rw [h] at hh
    exact hn.not_ge (by exact_mod_cast hh)

#print axioms singular_count
#print axioms threshold_lt_singular_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
