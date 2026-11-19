import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.CauchyJumpUnisolvence

/-!
# Signs of cross minors on arbitrary ordered probe grids

The normalized logarithmic jump kernel is strictly totally positive on
the full square (−1,1)². Dividing out each signed contrast explains the
orientation of every unnormalized cross minor, including the exact
singularity when a row or column equals the reference momentum.
-/

noncomputable section
open Matrix Finset Set Real
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
open HilbertMetric.CauchyDephasing

private def shift (t x : ℝ) := (1-t/2)*x+t/2

private theorem shift_mono {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : StrictMono (shift t) := by
  intro x y h
  have hs : 0 < 1-t/2 := by linarith only [ht.2]
  unfold shift
  linarith only [mul_lt_mul_of_pos_left h hs]

private theorem shift_inside {t x : ℝ} (ht : t∈Icc (0:ℝ) 1) (hx : x∈OpenDisk) :
    shift t x∈OpenDisk := by
  have hlo := shift_mono ht hx.1
  have hhi := shift_mono ht hx.2
  constructor <;> unfold shift at * <;> linarith only [hlo,hhi,ht.1]

private def shifted {n : ℕ} (z : Fin n ↪o OpenDisk) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    Fin n ↪o OpenDisk :=
  OrderEmbedding.ofStrictMono (fun i => ⟨shift t (z i).val,shift_inside ht (z i).property⟩)
    (fun _ _ he => shift_mono ht (z.strictMono he))

private def positiveEnd {n : ℕ} (z : Fin n ↪o OpenDisk) : ContrastGrid n :=
  OrderEmbedding.ofStrictMono (fun i => ⟨shift 1 (z i).val,by
    constructor
    · unfold shift; linarith only [(z i).property.1]
    · exact (shift_inside (show (1:ℝ)∈Icc 0 1 by constructor <;> norm_num) (z i).property).2⟩)
    (fun _ _ h => shift_mono (show (1:ℝ)∈Icc 0 1 by constructor <;> norm_num) (z.strictMono h))

private theorem factor_det {n : ℕ} (z w : Fin n → ℝ) :
    (Matrix.of fun i j => diskKernel (z i) (w j)).det =
      (∏ i, z i)*((∏ j, w j)*(Matrix.of fun i j => logRatio (z i*w j)).det) := by
  have he : (Matrix.of fun i j => diskKernel (z i) (w j)) =
      Matrix.of fun i j => z i*(Matrix.of fun u v => w v*(Matrix.of fun a b => logRatio (z a*w b)) u v) i j := by
    ext i j
    simp only [Matrix.of_apply,diskKernel_factor,mul_assoc]
  rw [he,det_mul_column,det_mul_row]

/-- Every ordered normalized cross minor is strictly positive even when
the row and column grids straddle their common anchor differently. -/
theorem normalized_det_pos {n : ℕ} (z w : Fin n ↪o OpenDisk) :
    0<(Matrix.of fun i j => logRatio ((z i).val*(w j).val)).det := by
  let M := fun t => Matrix.of fun i j => logRatio (shift t (z i).val*shift t (w j).val)
  have hc : ContinuousOn (fun t => (M t).det) (Icc (0:ℝ) 1) := by
    intro t ht
    apply continuous_det.continuousAt.comp_continuousWithinAt
    apply continuousWithinAt_pi.mpr
    intro i
    apply continuousWithinAt_pi.mpr
    intro j
    have hprod : shift t (z i).val*shift t (w j).val<1 := by
      have a := abs_lt.mpr (shift_inside ht (z i).property)
      have b := abs_lt.mpr (shift_inside ht (w j).property)
      apply (le_abs_self _).trans_lt
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left b.le (abs_nonneg _)).trans_lt (by simpa using a)
    exact (logRatio_continuousAt hprod).comp_continuousWithinAt (by unfold shift; fun_prop)
  have hn (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : (M t).det≠0 :=
    normalized_det_ne ⟨shifted z t ht,(shifted z t ht).injective⟩
      ⟨shifted w t ht,(shifted w t ht).injective⟩
  have hp : 0<(M 1).det := by
    have h := cross_det_pos (positiveEnd z) (positiveEnd w)
    rw [factor_det] at h
    exact pos_of_mul_pos_right (pos_of_mul_pos_right h
      (prod_nonneg fun i _ => (positiveEnd z i).property.1.le))
      (prod_nonneg fun j _ => (positiveEnd w j).property.1.le)
  have hstart : 0<(M 0).det := by
    by_contra! h
    obtain ⟨t,ht,e⟩ := intermediate_value_Icc zero_le_one hc (show (0:ℝ)∈Icc ((M 0).det) ((M 1).det) from ⟨h,hp.le⟩)
    exact hn t ht e
  simpa only [M,shift,zero_div,sub_zero,one_mul,add_zero] using hstart

private def contrastGrid {n : ℕ} (o : ℝ) (r : Fin n ↪o ℝ) : Fin n ↪o OpenDisk :=
  OrderEmbedding.ofStrictMono (fun i => ⟨contrast (r i) o,abs_lt.mp (contrast_inside (r i) o)⟩)
    ((ordered_contrast o).comp r.strictMono)

/-- The sign of a centered cross covariance is exactly the sign of the
product of its row and column contrasts. -/
theorem cross_covariance_orientation {n : ℕ} (o : ℝ) (r s : Fin n ↪o ℝ) :
    ∃ b : ℝ, 0<b ∧
      (Matrix.of fun i j => cost (r i) o+cost (s j) o-cost (r i) (s j)).det =
        (∏ i, contrast (r i) o)*(∏ j, contrast (s j) o)*b := by
  refine ⟨_,normalized_det_pos (contrastGrid o r) (contrastGrid o s),?_⟩
  simp only [anchored_log,factor_det,mul_assoc]
  rfl

theorem cross_covariance_singular_iff {n : ℕ} (o : ℝ) (r s : Fin n ↪o ℝ) :
    (Matrix.of fun i j => cost (r i) o+cost (s j) o-cost (r i) (s j)).det=0 ↔
      (∃ i, r i=o) ∨ (∃ j, s j=o) := by
  obtain ⟨b,hb,e⟩ := cross_covariance_orientation o r s
  rw [e]
  simp only [mul_eq_zero,hb.ne',or_false,prod_eq_zero_iff,mem_univ,true_and,contrast_eq_zero_iff]

#print axioms normalized_det_pos
#print axioms cross_covariance_orientation
#print axioms cross_covariance_singular_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
