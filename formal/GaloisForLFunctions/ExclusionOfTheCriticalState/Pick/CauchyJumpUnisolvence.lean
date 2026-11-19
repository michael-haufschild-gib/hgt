import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.CauchyJumpMinors
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Logarithmic jump interpolation across the anchor

Dividing −log(1−zw) by zw removes its zero at the anchor. A primitive
of the resulting kernel in its first argument has derivative 1/(1−zw).
Rolle interlacing and the Cauchy determinant then prove unisolvence on
arbitrary distinct grids in (−1,1), including grids containing zero.
-/

noncomputable section
open Matrix Finset Set Real
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy

abbrev OpenDisk := Ioo (-1:ℝ) 1

/-- Normalized logarithmic response, including its removable value. -/
def logRatio (t : ℝ) := if t=0 then 1 else -log (1-t)/t

theorem diskKernel_factor (z w : ℝ) : diskKernel z w=(z*w)*logRatio (z*w) := by
  by_cases h : z*w=0
  · simp [diskKernel,logRatio,h]
  · rw [diskKernel,logRatio,if_neg h,mul_div_cancel₀ _ h]

private theorem log_deriv (z : ℝ) (h : z<1) :
    HasDerivAt (fun x : ℝ => -log (1-x)) (1-z)⁻¹ z := by
  have hd := (((hasDerivAt_id z).const_sub (1:ℝ)).log (sub_pos.mpr h).ne').neg
  change HasDerivAt (fun x : ℝ => -log (1-x)) (-(-1/(1-z))) z at hd
  simpa only [neg_div,neg_neg,one_div] using hd

theorem logRatio_continuousAt {t : ℝ} (ht : t<1) : ContinuousAt logRatio t := by
  by_cases h : t=0
  · subst t
    have H := (log_deriv 0 (by norm_num)).continuousAt_div
    have eq : Function.update (fun x : ℝ => (-log (1-x)- -log (1-0))/(x-0)) 0 ((1-(0:ℝ))⁻¹)=logRatio := by
      funext x
      by_cases hx : x=0 <;> simp [Function.update,logRatio,hx]
    rwa [eq] at H
  · apply ContinuousAt.congr_of_eventuallyEq
      ((log_deriv t ht).continuousAt.div continuousAt_id h)
    filter_upwards [eventually_ne_nhds h] with x hx
    simp [logRatio,hx]

private theorem disk_product {z w : ℝ} (hz : z ∈ OpenDisk) (hw : w ∈ OpenDisk) : z*w<1 := by
  have a := abs_lt.mpr hz
  have b := abs_lt.mpr hw
  exact (le_abs_self _).trans_lt (by rw [abs_mul]; exact (mul_le_mul_of_nonneg_left b.le (abs_nonneg z)).trans_lt (by simpa using a))

private theorem primitive_deriv {w z : ℝ} (hw : w∈OpenDisk) (hz : z∈OpenDisk) :
    HasDerivAt (fun x => x*logRatio (x*w)) (1-z*w)⁻¹ z := by
  by_cases h : w=0
  · subst w
    have hzero : logRatio 0 = 1 := by simp [logRatio]
    simp only [mul_zero,hzero,mul_one,sub_zero,inv_one]
    exact hasDerivAt_id z
  have he : (fun x => x*logRatio (x*w))=(fun x => -log (1-x*w)/w) := by
    funext x
    apply (eq_div_iff h).mpr
    calc
      _ = (x*w)*logRatio (x*w) := by ring
      _ = _ := (diskKernel_factor x w).symm
  rw [he]
  have hd := (((log_deriv (z*w) (disk_product hz hw)).comp z ((hasDerivAt_id z).mul_const w)).div_const w)
  change HasDerivAt (fun x : ℝ => -log (1-x*w)/w) (((1-z*w)⁻¹*(1*w))/w) z at hd
  have cancel : ((1-z*w)⁻¹*(1*w))/w = (1-z*w)⁻¹ := by rw [one_mul,div_eq_iff h]
  rwa [cancel] at hd

private def cayley (x : ℝ) := (1+x)/(1-x)

private theorem cayley_pos {x : ℝ} (h : x∈OpenDisk) : 0<cayley x :=
  div_pos (by linarith only [h.1]) (sub_pos.mpr h.2)

private theorem cayley_inj {x y : ℝ} (hx : x∈OpenDisk) (hy : y∈OpenDisk) :
    cayley x=cayley y → x=y := by
  intro h
  have e := (div_eq_div_iff (sub_pos.mpr hx.2).ne' (sub_pos.mpr hy.2).ne').mp h
  linarith only [e]

/-- Independent signed disk grids give an invertible Cauchy derivative matrix. -/
theorem derivative_det_ne {n : ℕ} (z w : Fin n ↪ OpenDisk) :
    (Matrix.of fun i j => (1-(z i).val*(w j).val)⁻¹).det≠0 := by
  let a := fun i => cayley (z i).val
  let b := fun j => cayley (w j).val
  have ha : Function.Injective a := fun i j h => z.injective (Subtype.ext (cayley_inj (z i).property (z j).property h))
  have hb : Function.Injective b := fun i j h => w.injective (Subtype.ext (cayley_inj (w i).property (w j).property h))
  have sums (i j) : a i+b j≠0 := (add_pos (cayley_pos (z i).property) (cayley_pos (w j).property)).ne'
  have hc := HTGeometry.det_cauchyMatrix a b sums
  have hn : (HTGeometry.cauchyMatrix a b).det≠0 := by
    intro e
    rw [e,zero_mul] at hc
    exact (prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j h =>
      mul_ne_zero (sub_ne_zero.mpr (ha.ne (mem_Ioi.mp h).ne)) (sub_ne_zero.mpr (hb.ne (mem_Ioi.mp h).ne))) hc.symm
  let A := HTGeometry.cauchyMatrix a b
  have he : (Matrix.of fun i j => (1-(z i).val*(w j).val)⁻¹) =
      Matrix.of fun i j => (2/(1-(z i).val))*(Matrix.of fun u v => (1-(w v).val)⁻¹*A u v) i j := by
    ext i j
    simp only [Matrix.of_apply,A,HTGeometry.cauchyMatrix_apply]
    have hx := (sub_pos.mpr (z i).property.2).ne'
    have hy := (sub_pos.mpr (w j).property.2).ne'
    have cancel (x y U : ℝ) (hx : 1-x ≠ 0) (hy : 1-y ≠ 0) (hxy : 1-x*y ≠ 0)
        (hU : U ≠ 0) (e : U*((1-x)*(1-y)) = 2*(1-x*y)) :
        (1-x*y)⁻¹ = 2/(1-x)*((1-y)⁻¹*U⁻¹) := by
      field_simp [hx,hy,hxy,hU]
      linear_combination e
    apply cancel _ _ _ hx hy (sub_pos.mpr (disk_product (z i).property (w j).property)).ne' (sums i j)
    dsimp [a,b,cayley]
    field_simp [hx,hy]
    ring
  rw [he,det_mul_column,det_mul_row]
  exact mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => div_ne_zero (by norm_num) (sub_pos.mpr (z i).property.2).ne')
    (mul_ne_zero (prod_ne_zero_iff.mpr fun j _ => inv_ne_zero (sub_pos.mpr (w j).property.2).ne') hn)

/-- Rolle interlacing supplies one fewer zero than the number of distinct knots.
When zero is an original knot, its derivative zero compensates for the repeated knot. -/
private theorem interleaved_count (A T : Finset ℝ)
    (h : (insert 0 A).card ≤ (T \ insert 0 A).card+1)
    (hzero : (0:ℝ) ∈ A → 0 ∈ T) : A.card ≤ T.card := by
  classical
  by_cases hz : (0:ℝ) ∈ A
  · rw [Finset.insert_eq_of_mem hz] at h
    have keep : T \ A ⊆ T.erase 0 := by
      intro x hx
      obtain ⟨ht,ha⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_erase.mpr ⟨fun he => ha (he ▸ hz),ht⟩
    have hc := Finset.card_le_card keep
    rw [Finset.card_erase_of_mem (hzero hz)] at hc
    have ht : 0 < T.card := Finset.card_pos.mpr ⟨0,hzero hz⟩
    omega
  · rw [Finset.card_insert_of_notMem hz] at h
    have hc : (T \ insert 0 A).card ≤ T.card :=
      Finset.card_le_card (fun _ hx => (Finset.mem_sdiff.mp hx).1)
    omega

private theorem rolle_zeros (A : Finset ℝ) (F G : ℝ → ℝ)
    (dF : ∀ x ∈ OpenDisk, HasDerivAt F (G x) x)
    (inside : ∀ {x : ℝ}, x ∈ insert 0 A → x ∈ OpenDisk)
    (zeros : ∀ {x : ℝ}, x ∈ insert 0 A → F x = 0)
    (atZero : (0:ℝ) ∈ A → G 0 = 0) :
    ∃ T : Finset ℝ, A.card ≤ T.card ∧ ∀ x ∈ T, x ∈ OpenDisk ∧ G x = 0 := by
  classical
  let S := insert (0:ℝ) A
  let P := {p : S × S // (p.1:ℝ)<(p.2:ℝ)}
  have inter (p : P) : ∃ x : ℝ, x∈Ioo (p.val.1:ℝ) (p.val.2:ℝ) ∧ x∈OpenDisk ∧ G x=0 := by
    have segment {x : ℝ} (hx : x∈Icc (p.val.1:ℝ) (p.val.2:ℝ)) : x∈OpenDisk :=
      ⟨(inside p.val.1.property).1.trans_le hx.1,hx.2.trans_lt (inside p.val.2.property).2⟩
    obtain ⟨x,hx,e⟩ := exists_hasDerivAt_eq_zero p.property
      (fun x hx => (dF x (segment hx)).continuousAt.continuousWithinAt)
      ((zeros p.val.1.property).trans (zeros p.val.2.property).symm)
      (fun x hx => dF x (segment ⟨hx.1.le,hx.2.le⟩))
    exact ⟨x,hx,segment ⟨hx.1.le,hx.2.le⟩,e⟩
  choose pick loc inDisk isZero using inter
  let T := (insert (0:ℝ) (Finset.univ.image pick)).filter (fun x => x∈OpenDisk ∧ G x=0)
  have interlace : S.card≤(T \ S).card+1 := by
    apply card_le_sdiff_of_interleaved
    intro x hx y hy hxy _
    let p : P := ⟨(⟨x,hx⟩,⟨y,hy⟩),hxy⟩
    exact ⟨pick p,mem_filter.mpr ⟨mem_insert_of_mem (mem_image_of_mem _ (mem_univ p)),inDisk p,isZero p⟩,
      (loc p).1,(loc p).2⟩
  refine ⟨T,interleaved_count A T interlace (fun hA => ?_),fun _ hx => (mem_filter.mp hx).2⟩
  exact mem_filter.mpr ⟨mem_insert_self _ _,inside (mem_insert_self _ _),atZero hA⟩

private theorem null_coefficients {n : ℕ} (z w : Fin n ↪ OpenDisk) (c : Fin n → ℝ)
    (h : ∀ i, ∑ j, c j*logRatio ((z i).val*(w j).val)=0) : c=0 := by
  classical
  let A : Finset ℝ := Finset.univ.image (fun i => (z i).val)
  let S := insert (0:ℝ) A
  let F := fun x : ℝ => ∑ j, c j*(x*logRatio (x*(w j).val))
  let G := fun x : ℝ => ∑ j, c j*(1-x*(w j).val)⁻¹
  have dF (x : ℝ) (hx : x∈OpenDisk) : HasDerivAt F (G x) x :=
    HasDerivAt.fun_sum fun j _ => (primitive_deriv (w j).property hx).const_mul (c j)
  have inside {x} (hx : x∈S) : x∈OpenDisk := by
    rcases mem_insert.mp hx with e|e
    · rw [e]; constructor <;> norm_num
    · obtain ⟨i,_,rfl⟩ := mem_image.mp e
      exact (z i).property
  have zeros {x} (hx : x∈S) : F x=0 := by
    rcases mem_insert.mp hx with e|e
    · simp [F,e]
    · obtain ⟨i,_,rfl⟩ := mem_image.mp e
      calc
        _ = (z i).val*∑ j, c j*logRatio ((z i).val*(w j).val) := by
          simp only [F,mul_sum]; exact sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [h,mul_zero]
  have ca : A.card=n := (card_image_of_injective _ (Subtype.val_injective.comp z.injective)).trans (by simp)
  have atZero (hA : (0:ℝ) ∈ A) : G 0 = 0 := by
    obtain ⟨i,_,ei⟩ := Finset.mem_image.mp hA
    simpa [G,ei,logRatio] using h i
  obtain ⟨T,hcard,hT⟩ := rolle_zeros A F G dF inside zeros atZero
  have enough : n ≤ T.card := ca ▸ hcard
  let e := (Fin.castLEOrderEmb enough).trans (T.orderIsoOfFin rfl).toOrderEmbedding
  let t : Fin n ↪ OpenDisk := ⟨fun i => ⟨(e i).val,(hT _ (e i).property).1⟩,
    fun _ _ he => e.injective (Subtype.ext (congrArg (fun x : OpenDisk => x.val) he))⟩
  let M := Matrix.of fun i j => (1-(t i).val*(w j).val)⁻¹
  have inv : IsUnit M := M.isUnit_iff_isUnit_det.mpr (derivative_det_ne t w).isUnit
  apply Matrix.mulVec_injective_iff_isUnit.mpr inv
  rw [Matrix.mulVec_zero]
  funext i
  change (∑ j, (1-(e i).val*(w j).val)⁻¹*c j) = 0
  calc
    _ = ∑ j, c j*(1-(e i).val*(w j).val)⁻¹ := Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ = 0 := (hT _ (e i).property).2

/-- Every normalized logarithmic cross matrix on distinct signed contrasts
is nonsingular; neither grid needs to stay on one side of the anchor. -/
theorem normalized_det_ne {n : ℕ} (z w : Fin n ↪ OpenDisk) :
    (Matrix.of fun i j => logRatio ((z i).val*(w j).val)).det≠0 := by
  let M := Matrix.of fun i j => logRatio ((z i).val*(w j).val)
  apply (M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp ?_)).ne_zero
  intro u v h
  apply sub_eq_zero.mp
  apply null_coefficients z w
  intro i
  have e : M.mulVec (u-v)=0 := by rw [Matrix.mulVec_sub,h,sub_self]
  simpa only [M,Matrix.of_apply,mulVec,dotProduct,Pi.zero_apply,mul_comm] using congrFun e i

#print axioms logRatio_continuousAt
#print axioms derivative_det_ne
#print axioms normalized_det_ne
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.LogCauchy
