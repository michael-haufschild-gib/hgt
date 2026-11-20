import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheNumberOfMeasurementsAtEachZeroDepth
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Exact covering numbers of finite zero-displacement samples

Each coordinate fills an interval. A closed ball in the supremum metric
can cover a cell of width twice its radius in every coordinate. Conversely,
a product of separated points forces one codeword per cell, including when
an interval length is an exact multiple of the cell width. The resulting
product is both the internal and external minimum.
-/

noncomputable section
open Finset Set Metric
open scoped NNReal ENNReal
namespace GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa

private def bins (d h : ℝ) := max 1 ⌈d/h⌉₊

private theorem bins_pos (d h : ℝ) : 0 < bins d h := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

private theorem unit_cell {b : ℕ} (hb : 0 < b) {z : ℝ} (hz : 0 ≤ z) (ht : z ≤ b) :
    ∃ j : Fin b, (j.val:ℝ) ≤ z ∧ z ≤ j.val+1 := by
  rcases b with _|b
  · omega
  by_cases hn : ⌊z⌋₊ < b+1
  · exact ⟨⟨_,hn⟩,Nat.floor_le hz,(Nat.lt_floor_add_one z).le⟩
  · have he := ht.antisymm ((Nat.cast_le.mpr (le_of_not_gt hn)).trans (Nat.floor_le hz))
    refine ⟨⟨b,Nat.lt_succ_self _⟩,?_,?_⟩ <;> rw [he] <;> push_cast <;> simp

private def center (d h : ℝ) (j : Fin (bins d h)) := min d (-d+(2*(j.val:ℝ)+1)*h)

private theorem center_inside {d h : ℝ} (hd : 0 ≤ d) (hh : 0 < h) (j : Fin (bins d h)) :
    |center d h j| ≤ d := by
  apply abs_le.mpr
  exact ⟨le_min (neg_le_self hd) (le_add_of_nonneg_right (mul_nonneg (by positivity) hh.le)),min_le_left _ _⟩

private theorem interval_cover {d h x : ℝ} (hh : 0 < h) (hx : |x| ≤ d) :
    ∃ j : Fin (bins d h), |x-center d h j| ≤ h := by
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  have hcap : d ≤ (bins d h:ℝ)*h := (div_le_iff₀ hh).mp ((Nat.le_ceil _).trans
    (Nat.cast_le.mpr (le_max_right 1 ⌈d/h⌉₊)))
  have hp : 0 < 2*h := by positivity
  obtain ⟨j,hj,hj'⟩ := unit_cell (bins_pos d h) (z:=(x+d)/(2*h))
    (div_nonneg (by linarith only [hl]) hp.le) ((div_le_iff₀ hp).mpr (by linarith only [hu,hcap]))
  have hleft := (le_div_iff₀ hp).mp hj
  have hright := (div_le_iff₀ hp).mp hj'
  refine ⟨j,abs_le.mpr ⟨?_,?_⟩⟩
  · calc -h ≤ x-(-d+(2*(j.val:ℝ)+1)*h) := by linarith only [hleft]
         _ ≤ x-center d h j := sub_le_sub_left (min_le_right _ _) x
  · apply sub_le_iff_le_add.mpr
    by_cases hb : -d+(2*(j.val:ℝ)+1)*h ≤ d
    · rw [center,min_eq_right hb]
      linarith only [hright]
    · rw [center,min_eq_left (le_of_not_ge hb)]
      linarith only [hu,hh]

private def step (d h : ℝ) := 2*d/((bins d h:ℝ)-1)
private def site (d h : ℝ) (j : Fin (bins d h)) := -d+step d h*j.val

private theorem step_nonneg {d h : ℝ} (hd : 0 ≤ d) : 0 ≤ step d h :=
  div_nonneg (mul_nonneg zero_le_two hd) (sub_nonneg.mpr (Nat.one_le_cast.mpr (bins_pos d h)))

private theorem site_inside {d h : ℝ} (hd : 0 ≤ d) (j : Fin (bins d h)) : |site d h j| ≤ d := by
  have hj : (j.val:ℝ)+1 ≤ (bins d h:ℝ) := by exact_mod_cast j.isLt
  have hstep := step_nonneg (h:=h) hd
  have hmax : step d h*((bins d h:ℝ)-1) ≤ 2*d := by
    by_cases hB : (bins d h:ℝ)-1=0
    · simp only [hB,mul_zero]; positivity
    · exact (div_mul_cancel₀ (2*d) hB).le
  have h := (mul_le_mul_of_nonneg_left (show (j.val:ℝ) ≤ (bins d h:ℝ)-1 by linarith only [hj]) hstep).trans hmax
  rw [site,abs_le]
  exact ⟨le_add_of_nonneg_right (mul_nonneg hstep (Nat.cast_nonneg _)),by linarith only [h]⟩

private theorem sites_far {d h : ℝ} (hd : 0 ≤ d) (hh : 0 < h) {j k : Fin (bins d h)} (hj : j ≠ k) :
    2*h < |site d h j-site d h k| := by
  have htwo : 2 ≤ bins d h := by
    have ha := j.isLt
    have hb := k.isLt
    have hn : j.val ≠ k.val := fun he => hj (Fin.ext he)
    omega
  have hc : 1 ≤ ⌈d/h⌉₊ := by unfold bins at htwo; omega
  have he : bins d h = ⌈d/h⌉₊ := max_eq_right hc
  have hstrict := Nat.ceil_lt_add_one (div_nonneg hd hh.le)
  rw [←he] at hstrict
  have hgap := (lt_div_iff₀ hh).mp (show (bins d h:ℝ)-1 < d/h by linarith only [hstrict])
  have hden : 0 < (bins d h:ℝ)-1 := by
    have ht : (2:ℝ) ≤ bins d h := by exact_mod_cast htwo
    linarith only [ht]
  have hs : 2*h < step d h := (lt_div_iff₀ hden).mpr (by linarith only [hgap])
  have hsep (a b : Fin (bins d h)) (hab : a.val < b.val) : 2*h < site d h b-site d h a := by
    have hi : (a.val:ℝ)+1 ≤ b.val := by exact_mod_cast hab
    have hm := mul_le_mul_of_nonneg_left hi (step_nonneg (h:=h) hd)
    dsimp only [site]
    linarith only [hm,hs]
  rcases lt_or_gt_of_ne (show j.val ≠ k.val from fun he => hj (Fin.ext he)) with h|h
  · rw [abs_sub_comm]
    exact (hsep _ _ h).trans_le (le_abs_self _)
  · exact (hsep _ _ h).trans_le (le_abs_self _)

private def coordBox {ι : Type*} (d : ι → ℝ) : Set (ι → ℝ) :=
  {x | ∀ i, |x i| ≤ d i}

/-- In the sup norm, packing at separation twice the error, external
covering, and internal covering have exactly the product of the
one-coordinate answers. A zero-width interval contributes one. -/
theorem coordinate_box_covering_numbers {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i)
    {h : ℝ≥0} (hh : 0 < h) :
    let B := {x : ι → ℝ | ∀ i, |x i| ≤ d i}
    let n := (∏ i, max 1 ⌈d i/(h:ℝ)⌉₊ : ℕ)
    packingNumber (2*h) B = n ∧ externalCoveringNumber h B = n ∧ coveringNumber h B = n := by
  classical
  intro B n
  let P := (i : ι) → Fin (bins (d i) h)
  let c (j : P) (i : ι) := center (d i) h (j i)
  let v (j : P) (i : ι) := site (d i) h (j i)
  have hr : 0 < (h:ℝ) := hh
  have hcard : ENat.card P=(n:ℕ∞) := by
    simp only [ENat.card_eq_coe_fintype_card,P,Fintype.card_pi,Fintype.card_fin,n,bins]
  have hcB : range c ⊆ B := by
    rintro x ⟨j,rfl⟩ i
    exact center_inside (hd i) hr (j i)
  have hvB : range v ⊆ B := by
    rintro x ⟨j,rfl⟩ i
    exact site_inside (hd i) (j i)
  have hcover : IsCover h B (range c) := by
    apply isCover_iff_subset_iUnion_closedBall.mpr
    intro x hx
    choose j hj using fun i => interval_cover hr (hx i)
    exact mem_iUnion.mpr ⟨c j,mem_iUnion.mpr ⟨⟨j,rfl⟩,
      (dist_pi_le_iff hr.le).mpr (fun i => by simpa only [Real.dist_eq] using hj i)⟩⟩
  have hdist {a b : P} (hn : a ≠ b) : 2*(h:ℝ) < dist (v a) (v b) := by
    obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
      by_contra! he
      exact hn (funext he)
    exact (sites_far (hd i) hr hi).trans_le (by simpa only [Real.dist_eq] using dist_le_pi_dist (v a) (v b) i)
  have hsep : IsSeparated ((2*h:ℝ≥0):ℝ≥0∞) (range v) := by
    rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩ hab
    rw [edist_nndist,ENNReal.coe_lt_coe]
    exact_mod_cast hdist (fun he => hab (congrArg v he))
  have hinj : Function.Injective v := by
    intro a b he
    by_contra hn
    have H := hdist hn
    rw [he,dist_self] at H
    linarith only [H,hr]
  have hlow := (hinj.encard_range).trans (hsep.encard_le_packingNumber hvB)
  rw [hcard] at hlow
  have hcardC := Set.encard_image_le c Set.univ
  rw [Set.image_univ,Set.encard_univ,hcard] at hcardC
  have htop := (hcover.coveringNumber_le_encard hcB).trans hcardC
  have hpe := packingNumber_two_mul_le_externalCoveringNumber h B
  have hei := externalCoveringNumber_le_coveringNumber (ε:=h) (A:=B)
  exact ⟨le_antisymm (hpe.trans (hei.trans htop)) hlow,
    le_antisymm (hei.trans htop) (hlow.trans hpe),le_antisymm htop (hlow.trans (hpe.trans hei))⟩

/-- All possible displacement-weighted readings on a finite sample. -/
def zeroDisplacementBox (S : Finset ℂ) := coordBox (fun i : S => rightDisplacement i)

theorem zeroDisplacementBox_eq_readings (S : Finset ℂ) :
    zeroDisplacementBox S = (fun u : S → ℝ => fun i : S => rightDisplacement i*u i) '' {u | ‖u‖ ≤ 1} := by
  ext x
  constructor
  · intro hx
    let u (i : S) := x i/rightDisplacement i
    have hxu (i : S) : rightDisplacement i*u i=x i := by
      by_cases h : rightDisplacement i=0
      · have he : |x i| ≤ 0 := h ▸ hx i
        have hh := abs_nonpos_iff.mp he
        simp [h,hh]
      · dsimp only [u]; field_simp
    refine ⟨u,(pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_,funext hxu⟩
    intro i
    change ‖x i/rightDisplacement i‖ ≤ (1:ℝ)
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (show 0 ≤ rightDisplacement i from le_max_right _ _)]
    by_cases h : rightDisplacement i=0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne (le_max_right _ _) (Ne.symm h))).mpr (hx i)
  · rintro ⟨u,hu,rfl⟩ i
    rw [abs_mul,abs_of_nonneg (show 0 ≤ rightDisplacement i from le_max_right _ _)]
    exact mul_le_of_le_one_right (le_max_right _ _) (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm u i).trans hu)

/-- Product of the numbers of intervals required on the sampled axes. -/
def zeroSampleCodeCount (S : Finset ℂ) (h : ℝ) : ℕ :=
  ∏ z ∈ S, max 1 ⌈rightDisplacement z / h⌉₊

/-- Minimum codebook cardinality at any positive tolerance for the
actual weighted zero amplitudes. The codewords may be arbitrary. -/
theorem zero_sample_codebook_size (S : Finset ℂ) {h : ℝ≥0} (hh : 0 < h) :
    externalCoveringNumber h (zeroDisplacementBox S) = (zeroSampleCodeCount S h : ℕ∞) := by
  have H := (coordinate_box_covering_numbers (fun i : S => rightDisplacement i)
    (fun _ => le_max_right _ _) hh).2.1
  rw [zeroSampleCodeCount, ← Finset.prod_coe_sort S (fun z : ℂ => max 1 ⌈rightDisplacement z/(h:ℝ)⌉₊)]
  exact H

#print axioms coordinate_box_covering_numbers
#print axioms zeroDisplacementBox_eq_readings
#print axioms zero_sample_codebook_size

end GaloisForLFunctions.ZeroConfigurationGeometry.ConfigAbscissa
