import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FiniteDilationTest
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Uniform dilation grids and observation windows -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

/-- Equally spaced dilations in (1,2], indexed by the right endpoints. -/
def rayGrid (q : ℕ) (i : Fin q) : ℝ := 1+((i.val:ℝ)+1)/q

theorem rayGrid_mem {q : ℕ} (i : Fin q) : rayGrid q i ∈ Icc 1 2 := by
  have hq : (0:ℝ)<q := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi : (i.val:ℝ)+1 ≤ q := by exact_mod_cast i.isLt
  exact ⟨le_add_of_nonneg_right (by positivity),by
    dsimp [rayGrid]
    linarith only [(div_le_one hq).mpr hi]⟩

/-- A successful endpoint contributes its entire preceding cell to the set
of window starts. Different endpoints have disjoint half-open cells. -/
private theorem grid_cells_le {q : ℕ} (S : Finset (Fin q)) (C : Set ℝ) (v δ W : ℝ)
    (hδ : 0 < δ) (hh : ∀ j ∈ S, ∃ t ∈ Icc (v+((j.val:ℝ)+1)*δ) (v+(j.val:ℝ)*δ+W), t ∈ C) :
    (S.card:ℝ)*δ ≤ volume.real
      ({u | ∃ t ∈ Icc u (u+W), t ∈ C} ∩ Icc v (v+(q:ℝ)*δ)) := by
  classical
  let cell (i : S) := Ioc (v+(i.val.val:ℝ)*δ) (v+((i.val.val:ℝ)+1)*δ)
  have sep (i j : S) (h : i.val < j.val) : Disjoint (cell i) (cell j) := by
    apply Set.disjoint_left.mpr
    intro u hi hj
    have hle : (i.val.val:ℝ)+1 ≤ j.val.val := by exact_mod_cast h
    have hline := mul_le_mul_of_nonneg_right hle hδ.le
    exact (not_lt_of_ge (hi.2.trans (add_le_add le_rfl hline))) hj.1
  have hp : Pairwise (fun i j => Disjoint (cell i) (cell j)) := fun i j hij =>
    (lt_or_gt_of_ne (fun h => hij (Subtype.ext h))).elim (sep i j) (fun h => (sep j i h).symm)
  have hsub : (⋃ i : S, cell i) ⊆ {u | ∃ t ∈ Icc u (u+W), t ∈ C} ∩ Icc v (v+(q:ℝ)*δ) := by
    intro u hu
    obtain ⟨i,hi⟩ := mem_iUnion.mp hu
    obtain ⟨t,ht,hc⟩ := hh i.val i.property
    have he : (i.val.val:ℝ)+1 ≤ q := by exact_mod_cast i.val.isLt
    refine ⟨⟨t,⟨hi.2.trans ht.1,by linarith only [ht.2,hi.1]⟩,hc⟩,?_,?_⟩
    · exact (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i.val.val) hδ.le)).trans hi.1.le
    · exact hi.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right he hδ.le))
  have hlen (i : S) : volume.real (cell i) = δ := by
    dsimp only [cell]
    rw [Real.volume_real_Ioc_of_le (by linarith only [hδ])]
    ring
  calc
    _ = ∑ i : S, volume.real (cell i) := by simp only [hlen,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    _ = volume.real (⋃ i, cell i) := (measureReal_iUnion_fintype hp (fun _ => measurableSet_Ioc)
      (fun _ => measure_Ioc_lt_top.ne)).symm
    _ ≤ _ := measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

/-- Long-window occupation bounds the number of successful dilations in
every row of the test. The target may itself include a whole time interval. -/
theorem rayGrid_count_of_window_occupation {ι : Type*} [Fintype ι] {q : ℕ} (i : Fin q)
    (E : Set (ι → ℝ)) (x : ι → ℝ) (C : Set ℝ) {t b G W M : ℝ}
    (ht : 0 < t) (hb : 0 ≤ b) (hq : t ≤ q) (hG : 2*G ≤ t) (hW : 2*b+1 ≤ W) (hM : 0 ≤ M)
    (hhit : ∀ a : ℝ, 0 < a → a • x ∈ E → ∃ y ∈ Icc (a*t) (a*t+a*b), y ∈ C)
    (hocc : ∀ A T : ℝ, 0 ≤ T →
      M*volume.real ({u | ∃ y ∈ Icc u (u+W), y ∈ C} ∩ Icc A (A+T)) ≤ T+G) :
    M*dilationCount (fun j => rayGrid q j/rayGrid q i) E x ≤ 2*(q:ℝ) := by
  classical
  let a := rayGrid q i
  let v := t/a
  let δ := v/q
  let S := Finset.univ.filter fun j : Fin q => (rayGrid q j/a) • x ∈ E
  have ha : a ∈ Icc 1 2 := rayGrid_mem i
  have hap : 0 < a := zero_lt_one.trans_le ha.1
  have hqp : (0:ℝ)<q := ht.trans_le hq
  have hv : 0 < v := div_pos ht hap
  have hδ : 0 < δ := div_pos hv hqp
  have hδ₁ : δ ≤ 1 := (div_le_one hqp).mpr ((div_le_self ht.le ha.1).trans hq)
  have he (j : Fin q) : rayGrid q j/a*t = v+((j.val:ℝ)+1)*δ := by
    dsimp [rayGrid,δ,v]
    ring
  have htotal : (q:ℝ)*δ = v := by dsimp [δ]; field_simp
  have hy := grid_cells_le S C v δ W hδ (fun j hj => by
    have hp := rayGrid_mem j
    obtain ⟨y,hy,hh⟩ := hhit _ (div_pos (zero_lt_one.trans_le hp.1) hap) (Finset.mem_filter.mp hj).2
    have hprice : rayGrid q j/a*b ≤ 2*b := mul_le_mul_of_nonneg_right
      ((div_le_self (zero_le_one.trans hp.1) ha.1).trans hp.2) hb
    rw [he] at hy
    exact ⟨y,⟨hy.1,by linarith only [hy.2,hprice,hW,hδ₁]⟩,hh⟩)
  rw [htotal] at hy
  have hok := (mul_le_mul_of_nonneg_left hy hM).trans (hocc v v hv.le)
  have hg : G ≤ v := by
    apply (le_div_iff₀ hap).mpr
    by_cases h : 0 ≤ G
    · exact (mul_le_mul_of_nonneg_left ha.2 h).trans (by linarith only [hG])
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hap.le).trans ht.le
  have hcount : dilationCount (fun j => rayGrid q j/a) E x = (S.card:ℝ) := by
    simp only [dilationCount,indicator_apply,mem_preimage,Finset.sum_boole,S]
  rw [show rayGrid q i = a from rfl,hcount]
  apply le_of_mul_le_mul_right _ hδ
  calc
    _ = M*((S.card:ℝ)*δ) := mul_assoc _ _ _
    _ ≤ v+G := hok
    _ ≤ 2*v := by linarith only [hg]
    _ = (2*(q:ℝ))*δ := by rw [mul_assoc,htotal]

#print axioms rayGrid_count_of_window_occupation
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
