import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupation

/-! # Eliminating the observation time on one circuit winding -/

open Set Finset
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
open private mem_forwardUnitArc_iff_fract from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupation
noncomputable section

/-- One real lift of the corrected phase packet fits a common arc in a given time window. -/
def windingWindow {I : Type*} (A b : I → ℝ) (x T U : ℝ) : Prop :=
  ∃ t ∈ Icc T U, ∃ p : ℝ, ∀ i, |t*A i-b i-p| ≤ x/2

/-- With inverse time and rescaled global phase, the feasibility conditions become
linear inequalities in the energy readings and both auxiliary variables. -/
def inverseWindow {I : Type*} (A b : I → ℝ) (x T U : ℝ) : Prop :=
  ∃ s ∈ Icc U⁻¹ T⁻¹, ∃ q : ℝ, ∀ i,
    q+s*(b i-x/2) ≤ A i ∧ A i ≤ q+s*(b i+x/2)

theorem winding_iff_inverse {I : Type*} (A b : I → ℝ) {x T U : ℝ} (hT : 0<T) (hTU : T≤U) :
    windingWindow A b x T U ↔ inverseWindow A b x T U := by
  have hU := hT.trans_le hTU
  constructor
  · rintro ⟨t,ht,p,hp⟩
    have hpos := hT.trans_le ht.1
    refine ⟨t⁻¹,⟨?_,?_⟩,t⁻¹*p,?_⟩
    · simpa only [one_div] using one_div_le_one_div_of_le hpos ht.2
    · simpa only [one_div] using one_div_le_one_div_of_le hT ht.1
    · intro i
      obtain ⟨hl,hu⟩ := abs_le.mp (hp i)
      constructor
      · apply le_of_mul_le_mul_left (a:=t) _ hpos
        simp only [mul_add,←mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul]
        linarith only [hl]
      · apply le_of_mul_le_mul_left (a:=t) _ hpos
        simp only [mul_add,←mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul]
        linarith only [hu]
  · rintro ⟨s,hs,q,hq⟩
    have hpos := (inv_pos.mpr hU).trans_le hs.1
    refine ⟨s⁻¹,⟨?_,?_⟩,s⁻¹*q,?_⟩
    · simpa only [one_div,inv_inv] using one_div_le_one_div_of_le hpos hs.2
    · simpa only [one_div,inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr hU) hs.1
    · intro i
      obtain ⟨hl,hu⟩ := hq i
      apply abs_le.mpr
      have hlow := mul_le_mul_of_nonneg_left hl (inv_pos.mpr hpos).le
      have hhigh := mul_le_mul_of_nonneg_left hu (inv_pos.mpr hpos).le
      simp only [mul_add,←mul_assoc,inv_mul_cancel₀ hpos.ne',one_mul] at hlow hhigh
      constructor <;> linarith only [hlow,hhigh]

/-- A short enclosing arc supplies a single integral winding vector for all levels.
The reference level fixes the lift before the common phase is centered. -/
theorem winding_of_arc {I : Type*} [Fintype I] (A b : I → ℝ) (x : Icc (0:ℝ) (1/2)) {t : ℝ}
    (h : (fun i => ((t*A i-b i:ℝ):UnitAddCircle)) ∈ enclosingUnitArc (x:ℝ)) :
    ∃ n : I → ℤ, ∃ p : ℝ, ∀ i, |t*A i-(b i+(n i:ℝ))-p| ≤ (x:ℝ)/2 := by
  obtain ⟨j,hj⟩ := mem_iUnion.mp h
  let q := t*A j-b j
  let d (i : I) := t*A i-b i-q
  have hf (i : I) : Int.fract (d i) ≤ (x:ℝ) := by
    by_cases hi : i=j
    · subst i
      simpa only [d,q,sub_self,Int.fract_zero] using x.2.1
    · apply (mem_forwardUnitArc_iff_fract (d i) x).mp
      dsimp only [d,q]
      rw [AddCircle.coe_sub]
      exact hj i hi
  refine ⟨fun i => ⌊d i⌋,q+(x:ℝ)/2,?_⟩
  intro i
  have hl := Int.fract_nonneg (d i)
  have hu := hf i
  rw [Int.fract] at hl hu
  dsimp only [d] at *
  exact abs_le.mpr ⟨by linarith only [hl],by linarith only [hu]⟩

/-- Every witness that annihilates the global phase and the lifted target tests
the same energy packet at all possible dates, with tolerance decreasing as 1/T. -/
theorem winding_test {I : Type*} [Fintype I] (A b w : I → ℝ) {x T U : ℝ}
    (hT : 0≤T) (hw : (∑ i, w i)=0) (hb : (∑ i, w i*b i)=0) (h : windingWindow A b x T U) :
    T*|∑ i, w i*A i| ≤ (x/2)*∑ i, |w i| := by
  obtain ⟨t,ht,p,hp⟩ := h
  have hid : (∑ i, w i*(t*A i-b i-p))=t*∑ i, w i*A i := by
    simp only [mul_sub,sum_sub_distrib,←sum_mul,hw,zero_mul,hb,sub_zero]
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  calc
    _ ≤ t*|∑ i, w i*A i| := mul_le_mul_of_nonneg_right ht.1 (abs_nonneg _)
    _ = |∑ i, w i*(t*A i-b i-p)| := by rw [hid,abs_mul,abs_of_nonneg (hT.trans ht.1)]
    _ ≤ ∑ i, |w i*(t*A i-b i-p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (x/2)*|w i| := sum_le_sum fun i _ => by
      rw [abs_mul,mul_comm (x/2)]
      exact mul_le_mul_of_nonneg_left (hp i) (abs_nonneg _)
    _ = _ := (mul_sum ..).symm

#print axioms winding_iff_inverse
#print axioms winding_of_arc
#print axioms winding_test
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
