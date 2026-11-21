import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortArcHaar

/-! # Consecutive powers of a short spectral arc -/
open Set
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section
variable {I : Type*} [Fintype I]

private theorem lifts {θ : I → UnitAddCircle} {r : ℝ} (hr : 0 ≤ r) (h : θ ∈ enclosingUnitArc r) :
    ∃ i : I, ∀ j, ∃ u ∈ Icc (0:ℝ) r, (u:UnitAddCircle) = θ j-θ i := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp h
  refine ⟨i,fun j => ?_⟩
  by_cases hj : j = i
  · subst j
    exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
  · exact hi j hj

private theorem difference_lift {θ : I → UnitAddCircle} {r : ℝ} (hr : 0 ≤ r)
    (h : θ ∈ enclosingUnitArc r) (i j : I) :
    ∃ v ∈ Icc (-r) r, (v:UnitAddCircle) = θ j-θ i := by
  obtain ⟨b,hb⟩ := lifts hr h
  obtain ⟨u,hu,hi⟩ := hb i
  obtain ⟨w,hw,hj⟩ := hb j
  refine ⟨w-u,⟨by linarith only [hw.1,hu.2],by linarith only [hw.2,hu.1]⟩,?_⟩
  rw [AddCircle.coe_sub,hj,hi,sub_sub_sub_cancel_right]

private theorem coe_multiple (k : ℕ) (u : ℝ) :
    (((k:ℝ)*u:ℝ):UnitAddCircle) = k • (u:UnitAddCircle) := by
  rw [←nsmul_eq_mul,AddCircle.coe_nsmul]

/-- Each new multiple lies between zero and 2r before reduction. When
3r<1 the allowed interval [−r,r] has no other lift in that range. -/
private theorem lift_multiples {u r : ℝ} (hu : u ∈ Icc (0:ℝ) r) (hr : 3*r < 1)
    (m : ℕ) (ht : ∀ k ≤ m, ∃ v ∈ Icc (-r) r, (v:UnitAddCircle) = (((k:ℝ)*u:ℝ):UnitAddCircle)) :
    (m:ℝ)*u ≤ r := by
  have h (k : ℕ) : k ≤ m → (k:ℝ)*u ≤ r := by
    induction k with
    | zero => intro _; simpa only [Nat.cast_zero,zero_mul] using hu.1.trans hu.2
    | succ k ih =>
      intro hkm
      have hprev := ih (Nat.le_of_succ_le hkm)
      obtain ⟨v,hv,he⟩ := ht (k+1) hkm
      have hk0 : 0 ≤ (k:ℝ)*u := mul_nonneg (Nat.cast_nonneg _) hu.1
      have h1 : v ∈ Ico (-r) (-r+1) := ⟨hv.1,by linarith only [hr,hv.2,hu.1,hu.2]⟩
      have h2 : ((k+1:ℕ):ℝ)*u ∈ Ico (-r) (-r+1) := by
        rw [Nat.cast_add_one,add_mul,one_mul]
        constructor <;> linarith only [hr,hu.1,hu.2,hk0,hprev]
      exact ((AddCircle.coe_eq_coe_iff_of_mem_Ico h1 h2).mp he).symm.le.trans hv.2
  exact h m le_rfl

/-- Passing every short-arc test at multiples 1 through m is equivalent
to passing one test with tolerance divided by m in angular units. -/
theorem consecutive_powers_iff (θ : I → UnitAddCircle) {r : ℝ} (hr : 0 ≤ r) (hshort : 3*r < 1)
    (m : ℕ) (hm : 0 < m) :
    (∀ k ≤ m, (k • θ) ∈ enclosingUnitArc r) ↔ θ ∈ enclosingUnitArc (r/(m:ℝ)) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  constructor
  · intro hall
    have h1 : θ ∈ enclosingUnitArc r := by simpa only [one_smul] using hall 1 hm
    obtain ⟨i,hi⟩ := lifts hr h1
    refine mem_iUnion.mpr ⟨i,fun j _ => ?_⟩
    obtain ⟨u,hu,he⟩ := hi j
    refine ⟨u,⟨hu.1,(le_div_iff₀ hm').mpr ?_⟩,he⟩
    rw [mul_comm]
    apply lift_multiples hu hshort m
    intro k hk
    obtain ⟨v,hv,hvθ⟩ := difference_lift hr (hall k hk) i j
    refine ⟨v,hv,?_⟩
    rw [coe_multiple,he,nsmul_sub]
    exact hvθ
  · intro h k hk
    obtain ⟨i,hi⟩ := lifts (div_nonneg hr hm'.le) h
    refine mem_iUnion.mpr ⟨i,fun j _ => ?_⟩
    obtain ⟨u,hu,he⟩ := hi j
    refine ⟨(k:ℝ)*u,⟨mul_nonneg (Nat.cast_nonneg _) hu.1,?_⟩,?_⟩
    · exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hu.1).trans
        (by simpa only [mul_comm (m:ℝ)] using (le_div_iff₀ hm').mp hu.2)
    · rw [coe_multiple,he,nsmul_sub]
      rfl

#print axioms consecutive_powers_iff
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
