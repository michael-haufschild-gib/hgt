import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.ArcPowers

/-! # Sharp localization for independent translates at consecutive harmonics -/
open Set
namespace GaloisForLFunctions.HTGeometry.HarmonicRuns
noncomputable section

/-- A point passes independently placed arcs at harmonics 1 through m. -/
def arcHistory {m : ℕ} (c : Fin m → UnitAddCircle) (r : ℝ) : Set UnitAddCircle :=
  {z | ∀ i : Fin m, (i.val+1) • z-c i ∈ forwardUnitArc r}

private theorem spread {m : ℕ} (c : Fin m → UnitAddCircle) {r : ℝ}
    (hr : 0 ≤ r) (hshort : 3*r < 1) (hm : 0 < m) {z w : UnitAddCircle}
    (hz : z ∈ arcHistory c r) (hw : w ∈ arcHistory c r) {d : ℝ}
    (hd : d ∈ Icc (0:ℝ) r) (he : (d:UnitAddCircle) = z-w) : d ≤ r/(m:ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hm)).mpr
  rw [mul_comm]
  apply lift_multiples hd hshort m
  intro k hk
  cases k with
  | zero => exact ⟨0,⟨neg_nonpos.mpr hr,hr⟩,by simp⟩
  | succ k =>
    let i : Fin m := ⟨k,hk⟩
    obtain ⟨u,hu,heu⟩ := hz i
    obtain ⟨v,hv,hev⟩ := hw i
    refine ⟨u-v,⟨by linarith only [hu.1,hv.2],by linarith only [hu.2,hv.1]⟩,?_⟩
    rw [AddCircle.coe_sub,heu,hev,sub_sub_sub_cancel_right,←nsmul_sub,←he,←AddCircle.coe_nsmul,nsmul_eq_mul]

/-- Every compatible set of initial phases lies in one forward arc of
length r/m, even when each harmonic has a different target. -/
theorem arcHistory_enclosed {m : ℕ} (hm : 0 < m) (c : Fin m → UnitAddCircle)
    {r : ℝ} (hr : 0 ≤ r) (hshort : 3*r < 1) :
    ∃ b : UnitAddCircle, ∀ z ∈ arcHistory c r, z-b ∈ forwardUnitArc (r/(m:ℝ)) := by
  classical
  let c₀ := c ⟨0,hm⟩
  let S := {u : ℝ | u ∈ Icc (0:ℝ) r ∧ (u:UnitAddCircle)+c₀ ∈ arcHistory c r}
  have hs : BddBelow S := ⟨0,fun u hu => hu.1.1⟩
  refine ⟨((sInf S:ℝ):UnitAddCircle)+c₀,?_⟩
  intro z hz
  obtain ⟨u,hu,he⟩ := hz ⟨0,hm⟩
  have hu' : (u:UnitAddCircle) = z-c₀ := by simpa only [Nat.zero_add,one_smul,c₀] using he
  have hz' : (u:UnitAddCircle)+c₀ = z := eq_sub_iff_add_eq.mp hu'
  have hmem : u ∈ S := ⟨hu,by rw [hz']; exact hz⟩
  have hlow : u-r/(m:ℝ) ≤ sInf S := by
    apply le_csInf ⟨u,hmem⟩
    intro v hv
    by_cases huv : v ≤ u
    · have hv' : (v:UnitAddCircle)+c₀ ∈ arcHistory c r := hv.2
      have hd : u-v ∈ Icc (0:ℝ) r := ⟨sub_nonneg.mpr huv,by linarith only [hu.2,hv.1.1]⟩
      have hdiff : ((u-v:ℝ):UnitAddCircle) = z-((v:UnitAddCircle)+c₀) := by
        rw [←hz',AddCircle.coe_sub,add_sub_add_right_eq_sub]
      linarith only [spread c hr hshort hm hz hv' hd hdiff]
    · exact (sub_le_self _ (div_nonneg hr (Nat.cast_nonneg _))).trans (le_of_not_ge huv)
  refine ⟨u-sInf S,⟨sub_nonneg.mpr (csInf_le hs hmem),by linarith only [hlow]⟩,?_⟩
  rw [←hz',AddCircle.coe_sub,add_sub_add_right_eq_sub]

/-- A grid of fixed size rounds any arc endpoint backwards by at most δ. -/
theorem finite_forward_grid {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : ℕ, ∃ g : Fin Q → UnitAddCircle, ∀ z : UnitAddCircle, ∃ i, z-g i ∈ forwardUnitArc δ := by
  obtain ⟨Q,hQ⟩ := exists_nat_gt (1/δ)
  have hQ' : (0:ℝ) < Q := (one_div_pos.mpr hδ).trans hQ
  let g (i : Fin Q) : UnitAddCircle := (((i.val:ℝ)/(Q:ℝ):ℝ):UnitAddCircle)
  refine ⟨Q,g,fun z => ?_⟩
  let u := (AddCircle.equivIco (1:ℝ) 0 z : ℝ)
  have hu : u ∈ Ico (0:ℝ) 1 := by simpa only [zero_add] using (AddCircle.equivIco (1:ℝ) 0 z).property
  have he : (u:UnitAddCircle) = z := AddCircle.coe_equivIco
  let k := ⌊u*(Q:ℝ)⌋₊
  have hlo : (k:ℝ) ≤ u*Q := Nat.floor_le (mul_nonneg hu.1 hQ'.le)
  have hhi : u*Q < (k:ℝ)+1 := Nat.lt_floor_add_one _
  have hk : k < Q := by
    exact_mod_cast hlo.trans_lt ((mul_lt_mul_of_pos_right hu.2 hQ').trans_eq (one_mul _))
  refine ⟨⟨k,hk⟩,u-(k:ℝ)/Q,⟨sub_nonneg.mpr ((div_le_iff₀ hQ').mpr hlo),?_⟩,?_⟩
  · have hmesh : (1:ℝ) < δ*Q := by simpa only [mul_comm δ] using (div_lt_iff₀ hδ).mp hQ
    apply (sub_le_iff_le_add).mpr
    calc
      u ≤ (δ*Q+k)/(Q:ℝ) := (le_div_iff₀ hQ').mpr (by linarith only [hhi,hmesh])
      _ = δ+(k:ℝ)/Q := by rw [add_div,mul_div_cancel_right₀ _ hQ'.ne']
  · rw [AddCircle.coe_sub,he]

#print axioms arcHistory_enclosed
#print axioms finite_forward_grid
end
end GaloisForLFunctions.HTGeometry.HarmonicRuns
