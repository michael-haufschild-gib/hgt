import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.CapMass

/-! # Separated product spectra inside two prescribed all-time circuit caps -/
open Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open PrescribedTimes
noncomputable section

private theorem cap_scale_iff (n : ℕ) (ε : ℝ) {c : ℝ} (hc : 0 < c) (x : PathLabel n→ℝ) :
    c • x ∈ capEvent n ε ↔ x ∈ capEvent n ε := by
  let θ := fun i => x (pathCoeffEquiv n i)
  change (∀ t, pathGateDistance n _ (c • θ) t ≤ ε) ↔ ∀ t, pathGateDistance n _ θ t ≤ ε
  simp only [distance_dilate]
  constructor
  · intro h t
    have he : c*(t/c)=t := by field_simp
    exact he ▸ h (t/c)
  · exact fun h t => h (c*t)

private def cappedEnergy (n : ℕ) (ε : ℝ) (x : PathLabel n→ℝ) (i : Fin (2^(n+2))) : ℝ :=
  (capEvent n ε).indicator (fun y => energies n y i) x

private theorem capped_scale {n : ℕ} (ε c : ℝ) (hc : 0 < c) (x : PathLabel n→ℝ) (i) :
    cappedEnergy n ε (c • x) i=c*cappedEnergy n ε x i := by
  by_cases h : x ∈ capEvent n ε
  · rw [cappedEnergy,cappedEnergy,indicator_of_mem ((cap_scale_iff n ε hc x).mpr h),
      indicator_of_mem h,energies_scale c hc]
  · rw [cappedEnergy,cappedEnergy,indicator_of_notMem (mt (cap_scale_iff n ε hc x).mp h),
      indicator_of_notMem h,mul_zero]

/-- A positive gap for the masked pair spectrum forces each block to be
in its own cap event. Dilation of the right block preserves that event. -/
theorem capped_product_mass (l r : ℕ) (hl : l ≤ r) (hr : r ≤ l+1) (ε : ℝ) :
    let μ := (standardLaw (PathLabel l)).prod (standardLaw (PathLabel r))
    (standardLaw (PathLabel l)).real (separatedCap l ε)*
      (standardLaw (PathLabel r)).real (separatedCap r ε) ≤
      (gridCount l r:ℝ)*2^(Fintype.card (PathLabel r))*
        μ.real ((capEvent l ε ×ˢ capEvent r ε) ∩ productEvent l r (2*gapScale (l+r+4))) := by
  intro μ
  let g := gapScale (r+2)
  let N := gridCount l r
  let δ := g/(8*(N:ℝ))
  have hg := gapScale_pos (r+2)
  have hN : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hd : 0 < δ := div_pos hg (mul_pos (by norm_num) hN)
  have hm (n : ℕ) (i) : Measurable (fun x => cappedEnergy n ε x i) :=
    (measurable_energies n i).indicator (measurable_capEvent n ε)
  let A (n : ℕ) := {x | ∀ i j, i≠j → g ≤ |cappedEnergy n ε x i-cappedEnergy n ε x j|}
  have hin (n : ℕ) (hn : n ≤ r) : separatedCap n ε ⊆ A n := by
    intro x hx i j hij
    simp only [cappedEnergy,indicator_of_mem hx.1]
    exact (gapScale_antitone (Nat.add_le_add_right hn 2)).trans (hx.2 i j hij)
  have hh := product_gap_mass (standardLaw (PathLabel l)) (cappedEnergy l ε) (cappedEnergy r ε)
    (hm l) (hm r) (capped_scale ε) hg
  apply (mul_le_mul (measureReal_mono (hin l hl)) (measureReal_mono (hin r le_rfl))
    measureReal_nonneg measureReal_nonneg).trans
  apply hh.trans (mul_le_mul_of_nonneg_left (measureReal_mono _) (by positivity))
  intro p hp
  let z (s : ℕ) : Fin (2^(s+2)) := ⟨0,by positivity⟩
  let w (s : ℕ) : Fin (2^(s+2)) := ⟨1,one_lt_pow₀ (by decide) (by omega)⟩
  have hne (s : ℕ) : z s≠w s := fun he => (by decide : (0:ℕ)≠1) (congrArg Fin.val he)
  have hL : p.1 ∈ capEvent l ε := by
    by_contra h
    have h' := hp (z l,z r) (w l,z r) (fun he => hne l (congrArg Prod.fst he))
    simp only [cappedEnergy,indicator_of_notMem h,zero_add,sub_self,abs_zero] at h'
    exact hd.not_ge h'
  have hR : p.2 ∈ capEvent r ε := by
    by_contra h
    have h' := hp (z l,z r) (z l,w r) (fun he => hne r (congrArg Prod.snd he))
    simp only [cappedEnergy,indicator_of_notMem h,add_zero,sub_self,abs_zero] at h'
    exact hd.not_ge h'
  refine ⟨⟨hL,hR⟩,fun i j hij => (parent_spacing l r hr).trans ?_⟩
  simpa only [cappedEnergy,indicator_of_mem hL,indicator_of_mem hR] using hp i j hij

#print axioms capped_product_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
