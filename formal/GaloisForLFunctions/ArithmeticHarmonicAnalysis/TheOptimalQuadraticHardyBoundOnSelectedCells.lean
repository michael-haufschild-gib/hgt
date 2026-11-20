import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TheSharpHardyConstantOnAGeometricMesh
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TheSharpThresholdLossForQuadraticHardyCells
import Mathlib.Analysis.Real.Sqrt

/-!
# Optimal quadratic Hardy bound for selected mesh cells

In the quadratic case of Chen–Frank–Xiao–Yang–Yuan–Zhang, Lemma 3.5,
the optimal universal constant is four. To test a proposed bound, take
cell widths q^(2i) and fill the mesh with a normalized plateau. Its
length tends to infinity first and its width ratio then tends to one.
-/

noncomputable section
open Finset Filter Set
open scoped Topology
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The normalized selected-cell coefficient at one fixed threshold. -/
def IsSelectedMeshHardyConstantAt (β C : ℝ) : Prop :=
  ∀ (h z : ℕ → ℝ) (m : ℕ) (G : Finset ℕ), h m=0 → z m=0 →
    (∀ i ∈ range m, 0≤h (i+1) ∧ h (i+1)<h i) → G⊆range m →
    (∀ i∈G, β*h i≤h i-h (i+1)) →
    β^2*(∑ i ∈ G,z (i+1)^2/(h i-h (i+1)))≤
      C*(∑ i ∈ range m,(z i-z (i+1))^2/(h i-h (i+1)))

/-- A coefficient valid for every allowed threshold and grounded mesh. -/
def IsSelectedMeshHardyConstant (C : ℝ) : Prop :=
  ∀ β : ℝ, 0<β → β≤1 → IsSelectedMeshHardyConstantAt β C

private theorem inner_ground {h z : ℕ → ℝ} {m i : ℕ} (endz : z m=0)
    (mesh : ∀ j∈range m, 0≤h (j+1) ∧ h (j+1)<h j) (hi : i∈range m) (zero : h (i+1)=0) :
    z (i+1)=0 := by
  by_cases last : i+1=m
  · rwa [last]
  · have inside : i+1∈range m := mem_range.mpr (by have := mem_range.mp hi; omega)
    obtain ⟨next,less⟩ := mesh (i+1) inside
    exact False.elim ((next.trans_lt less).ne' zero)

private theorem geometric_mesh_test {C q : ℝ} (hq : 0<q) (hq1 : q<1)
    (paid : IsSelectedMeshHardyConstantAt (1-q^2) C) {m : ℕ} (x : ℕ → ℝ) (endx : x m=0) :
    (1-q^2)^2*(∑ i ∈ range m,(q*x (i+1))^2) ≤ C*(∑ i ∈ range m,(x i-q*x (i+1))^2) := by
  let β := 1-q^2
  let r (i : ℕ) := (q^i)^2
  let h (i : ℕ) := (r i-r m)/β
  let z (i : ℕ) := q^i*x i
  have βpos : 0<β := by
    have sq := mul_lt_mul_of_pos_right hq1 hq
    dsimp only [β]
    nlinarith only [sq,hq1]
  have width (i : ℕ) : h i-h (i+1)=r i := by
    dsimp only [h,r]
    rw [pow_succ q]
    field_simp [βpos.ne']
    dsimp only [β]
    ring
  have ground (i : ℕ) (le : i≤m) : 0≤h i :=
    div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (pow_pos hq m).le
      (pow_le_pow_of_le_one hq.le hq1.le le) 2)) βpos.le
  have mesh (i : ℕ) (hi : i∈range m) : 0≤h (i+1) ∧ h (i+1)<h i :=
    ⟨ground (i+1) (mem_range.mp hi),sub_pos.mp ((width i).symm ▸ sq_pos_of_pos (pow_pos hq i))⟩
  have selected (i : ℕ) (_ : i∈range m) : β*h i≤h i-h (i+1) := by
    rw [width,show β*h i=r i-r m by dsimp only [h]; field_simp [βpos.ne']]
    exact sub_le_self _ (sq_nonneg (q^m))
  have bound := paid h z m (range m)
    (by simp [h]) (by simp [z,endx]) mesh (fun _ hi => hi) selected
  have readout (i : ℕ) : z (i+1)^2/(h i-h (i+1))=(q*x (i+1))^2 := by
    rw [width]
    dsimp only [z,r]
    rw [pow_succ q]
    field_simp [pow_ne_zero i hq.ne']
  have loss (i : ℕ) : (z i-z (i+1))^2/(h i-h (i+1))=(x i-q*x (i+1))^2 := by
    rw [width]
    dsimp only [z,r]
    rw [pow_succ q]
    field_simp [pow_ne_zero i hq.ne']
  simpa only [readout,loss,β] using bound

/-- At any fixed positive complementary height ratio, the normalized
best coefficient is q²(1+q)². Geometric widths and longer plateaus
attain its limit even when the set of allowed meshes is unrestricted. -/
theorem sharp_selected_mesh_constant_at_ratio {q : ℝ} (positive : 0<q) (small : q<1) (C : ℝ) :
    IsSelectedMeshHardyConstantAt (1-q^2) C ↔ q^2*(1+q)^2≤C := by
  constructor
  · intro paid
    by_contra! fail
    have gap : 0<(1-q^2)^2*q^2-C*(1-q)^2 := by
      calc 0 < (1-q)^2*(q^2*(1+q)^2-C) :=
                 mul_pos (sq_pos_of_pos (sub_pos.mpr small)) (sub_pos.mpr fail)
           _ = _ := by ring
    obtain ⟨n,big⟩ := exists_nat_gt (C/((1-q^2)^2*q^2-C*(1-q)^2))
    obtain ⟨x,edge,_,mass,cost⟩ := grounded_geometric_plateau q n
    have bound := geometric_mesh_test positive small paid x edge
    rw [mass,cost] at bound
    linarith only [(div_lt_iff₀ gap).mp big,bound]
  · intro paid h z m G hm zm mesh sub large
    let A := ∑ i ∈ G,z (i+1)^2/(h i-h (i+1))
    let E := ∑ i ∈ range m,(z i-z (i+1))^2/(h i-h (i+1))
    have h0 : 0≤h 0 := by
      rcases m with _|n
      · exact hm.ge
      · obtain ⟨next,less⟩ := mesh 0 (mem_range.mpr (Nat.succ_pos n))
        exact next.trans less.le
    have trace := div_nonneg (sq_nonneg (z 0)) (mul_nonneg (add_pos zero_lt_one positive).le h0)
    have energy : 0≤E := sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (sub_nonneg.mpr (mesh i hi).2.le)
    have control : (1-q)^2/q^2*A≤E := (le_add_of_nonneg_right trace).trans
      (selected_hardy_cells_at_fixed_ratio positive small h z m G zm mesh sub large)
    calc (1-q^2)^2*A = (q^2*(1+q)^2)*((1-q)^2/q^2*A) := by
              field_simp [positive.ne']
              ring
         _ ≤ (q^2*(1+q)^2)*E := mul_le_mul_of_nonneg_left control (mul_nonneg (sq_nonneg _) (sq_nonneg _))
         _ ≤ C*E := mul_le_mul_of_nonneg_right paid energy

private theorem full_mesh_threshold (C : ℝ) : IsSelectedMeshHardyConstantAt 1 C ↔ 0≤C := by
  constructor
  · intro paid
    let h (i : ℕ) : ℝ := if i=0 then 1 else 0
    have mesh (i : ℕ) (hi : i∈range 1) : 0≤h (i+1) ∧ h (i+1)<h i := by
      have zero : i=0 := by have := mem_range.mp hi; omega
      simp [zero,h]
    have bound := paid h h 1 ∅ (by simp [h]) (by simp [h]) mesh (empty_subset _) (by simp)
    simpa [h,sum_range_succ] using bound
  · intro nonneg h z m G _ zm mesh sub large
    have vanish : (∑ i ∈ G,z (i+1)^2/(h i-h (i+1)))=0 := by
      refine sum_eq_zero fun i hi => ?_
      have step := large i hi
      rw [one_mul] at step
      have zero : h (i+1)=0 := le_antisymm (by linarith only [step]) (mesh i (sub hi)).1
      simp only [inner_ground zm mesh (sub hi) zero,zero_pow (by norm_num : 2≠0),zero_div]
    rw [vanish,mul_zero]
    exact mul_nonneg nonneg (sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (sub_nonneg.mpr (mesh i hi).2.le))

/-- For each original threshold β, the full normalized constant is
(1−β)(1+√(1−β))². At β=1 all selected inner samples vanish. -/
theorem optimal_selected_mesh_threshold {β : ℝ} (positive : 0<β) (cap : β≤1) (C : ℝ) :
    IsSelectedMeshHardyConstantAt β C ↔ (1-β)*(1+Real.sqrt (1-β))^2≤C := by
  rcases cap.eq_or_lt with rfl|strict
  · simpa only [sub_self,zero_mul] using full_mesh_threshold C
  let q := Real.sqrt (1-β)
  have sq : q^2=1-β := Real.sq_sqrt (sub_nonneg.mpr cap)
  have qp : 0<q := Real.sqrt_pos.mpr (sub_pos.mpr strict)
  have q1 : q<1 := by
    by_contra! ge
    have lower := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) ge 2
    rw [one_pow,sq] at lower
    linarith only [positive,lower]
  have best := sharp_selected_mesh_constant_at_ratio qp q1 C
  rwa [sq,show 1-(1-β)=β by ring] at best

/-- Four is the least coefficient that works for every threshold, every
finite mesh, and every allowed subset of its cells. -/
theorem selected_mesh_hardy_constant_iff (C : ℝ) : IsSelectedMeshHardyConstant C ↔ 4≤C := by
  constructor
  · intro paid
    have each {q : ℝ} (positive : 0<q) (small : q<1) : q^2*(1+q)^2≤C := by
      have cap : 0<1-q^2 := by nlinarith only [mul_lt_mul_of_pos_right small positive,small]
      exact (sharp_selected_mesh_constant_at_ratio positive small C).mp
        (paid (1-q^2) cap (sub_le_self _ (sq_nonneg q)))
    have cont : Continuous (fun q : ℝ => q^2*(1+q)^2) := by fun_prop
    have lim : Tendsto (fun q : ℝ => q^2*(1+q)^2) (𝓝[<] 1) (𝓝 4) := by
      convert (cont.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds : 𝓝[<] (1:ℝ)≤𝓝 1) using 1
      norm_num
    apply le_of_tendsto lim
    have left : ∀ᶠ q : ℝ in 𝓝[<] 1,q<1 := self_mem_nhdsWithin
    have pos : ∀ᶠ q : ℝ in 𝓝[<] 1,0<q :=
      (eventually_gt_nhds (zero_lt_one : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [pos,left] with q hq h1
    exact each hq h1
  · intro bound β positive cap
    apply (optimal_selected_mesh_threshold positive cap C).mpr
    have root : Real.sqrt (1-β)≤1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (sub_le_self (1:ℝ) positive.le)
    have side : 1+Real.sqrt (1-β)≤2 := by linarith only [root]
    have sq := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.sqrt_nonneg _)) side 2
    have price := mul_le_mul (sub_le_self (1:ℝ) positive.le) sq (sq_nonneg _) zero_le_one
    exact price.trans ((by norm_num : (1:ℝ)*2^2=4).le.trans bound)

#print axioms optimal_selected_mesh_threshold
#print axioms sharp_selected_mesh_constant_at_ratio
#print axioms selected_mesh_hardy_constant_iff
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
