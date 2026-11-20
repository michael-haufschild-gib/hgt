import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TheBoundaryAndCellTermsOfTheMeshHardyInequality
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optimal joint bulk and trace prices for the quadratic mesh Hardy inequality

At a fixed selection threshold, a grounded geometric sequence tests the
outer trace. For a strictly decaying test its only loss is the final jump.
At the critical bulk price, a linear taper makes the loss tend to zero.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Price per selected cell at the geometric test ratio r. -/
def selectedMeshBulk (q r : ℝ) : ℝ := (1+q^2-q*(r+r⁻¹))/q^2

/-- A common trace coefficient for all grounded meshes at the stated bulk price. -/
def IsSelectedMeshTracePrice (q r C : ℝ) : Prop :=
  ∀ (h z : ℕ → ℝ) (m : ℕ) (G : Finset ℕ), h m=0 → z m=0 →
    (∀ i∈range m, 0≤h (i+1) ∧ h (i+1)<h i) → G⊆range m →
    (∀ i∈G, (1-q^2)*h i≤h i-h (i+1)) →
    selectedMeshBulk q r*(∑ i ∈ G,z (i+1)^2/(h i-h (i+1)))+C*(z 0^2/h 0)≤
      ∑ i ∈ range m,(z i-z (i+1))^2/(h i-h (i+1))

private theorem grounded_trace_decomposition {q r : ℝ} (hq : 0<q) (hr : 0<r)
    {m : ℕ} (x : ℕ → ℝ) (endx : x m=0) :
    (∑ i ∈ range m,(x i-q*x (i+1))^2)=
      selectedMeshBulk q r*(∑ i ∈ range m,(q*x (i+1))^2)+(1-q*r)*x 0^2+
      (q/r)*(∑ i ∈ range m,(x (i+1)-r*x i)^2) := by
  have point (i : ℕ) : (x i-q*x (i+1))^2=
      selectedMeshBulk q r*(q*x (i+1))^2+(1-q*r)*(x i^2-x (i+1)^2)+
      (q/r)*(x (i+1)-r*x i)^2 := by
    unfold selectedMeshBulk
    field_simp [hq.ne',hr.ne']
    ring
  simp_rw [point]
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum,←mul_sum,sum_range_sub',endx]
  simp

private theorem geometric_trace_test {q r C : ℝ} (hq : 0<q) (h1 : q<1) (hr : 0<r)
    (hc : 0≤C) (paid : IsSelectedMeshTracePrice q r C)
    {m : ℕ} (hm : 0<m) (x : ℕ → ℝ) (endx : x m=0) :
    (C*(1-q^2)-(1-q*r))*x 0^2≤(q/r)*(∑ i ∈ range m,(x (i+1)-r*x i)^2) := by
  obtain ⟨h,z,H,Z,mesh,selected,first,initial,readout,loss⟩ :=
    exists_grounded_geometric_hardy_mesh hq h1 x endx
  have bound := paid h z m (range m) H Z mesh (fun _ hi => hi) selected
  rw [readout,loss,initial,grounded_trace_decomposition hq hr x endx] at bound
  have nonzero := (mesh 0 (mem_range.mpr hm)).1.trans_lt (mesh 0 (mem_range.mpr hm)).2
  have width : 0<1-q^2 := by nlinarith only [mul_lt_mul_of_pos_right h1 hq,h1]
  have cap : (1-q^2)*h 0≤1 := by
    calc _ = 1-(q^m)^2 := by rw [first]; field_simp [width.ne']
         _ ≤ 1 := sub_le_self _ (sq_nonneg _)
  have trace : (1-q^2)*x 0^2≤x 0^2/h 0 := by
    apply (le_div_iff₀ nonzero).mpr
    calc _ = x 0^2*((1-q^2)*h 0) := by ring
         _ ≤ x 0^2*1 := mul_le_mul_of_nonneg_left cap (sq_nonneg _)
         _ = _ := mul_one _
  linarith only [bound,mul_le_mul_of_nonneg_left trace hc]

private theorem sharp_trace_upper {q r : ℝ} (hq : 0<q) (h1 : q<1) (qr : q≤r) (r1 : r≤1) :
    IsSelectedMeshTracePrice q r ((1-q*r)/(1-q^2)) := by
  intro h z m G _ Z mesh sub selected
  have hr := hq.trans_le qr
  have width : 0<1-q^2 := by nlinarith only [mul_lt_mul_of_pos_right h1 hq,h1]
  have dr : 0<1-q*r := by linarith only [mul_le_mul_of_nonneg_left r1 hq.le,h1]
  let t := q*(r-q)/(1-q*r)
  have tp : 0≤t := div_nonneg (mul_nonneg hq.le (sub_nonneg.mpr qr)) dr.le
  have A : 1+t=(1-q^2)/(1-q*r) := by dsimp only [t]; field_simp [dr.ne']; ring
  have B : t+q^2=q*r*(1-q^2)/(1-q*r) := by dsimp only [t]; field_simp [dr.ne']; ring
  have price : meshHardyCellPrice t (q^2)=selectedMeshBulk q r := by
    rw [meshHardyCellPrice,A,B,selectedMeshBulk]
    dsimp only [t]
    field_simp [hq.ne',hr.ne',width.ne',dr.ne']
    ring
  have bound := selected_hardy_cells_with_trace tp (sq_pos_of_pos hq) (by linarith only [width])
    h z m G Z mesh sub selected
  rw [price,A] at bound
  convert bound using 1
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

/-- For q≤r≤1 the best trace coefficient at bulk price
(1+q²−q(r+1/r))/q² is (1−qr)/(1−q²), including both endpoints. -/
theorem selected_mesh_trace_price_iff {q r : ℝ} (hq : 0<q) (h1 : q<1)
    (qr : q≤r) (r1 : r≤1) (C : ℝ) :
    IsSelectedMeshTracePrice q r C ↔ C≤(1-q*r)/(1-q^2) := by
  have width : 0<1-q^2 := by nlinarith only [mul_lt_mul_of_pos_right h1 hq,h1]
  have dr : 0<1-q*r := by linarith only [mul_le_mul_of_nonneg_left r1 hq.le,h1]
  constructor
  · intro paid
    by_contra! big
    have hc := (div_pos dr width).trans big
    let gap := C*(1-q^2)-(1-q*r)
    have hg : 0<gap := sub_pos.mpr ((div_lt_iff₀ width).mp big)
    have hr := hq.trans_le qr
    rcases r1.eq_or_lt with eq|small
    · subst r
      obtain ⟨n,large⟩ := exists_nat_gt (q/gap)
      let m := n+1
      let x (i : ℕ) : ℝ := (m:ℝ)-i
      have test := geometric_trace_test hq h1 zero_lt_one hc.le paid (Nat.succ_pos n) x (by simp [x,m])
      have loss (i : ℕ) : (x (i+1)-1*x i)^2=1 := by
        simp only [x,Nat.cast_add,Nat.cast_one]
        ring
      simp only [loss,sum_const,card_range,nsmul_eq_mul,mul_one,div_one] at test
      rw [show x 0=(m:ℝ) by simp [x]] at test
      have bound : gap*(m:ℝ)^2≤q*(m:ℝ) := by simpa only [gap,mul_one] using test
      have pos : 0<(m:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
      have gt : q<gap*(m:ℝ) := by
        have above := (div_lt_iff₀ hg).mp large
        dsimp only [m]; rw [Nat.cast_succ]
        linarith only [above,hg]
      exact (not_lt_of_ge bound) (by
        change q*(m:ℝ)<gap*(m:ℝ)^2
        simpa only [pow_two,mul_assoc] using mul_lt_mul_of_pos_right gt pos)
    · have van := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le small
      have lim : Tendsto (fun n : ℕ => (q/r)*((r^n)*r)^2) atTop (𝓝 0) := by
        simpa only [zero_mul,zero_pow (by norm_num : 2≠0),mul_zero] using ((van.mul_const r).pow 2).const_mul (q/r)
      apply hg.not_ge
      apply ge_of_tendsto lim
      apply Filter.Eventually.of_forall
      intro n
      let x (i : ℕ) : ℝ := if i≤n then r^i else 0
      have edge : x (n+1)=0 := if_neg (by omega)
      have test := geometric_trace_test hq h1 hr hc.le paid (Nat.succ_pos n) x edge
      have zero (i : ℕ) (hi : i∈range n) : (x (i+1)-r*x i)^2=0 := by
        have lt := mem_range.mp hi
        have step : i+1≤n := lt
        simp only [x,if_pos step,if_pos lt.le,pow_succ]
        ring
      rw [sum_range_succ,sum_eq_zero zero,zero_add,edge,show x n=r^n from if_pos le_rfl,
        show x 0=1 by simp [x],one_pow,mul_one] at test
      simpa only [zero_sub,neg_sq,mul_comm r] using test
  · intro cap h z m G H Z mesh sub selected
    have h0 : 0≤h 0 := by
      cases m with
      | zero => exact H.ge
      | succ n =>
        have first := mesh 0 (mem_range.mpr (Nat.succ_pos n))
        exact first.1.trans first.2.le
    exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right cap (div_nonneg (sq_nonneg (z 0)) h0))).trans
      (sharp_trace_upper hq h1 qr r1 h z m G H Z mesh sub selected)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
