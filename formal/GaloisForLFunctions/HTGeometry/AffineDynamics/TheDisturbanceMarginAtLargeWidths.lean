import GaloisForLFunctions.HTGeometry.AffineDynamics.MaximumDisturbanceOnABoundedRoad

/-!
# Shape and limiting deficit of the disturbance tolerance

The largest disturbance compatible with any robust state is a strictly
increasing concave function of width. Its supporting lines come from
integer stopping horizons. As width W tends to infinity its deficit
from the full control authority a is asymptotic to 2a²/W.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance

/-- The tolerance is defined directly from the controlled invariants. -/
def tolerance (a W : ℝ) : ℝ :=
  sSup {b | 0≤b ∧ ∃ x v, Robust a b 0 W x v}

/-- Each affine branch attains the supremum over actual disturbances. -/
theorem tolerance_eq {a W : ℝ} (ha : 0<a) (j : ℕ) (hl : knot a j≤W) (hh : W≤knot a (j+1)) :
    tolerance a W=capacity a W j := by
  have hc := fits_iff (b:=capacity a W j) (l:=0) (r:=W) ha (capacity_speeds ha j hl hh).1 j
    (by simpa only [sub_zero] using hl) (by simpa only [sub_zero] using hh)
  have hm : capacity a W j∈{b | 0≤b ∧ ∃ x v, Robust a b 0 W x v} :=
    ⟨(capacity_speeds ha j hl hh).1,hc.2 (by rw [sub_zero])⟩
  have hu : ∀ b∈{b | 0≤b ∧ ∃ x v, Robust a b 0 W x v}, b≤capacity a W j := by
    rintro b ⟨hb,x,v,h⟩
    simpa only [sub_zero] using horizon_cap hb h j
  exact le_antisymm (csSup_le ⟨_,hm⟩ hu) (le_csSup ⟨_,hu⟩ hm)

/-- Full control authority is approached strictly, and the optimum is
always a viable disturbance on every finite nonnegative width. -/
theorem optimum {a W : ℝ} (ha : 0<a) (hW : 0≤W) :
    0≤tolerance a W ∧ tolerance a W<a ∧
      distance (a-tolerance a W) (2*tolerance a W)=W ∧ ∃ x v, Robust a (tolerance a W) 0 W x v := by
  obtain ⟨j,hl,hh⟩ := exists_width_interval ha hW
  rw [tolerance_eq ha j hl hh]
  obtain ⟨h₀,h₁,_,_⟩ := capacity_speeds ha j hl hh
  have he := capacity_fills_width ha j hl hh
  exact ⟨h₀,h₁,he,(nonempty_iff h₀ h₁).2 (by simpa only [sub_zero] using he.le)⟩

/-- Every stopping horizon defines a supporting line on the whole half-line. -/
theorem tolerance_le_capacity {a W : ℝ} (ha : 0<a) (hW : 0≤W) (j : ℕ) :
    tolerance a W≤capacity a W j := by
  obtain ⟨hb,_,_,x,v,hr⟩ := optimum ha hW
  simpa only [sub_zero] using horizon_cap hb hr j

theorem tolerance_strictMono {a : ℝ} (ha : 0<a) : StrictMonoOn (tolerance a) (Set.Ici 0) := by
  intro x hx y hy hxy
  obtain ⟨j,hl,hh⟩ := exists_width_interval ha hy
  rw [tolerance_eq ha j hl hh]
  apply (tolerance_le_capacity ha hx j).trans_lt
  unfold capacity
  apply div_lt_div_of_pos_right _ (by positivity)
  linarith only [hxy]

theorem tolerance_concave {a : ℝ} (ha : 0<a) : ConcaveOn ℝ (Set.Ici 0) (tolerance a) := by
  refine ⟨convex_Ici _,?_⟩
  intro x hx y hy u v hu hv hs
  change 0≤x at hx
  change 0≤y at hy
  change u*tolerance a x+v*tolerance a y≤tolerance a (u*x+v*y)
  obtain ⟨j,hl,hh⟩ := exists_width_interval ha (add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy))
  rw [tolerance_eq ha j hl hh]
  refine (add_le_add (mul_le_mul_of_nonneg_left (tolerance_le_capacity ha hx j) hu)
    (mul_le_mul_of_nonneg_left (tolerance_le_capacity ha hy j) hv)).trans_eq ?_
  simp only [capacity,div_eq_mul_inv]
  linear_combination (a*((j : ℝ)+1)*j*(((j : ℝ)+1)*(j+4))⁻¹)*hs

/-- The sampling error gives a quadratic bracket around the deficit even
at finite width; the discrete correction vanishes at the horizon knots. -/
theorem deficit_bounds {a W : ℝ} (ha : 0<a) (hW : 0≤W) :
    let B := tolerance a W
    B*(a+B)≤W*(a-B) ∧ W*(a-B)≤B*(a+B)+(a-B)^2/8 := by
  intro B
  obtain ⟨hb,hba,he,_⟩ := optimum ha hW
  have hd : 0<a-B := sub_pos.mpr hba
  obtain ⟨lo,hi⟩ := sampling_bounds (a-B) (2*B) hd (mul_nonneg (by norm_num) hb)
  change distance (a-B) (2*B)=W at he
  rw [he] at lo hi
  have hcalc : ((2*B)^2/(2*(a-B))+2*B/2)*(a-B)=B*(a+B) := by
    field_simp [hd.ne']
    ring
  have hl := mul_le_mul_of_nonneg_right lo hd.le
  have hh := mul_le_mul_of_nonneg_right hi hd.le
  rw [hcalc] at hl
  rw [add_mul,hcalc] at hh
  exact ⟨hl,by linarith only [hh]⟩

private theorem deficit_upper {a W : ℝ} (ha : 0<a) (hW : 0<W) :
    a-tolerance a W≤(17*a^2/8)/W := by
  let B := tolerance a W
  obtain ⟨hb,hl,_,_⟩ := optimum ha hW.le
  have h₁ : B*(a+B)≤a*(a+a) :=
    mul_le_mul hl.le (add_le_add_right hl.le a) (add_nonneg ha.le hb) ha.le
  have h₂ : (a-B)^2≤a^2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hl.le) ha.le).2 (sub_le_self _ hb)
  have h₃ := (deficit_bounds ha hW.le).2
  change W*(a-B)≤B*(a+B)+(a-B)^2/8 at h₃
  apply (le_div_iff₀ hW).2
  change (a-B)*W≤_
  linarith only [h₁,h₂,h₃]

/-- At large width the optimal disturbance tends to the control authority. -/
theorem tolerance_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (tolerance a) atTop (𝓝 a) := by
  have hU : Tendsto (fun W : ℝ => (17*a^2/8)/W) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x:=17*a^2/8)).mul (tendsto_inv_atTop_zero : Tendsto (fun W : ℝ => W⁻¹) atTop (𝓝 0))
  have hd : Tendsto (fun W => a-tolerance a W) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with W hW
      exact sub_nonneg.mpr (optimum ha hW).2.1.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with W hW
      exact deficit_upper ha hW
  simpa only [sub_zero,sub_sub_cancel] using (tendsto_const_nhds (x:=a)).sub hd

/-- The exact first-order loss to bounded road width is 2a²/W. -/
theorem scaled_deficit_tendsto {a : ℝ} (ha : 0<a) :
    Tendsto (fun W => W*(a-tolerance a W)) atTop (𝓝 (2*a^2)) := by
  have hB := tolerance_tendsto ha
  have hl := hB.mul ((tendsto_const_nhds (x:=a)).add hB)
  have he := (((tendsto_const_nhds (x:=a)).sub hB).pow 2).div_const 8
  have hr := hl.add he
  rw [sub_self,zero_pow (by decide),zero_div,add_zero] at hr
  rw [show 2*a^2=a*(a+a) by ring]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with W hW
    exact (deficit_bounds ha hW).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with W hW
    exact (deficit_bounds ha hW).2

end GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance

#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.tolerance_eq
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.optimum
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.tolerance_le_capacity
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.tolerance_strictMono
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.tolerance_concave
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.deficit_bounds
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.tolerance_tendsto
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.scaled_deficit_tendsto
