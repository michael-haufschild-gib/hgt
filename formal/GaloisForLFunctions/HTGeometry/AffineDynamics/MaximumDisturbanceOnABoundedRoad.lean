import GaloisForLFunctions.HTGeometry.AffineDynamics.DisturbanceWidthForSampledBraking

/-!
# The largest acceleration error permitted on a bounded road

For control authority a>0 the width at which the critical stopping horizon
changes from n to n+1 is a·n(n+1)/(n+2). Between successive widths the
largest robust disturbance is affine in the road width. Its slope on
the n-step interval is 2/(n(n+3)). In particular the width certificate
can be inverted without an infinite-horizon optimization.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance

/-- Critical width at which two adjacent stopping horizons tie. -/
def knot (a : ℝ) (j : ℕ) : ℝ := a*j*(j+1)/(j+2)

/-- Largest disturbance on the interval between knots j and j+1. -/
def capacity (a W : ℝ) (j : ℕ) : ℝ :=
  (2*W+a*(j+1)*j)/((j+1)*(j+4))

/-- Shrinking the disturbance interval preserves every robustly viable state. -/
theorem robust_mono {a b B l r x v : ℝ} (hb : b≤B) :
    Robust a B l r x v → Robust a b l r x v := by
  rintro ⟨S,hx,hS⟩
  refine ⟨S,hx,?_⟩
  rintro ⟨y,w⟩ h
  obtain ⟨hy,u,hu,he⟩ := hS h
  exact ⟨hy,u,hu,fun e he' => he e ⟨(neg_le_neg hb).trans he'.1,he'.2.trans hb⟩⟩

/-- The discrete ramp reaches its maximum at n whenever the signed speed
lies between (n−1)d and nd. At a boundary either adjacent horizon works. -/
theorem ramp_peak (d v : ℝ) (hd : 0<d) (n : ℕ) (lo : d*((n : ℝ)-1)≤v)
    (hi : v≤d*n) : distance d v=ramp d v n := by
  apply le_antisymm
  · apply (distance_le_iff _ _ _ hd).2
    intro m
    have diff : ramp d v m-ramp d v n =
        ((m : ℝ)-n)*(v-d*((m : ℝ)+n-1)/2) := by unfold ramp; ring
    apply sub_nonpos.mp
    rw [diff]
    rcases lt_trichotomy m n with h | rfl | h
    · have hm : (m : ℝ)+1≤n := by exact_mod_cast h
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith only [hm])
      linarith only [lo,mul_nonneg hd.le (show 0≤(n : ℝ)-m-1 by linarith only [hm])]
    · rw [sub_self,zero_mul]
    · have hm : (n : ℝ)+1≤m := by exact_mod_cast h
      apply mul_nonpos_of_nonneg_of_nonpos (by linarith only [hm])
      linarith only [hi,mul_nonneg hd.le (show 0≤(m : ℝ)-n-1 by linarith only [hm])]
  · exact (distance_le_iff _ _ _ hd).1 le_rfl n

private theorem width_interval {a W : ℝ} (j : ℕ) (lo : knot a j≤W) (hi : W≤knot a (j+1)) :
    a*(j : ℝ)*(j+1)≤W*(j+2) ∧ W*(j+3)≤a*(j+1)*(j+2) := by
  have hj : 0≤(j : ℝ) := Nat.cast_nonneg _
  unfold knot at lo hi
  rw [Nat.cast_succ] at hi
  have hl := (div_le_iff₀ (by positivity)).1 lo
  have hh := (le_div_iff₀ (by positivity)).1 hi
  exact ⟨hl,by linarith only [hh]⟩

private theorem capacity_times (a W : ℝ) (j : ℕ) :
    capacity a W j*((j+1)*(j+4))=2*W+a*(j+1)*j :=
  (div_mul_cancel₀ _ (by positivity : ((j : ℝ)+1)*(j+4)≠0))

private theorem capacity_speeds {a W : ℝ} (ha : 0<a) (j : ℕ)
    (lo : knot a j≤W) (hi : W≤knot a (j+1)) :
    0≤capacity a W j ∧ capacity a W j<a ∧
      (a-capacity a W j)*j≤2*capacity a W j ∧
      2*capacity a W j≤(a-capacity a W j)*(j+1) := by
  let m : ℝ := j
  let B := capacity a W j
  have hm : 0≤m := Nat.cast_nonneg _
  have hD : 0<(m+1)*(m+4) := by positivity
  obtain ⟨hl,hh⟩ := width_interval j lo hi
  change a*m*(m+1)≤W*(m+2) at hl
  change W*(m+3)≤a*(m+1)*(m+2) at hh
  have hw : 0≤W := (div_nonneg (by positivity) (by positivity) : 0≤knot a j).trans lo
  have hb : 0≤B := div_nonneg (by change 0≤2*W+a*(m+1)*m; positivity) hD.le
  have h₀ : a*m/(m+2)≤B := by
    change _≤(2*W+a*(m+1)*m)/((m+1)*(m+4))
    apply (div_le_div_iff₀ (by positivity) hD).2
    linarith only [hl]
  have h₁ : B≤a*(m+1)/(m+3) := by
    change (2*W+a*(m+1)*m)/((m+1)*(m+4))≤_
    apply (div_le_div_iff₀ hD (by positivity)).2
    linarith only [hh]
  have h₀' := (div_le_iff₀ (by positivity)).1 h₀
  have h₁' := (le_div_iff₀ (by positivity)).1 h₁
  have hba : B<a := lt_of_le_of_lt h₁ ((div_lt_iff₀ (by positivity)).2 (by linarith only [ha]))
  exact ⟨hb,hba,by linarith only [h₀'],by linarith only [h₁']⟩

/-- At the maximum disturbance the worst-case stopping distance exactly
fills the road, including at both ends of each width interval. -/
theorem capacity_fills_width {a W : ℝ} (ha : 0<a) (j : ℕ)
    (lo : knot a j≤W) (hi : W≤knot a (j+1)) :
    distance (a-capacity a W j) (2*capacity a W j)=W := by
  obtain ⟨_,hb,h₀,h₁⟩ := capacity_speeds ha j lo hi
  rw [ramp_peak _ _ (sub_pos.mpr hb) (j+1) (by simpa using h₀) (by simpa using h₁)]
  unfold ramp
  rw [Nat.cast_succ]
  linarith only [capacity_times a W j]

/-- The admissible disturbances form a closed interval with the stated
right endpoint, allowing arbitrarily large proposed disturbances. -/
theorem fits_iff {a b l r : ℝ} (ha : 0<a) (hb : 0≤b) (j : ℕ)
    (lo : knot a j≤r-l) (hi : r-l≤knot a (j+1)) :
    (∃ x v, Robust a b l r x v) ↔ b≤capacity a (r-l) j := by
  constructor
  · rintro ⟨x,v,h⟩
    have hw := necessary_width hb h (j+1)
    simp only [ramp,Nat.cast_succ] at hw
    unfold capacity
    apply (le_div_iff₀ (by positivity)).2
    linarith only [hw]
  · intro h
    obtain ⟨h₀,h₁,_,_⟩ := capacity_speeds ha j lo hi
    obtain ⟨x,v,hV⟩ := (nonempty_iff h₀ h₁).2 (capacity_fills_width ha j lo hi).le
    exact ⟨x,v,robust_mono h hV⟩

/-- The explicit intervals cover every nonnegative width. -/
theorem exists_width_interval {a W : ℝ} (ha : 0<a) (hW : 0≤W) :
    ∃ j : ℕ, knot a j≤W ∧ W≤knot a (j+1) := by
  classical
  obtain ⟨j,hj⟩ := exists_nat_gt (W/a)
  have h₁ : W<a*j := by simpa only [mul_comm a] using (div_lt_iff₀ ha).1 hj
  have h₂ : a*j≤knot a (j+1) := by
    unfold knot
    rw [Nat.cast_succ]
    apply (le_div_iff₀ (by positivity)).2
    linarith only [ha]
  have hex : ∃ j : ℕ, W≤knot a (j+1) := ⟨j,h₁.le.trans h₂⟩
  let m := Nat.find hex
  have hm : W≤knot a (m+1) := Nat.find_spec hex
  refine ⟨m,?_,hm⟩
  cases he : m with
  | zero => simpa [knot] using hW
  | succ k =>
    have hk : k<Nat.find hex := by change k<m; omega
    exact le_of_not_ge (Nat.find_min hex hk)

/-- Consecutive slopes are strictly decreasing. Each additional unit of
road length buys less disturbance tolerance on the next interval. -/
theorem slope_drop (j : ℕ) :
    2/(((j : ℝ)+2)*(j+5)) < 2/((j+1)*(j+4)) := by
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  linarith only [Nat.cast_nonneg (R:=ℝ) j]

end GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance

#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.robust_mono
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.ramp_peak
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.capacity_fills_width
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.fits_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.exists_width_interval
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.slope_drop
