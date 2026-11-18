import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The projected velocity envelope for a sampled integrator

Definition 3 of Singh and Vaughan (arXiv:2610.15936) projects a set of viable
position–velocity pairs onto velocity. For an explicit-Euler integrator with
bounded acceleration, the whole set and both interpretations of its velocity
projection can be calculated exactly. Position advances with the old velocity.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.AffineDynamics.Braking

/-- Positions obtained by following a speed sequence for unit sampling periods. -/
def position (x : ℝ) (w : ℕ → ℝ) (n : ℕ) := x + ∑ k ∈ range n, w k

/-- A viable pair admits an infinite path with bounded acceleration and position. -/
def Viable (a l r x v : ℝ) : Prop := ∃ w : ℕ → ℝ, w 0 = v ∧
  (∀ k, |w (k+1)-w k| ≤ a) ∧ ∀ k, position x w k ∈ Set.Icc l r

/-- Number of positive-velocity steps under maximal braking. -/
def steps (a v : ℝ) : ℕ := ⌈v/a⌉₊

def speed (a v : ℝ) (k : ℕ) : ℝ := max 0 (v-k*a)

/-- Total forward distance traversed by the positive part of the initial velocity. -/
def distance (a v : ℝ) : ℝ := ∑ k ∈ range (steps a v), speed a v k

private theorem speed_pos_iff (a v : ℝ) (ha : 0 < a) (k : ℕ) :
    0 < v-k*a ↔ k < steps a v := by
  rw [steps,Nat.lt_ceil,lt_div_iff₀ ha,sub_pos]

theorem distance_formula (a v : ℝ) (ha : 0 < a) :
    let n : ℝ := steps a v
    distance a v = n*v-a*n*(n-1)/2 := by
  have hs (n : ℕ) : (∑ k ∈ range n, (v-(k : ℝ)*a)) =
      (n : ℝ)*v-a*n*(n-1)/2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,ih]; push_cast; ring
  calc
    _ = ∑ k ∈ range (steps a v), (v-(k : ℝ)*a) := by
      exact sum_congr rfl fun k hk => max_eq_right ((speed_pos_iff a v ha k).2 (mem_range.mp hk)).le
    _ = _ := hs _

theorem distance_nonneg (a v : ℝ) : 0 ≤ distance a v := sum_nonneg fun _ _ => le_max_left _ _

theorem distance_of_nonpos (a v : ℝ) (ha : 0 < a) (hv : v ≤ 0) : distance a v=0 := by
  have hn : steps a v=0 := Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hv ha.le)
  simp [distance,hn]

/-- A speed path with bounded acceleration cannot brake faster than a linear ramp. -/
theorem ramp_lower (a : ℝ) (w : ℕ → ℝ) (hw : ∀ k, |w (k+1)-w k| ≤ a) (n : ℕ) :
    w 0 - (n : ℝ)*a ≤ w n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (abs_le.mp (hw n)).1
    push_cast
    linarith only [ih,h]

/-- Every viable path pays the entire forward braking distance by its stopping time. -/
theorem upper_obstruction (a l r x v : ℝ) (ha : 0 < a) (h : Viable a l r x v) :
    x + distance a v ≤ r := by
  obtain ⟨w,hv,hw,hp⟩ := h
  have hh : distance a v ≤ ∑ k ∈ range (steps a v), w k := by
    apply sum_le_sum
    intro k hk
    rw [speed,max_eq_right ((speed_pos_iff a v ha k).2 (mem_range.mp hk)).le,← hv]
    exact ramp_lower a w hw k
  exact (add_le_add_right hh x).trans (hp (steps a v)).2

private theorem reflected (a l r x v : ℝ) : Viable a l r x v → Viable a (-r) (-l) (-x) (-v) := by
  rintro ⟨w,h₀,h₁,h₂⟩
  refine ⟨fun k => -w k,congrArg Neg.neg h₀,fun k => ?_,fun k => ?_⟩
  · simpa only [neg_sub_neg,abs_sub_comm] using h₁ k
  · have he : position (-x) (fun k => -w k) k = -position x w k := by
      simp [position,Finset.sum_neg_distrib]
    rw [he]
    exact ⟨neg_le_neg (h₂ k).2,neg_le_neg (h₂ k).1⟩

private theorem brake_step (a v : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    |speed a v (k+1)-speed a v k| ≤ a := by
  let z := v-(k : ℝ)*a
  have e : v-((k+1 : ℕ) : ℝ)*a = z-a := by dsimp [z]; push_cast; ring
  rw [speed,speed,e,abs_le]
  have h₁ : max 0 (z-a) ≤ max 0 z := max_le_max_left _ (sub_le_self _ ha)
  have h₂ : max 0 z ≤ max 0 (z-a)+a := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) ha
    · linarith only [le_max_right (0 : ℝ) (z-a)]
  exact ⟨by linarith only [h₂],by linarith only [h₁,ha]⟩

private theorem travel_le (a v : ℝ) (ha : 0 < a) (n : ℕ) :
    (∑ k ∈ range n, speed a v k) ≤ distance a v := by
  rcases le_total n (steps a v) with h | h
  · exact sum_le_sum_of_subset_of_nonneg (range_mono h) fun _ _ _ => le_max_left _ _
  · apply le_of_eq
    apply (sum_subset (range_mono h) ?_).symm
    intro k _ hk
    have hneg : ¬0<v-k*a := fun hp => hk (mem_range.mpr ((speed_pos_iff a v ha k).1 hp))
    exact max_eq_left (le_of_not_gt hneg)

private theorem positive_path (a l r x v : ℝ) (ha : 0 < a) (hv : 0 ≤ v)
    (hl : l ≤ x) (hr : x+distance a v ≤ r) : Viable a l r x v := by
  refine ⟨speed a v,by simp [speed,hv],brake_step a v ha.le,fun k => ?_⟩
  exact ⟨hl.trans (le_add_of_nonneg_right (sum_nonneg fun _ _ => le_max_left _ _)),
    (add_le_add_right (travel_le a v ha k) x).trans hr⟩

/-- Exact maximal viability kernel of the two-sided interval. -/
theorem viable_iff (a l r x v : ℝ) (ha : 0 < a) :
    Viable a l r x v ↔ l + distance a (-v) ≤ x ∧ x + distance a v ≤ r := by
  constructor
  · intro h
    have hh := upper_obstruction a (-r) (-l) (-x) (-v) ha (reflected _ _ _ _ _ h)
    exact ⟨by linarith only [hh],upper_obstruction a l r x v ha h⟩
  · rintro ⟨hl,hr⟩
    by_cases hv : 0 ≤ v
    · exact positive_path a l r x v ha hv ((le_add_of_nonneg_right (distance_nonneg _ _)).trans hl) hr
    · have h := positive_path a (-r) (-l) (-x) (-v) ha (by linarith)
        (by linarith only [hr,distance_nonneg a v]) (by linarith only [hl])
      simpa only [neg_neg] using reflected _ _ _ _ _ h

/-- Projecting away position retains exactly those speeds whose two braking
distances fit within the interval width. -/
theorem projected_iff (a l r v : ℝ) (ha : 0 < a) :
    (∃ x, Viable a l r x v) ↔ distance a (-v)+distance a v ≤ r-l := by
  simp only [viable_iff _ _ _ _ _ ha]
  constructor
  · rintro ⟨x,h₁,h₂⟩
    linarith only [h₁,h₂]
  · intro h
    exact ⟨_,le_rfl,by linarith only [h]⟩

/-- Keeping every initial position in the interval admits only zero initial
velocity, even when the projected envelope allows nonzero velocities. -/
theorem all_positions_iff (a l r v : ℝ) (ha : 0 < a) (hlr : l ≤ r) :
    (∀ x ∈ Set.Icc l r, Viable a l r x v) ↔ v=0 := by
  constructor
  · intro H
    obtain ⟨w₁,h₁,_,p₁⟩ := H l ⟨le_rfl,hlr⟩
    obtain ⟨w₂,h₂,_,p₂⟩ := H r ⟨hlr,le_rfl⟩
    have hL := (p₁ 1).1
    have hR := (p₂ 1).2
    simp only [position,sum_range_one,h₁,h₂] at hL hR
    linarith only [hL,hR]
  · rintro rfl x hx
    rw [viable_iff _ _ _ _ _ ha,neg_zero,distance_of_nonpos _ _ ha le_rfl,add_zero,add_zero]
    exact hx

/-- The exact correction to continuous stopping distance includes a half-step
term and a periodic quadratic term in the fractional stopping time. -/
theorem sampling_excess (a v : ℝ) (ha : 0 < a) :
    let θ := (steps a v : ℝ)-v/a
    distance a v = v^2/(2*a)+v/2+a*θ*(1-θ)/2 := by
  rw [distance_formula a v ha]
  dsimp only
  field_simp
  ring

/-- The rounding part of the braking penalty lies between zero and a/8,
uniformly in the initial forward velocity. -/
theorem sampling_bounds (a v : ℝ) (ha : 0 < a) (hv : 0 ≤ v) :
    v^2/(2*a)+v/2 ≤ distance a v ∧ distance a v ≤ v^2/(2*a)+v/2+a/8 := by
  let θ := (steps a v : ℝ)-v/a
  have h₀ : 0 ≤ θ := sub_nonneg.mpr (Nat.le_ceil _)
  have h₁ : θ < 1 := by
    have h := Nat.ceil_lt_add_one (div_nonneg hv ha.le)
    dsimp only [θ,steps]
    linarith only [h]
  have hh : θ*(1-θ) ≤ 1/4 := by nlinarith only [sq_nonneg (θ-1/2)]
  have e := sampling_excess a v ha
  change distance a v = v^2/(2*a)+v/2+a*θ*(1-θ)/2 at e
  constructor
  · linarith only [e,mul_nonneg ha.le (mul_nonneg h₀ (sub_nonneg.mpr h₁.le))]
  · linarith only [e,mul_le_mul_of_nonneg_left hh ha.le]

/-- The velocity equal to one full acceleration step is viable at exactly the
left endpoint of an interval of the same width. -/
theorem extreme_speed_fiber (a x : ℝ) (ha : 0 < a) :
    Viable a 0 a x a ↔ x=0 := by
  have hn : steps a a=1 := by simp [steps,div_self ha.ne']
  have hd : distance a a=a := by simp [distance,hn,speed,ha.le]
  rw [viable_iff _ _ _ _ _ ha,distance_of_nonpos _ _ ha (neg_nonpos.mpr ha.le),hd]
  constructor
  · rintro ⟨h₁,h₂⟩
    linarith only [h₁,h₂]
  · rintro rfl
    simp

end GaloisForLFunctions.HTGeometry.AffineDynamics.Braking

#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.distance_formula
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.distance_nonneg
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.distance_of_nonpos
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.ramp_lower
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.upper_obstruction
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.viable_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.projected_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.all_positions_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.sampling_excess
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.sampling_bounds
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.extreme_speed_fiber
