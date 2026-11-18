import GaloisForLFunctions.HTGeometry.AffineDynamics.SampledBrakingViability
import GaloisForLFunctions.HTGeometry.ConstitutiveEndogenousViability

/-!
# Minimum road width under adversarial acceleration errors

A control chooses the next speed u with |u−v| ≤ a. An adversary then
adds any error in [−b,b], while position advances by the old speed v.
When a>b, robust viability coincides with ordinary braking at rate a−b
on roads of width at least the stopping distance from speed 2b. On
narrower roads even a single robustly viable state is impossible.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance

/-- Signed distance of the untruncated braking ramp during n steps. -/
def ramp (d v : ℝ) (n : ℕ) : ℝ := n*v-d*n*((n : ℝ)-1)/2

private theorem ramp_succ (d v : ℝ) (n : ℕ) :
    ramp d v (n+1) = v+ramp d (v-d) n := by unfold ramp; push_cast; ring

private theorem ramp_mono (d : ℝ) (n : ℕ) : Monotone (fun v => ramp d v n) :=
  fun _ _ h => sub_le_sub_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)) _

/-- Stopping distance is the largest of all signed ramp distances, including
the zero-step distance. The maximizing horizon is the rounded stopping time. -/
theorem distance_le_iff (d v L : ℝ) (hd : 0<d) :
    distance d v ≤ L ↔ ∀ n, ramp d v n ≤ L := by
  constructor
  · intro h n
    have path := (viable_iff d (-distance d (-v)) (distance d v) 0 v hd).2
      ⟨by linarith,by simp⟩
    obtain ⟨w,hw,ha,hp⟩ := path
    have hr (m : ℕ) : (∑ k ∈ range m, (v-k*d))=ramp d v m := by
      induction m with
      | zero => simp [ramp]
      | succ m ih => rw [sum_range_succ,ih]; unfold ramp; push_cast; ring
    rw [← hr n]
    refine (sum_le_sum fun k _ => ?_).trans ((show (∑ k ∈ range n,w k) ≤ distance d v by
      simpa only [position,zero_add] using (hp n).2).trans h)
    simpa only [hw] using ramp_lower d w ha k
  · intro H
    simpa only [distance_formula d v hd,ramp] using H (steps d v)

/-- Half-plane description of the ordinary stopping envelope. -/
def strip (d l r : ℝ) (x v : ℝ) :=
  ∀ n, l+ramp d (-v) n ≤ x ∧ x+ramp d v n ≤ r

theorem strip_iff (d l r x v : ℝ) (hd : 0<d) : strip d l r x v ↔ Viable d l r x v := by
  rw [viable_iff _ _ _ _ _ hd]
  have low := distance_le_iff d (-v) (x-l) hd
  have high := distance_le_iff d v (r-x) hd
  constructor
  · intro h
    exact ⟨by linarith only [low.2 (fun n => by linarith only [(h n).1])],
      by linarith only [high.2 (fun n => by linarith only [(h n).2])]⟩
  · rintro ⟨hl,hr⟩ n
    exact ⟨by linarith only [low.1 (by linarith only [hl]) n],
      by linarith only [high.1 (by linarith only [hr]) n]⟩

def predecessor (a b l r : ℝ) (S : Set (ℝ × ℝ)) :=
  endogenousPredecessor {p : ℝ × ℝ | p.1 ∈ Set.Icc l r} (fun p u => |u-p.2| ≤ a)
    (fun _ _ => Set.Icc (-b) b) (fun p u e => (p.1+p.2,u+e)) S

/-- Membership in some robust controlled invariant, equivalently in the
greatest one, allows a single choice before every disturbance. -/
def Robust (a b l r x v : ℝ) : Prop :=
  ∃ S : Set (ℝ × ℝ), (x,v) ∈ S ∧ S ⊆ predecessor a b l r S

private theorem next_mem {a b l r : ℝ} {S : Set (ℝ × ℝ)} (hS : S ⊆ predecessor a b l r S)
    {x v : ℝ} (hp : (x,v) ∈ S) :
    x ∈ Set.Icc l r ∧ ∃ u, |u-v|≤a ∧ ∀ e ∈ Set.Icc (-b) b, (x+v,u+e) ∈ S := hS hp

/-- Sustained positive and negative disturbance force both signed ramp
bounds on every robust controlled invariant. -/
theorem invariant_ramps {a b l r : ℝ} (hb : 0≤b) {S : Set (ℝ × ℝ)}
    (hS : S ⊆ predecessor a b l r S) {x v : ℝ} (hp : (x,v) ∈ S) :
    strip (a-b) l r x v := by
  intro n
  induction n generalizing x v with
  | zero => simpa [ramp] using (next_mem hS hp).1
  | succ n ih =>
    obtain ⟨_,u,hu,h⟩ := next_mem hS hp
    have h₁ := (ih (h (-b) ⟨le_rfl,by linarith only [hb]⟩)).1
    have h₂ := (ih (h b ⟨by linarith only [hb],le_rfl⟩)).2
    have hl := ramp_mono (a-b) n (show -v-(a-b) ≤ -(u+ -b) by linarith only [(abs_le.mp hu).2])
    have hr := ramp_mono (a-b) n (show v-(a-b) ≤ u+b by linarith only [(abs_le.mp hu).1])
    rw [ramp_succ,ramp_succ]
    constructor <;> linarith only [h₁,h₂,hl,hr]

/-- Any nonempty robust invariant requires the full stopping width from
speed 2b. The statement in ramps also applies when braking authority vanishes. -/
theorem necessary_width {a b l r x v : ℝ} (hb : 0≤b) (H : Robust a b l r x v) (n : ℕ) :
    ramp (a-b) (2*b) n ≤ r-l := by
  obtain ⟨S,hp,hS⟩ := H
  let B := (fun z : ℝ × ℝ => z.1+z.2) '' S
  have memB {y w : ℝ} (h : (y,w) ∈ S) : y+w ∈ B := ⟨(y,w),h,rfl⟩
  have safe {y w : ℝ} (h : (y,w) ∈ S) : y+w ∈ Set.Icc l r := by
    obtain ⟨_,u,_,hc⟩ := next_mem hS h
    exact (next_mem hS (hc 0 ⟨neg_nonpos.mpr hb,hb⟩)).1
  have upper : ∀ y ∈ B, y≤r := by rintro _ ⟨⟨x,v⟩,h,rfl⟩; exact (safe h).2
  have hbdd : BddAbove B := ⟨r,upper⟩
  have hne : B.Nonempty := ⟨_,memB hp⟩
  let M := sSup B
  by_cases hn : n=0
  · subst n
    simpa [ramp] using sub_nonneg.mpr ((safe hp).1.trans (safe hp).2)
  have hn' : (0 : ℝ)<n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu : M ≤ M+(r-l-ramp (a-b) (2*b) n)/n := by
    apply csSup_le hne
    rintro _ ⟨⟨y,w⟩,hy,rfl⟩
    obtain ⟨_,u,_,hc⟩ := next_mem hS hy
    have hhi : y+w+(u+b) ≤ M := le_csSup hbdd (memB (hc b ⟨by linarith only [hb],le_rfl⟩))
    have hlo := (invariant_ramps hb hS (hc (-b) ⟨le_rfl,by linarith only [hb]⟩) n).1
    have ht := ramp_mono (a-b) n (show 2*b+(y+w)-M ≤ -(u+ -b) by linarith only [hhi])
    apply (sub_le_iff_le_add').1
    apply (le_div_iff₀ hn').2
    dsimp only [ramp] at ht hlo ⊢
    linarith only [hlo,ht,(safe hy).2]
  have hz : 0 ≤ (r-l-ramp (a-b) (2*b) n)/n := by linarith only [hu]
  exact sub_nonneg.mp ((div_nonneg_iff_of_pos_right hn').mp hz)

private theorem interpolate {d l r x y v w : ℝ}
    (hx : strip d l r x v) (hy : strip d l r y w) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    strip d l r ((1-t)*x+t*y) ((1-t)*v+t*w) := by
  intro n
  have h₁ := mul_le_mul_of_nonneg_left (hx n).1 (sub_nonneg.mpr ht.2)
  have h₂ := mul_le_mul_of_nonneg_left (hy n).1 ht.1
  have h₃ := mul_le_mul_of_nonneg_left (hx n).2 (sub_nonneg.mpr ht.2)
  have h₄ := mul_le_mul_of_nonneg_left (hy n).2 ht.1
  dsimp only [ramp] at h₁ h₂ h₃ h₄ ⊢
  constructor <;> linarith only [h₁,h₂,h₃,h₄]

/-- Every vertical section contains a speed interval of length 2b. The
endpoint intervals interpolate inside the convex stopping envelope. -/
theorem buffer {d b l r y : ℝ} (hd : 0<d) (hb : 0≤b) (hy : y ∈ Set.Icc l r)
    (hW : distance d (2*b) ≤ r-l) :
    ∃ m, strip d l r y (m-b) ∧ strip d l r y (m+b) := by
  have zero_at (x : ℝ) (hx : x ∈ Set.Icc l r) : strip d l r x 0 := by
    rw [strip_iff _ _ _ _ _ hd,viable_iff _ _ _ _ _ hd]
    simpa [distance_of_nonpos d 0 hd le_rfl] using hx
  have hneg : distance d (-(2*b))=0 := distance_of_nonpos _ _ hd (by linarith only [hb])
  have left : strip d l r l (2*b) := by
    rw [strip_iff _ _ _ _ _ hd,viable_iff _ _ _ _ _ hd,hneg,add_zero]
    exact ⟨le_rfl,by linarith only [hW]⟩
  have right : strip d l r r (-(2*b)) := by
    rw [strip_iff _ _ _ _ _ hd,viable_iff _ _ _ _ _ hd,neg_neg,hneg,add_zero]
    exact ⟨by linarith only [hW],le_rfl⟩
  have lr := hy.1.trans hy.2
  obtain ⟨t,ht,he⟩ : ∃ t ∈ Set.Icc (0 : ℝ) 1, (1-t)*l+t*r=y := by
    rcases lr.eq_or_lt with he | hlt
    · have ey : y=l := hy.2.trans_eq he.symm |>.antisymm hy.1
      exact ⟨0,⟨le_rfl,zero_le_one⟩,by simp [ey]⟩
    · have hp := sub_pos.mpr hlt
      exact ⟨(y-l)/(r-l),⟨div_nonneg (sub_nonneg.mpr hy.1) hp.le,
        (div_le_one hp).2 (sub_le_sub_right hy.2 l)⟩,by field_simp [hp.ne']; ring⟩
  refine ⟨b-2*t*b,?_,?_⟩
  · have h := interpolate (zero_at l ⟨le_rfl,lr⟩) right ht
    rwa [he,show (1-t)*0+t* -(2*b)=(b-2*t*b)-b by ring] at h
  · have h := interpolate left (zero_at r ⟨lr,le_rfl⟩) ht
    rwa [he,show (1-t)*(2*b)+t*0=(b-2*t*b)+b by ring] at h

/-- The safe command can be chosen by clamping the center of a surviving
speed interval to the acceleration limits. -/
theorem strip_invariant {a b l r : ℝ} (hb : 0≤b) (hd : b<a)
    (hW : distance (a-b) (2*b) ≤ r-l) :
    {z : ℝ × ℝ | strip (a-b) l r z.1 z.2} ⊆
      predecessor a b l r {z | strip (a-b) l r z.1 z.2} := by
  rintro ⟨x,v⟩ h
  change strip (a-b) l r x v at h
  have h₀ : x ∈ Set.Icc l r := by simpa [ramp] using h 0
  have h₁ : x+v ∈ Set.Icc l r := by
    have h1 := h 1
    simp only [ramp,Nat.cast_one,one_mul,mul_one,sub_self,mul_zero,zero_div,sub_zero] at h1
    exact ⟨by linarith only [h1.1],h1.2⟩
  obtain ⟨m,ml,mh⟩ := buffer (sub_pos.mpr hd) hb h₁ hW
  let u := min (max m (v-a)) (v+a)
  have ha := hb.trans hd.le
  have hu : |u-v|≤a := abs_le.mpr ⟨by
    have h : v-a ≤ u := le_min (le_max_right _ _) (by linarith only [ha])
    linarith only [h],by
    have h : u ≤ v+a := min_le_right _ _
    linarith only [h]⟩
  refine ⟨h₀,u,hu,fun e he n => ?_⟩
  have hi := h (n+1)
  rw [ramp_succ,ramp_succ] at hi
  have boundL : l+ramp (a-b) (-(v+a-b)) n ≤ x+v := by
    rw [show -(v+a-b)= -v-(a-b) by ring]
    linarith only [hi.1]
  have boundR : x+v+ramp (a-b) (v-a+b) n ≤ r := by
    rw [show v-a+b=v-(a-b) by ring]
    linarith only [hi.2]
  constructor
  · rcases le_total (max m (v-a)) (v+a) with hc | hc
    · have hv : -(u+e) ≤ -(m-b) := by
        dsimp only [u]; rw [min_eq_left hc]
        linarith only [le_max_left m (v-a),he.1]
      exact (add_le_add_right (ramp_mono _ _ hv) l).trans (ml n).1
    · have hv : -(u+e) ≤ -(v+a-b) := by
        dsimp only [u]; rw [min_eq_right hc]; linarith only [he.1]
      exact (add_le_add_right (ramp_mono _ _ hv) l).trans boundL
  · rcases le_total m (v-a) with hc | hc
    · have hv : u+e ≤ v-a+b := by
        have hu' : u ≤ v-a := (min_le_left _ _).trans_eq (max_eq_right hc)
        linarith only [hu',he.2]
      exact (add_le_add_right (ramp_mono _ _ hv) (x+v)).trans boundR
    · have hv : u+e ≤ m+b := by
        have hu' : u ≤ m := (min_le_left _ _).trans_eq (max_eq_left hc)
        linarith only [hu',he.2]
      exact (add_le_add_right (ramp_mono _ _ hv) (x+v)).trans (mh n).2

/-- Exact robust kernel. The width condition is independent of the initial
state and the remaining state inequalities are ordinary braking with the
effective acceleration a−b. -/
theorem robust_iff {a b l r x v : ℝ} (hb : 0≤b) (hd : b<a) :
    Robust a b l r x v ↔ distance (a-b) (2*b) ≤ r-l ∧ Viable (a-b) l r x v := by
  have hd' := sub_pos.mpr hd
  constructor
  · intro H
    have hw := (distance_le_iff _ _ _ hd').2 (necessary_width hb H)
    obtain ⟨S,hp,hS⟩ := H
    exact ⟨hw,(strip_iff _ _ _ _ _ hd').1 (invariant_ramps hb hS hp)⟩
  · rintro ⟨hW,hv⟩
    exact ⟨_,(strip_iff _ _ _ _ _ hd').2 hv,strip_invariant hb hd hW⟩

end GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance

#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.distance_le_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.strip_iff
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.invariant_ramps
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.necessary_width
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.buffer
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.strip_invariant
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.Disturbance.robust_iff
