import GaloisForLFunctions.HTGeometry.AffineDynamics.SampledBrakingViability
import GaloisForLFunctions.HTGeometry.ConstitutiveEndogenousViability

/-!
# Exact stabilization horizon for sampled braking

For unit sampling periods, an interval of width W has reached its infinite
viability kernel after n positive steps exactly when W ≤ a n(n+1)/2.
The converse has an explicit witness at the left endpoint that survives
exactly n steps. The control is the next velocity.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry.AffineDynamics.Braking

/-- Forward distance paid during the first n steps of maximal braking. -/
def prefix (a v : ℝ) (n : ℕ) := ∑ k ∈ range n, speed a v k

private theorem prefix_zero_of_nonpos (a v : ℝ) (ha : 0 ≤ a) (hv : v ≤ 0) (n : ℕ) :
    prefix a v n = 0 := by
  apply sum_eq_zero
  intro k _
  exact max_eq_left (sub_nonpos.mpr (hv.trans (mul_nonneg (Nat.cast_nonneg k) ha)))

private theorem prefix_nonneg (a v : ℝ) (n : ℕ) : 0 ≤ prefix a v n :=
  sum_nonneg fun _ _ => le_max_left _ _

private theorem prefix_mono (a : ℝ) (n : ℕ) : Monotone (fun v => prefix a v n) := by
  intro v w h
  exact sum_le_sum fun _ _ => max_le_max_left _ (sub_le_sub_right h _)

private theorem prefix_shift (a v : ℝ) (n : ℕ) :
    prefix a v (n+1) = max 0 v + prefix a (v-a) n := by
  unfold prefix
  rw [sum_range_succ']
  simp only [speed, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, sub_zero]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro k _
  congr 1
  ring

/-- Each finite horizon has two explicit braking boundaries. -/
def band (a l r : ℝ) (n : ℕ) : Set (ℝ × ℝ) :=
  {p | l + prefix a (-p.2) n ≤ p.1 ∧ p.1 + prefix a p.2 n ≤ r}

def road (l r : ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc l r}

def predecessor (a l r : ℝ) : Set (ℝ × ℝ) → Set (ℝ × ℝ) :=
  endogenousPredecessor (road l r) (fun p u => |u-p.2| ≤ a)
    (fun _ _ => (Set.univ : Set Unit)) (fun p u _ => (p.1+p.2,u))

private theorem step_iff (a l r x v : ℝ) (S : Set (ℝ × ℝ)) :
    (x,v) ∈ predecessor a l r S ↔ x ∈ Set.Icc l r ∧ ∃ u, |u-v| ≤ a ∧ (x+v,u) ∈ S := by
  simp [predecessor,endogenousPredecessor,endogenousControlSet,road,Set.Nonempty]

private theorem reflected_band (a l r x v : ℝ) (n : ℕ) :
    (-x,-v) ∈ band a (-r) (-l) n ↔ (x,v) ∈ band a l r n := by
  change -r + prefix a (- -v) n ≤ -x ∧ -x + prefix a (-v) n ≤ -l ↔ _
  rw [neg_neg]
  change _ ↔ l + prefix a (-v) n ≤ x ∧ x + prefix a v n ≤ r
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]

private theorem reflected_step (a l r x v : ℝ) (n : ℕ) :
    (x,v) ∈ predecessor a l r (band a l r n) →
      (-x,-v) ∈ predecessor a (-r) (-l) (band a (-r) (-l) n) := by
  rw [step_iff,step_iff]
  rintro ⟨hx,u,hu,h⟩
  refine ⟨⟨neg_le_neg hx.2,neg_le_neg hx.1⟩,-u,?_,?_⟩
  · simpa only [neg_sub_neg,abs_sub_comm] using hu
  · simpa only [neg_add_rev,add_comm] using (reflected_band _ _ _ _ _ _).2 h

private theorem positive_step (a l r x v : ℝ) (ha : 0 ≤ a) (hv : 0 ≤ v) (n : ℕ) :
    (x,v) ∈ predecessor a l r (band a l r n) ↔ (x,v) ∈ band a l r (n+1) := by
  rw [step_iff]
  change _ ↔ l + prefix a (-v) (n+1) ≤ x ∧ x + prefix a v (n+1) ≤ r
  rw [prefix_zero_of_nonpos _ _ ha (neg_nonpos.mpr hv),add_zero,prefix_shift,max_eq_right hv]
  constructor
  · rintro ⟨hx,u,hu,_,hr⟩
    have h := prefix_mono a n (show v-a ≤ u by linarith only [(abs_le.mp hu).1])
    change x+v+prefix a u n ≤ r at hr
    exact ⟨hx.1,by linarith only [h,hr]⟩
  · rintro ⟨hl,hr⟩
    let u := max 0 (v-a)
    have hu : 0 ≤ u := le_max_left _ _
    have he : prefix a u n = prefix a (v-a) n := by
      by_cases h : 0 ≤ v-a
      · rw [show u = v-a from max_eq_right h]
      · rw [prefix_zero_of_nonpos _ _ ha (le_of_not_ge h),
          show u=0 from max_eq_left (le_of_not_ge h),prefix_zero_of_nonpos _ _ ha le_rfl]
    refine ⟨⟨hl,by linarith only [hr,hv,prefix_nonneg a (v-a) n]⟩,u,abs_le.mpr ⟨?_,?_⟩,?_,?_⟩
    · linarith only [le_max_right (0 : ℝ) (v-a)]
    · have hh : u ≤ v := max_le hv (sub_le_self _ ha)
      linarith only [hh,ha]
    · change l+prefix a (-u) n ≤ x+v
      rw [prefix_zero_of_nonpos _ _ ha (neg_nonpos.mpr hu),add_zero]
      exact hl.trans (le_add_of_nonneg_right hv)
    · change x+v+prefix a u n ≤ r
      rw [he,add_assoc]
      exact hr

theorem predecessor_band (a l r : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    predecessor a l r (band a l r n) = band a l r (n+1) := by
  ext ⟨x,v⟩
  rcases le_total 0 v with hv | hv
  · exact positive_step a l r x v ha hv n
  · have h := positive_step a (-r) (-l) (-x) (-v) ha (neg_nonneg.mpr hv) n
    rw [reflected_band] at h
    refine ⟨fun hs => h.1 (reflected_step _ _ _ _ _ _ hs),fun hs => ?_⟩
    simpa only [neg_neg] using reflected_step _ _ _ _ _ _ (h.2 hs)

theorem horizon_eq (a l r : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    viabilityHorizon (predecessor a l r) (road l r) n = band a l r n := by
  induction n with
  | zero => ext p; simp [road,band,prefix]
  | succ n ih => rw [viabilityHorizon_succ,ih,predecessor_band a l r ha]

/-- Above the last braking threshold, the finite envelope is affine in velocity. -/
theorem prefix_affine (a v : ℝ) (ha : 0 ≤ a) (n : ℕ) (h : (n : ℝ)*a ≤ v) :
    prefix a v n = (n : ℝ)*v-a*n*((n : ℝ)-1)/2 := by
  induction n with
  | zero => simp [prefix]
  | succ n ih =>
    push_cast at h ⊢
    have hn : (n : ℝ)*a ≤ v := by linarith only [h,ha]
    change (∑ k ∈ range (n+1),speed a v k) = _
    rw [sum_range_succ,show (∑ k ∈ range n,speed a v k)=_ from ih hn,
      speed,max_eq_right (sub_nonneg.mpr hn)]
    ring

private theorem prefix_stopped (a v : ℝ) (ha : 0 < a) (n : ℕ) (hv : v ≤ (n : ℝ)*a) :
    prefix a v n = distance a v := by
  have h : steps a v ≤ n := Nat.ceil_le.mpr ((div_le_iff₀ ha).2 hv)
  apply (sum_subset (range_mono h) ?_).symm
  intro k _ hk
  have h' : steps a v ≤ k := Nat.le_of_not_gt fun hh => hk (mem_range.mpr hh)
  have hk' : v/a ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h')
  exact max_eq_left (sub_nonpos.mpr ((div_le_iff₀ ha).1 hk'))

private theorem stops_at_width (a v W : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 0 < n)
    (hW : W ≤ a*n*((n : ℝ)+1)/2) (hv : prefix a v n ≤ W) : v ≤ (n : ℝ)*a := by
  by_contra! h
  rw [prefix_affine a v ha n h.le] at hv
  have hp : 0 < (n : ℝ)*(v-n*a) := mul_pos (Nat.cast_pos.mpr hn) (sub_pos.mpr h)
  linarith only [hp,hW,hv]

/-- Width at or below the triangular threshold forces both finite braking
distances to equal their infinite counterparts. -/
theorem horizon_eq_kernel (a l r : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n)
    (hW : r-l ≤ a*n*((n : ℝ)+1)/2) :
    viabilityHorizon (predecessor a l r) (road l r) n = {p | Viable a l r p.1 p.2} := by
  rw [horizon_eq a l r ha.le]
  ext ⟨x,v⟩
  rw [Set.mem_setOf_eq,viable_iff _ _ _ _ _ ha]
  change (l+prefix a (-v) n ≤ x ∧ x+prefix a v n ≤ r) ↔ _
  constructor
  · rintro ⟨hl,hr⟩
    have h (w : ℝ) (hw : prefix a w n ≤ r-l) :=
      prefix_stopped a w ha n (stops_at_width a w _ ha.le n hn hW hw)
    rw [← h (-v) (by linarith only [hl,hr,prefix_nonneg a v n]),
        ← h v (by linarith only [hl,hr,prefix_nonneg a (-v) n])]
    exact ⟨hl,hr⟩
  · rintro ⟨hl,hr⟩
    have bound (w : ℝ) : prefix a w n ≤ distance a w := by
      by_cases h : w ≤ (n : ℝ)*a
      · exact (prefix_stopped a w ha n h).le
      · have hs : n ≤ steps a w := ((Nat.lt_ceil).2 ((lt_div_iff₀ ha).2 (lt_of_not_ge h))).le
        exact sum_le_sum_of_subset_of_nonneg (range_mono hs) fun _ _ _ => le_max_left _ _
    exact ⟨by linarith only [hl,bound (-v)],by linarith only [hr,bound v]⟩

/-- Above threshold the boundary velocity at the left endpoint survives
exactly n steps before the next predecessor removes it. -/
theorem strict_witness (a l r : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n)
    (hW : a*n*((n : ℝ)+1)/2 < r-l) :
    ∃ v, (l,v) ∈ band a l r n ∧ (l,v) ∉ band a l r (n+1) := by
  let v := ((r-l)+a*n*((n : ℝ)-1)/2)/n
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hv : (n : ℝ)*a < v := (lt_div_iff₀ hn').2 (by linarith only [hW])
  have hv₀ := (mul_nonneg hn'.le ha.le).trans hv.le
  have hv' : (n : ℝ)*v = (r-l)+a*n*((n : ℝ)-1)/2 := by
    dsimp only [v]
    field_simp
  have he : prefix a v n = r-l := by
    rw [prefix_affine a v ha.le n hv.le,hv']
    ring
  refine ⟨v,⟨?_,?_⟩,fun h => ?_⟩
  · change l+prefix a (-v) n ≤ l
    rw [prefix_zero_of_nonpos _ _ ha.le (neg_nonpos.mpr hv₀),add_zero]
  · change l+prefix a v n ≤ r
    linarith only [he]
  · have hr := h.2
    change l+(∑ k ∈ range (n+1),speed a v k) ≤ r at hr
    rw [sum_range_succ,show (∑ k ∈ range n,speed a v k)=r-l from he,
      speed,max_eq_right (sub_nonneg.mpr hv.le)] at hr
    linarith only [hr,hv]

/-- Sharp test for finite stabilization of the endogenous predecessor. -/
theorem plateau_iff (a l r : ℝ) (ha : 0 < a) (n : ℕ) (hn : 0 < n) :
    viabilityHorizon (predecessor a l r) (road l r) (n+1) =
      viabilityHorizon (predecessor a l r) (road l r) n ↔ r-l ≤ a*n*((n : ℝ)+1)/2 := by
  constructor
  · intro h
    by_contra! hW
    obtain ⟨v,hv,hv'⟩ := strict_witness a l r ha n hn hW
    rw [horizon_eq _ _ _ ha.le,horizon_eq _ _ _ ha.le] at h
    exact hv' (h ▸ hv)
  · intro hW
    have h : r-l ≤ a*(n+1 : ℕ)*(((n+1 : ℕ) : ℝ)+1)/2 := by
      push_cast
      linarith only [hW,mul_nonneg ha.le (Nat.cast_nonneg n),ha.le]
    rw [horizon_eq_kernel _ _ _ ha _ (Nat.succ_pos _) h,horizon_eq_kernel _ _ _ ha n hn hW]

end GaloisForLFunctions.HTGeometry.AffineDynamics.Braking

#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.predecessor_band
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.horizon_eq
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.prefix_affine
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.horizon_eq_kernel
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.strict_witness
#print axioms GaloisForLFunctions.HTGeometry.AffineDynamics.Braking.plateau_iff
