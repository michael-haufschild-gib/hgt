import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicHullEhrhart

/-!
# Additive generation in the cubic integer hull

Every lattice point of the k-fold dilation is a sum of exactly k totally
positive height-one coordinates. A greedy division along one row suffices
in each outer sector, and the inner simplex uses a two-coordinate division.
The three integral facet tests therefore characterize the semigroup in every
degree.
-/

noncomputable section
namespace RHTower.OrbitCubic.IntegerHull.Ehrhart

def generated (n k : ℕ) (p : ℤ × ℤ) := ∃ xs : List (ℤ × ℤ),
  xs.length=k ∧ xs.sum=p ∧ ∀ x∈xs, positiveSlice ((n:ℤ)+2) x

private theorem unit_iff (n : ℕ) (p : ℤ × ℤ) : positiveSlice ((n:ℤ)+2) p ↔ dilated n 1 p := by
  obtain ⟨u,v⟩ := p
  rw [integer_hull_exact]
  simp only [dilated,centerMass,Nat.cast_one,one_mul]
  omega

private theorem add_closed {n j k : ℕ} {p q : ℤ × ℤ} (hp : dilated n j p) (hq : dilated n k q) :
    dilated n (j+k) (p+q) := by
  obtain ⟨h1,h2,h3⟩ := hp
  obtain ⟨g1,g2,g3⟩ := hq
  have hl : leftMass ((n:ℤ)+2) (p+q).1 (p+q).2 =
      leftMass ((n:ℤ)+2) p.1 p.2+leftMass ((n:ℤ)+2) q.1 q.2 := by
    change _*(p.1+q.1)+(p.2+q.2)=_; unfold leftMass; ring
  have hr : rightMass ((n:ℤ)+2) (p+q).1 (p+q).2 =
      rightMass ((n:ℤ)+2) p.1 p.2+rightMass ((n:ℤ)+2) q.1 q.2 := by
    change _*(p.2+q.2)-(p.1+q.1)=_; unfold rightMass; ring
  unfold dilated
  rw [hl,hr,Nat.cast_add,add_mul]
  exact ⟨add_nonneg h1 g1,add_nonneg h2 g2,by linarith only [h3,g3]⟩

private theorem turn_closed {n k : ℕ} {p : ℤ × ℤ} (hp : dilated n k p) :
    dilated n k (turnPoint n k p) := by
  obtain ⟨h1,h2,h3⟩ := hp
  have hL : leftMass ((n:ℤ)+2) (turnPoint n k p).1 (turnPoint n k p).2 =
      (k:ℤ)*index ((n:ℤ)+2)-leftMass ((n:ℤ)+2) p.1 p.2-rightMass ((n:ℤ)+2) p.1 p.2 := by
    unfold leftMass rightMass turnPoint index
    ring
  have hR : rightMass ((n:ℤ)+2) (turnPoint n k p).1 (turnPoint n k p).2 =
      leftMass ((n:ℤ)+2) p.1 p.2 := by unfold turnPoint leftMass rightMass; ring
  unfold dilated
  rw [hL,hR]
  exact ⟨by linarith only [h3],h1,by linarith only [h2]⟩

private theorem necessary (n : ℕ) (xs : List (ℤ × ℤ))
    (h : ∀ x∈xs, positiveSlice ((n:ℤ)+2) x) : dilated n xs.length xs.sum := by
  induction xs with
  | nil => simp [dilated,leftMass,rightMass]
  | cons x xs ih =>
    have h1 := (unit_iff n _).mp (h x List.mem_cons_self)
    simpa only [Nat.one_add,List.length_cons,List.sum_cons] using
      add_closed h1 (ih fun z hz => h z (List.mem_cons_of_mem _ hz))

private theorem generated_zero (n : ℕ) : generated n 0 (0,0) :=
  ⟨[],rfl,rfl,by simp⟩

private theorem generated_cons {n k : ℕ} {p q : ℤ × ℤ}
    (hp : positiveSlice ((n:ℤ)+2) p) (hq : generated n k q) : generated n (k+1) (p+q) := by
  obtain ⟨xs,hk,hs,h⟩ := hq
  exact ⟨p::xs,by simp [hk],by simp [hs],fun x hx => (List.mem_cons.mp hx).elim
    (fun he => he.symm ▸ hp) (fun hh => h x hh)⟩

private theorem generated_turn {n k : ℕ} {p : ℤ × ℤ} (hp : generated n k p) :
    generated n k (turnPoint n k p) := by
  obtain ⟨xs,rfl,rfl,h⟩ := hp
  have hs (l : List (ℤ × ℤ)) : (l.map (turnPoint n 1)).sum=turnPoint n l.length l.sum := by
    induction l with
    | nil => simp [turnPoint]
    | cons x l ih =>
      simp only [List.map_cons,List.length_cons,List.sum_cons,ih]
      apply Prod.ext <;> simp [turnPoint] <;> ring
  refine ⟨_,List.length_map,hs xs,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  exact (unit_iff _ _).mpr (turn_closed ((unit_iff _ _).mp (h y hy)))

private theorem simplex_point (n : ℕ) {u v : ℤ} (hu : 0≤u) (hv : 0≤v) (hs : u+v≤n) :
    positiveSlice ((n:ℤ)+2) (u,v+1) :=
  (exact_positive_slice n _ _).mpr (Or.inr (Or.inr (Or.inr ⟨hu,by omega,by omega⟩)))

private theorem simplex_generated (n k : ℕ) (u v : ℤ) (hu : 0≤u) (hv : 0≤v)
    (hs : u+v≤(n:ℤ)*k) : generated n k (u,v+k) := by
  induction k generalizing u v with
  | zero =>
    simp only [Nat.cast_zero,mul_zero,add_zero] at hs ⊢
    obtain rfl : u=0 := by omega
    obtain rfl : v=0 := by omega
    exact generated_zero _
  | succ k ih =>
    let a := min u (n:ℤ)
    let b := min v ((n:ℤ)-a)
    have ha : 0≤a := le_min hu (Int.natCast_nonneg _)
    have hb : 0≤b := le_min hv (sub_nonneg.mpr (min_le_right _ _))
    have hab : a+b≤n := by have hh := min_le_right v ((n:ℤ)-a); dsimp only [b]; omega
    have au : a≤u := min_le_left _ _
    have bv : b≤v := min_le_left _ _
    have hrest : u-a+(v-b)≤(n:ℤ)*k := by
      rw [Nat.cast_succ,mul_add,mul_one] at hs
      dsimp only [a,b]
      have hnk := mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg k)
      omega
    have H := generated_cons (simplex_point n ha hb hab)
      (ih (u-a) (v-b) (sub_nonneg.mpr au) (sub_nonneg.mpr bv) hrest)
    convert H using 1
    apply Prod.ext <;> simp <;> ring

private theorem fan_row (n : ℕ) {u : ℤ} (hu : 0≤u) (hv : u≤n+1) :
    positiveSlice ((n:ℤ)+2) (u,1) := by
  by_cases h : u=(n:ℤ)+1
  · exact (exact_positive_slice n _ _).mpr (Or.inr (Or.inl ⟨h,rfl⟩))
  · exact simplex_point n hu (v:=0) le_rfl (by omega)

private theorem fan_generated (n k : ℕ) (u v : ℤ) (hu : 0≤u) (hv : 0≤v)
    (ht : v≤k) (hs : u≤((n:ℤ)+1)*v) : generated n k (u,v) := by
  induction k generalizing u v with
  | zero =>
    obtain rfl : v=0 := by omega
    obtain rfl : u=0 := le_antisymm (by simpa only [mul_zero] using hs) hu
    exact generated_zero _
  | succ k ih =>
    by_cases he : v=0
    · subst v
      have hz : u=0 := le_antisymm (by simpa only [mul_zero] using hs) hu
      subst u
      have H := generated_cons ((exact_positive_slice n 0 0).mpr (Or.inl ⟨rfl,rfl⟩))
        (ih 0 0 le_rfl le_rfl (Int.natCast_nonneg k) (by simp))
      simpa using H
    let a := min u ((n:ℤ)+1)
    have ha : 0≤a := le_min hu (by positivity)
    have hr : u-a≤((n:ℤ)+1)*(v-1) := by
      have h := mul_nonneg (show (0:ℤ)≤n+1 by positivity) (show 0≤v-1 by omega)
      rw [mul_sub,mul_one] at h ⊢
      dsimp only [a]
      omega
    have H := generated_cons (fan_row n ha (min_le_right _ _))
      (ih (u-a) (v-1) (sub_nonneg.mpr (min_le_left _ _)) (by omega) (by omega) hr)
    convert H using 1
    apply Prod.ext <;> simp <;> ring

/-- In every degree, the three facet inequalities are necessary and sufficient
for an integral sum of height-one positive elements. -/
theorem semigroup_exact (n k : ℕ) (p : ℤ × ℤ) : generated n k p ↔ dilated n k p := by
  constructor
  · rintro ⟨xs,rfl,rfl,h⟩
    exact necessary n xs h
  · intro h
    rcases sector_cover n k ⟨p,h⟩ with ⟨u,v,hu,hv,hs,he⟩|⟨u,v,hu,hv,hk,hs,he⟩
    · exact he.symm ▸ simplex_generated n k u v hu hv hs
    have H := fan_generated n k u v hu hv hk.le hs
    rcases he with he|he|he
    · exact he.symm ▸ H
    · exact he.symm ▸ generated_turn H
    · exact he.symm ▸ generated_turn (generated_turn H)

/-- Closed formula for the number of distinct sums, with repetitions allowed. -/
theorem card_distinct_sums (n k : ℕ) :
    2*Nat.card {p : ℤ × ℤ // generated n k p}=((n+2)*(n+1)+1)*k^2+3*k+2 := by
  let e : {p : ℤ × ℤ // generated n k p} ≃ latticePoint n k :=
    Equiv.subtypeEquivRight fun p => semigroup_exact n k p
  rw [Nat.card_congr e,ehrhart]

#print axioms semigroup_exact
#print axioms card_distinct_sums
end RHTower.OrbitCubic.IntegerHull.Ehrhart
