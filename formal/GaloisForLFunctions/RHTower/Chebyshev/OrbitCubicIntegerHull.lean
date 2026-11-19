import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicPositiveTraceSlice

/-!
# The integer hull of the positive cubic trace slice

The lattice points of the open embedding triangle are exactly those of
the closed triangle spanned by the three unit squares. Its edges have
no other lattice points. Passing to the integer hull loses exactly three
units of coordinate area at every parameter.
-/

noncomputable section
namespace RHTower.OrbitCubic.IntegerHull

/-- Determinant of the two edge vectors (m−1,1) and (−1,m). -/
def index {R : Type*} [CommRing R] (m : R) := m*(m-1)+1
def leftMass {R : Type*} [CommRing R] (m u v : R) := m*u+v
def rightMass {R : Type*} [CommRing R] (m u v : R) := (m-1)*v-u
def centerMass {R : Type*} [CommRing R] (m u v : R) := index m-leftMass m u v-rightMass m u v

private theorem index_pos {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {m : R} (hm : 2 ≤ m) : 0 < index m := by
  unfold index
  have h1 : 0 ≤ m-1 := by linarith only [hm]
  have h0 : 0 ≤ m := by linarith only [hm]
  linarith only [mul_nonneg h0 h1]

/-- These three linear inequalities describe the actual convex hull of the
unit-square coordinates, including its boundary. -/
theorem convex_coordinates (n : ℕ) (u v : ℝ) :
    let m := (n:ℝ)+2
    (0 ≤ centerMass m u v ∧ 0 ≤ leftMass m u v ∧ 0 ≤ rightMass m u v) ↔
      ∃ l r : ℝ, 0 ≤ l ∧ 0 ≤ r ∧ l+r ≤ 1 ∧ u=l*(m-1)-r ∧ v=l+r*m := by
  intro m
  have hm : 2 ≤ m := by dsimp only [m]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hd := index_pos hm
  constructor
  · rintro ⟨ha,hb,hc⟩
    refine ⟨leftMass m u v/index m,rightMass m u v/index m,div_nonneg hb hd.le,
      div_nonneg hc hd.le,?_,?_,?_⟩
    · rw [← add_div,div_le_one hd]
      unfold centerMass at ha
      linarith only [ha]
    all_goals field_simp [hd.ne']; unfold index leftMass rightMass; ring
  · rintro ⟨l,r,hl,hr,hs,rfl,rfl⟩
    have L : leftMass m (l*(m-1)-r) (l+r*m)=l*index m := by unfold leftMass index; ring
    have R : rightMass m (l*(m-1)-r) (l+r*m)=r*index m := by unfold rightMass index; ring
    rw [centerMass,L,R]
    refine ⟨?_,mul_nonneg hl hd.le,mul_nonneg hr hd.le⟩
    nlinarith only [mul_nonneg (sub_nonneg.mpr hs) hd.le]

private theorem interior {m u v : ℤ} (hm : 2 ≤ m) (hu : 0≤u) (hv : 1≤v) (hs : u+v ≤ m-1) :
    0<centerMass m u v ∧ 0<leftMass m u v ∧ 0<rightMass m u v := by
  have hm' : 0 ≤ m := by omega
  have hx : 0 ≤ m-1-u-v := by omega
  have h := mul_nonneg (show 0 ≤ m-1 by omega) hx
  have h' := mul_nonneg hm' (show 0 ≤ v-1 by omega)
  unfold centerMass index leftMass rightMass
  exact ⟨by nlinarith only [h,hs,hu],by linarith only [mul_nonneg hm' hu,hv],by nlinarith only [h',hx]⟩

/-- Every point of the real square hull represents a positive value at every
root: the three basis squares appear with their barycentric numerators. -/
theorem square_decomposition (m u v x : ℝ) (hx : binary (m-1/2) x 1=0) :
    index m*traceBasis 1 (-u) (-v) x =
      centerMass m u v+leftMass m u v*x⁻¹^2+rightMass m u v*(x-1)⁻¹^2 := by
  obtain ⟨hU,hV⟩ := reciprocal_square_coordinates m x hx
  rw [hU,hV]
  unfold traceBasis centerMass leftMass rightMass index
  ring

private theorem real_hull_positive {m u v x : ℝ} (hm : 2 ≤ m) (hx : binary (m-1/2) x 1=0)
    (hA : 0≤centerMass m u v) (hB : 0≤leftMass m u v) (hC : 0≤rightMass m u v) :
    0 < traceBasis 1 (-u) (-v) x := by
  have hd := index_pos hm
  have e := square_decomposition m u v x hx
  have hroot := hx
  rw [arrowhead_secular] at hroot
  have h0 : x ≠ 0 := by rintro rfl; norm_num at hroot
  have h1 : x-1 ≠ 0 := by intro hz; rw [sub_eq_zero.mp hz] at hroot; norm_num at hroot
  have hU := sq_pos_of_ne_zero (inv_ne_zero h0)
  have hV := sq_pos_of_ne_zero (inv_ne_zero h1)
  have hsum : centerMass m u v+leftMass m u v+rightMass m u v=index m := by unfold centerMass; ring
  apply pos_of_mul_pos_right _ hd.le
  rw [e]
  by_cases ha : 0<centerMass m u v
  · linarith only [ha,mul_nonneg hB hU.le,mul_nonneg hC hV.le]
  by_cases hb : 0<leftMass m u v
  · linarith only [hA,mul_pos hb hU,mul_nonneg hC hV.le]
  have hc : 0<rightMass m u v := by linarith only [not_lt.mp ha,not_lt.mp hb,hsum,hd]
  linarith only [hA,mul_nonneg hB hU.le,mul_pos hc hV]

/-- Restricting total positivity to integer trace-one coordinates replaces
the irrational open triangle by three closed integral half-planes exactly. -/
theorem integer_hull_exact (n : ℕ) (u v : ℤ) :
    let m := (n:ℤ)+2
    positiveSlice m (u,v) ↔ 0 ≤ centerMass m u v ∧ 0 ≤ leftMass m u v ∧ 0 ≤ rightMass m u v := by
  intro m
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hd := index_pos hm
  constructor
  · intro hp
    rcases (exact_positive_slice n u v).mp hp with ⟨rfl,rfl⟩|⟨h1,rfl⟩|⟨rfl,h2⟩|⟨hu,hv,hs⟩
    · simpa [centerMass,leftMass,rightMass] using hd.le
    · have hu : u=m-1 := by dsimp [m]; omega
      rw [hu]
      simp [centerMass,leftMass,rightMass,index,hd.le,show 0 ≤ m*(m-1)+1 from hd.le]
    · change v=m at h2
      rw [h2]
      have hr : rightMass m (-1) m=index m := by unfold rightMass index; ring
      simp [centerMass,leftMass,hr,hd.le]
    · have ⟨A,B,C⟩ := interior hm hu hv (by dsimp [m]; omega)
      exact ⟨A.le,B.le,C.le⟩
  · rintro ⟨ha,hb,hc⟩ x hx
    apply real_hull_positive (m := (m:ℝ)) (by exact_mod_cast hm) hx
    · unfold centerMass leftMass rightMass index at ha ⊢; exact_mod_cast ha
    · unfold leftMass at hb ⊢; exact_mod_cast hb
    · unfold rightMass at hc ⊢; exact_mod_cast hc

/-- The only lattice points on the boundary of the integer hull are its
three vertices. Every other positive integer has three strictly positive
barycentric weights. -/
theorem primitive_boundary (n : ℕ) (u v : ℤ) :
    let m := (n:ℤ)+2
    positiveSlice m (u,v) ∧ (centerMass m u v=0 ∨ leftMass m u v=0 ∨ rightMass m u v=0) ↔
      (u=0 ∧ v=0) ∨ (u=m-1 ∧ v=1) ∨ (u = -1 ∧ v=m) := by
  intro m
  have hm : 2 ≤ m := by dsimp [m]; omega
  constructor
  · rintro ⟨hp,h⟩
    rcases (exact_positive_slice n u v).mp hp with h0|h1|h2|⟨hu,hv,hs⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨by dsimp [m]; omega,h1.2⟩)
    · exact Or.inr (Or.inr h2)
    · obtain ⟨a,b,c⟩ := interior hm hu hv (by dsimp [m]; omega)
      rcases h with h|h|h <;> omega
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact ⟨(exact_positive_slice n _ _).mpr (Or.inl ⟨rfl,rfl⟩),Or.inr (Or.inl (by simp [leftMass]))⟩
    · exact ⟨(exact_positive_slice n _ _).mpr (Or.inr (Or.inl ⟨by dsimp [m]; omega,rfl⟩)),
        Or.inr (Or.inr (by simp [rightMass]))⟩
    · exact ⟨(exact_positive_slice n _ _).mpr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))),
        Or.inr (Or.inl (by simp [leftMass]))⟩

/-- Embedded open triangle and integer hull differ in area by exactly three. -/
theorem area_loss (n : ℕ) :
    let m := (n:ℝ)+2
    ∃ r, m < r ∧ r < m+1 ∧ binary (m-1/2) r 1=0 ∧ twiceSliceArea r/2-index m/2=3 := by
  intro m
  obtain ⟨r,hl,hr,he,harea,_⟩ := slice_area_discriminant n
  refine ⟨r,hl,hr,he,?_⟩
  rw [harea,chebyshevRealOrbitCubic_discr,Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
  dsimp only [m,index]
  ring

end RHTower.OrbitCubic.IntegerHull
