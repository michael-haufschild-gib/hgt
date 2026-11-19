import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceOneElements

/-!
# Shanks coordinates for the orbit cubic

Translating the generator by one gives Shanks' simplest cubic. Multiplication
by its square carries the interior height-one array to the indecomposable
triangle of Kala–Tinková, arXiv:2005.12312, in the original power basis.
The trace functional for the translated triangle is constant coefficient
plus quadratic coefficient. All identities hold in the monogenic order.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace

/-- Shanks generator at parameter m−2. -/
def shanksRoot (m : ℤ) : K m := root m-1

theorem shanks_equation (m : ℤ) :
    let y := shanksRoot m
    y^3 - (m-2)*y^2 - (m+1)*y - 1 = 0 := by
  obtain ⟨h,_,_⟩ := reciprocal_table m
  unfold U at h
  unfold shanksRoot
  linear_combination -h

private theorem shanks_unit (m : ℤ) : shanksRoot m*V m=1 := (reciprocal_table m).2.1

/-- Multiplying a Shanks power-basis element by the inverse square unit
gives its exact coordinates in the orthonormal trace lattice. -/
theorem shanks_to_reciprocal (m : ℤ) (a b c : ℚ) :
    V m^2*(algebraMap ℚ (K m) a + algebraMap ℚ (K m) b*shanksRoot m +
      algebraMap ℚ (K m) c*shanksRoot m^2) = coords m (a+c) a (b-(m:ℚ)*a) := by
  have h := shanks_unit m
  have hV := (reciprocal_table m).2.2.2.2.2
  have hsq : V m^2*shanksRoot m^2=1 := by rw [← mul_pow,mul_comm,h,one_pow]
  simp only [coords,Algebra.smul_def,map_add,map_sub,map_mul,map_intCast,mul_one]
  linear_combination (algebraMap ℚ (K m) a)*hV + (algebraMap ℚ (K m) b)*V m*h +
    (algebraMap ℚ (K m) c)*hsq

/-- The codifferent generator for the classical triangle reads a+c from
a+bρ+cρ², independently of its linear coefficient. -/
theorem shanks_height (m : ℤ) (a b c : ℚ) :
    Algebra.trace ℚ (K m) ((delta m*V m^2)*(algebraMap ℚ (K m) a +
      algebraMap ℚ (K m) b*shanksRoot m + algebraMap ℚ (K m) c*shanksRoot m^2)) = a+c := by
  rw [mul_assoc,shanks_to_reciprocal,trace_coords]

/-- Standard quadratic representative of the Shanks triangle. -/
def shanksEntry (m u w : ℤ) : K m :=
  -(u:K m)-(w:K m)*shanksRoot m+(u+1)*shanksRoot m^2

/-- Exact transport by ρ². The shear w=mu+v is integral and unimodular. -/
theorem shanks_triangle_transport (m u v : ℤ) :
    shanksRoot m^2*coords m 1 (-(u:ℚ)) (-(v:ℚ)) = shanksEntry m u (m*u+v) := by
  have h := shanks_to_reciprocal m (-(u:ℚ)) (-((m:ℚ)*u+v)) ((u:ℚ)+1)
  rw [show -(u:ℚ)+((u:ℚ)+1) = 1 by ring,
    show -((m:ℚ)*u+v)-(m:ℚ)*(-(u:ℚ)) = -(v:ℚ) by ring] at h
  have he : V m^2*shanksEntry m u (m*u+v) = coords m 1 (-(u:ℚ)) (-(v:ℚ)) := by
    simpa only [shanksEntry,map_neg,map_add,map_one,map_mul,map_intCast,Int.cast_add,Int.cast_mul,
      neg_mul,sub_eq_add_neg] using h
  rw [← he,← mul_assoc,← mul_pow,shanks_unit,one_pow,one_mul]

/-- In the standard coordinates the range of w is
(m u)+1 through (u+1)(m−1), inclusive, on rows 0 through m−2. -/
theorem shanks_triangle_range (m u w : ℤ) :
    (∃ v : ℤ, 0 ≤ u ∧ 1 ≤ v ∧ u+v ≤ m-1 ∧ w=m*u+v) ↔
      0 ≤ u ∧ u ≤ m-2 ∧ m*u+1 ≤ w ∧ w ≤ (u+1)*(m-1) := by
  have h : (u+1)*(m-1) = m*u+m-1-u := by ring
  rw [h]
  constructor
  · rintro ⟨v,hu,hv,hs,rfl⟩
    omega
  · rintro ⟨hu,_,hl,hr⟩
    exact ⟨w-m*u,hu,by omega,by omega,by omega⟩

/-- The transported classical triangle is realized by totally positive
height-one elements of the orbit order at every nonnegative Shanks parameter. -/
theorem shanks_entries_have_height_one (n : ℕ) (u w : ℤ) :
    let m := (n:ℤ)+2
    (0 ≤ u ∧ u ≤ m-2 ∧ m*u+1 ≤ w ∧ w ≤ (u+1)*(m-1)) →
      ∃ z : heightOne m, shanksRoot m^2*z.val = shanksEntry m u w := by
  intro m h
  obtain ⟨v,hu,hv,hs,rfl⟩ := (shanks_triangle_range m u w).mpr h
  have hp : positiveSlice m (u,v) := (exact_positive_slice n u v).mpr <|
    Or.inr (Or.inr (Or.inr ⟨hu,hv,by dsimp only [m] at hs; omega⟩))
  exact ⟨heightOneEquiv m ⟨(u,v),hp⟩,shanks_triangle_transport m u v⟩

#print axioms shanks_equation
#print axioms shanks_to_reciprocal
#print axioms shanks_height
#print axioms shanks_triangle_transport
#print axioms shanks_triangle_range
#print axioms shanks_entries_have_height_one
end RHTower.OrbitCubic.NumberFieldTrace
