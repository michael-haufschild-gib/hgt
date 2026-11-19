import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceOneElements
import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicIntegralNormPeak
import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicCodifferentMinimum

/-!
# The norm spectrum of the positive height-one integers

The three square directions have norm one. Every other element corresponds
to a nonnegative integer barycentric triple. Its field norm is minimized at
vertices and maximized at the triples nearest the centroid.
-/

noncomputable section
namespace RHTower.OrbitCubic.NumberFieldTrace
open Matrix

/-- Trace-one element at the integral affine coordinates (u,v). -/
def heightEntry (m : ℤ) (u v : ℤ) := coords m 1 (-(u:ℚ)) (-(v:ℚ))

private theorem entry_value (m : ℤ) (p : {p : ℤ × ℤ // positiveSlice m p}) :
    (heightOneEquiv m p).val = heightEntry m p.val.1 p.val.2 := rfl

/-- Field norm of an interior lattice entry, using the cyclic array coordinates. -/
theorem entry_norm (a b c : ℕ) :
    Algebra.norm ℚ (heightEntry ((a:ℤ)+b+c+2) a ((b:ℤ)+1)) =
      ((triangleNorm (a:ℤ) b c : ℤ):ℚ) := by
  simpa only [heightEntry,Int.cast_add,Int.cast_one] using norm_barycentric (a:ℤ) b c

private theorem corners (m : ℤ) :
    heightEntry m 0 0 = 1 ∧ heightEntry m (m-1) 1 = U m^2 ∧ heightEntry m (-1) m = V m^2 := by
  obtain ⟨_,_,_,_,hu,hv⟩ := reciprocal_table m
  simp only [heightEntry,coords,Int.cast_zero,Int.cast_one,Int.cast_neg,Algebra.smul_def,map_one,
    map_neg,map_zero,map_sub,map_intCast,neg_zero,zero_mul,add_zero,one_mul,mul_one,neg_neg]
  refine ⟨rfl,?_,?_⟩
  · linear_combination -hu
  · linear_combination -hv

/-- Complete classification of the elements themselves, with the barycentric sum fixed. -/
theorem height_one_entries (n : ℕ) (z : K ((n:ℤ)+2)) :
    z ∈ heightOne ((n:ℤ)+2) ↔ z=1 ∨ z=U ((n:ℤ)+2)^2 ∨ z=V ((n:ℤ)+2)^2 ∨
      ∃ a b c : ℕ, a+b+c=n ∧ z=heightEntry ((n:ℤ)+2) a ((b:ℤ)+1) := by
  let m : ℤ := n+2
  have h0 := (corners m).1
  have h1 : heightEntry m ((n:ℤ)+1) 1 = U m^2 := by simpa [m] using (corners m).2.1
  have h2 := (corners m).2.2
  have mem (u v : ℤ) (h : positiveSlice m (u,v)) : heightEntry m u v ∈ heightOne m :=
    (entry_value m ⟨(u,v),h⟩) ▸ (heightOneEquiv m ⟨(u,v),h⟩).property
  constructor
  · intro hz
    obtain ⟨⟨⟨u,v⟩,hp⟩,he⟩ := (heightOneEquiv m).surjective ⟨z,hz⟩
    have h : heightEntry m u v = z := congrArg Subtype.val he
    rcases (exact_positive_slice n u v).mp hp with H|H|H|H
    · rw [H.1,H.2,h0] at h
      exact Or.inl h.symm
    · rw [H.1,H.2,h1] at h
      exact Or.inr (Or.inl h.symm)
    · rw [H.1,H.2,h2] at h
      exact Or.inr (Or.inr (Or.inl h.symm))
    · refine Or.inr (Or.inr (Or.inr ⟨u.toNat,(v-1).toNat,((n:ℤ)+1-u-v).toNat,by omega,?_⟩))
      have hu : (u.toNat:ℤ)=u := by omega
      have hv : ((v-1).toNat:ℤ)+1=v := by omega
      simpa only [hu,hv] using h.symm
  · rintro (rfl|rfl|rfl|⟨a,b,c,hs,rfl⟩)
    · exact h0 ▸ mem _ _ ((exact_positive_slice n _ _).mpr (Or.inl ⟨rfl,rfl⟩))
    · exact h1 ▸ mem _ _ ((exact_positive_slice n _ _).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
    · exact h2 ▸ mem _ _ ((exact_positive_slice n _ _).mpr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))))
    · apply mem
      apply (exact_positive_slice n _ _).mpr
      exact Or.inr (Or.inr (Or.inr ⟨by positivity,by omega,by omega⟩))

private theorem square_unit_norms (m : ℤ) :
    Algebra.norm ℚ (U m^2) = 1 ∧ Algebra.norm ℚ (V m^2) = 1 := by
  obtain ⟨_,hU,hV⟩ := corners m
  rw [← hU,← hV,heightEntry,heightEntry,norm_coordinates,norm_coordinates]
  simp [reciprocalMatrix,Matrix.det_fin_three] <;> ring

/-- A gap in the field norms of height-one integers. Norm one occurs exactly
on the three squares, and every other norm is at least 2m−1. -/
theorem norm_one_and_gap (n : ℕ) (z : heightOne ((n:ℤ)+2)) :
    (Algebra.norm ℚ z.val = 1 ↔ z.val=1 ∨ z.val=U ((n:ℤ)+2)^2 ∨ z.val=V ((n:ℤ)+2)^2) ∧
    (Algebra.norm ℚ z.val = 1 ∨ 2*(n:ℚ)+3 ≤ Algebra.norm ℚ z.val) := by
  obtain ⟨hU,hV⟩ := square_unit_norms ((n:ℤ)+2)
  have sq (h : z.val=1 ∨ z.val=U ((n:ℤ)+2)^2 ∨ z.val=V ((n:ℤ)+2)^2) :
      Algebra.norm ℚ z.val = 1 := by rcases h with h|h|h <;> simp [h,hU,hV]
  rcases (height_one_entries n z.val).mp z.property with h|h|h|⟨a,b,c,hs,he⟩
  · exact ⟨⟨fun _ => Or.inl h,sq⟩,Or.inl (sq (Or.inl h))⟩
  · exact ⟨⟨fun _ => Or.inr (Or.inl h),sq⟩,Or.inl (sq (Or.inr (Or.inl h)))⟩
  · exact ⟨⟨fun _ => Or.inr (Or.inr h),sq⟩,Or.inl (sq (Or.inr (Or.inr h)))⟩
  · subst n
    have hh := entry_norm a b c
    have hN : 2*((a:ℚ)+b+c)+3 ≤ Algebra.norm ℚ z.val := by
      rw [he]
      push_cast
      rw [hh]
      simpa [triangleNorm,arm] using (lower_triangle_norm (a:ℚ≥0) (b:ℚ≥0) (c:ℚ≥0)).1
    have hn : Algebra.norm ℚ z.val ≠ 1 := by
      intro h
      linarith only [hN,h,Nat.cast_nonneg (α:=ℚ) a,Nat.cast_nonneg (α:=ℚ) b,Nat.cast_nonneg (α:=ℚ) c]
    exact ⟨⟨fun h => (hn h).elim,sq⟩,Or.inr (by push_cast; exact hN)⟩

/-- Among positive height-one elements, having an inverse in the monogenic
order is equivalent to field norm one. -/
theorem order_unit_iff_norm_one (n : ℕ) (z : heightOne ((n:ℤ)+2)) :
    (∃ y ∈ powerOrder ((n:ℤ)+2), z.val*y=1) ↔ Algebra.norm ℚ z.val = 1 := by
  have hn : 0 < Algebra.norm ℚ z.val := by
    rcases (norm_one_and_gap n z).2 with h | h
    · rw [h]; exact zero_lt_one
    · linarith only [h,Nat.cast_nonneg (α := ℚ) n]
  simpa only [abs_of_pos hn] using order_unit_norm_iff ((n:ℤ)+2) ⟨z.val,z.property.1⟩

/-- The lower edge of the nonunit norm spectrum is attained in every field of the family. -/
theorem least_nonunit_norm_attained (n : ℕ) :
    ∃ z : heightOne ((n:ℤ)+2), Algebra.norm ℚ z.val = 2*(n:ℚ)+3 := by
  let z := heightEntry ((n:ℤ)+2) 0 1
  have hz : z ∈ heightOne ((n:ℤ)+2) := (height_one_entries n z).mpr <|
    Or.inr (Or.inr (Or.inr ⟨0,0,n,by simp,by simp [z]⟩))
  refine ⟨⟨z,hz⟩,?_⟩
  simpa [z,triangleNorm,arm] using entry_norm 0 0 n

#print axioms entry_norm
#print axioms height_one_entries
#print axioms norm_one_and_gap
#print axioms order_unit_iff_norm_one
#print axioms least_nonunit_norm_attained
end RHTower.OrbitCubic.NumberFieldTrace
