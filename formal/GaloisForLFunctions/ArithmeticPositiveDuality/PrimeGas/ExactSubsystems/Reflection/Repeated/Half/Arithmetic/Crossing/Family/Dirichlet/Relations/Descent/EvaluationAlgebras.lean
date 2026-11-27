import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Descent.Spectra

/-! # Signed prime-coordinate algebra isomorphisms characterize mutual forcing -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

/-- Agreement on all prime polynomials under one isomorphism of evaluation algebras. -/
def matchingAlgebras (x y : ℝ) : Prop :=
  ∃ e : (value x).range ≃ₐ[ℤ] (value y).range,
    ∀ P, e ((value x).rangeRestrict P)=(value y).rangeRestrict P

private theorem range_isomorphism_iff {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f g : A →ₐ[R] B) :
    (∃ e : f.range ≃ₐ[R] g.range, ∀ a, e (f.rangeRestrict a)=g.rangeRestrict a) ↔
      RingHom.ker f.toRingHom=RingHom.ker g.toRingHom := by
  constructor
  · rintro ⟨e,comm⟩
    ext a
    have vanishes (h : A →ₐ[R] B) : a ∈ RingHom.ker h.toRingHom ↔ h.rangeRestrict a=0 :=
      ⟨fun eq => Subtype.ext eq,fun eq => congrArg ((↑) : h.range → B) eq⟩
    rw [vanishes,vanishes,← comm,map_eq_zero_iff e e.injective]
  · intro eq
    let left := Ideal.quotientKerEquivRange f
    let right := Ideal.quotientKerEquivRange g
    let middle := Ideal.quotientEquivAlgOfEq R eq
    refine ⟨left.symm.trans (middle.trans right),fun a => ?_⟩
    have pre : left.symm (f.rangeRestrict a)=Ideal.Quotient.mk (RingHom.ker f.toRingHom) a :=
      left.symm_apply_eq.mpr rfl
    change right (middle (left.symm (f.rangeRestrict a)))=g.rangeRestrict a
    rw [pre]
    exact congrArg right (Ideal.quotientEquivAlgOfEq_mk R eq a)

theorem matching_iff_kernel {x y : ℝ} : matchingAlgebras x y ↔ kernel x=kernel y :=
  range_isomorphism_iff (value x) (value y)

private theorem self_reflection {x : ℝ} (h : kernel x ≤ kernel (-x)) : kernel x=kernel (-x) :=
  le_antisymm h (by simpa only [neg_neg] using kernel_negate h)

/-- Reversing a kernel inclusion preserves inclusion. Consequently two
opposite forcing implications already give equality at one consistent sign. -/
theorem mutual_iff_signed_kernel {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    Forces x y ∧ Forces y x ↔ kernel x=kernel y ∨ kernel x=kernel (-y) := by
  rw [forces_iff hx hy,forces_iff hy hx]
  constructor
  · rintro ⟨f | f,g | g⟩
    · exact Or.inl (le_antisymm f g)
    · exact Or.inl (le_antisymm f (g.trans (self_reflection (f.trans g)).ge))
    · exact Or.inr (le_antisymm f ((self_reflection (g.trans f)).ge.trans g))
    · exact Or.inr (le_antisymm f (by simpa only [neg_neg] using kernel_negate g))
  · rintro (eq | eq)
    · exact ⟨Or.inl eq.le,Or.inl eq.ge⟩
    · exact ⟨Or.inr eq.le,Or.inr (by simpa only [neg_neg] using kernel_negate eq.ge)⟩

/-- One scale and one sign per target identify all prime-polynomial values
for every positive multiple of that scale. -/
theorem uniform_signed_algebras {t : ℝ} (ht : 0<t) (res : Resonant t) :
    ∃ M : ℕ, 0<M ∧ ∀ u : ℝ, 0<u → (u ∈ mutualOrders t ↔
      (∀ k : ℕ, 0<k → matchingAlgebras (t*↑(M*k)) (u*↑(M*k))) ∨
      (∀ k : ℕ, 0<k → matchingAlgebras (t*↑(M*k)) (-(u*↑(M*k))))) := by
  obtain ⟨M,mp,all⟩ := mutual_spectra ht res
  refine ⟨M,mp,fun u hu => ?_⟩
  have atM := (all 1 zero_lt_one).2 u hu
  simp only [mul_one] at atM
  have tp := mul_pos ht (Nat.cast_pos.mpr mp : 0<(M : ℝ))
  have up := mul_pos hu (Nat.cast_pos.mpr mp : 0<(M : ℝ))
  rw [← atM,consequences_eq_iff_mutual tp up,mutual_iff_signed_kernel tp up]
  have dilate {x y : ℝ} (eq : kernel x=kernel y) (k : ℕ) : matchingAlgebras (x*k) (y*k) :=
    matching_iff_kernel.mpr (le_antisymm (kernel_dilate eq.le k) (kernel_dilate eq.ge k))
  constructor
  · rintro (eq | eq)
    · exact Or.inl (fun k _ => by simpa only [Nat.cast_mul,← mul_assoc] using dilate eq k)
    · exact Or.inr (fun k _ => by simpa only [Nat.cast_mul,← mul_assoc,neg_mul] using dilate eq k)
  · rintro (all | all)
    · exact Or.inl (by simpa only [mul_one] using matching_iff_kernel.mp (all 1 zero_lt_one))
    · exact Or.inr (by simpa only [mul_one] using matching_iff_kernel.mp (all 1 zero_lt_one))

#print axioms matching_iff_kernel
#print axioms mutual_iff_signed_kernel
#print axioms uniform_signed_algebras

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
