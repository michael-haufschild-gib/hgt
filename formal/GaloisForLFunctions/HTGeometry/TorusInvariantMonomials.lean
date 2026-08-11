import GaloisForLFunctions.HTGeometry.TorusInvariantField

/-!
# The scaling invariants are the annihilating monomials over the velocity field

For an arbitrary set of constant rescalings of a freely generating palette, the invariant field is
generated over the velocity field by the Laurent monomials whose exponent vector has trivial
character on the acting set.

One inclusion is a direct computation: such a monomial is multiplied by its character, which is one.
The other is the eigen-representation of an invariant: numerator and denominator have all their
exponents in one character class, so dividing both by a fixed exponent of that class exhibits the
invariant as a quotient of two combinations of annihilating monomials.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

section Monomial

variable {C E : Type u} [Field C] [Field E] [Algebra C E] {r : ℕ}

/-- The Laurent monomial of an integer exponent vector in a palette. -/
def laurentMonomial (x : Fin r → E) (a : Fin r → ℤ) : E := ∏ k, (x k) ^ (a k)

theorem laurentMonomial_natCast (x : Fin r → E) (e : Fin r →₀ ℕ) :
    laurentMonomial x (fun k ↦ ((e k : ℤ))) = ∏ k, (x k) ^ (e k) :=
  Finset.prod_congr rfl fun _ _ ↦ zpow_natCast _ _

theorem laurentMonomial_add {x : Fin r → E} (hx0 : ∀ k, x k ≠ 0) (a b : Fin r → ℤ) :
    laurentMonomial x (a + b) = laurentMonomial x a * laurentMonomial x b := by
  rw [laurentMonomial, laurentMonomial, laurentMonomial, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ ↦ zpow_add₀ (hx0 k) _ _

theorem laurentMonomial_ne_zero {x : Fin r → E} (hx0 : ∀ k, x k ≠ 0) (a : Fin r → ℤ) :
    laurentMonomial x a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (hx0 k)

/-- The exponent vectors whose character is trivial on a set of rescalings. -/
def scaleAnnihilator (C : Type u) [Field C] {r : ℕ} (S : Set (Fin r → Cˣ)) : Set (Fin r → ℤ) :=
  {a | ∀ u ∈ S, (∏ k, ((u k : C)) ^ (a k)) = 1}

end Monomial

section Invariance

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

omit [CharZero E] in
include hx hgen in
/-- **Rescaling multiplies a Laurent monomial by its character.** -/
theorem torusScaleEquiv_laurentMonomial (u : Fin r → Cˣ) (a : Fin r → ℤ) :
    torusScaleEquiv hx hgen u (laurentMonomial x a)
      = algebraMap C E (∏ k, ((u k : C)) ^ (a k)) * laurentMonomial x a := by
  simp only [laurentMonomial]
  rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [map_zpow₀, map_zpow₀, torusScaleEquiv_apply, mul_zpow]

omit [CharZero E] in
include hx hgen in
/-- An annihilating monomial is fixed by every rescaling in the set. -/
theorem torusScaleEquiv_laurentMonomial_of_mem_annihilator {S : Set (Fin r → Cˣ)}
    {a : Fin r → ℤ} (ha : a ∈ scaleAnnihilator C S) {u : Fin r → Cˣ} (hu : u ∈ S) :
    torusScaleEquiv hx hgen u (laurentMonomial x a) = laurentMonomial x a := by
  rw [torusScaleEquiv_laurentMonomial hx hgen u a, ha u hu, map_one, one_mul]

/-- The invariant field candidate: the velocity field with the annihilating monomials adjoined. -/
def torusInvariantMonomialField (C : Type u) [Field C] [Algebra C E] {r : ℕ} (x : Fin r → E)
    (S : Set (Fin r → Cˣ)) : IntermediateField (↥(torusVelocityField C x)) E :=
  IntermediateField.adjoin (↥(torusVelocityField C x))
    (laurentMonomial x '' scaleAnnihilator C S)

include hx hgen in
/-- **Every element of the monomial field is invariant.** -/
theorem torusScale_invariant_of_mem_torusInvariantMonomialField (hconst : ∀ c : C, c′ = 0)
    {S : Set (Fin r → Cˣ)} {z : E} (hz : z ∈ torusInvariantMonomialField C x S)
    {u : Fin r → Cˣ} (hu : u ∈ S) :
    torusScaleEquiv hx hgen u z = z := by
  rw [torusInvariantMonomialField] at hz
  refine IntermediateField.adjoin_induction (↥(torusVelocityField C x))
    (s := laurentMonomial x '' scaleAnnihilator C S)
    (p := fun w _ ↦ torusScaleEquiv hx hgen u w = w) ?_ ?_ ?_ ?_ ?_ hz
  · rintro w ⟨a, ha, rfl⟩
    exact torusScaleEquiv_laurentMonomial_of_mem_annihilator hx hgen ha hu
  · intro c
    exact torusScaleEquiv_fixes_velocityField hx hgen hconst u c.2
  · intro a b _ _ ha hb
    rw [map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, ha, hb]

include hx hgen in
/-- **Every invariant lies in the monomial field.**  Dividing the eigen-representation of an
invariant by a fixed monomial of its character class exhibits it as a quotient of two combinations
of annihilating monomials. -/
theorem mem_torusInvariantMonomialField_of_torusScale_invariant [CharZero C]
    (hconst : ∀ c : C, c′ = 0) {S : Set (Fin r → Cˣ)} {z : E}
    (hfix : ∀ u ∈ S, torusScaleEquiv hx hgen u z = z) :
    z ∈ torusInvariantMonomialField C x S := by
  classical
  have hx0 : ∀ k, x k ≠ 0 := torus_palette_ne_zero hx
  by_cases hz0 : z = 0
  · rw [hz0]
    exact (torusInvariantMonomialField C x S).zero_mem
  have hzmem : z ∈ IntermediateField.adjoin (↥(torusVelocityField C x)) (Set.range x) := by
    rw [adjoin_velocity_palette_eq_top hx hgen]
    exact IntermediateField.mem_top
  obtain ⟨d, P, Q, hd, hPQeq, hQchar, hPchar⟩ :=
    exists_torusScale_eigen_representation hx hgen (torusVelocityField C x)
      (algebraicIndependent_palette_over_velocityField hx hgen hconst)
      (fun u _ w hw ↦ torusScaleEquiv_fixes_velocityField hx hgen hconst u hw) hz0 hzmem hfix
  -- an exponent with the character of `d` differs from `d` by an annihilating vector
  have hann : ∀ e : Fin r →₀ ℕ,
      (∀ u ∈ S, scaleChar (torusVelocityField C x) u e = scaleChar (torusVelocityField C x) u d) →
      (fun k ↦ ((e k : ℤ)) - ((d k : ℤ))) ∈ scaleAnnihilator C S := by
    intro e he u hu
    have hchar := (scaleChar_eq_iff (torusVelocityField C x) u e d).mp (he u hu)
    have hsplit : (∏ k, ((u k : C)) ^ (((e k : ℤ)) - ((d k : ℤ))))
        = (∏ k, ((u k : C)) ^ (e k)) / ∏ k, ((u k : C)) ^ (d k) := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ ↦ by
        rw [zpow_sub₀ (Units.ne_zero (u k)), zpow_natCast, zpow_natCast]
    have hne : (∏ k, ((u k : C)) ^ (d k)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (Units.ne_zero (u k))
    rw [hsplit, hchar, div_self hne]
  -- an eigen-polynomial evaluates to an element of the monomial field times the fixed monomial
  have key : ∀ W : MvPolynomial (Fin r) ↥(torusVelocityField C x),
      (∀ e ∈ W.support, ∀ u ∈ S,
        scaleChar (torusVelocityField C x) u e = scaleChar (torusVelocityField C x) u d) →
      ∃ w ∈ torusInvariantMonomialField C x S,
        MvPolynomial.aeval x W = w * laurentMonomial x (fun k ↦ ((d k : ℤ))) := by
    intro W hW
    refine ⟨∑ e ∈ W.support, algebraMap (↥(torusVelocityField C x)) E (MvPolynomial.coeff e W)
        * laurentMonomial x (fun k ↦ ((e k : ℤ)) - d k), ?_, ?_⟩
    · exact sum_mem fun e he ↦
        mul_mem ((torusInvariantMonomialField C x S).algebraMap_mem _)
          (IntermediateField.subset_adjoin _ _ ⟨_, hann e (hW e he), rfl⟩)
    · rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      have hsplit : laurentMonomial x (fun k ↦ ((e k : ℤ)) - d k)
          * laurentMonomial x (fun k ↦ ((d k : ℤ)))
          = laurentMonomial x (fun k ↦ ((e k : ℤ))) := by
        rw [← laurentMonomial_add hx0]
        congr 1
        funext k
        simp
      rw [mul_assoc, hsplit, laurentMonomial_natCast]
      congr 1
      exact (Finset.prod_subset (Finset.subset_univ e.support) fun k _ hk ↦ by
        rw [Finsupp.notMem_support_iff.mp hk, pow_zero])
  obtain ⟨n, hnmem, hnP⟩ := key P hPchar
  obtain ⟨w, hwmem, hwQ⟩ := key Q hQchar
  have hmon0 : laurentMonomial x (fun k ↦ ((d k : ℤ))) ≠ 0 := laurentMonomial_ne_zero hx0 _
  have hQpoly0 : Q ≠ 0 := by
    intro h
    rw [h, MvPolynomial.support_zero] at hd
    exact absurd hd (Finset.notMem_empty d)
  have hQ0 : MvPolynomial.aeval x Q ≠ 0 := fun h ↦
    hQpoly0 (algebraicIndependent_iff.mp
      (algebraicIndependent_palette_over_velocityField hx hgen hconst) Q h)
  have hw0 : w ≠ 0 := by
    intro h
    apply hQ0
    rw [hwQ, h, zero_mul]
  have hcancel : z * w = n := by
    refine mul_right_cancel₀ hmon0 ?_
    rw [mul_assoc, ← hwQ, hPQeq, hnP]
  have hzeq : z = n / w := by
    rw [eq_div_iff hw0]
    exact hcancel
  rw [hzeq]
  exact div_mem hnmem hwmem

include hx hgen in
/-- **The invariant field of a set of rescalings.**  It is the velocity field with the monomials
annihilating the set adjoined. -/
theorem torusScale_invariant_iff_mem_torusInvariantMonomialField [CharZero C]
    (hconst : ∀ c : C, c′ = 0) {S : Set (Fin r → Cˣ)} {z : E} :
    (∀ u ∈ S, torusScaleEquiv hx hgen u z = z) ↔ z ∈ torusInvariantMonomialField C x S :=
  ⟨fun hfix ↦ mem_torusInvariantMonomialField_of_torusScale_invariant hx hgen hconst hfix,
    fun hz _ hu ↦ torusScale_invariant_of_mem_torusInvariantMonomialField hx hgen hconst hz hu⟩

end Invariance

end

end GaloisForLFunctions.HTGeometry
