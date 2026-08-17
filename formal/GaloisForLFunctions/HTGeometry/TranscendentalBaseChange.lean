import Mathlib

/-!
# Adjoining a transcendental element preserves linear independence

A family that is linearly independent over `F` and lies inside a field `E` over which `t` is
transcendental stays linearly independent over `F(t)`.

Clearing denominators turns an `F(t)`-relation into a polynomial relation `∑ P_i(t) b_i = 0`;
collecting powers of `t` exhibits it as a polynomial in `t` with coefficients in `E`, so
transcendence kills every coefficient, and independence over `F` kills every coefficient of every
`P_i`.

This is the linear-disjointness input to base change along a free parameter: it is what makes the
degree of a finite extension, and hence its Galois group, survive the adjunction of an independent
transcendental.
-/

open Polynomial IntermediateField

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- **Linear independence survives a transcendental adjunction.** -/
theorem linearIndependent_adjoin_transcendental
    (E : IntermediateField F Ω) (t : Ω) (ht : Transcendental E t)
    {ι : Type*} [Fintype ι] (b : ι → Ω) (hbE : ∀ i, b i ∈ E)
    (hind : LinearIndependent F b) :
    LinearIndependent (F⟮t⟯) b := by
  classical
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  -- write each coefficient as a quotient of polynomial values
  have hrep : ∀ i, ∃ r s : F[X], Polynomial.aeval t s ≠ 0 ∧
      (c i : Ω) = Polynomial.aeval t r / Polynomial.aeval t s := by
    intro i
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff F (c i : Ω)).1 (c i).2
    by_cases hs : Polynomial.aeval t s = 0
    · refine ⟨0, 1, ?_, ?_⟩
      · simp
      · rw [hrs, hs, div_zero]
        simp
    · exact ⟨r, s, hs, hrs⟩
  choose r s hs hcrs using hrep
  set S : Ω := ∏ i, Polynomial.aeval t (s i) with hS
  have hSne : S ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hs i
  -- the cleared numerators
  set P : ι → F[X] := fun i => r i * ∏ j ∈ Finset.univ.erase i, s j with hP
  have hclear : ∀ i, S * (c i : Ω) = Polynomial.aeval t (P i) := by
    intro i
    have hsplit : S = Polynomial.aeval t (s i) * ∏ j ∈ Finset.univ.erase i,
        Polynomial.aeval t (s j) := by
      rw [hS]
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [hP, map_mul, map_prod, hcrs i, hsplit]
    field_simp [hs i]
  -- the relation in `Ω`
  have hrel : ∑ i, Polynomial.aeval t (P i) * b i = 0 := by
    have hc' : ∑ i, (c i : Ω) * b i = 0 := by
      have := congrArg (fun x : Ω => x) hc
      simpa [Algebra.smul_def] using hc
    calc ∑ i, Polynomial.aeval t (P i) * b i
        = ∑ i, S * ((c i : Ω) * b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← hclear i]
          ring
      _ = S * ∑ i, (c i : Ω) * b i := by rw [Finset.mul_sum]
      _ = 0 := by rw [hc', mul_zero]
  -- read the relation as a polynomial over `E`
  set Q : (E)[X] := ∑ i, (P i).map (algebraMap F E) * Polynomial.C ⟨b i, hbE i⟩ with hQ
  have hQeval : Polynomial.aeval t Q = 0 := by
    rw [hQ, map_sum, ← hrel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Polynomial.aeval_C]
    congr 1
    rw [Polynomial.aeval_map_algebraMap]
  have hQ0 : Q = 0 := transcendental_iff.1 ht Q hQeval
  -- every coefficient of every numerator vanishes
  have hPzero : ∀ i, P i = 0 := by
    have hcoeff : ∀ k : ℕ, ∀ i, (P i).coeff k = 0 := by
      intro k
      have hQk : Q.coeff k = 0 := by rw [hQ0, Polynomial.coeff_zero]
      have hval : ((Q.coeff k : E) : Ω) = ∑ i, algebraMap F Ω ((P i).coeff k) * b i := by
        rw [hQ]
        simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_map]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rfl
      have hzero : ∑ i, algebraMap F Ω ((P i).coeff k) * b i = 0 := by
        rw [← hval, hQk]
        simp
      have := Fintype.linearIndependent_iff.1 hind (fun i => (P i).coeff k) ?_
      · exact this
      · simpa [Algebra.smul_def] using hzero
    intro i
    ext k
    simpa using hcoeff k i
  -- hence every coefficient vanishes
  intro i
  have : S * (c i : Ω) = 0 := by rw [hclear i, hPzero i, map_zero]
  have hci : (c i : Ω) = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hSne
    · exact h
  exact Subtype.ext hci

/-- The `F(t)`-span of a spanning family of `E` exhausts `E(t)`. -/
theorem adjoin_le_span_of_span
    (E : IntermediateField F Ω) [FiniteDimensional F E] (t : Ω)
    {ι : Type*} [Fintype ι] (b : ι → Ω)
    (hspanE : (E : Set Ω) ⊆ Submodule.span F (Set.range b)) :
    ((IntermediateField.adjoin (↥F⟮t⟯) (E : Set Ω) : IntermediateField (↥F⟮t⟯) Ω) : Set Ω)
      ⊆ Submodule.span (↥F⟮t⟯) (Set.range b) := by
  classical
  have halg : ∀ x ∈ (E : Set Ω), IsAlgebraic (↥F⟮t⟯) x := by
    intro x hx
    have hx' : IsAlgebraic F x := by
      have : IsIntegral F (⟨x, hx⟩ : ↥E) := IsIntegral.of_finite F _
      have h2 : IsIntegral F x := by
        simpa using this.map (IntermediateField.val E)
      exact h2.isAlgebraic
    exact hx'.tower_top (↥F⟮t⟯)
  have hsub := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := ↥F⟮t⟯) (S := (E : Set Ω))
    halg
  intro x hx
  have hxalg : x ∈ Algebra.adjoin (↥F⟮t⟯) (E : Set Ω) := by
    rw [← hsub]
    exact hx
  have hspan : (Algebra.adjoin (↥F⟮t⟯) (E : Set Ω) : Set Ω)
      ⊆ Submodule.span (↥F⟮t⟯) (E : Set Ω) := by
    intro y hy
    have hy' : y ∈ Subalgebra.toSubmodule (Algebra.adjoin (↥F⟮t⟯) (E : Set Ω)) := hy
    rw [Algebra.adjoin_eq_span] at hy'
    refine Submodule.span_le.2 ?_ hy'
    intro z hz
    refine Submonoid.closure_induction ?_ ?_ ?_ hz
    · intro w hw
      exact Submodule.subset_span hw
    · exact Submodule.subset_span (E.one_mem)
    · intro u v _ _ hu hv
      have : u * v ∈ (E : Set Ω) := by
        have hu' : u ∈ E := by
          have := Submodule.span_le.2 (le_refl ((E : Set Ω))) hu
          exact this
        have hv' : v ∈ E := by
          have := Submodule.span_le.2 (le_refl ((E : Set Ω))) hv
          exact this
        exact E.mul_mem hu' hv'
      exact Submodule.subset_span this
  have hxspan : x ∈ Submodule.span (↥F⟮t⟯) (E : Set Ω) := hspan hxalg
  refine Submodule.span_le.2 ?_ hxspan
  intro y hy
  have hy' : y ∈ Submodule.span F (Set.range b) := hspanE hy
  refine Submodule.span_le.2 ?_ hy'
  intro z hz
  exact Submodule.subset_span hz

end GaloisForLFunctions.HTGeometry

end
