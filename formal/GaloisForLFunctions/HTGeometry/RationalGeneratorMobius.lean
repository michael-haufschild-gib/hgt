import Mathlib.FieldTheory.RatFunc.Luroth

/-!
# A rational function that generates is a Möbius transform

A rational function generates the whole rational function field exactly when the extension it cuts out
has degree one, and that degree is the larger of the degrees of its numerator and denominator.  So a
generator has numerator and denominator of degree at most one, and coprimality forces the resulting
two-by-two coefficient matrix to be invertible.

This is the classification of generator changes: two generators of the same rational function field
differ by an element of `PGL₂`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IntermediateField

noncomputable section

variable {K : Type*} [Field K]

/-- **A generator of the rational function field is a Möbius transform of the coordinate.**  Its
numerator and denominator are linear with invertible coefficient matrix. -/
theorem exists_mobius_of_finrank_eq_one {f : RatFunc K}
    (h : Module.finrank K⟮f⟯ (RatFunc K) = 1) :
    ∃ a b c d : K, a * d - b * c ≠ 0 ∧
      f * (algebraMap K[X] (RatFunc K)) (C c * X + C d)
        = (algebraMap K[X] (RatFunc K)) (C a * X + C b) := by
  have hmax : max f.num.natDegree f.denom.natDegree = 1 := by
    rw [← RatFunc.finrank_eq_max_natDegree f]
    exact h
  have hnumle : f.num.natDegree ≤ 1 := le_of_max_le_left (le_of_eq hmax)
  have hdenle : f.denom.natDegree ≤ 1 := le_of_max_le_right (le_of_eq hmax)
  have hnum : f.num = C (f.num.coeff 1) * X + C (f.num.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one hnumle
  have hden : f.denom = C (f.denom.coeff 1) * X + C (f.denom.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one hdenle
  set a := f.num.coeff 1
  set b := f.num.coeff 0
  set c := f.denom.coeff 1
  set d := f.denom.coeff 0
  have hfne : f ≠ 0 := by
    intro h0
    rw [h0] at hmax
    simp at hmax
  have hnum0 : f.num ≠ 0 := RatFunc.num_ne_zero hfne
  have hcop : IsCoprime f.num f.denom := RatFunc.isCoprime_num_denom f
  refine ⟨a, b, c, d, ?_, ?_⟩
  · -- the coefficient matrix is invertible
    intro hdet
    have hkey : C c * f.num = C a * f.denom := by
      rw [hnum, hden]
      ring_nf
      rw [← C_mul, ← C_mul, ← C_mul,
        show c * b = a * d from by linear_combination -hdet]
    by_cases ha : a = 0
    · -- then the denominator is constant and the numerator is linear
      have hc : c = 0 := by
        have : C c * f.num = 0 := by rw [hkey, ha, map_zero, zero_mul]
        rcases mul_eq_zero.1 this with hc0 | hn0
        · simpa using congrArg (fun p => Polynomial.coeff p 0) hc0
        · exact absurd hn0 hnum0
      have hdenc : f.denom = C d := by rw [hden, hc, map_zero, zero_mul, zero_add]
      have hdeg : f.denom.natDegree = 0 := by rw [hdenc]; exact natDegree_C d
      have hnumdeg : f.num.natDegree = 1 := by
        rw [hdeg] at hmax
        simpa using hmax
      have hane : a ≠ 0 := by
        have hlead : f.num.coeff f.num.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hnum0
        rwa [hnumdeg] at hlead
      exact hane ha
    · -- coprimality forces both degrees to vanish
      have hdvd1 : f.num ∣ C a * f.denom := ⟨C c, by rw [← hkey]; ring⟩
      have hnumdvd : f.num ∣ C a := hcop.dvd_of_dvd_mul_right hdvd1
      have hdegnum : f.num.natDegree = 0 := by
        have hCa : (C a : K[X]) ≠ 0 := by simpa using ha
        have := Polynomial.natDegree_le_of_dvd hnumdvd hCa
        simpa using this
      have hdvd2 : f.denom ∣ C c * f.num := ⟨C a, by rw [hkey]; ring⟩
      have hdegden : f.denom.natDegree = 0 := by
        by_cases hc : c = 0
        · have : f.denom = C d := by rw [hden, hc, map_zero, zero_mul, zero_add]
          rw [this]
          exact natDegree_C d
        · have hCc : (C c : K[X]) ≠ 0 := by simpa using hc
          have hdenddvd : f.denom ∣ C c := hcop.symm.dvd_of_dvd_mul_right hdvd2
          have := Polynomial.natDegree_le_of_dvd hdenddvd hCc
          simpa using this
      rw [hdegnum, hdegden] at hmax
      simp at hmax
  · -- the Möbius identity
    set A := (algebraMap K[X] (RatFunc K)) f.num with hA
    set B := (algebraMap K[X] (RatFunc K)) f.denom with hB
    have hden0 : B ≠ 0 := by
      rw [hB]
      simpa using RatFunc.denom_ne_zero f
    have hAB : A / B = f := RatFunc.num_div_denom f
    have hmul : f * B = A := by
      rw [← hAB]
      field_simp
    rw [← hnum, ← hden]
    exact hmul

/-- **A generator is a Möbius transform.**  Stated with the generation hypothesis directly: if a
rational function adjoins to everything, it is a Möbius transform of the coordinate. -/
theorem exists_mobius_of_adjoin_eq_top {f : RatFunc K} (h : K⟮f⟯ = ⊤) :
    ∃ a b c d : K, a * d - b * c ≠ 0 ∧
      f * (algebraMap K[X] (RatFunc K)) (C c * X + C d)
        = (algebraMap K[X] (RatFunc K)) (C a * X + C b) :=
  exists_mobius_of_finrank_eq_one (by rw [h]; exact IntermediateField.finrank_top)

/-- **Mutually generating elements differ by a Möbius transform.**  If a transcendental `y` and an
element `v` generate the same simple extension, then `v` is a Möbius transform of `y` with invertible
coefficient matrix.  This is the generator classification: a change of generator of a simple purely
transcendental extension is projective. -/
theorem exists_mobius_of_mutual_adjoin {C E : Type*} [Field C] [Field E] [Algebra C E]
    {y v : E} (hy : Transcendental C y) (hv : v ∈ C⟮y⟯) (hyv : y ∈ C⟮v⟯) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      v * (algebraMap C E c * y + algebraMap C E d)
        = algebraMap C E a * y + algebraMap C E b := by
  classical
  have hEq : C⟮v⟯ = C⟮y⟯ :=
    le_antisymm (IntermediateField.adjoin_simple_le_iff.2 hv)
      (IntermediateField.adjoin_simple_le_iff.2 hyv)
  set e := RatFunc.algEquivOfTranscendental y hy with he
  set w : ↥C⟮y⟯ := ⟨v, hv⟩ with hw
  set F := e.symm w with hF
  -- `w` generates the simple extension, read inside it
  have hvaltop : IntermediateField.map (C⟮y⟯.val) (⊤ : IntermediateField C ↥C⟮y⟯) = C⟮y⟯ := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ⟨⟨x, hx⟩, trivial, rfl⟩)
    obtain ⟨z, -, rfl⟩ := hx
    exact z.2
  have hwtop : C⟮w⟯ = (⊤ : IntermediateField C ↥C⟮y⟯) := by
    refine IntermediateField.map_injective (C⟮y⟯.val) ?_
    rw [IntermediateField.adjoin_map, hvaltop]
    have himg : (C⟮y⟯.val : ↥C⟮y⟯ →ₐ[C] E) '' ({w} : Set ↥C⟮y⟯) = ({v} : Set E) := by
      simp [hw]
    rw [himg]
    exact hEq
  -- transport to the rational function field
  have hFtop : C⟮F⟯ = (⊤ : IntermediateField C (RatFunc C)) := by
    refine IntermediateField.map_injective (e : RatFunc C →ₐ[C] ↥C⟮y⟯) ?_
    rw [IntermediateField.adjoin_map]
    have himg : (e : RatFunc C →ₐ[C] ↥C⟮y⟯) '' ({F} : Set (RatFunc C)) = ({w} : Set ↥C⟮y⟯) := by
      simp [hF]
    rw [himg, hwtop]
    exact le_antisymm (fun x _ => ⟨e.symm x, trivial, by simp⟩) le_top
  obtain ⟨a, b, c, d, hdet, hmob⟩ := exists_mobius_of_adjoin_eq_top hFtop
  refine ⟨a, b, c, d, hdet, ?_⟩
  have hmap := congrArg (fun z => ((e z : ↥C⟮y⟯) : E)) hmob
  simp only [map_mul, map_add] at hmap
  have hC : ∀ t : C, ((e (RatFunc.C t) : ↥C⟮y⟯) : E) = algebraMap C E t := by
    intro t
    have hCt : (RatFunc.C t : RatFunc C) = algebraMap C (RatFunc C) t := by
      simp [RatFunc.algebraMap_eq_C]
    rw [hCt, AlgEquiv.commutes]
    simp
  have hX : ((e (RatFunc.X : RatFunc C) : ↥C⟮y⟯) : E) = y := by
    simp [he]
  simpa [hF, hw, hC, hX] using hmap

end

end GaloisForLFunctions.HTGeometry
