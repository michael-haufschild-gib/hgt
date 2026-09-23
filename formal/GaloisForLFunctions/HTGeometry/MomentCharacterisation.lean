import GaloisForLFunctions.HTGeometry.HamburgerExistence

/-!
# Positive definiteness characterises representability

`positiveMomentForm_of_infiniteSupport` builds a positive definite form from a representing measure
charging the complement of every finite set.  That support hypothesis is not an extra assumption to
be carried around: it is *forced*.  If some finite set carried all the mass, the polynomial
vanishing on it would be a nonzero polynomial of zero norm, contradicting positive definiteness.

Combining this with the existence theorem gives the characterisation: a moment sequence has a
positive definite form exactly when it is represented by a finite measure with infinite support.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The monic polynomial vanishing on a finite set. -/
noncomputable def vanishingPoly (F : Finset ℝ) : Polynomial ℝ := ∏ a ∈ F, (X - C a)

theorem vanishingPoly_monic (F : Finset ℝ) : (vanishingPoly F).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem vanishingPoly_ne_zero (F : Finset ℝ) : vanishingPoly F ≠ 0 :=
  (vanishingPoly_monic F).ne_zero

theorem vanishingPoly_eval_eq_zero {F : Finset ℝ} {x : ℝ} (hx : x ∈ F) :
    (vanishingPoly F).eval x = 0 := by
  rw [vanishingPoly, eval_prod]
  exact Finset.prod_eq_zero hx (by simp)

/-- **Positive definiteness forces infinite support.**  Any measure representing a positive
definite moment sequence charges the complement of every finite set. -/
theorem measure_compl_finset_pos_of_positiveMomentForm (h : PositiveMomentForm s)
    {ν : Measure ℝ} (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂ν)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) ν) (F : Finset ℝ) :
    0 < ν {x : ℝ | x ∉ F} := by
  rcases eq_or_ne (ν {x : ℝ | x ∉ F}) 0 with hzero | hne
  · exfalso
    set p := vanishingPoly F with hp
    have hae : (fun x : ℝ => (Polynomial.eval x p) ^ (2 : ℕ)) =ᵐ[ν] fun _ => (0 : ℝ) := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun x hx => ?_) hzero
      simp only [Set.mem_setOf_eq]
      intro hxF
      exact hx (by rw [hp, vanishingPoly_eval_eq_zero hxF]; ring)
    have hzeroint : momentInner s p p = 0 := by
      rw [momentInner_def, ← sq, momentFunctional_pow_two_eq_integral_sq s hs hint p,
        integral_eq_zero_of_ae hae]
    exact absurd hzeroint (ne_of_gt (h.pos_of_ne_zero p (vanishingPoly_ne_zero F)))
  · exact pos_iff_ne_zero.mpr hne

/-- **Characterisation.**  A moment sequence is positive definite exactly when some finite measure
with infinite support represents it. -/
theorem positiveMomentForm_iff_exists_representing (s : ℕ → ℝ) :
    PositiveMomentForm s ↔
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
        GaloisForLFunctions.HTGeometry.HasHamburgerMoments s ν ∧
        ∀ F : Finset ℝ, 0 < ν {x : ℝ | x ∉ F} := by
  constructor
  · intro h
    obtain ⟨ν, hfin, hmom⟩ := exists_finiteMeasure_hasHamburgerMoments h
    exact ⟨ν, hfin, hmom, measure_compl_finset_pos_of_positiveMomentForm h
      (fun k => (hmom k).2.symm) (fun k => (hmom k).1)⟩
  · rintro ⟨ν, -, hmom, hinf⟩
    exact positiveMomentForm_of_infiniteSupport s (fun k => (hmom k).2.symm)
      (fun k => (hmom k).1) hinf

end HTGeometry
