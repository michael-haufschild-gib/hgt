import GaloisForLFunctions.RepresentationLifting.Probability.QuadraticMatrixFibres

/-!
# Quadratic root counts from root separation

Over a finite commutative ring, marking a root and translating it to zero
replaces both quadratic coefficients by a single separation parameter.
Weighting each marked root by the reciprocal fibre size counts exactly
the split coefficient labels. This counts even nonreduced residue rings
in the finite approximations to Lapid and Shusterman's Lemma C.1.
-/

namespace GaloisForLFunctions.RepresentationLifting
open Finset
noncomputable section
open scoped Classical
variable {R : Type*} [CommRing R]

/-- Root count of a monic quadratic known to have the marked root zero. -/
abbrev separatedRootCount (s : R) : ℕ := Nat.card (traceDetRoot s 0)

private theorem translate_marked_root_count (t x : R) :
    Nat.card (traceDetRoot t (x*(t-x))) = separatedRootCount (t-2*x) := by
  have h := Nat.card_congr (traceDetRootTranslate (t-2*x) 0 x)
  rw [sub_add_cancel,show 0+x*(t-2*x)+x^2=x*(t-x) by ring] at h
  exact h.symm

variable [Fintype R]

/-- The root-count distribution for uniformly marked quadratics is the
one-parameter distribution of roots of X(X-s), including zero divisors. -/
theorem quadratic_marked_root_sum (W : ℕ → ℝ) :
    ∑ z : R×R, (Nat.card (traceDetRoot z.1 z.2):ℝ)*W (Nat.card (traceDetRoot z.1 z.2)) =
      (Fintype.card R:ℝ)*∑ s : R, W (separatedRootCount s) := by
  have atTrace (t : R) :
      ∑ d : R, (Nat.card (traceDetRoot t d):ℝ)*W (Nat.card (traceDetRoot t d)) =
        ∑ x : R, W (separatedRootCount (t-2*x)) := by
    have hf := Fintype.sum_fiberwise' (fun x : R => x*(t-x)) (fun d => W (Nat.card (traceDetRoot t d)))
    simp only [sum_const,card_univ,nsmul_eq_mul] at hf
    simpa only [Nat.card_eq_fintype_card (α := traceDetRoot t _)] using
      hf.trans (sum_congr rfl fun x _ => congrArg W (translate_marked_root_count t x))
  rw [Fintype.sum_prod_type]
  change ∑ t : R, (∑ d : R, _) = _
  rw [sum_congr rfl (fun t _ => atTrace t),sum_comm]
  have oneRoot (x : R) : ∑ t : R, W (separatedRootCount (t-2*x)) = ∑ s : R, W (separatedRootCount s) :=
    (Equiv.subRight (2*x)).sum_comp (fun s => W (separatedRootCount s))
  simp_rw [oneRoot]
  rw [sum_const,card_univ,nsmul_eq_mul]

/-- Split coefficient labels over a finite ring, counted once regardless
of the number of factorizations or the multiplicities of the roots. -/
def splitCoefficientLabels (R : Type*) [CommRing R] [Fintype R] : Finset (R×R) :=
  univ.filter fun z => ∃ x : R, x*(z.1-x)=z.2

/-- Exact probability that a uniform monic quadratic has a root in R.
Only the one-dimensional root counts of X(X-s) enter the formula. -/
theorem split_probability_as_mean_inverse_roots :
    ((splitCoefficientLabels R).card:ℝ)/(Fintype.card R:ℝ)^2 =
      (∑ s : R, (separatedRootCount s:ℝ)⁻¹)/(Fintype.card R:ℝ) := by
  have h := quadratic_marked_root_sum (R:=R) (fun n => (n:ℝ)⁻¹)
  have unmark (z : R×R) :
      (Nat.card (traceDetRoot z.1 z.2):ℝ)*(Nat.card (traceDetRoot z.1 z.2):ℝ)⁻¹ =
        if ∃ x : R, x*(z.1-x)=z.2 then (1:ℝ) else 0 := by
    split
    · rename_i hx
      obtain ⟨x,hx⟩ := hx
      letI : Nonempty (traceDetRoot z.1 z.2) := ⟨⟨x,hx⟩⟩
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.card_pos (α := traceDetRoot z.1 z.2)).ne')
    · rename_i hx
      letI : IsEmpty (traceDetRoot z.1 z.2) := ⟨fun x => hx ⟨x.val,x.property⟩⟩
      simp only [Nat.card_of_isEmpty,Nat.cast_zero,zero_mul]
  simp_rw [unmark] at h
  rw [sum_boole] at h
  change ((splitCoefficientLabels R).card:ℝ) = _ at h
  have hq : (Fintype.card R:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [h]
  field_simp [hq]

#print axioms quadratic_marked_root_sum
#print axioms split_probability_as_mean_inverse_roots
end
end GaloisForLFunctions.RepresentationLifting
