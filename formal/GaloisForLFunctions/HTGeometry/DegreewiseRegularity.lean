import GaloisForLFunctions.HTGeometry.FamilyXGrading

/-!
# Regularity of a homogeneous element is a degreewise condition

```text
homogeneousComponent_mul_left     multiplying by a homogeneous polynomial shifts the components
IsHomogIdeal                      homogeneity of an ideal, stated with the standard components
forall_mem_of_forall_homogeneous  ** a homogeneous element that is regular on the homogeneous
                                     elements is regular **
```

Decompose: if `l · f` lies in a homogeneous ideal then so does every component of `l · f`, and
multiplying by a homogeneous element shifts components, so each `l · f_e` lies in the ideal; the
degreewise hypothesis then puts every `f_e` there, hence `f`.

This is the step that turns a Hilbert-function computation — which is inherently degreewise — into
the statement that a linear form is a nonzerodivisor.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **Multiplying by a homogeneous polynomial shifts the homogeneous components.** -/
theorem homogeneousComponent_mul_left {h : MvPolynomial σ K} {d : ℕ}
    (hh : h.IsHomogeneous d) (g : MvPolynomial σ K) (e : ℕ) :
    MvPolynomial.homogeneousComponent (d + e) (h * g)
      = h * MvPolynomial.homogeneousComponent e g := by
  classical
  ext γ
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hγ : Finsupp.degree γ = d + e
  · rw [if_pos hγ]
    refine Finset.sum_congr rfl ?_
    rintro ⟨α, β⟩ hαβ
    have hsum : α + β = γ := Finset.HasAntidiagonal.mem_antidiagonal.mp hαβ
    by_cases hα : MvPolynomial.coeff α h = 0
    · rw [hα, zero_mul, zero_mul]
    · have hdα : Finsupp.degree α = d := by
        have := hh hα
        rwa [weight_one_eq_degree] at this
      have hdβ : Finsupp.degree β = e := by
        have hadd : Finsupp.degree α + Finsupp.degree β = Finsupp.degree γ := by
          rw [← hsum]
          simp [map_add]
        omega
      rw [MvPolynomial.coeff_homogeneousComponent, if_pos hdβ]
  · rw [if_neg hγ]
    refine (Finset.sum_eq_zero ?_).symm
    rintro ⟨α, β⟩ hαβ
    have hsum : α + β = γ := Finset.HasAntidiagonal.mem_antidiagonal.mp hαβ
    by_cases hα : MvPolynomial.coeff α h = 0
    · rw [hα, zero_mul]
    · have hdα : Finsupp.degree α = d := by
        have := hh hα
        rwa [weight_one_eq_degree] at this
      have hdβ : Finsupp.degree β ≠ e := by
        intro hcon
        refine hγ ?_
        have hadd : Finsupp.degree α + Finsupp.degree β = Finsupp.degree γ := by
          rw [← hsum]
          simp [map_add]
        omega
      rw [MvPolynomial.coeff_homogeneousComponent, if_neg hdβ, mul_zero]

/-- Homogeneity of an ideal, stated with the standard components. -/
def IsHomogIdeal (a : Ideal (MvPolynomial σ K)) : Prop :=
  ∀ (e : ℕ) (f : MvPolynomial σ K), f ∈ a → MvPolynomial.homogeneousComponent e f ∈ a

/-- **Regularity of a homogeneous element is a degreewise condition.** -/
theorem forall_mem_of_forall_homogeneous {a : Ideal (MvPolynomial σ K)} (ha : IsHomogIdeal a)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d)
    (h : ∀ (e : ℕ) (f : MvPolynomial σ K), f.IsHomogeneous e → l * f ∈ a → f ∈ a)
    (f : MvPolynomial σ K) (hf : l * f ∈ a) : f ∈ a := by
  classical
  rw [← MvPolynomial.sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun e _ => ?_
  refine h e _ (MvPolynomial.homogeneousComponent_isHomogeneous e f) ?_
  rw [← homogeneousComponent_mul_left hl f e]
  exact ha _ _ hf

end GaloisForLFunctions.HTGeometry
