import GaloisForLFunctions.HTGeometry.FamilyXGrading
import GaloisForLFunctions.HTGeometry.DegreewiseRegularity

/-!
# The family ideal respects the `x`-grading

```text
xComp_famComp             the weight parts and the x-degree parts commute
eval_one_xComp            ** dehomogenising commutes with taking x-homogeneous parts **
IsXGradedIdeal            an ideal closed under x-homogeneous parts
isXGraded_familyIdeal     ** the family ideal of a homogeneous ideal is x-graded **
isXGraded_sup_span_C      ** and adjoining a homogeneous constant preserves that **
```

Both gradings act coefficientwise on the same array of coefficients — one restricts the support by
weight, the other by total degree — so they commute, and the membership criterion
`mem_familyIdeal_iff`, which tests the weight parts after dehomogenising, transfers directly.

For the adjoined constant the point is the shift lemma `homogeneousComponent_mul_left`: the
`x`-degree-`(d+e)` part of `H·l` is `l` times the degree-`e` part of `H`, and below `d` it vanishes.

This is what lets the graded pieces of the family be read off as modules over the base line: an
`x`-graded ideal meets each graded piece in a submodule whose image under evaluation is the graded
piece of the fibre.
-/

namespace GaloisForLFunctions.HTGeometry
open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- Below the degree of the homogeneous factor the components vanish. -/
theorem homogeneousComponent_mul_left_of_lt {l : MvPolynomial σ K} {d e : ℕ}
    (hl : l.IsHomogeneous d) (p : MvPolynomial σ K) (he : e < d) :
    MvPolynomial.homogeneousComponent e (l * p) = 0 := by
  classical
  ext γ
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero]
  by_cases hγ : Finsupp.degree γ = e
  · rw [if_pos hγ, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero ?_
    rintro ⟨α, β⟩ hαβ
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hαβ
    dsimp only at hαβ ⊢
    by_cases hα : MvPolynomial.coeff α l = 0
    · rw [hα, zero_mul]
    · have hdα : Finsupp.degree α = d := by
        have hw := hl hα
        rwa [weight_one_eq_degree] at hw
      have hdeg : Finsupp.degree α + Finsupp.degree β = Finsupp.degree γ := by
        rw [← hαβ]
        exact (AddMonoidHom.map_add Finsupp.degree α β).symm
      omega
  · rw [if_neg hγ]

/-- The two component operators commute: one restricts the support by total degree, the other by
weight. -/
theorem homogeneousComponent_weightedHomogeneousComponent (w : σ → ℤ) (c : ℤ) (e : ℕ)
    (p : MvPolynomial σ K) :
    MvPolynomial.homogeneousComponent e (MvPolynomial.weightedHomogeneousComponent w c p)
      = MvPolynomial.weightedHomogeneousComponent w c
          (MvPolynomial.homogeneousComponent e p) := by
  classical
  ext γ
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_homogeneousComponent]
  by_cases hd : Finsupp.degree γ = e <;> by_cases hw : Finsupp.weight w γ = c <;>
    simp [hd, hw]

theorem xComp_famComp (w : σ → ℤ) (d : ℤ) (e : ℕ) (F : Polynomial (MvPolynomial σ K)) :
    xComp e (famComp w d F) = famComp w d (xComp e F) := by
  refine Polynomial.ext fun j => ?_
  rw [xComp_coeff, famComp_coeff, famComp_coeff, xComp_coeff,
    homogeneousComponent_weightedHomogeneousComponent]

theorem support_xComp_subset (e : ℕ) (F : Polynomial (MvPolynomial σ K)) :
    (xComp e F).support ⊆ F.support := by
  intro j hj
  rw [Polynomial.mem_support_iff, xComp_coeff] at hj
  rw [Polynomial.mem_support_iff]
  intro hzero
  rw [hzero, map_zero] at hj
  exact hj rfl

theorem eval_one_eq_sum_support (F : Polynomial (MvPolynomial σ K)) :
    Polynomial.eval 1 F = ∑ j ∈ F.support, F.coeff j := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_congr rfl fun j _ => by simp

/-- **Evaluating at one commutes with taking `x`-homogeneous parts.** -/
theorem eval_one_xComp (e : ℕ) (F : Polynomial (MvPolynomial σ K)) :
    Polynomial.eval 1 (xComp e F)
      = MvPolynomial.homogeneousComponent e (Polynomial.eval 1 F) := by
  classical
  rw [eval_one_eq_sum_support, eval_one_eq_sum_support, map_sum,
    show (∑ j ∈ F.support, MvPolynomial.homogeneousComponent e (F.coeff j))
      = ∑ j ∈ F.support, (xComp e F).coeff j from
      Finset.sum_congr rfl fun j _ => (xComp_coeff e F j).symm]
  exact Finset.sum_subset (support_xComp_subset e F)
    fun j _ hj => Polynomial.notMem_support_iff.mp hj

/-- An ideal of the family ring that respects the `x`-grading. -/
def IsXGradedIdeal (A : Ideal (Polynomial (MvPolynomial σ K))) : Prop :=
  ∀ (e : ℕ) (F : Polynomial (MvPolynomial σ K)), F ∈ A → xComp e F ∈ A

/-- **The family ideal of a homogeneous ideal respects the `x`-grading.** -/
theorem isXGraded_familyIdeal (w : σ → ℤ) {I : Ideal (MvPolynomial σ K)} (hI : IsHomogIdeal I) :
    IsXGradedIdeal (familyIdeal w I) := by
  intro e F hF
  rw [mem_familyIdeal_iff] at hF ⊢
  intro d
  rw [← xComp_famComp, eval_one_xComp]
  exact hI e _ (hF d)

/-- **Adjoining a homogeneous constant keeps the ideal `x`-graded.** -/
theorem isXGraded_sup_span_C {A : Ideal (Polynomial (MvPolynomial σ K))} (hA : IsXGradedIdeal A)
    {l : MvPolynomial σ K} {d : ℕ} (hl : l.IsHomogeneous d) :
    IsXGradedIdeal (A ⊔ Ideal.span {Polynomial.C l}) := by
  intro e F hF
  obtain ⟨G, hG, y, hy, rfl⟩ := Submodule.mem_sup.mp hF
  obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [xComp_add]
  refine Submodule.add_mem _ (Submodule.mem_sup_left (hA e G hG)) ?_
  refine Submodule.mem_sup_right ?_
  rcases lt_or_ge e d with hlt | hge
  · have hzero : xComp e (H * Polynomial.C l) = 0 := by
      refine Polynomial.ext fun j => ?_
      rw [xComp_coeff, Polynomial.coeff_zero, Polynomial.coeff_mul_C,
        mul_comm (H.coeff j) l, homogeneousComponent_mul_left_of_lt hl _ hlt]
    rw [hzero]
    exact Submodule.zero_mem _
  · obtain ⟨e', rfl⟩ : ∃ e', e = d + e' := ⟨e - d, by omega⟩
    have hval : xComp (d + e') (H * Polynomial.C l) = xComp e' H * Polynomial.C l := by
      refine Polynomial.ext fun j => ?_
      rw [xComp_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C, xComp_coeff,
        mul_comm (H.coeff j) l, homogeneousComponent_mul_left hl (H.coeff j) e',
        mul_comm l (MvPolynomial.homogeneousComponent e' (H.coeff j))]
    rw [hval]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self (Polynomial.C l))

end GaloisForLFunctions.HTGeometry
