/-
# The criticality expression on the joint ring is homogeneous

Written on the joint variable set, with the auxiliary variable replaced by the linear form of the
spectral action and the shell coefficients renamed in, the corrected criticality expression is
homogeneous: its gradient term carries degrees `(M − n − 1) + 2 + n` and its radial term
`(M − n) + (n − 1) + 2`, both equal to `M + 1`.  The two boundary terms vanish -- the gradient one
because a degree-zero homogeneous polynomial is constant, the radial one because its scalar factor
is zero.

Main results:
* `eq_C_of_isHomogeneous_zero`, `pderiv_eq_zero_of_isHomogeneous_zero` — degree zero means constant.
* `isHomogeneous_normSqPoly` — the norm-square polynomial has degree two.
* `jointCriticality`, `isHomogeneous_jointCriticality` — **the homogeneous criticality expression**.
-/
import GaloisForLFunctions.HTGeometry.JointSpectralAction
import GaloisForLFunctions.HTGeometry.HomogenisedCriticality

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

theorem eq_C_of_isHomogeneous_zero {σ R : Type*} [CommRing R] {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous 0) : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
  classical
  ext α
  rw [MvPolynomial.coeff_C]
  by_cases hα : α = 0
  · subst hα
    simp
  · rw [if_neg (Ne.symm hα)]
    by_contra hc
    have hw := hp hc
    have hsum : ∑ i ∈ α.support, α i = 0 := by
      rw [← hw, Finsupp.weight_apply]
      simp [Finsupp.sum]
    have hempty : α.support = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_of_ne_empty hne
      exact (Finsupp.mem_support_iff.mp hi) ((Finset.sum_eq_zero_iff.mp hsum) i hi)
    exact hα (Finsupp.support_eq_empty.mp hempty)

theorem pderiv_eq_zero_of_isHomogeneous_zero {σ R : Type*} [CommRing R] {p : MvPolynomial σ R}
    (hp : p.IsHomogeneous 0) (i : σ) : MvPolynomial.pderiv i p = 0 := by
  rw [eq_C_of_isHomogeneous_zero hp, MvPolynomial.pderiv_C]

theorem isHomogeneous_normSqPoly : (normSqPoly N).IsHomogeneous 2 := by
  rw [normSqPoly]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
  simpa using (MvPolynomial.isHomogeneous_X ℝ a).pow 2

/-- The corrected criticality expression of one labelling and one direction, on the joint ring. -/
def jointCriticality (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π : Equiv.Perm (Fin D)) (i : Fin N) : MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  (∑ n ∈ Finset.range (M + 1),
      MvPolynomial.rename Sum.inr (MvPolynomial.pderiv i (c n))
        * MvPolynomial.rename Sum.inr (normSqPoly N) * (jointAction k π) ^ n)
    + (∑ n ∈ Finset.range (M + 1),
        MvPolynomial.C (n : ℝ) * MvPolynomial.rename Sum.inr (c n)
          * (jointAction k π) ^ (n - 1))
      * ((jointAction k π) * MvPolynomial.X (Sum.inr i))

/-- **The criticality expression on the joint ring is homogeneous of degree `M + 1`.** -/
theorem isHomogeneous_jointCriticality (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (hc : ∀ n, (c n).IsHomogeneous (M - n)) (k : Fin D → ℝ) (π : Equiv.Perm (Fin D))
    (i : Fin N) :
    (jointCriticality M c k π i).IsHomogeneous (M + 1) := by
  classical
  refine MvPolynomial.IsHomogeneous.add ?_ ?_
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun n hn => ?_
    have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rcases Nat.eq_or_lt_of_le hnM with hEq | hLt
    · subst hEq
      have hzero : MvPolynomial.pderiv i (c n) = 0 := by
        refine pderiv_eq_zero_of_isHomogeneous_zero ?_ i
        simpa using hc n
      rw [hzero, map_zero, zero_mul, zero_mul]
      exact MvPolynomial.isHomogeneous_zero _ _ _
    · have hdeg : M - n - 1 + 2 + n = M + 1 := by omega
      rw [← hdeg]
      exact ((isHomogeneous_rename_inr ((hc n).pderiv)).mul
        (isHomogeneous_rename_inr isHomogeneous_normSqPoly)).mul
        (by simpa using (isHomogeneous_jointAction k π).pow n)
  · rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      have hsum0 : (∑ n ∈ Finset.range (0 + 1),
          MvPolynomial.C ((n : ℕ) : ℝ) * MvPolynomial.rename Sum.inr (c n)
            * (jointAction k π) ^ (n - 1)) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        have hn0 : n = 0 := Nat.lt_one_iff.mp (by simpa using Finset.mem_range.mp hn)
        subst hn0
        simp
      rw [hsum0, zero_mul]
      exact MvPolynomial.isHomogeneous_zero _ _ _
    · have h1 : (∑ n ∈ Finset.range (M + 1),
          MvPolynomial.C ((n : ℕ) : ℝ) * MvPolynomial.rename Sum.inr (c n)
            * (jointAction k π) ^ (n - 1)).IsHomogeneous (M - 1) := by
        refine MvPolynomial.IsHomogeneous.sum _ _ _ fun n hn => ?_
        rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · subst hn0
          simp only [Nat.cast_zero, MvPolynomial.C_0, zero_mul]
          exact MvPolynomial.isHomogeneous_zero _ _ _
        · have hnM : n ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
          have hdeg : (0 : ℕ) + (M - n) + (n - 1) = M - 1 := by omega
          rw [← hdeg]
          exact ((MvPolynomial.isHomogeneous_C _ ((n : ℝ))).mul
            (isHomogeneous_rename_inr (hc n))).mul
            (by simpa using (isHomogeneous_jointAction k π).pow (n - 1))
      have h2a := (isHomogeneous_jointAction (N := N) k π).mul
        (MvPolynomial.isHomogeneous_X ℝ (Sum.inr i : Fin D ⊕ Fin N))
      have h2 : ((jointAction k π) *
          MvPolynomial.X (Sum.inr i : Fin D ⊕ Fin N)).IsHomogeneous 2 := by
        simpa using h2a
      have hmul := h1.mul h2
      have hEq : (M - 1) + 2 = M + 1 := by omega
      rwa [hEq] at hmul

end

end GaloisForLFunctions.HTGeometry
