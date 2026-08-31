import GaloisForLFunctions.HTGeometry.FlatFamilyIdeal

/-!
# The two fibres of the family

```text
familyIdeal_sup_X_sub_one   ** modulo t - 1 the family ideal is the ideal itself **
familyIdeal_sup_X           ** modulo t it is the initial ideal **
```

Both are the two evaluations of the homogenization, turned into ideal statements.  A homogenization
differs from the constant `f` by a multiple of `t - 1`, because evaluating at one returns `f`; and it
differs from the constant `lowestForm f` by a multiple of `t`, because its constant coefficient is
the lowest form.  The second inclusion in each case runs the same identity backwards, using for the
special fibre that the initial ideal is the `K`-span of the initial forms, so a span induction
reduces to a single generator.

Together with `familyIdeal_saturated` this is the flat family: torsion-free over the base line, with
the initial degeneration over `t = 0` and the original ideal over `t = 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **The generic fibre.**  Modulo `t - 1` the family ideal is the ideal itself. -/
theorem familyIdeal_sup_X_sub_one (w : σ → ℤ) (I : Ideal (MvPolynomial σ K)) :
    familyIdeal w I ⊔ Ideal.span {Polynomial.X - 1}
      = Ideal.map Polynomial.C I ⊔ Ideal.span {(Polynomial.X : Polynomial (MvPolynomial σ K)) - 1} := by
  have hone : (Polynomial.C (1 : MvPolynomial σ K)) = 1 := by simp
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
  · rw [familyIdeal, Ideal.span_le]
    rintro F ⟨f, hf, hf0, rfl⟩
    have hdvd : (Polynomial.X - Polynomial.C (1 : MvPolynomial σ K))
        ∣ homogenize w f - Polynomial.C (Polynomial.eval 1 (homogenize w f)) :=
      Polynomial.X_sub_C_dvd_sub_C_eval
    rw [homogenize_eval_one] at hdvd
    obtain ⟨G, hG⟩ := hdvd
    have hsplit : homogenize w f
        = Polynomial.C f + (Polynomial.X - Polynomial.C (1 : MvPolynomial σ K)) * G := by
      rw [← hG]
      ring
    rw [hsplit]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)) ?_
    refine Ideal.mem_sup_right (Ideal.mul_mem_right _ _ ?_)
    rw [hone]
    exact Ideal.subset_span rfl
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    · have hdvd : (Polynomial.X - Polynomial.C (1 : MvPolynomial σ K))
          ∣ homogenize w f - Polynomial.C (Polynomial.eval 1 (homogenize w f)) :=
        Polynomial.X_sub_C_dvd_sub_C_eval
      rw [homogenize_eval_one] at hdvd
      obtain ⟨G, hG⟩ := hdvd
      have hsplit : Polynomial.C f
          = homogenize w f - (Polynomial.X - Polynomial.C (1 : MvPolynomial σ K)) * G := by
        rw [← hG]
        ring
      rw [Ideal.mem_comap, hsplit]
      refine Ideal.sub_mem _
        (Ideal.mem_sup_left (homogenize_mem_familyIdeal hf hf0)) ?_
      refine Ideal.mem_sup_right (Ideal.mul_mem_right _ _ ?_)
      rw [hone]
      exact Ideal.subset_span rfl

theorem C_lowestForm_mem_sup {w : σ → ℤ} {I : Ideal (MvPolynomial σ K)} {f : MvPolynomial σ K}
    (hf : f ∈ I) (hf0 : f ≠ 0) :
    Polynomial.C (lowestForm w f)
      ∈ familyIdeal w I ⊔ Ideal.span {(Polynomial.X : Polynomial (MvPolynomial σ K))} := by
  have hdvd : (Polynomial.X : Polynomial (MvPolynomial σ K))
      ∣ homogenize w f - Polynomial.C ((homogenize w f).coeff 0) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero, sub_self]
  obtain ⟨G, hG⟩ := hdvd
  have hsplit : Polynomial.C (lowestForm w f) = homogenize w f - Polynomial.X * G := by
    rw [← hG, homogenize_coeff_zero]
    ring
  rw [hsplit]
  refine Ideal.sub_mem _ (Ideal.mem_sup_left (homogenize_mem_familyIdeal hf hf0)) ?_
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

/-- **The special fibre.**  Modulo `t` the family ideal is the initial ideal. -/
theorem familyIdeal_sup_X (w : σ → ℤ) (I : Ideal (MvPolynomial σ K)) :
    familyIdeal w I ⊔ Ideal.span {(Polynomial.X : Polynomial (MvPolynomial σ K))}
      = Ideal.map Polynomial.C (initialIdeal w I)
        ⊔ Ideal.span {(Polynomial.X : Polynomial (MvPolynomial σ K))} := by
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
  · rw [familyIdeal, Ideal.span_le]
    rintro F ⟨f, hf, hf0, rfl⟩
    have hdvd : (Polynomial.X : Polynomial (MvPolynomial σ K))
        ∣ homogenize w f - Polynomial.C ((homogenize w f).coeff 0) := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero, sub_self]
    obtain ⟨G, hG⟩ := hdvd
    have hsplit : homogenize w f
        = Polynomial.C (lowestForm w f) + Polynomial.X * G := by
      rw [← hG, homogenize_coeff_zero]
      ring
    rw [hsplit]
    refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right (Ideal.mul_mem_right _ _
      (Ideal.subset_span rfl)))
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (lowestForm_mem_initialIdeal hf hf0))
  · rw [Ideal.map_le_iff_le_comap]
    intro u hu
    rw [Ideal.mem_comap]
    rw [mem_initialIdeal_iff] at hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨f, hf, hf0, rfl⟩ := hv
      exact C_lowestForm_mem_sup hf hf0
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
      have hsm : (c • a : MvPolynomial σ K) = MvPolynomial.C c * a :=
        MvPolynomial.smul_eq_C_mul a c
      rw [hsm, map_mul]
      exact Ideal.mul_mem_left _ _ ha

end GaloisForLFunctions.HTGeometry
