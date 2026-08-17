import GaloisForLFunctions.RHTower.SchanuelPeriodBranchDefect

/-!
# The algebraic-period branch of the period-completion dichotomy

When the period is algebraic over the value field, the Kähler module does not grow: the period
differential lies in the span of the old defect, so every shifted defect pair is collinear and has
rank at most one.

The additive coordinates nevertheless stay rationally independent for all but one affine line of
integral shifts.  Writing the period as a rational combination of the two coordinates, the shifted
pair is the image of the old pair under `1 + k qᵀ`, whose determinant is `1 + q₁k₁ + q₂k₂`; the
shifted pair is independent whenever that number is nonzero, and only one rational line of integer
shifts is excluded, so infinitely many shifts survive.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## Collinear pairs are never independent -/

section Collinear

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Two multiples of one vector are never linearly independent. -/
theorem not_linearIndependent_smul_pair (u : V) (a b : F) :
    ¬ LinearIndependent F ![a • u, b • u] := by
  intro hind
  by_cases ha : a = 0
  · have hzero : (![a • u, b • u] : Fin 2 → V) 0 = 0 := by
      simp [ha]
    exact hind.ne_zero 0 hzero
  · have hrel : ∑ j, (![b, -a] : Fin 2 → F) j • (![a • u, b • u] : Fin 2 → V) j = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      module
    have h1 := Fintype.linearIndependent_iff.mp hind ![b, -a] hrel 1
    simp only [Matrix.cons_val_one] at h1
    exact ha (neg_eq_zero.mp h1)

/-- **The algebraic-period case has rank at most one.**  If the period differential is a multiple of
the defect, every shifted defect pair is collinear, hence dependent. -/
theorem not_linearIndependent_period_shift_of_mem_span (epsilon : V) (c rho k₁ k₂ m : F) :
    ¬ LinearIndependent F ![
      m⁻¹ • (epsilon - k₁ • (c • epsilon)),
      m⁻¹ • (rho • epsilon - k₂ • (c • epsilon))] := by
  have hfirst : m⁻¹ • (epsilon - k₁ • (c • epsilon)) = (m⁻¹ * (1 - k₁ * c)) • epsilon := by
    module
  have hsecond : m⁻¹ • (rho • epsilon - k₂ • (c • epsilon)) = (m⁻¹ * (rho - k₂ * c)) • epsilon := by
    module
  rw [hfirst, hsecond]
  exact not_linearIndependent_smul_pair epsilon _ _

end Collinear

/-! ## The rational shift criterion -/

section Shift

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **The determinant criterion for an affine period shift.**  If the period is the rational
combination `q₁x₁ + q₂x₂` of an independent pair, the shifted pair `xᵢ + kᵢτ` stays independent
whenever `1 + q₁k₁ + q₂k₂ ≠ 0`. -/
theorem linearIndependent_period_shift_of_det_ne_zero {x₁ x₂ : V}
    (hx : LinearIndependent F ![x₁, x₂]) (q₁ q₂ k₁ k₂ : F)
    (hdet : 1 + q₁ * k₁ + q₂ * k₂ ≠ 0) :
    LinearIndependent F ![x₁ + k₁ • (q₁ • x₁ + q₂ • x₂), x₂ + k₂ • (q₁ • x₁ + q₂ • x₂)] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  -- expand the relation in the old coordinates
  have hexp : ((c 0 * (1 + k₁ * q₁) + c 1 * (k₂ * q₁)) • x₁
      + (c 0 * (k₁ * q₂) + c 1 * (1 + k₂ * q₂)) • x₂) = 0 := by
    rw [Fin.sum_univ_two] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    rw [← hc]
    module
  have hrel : ∑ j, (![c 0 * (1 + k₁ * q₁) + c 1 * (k₂ * q₁),
      c 0 * (k₁ * q₂) + c 1 * (1 + k₂ * q₂)] : Fin 2 → F) j •
      (![x₁, x₂] : Fin 2 → V) j = 0 := by
    rw [Fin.sum_univ_two]
    simpa using hexp
  have h0 := Fintype.linearIndependent_iff.mp hx _ hrel 0
  have h1 := Fintype.linearIndependent_iff.mp hx _ hrel 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hc0 : (1 + q₁ * k₁ + q₂ * k₂) * c 0 = 0 := by
    linear_combination (1 + k₂ * q₂) * h0 - (k₂ * q₁) * h1
  have hc1 : (1 + q₁ * k₁ + q₂ * k₂) * c 1 = 0 := by
    linear_combination (1 + k₁ * q₁) * h1 - (k₁ * q₂) * h0
  fin_cases i
  · exact (mul_eq_zero.mp hc0).resolve_left hdet
  · exact (mul_eq_zero.mp hc1).resolve_left hdet

/-- **The transcendental-period case keeps every shift independent.**  If the period is
independent of the two coordinates, then every integral shift of the pair stays independent. -/
theorem linearIndependent_period_shift_of_linearIndependent_triple {x₁ x₂ tau : V}
    (hx : LinearIndependent F ![x₁, x₂, tau]) (k₁ k₂ : F) :
    LinearIndependent F ![x₁ + k₁ • tau, x₂ + k₂ • tau] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hrel : ∑ j, (![c 0, c 1, c 0 * k₁ + c 1 * k₂] : Fin 3 → F) j •
      (![x₁, x₂, tau] : Fin 3 → V) j = 0 := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [Fin.sum_univ_two] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
    rw [← hc]
    module
  have h0 := Fintype.linearIndependent_iff.mp hx _ hrel 0
  have h1 := Fintype.linearIndependent_iff.mp hx _ hrel 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  fin_cases i
  · exact h0
  · exact h1

end Shift

/-! ## Infinitely many surviving shifts -/

section Infinite

/-- **Only one rational line of shifts is excluded.**  The integral shifts whose determinant is
nonzero form an infinite set. -/
theorem infinite_setOf_det_ne_zero (q₁ q₂ : ℚ) :
    {k : ℤ × ℤ | 1 + q₁ * (k.1 : ℚ) + q₂ * (k.2 : ℚ) ≠ 0}.Infinite := by
  classical
  by_cases hq : q₁ = 0
  · -- the first coordinate is free
    refine Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => ((n : ℤ), (0 : ℤ))) ?_ ?_
    · intro a b hab
      simpa using hab
    · intro n
      simp [hq]
  · -- for each second coordinate one of two first coordinates works
    refine Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ =>
        ((if 1 + q₂ * (n : ℚ) = 0 then 1 else 0 : ℤ), (n : ℤ))) ?_ ?_
    · intro a b hab
      have := congrArg Prod.snd hab
      simpa using this
    · intro n
      by_cases hn : 1 + q₂ * (n : ℚ) = 0
      · simp only [Set.mem_setOf_eq, hn, if_pos]
        push_cast
        rw [show (1 : ℚ) + q₁ * 1 + q₂ * (n : ℚ) = q₁ + (1 + q₂ * (n : ℚ)) by ring, hn, add_zero]
        exact hq
      · simp only [Set.mem_setOf_eq, hn, if_neg, not_false_iff]
        push_cast
        rw [show (1 : ℚ) + q₁ * 0 + q₂ * (n : ℚ) = 1 + q₂ * (n : ℚ) by ring]
        exact hn

end Infinite

end

end GaloisForLFunctions.RHTower
