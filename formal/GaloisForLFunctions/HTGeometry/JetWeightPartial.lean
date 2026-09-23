import GaloisForLFunctions.HTGeometry.JetWeightAction

/-!
# The weighted action and the coordinate partials

The weighted torus acts on the coordinate of order `j` by `λ^j`, so it twists the corresponding
partial derivative by exactly that factor:

`∂_j(w_λ v) = λ^j · w_λ(∂_j v)`.

At the polynomial level this is a monomial computation; the extension to the free jet field is the
quotient rule.  The consequence used downstream is that the weight of a partial derivative is the
weight of the element minus the order of the coordinate, which is what pins the isobaric type of
each coefficient of a sliced normalizing shift.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C]

theorem weightScaleAlgEquiv_pderiv {lam : C} (h : lam ≠ 0) (j : ℕ) (a : JetPoly C Unit) :
    MvPolynomial.pderiv ((), j) (weightScaleAlgEquiv h a)
      = MvPolynomial.C (lam ^ j) * weightScaleAlgEquiv h (MvPolynomial.pderiv ((), j) a) := by
  induction a using MvPolynomial.induction_on with
  | C c =>
      have h2 : weightScaleAlgEquiv h (MvPolynomial.C c : JetPoly C Unit) = MvPolynomial.C c :=
        weightScaleAlgHom_C lam c
      rw [h2, MvPolynomial.pderiv_C]
      simp
  | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, hp, hq]
      ring
  | mul_X p n hp =>
      have hX : weightScaleAlgEquiv h (MvPolynomial.X n : JetPoly C Unit)
          = MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n := weightScaleAlgEquiv_X h n
      set d : JetPoly C Unit :=
        MvPolynomial.pderiv ((), j) (MvPolynomial.X n : JetPoly C Unit) with hddef
      have hdw : weightScaleAlgEquiv h d = d := by
        by_cases hn : ((), j) = n
        · rw [hddef, ← hn, MvPolynomial.pderiv_X_self, map_one]
        · rw [hddef, MvPolynomial.pderiv_X_of_ne (Ne.symm hn), map_zero]
      have hkey : MvPolynomial.C (lam ^ n.2) * d = MvPolynomial.C (lam ^ j) * d := by
        by_cases hn : ((), j) = n
        · rw [← hn]
        · rw [hddef, MvPolynomial.pderiv_X_of_ne (Ne.symm hn), mul_zero, mul_zero]
      have hleibL := (MvPolynomial.pderiv ((), j) :
        Derivation C (JetPoly C Unit) (JetPoly C Unit)).leibniz
          (weightScaleAlgEquiv h p) (MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n)
      have hleibC := (MvPolynomial.pderiv ((), j) :
        Derivation C (JetPoly C Unit) (JetPoly C Unit)).leibniz
          (MvPolynomial.C (lam ^ n.2) : JetPoly C Unit) (MvPolynomial.X n)
      have hleibR := (MvPolynomial.pderiv ((), j) :
        Derivation C (JetPoly C Unit) (JetPoly C Unit)).leibniz p (MvPolynomial.X n)
      simp only [smul_eq_mul, MvPolynomial.pderiv_C] at hleibL hleibC hleibR
      have hRHSexp : weightScaleAlgEquiv h
            (MvPolynomial.pderiv ((), j) (p * MvPolynomial.X n))
          = weightScaleAlgEquiv h (MvPolynomial.pderiv ((), j) p)
              * (MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n)
            + weightScaleAlgEquiv h p * d := by
        rw [hleibR, map_add, map_mul, map_mul, hX, hdw]
        ring
      have hLHSexp : MvPolynomial.pderiv ((), j) (weightScaleAlgEquiv h (p * MvPolynomial.X n))
          = MvPolynomial.C (lam ^ j) * weightScaleAlgEquiv h (MvPolynomial.pderiv ((), j) p)
              * (MvPolynomial.C (lam ^ n.2) * MvPolynomial.X n)
            + weightScaleAlgEquiv h p * (MvPolynomial.C (lam ^ n.2) * d) := by
        rw [map_mul, hX, hleibL, hleibC, hp]
        ring
      rw [hLHSexp, hRHSexp]
      linear_combination (weightScaleAlgEquiv h p) * hkey

/-- **The weighted action twists a coordinate partial by the weight of that coordinate.** -/
theorem weightScale_pd {lam : C} (h : lam ≠ 0) (j : ℕ) (v : JetField C Unit) :
    JetField.pd ((), j) (weightScale h v)
      = algebraMap C (JetField C Unit) (lam ^ j) * weightScale h (JetField.pd ((), j) v) := by
  have hquot : ∀ x y : JetField C Unit, y ≠ 0 →
      JetField.pd ((), j) (x / y)
        = (JetField.pd ((), j) x * y - x * JetField.pd ((), j) y) / y ^ (2 : ℕ) := by
    intro x y hy
    have hl := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz (x / y) y
    simp only [smul_eq_mul] at hl
    rw [div_mul_cancel₀ x hy] at hl
    have h3 : JetField.pd ((), j) (x / y)
        = (JetField.pd ((), j) x - (x / y) * JetField.pd ((), j) y) / y := by
      rw [eq_div_iff hy, hl]
      ring
    rw [h3]
    field_simp
  have hpoly : ∀ a : JetPoly C Unit,
      JetField.pd ((), j) (weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) a))
        = algebraMap C (JetField C Unit) (lam ^ j)
          * weightScale h (JetField.pd ((), j)
            (algebraMap (JetPoly C Unit) (JetField C Unit) a)) := by
    intro a
    rw [weightScale_algebraMap, JetField.pd_algebraMap, JetField.pd_algebraMap, weightScale_algebraMap,
      weightScaleAlgEquiv_pderiv, map_mul]
    rfl
  obtain ⟨a, b, hbmem, hab⟩ := IsFractionRing.div_surjective (A := JetPoly C Unit) v
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hbmem
  have hbne : algebraMap (JetPoly C Unit) (JetField C Unit) b ≠ 0 := fun hh =>
    hb ((IsFractionRing.injective (JetPoly C Unit) (JetField C Unit)) (by rw [hh, map_zero]))
  have hwb : weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b) ≠ 0 := by
    intro hh
    exact hbne ((weightScale h).injective
      (a₁ := algebraMap (JetPoly C Unit) (JetField C Unit) b) (a₂ := 0) (by rw [hh, map_zero]))
  have hLHS : JetField.pd ((), j) (weightScale h
      (algebraMap (JetPoly C Unit) (JetField C Unit) a
        / algebraMap (JetPoly C Unit) (JetField C Unit) b))
      = (JetField.pd ((), j) (weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) a))
            * weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)
          - weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) a)
            * JetField.pd ((), j)
              (weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)))
        / (weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)) ^ (2 : ℕ) := by
    rw [map_div₀]
    exact hquot _ _ hwb
  have hRHS : weightScale h (JetField.pd ((), j)
      (algebraMap (JetPoly C Unit) (JetField C Unit) a
        / algebraMap (JetPoly C Unit) (JetField C Unit) b))
      = (weightScale h (JetField.pd ((), j)
              (algebraMap (JetPoly C Unit) (JetField C Unit) a))
            * weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)
          - weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) a)
            * weightScale h (JetField.pd ((), j)
              (algebraMap (JetPoly C Unit) (JetField C Unit) b)))
        / (weightScale h (algebraMap (JetPoly C Unit) (JetField C Unit) b)) ^ (2 : ℕ) := by
    rw [hquot _ _ hbne, map_div₀, map_sub, map_mul, map_mul, map_pow]
  rw [← hab, hLHS, hRHS, hpoly a, hpoly b]
  field_simp

end

end GaloisForLFunctions.HTGeometry
