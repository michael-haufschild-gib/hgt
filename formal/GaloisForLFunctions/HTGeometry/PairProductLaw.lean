import GaloisForLFunctions.HTGeometry.PeelInduction

/-!
# The two-coordinate product law

A first-order equation solved polynomially for the derivative, `f' = p(z, f)`, makes the cascade
states obey

`δ X_k = ∏_(j<k) p_j(X_j, X_(j+1))`,

a product law whose factors involve **two consecutive coordinates** rather than one.  This is the
shape a general first-order cascade has — the univariate law of a polynomial-coefficient cascade
arises only because `p_j` there factors as `A_j'(X_j)·(X_(j+1) − d_j)`, letting the second piece be
absorbed into the next univariate factor.

The three response laws that carry the whole peel survive the change: a jet below the coordinate
does not respond, the jet at the coordinate responds by its own logarithmic derivative, and jets
above respond by a single logarithmic factor — now the sum of two terms, because the coordinate
occurs in two consecutive factors.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## Two-coordinate factors -/

/-- A two-variable polynomial placed at the consecutive coordinates `j`, `j+1`. -/
noncomputable def pairPoly (p : MvPolynomial (Fin 2) ℂ) (j : ℕ) : MvPolynomial ℕ ℂ :=
  MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.X (j + (i : ℕ))) p

/-- Its image in the rational model. -/
noncomputable def pairFactor (p : MvPolynomial (Fin 2) ℂ) (j : ℕ) : CascadeField :=
  algebraMap (MvPolynomial ℕ ℂ) CascadeField (pairPoly p j)

theorem pairPoly_C (a : ℂ) (j : ℕ) : pairPoly (MvPolynomial.C a) j = MvPolynomial.C a := by
  rw [pairPoly, MvPolynomial.aeval_C]
  rfl

theorem pairPoly_add (p q : MvPolynomial (Fin 2) ℂ) (j : ℕ) :
    pairPoly (p + q) j = pairPoly p j + pairPoly q j := by
  rw [pairPoly, pairPoly, pairPoly, map_add]

theorem pairPoly_mul_X (p : MvPolynomial (Fin 2) ℂ) (i : Fin 2) (j : ℕ) :
    pairPoly (p * MvPolynomial.X i) j = pairPoly p j * MvPolynomial.X (j + (i : ℕ)) := by
  rw [pairPoly, pairPoly, map_mul, MvPolynomial.aeval_X]

/-- **A two-coordinate factor is invisible to every other coordinate.** -/
theorem pderiv_pairPoly_of_ne {k j : ℕ} (h0 : k ≠ j) (h1 : k ≠ j + 1)
    (p : MvPolynomial (Fin 2) ℂ) : MvPolynomial.pderiv k (pairPoly p j) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [pairPoly_C]
      simp
  | add p q hp hq =>
      rw [pairPoly_add, map_add, hp, hq, add_zero]
  | mul_X q i hq =>
      rw [pairPoly_mul_X, Derivation.leibniz, hq]
      have hX : MvPolynomial.pderiv k (MvPolynomial.X (j + (i : ℕ)) : MvPolynomial ℕ ℂ) = 0 := by
        refine MvPolynomial.pderiv_X_of_ne ?_
        have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
        rcases hi with hi | hi <;> rw [hi] <;> omega
      rw [hX]
      simp

theorem fpderiv_pairFactor_of_ne {k j : ℕ} (h0 : k ≠ j) (h1 : k ≠ j + 1)
    (p : MvPolynomial (Fin 2) ℂ) : fpderiv k (pairFactor p j) = 0 := by
  rw [pairFactor, fpderiv_algebraMap, pderiv_pairPoly_of_ne h0 h1, map_zero]

/-! ## The jet of a two-coordinate product law -/

/-- The jet of the `k`-th coordinate: the product of the factors below it. -/
noncomputable def pairJet (p : ℕ → MvPolynomial (Fin 2) ℂ) (k : ℕ) : CascadeField :=
  ∏ j ∈ Finset.range k, pairFactor (p j) j

@[simp] theorem pairJet_zero (p : ℕ → MvPolynomial (Fin 2) ℂ) : pairJet p 0 = 1 := by
  simp [pairJet]

theorem pairJet_succ (p : ℕ → MvPolynomial (Fin 2) ℂ) (k : ℕ) :
    pairJet p (k + 1) = pairJet p k * pairFactor (p k) k := by
  rw [pairJet, pairJet, Finset.prod_range_succ]

theorem pairJet_ne_zero {p : ℕ → MvPolynomial (Fin 2) ℂ}
    (hne : ∀ j, pairFactor (p j) j ≠ 0) (k : ℕ) : pairJet p k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => hne j

/-! ## The three response laws -/

/-- **A jet strictly below the coordinate does not respond.** -/
theorem fpderiv_pairJet_of_gt (p : ℕ → MvPolynomial (Fin 2) ℂ) {k : ℕ} :
    ∀ {l : ℕ}, l < k → fpderiv k (pairJet p l) = 0 := by
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ih =>
      intro h
      rw [pairJet_succ, Derivation.leibniz, ih (by omega),
        fpderiv_pairFactor_of_ne (by omega) (by omega)]
      simp

/-- The logarithmic factor of the law at a coordinate: the coordinate occurs in the jet below it and
in the factor at it, so its response has two terms. -/
noncomputable def pairLog (p : ℕ → MvPolynomial (Fin 2) ℂ) (k : ℕ) : CascadeField :=
  fpderiv k (pairJet p k) / pairJet p k
    + fpderiv k (pairFactor (p k) k) / pairFactor (p k) k

/-- **Jets above the coordinate respond by the logarithmic factor.** -/
theorem fpderiv_pairJet_of_lt {p : ℕ → MvPolynomial (Fin 2) ℂ}
    (hne : ∀ j, pairFactor (p j) j ≠ 0) {k : ℕ} :
    ∀ {l : ℕ}, k < l → fpderiv k (pairJet p l) = pairLog p k * pairJet p l := by
  intro l
  induction l with
  | zero => intro h; omega
  | succ l ih =>
      intro h
      rcases Nat.lt_or_ge k l with hkl | hkl
      · rw [pairJet_succ, Derivation.leibniz, ih hkl,
          fpderiv_pairFactor_of_ne (by omega) (by omega)]
        simp only [smul_eq_mul, mul_zero]
        ring
      · have hkeq : k = l := by omega
        subst hkeq
        rw [pairJet_succ, Derivation.leibniz, pairLog]
        have hj : pairJet p k ≠ 0 := pairJet_ne_zero hne k
        have hf : pairFactor (p k) k ≠ 0 := hne k
        field_simp
        ring

end GaloisForLFunctions.HTGeometry
