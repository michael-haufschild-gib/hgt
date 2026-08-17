import GaloisForLFunctions.HTGeometry.JetShiftPolynomialBranch
import GaloisForLFunctions.HTGeometry.QuadraticOrbifoldTail

/-!
# The linear coefficient of the shift term

The shift term of the substitution at jet level `M` is affine in the coordinate below the top, and
its linear coefficient is completely explicit:

`∂_{M−1} σ_M = M · R''(y₀) · y₁`.

The induction starts from `σ₂ = R''·y₁²` and runs on the recursion `∂_{M−1}σ_M = δ(R') +
∂_{M−2}σ_{M−1}`, itself a consequence of the commutator of a coordinate partial with the ambient
derivation.  In characteristic zero the coefficient is therefore nonzero as soon as `R''` is, which
is what turns the degree-zero branch of the descent into an outright contradiction.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
theorem jet_ne_zero (p : Unit × ℕ) : (JetField.jet p : JetField C Unit) ≠ 0 := by
  intro h
  have h1 : JetField.pd p (JetField.jet p : JetField C Unit) = 1 := JetField.pd_jet_self p
  rw [h, map_zero] at h1
  exact one_ne_zero h1.symm

/-- **The linear coefficient of the shift term.** -/
theorem pd_top_substitutionShift_eq (R : RatFunc C) : ∀ N : ℕ,
    JetField.pd ((), N + 1) (substitutionShift R (N + 2))
      = ((N + 2 : ℕ) : JetField C Unit)
        * (JetField.pd ((), 0) (substitutionDeriv R) * JetField.jet ((), 1)) := by
  intro N
  induction N with
  | zero =>
      have hleib := (JetField.pd ((), 1) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (JetField.pd ((), 0) (substitutionDeriv R))
          ((JetField.jet ((), 1) : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit))
      simp only [smul_eq_mul] at hleib
      have hsq := (JetField.pd ((), 1) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (JetField.jet ((), 1) : JetField C Unit) (JetField.jet ((), 1) : JetField C Unit)
      simp only [smul_eq_mul] at hsq
      have hself : JetField.pd ((), 1) (JetField.jet ((), 1) : JetField C Unit) = 1 :=
        JetField.pd_jet_self _
      have hzero : JetField.pd ((), 1) (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
        rw [pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
      have hshift : substitutionShift R 2
          = JetField.pd ((), 0) (substitutionDeriv R)
            * ((JetField.jet ((), 1) : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit))
            := by
        rw [substitutionShift_two]
        ring
      rw [hshift, hleib, hsq, hself, hzero]
      push_cast
      ring
  | succ N ih =>
      have haff := substitutionJet_eq_affine R (N + 2)
      have hleib := (JetField.pd ((), N + 1) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (substitutionDeriv R) (JetField.jet ((), N + 2) : JetField C Unit)
      simp only [smul_eq_mul] at hleib
      have h1 : JetField.pd ((), N + 1) (JetField.jet ((), N + 2) : JetField C Unit) = 0 :=
        JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
      have h2 : JetField.pd ((), N + 1) (substitutionDeriv R) = 0 :=
        pd_substitutionDeriv_eq_zero R (by omega)
      have hprod : JetField.pd ((), N + 1)
          (substitutionDeriv R * (JetField.jet ((), N + 2) : JetField C Unit)) = 0 := by
        rw [hleib, h1, h2, mul_zero, mul_zero, add_zero]
      have hjet : JetField.pd ((), N + 1) (substitutionJet R (N + 2))
          = JetField.pd ((), N + 1) (substitutionShift R (N + 2)) := by
        rw [haff, map_add, hprod, zero_add]
      have hderiv : JetField.jetDerivation (substitutionDeriv R)
          = JetField.jet ((), 1) * JetField.pd ((), 0) (substitutionDeriv R) :=
        jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)
      rw [pd_top_substitutionShift, hjet, ih, hderiv]
      push_cast
      ring

/-- The linear coefficient of the shift term is nonzero as soon as the second derivative is. -/
theorem pd_top_substitutionShift_ne_zero (R : RatFunc C) (N : ℕ)
    (h : JetField.pd ((), 0) (substitutionDeriv R) ≠ 0) :
    JetField.pd ((), N + 1) (substitutionShift R (N + 2)) ≠ 0 := by
  rw [pd_top_substitutionShift_eq]
  refine mul_ne_zero ?_ (mul_ne_zero h (jet_ne_zero _))
  have hcast : ((N + 2 : ℕ) : JetField C Unit) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact hcast

/-- The linear coefficient of an affine presentation of the shift is its top partial. -/
theorem coe_eq_pd_top_of_affine (R : RatFunc C) (N : ℕ)
    {A B : ↥(jetPrefixField C (N + 2))}
    (hAB : substitutionShift R (N + 3)
      = (A : JetField C Unit) * (JetField.jet ((), N + 2) : JetField C Unit)
        + (B : JetField C Unit)) :
    (A : JetField C Unit) = JetField.pd ((), N + 2) (substitutionShift R (N + 3)) := by
  have hA : JetField.pd ((), N + 2) (A : JetField C Unit) = 0 :=
    (mem_jetPrefixField_iff (N + 2) _).mp A.2 (N + 2) (le_refl _)
  have hB : JetField.pd ((), N + 2) (B : JetField C Unit) = 0 :=
    (mem_jetPrefixField_iff (N + 2) _).mp B.2 (N + 2) (le_refl _)
  have hleib := (JetField.pd ((), N + 2) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (A : JetField C Unit) (JetField.jet ((), N + 2) : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  have hself : JetField.pd ((), N + 2) (JetField.jet ((), N + 2) : JetField C Unit) = 1 :=
    JetField.pd_jet_self _
  rw [hAB, map_add, hleib, hself, hA, hB, mul_one, mul_zero, add_zero, add_zero]

/-! ## The two quadratic maps -/

theorem quadOne_pd_substitutionDeriv_ne_zero :
    JetField.pd ((), 0) (substitutionDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadOne))
      ≠ 0 := by
  rw [← substitutionDeriv_ratFuncDeriv, ratFuncDeriv_algebraMap]
  refine substitutionDeriv_algebraMap_ne_zero ?_
  rw [derivative_quadOne, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, mul_one, zero_add]
  intro hh
  have hc := congrArg (fun p => Polynomial.coeff p 0) hh
  simp at hc

theorem quadTwo_pd_substitutionDeriv_ne_zero :
    JetField.pd ((), 0) (substitutionDeriv (algebraMap (Polynomial ℂ) (RatFunc ℂ) quadTwo))
      ≠ 0 := by
  rw [← substitutionDeriv_ratFuncDeriv, ratFuncDeriv_algebraMap]
  refine substitutionDeriv_algebraMap_ne_zero ?_
  rw [derivative_quadTwo, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
    zero_mul, mul_one, zero_add]
  intro hh
  have hc := congrArg (fun p => Polynomial.coeff p 0) hh
  simp at hc

end

end GaloisForLFunctions.HTGeometry
