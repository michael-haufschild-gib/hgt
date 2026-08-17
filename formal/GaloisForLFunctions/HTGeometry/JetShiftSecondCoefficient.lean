import GaloisForLFunctions.HTGeometry.JetLevelThreeDescent

/-!
# The second coefficient of the shift term

The shift term at jet level `M` is affine in the coordinate below the top with coefficient
`M·R''·y₁`.  Two coordinates below the top the coefficient is again completely explicit:

`∂_{M−2}σ_M = (M(M−1)/2)·(R''·y₂ + R'''·y₁²)`.

The recursion is the same commutator of a coordinate partial with the ambient derivation that gives
the top coefficient: differentiating the top coefficient of one level lower adds
`(M−1)·(R''·y₂ + R'''·y₁²)`, and the base of the induction is `∂₁σ₃ = 3·(R''·y₂ + R'''·y₁²)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- The recursion for the coefficient two below the top. -/
theorem pd_second_substitutionShift (R : RatFunc C) (N : ℕ) :
    JetField.pd ((), N + 1) (substitutionShift R (N + 3))
      = JetField.jetDerivation (JetField.pd ((), N + 1) (substitutionJet R (N + 2)))
        + JetField.pd ((), N) (substitutionJet R (N + 2)) := by
  have hleib := (JetField.pd ((), N + 1) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionDeriv R) (JetField.jet ((), N + 3) : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  have h1 : JetField.pd ((), N + 1) (JetField.jet ((), N + 3) : JetField C Unit) = 0 :=
    JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
  have h2 : JetField.pd ((), N + 1) (substitutionDeriv R) = 0 :=
    pd_substitutionDeriv_eq_zero R (by omega)
  have hprod : JetField.pd ((), N + 1)
      (substitutionDeriv R * (JetField.jet ((), N + 3) : JetField C Unit)) = 0 := by
    rw [hleib, h1, h2, mul_zero, mul_zero, add_zero]
  have hjet : substitutionJet R (N + 3)
      = JetField.jetDerivation (substitutionJet R (N + 2)) := by
    rw [substitutionJet, substitutionJet, show N + 3 = (N + 2) + 1 from rfl, differentialJet_succ,
      JetField.deriv_eq]
  rw [substitutionShift, map_sub, hprod, sub_zero, hjet, pd_jetDerivation_apply]

/-- **The coefficient of the shift term two coordinates below the top.** -/
theorem pd_second_substitutionShift_eq (R : RatFunc C) : ∀ K : ℕ,
    2 * JetField.pd ((), K + 1) (substitutionShift R (K + 3))
      = ((K + 2 : ℕ) * (K + 3 : ℕ) : ℕ)
        * (JetField.pd ((), 0) (substitutionDeriv R) * (JetField.jet ((), 2) : JetField C Unit)
          + JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R))
            * (JetField.jet ((), 1) : JetField C Unit) ^ 2) := by
  intro K
  induction K with
  | zero =>
      have h3 := substitutionShift_three R
      set ρ₁ : JetField C Unit := JetField.pd ((), 0) (substitutionDeriv R) with hρ₁def
      set ρ₂ : JetField C Unit := JetField.pd ((), 0) ρ₁ with hρ₂def
      have hρ₁ : JetField.pd ((), 1) ρ₁ = 0 := by
        rw [hρ₁def, pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
      have hρ₂ : JetField.pd ((), 1) ρ₂ = 0 := by
        rw [hρ₂def, pd_comm, hρ₁, map_zero]
      have hy1 : JetField.pd ((), 1) (JetField.jet ((), 1) : JetField C Unit) = 1 :=
        JetField.pd_jet_self _
      have hy2 : JetField.pd ((), 1) (JetField.jet ((), 2) : JetField C Unit) = 0 :=
        JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
      have hcube : JetField.pd ((), 1) ((JetField.jet ((), 1) : JetField C Unit) ^ 3)
          = 3 * (JetField.jet ((), 1) : JetField C Unit) ^ 2 := by
        have hl := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
            (JetField.jet ((), 1) : JetField C Unit) 3
        simp only [smul_eq_mul, hy1, mul_one] at hl
        rw [hl]
        push_cast
        ring
      have hA : JetField.pd ((), 1)
          (3 * ρ₁ * (JetField.jet ((), 1) : JetField C Unit)
            * (JetField.jet ((), 2) : JetField C Unit))
          = 3 * ρ₁ * (JetField.jet ((), 2) : JetField C Unit) := by
        have hl1 := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (3 * ρ₁ * (JetField.jet ((), 1) : JetField C Unit))
            (JetField.jet ((), 2) : JetField C Unit)
        have hl2 := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (3 * ρ₁) (JetField.jet ((), 1) : JetField C Unit)
        have hl3 := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (3 : JetField C Unit) ρ₁
        simp only [smul_eq_mul] at hl1 hl2 hl3
        have h3z : JetField.pd ((), 1) (3 : JetField C Unit) = 0 := by
          rw [show (3 : JetField C Unit) = algebraMap C (JetField C Unit) 3 from by
            rw [map_ofNat], Derivation.map_algebraMap]
        rw [hl1, hy2, hl2, hl3, hρ₁, h3z, hy1]
        ring
      have hB : JetField.pd ((), 1) (ρ₂ * (JetField.jet ((), 1) : JetField C Unit) ^ 3)
          = 3 * ρ₂ * (JetField.jet ((), 1) : JetField C Unit) ^ 2 := by
        have hl := (JetField.pd ((), 1) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            ρ₂ ((JetField.jet ((), 1) : JetField C Unit) ^ 3)
        simp only [smul_eq_mul] at hl
        rw [hl, hcube, hρ₂]
        ring
      rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 3 = 3 from rfl, h3, map_add, hA, hB]
      push_cast
      ring
  | succ K ih =>
      set ρ₁ : JetField C Unit := JetField.pd ((), 0) (substitutionDeriv R) with hρ₁def
      set ρ₂ : JetField C Unit := JetField.pd ((), 0) ρ₁ with hρ₂def
      have hstep := pd_second_substitutionShift R (K + 1)
      have haff := substitutionJet_eq_affine R (K + 3)
      have hleib := (JetField.pd ((), K + 2) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (substitutionDeriv R) (JetField.jet ((), K + 3) : JetField C Unit)
      have hleib' := (JetField.pd ((), K + 1) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (substitutionDeriv R) (JetField.jet ((), K + 3) : JetField C Unit)
      simp only [smul_eq_mul] at hleib hleib'
      have hz1 : JetField.pd ((), K + 2)
          (substitutionDeriv R * (JetField.jet ((), K + 3) : JetField C Unit)) = 0 := by
        rw [hleib, JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega),
          pd_substitutionDeriv_eq_zero R (by omega), mul_zero, mul_zero, add_zero]
      have hz2 : JetField.pd ((), K + 1)
          (substitutionDeriv R * (JetField.jet ((), K + 3) : JetField C Unit)) = 0 := by
        rw [hleib', JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega),
          pd_substitutionDeriv_eq_zero R (by omega), mul_zero, mul_zero, add_zero]
      have htop : JetField.pd ((), K + 2) (substitutionJet R (K + 3))
          = ((K + 3 : ℕ) : JetField C Unit) * (ρ₁ * (JetField.jet ((), 1) : JetField C Unit)) := by
        rw [haff, map_add, hz1, zero_add, pd_top_substitutionShift_eq R (K + 1)]
      have hsecond : JetField.pd ((), K + 1) (substitutionJet R (K + 3))
          = JetField.pd ((), K + 1) (substitutionShift R (K + 3)) := by
        rw [haff, map_add, hz2, zero_add]
      have hδρ₁ : JetField.jetDerivation ρ₁
          = (JetField.jet ((), 1) : JetField C Unit) * ρ₂ := by
        refine jetDerivation_of_order_zero (fun k hk => ?_)
        rw [hρ₁def, pd_comm, pd_substitutionDeriv_eq_zero R hk, map_zero]
      have hδ1 : JetField.jetDerivation (JetField.jet ((), 1) : JetField C Unit)
          = JetField.jet ((), 2) := JetField.jetDerivation_jet ((), 1)
      have hδtop : JetField.jetDerivation (JetField.pd ((), K + 2) (substitutionJet R (K + 3)))
          = ((K + 3 : ℕ) : JetField C Unit)
            * (ρ₂ * (JetField.jet ((), 1) : JetField C Unit) ^ 2
              + ρ₁ * (JetField.jet ((), 2) : JetField C Unit)) := by
        rw [htop]
        have hl1 := (JetField.jetDerivation :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            (((K + 3 : ℕ) : JetField C Unit)) (ρ₁ * (JetField.jet ((), 1) : JetField C Unit))
        have hl2 := (JetField.jetDerivation :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz
            ρ₁ (JetField.jet ((), 1) : JetField C Unit)
        simp only [smul_eq_mul] at hl1 hl2
        have hnat : JetField.jetDerivation (((K + 3 : ℕ) : JetField C Unit)) = 0 := by
          rw [show (((K + 3 : ℕ)) : JetField C Unit)
            = algebraMap C (JetField C Unit) ((K + 3 : ℕ) : C) from by rw [map_natCast],
            Derivation.map_algebraMap]
        rw [hl1, hl2, hnat, hδρ₁, hδ1]
        ring
      rw [show K + 1 + 1 = K + 2 from rfl, show K + 1 + 3 = (K + 1) + 3 from rfl, hstep, hδtop,
        hsecond]
      rw [show (K + 1) + 1 = K + 2 from rfl] at ih
      push_cast at ih ⊢
      linear_combination ih

end

end GaloisForLFunctions.HTGeometry
