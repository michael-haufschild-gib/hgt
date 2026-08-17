import GaloisForLFunctions.HTGeometry.JetAffineConnectionLevelTwo

/-!
# The shift term is affine in the top jet coordinate

At jet level `M ≥ 3` the substitution acts on the top coordinate `y_M` by `y_M ↦ R'·y_M + σ_M`, and
the remainder `σ_M` is itself *affine* in the coordinate `y_{M−1}` below it:

`σ_M = A · y_{M−1} + B`,   `A`, `B` of order below `M − 1`.

This is the presentation a descent of the normalizing shift needs, because it is what makes the
shift equation, after slicing in `y_{M−1}`, an identity between polynomials over the prefix field.

The proof is the commutator `[∂_{m+1}, δ] = ∂_m` of a coordinate partial with the ambient
derivation.  Writing `σ_M = δ(σ_{M−1}) + δ(R')·y_{M−1}` implicitly, the commutator gives
`∂_{M−1}σ_M = δ(R') + ∂_{M−2}(δ^{M−1}R)`, whose own top partial vanishes because `R'` has order
zero and the partials commute.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- **The commutator of a coordinate partial with the ambient derivation**, applied to an
element. -/
theorem pd_jetDerivation_apply (m : ℕ) (v : JetField C Unit) :
    JetField.pd ((), m + 1) (JetField.jetDerivation v)
      = JetField.jetDerivation (JetField.pd ((), m + 1) v) + JetField.pd ((), m) v := by
  have h := JetField.commutator_pd_succ (C := C) (ι := Unit) () m
  have happ := congrArg
    (fun D : Derivation C (JetField C Unit) (JetField C Unit) => D v) h
  simp only [Derivation.commutator_apply] at happ
  rw [← happ]
  ring

omit [CharZero C] in
theorem substitutionJet_succ (R : RatFunc C) (l : ℕ) :
    substitutionJet R (l + 1) = JetField.jetDerivation (substitutionJet R l) := by
  rw [substitutionJet, substitutionJet, differentialJet_succ, JetField.deriv_eq]

/-- The partial of the derivative factor in any positive coordinate vanishes, so the ambient
derivation of the derivative factor has order one. -/
theorem pd_jetDerivation_substitutionDeriv (R : RatFunc C) {j : ℕ} (hj : 2 ≤ j) :
    JetField.pd ((), j) (JetField.jetDerivation (substitutionDeriv R)) = 0 := by
  have hexp : JetField.jetDerivation (substitutionDeriv R)
      = JetField.jet ((), 1) * JetField.pd ((), 0) (substitutionDeriv R) :=
    jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)
  have hleib := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (JetField.jet ((), 1) : JetField C Unit) (JetField.pd ((), 0) (substitutionDeriv R))
  simp only [smul_eq_mul] at hleib
  have h1 : JetField.pd ((), j) (JetField.jet ((), 1) : JetField C Unit) = 0 :=
    JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
  have h2 : JetField.pd ((), j) (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
    rw [pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
  rw [hexp, hleib, h1, h2, mul_zero, mul_zero, add_zero]

/-! ## The top partial of the shift -/

omit [CharZero C] in
/-- **The top partial of the shift at level `N + 3`.** -/
theorem pd_top_substitutionShift (R : RatFunc C) (N : ℕ) :
    JetField.pd ((), N + 2) (substitutionShift R (N + 3))
      = JetField.jetDerivation (substitutionDeriv R)
        + JetField.pd ((), N + 1) (substitutionJet R (N + 2)) := by
  have hleib := (JetField.pd ((), N + 2) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionDeriv R) (JetField.jet ((), N + 3) : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  have h1 : JetField.pd ((), N + 2) (JetField.jet ((), N + 3) : JetField C Unit) = 0 :=
    JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
  have h2 : JetField.pd ((), N + 2) (substitutionDeriv R) = 0 :=
    pd_substitutionDeriv_eq_zero R (by omega)
  have hprod : JetField.pd ((), N + 2)
      (substitutionDeriv R * (JetField.jet ((), N + 3) : JetField C Unit)) = 0 := by
    rw [hleib, h1, h2, mul_zero, mul_zero, add_zero]
  have hjet : JetField.pd ((), N + 2) (substitutionJet R (N + 3))
      = JetField.jetDerivation (substitutionDeriv R)
        + JetField.pd ((), N + 1) (substitutionJet R (N + 2)) := by
    rw [substitutionJet_succ R (N + 2), pd_jetDerivation_apply, pd_substitutionJet_self]
  rw [substitutionShift, map_sub, hprod, hjet, sub_zero]

/-- The top partial of the shift has order below the top coordinate. -/
theorem pd_top_substitutionShift_mem (R : RatFunc C) (N : ℕ) :
    JetField.pd ((), N + 2) (substitutionShift R (N + 3)) ∈ jetPrefixField C (N + 2) := by
  rw [mem_jetPrefixField_iff]
  intro j hj
  rw [pd_top_substitutionShift, map_add, pd_jetDerivation_substitutionDeriv R (by omega)]
  have hcomm : JetField.pd ((), j)
      (JetField.pd ((), N + 1) (substitutionJet R (N + 2)))
      = JetField.pd ((), N + 1) (JetField.pd ((), j) (substitutionJet R (N + 2))) :=
    pd_comm _ _ _
  rw [hcomm]
  rcases eq_or_lt_of_le hj with heq | hlt
  · rw [← heq, pd_substitutionJet_self, pd_substitutionDeriv_eq_zero R (by omega), zero_add]
  · rw [pd_substitutionJet_eq_zero_of_lt R (by omega), map_zero, zero_add]

/-- The constant part of the shift has order below the top coordinate. -/
theorem substitutionShift_sub_top_mem (R : RatFunc C) (N : ℕ) :
    substitutionShift R (N + 3)
        - JetField.pd ((), N + 2) (substitutionShift R (N + 3))
          * (JetField.jet ((), N + 2) : JetField C Unit)
      ∈ jetPrefixField C (N + 2) := by
  rw [mem_jetPrefixField_iff]
  intro j hj
  have hA : JetField.pd ((), N + 2) (substitutionShift R (N + 3)) ∈ jetPrefixField C (N + 2) :=
    pd_top_substitutionShift_mem R N
  have hleib := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (JetField.pd ((), N + 2) (substitutionShift R (N + 3)))
      (JetField.jet ((), N + 2) : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  rw [map_sub, hleib]
  rcases eq_or_lt_of_le hj with heq | hlt
  · have hAj : JetField.pd ((), j)
        (JetField.pd ((), N + 2) (substitutionShift R (N + 3))) = 0 :=
      (mem_jetPrefixField_iff (N + 2) _).mp hA j hj
    have hjet : JetField.pd ((), j) (JetField.jet ((), N + 2) : JetField C Unit) = 1 := by
      rw [← heq]
      exact JetField.pd_jet_self _
    rw [hAj, hjet, mul_one, mul_zero, add_zero, ← heq, sub_self]
  · have hAj : JetField.pd ((), j)
        (JetField.pd ((), N + 2) (substitutionShift R (N + 3))) = 0 :=
      (mem_jetPrefixField_iff (N + 2) _).mp hA j hj
    have hjet : JetField.pd ((), j) (JetField.jet ((), N + 2) : JetField C Unit) = 0 :=
      JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
    have hσ : JetField.pd ((), j) (substitutionShift R (N + 3)) = 0 :=
      (mem_jetPrefixField_iff (N + 3) _).mp
        (substitutionShift_mem_jetPrefixField R (by omega)) j (by omega)
    rw [hAj, hjet, mul_zero, mul_zero, add_zero, hσ, sub_zero]

/-- **The shift term is affine in the top jet coordinate below it.** -/
theorem exists_affine_substitutionShift (R : RatFunc C) (N : ℕ) :
    ∃ A B : ↥(jetPrefixField C (N + 2)),
      substitutionShift R (N + 3)
        = (A : JetField C Unit) * (JetField.jet ((), N + 2) : JetField C Unit)
          + (B : JetField C Unit) := by
  refine ⟨⟨JetField.pd ((), N + 2) (substitutionShift R (N + 3)),
      pd_top_substitutionShift_mem R N⟩,
    ⟨substitutionShift R (N + 3)
        - JetField.pd ((), N + 2) (substitutionShift R (N + 3))
          * (JetField.jet ((), N + 2) : JetField C Unit),
      substitutionShift_sub_top_mem R N⟩, ?_⟩
  show substitutionShift R (N + 3)
      = JetField.pd ((), N + 2) (substitutionShift R (N + 3))
          * (JetField.jet ((), N + 2) : JetField C Unit)
        + (substitutionShift R (N + 3)
          - JetField.pd ((), N + 2) (substitutionShift R (N + 3))
            * (JetField.jet ((), N + 2) : JetField C Unit))
  ring

end

end GaloisForLFunctions.HTGeometry
