import GaloisForLFunctions.HTGeometry.JetShiftAffinePresentation

/-!
# Descending a normalizing shift one jet level

At jet level `M = N + 3` the substitution acts on the coordinate `y_{N+2}` below the top by the
affine polynomial `T = R'·X + σ_{N+2}`, and the shift term `σ_{N+3}` is affine in `y_{N+2}`.  So a
normalizing shift at level `N + 3`, sliced as a coprime fraction in `y_{N+2}`, gives an identity
between polynomials over the prefix field, and the denominator divides its own twisted image.

Degrees are preserved by a twisted affine substitution, so the denominator is a scalar eigenvector.
If its degree is positive, the affine cocycle of its two top coefficients is a normalizing shift one
level down.  Otherwise the shift is a *polynomial* in `y_{N+2}`, and what is left is the coefficient
analysis of

`Φ̃(u) = R'·u − (A·X + B)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **One level of the descent.**  A normalizing shift at jet level `N + 3` either produces a
normalizing shift at level `N + 2`, or is a polynomial in the coordinate `y_{N+2}` satisfying the
affine shift equation over the prefix field. -/
theorem hasNormalizingShift_pred_or_polynomial (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (N : ℕ) (h : HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 3 by omega)) :
    HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 2 by omega)
      ∨ ∃ (u : Polynomial ↥(jetPrefixField C (N + 2))) (A B : ↥(jetPrefixField C (N + 2))),
          substitutionShift R (N + 3)
              = (A : JetField C Unit) * (JetField.jet ((), N + 2) : JetField C Unit)
                + (B : JetField C Unit) ∧
            twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
                (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
              = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
                - (Polynomial.C A * Polynomial.X + Polynomial.C B) := by
  classical
  obtain ⟨t, ht⟩ := h
  set hM2 : (1 : ℕ) ≤ N + 2 := by omega
  set x : JetField C Unit := JetField.jet ((), N + 2) with hxdef
  have hxtr : Transcendental (jetPrefixField C (N + 2)) x :=
    transcendental_jet_over_jetPrefixField (N + 2)
  have hinj : Function.Injective (Polynomial.aeval (R := ↥(jetPrefixField C (N + 2))) x) :=
    transcendental_iff_injective.mp hxtr
  set Φ : ↥(jetPrefixField C (N + 2)) →+* ↥(jetPrefixField C (N + 2)) :=
    (jetSubstitutionPrefix R hR (N + 2)).toRingHom with hΦdef
  set ρF : ↥(jetPrefixField C (N + 2)) := substitutionDerivPrefix R hM2 with hρFdef
  have hρF : ρF ≠ 0 := substitutionDerivPrefix_ne_zero R hR hM2
  have hρval : (algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)) ρF
      = substitutionDeriv R := rfl
  set T : Polynomial ↥(jetPrefixField C (N + 2)) := substitutionAffine R hM2 with hTdef
  have hT : T.natDegree = 1 := natDegree_substitutionAffine R hR hM2
  -- the affine presentation of the shift term
  obtain ⟨A, B, hAB⟩ := exists_affine_substitutionShift R N
  set S : Polynomial ↥(jetPrefixField C (N + 2)) :=
    Polynomial.C A * Polynomial.X + Polynomial.C B with hSdef
  have hSeval : Polynomial.aeval x S = substitutionShift R (N + 3) := by
    rw [hSdef, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X, hAB]
    rfl
  -- the shift equation on the jet field
  have htJ : jetSubstitution R hR (t : JetField C Unit)
      = substitutionDeriv R * (t : JetField C Unit) - substitutionShift R (N + 3) := by
    have hc := congrArg (fun z : ↥(jetPrefixField C (N + 3)) =>
      (algebraMap ↥(jetPrefixField C (N + 3)) (JetField C Unit) z)) ht
    simp only [map_sub, map_mul] at hc
    rw [← jetSubstitution_algebraMap_prefix] at hc
    exact hc
  have hord : ∀ j : ℕ, N + 2 < j → JetField.pd ((), j) (t : JetField C Unit) = 0 := by
    intro j hj
    exact (mem_jetPrefixField_iff (N + 3) (t : JetField C Unit)).mp t.2 j (by omega)
  have hmemadj : (t : JetField C Unit) ∈ IntermediateField.adjoin (jetPrefixField C (N + 2))
      ({x} : Set (JetField C Unit)) := mem_adjoin_jet_of_order hord
  -- the substitution acts on the coordinate by the affine polynomial
  have hact : jetSubstitution R hR x = Polynomial.aeval x T := by
    rw [hxdef, jetSubstitution_jet, hTdef, aeval_substitutionAffine]
  -- slice
  set f : RatFunc ↥(jetPrefixField C (N + 2)) :=
    (RatFunc.algEquivOfTranscendental x hxtr).symm ⟨(t : JetField C Unit), hmemadj⟩ with hfdef
  have hxeval : ratFuncEval x hxtr f = (t : JetField C Unit) := by
    simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hfdef,
      AlgEquiv.apply_symm_apply]
    rfl
  set P : Polynomial ↥(jetPrefixField C (N + 2)) := f.num with hPdef
  set Q : Polynomial ↥(jetPrefixField C (N + 2)) := f.denom with hQdef
  have hQ0 : Q ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime P Q := RatFunc.isCoprime_num_denom f
  have hQy : Polynomial.aeval x Q ≠ 0 := fun hh => hQ0 (hinj (by simpa using hh))
  have htdiv : (t : JetField C Unit) = Polynomial.aeval x P / Polynomial.aeval x Q := by
    rw [← hxeval, ratFuncEval_eq_div]
  have hΦQ0 : twistComp Φ T Q ≠ 0 := twistComp_ne_zero Φ hT hQ0
  have hΦQy : Polynomial.aeval x (twistComp Φ T Q) ≠ 0 :=
    fun hh => hΦQ0 (hinj (by simpa using hh))
  have hLHS : jetSubstitution R hR (t : JetField C Unit)
      = Polynomial.aeval x (twistComp Φ T P) / Polynomial.aeval x (twistComp Φ T Q) := by
    rw [htdiv, map_div₀, jetSubstitution_aeval_of_act R hR hact,
      jetSubstitution_aeval_of_act R hR hact]
  rw [hLHS, htdiv, ← hSeval, ← hρval] at htJ
  have hcrossJ : Polynomial.aeval x (twistComp Φ T P * Q)
      = Polynomial.aeval x (twistComp Φ T Q * (Polynomial.C ρF * P - S * Q)) := by
    simp only [map_mul, map_sub, Polynomial.aeval_C]
    field_simp at htJ
    linear_combination htJ
  have hcross := hinj hcrossJ
  -- the denominator is a scalar eigenvector
  have hcopΦ : IsCoprime (twistComp Φ T P) (twistComp Φ T Q) := by
    obtain ⟨v, w, hvw⟩ := hcop
    refine ⟨twistComp Φ T v, twistComp Φ T w, ?_⟩
    rw [← twistComp_mul, ← twistComp_mul, ← twistComp_add, hvw]
    rw [show (1 : Polynomial ↥(jetPrefixField C (N + 2))) = Polynomial.C 1 from by rw [map_one],
      twistComp_C, map_one, map_one]
  have hdvd : twistComp Φ T Q ∣ Q := hcopΦ.symm.dvd_of_dvd_mul_left ⟨_, hcross⟩
  obtain ⟨e', he'0, he'⟩ := eq_C_mul_of_dvd_of_natDegree_eq hQ0 hdvd
    (natDegree_twistComp Φ hT Q).symm
  have hdQ : twistComp Φ T Q = Polynomial.C e'⁻¹ * Q := by
    conv_rhs => rw [he']
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ he'0, map_one, one_mul]
  -- the two branches
  by_cases hdeg : 1 ≤ Q.natDegree
  · exact Or.inl (exists_normalizing_shift R hR hM2 hdeg (by rw [← hTdef]; exact hdQ))
  · refine Or.inr ⟨Polynomial.C (Q.coeff 0)⁻¹ * P, A, B, hAB, ?_⟩
    rw [← hSdef]
    have hQC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hq0 : Q.coeff 0 ≠ 0 := fun hh => hQ0 (by rw [hQC, hh, map_zero])
    have hΦq0 : Φ (Q.coeff 0) ≠ 0 := fun hh => hq0 ((map_eq_zero_iff Φ Φ.injective).mp hh)
    have hCq0 : (Polynomial.C (Q.coeff 0) : Polynomial ↥(jetPrefixField C (N + 2))) ≠ 0 := by
      intro hh
      exact hq0 (by simpa using hh)
    have hTQ : twistComp Φ T Q = Polynomial.C (Φ (Q.coeff 0)) := by
      conv_lhs => rw [hQC]
      rw [twistComp_C]
    have hcross' : twistComp Φ T P * Polynomial.C (Q.coeff 0)
        = Polynomial.C (Φ (Q.coeff 0))
          * (Polynomial.C ρF * P - S * Polynomial.C (Q.coeff 0)) := by
      calc twistComp Φ T P * Polynomial.C (Q.coeff 0)
          = twistComp Φ T P * Q := by rw [← hQC]
        _ = twistComp Φ T Q * (Polynomial.C ρF * P - S * Q) := hcross
        _ = Polynomial.C (Φ (Q.coeff 0))
              * (Polynomial.C ρF * P - S * Polynomial.C (Q.coeff 0)) := by
            rw [hTQ, ← hQC]
    rw [twistComp_mul, twistComp_C, map_inv₀]
    refine mul_right_cancel₀ hCq0 ?_
    calc Polynomial.C (Φ (Q.coeff 0))⁻¹ * twistComp Φ T P * Polynomial.C (Q.coeff 0)
        = Polynomial.C (Φ (Q.coeff 0))⁻¹
            * (twistComp Φ T P * Polynomial.C (Q.coeff 0)) := by ring
      _ = Polynomial.C (Φ (Q.coeff 0))⁻¹ * (Polynomial.C (Φ (Q.coeff 0))
            * (Polynomial.C ρF * P - S * Polynomial.C (Q.coeff 0))) := by rw [hcross']
      _ = Polynomial.C ρF * P - S * Polynomial.C (Q.coeff 0) := by
          rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hΦq0, map_one, one_mul]
      _ = (Polynomial.C ρF * (Polynomial.C (Q.coeff 0)⁻¹ * P) - S)
            * Polynomial.C (Q.coeff 0) := by
          rw [sub_mul]
          congr 1
          rw [mul_assoc, mul_comm (Polynomial.C (Q.coeff 0)⁻¹ * P) (Polynomial.C (Q.coeff 0)),
            ← mul_assoc (Polynomial.C (Q.coeff 0)) (Polynomial.C (Q.coeff 0)⁻¹) P,
            ← Polynomial.C_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end

end GaloisForLFunctions.HTGeometry
