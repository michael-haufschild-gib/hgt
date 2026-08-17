import GaloisForLFunctions.HTGeometry.JetNormalizingShiftDescent

/-!
# Slicing an inhomogeneous relation in the top coordinate

The descent of a normalizing shift uses only two features of the shift term: that it is a polynomial
in the coordinate `y_{N+2}` over the field of lower order, and that the substitution acts on that
coordinate by an affine polynomial with coefficients of lower order.  So the whole argument runs for
an *arbitrary* inhomogeneous polynomial:

`Φ(v) = R'·v − S(y_{N+2})`

with `v` of order at most `N + 2`.  Slicing `v` as a coprime fraction, the denominator divides its
own twisted image and has the same degree, hence is a scalar eigenvector; if its degree is positive
the affine cocycle of its two top coefficients is a normalizing shift at level `N + 2`, and otherwise
`v` is itself a polynomial in the coordinate satisfying the same relation.

This is the form the descent needs above jet level three, where the inhomogeneous term produced by
one level is no longer the shift term of the next.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **The slicing of an inhomogeneous relation in the top coordinate.** -/
theorem hasNormalizingShift_or_polynomial_of_relation (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0) (N : ℕ) {v : JetField C Unit}
    (hv : ∀ j : ℕ, N + 2 < j → JetField.pd ((), j) v = 0)
    (S : Polynomial ↥(jetPrefixField C (N + 2)))
    (heq : jetSubstitution R hR v
      = substitutionDeriv R * v
        - Polynomial.aeval (JetField.jet ((), N + 2) : JetField C Unit) S) :
    HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 2 by omega)
      ∨ ∃ u : Polynomial ↥(jetPrefixField C (N + 2)),
          v = Polynomial.aeval (JetField.jet ((), N + 2) : JetField C Unit) u ∧
            twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
                (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
              = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
                - S := by
  classical
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
  have hmemadj : v ∈ IntermediateField.adjoin (jetPrefixField C (N + 2))
      ({x} : Set (JetField C Unit)) := mem_adjoin_jet_of_order hv
  have hact : jetSubstitution R hR x = Polynomial.aeval x T := by
    rw [hxdef, jetSubstitution_jet, hTdef, aeval_substitutionAffine]
  set f : RatFunc ↥(jetPrefixField C (N + 2)) :=
    (RatFunc.algEquivOfTranscendental x hxtr).symm ⟨v, hmemadj⟩ with hfdef
  have hxeval : ratFuncEval x hxtr f = v := by
    simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hfdef,
      AlgEquiv.apply_symm_apply]
    rfl
  set P : Polynomial ↥(jetPrefixField C (N + 2)) := f.num with hPdef
  set Q : Polynomial ↥(jetPrefixField C (N + 2)) := f.denom with hQdef
  have hQ0 : Q ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime P Q := RatFunc.isCoprime_num_denom f
  have hQy : Polynomial.aeval x Q ≠ 0 := fun hh => hQ0 (hinj (by simpa using hh))
  have hvdiv : v = Polynomial.aeval x P / Polynomial.aeval x Q := by
    rw [← hxeval, ratFuncEval_eq_div]
  have hΦQ0 : twistComp Φ T Q ≠ 0 := twistComp_ne_zero Φ hT hQ0
  have hΦQy : Polynomial.aeval x (twistComp Φ T Q) ≠ 0 :=
    fun hh => hΦQ0 (hinj (by simpa using hh))
  have hLHS : jetSubstitution R hR v
      = Polynomial.aeval x (twistComp Φ T P) / Polynomial.aeval x (twistComp Φ T Q) := by
    rw [hvdiv, map_div₀, jetSubstitution_aeval_of_act R hR hact,
      jetSubstitution_aeval_of_act R hR hact]
  rw [hLHS, hvdiv, ← hρval] at heq
  have hcrossJ : Polynomial.aeval x (twistComp Φ T P * Q)
      = Polynomial.aeval x (twistComp Φ T Q * (Polynomial.C ρF * P - S * Q)) := by
    simp only [map_mul, map_sub, Polynomial.aeval_C]
    field_simp at heq
    linear_combination heq
  have hcross := hinj hcrossJ
  have hcopΦ : IsCoprime (twistComp Φ T P) (twistComp Φ T Q) := by
    obtain ⟨a, b, hab⟩ := hcop
    refine ⟨twistComp Φ T a, twistComp Φ T b, ?_⟩
    rw [← twistComp_mul, ← twistComp_mul, ← twistComp_add, hab]
    rw [show (1 : Polynomial ↥(jetPrefixField C (N + 2))) = Polynomial.C 1 from by rw [map_one],
      twistComp_C, map_one, map_one]
  have hdvd : twistComp Φ T Q ∣ Q := hcopΦ.symm.dvd_of_dvd_mul_left ⟨_, hcross⟩
  obtain ⟨e', he'0, he'⟩ := eq_C_mul_of_dvd_of_natDegree_eq hQ0 hdvd
    (natDegree_twistComp Φ hT Q).symm
  have hdQ : twistComp Φ T Q = Polynomial.C e'⁻¹ * Q := by
    conv_rhs => rw [he']
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ he'0, map_one, one_mul]
  by_cases hdeg : 1 ≤ Q.natDegree
  · exact Or.inl (exists_normalizing_shift R hR hM2 hdeg (by rw [← hTdef]; exact hdQ))
  refine Or.inr ⟨Polynomial.C (Q.coeff 0)⁻¹ * P, ?_, ?_⟩
  · have hQC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hq0 : Q.coeff 0 ≠ 0 := fun hh => hQ0 (by rw [hQC, hh, map_zero])
    have hqval : Polynomial.aeval x Q
        = algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) (Q.coeff 0) := by
      conv_lhs => rw [hQC]
      rw [Polynomial.aeval_C]
    have hqne : algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) (Q.coeff 0) ≠ 0 := by
      rw [← hqval]; exact hQy
    rw [hvdiv, map_mul, Polynomial.aeval_C, map_inv₀, hqval]
    field_simp
  · have hQC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
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
