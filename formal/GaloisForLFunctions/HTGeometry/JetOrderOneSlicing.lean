import GaloisForLFunctions.HTGeometry.JetAffineConnectionLevelTwo

/-!
# Slicing an inhomogeneous relation of order one

An element `v` of the free jet field of order at most one satisfying

`Φ(v) = R'·v − S(y₁)`

with `S` a polynomial in the first jet coordinate over the rational functions of the free generator
is a coprime fraction in `y₁`, and the substitution acts on `y₁` by the pure scaling `y₁ ↦ R'·y₁`.
The twisted composition therefore preserves degrees and coprimality, so the denominator divides its
own image and equals it up to a scalar; comparing the numerator coefficient `m` above the degree of
the denominator, where `m` bounds the degree of `S`, turns the relation into

`a(R)·(R')^m = R'·a − S_m`

for the ratio of that coefficient by the leading coefficient of the denominator.  At `S = R''·y₁²`
this is the affine-connection equation; the higher `m` are the equations the level-three descent
produces.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **The slicing.**  An inhomogeneous relation of order one produces an affine transport of
exponent the degree bound of the inhomogeneous polynomial, with inhomogeneous term its top
coefficient. -/
theorem exists_prefix_affineTransport_of_order_one (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {v : JetField C Unit} (hv : ∀ j : ℕ, 1 < j → JetField.pd ((), j) v = 0)
    {S : Polynomial ↥(jetPrefixField C 1)} {m n : ℕ} (hS : S.natDegree ≤ m)
    (heq : jetSubstitution R hR v * substitutionDeriv R ^ n
      = substitutionDeriv R * v
        - Polynomial.aeval (JetField.jet ((), 1) : JetField C Unit) S) :
    ∃ a : ↥(jetPrefixField C 1),
      (jetSubstitutionPrefix R hR 1).toRingHom a
          * substitutionDerivPrefix R (le_refl 1) ^ (n + m)
        = substitutionDerivPrefix R (le_refl 1) * a - S.coeff m := by
  classical
  set x : JetField C Unit := JetField.jet ((), 1) with hxdef
  have hxtr : Transcendental (jetPrefixField C 1) x := transcendental_jet_over_jetPrefixField 1
  have hinj : Function.Injective (Polynomial.aeval (R := ↥(jetPrefixField C 1)) x) :=
    transcendental_iff_injective.mp hxtr
  set Φ : ↥(jetPrefixField C 1) →+* ↥(jetPrefixField C 1) :=
    (jetSubstitutionPrefix R hR 1).toRingHom with hΦdef
  set ρF : ↥(jetPrefixField C 1) := substitutionDerivPrefix R (le_refl 1) with hρFdef
  have hρF : ρF ≠ 0 := substitutionDerivPrefix_ne_zero R hR (le_refl 1)
  have hρval : (algebraMap ↥(jetPrefixField C 1) (JetField C Unit)) ρF = substitutionDeriv R := rfl
  set T : Polynomial ↥(jetPrefixField C 1) := Polynomial.C ρF * Polynomial.X with hTdef
  have hT : T.natDegree = 1 := natDegree_scaleSubst hρF
  -- the substitution acts on the first jet coordinate by a pure scaling
  have hact : jetSubstitution R hR x = Polynomial.aeval x T := by
    rw [hxdef, jetSubstitution_jet, substitutionJet_one, hTdef, map_mul, Polynomial.aeval_C,
      Polynomial.aeval_X, hρval]
    ring
  have hmemadj : v ∈ IntermediateField.adjoin (jetPrefixField C 1)
      ({x} : Set (JetField C Unit)) := mem_adjoin_jet_of_order hv
  -- slice as a coprime fraction in the first jet coordinate
  set f : RatFunc ↥(jetPrefixField C 1) :=
    (RatFunc.algEquivOfTranscendental x hxtr).symm ⟨v, hmemadj⟩ with hfdef
  have hxeval : ratFuncEval x hxtr f = v := by
    simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hfdef,
      AlgEquiv.apply_symm_apply]
    rfl
  set P : Polynomial ↥(jetPrefixField C 1) := f.num with hPdef
  set Q : Polynomial ↥(jetPrefixField C 1) := f.denom with hQdef
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
  rw [hLHS, hvdiv, ← hρval, ← map_pow] at heq
  have hcrossJ : Polynomial.aeval x (Polynomial.C (ρF ^ n) * twistComp Φ T P * Q)
      = Polynomial.aeval x (twistComp Φ T Q * (Polynomial.C ρF * P - S * Q)) := by
    simp only [map_mul, map_sub, Polynomial.aeval_C] at heq ⊢
    field_simp at heq
    linear_combination heq
  have hcross := hinj hcrossJ
  have hCρn : (Polynomial.C (ρF ^ n) : Polynomial ↥(jetPrefixField C 1)) ≠ 0 := by
    intro hh
    exact pow_ne_zero n hρF (by simpa using hh)
  -- the denominator is a scalar eigenvector
  have hcopΦ : IsCoprime (twistComp Φ T P) (twistComp Φ T Q) := by
    obtain ⟨u, w, huw⟩ := hcop
    refine ⟨twistComp Φ T u, twistComp Φ T w, ?_⟩
    rw [← twistComp_mul, ← twistComp_mul, ← twistComp_add, huw]
    rw [show (1 : Polynomial ↥(jetPrefixField C 1)) = Polynomial.C 1 from by rw [map_one],
      twistComp_C, map_one, map_one]
  have hcross' : twistComp Φ T P * Q
      = twistComp Φ T Q * (Polynomial.C (ρF ^ n)⁻¹ * (Polynomial.C ρF * P - S * Q)) := by
    refine mul_left_cancel₀ hCρn ?_
    calc Polynomial.C (ρF ^ n) * (twistComp Φ T P * Q)
        = Polynomial.C (ρF ^ n) * twistComp Φ T P * Q := by ring
      _ = twistComp Φ T Q * (Polynomial.C ρF * P - S * Q) := hcross
      _ = Polynomial.C (ρF ^ n) * (twistComp Φ T Q
            * (Polynomial.C (ρF ^ n)⁻¹ * (Polynomial.C ρF * P - S * Q))) := by
          rw [show Polynomial.C (ρF ^ n) * (twistComp Φ T Q
              * (Polynomial.C (ρF ^ n)⁻¹ * (Polynomial.C ρF * P - S * Q)))
            = (Polynomial.C (ρF ^ n) * Polynomial.C (ρF ^ n)⁻¹)
              * (twistComp Φ T Q * (Polynomial.C ρF * P - S * Q)) from by ring,
            ← Polynomial.C_mul, mul_inv_cancel₀ (pow_ne_zero n hρF), map_one, one_mul]
  have hdvd : twistComp Φ T Q ∣ Q := hcopΦ.symm.dvd_of_dvd_mul_left ⟨_, hcross'⟩
  obtain ⟨e', he'0, he'⟩ := eq_C_mul_of_dvd_of_natDegree_eq hQ0 hdvd
    (natDegree_twistComp Φ hT Q).symm
  set e : ↥(jetPrefixField C 1) := e'⁻¹ with hedef
  have hdQ : twistComp Φ T Q = Polynomial.C e * Q := by
    conv_rhs => rw [he']
    rw [hedef, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ he'0, map_one, one_mul]
  have hPeq : Polynomial.C (ρF ^ n) * twistComp Φ T P
      = Polynomial.C e * (Polynomial.C ρF * P - S * Q) := by
    refine mul_right_cancel₀ hQ0 ?_
    rw [hcross, hdQ]
    ring
  -- compare coefficients `m` above the degree of the denominator
  set nQ : ℕ := Q.natDegree with hndef
  set q : ↥(jetPrefixField C 1) := Q.coeff nQ with hqdef
  set p : ↥(jetPrefixField C 1) := P.coeff (nQ + m) with hpdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, hndef, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ0
  have h2 : Φ q * ρF ^ nQ = e * q :=
    coeff_eigen_of_twistComp_scale Φ (ρ := ρF) (c := e) (P := Q) (by rw [← hTdef]; exact hdQ) nQ
  have hSQ : (S * Q).coeff (nQ + m) = S.coeff m * q := by
    rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_single (m, nQ) ?_ ?_
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      by_cases hi : i ≤ m
      · have him : i ≠ m := by
          rintro rfl
          exact hne (by simp only [Prod.mk.injEq, true_and]; omega)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), mul_zero]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := S) (by omega), zero_mul]
    · intro h
      refine absurd ?_ h
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp [Nat.add_comm])
  have h1 : ρF ^ n * (Φ p * ρF ^ (nQ + m)) = e * (ρF * p - S.coeff m * q) := by
    have hL : (twistComp Φ T P).coeff (nQ + m) = Φ (P.coeff (nQ + m)) * ρF ^ (nQ + m) := by
      rw [hTdef]; exact coeff_twistComp_scale Φ ρF P (nQ + m)
    have hR' : (Polynomial.C (ρF ^ n) * twistComp Φ T P).coeff (nQ + m)
        = (Polynomial.C e * (Polynomial.C ρF * P - S * Q)).coeff (nQ + m) := by rw [hPeq]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_sub, hL] at hR'
    rw [hR', hSQ]
  -- eliminate the scalar
  have hkey : Φ p * ρF ^ (n + m) * q = Φ q * (ρF * p - S.coeff m * q) := by
    have h3 : ρF ^ n * (Φ p * ρF ^ (nQ + m)) * q
        = Φ q * ρF ^ nQ * (ρF * p - S.coeff m * q) := by
      calc ρF ^ n * (Φ p * ρF ^ (nQ + m)) * q = (e * (ρF * p - S.coeff m * q)) * q := by rw [h1]
        _ = (e * q) * (ρF * p - S.coeff m * q) := by ring
        _ = (Φ q * ρF ^ nQ) * (ρF * p - S.coeff m * q) := by rw [h2]
    have hpow : ρF ^ n * ρF ^ (nQ + m) = ρF ^ nQ * ρF ^ (n + m) := by
      rw [← pow_add, ← pow_add]
      ring_nf
    refine mul_left_cancel₀ (pow_ne_zero nQ hρF) ?_
    calc ρF ^ nQ * (Φ p * ρF ^ (n + m) * q)
        = ρF ^ n * (Φ p * ρF ^ (nQ + m)) * q := by
          rw [show ρF ^ n * (Φ p * ρF ^ (nQ + m)) * q
            = (ρF ^ n * ρF ^ (nQ + m)) * (Φ p * q) from by ring, hpow]
          ring
      _ = Φ q * ρF ^ nQ * (ρF * p - S.coeff m * q) := h3
      _ = ρF ^ nQ * (Φ q * (ρF * p - S.coeff m * q)) := by ring
  have hΦq0 : Φ q ≠ 0 := fun hh => hq0 ((map_eq_zero_iff Φ Φ.injective).mp hh)
  refine ⟨p / q, ?_⟩
  rw [map_div₀]
  field_simp
  linear_combination hkey

/-- **The slicing, in rational functions.** -/
theorem exists_ratFunc_affineTransport_of_order_one (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {v : JetField C Unit} (hv : ∀ j : ℕ, 1 < j → JetField.pd ((), j) v = 0)
    {S : Polynomial ↥(jetPrefixField C 1)} {m n : ℕ} (hS : S.natDegree ≤ m)
    (heq : jetSubstitution R hR v * substitutionDeriv R ^ n
      = substitutionDeriv R * v
        - Polynomial.aeval (JetField.jet ((), 1) : JetField C Unit) S)
    {D : RatFunc C}
    (hD : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen D
      = (algebraMap ↥(jetPrefixField C 1) (JetField C Unit)) (S.coeff m)) :
    ∃ a : RatFunc C,
      ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) a
          * ratFuncDeriv R ^ (n + m) = ratFuncDeriv R * a - D := by
  obtain ⟨b, hb⟩ := exists_prefix_affineTransport_of_order_one R hR hv hS heq
  have hordA : ∀ j : ℕ, 0 < j → JetField.pd ((), j)
      (algebraMap ↥(jetPrefixField C 1) (JetField C Unit) b) = 0 := by
    intro j hj
    exact (mem_jetPrefixField_iff 1 _).mp b.2 j (by omega)
  obtain ⟨A, hA⟩ := exists_ratFunc_of_order_zero hordA
  refine ⟨A, ?_⟩
  have hev : Function.Injective
      (ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen) :=
    ratFuncEval_injective _ transcendental_freeGen
  refine hev ?_
  rw [map_mul, map_pow, map_sub, map_mul, ratFuncEval_ratFuncSubstitution, hA,
    ratFuncEval_ratFuncDeriv, hD]
  have hcoe := congrArg (fun z : ↥(jetPrefixField C 1) =>
    (algebraMap ↥(jetPrefixField C 1) (JetField C Unit) z)) hb
  simp only [map_sub, map_mul, map_pow] at hcoe
  have hcoeq : jetSubstitution R hR
      (algebraMap ↥(jetPrefixField C 1) (JetField C Unit) b)
      = algebraMap ↥(jetPrefixField C 1) (JetField C Unit)
          ((jetSubstitutionPrefix R hR 1).toRingHom b) := rfl
  rw [← hcoeq] at hcoe
  exact hcoe

end

end GaloisForLFunctions.HTGeometry
