import GaloisForLFunctions.HTGeometry.JetWeightZeroSlice

/-!
# The slicing dichotomy in a weight-zero coordinate

The general form of the descent step.  An element of jet order at most `k` satisfying

`Φ(w) = c·w − S(z_k)`

with the substitution acting on the weight-zero coordinate by an affine polynomial
`Φ(z_k) = a·z_k + b` is a coprime fraction in `z_k`; the denominator divides its own twisted image
and has the same degree, so it is a scalar eigenvector.  Positive degree gives the affine cocycle of
its two top coefficients, and degree zero makes `w` a polynomial in `z_k` satisfying the same
relation.

Both the coefficient `c` and the affine data `a, b` are arbitrary, so the same statement covers the
homogeneous eigen-relations of the weight-zero tower and the inhomogeneous ones the descent
produces.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **The slicing dichotomy in the weight-zero coordinate.** -/
theorem cocycle_or_polynomial_of_zslice (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {k : ℕ}
    (hk : 1 < k) {w : JetField C Unit} (hwz : IsWeightZero w)
    (hw : ∀ j : ℕ, k < j → JetField.pd ((), j) w = 0)
    {a b c : ↥(jetPrefixField C k)} (ha : a ≠ 0)
    (hact : jetSubstitution R hR (jetRatio k : JetField C Unit)
      = Polynomial.aeval (jetRatio k : JetField C Unit)
        (Polynomial.C a * Polynomial.X + Polynomial.C b))
    (S : Polynomial ↥(jetPrefixField C k))
    (heq : jetSubstitution R hR w
      = algebraMap ↥(jetPrefixField C k) (JetField C Unit) c * w
        - Polynomial.aeval (jetRatio k : JetField C Unit) S) :
    (∃ (ν : ℕ) (s : ↥(jetPrefixField C k)), 1 ≤ ν ∧
        (jetSubstitutionPrefix R hR k).toRingHom s = a * s - (ν : ↥(jetPrefixField C k)) * b)
      ∨ ∃ u : Polynomial ↥(jetPrefixField C k),
          (∀ i : ℕ, IsWeightZero ((u.coeff i : ↥(jetPrefixField C k)) : JetField C Unit)) ∧
            w = Polynomial.aeval (jetRatio k : JetField C Unit) u ∧
            twistComp (jetSubstitutionPrefix R hR k).toRingHom
                (Polynomial.C a * Polynomial.X + Polynomial.C b) u
              = Polynomial.C c * u - S := by
  classical
  set z : JetField C Unit := (jetRatio k : JetField C Unit) with hzdef
  have hztr : Transcendental (jetPrefixField C k) z :=
    transcendental_jetRatio_over_jetPrefixField hk
  have hinj : Function.Injective (Polynomial.aeval (R := ↥(jetPrefixField C k)) z) :=
    transcendental_iff_injective.mp hztr
  set Φ : ↥(jetPrefixField C k) →+* ↥(jetPrefixField C k) :=
    (jetSubstitutionPrefix R hR k).toRingHom with hΦdef
  set T : Polynomial ↥(jetPrefixField C k) :=
    Polynomial.C a * Polynomial.X + Polynomial.C b with hTdef
  have hT : T.natDegree = 1 := Polynomial.natDegree_linear ha
  have hmemadj : w ∈ IntermediateField.adjoin (jetPrefixField C k)
    ({z} : Set (JetField C Unit)) := mem_adjoin_jetRatio_of_order hk hw
  set f : RatFunc ↥(jetPrefixField C k) :=
    (RatFunc.algEquivOfTranscendental z hztr).symm ⟨w, hmemadj⟩ with hfdef
  have hzeval : ratFuncEval z hztr f = w := by
    simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hfdef,
      AlgEquiv.apply_symm_apply]
    rfl
  set P : Polynomial ↥(jetPrefixField C k) := f.num with hPdef
  set Q : Polynomial ↥(jetPrefixField C k) := f.denom with hQdef
  have hQ0 : Q ≠ 0 := RatFunc.denom_ne_zero f
  have hcop : IsCoprime P Q := RatFunc.isCoprime_num_denom f
  have hQy : Polynomial.aeval z Q ≠ 0 := fun hh => hQ0 (hinj (by simpa using hh))
  have hwdiv : w = Polynomial.aeval z P / Polynomial.aeval z Q := by
    rw [← hzeval, ratFuncEval_eq_div]
  have hΦQ0 : twistComp Φ T Q ≠ 0 := twistComp_ne_zero Φ hT hQ0
  have hΦQy : Polynomial.aeval z (twistComp Φ T Q) ≠ 0 :=
    fun hh => hΦQ0 (hinj (by simpa using hh))
  have hLHS : jetSubstitution R hR w
      = Polynomial.aeval z (twistComp Φ T P) / Polynomial.aeval z (twistComp Φ T Q) := by
    rw [hwdiv, map_div₀, jetSubstitution_aeval_of_act R hR hact,
      jetSubstitution_aeval_of_act R hR hact]
  rw [hLHS, hwdiv] at heq
  have hcrossJ : Polynomial.aeval z (twistComp Φ T P * Q)
      = Polynomial.aeval z (twistComp Φ T Q * (Polynomial.C c * P - S * Q)) := by
    simp only [map_mul, map_sub, Polynomial.aeval_C]
    field_simp at heq
    linear_combination heq
  have hcross := hinj hcrossJ
  have hcopΦ : IsCoprime (twistComp Φ T P) (twistComp Φ T Q) := by
    obtain ⟨p, q, hpq⟩ := hcop
    refine ⟨twistComp Φ T p, twistComp Φ T q, ?_⟩
    rw [← twistComp_mul, ← twistComp_mul, ← twistComp_add, hpq]
    rw [show (1 : Polynomial ↥(jetPrefixField C k)) = Polynomial.C 1 from by rw [map_one],
      twistComp_C, map_one, map_one]
  have hdvd : twistComp Φ T Q ∣ Q := hcopΦ.symm.dvd_of_dvd_mul_left ⟨_, hcross⟩
  obtain ⟨e', he'0, he'⟩ := eq_C_mul_of_dvd_of_natDegree_eq hQ0 hdvd
    (natDegree_twistComp Φ hT Q).symm
  have hdQ : twistComp Φ T Q = Polynomial.C e'⁻¹ * Q := by
    conv_rhs => rw [he']
    rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ he'0, map_one, one_mul]
  by_cases hdeg : 1 ≤ Q.natDegree
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, Q.natDegree = n + 1 := ⟨Q.natDegree - 1, by omega⟩
    refine Or.inl ⟨n + 1, Q.coeff n / Q.coeff (n + 1), by omega, ?_⟩
    have hcoc := twistComp_affine_cocycle Φ ha hn (by rw [← hTdef]; exact hdQ)
    rw [hcoc]
    push_cast
    ring
  · have hQm : Q.Monic := RatFunc.monic_denom f
    have hcoeffwz : ∀ i : ℕ,
        IsWeightZero ((P.coeff i : ↥(jetPrefixField C k)) : JetField C Unit)
          ∧ IsWeightZero ((Q.coeff i : ↥(jetPrefixField C k)) : JetField C Unit) := by
      intro i
      exact isWeightZero_coeff_of_slice hk hwz hQ0 hQm hcop hwdiv i
    refine Or.inr ⟨Polynomial.C (Q.coeff 0)⁻¹ * P, ?_, ?_, ?_⟩
    · intro i
      rw [Polynomial.coeff_C_mul]
      have hcoe : (((Q.coeff 0)⁻¹ * P.coeff i : ↥(jetPrefixField C k)) : JetField C Unit)
          = (((Q.coeff 0 : ↥(jetPrefixField C k)) : JetField C Unit))⁻¹
            * ((P.coeff i : ↥(jetPrefixField C k)) : JetField C Unit) := by
        push_cast
        rfl
      rw [hcoe]
      exact IsWeightZero.mul ((hcoeffwz 0).2.inv) (hcoeffwz i).1
    · have hQC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
      have hq0 : Q.coeff 0 ≠ 0 := fun hh => hQ0 (by rw [hQC, hh, map_zero])
      have hqval : Polynomial.aeval z Q
          = algebraMap ↥(jetPrefixField C k) (JetField C Unit) (Q.coeff 0) := by
        conv_lhs => rw [hQC]
        rw [Polynomial.aeval_C]
      have hqne : algebraMap ↥(jetPrefixField C k) (JetField C Unit) (Q.coeff 0) ≠ 0 := by
        rw [← hqval]; exact hQy
      rw [hwdiv, map_mul, Polynomial.aeval_C, map_inv₀, hqval]
      field_simp
    · have hQC : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
      have hq0 : Q.coeff 0 ≠ 0 := fun hh => hQ0 (by rw [hQC, hh, map_zero])
      have hΦq0 : Φ (Q.coeff 0) ≠ 0 := fun hh => hq0 ((map_eq_zero_iff Φ Φ.injective).mp hh)
      have hCq0 : (Polynomial.C (Q.coeff 0) : Polynomial ↥(jetPrefixField C k)) ≠ 0 := by
        intro hh
        exact hq0 (by simpa using hh)
      have hTQ : twistComp Φ T Q = Polynomial.C (Φ (Q.coeff 0)) := by
        conv_lhs => rw [hQC]
        rw [twistComp_C]
      have hcross' : twistComp Φ T P * Polynomial.C (Q.coeff 0)
          = Polynomial.C (Φ (Q.coeff 0))
            * (Polynomial.C c * P - S * Polynomial.C (Q.coeff 0)) := by
        calc twistComp Φ T P * Polynomial.C (Q.coeff 0)
            = twistComp Φ T P * Q := by rw [← hQC]
          _ = twistComp Φ T Q * (Polynomial.C c * P - S * Q) := hcross
          _ = Polynomial.C (Φ (Q.coeff 0))
                * (Polynomial.C c * P - S * Polynomial.C (Q.coeff 0)) := by
              rw [hTQ, ← hQC]
      rw [twistComp_mul, twistComp_C, map_inv₀]
      refine mul_right_cancel₀ hCq0 ?_
      calc Polynomial.C (Φ (Q.coeff 0))⁻¹ * twistComp Φ T P * Polynomial.C (Q.coeff 0)
          = Polynomial.C (Φ (Q.coeff 0))⁻¹
              * (twistComp Φ T P * Polynomial.C (Q.coeff 0)) := by ring
        _ = Polynomial.C (Φ (Q.coeff 0))⁻¹ * (Polynomial.C (Φ (Q.coeff 0))
              * (Polynomial.C c * P - S * Polynomial.C (Q.coeff 0))) := by rw [hcross']
        _ = Polynomial.C c * P - S * Polynomial.C (Q.coeff 0) := by
            rw [← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hΦq0, map_one, one_mul]
        _ = (Polynomial.C c * (Polynomial.C (Q.coeff 0)⁻¹ * P) - S)
              * Polynomial.C (Q.coeff 0) := by
            rw [sub_mul]
            congr 1
            rw [mul_assoc, mul_comm (Polynomial.C (Q.coeff 0)⁻¹ * P) (Polynomial.C (Q.coeff 0)),
              ← mul_assoc (Polynomial.C (Q.coeff 0)) (Polynomial.C (Q.coeff 0)⁻¹) P,
              ← Polynomial.C_mul, mul_inv_cancel₀ hq0, map_one, one_mul]

end

end GaloisForLFunctions.HTGeometry
