import GaloisForLFunctions.HTGeometry.JetLevelBranchAboveThree
import GaloisForLFunctions.HTGeometry.JetTopPartialSubstitution
import GaloisForLFunctions.HTGeometry.JetWeightPartial
import GaloisForLFunctions.HTGeometry.JetShiftWeightNormalization

/-!
# The isobaric type of the sliced shift

A normalizing shift is isobaric of weight its level up to a multiple of the first jet coordinate, so
its coefficient in the coordinate below the top — obtained by one partial derivative — is isobaric of
weight one.  A constant has weight zero, so the constant term of that coefficient vanishes:

`u₁ = −(N + 3)·y₂/y₁`

with no additive constant.  This pins the linear branch of the slicing above jet level three
completely.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- The weighted action scales a ratio by the first jet coordinate by one weight less. -/
theorem weightScale_jetOverOne {lam : C} (h : lam ≠ 0) (j : ℕ) :
    weightScale h (jetOverOne j : JetField C Unit)
      = algebraMap C (JetField C Unit) (lam ^ j / lam) * jetOverOne j := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hlam : algebraMap C (JetField C Unit) lam ≠ 0 := by
    intro hh
    exact h ((algebraMap C (JetField C Unit)).injective (by rw [hh, map_zero]))
  rw [jetOverOne, map_div₀, weightScale_jet, weightScale_jet, pow_one, map_div₀, map_pow]
  field_simp

/-- Every polynomial expression in a jet coordinate is killed by the higher partials. -/
theorem pd_aeval_jet_eq_zero {i j : ℕ} (hj : i < j) (P : Polynomial ↥(jetPrefixField C i)) :
    JetField.pd ((), j) (Polynomial.aeval (JetField.jet ((), i) : JetField C Unit) P) = 0 := by
  have hx : JetField.pd ((), j) (JetField.jet ((), i) : JetField C Unit) = 0 :=
    JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)
  induction P using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.aeval_C]
      exact (mem_jetPrefixField_iff i _).mp a.2 j (by omega)
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | monomial n a _ =>
      have hpow : JetField.pd ((), j)
          ((JetField.jet ((), i) : JetField C Unit) ^ (n + 1)) = 0 := by
        have hl := (JetField.pd ((), j) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
            (JetField.jet ((), i) : JetField C Unit) (n + 1)
        simp only [smul_eq_mul, hx, mul_zero, smul_zero] at hl
        exact hl
      have ha : JetField.pd ((), j)
          (algebraMap ↥(jetPrefixField C i) (JetField C Unit) a) = 0 :=
        (mem_jetPrefixField_iff i _).mp a.2 j (by omega)
      have hleib := (JetField.pd ((), j) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (algebraMap ↥(jetPrefixField C i) (JetField C Unit) a)
          ((JetField.jet ((), i) : JetField C Unit) ^ (n + 1))
      simp only [smul_eq_mul] at hleib
      rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, hleib, ha, hpow]
      ring

/-- **The polynomial branch is itself a normalizing shift.** -/
theorem hasNormalizingShift_of_branch (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (N : ℕ)
    {u : Polynomial ↥(jetPrefixField C (N + 2))} {A B : ↥(jetPrefixField C (N + 2))}
    (hAB : substitutionShift R (N + 3)
      = (A : JetField C Unit) * (JetField.jet ((), N + 2) : JetField C Unit)
        + (B : JetField C Unit))
    (hcu : twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
        (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
      = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
        - (Polynomial.C A * Polynomial.X + Polynomial.C B)) :
    ∃ t : ↥(jetPrefixField C (N + 3)),
      jetSubstitutionPrefix R hR (N + 3) t
          = substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 3 by omega) * t
            - substitutionShiftPrefix R (show (1 : ℕ) ≤ N + 3 by omega)
        ∧ (t : JetField C Unit)
          = Polynomial.aeval (JetField.jet ((), N + 2) : JetField C Unit) u := by
  set x : JetField C Unit := JetField.jet ((), N + 2) with hxdef
  set hM2 : (1 : ℕ) ≤ N + 2 := by omega
  have hmem : Polynomial.aeval x u ∈ jetPrefixField C (N + 3) := by
    rw [mem_jetPrefixField_iff]
    intro j hj
    exact pd_aeval_jet_eq_zero (by omega) u
  have hact : jetSubstitution R hR x = Polynomial.aeval x (substitutionAffine R hM2) := by
    rw [hxdef, jetSubstitution_jet, aeval_substitutionAffine]
  have hJ := congrArg (Polynomial.aeval x) hcu
  rw [← jetSubstitution_aeval_of_act R hR hact] at hJ
  simp only [map_sub, map_mul, map_add, Polynomial.aeval_C, Polynomial.aeval_X] at hJ
  refine ⟨⟨Polynomial.aeval x u, hmem⟩, ?_, rfl⟩
  refine Subtype.ext ?_
  show jetSubstitution R hR (Polynomial.aeval x u)
    = substitutionDeriv R * Polynomial.aeval x u - substitutionShift R (N + 3)
  rw [hJ, hAB]
  rfl

/-- **The linear coefficient of the sliced shift above level three has no constant term.** -/
theorem branch_linear_coefficient_eq (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ}
    (hN : 1 ≤ N)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N + 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {u : Polynomial ↥(jetPrefixField C (N + 2))} {A B : ↥(jetPrefixField C (N + 2))}
    (hdeg : u.natDegree = 1 ∨ u.natDegree = 2)
    (hAB : substitutionShift R (N + 3)
      = (A : JetField C Unit) * (JetField.jet ((), N + 2) : JetField C Unit)
        + (B : JetField C Unit))
    (hcu : twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
        (substitutionAffine R (show (1 : ℕ) ≤ N + 2 by omega)) u
      = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)) * u
        - (Polynomial.C A * Polynomial.X + Polynomial.C B)) :
    (u.coeff 1 : JetField C Unit)
      = -(algebraMap C (JetField C Unit) ((N + 3 : ℕ) : C) * jetOverOne 2) := by
  classical
  obtain ⟨hdeg1, c₀, hc₀⟩ := branch_linear_above_three R hR hN hfix hdeg hAB hcu
  obtain ⟨t, ht, htu⟩ := hasNormalizingShift_of_branch R hR N hAB hcu
  -- the coefficient is the top partial of the shift
  have hu1 : (u.coeff 1 : JetField C Unit)
      = JetField.pd ((), N + 2) (t : JetField C Unit) := by
    rw [htu, pd_aeval_jet]
    have hder : Polynomial.derivative u = Polynomial.C (u.coeff 1) := by
      have h2 : u.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      have hu : u = Polynomial.C (u.coeff 1) * Polynomial.X + Polynomial.C (u.coeff 0) := by
        have := eq_quadratic_of_natDegree_le_two (u := u) (by omega)
        rw [h2, map_zero, zero_mul, zero_add] at this
        exact this
      conv_lhs => rw [hu]
      rw [Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_X,
        Polynomial.derivative_C, mul_one, add_zero]
    rw [hder, Polynomial.aeval_C]
    rfl
  -- isobarity of the shift
  have hc0 : c₀ = 0 := by
    have htwo : (2 : C) ≠ 0 := two_ne_zero
    obtain ⟨γ, hγ⟩ := exists_const_weightScale_shift_sub R hR (show 2 ≤ N + 3 by omega)
      (fun g hg hgfix => hfix g (fun j hj => hg j (by omega)) hgfix) htwo t ht
    have hzero : JetField.pd ((), N + 2)
        (algebraMap C (JetField C Unit) γ * (JetField.jet ((), 1) : JetField C Unit)) = 0 := by
      have hl := (JetField.pd ((), N + 2) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (algebraMap C (JetField C Unit) γ) (JetField.jet ((), 1) : JetField C Unit)
      simp only [smul_eq_mul] at hl
      rw [hl, Derivation.map_algebraMap,
        JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)]
      ring
    have hlin : JetField.pd ((), N + 2)
        (algebraMap C (JetField C Unit) ((2 : C) ^ (N + 3)) * (t : JetField C Unit))
        = algebraMap C (JetField C Unit) ((2 : C) ^ (N + 3))
          * JetField.pd ((), N + 2) (t : JetField C Unit) := by
      have hl := (JetField.pd ((), N + 2) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (algebraMap C (JetField C Unit) ((2 : C) ^ (N + 3))) (t : JetField C Unit)
      simp only [smul_eq_mul] at hl
      rw [hl, Derivation.map_algebraMap]
      ring
    have hpd := congrArg (JetField.pd ((), N + 2) : JetField C Unit → JetField C Unit) hγ
    rw [map_sub, weightScale_pd, hlin, hzero] at hpd
    have hpow : algebraMap C (JetField C Unit) ((2 : C) ^ (N + 2)) ≠ 0 := by
      intro hh
      exact pow_ne_zero (N + 2) htwo
        ((algebraMap C (JetField C Unit)).injective (by rw [hh, map_zero]))
    have hiso : weightScale htwo (u.coeff 1 : JetField C Unit)
        = algebraMap C (JetField C Unit) (2 : C) * (u.coeff 1 : JetField C Unit) := by
      refine mul_left_cancel₀ hpow ?_
      rw [hu1]
      have h23 : (2 : C) ^ (N + 2) * 2 = 2 ^ (N + 3) := by ring
      calc algebraMap C (JetField C Unit) ((2 : C) ^ (N + 2))
              * weightScale htwo (JetField.pd ((), N + 2) (t : JetField C Unit))
          = algebraMap C (JetField C Unit) ((2 : C) ^ (N + 3))
              * JetField.pd ((), N + 2) (t : JetField C Unit) := by linear_combination hpd
        _ = algebraMap C (JetField C Unit) ((2 : C) ^ (N + 2))
              * (algebraMap C (JetField C Unit) (2 : C)
                * JetField.pd ((), N + 2) (t : JetField C Unit)) := by
              rw [← mul_assoc, ← map_mul, h23]
    rw [hc₀, map_sub, map_mul, weightScale_jetOverOne, AlgEquiv.commutes, AlgEquiv.commutes] at hiso
    have h2sq : ((2 : C) ^ 2 / 2) = 2 := by norm_num
    rw [h2sq] at hiso
    have hkey : algebraMap C (JetField C Unit) c₀
        = algebraMap C (JetField C Unit) (2 : C) * algebraMap C (JetField C Unit) c₀ := by
      linear_combination hiso
    have hz : algebraMap C (JetField C Unit) c₀ = 0 := by
      have h2 : algebraMap C (JetField C Unit) (2 : C) = 1 + 1 := by
        rw [show (2 : C) = 1 + 1 from by norm_num, map_add, map_one]
      rw [h2] at hkey
      linear_combination -hkey
    exact (algebraMap C (JetField C Unit)).injective (by rw [hz, map_zero])
  rw [hc₀, hc0, map_zero, zero_sub]

end

end GaloisForLFunctions.HTGeometry
