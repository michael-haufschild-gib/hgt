import GaloisForLFunctions.HTGeometry.JetLevelFourTools
import GaloisForLFunctions.HTGeometry.JetLevelBranchIsobaric
import GaloisForLFunctions.HTGeometry.JetShiftSecondCoefficient

/-!
# The jet descent at level four

At level four the sliced shift is linear with coefficient `−4·y₂/y₁`, so its constant term satisfies

`Φ(u₀) = R'·u₀ − [ −9R''·y₂² + (2R''' − 12(R'')²/R')·y₁²·y₂ + (R'''' − 4R''R'''/R')·y₁⁴ ]`,

an inhomogeneous relation of order two.  Slicing it in `y₂` either descends to level two or makes
`u₀` a polynomial; degrees at least four reproduce the affine cocycle, and the remaining coefficient
comparisons are explicit: the cubic coefficient satisfies a pure scaling relation of exponent two, so
`c₃·y₁²` is a constant `a₃`; the quadratic coefficient then satisfies
`Φ(c₂)·(R')² = R'·c₂ − (3a₃ − 9)·R''`, which for `a₃ ≠ 3` is a scaled affine connection; and with
`a₃ = 3` the linear coefficient produces the affine transport of exponent three with inhomogeneous
term `2R''' − 3(R'')²/R'`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **The alternatives at jet level four.** -/
theorem level_four_alternatives (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (hR2 : JetField.pd ((), 0) (substitutionDeriv R) ≠ 0)
    (hfix3 : ∀ g : JetField C Unit, (∀ j : ℕ, 3 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    (h : HasNormalizingShift R hR (show (1 : ℕ) ≤ 4 by omega)) :
    HasNormalizingShift R hR (show (1 : ℕ) ≤ 3 by omega)
      ∨ HasNormalizingShift R hR (show (1 : ℕ) ≤ 2 by omega)
      ∨ (∃ (γ : C) (α : RatFunc C), γ ≠ 0 ∧
          ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) α
              * ratFuncDeriv R ^ 2
            = ratFuncDeriv R * α - RatFunc.C γ * ratFuncDeriv (ratFuncDeriv R))
      ∨ (∃ α : RatFunc C,
          ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) α
              * ratFuncDeriv R ^ 3
            = ratFuncDeriv R * α
              - (2 * ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R))
                - RatFunc.C (3 : C) * ratFuncDeriv (ratFuncDeriv R) ^ 2 / ratFuncDeriv R)) := by
  classical
  have hfix2 : ∀ g : JetField C Unit, (∀ j : ℕ, 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e :=
    fun g hg hgfix => hfix3 g (fun j hj => hg j (by omega)) hgfix
  rcases hasNormalizingShift_pred_or_low_degree R hR hR2 1 (by simpa using h) with hpred | hbr
  · exact Or.inl (by simpa using hpred)
  obtain ⟨u, A, B, hdeg, hAB, hcu⟩ := hbr
  refine Or.inr ?_
  -- the linear branch and its coefficient
  obtain ⟨hdeg1, hu1⟩ :=
    branch_linear_above_three R hR (show (1 : ℕ) ≤ 1 by omega) (by simpa using hfix3) hdeg
      (by simpa using hAB) (by simpa using hcu)
  have hu1eq : ((u.coeff 1 : ↥(jetPrefixField C 3)) : JetField C Unit)
      = -(algebraMap C (JetField C Unit) ((4 : ℕ) : C) * jetOverOne 2) := by
    have := branch_linear_coefficient_eq R hR (show (1 : ℕ) ≤ 1 by omega)
      (by simpa using hfix3) hdeg (by simpa using hAB) (by simpa using hcu)
    simpa using this
  -- notation
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set ρ₁ : JetField C Unit := JetField.pd ((), 0) ρ with hρ₁def
  set ρ₂ : JetField C Unit := JetField.pd ((), 0) ρ₁ with hρ₂def
  set ρ₃ : JetField C Unit := JetField.pd ((), 0) ρ₂ with hρ₃def
  set y₁ : JetField C Unit := (JetField.jet ((), 1) : JetField C Unit) with hy₁def
  set y₂ : JetField C Unit := (JetField.jet ((), 2) : JetField C Unit) with hy₂def
  set y₃ : JetField C Unit := (JetField.jet ((), 3) : JetField C Unit) with hy₃def
  have hy1ne : y₁ ≠ 0 := jet_ne_zero _
  set w₀ : JetField C Unit := ((u.coeff 0 : ↥(jetPrefixField C (1 + 2))) : JetField C Unit)
    with hw₀def
  set w₁ : JetField C Unit := ((u.coeff 1 : ↥(jetPrefixField C (1 + 2))) : JetField C Unit)
    with hw₁def
  -- the coefficient relations
  have hu : u.natDegree ≤ 2 := by omega
  obtain ⟨-, -, E0raw⟩ := branch_coefficient_relations R hR 1 hu hcu
  have hw2 : ((u.coeff 2 : ↥(jetPrefixField C (1 + 2))) : JetField C Unit) = 0 := by
    have h2 : u.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h2]
    rfl
  have E0 : jetSubstitution R hR w₁ * substitutionShift R 3
      + jetSubstitution R hR w₀ = ρ * w₀ - ((B : ↥(jetPrefixField C (1 + 2))) : JetField C Unit)
      := by
    have hz : jetSubstitution R hR
        ((u.coeff 2 : ↥(jetPrefixField C (1 + 2))) : JetField C Unit) = 0 := by
      rw [hw2, map_zero]
    have E0' : jetSubstitution R hR
          ((u.coeff 2 : ↥(jetPrefixField C (1 + 2))) : JetField C Unit)
            * substitutionShift R 3 ^ 2
          + jetSubstitution R hR w₁ * substitutionShift R 3
          + jetSubstitution R hR w₀
        = ρ * w₀ - ((B : ↥(jetPrefixField C (1 + 2))) : JetField C Unit) := E0raw
    rw [hz, zero_mul, zero_add] at E0'
    exact E0'
  -- the shift terms
  have hσ₂ : substitutionShift R 2 = ρ₁ * y₁ ^ 2 := substitutionShift_two R
  have hσ₃ : substitutionShift R 3 = 3 * ρ₁ * y₁ * y₂ + ρ₂ * y₁ ^ 3 := substitutionShift_three R
  have hσ₄ : substitutionShift R 4
      = 4 * ρ₁ * y₁ * y₃ + 3 * ρ₁ * y₂ ^ 2 + 6 * ρ₂ * y₁ ^ 2 * y₂ + ρ₃ * y₁ ^ 4 :=
    substitutionShift_four R
  have hABn : substitutionShift R 4
      = ((A : ↥(jetPrefixField C (1 + 2))) : JetField C Unit) * y₃
        + ((B : ↥(jetPrefixField C (1 + 2))) : JetField C Unit) := hAB
  have hAval : ((A : ↥(jetPrefixField C (1 + 2))) : JetField C Unit)
      = ((4 : ℕ) : JetField C Unit) * (ρ₁ * y₁) := by
    have hpd : ((A : ↥(jetPrefixField C (1 + 2))) : JetField C Unit)
        = JetField.pd ((), 3) (substitutionShift R 4) := coe_eq_pd_top_of_affine R 1 hAB
    have htop : JetField.pd ((), 2 + 1) (substitutionShift R (2 + 2))
        = ((2 + 2 : ℕ) : JetField C Unit) * (ρ₁ * y₁) := pd_top_substitutionShift_eq R 2
    rw [hpd]
    exact htop
  have hBval : ((B : ↥(jetPrefixField C (1 + 2))) : JetField C Unit)
      = 3 * ρ₁ * y₂ ^ 2 + 6 * ρ₂ * y₁ ^ 2 * y₂ + ρ₃ * y₁ ^ 4 := by
    rw [hσ₄, hAval] at hABn
    push_cast at hABn
    linear_combination -hABn
  -- the substitution on the linear coefficient
  have hΦratio : jetSubstitution R hR (jetOverOne 2 : JetField C Unit) * (ρ * y₁)
      = ρ * y₂ + ρ₁ * y₁ ^ 2 := by
    have hj := jetSubstitution_jetOverOne R hR 2
    have hm : (jetOverOne 2 : JetField C Unit) * y₁ = y₂ := jetOverOne_mul 2
    rw [hσ₂] at hj
    linear_combination hj + ρ * hm
  have hΦw1 : jetSubstitution R hR w₁ * (ρ * y₁) = -(4 * (ρ * y₂ + ρ₁ * y₁ ^ 2)) := by
    rw [hu1eq, map_neg, map_mul, AlgHom.commutes]
    have hc4 : algebraMap C (JetField C Unit) ((4 : ℕ) : C) = (4 : JetField C Unit) := by
      rw [map_natCast]
      norm_num
    rw [hc4]
    linear_combination (-(4 : JetField C Unit)) * hΦratio
  -- the inhomogeneous polynomial in the second coordinate
  have hle2 : (1 : ℕ) ≤ 2 := by omega
  set p0 : ↥(jetPrefixField C 2) := substitutionDerivPrefix R hle2 with hp0def
  set p1 : ↥(jetPrefixField C 2) := substitutionDerivPrefix (ratFuncDeriv R) hle2 with hp1def
  set p2 : ↥(jetPrefixField C 2) :=
    substitutionDerivPrefix (ratFuncDeriv (ratFuncDeriv R)) hle2 with hp2def
  set p3 : ↥(jetPrefixField C 2) :=
    substitutionDerivPrefix (ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R))) hle2 with hp3def
  set Y1 : ↥(jetPrefixField C 2) := ⟨y₁, jet_mem_jetPrefixField (by omega)⟩ with hY1def
  have hι0 : algebraMap ↥(jetPrefixField C 2) (JetField C Unit) p0 = ρ := rfl
  have hι1 : algebraMap ↥(jetPrefixField C 2) (JetField C Unit) p1 = ρ₁ :=
    substitutionDeriv_ratFuncDeriv R
  have hι2 : algebraMap ↥(jetPrefixField C 2) (JetField C Unit) p2 = ρ₂ := by
    show substitutionDeriv (ratFuncDeriv (ratFuncDeriv R)) = ρ₂
    rw [substitutionDeriv_ratFuncDeriv (ratFuncDeriv R), substitutionDeriv_ratFuncDeriv R]
  have hι3 : algebraMap ↥(jetPrefixField C 2) (JetField C Unit) p3 = ρ₃ := by
    show substitutionDeriv (ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R))) = ρ₃
    rw [substitutionDeriv_ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R)),
      substitutionDeriv_ratFuncDeriv (ratFuncDeriv R), substitutionDeriv_ratFuncDeriv R]
  have hιY : algebraMap ↥(jetPrefixField C 2) (JetField C Unit) Y1 = y₁ := rfl
  set S : Polynomial ↥(jetPrefixField C 2) :=
    Polynomial.C (-(9 * p1)) * Polynomial.X ^ 2
      + Polynomial.C ((2 * p2 - 12 * p1 ^ 2 / p0) * Y1 ^ 2) * Polynomial.X
      + Polynomial.C ((p3 - 4 * p1 * p2 / p0) * Y1 ^ 4) with hSdef
  have haevalS : Polynomial.aeval y₂ S
      = -(9 * ρ₁) * y₂ ^ 2 + (2 * ρ₂ - 12 * ρ₁ ^ 2 / ρ) * y₁ ^ 2 * y₂
        + (ρ₃ - 4 * ρ₁ * ρ₂ / ρ) * y₁ ^ 4 := by
    rw [hSdef]
    simp only [map_add, map_mul, map_pow, map_sub, map_div₀, map_neg, map_ofNat,
      Polynomial.aeval_C, Polynomial.aeval_X, hι0, hι1, hι2, hι3, hιY]
  -- the relation satisfied by the constant coefficient
  have hE0 : jetSubstitution R hR w₁ * (3 * ρ₁ * y₁ * y₂ + ρ₂ * y₁ ^ 3)
      + jetSubstitution R hR w₀
      = ρ * w₀ - (3 * ρ₁ * y₂ ^ 2 + 6 * ρ₂ * y₁ ^ 2 * y₂ + ρ₃ * y₁ ^ 4) := by
    rw [hσ₃, hBval] at E0
    exact E0
  have hrel : jetSubstitution R hR w₀ = ρ * w₀ - Polynomial.aeval y₂ S := by
    refine mul_right_cancel₀ (mul_ne_zero hR hy1ne) ?_
    have key : jetSubstitution R hR w₀ * (ρ * y₁)
        = ρ * w₀ * (ρ * y₁)
          - ((3 * ρ₁ * y₂ ^ 2 + 6 * ρ₂ * y₁ ^ 2 * y₂ + ρ₃ * y₁ ^ 4) * (ρ * y₁)
            - 4 * (ρ * y₂ + ρ₁ * y₁ ^ 2) * (3 * ρ₁ * y₁ * y₂ + ρ₂ * y₁ ^ 3)) := by
      linear_combination (ρ * y₁) * hE0 - (3 * ρ₁ * y₁ * y₂ + ρ₂ * y₁ ^ 3) * hΦw1
    have hWS : Polynomial.aeval y₂ S * (ρ * y₁)
        = (3 * ρ₁ * y₂ ^ 2 + 6 * ρ₂ * y₁ ^ 2 * y₂ + ρ₃ * y₁ ^ 4) * (ρ * y₁)
          - 4 * (ρ * y₂ + ρ₁ * y₁ ^ 2) * (3 * ρ₁ * y₁ * y₂ + ρ₂ * y₁ ^ 3) := by
      rw [haevalS]
      field_simp
      ring
    rw [sub_mul]
    linear_combination key + hWS
  -- slice the constant coefficient in the second coordinate
  have hw₀ord : ∀ j : ℕ, 0 + 2 < j → JetField.pd ((), j) w₀ = 0 := by
    intro j hj
    exact (mem_jetPrefixField_iff (1 + 2) _).mp (u.coeff 0).2 j (by omega)
  rcases hasNormalizingShift_or_polynomial_of_relation R hR 0 hw₀ord S hrel with hsh2 | hpoly
  · exact Or.inl hsh2
  obtain ⟨v, -, hvcu⟩ := hpoly
  rw [substitutionAffine] at hvcu
  have hSdeg : S.natDegree ≤ 2 := by
    rw [hSdef]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X]
        omega
    · rw [Polynomial.natDegree_C]
      omega
  have hρF : substitutionDerivPrefix R hle2 ≠ 0 := substitutionDerivPrefix_ne_zero R hR hle2
  by_cases hvd : 4 ≤ v.natDegree
  · obtain ⟨a, hadef⟩ : ∃ a : ℕ, v.natDegree = a + 1 := ⟨v.natDegree - 1, by omega⟩
    obtain ⟨t, ht⟩ := exists_cocycle_of_shift_polynomial_lt
      (jetSubstitutionPrefix R hR 2).toRingHom hρF hadef (by omega) (by omega) hvcu
    exact Or.inl ⟨t, ht⟩
  rw [not_le] at hvd
  refine Or.inr ?_
  obtain ⟨F3, F2, F1, -⟩ := coeff_eqs_of_twistComp_affine_deg_le_three
    (jetSubstitutionPrefix R hR 2).toRingHom (substitutionDerivPrefix R hle2)
    (substitutionShiftPrefix R hle2) (substitutionDerivPrefix R hle2) (by omega) hvcu
  -- push the coefficient relations to the jet field
  set ι2 := algebraMap ↥(jetPrefixField C 2) (JetField C Unit) with hι2def
  have hΦι : ∀ z : ↥(jetPrefixField C 2),
      ι2 ((jetSubstitutionPrefix R hR 2).toRingHom z) = jetSubstitution R hR (ι2 z) :=
    fun _ => rfl
  have hρι : ι2 (substitutionDerivPrefix R hle2) = ρ := rfl
  have hsι : ι2 (substitutionShiftPrefix R hle2) = ρ₁ * y₁ ^ 2 := hσ₂
  have hS3 : S.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hS2 : ι2 (S.coeff 2) = -(9 * ρ₁) := by
    have hc : S.coeff 2 = -(9 * p1) := by
      rw [hSdef]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X]
      norm_num
    rw [hc]
    simp only [map_neg, map_mul, map_ofNat, hι1]
  have hS1 : ι2 (S.coeff 1) = (2 * ρ₂ - 12 * ρ₁ ^ 2 / ρ) * y₁ ^ 2 := by
    have hc : S.coeff 1 = (2 * p2 - 12 * p1 ^ 2 / p0) * Y1 ^ 2 := by
      rw [hSdef]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_C, Polynomial.coeff_X]
      norm_num
    rw [hc]
    simp only [map_mul, map_sub, map_div₀, map_pow, map_ofNat, hι0, hι1, hι2, hιY]
  set C3 : JetField C Unit := ι2 (v.coeff 3) with hC3def
  set C2 : JetField C Unit := ι2 (v.coeff 2) with hC2def
  set C1 : JetField C Unit := ι2 (v.coeff 1) with hC1def
  have hvord : ∀ (z : ↥(jetPrefixField C 2)) (j : ℕ), 1 < j → JetField.pd ((), j) (ι2 z) = 0 := by
    intro z j hj
    exact (mem_jetPrefixField_iff 2 _).mp z.2 j (by omega)
  have G3 : jetSubstitution R hR C3 * ρ ^ 3 = ρ * C3 := by
    have hc := congrArg ι2 F3
    simp only [map_mul, map_pow, hΦι, hρι, hS3, sub_zero] at hc
    exact hc
  have G2 : jetSubstitution R hR C3 * (3 * ρ ^ 2 * (ρ₁ * y₁ ^ 2))
      + jetSubstitution R hR C2 * ρ ^ 2 = ρ * C2 + 9 * ρ₁ := by
    have hc := congrArg ι2 F2
    simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, hΦι, hρι, hsι, hS2] at hc
    linear_combination hc
  have G1 : jetSubstitution R hR C3 * (3 * ρ * (ρ₁ * y₁ ^ 2) ^ 2)
      + jetSubstitution R hR C2 * (2 * ρ * (ρ₁ * y₁ ^ 2))
      + jetSubstitution R hR C1 * ρ
      = ρ * C1 - (2 * ρ₂ - 12 * ρ₁ ^ 2 / ρ) * y₁ ^ 2 := by
    have hc := congrArg ι2 F1
    simp only [map_mul, map_pow, map_sub, map_add, map_ofNat, hΦι, hρι, hsι, hS1] at hc
    linear_combination hc
  -- the cubic coefficient is a constant multiple of `y₁⁻²`
  have hC3eig : jetSubstitution R hR C3 * ρ ^ 2 = C3 := by
    refine mul_left_cancel₀ hR ?_
    linear_combination G3
  obtain ⟨a₃, ha₃⟩ := exists_const_of_scaling_eigen_pow R hR (Kb := 2) (j := 2) (by omega)
    hfix2 (n := 1) (by omega) (hvord (v.coeff 3)) hC3eig
  -- the quadratic coefficient
  have hC2rel : jetSubstitution R hR C2 * ρ ^ 2
      = ρ * C2 - (3 * algebraMap C (JetField C Unit) a₃ - 9) * ρ₁ := by
    linear_combination G2 - 3 * ρ₁ * y₁ ^ 2 * hC3eig - 3 * ρ₁ * ha₃
  set q0 : ↥(jetPrefixField C 1) := substitutionDerivPrefix R (le_refl 1) with hq0def
  set q1 : ↥(jetPrefixField C 1) := substitutionDerivPrefix (ratFuncDeriv R) (le_refl 1)
    with hq1def
  set q2 : ↥(jetPrefixField C 1) :=
    substitutionDerivPrefix (ratFuncDeriv (ratFuncDeriv R)) (le_refl 1) with hq2def
  have hj0 : algebraMap ↥(jetPrefixField C 1) (JetField C Unit) q0 = ρ := rfl
  have hj1 : algebraMap ↥(jetPrefixField C 1) (JetField C Unit) q1 = ρ₁ :=
    substitutionDeriv_ratFuncDeriv R
  have hj2 : algebraMap ↥(jetPrefixField C 1) (JetField C Unit) q2 = ρ₂ := by
    show substitutionDeriv (ratFuncDeriv (ratFuncDeriv R)) = ρ₂
    rw [substitutionDeriv_ratFuncDeriv (ratFuncDeriv R), substitutionDeriv_ratFuncDeriv R]
  have hev : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
      (ratFuncDeriv (ratFuncDeriv R)) = ρ₁ := by
    rw [ratFuncEval_ratFuncDeriv]
    exact substitutionDeriv_ratFuncDeriv R
  have hev2 : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
      (ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R))) = ρ₂ := by
    rw [ratFuncEval_ratFuncDeriv]
    show substitutionDeriv (ratFuncDeriv (ratFuncDeriv R)) = ρ₂
    rw [substitutionDeriv_ratFuncDeriv (ratFuncDeriv R), substitutionDeriv_ratFuncDeriv R]
  have hev0 : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
      (ratFuncDeriv R) = ρ := ratFuncEval_ratFuncDeriv R
  by_cases ha3 : a₃ = 3
  · -- the linear coefficient produces the transport of exponent three
    have ha₃' : C3 * y₁ ^ 2 = 3 := by
      rw [ha₃, ha3, map_ofNat]
    have hC2eig : jetSubstitution R hR C2 * ρ ^ 1 = C2 := by
      rw [pow_one]
      refine mul_left_cancel₀ hR ?_
      have h9 : (3 : JetField C Unit) * algebraMap C (JetField C Unit) a₃ - 9 = 0 := by
        rw [ha3, map_ofNat]
        ring
      linear_combination hC2rel - ρ₁ * h9
    obtain ⟨κ, hκ⟩ := exists_const_of_scaling_eigen_pow R hR (Kb := 2) (j := 1) (by omega)
      hfix2 (n := 1) (by omega) (hvord (v.coeff 2)) hC2eig
    have hT3 : jetSubstitution R hR C3 * (3 * ρ * (ρ₁ * y₁ ^ 2) ^ 2) * ρ
        = 9 * ρ₁ ^ 2 * y₁ ^ 2 := by
      linear_combination (3 * ρ₁ ^ 2 * y₁ ^ 4) * hC3eig + (3 * ρ₁ ^ 2 * y₁ ^ 2) * ha₃'
    have hT2 : jetSubstitution R hR C2 * (2 * ρ * (ρ₁ * y₁ ^ 2)) * ρ
        = 2 * algebraMap C (JetField C Unit) κ * ρ₁ * y₁ * ρ := by
      linear_combination (2 * ρ₁ * y₁ ^ 2 * ρ) * hC2eig + (2 * ρ₁ * y₁ * ρ) * hκ
    set Sb : Polynomial ↥(jetPrefixField C 1) :=
      Polynomial.C (2 * q2 - 3 * q1 ^ 2 / q0) * Polynomial.X ^ 2
        + Polynomial.C (2 * algebraMap C ↥(jetPrefixField C 1) κ * q1) * Polynomial.X
      with hSbdef
    have hSbdeg : Sb.natDegree ≤ 2 := by
      rw [hSbdef]
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X_pow]
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X]
        omega
    have hSbc : Sb.coeff 2 = 2 * q2 - 3 * q1 ^ 2 / q0 := by
      rw [hSbdef]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_X]
      norm_num
    have haevalSb : Polynomial.aeval y₁ Sb
        = (2 * ρ₂ - 3 * ρ₁ ^ 2 / ρ) * y₁ ^ 2
          + 2 * algebraMap C (JetField C Unit) κ * ρ₁ * y₁ := by
      rw [hSbdef]
      simp only [map_add, map_mul, map_pow, map_sub, map_div₀, map_ofNat,
        Polynomial.aeval_C, Polynomial.aeval_X, hj0, hj1, hj2]
      rw [← IsScalarTower.algebraMap_apply]
    have hC1rel : jetSubstitution R hR C1 * ρ ^ 1 = ρ * C1 - Polynomial.aeval y₁ Sb := by
      rw [haevalSb, pow_one]
      refine mul_right_cancel₀ hR ?_
      have hW1 : ((2 * ρ₂ - 3 * ρ₁ ^ 2 / ρ) * y₁ ^ 2
            + 2 * algebraMap C (JetField C Unit) κ * ρ₁ * y₁) * ρ
          = (2 * ρ₂ * ρ - 3 * ρ₁ ^ 2) * y₁ ^ 2
            + 2 * algebraMap C (JetField C Unit) κ * ρ₁ * y₁ * ρ := by
        field_simp
      have hW2 : (2 * ρ₂ - 12 * ρ₁ ^ 2 / ρ) * y₁ ^ 2 * ρ
          = (2 * ρ₂ * ρ - 12 * ρ₁ ^ 2) * y₁ ^ 2 := by
        field_simp
      rw [sub_mul, hW1]
      linear_combination ρ * G1 - hT3 - hT2 - hW2
    have hDb : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
        (2 * ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R))
          - RatFunc.C (3 : C) * ratFuncDeriv (ratFuncDeriv R) ^ 2 / ratFuncDeriv R)
        = algebraMap ↥(jetPrefixField C 1) (JetField C Unit) (Sb.coeff 2) := by
      rw [hSbc]
      simp only [map_sub, map_mul, map_div₀, map_pow, map_ofNat, hj0, hj1, hj2, hev, hev2, hev0]
    obtain ⟨α, hα⟩ := exists_ratFunc_affineTransport_of_order_one R hR (hvord (v.coeff 1))
      hSbdeg hC1rel hDb
    exact Or.inr ⟨α, by simpa using hα⟩
  · -- the quadratic coefficient produces a scaled affine connection
    refine Or.inl ⟨3 * a₃ - 9, ?_⟩
    set Sa : Polynomial ↥(jetPrefixField C 1) :=
      Polynomial.C ((3 * algebraMap C ↥(jetPrefixField C 1) a₃ - 9) * q1) with hSadef
    have hSadeg : Sa.natDegree ≤ 0 := by rw [hSadef, Polynomial.natDegree_C]
    have hSac : Sa.coeff 0 = (3 * algebraMap C ↥(jetPrefixField C 1) a₃ - 9) * q1 := by
      rw [hSadef, Polynomial.coeff_C_zero]
    have haevalSa : Polynomial.aeval y₁ Sa
        = (3 * algebraMap C (JetField C Unit) a₃ - 9) * ρ₁ := by
      rw [hSadef, Polynomial.aeval_C]
      simp only [map_mul, map_sub, map_ofNat, hj1]
      rw [← IsScalarTower.algebraMap_apply]
    have hC2rel' : jetSubstitution R hR C2 * ρ ^ 2 = ρ * C2 - Polynomial.aeval y₁ Sa := by
      rw [haevalSa]
      exact hC2rel
    have hDa : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen
        (RatFunc.C (3 * a₃ - 9) * ratFuncDeriv (ratFuncDeriv R))
        = algebraMap ↥(jetPrefixField C 1) (JetField C Unit) (Sa.coeff 0) := by
      rw [hSac]
      simp only [map_mul, map_sub, map_ofNat, hj1, hev, ratFuncEval_C,
        ← IsScalarTower.algebraMap_apply]
    obtain ⟨α, hα⟩ := exists_ratFunc_affineTransport_of_order_one R hR (hvord (v.coeff 2))
      hSadeg hC2rel' hDa
    refine ⟨α, ?_, ?_⟩
    · intro hh
      refine ha3 ?_
      have h3 : (3 : C) * a₃ = 3 * 3 := by linear_combination hh
      exact mul_left_cancel₀ (by norm_num : (3 : C) ≠ 0) h3
    · simpa using hα

end

end GaloisForLFunctions.HTGeometry
