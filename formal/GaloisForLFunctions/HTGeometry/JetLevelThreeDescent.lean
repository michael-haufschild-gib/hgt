import GaloisForLFunctions.HTGeometry.JetOrderOneSlicing
import GaloisForLFunctions.HTGeometry.QuadraticShiftDescentBranches

/-!
# The jet descent at level three

The shift term at level three is `σ₃ = 3·R''·y₁·y₂ + R'''·y₁³`, and the slicing of a normalizing
shift at that level leaves a polynomial of degree one or two in `y₂` over the field of order at most
one.  Comparing coefficients turns the relation into three equations.

The coefficient of `y₂` in either degree has the shape `Φ(w) = w − κ·R''·y₁/R'` with `κ` a scalar,
and `w + κ·y₂/y₁` is then a fixed element of order at most two; when those are constant the partial
in `y₂` forces `κ = 0`.  In degree one `κ = 3`, which is impossible; in degree two `κ = 3 + 2e` where
`e·y₁⁻¹` is the leading coefficient, so `e = −3/2` and the linear coefficient is a constant.

The constant coefficient then satisfies an inhomogeneous relation of order one whose inhomogeneous
polynomial has degree three in `y₁` with top coefficient `R''' − (3/2)·(R'')²/R'`, and slicing it
produces a rational affine transport of exponent three with that inhomogeneous term.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-! ## The shift term at level three -/

/-- **The shift term at level three.** -/
theorem substitutionShift_three (R : RatFunc C) :
    substitutionShift R 3
      = 3 * JetField.pd ((), 0) (substitutionDeriv R)
          * (JetField.jet ((), 1) : JetField C Unit) * (JetField.jet ((), 2) : JetField C Unit)
        + JetField.pd ((), 0) (JetField.pd ((), 0) (substitutionDeriv R))
          * (JetField.jet ((), 1) : JetField C Unit) ^ 3 := by
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set ρ₁ : JetField C Unit := JetField.pd ((), 0) ρ with hρ₁def
  set ρ₂ : JetField C Unit := JetField.pd ((), 0) ρ₁ with hρ₂def
  set δ := (JetField.jetDerivation : Derivation C (JetField C Unit) (JetField C Unit)) with hδdef
  have hjet : substitutionJet R 3 = δ (substitutionJet R 2) := by
    rw [substitutionJet, substitutionJet, show (3 : ℕ) = 2 + 1 from rfl, differentialJet_succ,
      JetField.deriv_eq, hδdef]
  have haff2 : substitutionJet R 2 = ρ * (JetField.jet ((), 2) : JetField C Unit)
      + ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2 := by
    rw [substitutionJet_eq_affine R 2, substitutionShift_two, hρdef, hρ₁def]
  have hδρ : δ ρ = (JetField.jet ((), 1) : JetField C Unit) * ρ₁ :=
    jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)
  have hδρ₁ : δ ρ₁ = (JetField.jet ((), 1) : JetField C Unit) * ρ₂ := by
    refine jetDerivation_of_order_zero (fun k hk => ?_)
    rw [hρ₁def, pd_comm, pd_substitutionDeriv_eq_zero R hk, map_zero]
  have hδ1 : δ (JetField.jet ((), 1) : JetField C Unit) = JetField.jet ((), 2) := by
    rw [hδdef]; exact JetField.jetDerivation_jet ((), 1)
  have hδ2 : δ (JetField.jet ((), 2) : JetField C Unit) = JetField.jet ((), 3) := by
    rw [hδdef]; exact JetField.jetDerivation_jet ((), 2)
  have hL1 : δ (ρ * (JetField.jet ((), 2) : JetField C Unit))
      = δ ρ * (JetField.jet ((), 2) : JetField C Unit) + ρ * δ (JetField.jet ((), 2)) := by
    have h := δ.leibniz ρ (JetField.jet ((), 2) : JetField C Unit)
    simp only [smul_eq_mul] at h
    rw [h]; ring
  have hsq : δ ((JetField.jet ((), 1) : JetField C Unit) ^ 2)
      = 2 * (JetField.jet ((), 1) : JetField C Unit) * δ (JetField.jet ((), 1)) := by
    have h := δ.leibniz (JetField.jet ((), 1) : JetField C Unit)
      (JetField.jet ((), 1) : JetField C Unit)
    simp only [smul_eq_mul] at h
    rw [pow_two, h]; ring
  have hL2 : δ (ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2)
      = δ ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2
        + ρ₁ * δ ((JetField.jet ((), 1) : JetField C Unit) ^ 2) := by
    have h := δ.leibniz ρ₁ ((JetField.jet ((), 1) : JetField C Unit) ^ 2)
    simp only [smul_eq_mul] at h
    rw [h]; ring
  rw [substitutionShift, hjet, haff2, map_add, hL1, hL2, hsq, hδρ, hδρ₁, hδ1, hδ2]
  ring

/-! ## Two coefficient extractions -/

variable {K : Type*} [Field K]

omit [Field C] [CharZero C] in
theorem eq_quadratic_of_natDegree_le_two {u : Polynomial K} (hu : u.natDegree ≤ 2) :
    u = Polynomial.C (u.coeff 2) * Polynomial.X ^ 2 + Polynomial.C (u.coeff 1) * Polynomial.X
      + Polynomial.C (u.coeff 0) := by
  ext n
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Polynomial.coeff_X]
  match n with
  | 0 => norm_num
  | 1 => norm_num
  | 2 => norm_num
  | (k + 3) =>
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      norm_num
      exact fun hh => absurd hh (by omega)

omit [Field C] [CharZero C] in
/-- **The three coefficient equations of a twisted affine relation in degree at most two.** -/
theorem coeff_eqs_of_twistComp_affine_deg_le_two (Φ : K →+* K) (ρ s c A B : K)
    {u : Polynomial K} (hu : u.natDegree ≤ 2)
    (hcu : twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C s) u
      = Polynomial.C c * u - (Polynomial.C A * Polynomial.X + Polynomial.C B)) :
    Φ (u.coeff 2) * ρ ^ 2 = c * u.coeff 2
      ∧ Φ (u.coeff 2) * (2 * ρ * s) + Φ (u.coeff 1) * ρ = c * u.coeff 1 - A
      ∧ Φ (u.coeff 2) * s ^ 2 + Φ (u.coeff 1) * s + Φ (u.coeff 0) = c * u.coeff 0 - B := by
  set T : Polynomial K := Polynomial.C ρ * Polynomial.X + Polynomial.C s with hTdef
  have hexp : twistComp Φ T u
      = Polynomial.C (Φ (u.coeff 2)) * T ^ 2 + Polynomial.C (Φ (u.coeff 1)) * T
        + Polynomial.C (Φ (u.coeff 0)) := by
    conv_lhs => rw [eq_quadratic_of_natDegree_le_two hu]
    rw [twistComp_add, twistComp_add, twistComp_C_mul_X_pow]
    congr 1
    · congr 1
      have h1 : Polynomial.C (u.coeff 1) * Polynomial.X
          = Polynomial.C (u.coeff 1) * Polynomial.X ^ 1 := by rw [pow_one]
      rw [h1, twistComp_C_mul_X_pow, pow_one]
    · exact twistComp_C Φ T (u.coeff 0)
  have hTsq : T ^ 2 = Polynomial.C (ρ ^ 2) * Polynomial.X ^ 2
      + Polynomial.C (2 * ρ * s) * Polynomial.X + Polynomial.C (s ^ 2) := by
    rw [hTdef]
    simp only [map_pow, map_mul, map_ofNat]
    ring
  rw [hexp, hTsq, hTdef] at hcu
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (fun p : Polynomial K => p.coeff 2) hcu
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination h
  · have h := congrArg (fun p : Polynomial K => p.coeff 1) hcu
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination h
  · have h := congrArg (fun p : Polynomial K => p.coeff 0) hcu
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at h
    norm_num at h
    linear_combination h

end

/-! ## The two structural lemmas of the level-three slice -/

section Structural

variable {C : Type*} [Field C] [CharZero C]

/-- The weight-zero ratio of the second and first jet coordinates. -/
private noncomputable def ratioTwo : JetField C Unit :=
  (JetField.jet ((), 2) : JetField C Unit) / (JetField.jet ((), 1) : JetField C Unit)

omit [CharZero C] in
private theorem pd_ratioTwo_mul {j : ℕ} (hj : j ≠ 1) :
    JetField.pd ((), j) (ratioTwo : JetField C Unit)
        * (JetField.jet ((), 1) : JetField C Unit)
      = JetField.pd ((), j) (JetField.jet ((), 2) : JetField C Unit) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hmul : (ratioTwo : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit)
      = (JetField.jet ((), 2) : JetField C Unit) := div_mul_cancel₀ _ hy1
  have hleib := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (ratioTwo : JetField C Unit) (JetField.jet ((), 1) : JetField C Unit)
  simp only [smul_eq_mul] at hleib
  rw [hmul] at hleib
  rw [hleib, JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)]
  ring

omit [CharZero C] in
private theorem pd_ratioTwo_two :
    JetField.pd ((), 2) (ratioTwo : JetField C Unit)
      = 1 / (JetField.jet ((), 1) : JetField C Unit) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_ratioTwo_mul (C := C) (j := 2) (by omega)
  rw [JetField.pd_jet_self] at h
  field_simp
  linear_combination h

omit [CharZero C] in
private theorem pd_ratioTwo_high {j : ℕ} (hj : 2 < j) :
    JetField.pd ((), j) (ratioTwo : JetField C Unit) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_ratioTwo_mul (C := C) (j := j) (by omega)
  rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at h
  exact (mul_eq_zero.mp h).resolve_right hy1

/-- **The linear obstruction of the level-three slice.**  A relation `Φ(w)·R' = R'·w − κ·R''·y₁`
with `w` of order at most one forces the scalar to vanish and `w` to be constant, as soon as fixed
elements of order at most two are constant. -/
theorem eq_zero_of_linear_shift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hw : ∀ j : ℕ, 1 < j → JetField.pd ((), j) w = 0) (κ : C)
    (heq : jetSubstitution R hR w * substitutionDeriv R
      = substitutionDeriv R * w
        - algebraMap C (JetField C Unit) κ * JetField.pd ((), 0) (substitutionDeriv R)
          * (JetField.jet ((), 1) : JetField C Unit)) :
    κ = 0 ∧ ∃ e : C, w = algebraMap C (JetField C Unit) e := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set ρ₁ : JetField C Unit := JetField.pd ((), 0) ρ with hρ₁def
  set κJ : JetField C Unit := algebraMap C (JetField C Unit) κ with hκdef
  set g : JetField C Unit := w + κJ * ratioTwo with hgdef
  have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
      = (JetField.jet ((), 1) : JetField C Unit) * ρ := by
    rw [jetSubstitution_jet, substitutionJet_one]
  have hΦ2 : jetSubstitution R hR (JetField.jet ((), 2) : JetField C Unit)
      = ρ * (JetField.jet ((), 2) : JetField C Unit)
        + ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2 := by
    rw [jetSubstitution_jet, substitutionJet_eq_affine, substitutionShift_two]
  have hΦratio : jetSubstitution R hR (ratioTwo : JetField C Unit)
      = ratioTwo + ρ₁ * (JetField.jet ((), 1) : JetField C Unit) / ρ := by
    rw [ratioTwo, map_div₀, hΦ1, hΦ2]
    field_simp
  have hgfix : jetSubstitution R hR g = g := by
    have hΦw : jetSubstitution R hR w = w - κJ * ρ₁ * (JetField.jet ((), 1) : JetField C Unit) / ρ
        := by
      field_simp
      linear_combination heq
    rw [hgdef, map_add, map_mul, hΦw, AlgHom.commutes, hΦratio]
    field_simp
    ring
  have hgord : ∀ j : ℕ, 2 < j → JetField.pd ((), j) g = 0 := by
    intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz κJ
        (ratioTwo : JetField C Unit)
    simp only [smul_eq_mul] at hleib
    have hκ0 : JetField.pd ((), j) κJ = 0 := by
      rw [hκdef, Derivation.map_algebraMap]
    rw [hgdef, map_add, hw j (by omega), hleib, hκ0, pd_ratioTwo_high hj]
    ring
  obtain ⟨e, he⟩ := hfix g hgord hgfix
  have hpd2 : JetField.pd ((), 2) g = 0 := by
    rw [he, Derivation.map_algebraMap]
  have hleib2 := (JetField.pd ((), 2) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz κJ (ratioTwo : JetField C Unit)
  simp only [smul_eq_mul] at hleib2
  have hκ02 : JetField.pd ((), 2) κJ = 0 := by rw [hκdef, Derivation.map_algebraMap]
  rw [hgdef, map_add, hw 2 (by omega), hleib2, hκ02, pd_ratioTwo_two] at hpd2
  have hκJ0 : κJ = 0 := by
    have hz : κJ * (1 / (JetField.jet ((), 1) : JetField C Unit)) = 0 := by
      linear_combination hpd2
    field_simp at hz
    simpa using hz
  have hκ : κ = 0 := by
    rw [hκdef] at hκJ0
    exact (algebraMap C (JetField C Unit)).injective (by rw [hκJ0, map_zero])
  refine ⟨hκ, e, ?_⟩
  rw [← he, hgdef, hκJ0, zero_mul, add_zero]

/-- **The leading obstruction of the level-three slice.**  A relation `Φ(w)·R' = w` with `w` of
order at most one forces `w·y₁` to be constant. -/
theorem exists_const_of_scaling_eigen (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hw : ∀ j : ℕ, 1 < j → JetField.pd ((), j) w = 0)
    (heq : jetSubstitution R hR w * substitutionDeriv R = w) :
    ∃ e : C, w * (JetField.jet ((), 1) : JetField C Unit)
      = algebraMap C (JetField C Unit) e := by
  refine hfix (w * (JetField.jet ((), 1) : JetField C Unit)) (fun j hj => ?_) ?_
  · have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz w
        (JetField.jet ((), 1) : JetField C Unit)
    simp only [smul_eq_mul] at hleib
    rw [hleib, hw j (by omega),
      JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)]
    ring
  · have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
        = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
      rw [jetSubstitution_jet, substitutionJet_one]
    rw [map_mul, hΦ1]
    linear_combination (JetField.jet ((), 1) : JetField C Unit) * heq

end Structural



/-! ## The level-three descent -/

section LevelThree

variable {C : Type*} [Field C] [CharZero C]

/-- **The level-three descent.**  When fixed elements of order at most two are constant, a
normalizing shift at jet level three either descends to level two, or produces a rational affine
transport of exponent three whose inhomogeneous term is the Schwarzian-type combination
`R''' - (3/2)*(R'')^2/R'`. -/
theorem hasNormalizingShift_two_or_affineTransport_three (R : RatFunc C)
    (hR : substitutionDeriv R ≠ 0)
    (hR2 : JetField.pd ((), 0) (substitutionDeriv R) ≠ 0)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    (h : HasNormalizingShift R hR (show (1 : ℕ) ≤ 3 by omega)) :
    HasNormalizingShift R hR (show (1 : ℕ) ≤ 2 by omega)
      ∨ ∃ a : RatFunc C,
          ratFuncSubstitutionAlgHom R (not_isConst_of_substitutionDeriv_ne_zero hR) a
              * ratFuncDeriv R ^ 3
            = ratFuncDeriv R * a
              - (ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R))
                - RatFunc.C (3 / 2 : C) * ratFuncDeriv (ratFuncDeriv R) ^ 2 / ratFuncDeriv R) := by
  classical
  rcases hasNormalizingShift_pred_or_low_degree R hR hR2 0 h with hpred | ⟨u, A, B, hdeg, hAB, hcu⟩
  · exact Or.inl hpred
  refine Or.inr ?_
  set h2 : (1 : ℕ) ≤ 2 := by omega
  set ι := algebraMap ↥(jetPrefixField C 2) (JetField C Unit) with hιdef
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  set ρ₁ : JetField C Unit := JetField.pd ((), 0) ρ with hρ₁def
  set ρ₂ : JetField C Unit := JetField.pd ((), 0) ρ₁ with hρ₂def
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hAval : (A : JetField C Unit) = 3 * (ρ₁ * (JetField.jet ((), 1) : JetField C Unit)) := by
    rw [coe_eq_pd_top_of_affine R 0 hAB, show (0 : ℕ) + 2 = 1 + 1 from rfl,
      show (0 : ℕ) + 3 = 1 + 2 from rfl, pd_top_substitutionShift_eq R 1]
    push_cast
    ring
  have hBval : (B : JetField C Unit) = ρ₂ * (JetField.jet ((), 1) : JetField C Unit) ^ 3 := by
    have h3 := substitutionShift_three R
    rw [hAB, hAval] at h3
    linear_combination h3
  rw [substitutionAffine] at hcu
  have hu : u.natDegree ≤ 2 := by rcases hdeg with hd | hd <;> omega
  obtain ⟨e2, e1, e0⟩ := coeff_eqs_of_twistComp_affine_deg_le_two
    (jetSubstitutionPrefix R hR 2).toRingHom (substitutionDerivPrefix R h2)
    (substitutionShiftPrefix R h2) (substitutionDerivPrefix R h2) A B hu hcu
  set w2 : JetField C Unit := ι (u.coeff 2) with hw2def
  set w1 : JetField C Unit := ι (u.coeff 1) with hw1def
  set w0 : JetField C Unit := ι (u.coeff 0) with hw0def
  have hσ2 : ι (substitutionShiftPrefix R h2)
      = ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2 := substitutionShift_two R
  have hρι : ι (substitutionDerivPrefix R h2) = ρ := rfl
  have hΦι : ∀ z : ↥(jetPrefixField C 2),
      ι ((jetSubstitutionPrefix R hR 2).toRingHom z) = jetSubstitution R hR (ι z) :=
    fun _ => rfl
  have hE2 : jetSubstitution R hR w2 * ρ ^ 2 = ρ * w2 := by
    have hc := congrArg ι e2
    simpa only [map_mul, map_pow, hΦι, hρι] using hc
  have hE1 : jetSubstitution R hR w2 * (2 * ρ * (ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2))
      + jetSubstitution R hR w1 * ρ = ρ * w1 - (A : JetField C Unit) := by
    have hc := congrArg ι e1
    simp only [map_mul, map_add, map_sub, map_ofNat, hΦι, hρι, hσ2] at hc
    exact hc
  have hE0 : jetSubstitution R hR w2 * (ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2) ^ 2
      + jetSubstitution R hR w1 * (ρ₁ * (JetField.jet ((), 1) : JetField C Unit) ^ 2)
      + jetSubstitution R hR w0 = ρ * w0 - (B : JetField C Unit) := by
    have hc := congrArg ι e0
    simp only [map_mul, map_add, map_sub, map_pow, hΦι, hρι, hσ2] at hc
    exact hc
  have hord : ∀ (z : ↥(jetPrefixField C 2)) (j : ℕ), 1 < j → JetField.pd ((), j) (ι z) = 0 := by
    intro z j hj
    exact (mem_jetPrefixField_iff 2 _).mp z.2 j (by omega)
  rw [hAval] at hE1
  rw [hBval] at hE0
  set y : JetField C Unit := (JetField.jet ((), 1) : JetField C Unit) with hydef
  -- the leading coefficient is a constant over the first jet coordinate
  have hw2eig : jetSubstitution R hR w2 * ρ = w2 := by
    refine mul_left_cancel₀ hR ?_
    linear_combination hE2
  obtain ⟨e, he⟩ := exists_const_of_scaling_eigen R hR hfix (hord (u.coeff 2)) hw2eig
  rw [← hw2def, ← hydef] at he
  -- the linear coefficient
  have hE1' : jetSubstitution R hR w1 * ρ
      = ρ * w1 - algebraMap C (JetField C Unit) (3 + 2 * e) * ρ₁ * y := by
    have hmap : algebraMap C (JetField C Unit) (3 + 2 * e)
        = 3 + 2 * algebraMap C (JetField C Unit) e := by
      rw [map_add, map_mul, map_ofNat, map_ofNat]
    rw [hmap]
    linear_combination hE1 - 2 * ρ₁ * y ^ 2 * hw2eig - 2 * ρ₁ * y * he
  obtain ⟨hκ, k, hk⟩ := eq_zero_of_linear_shift R hR hfix (hord (u.coeff 1)) (3 + 2 * e) hE1'
  rw [← hw1def] at hk
  have he2 : (2 : C) * e = -3 := by linear_combination hκ
  have hEc : e = -(3 / 2 : C) := by
    have htwo : (2 : C) ≠ 0 := two_ne_zero
    field_simp
    linear_combination he2
  have hE : algebraMap C (JetField C Unit) e
      = -(algebraMap C (JetField C Unit) (3 / 2 : C)) := by
    rw [hEc, map_neg]
  -- the constant coefficient satisfies an inhomogeneous relation of order one
  set ρP : ↥(jetPrefixField C 1) := substitutionDerivPrefix R (le_refl 1) with hρPdef
  set ρ₁P : ↥(jetPrefixField C 1) :=
    substitutionDerivPrefix (ratFuncDeriv R) (le_refl 1) with hρ₁Pdef
  set ρ₂P : ↥(jetPrefixField C 1) :=
    substitutionDerivPrefix (ratFuncDeriv (ratFuncDeriv R)) (le_refl 1) with hρ₂Pdef
  set G : JetField C Unit := algebraMap C (JetField C Unit) (3 / 2 : C) with hGdef
  set K : JetField C Unit := algebraMap C (JetField C Unit) k with hKdef
  set Dp : ↥(jetPrefixField C 1) :=
    ρ₂P - algebraMap C ↥(jetPrefixField C 1) (3 / 2 : C) * ρ₁P ^ 2 / ρP with hDpdef
  set Ep : ↥(jetPrefixField C 1) := algebraMap C ↥(jetPrefixField C 1) k * ρ₁P with hEpdef
  set S : Polynomial ↥(jetPrefixField C 1) :=
    Polynomial.C Dp * Polynomial.X ^ 3 + Polynomial.C Ep * Polynomial.X ^ 2 with hSdef
  set ι₁ := algebraMap ↥(jetPrefixField C 1) (JetField C Unit) with hι₁def
  have hι₁ρ : ι₁ ρP = ρ := rfl
  have hι₁ρ₁ : ι₁ ρ₁P = ρ₁ := substitutionDeriv_ratFuncDeriv R
  have hι₁ρ₂ : ι₁ ρ₂P = ρ₂ := by
    show substitutionDeriv (ratFuncDeriv (ratFuncDeriv R)) = ρ₂
    rw [substitutionDeriv_ratFuncDeriv (ratFuncDeriv R), substitutionDeriv_ratFuncDeriv R]
  have hι₁G : ι₁ (algebraMap C ↥(jetPrefixField C 1) (3 / 2 : C)) = G := by
    rw [hGdef, ← IsScalarTower.algebraMap_apply]
  have hι₁K : ι₁ (algebraMap C ↥(jetPrefixField C 1) k) = K := by
    rw [hKdef, ← IsScalarTower.algebraMap_apply]
  have hι₁Dp : ι₁ Dp = ρ₂ - G * ρ₁ ^ 2 / ρ := by
    rw [hDpdef, map_sub, map_div₀, map_mul, map_pow, hι₁ρ, hι₁ρ₁, hι₁ρ₂, hι₁G]
  have hι₁Ep : ι₁ Ep = K * ρ₁ := by
    rw [hEpdef, map_mul, hι₁K, hι₁ρ₁]
  have haevalS : Polynomial.aeval y S = ι₁ Dp * y ^ 3 + ι₁ Ep * y ^ 2 := by
    rw [hSdef, map_add, map_mul, map_mul, map_pow, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_C, Polynomial.aeval_X]
  have hΦ1K : jetSubstitution R hR w1 = K := by
    rw [hk, hKdef, AlgHom.commutes]
  have hquad : jetSubstitution R hR w2 * (ρ₁ * y ^ 2) ^ 2 * ρ
      = ρ₁ ^ 2 * y ^ 3 * algebraMap C (JetField C Unit) e := by
    linear_combination (ρ₁ ^ 2 * y ^ 4) * hw2eig + (ρ₁ ^ 2 * y ^ 3) * he
  have hEq0 : ρ * jetSubstitution R hR w0
      = ρ * ρ * w0 - ρ * ρ₂ * y ^ 3 + G * ρ₁ ^ 2 * y ^ 3 - ρ * K * ρ₁ * y ^ 2 := by
    have hEfull : algebraMap C (JetField C Unit) e = -G := by rw [hE, hGdef]
    linear_combination ρ * hE0 - hquad - hEfull * (ρ₁ ^ 2 * y ^ 3)
      - (ρ * (ρ₁ * y ^ 2)) * hΦ1K
  have hEq : jetSubstitution R hR w0 * substitutionDeriv R ^ 0
      = ρ * w0 - Polynomial.aeval y S := by
    rw [pow_zero, mul_one, haevalS, hι₁Dp, hι₁Ep]
    field_simp
    linear_combination hEq0
  have hSdeg : S.natDegree ≤ 3 := by
    rw [hSdef]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans Polynomial.natDegree_mul_le (by simp)
    · exact le_trans Polynomial.natDegree_mul_le (by simp)
  have hScoeff : S.coeff 3 = Dp := by
    rw [hSdef]
    simp
  set D : RatFunc C := ratFuncDeriv (ratFuncDeriv (ratFuncDeriv R))
    - RatFunc.C (3 / 2 : C) * ratFuncDeriv (ratFuncDeriv R) ^ 2 / ratFuncDeriv R with hDdef
  have hD : ratFuncEval (JetField.jet ((), 0) : JetField C Unit) transcendental_freeGen D
      = ι₁ (S.coeff 3) := by
    rw [hScoeff, hι₁Dp, hDdef, map_sub, map_div₀, map_mul, map_pow, ratFuncEval_ratFuncDeriv,
      ratFuncEval_ratFuncDeriv, ratFuncEval_ratFuncDeriv, ratFuncEval_C]
    rw [substitutionDeriv_ratFuncDeriv (ratFuncDeriv R), substitutionDeriv_ratFuncDeriv R]
  have hres := exists_ratFunc_affineTransport_of_order_one R hR (hord (u.coeff 0)) hSdeg hEq hD
  simpa using hres

end LevelThree

end GaloisForLFunctions.HTGeometry
