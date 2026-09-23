import GaloisForLFunctions.HTGeometry.JetWeightZeroShift

/-!
# Normalizing a weight-zero shift

The weight-zero form of a normalizing shift is invariant under the weighted action up to a multiple
of `y₁^{1−M}`: the difference of the shift and its scaled image solves the homogeneous relation, so
multiplying it by `y₁^{M−1}` gives a fixed element of jet order below `M`, hence a constant.  Adding
the right multiple of `y₁^{1−M}` — which the homogeneous relation also solves — makes the shift
genuinely invariant.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

theorem two_pow_sub_one_ne_zero {M : ℕ} (hM : 1 ≤ M) : ((2 : C) ^ M - 1) ≠ 0 := by
  intro hh
  have h1 : (2 : C) ^ M = 1 := by linear_combination hh
  have hnat : ((2 ^ M : ℕ) : C) = ((1 : ℕ) : C) := by push_cast; exact h1
  have := Nat.cast_injective (R := C) hnat
  have h2 : (2 : ℕ) ^ M = 2 ^ (0 : ℕ) := by simpa using this
  exact absurd (Nat.pow_right_injective (le_refl 2) h2) (by omega)

/-- **The weight-zero shift can be normalized to be torus-invariant.** -/
theorem exists_isWeightZero_zshift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {M : ℕ}
    (hM : 1 < M)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, M - 1 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    (h : HasNormalizingShift R hR (le_of_lt hM)) :
    ∃ w : JetField C Unit, IsWeightZero w ∧
      (∀ j : ℕ, M - 1 < j → JetField.pd ((), j) w = 0) ∧
      substitutionDeriv R ^ M * jetSubstitution R hR w
        = substitutionDeriv R * w - substitutionShiftRatio R M := by
  classical
  have htwo : (2 : C) ≠ 0 := two_ne_zero
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  obtain ⟨w₀, hw₀ord, hw₀⟩ := exists_zshift_of_hasNormalizingShift R hR hM h
  set y : JetField C Unit := (JetField.jet ((), 1) : JetField C Unit) with hydef
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  -- the correction term
  set u : JetField C Unit := 1 / y ^ (M - 1) with hudef
  have hupow : y ^ (M - 1) ≠ 0 := pow_ne_zero _ hy1
  have hρpow : ρ ^ M = ρ * ρ ^ (M - 1) := by
    conv_lhs => rw [show M = (M - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  have hΦ1 : jetSubstitution R hR y = y * ρ := by
    rw [hydef, jetSubstitution_jet, substitutionJet_one]
  have hΦu : ρ ^ M * jetSubstitution R hR u = ρ * u := by
    rw [hudef, map_div₀, map_one, map_pow, hΦ1, mul_pow, hρpow]
    field_simp
  have hwu : weightScale htwo u = algebraMap C (JetField C Unit) ((2 : C) ^ (M - 1))⁻¹ * u := by
    rw [hudef, map_div₀, map_one, map_pow, hydef, weightScale_jet, pow_one, mul_pow]
    rw [map_inv₀, map_pow]
    field_simp
  -- the scaled shift differs by a constant multiple of the correction term
  have hscaled : ρ ^ M * jetSubstitution R hR (weightScale htwo w₀)
      = ρ * weightScale htwo w₀ - substitutionShiftRatio R M := by
    have hc := congrArg (weightScale htwo) hw₀
    rw [map_mul, map_pow, weightScale_substitutionDeriv, weightScale_jetSubstitution,
      map_sub, map_mul, weightScale_substitutionDeriv,
      weightScale_substitutionShiftRatio] at hc
    exact hc
  set d : JetField C Unit := weightScale htwo w₀ - w₀ with hddef
  have hdhom : ρ ^ M * jetSubstitution R hR d = ρ * d := by
    rw [hddef, map_sub, mul_sub, hscaled, hw₀]
    ring
  have hdord : ∀ j : ℕ, M - 1 < j → JetField.pd ((), j) d = 0 := by
    intro j hj
    have hws : JetField.pd ((), j) (weightScale htwo w₀) = 0 := by
      rw [weightScale_pd, hw₀ord j hj, map_zero, mul_zero]
    rw [hddef, map_sub, hws, hw₀ord j hj, sub_zero]
  have hfixd : jetSubstitution R hR (d * y ^ (M - 1)) = d * y ^ (M - 1) := by
    rw [map_mul, map_pow, hΦ1, mul_pow]
    have hρ0 : ρ ^ M ≠ 0 := pow_ne_zero M hR
    refine mul_left_cancel₀ hρ0 ?_
    calc ρ ^ M * (jetSubstitution R hR d * (y ^ (M - 1) * ρ ^ (M - 1)))
        = (ρ ^ M * jetSubstitution R hR d) * (y ^ (M - 1) * ρ ^ (M - 1)) := by ring
      _ = (ρ * d) * (y ^ (M - 1) * ρ ^ (M - 1)) := by rw [hdhom]
      _ = ρ ^ M * (d * y ^ (M - 1)) := by
          rw [hρpow]
          ring
  have hordd : ∀ j : ℕ, M - 1 < j → JetField.pd ((), j) (d * y ^ (M - 1)) = 0 := by
    intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz d (y ^ (M - 1))
    simp only [smul_eq_mul] at hleib
    have hpow : JetField.pd ((), j) (y ^ (M - 1)) = 0 := by
      have hl := (JetField.pd ((), j) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow y (M - 1)
      rw [hydef, JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
      simpa using hl
    rw [hleib, hpow, hdord j hj, mul_zero, mul_zero, add_zero]
  obtain ⟨γ, hγ⟩ := hfix (d * y ^ (M - 1)) hordd hfixd
  have hdval : d = algebraMap C (JetField C Unit) γ * u := by
    rw [hudef]
    field_simp
    linear_combination hγ
  -- the normalization
  set e : C := γ * (2 : C) ^ (M - 1) / ((2 : C) ^ (M - 1) - 1) with hedef
  have hne : ((2 : C) ^ (M - 1) - 1) ≠ 0 := two_pow_sub_one_ne_zero (by omega)
  refine ⟨w₀ + algebraMap C (JetField C Unit) e * u, ?_, ?_, ?_⟩
  · show weightScale htwo (w₀ + algebraMap C (JetField C Unit) e * u)
      = w₀ + algebraMap C (JetField C Unit) e * u
    rw [map_add, map_mul, AlgEquiv.commutes, hwu]
    have hd : weightScale htwo w₀ = w₀ + algebraMap C (JetField C Unit) γ * u := by
      rw [← hdval, hddef]
      ring
    rw [hd]
    have hkey : algebraMap C (JetField C Unit) γ
        + algebraMap C (JetField C Unit) e * algebraMap C (JetField C Unit) ((2 : C) ^ (M - 1))⁻¹
        = algebraMap C (JetField C Unit) e := by
      rw [← map_mul, ← map_add]
      congr 1
      rw [hedef]
      field_simp
      ring
    linear_combination u * hkey
  · intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz
        (algebraMap C (JetField C Unit) e) u
    simp only [smul_eq_mul] at hleib
    have hu0 : JetField.pd ((), j) u = 0 := by
      have hl := (JetField.pd ((), j) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz u (y ^ (M - 1))
      simp only [smul_eq_mul] at hl
      have hmul : u * y ^ (M - 1) = 1 := by
        rw [hudef]
        field_simp
      rw [hmul, Derivation.map_one_eq_zero] at hl
      have hpow : JetField.pd ((), j) (y ^ (M - 1)) = 0 := by
        have hp := (JetField.pd ((), j) :
          Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow y (M - 1)
        rw [hydef,
          JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hp
        simpa using hp
      rw [hpow, mul_zero, zero_add] at hl
      exact (mul_eq_zero.mp hl.symm).resolve_left hupow
    rw [map_add, hw₀ord j hj, hleib, hu0, Derivation.map_algebraMap]
    ring
  · rw [map_add, map_mul, AlgHom.commutes, mul_add]
    rw [show ρ ^ M * (algebraMap C (JetField C Unit) e * jetSubstitution R hR u)
      = algebraMap C (JetField C Unit) e * (ρ ^ M * jetSubstitution R hR u) from by ring, hΦu]
    linear_combination hw₀
