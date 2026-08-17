import GaloisForLFunctions.HTGeometry.JetWeightZeroDichotomy

/-!
# The normalizing shift in weight-zero form

Dividing a normalizing shift at jet level `M` by `y₁^M` turns it into the weight-zero relation

`R'^M·Φ(w) = R'·w − s_M`,   `s_M = σ_M/y₁^M`,

and the passage is reversible.  In this form the substitution acts on the coordinate by the affine
polynomial `R'^{1−k}·X + s_k·R'^{-k}` over the prefix field, which is what feeds the slicing
dichotomy.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

theorem substitutionShiftRatio_mem_jetPrefixField (R : RatFunc C) {k : ℕ} (hk : 1 < k) :
    substitutionShiftRatio R k ∈ jetPrefixField C k := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ∈ jetPrefixField C k :=
    jet_mem_jetPrefixField hk
  have hσ : substitutionShift R k ∈ jetPrefixField C k :=
    substitutionShift_mem_jetPrefixField R (by omega)
  rw [substitutionShiftRatio]
  exact div_mem hσ (pow_mem hy1 k)

/-- The shift term in weight-zero form, as an element of the prefix field. -/
def substitutionShiftRatioPrefix (R : RatFunc C) {k : ℕ} (hk : 1 < k) : ↥(jetPrefixField C k) :=
  ⟨substitutionShiftRatio R k, substitutionShiftRatio_mem_jetPrefixField R hk⟩

/-- **The affine action on the weight-zero coordinate.** -/
theorem jetSubstitution_jetRatio_aeval (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {k : ℕ}
    (hk : 1 < k) :
    jetSubstitution R hR (jetRatio k : JetField C Unit)
      = Polynomial.aeval (jetRatio k : JetField C Unit)
        (Polynomial.C (substitutionDerivPrefix R (le_of_lt hk) ^ (1 - (k : ℤ)))
            * Polynomial.X
          + Polynomial.C (substitutionShiftRatioPrefix R hk
              * substitutionDerivPrefix R (le_of_lt hk) ^ (-(k : ℤ)))) := by
  have hρ : substitutionDeriv R ≠ 0 := hR
  have hkey := jetSubstitution_jetRatio R hR k
  rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
  have hc1 : algebraMap ↥(jetPrefixField C k) (JetField C Unit)
      (substitutionDerivPrefix R (le_of_lt hk) ^ (1 - (k : ℤ)))
      = substitutionDeriv R ^ (1 - (k : ℤ)) := by
    rw [map_zpow₀]
    rfl
  have hc2 : algebraMap ↥(jetPrefixField C k) (JetField C Unit)
      (substitutionShiftRatioPrefix R hk * substitutionDerivPrefix R (le_of_lt hk) ^ (-(k : ℤ)))
      = substitutionShiftRatio R k * substitutionDeriv R ^ (-(k : ℤ)) := by
    rw [map_mul, map_zpow₀]
    rfl
  rw [hc1, hc2]
  have hz1 : substitutionDeriv R ^ k * substitutionDeriv R ^ (1 - (k : ℤ))
      = substitutionDeriv R := by
    rw [← zpow_natCast (substitutionDeriv R) k, ← zpow_add₀ hρ]
    norm_num
  have hz2 : substitutionDeriv R ^ k * substitutionDeriv R ^ (-(k : ℤ)) = 1 := by
    rw [← zpow_natCast (substitutionDeriv R) k, ← zpow_add₀ hρ]
    norm_num
  have hzk : substitutionDeriv R ^ k ≠ 0 := pow_ne_zero k hρ
  refine mul_left_cancel₀ hzk ?_
  rw [hkey]
  linear_combination (-(jetRatio k : JetField C Unit)) * hz1
    - (substitutionShiftRatio R k) * hz2

/-! ## The weight-zero form of a normalizing shift -/

/-- **A normalizing shift in weight-zero form.** -/
theorem exists_zshift_of_hasNormalizingShift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {M : ℕ} (hM : 1 < M) (h : HasNormalizingShift R hR (le_of_lt hM)) :
    ∃ w : JetField C Unit, (∀ j : ℕ, M - 1 < j → JetField.pd ((), j) w = 0) ∧
      substitutionDeriv R ^ M * jetSubstitution R hR w
        = substitutionDeriv R * w - substitutionShiftRatio R M := by
  obtain ⟨t, ht⟩ := h
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have htJ : jetSubstitution R hR (t : JetField C Unit)
      = substitutionDeriv R * (t : JetField C Unit) - substitutionShift R M := by
    have hc := congrArg (fun z : ↥(jetPrefixField C M) =>
      (algebraMap ↥(jetPrefixField C M) (JetField C Unit) z)) ht
    simp only [map_sub, map_mul] at hc
    rw [← jetSubstitution_algebraMap_prefix] at hc
    exact hc
  refine ⟨(t : JetField C Unit) / (JetField.jet ((), 1) : JetField C Unit) ^ M, ?_, ?_⟩
  · intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz
        ((t : JetField C Unit) / (JetField.jet ((), 1) : JetField C Unit) ^ M)
        ((JetField.jet ((), 1) : JetField C Unit) ^ M)
    simp only [smul_eq_mul] at hleib
    have hmul : (t : JetField C Unit) / (JetField.jet ((), 1) : JetField C Unit) ^ M
        * (JetField.jet ((), 1) : JetField C Unit) ^ M = (t : JetField C Unit) :=
      div_mul_cancel₀ _ (pow_ne_zero M hy1)
    rw [hmul] at hleib
    have hpow : JetField.pd ((), j) ((JetField.jet ((), 1) : JetField C Unit) ^ M) = 0 := by
      have hl := (JetField.pd ((), j) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
          (JetField.jet ((), 1) : JetField C Unit) M
      rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
      simpa using hl
    have htj : JetField.pd ((), j) (t : JetField C Unit) = 0 :=
      (mem_jetPrefixField_iff M _).mp t.2 j (by omega)
    rw [htj, hpow, mul_zero, zero_add] at hleib
    exact (mul_eq_zero.mp hleib.symm).resolve_left (pow_ne_zero M hy1)
  · have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
        = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
      rw [jetSubstitution_jet, substitutionJet_one]
    rw [map_div₀, map_pow, hΦ1, htJ, substitutionShiftRatio, mul_pow]
    field_simp

/-- **The converse: a weight-zero relation is a normalizing shift.** -/
theorem hasNormalizingShift_of_zshift (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    {M : ℕ} (hM : 1 < M) {w : JetField C Unit}
    (hw : ∀ j : ℕ, M - 1 < j → JetField.pd ((), j) w = 0)
    (heq : substitutionDeriv R ^ M * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R M) :
    HasNormalizingShift R hR (le_of_lt hM) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hmem : w * (JetField.jet ((), 1) : JetField C Unit) ^ M ∈ jetPrefixField C M := by
    rw [mem_jetPrefixField_iff]
    intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz w
        ((JetField.jet ((), 1) : JetField C Unit) ^ M)
    simp only [smul_eq_mul] at hleib
    have hpow : JetField.pd ((), j) ((JetField.jet ((), 1) : JetField C Unit) ^ M) = 0 := by
      have hl := (JetField.pd ((), j) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
          (JetField.jet ((), 1) : JetField C Unit) M
      rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
      simpa using hl
    rw [hleib, hpow, hw j (by omega), mul_zero, mul_zero, add_zero]
  refine ⟨⟨w * (JetField.jet ((), 1) : JetField C Unit) ^ M, hmem⟩, ?_⟩
  refine Subtype.ext ?_
  show jetSubstitution R hR (w * (JetField.jet ((), 1) : JetField C Unit) ^ M)
    = substitutionDeriv R * (w * (JetField.jet ((), 1) : JetField C Unit) ^ M)
      - substitutionShift R M
  have hΦ1 : jetSubstitution R hR (JetField.jet ((), 1) : JetField C Unit)
      = (JetField.jet ((), 1) : JetField C Unit) * substitutionDeriv R := by
    rw [jetSubstitution_jet, substitutionJet_one]
  have hσ : substitutionShift R M
      = substitutionShiftRatio R M * (JetField.jet ((), 1) : JetField C Unit) ^ M := by
    rw [substitutionShiftRatio]
    field_simp
  rw [map_mul, map_pow, hΦ1, mul_pow, hσ]
  linear_combination ((JetField.jet ((), 1) : JetField C Unit) ^ M) * heq

end

end GaloisForLFunctions.HTGeometry
