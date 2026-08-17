import GaloisForLFunctions.HTGeometry.JetWeightZeroNormalization

/-!
# One step of the weight-zero descent

The shift term in weight-zero form is affine in the ratio one below the top,

`s_M = M·R''·z_{M−1} + b_M`,

with `b_M` of jet order at most `M − 2`.  So a normalizing shift at level `M`, normalized to be
torus-invariant and sliced in `z_{M−1}`, either produces the affine cocycle of the two top
coefficients of its denominator — which is a normalizing shift one level down — or is a polynomial in
`z_{M−1}` whose coefficients are again torus-invariant.

Because the coefficients stay torus-invariant, iterating the step reaches jet order one, where
torus invariance forces jet order zero and every remaining relation is a rational affine transport.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-! ## Partials of the weight-zero coordinates -/

theorem pd_jetRatio_mul {i j : ℕ} (hi : i ≠ 1) :
    JetField.pd ((), i) (jetRatio j : JetField C Unit)
        * (JetField.jet ((), 1) : JetField C Unit) ^ j
      = JetField.pd ((), i) (JetField.jet ((), j) : JetField C Unit) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hmul : (jetRatio j : JetField C Unit) * (JetField.jet ((), 1) : JetField C Unit) ^ j
      = (JetField.jet ((), j) : JetField C Unit) := by
    rw [jetRatio]
    field_simp
  have hleib := (JetField.pd ((), i) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (jetRatio j : JetField C Unit) ((JetField.jet ((), 1) : JetField C Unit) ^ j)
  simp only [smul_eq_mul] at hleib
  rw [hmul] at hleib
  have hpow : JetField.pd ((), i) ((JetField.jet ((), 1) : JetField C Unit) ^ j) = 0 := by
    have hl := (JetField.pd ((), i) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
        (JetField.jet ((), 1) : JetField C Unit) j
    rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
    simpa using hl
  rw [hleib, hpow]
  ring

theorem pd_jetRatio_self {j : ℕ} (hj : j ≠ 1) :
    JetField.pd ((), j) (jetRatio j : JetField C Unit)
      = 1 / (JetField.jet ((), 1) : JetField C Unit) ^ j := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_jetRatio_mul (C := C) (i := j) (j := j) hj
  rw [JetField.pd_jet_self] at h
  field_simp
  linear_combination h

theorem pd_jetRatio_of_ne {i j : ℕ} (hi : i ≠ 1) (hij : i ≠ j) :
    JetField.pd ((), i) (jetRatio j : JetField C Unit) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_jetRatio_mul (C := C) (i := i) (j := j) hi
  rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero j hy1)

/-! ## Partials of the weight-zero shift term -/

theorem pd_substitutionShiftRatio_mul (R : RatFunc C) {i M : ℕ} (hi : i ≠ 1) :
    JetField.pd ((), i) (substitutionShiftRatio R M)
        * (JetField.jet ((), 1) : JetField C Unit) ^ M
      = JetField.pd ((), i) (substitutionShift R M) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hmul : substitutionShiftRatio R M * (JetField.jet ((), 1) : JetField C Unit) ^ M
      = substitutionShift R M := by
    rw [substitutionShiftRatio]
    field_simp
  have hleib := (JetField.pd ((), i) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (substitutionShiftRatio R M) ((JetField.jet ((), 1) : JetField C Unit) ^ M)
  simp only [smul_eq_mul] at hleib
  rw [hmul] at hleib
  have hpow : JetField.pd ((), i) ((JetField.jet ((), 1) : JetField C Unit) ^ M) = 0 := by
    have hl := (JetField.pd ((), i) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz_pow
        (JetField.jet ((), 1) : JetField C Unit) M
    rw [JetField.pd_jet_of_ne (by simp only [ne_eq, Prod.mk.injEq, true_and]; omega)] at hl
    simpa using hl
  rw [hleib, hpow]
  ring

/-- **The affine part of the weight-zero shift term.** -/
theorem pd_top_substitutionShiftRatio (R : RatFunc C) {N : ℕ} (hN : 1 ≤ N) :
    JetField.pd ((), N + 1) (substitutionShiftRatio R (N + 2))
      = ((N + 2 : ℕ) : JetField C Unit) * JetField.pd ((), 0) (substitutionDeriv R)
        / (JetField.jet ((), 1) : JetField C Unit) ^ (N + 1) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_substitutionShiftRatio_mul R (i := N + 1) (M := N + 2) (by omega)
  rw [pd_top_substitutionShift_eq R N] at h
  refine mul_right_cancel₀ (pow_ne_zero (N + 2) hy1) ?_
  rw [h]
  field_simp
  ring

theorem pd_substitutionShiftRatio_eq_zero (R : RatFunc C) {i M : ℕ} (hM : 1 ≤ M) (hi : i ≠ 1)
    (hiM : M ≤ i) : JetField.pd ((), i) (substitutionShiftRatio R M) = 0 := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have h := pd_substitutionShiftRatio_mul R (i := i) (M := M) hi
  have hσ : JetField.pd ((), i) (substitutionShift R M) = 0 :=
    (mem_jetPrefixField_iff M _).mp (substitutionShift_mem_jetPrefixField R hM) i hiM
  rw [hσ] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero M hy1)

/-! ## The affine part of the weight-zero shift term -/

/-- The part of the weight-zero shift term below the top ratio. -/
def weightZeroShiftTail (R : RatFunc C) (M : ℕ) : JetField C Unit :=
  substitutionShiftRatio R M
    - (M : JetField C Unit) * JetField.pd ((), 0) (substitutionDeriv R) * jetRatio (M - 1)

theorem weightZeroShiftTail_mem (R : RatFunc C) (N : ℕ) :
    weightZeroShiftTail R (N + 3) ∈ jetPrefixField C (N + 2) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  rw [mem_jetPrefixField_iff]
  intro j hj
  have hρ1 : JetField.pd ((), j) (JetField.pd ((), 0) (substitutionDeriv R)) = 0 := by
    rw [pd_comm, pd_substitutionDeriv_eq_zero R (by omega), map_zero]
  have hnat : JetField.pd ((), j) ((N + 3 : ℕ) : JetField C Unit) = 0 := by
    rw [show (((N + 3 : ℕ)) : JetField C Unit)
      = algebraMap C (JetField C Unit) ((N + 3 : ℕ) : C) from by rw [map_natCast],
      Derivation.map_algebraMap]
  have hleib1 := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (((N + 3 : ℕ) : JetField C Unit) * JetField.pd ((), 0) (substitutionDeriv R))
      (jetRatio (N + 2) : JetField C Unit)
  have hleib2 := (JetField.pd ((), j) :
    Derivation C (JetField C Unit) (JetField C Unit)).leibniz
      (((N + 3 : ℕ) : JetField C Unit)) (JetField.pd ((), 0) (substitutionDeriv R))
  simp only [smul_eq_mul] at hleib1 hleib2
  have hidx : N + 3 - 1 = N + 2 := by omega
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with heq | hlt
  · have hjv : j = N + 2 := by omega
    subst hjv
    have hs : JetField.pd ((), N + 2) (substitutionShiftRatio R (N + 3))
        = ((N + 3 : ℕ) : JetField C Unit) * JetField.pd ((), 0) (substitutionDeriv R)
          / (JetField.jet ((), 1) : JetField C Unit) ^ (N + 2) := by
      exact pd_top_substitutionShiftRatio R (N := N + 1) (by omega)
    rw [weightZeroShiftTail, hidx, map_sub, hleib1, hleib2, hρ1, hnat,
      pd_jetRatio_self (by omega), hs]
    push_cast
    field_simp
    ring
  · have hjv : N + 2 < j := by omega
    rw [weightZeroShiftTail, hidx, map_sub, hleib1, hleib2, hρ1, hnat,
      pd_jetRatio_of_ne (by omega) (by omega),
      pd_substitutionShiftRatio_eq_zero R (by omega) (by omega) (by omega)]
    ring

/-! ## One descent step -/

/-- **The descent step in weight-zero form.**  A normalizing shift at level `N + 3` either descends
one level or is a polynomial in `z_{N+2}` with torus-invariant coefficients. -/
theorem hasNormalizingShift_pred_or_zpolynomial (R : RatFunc C) (hR : substitutionDeriv R ≠ 0)
    (N : ℕ)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N + 2 < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    (h : HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 3 by omega)) :
    HasNormalizingShift R hR (show (1 : ℕ) ≤ N + 2 by omega)
      ∨ ∃ u : Polynomial ↥(jetPrefixField C (N + 2)),
          (∀ i : ℕ,
            IsWeightZero ((u.coeff i : ↥(jetPrefixField C (N + 2))) : JetField C Unit)) ∧
          twistComp (jetSubstitutionPrefix R hR (N + 2)).toRingHom
              (Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
                  ^ (1 - ((N + 2 : ℕ) : ℤ))) * Polynomial.X
                + Polynomial.C (substitutionShiftRatioPrefix R (show 1 < N + 2 by omega)
                    * substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
                      ^ (-((N + 2 : ℕ) : ℤ)))) u
            = Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
                ^ (1 - ((N + 3 : ℕ) : ℤ))) * u
              - (Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
                    ^ (-((N + 3 : ℕ) : ℤ))
                  * (((N + 3 : ℕ) : ↥(jetPrefixField C (N + 2)))
                    * substitutionDerivPrefix (ratFuncDeriv R)
                        (show (1 : ℕ) ≤ N + 2 by omega))) * Polynomial.X
                + Polynomial.C (substitutionDerivPrefix R (show (1 : ℕ) ≤ N + 2 by omega)
                    ^ (-((N + 3 : ℕ) : ℤ))
                  * ⟨weightZeroShiftTail R (N + 3), weightZeroShiftTail_mem R N⟩)) := by
  classical
  set hk2 : (1 : ℕ) ≤ N + 2 := by omega
  set hk : 1 < N + 2 := by omega
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  obtain ⟨w, hwz, hword, hweq⟩ :=
    exists_isWeightZero_zshift R hR (M := N + 3) (by omega) (by simpa using hfix) h
  set ρ : JetField C Unit := substitutionDeriv R with hρdef
  have hρ0 : ρ ≠ 0 := hR
  -- the affine data
  set aP : ↥(jetPrefixField C (N + 2)) :=
    substitutionDerivPrefix R hk2 ^ (1 - ((N + 2 : ℕ) : ℤ)) with haPdef
  set bP : ↥(jetPrefixField C (N + 2)) :=
    substitutionShiftRatioPrefix R hk * substitutionDerivPrefix R hk2 ^ (-((N + 2 : ℕ) : ℤ))
    with hbPdef
  set cP : ↥(jetPrefixField C (N + 2)) :=
    substitutionDerivPrefix R hk2 ^ (1 - ((N + 3 : ℕ) : ℤ)) with hcPdef
  set S1 : ↥(jetPrefixField C (N + 2)) :=
    substitutionDerivPrefix R hk2 ^ (-((N + 3 : ℕ) : ℤ))
      * (((N + 3 : ℕ) : ↥(jetPrefixField C (N + 2)))
        * substitutionDerivPrefix (ratFuncDeriv R) hk2) with hS1def
  set S0 : ↥(jetPrefixField C (N + 2)) :=
    substitutionDerivPrefix R hk2 ^ (-((N + 3 : ℕ) : ℤ))
      * ⟨weightZeroShiftTail R (N + 3), weightZeroShiftTail_mem R N⟩ with hS0def
  set S : Polynomial ↥(jetPrefixField C (N + 2)) :=
    Polynomial.C S1 * Polynomial.X + Polynomial.C S0 with hSdef
  have haP0 : aP ≠ 0 := by
    rw [haPdef]
    exact zpow_ne_zero _ (substitutionDerivPrefix_ne_zero R hR hk2)
  have hact := jetSubstitution_jetRatio_aeval R hR hk
  -- the sliced relation
  have hιρ : algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)
      (substitutionDerivPrefix R hk2) = ρ := rfl
  have hιρ1 : algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)
      (substitutionDerivPrefix (ratFuncDeriv R) hk2)
      = JetField.pd ((), 0) ρ := substitutionDeriv_ratFuncDeriv R
  have haevalS : Polynomial.aeval (jetRatio (N + 2) : JetField C Unit) S
      = ρ ^ (-((N + 3 : ℕ) : ℤ)) * substitutionShiftRatio R (N + 3) := by
    rw [hSdef, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
      hS1def, hS0def]
    simp only [map_mul, map_zpow₀, map_natCast, hιρ, hιρ1]
    have hcoe : algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)
        ⟨weightZeroShiftTail R (N + 3), weightZeroShiftTail_mem R N⟩
        = weightZeroShiftTail R (N + 3) := rfl
    rw [hcoe, weightZeroShiftTail]
    have hidx : N + 3 - 1 = N + 2 := by omega
    rw [hidx]
    push_cast
    ring
  have hsliced : jetSubstitution R hR w
      = algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) cP * w
        - Polynomial.aeval (jetRatio (N + 2) : JetField C Unit) S := by
    rw [haevalS, hcPdef, map_zpow₀, hιρ]
    have hpow : ρ ^ (N + 3) ≠ 0 := pow_ne_zero _ hρ0
    refine mul_left_cancel₀ hpow ?_
    rw [hweq]
    have hz1 : ρ ^ (N + 3) * ρ ^ (1 - ((N + 3 : ℕ) : ℤ)) = ρ := by
      rw [← zpow_natCast ρ (N + 3), ← zpow_add₀ hρ0]
      norm_num
    have hz2 : ρ ^ (N + 3) * ρ ^ (-((N + 3 : ℕ) : ℤ)) = 1 := by
      rw [← zpow_natCast ρ (N + 3), ← zpow_add₀ hρ0]
      norm_num
    linear_combination -w * hz1 + (substitutionShiftRatio R (N + 3)) * hz2
  rcases cocycle_or_polynomial_of_zslice R hR hk hwz (by simpa using hword) haP0 hact S hsliced
    with ⟨ν, s, hν, hs⟩ | ⟨u, huwz, -, hu⟩
  · refine Or.inl ?_
    have hνne : ((ν : ↥(jetPrefixField C (N + 2)))) ≠ 0 := by
      have : ((ν : ℕ) : ↥(jetPrefixField C (N + 2))) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      exact this
    refine hasNormalizingShift_of_zshift R hR (M := N + 2) hk
      (w := algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) (s / (ν : _))) ?_ ?_
    · intro j hj
      exact (mem_jetPrefixField_iff (N + 2) _).mp (s / (ν : _)).2 j (by omega)
    · have hΦι : algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)
          ((jetSubstitutionPrefix R hR (N + 2)).toRingHom s)
          = jetSubstitution R hR
            (algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) s) := rfl
      have hsr : algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)
          (substitutionShiftRatioPrefix R hk) = substitutionShiftRatio R (N + 2) := rfl
      have hc := congrArg (algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit)) hs
      simp only [haPdef, map_sub, map_mul, map_natCast, map_zpow₀, hιρ, hsr] at hc
      rw [hΦι] at hc
      have hz1 : ρ ^ (N + 2) * ρ ^ (1 - ((N + 2 : ℕ) : ℤ)) = ρ := by
        rw [← zpow_natCast ρ (N + 2), ← zpow_add₀ hρ0]
        norm_num
      have hz2 : ρ ^ (N + 2) * ρ ^ (-((N + 2 : ℕ) : ℤ)) = 1 := by
        rw [← zpow_natCast ρ (N + 2), ← zpow_add₀ hρ0]
        norm_num
      have hνJ0 : ((ν : ℕ) : JetField C Unit) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hc' : ρ ^ (N + 2)
          * jetSubstitution R hR
              (algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) s)
          = ρ * algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) s
            - ((ν : ℕ) : JetField C Unit) * substitutionShiftRatio R (N + 2) := by
        rw [hc]
        linear_combination
          (algebraMap ↥(jetPrefixField C (N + 2)) (JetField C Unit) s) * hz1
          - (((ν : ℕ) : JetField C Unit) * substitutionShiftRatio R (N + 2)) * hz2
      simp only [map_div₀, map_natCast]
      field_simp
      linear_combination hc'
  · exact Or.inr ⟨u, huwz, hu⟩

end

end GaloisForLFunctions.HTGeometry
