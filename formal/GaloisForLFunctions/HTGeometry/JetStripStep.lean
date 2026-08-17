import GaloisForLFunctions.HTGeometry.JetUniformCoefficient

/-!
# The general strip step

One uniform step of the descent.  If a torus-invariant `v` of jet order at most `K` satisfies

`R'^κ·Φ(v) = R'·v − D`

and is affine in its top coordinate, then subtracting the pinned top term `P·z_K`, with
`P = y₁^K·∂_K v`, leaves a torus-invariant element of jet order at most `K − 1` satisfying the same
relation with the same exponent and with `D` replaced by

`D + P·s_K − E·z_K − E·s_K/R'`,   `E = y₁^K·∂_K D`.

The proof is the product of the descended relation for `P`, of exponent `κ + 1 − K`, with the
coordinate law for `z_K`, of exponent `K`.  Nothing here depends on the level, so this single step
carries a normalizing shift at an arbitrary level all the way down to jet order zero.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- The inhomogeneous term produced by one strip step. -/
def stripDefect (R : RatFunc C) (K : ℕ) (D P E : JetField C Unit) : JetField C Unit :=
  D + P * substitutionShiftRatio R K - E * (jetRatio K : JetField C Unit)
    - E * substitutionShiftRatio R K / substitutionDeriv R

/-- **The general strip step.** -/
theorem strip_step (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {K : ℕ} (hK : 2 ≤ K)
    {v D : JetField C Unit} (hvwz : IsWeightZero v)
    (hvord : ∀ j : ℕ, K < j → JetField.pd ((), j) v = 0)
    {κ : ℤ} (heq : substitutionDeriv R ^ κ * jetSubstitution R hR v = substitutionDeriv R * v - D)
    (hlin : topDescent K (topDescent K v) = 0) :
    (∀ j : ℕ, K ≤ j → JetField.pd ((), j)
        (v - topDescent K v * (jetRatio K : JetField C Unit)) = 0)
      ∧ IsWeightZero (v - topDescent K v * (jetRatio K : JetField C Unit))
      ∧ substitutionDeriv R ^ κ * jetSubstitution R hR
          (v - topDescent K v * (jetRatio K : JetField C Unit))
        = substitutionDeriv R * (v - topDescent K v * (jetRatio K : JetField C Unit))
          - stripDefect R K D (topDescent K v) (topDescent K D) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hK1 : 1 ≤ K := by omega
  have hPpd : JetField.pd ((), K) (topDescent K v) = 0 := by
    have h := hlin
    rw [topDescent] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero K hy1)
  have hPord : ∀ j : ℕ, K < j → JetField.pd ((), j) (topDescent K v) = 0 :=
    topDescent_order hK1 hvord
  have hzKpd : JetField.pd ((), K) (jetRatio K : JetField C Unit)
      = 1 / (JetField.jet ((), 1) : JetField C Unit) ^ K := pd_jetRatio_self (by omega)
  have hvpd : (JetField.jet ((), 1) : JetField C Unit) ^ K * JetField.pd ((), K) v
      = topDescent K v := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz
        (topDescent K v) (jetRatio K : JetField C Unit)
    simp only [smul_eq_mul] at hleib
    rcases eq_or_lt_of_le hj with heqj | hlt
    · subst heqj
      rw [map_sub, hleib, hPpd, hzKpd, mul_zero, add_zero]
      field_simp
      linear_combination hvpd
    · rw [map_sub, hleib, hPord j hlt, pd_jetRatio_of_ne (by omega) (by omega),
        mul_zero, mul_zero, add_zero, hvord j hlt, sub_zero]
  · exact hvwz.sub ((isWeightZero_topDescent hvwz).mul (isWeightZero_jetRatio K))
  · have hstep := jetSubstitution_topDescent R hR hK1 hvord heq
    have hzK := jetSubstitution_jetRatio R hR K
    have hpow : substitutionDeriv R ^ (κ + 1 - (K : ℤ)) * substitutionDeriv R ^ (K : ℕ)
        = substitutionDeriv R * substitutionDeriv R ^ κ := by
      rw [← zpow_natCast (substitutionDeriv R) K, ← zpow_add₀ hρ0,
        show κ + 1 - (K : ℤ) + (K : ℤ) = 1 + κ from by ring, zpow_add₀ hρ0, zpow_one]
    have hprod : substitutionDeriv R * substitutionDeriv R ^ κ
        * (jetSubstitution R hR (topDescent K v)
          * jetSubstitution R hR (jetRatio K : JetField C Unit))
        = (substitutionDeriv R * topDescent K v - topDescent K D)
          * (substitutionDeriv R * (jetRatio K : JetField C Unit)
            + substitutionShiftRatio R K) := by
      rw [← hpow]
      calc substitutionDeriv R ^ (κ + 1 - (K : ℤ)) * substitutionDeriv R ^ (K : ℕ)
            * (jetSubstitution R hR (topDescent K v)
              * jetSubstitution R hR (jetRatio K : JetField C Unit))
          = (substitutionDeriv R ^ (κ + 1 - (K : ℤ))
              * jetSubstitution R hR (topDescent K v))
            * (substitutionDeriv R ^ (K : ℕ)
              * jetSubstitution R hR (jetRatio K : JetField C Unit)) := by ring
        _ = _ := by rw [hstep, hzK]
    rw [map_sub, map_mul, stripDefect]
    field_simp
    linear_combination substitutionDeriv R * heq - hprod

/-! ## Linearity in the top coordinate -/

omit [CharZero C] in
theorem iterate_two_topDescent (K : ℕ) (x : JetField C Unit) :
    (topDescent (C := C) K)^[2] x = topDescent K (topDescent K x) := by
  rw [Function.iterate_succ_apply', Function.iterate_one]

/-- **Linearity in the top coordinate.**  Unless the exponent hits the resonance `κ = 2K − 1`, the
second descent of a solution vanishes, so the solution is affine in its top coordinate. -/
theorem topDescent_topDescent_eq_zero (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {K : ℕ}
    (hK : 1 ≤ K)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, K < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {v D : JetField C Unit} (hvwz : IsWeightZero v)
    (hvord : ∀ j : ℕ, K < j → JetField.pd ((), j) v = 0) {κ : ℤ}
    (heq : substitutionDeriv R ^ κ * jetSubstitution R hR v = substitutionDeriv R * v - D)
    (hD : topDescent K (topDescent K D) = 0)
    (hκ : κ + 1 - 2 * (K : ℤ) ≠ 0) :
    topDescent K (topDescent K v) = 0 := by
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  by_contra hne
  have h2 := jetSubstitution_topDescent_iterate R hR hK hvord heq 2
  rw [iterate_two_topDescent, iterate_two_topDescent, hD, sub_zero] at h2
  have hwz2 : IsWeightZero (topDescent K (topDescent K v)) :=
    isWeightZero_topDescent (isWeightZero_topDescent hvwz)
  have hord2 : ∀ j : ℕ, K < j →
      JetField.pd ((), j) (topDescent K (topDescent K v)) = 0 := by
    intro j hj
    have h := topDescent_iterate_order (C := C) hK hvord 2 j hj
    rwa [iterate_two_topDescent] at h
  have heig : substitutionDeriv R ^ (κ + ((2 : ℕ) : ℤ) * (1 - (K : ℤ)) - 1)
      * jetSubstitution R hR (topDescent K (topDescent K v))
      = topDescent K (topDescent K v) := by
    refine mul_left_cancel₀ hρ0 ?_
    rw [← mul_assoc, ← zpow_one_add₀ hρ0,
      show (1 : ℤ) + (κ + ((2 : ℕ) : ℤ) * (1 - (K : ℤ)) - 1)
        = κ + ((2 : ℕ) : ℤ) * (1 - (K : ℤ)) from by ring]
    exact h2
  have hzero := exponent_eq_zero_of_weightZero_eigen R hR hK hfix hwz2 hne hord2 heig
  apply hκ
  push_cast at hzero ⊢
  linarith

end

end GaloisForLFunctions.HTGeometry
