import GaloisForLFunctions.HTGeometry.JetUniformLevel

/-!
# Removing the top coordinate from a normalizing shift

The two coordinate laws multiply: `R'^{N+2}·Φ(z₂·z_N) = (R'z₂ + R'')·(R'z_N + s_N)`.  Subtracting
the pinned top term of a normalizing shift therefore produces a solution of the same shape one jet
order lower, with the shift replaced by an explicit defect

`s_{N+1} − (N+1)·(R'·R''·z_N + R'·z₂·s_N + R''·s_N)/R'`,

and the exponent unchanged.  This is the step that carries a normalizing shift at an arbitrary level
down to the next coordinate without any level-dependent case analysis.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

/-- **The product of the two coordinate laws.** -/
theorem jetSubstitution_jetRatio_two_mul (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (N : ℕ) :
    substitutionDeriv R ^ (N + 2)
        * (jetSubstitution R hR ((jetRatio 2 : JetField C Unit) * (jetRatio N : JetField C Unit)))
      = (substitutionDeriv R * (jetRatio 2 : JetField C Unit)
          + JetField.pd ((), 0) (substitutionDeriv R))
        * (substitutionDeriv R * (jetRatio N : JetField C Unit)
          + substitutionShiftRatio R N) := by
  have h2 := jetSubstitution_jetRatio R hR 2
  rw [substitutionShiftRatio_two] at h2
  have hN := jetSubstitution_jetRatio R hR N
  have hsplit : substitutionDeriv R ^ (N + 2)
      = substitutionDeriv R ^ (2 : ℕ) * substitutionDeriv R ^ N := by
    rw [← pow_add]
    congr 1
    omega
  rw [map_mul, hsplit]
  calc substitutionDeriv R ^ (2 : ℕ) * substitutionDeriv R ^ N
        * (jetSubstitution R hR (jetRatio 2 : JetField C Unit)
          * jetSubstitution R hR (jetRatio N : JetField C Unit))
      = (substitutionDeriv R ^ (2 : ℕ) * jetSubstitution R hR (jetRatio 2 : JetField C Unit))
        * (substitutionDeriv R ^ N
          * jetSubstitution R hR (jetRatio N : JetField C Unit)) := by ring
    _ = _ := by rw [h2, hN]

/-- The defect left behind after removing the pinned top term of a normalizing shift. -/
def zshiftDefect (R : RatFunc C) (N : ℕ) : JetField C Unit :=
  substitutionShiftRatio R (N + 1)
    - ((N + 1 : ℕ) : JetField C Unit)
      * (substitutionDeriv R * JetField.pd ((), 0) (substitutionDeriv R)
            * (jetRatio N : JetField C Unit)
          + substitutionDeriv R * (jetRatio 2 : JetField C Unit) * substitutionShiftRatio R N
          + JetField.pd ((), 0) (substitutionDeriv R) * substitutionShiftRatio R N)
      / substitutionDeriv R

/-- **The stripped shift.**  Removing the pinned top term of a normalizing shift at level `N + 1`
leaves a torus-invariant solution of jet order at most `N − 1` with the same exponent and with the
shift replaced by the defect. -/
theorem zshift_strip (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) {N : ℕ} (hN : 3 ≤ N)
    (hfix : ∀ g : JetField C Unit, (∀ j : ℕ, N < j → JetField.pd ((), j) g = 0) →
      jetSubstitution R hR g = g → ∃ e : C, g = algebraMap C (JetField C Unit) e)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (hord : ∀ j : ℕ, N < j → JetField.pd ((), j) w = 0)
    (heq : substitutionDeriv R ^ (N + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (N + 1)) :
    IsWeightZero (w + ((N + 1 : ℕ) : JetField C Unit)
        * (jetRatio 2 : JetField C Unit) * (jetRatio N : JetField C Unit))
      ∧ (∀ j : ℕ, N ≤ j → JetField.pd ((), j)
          (w + ((N + 1 : ℕ) : JetField C Unit)
            * (jetRatio 2 : JetField C Unit) * (jetRatio N : JetField C Unit)) = 0)
      ∧ substitutionDeriv R ^ (N + 1) * jetSubstitution R hR
          (w + ((N + 1 : ℕ) : JetField C Unit)
            * (jetRatio 2 : JetField C Unit) * (jetRatio N : JetField C Unit))
        = substitutionDeriv R * (w + ((N + 1 : ℕ) : JetField C Unit)
            * (jetRatio 2 : JetField C Unit) * (jetRatio N : JetField C Unit))
          - zshiftDefect R N := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  have hcast : ((N + 1 : ℕ) : JetField C Unit)
      = algebraMap C (JetField C Unit) (((N + 1 : ℕ) : C)) :=
    (map_natCast (algebraMap C (JetField C Unit)) (N + 1)).symm
  obtain ⟨htop, -⟩ := topDescent_of_zshift R hR hN hfix hwz hord heq
  refine ⟨?_, ?_, ?_⟩
  · refine IsWeightZero.add hwz ?_
    refine IsWeightZero.mul (IsWeightZero.mul ?_ (isWeightZero_jetRatio 2)) (isWeightZero_jetRatio N)
    rw [hcast]
    exact isWeightZero_algebraMap _
  · intro j hj
    have hleib := (JetField.pd ((), j) :
      Derivation C (JetField C Unit) (JetField C Unit)).leibniz
        (((N + 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit))
        (jetRatio N : JetField C Unit)
    simp only [smul_eq_mul] at hleib
    have hcpd : JetField.pd ((), j)
        (((N + 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit))
        = ((N + 1 : ℕ) : JetField C Unit) * JetField.pd ((), j) (jetRatio 2 : JetField C Unit) := by
      have h := (JetField.pd ((), j) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (((N + 1 : ℕ) : JetField C Unit)) (jetRatio 2 : JetField C Unit)
      simp only [smul_eq_mul] at h
      rw [h, hcast, Derivation.map_algebraMap, mul_zero, add_zero, ← hcast]
    have hz2 : JetField.pd ((), j) (jetRatio 2 : JetField C Unit) = 0 :=
      pd_jetRatio_of_ne (by omega) (by omega)
    rcases eq_or_lt_of_le hj with heqj | hlt
    · -- the pinned coefficient cancels the top partial of `w`
      subst heqj
      have htop' : (JetField.jet ((), 1) : JetField C Unit) ^ N * JetField.pd ((), N) w
          = -(((N + 1 : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit)) := by
        have h := htop
        rw [topDescent] at h
        rw [h, hcast]
      rw [map_add, hleib, hcpd, hz2, mul_zero, mul_zero, add_zero,
        pd_jetRatio_self (show N ≠ 1 by omega)]
      field_simp
      linear_combination htop'
    · rw [map_add, hleib, hcpd, hz2, mul_zero, mul_zero, add_zero,
        pd_jetRatio_of_ne (by omega) (by omega), mul_zero, hord j hlt, add_zero]
  · have hprod := jetSubstitution_jetRatio_two_mul R hR N
    have hpow : substitutionDeriv R ^ (N + 2)
        = substitutionDeriv R * substitutionDeriv R ^ (N + 1) := by
      rw [← pow_succ']
    rw [hpow, map_mul] at hprod
    rw [map_add, map_mul, map_mul, map_natCast, zshiftDefect]
    field_simp
    linear_combination substitutionDeriv R * heq
      + ((N + 1 : ℕ) : JetField C Unit) * hprod

end

end GaloisForLFunctions.HTGeometry
