import GaloisForLFunctions.HTGeometry.JetInverseTower

/-!
# Normalizing shifts propagate upwards

A torus-invariant solution of the shift relation at level `m + 1` produces one at level `m + 2`:

`w' = ∇w + m·z₂·w − z₂·z_{m+1}`.

Applying `∇` to the relation and using `∇(Φ v) = R'·Φ(∇v)` together with the covariant recursion
`s_{k+1} = ∇s_k + k·z₂·s_k + R''(y₀)·z_k` makes every term cancel except the next shift.  So the
levels at which a normalizing shift exists form an upward-closed set, and killing the even levels
kills them all.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {C : Type*} [Field C] [CharZero C]

theorem jetNabla_substitutionDeriv (R : RatFunc C) :
    jetNabla (substitutionDeriv R) = JetField.pd ((), 0) (substitutionDeriv R) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  rw [jetNabla_apply,
    jetDerivation_of_order_zero (fun k hk => pd_substitutionDeriv_eq_zero R hk)]
  field_simp

theorem isWeightZero_jetNabla {v : JetField C Unit} (hv : IsWeightZero v) :
    IsWeightZero (jetNabla v) := by
  have h2 : (2 : C) ≠ 0 := two_ne_zero
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hA : algebraMap C (JetField C Unit) (2 : C) ≠ 0 := by
    intro hh
    exact absurd ((algebraMap C (JetField C Unit)).injective (by rw [hh, map_zero])) h2
  show weightScale h2 (jetNabla v) = jetNabla v
  rw [jetNabla_apply, map_div₀, weightScale_jetDerivation,
    show weightScale h2 v = v from hv, weightScale_jet, pow_one]
  field_simp

/-- **Normalizing shifts propagate to the next level.** -/
theorem zshift_succ (R : RatFunc C) (hR : substitutionDeriv R ≠ 0) (m : ℕ)
    {w : JetField C Unit} (hwz : IsWeightZero w)
    (hord : ∀ j : ℕ, m < j → JetField.pd ((), j) w = 0)
    (heq : substitutionDeriv R ^ (m + 1) * jetSubstitution R hR w
      = substitutionDeriv R * w - substitutionShiftRatio R (m + 1)) :
    IsWeightZero (jetNabla w + ((m : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit) * w
        - (jetRatio 2 : JetField C Unit) * (jetRatio (m + 1) : JetField C Unit))
      ∧ (∀ j : ℕ, m + 1 < j → JetField.pd ((), j)
          (jetNabla w + ((m : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit) * w
            - (jetRatio 2 : JetField C Unit) * (jetRatio (m + 1) : JetField C Unit)) = 0)
      ∧ substitutionDeriv R ^ (m + 1 + 1) * jetSubstitution R hR
          (jetNabla w + ((m : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit) * w
            - (jetRatio 2 : JetField C Unit) * (jetRatio (m + 1) : JetField C Unit))
        = substitutionDeriv R
            * (jetNabla w + ((m : ℕ) : JetField C Unit) * (jetRatio 2 : JetField C Unit) * w
              - (jetRatio 2 : JetField C Unit) * (jetRatio (m + 1) : JetField C Unit))
          - substitutionShiftRatio R (m + 1 + 1) := by
  have hy1 : (JetField.jet ((), 1) : JetField C Unit) ≠ 0 := jet_ne_zero _
  have hρ0 : substitutionDeriv R ≠ 0 := hR
  refine ⟨?_, ?_, ?_⟩
  · refine ((isWeightZero_jetNabla hwz).add ?_).sub
      ((isWeightZero_jetRatio 2).mul (isWeightZero_jetRatio (m + 1)))
    refine IsWeightZero.mul (IsWeightZero.mul ?_ (isWeightZero_jetRatio 2)) hwz
    rw [show ((m : ℕ) : JetField C Unit) = algebraMap C (JetField C Unit) ((m : ℕ) : C) from
      (map_natCast (algebraMap C (JetField C Unit)) m).symm]
    exact isWeightZero_algebraMap _
  · intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hnab : JetField.pd ((), i + 1) (jetNabla w) = 0 := by
      have hinv : JetField.pd ((), i + 1)
          ((JetField.jet ((), 1) : JetField C Unit)⁻¹) = 0 :=
        pd_inv_eq_zero (JetField.pd_jet_of_ne (by
          simp only [ne_eq, Prod.mk.injEq, true_and]; omega))
      have hl := (JetField.pd ((), i + 1) :
        Derivation C (JetField C Unit) (JetField C Unit)).leibniz
          (JetField.jetDerivation w) ((JetField.jet ((), 1) : JetField C Unit)⁻¹)
      simp only [smul_eq_mul] at hl
      rw [jetNabla_apply, div_eq_mul_inv, hl, hinv, mul_zero, zero_add,
        ← JetField.deriv_eq, JetField.pd_deriv_succ, JetField.deriv_eq,
        hord (i + 1) (by omega), hord i (by omega), map_zero, add_zero, mul_zero]
    rw [map_sub, map_add, hnab,
      pd_mul_eq_zero (pd_mul_eq_zero (pd_natCast_eq_zero _ _)
        (pd_jetRatio_of_ne (by omega) (by omega))) (hord (i + 1) (by omega)),
      pd_mul_eq_zero (pd_jetRatio_of_ne (by omega) (by omega))
        (pd_jetRatio_of_ne (by omega) (by omega)), add_zero, sub_zero]
  · -- the substitution law
    have hρ1 : jetNabla (substitutionDeriv R) = JetField.pd ((), 0) (substitutionDeriv R) :=
      jetNabla_substitutionDeriv R
    have hpow : jetNabla (substitutionDeriv R ^ (m + 1))
        = ((m + 1 : ℕ) : JetField C Unit) * substitutionDeriv R ^ m
          * JetField.pd ((), 0) (substitutionDeriv R) := by
      have h := (jetNabla (C := C)).leibniz_pow (substitutionDeriv R) (m + 1)
      simp only [smul_eq_mul, hρ1, Nat.add_sub_cancel] at h
      rw [h]
      push_cast
      ring
    -- differentiate the relation covariantly
    have hnabeq := congrArg (fun v => jetNabla v) heq
    simp only at hnabeq
    have hL := (jetNabla (C := C)).leibniz (substitutionDeriv R ^ (m + 1))
      (jetSubstitution R hR w)
    have hR' := (jetNabla (C := C)).leibniz (substitutionDeriv R) w
    simp only [smul_eq_mul] at hL hR'
    rw [map_sub, hL, hR', hpow, hρ1,
      ← jetSubstitution_jetNabla R hR w] at hnabeq
    -- the coordinate laws
    have h2 := jetSubstitution_jetRatio R hR 2
    rw [substitutionShiftRatio_two] at h2
    have hm := jetSubstitution_jetRatio R hR (m + 1)
    have hsucc := substitutionShiftRatio_succ R (m + 1)
    have hnz := jetNabla_jetRatio (C := C) (m + 1)
    rw [map_sub, map_add, map_mul, map_mul, map_natCast]
    field_simp
    linear_combination
      (substitutionDeriv R ^ (m + 1) * substitutionDeriv R) * hnabeq
      - (substitutionDeriv R ^ (m + 1) * substitutionDeriv R
          * ((m : ℕ) : JetField C Unit) * w
        + substitutionDeriv R ^ (m + 1) * substitutionDeriv R
          * (jetRatio (m + 1) : JetField C Unit)) * h2
      - (substitutionDeriv R * substitutionDeriv R
          * ((m : ℕ) : JetField C Unit) * jetSubstitution R hR (jetRatio 2 : JetField C Unit)
        ) * heq
      + (substitutionDeriv R ^ (m + 1) * substitutionDeriv R
          * (jetRatio 2 : JetField C Unit)) * hm
      - (substitutionDeriv R ^ (m + 1) * substitutionDeriv R ^ 2) * hsucc

end

end GaloisForLFunctions.HTGeometry
