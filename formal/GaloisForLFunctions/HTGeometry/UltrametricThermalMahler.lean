import GaloisForLFunctions.HTGeometry.MahlerColliderSignal

/-!
# Ultrametric thermal Mahler constraint

For an integer branching ratio `p ≥ 2`, this module constructs the formal reduced one-particle
heat trace attached to the exact ultrametric shell spectrum

`Kₚ(X) = (p - 2) X + (p - 1)² ∑_{k ≥ 1} p^(k - 1) X^(p^k)`.

It proves coefficientwise that this trace is the unique formal solution of

`Kₚ(X) = (p - 2) X + X^p + p Kₚ(X^p)`.

The external physical identification of the coefficients and the external Mahler
hypertranscendence theorem are not claimed here.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

/-- The geometrically weighted shell series `∑_{k ≥ 0} p^k X^(p^k)`. -/
noncomputable def branchingThermalSignal (p : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.mk (fun n => (n : ℂ) * mahlerColliderCoefficient p n)

@[simp]
theorem coeff_branchingThermalSignal (p n : ℕ) :
    coeff n (branchingThermalSignal p) =
      (n : ℂ) * mahlerColliderCoefficient p n := by
  simp [branchingThermalSignal]

/-- Coefficient recursion for the geometrically weighted shell series. -/
theorem branchingThermalCoefficient_recursion
    {p n : ℕ} (hp : 2 ≤ p) :
    (n : ℂ) * mahlerColliderCoefficient p n =
      (if n = 1 then 1 else 0) +
        (p : ℂ) *
          (if p ∣ n then
            (n / p : ℕ) * mahlerColliderCoefficient p (n / p)
          else 0) := by
  rw [mahlerColliderCoefficient_recursion hp]
  by_cases h1 : n = 1
  · subst n
    have hp1 : ¬p ∣ 1 := fun h => by
      have := Nat.dvd_one.mp h
      omega
    simp [hp1]
  · by_cases hd : p ∣ n
    · simp only [h1, if_false, zero_add, hd, if_true]
      have hncast : (n : ℂ) = (n / p : ℕ) * (p : ℕ) := by
        exact_mod_cast (Nat.div_mul_cancel hd).symm
      rw [hncast]
      ring
    · simp [h1, hd]

/-- The weighted shell series is fixed by one static branching constraint. -/
theorem branchingThermalSignal_constraint
    {p : ℕ} (hp : 2 ≤ p) :
    branchingThermalSignal p =
      PowerSeries.X + PowerSeries.C (p : ℂ) *
        PowerSeries.subst (PowerSeries.X ^ p) (branchingThermalSignal p) := by
  ext n
  rw [map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_subst_X_pow (by omega : p ≠ 0)]
  rw [coeff_branchingThermalSignal,
    branchingThermalCoefficient_recursion hp]
  simp only [coeff_branchingThermalSignal]
  by_cases h1 : n = 1
  · subst n
    have hp1 : ¬p ∣ 1 := fun h => by
      have := Nat.dvd_one.mp h
      omega
    simp [PowerSeries.coeff_X, hp1]
  · simp [PowerSeries.coeff_X, h1]

/-- A formal series invariant under weighted branching is zero.  Unlike the unweighted Mahler
constraint, no separate constant-term normalization is needed because `p ≠ 1`. -/
theorem branchingThermalInvariant_eq_zero
    {p : ℕ} (hp : 2 ≤ p) {Y : ℂ⟦X⟧}
    (hY : Y = PowerSeries.C (p : ℂ) *
      PowerSeries.subst (PowerSeries.X ^ p) Y) :
    Y = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hc := congrArg (PowerSeries.coeff n) hY
      rw [PowerSeries.coeff_C_mul,
        PowerSeries.coeff_subst_X_pow (by omega : p ≠ 0)] at hc
      by_cases hn0 : n = 0
      · subst n
        simp only [dvd_zero, if_true, Nat.zero_div] at hc
        have hpC : (p : ℂ) ≠ 1 := by exact_mod_cast (by omega : p ≠ 1)
        have hfac : ((p : ℂ) - 1) * coeff 0 Y = 0 := by
          calc
            ((p : ℂ) - 1) * coeff 0 Y =
                (p : ℂ) * coeff 0 Y - coeff 0 Y := by ring
            _ = 0 := sub_eq_zero.mpr hc.symm
        rcases mul_eq_zero.mp hfac with hbad | hzero
        · exact absurd (sub_eq_zero.mp hbad) hpC
        · exact hzero
      · by_cases hd : p ∣ n
        · rw [if_pos hd] at hc
          have hlt : n / p < n :=
            Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
          rw [ih (n / p) hlt] at hc
          simpa using hc
        · rw [if_neg hd] at hc
          simpa using hc

/-- The weighted branching constraint has a unique formal solution. -/
theorem branchingThermalSignal_unique
    {p : ℕ} (hp : 2 ≤ p) {Y : ℂ⟦X⟧}
    (hY : Y = PowerSeries.X + PowerSeries.C (p : ℂ) *
      PowerSeries.subst (PowerSeries.X ^ p) Y) :
    Y = branchingThermalSignal p := by
  apply sub_eq_zero.mp
  apply branchingThermalInvariant_eq_zero hp
  calc
    Y - branchingThermalSignal p =
        (PowerSeries.X + PowerSeries.C (p : ℂ) *
          PowerSeries.subst (PowerSeries.X ^ p) Y) -
        (PowerSeries.X + PowerSeries.C (p : ℂ) *
          PowerSeries.subst (PowerSeries.X ^ p)
            (branchingThermalSignal p)) := by
              rw [← hY, ← branchingThermalSignal_constraint hp]
    _ = PowerSeries.C (p : ℂ) *
        (PowerSeries.subst (PowerSeries.X ^ p) Y -
          PowerSeries.subst (PowerSeries.X ^ p)
            (branchingThermalSignal p)) := by ring
    _ = PowerSeries.C (p : ℂ) *
        PowerSeries.subst (PowerSeries.X ^ p)
          (Y - branchingThermalSignal p) := by
            rw [← PowerSeries.coe_substAlgHom
              (PowerSeries.HasSubst.X_pow (by omega : p ≠ 0)),
              map_sub, PowerSeries.coe_substAlgHom]

/-- The reduced ultrametric one-particle thermal signal.  The affine combination rewrites the
coefficient at `X` as `p - 2` and every coefficient at `X^(p^k)`, `k ≥ 1`, as
`(p - 1)² p^(k - 1)`. -/
noncomputable def ultrametricThermalSignal (p : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.C (-1 / (p : ℂ)) * PowerSeries.X +
    PowerSeries.C ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
      branchingThermalSignal p

@[simp]
theorem coeff_ultrametricThermalSignal (p n : ℕ) :
    coeff n (ultrametricThermalSignal p) =
      (-1 / (p : ℂ)) * (if n = 1 then 1 else 0) +
        ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
          ((n : ℂ) * mahlerColliderCoefficient p n) := by
  simp [ultrametricThermalSignal, PowerSeries.coeff_X]

/-- Coefficient form of the exact affine ultrametric thermal constraint. -/
theorem ultrametricThermalCoefficient_recursion
    {p n : ℕ} (hp : 2 ≤ p) :
    (-1 / (p : ℂ)) * (if n = 1 then 1 else 0) +
        ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
          ((n : ℂ) * mahlerColliderCoefficient p n) =
      ((p : ℂ) - 2) * (if n = 1 then 1 else 0) +
        (if n = p then 1 else 0) +
          (p : ℂ) *
            (if p ∣ n then
              (-1 / (p : ℂ)) * (if n / p = 1 then 1 else 0) +
                ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
                  (((n / p : ℕ) : ℂ) *
                    mahlerColliderCoefficient p (n / p))
            else 0) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [branchingThermalCoefficient_recursion hp]
  by_cases h1 : n = 1
  · subst n
    have hp1 : ¬p ∣ 1 := fun h => by
      have := Nat.dvd_one.mp h
      omega
    have h1p : 1 ≠ p := by omega
    simp [hp1, h1p]
    field_simp [hp0]
    ring
  · by_cases hd : p ∣ n
    · have hnp : n = p ↔ n / p = 1 := by
        constructor
        · intro hn
          subst n
          exact Nat.div_self (by omega)
        · intro hn
          simpa [hn] using (Nat.div_mul_cancel hd).symm
      simp only [h1, if_false, zero_add, hd, if_true]
      by_cases hnp' : n = p
      · simp [hnp', Nat.div_self (by omega : 0 < p)]
        field_simp [hp0]
        ring
      · have hquot : n / p ≠ 1 := fun h => hnp'.elim (hnp.mpr h)
        simp [hnp', hquot]
        ring
    · have hnp : n ≠ p := fun h => hd (h ▸ dvd_rfl)
      simp [h1, hd, hnp]

/-- **Exact thermal constraint.** The finite boundary defect and one scale substitution determine
the complete ultrametric thermal signal. -/
theorem ultrametricThermalSignal_constraint
    {p : ℕ} (hp : 2 ≤ p) :
    ultrametricThermalSignal p =
      PowerSeries.C ((p : ℂ) - 2) * PowerSeries.X +
        PowerSeries.X ^ p +
          PowerSeries.C (p : ℂ) *
            PowerSeries.subst (PowerSeries.X ^ p)
              (ultrametricThermalSignal p) := by
  ext n
  rw [map_add, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_subst_X_pow (by omega : p ≠ 0)]
  rw [coeff_ultrametricThermalSignal,
    ultrametricThermalCoefficient_recursion hp]
  simp only [coeff_ultrametricThermalSignal]
  simp [PowerSeries.coeff_X]

/-- **Constraint uniqueness.** No normalization or initial datum is required in addition to the
affine ultrametric thermal constraint. -/
theorem ultrametricThermalSignal_unique
    {p : ℕ} (hp : 2 ≤ p) {Y : ℂ⟦X⟧}
    (hY : Y = PowerSeries.C ((p : ℂ) - 2) * PowerSeries.X +
      PowerSeries.X ^ p + PowerSeries.C (p : ℂ) *
        PowerSeries.subst (PowerSeries.X ^ p) Y) :
    Y = ultrametricThermalSignal p := by
  apply sub_eq_zero.mp
  apply branchingThermalInvariant_eq_zero hp
  calc
    Y - ultrametricThermalSignal p =
        (PowerSeries.C ((p : ℂ) - 2) * PowerSeries.X +
          PowerSeries.X ^ p + PowerSeries.C (p : ℂ) *
            PowerSeries.subst (PowerSeries.X ^ p) Y) -
        (PowerSeries.C ((p : ℂ) - 2) * PowerSeries.X +
          PowerSeries.X ^ p + PowerSeries.C (p : ℂ) *
            PowerSeries.subst (PowerSeries.X ^ p)
              (ultrametricThermalSignal p)) := by
                rw [← hY, ← ultrametricThermalSignal_constraint hp]
    _ = PowerSeries.C (p : ℂ) *
        (PowerSeries.subst (PowerSeries.X ^ p) Y -
          PowerSeries.subst (PowerSeries.X ^ p)
            (ultrametricThermalSignal p)) := by ring
    _ = PowerSeries.C (p : ℂ) *
        PowerSeries.subst (PowerSeries.X ^ p)
          (Y - ultrametricThermalSignal p) := by
            rw [← PowerSeries.coe_substAlgHom
              (PowerSeries.HasSubst.X_pow (by omega : p ≠ 0)),
              map_sub, PowerSeries.coe_substAlgHom]

end GaloisForLFunctions.HTGeometry
