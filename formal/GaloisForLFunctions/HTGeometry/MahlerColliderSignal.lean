import GaloisForLFunctions.HTGeometry.GapSeriesIrrational

/-!
# A Mahler cosmological-collider signal

For an integer scale ratio `p ≥ 2`, the formal lacunary signal

`Mₚ(X) = ∑ₖ X^(p^k)`

is the unique zero-constant-term solution of the static Mahler constraint

`Mₚ(X) = X + Mₚ(X^p)`.

This module constructs the exact formal series, proves the constraint and its normalized
uniqueness, and proves that the series is not rational by its arbitrarily long support gaps.  It
does not claim the external rational-or-hypertranscendental Mahler theorem or a cosmological model.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

/-- Coefficient indicator of the geometric frequency tower `{p^k | k ≥ 0}`. -/
noncomputable def mahlerColliderCoefficient (p n : ℕ) : ℂ := by
  classical
  exact if ∃ k : ℕ, n = p ^ k then 1 else 0

/-- Formal positive-frequency signal supported on a geometric frequency tower. -/
noncomputable def mahlerColliderSignal (p : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.mk (mahlerColliderCoefficient p)

@[simp]
theorem coeff_mahlerColliderSignal (p n : ℕ) :
    coeff n (mahlerColliderSignal p) = mahlerColliderCoefficient p n := by
  simp [mahlerColliderSignal]

/-- A geometric frequency is either the boundary frequency `1` or one scale step above another
geometric frequency. -/
theorem exists_eq_pow_iff
    {p n : ℕ} (hp : 2 ≤ p) :
    (∃ k : ℕ, n = p ^ k) ↔
      n = 1 ∨ (p ∣ n ∧ ∃ k : ℕ, n / p = p ^ k) := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => simp
    | succ k =>
        right
        constructor
        · exact dvd_pow_self p (Nat.succ_ne_zero k)
        · refine ⟨k, ?_⟩
          rw [pow_succ, Nat.mul_div_left _ (by omega : 0 < p)]
  · rintro (rfl | ⟨hdiv, k, hk⟩)
    · exact ⟨0, by simp⟩
    · refine ⟨k + 1, ?_⟩
      rw [pow_succ]
      calc
        n = n / p * p := (Nat.div_mul_cancel hdiv).symm
        _ = p ^ k * p := by rw [hk]

/-- Coefficient recursion underlying the one-shell Mahler constraint. -/
theorem mahlerColliderCoefficient_recursion
    {p n : ℕ} (hp : 2 ≤ p) :
    mahlerColliderCoefficient p n =
      (if n = 1 then 1 else 0) +
        (if p ∣ n then mahlerColliderCoefficient p (n / p) else 0) := by
  classical
  rw [mahlerColliderCoefficient]
  rw [exists_eq_pow_iff hp]
  by_cases h1 : n = 1
  · subst n
    have hp1 : ¬p ∣ 1 := fun h => by
      have := Nat.dvd_one.mp h
      omega
    simp [hp1]
  · simp only [h1, false_or, if_false, zero_add]
    by_cases hd : p ∣ n
    · rw [if_pos hd]
      simp only [hd, true_and]
      rw [mahlerColliderCoefficient]
    · rw [if_neg hd]
      simp [hd]

/-- **Static Mahler constraint.** Removing the boundary frequency and scaling the remaining
frequency tower down by `p` reproduces the full signal. -/
theorem mahlerColliderSignal_constraint
    {p : ℕ} (hp : 2 ≤ p) :
    mahlerColliderSignal p =
      PowerSeries.X + PowerSeries.subst (PowerSeries.X ^ p) (mahlerColliderSignal p) := by
  ext n
  rw [map_add, PowerSeries.coeff_subst_X_pow (by omega : p ≠ 0)]
  rw [coeff_mahlerColliderSignal, mahlerColliderCoefficient_recursion hp]
  simp only [coeff_mahlerColliderSignal]
  by_cases h1 : n = 1
  · subst n
    have hp1 : ¬p ∣ 1 := fun h => by
      have := Nat.dvd_one.mp h
      omega
    simp [hp1]
  · simp [PowerSeries.coeff_X, h1]

/-- A Mahler-invariant formal series with zero constant coefficient is zero. -/
theorem mahlerInvariant_eq_zero
    {p : ℕ} (hp : 2 ≤ p) {Y : ℂ⟦X⟧}
    (hY : Y = PowerSeries.subst (PowerSeries.X ^ p) Y)
    (h0 : coeff 0 Y = 0) :
    Y = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · simpa [hn0] using h0
      · have hc := congrArg (PowerSeries.coeff n) hY
        rw [PowerSeries.coeff_subst_X_pow (by omega : p ≠ 0)] at hc
        by_cases hd : p ∣ n
        · rw [if_pos hd] at hc
          have hlt : n / p < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by omega)
          rw [ih (n / p) hlt] at hc
          exact hc
        · rw [if_neg hd] at hc
          exact hc

@[simp]
theorem coeff_zero_mahlerColliderSignal
    {p : ℕ} (hp : 2 ≤ p) :
    coeff 0 (mahlerColliderSignal p) = 0 := by
  rw [coeff_mahlerColliderSignal, mahlerColliderCoefficient]
  apply if_neg
  rintro ⟨k, hk⟩
  have hpos : 0 < p ^ k := pow_pos (by omega : 0 < p) k
  omega

/-- **Constraint uniqueness.** The zero-constant-term Mahler constraint determines the complete
geometric-frequency signal coefficientwise. -/
theorem mahlerColliderSignal_unique
    {p : ℕ} (hp : 2 ≤ p) {Y : ℂ⟦X⟧}
    (hY : Y = PowerSeries.X + PowerSeries.subst (PowerSeries.X ^ p) Y)
    (h0 : coeff 0 Y = 0) :
    Y = mahlerColliderSignal p := by
  apply sub_eq_zero.mp
  apply mahlerInvariant_eq_zero hp
  · calc
      Y - mahlerColliderSignal p =
          (PowerSeries.X + PowerSeries.subst (PowerSeries.X ^ p) Y) -
            (PowerSeries.X + PowerSeries.subst (PowerSeries.X ^ p)
              (mahlerColliderSignal p)) := by
                rw [← hY, ← mahlerColliderSignal_constraint hp]
      _ = PowerSeries.subst (PowerSeries.X ^ p) Y -
            PowerSeries.subst (PowerSeries.X ^ p) (mahlerColliderSignal p) := by ring
      _ = PowerSeries.subst (PowerSeries.X ^ p)
            (Y - mahlerColliderSignal p) := by
              rw [← PowerSeries.coe_substAlgHom
                (PowerSeries.HasSubst.X_pow (by omega : p ≠ 0)),
                map_sub, PowerSeries.coe_substAlgHom]
  · rw [map_sub, h0, coeff_zero_mahlerColliderSignal hp, sub_zero]

/-- **Support-gap nonrationality.** The normalized Mahler signal is not the power-series expansion
of any rational function. -/
theorem mahlerColliderSignal_not_rational
    {p : ℕ} (hp : 2 ≤ p) (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    (Q : ℂ⟦X⟧) * mahlerColliderSignal p ≠ (P : ℂ⟦X⟧) := by
  apply powerSeries_not_rational_of_gaps (A := mahlerColliderSignal p) _ P Q hQ
  intro g M
  let L := max g M
  refine ⟨p ^ (L + 1), ?_, ?_, ?_⟩
  · have hML : M ≤ L := le_max_right _ _
    have hLpow : L < 2 ^ L := Nat.lt_two_pow_self
    have h2p : 2 ^ L ≤ p ^ L := Nat.pow_le_pow_left hp L
    have hstep : p ^ L ≤ p ^ (L + 1) :=
      Nat.pow_le_pow_right (by omega : 0 < p) (Nat.le_succ L)
    omega
  · rw [coeff_mahlerColliderSignal, mahlerColliderCoefficient]
    simp
  · intro k hklo hkhi
    rw [coeff_mahlerColliderSignal, mahlerColliderCoefficient]
    apply if_neg
    rintro ⟨m, rfl⟩
    have hm : m < L + 1 :=
      (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp hkhi
    have hpowle : p ^ m ≤ p ^ L :=
      Nat.pow_le_pow_right (by omega : 0 < p) (by omega)
    have hLpow : g < 2 ^ L :=
      lt_of_le_of_lt (le_max_left g M) Nat.lt_two_pow_self
    have h2p : 2 ^ L ≤ p ^ L := Nat.pow_le_pow_left hp L
    have hsplit : p ^ (L + 1) = p ^ L * p := by rw [pow_succ]
    have hgap : g < p ^ (L + 1) - p ^ L := by
      rw [hsplit]
      have hmul : p ^ L + p ^ L ≤ p ^ L * p := by
        simpa [mul_two] using Nat.mul_le_mul_left (p ^ L) hp
      have hdiff : p ^ L ≤ p ^ L * p - p ^ L :=
        Nat.le_sub_of_add_le hmul
      exact lt_of_lt_of_le (lt_of_lt_of_le hLpow h2p) hdiff
    omega

end GaloisForLFunctions.HTGeometry
