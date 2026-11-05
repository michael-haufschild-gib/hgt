import GaloisForLFunctions.ArithmeticDiscreteness.FinitelyManyOrdersCertifyIntegralPurity

/-!
# The certificate length grows with `q`

The finite certificate of `FinitelyManyOrdersCertifyIntegralPurity` has an unavoidable cost. The
integral trace polynomial `X − m`, `m = ⌊2√q⌋ + 1`, is impure, but its eigenvalues
`α, β = (m ± √(m² − 4q))/2` have `α/√q = r` with `(r − 1)² ≤ r(r + 1/r − 2) ≤ 3/√q`, so
`α^ν ≤ e · q^{ν/2}` as long as `9ν⁴ ≤ q` (`quarter_power_mimic`). Hence any size bound
`|S_ν| ≤ 2e · q^{ν/2}` at orders `ν ≤ (q/9)^{1/4}` is satisfied by an impure integral
configuration: a certificate with `B = 2e` needs orders beyond `(q/9)^{1/4}`.

Integrality makes certification finite, but the number of orders it needs grows with the quantization
scale, which shrinks as `q` grows.
-/

open Polynomial Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **An impure integral configuration passes every order `ν` with `9ν⁴ ≤ q`.** -/
theorem quarter_power_mimic (q : ℕ) (hq : 1 ≤ q) :
    ∃ h : ℤ[X], h.Monic ∧ h.natDegree = 1 ∧ (∃ τ ∈ (toC h).roots, ¬ IsPureTrace q τ) ∧
      ∃ z : Fin 2 → ℂ, IsEigenConfig q h Finset.univ z ∧
        ∀ ν : ℕ, 9 * (ν : ℝ) ^ 4 ≤ q →
          ‖∑ i, z i ^ ν‖ ≤ 2 * Real.exp 1 * Real.sqrt q ^ ν := by
  set m : ℕ := ⌊2 * Real.sqrt q⌋₊ + 1 with hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hs1 : 1 ≤ Real.sqrt q := by rw [Real.one_le_sqrt]; exact_mod_cast hq
  have hmgt : 2 * Real.sqrt q < m := by rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have hmle : (m : ℝ) ≤ 2 * Real.sqrt q + 1 := by
    rw [hm]; push_cast; linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt q)]
  have hdisc : 0 ≤ (m : ℝ) ^ 2 - 4 * q := by nlinarith
  set D : ℝ := Real.sqrt ((m : ℝ) ^ 2 - 4 * q) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hDsq : D ^ 2 = (m : ℝ) ^ 2 - 4 * q := Real.sq_sqrt hdisc
  set α : ℝ := ((m : ℝ) + D) / 2 with hα
  set β : ℝ := ((m : ℝ) - D) / 2 with hβ
  have hαβ : α * β = q := by rw [hα, hβ]; nlinarith
  have hsum : α + β = m := by rw [hα, hβ]; ring
  have hDm : D < m := by
    rw [hD, Real.sqrt_lt' (by positivity)]; linarith
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hα0 : 0 < α := by rw [hα]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hβα : β ≤ α := by rw [hα, hβ]; linarith
  refine ⟨X - C (m : ℤ), monic_X_sub_C _, natDegree_X_sub_C _, ⟨(m : ℂ), ?_, ?_⟩,
    ![(α : ℂ), (β : ℂ)], ⟨?_, ?_, ?_⟩, fun ν hν => ?_⟩
  · rw [mem_roots (toC_ne_zero (monic_X_sub_C _))]; simp [toC]
  · rintro ⟨-, hle⟩
    simp only [natCast_re, Nat.abs_cast] at hle
    linarith
  · intro i _
    fin_cases i <;> simp [hα0.ne', hβ0.ne']
  · have hqc : (q : ℂ) = (α : ℂ) * (β : ℂ) := by exact_mod_cast hαβ.symm
    intro i _
    fin_cases i
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.zero_eta]
      rw [hqc]; field_simp [show (α : ℂ) ≠ 0 by exact_mod_cast hα0.ne']
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one]
      rw [hqc]; field_simp [show (β : ℂ) ≠ 0 by exact_mod_cast hβ0.ne']
  · intro τ hτ
    have hτ' : τ = (m : ℂ) := by
      rw [mem_roots (toC_ne_zero (monic_X_sub_C _))] at hτ
      simpa [toC, sub_eq_zero] using hτ
    refine ⟨0, Finset.mem_univ _, ?_⟩
    simp only [Matrix.cons_val_zero]
    have hqc : (q : ℂ) = (α : ℂ) * (β : ℂ) := by exact_mod_cast hαβ.symm
    rw [hqc, hτ', mul_div_cancel_left₀ _ (show (α : ℂ) ≠ 0 by exact_mod_cast hα0.ne')]
    exact_mod_cast hsum
  · -- `α^ν ≤ e q^{ν/2}`
    have hs0 : 0 < Real.sqrt q := by linarith
    have hαm : α ^ 2 + q = α * m := by rw [← hsum, ← hαβ]; ring
    have hαs : Real.sqrt q ≤ α := by
      by_contra hlt
      push Not at hlt
      have h1 : α ^ 2 < q := by nlinarith
      have h2 : q ≤ α ^ 2 := by rw [← hαβ, sq]; exact mul_le_mul_of_nonneg_left hβα hα0.le
      linarith
    -- `(α − √q)² = α(m − 2√q) ≤ α ≤ 3√q`
    have hdev : (α - Real.sqrt q) ^ 2 ≤ 3 * Real.sqrt q := by
      have h1 : (α - Real.sqrt q) ^ 2 = α * (m - 2 * Real.sqrt q) := by
        have : (α - Real.sqrt q) ^ 2 = α ^ 2 + Real.sqrt q ^ 2 - 2 * α * Real.sqrt q := by ring
        rw [this, hsq, hαm]; ring
      have h2 : α ≤ 3 * Real.sqrt q := by
        have : α ≤ m := by linarith
        linarith
      rw [h1]
      calc α * (m - 2 * Real.sqrt q) ≤ α * 1 := mul_le_mul_of_nonneg_left (by linarith) hα0.le
        _ ≤ 3 * Real.sqrt q := by linarith
    set u : ℝ := (α - Real.sqrt q) / Real.sqrt q with hu
    have hu0 : 0 ≤ u := div_nonneg (by linarith) hs0.le
    have hαu : α = Real.sqrt q * (1 + u) := by rw [hu]; field_simp; ring
    have hνu : (ν : ℝ) * u ≤ 1 := by
      have h3 : 3 * (ν : ℝ) ^ 2 ≤ Real.sqrt q := by
        rw [Real.le_sqrt (by positivity) hq0.le]; nlinarith
      have hu2 : u ^ 2 ≤ 3 / Real.sqrt q := by
        rw [hu, div_pow, hsq, div_le_div_iff₀ hq0 hs0]
        calc (α - Real.sqrt q) ^ 2 * Real.sqrt q ≤ 3 * Real.sqrt q * Real.sqrt q :=
              mul_le_mul_of_nonneg_right hdev hs0.le
          _ = 3 * q := by rw [mul_assoc, Real.mul_self_sqrt hq0.le]
      have h4 : ((ν : ℝ) * u) ^ 2 ≤ 1 := by
        rw [mul_pow]
        calc (ν : ℝ) ^ 2 * u ^ 2 ≤ (ν : ℝ) ^ 2 * (3 / Real.sqrt q) :=
              mul_le_mul_of_nonneg_left hu2 (by positivity)
          _ = 3 * (ν : ℝ) ^ 2 / Real.sqrt q := by ring
          _ ≤ 1 := by rw [div_le_one hs0]; exact h3
      have h5 : 0 ≤ (ν : ℝ) * u := mul_nonneg (Nat.cast_nonneg ν) hu0
      nlinarith
    have hrν : (1 + u) ^ ν ≤ Real.exp 1 := by
      calc (1 + u) ^ ν ≤ Real.exp u ^ ν :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) ν
        _ = Real.exp ((ν : ℝ) * u) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hνu
    have hαν : α ^ ν ≤ Real.exp 1 * Real.sqrt q ^ ν := by
      rw [hαu, mul_pow, mul_comm (Real.exp 1)]
      exact mul_le_mul_of_nonneg_left hrν (pow_nonneg hs0.le ν)
    have hβν : β ^ ν ≤ α ^ ν := pow_le_pow_left₀ hβ0.le hβα ν
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    calc ‖(α : ℂ) ^ ν + (β : ℂ) ^ ν‖ ≤ ‖(α : ℂ) ^ ν‖ + ‖(β : ℂ) ^ ν‖ := norm_add_le _ _
      _ = α ^ ν + β ^ ν := by
          rw [norm_pow, norm_pow, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos hα0, abs_of_pos hβ0]
      _ ≤ 2 * Real.exp 1 * Real.sqrt q ^ ν := by linarith

end GaloisForLFunctions.ArithmeticDiscreteness
