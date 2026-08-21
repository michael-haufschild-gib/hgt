import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPowerWindowSchedule
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

namespace RHTower.Sieve

open Filter

noncomputable section

/-- Product-scale comparability transfers Type-II short-factor bounds to the exact
literature Huxley window for the unraised long factor. -/
theorem matomakiTeravainen_typeII_long_factor_window
    {T M₁ M₂ eps delta mu : ℝ}
    (hT : 1 < T) (hM₁ : 0 < M₁)
    (hprodLo : T ^ (1 - delta) ≤ M₁ * M₂)
    (hprodHi : M₁ * M₂ ≤ T ^ (1 + delta))
    (hM₁lo : T ^ mu ≤ M₁)
    (hM₁hi : M₁ ≤ T ^ ((2 : ℝ) / 11 + 4 * eps))
    (hdeltaLo : delta ≤ 6 * eps)
    (hdeltaHi : 2 * eps + delta ≤ mu) :
    T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ M₂ ∧
      M₂ ≤ T ^ (1 - 2 * eps) := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hprodPos : 0 < M₁ * M₂ :=
    (Real.rpow_pos_of_pos hT0 (1 - delta)).trans_le hprodLo
  have hM₂ : 0 < M₂ := by
    rcases mul_pos_iff.mp hprodPos with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge hM₁.le) hneg.1)
  constructor
  · have hden : 0 < T ^ ((2 : ℝ) / 11 + 4 * eps) := Real.rpow_pos_of_pos hT0 _
    have hquot : T ^ (1 - delta) / T ^ ((2 : ℝ) / 11 + 4 * eps) ≤ M₂ := by
      rw [div_le_iff₀ hden]
      exact hprodLo.trans
        (by simpa [mul_comm] using mul_le_mul_of_nonneg_right hM₁hi hM₂.le)
    have hquotEq : T ^ (1 - delta) / T ^ ((2 : ℝ) / 11 + 4 * eps) =
        T ^ ((9 : ℝ) / 11 - delta - 4 * eps) := by
      rw [← Real.rpow_sub hT0]
      congr 1
      ring
    rw [hquotEq] at hquot
    exact (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)).trans hquot
  · have hnum : 0 < T ^ mu := Real.rpow_pos_of_pos hT0 _
    have hmul : T ^ mu * M₂ ≤ T ^ (1 + delta) :=
      (mul_le_mul_of_nonneg_right hM₁lo hM₂.le).trans hprodHi
    have hquot : M₂ ≤ T ^ (1 + delta) / T ^ mu := by
      rw [le_div_iff₀ hnum]
      simpa [mul_comm] using hmul
    have hquotEq : T ^ (1 + delta) / T ^ mu = T ^ (1 + delta - mu) := by
      rw [← Real.rpow_sub hT0]
    rw [hquotEq] at hquot
    exact hquot.trans (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith))

/-- A fixed polylogarithmic distortion is eventually contained in `T^±delta`. -/
theorem exists_matomakiTeravainen_polylog_product_window
    {C delta : ℝ} (hC : 0 < C) (hdelta : 0 < delta) (k : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T P : ℝ),
      T₀ ≤ T →
      T / (C * (1 + |Real.log T|) ^ k) ≤ P →
      P ≤ T * (C * (1 + |Real.log T|) ^ k) →
      T ^ (1 - delta) ≤ P ∧ P ≤ T ^ (1 + delta) := by
  have hloEvent := eventually_const_mul_rpow_polylog_le_rpow
    (C := C) (α := 1 - delta) (β := (1 : ℝ)) k (by linarith)
  have hhiEvent := eventually_const_mul_rpow_polylog_le_rpow
    (C := C) (α := (1 : ℝ)) (β := 1 + delta) k (by linarith)
  have hlarge : ∀ᶠ T : ℝ in atTop, 1 ≤ T := Filter.eventually_ge_atTop 1
  have hevent : ∀ᶠ T : ℝ in atTop,
      C * T ^ (1 - delta) * (1 + |Real.log T|) ^ k ≤ T ∧
      C * T * (1 + |Real.log T|) ^ k ≤ T ^ (1 + delta) ∧
      1 ≤ T := by
    filter_upwards [hloEvent, hhiEvent, hlarge] with T hlo hhi hT
    simpa only [Real.rpow_one] using And.intro hlo (And.intro hhi hT)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 T₁, le_max_left _ _, ?_⟩
  intro T P hT hPlo hPhi
  have hdata := hT₁ T (le_trans (le_max_right _ _) hT)
  have hpolyPos : 0 < C * (1 + |Real.log T|) ^ k := by positivity
  constructor
  · apply hPlo.trans'
    rw [le_div_iff₀ hpolyPos]
    have hlo := hdata.1
    calc
      T ^ (1 - delta) * (C * (1 + |Real.log T|) ^ k)
          = C * T ^ (1 - delta) * (1 + |Real.log T|) ^ k := by ring
      _ ≤ T := hlo
  · exact hPhi.trans (by
      have hhi := hdata.2.1
      calc
        T * (C * (1 + |Real.log T|) ^ k)
            = C * T * (1 + |Real.log T|) ^ k := by ring
        _ ≤ T ^ (1 + delta) := hhi)

end

end RHTower.Sieve
