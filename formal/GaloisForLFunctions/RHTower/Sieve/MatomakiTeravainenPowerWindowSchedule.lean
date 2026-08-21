import GaloisForLFunctions.RHTower.Sieve.PowerWindowSelect

/-!
# Bounded Matomäki--Teräväinen power-window selection

The paper's lower Type-II length bound makes the selected raising degree uniformly bounded.  This
is the missing source fact needed to feed the fixed-degree raised Huxley schedule.
-/

namespace RHTower.Sieve

/-- The full Type-II power-window selection, now with an explicit degree cap forced by
`T^mu ≤ M`. -/
theorem exists_pow_mem_matomakiTeravainen_window_bounded
    {T M eps mu : ℝ} (hT : 1 < T) (hM : 1 < M)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 1000)
    (hmu : 0 < mu) (hMlower : T ^ mu ≤ M)
    (hMupper : M ≤ T ^ ((2 : ℝ) / 11 + eps)) :
    ∃ ell : ℕ, 1 ≤ ell ∧ ell ≤ ⌈1 / mu⌉₊ ∧
      T ^ ((5 : ℝ) / 6 - eps) ≤ M ^ ell ∧
      M ^ ell ≤ T ^ (1 - eps / 2) := by
  obtain ⟨ell, hell, hlo, hhi⟩ :=
    exists_pow_mem_matomakiTeravainen_window hT hM heps0 heps hMupper
  have hT0 : 0 < T := by linarith
  have hpowLower : (T ^ mu) ^ ell ≤ M ^ ell :=
    pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hMlower ell
  have hpowEq : (T ^ mu) ^ ell = T ^ ((ell : ℝ) * mu) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    congr 1
    ring
  have htoOne : T ^ (1 - eps / 2) ≤ T ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
  have hpow : T ^ ((ell : ℝ) * mu) ≤ T ^ (1 : ℝ) := by
    rw [← hpowEq]
    exact hpowLower.trans (hhi.trans htoOne)
  have hexp : (ell : ℝ) * mu ≤ 1 := by
    exact (Real.strictMono_rpow_of_base_gt_one hT).le_iff_le.mp hpow
  have hellReal : (ell : ℝ) ≤ 1 / mu := by
    rw [le_div_iff₀ hmu]
    simpa [mul_comm] using hexp
  have hceilReal : (ell : ℝ) ≤ (⌈1 / mu⌉₊ : ℝ) :=
    hellReal.trans (Nat.le_ceil (1 / mu))
  have hellCeil : ell ≤ ⌈1 / mu⌉₊ := by exact_mod_cast hceilReal
  exact ⟨ell, hell, hellCeil, hlo, hhi⟩

/-- Epsilon-rescaled form matching `exists_matomakiTeravainen_raised_huxley_schedule`: selecting
with `4 eps` gives the stricter upper edge `T^(1-2 eps)`, while its lower edge remains above
`T^(9/11)`. -/
theorem exists_pow_mem_matomakiTeravainen_huxley_window_bounded
    {T M eps mu : ℝ} (hT : 1 < T) (hM : 1 < M)
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hMlower : T ^ mu ≤ M)
    (hMupper : M ≤ T ^ ((2 : ℝ) / 11 + 4 * eps)) :
    ∃ ell : ℕ, 1 ≤ ell ∧ ell ≤ ⌈1 / mu⌉₊ ∧
      T ^ ((9 : ℝ) / 11) ≤ M ^ ell ∧
      M ^ ell ≤ T ^ (1 - 2 * eps) := by
  obtain ⟨ell, hell, hellCap, hlo, hhi⟩ :=
    exists_pow_mem_matomakiTeravainen_window_bounded hT hM
      (show 0 ≤ 4 * eps by positivity) (show 4 * eps ≤ 1 / 1000 by linarith)
      hmu hMlower hMupper
  refine ⟨ell, hell, hellCap, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)).trans hlo
  · simpa only [show (4 * eps) / 2 = 2 * eps by ring] using hhi

end RHTower.Sieve
