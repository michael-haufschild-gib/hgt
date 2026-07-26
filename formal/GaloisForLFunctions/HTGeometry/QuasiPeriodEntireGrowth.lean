import GaloisForLFunctions.HTGeometry.FundamentalParallelogram

/-!
# Growth of a quasi-periodic entire function

A function reproduced by two `ℝ`-independent translations up to nonzero constant multipliers has
**exponential type**: every point differs from a point of the compact fundamental parallelogram by an
integer combination of the steps whose coefficients are bounded by a multiple of the norm
(`exists_bounded_intCombination`), and each lattice step multiplies the value by a fixed constant.

* `quasiPeriodic_zsmul` — a constant-multiplier quasi-period iterates over `ℤ`;
* `quasiPeriodic_lattice` — and over the whole step lattice;
* **`exists_exp_growth_bound_of_quasiperiods`** — `‖f z‖ ≤ K · exp (c ‖z‖)`.

This is the growth half of the statement that an entire function with constant multipliers over a
lattice cannot vanish: its zero set would be a full lattice coset, whose counting function grows
like `r²`, while Jensen's inequality bounds the zero count of a function of exponential type
linearly in `r`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-! ### Iterating the multiplier -/

/-- A constant-multiplier quasi-period iterates over the integers. -/
theorem quasiPeriodic_zsmul {f : ℂ → ℂ} {w c : ℂ} (hc : c ≠ 0)
    (h : ∀ z, f (z + w) = c * f z) (m : ℤ) (z : ℂ) :
    f (z + m • w) = c ^ m * f z := by
  have hback : ∀ u : ℂ, f (u + -w) = c⁻¹ * f u := by
    intro u
    have hz : u + -w + w = u := by ring
    have hu := h (u + -w)
    rw [hz] at hu
    rw [hu]
    field_simp
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hs : ((n : ℤ) + 1) • w = (n : ℤ) • w + w := by rw [add_smul, one_smul]
      rw [hs, ← add_assoc, h (z + (n : ℤ) • w), ih, zpow_add₀ hc]
      simp only [zpow_one]
      ac_rfl
  | pred n ih =>
      have hs : (-(n : ℤ) - 1) • w = (-(n : ℤ)) • w + -w := by rw [sub_smul, one_smul]; ring
      rw [hs, ← add_assoc, hback (z + (-(n : ℤ)) • w), ih, zpow_sub₀ hc]
      field_simp

/-- Both multipliers iterate over the whole step lattice. -/
theorem quasiPeriodic_lattice {f : ℂ → ℂ} {w₁ w₂ a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) (m n : ℤ) (z : ℂ) :
    f (z + m • w₁ + n • w₂) = a ^ m * b ^ n * f z := by
  rw [quasiPeriodic_zsmul hb h₂ n (z + m • w₁), quasiPeriodic_zsmul ha h₁ m z]
  ring

/-! ### Exponential type -/

/-- The absolute value of an integer power is bounded by the corresponding power of
`max ‖c‖ ‖c‖⁻¹`. -/
theorem norm_zpow_le_max_pow {c : ℂ} (m : ℤ) :
    ‖c ^ m‖ ≤ (max ‖c‖ ‖c‖⁻¹) ^ m.natAbs := by
  rcases m.natAbs_eq with hm | hm
  · rw [hm, zpow_natCast, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) _
  · rw [hm, zpow_neg, zpow_natCast, norm_inv, norm_pow, ← inv_pow]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg c))
      (le_max_right ‖c‖ ‖c‖⁻¹) m.natAbs

/-- `1 ≤ max ‖c‖ ‖c‖⁻¹` for a nonzero `c`. -/
theorem one_le_max_norm_inv {c : ℂ} (hc : c ≠ 0) : 1 ≤ max ‖c‖ ‖c‖⁻¹ := by
  rcases le_total ‖c‖ 1 with hle | hle
  · exact le_max_of_le_right (one_le_inv_iff₀.mpr ⟨norm_pos_iff.mpr hc, hle⟩)
  · exact le_max_of_le_left hle

/-- **A quasi-periodic entire function has exponential type.** -/
theorem exists_exp_growth_bound_of_quasiperiods {f : ℂ → ℂ} (hcont : Continuous f)
    {w₁ w₂ a b : ℂ} (hindep : LinearIndependent ℝ ![w₁, w₂]) (ha : a ≠ 0) (hb : b ≠ 0)
    (h₁ : ∀ z, f (z + w₁) = a * f z) (h₂ : ∀ z, f (z + w₂) = b * f z) :
    ∃ K c : ℝ, 0 < K ∧ 0 ≤ c ∧ ∀ z, ‖f z‖ ≤ K * Real.exp (c * ‖z‖) := by
  classical
  obtain ⟨M, hM⟩ := (isCompact_fundamentalParallelogram w₁ w₂).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (zero_mem_fundamentalParallelogram w₁ w₂))
  have hA₁1 : 1 ≤ max ‖a‖ ‖a‖⁻¹ := one_le_max_norm_inv ha
  have hA₂1 : 1 ≤ max ‖b‖ ‖b‖⁻¹ := one_le_max_norm_inv hb
  have hlogA₁ : 0 ≤ Real.log (max ‖a‖ ‖a‖⁻¹) := Real.log_nonneg hA₁1
  have hlogA₂ : 0 ≤ Real.log (max ‖b‖ ‖b‖⁻¹) := Real.log_nonneg hA₂1
  obtain ⟨C, hC0, hcov⟩ := exists_bounded_intCombination hindep
  refine ⟨M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) + 1,
    C * Real.log (max ‖a‖ ‖a‖⁻¹) + C * Real.log (max ‖b‖ ‖b‖⁻¹), by positivity,
    by positivity, ?_⟩
  intro z
  obtain ⟨m, n, hmem, hmz, hnz⟩ := hcov z
  have hval : f z = a ^ m * b ^ n * f (z - (m • w₁ + n • w₂)) := by
    have hlat := quasiPeriodic_lattice ha hb h₁ h₂ m n (z - (m • w₁ + n • w₂))
    rw [show z - (m • w₁ + n • w₂) + m • w₁ + n • w₂ = z by ring] at hlat
    exact hlat
  have hnorm : ‖f z‖ ≤ (max ‖a‖ ‖a‖⁻¹) ^ m.natAbs * (max ‖b‖ ‖b‖⁻¹) ^ n.natAbs * M := by
    rw [hval, norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul (norm_zpow_le_max_pow _) (norm_zpow_le_max_pow _)
        (norm_nonneg _) (by positivity))
      (hM _ hmem) (norm_nonneg _) (by positivity)
  have hpow1 : (max ‖a‖ ‖a‖⁻¹) ^ m.natAbs ≤ (max ‖a‖ ‖a‖⁻¹) ^ (C * ‖z‖ + 1 : ℝ) := by
    rw [← Real.rpow_natCast (max ‖a‖ ‖a‖⁻¹) m.natAbs]
    exact Real.rpow_le_rpow_of_exponent_le hA₁1 hmz
  have hpow2 : (max ‖b‖ ‖b‖⁻¹) ^ n.natAbs ≤ (max ‖b‖ ‖b‖⁻¹) ^ (C * ‖z‖ + 1 : ℝ) := by
    rw [← Real.rpow_natCast (max ‖b‖ ‖b‖⁻¹) n.natAbs]
    exact Real.rpow_le_rpow_of_exponent_le hA₂1 hnz
  have hA₁pos : (0 : ℝ) < max ‖a‖ ‖a‖⁻¹ := lt_of_lt_of_le zero_lt_one hA₁1
  have hA₂pos : (0 : ℝ) < max ‖b‖ ‖b‖⁻¹ := lt_of_lt_of_le zero_lt_one hA₂1
  have hexp : (max ‖a‖ ‖a‖⁻¹) ^ (C * ‖z‖ + 1 : ℝ) * (max ‖b‖ ‖b‖⁻¹) ^ (C * ‖z‖ + 1 : ℝ) * M
      = M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) *
        Real.exp ((C * Real.log (max ‖a‖ ‖a‖⁻¹) + C * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) := by
    rw [Real.rpow_add hA₁pos, Real.rpow_add hA₂pos, Real.rpow_one, Real.rpow_one,
      Real.rpow_def_of_pos hA₁pos, Real.rpow_def_of_pos hA₂pos]
    have harg :
        (C * Real.log (max ‖a‖ ‖a‖⁻¹) + C * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖ =
          Real.log (max ‖a‖ ‖a‖⁻¹) * (C * ‖z‖) + Real.log (max ‖b‖ ‖b‖⁻¹) * (C * ‖z‖) := by
      ring
    rw [harg, Real.exp_add]
    ring
  calc ‖f z‖ ≤ (max ‖a‖ ‖a‖⁻¹) ^ m.natAbs * (max ‖b‖ ‖b‖⁻¹) ^ n.natAbs * M := hnorm
    _ ≤ (max ‖a‖ ‖a‖⁻¹) ^ (C * ‖z‖ + 1 : ℝ) * (max ‖b‖ ‖b‖⁻¹) ^ (C * ‖z‖ + 1 : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        exact mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
    _ = M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) *
        Real.exp ((C * Real.log (max ‖a‖ ‖a‖⁻¹) + C * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) := hexp
    _ ≤ (M * ((max ‖a‖ ‖a‖⁻¹) * (max ‖b‖ ‖b‖⁻¹)) + 1) *
        Real.exp ((C * Real.log (max ‖a‖ ‖a‖⁻¹) + C * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) := by
        have hpos : (0 : ℝ) < Real.exp
          ((C * Real.log (max ‖a‖ ‖a‖⁻¹) + C * Real.log (max ‖b‖ ‖b‖⁻¹)) * ‖z‖) :=
          Real.exp_pos _
        nlinarith

end GaloisForLFunctions.HTGeometry
