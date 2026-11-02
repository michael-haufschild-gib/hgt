import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryCompactProfileHasAnExplicitTailClock

/-!
# Subpolynomial conductor ratios set explicit overlap clocks

Adding the logarithmic conductor block preserves subpolynomial growth. The
reciprocal square root of its logarithmic ratio caps the spectral clock without
losing growth beyond every fixed multiple of `log log N`.
-/

noncomputable section
set_option autoImplicit false
open Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- Enlarge a conductor cutoff to contain the entire logarithmic block. -/
def subpolynomialConductorHull (R : ℕ → ℕ) (N : ℕ) : ℕ :=
  max (R N) (⌊Real.log (N : ℝ)⌋₊ + 2)

/-- The augmented conductor cutoff measured on the logarithmic horizon scale. -/
def subpolynomialConductorRatio (R : ℕ → ℕ) (N : ℕ) : ℝ :=
  (1 + Real.log (subpolynomialConductorHull R N)) / Real.log N

/-- The spectral clock capped so that the linear conductor-ratio cost is small. -/
def subpolynomialProfileClock (φ : ℝ → ℝ) (R : ℕ → ℕ) (N : ℕ) : ℝ :=
  min (compactProfileTailClock φ (Real.log (Real.log (N : ℝ))))
    (Real.log (Real.log (N : ℝ)) / Real.sqrt (subpolynomialConductorRatio R N))

private theorem hull_cast_le {R : ℕ → ℕ} {N : ℕ} (hL2 : 2 ≤ Real.log (N : ℝ)) :
    (subpolynomialConductorHull R N : ℝ) ≤ (max 1 (R N) : ℕ) * (2 * Real.log N) := by
  let A := (max 1 (R N) : ℕ)
  let L := Real.log (N : ℝ)
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast (le_max_left 1 (R N))
  have hA : (0 : ℝ) ≤ A := by positivity
  have hR : (R N : ℝ) ≤ A := by exact_mod_cast (le_max_right 1 (R N))
  have hL : 0 ≤ L := by linarith only [hL2]
  have hfloor : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL
  change (max (R N) (⌊L⌋₊ + 2) : ℕ) ≤ (A : ℝ) * (2 * L)
  rw [Nat.cast_max, Nat.cast_add, Nat.cast_ofNat]
  apply max_le
  · exact hR.trans (le_mul_of_one_le_right hA (by linarith only [hL2]))
  · have hh := mul_le_mul_of_nonneg_right hA1 (show 0 ≤ 2 * L by positivity)
    linarith only [hfloor, hL2, hh]

/-- Adjoining a logarithmic block preserves the vanishing logarithmic ratio. -/
theorem tendsto_subpolynomialConductorRatio {R : ℕ → ℕ}
    (hR : Tendsto (fun N : ℕ => Real.log (max 1 (R N) : ℕ) / Real.log N)
      atTop (𝓝 0)) :
    Tendsto (subpolynomialConductorRatio R) atTop (𝓝 0) := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun N : ℕ => (1 + Real.log 2) / Real.log N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hLlim).const_mul (1 + Real.log 2)
  have hlog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log N)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop 1 zero_lt_one).tendsto_div_nhds_zero).comp hLlim
  have hupper := (hR.add hconst).add hlog
  simp only [add_zero] at hupper
  have hnonneg (N : ℕ) : 0 ≤ subpolynomialConductorRatio R N := by
    exact div_nonneg (by have := Real.log_natCast_nonneg (subpolynomialConductorHull R N); positivity)
      (Real.log_natCast_nonneg N)
  apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ hupper
  filter_upwards [hLlim.eventually_ge_atTop 2] with N hL2
  let L := Real.log (N : ℝ)
  let A := max 1 (R N)
  let r := subpolynomialConductorHull R N
  have hL : 0 < L := by linarith only [hL2]
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : (0 : ℝ) < A := by exact_mod_cast hA1
  have hr2 : 2 ≤ r := by
    have hh := le_max_right (R N) (⌊L⌋₊ + 2)
    change ⌊L⌋₊ + 2 ≤ r at hh
    omega
  have hr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hbound : (r : ℝ) ≤ (A : ℝ) * (2 * L) := hull_cast_le hL2
  have hlogr := Real.log_le_log hr hbound
  rw [Real.log_mul hA.ne' (mul_pos (by norm_num) hL).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hL.ne'] at hlogr
  change (1 + Real.log r) / L ≤ Real.log A / L + (1 + Real.log 2) / L + Real.log L / L
  calc
    _ ≤ (1 + (Real.log A + (Real.log 2 + Real.log L))) / L :=
      div_le_div_of_nonneg_right (by linarith only [hlogr]) hL.le
    _ = _ := by ring

/-- The explicit cutoff-dependent clock exceeds every fixed log-log multiple
for every subpolynomial conductor sequence. -/
theorem tendsto_subpolynomialProfileClock_div_loglog_atTop (φ : ℝ → ℝ) {R : ℕ → ℕ}
    (hR : Tendsto (fun N : ℕ => Real.log (max 1 (R N) : ℕ) / Real.log N)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => subpolynomialProfileClock φ R N /
      Real.log (Real.log (N : ℝ))) atTop atTop := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  have hρlim := tendsto_subpolynomialConductorRatio hR
  have hprofile := (tendsto_compactProfileTailClock_div_atTop φ).comp htlim
  apply tendsto_atTop.2
  intro K
  let M := max K 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  have hInv : 0 < 1 / M := one_div_pos.mpr hM
  filter_upwards [hLlim.eventually_ge_atTop 1, htlim.eventually_ge_atTop 1,
    hprofile.eventually_ge_atTop K, hρlim.eventually (ge_mem_nhds (sq_pos_of_pos hInv))]
    with N hL1 ht1 hprofileN hρsmall
  let t := Real.log (Real.log (N : ℝ))
  let ρ := subpolynomialConductorRatio R N
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hL : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hρ : 0 < ρ := by
    dsimp only [ρ, subpolynomialConductorRatio]
    exact div_pos (by have := Real.log_natCast_nonneg (subpolynomialConductorHull R N); positivity) hL
  have hroot : Real.sqrt ρ ≤ 1 / M := by
    have hh := Real.sq_sqrt hρ.le
    change ρ ≤ (1 / M) ^ 2 at hρsmall
    nlinarith only [hh, hρsmall, Real.sqrt_nonneg ρ, hInv]
  have hKroot : K * Real.sqrt ρ ≤ 1 := by
    have hh := (le_div_iff₀ hM).mp hroot
    have hk := mul_le_mul_of_nonneg_right (le_max_left K 1) (Real.sqrt_nonneg ρ)
    change K * Real.sqrt ρ ≤ M * Real.sqrt ρ at hk
    nlinarith only [hh, hk]
  apply (le_div_iff₀ ht).mpr
  change K * t ≤ min (compactProfileTailClock φ t) (t / Real.sqrt ρ)
  apply le_min
  · exact (le_div_iff₀ ht).mp hprofileN
  · apply (le_div_iff₀ (Real.sqrt_pos.mpr hρ)).mpr
    calc
      _ = t * (K * Real.sqrt ρ) := by ring
      _ ≤ t * 1 := mul_le_mul_of_nonneg_left hKroot ht.le
      _ = _ := mul_one _

#print axioms tendsto_subpolynomialConductorRatio
#print axioms tendsto_subpolynomialProfileClock_div_loglog_atTop

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
