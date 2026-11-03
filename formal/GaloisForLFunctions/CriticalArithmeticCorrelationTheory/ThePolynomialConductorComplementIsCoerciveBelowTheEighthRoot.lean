import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFarReserveBelowTheEighthRoot

/-!
# The polynomial-conductor complement is coercive below the eighth root

On `(conductorSubspace R N)ᗮ` with `R = ⌊N^θ⌋₊`, the prefix pole defect is at least
`k ((15/16) P − 2 B S)` with `k = log R / D − 1 ≍ θ log N` and `B = O(log c / log N)`
(`poleDefect_prefix_ge_of_conductor_orthogonal`). The far reserve
`eventually_completeWeilEnergy_far_reserve_below_one_eighth`, applied with a prefix cost
`θ' log N` below `k / 4`, then leaves `(k/2) P` on the prefix and `κ/(8c⁷) · log N` per unit
top mass, because the leakage `k B = O(log c)` is below `κ log N / c⁷` once `c⁸ = o(log N)`.

* `eventually_completeWeilEnergy_two_region_on_polynomialConductorOrthogonal_below_one_eighth`:
  for `0 < θ ≤ 1/36`, `(θ/8D) log N` per unit prefix mass and `g log N/(8c⁷)` per unit top mass.
* `eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal_below_one_eighth`:
  for `θ > 0` and `0 < α < 1/8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
  `(c_orth log N / c⁷) ‖z‖² ≤ completeWeilEnergy` on `(conductorSubspace ⌊N^θ⌋₊ N)ᗮ`.
* `eventually_completeWeil_global_negIndex_le_polynomialConductor_below_one_eighth`: in the same
  range every subspace on which the energy is nonpositive has dimension at most `⌊N^θ⌋₊`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology RHTower Zeta23 ArithmeticFunction
open scoped Classical BigOperators RealInnerProductSpace ArithmeticFunction Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics ArithmeticEffectivityTheory

private theorem eventually_log_nat_le_rpow_36_eighth :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
  exact (le_abs_self _).trans habs

/-- The Euclidean mass splits at `M` into the prefix and the top. -/
private theorem norm_sq_eq_prefix_add_top {N : ℕ} (M : ℕ) (hMN : M ≤ N)
    (z : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖z‖ ^ 2 = (∑ n ∈ Icc 1 M, primeHorizonExtension z n ^ 2) +
      ∑ n ∈ Ioc M N, primeHorizonExtension z n ^ 2 := by
  rw [← sum_primeHorizonExtension_sq]
  have hs : (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]; omega
  rw [hs, add_comm]
  exact (sum_sdiff (Icc_subset_Icc le_rfl hMN)).symm

/-- **Cutoff geometry at a polynomial conductor.** With `R = ⌊N^θ⌋₊` (`θ ≤ 1/36`),
`T = linearDefectCutoff c` and `M = N / T`: `R² ≤ M`, `log M ≥ log N / 2`, the prefix condition
`18 (1 + log R) ≤ log M`, the gap `k = log R / D − 1 ≥ (θ / 4D) log N`, and `log R ≤ θ log N`. -/
private theorem polynomial_cutoff_geometry {θ c : ℝ} {N : ℕ} (hθ : 0 < θ) (hθ36 : θ ≤ 1 / 36)
    (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hL2000 : 2000 ≤ Real.log N)
    (hHL : 256 * Real.exp 2 + 4 ≤ Real.log N)
    (hL2θ : 2 / θ ≤ Real.log N)
    (hL4Dθ : 4 * explicitConductorCutoffConstant / θ ≤ Real.log N)
    (hLX : Real.log N ≤ (N : ℝ) ^ (1 / 36 : ℝ)) (hNθ4 : 4 ≤ (N : ℝ) ^ θ) :
    2 ≤ ⌊(N : ℝ) ^ θ⌋₊ ∧ linearDefectCutoff c ≤ N ∧
      ⌊(N : ℝ) ^ θ⌋₊ * ⌊(N : ℝ) ^ θ⌋₊ ≤ N / linearDefectCutoff c ∧
      2 ≤ N / linearDefectCutoff c ∧
      Real.log N / 2 ≤ Real.log ((N / linearDefectCutoff c : ℕ) : ℝ) ∧
      18 * (1 + Real.log ⌊(N : ℝ) ^ θ⌋₊) ≤ Real.log ((N / linearDefectCutoff c : ℕ) : ℝ) ∧
      (θ / (4 * explicitConductorCutoffConstant)) * Real.log N ≤
        Real.log ⌊(N : ℝ) ^ θ⌋₊ / explicitConductorCutoffConstant - 1 ∧
      Real.log ⌊(N : ℝ) ^ θ⌋₊ ≤ θ * Real.log N := by
  obtain ⟨R, hR⟩ : ∃ R, R = ⌊(N : ℝ) ^ θ⌋₊ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = linearDefectCutoff c := ⟨_, rfl⟩
  rw [← hR, ← hT]
  have hD := explicitConductorCutoffConstant_pos
  have hL1 : 1 ≤ Real.log N := by linarith only [hL2000]
  have hL0 : 0 < Real.log N := by linarith only [hL2000]
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hN1 : 1 ≤ N := by
    by_contra h
    have : N = 0 := by omega
    subst this; simp at hL0
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1R
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  rw [← hT] at hT3 hTup
  have hT1 : 1 ≤ T := by omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  obtain ⟨X, hXdef⟩ : ∃ X, X = (N : ℝ) ^ (1 / 36 : ℝ) := ⟨_, rfl⟩
  rw [← hXdef] at hLX
  have hX1 : 1 ≤ X := hL1.trans hLX
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hlogX : Real.log X = (1 / 36 : ℝ) * Real.log N := by rw [hXdef, Real.log_rpow hN0]
  have hR2 : 2 ≤ R := by
    rw [hR]; exact Nat.le_floor (by push_cast; linarith only [hNθ4])
  have hRX : (R : ℝ) ≤ X := by
    rw [hR, hXdef]
    exact (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le hN1R hθ36)
  have hTX : (T : ℝ) ≤ X ^ 2 := by
    calc (T : ℝ) ≤ (256 * Real.exp 2 + 4) * c := hTup
      _ ≤ X * X := mul_le_mul (hHL.trans hLX) (hcL.trans hLX) hc0.le hX0.le
      _ = X ^ 2 := by ring
  have hRRT : R * R * T ≤ N := by
    have hh : (R : ℝ) ^ 2 * T ≤ (N : ℝ) := by
      calc (R : ℝ) ^ 2 * T ≤ X ^ 2 * X ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2) hTX hT0.le (by positivity)
        _ = X ^ 4 := by ring
        _ ≤ (N : ℝ) := (pow_le_pow_right₀ hX1 (by norm_num : 4 ≤ 36)).trans_eq hX36
    have hhNat : R ^ 2 * T ≤ N := by exact_mod_cast hh
    simpa only [pow_two] using hhNat
  have hRM : R * R ≤ N / T := (Nat.le_div_iff_mul_le (by omega : 0 < T)).mpr hRRT
  have hTN : T ≤ N := by
    have hR1 : 1 ≤ R * R := Nat.mul_pos (by omega) (by omega)
    exact (by simpa only [one_mul] using Nat.mul_le_mul_right T hR1 : T ≤ R * R * T).trans hRRT
  have hM2 : 2 ≤ N / T := (by norm_num : 2 ≤ 2 * 2).trans ((Nat.mul_le_mul hR2 hR2).trans hRM)
  obtain ⟨M, hM⟩ : ∃ M, M = N / T := ⟨_, rfl⟩
  rw [← hM] at hRM hM2 ⊢
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hfloor : (N : ℝ) < ((M : ℝ) + 1) * T := by
    have hh : N < (M + 1) * T := by
      rw [hM]; simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < T by omega)
    exact_mod_cast hh
  have hratio : Real.log N - Real.log M ≤ Real.log (2 * (T : ℝ)) := by
    rw [← Real.log_div hN0.ne' hM0.ne']
    apply Real.log_le_log (div_pos hN0 hM0)
    apply (div_le_iff₀ hM0).mpr
    nlinarith only [hfloor, mul_nonneg (sub_nonneg.mpr hM1) hT0.le]
  have hlog2T : Real.log (2 * (T : ℝ)) ≤ Real.log N / 4 + 1 := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hTX zero_le_two)
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hX0.ne'), Real.log_pow, hlogX] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    push_cast at hh
    linarith only [hh, h2, hL0]
  have hhalf_M : Real.log N / 2 ≤ Real.log M := by linarith only [hratio, hlog2T, hL2000]
  have hlogR_le36 : Real.log R ≤ (1 / 36 : ℝ) * Real.log N := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) hRX
    rwa [hlogX] at hh
  have hlogM_cond : 18 * (1 + Real.log R) ≤ Real.log M := by
    linarith only [hlogR_le36, hratio, hlog2T, hL2000]
  have hlogR_le : Real.log R ≤ θ * Real.log N := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < R by omega))
      (show (R : ℝ) ≤ (N : ℝ) ^ θ by rw [hR]; exact Nat.floor_le (by positivity))
    rwa [Real.log_rpow hN0] at hh
  have hR_half : (1 / 2 : ℝ) * (N : ℝ) ^ θ ≤ (R : ℝ) := by
    have hgt : (N : ℝ) ^ θ - 1 < (R : ℝ) := by
      rw [hR]; exact sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hNθ4, hgt]
  have hlogR_lb : (θ / 2) * Real.log N ≤ Real.log R := by
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpos : 0 < (N : ℝ) ^ θ := by linarith only [hNθ4]
    have h1 := Real.log_le_log (by positivity) hR_half
    rw [Real.log_mul (by norm_num) hpos.ne', one_div, Real.log_inv, Real.log_rpow hN0] at h1
    have h2 : 2 ≤ θ * Real.log N := by
      have h := (div_le_iff₀ hθ).mp hL2θ; linarith only [h]
    linarith only [h1, hlog2, h2]
  have hgap : (θ / (4 * explicitConductorCutoffConstant)) * Real.log N ≤
      Real.log R / explicitConductorCutoffConstant - 1 := by
    have hdiv := div_le_div_of_nonneg_right hlogR_lb hD.le
    have h1 : (θ / 2) * Real.log N / explicitConductorCutoffConstant =
        2 * ((θ / (4 * explicitConductorCutoffConstant)) * Real.log N) := by
      field_simp; ring
    have h4D : 4 * explicitConductorCutoffConstant ≤ θ * Real.log N := by
      have h := (div_le_iff₀ hθ).mp hL4Dθ; linarith only [h]
    have h2 : 1 ≤ (θ / (4 * explicitConductorCutoffConstant)) * Real.log N := by
      rw [div_mul_eq_mul_div, one_le_div (by positivity)]
      linarith only [h4D]
    linarith only [hdiv, h1, h2]
  exact ⟨hR2, hTN, hRM, hM2, hhalf_M, hlogM_cond, hgap, hlogR_le⟩

/-- **Prefix and top coefficients after the pole-defect bound.** With `k ≥ (θ/4D) ℓ`,
`k ≤ θ ℓ / D`, a far prefix cost `(θ/16D) ℓ` and a leakage `(7/4) k B ≤ κ ℓ / (8 c⁷)`, the far
reserve leaves `(θ/8D) ℓ P + κ ℓ/(8c⁷) S`. -/
private theorem coercive_combine {k θ D ℓ g c P S B Dm E : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hℓ : 0 ≤ ℓ) (hc1 : 1 ≤ c) (hP : 0 ≤ P) (hS : 0 ≤ S) (hgap : (θ / (4 * D)) * ℓ ≤ k)
    (hpre : k * ((15 / 16 : ℝ) * P - 2 * B * S) ≤ Dm)
    (hleak : (7 / 4 : ℝ) * k * B ≤ g / (8 * c ^ 7) * ℓ)
    (hfar : (7 / 8 : ℝ) * Dm + g / c ^ 7 / 4 * ℓ * S - θ / (16 * D) * ℓ * P ≤ E) :
    (θ / (8 * D)) * ℓ * P + g / (8 * c ^ 7) * ℓ * S ≤ E := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have e1 : θ / (16 * D) * ℓ = (1 / 4) * ((θ / (4 * D)) * ℓ) := by field_simp; ring
  have e2 : θ / (8 * D) * ℓ = (1 / 2) * ((θ / (4 * D)) * ℓ) := by field_simp; ring
  have e3 : g / c ^ 7 / 4 * ℓ = 2 * (g / (8 * c ^ 7) * ℓ) := by field_simp; ring
  rw [e1, e3] at hfar
  rw [e2]
  have hA : 0 ≤ (θ / (4 * D)) * ℓ := by positivity
  have hAP : 0 ≤ (θ / (4 * D)) * ℓ * P := mul_nonneg hA hP
  have h1 : (θ / (4 * D)) * ℓ * P ≤ k * P := mul_le_mul_of_nonneg_right hgap hP
  have h2 : (7 / 4 : ℝ) * k * B * S ≤ g / (8 * c ^ 7) * ℓ * S :=
    mul_le_mul_of_nonneg_right hleak hS
  linarith only [hpre, hfar, h1, h2, hAP]

/-- **Two-region reserve on a polynomial-conductor complement below the eighth root.** For
`0 < θ ≤ 1 / 36` and `0 < α < 1 / 8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
every `z ∈ (conductorSubspace ⌊N^θ⌋₊ N)ᗮ` has energy at least `(θ / 8D) log N` per unit mass on the
prefix rows `n ≤ N / T` (`T = linearDefectCutoff c`) and `g log N / (8 c⁷)` per unit mass on the
top rows: the pole-defect prefix bound plus the far reserve, with the leakage `k B = O(c)` paid by
`g log N / c⁷` because `c⁸ = o(log N)`. -/
theorem eventually_completeWeilEnergy_two_region_on_polynomialConductorOrthogonal_below_one_eighth
    {θ α : ℝ} (hθ : 0 < θ) (hθ36 : θ ≤ 1 / 36) (hα : 0 < α) (hα_lt : α < 1 / 8) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ →
        θ / (8 * explicitConductorCutoffConstant) * Real.log (N : ℝ) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
          growingMassConstant / (8 * c ^ 7) * Real.log (N : ℝ) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N z := by
  set D := explicitConductorCutoffConstant with hDdef
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  set θ₀ := θ with hθ₀def
  have hθ₀ : 0 < θ₀ := hθ
  have hθ₀_36 : θ₀ ≤ 1 / 36 := hθ36
  set g := growingMassConstant with hgdef
  have hg : 0 < g := growingMassConstant_pos
  set H := 256 * Real.exp 2 + 4 with hHdef
  have hH1 : 1 ≤ H := by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num); rw [hHdef]; linarith
  -- leakage constant: `(7/4) k B ≤ C_lk (1 + c)` with `C_lk = 7 θ₀ (5 + log 2H) / (2 D)`
  set C_lk := 7 * θ₀ * (5 + Real.log (2 * H)) / (2 * D) with hClk
  have hClk0 : 0 ≤ C_lk := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * H by linarith); positivity
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ₀) atTop atTop :=
    (tendsto_rpow_atTop hθ₀).comp tendsto_natCast_atTop_atTop
  have h8α : 0 < 1 - 8 * α := by linarith
  filter_upwards [eventually_completeWeilEnergy_far_reserve_below_one_eighth hα hα_lt
      (show 0 < θ₀ / (16 * D) by positivity),
    hNθlim.eventually_ge_atTop 4,
    hLlim.eventually_ge_atTop (max 2000 (max H (max (2 / θ₀) (4 * D / θ₀)))),
    ((tendsto_rpow_atTop h8α).comp hLlim).eventually_ge_atTop (16 * C_lk / g),
    eventually_log_nat_le_rpow_36_eighth] with N hfar hNθ4 hLM hLμ hLX
  intro c hc1 hcα z hz
  dsimp only [Function.comp_def] at hLμ
  have hL2000 : 2000 ≤ Real.log N := (le_max_left _ _).trans hLM
  have hHL : H ≤ Real.log N := ((le_max_left _ _).trans (le_max_right _ _)).trans hLM
  have hL2θ : 2 / θ₀ ≤ Real.log N :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLM
  have hL4Dθ : 4 * D / θ₀ ≤ Real.log N :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hLM
  have hL1 : 1 ≤ Real.log N := by linarith only [hL2000]
  have hL0 : 0 < Real.log N := by linarith only [hL2000]
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcL : c ≤ Real.log N := hcα.trans ((Real.rpow_le_rpow_of_exponent_le hL1
    (show α ≤ 1 by linarith)).trans_eq (Real.rpow_one _))
  obtain ⟨hR2, hTN, hRM, hM2, hhalf_M, hlogM_cond, hgap, hlogR_le⟩ :=
    polynomial_cutoff_geometry hθ₀ hθ₀_36 hc1 hcL hL2000 hHL hL2θ hL4Dθ hLX hNθ4
  have hN1R : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := le_trans (by omega : 1 ≤ 2) (hM2.trans (Nat.div_le_self _ _))
    exact_mod_cast this
  have hzR : z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ₀⌋₊ N)ᗮ := hz
  have hz1 : z ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hzR v (conductorSubspace_mono (by omega) N hv)
  have hk_pos : 0 < Real.log ⌊(N : ℝ) ^ θ₀⌋₊ / D - 1 :=
    lt_of_lt_of_le (by positivity) hgap
  have hscale : D ≤ Real.log ⌊(N : ℝ) ^ θ₀⌋₊ := by
    have h1 : 1 ≤ Real.log ⌊(N : ℝ) ^ θ₀⌋₊ / D := by linarith only [hk_pos]
    simpa only [one_mul] using (le_div_iff₀ hD).mp h1
  have hpre := poleDefect_prefix_ge_of_conductor_orthogonal hR2 hM2 (Nat.div_le_self _ _) hRM
    hlogM_cond hscale hzR
  have hfarz := hfar c hc1 hcα hz1
  -- the leakage `(7/4) k B ≤ κ ℓ / (8 c⁷)`
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hTB := terminalPacketCost_nat_div_le (Q := ⌊(N : ℝ) ^ θ₀⌋₊) (by omega) hTN hRM
  have hlogM_pos : 0 < Real.log ((N / linearDefectCutoff c : ℕ) : ℝ) := by linarith only [hhalf_M, hL0]
  have hlog2T : Real.log (2 * (linearDefectCutoff c : ℝ)) ≤ Real.log (2 * H) + c := by
    have hpos : (0 : ℝ) < 2 * (linearDefectCutoff c : ℝ) := by
      have : (3 : ℝ) ≤ linearDefectCutoff c := by exact_mod_cast hT3
      linarith
    have ht := Real.log_le_log hpos (mul_le_mul_of_nonneg_left hTup zero_le_two)
    rw [show 2 * (H * c) = (2 * H) * c by ring,
      Real.log_mul (by linarith only [hH1]) hc0.ne'] at ht
    have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
    linarith only [ht, hlogc]
  set k := Real.log ⌊(N : ℝ) ^ θ₀⌋₊ / D - 1 with hkdef
  set B := terminalPacketCost ⌊(N : ℝ) ^ θ₀⌋₊ (N / linearDefectCutoff c) N /
    Real.log ((N / linearDefectCutoff c : ℕ) : ℝ) with hBdef
  have hk_le : k ≤ θ₀ * Real.log N / D := by
    rw [hkdef]
    have := div_le_div_of_nonneg_right hlogR_le hD.le
    linarith only [this]
  have hB_le : B ≤ 2 * (4 + Real.log (2 * H) + c) / Real.log N := by
    rw [hBdef, div_le_div_iff₀ hlogM_pos hL0]
    have h1 : terminalPacketCost ⌊(N : ℝ) ^ θ₀⌋₊ (N / linearDefectCutoff c) N ≤
        4 + Real.log (2 * H) + c := by linarith only [hTB, hlog2T]
    have h0 : 0 ≤ terminalPacketCost ⌊(N : ℝ) ^ θ₀⌋₊ (N / linearDefectCutoff c) N :=
      terminalPacketCost_nonneg _ (Nat.div_le_self _ _)
    have hpos : 0 ≤ 4 + Real.log (2 * H) + c := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * H by linarith only [hH1]); linarith
    nlinarith only [h1, h0, hpos, hhalf_M, hL0]
  have hB0 : 0 ≤ B := div_nonneg (terminalPacketCost_nonneg _ (Nat.div_le_self _ _))
    hlogM_pos.le
  have hleak : (7 / 4 : ℝ) * k * B ≤ g / (8 * c ^ 7) * Real.log N := by
    have h1 : (7 / 4 : ℝ) * k * B ≤
        (7 / 4 : ℝ) * (θ₀ * Real.log N / D) * (2 * (4 + Real.log (2 * H) + c) / Real.log N) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hk_le (by norm_num)) hB_le hB0 (by positivity)
    have h2 : (7 / 4 : ℝ) * (θ₀ * Real.log N / D) * (2 * (4 + Real.log (2 * H) + c) /
        Real.log N) = 7 * θ₀ * (4 + Real.log (2 * H) + c) / (2 * D) := by
      field_simp; ring
    have h3 : 7 * θ₀ * (4 + Real.log (2 * H) + c) / (2 * D) ≤ C_lk * c := by
      have hl := Real.log_nonneg (show (1 : ℝ) ≤ 2 * H by linarith only [hH1])
      have hnum : 7 * θ₀ * (4 + Real.log (2 * H) + c) ≤ 7 * θ₀ * (5 + Real.log (2 * H)) * c := by
        have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 7 * θ₀)
          (by linarith only [hl] : (0 : ℝ) ≤ 4 + Real.log (2 * H))) (sub_nonneg.mpr hc1)
        nlinarith only [this]
      calc 7 * θ₀ * (4 + Real.log (2 * H) + c) / (2 * D)
          ≤ 7 * θ₀ * (5 + Real.log (2 * H)) * c / (2 * D) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = C_lk * c := by rw [hClk]; ring
    have h4 : C_lk * c ≤ g / (8 * c ^ 7) * Real.log N := by
      have hc8 : c ^ 8 ≤ Real.log N ^ (8 * α) := by
        have hp := pow_le_pow_left₀ hc0.le hcα 8
        exact hp.trans_eq (by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring)
      have hsplit : Real.log N ^ (1 - 8 * α) * Real.log N ^ (8 * α) = Real.log N := by
        rw [← Real.rpow_add hL0, show 1 - 8 * α + 8 * α = (1 : ℝ) by ring, Real.rpow_one]
      have hμ : 16 * C_lk / g ≤ Real.log N ^ (1 - 8 * α) := hLμ
      have hμ' : 16 * C_lk ≤ g * Real.log N ^ (1 - 8 * α) := by
        have := (div_le_iff₀ hg).mp hμ; linarith only [this]
      rw [show g / (8 * c ^ 7) * Real.log N = g * Real.log N / (8 * c ^ 7) by ring,
        le_div_iff₀ (by positivity)]
      calc C_lk * c * (8 * c ^ 7) = 8 * C_lk * c ^ 8 := by ring
        _ ≤ 8 * C_lk * Real.log N ^ (8 * α) := mul_le_mul_of_nonneg_left hc8 (by positivity)
        _ ≤ (g * Real.log N ^ (1 - 8 * α) / 2) * Real.log N ^ (8 * α) :=
            mul_le_mul_of_nonneg_right (by linarith only [hμ']) (by positivity)
        _ = g / 2 * (Real.log N ^ (1 - 8 * α) * Real.log N ^ (8 * α)) := by ring
        _ = g * Real.log N / 2 := by rw [hsplit]; ring
        _ ≤ g * Real.log N := by linarith only [mul_pos hg hL0]
    linarith only [h1, h2, h3, h4]
  have hP0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hpre' : k * ((15 / 16 : ℝ) *
      (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) -
      2 * B * (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2)) ≤
      poleDefect (N / linearDefectCutoff c) (primeHorizonExtension z) := by
    have e : 2 * terminalPacketCost ⌊(N : ℝ) ^ θ₀⌋₊ (N / linearDefectCutoff c) N /
        Real.log ((N / linearDefectCutoff c : ℕ) : ℝ) = 2 * B := by rw [hBdef]; ring
    rw [← e]; exact hpre
  have hcomb := coercive_combine hD hθ₀ hL0.le hc1 hP0 hS0 hgap hpre' hleak hfarz
  exact hcomb

/-- **Polynomial-conductor complement coercivity below the eighth root.** For every `θ > 0` and
every `0 < α < 1 / 8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`, every
`z ∈ (conductorSubspace ⌊N^θ⌋₊ N)ᗮ` satisfies
`(c_orth log N / c⁷) ‖z‖² ≤ completeWeilEnergy tiltedUnitSpline c N z`. -/
theorem eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal_below_one_eighth
    {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α) (hα_lt : α < 1 / 8) :
    ∃ c_orth : ℝ, 0 < c_orth ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N)ᗮ →
          (c_orth * Real.log (N : ℝ) / c ^ 7) * ‖z‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N z := by
  set D := explicitConductorCutoffConstant with hDdef
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  set θ₀ := min θ (1 / 36) with hθ₀def
  have hθ₀ : 0 < θ₀ := lt_min hθ (by norm_num)
  have hθ₀_le : θ₀ ≤ θ := min_le_left _ _
  have hθ₀_36 : θ₀ ≤ 1 / 36 := min_le_right _ _
  set g := growingMassConstant with hgdef
  have hg : 0 < g := growingMassConstant_pos
  refine ⟨min (θ₀ / (8 * D)) (g / 8), lt_min (by positivity) (by positivity), ?_⟩
  filter_upwards [eventually_completeWeilEnergy_two_region_on_polynomialConductorOrthogonal_below_one_eighth
      hθ₀ hθ₀_36 hα hα_lt, eventually_ge_atTop 1] with N htwo hN1
  intro c hc1 hcα z hz
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg hN1R
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hR_le : ⌊(N : ℝ) ^ θ₀⌋₊ ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1R hθ₀_le)
  have hzR : z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ₀⌋₊ N)ᗮ := fun v hv =>
    hz v (conductorSubspace_mono hR_le N hv)
  have hcomb := htwo c hc1 hcα hzR
  have hP0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  rw [norm_sq_eq_prefix_add_top (N / linearDefectCutoff c) (Nat.div_le_self _ _) z]
  have hc7 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
  have hcoefP : min (θ₀ / (8 * D)) (g / 8) * Real.log N / c ^ 7 ≤ θ₀ / (8 * D) * Real.log N := by
    rw [div_le_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_right (min_le_left (θ₀ / (8 * D)) (g / 8)) hL0
    have h2 := mul_le_mul_of_nonneg_left hc7
      (mul_nonneg (by positivity : (0 : ℝ) ≤ θ₀ / (8 * D)) hL0)
    linarith only [h1, h2]
  have hcoefS : min (θ₀ / (8 * D)) (g / 8) * Real.log N / c ^ 7 ≤ g / (8 * c ^ 7) * Real.log N := by
    have h1 := min_le_right (θ₀ / (8 * D)) (g / 8)
    rw [show g / (8 * c ^ 7) * Real.log N = (g / 8) * Real.log N / c ^ 7 by field_simp]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hL0) (by positivity)
  have hp := mul_le_mul_of_nonneg_right hcoefP hP0
  have hs := mul_le_mul_of_nonneg_right hcoefS hS0
  linarith only [hcomb, hp, hs]

/-- **Global polynomial-conductor ceiling on nonpositive subspaces below the eighth root.** For
every `θ > 0` and `0 < α < 1 / 8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
every subspace on which `completeWeilEnergy` is nonpositive on nonzero vectors has dimension at
most `⌊N^θ⌋₊`. -/
theorem eventually_completeWeil_global_negIndex_le_polynomialConductor_below_one_eighth
    {θ α : ℝ} (hθ : 0 < θ) (hα : 0 < α) (hα_lt : α < 1 / 8) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ U : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)),
        (∀ z ∈ U, z ≠ 0 → completeWeilEnergy tiltedUnitSpline c N z ≤ 0) →
        Module.finrank ℝ U ≤ ⌊(N : ℝ) ^ θ⌋₊ := by
  let θ₀ := min θ (1 / 4)
  have hθ₀ : 0 < θ₀ := lt_min hθ (by norm_num)
  have hθ₀_le : θ₀ ≤ θ := min_le_left _ _
  have hθ₀_4 : θ₀ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨c_orth, hc_orth, horth⟩ :=
    eventually_completeWeilEnergy_ge_on_polynomialConductorOrthogonal_below_one_eighth
      hθ₀ hα hα_lt
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ₀) atTop atTop :=
    (tendsto_rpow_atTop hθ₀).comp tendsto_natCast_atTop_atTop
  filter_upwards [horth, hNθlim.eventually_ge_atTop 2, eventually_ge_atTop 3] with
    N horthN hNθ2 hN3 c hc1 hcup U hU
  have hN2 : 2 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  let Q₀ := ⌊(N : ℝ) ^ θ₀⌋₊
  have hQ₀_mono : Q₀ ≤ ⌊(N : ℝ) ^ θ⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hN1R hθ₀_le)
  have hQ₀_pos : 0 < Q₀ :=
    Nat.le_floor (by exact_mod_cast (show (1 : ℝ) ≤ (N : ℝ) ^ θ₀ by linarith only [hNθ2]))
  have hQ₀_le : (Q₀ : ℝ) ≤ (N : ℝ) ^ θ₀ := Nat.floor_le (by positivity)
  have h2log : 2 * Real.log (Q₀ : ℝ) < Real.log (N : ℝ) := by
    have hlog_le : Real.log (Q₀ : ℝ) ≤ θ₀ * Real.log (N : ℝ) :=
      (Real.log_le_log (by exact_mod_cast hQ₀_pos) hQ₀_le).trans_eq (Real.log_rpow hN0 θ₀)
    have hhalf : 2 * (θ₀ * Real.log (N : ℝ)) ≤ (1 / 2) * Real.log (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hθ₀_4 hL0.le; linarith only [h]
    linarith only [hlog_le, hhalf, hL0]
  have hinf_bot : U ⊓ (conductorSubspace Q₀ N)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    by_contra hzne
    have hz_le := hU z hz.1 hzne
    have hz_ge := horthN c hc1 hcup hz.2
    have hpos : 0 < (c_orth * Real.log (N : ℝ) / c ^ 7) * ‖z‖ ^ 2 :=
      mul_pos (div_pos (mul_pos hc_orth hL0) (pow_pos hc0 7))
        (sq_pos_of_pos (norm_pos_iff.mpr hzne))
    linarith only [hz_le, hz_ge, hpos]
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq U ((conductorSubspace Q₀ N)ᗮ)
  rw [Submodule.finrank_eq_zero.mpr hinf_bot, add_zero] at hgrass
  have hsup_le : Module.finrank ℝ ↥(U ⊔ (conductorSubspace Q₀ N)ᗮ) ≤
      Module.finrank ℝ (conductorSubspace Q₀ N) +
        Module.finrank ℝ ↥((conductorSubspace Q₀ N)ᗮ) := by
    calc
      Module.finrank ℝ ↥(U ⊔ (conductorSubspace Q₀ N)ᗮ) ≤
          Module.finrank ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)) :=
        Submodule.finrank_le _
      _ = Module.finrank ℝ (conductorSubspace Q₀ N) +
            Module.finrank ℝ ↥((conductorSubspace Q₀ N)ᗮ) :=
        (Submodule.finrank_add_finrank_orthogonal (conductorSubspace Q₀ N)).symm
  have hfin_eq := finrank_conductorSubspace_eq hN2 h2log
  rw [hgrass, hfin_eq] at hsup_le
  exact (Nat.le_of_add_le_add_right hsup_le).trans hQ₀_mono

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
