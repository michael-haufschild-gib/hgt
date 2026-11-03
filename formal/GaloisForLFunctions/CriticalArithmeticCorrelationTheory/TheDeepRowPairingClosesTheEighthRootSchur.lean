import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheConductorResidualsAreSmallOnTheDeepRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheEighthRootComplementKeepsItsBlockReserves

/-!
# The deep-row pairing closes the eighth-root Schur step

The Schur coupling of the conductor block `y = Σ_{m ≤ Q₁} a_m v_m` with the complement
`z = u₀ + u₁ + w` is `⟨W'y, z⟩ = Σ a_m ⟨r_m, z⟩` (`r_m = W v_m − E_m v_m`). Its cost
`Σ ⟨r_m, z⟩²/E_m` is split by rows: on the top rows `nX > N` only `u₀`'s top mass
(`O(log X / log N)` of `‖u₀‖²`, `sum_topRows_sq_le`) meets the full residual, and on the deep rows
`nX ≤ N` the residual is `O(m(1 + log m)²/log N)` (`TheConductorResidualsAreSmallOnTheDeepRows`).
`u₁` and `w` pay with the full residual mass against their large block reserves.

* `inner_sq_le_deep_add_top`, `pairing_sum_le`: the row split of the pairing.
* `schur_with_deep_pairing_pos`, `spectralFloor_posDef_of_blocks`: Schur synthesis with block
  reserves `μ₀ ≥ 32(Ψρ_top + Ψ_D)`, `μ₁, μ_S ≥ 16Ψ`.
* `deepResidualBudget_le_rate`, `deepResidualRate_le`, `deep_inverse_energy_mass_le`: the
  deep-row inverse-energy mass `Ψ_D ≤ 8(C_p + 1)/log N · (8c⁷ + Q²(1 + log Q)²)/κ` at
  `X = ⌊exp √log N⌋`, with the affine shell rate at scale `Y = X/(2c)`.
* `schur_scalars_one_eighth`: the three budget inequalities below `1/8`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-! ### Pairing a residual with a band split across top and deep rows -/

/-- The top rows `N < nX`. -/
def topRows (N : ℕ) (X : ℝ) : Finset ℕ := (Icc 1 N).filter fun n : ℕ => ¬ ((n : ℝ) * X ≤ N)

theorem inner_sq_le_deep_add_top {N : ℕ} (X : ℝ) (r u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪r, u⟫ ^ 2 ≤ 2 * (‖r‖ ^ 2 * ∑ n ∈ topRows N X, primeHorizonExtension u n ^ 2) +
      2 * (deepMass X r * ‖u‖ ^ 2) := by
  rw [inner_eq_sum_primeHorizonExtension, ← sum_filter_add_sum_filter_not (Icc 1 N)
    (fun n : ℕ => (n : ℝ) * X ≤ N)]
  set D := ∑ n ∈ deepRows N X, primeHorizonExtension r n * primeHorizonExtension u n
  set T := ∑ n ∈ topRows N X, primeHorizonExtension r n * primeHorizonExtension u n
  change (D + T) ^ 2 ≤ _
  have hD := Finset.sum_mul_sq_le_sq_mul_sq (deepRows N X) (primeHorizonExtension r)
    (primeHorizonExtension u)
  have hT := Finset.sum_mul_sq_le_sq_mul_sq (topRows N X) (primeHorizonExtension r)
    (primeHorizonExtension u)
  have hr : (∑ n ∈ topRows N X, primeHorizonExtension r n ^ 2) ≤ ‖r‖ ^ 2 := by
    rw [← sum_primeHorizonExtension_sq]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hu : (∑ n ∈ deepRows N X, primeHorizonExtension u n ^ 2) ≤ ‖u‖ ^ 2 :=
    deepMass_le_norm_sq X u
  have hu0 : 0 ≤ ∑ n ∈ topRows N X, primeHorizonExtension u n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hr0 : 0 ≤ deepMass X r := deepMass_nonneg X r
  have h1 : T ^ 2 ≤ ‖r‖ ^ 2 * ∑ n ∈ topRows N X, primeHorizonExtension u n ^ 2 :=
    hT.trans (mul_le_mul_of_nonneg_right hr hu0)
  have h2 : D ^ 2 ≤ deepMass X r * ‖u‖ ^ 2 := hD.trans (mul_le_mul_of_nonneg_left hu hr0)
  nlinarith [sq_nonneg (D - T)]

/-- The top rows of a band of conductors `≤ R` carry `O(log X/log N)` of its mass. -/
theorem sum_topRows_sq_le {R N : ℕ} {X : ℝ} (hR : 2 ≤ R) (hX : 1 ≤ X)
    (hRNX : ((R * R : ℕ) + 1 : ℝ) * X ≤ N) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    (∑ n ∈ topRows N X, primeHorizonExtension u n ^ 2) ≤
      2 * (Real.log (2 * X) + 3) / Real.log N * ‖u‖ ^ 2 := by
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  have h := sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hX hRNX hlog hu
  have he : topRows N X = (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < X) := by
    unfold topRows
    refine filter_congr fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    rw [not_le, div_lt_iff₀ hn0, mul_comm]
  rw [he, div_mul_eq_mul_div, le_div_iff₀ hL]
  linarith

/-! ### The Schur step with the deep-row pairing -/

/-- **The deep-row pairing.** `Σ ⟨r_m, u₀ + u₁ + w⟩²/E_m ≤ 4Ψρ_top‖u₀‖² + 4Ψ_D‖u₀‖² + 2Ψ(‖u₁‖² + ‖w‖²)`
when the top rows carry at most `ρ_top` of `u₀`, `Ψ ≥ Σ ‖r_m‖²/E_m` and `Ψ_D ≥ Σ deepMass(r_m)/E_m`. -/
theorem pairing_sum_le {N : ℕ} {s : Finset ℕ} {E : ℕ → ℝ}
    {r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N)} {X Ψ Ψ_D ρ_top : ℝ}
    {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hE : ∀ m ∈ s, 0 < E m)
    (hu₁w : ‖u₁ + w‖ ^ 2 = ‖u₁‖ ^ 2 + ‖w‖ ^ 2)
    (htop : (∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2) ≤ ρ_top * ‖u₀‖ ^ 2)
    (hΨ : (∑ m ∈ s, ‖r m‖ ^ 2 / E m) ≤ Ψ) (hΨD : (∑ m ∈ s, deepMass X (r m) / E m) ≤ Ψ_D) :
    (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      4 * Ψ * ρ_top * ‖u₀‖ ^ 2 + 4 * Ψ_D * ‖u₀‖ ^ 2 + 2 * Ψ * (‖u₁‖ ^ 2 + ‖w‖ ^ 2) := by
  have htop0 : 0 ≤ ∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hdeep := fun m => inner_sq_le_deep_add_top X (r m) u₀
  generalize (∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2) = top at htop htop0 hdeep
  have hpair : ∀ m, ⟪r m, u₀ + u₁ + w⟫ ^ 2 ≤
      4 * (‖r m‖ ^ 2 * top) + 4 * (deepMass X (r m) * ‖u₀‖ ^ 2) +
        2 * (‖r m‖ ^ 2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2)) := by
    intro m
    have hsplit : ⟪r m, u₀ + u₁ + w⟫ = ⟪r m, u₀⟫ + ⟪r m, u₁ + w⟫ := by
      rw [add_assoc, inner_add_right]
    have h0 := hdeep m
    have h1 : ⟪r m, u₁ + w⟫ ^ 2 ≤ ‖r m‖ ^ 2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2) := by
      rw [← hu₁w, ← mul_pow]
      have := abs_real_inner_le_norm (r m) (u₁ + w)
      exact (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) this 2)
    rw [hsplit]
    have h2 : (⟪r m, u₀⟫ + ⟪r m, u₁ + w⟫) ^ 2 ≤ 2 * ⟪r m, u₀⟫ ^ 2 + 2 * ⟪r m, u₁ + w⟫ ^ 2 := by
      nlinarith only [sq_nonneg (⟪r m, u₀⟫ - ⟪r m, u₁ + w⟫)]
    linarith only [h0, h1, h2]
  have hΨ0 : 0 ≤ ∑ m ∈ s, ‖r m‖ ^ 2 / E m := sum_nonneg fun m hm => div_nonneg (sq_nonneg _) (hE m hm).le
  have hrhs : 4 * top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
      4 * ‖u₀‖ ^ 2 * (∑ m ∈ s, deepMass X (r m) / E m) +
      2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2) * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) =
      ∑ m ∈ s, (4 * top * (‖r m‖ ^ 2 / E m) + 4 * ‖u₀‖ ^ 2 * (deepMass X (r m) / E m) +
        2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2) * (‖r m‖ ^ 2 / E m)) := by
    rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
  have h1 : (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      4 * top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
        4 * ‖u₀‖ ^ 2 * (∑ m ∈ s, deepMass X (r m) / E m) +
        2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2) * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) := by
    rw [hrhs]
    refine sum_le_sum fun m hm => ?_
    have hEm := hE m hm
    rw [div_le_iff₀ hEm]
    have e : (4 * top * (‖r m‖ ^ 2 / E m) + 4 * ‖u₀‖ ^ 2 * (deepMass X (r m) / E m) +
        2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2) * (‖r m‖ ^ 2 / E m)) * E m =
        4 * (‖r m‖ ^ 2 * top) + 4 * (deepMass X (r m) * ‖u₀‖ ^ 2) +
          2 * (‖r m‖ ^ 2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2)) := by
      field_simp
    rw [e]; exact hpair m
  have hΨ' : 0 ≤ Ψ := hΨ0.trans hΨ
  have h2 : top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) ≤ (ρ_top * ‖u₀‖ ^ 2) * Ψ :=
    mul_le_mul htop hΨ hΨ0 (htop0.trans htop)
  have h3 := mul_le_mul_of_nonneg_left hΨD (by positivity : (0 : ℝ) ≤ 4 * ‖u₀‖ ^ 2)
  have h4 := mul_le_mul_of_nonneg_left hΨ (by positivity : (0 : ℝ) ≤ 2 * (‖u₁‖ ^ 2 + ‖w‖ ^ 2))
  have e2 : 4 * top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) = 4 * (top * (∑ m ∈ s, ‖r m‖ ^ 2 / E m)) := by
    ring
  have e3 : (ρ_top * ‖u₀‖ ^ 2) * Ψ = Ψ * ρ_top * ‖u₀‖ ^ 2 := by ring
  linarith only [h1, h2, h3, h4, e2, e3]

/-- `2 |Σ a_m t_m| ≤ (Σ E_m a_m²)/8 + 8 Σ t_m²/E_m` for positive weights `E_m`. -/
theorem two_abs_weighted_sum_le {s : Finset ℕ} {E a t : ℕ → ℝ} (hE : ∀ m ∈ s, 0 < E m) :
    2 * |∑ m ∈ s, a m * t m| ≤ (∑ m ∈ s, E m * a m ^ 2) / 8 + 8 * ∑ m ∈ s, t m ^ 2 / E m := by
  have hS : 0 ≤ ∑ m ∈ s, E m * a m ^ 2 := sum_nonneg fun m hm => mul_nonneg (hE m hm).le (sq_nonneg _)
  have hΦ : 0 ≤ ∑ m ∈ s, t m ^ 2 / E m := sum_nonneg fun m hm => div_nonneg (sq_nonneg _) (hE m hm).le
  have hcs : (∑ m ∈ s, a m * t m) ^ 2 ≤
      (∑ m ∈ s, E m * a m ^ 2) * Real.sqrt (∑ m ∈ s, t m ^ 2 / E m) ^ 2 := by
    rw [Real.sq_sqrt hΦ]
    have hf : ∀ m ∈ s, a m * t m = (a m * Real.sqrt (E m)) * (t m / Real.sqrt (E m)) := by
      intro m hm
      have hs : 0 < Real.sqrt (E m) := Real.sqrt_pos.mpr (hE m hm)
      field_simp
    rw [sum_congr rfl hf]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
    congr 1
    · refine sum_congr rfl fun m hm => ?_
      rw [mul_pow, Real.sq_sqrt (hE m hm).le]; ring
    · refine sum_congr rfl fun m hm => ?_
      rw [div_pow, Real.sq_sqrt (hE m hm).le]
  have := two_abs_le_of_sq_le hS (by norm_num : (0 : ℝ) < 8) hcs
  rwa [Real.sq_sqrt hΦ] at this

/-- **Schur synthesis with block reserves and the deep-row pairing.** Let `y = Σ_{m ≤ Q₁} a_m v_m`,
`z = u₀ + u₁ + w ⊥ V_{Q₁}` with orthogonal blocks, and let the residuals `r_m = W v_m − E_m v_m`
have inverse-energy mass `≤ Ψ` and deep-row inverse-energy mass `≤ Ψ_D`. If the top rows carry at
most `ρ_top` of `u₀`, the block reserves `μ₀ ≥ 32(Ψρ_top + Ψ_D)`, `μ₁, μ_S ≥ 16Ψ` absorb the
cross term and `⟪W'(y + z), y + z⟫ > 0` for `y + z ≠ 0`. -/
theorem schur_with_deep_pairing_pos {Q₁ N : ℕ} {c X Ψ Ψ_D ρ_top μ₀ μ₁ μ_S : ℝ}
    (hc1 : 1 ≤ c) (a : ℕ → ℝ) {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hz : u₀ + u₁ + w ∈ (conductorSubspace Q₁ N)ᗮ)
    (hnorm : ‖u₀ + u₁ + w‖ ^ 2 = ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖w‖ ^ 2)
    (hu₁w : ‖u₁ + w‖ ^ 2 = ‖u₁‖ ^ 2 + ‖w‖ ^ 2)
    (hy_floor :
      (1 / 4 : ℝ) * (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
        ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
            (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N⟫)
    (hz_floor : (tiltedSplineSpectralFloorConstant + 2 + μ₀) * ‖u₀‖ ^ 2 +
        (tiltedSplineSpectralFloorConstant + 2 + μ₁) * ‖u₁‖ ^ 2 +
        (tiltedSplineSpectralFloorConstant + 2 + μ_S) * ‖w‖ ^ 2 ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w))
    (htop : (∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2) ≤ ρ_top * ‖u₀‖ ^ 2)
    (hΨ : (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m) ≤ Ψ)
    (hΨD : (∑ m ∈ Icc 1 Q₁,
        deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤ Ψ_D)
    (hμ₀ : 32 * Ψ * ρ_top + 32 * Ψ_D ≤ μ₀) (hμ₁ : 16 * Ψ ≤ μ₁) (hμS : 16 * Ψ ≤ μ_S)
    (hne : (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w) ≠ 0) :
    0 < ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          ((∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w)),
        (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w)⟫ := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hE_pos : ∀ m ∈ Icc 1 Q₁, 0 < completedConductorEnergy tiltedUnitSpline c m := by
    intro m hm
    have hs : 0 < tiltedSplineSpectralFloorConstant / (2 * c ^ 7) :=
      div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
    have hge := spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1
    linarith only [hs, hge]
  have hSy0 : 0 ≤ ∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2 :=
    sum_nonneg fun m hm => mul_nonneg (hE_pos m hm).le (sq_nonneg _)
  -- the cross term
  have hy_mem : (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) ∈
      conductorSubspace Q₁ N := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N a
  have hyz0 : ⟪∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N, u₀ + u₁ + w⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hy_mem hz
  have hvm_z0 : ∀ m ∈ Icc 1 Q₁, ⟪normalizedRamanujanHorizonVector m N, u₀ + u₁ + w⟫ = 0 := by
    intro m hm
    let b : ℕ → ℝ := fun k => if k = m then 1 else 0
    have hb_eq : (∑ k ∈ Icc 1 Q₁, b k • normalizedRamanujanHorizonVector k N) =
        normalizedRamanujanHorizonVector m N := by
      dsimp only [b]
      rw [sum_eq_single m]
      · simp
      · intro k _ hkm; rw [if_neg hkm, zero_smul]
      · intro hm_not; exact False.elim (hm_not hm)
    have hmem : normalizedRamanujanHorizonVector m N ∈ conductorSubspace Q₁ N := by
      rw [← hb_eq]
      exact sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N b
    exact Submodule.inner_right_of_mem_orthogonal hmem hz
  have hcross_eq : ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
        (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫ =
      ∑ m ∈ Icc 1 Q₁, a m * ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N,
        u₀ + u₁ + w⟫ := by
    have h1 : ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫ =
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫ := by
      simp only [spectralFloorWeilMatrix, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, identity_euclid_apply_telescoped, inner_sub_left,
        real_inner_smul_left, hyz0, mul_zero, sub_zero]
    rw [h1, map_sum, sum_inner]
    refine sum_congr rfl fun m hm => ?_
    rw [map_smul, real_inner_smul_left]
    congr 1
    rw [inner_sub_left, real_inner_smul_left, hvm_z0 m hm, mul_zero, sub_zero]
  have hcross_abs := two_abs_weighted_sum_le (a := a) (t := fun m =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N,
        u₀ + u₁ + w⟫) hE_pos
  rw [← hcross_eq] at hcross_abs
  have hΦ := pairing_sum_le hE_pos hu₁w htop hΨ hΨD
  -- the block `z`
  have hz_A : 2 * ‖u₀ + u₁ + w‖ ^ 2 + μ₀ * ‖u₀‖ ^ 2 + μ₁ * ‖u₁‖ ^ 2 + μ_S * ‖w‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) (u₀ + u₁ + w), u₀ + u₁ + w⟫ := by
    rw [spectralFloorWeilMatrix_inner]
    have hc7 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
    have hshift_le : tiltedSplineSpectralFloorConstant / (2 * c ^ 7) ≤
        tiltedSplineSpectralFloorConstant :=
      div_le_self tiltedSplineSpectralFloorConstant_pos.le (by linarith only [hc7])
    have hm := mul_le_mul_of_nonneg_right hshift_le (sq_nonneg ‖u₀ + u₁ + w‖)
    rw [hnorm] at hm ⊢
    linarith only [hz_floor, hm]
  have hΦμ : 8 * (4 * Ψ * ρ_top * ‖u₀‖ ^ 2 + 4 * Ψ_D * ‖u₀‖ ^ 2 + 2 * Ψ * (‖u₁‖ ^ 2 + ‖w‖ ^ 2)) ≤
      μ₀ * ‖u₀‖ ^ 2 + μ₁ * ‖u₁‖ ^ 2 + μ_S * ‖w‖ ^ 2 := by
    have h0 := mul_le_mul_of_nonneg_right hμ₀ (sq_nonneg ‖u₀‖)
    have h1 := mul_le_mul_of_nonneg_right hμ₁ (sq_nonneg ‖u₁‖)
    have h2 := mul_le_mul_of_nonneg_right hμS (sq_nonneg ‖w‖)
    linarith only [h0, h1, h2]
  have hexp := hermitian_inner_add_eq_telescoped (spectralFloorWeilMatrix_isHermitian c N)
    (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) (u₀ + u₁ + w)
  have habs := neg_abs_le ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
    (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N), u₀ + u₁ + w⟫
  have hlb : (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) / 8 +
      2 * ‖u₀ + u₁ + w‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          ((∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w)),
        (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w)⟫ := by
    rw [hexp]
    linarith only [hy_floor, hz_A, hcross_abs, habs, hΦμ, hΦ]
  refine lt_of_lt_of_le ?_ hlb
  by_contra hnot
  have hle0 := not_lt.mp hnot
  have hz_sq0 : ‖u₀ + u₁ + w‖ ^ 2 = 0 := by linarith only [hle0, hSy0, sq_nonneg ‖u₀ + u₁ + w‖]
  have hSy00 : (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) = 0 := by
    linarith only [hle0, hSy0, sq_nonneg ‖u₀ + u₁ + w‖]
  have hz0 : u₀ + u₁ + w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz_sq0)
  have hterm0 : ∀ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2 = 0 :=
    fun m hm => (sum_eq_zero_iff_of_nonneg fun k hk => mul_nonneg (hE_pos k hk).le
      (sq_nonneg _)).mp hSy00 m hm
  have ha0 : ∀ m ∈ Icc 1 Q₁, a m = 0 := by
    intro m hm
    rcases mul_eq_zero.mp (hterm0 m hm) with hEm0 | ham0
    · exact False.elim ((hE_pos m hm).ne' hEm0)
    · exact sq_eq_zero_iff.mp ham0
  have hy0 : (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) = 0 :=
    sum_eq_zero fun m hm => by rw [ha0 m hm, zero_smul]
  exact hne (by rw [hy0, hz0, add_zero])

/-! ### The deep-row inverse-energy budget -/

/-- The per-unit-`m(1 + log m)²` deep-row residual rate for conductors `m ≤ Q`. -/
def deepResidualRate (C_p C_s C_q K₀ K_up : ℝ) (Q N : ℕ) (c X ρ : ℝ) : ℝ :=
  C_p / Real.log N + C_s * c ^ 2 / (N : ℝ) ^ 2 +
    (2 * c ^ 2 * (Q : ℝ) * harmonic N / ((N : ℝ) ^ 2 * Real.log N) +
      18 * c ^ 2 * (Q : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)) +
    (32 * K₀ ^ 2 * c ^ 4 / ((N : ℝ) * X * Real.log N) +
      2048 * K₀ ^ 2 * c ^ 2 / (X ^ 2 * Real.log N)) +
    C_q * c ^ 10 * (Real.log N / N) ^ 2 +
    3 * (K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 +
      2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 / (X * Real.log N) +
      ρ ^ 2 * harmonic N / Real.log N)

theorem deepResidualBudget_le_rate {C_p C_s C_q K₀ K_up : ℝ} {m Q N : ℕ} {c X ρ : ℝ}
    (hCs : 0 ≤ C_s) (hCq : 0 ≤ C_q) (hKup : 0 ≤ K_up)
    (hm : 1 ≤ m) (hmQ : m ≤ Q) (hX : 0 < X) (hL : 0 < Real.log N) :
    deepResidualBudget C_p C_s C_q K₀ K_up m N c X ρ ≤
      (m : ℝ) * (1 + Real.log m) ^ 2 * deepResidualRate C_p C_s C_q K₀ K_up Q N c X ρ := by
  unfold deepResidualBudget deepResidualRate
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmQ' : (m : ℝ) ≤ Q := by exact_mod_cast hmQ
  have hlm : 1 ≤ (1 + Real.log m) ^ 2 := one_le_pow₀ (by linarith [Real.log_natCast_nonneg m])
  set w := (m : ℝ) * (1 + Real.log m) ^ 2 with hw
  have hw1 : (m : ℝ) ≤ w := le_mul_of_one_le_right (by positivity) hlm
  have hw1' : 1 ≤ w := hm1.trans hw1
  have hm2 : (m : ℝ) ^ 2 ≤ w * Q := by
    rw [sq]; exact mul_le_mul hw1 hmQ' (by positivity) (by positivity)
  have htot : (m.totient : ℝ) ≤ w := (by exact_mod_cast Nat.totient_le m : (m.totient : ℝ) ≤ m).trans hw1
  have hH := harmonic_nonneg_real N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- termwise
  have t1 : C_p * w / Real.log N = w * (C_p / Real.log N) := by ring
  have t2 : C_s * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 ≤ w * (C_s * c ^ 2 / (N : ℝ) ^ 2) := by
    have : C_s * (m : ℝ) * c ^ 2 / (N : ℝ) ^ 2 = (m : ℝ) * (C_s * c ^ 2 / (N : ℝ) ^ 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hw1 (by positivity)
  have t3 : 2 * c ^ 2 * (m : ℝ) ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N) ≤
      w * (2 * c ^ 2 * (Q : ℝ) * harmonic N / ((N : ℝ) ^ 2 * Real.log N)) := by
    have e1 : 2 * c ^ 2 * (m : ℝ) ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N) =
        (m : ℝ) ^ 2 * (2 * c ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N)) := by ring
    have e2 : w * (2 * c ^ 2 * (Q : ℝ) * harmonic N / ((N : ℝ) ^ 2 * Real.log N)) =
        (w * Q) * (2 * c ^ 2 * harmonic N / ((N : ℝ) ^ 2 * Real.log N)) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hm2 (by positivity)
  have t4 : 18 * c ^ 2 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N) ≤
      w * (18 * c ^ 2 * (Q : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)) := by
    have e1 : 18 * c ^ 2 * (m : ℝ) ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N) =
        (m : ℝ) ^ 2 * (18 * c ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)) := by ring
    have e2 : w * (18 * c ^ 2 * (Q : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)) =
        (w * Q) * (18 * c ^ 2 * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)) := by ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hm2 (by positivity)
  have t5 : 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / ((N : ℝ) * X * Real.log N) ≤
      w * (32 * K₀ ^ 2 * c ^ 4 / ((N : ℝ) * X * Real.log N)) := by
    have : 32 * K₀ ^ 2 * (m : ℝ) * c ^ 4 / ((N : ℝ) * X * Real.log N) =
        (m : ℝ) * (32 * K₀ ^ 2 * c ^ 4 / ((N : ℝ) * X * Real.log N)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hw1 (by positivity)
  have t6 : 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / (X ^ 2 * Real.log N) ≤
      w * (2048 * K₀ ^ 2 * c ^ 2 / (X ^ 2 * Real.log N)) := by
    have : 2048 * K₀ ^ 2 * (m : ℝ) * c ^ 2 / (X ^ 2 * Real.log N) =
        (m : ℝ) * (2048 * K₀ ^ 2 * c ^ 2 / (X ^ 2 * Real.log N)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hw1 (by positivity)
  have t7 : C_q * (m : ℝ) * c ^ 10 * (Real.log N / N) ^ 2 ≤
      w * (C_q * c ^ 10 * (Real.log N / N) ^ 2) := by
    have : C_q * (m : ℝ) * c ^ 10 * (Real.log N / N) ^ 2 =
        (m : ℝ) * (C_q * c ^ 10 * (Real.log N / N) ^ 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hw1 (by positivity)
  have t8 : K_up * (m.totient : ℝ) * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 *
      (Real.log N / N) ^ 2 ≤ w * (K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 *
        (Real.log N / N) ^ 2) := by
    have : K_up * (m.totient : ℝ) * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 *
        (Real.log N / N) ^ 2 = (m.totient : ℝ) * (K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 *
        (Real.log N / N) ^ 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right htot (by positivity)
  have t9 : 2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 *
      (m.totient : ℝ) / (X * Real.log N) ≤ w * (2048 * (linearPrimeStrip c : ℝ) ^ 2 *
        ((linearPrimeStrip c : ℝ) + 1) ^ 2 / (X * Real.log N)) := by
    have : 2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 *
        (m.totient : ℝ) / (X * Real.log N) = (m.totient : ℝ) * (2048 * (linearPrimeStrip c : ℝ) ^ 2 *
        ((linearPrimeStrip c : ℝ) + 1) ^ 2 / (X * Real.log N)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right htot (by positivity)
  have t10 : ρ ^ 2 * harmonic N / Real.log N ≤ w * (ρ ^ 2 * harmonic N / Real.log N) :=
    le_mul_of_one_le_left (by positivity) hw1'
  have e : w * (C_p / Real.log N + C_s * c ^ 2 / (N : ℝ) ^ 2 +
      (2 * c ^ 2 * (Q : ℝ) * harmonic N / ((N : ℝ) ^ 2 * Real.log N) +
        18 * c ^ 2 * (Q : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N)) +
      (32 * K₀ ^ 2 * c ^ 4 / ((N : ℝ) * X * Real.log N) +
        2048 * K₀ ^ 2 * c ^ 2 / (X ^ 2 * Real.log N)) +
      C_q * c ^ 10 * (Real.log N / N) ^ 2 +
      3 * (K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2 +
        2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 / (X * Real.log N) +
        ρ ^ 2 * harmonic N / Real.log N)) =
      w * (C_p / Real.log N) + w * (C_s * c ^ 2 / (N : ℝ) ^ 2) +
        (w * (2 * c ^ 2 * (Q : ℝ) * harmonic N / ((N : ℝ) ^ 2 * Real.log N)) +
          w * (18 * c ^ 2 * (Q : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * Real.log N))) +
        (w * (32 * K₀ ^ 2 * c ^ 4 / ((N : ℝ) * X * Real.log N)) +
          w * (2048 * K₀ ^ 2 * c ^ 2 / (X ^ 2 * Real.log N))) +
        w * (C_q * c ^ 10 * (Real.log N / N) ^ 2) +
        3 * (w * (K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * (Real.log N / N) ^ 2) +
          w * (2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 /
            (X * Real.log N)) +
          w * (ρ ^ 2 * harmonic N / Real.log N)) := by ring
  rw [e]
  linarith only [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]

/-- **Deep-row inverse-energy mass.** If every `deepMass(r_m) ≤ 8 m (1 + log m)² β` for
`m ≤ Q`, then `Σ deepMass(r_m)/E_m ≤ 8β (8c⁷ + Q²(1 + log Q)²)/κ`. -/
theorem sum_deepMass_inv_energy_le {N Q : ℕ} {c X β : ℝ} (hc1 : 1 ≤ c) (hβ : 0 ≤ β)
    (hdeep : ∀ m ∈ Icc 1 Q,
      deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) ≤
        8 * ((m : ℝ) * (1 + Real.log m) ^ 2 * β)) :
    (∑ m ∈ Icc 1 Q,
        deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤
      8 * β * ((8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / tiltedSplineSpectralFloorConstant) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  calc _ ≤ ∑ m ∈ Icc 1 Q, 8 * β * ((m : ℝ) * (1 + Real.log m) ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m) := by
        refine sum_le_sum fun m hm => ?_
        have hm1 := (mem_Icc.mp hm).1
        have hE := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
          integral_tiltedUnitSpline_sq_pos hc0 hm1
        rw [mul_div_assoc', ← mul_assoc]
        refine div_le_div_of_nonneg_right ?_ hE
        linarith only [hdeep m hm]
    _ = 8 * β * ∑ m ∈ Icc 1 Q, (m : ℝ) * (1 + Real.log m) ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_conductor_log_sq_inv_energy_le hc1 Q) (by positivity)

/-! ### Scalar closure of the deep-row rate -/

/-- `A / B ≤ C / L²` from `A ≤ C L^a`, `L^b ≤ B`, `a + 2 ≤ b`. -/
theorem div_le_of_pow_le {A B C L : ℝ} {a b : ℕ} (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hA : A ≤ C * L ^ a) (hB : L ^ b ≤ B) (hab : a + 2 ≤ b) : A / B ≤ C / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) hB
  rw [div_le_div_iff₀ hB0 (by positivity)]
  have h1 : L ^ a * L ^ 2 ≤ L ^ b := by rw [← pow_add]; exact pow_le_pow_right₀ hL hab
  calc A * L ^ 2 ≤ C * L ^ a * L ^ 2 := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = C * (L ^ a * L ^ 2) := by ring
    _ ≤ C * L ^ b := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * B := mul_le_mul_of_nonneg_left hB hC

/-- The deep-row rate is `(C_p + O(1/L))/L`: with `X ≥ L⁸`, `N ≥ L¹⁸`, `c, Q ≤ L`,
`H_N ≤ 2L`, the prime strip `≤ 4L` and `ρ² ≤ K_r/L²`, every non-prime term is `O(1/L²)`. -/
theorem deepResidualRate_le {C_p C_s C_q K₀ K_up K_r : ℝ} {Q N : ℕ} {c X ρ : ℝ}
    (hCs : 0 ≤ C_s) (hCq : 0 ≤ C_q) (hKup : 0 ≤ K_up) (hKr : 0 ≤ K_r)
    (hL1 : 1 ≤ Real.log N) (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hQL : (Q : ℝ) ≤ Real.log N)
    (hH : (harmonic N : ℝ) ≤ 2 * Real.log N) (hB : (linearPrimeStrip c : ℝ) ≤ 4 * Real.log N)
    (hX : Real.log N ^ 8 ≤ X) (hN : Real.log N ^ 18 ≤ N) (hρ : ρ ^ 2 ≤ K_r / Real.log N ^ 2)
    (hbig : C_s + 4 + 162 + 32 * K₀ ^ 2 + 2048 * K₀ ^ 2 + C_q + 46875 * K_up + 2457600 + 6 * K_r ≤
      Real.log N) :
    deepResidualRate C_p C_s C_q K₀ K_up Q N c X ρ ≤ (C_p + 1) / Real.log N := by
  unfold deepResidualRate
  set L := Real.log (N : ℝ) with hLdef
  have hL0 : 0 < L := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hH0 := harmonic_nonneg_real N
  have hB0 : (0 : ℝ) ≤ linearPrimeStrip c := Nat.cast_nonneg _
  have hX1 : 1 ≤ X := le_trans (one_le_pow₀ hL1) hX
  have hX0 : 0 < X := by linarith
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hN2 : L ^ 36 ≤ (N : ℝ) ^ 2 := by
    rw [show L ^ 36 = (L ^ 18) ^ 2 by ring]; exact pow_le_pow_left₀ (by positivity) hN 2
  have hc2 : c ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hc0 hcL 2
  have hc4 : c ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hc0 hcL 4
  have hc10 : c ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ hc0 hcL 10
  have t1 : C_s * c ^ 2 / (N : ℝ) ^ 2 ≤ C_s / L ^ 2 :=
    div_le_of_pow_le hL1 hCs (mul_le_mul_of_nonneg_left hc2 hCs) hN2 (by norm_num)
  have t2 : 2 * c ^ 2 * (Q : ℝ) * harmonic N / ((N : ℝ) ^ 2 * L) ≤ 4 / L ^ 2 := by
    refine div_le_of_pow_le (a := 4) (b := 37) hL1 (by norm_num) ?_ ?_ (by norm_num)
    · calc 2 * c ^ 2 * (Q : ℝ) * harmonic N ≤ 2 * L ^ 2 * L * (2 * L) := by gcongr
        _ = 4 * L ^ 4 := by ring
    · calc L ^ 37 = L ^ 36 * L := by ring
        _ ≤ (N : ℝ) ^ 2 * L := mul_le_mul_of_nonneg_right hN2 hL0.le
  have t3 : 18 * c ^ 2 * (Q : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 / (X ^ 2 * L) ≤ 162 / L ^ 2 := by
    refine div_le_of_pow_le (a := 5) (b := 17) hL1 (by norm_num) ?_ ?_ (by norm_num)
    · have hH1 : (harmonic N : ℝ) + 1 ≤ 3 * L := by linarith
      calc 18 * c ^ 2 * (Q : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 ≤ 18 * L ^ 2 * L * (3 * L) ^ 2 := by
            gcongr
        _ = 162 * L ^ 5 := by ring
    · calc L ^ 17 = (L ^ 8) ^ 2 * L := by ring
        _ ≤ X ^ 2 * L := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hX 2) hL0.le
  have t4 : 32 * K₀ ^ 2 * c ^ 4 / ((N : ℝ) * X * L) ≤ 32 * K₀ ^ 2 / L ^ 2 := by
    refine div_le_of_pow_le (a := 4) (b := 27) hL1 (by positivity)
      (mul_le_mul_of_nonneg_left hc4 (by positivity)) ?_ (by norm_num)
    calc L ^ 27 = L ^ 18 * L ^ 8 * L := by ring
      _ ≤ (N : ℝ) * X * L := by gcongr
  have t5 : 2048 * K₀ ^ 2 * c ^ 2 / (X ^ 2 * L) ≤ 2048 * K₀ ^ 2 / L ^ 2 := by
    refine div_le_of_pow_le (a := 2) (b := 17) hL1 (by positivity)
      (mul_le_mul_of_nonneg_left hc2 (by positivity)) ?_ (by norm_num)
    calc L ^ 17 = (L ^ 8) ^ 2 * L := by ring
      _ ≤ X ^ 2 * L := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hX 2) hL0.le
  have t6 : C_q * c ^ 10 * (L / N) ^ 2 ≤ C_q / L ^ 2 := by
    rw [div_pow, ← mul_div_assoc]
    refine div_le_of_pow_le (a := 12) (b := 36) hL1 hCq ?_ hN2 (by norm_num)
    calc C_q * c ^ 10 * L ^ 2 ≤ C_q * L ^ 10 * L ^ 2 := by gcongr
      _ = C_q * L ^ 12 := by ring
  have t7 : K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * (L / N) ^ 2 ≤
      15625 * K_up / L ^ 2 := by
    rw [div_pow, ← mul_div_assoc]
    refine div_le_of_pow_le (a := 12) (b := 36) hL1 (by positivity) ?_ hN2 (by norm_num)
    have hB1 : (linearPrimeStrip c : ℝ) + 1 ≤ 5 * L := by linarith
    calc K_up * c ^ 4 * ((linearPrimeStrip c : ℝ) + 1) ^ 6 * L ^ 2 ≤
        K_up * L ^ 4 * (5 * L) ^ 6 * L ^ 2 := by gcongr
      _ = 15625 * K_up * L ^ 12 := by ring
  have t8 : 2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 / (X * L) ≤
      819200 / L ^ 2 := by
    refine div_le_of_pow_le (a := 4) (b := 9) hL1 (by norm_num) ?_ ?_ (by norm_num)
    · have hB1 : (linearPrimeStrip c : ℝ) + 1 ≤ 5 * L := by linarith
      calc 2048 * (linearPrimeStrip c : ℝ) ^ 2 * ((linearPrimeStrip c : ℝ) + 1) ^ 2 ≤
          2048 * (4 * L) ^ 2 * (5 * L) ^ 2 := by gcongr
        _ = 819200 * L ^ 4 := by ring
    · calc L ^ 9 = L ^ 8 * L := by ring
        _ ≤ X * L := mul_le_mul_of_nonneg_right hX hL0.le
  have t9 : ρ ^ 2 * harmonic N / L ≤ 2 * K_r / L ^ 2 := by
    rw [div_le_div_iff₀ hL0 (by positivity)]
    have h1 : ρ ^ 2 * harmonic N ≤ K_r / L ^ 2 * (2 * L) :=
      mul_le_mul hρ hH hH0 (by positivity)
    calc ρ ^ 2 * harmonic N * L ^ 2 ≤ K_r / L ^ 2 * (2 * L) * L ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 2 * K_r * L := by field_simp
  have hsum : C_s / L ^ 2 + (4 / L ^ 2 + 162 / L ^ 2) + (32 * K₀ ^ 2 / L ^ 2 + 2048 * K₀ ^ 2 / L ^ 2) +
      C_q / L ^ 2 + 3 * (15625 * K_up / L ^ 2 + 819200 / L ^ 2 + 2 * K_r / L ^ 2) ≤ 1 / L := by
    have e : C_s / L ^ 2 + (4 / L ^ 2 + 162 / L ^ 2) + (32 * K₀ ^ 2 / L ^ 2 + 2048 * K₀ ^ 2 / L ^ 2) +
        C_q / L ^ 2 + 3 * (15625 * K_up / L ^ 2 + 819200 / L ^ 2 + 2 * K_r / L ^ 2) =
        (C_s + 4 + 162 + 32 * K₀ ^ 2 + 2048 * K₀ ^ 2 + C_q + 46875 * K_up + 2457600 + 6 * K_r) /
          L ^ 2 := by ring
    rw [e, div_le_div_iff₀ (by positivity) hL0, one_mul]
    calc (C_s + 4 + 162 + 32 * K₀ ^ 2 + 2048 * K₀ ^ 2 + C_q + 46875 * K_up + 2457600 + 6 * K_r) * L ≤
        L * L := mul_le_mul_of_nonneg_right hbig hL0.le
      _ = L ^ 2 := by ring
  have e2 : (C_p + 1) / L = C_p / L + 1 / L := by ring
  rw [e2]
  linarith only [t1, t2, t3, t4, t5, t6, t7, t8, t9, hsum]

/-- `⌈c e⌉ ≤ 4L` for `1 ≤ c ≤ L`. -/
theorem linearPrimeStrip_le_four_mul {c L : ℝ} (hc1 : 1 ≤ c) (hcL : c ≤ L) :
    (linearPrimeStrip c : ℝ) ≤ 4 * L := by
  unfold linearPrimeStrip
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h := Nat.ceil_lt_add_one (show 0 ≤ c * Real.exp 1 by positivity)
  nlinarith [Real.exp_pos 1]

/-- **The deep-row inverse-energy mass.** With `X = 2cY`, `L⁸ ≤ X`, `L¹⁸ ≤ N`, the affine shell
rate `C_sh c/(log Y)⁴` on the deep rows and `log Y ≥ √L/4`, the deep residual of every conductor
`m ≤ Q` is `≤ 8 m (1 + log m)² (C_p + 1)/L`, and
`Σ_{m ≤ Q} deepMass(r_m)/E_m ≤ 8 (C_p + 1)/L · (8c⁷ + Q²(1 + log Q)²)/κ`. -/
theorem deep_inverse_energy_mass_le {C_p C_s C_q K₀ K_up C_sh : ℝ} (hCp : 0 ≤ C_p)
    (hCs : 0 ≤ C_s) (hCq : 0 ≤ C_q) (hKup : 0 ≤ K_up)
    (hdeep : ∀ {m N : ℕ} {c X ρ : ℝ}, 0 < m → 1 ≤ N → 1 ≤ Real.log N → 1 ≤ c → c / N ≤ 1 →
      2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      2 * (linearPrimeStrip c : ℝ) + 3 ≤ X → linearNearRowRadius c < X → 2 * c < X →
      (∀ n ∈ Icc 1 N, (n : ℝ) * X ≤ N →
        |shiftedReciprocalUpwardRowError tiltedUnitSpline c id N m n| ≤ ρ / Real.sqrt n ∧
        |shiftedReciprocalUpwardRowError tiltedUnitSpline c (reflectedAffineShift m) N m n| ≤
          ρ / Real.sqrt n) →
      deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) ≤
        8 * deepResidualBudget C_p C_s C_q K₀ K_up m N c X ρ)
    {N Q : ℕ} {c X Y : ℝ}
    (hshY : ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log Y ^ (2 : ℝ) → ∀ c X' : ℝ, 1 ≤ c →
      2 * c * Y ≤ X' → ∀ shift : ℕ → ℕ, ∀ n : ℕ,
      |affinePrimeShellCorrectionOfShift q n shift tiltedUnitSpline c X' -
        ramanujanLagCoefficient q n * shellCorrectionOfShift tiltedUnitSpline c q shift| ≤
        C_sh * c / Real.log Y ^ 4)
    (hL2 : 2 ≤ Real.log N) (hc1 : 1 ≤ c) (hcL : c ≤ Real.log N) (hQL : (Q : ℝ) ≤ Real.log N)
    (hQY : (Q : ℝ) ≤ Real.log Y ^ (2 : ℝ)) (hX : Real.log N ^ 8 ≤ X)
    (hNL : Real.log N ^ 18 ≤ N) (hXY : X = 2 * c * Y)
    (hlogY : Real.log N ^ (1 / 2 : ℝ) / 4 ≤ Real.log Y)
    (hbig : C_s + 4 + 162 + 32 * K₀ ^ 2 + 2048 * K₀ ^ 2 + C_q + 46875 * K_up + 2457600 +
      6 * (65536 * C_sh ^ 2) ≤ Real.log N) :
    (∑ m ∈ Icc 1 Q,
        deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤
      8 * ((C_p + 1) / Real.log N) *
        ((8 * c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) / tiltedSplineSpectralFloorConstant) := by
  set L := Real.log (N : ℝ) with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hN1R : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ hL1) hNL
  have hN1 : 1 ≤ N := by exact_mod_cast hN1R
  have hLh : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hlogY0 : 0 < Real.log Y := lt_of_lt_of_le (by positivity) hlogY
  -- the shell rate on the deep rows
  set ρ := C_sh * c / Real.log Y ^ 4 with hρdef
  have hρ2 : ρ ^ 2 ≤ 65536 * C_sh ^ 2 / L ^ 2 := by
    have hY8 : L ^ 4 / 65536 ≤ Real.log Y ^ 8 := by
      have h1 : (L ^ (1 / 2 : ℝ) / 4) ^ 8 ≤ Real.log Y ^ 8 :=
        pow_le_pow_left₀ (by positivity) hlogY 8
      have h2 : (L ^ (1 / 2 : ℝ) / 4) ^ 8 = L ^ 4 / 65536 := by
        rw [div_pow, ← Real.rpow_natCast (L ^ (1 / 2 : ℝ)), ← Real.rpow_mul hL0.le]
        norm_num
      linarith
    rw [hρdef, div_pow, mul_pow, ← pow_mul]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hc2 : c ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hc0.le hcL 2
    have h3 : C_sh ^ 2 * c ^ 2 * L ^ 2 ≤ C_sh ^ 2 * L ^ 4 := by
      have : C_sh ^ 2 * c ^ 2 * L ^ 2 ≤ C_sh ^ 2 * L ^ 2 * L ^ 2 := by gcongr
      linarith [show C_sh ^ 2 * L ^ 2 * L ^ 2 = C_sh ^ 2 * L ^ 4 by ring]
    have h4 : C_sh ^ 2 * L ^ 4 ≤ 65536 * C_sh ^ 2 * Real.log Y ^ (4 * 2) := by
      have := mul_le_mul_of_nonneg_left hY8 (by positivity : (0 : ℝ) ≤ 65536 * C_sh ^ 2)
      rw [show 4 * 2 = 8 by norm_num]
      calc C_sh ^ 2 * L ^ 4 = 65536 * C_sh ^ 2 * (L ^ 4 / 65536) := by ring
        _ ≤ _ := this
    linarith
  have hB := linearPrimeStrip_le_four_mul hc1 hcL
  have hL8 : 128 * L ≤ L ^ 8 := by
    have h7 : (2 : ℝ) ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL2 7
    have e : L ^ 8 = L * L ^ 7 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h7 hL0.le
    norm_num at this ⊢; linarith
  have hrate : ∀ m ∈ Icc 1 Q, ∀ n ∈ Icc 1 N, (n : ℝ) * X ≤ N →
      |shiftedReciprocalUpwardRowError tiltedUnitSpline c id N m n| ≤ ρ / Real.sqrt n ∧
      |shiftedReciprocalUpwardRowError tiltedUnitSpline c (reflectedAffineShift m) N m n| ≤
        ρ / Real.sqrt n := by
    intro m hm n hn hnX
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hmY : (m : ℝ) ≤ Real.log Y ^ (2 : ℝ) :=
      le_trans (by exact_mod_cast (mem_Icc.mp hm).2) hQY
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hX' : 2 * c * Y ≤ (N : ℝ) / n := by
      rw [← hXY, le_div_iff₀ hn0, mul_comm]; exact hnX
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    constructor
    · unfold shiftedReciprocalUpwardRowError
      rw [abs_div, abs_of_pos hsq]
      exact div_le_div_of_nonneg_right (hshY m hm0 hmY c _ hc1 hX' id n) hsq.le
    · unfold shiftedReciprocalUpwardRowError
      rw [abs_div, abs_of_pos hsq]
      exact div_le_div_of_nonneg_right (hshY m hm0 hmY c _ hc1 hX' (reflectedAffineShift m) n) hsq.le
  -- the side conditions of the deep residual
  have hcN : c / N ≤ 1 := by
    rw [div_le_one (by linarith)]
    have : L ≤ L ^ 18 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 18 := pow_le_pow_right₀ hL1 (by norm_num)
    linarith
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) := by
    have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have h1 : 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ 2 * (6 * L) * (4 * L) := by
      apply mul_le_mul _ hB (Nat.cast_nonneg _) (by positivity)
      nlinarith [Real.exp_pos 1]
    have h2 : 2 * (6 * L) * (4 * L) ≤ L ^ 18 := by
      have : 48 * L ^ 2 ≤ L ^ 18 := by
        have h3 : (2 : ℝ) ^ 16 ≤ L ^ 16 := pow_le_pow_left₀ (by norm_num) hL2 16
        have : L ^ 18 = L ^ 2 * L ^ 16 := by ring
        nlinarith [sq_nonneg L]
      nlinarith
    linarith
  have hXB : 2 * (linearPrimeStrip c : ℝ) + 3 ≤ X := by linarith
  have hXR : linearNearRowRadius c < X := by
    unfold linearNearRowRadius
    have he2 : Real.exp 2 ≤ 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos 1, Real.exp_one_lt_d9]
    have h1 : 2 * c * Real.exp 2 ≤ 18 * L := by nlinarith [Real.exp_pos 2]
    linarith
  have hX2 : 2 * c < X := by linarith
  have hH : (harmonic N : ℝ) ≤ 2 * L := by
    have := harmonic_le_one_add_log' N; linarith
  have hβ := deepResidualRate_le (C_p := C_p) (K₀ := K₀) (Q := Q) (X := X) (ρ := ρ) hCs hCq hKup
    (by positivity : (0 : ℝ) ≤ 65536 * C_sh ^ 2) hL1 hc1 hcL hQL hH hB hX hNL hρ2 hbig
  refine sum_deepMass_inv_energy_le hc1 (by positivity) fun m hm => ?_
  have hm1 := (mem_Icc.mp hm).1
  have hd := hdeep (X := X) (ρ := ρ) hm1 hN1 hL1 hc1 hcN hkernel hXB hXR hX2 (hrate m hm)
  have hX0 : 0 < X := by linarith
  have hb := deepResidualBudget_le_rate (C_p := C_p) (K₀ := K₀) (ρ := ρ) (N := N) (c := c) hCs hCq
    hKup hm1 (mem_Icc.mp hm).2 hX0 hL0
  have hw : 0 ≤ (m : ℝ) * (1 + Real.log m) ^ 2 := by
    have := Real.log_natCast_nonneg m; positivity
  have := mul_le_mul_of_nonneg_left hβ hw
  linarith

/-! ### Scalar closure of the Schur step below the eighth root -/

theorem mul_le_rpow_add {L x y a b : ℝ} (hL : 0 < L) (hx : x ≤ L ^ a) (hy0 : 0 ≤ y)
    (hy : y ≤ L ^ b) : x * y ≤ L ^ (a + b) := by
  rw [Real.rpow_add hL]; exact mul_le_mul hx hy hy0 (by positivity)

theorem pow_le_rpow_mul {L x a : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hx : x ≤ L ^ a) (n : ℕ) :
    x ^ n ≤ L ^ ((n : ℝ) * a) := by
  have hp := pow_le_pow_left₀ hx0 hx n
  have e : (L ^ a) ^ n = L ^ ((n : ℝ) * a) := by
    rw [← Real.rpow_natCast (L ^ a) n, ← Real.rpow_mul hL.le, mul_comm]
  exact hp.trans_eq e

theorem schur_budget_sqrt {L K T₁ T₂ α ν : ℝ} (hL1 : 1 ≤ L) (hK : 0 ≤ K)
    (hT₁ : T₁ ≤ L ^ (9 * α + 4 * ν - 1)) (hT₂ : T₂ ≤ L ^ (4 * α + 6 * ν - 1 / 2))
    (he₁ : 9 * α + 5 * ν ≤ 3 / 2) (he₂ : 4 * α + 7 * ν ≤ 1) (hK1 : 2048 * K ≤ L ^ ν) :
    16 * (2 * K * (T₁ + T₂)) ≤ L ^ (1 / 2 : ℝ) / 32 := by
  have hL0 : 0 < L := by linarith
  have h1 : T₁ ≤ L ^ (1 / 2 - ν : ℝ) :=
    hT₁.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have h2 : T₂ ≤ L ^ (1 / 2 - ν : ℝ) :=
    hT₂.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hsplit : L ^ (1 / 2 : ℝ) = L ^ ν * L ^ (1 / 2 - ν : ℝ) := by
    rw [← Real.rpow_add hL0]; congr 1; ring
  have h0 : 0 ≤ L ^ (1 / 2 - ν : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_right hK1 h0
  have h4 : 1024 * K * (T₁ + T₂) ≤ 1024 * K * (2 * L ^ (1 / 2 - ν : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [hsplit]
  linarith

theorem schur_budget_top {L K T₁ T₂ α ν c b θ D : ℝ} (hL1 : 1 ≤ L) (hK : 0 ≤ K) (hc1 : 1 ≤ c)
    (hc7 : c ^ 7 ≤ L ^ (7 * α)) (hT₁0 : 0 ≤ T₁) (hT₂0 : 0 ≤ T₂)
    (hT₁ : T₁ ≤ L ^ (9 * α + 4 * ν - 1)) (hT₂ : T₂ ≤ L ^ (4 * α + 6 * ν - 1 / 2))
    (he₁ : 16 * α + 5 * ν ≤ 2) (he₂ : 11 * α + 7 * ν ≤ 3 / 2) (hb : 0 < b) (hθ : 0 < θ) (hD : 0 < D)
    (hX : 2048 * D * K / (3 * b * θ) ≤ L ^ ν) :
    16 * (2 * K * (T₁ + T₂)) ≤ 3 * b * (θ * L / (2 * D)) / (16 * c ^ 7) := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have h1 : c ^ 7 * T₁ ≤ L ^ (1 - ν) :=
    (mul_le_rpow_add hL0 hc7 hT₁0 hT₁).trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have h2 : c ^ 7 * T₂ ≤ L ^ (1 - ν) :=
    (mul_le_rpow_add hL0 hc7 hT₂0 hT₂).trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hsplit : L = L ^ ν * L ^ (1 - ν) := by
    rw [← Real.rpow_add hL0, show ν + (1 - ν) = 1 by ring, Real.rpow_one]
  rw [le_div_iff₀ (by positivity)]
  have h3 : 16 * (2 * K * (T₁ + T₂)) * (16 * c ^ 7) = (512 * K) * (c ^ 7 * T₁ + c ^ 7 * T₂) := by ring
  have h4 : 3 * b * (θ * L / (2 * D)) = (3 * b * θ / (2 * D)) * L := by ring
  rw [h3, h4]
  have h5 : (512 * K) * (c ^ 7 * T₁ + c ^ 7 * T₂) ≤ (512 * K) * (2 * L ^ (1 - ν)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h6 : (512 * K) * (2 * L ^ (1 - ν)) =
      (3 * b * θ / (2 * D)) * (2048 * D * K / (3 * b * θ)) * L ^ (1 - ν) := by field_simp; ring
  have h7 : (3 * b * θ / (2 * D)) * (2048 * D * K / (3 * b * θ)) * L ^ (1 - ν) ≤
      (3 * b * θ / (2 * D)) * L ^ ν * L ^ (1 - ν) := by
    have := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 3 * b * θ / (2 * D))
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h8 : (3 * b * θ / (2 * D)) * L ^ ν * L ^ (1 - ν) = (3 * b * θ / (2 * D)) * L := by
    rw [mul_assoc, ← hsplit]
  linarith

theorem schur_budget_rows {L K T₁ T₂ α ν R₀ : ℝ} (hL1 : 1 ≤ L) (hK : 0 ≤ K) (hT₁0 : 0 ≤ T₁)
    (hT₂0 : 0 ≤ T₂) (hT₁ : T₁ ≤ L ^ (9 * α + 4 * ν - 1)) (hT₂ : T₂ ≤ L ^ (4 * α + 6 * ν - 1 / 2))
    (he₁ : 9 * α + 5 * ν ≤ 3 / 2) (he₂ : 4 * α + 7 * ν ≤ 1) (hR₀1 : 1 ≤ R₀)
    (hR₀ : 1 + Real.log R₀ ≤ 2 * L ^ (1 / 2 : ℝ)) (hK1 : 5120 * K ≤ L ^ ν) :
    32 * (2 * K * (T₁ + T₂)) * (2 * (Real.log (2 * R₀) + 3) / L) ≤ 1 / 2 := by
  have hL0 : 0 < L := by linarith
  have hl2 : Real.log (2 * R₀) = Real.log 2 + Real.log R₀ := Real.log_mul (by norm_num) (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hLh1 : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hnum : 2 * (Real.log (2 * R₀) + 3) ≤ 10 * L ^ (1 / 2 : ℝ) := by rw [hl2]; linarith
  have hT : (T₁ + T₂) * L ^ (1 / 2 : ℝ) ≤ 2 * L ^ (1 - ν) := by
    have h1 : T₁ * L ^ (1 / 2 : ℝ) ≤ L ^ (1 - ν) :=
      (mul_le_rpow_add hL0 hT₁ (by positivity) le_rfl).trans
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    have h2 : T₂ * L ^ (1 / 2 : ℝ) ≤ L ^ (1 - ν) :=
      (mul_le_rpow_add hL0 hT₂ (by positivity) le_rfl).trans
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    linarith
  have hsplit : L = L ^ ν * L ^ (1 - ν) := by
    rw [← Real.rpow_add hL0, show ν + (1 - ν) = 1 by ring, Real.rpow_one]
  have h3 : 32 * (2 * K * (T₁ + T₂)) * (2 * (Real.log (2 * R₀) + 3) / L) ≤
      32 * (2 * K * (T₁ + T₂)) * (10 * L ^ (1 / 2 : ℝ) / L) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hL0.le) (by positivity)
  have h4 : 32 * (2 * K * (T₁ + T₂)) * (10 * L ^ (1 / 2 : ℝ) / L) =
      640 * K * ((T₁ + T₂) * L ^ (1 / 2 : ℝ)) / L := by ring
  have h5 : 640 * K * ((T₁ + T₂) * L ^ (1 / 2 : ℝ)) ≤ 640 * K * (2 * L ^ (1 - ν)) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have h6 : 640 * K * (2 * L ^ (1 - ν)) ≤ L / 2 := by
    have h := mul_le_mul_of_nonneg_right hK1 (by positivity : (0 : ℝ) ≤ L ^ (1 - ν))
    rw [← hsplit] at h
    linarith
  rw [h4] at h3
  have h7 : 640 * K * ((T₁ + T₂) * L ^ (1 / 2 : ℝ)) / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]; linarith
  linarith

theorem schur_budget_deep {L c Q C_p κ α ν : ℝ} (hL1 : 1 ≤ L) (hCp : 0 ≤ C_p) (hκ : 0 < κ)
    (hc7 : c ^ 7 ≤ L ^ (7 * α)) (hQ2 : Q ^ 2 * (1 + Real.log Q) ^ 2 ≤
      L ^ (2 * (α + 1 / 4) + 2 * ν)) (he₁ : 7 * α + ν ≤ 1) (he₂ : 2 * α + 3 * ν ≤ 1 / 2)
    (hX : 9216 * (C_p + 1) / κ ≤ L ^ ν) :
    32 * (8 * ((C_p + 1) / L) * ((8 * c ^ 7 + Q ^ 2 * (1 + Real.log Q) ^ 2) / κ)) ≤ 1 / 2 := by
  have hL0 : 0 < L := by linarith
  have hLmν0 : 0 ≤ L ^ (-ν) := by positivity
  have hmul : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have h1 : c ^ 7 / L ≤ L ^ (-ν) := by
    rw [div_le_iff₀ hL0]
    calc c ^ 7 ≤ L ^ (7 * α) := hc7
      _ ≤ L ^ (-ν + 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L ^ (-ν) * L := Real.rpow_add_one hL0.ne' _
  have h2 : Q ^ 2 * (1 + Real.log Q) ^ 2 / L ≤ L ^ (-ν) := by
    rw [div_le_iff₀ hL0]
    calc Q ^ 2 * (1 + Real.log Q) ^ 2 ≤ L ^ (2 * (α + 1 / 4) + 2 * ν) := hQ2
      _ ≤ L ^ (-ν + 1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L ^ (-ν) * L := Real.rpow_add_one hL0.ne' _
  have e : 32 * (8 * ((C_p + 1) / L) * ((8 * c ^ 7 + Q ^ 2 * (1 + Real.log Q) ^ 2) / κ)) =
      256 * (C_p + 1) / κ * (8 * (c ^ 7 / L) + Q ^ 2 * (1 + Real.log Q) ^ 2 / L) := by
    field_simp; ring
  rw [e]
  have h3 : 256 * (C_p + 1) / κ * (8 * (c ^ 7 / L) + Q ^ 2 * (1 + Real.log Q) ^ 2 / L) ≤
      256 * (C_p + 1) / κ * (9 * L ^ (-ν)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : 256 * (C_p + 1) / κ * (9 * L ^ (-ν)) = (9216 * (C_p + 1) / κ) * L ^ (-ν) / 4 := by ring
  have h5 := mul_le_mul_of_nonneg_right hX hLmν0
  linarith

/-- **The Schur budgets below the eighth root.** With `ν = (1 − 8α)/64`, `Q ≤ L^{α+1/4}` and
`Ψ = 2K (c⁷ + Q²(1 + log Q)²) c²(1 + log c)³ L^ν / L`: `16Ψ ≤ √L/32`, `16Ψ ≤ 3bk/(16c⁷)`
(`k = θL/(2D)`) and `32Ψ ρ_top + 32Ψ_D ≤ 1` for `ρ_top = 2(log 2R₀ + 3)/L`, `1 + log R₀ ≤ 2√L`,
`Ψ_D = 8(C_p + 1)/L · (8c⁷ + Q²(1 + log Q)²)/κ`. -/
theorem schur_scalars_one_eighth {α ν L c Q R₀ K C_p κ b θ D : ℝ}
    (hα : 0 < α) (hν : 0 < ν) (hν8 : 64 * ν ≤ 1 - 8 * α) (hL1 : 1 ≤ L) (hc1 : 1 ≤ c)
    (hcup : c ≤ L ^ α) (hlc : 1 + Real.log c ≤ L ^ ν) (hQ1 : 1 ≤ Q) (hQ : Q ≤ L ^ (α + 1 / 4))
    (hlQ : 1 + Real.log Q ≤ L ^ ν) (hR₀1 : 1 ≤ R₀) (hR₀ : 1 + Real.log R₀ ≤ 2 * L ^ (1 / 2 : ℝ))
    (hK : 0 ≤ K) (hCp : 0 ≤ C_p) (hκ : 0 < κ) (hb : 0 < b) (hθ : 0 < θ) (hD : 0 < D)
    (hbig : 5120 * K + 2048 * D * K / (3 * b * θ) + 9216 * (C_p + 1) / κ ≤ L ^ ν) :
    16 * (2 * (K * (c ^ 7 + Q ^ 2 * (1 + Real.log Q) ^ 2)) *
        (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L)) ≤ L ^ (1 / 2 : ℝ) / 32 ∧
    16 * (2 * (K * (c ^ 7 + Q ^ 2 * (1 + Real.log Q) ^ 2)) *
        (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L)) ≤ 3 * b * (θ * L / (2 * D)) / (16 * c ^ 7) ∧
    32 * (2 * (K * (c ^ 7 + Q ^ 2 * (1 + Real.log Q) ^ 2)) *
        (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L)) * (2 * (Real.log (2 * R₀) + 3) / L) +
      32 * (8 * ((C_p + 1) / L) * ((8 * c ^ 7 + Q ^ 2 * (1 + Real.log Q) ^ 2) / κ)) ≤ 1 := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hlc0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hlQ0 : 0 ≤ 1 + Real.log Q := by linarith [Real.log_nonneg hQ1]
  have hc7 : c ^ 7 ≤ L ^ (7 * α) := by
    have := pow_le_rpow_mul hL0 hc0.le hcup 7; push_cast at this; exact this
  have hc2 : c ^ 2 ≤ L ^ (2 * α) := by
    have := pow_le_rpow_mul hL0 hc0.le hcup 2; push_cast at this; exact this
  have hlc3 : (1 + Real.log c) ^ 3 ≤ L ^ (3 * ν) := by
    have := pow_le_rpow_mul hL0 hlc0 hlc 3; push_cast at this; exact this
  have hQ2' : Q ^ 2 ≤ L ^ (2 * (α + 1 / 4)) := by
    have := pow_le_rpow_mul hL0 (by linarith) hQ 2; push_cast at this; exact this
  have hlQ2 : (1 + Real.log Q) ^ 2 ≤ L ^ (2 * ν) := by
    have := pow_le_rpow_mul hL0 hlQ0 hlQ 2; push_cast at this; exact this
  have hQ2 : Q ^ 2 * (1 + Real.log Q) ^ 2 ≤ L ^ (2 * (α + 1 / 4) + 2 * ν) :=
    mul_le_rpow_add hL0 hQ2' (by positivity) hlQ2
  have hr : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L ≤ L ^ (2 * α + 4 * ν - 1) := by
    have h1 := mul_le_rpow_add hL0 (mul_le_rpow_add hL0 hc2 (by positivity) hlc3)
      (by positivity : (0 : ℝ) ≤ L ^ ν) (le_refl (L ^ ν))
    rw [div_le_iff₀ hL0]
    calc c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν ≤ L ^ (2 * α + 3 * ν + ν) := h1
      _ = L ^ (2 * α + 4 * ν - 1) * L := by
          rw [← Real.rpow_add_one hL0.ne']; congr 1; ring
  have hr0 : 0 ≤ c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L := by positivity
  generalize hrdef : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L = r at hr hr0 ⊢
  have hT1 : c ^ 7 * r ≤ L ^ (9 * α + 4 * ν - 1) :=
    (mul_le_rpow_add hL0 hc7 hr0 hr).trans_eq (by congr 1; ring)
  have hT2 : Q ^ 2 * (1 + Real.log Q) ^ 2 * r ≤ L ^ (4 * α + 6 * ν - 1 / 2) :=
    (mul_le_rpow_add hL0 hQ2 hr0 hr).trans_eq (by congr 1; ring)
  have hΨe : 2 * (K * (c ^ 7 + Q ^ 2 * (1 + Real.log Q) ^ 2)) * r =
      2 * K * (c ^ 7 * r + Q ^ 2 * (1 + Real.log Q) ^ 2 * r) := by ring
  rw [hΨe]
  have hT10 : 0 ≤ c ^ 7 * r := by positivity
  have hT20 : 0 ≤ Q ^ 2 * (1 + Real.log Q) ^ 2 * r := by positivity
  have hp1 : 0 ≤ 2048 * D * K / (3 * b * θ) := by positivity
  have hp2 : 0 ≤ 9216 * (C_p + 1) / κ := by positivity
  have hK1 : 5120 * K ≤ L ^ ν := by linarith
  refine ⟨schur_budget_sqrt hL1 hK hT1 hT2 (by linarith) (by linarith) (by linarith),
    schur_budget_top hL1 hK hc1 hc7 hT10 hT20 hT1 hT2 (by linarith) (by linarith) hb hθ hD
      (by linarith), ?_⟩
  have h1 := schur_budget_rows hL1 hK hT10 hT20 hT1 hT2 (by linarith) (by linarith) hR₀1 hR₀ hK1
  have h2 := schur_budget_deep hL1 hCp hκ hc7 hQ2 (by linarith) (by linarith) (by linarith)
  linarith

/-! ### The deep-row cutoff -/

/-- **The deep-row cutoff `X = R₀ = ⌊exp √L⌋`.** With `16(1 + log L) ≤ √L`: `R₀ ≥ L⁸`, the shell
scale `Y = R₀/(2c)` has `log Y ≥ √L/4`, exceeds any fixed `Y₀ ≤ L/2`, and every conductor
`Q ≤ √L` is at most `(log Y)²`. -/
theorem deep_cutoff_facts {L c R₀ Y₀ Q : ℝ} (hL256 : 256 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L)
    (h16 : 16 * (1 + Real.log L) ≤ L ^ (1 / 2 : ℝ)) (hR₀1 : 1 ≤ R₀)
    (hlogR₀ : L ^ (1 / 2 : ℝ) - 1 ≤ Real.log R₀) (hY₀ : 2 * Y₀ ≤ L)
    (hQ : Q ≤ L ^ (1 / 2 : ℝ)) :
    L ^ 8 ≤ R₀ ∧ L ^ (1 / 2 : ℝ) / 4 ≤ Real.log (R₀ / (2 * c)) ∧ Y₀ ≤ R₀ / (2 * c) ∧
      Q ≤ Real.log (R₀ / (2 * c)) ^ (2 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hc0 : 0 < c := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hLh_sq : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
    rw [← Real.rpow_add hL0]; norm_num
  have hLh0 : 0 < L ^ (1 / 2 : ℝ) := by positivity
  have hLh16 : 16 ≤ L ^ (1 / 2 : ℝ) := by nlinarith
  have hR₀L8 : L ^ 8 ≤ R₀ := by
    have h1 : Real.log (L ^ 8) ≤ Real.log R₀ := by
      rw [Real.log_pow]; push_cast; linarith
    exact (Real.log_le_log_iff (by positivity) (by linarith)).mp h1
  have hlog2c : Real.log (2 * c) ≤ 1 + Real.log L := by
    rw [Real.log_mul (by norm_num) hc0.ne']
    have h1 := Real.log_le_log hc0 hcL
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hR₀0 : 0 < R₀ := by linarith
  have hlogY : L ^ (1 / 2 : ℝ) / 4 ≤ Real.log (R₀ / (2 * c)) := by
    rw [Real.log_div hR₀0.ne' (by positivity)]
    linarith
  refine ⟨hR₀L8, hlogY, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have hL7 : L ≤ L ^ 7 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 7 := pow_le_pow_right₀ hL1 (by norm_num)
    have h8 : L ^ 8 = L * L ^ 7 := by ring
    nlinarith
  · rw [Real.rpow_two]
    have h1 : (L ^ (1 / 2 : ℝ) / 4) ^ 2 ≤ Real.log (R₀ / (2 * c)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlogY 2
    have h2 : (L ^ (1 / 2 : ℝ) / 4) ^ 2 = L / 16 := by rw [div_pow, sq, hLh_sq]; ring
    have h3 : L ^ (1 / 2 : ℝ) ≤ L / 16 := by nlinarith
    linarith

/-! ### Positive definiteness below the eighth root -/

/-- **Positive definiteness from block reserves.** If the conductor block `V_{Q₁}` has the
polylogarithmic floor, the complement has block reserves `μ₀, μ₁, μ_S` on the three-band split,
the top rows of `V_{R₀}` carry at most `ρ_top` of the mass, and the residual masses `Ψ`, `Ψ_D`
fit the reserves, then `spectralFloorWeilMatrix c N` is positive definite. -/
theorem spectralFloor_posDef_of_blocks {Q₁ R₀ R₁ N : ℕ} {c X Ψ Ψ_D ρ_top μ₀ μ₁ μ_S : ℝ}
    (hc1 : 1 ≤ c) (hQR₀ : Q₁ ≤ R₀) (hR₀R₁ : R₀ ≤ R₁)
    (hlow : ∀ a : ℕ → ℝ,
      (1 / 4 : ℝ) * (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
        ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
            (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N⟫)
    (hcomp : ∀ {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      u₀ ∈ conductorSubspace R₀ N → u₀ ∈ (conductorSubspace Q₁ N)ᗮ →
      u₁ ∈ conductorSubspace R₁ N → u₁ ∈ (conductorSubspace R₀ N)ᗮ →
      w ∈ (conductorSubspace R₁ N)ᗮ →
      (tiltedSplineSpectralFloorConstant + 2 + μ₀) * ‖u₀‖ ^ 2 +
          (tiltedSplineSpectralFloorConstant + 2 + μ₁) * ‖u₁‖ ^ 2 +
          (tiltedSplineSpectralFloorConstant + 2 + μ_S) * ‖w‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w))
    (htop : ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace R₀ N →
      (∑ n ∈ topRows N X, primeHorizonExtension u n ^ 2) ≤ ρ_top * ‖u‖ ^ 2)
    (hΨ : (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m) ≤ Ψ)
    (hΨD : (∑ m ∈ Icc 1 Q₁,
        deepMass X (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) /
          completedConductorEnergy tiltedUnitSpline c m) ≤ Ψ_D)
    (hμ₀ : 32 * Ψ * ρ_top + 32 * Ψ_D ≤ μ₀) (hμ₁ : 16 * Ψ ≤ μ₁) (hμS : 16 * Ψ ≤ μ_S) :
    (spectralFloorWeilMatrix c N).PosDef := by
  refine posDef_of_inner_pos_on_ne_zero (spectralFloorWeilMatrix_isHermitian c N) fun x hx_ne => ?_
  have hy_mem : (conductorSubspace Q₁ N).starProjection x ∈ conductorSubspace Q₁ N :=
    (conductorSubspace Q₁ N).starProjection_apply_mem x
  have hz_orth : x - (conductorSubspace Q₁ N).starProjection x ∈ (conductorSubspace Q₁ N)ᗮ :=
    sub_starProjection_mem_orthogonal_telescoped _ x
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (M := Q₁) (N := N)
    (x := (conductorSubspace Q₁ N).starProjection x)).mp hy_mem
  obtain ⟨u₀, u₁, w, hz_eq, hu₀_mem, hu₀_orthQ, hu₁_mem, hu₁_orthR₀, hw_orthR₁, hnorm⟩ :=
    telescoped_three_band_orthogonal_split hQR₀ hR₀R₁ hz_orth
  have hx_eq : x = (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + (u₀ + u₁ + w) := by
    rw [← hz_eq, ha]; abel
  have hu₁w : ‖u₁ + w‖ ^ 2 = ‖u₁‖ ^ 2 + ‖w‖ ^ 2 := by
    have h0 : ⟪u₁, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu₁_mem hw_orthR₁
    rw [norm_add_sq_real, h0]; ring
  rw [hz_eq] at hz_orth hnorm
  rw [hx_eq]
  exact schur_with_deep_pairing_pos hc1 a hz_orth hnorm hu₁w (hlow a)
    (hcomp hu₀_mem hu₀_orthQ hu₁_mem hu₁_orthR₀ hw_orthR₁) (htop hu₀_mem) hΨ hΨD hμ₀ hμ₁ hμS
    (hx_eq ▸ hx_ne)

/-- `(R² + 1) R ≤ N` from `R⁶ ≤ N`, `R ≥ 2`. -/
theorem sq_add_one_mul_le_of_pow_six_le {R N : ℕ} (hR : 2 ≤ R) (h6 : R ^ 6 ≤ N) :
    ((R * R : ℕ) + 1 : ℝ) * (R : ℝ) ≤ N := by
  have hR6 : (R : ℝ) ^ 6 ≤ N := by exact_mod_cast h6
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
  push_cast
  generalize (R : ℝ) = x at hR6 hR2 ⊢
  have hx1 : 1 ≤ x := by linarith only [hR2]
  have h3 : (2 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hR2 3
  have hxx3 : x ≤ x ^ 3 := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 3 := pow_le_pow_right₀ hx1 (by norm_num)
  have e1 : (x * x + 1) * x = x ^ 3 + x := by ring
  have e2 : x ^ 6 = x ^ 3 * x ^ 3 := by ring
  have h4 : 2 * x ^ 3 ≤ x ^ 3 * x ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_num at h3; linarith only [h3]) (by positivity)
  rw [e1]
  linarith only [hxx3, h4, e2, hR6]


end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
