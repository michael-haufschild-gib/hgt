import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ThePolynomialConductorComplementIsCoerciveBelowTheEighthRoot
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheBandFarCrossBelowTheEighthRoot

/-!
# The eighth-root complement keeps its block reserves

On `(conductorSubspace Q₁ N)ᗮ`, split `z = u₀ + u₁ + w` with `u₀ ∈ V_{R₀} ∩ V_{Q₁}^⊥`,
`u₁ ∈ V_{R₁} ∩ V_{R₀}^⊥`, `w ∈ V_{R₁}^⊥` (`Q₁ = ⌊L^{α+1/4}⌋`, `R₀ = ⌊exp √L⌋`, `R₁ = ⌊N^{θ₁}⌋`,
`L = log N`). Below `1/8` the complete Weil energy keeps a separate reserve on every block:

`(κ₀ + 3)‖u₀‖² + (κ₀ + 2 + √L/32)‖u₁‖² + (κ₀ + 2 + 3bk/(16c⁷))‖w‖² ≤ E(z)`, `k = θ₁ L/(2D)`.

* `complement_three_band_reserve_assembly`: the three-band assembly with block floors `K₀, K₁, K₂`.
* `exists_band_far_cross_le_reserve_shape`: the channel form of the band–far cross
  (`exists_band_far_cross_le_channels`) at `s = k/128`, `t = bk/(128c⁷)`, `γ = bk/(32c⁷)`, with
  `Σ a² ≤ 2‖u‖²` and `Σ (1 + log m) a² ≤ Σ a² + E`; `budgetE_le`, `budgetU_le` verify its two
  scalar budgets from the monomial bounds `c⁸ (1 + log c) Sg²/L ≤ σ`, `c¹¹ (1 + log c)³ Sg Λ/L² ≤ σ`
  (`8α + 4ν ≤ 1`, the eighth-root condition).
* `two_region_reserve_assembly_shape`: the two-region reserve below `1/8` on `V_{R₁}^⊥`
  (`eventually_completeWeilEnergy_two_region_on_polynomialConductorOrthogonal_below_one_eighth`).
* `exists_complement_block_reserves_below_one_eighth`: the eventual statement.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- **Three-band complement coercivity with block reserves.** For `u₀ ∈ V_{R₀} ∩ V_{Q₁}^⊥`,
`u₁ ∈ V_{R₁} ∩ V_{R₀}^⊥` and `w ∈ V_{R₁}^⊥`, the block coercivities, the two-region reserve on `w`
and the three cross payments leave every block its own floor: `K₀` on `u₀`, `K₁` on `u₁` and
`K₂` on `w`. -/
theorem complement_three_band_reserve_assembly
    {Q₁ R₀ R₁ N : ℕ} {c b k₁ Lh K₀ K₁ K₂ C_coerc0 C_band1 : ℝ}
    (hQ2 : 2 ≤ Q₁) (hQR₀ : Q₁ ≤ R₀)
    (hc1 : 1 ≤ c) (hb : 0 < b) (hb8 : b ≤ 1 / 8) (hk₁_pos : 0 < k₁)
    (hband0 : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace Q₁ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₀ a₀ +
        ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) *
          ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N))
    (hband1 : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace R₀ N)ᗮ →
      (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
        ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) *
          ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N))
    (hband2 : ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      w ∈ (conductorSubspace R₁ N)ᗮ →
      (k₁ / 4) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (b * k₁ / (2 * c ^ 7)) *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
        completeWeilEnergy tiltedUnitSpline c N w)
    (hcr01_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {u₁ : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u₁ ∈ (conductorSubspace R₀ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), u₁⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2)
    (hcr0w_fn : ∀ a₀ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k₁ / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hcr1w_fn : ∀ a₁ : ℕ → ℝ,
      (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
        (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N), w⟫| ≤
        (1 / 32 : ℝ) * primeAdjunctionMass R₁ a₁ +
          (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          (k₁ / 32) * (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) *
            (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2)
    (hfl0 : K₀ + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0)
    (hfl1 : K₁ + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c))
    (hfl2_P : K₂ ≤ k₁ / 8) (hfl2_S : K₂ ≤ 3 * b * k₁ / (8 * c ^ 7))
    {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu₀_mem : u₀ ∈ conductorSubspace R₀ N) (hu₀_orthQ : u₀ ∈ (conductorSubspace Q₁ N)ᗮ)
    (hu₁_mem : u₁ ∈ conductorSubspace R₁ N) (hu₁_orthR₀ : u₁ ∈ (conductorSubspace R₀ N)ᗮ)
    (hw_orthR₁ : w ∈ (conductorSubspace R₁ N)ᗮ) :
    K₀ * ‖u₀‖ ^ 2 + K₁ * ‖u₁‖ ^ 2 + K₂ * ‖w‖ ^ 2 ≤
      completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  obtain ⟨a₀, -, ha₀⟩ := (mem_conductorSubspace_iff (M := R₀) (N := N) (x := u₀)).mp hu₀_mem
  obtain ⟨a₁, -, ha₁⟩ := (mem_conductorSubspace_iff (M := R₁) (N := N) (x := u₁)).mp hu₁_mem
  have hu₀_1 : u₀ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₀_orthQ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hQ2) N hv)
  have hu₁_1 : u₁ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₁_orthR₀ v (conductorSubspace_mono ((by norm_num : 1 ≤ 2).trans hR₀2) N hv)
  have hdiag0 := hband0 a₀ (ha₀.symm ▸ hu₀_orthQ)
  rw [← ha₀] at hdiag0
  have hdiag1 := hband1 a₁ (ha₁.symm ▸ hu₁_orthR₀)
  rw [← ha₁] at hdiag1
  have hdiag2 := hband2 hw_orthR₁
  have hcr01 := hcr01_fn a₀ (ha₀.symm ▸ hu₀_1) hu₁_orthR₀
  rw [← ha₀] at hcr01
  have hcr0w := hcr0w_fn a₀ (ha₀.symm ▸ hu₀_1) hw_orthR₁
  rw [← ha₀] at hcr0w
  have hcr1w := hcr1w_fn a₁ (ha₁.symm ▸ hu₁_1) hw_orthR₁
  rw [← ha₁] at hcr1w
  have hPw0 : 0 ≤ ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hSw0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hw_split : ‖w‖ ^ 2 =
      (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) := by
    rw [← sum_primeHorizonExtension_sq w,
      Ioc_eq_Icc_sdiff_Icc_telescoped (N / linearDefectCutoff c) N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl (Nat.div_le_self N _))).symm
  generalize (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) = P_w at hdiag2 hcr0w hcr1w hPw0 hw_split
  generalize (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) = S_w at hdiag2 hcr0w hcr1w hSw0 hw_split
  have hfloor0 : K₀ * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 ≤
      ((3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0) * ‖u₀‖ ^ 2 := by
    rw [show K₀ * ‖u₀‖ ^ 2 + (1 / 2 : ℝ) * ‖u₀‖ ^ 2 = (K₀ + 1 / 2) * ‖u₀‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl0 (sq_nonneg ‖u₀‖)
  have hfloor1 : K₁ * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 + (1 / 4 : ℝ) * ‖u₁‖ ^ 2 ≤
      ((1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 := by
    rw [show K₁ * ‖u₁‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 + (1 / 4 : ℝ) * ‖u₁‖ ^ 2 =
      (K₁ + (1 / 16 : ℝ) * Lh + 1 / 4) * ‖u₁‖ ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right hfl1 (sq_nonneg ‖u₁‖)
  have hfloor2 : K₂ * ‖w‖ ^ 2 ≤
      (k₁ / 4) * P_w + (b * k₁ / (2 * c ^ 7)) * S_w -
        2 * ((k₁ / 32) * P_w + (b * k₁ / (32 * c ^ 7)) * S_w +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2) := by
    rw [hw_split]
    have hb_c7 : b / c ^ 7 ≤ 1 / 8 :=
      (div_le_self hb.le (one_le_pow₀ hc1)).trans hb8
    have hP_net : (k₁ / 8) * P_w ≤
        (k₁ / 4 - 2 * (k₁ / 32) - 2 * (b * k₁ / (32 * c ^ 7))) * P_w := by
      apply mul_le_mul_of_nonneg_right _ hPw0
      have hh : b * k₁ / (32 * c ^ 7) ≤ k₁ / 256 := by
        have hm := mul_le_mul_of_nonneg_right hb_c7 (div_nonneg hk₁_pos.le (by norm_num : (0 : ℝ) ≤ 32))
        exact (by field_simp [hc0.ne'] : b * k₁ / (32 * c ^ 7) = (b / c ^ 7) * (k₁ / 32)).trans_le
          (hm.trans_eq (by ring))
      linarith only [hh, hk₁_pos]
    have hP_k : K₂ * P_w ≤ (k₁ / 8) * P_w := mul_le_mul_of_nonneg_right hfl2_P hPw0
    have hS_k : K₂ * S_w ≤ (3 * b * k₁ / (8 * c ^ 7)) * S_w :=
      mul_le_mul_of_nonneg_right hfl2_S hSw0
    have hident :
        (k₁ / 4) * P_w + (b * k₁ / (2 * c ^ 7)) * S_w -
          2 * ((k₁ / 32) * P_w + (b * k₁ / (32 * c ^ 7)) * S_w +
            (b * k₁ / (32 * c ^ 7)) * (P_w + S_w)) =
        (k₁ / 4 - 2 * (k₁ / 32) - 2 * (b * k₁ / (32 * c ^ 7))) * P_w +
          (3 * b * k₁ / (8 * c ^ 7)) * S_w := by
      field_simp [hc0.ne']; ring
    rw [hident, mul_add]
    linarith only [hP_net, hP_k, hS_k]
  have h3add := completeWeilEnergy_three_add_ge tiltedUnitSpline c u₀ u₁ w
  have hE₀_0 : 0 ≤ primeAdjunctionMass R₀ a₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hE₁_0 : 0 ≤ primeAdjunctionMass R₁ a₁ := primeAdjunctionMass_nonneg R₁ a₁
  linarith only [h3add, hdiag0, hdiag1, hdiag2, hcr01, hcr0w, hcr1w,
    hfloor0, hfloor1, hfloor2, hE₀_0, hE₁_0]

/-! ### The band–far cross in the assembly shape -/

/-- The per-unit-`‖u‖²` part of `bandFarChannelBudget`. -/
def bandFarBudgetU (R N : ℕ) (c ρ Sg₁ : ℝ) : ℝ :=
  ((1 + Real.log R) / Real.log N) ^ 2 * ρ +
    c ^ 2 * (24 + 780 * Sg₁ + 72 * (R : ℝ) ^ 15 / N) / Real.log N +
    c ^ 4 * (1 + Real.log c) / Real.log N + c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)

/-- The per-unit-`Σ (1 + log m) a_m²` part of `bandFarChannelBudget`. -/
def bandFarBudgetG (R N : ℕ) (c Sg₁ : ℝ) : ℝ :=
  (1 + Real.log R) * (1 + Real.log c) / Real.log N +
    c * (Sg₁ ^ 2 * (1 + Real.log c) / Real.log N + c ^ 5 / N +
      c ^ 3 * (R : ℝ) ^ 4 / (N * Real.log N)) * (1 + Real.log R)

/-- The per-unit-`Σ a_m²` part of `bandFarChannelBudget`. -/
def bandFarBudgetA (R N : ℕ) (c : ℝ) : ℝ := c ^ 2 * (R : ℝ) ^ 5 / ((N : ℝ) ^ 2 * Real.log N)

theorem bandFarChannelBudget_eq (R N : ℕ) (c ρ Sg₁ A G U : ℝ) :
    bandFarChannelBudget R N c ρ Sg₁ A G U =
      bandFarBudgetU R N c ρ Sg₁ * U + bandFarBudgetG R N c Sg₁ * G + bandFarBudgetA R N c * A := by
  unfold bandFarChannelBudget bandFarBudgetU bandFarBudgetG bandFarBudgetA; ring

theorem tameDifferent_nonneg' (m : ℕ) : 0 ≤ ArithmeticIntersectionTheory.tameDifferent m :=
  sum_nonneg fun p hp => div_nonneg (Real.log_natCast_nonneg p)
    (by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      have : (2 : ℝ) ≤ p := by exact_mod_cast this
      linarith)

/-- `Σ (1 + log m) a_m² ≤ Σ a_m² + primeAdjunctionMass`. -/
theorem sum_one_add_log_mul_sq_le (R : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) ≤
      (∑ m ∈ Icc 1 R, a m ^ 2) + primeAdjunctionMass R a := by
  unfold primeAdjunctionMass
  rw [← sum_add_distrib]
  exact sum_le_sum fun m _ => by
    have := tameDifferent_nonneg' m
    nlinarith [sq_nonneg (a m)]

/-- `Σ a_m² ≤ 2 ‖u‖²` for a band with `18 (1 + log R) ≤ log N`. -/
theorem sum_sq_le_two_norm_sq {R N : ℕ} (hR : 2 ≤ R) (hRR : R * R ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 R, a m ^ 2) ≤
      2 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have h := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hR hRR a
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  have hA : 0 ≤ ∑ m ∈ Icc 1 R, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hc : 9 * (1 + Real.log R) / Real.log N ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]; linarith
  have h2 := mul_le_mul_of_nonneg_right hc hA
  have h3 := (abs_le.mp h).1
  linarith

theorem band_far_shape_arith {A G E U P S W a1 e1 a2 e2 g βU βG βA u v k b c7 : ℝ}
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hAU : A ≤ 2 * U) (hGE : G ≤ A + E)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hg : 0 ≤ g) (hβG : 0 ≤ βG) (hβA : 0 ≤ βA)
    (hsE : e1 + e2 + g * βG ≤ 1 / 32)
    (hsU : 2 * a1 + 2 * a2 + g * (βU + 2 * βG + 2 * βA) + u + v ≤ 1 / 4)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hk : 0 < k) (hbc : 0 ≤ b * k / c7) :
    (a1 * A + e1 * E + (a2 * A + e2 * E) + k / 128 * P + b * k / (128 * c7) * S) +
        g * (βU * U + βG * G + βA * A) + b * k / (32 * c7) * W +
        (u * U + k / 128 * P) + (v * U + b * k / (128 * c7) * S) ≤
      1 / 32 * E + 1 / 4 * U + k / 32 * P + b * k / (32 * c7) * S + b * k / (32 * c7) * W := by
  have hG2 : g * βG * G ≤ g * βG * (2 * U + E) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hg hβG)
  have hA2 : (a1 + a2 + g * βA) * A ≤ (a1 + a2 + g * βA) * (2 * U) :=
    mul_le_mul_of_nonneg_left hAU (by positivity)
  have hU0 : 0 ≤ U := by linarith
  have h1 := mul_le_mul_of_nonneg_right hsE hE
  have h2 := mul_le_mul_of_nonneg_right hsU hU0
  have hPk : 0 ≤ k * P := mul_nonneg hk.le hP
  have hSk : 0 ≤ b * k / c7 * S := mul_nonneg hbc hS
  have e1' : b * k / (128 * c7) * S = (1 / 128) * (b * k / c7 * S) := by ring
  have e2' : b * k / (32 * c7) * S = (1 / 32) * (b * k / c7 * S) := by ring
  rw [e1', e2']
  nlinarith

/-- **The band–far cross in the shape of the three-band assembly.** With the free parameters
`s = k/128`, `t = bk/(128c⁷)`, `γ = bk/(32c⁷)` in `exists_band_far_cross_le_channels`, and
`Σ a² ≤ 2‖u‖²`, `Σ (1 + log m) a² ≤ Σ a² + E`, the cross costs `E/32 + ‖u‖²/4` plus
`k/32` per unit prefix mass and `bk/(32c⁷)` per unit top and total mass of `w`, as soon as the
two scalar budgets (coefficient of `E`, coefficient of `‖u‖²`) are at most `1/32` and `1/4`. -/
theorem exists_band_far_cross_le_reserve_shape :
    ∃ C_pr C_up C_upT C_np : ℝ, 0 < C_pr ∧ 0 ≤ C_up ∧ 0 ≤ C_upT ∧ 0 ≤ C_np ∧
      ∀ {R M N : ℕ} {c ρ Sg₁ k b : ℝ}, 2 ≤ R → R ^ 6 ≤ N → 1 ≤ M → M ≤ N →
        18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → 8 * c ≤ N → c ^ 4 ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ⌈linearNearRowRadius c⌉₊ + 1 ≤ N → R * R ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) →
        1 ≤ Sg₁ → (∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ Sg₁) →
        ‖poleModeResidual c N‖ ^ 2 ≤ ρ → 0 < k → 0 < b →
        128 * C_pr * (1 + Real.log R) ^ 2 / (Real.log N * k) +
            128 * c ^ 7 * C_pr * (1 + Real.log R) * terminalPacketCost R M N /
              (Real.log N * b * k) +
            32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) ≤ 1 / 32 →
        256 * C_pr * (1 + Real.log R) / (Real.log N * k) +
            256 * c ^ 7 * C_pr * (1 + Real.log R) / (Real.log N * b * k) +
            32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetG R N c Sg₁ +
              2 * bandFarBudgetA R N c) / (b * k) +
            128 * C_up * c ^ 2 * (1 + Real.log c) / k +
            128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) /
              (Real.log N * b * k) ≤ 1 / 4 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R a +
            (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
            (k / 32) * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
            (b * k / (32 * c ^ 7)) * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) +
            (b * k / (32 * c ^ 7)) * ‖w‖ ^ 2 := by
  obtain ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, hT2⟩ :=
    exists_band_far_cross_le_channels
  refine ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, ?_⟩
  intro R M N c ρ Sg₁ k b hR hR6 hM1 hMN hlog hc1 h8 h4 hsize_near hsize_up hrad hceil hRK
    hSg1 hSg hρ hk hb hsE hsU a hu1 w hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc7 : 0 < c ^ 7 := by positivity
  have hL : 0 < Real.log N := by linarith [Real.log_natCast_nonneg R]
  have hN0 : (0 : ℝ) < N := by linarith
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hρ0 : 0 ≤ ρ := (sq_nonneg _).trans hρ
  have hlR : 0 ≤ 1 + Real.log R := by linarith [Real.log_natCast_nonneg R]
  have hlc : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hX := hT2 hR hR6 hM1 hMN hlog hc1 h8 h4 hsize_near hsize_up hrad hceil hRK hSg1 hSg hρ a hu1
    hw (k / 128) (b * k / (128 * c ^ 7)) (k / 128) (b * k / (128 * c ^ 7)) (b * k / (32 * c ^ 7))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  rw [bandFarChannelBudget_eq] at hX
  set A := ∑ m ∈ Icc 1 R, a m ^ 2 with hAdef
  set G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 with hGdef
  set E := primeAdjunctionMass R a with hEdef
  set U := ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 with hUdef
  set P := ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 with hPdef
  set S := ∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2 with hSdef
  set TPC := terminalPacketCost R M N with hTPC
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hP0 : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hAU : A ≤ 2 * U := sum_sq_le_two_norm_sq hR hRR hlog a
  have hGE : G ≤ A + E := sum_one_add_log_mul_sq_le R a
  have hβG : 0 ≤ bandFarBudgetG R N c Sg₁ := by unfold bandFarBudgetG; positivity
  have hβA : 0 ≤ bandFarBudgetA R N c := by unfold bandFarBudgetA; positivity
  have e1 : C_pr * ((1 + Real.log R) * A + (1 + Real.log R) ^ 2 * E) / (Real.log N * (k / 128)) =
      128 * C_pr * (1 + Real.log R) / (Real.log N * k) * A +
        128 * C_pr * (1 + Real.log R) ^ 2 / (Real.log N * k) * E := by
    field_simp
  have e2 : C_pr * ((1 + Real.log R) * A + (1 + Real.log R) * TPC * E) /
        (Real.log N * (b * k / (128 * c ^ 7))) =
      128 * c ^ 7 * C_pr * (1 + Real.log R) / (Real.log N * b * k) * A +
        128 * c ^ 7 * C_pr * (1 + Real.log R) * TPC / (Real.log N * b * k) * E := by
    field_simp
  have e3 : C_np * (bandFarBudgetU R N c ρ Sg₁ * U + bandFarBudgetG R N c Sg₁ * G +
        bandFarBudgetA R N c * A) / (b * k / (32 * c ^ 7)) =
      32 * c ^ 7 * C_np / (b * k) * (bandFarBudgetU R N c ρ Sg₁ * U +
        bandFarBudgetG R N c Sg₁ * G + bandFarBudgetA R N c * A) := by
    field_simp
  have e4 : C_up * c ^ 2 * (1 + Real.log c) * U / (k / 128) =
      128 * C_up * c ^ 2 * (1 + Real.log c) / k * U := by
    field_simp
  have e5 : C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / Real.log N * U /
        (b * k / (128 * c ^ 7)) =
      128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (Real.log N * b * k) * U := by
    field_simp
  rw [e1, e2, e3, e4, e5] at hX
  have hsE' : 128 * C_pr * (1 + Real.log R) ^ 2 / (Real.log N * k) +
      128 * c ^ 7 * C_pr * (1 + Real.log R) * TPC / (Real.log N * b * k) +
      32 * c ^ 7 * C_np / (b * k) * bandFarBudgetG R N c Sg₁ ≤ 1 / 32 := by
    have : 32 * c ^ 7 * C_np / (b * k) * bandFarBudgetG R N c Sg₁ =
        32 * c ^ 7 * C_np * bandFarBudgetG R N c Sg₁ / (b * k) := by ring
    linarith
  have hsU' : 2 * (128 * C_pr * (1 + Real.log R) / (Real.log N * k)) +
      2 * (128 * c ^ 7 * C_pr * (1 + Real.log R) / (Real.log N * b * k)) +
      32 * c ^ 7 * C_np / (b * k) * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetG R N c Sg₁ +
        2 * bandFarBudgetA R N c) +
      128 * C_up * c ^ 2 * (1 + Real.log c) / k +
      128 * c ^ 7 * C_upT * c ^ 2 * ((N : ℝ) / M) * (1 + Real.log c) / (Real.log N * b * k) ≤
        1 / 4 := by
    have h1 : 2 * (128 * C_pr * (1 + Real.log R) / (Real.log N * k)) =
        256 * C_pr * (1 + Real.log R) / (Real.log N * k) := by ring
    have h2 : 2 * (128 * c ^ 7 * C_pr * (1 + Real.log R) / (Real.log N * b * k)) =
        256 * c ^ 7 * C_pr * (1 + Real.log R) / (Real.log N * b * k) := by ring
    have h3 : 32 * c ^ 7 * C_np / (b * k) * (bandFarBudgetU R N c ρ Sg₁ +
        2 * bandFarBudgetG R N c Sg₁ + 2 * bandFarBudgetA R N c) =
        32 * c ^ 7 * C_np * (bandFarBudgetU R N c ρ Sg₁ + 2 * bandFarBudgetG R N c Sg₁ +
          2 * bandFarBudgetA R N c) / (b * k) := by ring
    linarith
  have hfin := band_far_shape_arith (W := ‖w‖ ^ 2) hA0 hE0 hAU hGE
    (by positivity : (0 : ℝ) ≤ 128 * C_pr * (1 + Real.log R) / (Real.log N * k))
    (by positivity : (0 : ℝ) ≤ 128 * c ^ 7 * C_pr * (1 + Real.log R) / (Real.log N * b * k))
    (by positivity : (0 : ℝ) ≤ 32 * c ^ 7 * C_np / (b * k)) hβG hβA
    hsE' hsU' hP0 hS0 hk (by positivity : (0 : ℝ) ≤ b * k / c ^ 7)
  linarith only [hX, hfin]

/-! ### Scalar budgets of the band–far cross -/

/-- Powers of `c ≤ L` and `R` against `N ≥ L¹⁸ R¹⁶`. -/
theorem cpow_Rpow_div_le {L c Rr Nr σ : ℝ} (hL1 : 1 ≤ L) (hc0 : 0 ≤ c) (hcL : c ≤ L)
    (hR1 : 1 ≤ Rr) (hRN : L ^ 18 * Rr ^ 16 ≤ Nr) (hLσ : 1 / L ≤ σ) {i j : ℕ} (hi : i ≤ 17)
    (hj : j ≤ 16) : c ^ i * Rr ^ j / Nr ≤ σ := by
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < Nr := lt_of_lt_of_le (by positivity) hRN
  refine le_trans ?_ hLσ
  rw [div_le_div_iff₀ hN0 hL0, one_mul]
  have h1 : c ^ i * Rr ^ j ≤ L ^ i * Rr ^ 16 :=
    mul_le_mul (pow_le_pow_left₀ hc0 hcL i) (pow_le_pow_right₀ hR1 hj) (by positivity) (by positivity)
  have h2 : L ^ i * L ≤ L ^ 18 := by rw [← pow_succ]; exact pow_le_pow_right₀ hL1 (by omega)
  calc c ^ i * Rr ^ j * L ≤ L ^ i * Rr ^ 16 * L := mul_le_mul_of_nonneg_right h1 hL0.le
    _ = (L ^ i * L) * Rr ^ 16 := by ring
    _ ≤ L ^ 18 * Rr ^ 16 := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ Nr := hRN

/-- `c⁷ βG / L ≤ 8 θ σ`. -/
theorem budgetG_le {L c θ σ Sg lR lc Rr Nr : ℝ} (hθ : 0 < θ)
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hlc1 : 1 ≤ lc) (hSg1 : 1 ≤ Sg)
    (hlR : lR ≤ 2 * θ * L) (hR1 : 1 ≤ Rr) (hRN : L ^ 18 * Rr ^ 16 ≤ Nr)
    (hm1 : c ^ 8 * lc * Sg ^ 2 / L ≤ σ) (hLσ : 1 / L ≤ σ) :
    c ^ 7 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) / L ≤
      8 * θ * σ := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hN0 : 0 < Nr := lt_of_lt_of_le (by positivity) hRN
  have hσ0 : 0 ≤ σ := le_trans (by positivity) hLσ
  have hlRL : lR / L ≤ 2 * θ := by rw [div_le_iff₀ hL0]; linarith
  have e : c ^ 7 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) *
      lR) / L = (lR / L) * (c ^ 7 * lc / L + c ^ 8 * lc * Sg ^ 2 / L + c ^ 13 / Nr +
        c ^ 11 * Rr ^ 4 / (Nr * L)) := by
    field_simp; ring
  rw [e]
  have h7 : c ^ 7 * lc / L ≤ σ := by
    refine le_trans (div_le_div_of_nonneg_right ?_ hL0.le) hm1
    calc c ^ 7 * lc ≤ c ^ 8 * lc :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) (by linarith)
      _ ≤ c ^ 8 * lc * Sg ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hSg1)
  have h13 : c ^ 13 / Nr ≤ σ := by
    have := cpow_Rpow_div_le hL1 hc0.le hcL hR1 hRN hLσ (i := 13) (j := 0) (by norm_num) (by norm_num)
    simpa using this
  have h4 : c ^ 11 * Rr ^ 4 / (Nr * L) ≤ σ :=
    le_trans (div_le_div_of_nonneg_left (by positivity) hN0 (le_mul_of_one_le_right hN0.le hL1))
      (cpow_Rpow_div_le hL1 hc0.le hcL hR1 hRN hLσ (by norm_num) (by norm_num))
  have h2 : c ^ 7 * lc / L + c ^ 8 * lc * Sg ^ 2 / L + c ^ 13 / Nr +
      c ^ 11 * Rr ^ 4 / (Nr * L) ≤ 4 * σ := by linarith only [h7, hm1, h13, h4]
  calc (lR / L) * (c ^ 7 * lc / L + c ^ 8 * lc * Sg ^ 2 / L + c ^ 13 / Nr +
        c ^ 11 * Rr ^ 4 / (Nr * L)) ≤ (2 * θ) * (4 * σ) :=
        mul_le_mul hlRL h2 (by positivity) (by positivity)
    _ = 8 * θ * σ := by ring

/-- `c⁷ βU / L ≤ (4θ²K_ρ + 878) σ`. -/
theorem budgetUpart_le {L c θ Kρ Λ σ Sg lR lc ρ Rr Nr : ℝ}
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hKρ : 0 ≤ Kρ) (hlc1 : 1 ≤ lc) (hSg1 : 1 ≤ Sg)
    (hΛ1 : 1 ≤ Λ) (hlR0 : 0 ≤ lR) (hlR : lR ≤ 2 * θ * L) (hR1 : 1 ≤ Rr)
    (hRN : L ^ 18 * Rr ^ 16 ≤ Nr) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Kρ * (c ^ 2 * lc ^ 3 * Λ / L))
    (hm2 : c ^ 11 * lc ^ 3 * Sg * Λ / L ^ 2 ≤ σ) (hLσ : 1 / L ≤ σ) :
    c ^ 7 * ((lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
      c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr)) / L ≤ (4 * θ ^ 2 * Kρ + 878) * σ := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hN0 : 0 < Nr := lt_of_lt_of_le (by positivity) hRN
  have hσ0 : 0 ≤ σ := le_trans (by positivity) hLσ
  have hlRL : lR / L ≤ 2 * θ := by rw [div_le_iff₀ hL0]; linarith
  have hlRL0 : 0 ≤ lR / L := by positivity
  have hX : c ^ 11 ≤ c ^ 11 * lc ^ 3 * Sg * Λ := by
    have h : 1 ≤ lc ^ 3 * Sg * Λ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlc1) hSg1) hΛ1
    calc c ^ 11 = c ^ 11 * 1 := (mul_one _).symm
      _ ≤ c ^ 11 * (lc ^ 3 * Sg * Λ) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = c ^ 11 * lc ^ 3 * Sg * Λ := by ring
  have hmono : ∀ x : ℝ, x ≤ c ^ 11 * lc ^ 3 * Sg * Λ → x / L ^ 2 ≤ σ := fun x hx =>
    le_trans (div_le_div_of_nonneg_right hx (by positivity)) hm2
  have e : c ^ 7 * ((lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
      c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr)) / L =
      (lR / L) ^ 2 * (c ^ 7 * ρ / L) + (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) * c ^ 9 / L ^ 2 +
        c ^ 11 * lc / L ^ 2 + c ^ 10 * Rr ^ 2 / Nr := by
    field_simp
  rw [e]
  have hρL : c ^ 7 * ρ / L ≤ Kρ * σ := by
    have h1 : c ^ 7 * ρ / L ≤ Kρ * (c ^ 9 * lc ^ 3 * Λ / L ^ 2) := by
      have : c ^ 7 * ρ ≤ c ^ 7 * (Kρ * (c ^ 2 * lc ^ 3 * Λ / L)) :=
        mul_le_mul_of_nonneg_left hρ (by positivity)
      calc c ^ 7 * ρ / L ≤ c ^ 7 * (Kρ * (c ^ 2 * lc ^ 3 * Λ / L)) / L :=
            div_le_div_of_nonneg_right this hL0.le
        _ = Kρ * (c ^ 9 * lc ^ 3 * Λ / L ^ 2) := by field_simp
    refine h1.trans (mul_le_mul_of_nonneg_left (hmono _ ?_) hKρ)
    calc c ^ 9 * lc ^ 3 * Λ ≤ c ^ 11 * lc ^ 3 * Λ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hc1 (by norm_num)) (by positivity)) (by linarith)
      _ = c ^ 11 * lc ^ 3 * Λ * 1 := (mul_one _).symm
      _ ≤ c ^ 11 * lc ^ 3 * Λ * Sg := mul_le_mul_of_nonneg_left hSg1 (by positivity)
      _ = c ^ 11 * lc ^ 3 * Sg * Λ := by ring
  have hR15 : Rr ^ 15 / Nr ≤ 1 := by
    rw [div_le_one hN0]
    have h1 : Rr ^ 15 ≤ Rr ^ 16 := pow_le_pow_right₀ hR1 (by norm_num)
    have h2 : Rr ^ 16 ≤ L ^ 18 * Rr ^ 16 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hL1)
    linarith only [h1, h2, hRN]
  have h9 : (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) * c ^ 9 / L ^ 2 ≤ 876 * σ := by
    have hR15' : 72 * Rr ^ 15 / Nr ≤ 72 := by rw [mul_div_assoc]; linarith only [hR15]
    have h1 : (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) ≤ 876 * Sg := by linarith only [hR15', hSg1]
    have h2 : (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) * c ^ 9 / L ^ 2 ≤ 876 * ((Sg * c ^ 9) / L ^ 2) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ c ^ 9)
      linarith only [this]
    refine h2.trans (mul_le_mul_of_nonneg_left (hmono _ ?_) (by norm_num))
    calc Sg * c ^ 9 ≤ Sg * c ^ 11 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (by norm_num)) (by linarith)
      _ ≤ Sg * (c ^ 11 * lc ^ 3 * Λ) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have h : 1 ≤ lc ^ 3 * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlc1) hΛ1
          calc c ^ 11 = c ^ 11 * 1 := (mul_one _).symm
            _ ≤ c ^ 11 * (lc ^ 3 * Λ) := mul_le_mul_of_nonneg_left h (by positivity)
            _ = c ^ 11 * lc ^ 3 * Λ := by ring
      _ = c ^ 11 * lc ^ 3 * Sg * Λ := by ring
  have h11 : c ^ 11 * lc / L ^ 2 ≤ σ := by
    refine hmono _ ?_
    have h : 1 ≤ lc ^ 2 * Sg * Λ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlc1) hSg1) hΛ1
    calc c ^ 11 * lc = c ^ 11 * lc * 1 := (mul_one _).symm
      _ ≤ c ^ 11 * lc * (lc ^ 2 * Sg * Λ) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = c ^ 11 * lc ^ 3 * Sg * Λ := by ring
  have h10 := cpow_Rpow_div_le hL1 hc0.le hcL hR1 hRN hLσ (i := 10) (j := 2) (by norm_num)
    (by norm_num)
  have hfirst : (lR / L) ^ 2 * (c ^ 7 * ρ / L) ≤ 4 * θ ^ 2 * Kρ * σ := by
    have hsq : (lR / L) ^ 2 ≤ (2 * θ) ^ 2 := pow_le_pow_left₀ hlRL0 hlRL 2
    calc (lR / L) ^ 2 * (c ^ 7 * ρ / L) ≤ (2 * θ) ^ 2 * (Kρ * σ) :=
          mul_le_mul hsq hρL (by positivity) (by positivity)
      _ = 4 * θ ^ 2 * Kρ * σ := by ring
  have : (4 * θ ^ 2 * Kρ + 878) * σ = 4 * θ ^ 2 * Kρ * σ + 876 * σ + σ + σ := by ring
  linarith only [hfirst, h9, h11, h10, this]

/-- `c⁷ (1 + log c) / L ≤ σ` from the main monomial bound. -/
theorem c7lc_le {L c σ Sg lc : ℝ} (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hlc1 : 1 ≤ lc) (hSg1 : 1 ≤ Sg)
    (hm1 : c ^ 8 * lc * Sg ^ 2 / L ≤ σ) : c ^ 7 * lc / L ≤ σ := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  refine le_trans (div_le_div_of_nonneg_right ?_ hL0.le) hm1
  calc c ^ 7 * lc ≤ c ^ 8 * lc :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) (by linarith)
    _ ≤ c ^ 8 * lc * Sg ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hSg1)

/-- `E`-budget of the band–far cross at `k = θ L/(2D)`. -/
theorem budgetE_le {L c θ D b Cpr Cnp CB σ Sg lR lc TPC Rr Nr : ℝ}
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hθ : 0 < θ) (hD : 0 < D) (hb : 0 < b)
    (hCpr : 0 ≤ Cpr) (hCnp : 0 ≤ Cnp) (hCB : 0 ≤ CB) (hlc1 : 1 ≤ lc) (hSg1 : 1 ≤ Sg)
    (hlR0 : 0 ≤ lR) (hlR : lR ≤ 2 * θ * L) (hR1 : 1 ≤ Rr) (hRN : L ^ 18 * Rr ^ 16 ≤ Nr)
    (hTPC0 : 0 ≤ TPC) (hTPC : TPC ≤ CB * lc)
    (hm1 : c ^ 8 * lc * Sg ^ 2 / L ≤ σ) (hLσ : 1 / L ≤ σ)
    (hθs : 1024 * D * Cpr * θ ≤ 1 / 64)
    (hσE : (512 * D * Cpr * CB / b + 512 * D * Cnp / b) * σ ≤ 1 / 64) :
    128 * Cpr * lR ^ 2 / (L * (θ * L / (2 * D))) +
        128 * c ^ 7 * Cpr * lR * TPC / (L * b * (θ * L / (2 * D))) +
        32 * c ^ 7 * Cnp * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr +
          c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) / (b * (θ * L / (2 * D))) ≤ 1 / 32 := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hσ0 : 0 ≤ σ := le_trans (by positivity) hLσ
  have hlRL : lR / L ≤ 2 * θ := by rw [div_le_iff₀ hL0]; linarith
  have hE1 : 128 * Cpr * lR ^ 2 / (L * (θ * L / (2 * D))) ≤ 1 / 64 := by
    rw [div_le_iff₀ (by positivity)]
    have hl2 : lR ^ 2 ≤ (2 * θ * L) ^ 2 := pow_le_pow_left₀ hlR0 hlR 2
    have h1 : 128 * Cpr * lR ^ 2 ≤ 128 * Cpr * (2 * θ * L) ^ 2 :=
      mul_le_mul_of_nonneg_left hl2 (by positivity)
    have e : 128 * Cpr * (2 * θ * L) ^ 2 = (1024 * D * Cpr * θ) * (L * (θ * L / (2 * D))) := by
      field_simp; ring
    have h2 := mul_le_mul_of_nonneg_right hθs (by positivity : (0 : ℝ) ≤ L * (θ * L / (2 * D)))
    linarith only [h1, e, h2]
  have hE2 : 128 * c ^ 7 * Cpr * lR * TPC / (L * b * (θ * L / (2 * D))) ≤
      512 * D * Cpr * CB / b * σ := by
    have e : 128 * c ^ 7 * Cpr * lR * TPC / (L * b * (θ * L / (2 * D))) =
        256 * D * Cpr / (b * θ) * (lR / L) * (c ^ 7 * TPC / L) := by
      field_simp; ring
    rw [e]
    have h2 : c ^ 7 * TPC / L ≤ CB * σ := by
      have h3 : c ^ 7 * TPC / L ≤ CB * (c ^ 7 * lc / L) := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hL0]
        have := mul_le_mul_of_nonneg_left hTPC (by positivity : (0 : ℝ) ≤ c ^ 7)
        linarith only [this]
      exact h3.trans (mul_le_mul_of_nonneg_left (c7lc_le hL1 hc1 hlc1 hSg1 hm1) hCB)
    calc 256 * D * Cpr / (b * θ) * (lR / L) * (c ^ 7 * TPC / L) ≤
        256 * D * Cpr / (b * θ) * (2 * θ) * (CB * σ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlRL (by positivity)) h2
            (by positivity) (by positivity)
      _ = 512 * D * Cpr * CB / b * σ := by field_simp; ring
  have hE3 : 32 * c ^ 7 * Cnp * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr +
        c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) / (b * (θ * L / (2 * D))) ≤ 512 * D * Cnp / b * σ := by
    have e : 32 * c ^ 7 * Cnp * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr +
        c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) / (b * (θ * L / (2 * D))) =
        64 * D * Cnp / (b * θ) * (c ^ 7 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr +
          c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) / L) := by
      field_simp; ring
    rw [e]
    calc 64 * D * Cnp / (b * θ) * (c ^ 7 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr +
          c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) / L) ≤ 64 * D * Cnp / (b * θ) * (8 * θ * σ) :=
          mul_le_mul_of_nonneg_left
            (budgetG_le hθ hL1 hc1 hcL hlc1 hSg1 hlR hR1 hRN hm1 hLσ) (by positivity)
      _ = 512 * D * Cnp / b * σ := by field_simp; ring
  have hexp : (512 * D * Cpr * CB / b + 512 * D * Cnp / b) * σ =
      512 * D * Cpr * CB / b * σ + 512 * D * Cnp / b * σ := by ring
  linarith only [hE1, hE2, hE3, hexp, hσE]

/-- `‖u‖²`-budget of the band–far cross at `k = θ L/(2D)`. -/
theorem budgetU_le {L c θ D b Cpr Cnp Cup CupT Hc Kρ Λ σ Sg lR lc ρ NM Rr Nr : ℝ}
    (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcL : c ≤ L) (hθ : 0 < θ) (hD : 0 < D) (hb : 0 < b)
    (hCpr : 0 ≤ Cpr) (hCnp : 0 ≤ Cnp) (hCup : 0 ≤ Cup) (hCupT : 0 ≤ CupT) (hHc : 0 ≤ Hc)
    (hKρ : 0 ≤ Kρ) (hlc1 : 1 ≤ lc) (hSg1 : 1 ≤ Sg) (hΛ1 : 1 ≤ Λ)
    (hlR0 : 0 ≤ lR) (hlR : lR ≤ 2 * θ * L) (hR1 : 1 ≤ Rr) (hRN : L ^ 18 * Rr ^ 16 ≤ Nr)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Kρ * (c ^ 2 * lc ^ 3 * Λ / L)) (hNM : NM ≤ 2 * Hc * c)
    (hm1 : c ^ 8 * lc * Sg ^ 2 / L ≤ σ) (hm2 : c ^ 11 * lc ^ 3 * Sg * Λ / L ^ 2 ≤ σ)
    (hLσ : 1 / L ≤ σ)
    (hσU : (1024 * D * Cpr + 1024 * D * Cpr / b +
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880 + 16 * θ) / (b * θ) + 256 * D * Cup / θ +
      512 * D * CupT * Hc / (b * θ)) * σ ≤ 1 / 4) :
    256 * Cpr * lR / (L * (θ * L / (2 * D))) +
        256 * c ^ 7 * Cpr * lR / (L * b * (θ * L / (2 * D))) +
        32 * c ^ 7 * Cnp * (((lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
            c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr)) +
          2 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) +
          2 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L))) / (b * (θ * L / (2 * D))) +
        128 * Cup * c ^ 2 * lc / (θ * L / (2 * D)) +
        128 * c ^ 7 * CupT * c ^ 2 * NM * lc / (L * b * (θ * L / (2 * D))) ≤ 1 / 4 := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hσ0 : 0 ≤ σ := le_trans (by positivity) hLσ
  have hN0 : 0 < Nr := lt_of_lt_of_le (by positivity) hRN
  have hlRL : lR / L ≤ 2 * θ := by rw [div_le_iff₀ hL0]; linarith
  have h7 := c7lc_le hL1 hc1 hlc1 hSg1 hm1
  have hc7 : c ^ 7 / L ≤ σ :=
    le_trans (div_le_div_of_nonneg_right (le_mul_of_one_le_right (by positivity) hlc1) hL0.le) h7
  have hU1 : 256 * Cpr * lR / (L * (θ * L / (2 * D))) ≤ 1024 * D * Cpr * σ := by
    have e : 256 * Cpr * lR / (L * (θ * L / (2 * D))) = 512 * D * Cpr / θ * (lR / L) * (1 / L) := by
      field_simp; ring
    rw [e]
    calc 512 * D * Cpr / θ * (lR / L) * (1 / L) ≤ 512 * D * Cpr / θ * (2 * θ) * σ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlRL (by positivity)) hLσ (by positivity)
            (by positivity)
      _ = 1024 * D * Cpr * σ := by field_simp; ring
  have hU2 : 256 * c ^ 7 * Cpr * lR / (L * b * (θ * L / (2 * D))) ≤ 1024 * D * Cpr / b * σ := by
    have e : 256 * c ^ 7 * Cpr * lR / (L * b * (θ * L / (2 * D))) =
        512 * D * Cpr / (b * θ) * (lR / L) * (c ^ 7 / L) := by
      field_simp; ring
    rw [e]
    calc 512 * D * Cpr / (b * θ) * (lR / L) * (c ^ 7 / L) ≤ 512 * D * Cpr / (b * θ) * (2 * θ) * σ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hlRL (by positivity)) hc7 (by positivity)
            (by positivity)
      _ = 1024 * D * Cpr / b * σ := by field_simp; ring
  have hβA : c ^ 7 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L)) / L ≤ σ := by
    have e : c ^ 7 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L)) / L =
        (c ^ 9 * Rr ^ 5 / Nr) * (1 / (Nr * L ^ 2)) := by
      field_simp
    rw [e]
    have h1 := cpow_Rpow_div_le hL1 hc0.le hcL hR1 hRN hLσ (i := 9) (j := 5) (by norm_num)
      (by norm_num)
    have hN1 : 1 ≤ Nr := le_trans (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1)
      (one_le_pow₀ hR1)) hRN
    have h2 : 1 / (Nr * L ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hL1)
    calc (c ^ 9 * Rr ^ 5 / Nr) * (1 / (Nr * L ^ 2)) ≤ σ * 1 :=
          mul_le_mul h1 h2 (by positivity) hσ0
      _ = σ := mul_one σ
  have hβU := budgetUpart_le hL1 hc1 hcL hKρ hlc1 hSg1 hΛ1 hlR0 hlR hR1 hRN hρ0 hρ hm2 hLσ
  have hβG := budgetG_le hθ hL1 hc1 hcL hlc1 hSg1 hlR hR1 hRN hm1 hLσ
  have hU3 : 32 * c ^ 7 * Cnp * (((lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
            c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr)) +
          2 * (lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) * lR) +
          2 * (c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L))) / (b * (θ * L / (2 * D))) ≤
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880 + 16 * θ) / (b * θ) * σ := by
    generalize hBU : (lR / L) ^ 2 * ρ + c ^ 2 * (24 + 780 * Sg + 72 * Rr ^ 15 / Nr) / L +
      c ^ 4 * lc / L + c ^ 3 * Rr ^ 2 * (L / Nr) = BU at hβU ⊢
    generalize hBG : lR * lc / L + c * (Sg ^ 2 * lc / L + c ^ 5 / Nr + c ^ 3 * Rr ^ 4 / (Nr * L)) *
      lR = BG at hβG ⊢
    generalize hBA : c ^ 2 * Rr ^ 5 / (Nr ^ 2 * L) = BA at hβA ⊢
    have e : 32 * c ^ 7 * Cnp * (BU + 2 * BG + 2 * BA) / (b * (θ * L / (2 * D))) =
        64 * D * Cnp / (b * θ) * (c ^ 7 * BU / L + 2 * (c ^ 7 * BG / L) + 2 * (c ^ 7 * BA / L)) := by
      field_simp; ring
    rw [e]
    have hsum : c ^ 7 * BU / L + 2 * (c ^ 7 * BG / L) + 2 * (c ^ 7 * BA / L) ≤
        (4 * θ ^ 2 * Kρ + 880 + 16 * θ) * σ := by
      have : (4 * θ ^ 2 * Kρ + 880 + 16 * θ) * σ =
          (4 * θ ^ 2 * Kρ + 878) * σ + 2 * (8 * θ * σ) + 2 * σ := by ring
      linarith only [hβU, hβG, hβA, this]
    calc 64 * D * Cnp / (b * θ) * (c ^ 7 * BU / L + 2 * (c ^ 7 * BG / L) + 2 * (c ^ 7 * BA / L)) ≤
        64 * D * Cnp / (b * θ) * ((4 * θ ^ 2 * Kρ + 880 + 16 * θ) * σ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880 + 16 * θ) / (b * θ) * σ := by ring
  have hU4 : 128 * Cup * c ^ 2 * lc / (θ * L / (2 * D)) ≤ 256 * D * Cup / θ * σ := by
    have e : 128 * Cup * c ^ 2 * lc / (θ * L / (2 * D)) = 256 * D * Cup / θ * (c ^ 2 * lc / L) := by
      field_simp; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (le_trans (div_le_div_of_nonneg_right ?_ hL0.le) h7)
      (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) (by linarith)
  have hU5 : 128 * c ^ 7 * CupT * c ^ 2 * NM * lc / (L * b * (θ * L / (2 * D))) ≤
      512 * D * CupT * Hc / (b * θ) * σ := by
    have e : 128 * c ^ 7 * CupT * c ^ 2 * NM * lc / (L * b * (θ * L / (2 * D))) =
        256 * D * CupT / (b * θ) * (NM * (c ^ 9 * lc / L ^ 2)) := by
      field_simp; ring
    rw [e]
    have h10 : c ^ 10 * lc / L ^ 2 ≤ σ := by
      refine le_trans (div_le_div_of_nonneg_right ?_ (by positivity)) hm2
      have h2 : 1 ≤ lc ^ 2 * Sg * Λ :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlc1) hSg1) hΛ1
      calc c ^ 10 * lc ≤ c ^ 11 * lc :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) (by linarith)
        _ = c ^ 11 * lc * 1 := (mul_one _).symm
        _ ≤ c ^ 11 * lc * (lc ^ 2 * Sg * Λ) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = c ^ 11 * lc ^ 3 * Sg * Λ := by ring
    have h1 : NM * (c ^ 9 * lc / L ^ 2) ≤ 2 * Hc * σ :=
      calc NM * (c ^ 9 * lc / L ^ 2) ≤ (2 * Hc * c) * (c ^ 9 * lc / L ^ 2) :=
            mul_le_mul_of_nonneg_right hNM (by positivity)
        _ = 2 * Hc * (c ^ 10 * lc / L ^ 2) := by ring
        _ ≤ 2 * Hc * σ := mul_le_mul_of_nonneg_left h10 (by positivity)
    calc 256 * D * CupT / (b * θ) * (NM * (c ^ 9 * lc / L ^ 2)) ≤
        256 * D * CupT / (b * θ) * (2 * Hc * σ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 512 * D * CupT * Hc / (b * θ) * σ := by ring
  have hexp : (1024 * D * Cpr + 1024 * D * Cpr / b +
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880 + 16 * θ) / (b * θ) + 256 * D * Cup / θ +
      512 * D * CupT * Hc / (b * θ)) * σ = 1024 * D * Cpr * σ + 1024 * D * Cpr / b * σ +
      64 * D * Cnp * (4 * θ ^ 2 * Kρ + 880 + 16 * θ) / (b * θ) * σ + 256 * D * Cup / θ * σ +
      512 * D * CupT * Hc / (b * θ) * σ := by ring
  linarith only [hU1, hU2, hU3, hU4, hU5, hexp, hσU]


/-- **The band–far cross from monomial bounds.** The assembly-shape cross bound at
`k = θ log N / (2D)`, with the two scalar budgets verified from `c⁸ (1 + log c) Sg² / log N ≤ σ`,
`c¹¹ (1 + log c)³ Sg Λ / (log N)² ≤ σ`, `1 / log N ≤ σ`, `1 + log R ≤ 2θ log N` and
`(log N)¹⁸ R¹⁶ ≤ N`. -/
theorem exists_band_far_cross_le_reserve_of_monomials :
    ∃ C_pr C_up C_upT C_np : ℝ, 0 < C_pr ∧ 0 ≤ C_up ∧ 0 ≤ C_upT ∧ 0 ≤ C_np ∧
      ∀ {R M N : ℕ} {c ρ Sg₁ θ D b CB Hc Kρ Λ σ : ℝ}, 2 ≤ R → R ^ 6 ≤ N → 1 ≤ M → M ≤ N →
        18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → 8 * c ≤ N → c ^ 4 ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ⌈linearNearRowRadius c⌉₊ + 1 ≤ N → R * R ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) →
        1 ≤ Sg₁ → (∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ Sg₁) →
        ‖poleModeResidual c N‖ ^ 2 ≤ ρ →
        1 ≤ Real.log N → c ≤ Real.log N → 0 < θ → 0 < D → 0 < b → 0 ≤ CB → 0 ≤ Hc → 0 ≤ Kρ →
        1 ≤ Λ → 1 + Real.log R ≤ 2 * θ * Real.log N →
        Real.log N ^ 18 * (R : ℝ) ^ 16 ≤ N →
        ρ ≤ Kρ * (c ^ 2 * (1 + Real.log c) ^ 3 * Λ / Real.log N) →
        terminalPacketCost R M N ≤ CB * (1 + Real.log c) → (N : ℝ) / M ≤ 2 * Hc * c →
        c ^ 8 * (1 + Real.log c) * Sg₁ ^ 2 / Real.log N ≤ σ →
        c ^ 11 * (1 + Real.log c) ^ 3 * Sg₁ * Λ / Real.log N ^ 2 ≤ σ →
        1 / Real.log N ≤ σ →
        1024 * D * C_pr * θ ≤ 1 / 64 →
        (512 * D * C_pr * CB / b + 512 * D * C_np / b) * σ ≤ 1 / 64 →
        (1024 * D * C_pr + 1024 * D * C_pr / b +
          64 * D * C_np * (4 * θ ^ 2 * Kρ + 880 + 16 * θ) / (b * θ) + 256 * D * C_up / θ +
          512 * D * C_upT * Hc / (b * θ)) * σ ≤ 1 / 4 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R a +
            (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
            (θ * Real.log N / (2 * D) / 32) * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
            (b * (θ * Real.log N / (2 * D)) / (32 * c ^ 7)) *
              (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) +
            (b * (θ * Real.log N / (2 * D)) / (32 * c ^ 7)) * ‖w‖ ^ 2 := by
  obtain ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, hspec⟩ :=
    exists_band_far_cross_le_reserve_shape
  refine ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, ?_⟩
  intro R M N c ρ Sg₁ θ D b CB Hc Kρ Λ σ hR hR6 hM1 hMN hlog hc1 h8 h4 hsize_near hsize_up hrad
    hceil hRK hSg1 hSg hρ hL1 hcL hθ hD hb hCB hHc hKρ hΛ1 hlR hRN hρK hTPC hNM hm1 hm2 hLσ hθs hσE
    hσU a hu1 w hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hlR0 : 0 ≤ 1 + Real.log R := by linarith [Real.log_natCast_nonneg R]
  have hlc1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hρ0 : 0 ≤ ρ := (sq_nonneg _).trans hρ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hTPC0 : 0 ≤ terminalPacketCost R M N := terminalPacketCost_nonneg R hMN
  refine hspec hR hR6 hM1 hMN hlog hc1 h8 h4 hsize_near hsize_up hrad hceil hRK hSg1 hSg hρ
    (by positivity) hb ?_ ?_ a hu1 hw
  · unfold bandFarBudgetG
    exact budgetE_le hL1 hc1 hcL hθ hD hb hCpr.le hCnp hCB hlc1 hSg1 hlR0 hlR hR1 hRN hTPC0 hTPC
      hm1 hLσ hθs hσE
  · unfold bandFarBudgetU bandFarBudgetG bandFarBudgetA
    exact budgetU_le hL1 hc1 hcL hθ hD hb hCpr.le hCnp hCup hCupT hHc hKρ hlc1 hSg1 hΛ1 hlR0 hlR hR1
      hRN hρ0 hρK hNM hm1 hm2 hLσ hσU

/-! ### Scalar smallness below the eighth root -/

/-- Monomials in `c ≤ L^α` and `1 + log c ≤ L^ν` against powers of `L`. -/
theorem monomial_le_rpow {L c α ν lc : ℝ} (hL1 : 1 ≤ L) (hc0 : 0 ≤ c) (hcup : c ≤ L ^ α)
    (hlc0 : 0 ≤ lc) (hlc : lc ≤ L ^ ν) (i j : ℕ) (e : ℝ)
    (he : (i : ℝ) * α + (j : ℝ) * ν ≤ e) : c ^ i * lc ^ j ≤ L ^ e := by
  have hL0 : 0 < L := by linarith
  have h1 : c ^ i ≤ L ^ ((i : ℝ) * α) := by
    have hp := pow_le_pow_left₀ hc0 hcup i
    have he' : (L ^ α) ^ i = L ^ ((i : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he'
  have h2 : lc ^ j ≤ L ^ ((j : ℝ) * ν) := by
    have hp := pow_le_pow_left₀ hlc0 hlc j
    have he' : (L ^ ν) ^ j = L ^ ((j : ℝ) * ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he'
  calc c ^ i * lc ^ j ≤ L ^ ((i : ℝ) * α) * L ^ ((j : ℝ) * ν) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = L ^ ((i : ℝ) * α + (j : ℝ) * ν) := by rw [← Real.rpow_add hL0]
    _ ≤ L ^ e := Real.rpow_le_rpow_of_exponent_le hL1 he

/-- `L^a / L^b ≤ L^(-ν)` from `a - b ≤ -ν`. -/
theorem rpow_div_rpow_le {L a b ν : ℝ} (hL1 : 1 ≤ L) (h : a - b ≤ -ν) :
    L ^ a / L ^ b ≤ L ^ (-ν) := by
  have hL0 : 0 < L := by linarith
  rw [← Real.rpow_sub hL0]
  exact Real.rpow_le_rpow_of_exponent_le hL1 h

/-- The monomial bounds of the band–far budgets below the eighth root. -/
theorem band_far_monomials_le {L c α ν Sg : ℝ} (hL1 : 1 ≤ L) (hc1 : 1 ≤ c) (hcup : c ≤ L ^ α)
    (hlc : 1 + Real.log c ≤ L ^ ν) (hSg0 : 0 ≤ Sg) (hSg : Sg ≤ L ^ ν)
    (h8 : 8 * α + 4 * ν ≤ 1) (h11 : 11 * α + 6 * ν ≤ 2) :
    c ^ 8 * (1 + Real.log c) * Sg ^ 2 / L ≤ L ^ (-ν) ∧
      c ^ 11 * (1 + Real.log c) ^ 3 * Sg * L ^ ν / L ^ 2 ≤ L ^ (-ν) := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hlc0 : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hSg2 : Sg ^ 2 ≤ L ^ (2 * ν) := by
    have hp := pow_le_pow_left₀ hSg0 hSg 2
    have he : (L ^ ν) ^ 2 = L ^ (2 * ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
    exact hp.trans_eq he
  constructor
  · have h1 := monomial_le_rpow hL1 hc0 hcup hlc0 hlc 8 1 (8 * α + ν) (by push_cast; linarith)
    have h2 : c ^ 8 * (1 + Real.log c) * Sg ^ 2 ≤ L ^ (8 * α + ν) * L ^ (2 * ν) := by
      rw [show c ^ 8 * (1 + Real.log c) = c ^ 8 * (1 + Real.log c) ^ 1 by ring]
      exact mul_le_mul h1 hSg2 (by positivity) (by positivity)
    rw [← Real.rpow_add hL0] at h2
    calc c ^ 8 * (1 + Real.log c) * Sg ^ 2 / L ≤ L ^ (8 * α + ν + 2 * ν) / L ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact div_le_div_of_nonneg_right h2 hL0.le
      _ ≤ L ^ (-ν) := rpow_div_rpow_le hL1 (by linarith)
  · have h1 := monomial_le_rpow hL1 hc0 hcup hlc0 hlc 11 3 (11 * α + 3 * ν) (by push_cast; linarith)
    have h2 : c ^ 11 * (1 + Real.log c) ^ 3 * Sg * L ^ ν ≤ L ^ (11 * α + 3 * ν) * L ^ ν * L ^ ν :=
      mul_le_mul (mul_le_mul h1 hSg hSg0 (by positivity)) le_rfl (by positivity) (by positivity)
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0] at h2
    calc c ^ 11 * (1 + Real.log c) ^ 3 * Sg * L ^ ν / L ^ 2 ≤
        L ^ (11 * α + 3 * ν + ν + ν) / L ^ (2 : ℝ) := by
          rw [Real.rpow_two]; exact div_le_div_of_nonneg_right h2 (by positivity)
      _ ≤ L ^ (-ν) := rpow_div_rpow_le hL1 (by linarith)

/-- **Scalar smallness of the block inputs below the eighth root.** With `ν = (1 - 8α)/64`,
`q = α + 1/4`: the band-0 and band-0/band-1 smallness conditions and the block floors
`κ₀ + 3`, `κ₀ + 2 + √L/32` and `κ₀ + 2 + 3bk/(16c⁷)` (`k = θ₁ L/(2D)`). -/
theorem complement_scalar_smallness_one_eighth
    {N Q₁ R₀ : ℕ} {α q ν c L Lh θ₁ D b κ₀ C_small0 C_coerc0 C_band1 C_cross01 : ℝ}
    (hα : 0 < α) (hν : 0 < ν) (hν8 : 64 * ν ≤ 1 - 8 * α) (hq : q = α + 1 / 4)
    (hc1 : 1 ≤ c) (hcup : c ≤ L ^ α) (hL1 : 1 ≤ L) (hLh_eq : Lh = L ^ (1 / 2 : ℝ))
    (hb : 0 < b) (hθ₁ : 0 < θ₁) (hD : 0 < D) (hκ₀ : 0 < κ₀)
    (hC_small0 : 0 < C_small0) (hC_cross01 : 0 < C_cross01)
    (hVc : 1 + Real.log c ≤ L ^ ν)
    (hsqrtQ : (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt Q₁)
    (hlogQ_lb : q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ))
    (hH₀_ub : 1 + Real.log (R₀ : ℝ) ≤ 2 * Lh)
    (hlogR₀_lb : Lh - 1 ≤ Real.log (R₀ : ℝ))
    (hR₀_tail : (R₀ : ℝ) * Real.sqrt (L / N) ≤ 1 / L)
    (hc5N : c ^ 5 * L / N ≤ 1 / L)
    (hc3R₀4 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ 1 / L)
    (hc3R₀2 : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / N) ≤ 1 / L)
    (hν_b1 : C_small0 * 18 ≤ L ^ ν)
    (hν_b2 : C_cross01 * 4 ≤ L ^ ν)
    (hν_b6 : 32 * C_band1 ≤ L ^ ν)
    (hν_b7 : 32 * D * (κ₀ + 2) / (3 * b * θ₁) ≤ L ^ ν)
    (hll_scaled : κ₀ + 4 + C_coerc0 + 3 / 4 ≤ ((3 / 4 : ℝ) * q - α) * Real.log L)
    (hL_Lh_gap : (8 * (κ₀ + 3)) ^ 2 ≤ L)
    (hL_w : 32 * D * (κ₀ + 2) / θ₁ ≤ L) (hb8 : b ≤ 1 / 8) :
    C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 ∧
    C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 ∧
    κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 ∧
    κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) ∧
    κ₀ + 2 + 3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7) ≤ θ₁ * L / (2 * D) / 8 ∧
    κ₀ + 2 + 3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7) ≤
      3 * b * (θ₁ * L / (2 * D)) / (8 * c ^ 7) := by
  subst hq
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := by rw [hLh_eq]; exact Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by
    rw [hLh_eq, ← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlc_ge1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hlc_nn : 0 ≤ 1 + Real.log c := zero_le_one.trans hlc_ge1
  have hLν0 : 0 ≤ L ^ ν := Real.rpow_nonneg hL0.le _
  have hLmν0 : 0 ≤ L ^ (-ν) := Real.rpow_nonneg hL0.le _
  have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hα8 : α < 1 / 8 := by linarith
  have h1_invL : 1 / L ≤ L ^ (-ν) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h1_invLh : 1 / Lh ≤ L ^ (-ν) := by
    rw [hLh_eq, one_div, ← Real.rpow_neg hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hH₀_div : (1 + Real.log (R₀ : ℝ)) / L ≤ 2 / Lh := by
    rw [div_le_div_iff₀ hL0 hLh0]
    calc
      (1 + Real.log (R₀ : ℝ)) * Lh ≤ (2 * Lh) * Lh := mul_le_mul_of_nonneg_right hH₀_ub hLh0.le
      _ = 2 * (Lh * Lh) := by ring
      _ = 2 * L := by rw [hLh_sq]
  have hc2_vc_Lh : c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (-ν) := by
    have h1 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 2 1 (2 * α + ν) (by push_cast; linarith)
    rw [pow_one] at h1
    calc c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (2 * α + ν) / L ^ (1 / 2 : ℝ) := by
          rw [← hLh_eq]; exact div_le_div_of_nonneg_right h1 hLh0.le
      _ ≤ L ^ (-ν) := rpow_div_rpow_le hL1 (by linarith)
  have hc2_vc_L : c ^ 2 * (1 + Real.log c) / L ≤ L ^ (-ν) :=
    (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg c) hlc_nn) hLh0
      (by nlinarith only [hLh1, hLh_sq])).trans hc2_vc_Lh
  have hc4_vc : c ^ 4 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
    have h1 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 4 1 (4 * α + ν) (by push_cast; linarith)
    rw [pow_one] at h1
    calc c ^ 4 * (1 + Real.log c) / L ≤ L ^ (4 * α + ν) / L ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact div_le_div_of_nonneg_right h1 hL0.le
      _ ≤ L ^ (-ν) := rpow_div_rpow_le hL1 (by linarith)
  have hc7_L : c ^ 7 / L ≤ L ^ (-ν) := by
    have h1 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 7 0 (7 * α) (by push_cast; linarith)
    rw [pow_zero, mul_one] at h1
    calc c ^ 7 / L ≤ L ^ (7 * α) / L ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact div_le_div_of_nonneg_right h1 hL0.le
      _ ≤ L ^ (-ν) := rpow_div_rpow_le hL1 (by linarith)
  -- 1. Band 0 smallness
  have hout1 : C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have hmid_Q₁ : c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤ 2 * L ^ (-ν) := by
      have hc32 : c * Real.sqrt c ≤ L ^ ((3 / 2 : ℝ) * α) := by
        have hsq : (c * Real.sqrt c) ^ 2 ≤ (L ^ ((3 / 2 : ℝ) * α)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc0.le, show c ^ 2 * c = c ^ 3 by ring,
            ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le]
          have h3 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 3 0 (3 * α) (by push_cast; linarith)
          rw [pow_zero, mul_one] at h3
          exact h3.trans_eq (by congr 1; push_cast; ring)
        have hp1 : 0 ≤ c * Real.sqrt c := mul_nonneg hc0.le (Real.sqrt_nonneg c)
        have hp2 : 0 ≤ L ^ ((3 / 2 : ℝ) * α) := Real.rpow_nonneg hL0.le _
        nlinarith only [hsq, hp1, hp2]
      have hden_pos : 0 < (1 / 2 : ℝ) * L ^ ((α + 1 / 4) / 2) :=
        mul_pos (by norm_num) (Real.rpow_pos_of_pos hL0 _)
      calc
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤
            (L ^ ((3 / 2 : ℝ) * α) * L ^ ν) / ((1 / 2 : ℝ) * L ^ ((α + 1 / 4) / 2)) :=
          (div_le_div_of_nonneg_right
            (mul_le_mul hc32 hVc hlc_nn (Real.rpow_nonneg hL0.le _))
            (Real.sqrt_nonneg _)).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg (Real.rpow_nonneg hL0.le _) hLν0) hden_pos hsqrtQ)
        _ = 2 * L ^ ((3 / 2 : ℝ) * α + ν - (α + 1 / 4) / 2) := by
          rw [show (L ^ ((3 / 2 : ℝ) * α) * L ^ ν) / ((1 / 2 : ℝ) * L ^ ((α + 1 / 4) / 2)) =
            2 * ((L ^ ((3 / 2 : ℝ) * α) * L ^ ν) / L ^ ((α + 1 / 4) / 2)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_sub hL0]
        _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) zero_le_two
    have ht4 : c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L ≤ 2 * L ^ (-ν) := by
      calc
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L =
            c ^ 2 * (1 + Real.log c) * ((1 + Real.log R₀) / L) := by ring
        _ ≤ c ^ 2 * (1 + Real.log c) * (2 / Lh) :=
          mul_le_mul_of_nonneg_left hH₀_div (mul_nonneg (sq_nonneg c) hlc_nn)
        _ = 2 * (c ^ 2 * (1 + Real.log c) / Lh) := by ring
        _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left hc2_vc_Lh zero_le_two
    have hlogR₀_nn : 0 ≤ 1 + Real.log (R₀ : ℝ) := by linarith [Real.log_natCast_nonneg R₀]
    have ht1 : c * (1 + Real.log c) * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) := by
      have hm : c * (1 + Real.log c) ≤ c ^ 2 * (1 + Real.log c) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hc1]) hlc_nn
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm hlogR₀_nn) hL0.le).trans
        ((by ring : c ^ 2 * (1 + Real.log c) * (1 + Real.log R₀) / L =
          c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L).trans_le ht4)
    have ht2 : c * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc0.le hlc_ge1) hlogR₀_nn) hL0.le).trans ht1
    have ht3 : c ^ 2 / L ≤ L ^ (-ν) :=
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg c) hlc_ge1) hL0.le).trans
        hc2_vc_L
    have ht5 : c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) ≤ L ^ (-ν) := by
      calc
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) = c ^ 2 * ((R₀ : ℝ) * Real.sqrt (L / N)) := by ring
        _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR₀_tail (sq_nonneg c)
        _ = c ^ 2 / L := by ring
        _ ≤ L ^ (-ν) := ht3
    have ht6 : c ^ 5 * L / N ≤ L ^ (-ν) := hc5N.trans h1_invL
    have ht8 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ L ^ (-ν) := hc3R₀4.trans h1_invL
    have hsum18 : c * (1 + Real.log c) * (1 + Real.log R₀) / L +
        c * (1 + Real.log R₀) / L + c ^ 2 / L +
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
        c ^ 5 * L / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
        c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L ≤ 18 * L ^ (-ν) := by
      linarith only [ht1, ht2, ht3, ht4, ht5, ht6, hmid_Q₁, ht8, hc2_vc_L, hLmν0]
    calc
      _ ≤ C_small0 * (18 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum18 hC_small0.le
      _ = (C_small0 * 18) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b1 hLmν0
      _ = 1 := hmul_ν
  -- 2. Cross (u₀, u₁) smallness
  have hout2 : C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 := by
    have hc3_N : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ L ^ (-ν) := hc3R₀2.trans h1_invL
    have hsum4 : 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ 4 * L ^ (-ν) := by
      linarith only [h1_invLh, hc2_vc_Lh, hc4_vc, hc3_N]
    calc
      _ ≤ C_cross01 * (4 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum4 hC_cross01.le
      _ = (C_cross01 * 4) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_b2 hLmν0
      _ = 1 := hmul_ν
  -- 3. Band 0 floor
  have hout3 : κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 := by
    have hlogc : Real.log c ≤ α * Real.log L :=
      (Real.log_le_log hc0 hcup).trans_eq (Real.log_rpow hL0 α)
    have hq_scaled : (3 / 4 : ℝ) * (α + 1 / 4) * Real.log L - 3 / 4 ≤
        (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hlogQ_lb (by norm_num : (0 : ℝ) ≤ 3 / 4)
      linarith only [hm]
    linarith only [hlogc, hq_scaled, hll_scaled]
  -- 4. Band 1 floor with the reserve `√L/32`
  have hout4 : κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
    have hc2_Lh : C_band1 * c ^ 2 * (1 + Real.log c) ≤ Lh / 32 := by
      have h1 : (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ 1 := by
        calc
          (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ L ^ ν * L ^ (-ν) :=
            mul_le_mul hν_b6 hc2_vc_Lh
              (div_nonneg (mul_nonneg (sq_nonneg c) hlc_nn) hLh0.le) hLν0
          _ = 1 := hmul_ν
      have hm := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ Lh / 32)
      have hid : (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) * (Lh / 32) =
          C_band1 * c ^ 2 * (1 + Real.log c) := by field_simp
      linarith only [hm, hid]
    have hLh_lb : 8 * (κ₀ + 3) ≤ Lh := by
      have hsq : (8 * (κ₀ + 3)) ^ 2 ≤ Lh ^ 2 := by rw [sq Lh, hLh_sq]; exact hL_Lh_gap
      have hp : 0 ≤ 8 * (κ₀ + 3) := by linarith only [hκ₀]
      nlinarith only [hsq, hp, hLh0]
    linarith only [hlogR₀_lb, hc2_Lh, hLh_lb, hκ₀]
  -- 5 & 6. Band 2 floors with the reserve `3bk/(16c⁷)`
  have hc7 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
  have hk0 : 0 < θ₁ * L / (2 * D) := by positivity
  have hout5 : κ₀ + 2 + 3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7) ≤ θ₁ * L / (2 * D) / 8 := by
    have hres : 3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7) ≤ (3 / 128) * (θ₁ * L / (2 * D)) := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 3 * b ≤ 3 / 8 := by linarith only [hb8]
      have h2 : (3 / 128 : ℝ) * (θ₁ * L / (2 * D)) * (16 * c ^ 7) =
          (3 / 8) * (θ₁ * L / (2 * D)) * c ^ 7 := by ring
      rw [h2]
      have h3 : 3 * b * (θ₁ * L / (2 * D)) ≤ (3 / 8) * (θ₁ * L / (2 * D)) :=
        mul_le_mul_of_nonneg_right h1 hk0.le
      have h4 : (3 / 8) * (θ₁ * L / (2 * D)) ≤ (3 / 8) * (θ₁ * L / (2 * D)) * c ^ 7 :=
        le_mul_of_one_le_right (by positivity) hc7
      linarith only [h3, h4]
    have hfl : κ₀ + 2 ≤ (θ₁ * L / (2 * D)) / 16 := by
      have h1 : 32 * D * (κ₀ + 2) ≤ θ₁ * L := by
        have hh := (div_le_iff₀ hθ₁).mp hL_w
        linarith only [hh]
      rw [le_div_iff₀ (by norm_num), le_div_iff₀ (by positivity)]
      linarith only [h1]
    linarith only [hres, hfl, hk0]
  have hout6 : κ₀ + 2 + 3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7) ≤
      3 * b * (θ₁ * L / (2 * D)) / (8 * c ^ 7) := by
    have h1 : (32 * D * (κ₀ + 2) / (3 * b * θ₁)) * (c ^ 7 / L) ≤ 1 := by
      calc
        (32 * D * (κ₀ + 2) / (3 * b * θ₁)) * (c ^ 7 / L) ≤ L ^ ν * L ^ (-ν) :=
          mul_le_mul hν_b7 hc7_L (div_nonneg (pow_nonneg hc0.le 7) hL0.le) hLν0
        _ = 1 := hmul_ν
    have h2 : κ₀ + 2 ≤ 3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7) := by
      have hm := mul_le_mul_of_nonneg_right h1
        (by positivity : (0 : ℝ) ≤ 3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7))
      have hid : (32 * D * (κ₀ + 2) / (3 * b * θ₁)) * (c ^ 7 / L) *
          (3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7)) = κ₀ + 2 := by
        field_simp; ring
      linarith only [hm, hid]
    have e : 3 * b * (θ₁ * L / (2 * D)) / (8 * c ^ 7) =
        2 * (3 * b * (θ₁ * L / (2 * D)) / (16 * c ^ 7)) := by field_simp; ring
    linarith only [h2, e]
  exact ⟨hout1, hout2, hout3, hout4, hout5, hout6⟩

/-! ### Side conditions at the polynomial cutoff -/

/-- `(log N)¹⁸ ⌊N^θ⌋¹⁶ ≤ N` for `θ ≤ 1/4096` once `log N ≤ N^{1/36}`. -/
theorem log_pow_mul_floor_rpow_pow_le {N : ℕ} {θ : ℝ} (hN1 : 1 ≤ N) (hθ : 0 < θ)
    (hθ4096 : θ ≤ 1 / 4096) (hL0 : 0 ≤ Real.log N)
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ)) :
    Real.log N ^ 18 * (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ^ 16 ≤ N := by
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hR : (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ (N : ℝ) ^ θ := Nat.floor_le (by positivity)
  have h1 : (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ^ 16 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ^ 16 ≤ ((N : ℝ) ^ θ) ^ 16 := pow_le_pow_left₀ (by positivity) hR 16
      _ = (N : ℝ) ^ (16 * θ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
  have h2 : Real.log N ^ 18 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc Real.log N ^ 18 ≤ ((N : ℝ) ^ (1 / 36 : ℝ)) ^ 18 := pow_le_pow_left₀ hL0 hLX 18
      _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  calc Real.log N ^ 18 * (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ^ 16 ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = N := by rw [← Real.rpow_add hN0]; norm_num

/-- The near-row ceiling, `8c ≤ N` and `c⁴ ≤ N` from `(log N)¹⁸ R¹⁶ ≤ N`. -/
theorem near_ceil_side_conditions {R N : ℕ} {c : ℝ} (hR1 : 1 ≤ R) (hc1 : 1 ≤ c)
    (hcL : c ≤ Real.log N) (hL2 : 2 ≤ Real.log N)
    (hRN : Real.log N ^ 18 * (R : ℝ) ^ 16 ≤ N) :
    ⌈linearNearRowRadius c⌉₊ + 1 ≤ N ∧ R * R ≤ N / (⌈linearNearRowRadius c⌉₊ + 1) ∧
      8 * c ≤ N ∧ c ^ 4 ≤ N := by
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have hR1R : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  have hL17 : (2 : ℝ) ^ 17 ≤ L ^ 17 := pow_le_pow_left₀ (by norm_num) hL2 17
  have hL18 : L ^ 18 ≤ N := by
    have : L ^ 18 ≤ L ^ 18 * (R : ℝ) ^ 16 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hR1R)
    linarith
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hrad : linearNearRowRadius c ≤ 18 * L := by
    unfold linearNearRowRadius
    have he2 : Real.exp 2 ≤ 9 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
    nlinarith
  have hceil : ((⌈linearNearRowRadius c⌉₊ + 1 : ℕ) : ℝ) ≤ 18 * L + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ linearNearRowRadius c by
      unfold linearNearRowRadius; positivity)
    push_cast; linarith
  have hbig : 18 * L + 2 ≤ L ^ 18 := by
    have : L ^ 18 = L * L ^ 17 := by ring
    nlinarith
  have hprod : ((R * R * (⌈linearNearRowRadius c⌉₊ + 1) : ℕ) : ℝ) ≤ N := by
    push_cast
    have hRR : (R : ℝ) * R ≤ (R : ℝ) ^ 16 := by
      rw [← sq]; exact pow_le_pow_right₀ hR1R (by norm_num)
    have hc0 : (0 : ℝ) ≤ (⌈linearNearRowRadius c⌉₊ : ℝ) + 1 := by positivity
    have hceil' : (⌈linearNearRowRadius c⌉₊ : ℝ) + 1 ≤ L ^ 18 := by
      have := hceil; push_cast at this; linarith
    calc (R : ℝ) * R * ((⌈linearNearRowRadius c⌉₊ : ℝ) + 1) ≤ (R : ℝ) ^ 16 * L ^ 18 :=
          mul_le_mul hRR hceil' hc0 (by positivity)
      _ ≤ N := by linarith
  have hprodN : R * R * (⌈linearNearRowRadius c⌉₊ + 1) ≤ N := by exact_mod_cast hprod
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hRR1 : 1 ≤ R * R := Nat.one_le_iff_ne_zero.mpr (by positivity)
    calc ⌈linearNearRowRadius c⌉₊ + 1 = 1 * (⌈linearNearRowRadius c⌉₊ + 1) := (one_mul _).symm
      _ ≤ R * R * (⌈linearNearRowRadius c⌉₊ + 1) := Nat.mul_le_mul_right _ hRR1
      _ ≤ N := hprodN
  · exact (Nat.le_div_iff_mul_le (by omega)).mpr hprodN
  · nlinarith
  · have h4 : c ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by linarith) hcL 4
    have : L ^ 4 ≤ L ^ 18 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith

/-- `N / (N / T) ≤ 2T` for `1 ≤ T ≤ N`. -/
theorem nat_div_div_le_two_mul {N T : ℕ} (hT : 1 ≤ T) (hTN : T ≤ N) :
    (N : ℝ) / (N / T : ℕ) ≤ 2 * T := by
  have hM1 : 1 ≤ N / T := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hM0 : (0 : ℝ) < (N / T : ℕ) := by exact_mod_cast hM1
  rw [div_le_iff₀ hM0]
  have h1 : N < (N / T + 1) * T := by
    simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < T by omega)
  have h2 : ((N : ℕ) : ℝ) < (((N / T : ℕ) : ℝ) + 1) * T := by exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ (N / T : ℕ) := by exact_mod_cast hM1
  nlinarith

/-- The totient ratio budget `Sg = K (1 + log (1 + log R₁))`. -/
theorem div_totient_le_loglog_of_le {K : ℝ} (hK : 1 ≤ K)
    (htot : ∀ m : ℕ, 1 ≤ m → (m : ℝ) / m.totient ≤ K * (1 + Real.log (1 + Real.log m)))
    {R R₁ : ℕ} (hRR₁ : R ≤ R₁) :
    ∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ K * (1 + Real.log (1 + Real.log R₁)) := by
  intro m hm
  obtain ⟨h2, hmR⟩ := mem_Icc.mp hm
  refine (htot m (by omega)).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hmR₁ : (m : ℝ) ≤ R₁ := by exact_mod_cast hmR.trans hRR₁
  have hl : Real.log m ≤ Real.log R₁ := Real.log_le_log (by linarith) hmR₁
  have hl0 : 0 ≤ Real.log m := Real.log_nonneg hm1
  have := Real.log_le_log (by linarith) (show 1 + Real.log m ≤ 1 + Real.log R₁ by linarith)
  linarith

/-- The totient budget is at most `2K (1 + log L)` when `1 + log R₁ ≤ L`. -/
theorem loglog_budget_le {K L : ℝ} {R₁ : ℕ} (hK : 0 ≤ K) (hL1 : 1 ≤ L)
    (hlog : 1 + Real.log R₁ ≤ L) :
    K * (1 + Real.log (1 + Real.log R₁)) ≤ 2 * K * (1 + Real.log L) := by
  have hl0 : 0 ≤ Real.log R₁ := Real.log_natCast_nonneg R₁
  have h1 := Real.log_le_log (by linarith) hlog
  have hlL : 0 ≤ Real.log L := Real.log_nonneg hL1
  nlinarith

/-- The pole-mode residual rate: `‖r₁‖² ≤ K (c² (1 + log c)³ L^{1/k}/L + c¹⁰ (L/N)²)
≤ 2K c² (1 + log c)³ L^ν / L` for `1/k ≤ ν`, `c ≤ L`, `L¹¹ ≤ N`. -/
theorem pole_rate_le {K c L ν : ℝ} {N k : ℕ} (hK : 0 ≤ K) (hc1 : 1 ≤ c) (hcL : c ≤ L)
    (hL1 : 1 ≤ L) (hk : 1 ≤ k) (hkν : 1 / (k : ℝ) ≤ ν) (hL11 : L ^ 11 ≤ N) :
    K * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L + c ^ 10 * (L / N) ^ 2) ≤
      2 * K * (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L) := by
  have hL0 : 0 < L := by linarith
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hL11
  have hlc : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hpow : L ^ (1 / (k : ℝ)) ≤ L ^ ν := Real.rpow_le_rpow_of_exponent_le hL1 hkν
  have hpow1 : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hsub : c ^ 10 * (L / N) ^ 2 ≤ c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L := by
    have h8 : c ^ 8 * (L / N) ^ 2 ≤ 1 / L := by
      rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) hL0, one_mul]
      have hc8 : c ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ hc0.le hcL 8
      have hN1 : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ hL1) hL11
      calc c ^ 8 * L ^ 2 * L ≤ L ^ 8 * L ^ 2 * L := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc8 (by positivity))
              hL0.le
        _ = L ^ 11 := by ring
        _ ≤ N := hL11
        _ ≤ (N : ℝ) ^ 2 := by nlinarith
    have h1 : 1 ≤ (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hlc) hpow1
    calc c ^ 10 * (L / N) ^ 2 = c ^ 2 * (c ^ 8 * (L / N) ^ 2) := by ring
      _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left h8 (sq_nonneg c)
      _ = c ^ 2 * 1 / L := by ring
      _ ≤ c ^ 2 * ((1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ))) / L :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (sq_nonneg c)) hL0.le
      _ = c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L := by ring
  have hmain : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L ≤
      c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hL0.le
  have := mul_le_mul_of_nonneg_left (add_le_add (hmain) (hsub.trans hmain)) hK
  linarith

/-! ### The band–far cross at the cutoffs -/

/-- **The band–far cross at the polynomial cutoffs.** For a band `R ≤ R₁` with the cutoff
geometry of `R` (`R⁶ ≤ N`, `36 (1 + log R) ≤ L`, near/upward size conditions, `R² ≤ N/T`) and
`(log N)¹⁸ R₁¹⁶ ≤ N`, the cross with `w ∈ V_{R₁}^⊥` costs `E/32 + ‖u‖²/4 + (k/32) P + (bk/(32c⁷))(S + ‖w‖²)`,
`k = θ L/(2D)`, once the totient budget `Sg ≤ L^ν`, the pole rate `ρ ≤ Kρ c² (1 + log c)³ L^ν/L` and
the two exponent conditions `8α + 4ν ≤ 1`, `11α + 6ν ≤ 2` hold. -/
theorem exists_band_far_cross_le_at_cutoff :
    ∃ C_pr C_up C_upT C_np : ℝ, 0 < C_pr ∧ 0 ≤ C_up ∧ 0 ≤ C_upT ∧ 0 ≤ C_np ∧
      ∀ {R R₁ N : ℕ} {c α ν ρ Sg θ D b CB Kρ : ℝ}, 2 ≤ R → R ≤ R₁ → R ^ 6 ≤ N →
        36 * (1 + Real.log R) ≤ Real.log N → 3000 ≤ Real.log N → 1 ≤ c →
        c ≤ Real.log N ^ α → 0 ≤ α → α ≤ 1 →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        R * R ≤ N / linearDefectCutoff c → linearDefectCutoff c ≤ N →
        terminalPacketCost R (N / linearDefectCutoff c) N ≤ CB * (1 + Real.log c) →
        1 + Real.log R ≤ 2 * θ * Real.log N →
        Real.log N ^ 18 * (R₁ : ℝ) ^ 16 ≤ N →
        ‖poleModeResidual c N‖ ^ 2 ≤ ρ →
        ρ ≤ Kρ * (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ ν / Real.log N) →
        1 ≤ Sg → (∀ m ∈ Icc 2 R, (m : ℝ) / m.totient ≤ Sg) → Sg ≤ Real.log N ^ ν →
        1 + Real.log c ≤ Real.log N ^ ν → 0 < ν → 8 * α + 4 * ν ≤ 1 → 11 * α + 6 * ν ≤ 2 →
        0 < θ → 0 < D → 0 < b → 0 ≤ CB → 0 ≤ Kρ →
        1024 * D * C_pr * θ ≤ 1 / 64 →
        (512 * D * C_pr * CB / b + 512 * D * C_np / b) * Real.log N ^ (-ν) ≤ 1 / 64 →
        (1024 * D * C_pr + 1024 * D * C_pr / b +
          64 * D * C_np * (4 * θ ^ 2 * Kρ + 880 + 16 * θ) / (b * θ) + 256 * D * C_up / θ +
          512 * D * C_upT * (256 * Real.exp 2 + 4) / (b * θ)) * Real.log N ^ (-ν) ≤ 1 / 4 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R a +
            (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
            (θ * Real.log N / (2 * D) / 32) *
              (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
            (b * (θ * Real.log N / (2 * D)) / (32 * c ^ 7)) *
              (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
            (b * (θ * Real.log N / (2 * D)) / (32 * c ^ 7)) * ‖w‖ ^ 2 := by
  obtain ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, hspec⟩ :=
    exists_band_far_cross_le_reserve_of_monomials
  refine ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, ?_⟩
  intro R R₁ N c α ν ρ Sg θ D b CB Kρ hR2 hRR₁ hR6 h36 hL3000 hc1 hcup hα0 hα1 hsize_near hsize_up hrad
    hRM hTN hB_ub hlR hRN₁ hρ hρK hSg1 hSg hSgν hVc hν h8 h11 hθ hD hb hCB hKρ hθs hσE hσU a hu w hw
  set L := Real.log (N : ℝ) with hLdef
  have hL1 : 1 ≤ L := by linarith only [hL3000]
  have hL0 : 0 < L := by linarith only [hL3000]
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL1 hα1)
  have hRN : L ^ 18 * (R : ℝ) ^ 16 ≤ N := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hRN₁
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hRR₁) 16
  obtain ⟨hceil, hRK, h8c, hc4⟩ :=
    near_ceil_side_conditions (by omega : 1 ≤ R) hc1 hcL (by linarith only [hL3000]) hRN
  obtain ⟨hT3, -, -, hTup⟩ := linearDefectCutoff_bounds hc1
  have hM1 : 1 ≤ N / linearDefectCutoff c :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hRM
  have hNM : (N : ℝ) / (N / linearDefectCutoff c : ℕ) ≤ 2 * (256 * Real.exp 2 + 4) * c := by
    have h1 := nat_div_div_le_two_mul (by omega : 1 ≤ linearDefectCutoff c) hTN
    linarith only [h1, hTup]
  obtain ⟨hm1, hm2⟩ := band_far_monomials_le hL1 hc1 hcup hVc (by linarith only [hSg1]) hSgν h8 h11
  have hLσ : 1 / L ≤ L ^ (-ν) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [h8, hα0])
  have h18 : 18 * (1 + Real.log (R : ℝ)) ≤ L := by
    linarith only [h36, Real.log_natCast_nonneg R]
  exact hspec hR2 (by exact_mod_cast hR6) hM1 (Nat.div_le_self _ _) h18 hc1 h8c hc4 hsize_near
    hsize_up hrad hceil hRK hSg1 hSg hρ hL1 hcL hθ hD hb hCB (by positivity) hKρ
    (Real.one_le_rpow hL1 hν.le) hlR hRN hρK hB_ub hNM hm1 hm2 hLσ hθs hσE hσU a hu
    (fun v hv => hw v (conductorSubspace_mono hRR₁ N hv))

/-- The two-region reserve below `1/8` in the assembly shape `k/4`, `bk/(2c⁷)`
(`k = θ L/(2D)`, `b ≤ gD/(2θ)`). -/
theorem two_region_reserve_assembly_shape {R N : ℕ} {c θ D g b : ℝ} (hc1 : 1 ≤ c) (hθ : 0 < θ)
    (hD : 0 < D) (hg : 0 < g) (hb : 0 < b) (hbg : b ≤ g * D / (2 * θ))
    (htwo : ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace R N)ᗮ →
      θ / (8 * D) * Real.log (N : ℝ) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
        g / (8 * c ^ 7) * Real.log (N : ℝ) *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) ≤
        completeWeilEnergy tiltedUnitSpline c N z) :
    ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
      (θ * Real.log N / (2 * D) / 4) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
        (b * (θ * Real.log N / (2 * D)) / (2 * c ^ 7)) *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) ≤
        completeWeilEnergy tiltedUnitSpline c N w := by
  intro w hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have h := htwo hw
  have hS0 : 0 ≤ ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have e1 : θ * Real.log N / (2 * D) / 4 = θ / (8 * D) * Real.log N := by field_simp; ring
  have hbθ : b * θ ≤ g * D / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hbg hθ.le
    have e : g * D / (2 * θ) * θ = g * D / 2 := by field_simp
    linarith only [h1, e]
  have e2 : b * (θ * Real.log N / (2 * D)) / (2 * c ^ 7) ≤ g / (8 * c ^ 7) * Real.log N := by
    have key : b * (θ * Real.log N / (2 * D)) / (2 * c ^ 7) =
        (b * θ) * (Real.log N / (4 * D * c ^ 7)) := by field_simp; ring
    have key2 : g / (8 * c ^ 7) * Real.log N = (g * D / 2) * (Real.log N / (4 * D * c ^ 7)) := by
      field_simp; ring
    rw [key, key2]
    exact mul_le_mul_of_nonneg_right hbθ (by positivity)
  have h3 := mul_le_mul_of_nonneg_right e2 hS0
  rw [e1]
  linarith only [h, h3]

/-! ### Complement coercivity with block reserves below the eighth root -/

/-- **Complement coercivity with block reserves below the eighth root.** For `0 < α < 1/8`, with
`Q₁ = ⌊L^{α+1/4}⌋`, `R₀ = ⌊exp √L⌋`, `R₁ = ⌊N^{θ₁}⌋` (`L = log N`), eventually in `N` and
uniformly across `1 ≤ c ≤ L^α`, every `u₀ ∈ V_{R₀} ∩ V_{Q₁}^⊥`, `u₁ ∈ V_{R₁} ∩ V_{R₀}^⊥`,
`w ∈ V_{R₁}^⊥` satisfy
`(κ₀ + 3)‖u₀‖² + (κ₀ + 2 + √L/32)‖u₁‖² + (κ₀ + 2 + 3bk/(16c⁷))‖w‖² ≤ E(u₀ + u₁ + w)`,
`k = θ₁ L/(2D)`: the two-region reserve on `V_{R₁}^⊥` below `1/8` and the band–far cross below
`1/8` replace their `c⁹` counterparts in the three-band assembly. -/
theorem exists_complement_block_reserves_below_one_eighth {α : ℝ} (hα : 0 < α)
    (hα8 : α < 1 / 8) :
    ∃ θ₁ b : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 / 4096 ∧ 0 < b ∧ b ≤ 1 / 8 ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
        ∀ {u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N →
          u₀ ∈ (conductorSubspace ⌊Real.log (N : ℝ) ^ (α + 1 / 4)⌋₊ N)ᗮ →
          u₁ ∈ conductorSubspace ⌊(N : ℝ) ^ θ₁⌋₊ N →
          u₁ ∈ (conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N)ᗮ →
          w ∈ (conductorSubspace ⌊(N : ℝ) ^ θ₁⌋₊ N)ᗮ →
          (tiltedSplineSpectralFloorConstant + 3) * ‖u₀‖ ^ 2 +
              (tiltedSplineSpectralFloorConstant + 2 + Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) *
                ‖u₁‖ ^ 2 +
              (tiltedSplineSpectralFloorConstant + 2 +
                3 * b * (θ₁ * Real.log (N : ℝ) / (2 * explicitConductorCutoffConstant)) /
                  (16 * c ^ 7)) * ‖w‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N (u₀ + u₁ + w) := by
  obtain ⟨C_pr, C_up, C_upT, C_np, hCpr, hCup, hCupT, hCnp, hcross⟩ :=
    exists_band_far_cross_le_at_cutoff
  obtain ⟨C_cross01, hC_cross01, hcross01⟩ := exists_band0_band1_cross_le
  obtain ⟨C_coerc0, C_small0, hC_coerc0, hC_small0, hcoerc0⟩ :=
    exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
  obtain ⟨C_band1, hC_band1, hcoerc1⟩ := exists_band1_coercive_homogeneous
  obtain ⟨K_res, hK_res, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  obtain ⟨K_tot, hK_tot, htot⟩ := exists_div_totient_le_loglog
  have hD : 0 < explicitConductorCutoffConstant := explicitConductorCutoffConstant_pos
  have hg : 0 < growingMassConstant := growingMassConstant_pos
  have hκ₀ : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
  obtain ⟨D, hDdef⟩ : ∃ D, D = explicitConductorCutoffConstant := ⟨_, rfl⟩
  obtain ⟨κ₀, hκ₀def⟩ : ∃ κ₀, κ₀ = tiltedSplineSpectralFloorConstant := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  rw [← hκ₀def] at hκ₀ ⊢
  obtain ⟨θ₁, hθ₁def⟩ : ∃ θ₁ : ℝ, θ₁ = min (1 / 4096 : ℝ) (1 / (65536 * D * C_pr)) := ⟨_, rfl⟩
  have hθ₁ : 0 < θ₁ := hθ₁def ▸ lt_min (by norm_num) (by positivity)
  have hθ₁_4096 : θ₁ ≤ 1 / 4096 := hθ₁def ▸ min_le_left _ _
  have hθs : 1024 * D * C_pr * θ₁ ≤ 1 / 64 := by
    have h := hθ₁def ▸ min_le_right (1 / 4096 : ℝ) (1 / (65536 * D * C_pr))
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 1024 * D * C_pr)
    have e : 1024 * D * C_pr * (1 / (65536 * D * C_pr)) = 1 / 64 := by field_simp; norm_num
    linarith only [h2, e]
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = min (1 / 8 : ℝ) (growingMassConstant * D / (2 * θ₁)) :=
    ⟨_, rfl⟩
  have hb : 0 < b := hbdef ▸ lt_min (by norm_num) (by positivity)
  have hb8 : b ≤ 1 / 8 := hbdef ▸ min_le_left _ _
  have hbg : b ≤ growingMassConstant * D / (2 * θ₁) := hbdef ▸ min_le_right _ _
  refine ⟨θ₁, b, hθ₁, hθ₁_4096, hb, hb8, ?_⟩
  have hq : 0 < α + 1 / 4 := by linarith only [hα]
  have hq_hi : α + 1 / 4 ≤ 1 / 2 := by linarith only [hα8]
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = (1 - 8 * α) / 64 := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hνdef]; linarith only [hα8]
  have hν8 : 64 * ν ≤ 1 - 8 * α := by rw [hνdef]; linarith only
  have h8ν : 8 * α + 4 * ν ≤ 1 := by linarith only [hν8, hν, hα8]
  have h11ν : 11 * α + 6 * ν ≤ 2 := by linarith only [hν8, hν, hα8]
  obtain ⟨kv, hkvdef⟩ : ∃ kv : ℕ, kv = ⌈1 / ν⌉₊ + 1 := ⟨_, rfl⟩
  have hkv : 1 ≤ kv := by omega
  have hkvν : 1 / (kv : ℝ) ≤ ν := by
    have hceil := Nat.le_ceil (1 / ν)
    have hk0 : (0 : ℝ) < kv := by exact_mod_cast hkv
    rw [div_le_iff₀ hk0]
    have h1 : (1 / ν) + 1 ≤ (kv : ℝ) := by rw [hkvdef]; push_cast; linarith only [hceil]
    have h2 : ν * (1 / ν) = 1 := mul_one_div_cancel hν.ne'
    nlinarith only [h1, h2, hν]
  obtain ⟨CB, hCBdef⟩ : ∃ CB : ℝ, CB = 4 + Real.log (2 * (256 * Real.exp 2 + 4)) + 1 := ⟨_, rfl⟩
  have hCB : 0 ≤ CB := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (256 * Real.exp 2 + 4) by
      nlinarith only [Real.exp_pos 2])
    rw [hCBdef]; linarith only [this]
  have hKρ : 0 ≤ 2 * K_res := by positivity
  obtain ⟨XE, hXE⟩ : ∃ XE : ℝ, XE = 512 * D * C_pr * CB / b + 512 * D * C_np / b := ⟨_, rfl⟩
  obtain ⟨XU, hXU⟩ : ∃ XU : ℝ, XU = 1024 * D * C_pr + 1024 * D * C_pr / b +
      64 * D * C_np * (4 * θ₁ ^ 2 * (2 * K_res) + 880 + 16 * θ₁) / (b * θ₁) +
      256 * D * C_up / θ₁ + 512 * D * C_upT * (256 * Real.exp 2 + 4) / (b * θ₁) := ⟨_, rfl⟩
  have hXE0 : 0 ≤ XE := by rw [hXE]; positivity
  have hXU0 : 0 ≤ XU := by rw [hXU]; positivity
  have hm7 : 0 ≤ 32 * D * (κ₀ + 2) / (3 * b * θ₁) := by positivity
  have ht1 : 0 ≤ C_small0 * 18 := by positivity
  have ht2 : 0 ≤ C_cross01 * 4 := by positivity
  have ht3 : 0 ≤ 32 * C_band1 := by positivity
  have hgap_q : 0 < (3 / 4) * (α + 1 / 4) - α := by linarith only [hα8]
  have hM_L1 : 0 ≤ (8 * (κ₀ + 3)) ^ 2 := by positivity
  have hM_L2 : 0 ≤ 32 * D * (κ₀ + 2) / θ₁ := by positivity
  have hM_L3 : 0 ≤ (1 / θ₁) ^ 2 := by positivity
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [eventually_three_cutoff_bounds_one_ninth hq hq_hi hθ₁ hθ₁_4096,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν (2 * K_tot + 1)),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop
      (C_small0 * 18 + C_cross01 * 4 + 32 * C_band1 + 32 * D * (κ₀ + 2) / (3 * b * θ₁) +
        64 * XE + 4 * XU),
    hllim.eventually_ge_atTop ((κ₀ + 4 + C_coerc0 + 3 / 4) / ((3 / 4) * (α + 1 / 4) - α)),
    hLlim.eventually_ge_atTop (3000 + (8 * (κ₀ + 3)) ^ 2 + 32 * D * (κ₀ + 2) / θ₁ + (1 / θ₁) ^ 2),
    eventually_completeWeilEnergy_two_region_on_polynomialConductorOrthogonal_below_one_eighth
      hθ₁ (by linarith only [hθ₁_4096]) hα hα8,
    hres 0 le_rfl kv hkv,
    eventually_ge_atTop 3] with N hcut hLX hpoly hν_big hll_big hL_big htwo hresN hN3
  dsimp only [Function.comp_def] at hpoly hν_big hll_big hL_big
  intro c hc1 hcup u₀ u₁ w hu₀_mem hu₀_orthQ hu₁_mem hu₁_orthR₀ hw
  obtain ⟨hQ2, hQR₀, hR₀R₁, -, hsqrtQ, hlogQ_lb, hH₀_ub, hlogR₀_lb, h36_R₀,
    hH₁_ub, h1080_R₁, -⟩ := hcut
  have hL3000 : 3000 ≤ Real.log (N : ℝ) := by linarith only [hL_big, hM_L1, hM_L2, hM_L3]
  have hL_Lh_gap : (8 * (κ₀ + 3)) ^ 2 ≤ Real.log (N : ℝ) := by
    linarith only [hL_big, hM_L1, hM_L2, hM_L3]
  have hL_w : 32 * D * (κ₀ + 2) / θ₁ ≤ Real.log (N : ℝ) := by
    linarith only [hL_big, hM_L1, hM_L2, hM_L3]
  have hLθ : (1 / θ₁) ^ 2 ≤ Real.log (N : ℝ) := by linarith only [hL_big, hM_L1, hM_L2, hM_L3]
  have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hL3000]
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hL3000]
  have hN1 : 1 ≤ N := by omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ Real.log (N : ℝ) := hcup.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα8] : α ≤ 1))
  have hpoly1 : (2 * K_tot + 1) * (1 + Real.log (Real.log (N : ℝ))) ≤ Real.log (N : ℝ) ^ ν := by
    simpa only [pow_one] using hpoly
  have hlogL0 : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hL1
  have hVc : 1 + Real.log c ≤ Real.log (N : ℝ) ^ ν := by
    have h1 := Real.log_le_log hc0 hcL
    have h2 : 1 + Real.log (Real.log (N : ℝ)) ≤
        (2 * K_tot + 1) * (1 + Real.log (Real.log (N : ℝ))) :=
      le_mul_of_one_le_left (by linarith only [hlogL0]) (by linarith only [hK_tot])
    linarith only [h1, h2, hpoly1]
  have hR₀2 : 2 ≤ ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ := hQ2.trans hQR₀
  have hR₁2 : 2 ≤ ⌊(N : ℝ) ^ θ₁⌋₊ := hR₀2.trans hR₀R₁
  have h36_R₁ : 36 * (1 + Real.log (⌊(N : ℝ) ^ θ₁⌋₊ : ℝ)) ≤ Real.log (N : ℝ) := by
    linarith only [h1080_R₁, Real.log_natCast_nonneg ⌊(N : ℝ) ^ θ₁⌋₊]
  obtain ⟨hcutN, hwidth, hw1, hrad, hR₀6, hsize_near0, hsize_up0, hR₀_tail, hc5N, hc3R₀4, hc3R₀2,
    -⟩ := rpow_horizon_N_bounds_one_ninth hN1 hR₀2 hc1 (by linarith only [hL3000]) hLX hcL h36_R₀
  obtain ⟨-, -, -, -, hR₁6, hsize_near1, hsize_up1, hR₁_tail, -, -, -, -⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₁2 hc1 (by linarith only [hL3000]) hLX hcL h36_R₁
  obtain ⟨hRM0, -, hB0_ub, -⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₀2 hc1 hL3000 hLX hcL h36_R₀
  obtain ⟨hRM1, -, hB1_ub, -⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₁2 hc1 hL3000 hLX hcL h36_R₁
  rw [← hCBdef] at hB0_ub hB1_ub
  have hν_b1 : C_small0 * 18 ≤ Real.log (N : ℝ) ^ ν := by
    linarith only [hν_big, ht2, ht3, hm7, hXE0, hXU0]
  have hν_b2 : C_cross01 * 4 ≤ Real.log (N : ℝ) ^ ν := by
    linarith only [hν_big, ht1, ht3, hm7, hXE0, hXU0]
  have hν_b6 : 32 * C_band1 ≤ Real.log (N : ℝ) ^ ν := by
    linarith only [hν_big, ht1, ht2, hm7, hXE0, hXU0]
  have hν_b7 : 32 * D * (κ₀ + 2) / (3 * b * θ₁) ≤ Real.log (N : ℝ) ^ ν := by
    linarith only [hν_big, ht1, ht2, ht3, hXE0, hXU0]
  have hll_scaled : κ₀ + 4 + C_coerc0 + 3 / 4 ≤
      ((3 / 4 : ℝ) * (α + 1 / 4) - α) * Real.log (Real.log (N : ℝ)) :=
    ((div_le_iff₀ hgap_q).mp hll_big).trans_eq (mul_comm _ _)
  obtain ⟨hsmall_band0, hsmall_cross01, hfl0, hfl1, hfl2_P, hfl2_S⟩ :=
    complement_scalar_smallness_one_eighth hα hν hν8 rfl hc1 hcup hL1 rfl hb hθ₁ hD hκ₀
      hC_small0 hC_cross01 hVc hsqrtQ hlogQ_lb hH₀_ub hlogR₀_lb hR₀_tail hc5N hc3R₀4 hc3R₀2
      hν_b1 hν_b2 hν_b6 hν_b7 hll_scaled hL_Lh_gap hL_w hb8
  -- the band–far budgets
  have hLνσ : Real.log (N : ℝ) ^ ν * Real.log (N : ℝ) ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hσ0 : 0 ≤ Real.log (N : ℝ) ^ (-ν) := Real.rpow_nonneg hL0.le _
  have hσE : XE * Real.log (N : ℝ) ^ (-ν) ≤ 1 / 64 := by
    have h1 : 64 * XE ≤ Real.log (N : ℝ) ^ ν := by
      linarith only [hν_big, ht1, ht2, ht3, hm7, hXU0]
    have := mul_le_mul_of_nonneg_right h1 hσ0
    linarith only [this, hLνσ]
  have hσU : XU * Real.log (N : ℝ) ^ (-ν) ≤ 1 / 4 := by
    have h1 : 4 * XU ≤ Real.log (N : ℝ) ^ ν := by
      linarith only [hν_big, ht1, ht2, ht3, hm7, hXE0]
    have := mul_le_mul_of_nonneg_right h1 hσ0
    linarith only [this, hLνσ]
  rw [hXE] at hσE
  rw [hXU] at hσU
  -- the totient budget
  have hlR₁0 : 0 ≤ Real.log (⌊(N : ℝ) ^ θ₁⌋₊ : ℝ) := Real.log_natCast_nonneg _
  have hSg1 : 1 ≤ K_tot * (1 + Real.log (1 + Real.log (⌊(N : ℝ) ^ θ₁⌋₊ : ℝ))) := by
    have : 0 ≤ Real.log (1 + Real.log (⌊(N : ℝ) ^ θ₁⌋₊ : ℝ)) :=
      Real.log_nonneg (by linarith only [hlR₁0])
    exact one_le_mul_of_one_le_of_one_le hK_tot (by linarith only [this])
  have hSgν : K_tot * (1 + Real.log (1 + Real.log (⌊(N : ℝ) ^ θ₁⌋₊ : ℝ))) ≤
      Real.log (N : ℝ) ^ ν := by
    have h2θ : 2 * θ₁ * Real.log (N : ℝ) ≤ Real.log (N : ℝ) := by
      have := mul_le_mul_of_nonneg_right (show 2 * θ₁ ≤ 1 by linarith only [hθ₁_4096]) hL0.le
      linarith only [this]
    have h3 := loglog_budget_le (by linarith only [hK_tot] : (0 : ℝ) ≤ K_tot) hL1
      (hH₁_ub.trans h2θ)
    have h4 : (2 * K_tot + 1) * (1 + Real.log (Real.log (N : ℝ))) =
        2 * K_tot * (1 + Real.log (Real.log (N : ℝ))) + (1 + Real.log (Real.log (N : ℝ))) := by
      ring
    linarith only [h3, h4, hpoly1, hlogL0]
  -- the pole-mode residual
  have hRN₁ := log_pow_mul_floor_rpow_pow_le hN1 hθ₁ hθ₁_4096 hL0.le hLX
  have hL11 : Real.log (N : ℝ) ^ 11 ≤ N := by
    refine le_trans ?_ hRN₁
    have h1 : Real.log (N : ℝ) ^ 11 ≤ Real.log (N : ℝ) ^ 18 := pow_le_pow_right₀ hL1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (⌊(N : ℝ) ^ θ₁⌋₊ : ℝ) ^ 16 :=
      one_le_pow₀ (by exact_mod_cast (show 1 ≤ ⌊(N : ℝ) ^ θ₁⌋₊ by omega))
    exact h1.trans (le_mul_of_one_le_right (by positivity) h2)
  have hρ : ‖poleModeResidual c N‖ ^ 2 ≤
      K_res * (c ^ 2 * (1 + Real.log c) ^ 3 * Real.log (N : ℝ) ^ (1 / (kv : ℝ)) /
        Real.log (N : ℝ) + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
    have h := hresN 1 one_pos (by simp) c hc1 hwidth
    simpa only [poleModeResidual, Nat.cast_one, Real.log_one, add_zero, one_pow, one_mul,
      mul_one] using h
  have hρK := pole_rate_le hK_res.le hc1 hcL hL1 hkv hkvν hL11
  -- the cross payments
  have hlR₀ : 1 + Real.log (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ) ≤
      2 * θ₁ * Real.log (N : ℝ) := by
    have hsq : Real.log (N : ℝ) ^ (1 / 2 : ℝ) * Real.log (N : ℝ) ^ (1 / 2 : ℝ) = Real.log N := by
      rw [← Real.rpow_add hL0]; norm_num
    have hLh0 : 0 < Real.log (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have h1 : 1 / θ₁ ≤ Real.log (N : ℝ) ^ (1 / 2 : ℝ) := by
      have hsq' : (1 / θ₁) ^ 2 ≤ (Real.log (N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [sq (Real.log (N : ℝ) ^ _), hsq]; exact hLθ
      exact (pow_le_pow_iff_left₀ (by positivity) hLh0.le (by norm_num)).mp hsq'
    have h2 : 1 ≤ θ₁ * Real.log (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hθ₁] at h1; linarith only [h1]
    have hLh : Real.log (N : ℝ) ^ (1 / 2 : ℝ) ≤ θ₁ * Real.log N :=
      calc Real.log (N : ℝ) ^ (1 / 2 : ℝ) = Real.log (N : ℝ) ^ (1 / 2 : ℝ) * 1 := (mul_one _).symm
        _ ≤ Real.log (N : ℝ) ^ (1 / 2 : ℝ) * (θ₁ * Real.log (N : ℝ) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hLh0.le
        _ = θ₁ * (Real.log (N : ℝ) ^ (1 / 2 : ℝ) * Real.log (N : ℝ) ^ (1 / 2 : ℝ)) := by ring
        _ = θ₁ * Real.log N := by rw [hsq]
    linarith only [hH₀_ub, hLh]
  have hcr0w := hcross hR₀2 hR₀R₁ hR₀6 h36_R₀ hL3000 hc1 hcup hα.le (by linarith only [hα8])
    hsize_near0 hsize_up0 hrad hRM0 hcutN hB0_ub hlR₀ hRN₁ hρ hρK hSg1
    (div_totient_le_loglog_of_le hK_tot htot hR₀R₁) hSgν hVc hν h8ν h11ν hθ₁ hD hb hCB hKρ hθs hσE
    hσU
  have hcr1w := hcross hR₁2 le_rfl hR₁6 h36_R₁ hL3000 hc1 hcup hα.le (by linarith only [hα8])
    hsize_near1 hsize_up1 hrad hRM1 hcutN hB1_ub hH₁_ub hRN₁ hρ hρK hSg1
    (div_totient_le_loglog_of_le hK_tot htot le_rfl) hSgν hVc hν h8ν h11ν hθ₁ hD hb hCB hKρ hθs hσE
    hσU
  have h18_R₀ : 18 * (1 + Real.log (⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ : ℝ)) ≤
      Real.log (N : ℝ) := by
    have := Real.log_natCast_nonneg ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊
    linarith only [h36_R₀, this]
  have htwo' : ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
      z ∈ (conductorSubspace ⌊(N : ℝ) ^ θ₁⌋₊ N)ᗮ →
      θ₁ / (8 * D) * Real.log (N : ℝ) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension z n ^ 2) +
        growingMassConstant / (8 * c ^ 7) * Real.log (N : ℝ) *
          (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension z n ^ 2) ≤
        completeWeilEnergy tiltedUnitSpline c N z := by
    intro z hz; rw [hDdef]; exact htwo c hc1 hcup hz
  exact complement_three_band_reserve_assembly hQ2 hQR₀ hc1 hb hb8 (by positivity)
    (hcoerc0 hQ2 hQR₀ hR₀6 h36_R₀ hc1 hcL hw1 hrad hsize_near0 hsmall_band0)
    (hcoerc1 hR₀2 hR₀R₁ hR₁6 h1080_R₁ hc1 hcL hw1 hsize_near1
      (hR₁_tail.trans ((div_le_one hL0).mpr hL1)))
    (two_region_reserve_assembly_shape hc1 hθ₁ hD hg hb hbg htwo')
    (hcross01 hR₀2 hR₀6 h18_R₀ hc1 hw1 hsize_near0 hsize_up0 hH₀_ub hsmall_cross01)
    hcr0w hcr1w hfl0 hfl1 hfl2_P hfl2_S hu₀_mem hu₀_orthQ hu₁_mem hu₁_orthR₀ hw

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
