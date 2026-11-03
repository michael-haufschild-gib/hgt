import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LogarithmFreeCriticalConductorResiduals
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalDeepRowsPayTheFirstBand

/-!
# The critical Schur pairing retains the collar weight

The low-conductor residual meets three different reserves. Deep rows pay its
pairing with the first band; the full residual pays the second band and the
far prefix; the dual seventh-power mass pays the far collar. Keeping these
payments separate avoids charging the full residual against the collar floor.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

/-- Rowwise Schur payment with distinct deep, prefix, and weighted collar masses. -/
theorem pairing_sum_le_deep_prefix_weighted_collar
    {M N : ℕ} {s : Finset ℕ} {E : ℕ → ℝ}
    {r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N)} {X Ψ Ψ_D Ψ_7 : ℝ}
    (hMN : M ≤ N) (hE : ∀ m ∈ s, 0 < E m)
    (u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (hΨ : (∑ m ∈ s, ‖r m‖ ^ 2 / E m) ≤ Ψ)
    (hΨD : (∑ m ∈ s, deepMass X (r m) / E m) ≤ Ψ_D)
    (hΨ7 : (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) ≤ Ψ_7) :
    (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      6 * Ψ * (∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2) +
        6 * Ψ_D * ‖u₀‖ ^ 2 + 3 * Ψ * ‖u₁‖ ^ 2 +
        6 * Ψ * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
        6 * Ψ_7 * topCollarSeventhMass M N (primeHorizonExtension w) := by
  let T := ∑ n ∈ topRows N X, primeHorizonExtension u₀ n ^ 2
  let P := ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2
  let S := topCollarSeventhMass M N (primeHorizonExtension w)
  have hT : 0 ≤ T := sum_nonneg fun _ _ => sq_nonneg _
  have hP : 0 ≤ P := sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ S := topCollarSeventhMass_nonneg _ _ _
  have hrow (m : ℕ) : ⟪r m, u₀ + u₁ + w⟫ ^ 2 ≤
      (6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * ‖r m‖ ^ 2 +
        6 * ‖u₀‖ ^ 2 * deepMass X (r m) +
        6 * S * topCollarDualSeventhMass M N (r m) := by
    have h₀ := inner_sq_le_deep_add_top X (r m) u₀
    have h₁ : ⟪r m, u₁⟫ ^ 2 ≤ ‖r m‖ ^ 2 * ‖u₁‖ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (r m) u₁) 2
      simpa only [sq_abs, mul_pow] using h
    have hw := inner_sq_le_prefix_add_topCollarSeventh hMN (r m) w
    have hpref : (∑ n ∈ Icc 1 M, primeHorizonExtension (r m) n ^ 2) ≤ ‖r m‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq]
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMN)
        fun _ _ _ => sq_nonneg _
    have hp := mul_le_mul_of_nonneg_right hpref hP
    have hthree : (⟪r m, u₀⟫ + ⟪r m, u₁⟫ + ⟪r m, w⟫) ^ 2 ≤
        3 * (⟪r m, u₀⟫ ^ 2 + ⟪r m, u₁⟫ ^ 2 + ⟪r m, w⟫ ^ 2) := by
      nlinarith only [sq_nonneg (⟪r m, u₀⟫ - ⟪r m, u₁⟫),
        sq_nonneg (⟪r m, u₀⟫ - ⟪r m, w⟫),
        sq_nonneg (⟪r m, u₁⟫ - ⟪r m, w⟫)]
    rw [inner_add_right, inner_add_right]
    change ⟪r m, u₀⟫ ^ 2 ≤ 2 * (‖r m‖ ^ 2 * T) +
      2 * (deepMass X (r m) * ‖u₀‖ ^ 2) at h₀
    change ⟪r m, w⟫ ^ 2 ≤ 2 * _ * P +
      2 * topCollarDualSeventhMass M N (r m) * S at hw
    nlinarith only [h₀, h₁, hw, hp, hthree]
  have hsum : (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      (6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * Ψ +
        6 * ‖u₀‖ ^ 2 * Ψ_D + 6 * S * Ψ_7 := by
    calc
      _ ≤ ∑ m ∈ s, ((6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * (‖r m‖ ^ 2 / E m) +
          6 * ‖u₀‖ ^ 2 * (deepMass X (r m) / E m) +
          6 * S * (topCollarDualSeventhMass M N (r m) / E m)) := by
        refine sum_le_sum fun m hm => ?_
        exact (div_le_div_of_nonneg_right (hrow m) (hE m hm).le).trans_eq (by ring)
      _ = (6 * T + 3 * ‖u₁‖ ^ 2 + 6 * P) * (∑ m ∈ s, ‖r m‖ ^ 2 / E m) +
          6 * ‖u₀‖ ^ 2 * (∑ m ∈ s, deepMass X (r m) / E m) +
          6 * S * (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
      _ ≤ _ := add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left hΨ (by positivity))
          (mul_le_mul_of_nonneg_left hΨD (by positivity)))
        (mul_le_mul_of_nonneg_left hΨ7 (by positivity))
  change _ ≤ 6 * Ψ * T + 6 * Ψ_D * ‖u₀‖ ^ 2 + 3 * Ψ * ‖u₁‖ ^ 2 +
    6 * Ψ * P + 6 * Ψ_7 * S
  linarith only [hsum]


/-- The actual low-conductor Schur cost fits arbitrarily small fixed portions
of the far prefix and weighted collar reserves at one small critical multiple.
The first two bands cost respectively `1` and `sqrt(log N)/32` per unit mass. -/
theorem exists_critical_multiple_schur_payment {κ_P κ_S : ℝ}
    (hκP : 0 < κ_P) (hκS : 0 < κ_S) :
    ∃ K : ℝ, 0 < K ∧ K ≤ 1 / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ,
        1 ≤ c → c ≤ 2 * K * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
        let Q := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊
        let r := fun m => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N
        ∀ M : ℕ, M ≤ N → 2 * linearPrimeStrip c ≤ M →
        ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
        ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
          8 * (∑ m ∈ Icc 1 Q, ⟪r m, u₀ + u₁ + w⟫ ^ 2 /
            completedConductorEnergy tiltedUnitSpline c m) ≤
          ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
            (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
              (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
            (κ_S * Real.log N / c ^ 7) * topCollarSeventhMass M N (primeHorizonExtension w) := by
  obtain ⟨K, hK, hKhalf, hpacket⟩ :=
    exists_critical_multiple_low_packet_and_collar_budget (div_pos hκS (by norm_num : (0 : ℝ) < 48))
  refine ⟨K, hK, hKhalf, ?_⟩
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpacket, eventually_critical_deep_residual_payment,
    hLlim.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hLlim).eventually_ge_atTop 768,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 3 / 4) (48 / κ_P))]
    with N hp hd hL1 hlarge hprefix
  dsimp only [Function.comp_def] at hlarge hprefix
  intro c hc1 hc
  dsimp only
  intro M hMN hstrip u₀ hu₀ u₁ w
  let L := Real.log (N : ℝ)
  let Q := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let R := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
  let E := fun m => completedConductorEnergy tiltedUnitSpline c m
  let r := fun m => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
    (normalizedRamanujanHorizonVector m N) - E m • normalizedRamanujanHorizonVector m N
  change 1 ≤ L at hL1
  change 768 ≤ L ^ (1 / 4 : ℝ) at hlarge
  change (48 / κ_P) * (1 + Real.log L) ^ 5 ≤ L ^ (3 / 4 : ℝ) at hprefix
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc7 : 0 < c ^ 7 := pow_pos hc0 7
  have hc' : c ≤ L ^ (1 / 8 : ℝ) := hc.trans (by
    have h2K : 2 * K ≤ 1 := by linarith only [hKhalf]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right h2K (Real.rpow_nonneg hL0.le (1 / 8 : ℝ)))
  obtain ⟨-, hΨ, hcollar⟩ := hp c hc1 hc
  obtain ⟨hD, hT⟩ := hd c hc1 hc'
  have h7 := hcollar M hstrip
  have h7' : (∑ m ∈ Icc 1 Q, topCollarDualSeventhMass M N (r m) / E m) ≤
      κ_S * L / (48 * c ^ 7) := by
    change c ^ 7 / L * (∑ m ∈ Icc 1 Q, topCollarDualSeventhMass M N (r m) / E m) ≤ κ_S / 48 at h7
    apply (le_div_iff₀ (show 0 < 48 * c ^ 7 by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right h7 (show 0 ≤ 48 * L by positivity)
    have he : (c ^ 7 / L * (∑ m ∈ Icc 1 Q, topCollarDualSeventhMass M N (r m) / E m)) *
        (48 * L) = (∑ m ∈ Icc 1 Q, topCollarDualSeventhMass M N (r m) / E m) * (48 * c ^ 7) := by
      field_simp
    rw [he] at h
    linarith only [h]
  have hE : ∀ m ∈ Icc 1 Q, 0 < E m := by
    intro m hm
    have hfloor := spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1
    have hpos : 0 < tiltedSplineSpectralFloorConstant / (2 * c ^ 7) :=
      div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
    change 0 < completedConductorEnergy tiltedUnitSpline c m
    linarith only [hfloor, hpos]
  have hpair := pairing_sum_le_deep_prefix_weighted_collar
    (X := (R : ℝ)) hMN hE u₀ u₁ w hΨ hD h7'
  have hfirst := hT u₀ hu₀
  change (∑ m ∈ Icc 1 Q, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
    6 * L ^ (1 / 4 : ℝ) * (∑ n ∈ topRows N (R : ℝ), primeHorizonExtension u₀ n ^ 2) +
    6 * (1 / 96 : ℝ) * ‖u₀‖ ^ 2 + 3 * L ^ (1 / 4 : ℝ) * ‖u₁‖ ^ 2 +
    6 * L ^ (1 / 4 : ℝ) * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
    6 * (κ_S * L / (48 * c ^ 7)) *
      topCollarSeventhMass M N (primeHorizonExtension w) at hpair
  change 48 * L ^ (1 / 4 : ℝ) *
    (∑ n ∈ topRows N (R : ℝ), primeHorizonExtension u₀ n ^ 2) ≤
      (1 / 2 : ℝ) * ‖u₀‖ ^ 2 at hfirst
  have hsecond : 24 * L ^ (1 / 4 : ℝ) ≤ L ^ (1 / 2 : ℝ) / 32 := by
    have he : L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have h := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hL0.le (1 / 4 : ℝ))
    nlinarith only [h, he]
  have ht0 : 0 < (1 + Real.log L) ^ 5 := by
    have := Real.log_nonneg hL1
    positivity
  have hpre : 48 * L ^ (1 / 4 : ℝ) ≤ κ_P * L / (1 + Real.log L) ^ 5 := by
    have h := mul_le_mul_of_nonneg_right hprefix
      (show 0 ≤ κ_P * L ^ (1 / 4 : ℝ) by positivity)
    have he : ((48 / κ_P) * (1 + Real.log L) ^ 5) * (κ_P * L ^ (1 / 4 : ℝ)) =
        48 * L ^ (1 / 4 : ℝ) * (1 + Real.log L) ^ 5 := by field_simp
    have hpowers : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [he] at h
    apply (le_div_iff₀ ht0).mpr
    calc
      _ ≤ L ^ (3 / 4 : ℝ) * (κ_P * L ^ (1 / 4 : ℝ)) := h
      _ = κ_P * L := by rw [← mul_assoc, mul_comm _ κ_P, mul_assoc, hpowers]
  have hsecond' := mul_le_mul_of_nonneg_right hsecond (sq_nonneg ‖u₁‖)
  have hpre' := mul_le_mul_of_nonneg_right hpre
    (show 0 ≤ ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 from sum_nonneg fun _ _ => sq_nonneg _)
  have hcollar_eq : 48 * (κ_S * L / (48 * c ^ 7)) = κ_S * L / c ^ 7 := by ring
  change 8 * (∑ m ∈ Icc 1 Q, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤ _
  nlinarith only [hpair, hfirst, hsecond', hpre',
    congrArg (fun t => t * topCollarSeventhMass M N (primeHorizonExtension w)) hcollar_eq]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_critical_multiple_schur_payment
