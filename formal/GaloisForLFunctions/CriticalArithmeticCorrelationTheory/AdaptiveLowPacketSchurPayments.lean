import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LowConductorCollarPairingsAndWindowLocalizedGarding

/-!
# Arbitrarily accurate low-packet Schur payment

A fixed Schur multiplier is absorbed by the deep, intermediate, and prefix
reserves. This permits an arbitrarily small loss in the packet diagonal.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis CriticalScaleArithmeticRigidity

/-- A fixed Schur multiplier is absorbed by the same band reserves; the literal collar cost
scales by that multiplier. -/
theorem eventually_critical_schur_pairing_with_multiplier
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {T κ_P : ℝ} (hT : 0 < T) (hκP : 0 < κ_P) :
    ∀ᶠ N : ℕ in atTop,
      let Q := ⌊Real.log (N : ℝ) ^ (13 / 32 : ℝ)⌋₊
      let r := fun m => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N
      ∀ s : Finset ℕ, s ⊆ Icc 1 Q → ∀ M : ℕ, M ≤ N →
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        T * (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 /
          completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
          (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
            (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
          (6 * T) * (∑ m ∈ s, topCollarDualSeventhMass M N (r m) /
            completedConductorEnergy tiltedUnitSpline (c N) m) *
              topCollarSeventhMass M N (primeHorizonExtension w) := by
  have hLlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_critical_low_packet_residual_budget hc hR hcrit,
    eventually_critical_deep_residual_le hc hcrit (by positivity : (0 : ℝ) < 1 / (12 * T)),
    eventually_three_cutoff_bounds_one_ninth
      (by norm_num : (0 : ℝ) < 13 / 32) (by norm_num : (13 / 32 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 4096) (le_refl (1 / 4096 : ℝ)),
    eventually_log_nat_le_rpow_36_one_ninth, hLlim.eventually_ge_atTop 2000,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hLlim).eventually_ge_atTop (120 * T),
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 5
      (by norm_num : (0 : ℝ) < 3 / 4) (6 * T / κ_P))]
    with N hfull hdeep hcut hLX hlarge hquarter hprefix
  simp only [Function.comp_def] at hlarge hquarter hprefix
  intro Q r s hs M hMN u₀ hu₀ u₁ w
  let L := Real.log (N : ℝ)
  let X := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
  let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
  have hL1 : 1 ≤ L := by linarith only [hlarge]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by
    by_contra hn
    have : N = 0 := by omega
    subst N
    simp [L] at hL0
  obtain ⟨hQ2, hQX, _, _, _, _, hXup, _, h36, _, _, _⟩ := hcut
  have hX2 : 2 ≤ X := hQ2.trans hQX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hE : ∀ m ∈ Icc 1 Q, 0 < E m := fun m hm => by
    have hh := spectralFloor_conductor_energy_ge (hc N) (mem_Icc.mp hm).1
    have hf : 0 < tiltedSplineSpectralFloorConstant / (2 * c N ^ 7) :=
      div_pos tiltedSplineSpectralFloorConstant_pos (by have := hc N; positivity)
    change 0 < completedConductorEnergy tiltedUnitSpline (c N) m
    linarith only [hf, hh]
  have hΨ : (∑ m ∈ s, ‖r m‖ ^ 2 / E m) ≤ L ^ (1 / 4 : ℝ) :=
    (sum_le_sum_of_subset_of_nonneg hs (fun m hm _ => div_nonneg (sq_nonneg _) (hE m hm).le)).trans hfull
  have hD : (∑ m ∈ s, deepMass (X : ℝ) (r m) / E m) ≤ 1 / (12 * T) :=
    (sum_le_sum_of_subset_of_nonneg hs (fun m hm _ =>
      div_nonneg (deepMass_nonneg _ _) (hE m hm).le)).trans hdeep
  obtain ⟨_, _, _, _, hX6, _, _, _, _, _, _, _⟩ :=
    rpow_horizon_N_bounds_one_ninth (c := 1) hN1 hX2 le_rfl hlarge hLX hL1 h36
  have h18 : 18 * (1 + Real.log (X : ℝ)) ≤ L := by
    linarith only [h36, Real.log_natCast_nonneg X]
  have htop := sum_topRows_sq_le hX2 hX1 (sq_add_one_mul_le_of_pow_six_le hX2 hX6) h18 hu₀
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hhalf1 : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hnum : 2 * (Real.log (2 * (X : ℝ)) + 3) ≤ 10 * L ^ (1 / 2 : ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith only [hXup, hlog2, hhalf1]
  have hqpos : 0 < L ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hpowers : L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hpowers' : L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
  have htopcoef : (6 * T) * L ^ (1 / 4 : ℝ) *
      (2 * (Real.log (2 * (X : ℝ)) + 3) / L) ≤ 1 / 2 := by
    calc
      _ ≤ 60 * T * (L ^ (1 / 4 : ℝ) * L ^ (1 / 2 : ℝ) / L) :=
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hL0.le)
          (by positivity)).trans_eq (by ring)
      _ = 60 * T / L ^ (1 / 4 : ℝ) := by
        rw [← mul_div_assoc]
        apply (div_eq_div_iff hL0.ne' hqpos.ne').mpr
        nlinarith only [congrArg (fun x : ℝ => 60 * T * x) hpowers']
      _ ≤ 1 / 2 := (div_le_iff₀ hqpos).mpr (by linarith only [hquarter])
  have htopPaid := (mul_le_mul_of_nonneg_left htop
    (show 0 ≤ (6 * T) * L ^ (1 / 4 : ℝ) by positivity)).trans
      (by simpa only [← mul_assoc] using mul_le_mul_of_nonneg_right htopcoef (sq_nonneg ‖u₀‖))
  have hsecond : (3 * T) * L ^ (1 / 4 : ℝ) ≤ L ^ (1 / 2 : ℝ) / 32 := by
    have hh := mul_le_mul_of_nonneg_right hquarter hqpos.le
    nlinarith only [hh, hpowers, mul_pos hT hqpos]
  have hℓ : 0 < (1 + Real.log L) ^ 5 := by have := Real.log_nonneg hL1; positivity
  have hpre : (6 * T) * L ^ (1 / 4 : ℝ) ≤ κ_P * L / (1 + Real.log L) ^ 5 := by
    have hh : (6 * T / κ_P) * (1 + Real.log L) ^ 5 ≤ L ^ (3 / 4 : ℝ) := hprefix
    have hh' : (6 * T * (1 + Real.log L) ^ 5) / κ_P ≤ L ^ (3 / 4 : ℝ) := by
      simpa only [div_mul_eq_mul_div] using hh
    have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hκP).mp hh') hqpos.le
    have he : L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    apply (le_div_iff₀ hℓ).mpr
    calc
      _ = 6 * T * (1 + Real.log L) ^ 5 * L ^ (1 / 4 : ℝ) := by ring
      _ ≤ L ^ (3 / 4 : ℝ) * κ_P * L ^ (1 / 4 : ℝ) := hmul
      _ = κ_P * L := by rw [mul_right_comm, he, mul_comm]
  have hpair₀ := pairing_sum_le_deep_prefix_weighted_collar (X := (X : ℝ))
    hMN (fun m hm => hE m (hs hm)) u₀ u₁ w hΨ hD le_rfl
  have hpair : T * (∑ m ∈ s, ⟪r m, u₀ + u₁ + w⟫ ^ 2 / E m) ≤
      (6 * T) * L ^ (1 / 4 : ℝ) *
        (∑ n ∈ topRows N (X : ℝ), primeHorizonExtension u₀ n ^ 2) +
      (1 / 2 : ℝ) * ‖u₀‖ ^ 2 + (3 * T) * L ^ (1 / 4 : ℝ) * ‖u₁‖ ^ 2 +
      (6 * T) * L ^ (1 / 4 : ℝ) * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
      (6 * T) * (∑ m ∈ s, topCollarDualSeventhMass M N (r m) / E m) *
        topCollarSeventhMass M N (primeHorizonExtension w) :=
    (mul_le_mul_of_nonneg_left hpair₀ hT.le).trans_eq (by field_simp [hT.ne'] <;> ring)
  have hsecondPaid := mul_le_mul_of_nonneg_right hsecond (sq_nonneg ‖u₁‖)
  have hprePaid := mul_le_mul_of_nonneg_right hpre
    (show 0 ≤ ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 from sum_nonneg fun _ _ => sq_nonneg _)
  ring_nf at hpair htopPaid hsecondPaid hprePaid ⊢
  linarith only [hpair, htopPaid, hsecondPaid, hprePaid]

/-- The whole nonpolar low packet is paid by arbitrarily small fixed prefix and collar reserves. -/
theorem eventually_nonpolar_lowPacket_schur_payment_with_multiplier
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {T κ_P κ_S : ℝ} (hT : 0 < T) (hκP : 0 < κ_P) (hκS : 0 < κ_S) :
    ∀ᶠ N : ℕ in atTop,
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        T * (∑ m ∈ Icc 2 (lowPacketCutoff N),
          ⟪conductorResidualVector (c N) m N, u₀ + u₁ + w⟫ ^ 2 /
            completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
          (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
            (∑ n ∈ Icc 1 (N / linearDefectCutoff (c N)), primeHorizonExtension w n ^ 2) +
          (κ_S * Real.log N / c N ^ 7) *
            topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension w) := by
  have hcost := (tendsto_nonpolar_lowPacket_collar_schur_cost hc hR hcrit).eventually
    (gt_mem_nhds (show 0 < κ_S / (6 * T) by positivity))
  filter_upwards [eventually_critical_schur_pairing_with_multiplier hc hR hcrit hT hκP, hcost,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hpair hcostN hL
  simp only [Function.comp_def] at hL
  intro u₀ hu₀ u₁ w
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  let M := N / linearDefectCutoff (c N)
  let D := ∑ m ∈ Icc 2 (lowPacketCutoff N),
    topCollarDualSeventhMass M N (conductorResidualVector (c N) m N) /
      completedConductorEnergy tiltedUnitSpline (c N) m
  have hs : Icc 2 (lowPacketCutoff N) ⊆ Icc 1 (lowPacketCutoff N) :=
    Icc_subset_Icc (by norm_num) le_rfl
  have hb := hpair (Icc 2 (lowPacketCutoff N)) hs M (Nat.div_le_self _ _) u₀ hu₀ u₁ w
  have hD : (6 * T) * D ≤ κ_S * Real.log N / c N ^ 7 := by
    change c N ^ 7 / Real.log N * D < κ_S / (6 * T) at hcostN
    have hh := mul_le_mul_of_nonneg_right hcostN.le
      (show 0 ≤ (6 * T) * Real.log (N : ℝ) / c N ^ 7 by positivity)
    have he : (c N ^ 7 / Real.log N * D) * ((6 * T) * Real.log N / c N ^ 7) = (6 * T) * D := by
      field_simp [ne_of_gt hL, ne_of_gt hc0]
    rw [he] at hh
    exact hh.trans_eq (by field_simp [hT.ne'])
  have hpay := mul_le_mul_of_nonneg_right hD (topCollarSeventhMass_nonneg M N (primeHorizonExtension w))
  dsimp only [D, M, conductorResidualVector] at hpay
  dsimp only [M] at hb
  dsimp only [conductorResidualVector]
  linarith only [hb, hpay]

/-- All low conductors, including the pole, decouple from the non-collar pieces. -/
theorem eventually_lowPacket_noncollar_schur_payment_with_multiplier
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {T κ_P : ℝ} (hT : 0 < T) (hκP : 0 < κ_P) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, M ≤ N →
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        T * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          ⟪conductorResidualVector (c N) m N, u₀ + u₁ + horizonPrefixVector M w⟫ ^ 2 /
            completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
          (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
            (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) := by
  filter_upwards [eventually_critical_schur_pairing_with_multiplier hc hR hcrit hT hκP]
    with N hpair M hMN u₀ hu₀ u₁ w
  have hb := hpair (Icc 1 (lowPacketCutoff N)) (by rfl) M hMN u₀ hu₀ u₁ (horizonPrefixVector M w)
  have hprefix : (∑ n ∈ Icc 1 M, primeHorizonExtension (horizonPrefixVector M w) n ^ 2) =
      ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 := by
    rw [primeHorizonExtension_horizonPrefixVector hMN]
    exact sum_congr rfl fun n hn => by simp only [if_pos (mem_Icc.mp hn).2]
  have hcollar : topCollarSeventhMass M N (primeHorizonExtension (horizonPrefixVector M w)) = 0 := by
    rw [primeHorizonExtension_horizonPrefixVector hMN]
    unfold topCollarSeventhMass
    exact sum_eq_zero fun n hn => by
      simp only [if_neg (not_le.mpr (mem_Ioc.mp hn).1), zero_pow (by decide : 2 ≠ 0), mul_zero]
  rw [hprefix, hcollar, mul_zero, add_zero] at hb
  exact hb


/-- Weighted Young inequality with an arbitrary positive diagonal payment. -/
theorem two_abs_weighted_sum_le_with_payment {s : Finset ℕ} {E a t : ℕ → ℝ} (hE : ∀ m ∈ s, 0 < E m) {ε : ℝ} (hε : 0 < ε) :
    2 * |∑ m ∈ s, a m * t m| ≤ ε * (∑ m ∈ s, E m * a m ^ 2) + (1 / ε) * ∑ m ∈ s, t m ^ 2 / E m := by
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
  have := two_abs_le_of_sq_le hS (one_div_pos.mpr hε) hcs
  rw [Real.sq_sqrt hΦ] at this
  simpa only [one_div, div_eq_mul_inv, inv_inv, one_mul, mul_one, mul_comm] using this

/-- The nonpolar collar alone costs an arbitrarily small seventh-power reserve. -/
theorem eventually_nonpolar_collar_schur_payment_with_multiplier
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {T κ_S : ℝ} (hT : 0 < T) (hκS : 0 < κ_S) :
    ∀ᶠ N : ℕ in atTop, ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      T * (∑ m ∈ Icc 2 (lowPacketCutoff N),
        ⟪conductorResidualVector (c N) m N,
          horizonCollarVector (N / linearDefectCutoff (c N)) w⟫ ^ 2 /
          completedConductorEnergy tiltedUnitSpline (c N) m) ≤
        (κ_S * Real.log N / c N ^ 7) *
          topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension w) := by
  filter_upwards [eventually_nonpolar_lowPacket_schur_payment_with_multiplier hc hR hcrit hT zero_lt_one hκS]
    with N hN w
  have h := hN 0 (Submodule.zero_mem _) 0
    (horizonCollarVector (N / linearDefectCutoff (c N)) w)
  simpa only [zero_add, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
    prefix_mass_horizonCollarVector, topCollarSeventhMass_horizonCollarVector] using h

/-- All packet cross terms except the literal polar collar pairing cost an arbitrarily small
packet diagonal and fixed band reserves. -/
theorem eventually_lowPacket_cross_sub_polar_le
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε κ_P κ_S : ℝ} (hε : 0 < ε) (hκP : 0 < κ_P) (hκS : 0 < κ_S) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      ∀ u₀ ∈ conductorSubspace ⌊Real.exp (Real.log (N : ℝ) ^ (1 / 2 : ℝ))⌋₊ N,
      ∀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
      u₀ + u₁ + w ∈ (conductorSubspace (lowPacketCutoff N) N)ᗮ →
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (∑ m ∈ Icc 1 (lowPacketCutoff N), b m • normalizedRamanujanHorizonVector m N),
          u₀ + u₁ + w⟫ - b 1 * ⟪conductorResidualVector (c N) 1 N,
          horizonCollarVector (N / linearDefectCutoff (c N)) w⟫| ≤
        ε * (∑ m ∈ Icc 1 (lowPacketCutoff N),
          completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2) +
        ‖u₀‖ ^ 2 + (Real.log (N : ℝ) ^ (1 / 2 : ℝ) / 32) * ‖u₁‖ ^ 2 +
        (κ_P * Real.log N / (1 + Real.log (Real.log N)) ^ 5) *
          (∑ n ∈ Icc 1 (N / linearDefectCutoff (c N)), primeHorizonExtension w n ^ 2) +
        (κ_S * Real.log N / c N ^ 7) *
          topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension w) := by
  have hQlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_lowPacket_noncollar_schur_payment_with_multiplier hc hR hcrit
      (show 0 < 1 / (ε / 2) by positivity) hκP,
    eventually_nonpolar_collar_schur_payment_with_multiplier hc hR hcrit
      (show 0 < 1 / (ε / 2) by positivity) hκS,
    hQlim.eventually_ge_atTop 1]
    with N hprefix hnonpolar hQge b u₀ hu₀ u₁ w horth
  let Q := lowPacketCutoff N
  let M := N / linearDefectCutoff (c N)
  let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
  let r := fun m => conductorResidualVector (c N) m N
  let T₀ := ∑ m ∈ Icc 1 Q, b m * ⟪r m, u₀ + u₁ + horizonPrefixVector M w⟫
  let T₂ := ∑ m ∈ Icc 2 Q, b m * ⟪r m, horizonCollarVector M w⟫
  let T₁ := b 1 * ⟪r 1, horizonCollarVector M w⟫
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hQge)
  have hE : ∀ m ∈ Icc 1 Q, 0 < E m := fun m hm =>
    completedConductorEnergy_tilted_pos (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1
  have hsplit : Icc 1 Q = insert 1 (Icc 2 Q) := by
    ext m; simp only [mem_Icc, mem_insert]; omega
  have hsum : (∑ m ∈ Icc 1 Q, b m * ⟪r m, u₀ + u₁ + w⟫) = T₀ + (T₁ + T₂) := by
    have hw : u₀ + u₁ + w =
        (u₀ + u₁ + horizonPrefixVector M w) + horizonCollarVector M w := by
      rw [add_assoc (u₀ + u₁), horizonPrefixVector_add_collar]
    calc
      _ = T₀ + ∑ m ∈ Icc 1 Q, b m * ⟪r m, horizonCollarVector M w⟫ := by
        dsimp only [T₀]
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro m hm
        rw [hw, inner_add_right, mul_add]
      _ = T₀ + (T₁ + T₂) := by
        congr 1
        rw [hsplit, sum_insert (by simp)]

  have hpre := two_abs_weighted_sum_le_with_payment (a := b)
    (t := fun m => ⟪r m, u₀ + u₁ + horizonPrefixVector M w⟫) hE (half_pos hε)
  have hnon := two_abs_weighted_sum_le_with_payment (a := b)
    (t := fun m => ⟪r m, horizonCollarVector M w⟫)
    (s := Icc 2 Q) (fun m hm => hE m (mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega,
      (mem_Icc.mp hm).2⟩)) (half_pos hε)
  have hsumE : (∑ m ∈ Icc 2 Q, E m * b m ^ 2) ≤ ∑ m ∈ Icc 1 Q, E m * b m ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by norm_num) le_rfl)
      (fun m hm _ => mul_nonneg (hE m hm).le (sq_nonneg _))
  have hp := hprefix M (Nat.div_le_self N _) u₀ hu₀ u₁ w
  have hn := hnonpolar w
  have hab := abs_add_le T₀ T₂
  have hpaySum := mul_le_mul_of_nonneg_left hsumE (half_pos hε).le
  rw [conductor_packet_cross_eq_residual_sum (c N) b horth, hsum]
  change 2 * |T₀ + (T₁ + T₂) - T₁| ≤ _
  rw [show T₀ + (T₁ + T₂) - T₁ = T₀ + T₂ by ring]
  dsimp only [T₀, T₁, T₂, E, r, Q, M] at hab hpre hnon hpaySum hp hn ⊢
  simp only [div_eq_mul_inv, mul_inv_rev] at hpre hnon hpaySum hp hn ⊢
  ring_nf at hpre hnon hpaySum hp hn hab ⊢
  linarith only [hpre, hnon, hpaySum, hp, hn, hab]

#print axioms eventually_lowPacket_cross_sub_polar_le
#print axioms eventually_critical_schur_pairing_with_multiplier
#print axioms eventually_nonpolar_lowPacket_schur_payment_with_multiplier
#print axioms eventually_lowPacket_noncollar_schur_payment_with_multiplier

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
