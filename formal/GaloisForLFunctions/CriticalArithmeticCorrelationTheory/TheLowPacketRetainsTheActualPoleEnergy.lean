import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalLowPacketRetainsItsSignedPolarPart

/-!
# The low packet retains its actual pole energy

Applying the signed packet estimate to the pole alone replaces its finite-part
model by the exact scalar matrix energy, with arbitrarily small diagonal error.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The full low-packet energy equals the nonpolar conductor diagonal plus the actual pole
energy, up to an arbitrarily small relative error in the full conductor diagonal. -/
theorem eventually_lowPacket_actual_pole_energy_approx
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      let S := ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2
      let v := normalizedRamanujanHorizonVector 1 N
      let y := ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N
      |completeWeilEnergy tiltedUnitSpline (c N) N y - S -
        (completeWeilEnergy tiltedUnitSpline (c N) N v -
          completedConductorEnergy tiltedUnitSpline (c N) 1) * b 1 ^ 2| ≤ ε * S := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_completeWeil_low_packet_signed_approx hc hR hcrit (half_pos hε),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hlog).eventually_ge_atTop 1]
    with N hN hQpow b Q S v y
  have hQ : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hQpow)
  have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
  let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
  let P := tiltedPolarFinitePart * (c N / Real.log N)
  let b₀ : ℕ → ℝ := fun m => if m = 1 then 1 else 0
  have hy₀ : (∑ m ∈ Icc 1 Q, b₀ m • normalizedRamanujanHorizonVector m N) = v := by
    rw [sum_eq_single_of_mem 1 h1]
    · simp only [b₀, if_pos rfl, one_smul, v]
    · intro m _ hm
      simp only [b₀, if_neg hm, zero_smul]
  have hS₀ : (∑ m ∈ Icc 1 Q, E m * b₀ m ^ 2) = E 1 := by
    rw [sum_eq_single_of_mem 1 h1]
    · simp only [b₀, if_pos rfl, one_pow, mul_one]
    · intro m _ hm
      simp only [b₀, if_neg hm, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have hscalar := hN b₀
  change |completeWeilEnergy tiltedUnitSpline (c N) N
      (∑ m ∈ Icc 1 Q, b₀ m • normalizedRamanujanHorizonVector m N) -
        (∑ m ∈ Icc 1 Q, E m * b₀ m ^ 2) - P * b₀ 1 ^ 2| ≤
      (ε / 2) * ∑ m ∈ Icc 1 Q, E m * b₀ m ^ 2 at hscalar
  rw [hy₀, hS₀] at hscalar
  simp only [b₀, if_pos rfl, one_pow, mul_one] at hscalar
  have hpacket := hN b
  change |completeWeilEnergy tiltedUnitSpline (c N) N y - S - P * b 1 ^ 2| ≤
    (ε / 2) * S at hpacket
  have hE : ∀ m ∈ Icc 1 Q, 0 ≤ E m := fun m hm =>
    completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
      integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1
  have hsingle : E 1 * b 1 ^ 2 ≤ S := single_le_sum
    (fun m hm => mul_nonneg (hE m hm) (sq_nonneg _)) h1
  have hscaled : |(completeWeilEnergy tiltedUnitSpline (c N) N v - E 1 - P) * b 1 ^ 2| ≤
      (ε / 2) * S := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (b 1))]
    exact (mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsingle (half_pos hε).le)
  have hid : completeWeilEnergy tiltedUnitSpline (c N) N y - S -
      (completeWeilEnergy tiltedUnitSpline (c N) N v - E 1) * b 1 ^ 2 =
      (completeWeilEnergy tiltedUnitSpline (c N) N y - S - P * b 1 ^ 2) -
        (completeWeilEnergy tiltedUnitSpline (c N) N v - E 1 - P) * b 1 ^ 2 := by ring
  change |completeWeilEnergy tiltedUnitSpline (c N) N y - S -
    (completeWeilEnergy tiltedUnitSpline (c N) N v - E 1) * b 1 ^ 2| ≤ ε * S
  rw [hid]
  exact ((abs_sub _ _).trans (add_le_add hpacket hscaled)).trans_eq (by ring)

/-- Discarding the nonpolar diagonal leaves the exact scalar pole cost, with arbitrarily
small packet-diagonal loss. -/
theorem eventually_lowPacket_ge_actual_pole_sub
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
      completeWeilEnergy tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) * b 1 ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline (c N) N
          (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) +
        ε * ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_lowPacket_actual_pole_energy_approx hc hR hcrit hε,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hlog).eventually_ge_atTop 1]
    with N hN hQpow b Q
  have hQ : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hQpow)
  have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, hQ⟩
  have hsingle : completedConductorEnergy tiltedUnitSpline (c N) 1 * b 1 ^ 2 ≤
      ∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2 :=
    single_le_sum (fun m hm => mul_nonneg
      (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
        integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1)
      (sq_nonneg _)) h1
  have hab := (abs_le.mp (hN b)).1
  nlinarith only [hab, hsingle]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
