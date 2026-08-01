import GaloisForLFunctions.RHTower.SoninCouplingPacketLimit

/-!
# Nonannihilation of the successive-layer coupling

The coupling sends the wavepacket to its inverse dilate, and the dilate has the same norm as the
packet, whose norm settles at a positive limit.  So the coupling has a norm-one action on the
packet family in the limit, and in particular it is nonzero for every sufficiently large clock.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- The packet's squared norm is the integral of its square. -/
theorem norm_sq_soninPacketEven (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    ‖soninPacketEven b c hb hbc κ‖ ^ 2 = ∫ x : ℝ, soninPacket b c hbc κ x ^ 2 := by
  rw [show ‖soninPacketEven b c hb hbc κ‖ = ‖soninPacketL2 b c hb hbc κ‖ from rfl,
    norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [soninPacketL2_coeFn b c hb hbc κ] with x hx
  rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The packet's norm settles at the square root of half the profile's energy. -/
theorem tendsto_norm_soninPacketEven (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    Tendsto (fun n : ℕ => ‖soninPacketEven b c hb hbc (κ n)‖) atTop
      (𝓝 (Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2))) := by
  have hsq : Tendsto (fun n : ℕ => ‖soninPacketEven b c hb hbc (κ n)‖ ^ 2) atTop
      (𝓝 ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2)) := by
    refine ((tendsto_integral_soninPacket_sq_atTop b c hb hbc).comp hκ).congr fun n => ?_
    exact (norm_sq_soninPacketEven b c hb hbc (κ n)).symm
  have hsqrt := (Real.continuous_sqrt.tendsto
    ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2)).comp hsq
  simp only [Function.comp_def] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- The limiting packet norm is positive. -/
theorem sqrt_half_energy_pos (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    0 < Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) := by
  refine Real.sqrt_pos.mpr ?_
  have := integral_soninAnnulusBump_sq_pos b c hb hbc
  positivity

/-- **`(4)`.**  The coupling's action on the wavepacket family has the packet's own limiting
norm. -/
theorem tendsto_norm_soninApertureCoupling_apply_soninPacketEven
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
          (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖) atTop
      (𝓝 (Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2))) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  have hdiff := tendsto_norm_soninApertureCoupling_soninPacketEven_sub a b c ha hb hab hbc q
    haq hqb r hrpos hrgt hcr hr
  have hpacket := tendsto_norm_soninPacketEven b c hb hbc
    (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have hdil : Tendsto (fun n : ℕ =>
      ‖soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖) atTop
      (𝓝 (Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2))) := by
    refine hpacket.congr fun n => ?_
    exact (norm_soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)).symm
  have hclose : Tendsto (fun n : ℕ =>
      ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
          (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ -
        ‖soninDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hdiff
    exact abs_norm_sub_norm_le _ _
  have := hclose.add hdil
  simpa using this

/-- **The coupling is nonzero for every large clock.** -/
theorem eventually_soninApertureCoupling_ne_zero
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) ≠ 0 := by
  have hlim := tendsto_norm_soninApertureCoupling_apply_soninPacketEven a b c ha hb hab hbc q
    haq hqb r hrpos hrgt hcr hr
  have hpos := sqrt_half_energy_pos b c hb hbc
  filter_upwards [hlim (lt_mem_nhds hpos)] with n hn
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hn
  intro hzero
  rw [hzero] at hn
  simp at hn

end RHTower
