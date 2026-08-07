import GaloisForLFunctions.RHTower.SoninCouplingNonannihilation
import GaloisForLFunctions.RHTower.SoninCouplingPartialUnitary

/-!
# The unit-norm wavepacket family

The coupling limits are proved for the raw modulated profile, whose norm settles at the square root
of half the profile's energy rather than at one.  Dividing by that norm turns the family into unit
vectors without changing any limit: an operator is linear, so the division passes through it, and
the denominator converges to a positive number.

On the resulting unit family the coupling carries the packet to its inverse dilate with error
tending to zero, its action has norm tending to one, and the adjoint inverts it on both classes —
the partial-unitary statement in its normalized form.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- Dividing a vector by another's norm divides its own norm by that number.  The degenerate case
is harmless: both sides vanish when the divisor does. -/
private theorem norm_invNorm_smul (u x : evenSubspace) :
    ‖((‖u‖ : ℂ))⁻¹ • x‖ = ‖x‖ / ‖u‖ := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u)]
  ring

private theorem norm_invNorm_smul_sub (u x y : evenSubspace) :
    ‖((‖u‖ : ℂ))⁻¹ • x - ((‖u‖ : ℂ))⁻¹ • y‖ = ‖x - y‖ / ‖u‖ := by
  rw [← smul_sub, norm_invNorm_smul]

/-- **The unit-norm wavepacket** `w = u / ‖u‖`. -/
def soninNormalizedPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) : evenSubspace :=
  ((‖soninPacketEven b c hb hbc κ‖ : ℂ))⁻¹ • soninPacketEven b c hb hbc κ

/-- **The unit-norm inverse-dilated wavepacket** `v = U_{1/r} w`. -/
def soninNormalizedDilatedPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ r : ℝ) (hr : 0 < r) : evenSubspace :=
  ((‖soninPacketEven b c hb hbc κ‖ : ℂ))⁻¹ • soninDilatedPacket b c hb hbc κ r hr

/-- The normalized dilate is the dilate of the normalized packet: dilation is linear, so it
commutes with the scalar division. -/
theorem soninNormalizedDilatedPacket_eq (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ r : ℝ) (hr : 0 < r) :
    soninNormalizedDilatedPacket b c hb hbc κ r hr =
      evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninNormalizedPacket b c hb hbc κ) := by
  rw [soninNormalizedDilatedPacket, soninNormalizedPacket, soninDilatedPacket, map_smul]

/-- The normalized packet is a unit vector whenever the raw packet is nonzero. -/
theorem norm_soninNormalizedPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) {κ : ℝ}
    (hu : soninPacketEven b c hb hbc κ ≠ 0) :
    ‖soninNormalizedPacket b c hb hbc κ‖ = 1 := by
  rw [soninNormalizedPacket, norm_invNorm_smul, div_self (norm_ne_zero_iff.mpr hu)]

/-- The normalized dilate is a unit vector as well, since dilation is an isometry. -/
theorem norm_soninNormalizedDilatedPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) {κ r : ℝ}
    (hr : 0 < r) (hu : soninPacketEven b c hb hbc κ ≠ 0) :
    ‖soninNormalizedDilatedPacket b c hb hbc κ r hr‖ = 1 := by
  rw [soninNormalizedDilatedPacket, norm_invNorm_smul, norm_soninDilatedPacket,
    div_self (norm_ne_zero_iff.mpr hu)]

/-- The raw packet is eventually nonzero along an escaping clock, because its norm converges to a
positive limit. -/
theorem eventually_soninPacketEven_ne_zero (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    ∀ᶠ n : ℕ in atTop, soninPacketEven b c hb hbc (κ n) ≠ 0 := by
  set L : ℝ := Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) with hL
  have hLpos : 0 < L := sqrt_half_energy_pos b c hb hbc
  have hnorm := tendsto_norm_soninPacketEven b c hb hbc κ hκ
  have hev : ∀ᶠ n : ℕ in atTop, L / 2 < ‖soninPacketEven b c hb hbc (κ n)‖ :=
    hnorm.eventually_const_lt (by linarith)
  filter_upwards [hev] with n hn
  intro hzero
  rw [hzero, norm_zero] at hn
  linarith

/-- Along an escaping clock the normalized packet is eventually a genuine unit vector. -/
theorem eventually_norm_soninNormalizedPacket_eq_one (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (κ : ℕ → ℝ) (hκ : Tendsto κ atTop atTop) :
    ∀ᶠ n : ℕ in atTop, ‖soninNormalizedPacket b c hb hbc (κ n)‖ = 1 := by
  filter_upwards [eventually_soninPacketEven_ne_zero b c hb hbc κ hκ] with n hn
  exact norm_soninNormalizedPacket b c hb hbc hn

/-- **`(3)` on the unit family.**  Past the crossing threshold the coupling carries the unit
wavepacket to its inverse dilate. -/
theorem tendsto_norm_soninApertureCoupling_soninNormalizedPacket_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (soninNormalizedPacket b c hb hbc (2 * Real.pi * (r n * q))) -
          soninNormalizedDilatedPacket b c hb hbc (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖)
      atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      (Filter.Tendsto.atTop_mul_const hq hr)
  have hraw := tendsto_norm_soninApertureCoupling_soninPacketEven_sub a b c ha hb hab hbc q
    haq hqb r hrpos hrgt hcr hr
  have hnorm := tendsto_norm_soninPacketEven b c hb hbc _ hfreq
  have hLne : Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) ≠ 0 :=
    (sqrt_half_energy_pos b c hb hbc).ne'
  have hdiv := hraw.div hnorm hLne
  rw [zero_div] at hdiv
  refine hdiv.congr fun n => ?_
  simp only [Pi.div_apply]
  rw [soninNormalizedPacket, soninNormalizedDilatedPacket, map_smul, norm_invNorm_smul_sub]

/-- **`(4)` on the unit family.**  The coupling's action on the unit wavepacket has norm tending
to one, so the coupling is asymptotically isometric there. -/
theorem tendsto_norm_soninApertureCoupling_apply_soninNormalizedPacket
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
          (soninNormalizedPacket b c hb hbc (2 * Real.pi * (r n * q)))‖) atTop (𝓝 1) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      (Filter.Tendsto.atTop_mul_const hq hr)
  have hraw := tendsto_norm_soninApertureCoupling_apply_soninPacketEven a b c ha hb hab hbc q
    haq hqb r hrpos hrgt hcr hr
  have hnorm := tendsto_norm_soninPacketEven b c hb hbc _ hfreq
  have hLne : Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) ≠ 0 :=
    (sqrt_half_energy_pos b c hb hbc).ne'
  have hdiv := hraw.div hnorm hLne
  rw [div_self hLne] at hdiv
  refine hdiv.congr fun n => ?_
  simp only [Pi.div_apply]
  rw [soninNormalizedPacket, map_smul, norm_invNorm_smul]

/-- **`(4a)` on the unit family.**  The adjoint coupling carries the unit inverse dilate back to
the unit wavepacket. -/
theorem tendsto_norm_adjoint_soninApertureCoupling_soninNormalizedDilatedPacket_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ 2) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖ContinuousLinearMap.adjoint
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
            (soninNormalizedDilatedPacket b c hb hbc
              (2 * Real.pi * (r n * q)) (r n) (hrpos n)) -
          soninNormalizedPacket b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      (Filter.Tendsto.atTop_mul_const hq hr)
  have hraw := tendsto_norm_adjoint_soninApertureCoupling_soninDilatedPacket_sub a b c ha hb
    hbc q haq hqb r hrpos hrgt hsq hr
  have hnorm := tendsto_norm_soninPacketEven b c hb hbc _ hfreq
  have hLne : Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) ≠ 0 :=
    (sqrt_half_energy_pos b c hb hbc).ne'
  have hdiv := hraw.div hnorm hLne
  rw [zero_div] at hdiv
  refine hdiv.congr fun n => ?_
  simp only [Pi.div_apply]
  rw [soninNormalizedPacket, soninNormalizedDilatedPacket, map_smul, norm_invNorm_smul_sub]

/-- **`(4b)`, first half, on the unit family.**  The adjoint inverts the coupling on the unit
wavepacket class. -/
theorem tendsto_norm_adjoint_mul_soninApertureCoupling_soninNormalizedPacket_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ 2) (hcr : ∀ n, c ≤ r n * a) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖ContinuousLinearMap.adjoint
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
            (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
              (soninNormalizedPacket b c hb hbc (2 * Real.pi * (r n * q)))) -
          soninNormalizedPacket b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      (Filter.Tendsto.atTop_mul_const hq hr)
  have hraw := tendsto_norm_adjoint_mul_soninApertureCoupling_soninPacketEven_sub a b c ha hb
    hab hbc q haq hqb r hrpos hrgt hsq hcr hr
  have hnorm := tendsto_norm_soninPacketEven b c hb hbc _ hfreq
  have hLne : Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) ≠ 0 :=
    (sqrt_half_energy_pos b c hb hbc).ne'
  have hdiv := hraw.div hnorm hLne
  rw [zero_div] at hdiv
  refine hdiv.congr fun n => ?_
  simp only [Pi.div_apply]
  rw [soninNormalizedPacket, map_smul, map_smul, norm_invNorm_smul_sub]

/-- **`(4b)`, second half, on the unit family.**  The coupling inverts its adjoint on the unit
inverse-dilate class. -/
theorem tendsto_norm_soninApertureCoupling_adjoint_soninNormalizedDilatedPacket_sub
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hsq : ∀ n, 0 < r n ^ 2) (hcr : ∀ n, c ≤ r n * a) (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (ContinuousLinearMap.adjoint
              (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n))
              (soninNormalizedDilatedPacket b c hb hbc
                (2 * Real.pi * (r n * q)) (r n) (hrpos n))) -
          soninNormalizedDilatedPacket b c hb hbc
            (2 * Real.pi * (r n * q)) (r n) (hrpos n)‖) atTop (𝓝 0) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi)
      (Filter.Tendsto.atTop_mul_const hq hr)
  have hraw := tendsto_norm_soninApertureCoupling_adjoint_soninDilatedPacket_sub a b c ha hb
    hab hbc q haq hqb r hrpos hrgt hsq hcr hr
  have hnorm := tendsto_norm_soninPacketEven b c hb hbc _ hfreq
  have hLne : Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) ≠ 0 :=
    (sqrt_half_energy_pos b c hb hbc).ne'
  have hdiv := hraw.div hnorm hLne
  rw [zero_div] at hdiv
  refine hdiv.congr fun n => ?_
  simp only [Pi.div_apply]
  rw [soninNormalizedDilatedPacket, map_smul, map_smul, norm_invNorm_smul_sub]

end RHTower
