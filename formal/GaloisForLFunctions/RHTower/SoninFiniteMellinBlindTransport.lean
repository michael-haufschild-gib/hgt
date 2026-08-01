import GaloisForLFunctions.RHTower.SoninMellinBlindness
import GaloisForLFunctions.RHTower.SoninCouplingOperatorNormFloor

/-!
# Finite Mellin blindness versus full Sonin transport

The same actual annular packet family is invisible, faster than every prescribed algebraic
order, to every fixed finite bank of Mellin evaluations, while successive-aperture transport
retains asymptotically its full relative norm.  This is an exact incompatibility between finite
scalar analytic observation and relation-valued aperture transport.
-/

noncomputable section

namespace RHTower

open MeasureTheory Filter
open scoped Topology

/-- The actual annular packets retain asymptotically their whole norm under successive-aperture
transport. -/
theorem tendsto_soninAperturePacketTransportRatio_one
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hcr : ∀ n, c ≤ r n * a) (hr : Tendsto r atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ /
          ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖)
      atTop (𝓝 1) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  set L : ℝ := Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2)
  have hLpos : 0 < L := sqrt_half_energy_pos b c hb hbc
  have hpacket :
      Tendsto
        (fun n : ℕ => ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖)
        atTop (𝓝 L) :=
    tendsto_norm_soninPacketEven b c hb hbc
      (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have himage :=
    tendsto_norm_soninApertureCoupling_apply_soninPacketEven
      a b c ha hb hab hbc q haq hqb r hrpos hrgt hcr hr
  have hratio := himage.div hpacket hLpos.ne'
  rwa [div_self hLpos.ne'] at hratio

/-- **Finite-bank singular transport law.** Along the same actual packet sequence, every fixed
finite family of Mellin evaluations is blind faster than every prescribed algebraic order, while
successive-aperture transport retains asymptotically full relative norm. -/
theorem eventually_finiteMellinBlind_and_soninTransportFull
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n)
    (hcr : ∀ n, c ≤ r n * a) (hr : Tendsto r atTop atTop)
    (E : Finset ℂ) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (∀ s ∈ E,
        (r n * q) ^ N *
            ‖soninPacketMellin b c hbc s (2 * Real.pi * (r n * q))‖ < ε) ∧
      1 - ε <
        ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
            (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ /
          ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖ := by
  have hq : 0 < q := ha.trans haq
  have hcarrier : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hq hr
  have hblind :
      ∀ᶠ n : ℕ in atTop, ∀ s ∈ E,
        (r n * q) ^ N *
            ‖soninPacketMellin b c hbc s (2 * Real.pi * (r n * q))‖ < ε := by
    rw [Finset.eventually_all]
    intro s _hs
    exact ((tendsto_pow_mul_norm_soninPacketMellin b c hb hbc s N).comp hcarrier).eventually
      (Iio_mem_nhds hε)
  have hratio :=
    tendsto_soninAperturePacketTransportRatio_one
      a b c ha hb hab hbc q haq hqb r hrpos hrgt hcr hr
  have hfull :
      ∀ᶠ n : ℕ in atTop,
        1 - ε <
          ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
              (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ /
            ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖ :=
    hratio.eventually (Ioi_mem_nhds (by linarith : 1 - ε < 1))
  exact hblind.and hfull

end RHTower
