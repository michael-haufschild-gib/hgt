import GaloisForLFunctions.RHTower.SoninCouplingEnergyLowerBound

/-!
# The coupling has asymptotic operator norm at least one

The normalised wavepacket is a unit vector whose image under the coupling has norm tending to one,
so the operator norm of the coupling is eventually above every level below one.

This is the operator-norm form of the cofinal nonannihilation: not only is the coupling nonzero, it
does not shrink.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **Operator-norm floor.**  Along any clock past the crossing threshold the coupling's operator
norm eventually exceeds every level below one. -/
theorem eventually_one_sub_le_norm_soninApertureCoupling
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c ≤ r n * a)
    (hr : Tendsto r atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      1 - ε ≤ ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)‖ := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  set L : ℝ := Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ 2) with hL
  have hLpos : 0 < L := sqrt_half_energy_pos b c hb hbc
  have hpacket : Tendsto (fun n : ℕ =>
      ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 L) :=
    tendsto_norm_soninPacketEven b c hb hbc (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have himage := tendsto_norm_soninApertureCoupling_apply_soninPacketEven a b c ha hb hab hbc q
    haq hqb r hrpos hrgt hcr hr
  have hratio : Tendsto (fun n : ℕ =>
      ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
          (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ /
        ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 1) := by
    have := himage.div hpacket hLpos.ne'
    rwa [div_self hLpos.ne'] at this
  filter_upwards [hratio (lt_mem_nhds (by linarith : 1 - ε < 1)),
    hpacket (lt_mem_nhds hLpos)] with n hn hpos
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hn hpos
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) with hw
  set Z := evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) with hZ
  have hdiv : ‖Z w‖ / ‖w‖ ≤ ‖Z‖ := by
    rw [div_le_iff₀ hpos]
    exact Z.le_opNorm w
  linarith [hn, hdiv]

end RHTower
