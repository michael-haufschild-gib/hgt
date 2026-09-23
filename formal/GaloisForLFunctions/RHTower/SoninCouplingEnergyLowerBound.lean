import GaloisForLFunctions.RHTower.SoninCouplingNonannihilation
import GaloisForLFunctions.HTGeometry.HilbertSchmidtDominatesPointwise
import GaloisForLFunctions.RHTower.SoninApertureCurvatureTrace

/-!
# The coupling energy stays bounded away from zero along the clock

Normalising the wavepacket gives unit vectors whose image under the coupling has norm tending to
one.  The Hilbert--Schmidt energy dominates the image of any unit vector, so the coupling energies
do not merely stay nonzero along the clock — they stay above a fixed positive constant.

This is what makes a growing unit-weight source packet drive the aperture curvature trace to minus
infinity, rather than merely keeping it negative.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **Uniform energy floor.**  Along any clock past the crossing threshold the coupling energy is
eventually at least a quarter. -/
theorem eventually_le_hsNormSq_soninApertureCoupling
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n) (hrgt : ∀ n, 1 < r n) (hcr : ∀ n, c < r n * a)
    (hr : Tendsto r atTop atTop) :
    ∀ᶠ n : ℕ in atTop, (4 : ℝ)⁻¹ ≤
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)) := by
  have hq : 0 < q := ha.trans haq
  have hfreq : Tendsto (fun n : ℕ => 2 * Real.pi * (r n * q)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => r n * q) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hq hr
    exact Filter.Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) h1
  set L : ℝ := Real.sqrt ((2 : ℝ)⁻¹ * ∫ x : ℝ, soninAnnulusBump b c hbc x ^ (2 : ℕ)) with hL
  have hLpos : 0 < L := sqrt_half_energy_pos b c hb hbc
  have hpacket : Tendsto (fun n : ℕ =>
      ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 L) :=
    tendsto_norm_soninPacketEven b c hb hbc (fun n : ℕ => 2 * Real.pi * (r n * q)) hfreq
  have himage := tendsto_norm_soninApertureCoupling_apply_soninPacketEven a b c ha hb hab hbc q
    haq hqb r hrpos hrgt (fun n => (hcr n).le) hr
  have hratio : Tendsto (fun n : ℕ =>
      ‖evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n)
          (soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)))‖ /
        ‖soninPacketEven b c hb hbc (2 * Real.pi * (r n * q))‖) atTop (𝓝 1) := by
    have := himage.div hpacket hLpos.ne'
    rwa [div_self hLpos.ne'] at this
  filter_upwards [hratio (lt_mem_nhds (by norm_num : (2 : ℝ)⁻¹ < 1)),
    hpacket (lt_mem_nhds hLpos)] with n hn hpos
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hn hpos
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * (r n * q)) with hw
  set Z := evenSoninApertureSuccessiveLayerTransition a b c (r n) (hrgt n) with hZ
  set t : ℂ := ((‖w‖⁻¹ : ℝ) : ℂ) with ht
  have hunit : ‖t • w‖ = 1 := by
    rw [norm_smul, ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    field_simp
  have himg : ‖Z (t • w)‖ = ‖Z w‖ / ‖w‖ := by
    rw [map_smul, norm_smul, ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos)]
    field_simp
  have hHS := evenSoninApertureSuccessiveLayerTransition_isHilbertSchmidt ha hab hbc
    (hrgt n) (hcr n)
  have hdom : ‖Z (t • w)‖ ^ (2 : ℕ) ≤ hsNormSq Z :=
    norm_sq_apply_le_hsNormSq (by simpa [hZ] using hHS) hunit
  rw [himg] at hdom
  have hge : (2 : ℝ)⁻¹ ≤ ‖Z w‖ / ‖w‖ := le_of_lt hn
  nlinarith [hdom, hge, div_nonneg (norm_nonneg (Z w)) (norm_nonneg w)]

end RHTower
