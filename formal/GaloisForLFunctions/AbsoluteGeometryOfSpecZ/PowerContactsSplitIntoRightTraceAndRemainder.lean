import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRightRemaindersHaveConvergentMeshes
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailRightZeroConvolutionTails
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerCombConvergencePaysContactAsymptotics

/-!
# The actual contact prefix splits into a right trace and a convergent remainder

The exact arithmetic convolution and the real part of the complete zero
convolution share the same divisor weights. Their sum is the remainder
mesh. Thus ordinary comb convergence reduces to convergence of the real
zero convolution once the right-band prime remainder is removed.
-/

noncomputable section

open Complex Finset Set MeasureTheory Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ZeroConfigurationGeometry

/-- The normalized harmonic convolution of the exact arithmetic remainder. -/
def normalizedPowerRightRemainder (a σ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (2 * a - 1) *
    ∑ m ∈ Icc 1 N, powerTailWeight (2 * a) m *
      powerTailPrimeRightRemainder a σ ((N : ℝ) / m)

/-- At every finite cutoff, the actual contact prefix is the remainder
mesh minus the real full zero convolution. -/
theorem normalizedPowerContacts_eq_remainder_sub_trace (a σ : ℝ) (N : ℕ) :
    normalizedPowerContacts a N = normalizedPowerRightRemainder a σ N -
      (powerTailRightZeroConvolution a σ N).re := by
  have hp : (∑ n ∈ Icc 1 N, (powerTailZeta (2 * a) * powerTailPrimeDeviation a) n) =
      ∑ m ∈ Icc 1 N, powerTailWeight (2 * a) m *
        ∑ n ∈ Icc 1 ⌊(N : ℝ) / m⌋₊, powerTailPrimeDeviation a n := by
    rw [RHTower.sum_Icc_mul_apply]
    apply Finset.sum_congr rfl
    intro m hm
    rw [powerTailZeta_apply (by have hh := (Finset.mem_Icc.mp hm).1; omega),
      Nat.floor_div_eq_div]
  have hr : (powerTailRightZeroConvolution a σ N).re =
      (N : ℝ) ^ (2 * a - 1) *
        ∑ m ∈ Icc 1 N, powerTailWeight (2 * a) m *
          (rightShiftedZeroTrace σ a a ((N : ℝ) / m)).re := by
    simp only [powerTailRightZeroConvolution, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.re_sum]
  rw [normalizedPowerContacts, hp, normalizedPowerRightRemainder, hr]
  simp_rw [powerTailPrimeRightRemainder, mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- In a subcritical right band, ordinary comb convergence is exactly
convergence of the real zero convolution; the arithmetic remainder
already has its genuine integral limit. -/
theorem powerCombTailConverges_iff_rightZeroConvolution_converges {a σ : ℝ}
    (ha : 0 < a) (ha2 : a < 1 / 2) (hσ : 1 / 2 < σ) (hσβ : σ < 1 - a)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 - a) :
    PowerCombTailConverges a ↔
      ∃ L : ℝ, Tendsto (fun N : ℕ => (powerTailRightZeroConvolution a σ N).re)
        atTop (𝓝 L) := by
  rw [powerCombTailConverges_iff_normalizedPowerContacts_converges ha ha2]
  have hR : Tendsto (normalizedPowerRightRemainder a σ) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1,
        t ^ (-(2 * a)) * powerTailPrimeRightRemainder a σ (1 / t))) :=
    tendsto_normalized_powerTailPrimeRightRemainder ha ha2 hσ hσβ hβ
  constructor
  · rintro ⟨L, hL⟩
    refine ⟨_, (hR.sub hL).congr fun N => ?_⟩
    have he := normalizedPowerContacts_eq_remainder_sub_trace a σ N
    linarith only [he]
  · rintro ⟨L, hL⟩
    refine ⟨_, (hR.sub hL).congr fun N => ?_⟩
    exact (normalizedPowerContacts_eq_remainder_sub_trace a σ N).symm

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
