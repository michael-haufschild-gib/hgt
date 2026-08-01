import GaloisForLFunctions.RHTower.SoninLobeBumpFourier
import GaloisForLFunctions.RHTower.SoninRapidFourierDecay

/-!
# The reference profile decays rapidly

The reference profile is smooth with compact support, so its Fourier transform beats every
polynomial rate.  Since the lobe of any annulus has that same transform, read at the half-width
times the frequency, one decay statement governs the whole family.

This is the single function the rate argument has to bound: annulus centre, width and carrier enter
only through the argument `δ ξ`.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology FourierTransform ContDiff

/-- The reference profile is smooth. -/
theorem contDiff_soninUnitBumpC : ContDiff ℝ ∞ soninUnitBumpC :=
  Complex.ofRealCLM.contDiff.comp soninUnitBumpData.contDiff

/-- The reference profile has compact support. -/
theorem hasCompactSupport_soninUnitBumpC : HasCompactSupport soninUnitBumpC := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  have hbump : soninUnitBumpData x ≠ 0 := by
    intro hzero
    exact hx (by simp [soninUnitBumpC, hzero])
  have hball : |x| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hbump (soninUnitBumpData_eq_zero_of_one_le hcon)
  rw [Set.mem_Icc]
  rcases abs_lt.mp hball with ⟨h1, h2⟩
  constructor <;> linarith

/-- **Rapid decay of the reference profile.** -/
theorem tendsto_pow_mul_norm_fourier_soninUnitBumpC_atTop (N : ℕ) :
    Tendsto (fun w : ℝ => w ^ N * ‖𝓕 soninUnitBumpC w‖) atTop (𝓝 0) :=
  tendsto_pow_mul_norm_fourier_atTop hasCompactSupport_soninUnitBumpC contDiff_soninUnitBumpC N

/-- **The lobe's transform inherits the decay, in the rescaled variable.**  Along any family of
half-widths and frequencies whose product tends to infinity, the lobe's transform beats every
polynomial rate in that product. -/
theorem tendsto_pow_mul_norm_fourier_soninOneSidedBump
    (N : ℕ) (m δ : ℕ → ℝ) (hδ : ∀ i, 0 < δ i) (ξ : ℕ → ℝ)
    (hprod : Tendsto (fun i => δ i * ξ i) atTop atTop) :
    Tendsto (fun i =>
        (δ i * ξ i) ^ N *
          ‖𝓕 (fun x : ℝ => ((soninOneSidedBump (m i) (δ i) x : ℝ) : ℂ)) (ξ i)‖ / δ i)
      atTop (𝓝 0) := by
  have hbase := (tendsto_pow_mul_norm_fourier_soninUnitBumpC_atTop N).comp hprod
  refine hbase.congr fun i => ?_
  have hne : δ i ≠ 0 := (hδ i).ne'
  rw [Function.comp_apply, norm_fourier_soninOneSidedBump (m i) (δ i) (hδ i) (ξ i)]
  field_simp

end RHTower
