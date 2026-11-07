import GaloisForLFunctions.SelbergClass.Primon.KestenMcKay
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Sharp uniform semicircle limit of the prime phase densities

The explicit Kesten–McKay phase density approaches the Sato–Tate phase
density `2 sin²(πt)` uniformly. The supremum distance is exactly `2/(p+1)`,
attained at the central phase. This concerns the explicit density family.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The semicircle distribution in the phase coordinate `x = 2 cos(πt)`. -/
def semicirclePhaseDensity (t : ℝ) : ℝ := 2 * Real.sin (Real.pi * t) ^ 2

/-- A sine-square denominator makes positivity and the large-prime limit explicit. -/
theorem kestenMcKayDensity_eq_sine_square (p : Nat.Primes) (t : ℝ) :
    kestenMcKayDensity p t =
      2 * (p : ℝ) * ((p : ℝ) + 1) * Real.sin (Real.pi * t) ^ 2 /
        (((p : ℝ) - 1) ^ 2 + 4 * (p : ℝ) * Real.sin (Real.pi * t) ^ 2) := by
  unfold kestenMcKayDensity
  congr 1
  rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul]
  nlinarith only [Real.sin_sq_add_cos_sq (Real.pi * t)]

/-- The uniform phase error has a prime-exact upper bound. -/
theorem abs_kestenMcKayDensity_sub_semicircle_le (p : Nat.Primes) (t : ℝ) :
    |kestenMcKayDensity p t - semicirclePhaseDensity t| ≤ 2 / ((p : ℝ) + 1) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hu0 := sq_nonneg (Real.sin (Real.pi * t))
  have hu1 : Real.sin (Real.pi * t) ^ 2 ≤ 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq (Real.pi * t), sq_nonneg (Real.cos (Real.pi * t))]
  rw [kestenMcKayDensity_eq_sine_square, semicirclePhaseDensity]
  generalize Real.sin (Real.pi * t) ^ 2 = u at hu0 hu1 ⊢
  have hp1 : 0 < (p : ℝ) + 1 := by linarith only [hp]
  have hD : 0 < ((p : ℝ) - 1) ^ 2 + 4 * (p : ℝ) * u := by
    have hs := sq_pos_of_pos (show 0 < (p : ℝ) - 1 by linarith only [hp])
    have hm : 0 ≤ 4 * (p : ℝ) * u := by positivity
    linarith only [hs, hm]
  have he : 2 * (p : ℝ) * ((p : ℝ) + 1) * u /
      (((p : ℝ) - 1) ^ 2 + 4 * (p : ℝ) * u) - 2 * u =
      (2 * u * (3 * (p : ℝ) - 1 - 4 * (p : ℝ) * u)) /
        (((p : ℝ) - 1) ^ 2 + 4 * (p : ℝ) * u) := by
    field_simp [ne_of_gt hD]
    ring
  rw [he, abs_le]
  constructor
  · rw [neg_div, div_le_div_iff₀ hp1 hD]
    have hfactor : 0 ≤ (1 - u) *
        (4 * (p : ℝ) * ((p : ℝ) + 1) * u + ((p : ℝ) - 1) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hu1) (by positivity)
    nlinarith only [hfactor]
  · rw [div_le_div_iff₀ hD hp1]
    have hs := sq_nonneg (2 * (p : ℝ) * u - ((p : ℝ) - 1))
    have h1 : 0 ≤ 4 * (p : ℝ) * u ^ 2 := by positivity
    have h2 : 0 ≤ ((p : ℝ) - 1) ^ 2 * u := by positivity
    nlinarith only [hs, h1, h2]

/-- The central phase attains the uniform error, proving sharpness. -/
theorem kestenMcKayDensity_sub_semicircle_half (p : Nat.Primes) :
    kestenMcKayDensity p (1 / 2) - semicirclePhaseDensity (1 / 2) =
      -(2 / ((p : ℝ) + 1)) := by
  have hp : (p : ℝ) + 1 ≠ 0 := by positivity
  have hD : ((p : ℝ) - 1) ^ 2 + 4 * (p : ℝ) = ((p : ℝ) + 1) ^ 2 := by ring
  rw [kestenMcKayDensity_eq_sine_square, semicirclePhaseDensity,
    show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  simp only [one_pow, mul_one]
  rw [hD]
  field_simp [hp]
  ring

/-- Prime phase density as an element of the sup-norm space on the closed unit interval. -/
def kestenDensityOnUnit (p : Nat.Primes) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t => kestenMcKayDensity p t,
    (continuous_kestenMcKayDensity p).comp continuous_subtype_val⟩

/-- The limiting phase density on the same compact interval. -/
def semicircleDensityOnUnit : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun t => semicirclePhaseDensity t, by unfold semicirclePhaseDensity; fun_prop⟩

/-- Exact sup-norm distance from the limiting phase law. -/
theorem norm_kestenDensityOnUnit_sub_semicircle (p : Nat.Primes) :
    ‖kestenDensityOnUnit p - semicircleDensityOnUnit‖ = 2 / ((p : ℝ) + 1) := by
  have hC : 0 ≤ 2 / ((p : ℝ) + 1) := by positivity
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ hC).mpr
    intro t
    change ‖kestenMcKayDensity p t - semicirclePhaseDensity t‖ ≤ _
    rw [Real.norm_eq_abs]
    exact abs_kestenMcKayDensity_sub_semicircle_le p t
  · have h := ContinuousMap.norm_coe_le_norm (kestenDensityOnUnit p - semicircleDensityOnUnit)
      (⟨1 / 2, by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)
    change ‖kestenMcKayDensity p (1 / 2) - semicirclePhaseDensity (1 / 2)‖ ≤ _ at h
    rwa [kestenMcKayDensity_sub_semicircle_half, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg hC] at h

/-- The explicit prime phase laws converge in the sup norm as primes escape finite sets. -/
theorem tendsto_kestenDensityOnUnit :
    Tendsto kestenDensityOnUnit cofinite (𝓝 semicircleDensityOnUnit) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_kestenDensityOnUnit_sub_semicircle, div_eq_mul_inv]
  have hp : Tendsto (fun p : Nat.Primes => (p : ℝ) + 1) cofinite atTop :=
    tendsto_atTop_add_const_right cofinite 1 tendsto_primeReal_cofinite_atTop
  simpa only [mul_zero, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp hp).const_mul 2

end
end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenMcKayDensity_eq_sine_square
#print axioms GaloisForLFunctions.SelbergClass.Primon.abs_kestenMcKayDensity_sub_semicircle_le
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenMcKayDensity_sub_semicircle_half
#print axioms GaloisForLFunctions.SelbergClass.Primon.norm_kestenDensityOnUnit_sub_semicircle
#print axioms GaloisForLFunctions.SelbergClass.Primon.tendsto_kestenDensityOnUnit
