import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheTwoFacesReadOneScaleDatum

/-!
# The arithmetic breaks the scale symmetry

On the zero side the scale is a free parameter. Every positive number occurs as a failure aperture
of some tempered configuration (`exists_mem_failureApertures`), because the lattice of spacing
`2π/ε` fails just above `ε/2`; so the zero-side scale unit has **no** universal floor, and
`sInf` over the whole data class of the first failure is `0`
(`not_bddBelow_floor_on_the_zero_side`).

On the prime side the picture is different. Whatever the weight, however large its tail, no failure
aperture lies below `3/10` (`weightFailureApertures_subset_Ioi_threeTenths`): the smallest prime
fixes an absolute window inside which the full Weil functional of *every* arithmetic weight is
nonnegative. The prime side therefore carries an absolute scale and the zero side does not
(`theArithmeticBreaksTheScaleSymmetry`).

This is the structural reason the problem is arithmetic. On the lattice family the depth is a free
invariant of the dilation action (`dilationEquiv_iff_sdDepth_eq`) and every scale certificate is a
coordinate along the orbits, so nothing analytic can pin the invariant. The primes are what breaks
that symmetry: they single out an absolute scale, and only data that see it can distinguish an orbit
from its dilates. Combined with the identity of the two faces on `ζ`
(`failureApertures_zetaConfig`), the scale datum of `ζ` inherits the absolute floor from the prime
side — an unconditional statement about the zeros that has no analogue for a general
configuration.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The zero side has no absolute scale -/

/-- **Every aperture is a failure aperture of some configuration.** The depth-`½` lattice of
spacing `2π/ε` fails just above `ε/2`. -/
theorem exists_mem_failureApertures {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : TemperedZeroConfig, ε ∈ failureApertures Z := by
  refine ⟨offLineLattice hε (by norm_num : (0 : ℝ) < 1 / 2) le_rfl, ?_⟩
  rw [failureApertures_offLineLattice hε (by norm_num) le_rfl]
  exact mem_Ioi.mpr (by linarith)

/-- **No universal floor on the zero side.** No positive number bounds the failure apertures of all
configurations from below. -/
theorem not_bddBelow_floor_on_the_zero_side :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ Z : TemperedZeroConfig, failureApertures Z ⊆ Ioi c := by
  rintro ⟨c, hc, h⟩
  obtain ⟨Z, hZ⟩ := exists_mem_failureApertures (half_pos hc)
  have := h Z hZ
  rw [mem_Ioi] at this
  linarith

/-! ### 2. The prime side has one -/

/-- Every weight is Weil-positive inside the absolute window of the smallest prime. -/
theorem bddBelow_floor_on_the_prime_side :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℕ → ℝ, weightFailureApertures lam ⊆ Ioi c :=
  ⟨3 / 10, by norm_num, weightFailureApertures_subset_Ioi_threeTenths⟩

/-! ### 3. The asymmetry -/

/-- **The arithmetic breaks the scale symmetry.** The zero-side scale unit admits no absolute
floor, the prime-side unit does, and on `ζ` the two units are the same set — so the configuration
of `ζ` inherits an absolute floor that no general configuration has. A mechanism that distinguishes
a configuration from its dilates must therefore read the arithmetic: the scale symmetry is broken
only there. -/
theorem theArithmeticBreaksTheScaleSymmetry :
    (¬ ∃ c : ℝ, 0 < c ∧ ∀ Z : TemperedZeroConfig, failureApertures Z ⊆ Ioi c) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ lam : ℕ → ℝ, weightFailureApertures lam ⊆ Ioi c) ∧
      failureApertures zetaConfig ⊆ Ioi (3 / 10) :=
  ⟨not_bddBelow_floor_on_the_zero_side, bddBelow_floor_on_the_prime_side,
    failureApertures_zetaConfig_subset_Ioi_threeTenths⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
