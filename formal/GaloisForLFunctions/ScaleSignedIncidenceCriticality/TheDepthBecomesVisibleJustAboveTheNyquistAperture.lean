import GaloisForLFunctions.ScaleSignedIncidenceCriticality.CoercivityAtABoundedApertureIsStillBlind
import GaloisForLFunctions.SquareRootThreshold.RelaxedHodgeExponentOfOffLineLattices

/-!
# The depth becomes visible just above the Nyquist aperture

Two negative results bracket the finite-aperture programme. Below the Nyquist aperture of a
configuration, bare positivity is blind to the depth, and so is a coercive certificate of any
size (`resolutionLimit_width_apertureGain`). The question left open is where the depth first
becomes visible at all. The answer is: immediately above the Nyquist aperture, and only in the
quantitative deficit, never in the sign.

For the off-line lattice of spacing `2π/L` and depth `δ`, on apertures `a` with `L/2 < a ≤ L`,
the polar-constrained Weil floor is an exact threshold
(`weilFloorAtLevel_offLineLattice_iff_cosh`):

`WeilFloorAtLevel a η  ↔  2L(cosh(δL) − 1) ≤ η`.

* `latticeFloor_two` — the lattice floor at the second aliasing step is exactly `2 − 2cosh(δL)`,
  the rank-two Toeplitz section of the lattice symbol.
* `weilFloorThreshold_strictMono` — the threshold is strictly increasing in the depth, so distinct
  depths are separated by an explicit level (`exists_level_separating_depths`), and the graded
  trans-Nyquist reading determines the depth exactly
  (`weilFloorThreshold_injOn`).

Reading it together with the sub-Nyquist results gives the exact frontier of the aperture face:

| aperture | reading | depth |
| --- | --- | --- |
| `a ≤ L/2` | positivity | invisible |
| `a ≤ L/2` | coercive, any gap | invisible |
| `L/2 < a ≤ L` | quantitative deficit | determined exactly |

So a mechanism must do two things at once, and neither alone suffices: cross the Nyquist aperture
of the configuration it studies, and read the size of the deficit rather than its sign.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The lattice floor at the second aliasing step -/

/-- **The rank-two lattice floor.** At the second aliasing step the floor is `2 − 2cosh(δL)`,
read off the closed form `n − sinh(nδL)/sinh(δL)` of the lattice ground energy. -/
theorem latticeFloor_two {L δ : ℝ} (hδL : 0 < δ * L) :
    latticeFloor L δ 2 = 2 - 2 * Real.cosh (δ * L) := by
  have hs : Real.sinh (δ * L) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hδL)
  rw [latticeFloor_eq hδL 2]
  push_cast
  rw [show (2 : ℝ) * (δ * L) = 2 * (δ * L) from rfl, Real.sinh_two_mul]
  field_simp

/-! ### 2. The threshold just above the Nyquist aperture -/

/-- On `(L/2, L]` the aliasing index is exactly `2`. -/
theorem ceil_two_mul_div_eq_two {L a : ℝ} (hL : 0 < L) (ha : L / 2 < a) (haL : a ≤ L) :
    ⌈2 * a / L⌉₊ = 2 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor
  · rw [show ((2 : ℕ) - 1 : ℕ) = 1 from rfl]
    push_cast
    rw [lt_div_iff₀ hL]
    linarith
  · push_cast
    rw [div_le_iff₀ hL]
    linarith

/-- **The exact level threshold just above the Nyquist aperture.** -/
theorem weilFloorAtLevel_offLineLattice_iff_cosh {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {a : ℝ} (ha : L / 2 < a) (haL : a ≤ L) (η : ℝ) :
    WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η ↔
      2 * L * (Real.cosh (δ * L) - 1) ≤ η := by
  rw [offLineLattice_weilFloor_iff hL hδ hδ' ha η, ceil_two_mul_div_eq_two hL ha haL,
    latticeFloor_two (by positivity : 0 < δ * L)]
  constructor <;> intro h <;> nlinarith [h]

/-! ### 3. The threshold reads the depth -/

/-- The level threshold of a lattice at the second aliasing step. -/
noncomputable def weilFloorThreshold (L δ : ℝ) : ℝ := 2 * L * (Real.cosh (δ * L) - 1)

/-- **The threshold is strictly increasing in the depth.** -/
theorem weilFloorThreshold_strictMono {L : ℝ} (hL : 0 < L) {δ δ' : ℝ} (hδ : 0 < δ)
    (hlt : δ < δ') : weilFloorThreshold L δ < weilFloorThreshold L δ' := by
  have hδ'0 : 0 < δ' := hδ.trans hlt
  have hcosh : Real.cosh (δ * L) < Real.cosh (δ' * L) := by
    rw [Real.cosh_lt_cosh, abs_of_pos (by positivity : 0 < δ * L),
      abs_of_pos (by positivity : 0 < δ' * L)]
    exact mul_lt_mul_of_pos_right hlt hL
  have hprod : 0 < 2 * L * (Real.cosh (δ' * L) - Real.cosh (δ * L)) :=
    mul_pos (by linarith) (by linarith)
  simp only [weilFloorThreshold]
  linarith

/-- **The depth enters quadratically.** The first visible trace of an off-line pair of depth `δ`
is a deficit of order `L³δ²`: it has no first-order term in the depth. A mechanism with only
first-order sensitivity to the position of a zero therefore sees nothing, however far above the
Nyquist aperture it works. -/
theorem cube_mul_sq_le_weilFloorThreshold {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) :
    L ^ 3 * δ ^ 2 ≤ weilFloorThreshold L δ := by
  set y : ℝ := δ * L / 2 with hy
  have hy0 : 0 ≤ y := by simp only [hy]; positivity
  have hsinh : y ≤ Real.sinh y := Real.self_le_sinh_iff.mpr hy0
  have hsq : y ^ 2 ≤ Real.sinh y ^ 2 := by nlinarith
  have hcosh : Real.cosh (δ * L) = 2 * Real.sinh y ^ 2 + 1 := by
    have h2 : δ * L = 2 * y := by simp only [hy]; ring
    rw [h2, Real.cosh_two_mul, Real.cosh_sq]
    ring
  have hykey : (δ * L) ^ 2 / 4 = y ^ 2 := by simp only [hy]; ring
  rw [weilFloorThreshold, hcosh]
  nlinarith [hsq, hykey, hL.le, sq_nonneg (δ * L)]

/-- Distinct depths are separated by an explicit level: at `η` between the two thresholds the
shallower lattice has the floor and the deeper one does not. -/
theorem exists_level_separating_depths {L : ℝ} (hL : 0 < L) {δ δ' : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hlt : δ < δ') (hδ'' : δ' ≤ 1 / 2) {a : ℝ} (ha : L / 2 < a) (haL : a ≤ L) :
    ∃ η : ℝ, WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η ∧
      ¬ WeilFloorAtLevel (offLineLatticeConfig hL (hδ.trans hlt) hδ'') a η := by
  refine ⟨weilFloorThreshold L δ, ?_, ?_⟩
  · exact (weilFloorAtLevel_offLineLattice_iff_cosh hL hδ hδ' ha haL _).mpr le_rfl
  · intro h
    have := (weilFloorAtLevel_offLineLattice_iff_cosh hL (hδ.trans hlt) hδ'' ha haL _).mp h
    exact absurd this (not_le.mpr (weilFloorThreshold_strictMono hL hδ hlt))

/-- **The graded trans-Nyquist reading determines the depth.** The threshold map is injective on
depths, so the level at which a lattice acquires a Weil floor just above its Nyquist aperture
recovers its depth exactly. -/
theorem weilFloorThreshold_injOn {L : ℝ} (hL : 0 < L) :
    Set.InjOn (weilFloorThreshold L) (Ioc 0 (1 / 2)) := by
  intro δ hδ δ' hδ' heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd heq (ne_of_lt (weilFloorThreshold_strictMono hL hδ.1 h))
  · exact absurd heq.symm (ne_of_lt (weilFloorThreshold_strictMono hL hδ'.1 h))

/-- **The frontier of the aperture face.** Below the Nyquist aperture no certificate sees the
depth, however large its gap; just above it, the level threshold determines the depth exactly. -/
theorem theApertureFaceFrontier {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : L / 2 < a) (haL : a ≤ L) :
    (∀ b η : ℝ, 0 < b → ∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain b η Z) ∧
      Set.InjOn (weilFloorThreshold L) (Ioc 0 (1 / 2)) ∧
      ∀ δ : ℝ, ∀ hδ : 0 < δ, ∀ hδ' : δ ≤ 1 / 2, ∀ η : ℝ,
        (WeilFloorAtLevel (offLineLatticeConfig hL hδ hδ') a η ↔ weilFloorThreshold L δ ≤ η) :=
  ⟨fun _ η hb => exists_width_eq_half_apertureGain hb η, weilFloorThreshold_injOn hL,
    fun _ hδ hδ' η => weilFloorAtLevel_offLineLattice_iff_cosh hL hδ hδ' ha haL η⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
