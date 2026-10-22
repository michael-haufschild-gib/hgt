import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHeightApertureSeamIsEmpty
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# The faces are incomparable

All the bounded readings of the field have the same floor, `½`, so the floors cannot distinguish
them. `TheRefutationOrderOnFaces` distinguishes them in the lower theory: the height face refutes and
the aperture face does not. This module shows that in the *refinement* order — which reading has the
other at its disposal — they are incomparable, so neither face is a weakening of the other and both
are needed.

* `not_refines_aperturePositivity_heightReading` — the aperture certificate does not refine the
  truncated divisor: the on-line lattice and the off-line lattice of the same spacing share the
  certificate at the Nyquist aperture and have different divisors, the off-line one carrying a zero
  off the line at ordinate `0`.
* `not_refines_heightReading_aperturePositivity` — the truncated divisor does not refine the
  certificate: the lattice with a visible pair inserted above the height shares the divisor with the
  on-line lattice and fails the certificate. "Visible" is the explicit inequality
  `2L + 2a < sinh (2δa)/δ` of the isolated-pair law.

`theFacesAreIncomparable` states both. The two faces therefore sit side by side: the aperture
certificate sees the far field and nothing local, the truncated divisor sees the local field and
nothing far, and their join is still trivial for the depth
(`TheHeightApertureSeamIsEmpty`). A mechanism may not substitute one for the other, and combining
them buys only what each gives separately.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The certificate does not see the local divisor -/

/-- At the Nyquist aperture the off-line lattice shares the certificate of the on-line lattice but
carries a zero off the line at ordinate `0`, which the truncated divisor records. -/
theorem not_refines_aperturePositivity_heightReading {a T δ : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ¬ Refines (aperturePositivity a) (heightReading T) := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  intro href
  have hmem : offLineLattice hL hδ hδ' ∈ shadow (aperturePositivity a) (onLineLattice hL) :=
    propext (iff_of_true
      ((offLineLattice_weil_positive_iff hL hδ hδ' a).mpr (by linarith))
      (aperturePositivity_onLineLattice hL a))
  have hread := href _ _ hmem
  -- evaluate the two divisors at the off-line point of ordinate `0`
  set ρ : ℂ := verticalLatticePoint (2 * a) δ 0 with hρ
  have hρim : ρ.im = 0 := by simp [hρ, verticalLatticePoint]
  have hρre : ρ.re = 1 / 2 + δ := by simp [hρ, verticalLatticePoint]
  have hmemoff : ρ ∈ heightWindow T (offLineLattice hL hδ hδ') :=
    mem_heightWindow.mpr ⟨Or.inl ⟨0, rfl⟩, by rw [hρim]; simpa using hT⟩
  have hoff : heightReading T (offLineLattice hL hδ hδ') ρ = 1 := by
    rw [heightReading_of_mem hmemoff]
    rfl
  have hnotmem : ρ ∉ heightWindow T (onLineLattice hL) := by
    intro hmem'
    obtain ⟨⟨k, hk⟩, -⟩ := mem_heightWindow.mp hmem'
    have : ρ.re = 1 / 2 := by rw [← hk]; simp [verticalLatticePoint]
    rw [hρre] at this
    linarith
  have hon : heightReading T (onLineLattice hL) ρ = 0 := heightReading_of_notMem hnotmem
  have := congrFun (mem_shadow_iff.mp hread) ρ
  rw [hoff, hon] at this
  exact absurd this (by norm_num)

/-! ### 2. The divisor does not see the far field -/

/-- A pair inserted above the height is invisible to the divisor and visible to the certificate, as
soon as the isolated-pair threshold is crossed. -/
theorem not_refines_heightReading_aperturePositivity {L a T δ : ℝ} (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L / 2) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hvis : 2 * L + 2 * a < Real.sinh (2 * δ * a) / δ) :
    ¬ Refines (heightReading T) (aperturePositivity a) := by
  intro href
  have hγ : T < |(|T| + 1 : ℝ)| := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |T| + 1)]
    linarith [le_abs_self T]
  have hmem : latticeWithPairAt hL hδ hδ' (|T| + 1) ∈
      shadow (heightReading T) (onLineLattice hL) :=
    heightReading_latticeWithPairAt hL hδ hδ' hγ
  have hread := href _ _ hmem
  have hpos : aperturePositivity a (latticeWithPairAt hL hδ hδ' (|T| + 1)) := by
    rw [mem_shadow_iff.mp hread]
    exact aperturePositivity_onLineLattice hL a
  have := (aperturePositivity_latticeWithPairAt_iff hL hδ hδ' (|T| + 1) ha haL).mp hpos
  linarith

/-! ### 3. Incomparability -/

/-- **The two bounded faces are incomparable.** Neither reading has the other at its disposal, so
neither can be dispensed with. -/
theorem theFacesAreIncomparable {L a T δ : ℝ} (hL : 0 < L) (ha : 0 < a) (haL : a ≤ L / 2)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hvis : 2 * L + 2 * a < Real.sinh (2 * δ * a) / δ) :
    ¬ Refines (aperturePositivity a) (heightReading T) ∧
      ¬ Refines (heightReading T) (aperturePositivity a) :=
  ⟨not_refines_aperturePositivity_heightReading ha hT hδ hδ',
    not_refines_heightReading_aperturePositivity hL ha haL hδ hδ' hvis⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
