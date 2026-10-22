import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodLeftClosure
import GaloisForLFunctions.RHTower.Sieve.InghamPoleRegularizedDetector
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling

/-!
# Weighted Littlewood lemma for Ingham's pole-regularized detector

Ingham's entire detector is `D_X(s) = G(s) M_X(s) (2(s-1) - G(s) M_X(s))`, where
`G(s) = (s-1) ζ(s)` and `M_X(s) = ∑_{n ≤ X} μ(n) n^{-s}`. This module applies the weighted
Littlewood (Jensen-type) rectangle identity to `D_X` on `[c,d] × [T₁,T₂]`: the zero sum
`2π ∑ ord_w(D_X) (Re w - c)` equals an explicit boundary functional of `log |D_X|` and of the
logarithmic derivative of `D_X`. Since every zero of `G` is a zero of `D_X` with at least the same
multiplicity, the weighted zeta-zero mass in the rectangle is bounded by that boundary functional.

## Main results

- `inghamLittlewoodBoundary`: the boundary side of the weighted Littlewood identity for `D_X`.
- `exists_inghamDetector_weighted_littlewood_rectangle`: the exact weighted Littlewood identity
  for the zeros of `D_X` in the closed rectangle.
- `two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary`: `2π` times the multiplicity-weighted sum
  of `(Re w - c)` over zeros `w` of `(s-1) ζ(s)` in the rectangle is at most the boundary functional.

## Hypotheses

The results hold for every mollifier length `X` and every nondegenerate rectangle `c < d`,
`T₁ < T₂`, assuming `D_X` has no zeros on the bottom edge, the top edge and the right edge `Re s = d`
of the rectangle. Zeros on the left edge are allowed; they carry weight zero.
-/

open Complex MeasureTheory intervalIntegral Set Topology

namespace RHTower.Sieve

noncomputable section

/-- Boundary side of the weighted Littlewood identity for `D_X` on `[c,d] × [T₁,T₂]`: the
difference of the vertical integrals of `log |D_X|` at `Re s = c` and `Re s = d`, plus
`(d - c) ∫ Re (D_X'/D_X)(d+it) dt`, plus the horizontal integrals of `(x - c) Im (D_X'/D_X)`
at height `T₁` minus those at height `T₂`. -/
noncomputable def inghamLittlewoodBoundary
    (X : ℕ) (c d T₁ T₂ : ℝ) : ℝ :=
  (∫ t in T₁..T₂, Real.log ‖inghamDetector X ((c : ℂ) + t * I)‖)
    - (∫ t in T₁..T₂, Real.log ‖inghamDetector X ((d : ℂ) + t * I)‖)
    + (d - c) *
      (∫ t in T₁..T₂, (logDeriv (inghamDetector X) ((d : ℂ) + t * I)).re)
    + (∫ x in c..d,
      (x - c) * (logDeriv (inghamDetector X) ((x : ℂ) + T₁ * I)).im)
    - ∫ x in c..d,
      (x - c) * (logDeriv (inghamDetector X) ((x : ℂ) + T₂ * I)).im

/-- Weighted Littlewood identity for Ingham's detector. Assuming `D_X` is nonzero on the bottom,
top and right edges of `[c,d] × [T₁,T₂]` (`c < d`, `T₁ < T₂`), the finite zero set `Z` of `D_X`
in the closed rectangle satisfies `2π ∑_{w ∈ Z} ord_w(D_X) (Re w - c) = inghamLittlewoodBoundary`. -/
theorem exists_inghamDetector_weighted_littlewood_rectangle
    (X : ℕ) {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, inghamDetector X ((d : ℂ) + t * I) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ inghamDetector X z = 0) ∧
      2 * Real.pi *
          (∑ w ∈ Z,
            ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c)) =
        inghamLittlewoodBoundary X c d T₁ T₂ := by
  have hne : ∃ z : ℂ, inghamDetector X z ≠ 0 :=
    ⟨(c : ℂ) + T₁ * I, hbot c left_mem_uIcc⟩
  simpa [inghamLittlewoodBoundary] using
    (exists_entire_weighted_littlewood_rectangle_left_boundary_zeros
      (inghamDetector_analyticOnNhd_univ X) hne hcd hT hbot htop hright)

/-- Zeta-zero mass bound from the detector identity. Under the same edge nonvanishing hypotheses
on `D_X`, `2π ∑ ord_w((s-1)ζ) (Re w - c)`, summed over zeros `w` of `(s-1)ζ(s)` in the closed
rectangle, is at most `inghamLittlewoodBoundary X c d T₁ T₂`. -/
theorem two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary
    (X : ℕ) {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, inghamDetector X ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, inghamDetector X ((d : ℂ) + t * I) ≠ 0) :
    2 * Real.pi *
        (∑ w ∈ zetaResidueUnitClosedRectangleZeros
            ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I),
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) ≤
      inghamLittlewoodBoundary X c d T₁ T₂ := by
  have hne : ∃ z : ℂ, inghamDetector X z ≠ 0 :=
    ⟨(c : ℂ) + T₁ * I, hbot c left_mem_uIcc⟩
  obtain ⟨Z, hmem, hboundary⟩ :=
    exists_inghamDetector_weighted_littlewood_rectangle X hcd hT
      hbot htop hright
  let ZG : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I)
  have hsub : ZG ⊆ Z := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_zetaResidueUnitClosedRectangleZeros.mp hw
    apply (hmem w).mpr
    refine ⟨?_, inghamDetector_eq_zero_of_zetaResidueUnit_eq_zero X hwzero⟩
    simpa [ZG] using hwK
  have hfirst :
      (∑ w ∈ ZG,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) ≤
        ∑ w ∈ ZG,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c) := by
    apply Finset.sum_le_sum
    intro w hw
    have hwK := (mem_zetaResidueUnitClosedRectangleZeros.mp hw).1
    have hwre := (Complex.mem_reProdIm.mp hwK).1
    have hwre' : w.re ∈ Set.Icc c d := by
      simpa [ZG, uIcc_of_le hcd.le] using hwre
    have hordN := zetaResidueUnit_multiplicity_le_inghamDetector X w hne
    have hordR : ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) ≤
        ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) := by
      exact_mod_cast hordN
    exact mul_le_mul_of_nonneg_right hordR (sub_nonneg.mpr hwre'.1)
  have hsecond :
      (∑ w ∈ ZG,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c)) ≤
        ∑ w ∈ Z,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro w hwZ _
    have hwK := ((hmem w).mp hwZ).1
    have hwre := (Complex.mem_reProdIm.mp hwK).1
    rw [uIcc_of_le hcd.le] at hwre
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hwre.1)
  have hmass :
      (∑ w ∈ ZG,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) ≤
        ∑ w ∈ Z,
          ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c) :=
    hfirst.trans hsecond
  calc
    2 * Real.pi *
        (∑ w ∈ zetaResidueUnitClosedRectangleZeros
            ((c : ℂ) + T₁ * I) ((d : ℂ) + T₂ * I),
          ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) =
        2 * Real.pi *
          (∑ w ∈ ZG,
            ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c)) := by rfl
    _ ≤ 2 * Real.pi *
          (∑ w ∈ Z,
            ((analyticOrderAt (inghamDetector X) w).toNat : ℝ) * (w.re - c)) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = inghamLittlewoodBoundary X c d T₁ T₂ := hboundary

end

end RHTower.Sieve
