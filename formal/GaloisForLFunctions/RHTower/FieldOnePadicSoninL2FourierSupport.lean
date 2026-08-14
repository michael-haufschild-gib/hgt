import GaloisForLFunctions.RHTower.FieldOnePadicRadialBruhatFourierSupport

/-!
# Closed Fourier-support theorem for radial p-adic Sonin vectors

Radial Bruhat gap vectors are dense among unit-invariant `L²` vectors with the
physical Sonin gap.  Contractivity of set projection and unitarity of Fourier
therefore extend their exact `p⁻¹ℤ_p` Fourier support to the full Hilbert space.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

theorem fieldOnePadicSoninOuterFourierBall_measurable :
    MeasurableSet (fieldOnePadicSoninOuterFourierBall p) :=
  (fieldOnePadicSoninBallSet_isClopen p 1).isOpen.measurableSet

theorem fieldOnePadicL2SetProjection_outerCompl_fourier_bruhat_eq_zero
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0) :
    fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninOuterFourierBall p)ᶜ
      (fieldOnePadicSoninOuterFourierBall_measurable p).compl
      (fieldOnePadicL2Fourier p
        (fieldOnePadicBruhatToL2Linear p f)) = 0 := by
  rw [fieldOnePadicL2Fourier_bruhat]
  apply Lp.ext
  filter_upwards [fieldOnePadicL2SetProjection_ae p
      (fieldOnePadicSoninOuterFourierBall p)ᶜ
      (fieldOnePadicSoninOuterFourierBall_measurable p).compl
      (fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicBruhatFourierLinearEquiv p f)),
    fieldOnePadicBruhatToL2_ae p
      (fieldOnePadicBruhatFourierLinearEquiv p f),
    Lp.coeFn_zero ℂ 2 (fieldOnePadicUnitBallNormalizedHaar p)]
      with x hproj hfourier hzero
  rw [hproj, hzero]
  have hfourier' :
      (((fieldOnePadicBruhatToL2Linear p
          (fieldOnePadicBruhatFourierLinearEquiv p f) : FieldOnePadicL2 p) :
            ℚ_[p] → ℂ) x) =
        (fieldOnePadicBruhatFourierLinearEquiv p f).1 x := by
    exact hfourier
  by_cases hx : x ∈ (fieldOnePadicSoninOuterFourierBall p)ᶜ
  · rw [Set.indicator_of_mem hx, hfourier']
    change (fieldOnePadicBruhatFourierLinear p f).1 x = 0
    exact fieldOnePadicRadialBruhat_fourier_eq_zero_outside_outer
      p f hunit hgap hx
  · rw [Set.indicator_of_notMem hx]
    rfl

theorem fieldOnePadicUnitInvariantGap_fourier_supported_outer
    {f : FieldOnePadicL2 p}
    (hunit : f ∈ FieldOnePadicUnitInvariantL2 p)
    (hgap : fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p) f = 0) :
    fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninOuterFourierBall p)ᶜ
      (fieldOnePadicSoninOuterFourierBall_measurable p).compl
      (fieldOnePadicL2Fourier p f) = 0 := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨g, hgunit, hggap, hgdist⟩ :=
    exists_radial_bruhat_gap_approx p hunit hgap hε
  have hgzero :=
    fieldOnePadicL2SetProjection_outerCompl_fourier_bruhat_eq_zero
      p g hgunit hggap
  calc
    dist (fieldOnePadicL2SetProjection p
        (fieldOnePadicSoninOuterFourierBall p)ᶜ
        (fieldOnePadicSoninOuterFourierBall_measurable p).compl
        (fieldOnePadicL2Fourier p f)) 0 =
        dist (fieldOnePadicL2SetProjection p
          (fieldOnePadicSoninOuterFourierBall p)ᶜ
          (fieldOnePadicSoninOuterFourierBall_measurable p).compl
          (fieldOnePadicL2Fourier p f))
        (fieldOnePadicL2SetProjection p
          (fieldOnePadicSoninOuterFourierBall p)ᶜ
          (fieldOnePadicSoninOuterFourierBall_measurable p).compl
          (fieldOnePadicL2Fourier p
            (fieldOnePadicBruhatToL2Linear p g))) := by rw [hgzero]
    _ ≤ dist (fieldOnePadicL2Fourier p f)
        (fieldOnePadicL2Fourier p
          (fieldOnePadicBruhatToL2Linear p g)) :=
      dist_fieldOnePadicL2SetProjection_le p _ _ _ _
    _ = dist f (fieldOnePadicBruhatToL2Linear p g) := by
      exact (fieldOnePadicL2Fourier p).isometry.dist_eq _ _
    _ ≤ ε := hgdist.le

end

end GaloisForLFunctions.RHTower
