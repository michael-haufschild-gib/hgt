import GaloisForLFunctions.RHTower.FieldOnePadicRadialBruhatTwoShell

/-!
# Two-shell closure of the unit-invariant p-adic Sonin space

Fourier inversion on radial Bruhat approximants extends to the full radial
Sonin `L²` space.  Both a vector and its Fourier transform are consequently
supported in `p⁻¹ℤ_p`, and finite-dimensional closedness forces the vector
into the span of `ε₀, ε₁`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

theorem fieldOnePadicBruhatFourierLinear_sq_eq_self_of_unitInvariant
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x) :
    fieldOnePadicBruhatFourierLinear p
      (fieldOnePadicBruhatFourierLinear p f) = f := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change fieldOnePadicBruhatFourier p
    (fieldOnePadicBruhatFourierBruhat p f) x = f.1 x
  rw [fieldOnePadicBruhatFourier_fourier]
  have hneg := hunit (-1) x
  simpa using hneg

theorem fieldOnePadicL2Fourier_sq_eq_self_of_unitInvariantGap
    {f : FieldOnePadicL2 p}
    (hunit : f ∈ FieldOnePadicUnitInvariantL2 p)
    (hgap : fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p) f = 0) :
    fieldOnePadicL2Fourier p (fieldOnePadicL2Fourier p f) = f := by
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨g, hgunit, hggap, hgdist⟩ :=
    exists_radial_bruhat_gap_approx p hunit hgap (half_pos hε)
  have hgsq : fieldOnePadicL2Fourier p
      (fieldOnePadicL2Fourier p
        (fieldOnePadicBruhatToL2Linear p g)) =
      fieldOnePadicBruhatToL2Linear p g := by
    rw [fieldOnePadicL2Fourier_bruhat,
      fieldOnePadicL2Fourier_bruhat]
    apply congrArg (fieldOnePadicBruhatToL2Linear p)
    exact fieldOnePadicBruhatFourierLinear_sq_eq_self_of_unitInvariant
      p g hgunit
  have hdistsq :
      dist (fieldOnePadicL2Fourier p (fieldOnePadicL2Fourier p f))
          (fieldOnePadicL2Fourier p
            (fieldOnePadicL2Fourier p
              (fieldOnePadicBruhatToL2Linear p g))) =
        dist f (fieldOnePadicBruhatToL2Linear p g) := by
    rw [(fieldOnePadicL2Fourier p).isometry.dist_eq,
      (fieldOnePadicL2Fourier p).isometry.dist_eq]
  calc
    dist (fieldOnePadicL2Fourier p (fieldOnePadicL2Fourier p f)) f ≤
        dist (fieldOnePadicL2Fourier p (fieldOnePadicL2Fourier p f))
          (fieldOnePadicL2Fourier p
            (fieldOnePadicL2Fourier p
              (fieldOnePadicBruhatToL2Linear p g))) +
        dist (fieldOnePadicL2Fourier p
            (fieldOnePadicL2Fourier p
              (fieldOnePadicBruhatToL2Linear p g))) f :=
      dist_triangle _ _ _
    _ = dist f (fieldOnePadicBruhatToL2Linear p g) +
        dist (fieldOnePadicBruhatToL2Linear p g) f := by
      rw [hdistsq, hgsq]
    _ ≤ ε := by
      rw [dist_comm (fieldOnePadicBruhatToL2Linear p g) f]
      linarith

theorem fieldOnePadicUnitInvariantSonin_supported_outer
    {f : FieldOnePadicL2 p}
    (hunit : f ∈ FieldOnePadicUnitInvariantL2 p)
    (hsonin : f ∈ FieldOnePadicSoninL2 p) :
    fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninOuterFourierBall p)ᶜ
      (fieldOnePadicSoninOuterFourierBall_measurable p).compl f = 0 := by
  change fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p) f = 0 ∧
    fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)
      (fieldOnePadicL2Fourier p f) = 0 at hsonin
  have hFunit := fieldOnePadicL2Fourier_mem_unitInvariant p hunit
  have hsupport := fieldOnePadicUnitInvariantGap_fourier_supported_outer
    p hFunit hsonin.2
  rw [fieldOnePadicL2Fourier_sq_eq_self_of_unitInvariantGap
    p hunit hsonin.1] at hsupport
  exact hsupport

def fieldOnePadicSoninShellL2 (n : ℤ) : FieldOnePadicL2 p :=
  fieldOnePadicBruhatToL2Linear p (fieldOnePadicSoninShell p n)

def FieldOnePadicTwoShellL2 : Submodule ℂ (FieldOnePadicL2 p) :=
  Submodule.span ℂ ({fieldOnePadicSoninShellL2 p 0,
    fieldOnePadicSoninShellL2 p 1} : Set (FieldOnePadicL2 p))

theorem fieldOnePadicTwoShellL2_isClosed :
    IsClosed (FieldOnePadicTwoShellL2 p : Set (FieldOnePadicL2 p)) := by
  change IsClosed (Submodule.span ℂ
    ({fieldOnePadicSoninShellL2 p 0,
      fieldOnePadicSoninShellL2 p 1} : Set (FieldOnePadicL2 p)) :
        Set (FieldOnePadicL2 p))
  letI : FiniteDimensional ℂ (Submodule.span ℂ
      ({fieldOnePadicSoninShellL2 p 0,
        fieldOnePadicSoninShellL2 p 1} : Set (FieldOnePadicL2 p))) :=
    FiniteDimensional.span_of_finite ℂ (by simp)
  exact Submodule.closed_of_finiteDimensional _

theorem fieldOnePadicBruhatToL2_radialOuter_mem_twoShell
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0)
    (houter : ∀ x, x ∉ fieldOnePadicSoninOuterFourierBall p → f.1 x = 0) :
    fieldOnePadicBruhatToL2Linear p f ∈ FieldOnePadicTwoShellL2 p := by
  rw [fieldOnePadicRadialOuterBruhat_eq_twoShells p f hunit hgap houter]
  change fieldOnePadicRadialShellCoefficient p f 0 •
      fieldOnePadicSoninShellL2 p 0 +
    fieldOnePadicRadialShellCoefficient p f 1 •
      fieldOnePadicSoninShellL2 p 1 ∈ FieldOnePadicTwoShellL2 p
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)
  · apply Submodule.smul_mem
    exact Submodule.subset_span (by simp)

def fieldOnePadicSoninOuterBruhatCut
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicBruhatRestrict p
    (fieldOnePadicSoninOuterFourierBall p)
    (fieldOnePadicSoninBallSet_isClopen p 1) f

theorem fieldOnePadicSoninOuterBruhatCut_unitInvariant
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hf : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x) :
    ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      (fieldOnePadicSoninOuterBruhatCut p f).1
          ((((u : ℤ_[p]) : ℚ_[p])) * x) =
        (fieldOnePadicSoninOuterBruhatCut p f).1 x :=
  fieldOnePadicBruhatRestrict_soninBall_unitInvariant p 1 f hf

theorem fieldOnePadicSoninOuterBruhatCut_gap
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hf : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0) :
    ∀ x ∈ fieldOnePadicSoninInnerBall p,
      (fieldOnePadicSoninOuterBruhatCut p f).1 x = 0 := by
  intro x hx
  rw [fieldOnePadicSoninOuterBruhatCut,
    fieldOnePadicBruhatRestrict_apply]
  by_cases hxo : x ∈ fieldOnePadicSoninOuterFourierBall p
  · rw [Set.indicator_of_mem hxo, hf x hx]
  · rw [Set.indicator_of_notMem hxo]

theorem fieldOnePadicSoninOuterBruhatCut_zero_outside
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    ∀ x, x ∉ fieldOnePadicSoninOuterFourierBall p →
      (fieldOnePadicSoninOuterBruhatCut p f).1 x = 0 := by
  intro x hx
  rw [fieldOnePadicSoninOuterBruhatCut,
    fieldOnePadicBruhatRestrict_apply, Set.indicator_of_notMem hx]

theorem fieldOnePadicSoninOuterBruhatCut_mem_twoShell
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0) :
    fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicSoninOuterBruhatCut p f) ∈
      FieldOnePadicTwoShellL2 p :=
  fieldOnePadicBruhatToL2_radialOuter_mem_twoShell p
    (fieldOnePadicSoninOuterBruhatCut p f)
    (fieldOnePadicSoninOuterBruhatCut_unitInvariant p f hunit)
    (fieldOnePadicSoninOuterBruhatCut_gap p f hgap)
    (fieldOnePadicSoninOuterBruhatCut_zero_outside p f)

theorem fieldOnePadicBruhatToL2_soninOuterCut
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicSoninOuterBruhatCut p f) =
      fieldOnePadicL2SetProjection p
        (fieldOnePadicSoninOuterFourierBall p)
        (fieldOnePadicSoninOuterFourierBall_measurable p)
        (fieldOnePadicBruhatToL2Linear p f) :=
  fieldOnePadicBruhatToL2_restrict p _ _ f

theorem dist_fieldOnePadicSoninOuterBruhatCut_le
    (f : FieldOnePadicL2 p)
    (g : compactlySupportedLocallyConstant ℚ_[p])
    (hfouter : fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninOuterFourierBall p)ᶜ
      (fieldOnePadicSoninOuterFourierBall_measurable p).compl f = 0) :
    dist f (fieldOnePadicBruhatToL2Linear p
      (fieldOnePadicSoninOuterBruhatCut p g)) ≤
        dist f (fieldOnePadicBruhatToL2Linear p g) := by
  rw [fieldOnePadicBruhatToL2_soninOuterCut]
  have hfself := fieldOnePadicL2SetProjection_compl_eq_self_of_eq_zero p
    (fieldOnePadicSoninOuterFourierBall p)ᶜ
    (fieldOnePadicSoninOuterFourierBall_measurable p).compl f hfouter
  have hfself' : fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninOuterFourierBall p)
      (fieldOnePadicSoninOuterFourierBall_measurable p) f = f := by
    simpa only [compl_compl] using hfself
  calc
    dist f (fieldOnePadicL2SetProjection p
        (fieldOnePadicSoninOuterFourierBall p)
        (fieldOnePadicSoninOuterFourierBall_measurable p)
        (fieldOnePadicBruhatToL2Linear p g)) =
      dist (fieldOnePadicL2SetProjection p
          (fieldOnePadicSoninOuterFourierBall p)
          (fieldOnePadicSoninOuterFourierBall_measurable p) f)
        (fieldOnePadicL2SetProjection p
          (fieldOnePadicSoninOuterFourierBall p)
          (fieldOnePadicSoninOuterFourierBall_measurable p)
          (fieldOnePadicBruhatToL2Linear p g)) := by rw [hfself']
    _ ≤ dist f (fieldOnePadicBruhatToL2Linear p g) :=
      dist_fieldOnePadicL2SetProjection_le p _ _ f
        (fieldOnePadicBruhatToL2Linear p g)

theorem exists_fieldOnePadicTwoShell_approx
    {f : FieldOnePadicL2 p}
    (hunit : f ∈ FieldOnePadicUnitInvariantL2 p)
    (hgap : fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p) f = 0)
    (hfouter : fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninOuterFourierBall p)ᶜ
      (fieldOnePadicSoninOuterFourierBall_measurable p).compl f = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g ∈ FieldOnePadicTwoShellL2 p, dist f g < ε := by
  obtain ⟨g, hgunit, hggap, hgdist⟩ :=
    exists_radial_bruhat_gap_approx p hunit hgap hε
  refine ⟨fieldOnePadicBruhatToL2Linear p
      (fieldOnePadicSoninOuterBruhatCut p g),
    fieldOnePadicSoninOuterBruhatCut_mem_twoShell p g hgunit hggap, ?_⟩
  exact (dist_fieldOnePadicSoninOuterBruhatCut_le p f g hfouter).trans_lt hgdist

theorem fieldOnePadicUnitInvariantSonin_mem_twoShell
    {f : FieldOnePadicL2 p}
    (hunit : f ∈ FieldOnePadicUnitInvariantL2 p)
    (hsonin : f ∈ FieldOnePadicSoninL2 p) :
    f ∈ FieldOnePadicTwoShellL2 p := by
  change fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p) f = 0 ∧
    fieldOnePadicL2SetProjection p
      (fieldOnePadicSoninInnerBall p)
      (fieldOnePadicSoninInnerBall_measurable p)
      (fieldOnePadicL2Fourier p f) = 0 at hsonin
  have hfouter := fieldOnePadicUnitInvariantSonin_supported_outer p hunit hsonin
  change f ∈ (FieldOnePadicTwoShellL2 p : Set (FieldOnePadicL2 p))
  rw [← (fieldOnePadicTwoShellL2_isClosed p).closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  exact exists_fieldOnePadicTwoShell_approx p hunit hsonin.1 hfouter hε

end

end GaloisForLFunctions.RHTower
