import GaloisForLFunctions.HTGeometry.StrictAccretiveMultiplier
import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezin
import GaloisForLFunctions.RHTower.BurnolCoPoissonSubWindowSource
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# Burnol divided-shift source leakage

In Mellin coordinates Burnol's forward divided shift has Cauchy symbol

`m_rho(t) = 1 / (rho - (1/2 + i t))`.

Writing `delta = Re rho - 1/2`, the symbol satisfies the exact Herglotz law
`Re m_rho = delta * |m_rho|²`.  Hence the divided shift is strictly accretive whenever
`delta > 0`.  A nonzero co-Poisson source vector therefore cannot be sent wholly into the source
orthogonal complement.  Its retained source projection is not merely nonzero: its norm controls
`delta` times the full divided-shift energy.

The final theorems instantiate this at every actual right-half Xi divisor point with the explicit
sub-window co-Poisson atom.  No critical-line placement, RH, kernel tightness, or source-flatness
hypothesis is used.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace RHTower

/-- Cauchy symbol of the forward Burnol divided shift on the critical Mellin line. -/
def burnolDividedShiftSymbol (rho : ℂ) (t : ℝ) : ℂ :=
  (rho - criticalLineArgument t)⁻¹

theorem measurable_burnolDividedShiftSymbol (rho : ℂ) :
    Measurable (burnolDividedShiftSymbol rho) := by
  apply Measurable.inv
  exact (by
    unfold criticalLineArgument
    fun_prop : Continuous (fun t : ℝ => rho - criticalLineArgument t)).measurable

theorem burnolDividedShiftSymbol_ne_zero {rho : ℂ} (h : 1 / 2 < rho.re) (t : ℝ) :
    burnolDividedShiftSymbol rho t ≠ 0 := by
  apply inv_ne_zero
  intro hz
  have hre := congrArg Complex.re hz
  simp [criticalLineArgument] at hre
  linarith

/-- The Cauchy symbol is uniformly bounded by inverse horizontal distance to the critical line. -/
theorem norm_burnolDividedShiftSymbol_le {rho : ℂ} (h : 1 / 2 < rho.re) (t : ℝ) :
    ‖burnolDividedShiftSymbol rho t‖ ≤ (rho.re - 1 / 2)⁻¹ := by
  rw [burnolDividedShiftSymbol, norm_inv]
  have hre : rho.re - 1 / 2 ≤ ‖rho - criticalLineArgument t‖ := by
    have habs := Complex.abs_re_le_norm (rho - criticalLineArgument t)
    rw [Complex.sub_re, criticalLineArgument_re, abs_of_pos (by linarith)] at habs
    exact habs
  exact (inv_le_inv₀ (lt_of_lt_of_le (by linarith) hre) (by linarith)).2 hre

/-- Exact pointwise Herglotz identity for the Cauchy symbol. -/
theorem re_burnolDividedShiftSymbol_eq {rho : ℂ} (h : 1 / 2 < rho.re) (t : ℝ) :
    (burnolDividedShiftSymbol rho t).re =
      (rho.re - 1 / 2) * Complex.normSq (burnolDividedShiftSymbol rho t) := by
  have hz : rho - criticalLineArgument t ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp [criticalLineArgument] at hre
    linarith
  rw [burnolDividedShiftSymbol, Complex.inv_re, Complex.normSq_inv]
  rw [Complex.sub_re, criticalLineArgument_re]
  have hsq : Complex.normSq (rho - criticalLineArgument t) ≠ 0 :=
    fun hs => hz (Complex.normSq_eq_zero.mp hs)
  field_simp [hsq]

/-- Bounded spectral divided shift, acting by the Cauchy symbol on Mellin `L²`. -/
def burnolSpectralDividedShift {rho : ℂ} (h : 1 / 2 < rho.re) :
    SpectralL2 →L[ℂ] SpectralL2 :=
  lpBoundedMulCLM (p := 2) (μ := volume)
    (measurable_burnolDividedShiftSymbol rho) (inv_nonneg.mpr (by linarith))
    (norm_burnolDividedShiftSymbol_le h)

theorem burnolSpectralDividedShift_ae {rho : ℂ} (h : 1 / 2 < rho.re)
    (f : SpectralL2) :
    burnolSpectralDividedShift h f =ᵐ[volume]
      fun t => burnolDividedShiftSymbol rho t * f t :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := volume)
    (measurable_burnolDividedShiftSymbol rho) (inv_nonneg.mpr (by linarith))
    (norm_burnolDividedShiftSymbol_le h) f

/-- Exact strict-accretivity identity for the spectral divided shift. -/
theorem re_inner_burnolSpectralDividedShift_eq {rho : ℂ} (h : 1 / 2 < rho.re)
    (f : SpectralL2) :
    (inner ℂ f (burnolSpectralDividedShift h f)).re =
      (rho.re - 1 / 2) * ‖burnolSpectralDividedShift h f‖ ^ 2 := by
  exact GaloisForLFunctions.HTGeometry.lpBoundedMulCLM_re_inner_eq
    (measurable_burnolDividedShiftSymbol rho) (inv_nonneg.mpr (by linarith))
    (norm_burnolDividedShiftSymbol_le h) (re_burnolDividedShiftSymbol_eq h) f

/-- A nonzero vector cannot be shifted into the orthogonal complement of a spectral subspace that
contains it. -/
theorem burnolSpectralDividedShift_not_mem_orthogonal
    {rho : ℂ} (h : 1 / 2 < rho.re) (S : Submodule ℂ SpectralL2)
    {f : SpectralL2} (hfS : f ∈ S) (hf : f ≠ 0) :
    burnolSpectralDividedShift h f ∉ Sᗮ := by
  exact GaloisForLFunctions.HTGeometry.lpBoundedMulCLM_not_mem_orthogonal_of_strictAccretive
    (measurable_burnolDividedShiftSymbol rho) (inv_nonneg.mpr (by linarith))
    (norm_burnolDividedShiftSymbol_le h) (re_burnolDividedShiftSymbol_eq h)
    (by linarith) (burnolDividedShiftSymbol_ne_zero h) S hfS hf

/-- Mellin realization of Burnol's forward divided shift on the even physical space. -/
def burnolMellinDividedShift {rho : ℂ} (h : 1 / 2 < rho.re) :
    evenSubspace →L[ℂ] evenSubspace :=
  unitaryPush archimedeanMellinUnitary.symm (burnolSpectralDividedShift h)

/-- Exact strict accretivity transported back to the even physical space. -/
theorem re_inner_burnolMellinDividedShift_eq {rho : ℂ} (h : 1 / 2 < rho.re)
    (f : evenSubspace) :
    (inner ℂ f (burnolMellinDividedShift h f)).re =
      (rho.re - 1 / 2) * ‖burnolMellinDividedShift h f‖ ^ 2 := by
  have hspec := re_inner_burnolSpectralDividedShift_eq h (archimedeanMellinUnitary f)
  have hinner :
      inner ℂ f (archimedeanMellinUnitary.symm
        (burnolSpectralDividedShift h (archimedeanMellinUnitary f))) =
        inner ℂ (archimedeanMellinUnitary f)
          (burnolSpectralDividedShift h (archimedeanMellinUnitary f)) := by
    simpa using archimedeanMellinUnitary.symm.inner_map_map
      (archimedeanMellinUnitary f)
      (burnolSpectralDividedShift h (archimedeanMellinUnitary f))
  change (inner ℂ f (archimedeanMellinUnitary.symm
    (burnolSpectralDividedShift h (archimedeanMellinUnitary f)))).re =
      (rho.re - 1 / 2) * ‖archimedeanMellinUnitary.symm
        (burnolSpectralDividedShift h (archimedeanMellinUnitary f))‖ ^ 2
  rw [hinner]
  simpa using hspec

/-- The physical divided-shift quadratic pairing is nonzero on every nonzero vector. -/
theorem burnolMellinDividedShift_inner_ne_zero {rho : ℂ} (h : 1 / 2 < rho.re)
    {f : evenSubspace} (hf : f ≠ 0) :
    inner ℂ f (burnolMellinDividedShift h f) ≠ 0 := by
  intro hzero
  have hspec : burnolSpectralDividedShift h (archimedeanMellinUnitary f) ≠ 0 := by
    intro hz
    have hinj := GaloisForLFunctions.HTGeometry.lpBoundedMulCLM_injective_general
      (p := (2 : ENNReal)) (μ := volume)
      (measurable_burnolDividedShiftSymbol rho) (inv_nonneg.mpr (by linarith))
      (norm_burnolDividedShiftSymbol_le h) (burnolDividedShiftSymbol_ne_zero h)
    apply hf
    apply archimedeanMellinUnitary.injective
    apply hinj
    simpa [burnolSpectralDividedShift] using hz
  have hreal := re_inner_burnolMellinDividedShift_eq h f
  rw [hzero] at hreal
  norm_num at hreal
  have hphys : burnolMellinDividedShift h f ≠ 0 := by
    simpa [burnolMellinDividedShift, unitaryPush] using
      (archimedeanMellinUnitary.symm.injective.ne hspec)
  exact hreal.elim (fun hdelta => (by linarith : rho.re - 1 / 2 ≠ 0) hdelta)
    (fun hshift => hphys hshift)

/-- A nonzero co-Poisson source vector cannot acquire a source-orthogonal divided shift. -/
theorem burnolMellinDividedShift_not_mem_source_orthogonal
    {rho : ℂ} (h : 1 / 2 < rho.re) (b : ℝ) {f : evenSubspace}
    (hfS : f ∈ burnolCoPoissonSourceSpace b) (hf : f ≠ 0) :
    burnolMellinDividedShift h f ∉ (burnolCoPoissonSourceSpace b)ᗮ := by
  intro hperp
  exact burnolMellinDividedShift_inner_ne_zero h hf
    (Submodule.inner_right_of_mem_orthogonal hfS hperp)

/-- The retained co-Poisson source projection of a nonzero source vector's divided shift is
nonzero. -/
theorem burnolCoPoissonSourceProjection_mellinDividedShift_ne_zero
    {rho : ℂ} (h : 1 / 2 < rho.re) (b : ℝ) {f : evenSubspace}
    (hfS : f ∈ burnolCoPoissonSourceSpace b) (hf : f ≠ 0) :
    burnolCoPoissonSourceProjection b (burnolMellinDividedShift h f) ≠ 0 := by
  rw [ne_eq, burnolCoPoissonSourceProjection_eq_zero_iff]
  exact burnolMellinDividedShift_not_mem_source_orthogonal h b hfS hf

/-- Quantitative fixed-aperture leakage: horizontal displacement times divided-shift energy is
bounded by the norm of the retained co-Poisson source component. -/
theorem burnolCoPoissonSourceProjection_mellinDividedShift_lower_bound
    {rho : ℂ} (h : 1 / 2 < rho.re) (b : ℝ) {f : evenSubspace}
    (hfS : f ∈ burnolCoPoissonSourceSpace b) :
    (rho.re - 1 / 2) * ‖burnolMellinDividedShift h f‖ ^ 2 ≤
      ‖f‖ * ‖burnolCoPoissonSourceProjection b (burnolMellinDividedShift h f)‖ := by
  letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
    (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
  let T := burnolMellinDividedShift h
  let p := burnolCoPoissonSourceProjection b (T f)
  have hperp : T f - p ∈ (burnolCoPoissonSourceSpace b)ᗮ := by
    change T f - (burnolCoPoissonSourceSpace b).starProjection (T f) ∈
      (burnolCoPoissonSourceSpace b)ᗮ
    exact Submodule.sub_starProjection_mem_orthogonal (T f)
  have hzero : inner ℂ f (T f - p) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hfS hperp
  have heq : inner ℂ f (T f) = inner ℂ f p := by
    rw [inner_sub_right] at hzero
    exact sub_eq_zero.mp hzero
  calc
    (rho.re - 1 / 2) * ‖T f‖ ^ 2 = (inner ℂ f (T f)).re :=
      (re_inner_burnolMellinDividedShift_eq h f).symm
    _ = (inner ℂ f p).re := congrArg Complex.re heq
    _ ≤ |(inner ℂ f p).re| := le_abs_self _
    _ ≤ ‖inner ℂ f p‖ := Complex.abs_re_le_norm _
    _ ≤ ‖f‖ * ‖p‖ := norm_inner_le_norm (𝕜 := ℂ) f p

/-- At every actual right-half Xi divisor point, one explicit sub-window co-Poisson atom has a
nonzero retained divided-shift source projection. -/
theorem xiDivisor_burnolSubWindow_mellinDividedShift_sourceProjection_ne_zero
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    burnolCoPoissonSourceProjection (subWindowAperture c d)
      (burnolMellinDividedShift (rho := (rho : ℂ)) h
        (coPoissonSubWindowEven hc hcd.le)) ≠ 0 := by
  apply burnolCoPoissonSourceProjection_mellinDividedShift_ne_zero
    (rho := (rho : ℂ)) h
  · exact (burnolCoPoissonAlgebraicSourceSpace (subWindowAperture c d)).le_topologicalClosure
      (Submodule.subset_span ⟨coPoissonSubWindowSource hc hcd.le, Or.inl rfl⟩)
  · exact coPoissonSubWindowEven_ne_zero hc hcd

/-- Quantitative source-leakage floor at an actual right-half Xi divisor point. -/
theorem xiDivisor_burnolSubWindow_mellinDividedShift_sourceProjection_lower_bound
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re)
    {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ((rho : ℂ).re - 1 / 2) *
        ‖burnolMellinDividedShift (rho := (rho : ℂ)) h
          (coPoissonSubWindowEven hc hcd.le)‖ ^ 2 ≤
      ‖coPoissonSubWindowEven hc hcd.le‖ *
        ‖burnolCoPoissonSourceProjection (subWindowAperture c d)
          (burnolMellinDividedShift (rho := (rho : ℂ)) h
            (coPoissonSubWindowEven hc hcd.le))‖ := by
  apply burnolCoPoissonSourceProjection_mellinDividedShift_lower_bound
    (rho := (rho : ℂ)) h
  exact (burnolCoPoissonAlgebraicSourceSpace (subWindowAperture c d)).le_topologicalClosure
    (Submodule.subset_span ⟨coPoissonSubWindowSource hc hcd.le, Or.inl rfl⟩)

/-- The one-coordinate pre-divisor source-flatness producer now sufficient for Route R. -/
def BurnolXiDividedShiftSourceFlatness : Prop :=
  ∀ (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re),
    burnolCoPoissonSourceProjection (subWindowAperture (1 / 2) 1)
      (burnolMellinDividedShift (rho := (rho : ℂ)) h
        (coPoissonSubWindowEven (c := (1 / 2 : ℝ)) (d := 1)
          (by norm_num) (by norm_num))) = 0

/-- A pre-divisor proof of the fixed source-flatness coordinate closes RH. -/
theorem riemannHypothesis_of_burnolXiDividedShiftSourceFlatness
    (hflat : BurnolXiDividedShiftSourceFlatness) : RiemannHypothesis := by
  unfold BurnolXiDividedShiftSourceFlatness at hflat
  rw [rh_iff_xi_ne_zero_right]
  intro z hzright hz
  let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
  have hright : 1 / 2 < (rho : ℂ).re := by
    simpa [rho] using mem_rightHalf.mp hzright
  have hne := xiDivisor_burnolSubWindow_mellinDividedShift_sourceProjection_ne_zero
    rho hright (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num)
  exact hne (hflat rho hright)

end RHTower
