import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilSourceAlignedArbitraryAccuracy

/-!
# Canonical-ground convergence on literal Gamma--Slepian heads

The exact restricted-Weil ground is not an arbitrary vector of the complete Gamma form domain:
its weak eigen-equation writes it as the adjoint form embedding applied to the literal
scalar--polar--prime forcing.  Orthogonal projection onto a low-Gamma exterior therefore gains
one full factor of the Gamma--Slepian cutoff in form norm and two factors in physical mass.

Choosing the existing accuracy heads at the closed schedule `(n + 1)⁻¹` gives an unconditional
sequence of finite-dimensional, literal Gamma--Slepian peripheral heads converging to the exact
CCM ground.  No ground simplicity, parity, RH assumption, or replacement prolate operator enters.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProduct InnerProductSpace
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Literal bounded forcing in the exact complete-form ground equation. -/
def ccmRestrictedWeilCanonicalGroundForcing
    (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  (((ccmRestrictedWeilGroundEnergy a : ℂ) -
      ccmArchimedeanRemainderScalar) •
    (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a) -
    ccmPolarOperator a
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a) +
    ccmFinitePrimeOperator a
      (ccmRestrictedWeilCanonicalGroundEigenstate a : suzukiApertureHilbert a))

theorem ccmRestrictedWeilCanonicalGroundFormLift_eq_adjoint_forcing
    (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilCanonicalGroundFormLift a =
      (ccmArchimedeanFormToAperture a).adjoint
        (ccmRestrictedWeilCanonicalGroundForcing a) := by
  exact ccmRestrictedWeilCanonicalGroundFormLift_eq_adjoint_primePolarForcing a

private theorem canonicalGround_exteriorTail_sq_le
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta)
    (hdelta : 0 < delta) :
    let u := ccmRestrictedWeilCanonicalGroundFormLift a
    let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection u
    ‖u - h‖ ^ 2 ≤
      ccmRestrictedWeilSourceAccuracyThreshold a delta *
        ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 := by
  dsimp only
  let H := CCMArchimedeanFormDomain a
  let A := ccmArchimedeanFormToAperture a
  let M := C.exterior
  let eps := ccmRestrictedWeilSourceAccuracyThreshold a delta
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let F := ccmRestrictedWeilCanonicalGroundForcing a
  letI : CompleteSpace M := C.exterior_isClosed.completeSpace_coe
  letI : M.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M
  letI : FiniteDimensional ℂ M.orthogonal := C.sourceHead_finiteDimensional
  letI : CompleteSpace M.orthogonal := inferInstance
  letI : M.orthogonal.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
  let m : M := M.orthogonalProjectionOnto u
  let h : M.orthogonal := M.orthogonal.orthogonalProjectionOnto u
  have hhead : C.sourceHeadProjection u = h := rfl
  have hdecomp : (m : H) + (h : H) = u := by
    change M.starProjection u + M.orthogonal.starProjection u = u
    exact M.starProjection_add_starProjection_orthogonal u
  have htail : u - (C.sourceHeadProjection u : H) = (m : H) := by
    rw [hhead, ← hdecomp]
    abel
  rw [htail]
  by_cases hm : m = 0
  · simp [hm]
    exact mul_nonneg
      (ccmRestrictedWeilSourceAccuracyThreshold_pos a hdelta).le
      (sq_nonneg _)
  have hmass : ‖A (m : H)‖ ^ 2 < eps * ‖m‖ ^ 2 :=
    C.exterior_physicalMass_lt (m : H) m.property
      (fun hz => hm (Subtype.ext hz))
  have huF : u = A.adjoint F := by
    dsimp only [u, A, F]
    exact ccmRestrictedWeilCanonicalGroundFormLift_eq_adjoint_forcing a
  have horth : inner ℂ (h : H) (m : H) = 0 := by
    exact inner_eq_zero_symm.mp
      (Submodule.inner_right_of_mem_orthogonal m.property h.property)
  have hinner : (inner ℂ u (m : H)).re = ‖m‖ ^ 2 := by
    rw [← hdecomp, inner_add_left, horth, add_zero,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  have hadj : inner ℂ u (m : H) = inner ℂ F (A (m : H)) := by
    rw [huF, ContinuousLinearMap.adjoint_inner_left]
  have hpair : ‖m‖ ^ 2 ≤ ‖F‖ * ‖A (m : H)‖ := by
    rw [← hinner, hadj]
    exact le_trans (Complex.re_le_norm _)
      (norm_inner_le_norm (𝕜 := ℂ) F (A (m : H)))
  have hmpos : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hFpos : 0 < ‖F‖ := by
    by_contra hnot
    have hFzero : ‖F‖ = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg F)
    rw [hFzero, zero_mul] at hpair
    nlinarith [sq_pos_of_pos hmpos]
  have hsquared : ‖m‖ ^ 4 ≤ ‖F‖ ^ 2 * ‖A (m : H)‖ ^ 2 := by
    nlinarith [norm_nonneg F, norm_nonneg (A (m : H))]
  have hstrict : ‖m‖ ^ 4 < ‖F‖ ^ 2 * (eps * ‖m‖ ^ 2) :=
    lt_of_le_of_lt hsquared
      (mul_lt_mul_of_pos_left hmass (sq_pos_of_pos hFpos))
  change ‖m‖ ^ 2 ≤ eps * ‖F‖ ^ 2
  nlinarith [sq_pos_of_pos hmpos]

private theorem canonicalGround_exteriorPhysicalTail_sq_le
    {a : SuzukiPositiveAperture} {delta : ℝ}
    (C : CCMRestrictedWeilSourceApproximationCertificate a delta)
    (hdelta : 0 < delta) :
    let u := ccmRestrictedWeilCanonicalGroundFormLift a
    let h : CCMArchimedeanFormDomain a := C.sourceHeadProjection u
    ‖ccmArchimedeanFormToAperture a (u - h)‖ ^ 2 ≤
      (ccmRestrictedWeilSourceAccuracyThreshold a delta) ^ 2 *
        ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 := by
  dsimp only
  let H := CCMArchimedeanFormDomain a
  let A := ccmArchimedeanFormToAperture a
  let M := C.exterior
  let eps := ccmRestrictedWeilSourceAccuracyThreshold a delta
  let u := ccmRestrictedWeilCanonicalGroundFormLift a
  let F := ccmRestrictedWeilCanonicalGroundForcing a
  letI : CompleteSpace M := C.exterior_isClosed.completeSpace_coe
  letI : M.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M
  letI : FiniteDimensional ℂ M.orthogonal := C.sourceHead_finiteDimensional
  letI : CompleteSpace M.orthogonal := inferInstance
  letI : M.orthogonal.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M.orthogonal
  let m : M := M.orthogonalProjectionOnto u
  let h : M.orthogonal := M.orthogonal.orthogonalProjectionOnto u
  have hhead : C.sourceHeadProjection u = h := rfl
  have hdecomp : (m : H) + (h : H) = u := by
    change M.starProjection u + M.orthogonal.starProjection u = u
    exact M.starProjection_add_starProjection_orthogonal u
  have htail : u - (C.sourceHeadProjection u : H) = (m : H) := by
    rw [hhead, ← hdecomp]
    abel
  rw [htail]
  have heps0 : 0 ≤ eps :=
    (ccmRestrictedWeilSourceAccuracyThreshold_pos a hdelta).le
  by_cases hm : m = 0
  · simp [hm]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmass : ‖A (m : H)‖ ^ 2 ≤ eps * ‖m‖ ^ 2 :=
    le_of_lt (C.exterior_physicalMass_lt (m : H) m.property
      (fun hz => hm (Subtype.ext hz)))
  have hform := canonicalGround_exteriorTail_sq_le C hdelta
  dsimp only at hform
  change ‖u - (C.sourceHeadProjection u : H)‖ ^ 2 ≤
    eps * ‖F‖ ^ 2 at hform
  rw [htail] at hform
  change ‖A (m : H)‖ ^ 2 ≤ eps ^ 2 * ‖F‖ ^ 2
  calc
    ‖A (m : H)‖ ^ 2 ≤ eps * ‖m‖ ^ 2 := hmass
    _ ≤ eps * (eps * ‖F‖ ^ 2) := mul_le_mul_of_nonneg_left hform heps0
    _ = eps ^ 2 * ‖F‖ ^ 2 := by ring

/-- Closed positive accuracy schedule for the canonical actual-head sequence. -/
def ccmRestrictedWeilCanonicalHeadAccuracy (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹

theorem ccmRestrictedWeilCanonicalHeadAccuracy_pos (n : ℕ) :
    0 < ccmRestrictedWeilCanonicalHeadAccuracy n := by
  unfold ccmRestrictedWeilCanonicalHeadAccuracy
  positivity

/-- Canonically chosen finite peripheral Gamma--Slepian certificate at depth `n`. -/
noncomputable def ccmRestrictedWeilCanonicalGroundHeadCertificate
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilSourceApproximationCertificate a
      (ccmRestrictedWeilCanonicalHeadAccuracy n) :=
  Classical.choice (exists_ccmRestrictedWeil_sourceApproximationCertificate a
    (ccmRestrictedWeilCanonicalHeadAccuracy_pos n))

/-- Projection of the exact CCM ground onto its literal finite Gamma--Slepian head. -/
noncomputable def ccmRestrictedWeilCanonicalGroundHead
    (a : SuzukiPositiveAperture) (n : ℕ) : CCMArchimedeanFormDomain a :=
  (ccmRestrictedWeilCanonicalGroundHeadCertificate a n).sourceHeadProjection
    (ccmRestrictedWeilCanonicalGroundFormLift a)

/-- Every canonical head belongs to the exact peripheral Gamma--Slepian spectral subspace. -/
theorem ccmRestrictedWeilCanonicalGroundHead_mem_gammaSlepianPeripheral
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilCanonicalGroundHead a n ∈
      compactPeripheralSpectralSubspace (ccmArchimedeanGammaSlepianGram a)
        (ccmRestrictedWeilSourceAccuracyThreshold a
          (ccmRestrictedWeilCanonicalHeadAccuracy n)) := by
  let C := ccmRestrictedWeilCanonicalGroundHeadCertificate a n
  change (C.sourceHeadProjection
    (ccmRestrictedWeilCanonicalGroundFormLift a) : CCMArchimedeanFormDomain a) ∈ _
  rw [← C.sourceHead_eq_gammaSlepianPeripheral]
  exact (C.sourceHeadProjection
    (ccmRestrictedWeilCanonicalGroundFormLift a)).property

/-- Explicit form-norm convergence rate for the literal finite Gamma--Slepian ground heads. -/
theorem ccmRestrictedWeilCanonicalGroundHead_rate
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ‖ccmRestrictedWeilCanonicalGroundFormLift a -
        ccmRestrictedWeilCanonicalGroundHead a n‖ ^ 2 ≤
      ccmRestrictedWeilSourceAccuracyThreshold a
          (ccmRestrictedWeilCanonicalHeadAccuracy n) *
        ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 := by
  exact canonicalGround_exteriorTail_sq_le
    (ccmRestrictedWeilCanonicalGroundHeadCertificate a n)
    (ccmRestrictedWeilCanonicalHeadAccuracy_pos n)

/-- Physical-mass convergence gains the square of the Gamma--Slepian cutoff. -/
theorem ccmRestrictedWeilCanonicalGroundHead_physical_rate
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ‖ccmArchimedeanFormToAperture a
        (ccmRestrictedWeilCanonicalGroundFormLift a -
          ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 ≤
      (ccmRestrictedWeilSourceAccuracyThreshold a
          (ccmRestrictedWeilCanonicalHeadAccuracy n)) ^ 2 *
        ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 := by
  exact canonicalGround_exteriorPhysicalTail_sq_le
    (ccmRestrictedWeilCanonicalGroundHeadCertificate a n)
    (ccmRestrictedWeilCanonicalHeadAccuracy_pos n)

theorem tendsto_ccmRestrictedWeilCanonicalHeadAccuracy :
    Tendsto ccmRestrictedWeilCanonicalHeadAccuracy atTop (nhds 0) := by
  unfold ccmRestrictedWeilCanonicalHeadAccuracy
  have htop : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  exact htop.inv_tendsto_atTop

theorem tendsto_ccmRestrictedWeilCanonicalHeadThreshold
    (a : SuzukiPositiveAperture) :
    Tendsto (fun n => ccmRestrictedWeilSourceAccuracyThreshold a
      (ccmRestrictedWeilCanonicalHeadAccuracy n)) atTop (nhds 0) := by
  let D : ℝ := 8 * (ccmRestrictedWeilRemainderEnvelope a + 1) ^ 2
  have hD : D ≠ 0 := by
    dsimp [D]
    have hE := ccmRestrictedWeilRemainderEnvelope_nonneg a
    positivity
  have hdelta := tendsto_ccmRestrictedWeilCanonicalHeadAccuracy
  have hden : Tendsto
      (fun n => D * (ccmRestrictedWeilCanonicalHeadAccuracy n + 1))
      atTop (nhds (D * (0 + 1))) :=
    tendsto_const_nhds.mul (hdelta.add tendsto_const_nhds)
  have hdiv := hdelta.div hden (by simpa using hD)
  convert hdiv using 1
  · ext n
    simp only [ccmRestrictedWeilSourceAccuracyThreshold, D, div_eq_mul_inv,
      Pi.mul_apply, Pi.inv_apply]
  · simp

/-- Unconditional convergence of literal finite Gamma--Slepian heads to the exact CCM ground. -/
theorem tendsto_ccmRestrictedWeilCanonicalGroundHead
    (a : SuzukiPositiveAperture) :
    Tendsto (fun n => ccmRestrictedWeilCanonicalGroundHead a n) atTop
      (nhds (ccmRestrictedWeilCanonicalGroundFormLift a)) := by
  have hthreshold := tendsto_ccmRestrictedWeilCanonicalHeadThreshold a
  have hbound : Tendsto
      (fun n => ccmRestrictedWeilSourceAccuracyThreshold a
          (ccmRestrictedWeilCanonicalHeadAccuracy n) *
        ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2)
      atTop (nhds 0) := by
    simpa using hthreshold.mul_const
      (‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto
      (fun n => ‖ccmRestrictedWeilCanonicalGroundHead a n -
        ccmRestrictedWeilCanonicalGroundFormLift a‖ ^ 2) atTop (nhds 0) := by
    exact squeeze_zero (fun _ => sq_nonneg _)
      (fun n => by
        rw [norm_sub_rev]
        exact ccmRestrictedWeilCanonicalGroundHead_rate a n)
      hbound
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  convert hsqrt using 1
  · ext n
    simp only [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  · simp

end RHTower
