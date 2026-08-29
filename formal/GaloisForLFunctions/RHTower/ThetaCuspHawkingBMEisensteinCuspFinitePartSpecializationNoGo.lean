import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinScalarLandingNoGo

/-!
# Analytic-family cusp finite part cannot descend through spectral specialization

The cusp finite part used by the actual balanced-Eisenstein chain is defined before spectral
specialization: it selects the coefficient whose affine height exponent is identically zero in
the spectral parameters.  A tempting pointwise replacement would first specialize every exponent
and then apply a reporter to the resulting height function.  This module proves that replacement
impossible, even if the reporter is allowed to be arbitrary and nonlinear.

The obstruction occurs inside the actual absolute-convergence chamber.  At Eisenstein parameters
`s = 2`, `t = 4`, hence shifted parameters `u = 3/2`, `v = 7/2`, the nonzero boundary exponent

`1/2 + 2u - v`

specializes to zero.  Therefore unit mass at the identically-zero affine exponent and unit mass at
this accidental-zero exponent give exactly the same height profile for every height.  Their
analytic-family finite parts are nevertheless `1` and `0`.

More sharply, a general quotient theorem proves that a linear functional factors through an
arbitrary linear specialization map by some set-theoretic reporter exactly when the specialization
kernel is contained in the functional kernel.  The explicit difference of the two unit families
lies in the specialization kernel but has finite part one, so even nonlinear pointwise
factorization is impossible.

This kills the pointwise finite-part representation used in the hostile C-A.9v abstraction.  The
positive survivor is family-level meromorphic regularization before specialization, exactly the
level at which a genuine pole-filled scalar Rankin--Selberg--Zagier identity must be proved.  The
remaining RH chain is

`family-level scalar RSZ -> C-A.9u balanced source -> negative BM -> left QNM -> HC94 cocycle -> RH`.

General automorphic regularization and deformation are classical; the novelty claim is restricted
to this source-normalized affine specialization-kernel obstruction and its exact descent
classification.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [ROUTE KILLED] [HB] [RSZ]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- A pointwise cusp-height profile, after all spectral parameters have been specialized. -/
abbrev D4BMCuspHeightProfile := ℝ → ℂ

/-- Linear specialization of a formal affine-exponent family to its pointwise height profile. -/
def d4BMCuspAffineHeightSpecialization (u v : ℂ) :
    (D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ) →ₗ[ℂ] D4BMCuspHeightProfile where
  toFun F := fun Y => d4BMEvaluateCuspAffineBoundaryFamily u v Y F
  map_add' F G := by
    funext Y
    simp [d4BMEvaluateCuspAffineBoundaryFamily]
  map_smul' c F := by
    funext Y
    simp [d4BMEvaluateCuspAffineBoundaryFamily]

/-- The corpus analytic-family finite part as a complex-linear functional. -/
def d4BMCuspAnalyticFamilyFinitePartLinear :
    (D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ) →ₗ[ℂ] ℂ where
  toFun := d4BMCuspAnalyticFamilyFinitePart
  map_add' F G := by simp [d4BMCuspAnalyticFamilyFinitePart]
  map_smul' c F := by simp [d4BMCuspAnalyticFamilyFinitePart]

/-- Unit mass at the exponent identically zero in the spectral parameters. -/
def d4BMCuspIdenticallyZeroUnitFamily :
    D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  Finsupp.single 0 1

/-- Unit mass at the actual boundary exponent `1/2 + 2u - v`. -/
def d4BMCuspAccidentalZeroUnitFamily :
    D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  Finsupp.single (d4BMDiagonalEisensteinCuspBoundaryExponent true true false) 1

/-- Difference between identically-zero and accidental-zero unit families. -/
def d4BMCuspSpecializationCollision :
    D4BMDiagonalEisensteinCuspAffineExponent →₀ ℂ :=
  d4BMCuspIdenticallyZeroUnitFamily - d4BMCuspAccidentalZeroUnitFamily

/-- Repeated Eisenstein parameter `s = 2`, packaged in the actual convergence chamber. -/
def d4BMCuspRepeatedResonanceParameter : D4BMEisensteinAbsoluteConvergenceParameter :=
  ⟨2, by norm_num⟩

/-- Projecting Eisenstein parameter `t = 4`, packaged in the actual convergence chamber. -/
def d4BMCuspProjectingResonanceParameter : D4BMEisensteinAbsoluteConvergenceParameter :=
  ⟨4, by norm_num⟩

/-- The nonzero affine boundary exponent `1/2 + 2u - v` collides with zero at the closed
convergence-chamber point `s = 2`, `t = 4`. -/
theorem d4BM_accidentalZeroExponent_specializes_to_zero :
    d4BMSpecializeDiagonalCuspAffineExponent
        (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
        (d4BMCuspProjectingResonanceParameter.s - 1 / 2)
        (d4BMDiagonalEisensteinCuspBoundaryExponent true true false) = 0 := by
  norm_num [d4BMCuspRepeatedResonanceParameter,
    d4BMCuspProjectingResonanceParameter,
    d4BMSpecializeDiagonalCuspAffineExponent,
    d4BMDiagonalEisensteinCuspBoundaryExponent,
    d4BMCuspSign]

/-- Identically-zero and accidental-zero affine families become the same height function after
specialization at `s = 2`, `t = 4`. -/
theorem d4BM_zero_and_accidentalZero_families_same_specialized_profile :
    d4BMCuspAffineHeightSpecialization
        (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
        (d4BMCuspProjectingResonanceParameter.s - 1 / 2)
        d4BMCuspIdenticallyZeroUnitFamily =
      d4BMCuspAffineHeightSpecialization
        (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
        (d4BMCuspProjectingResonanceParameter.s - 1 / 2)
        d4BMCuspAccidentalZeroUnitFamily := by
  funext Y
  change d4BMEvaluateCuspAffineBoundaryFamily
      (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
      (d4BMCuspProjectingResonanceParameter.s - 1 / 2) Y
      d4BMCuspIdenticallyZeroUnitFamily =
    d4BMEvaluateCuspAffineBoundaryFamily
      (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
      (d4BMCuspProjectingResonanceParameter.s - 1 / 2) Y
      d4BMCuspAccidentalZeroUnitFamily
  simp only [d4BMEvaluateCuspAffineBoundaryFamily,
    d4BMCuspIdenticallyZeroUnitFamily,
    d4BMCuspAccidentalZeroUnitFamily,
    Finsupp.linearCombination_single]
  rw [show d4BMSpecializeDiagonalCuspAffineExponent
          (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
          (d4BMCuspProjectingResonanceParameter.s - 1 / 2) 0 = 0 by
        simp [d4BMSpecializeDiagonalCuspAffineExponent],
    d4BM_accidentalZeroExponent_specializes_to_zero]

/-- The identically-zero unit family has analytic-family finite part one. -/
theorem d4BM_identicallyZeroUnitFamily_finitePart_eq_one :
    d4BMCuspAnalyticFamilyFinitePart d4BMCuspIdenticallyZeroUnitFamily = 1 := by
  simp [d4BMCuspAnalyticFamilyFinitePart, d4BMCuspIdenticallyZeroUnitFamily]

/-- The accidental-zero unit family has analytic-family finite part zero: its exponent is not
identically zero before specialization. -/
theorem d4BM_accidentalZeroUnitFamily_finitePart_eq_zero :
    d4BMCuspAnalyticFamilyFinitePart d4BMCuspAccidentalZeroUnitFamily = 0 := by
  simp [d4BMCuspAnalyticFamilyFinitePart, d4BMCuspAccidentalZeroUnitFamily,
    d4BMDiagonalEisensteinCuspBoundaryExponent_ne_zero]

/-- The explicit difference family is invisible to pointwise height specialization. -/
theorem d4BM_cuspSpecializationCollision_mem_ker :
    d4BMCuspSpecializationCollision ∈ LinearMap.ker
      (d4BMCuspAffineHeightSpecialization
        (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
        (d4BMCuspProjectingResonanceParameter.s - 1 / 2)) := by
  rw [LinearMap.mem_ker]
  simp only [d4BMCuspSpecializationCollision, map_sub]
  exact sub_eq_zero.mpr d4BM_zero_and_accidentalZero_families_same_specialized_profile

/-- The same invisible difference has analytic-family finite part exactly one. -/
theorem d4BM_cuspSpecializationCollision_finitePart_eq_one :
    d4BMCuspAnalyticFamilyFinitePartLinear d4BMCuspSpecializationCollision = 1 := by
  change d4BMCuspAnalyticFamilyFinitePart
      (d4BMCuspIdenticallyZeroUnitFamily - d4BMCuspAccidentalZeroUnitFamily) = 1
  rw [show d4BMCuspAnalyticFamilyFinitePart
        (d4BMCuspIdenticallyZeroUnitFamily - d4BMCuspAccidentalZeroUnitFamily) =
      d4BMCuspAnalyticFamilyFinitePart d4BMCuspIdenticallyZeroUnitFamily -
        d4BMCuspAnalyticFamilyFinitePart d4BMCuspAccidentalZeroUnitFamily by rfl,
    d4BM_identicallyZeroUnitFamily_finitePart_eq_one,
    d4BM_accidentalZeroUnitFamily_finitePart_eq_zero]
  norm_num

/-- Exact descent criterion.  A linear functional can be recovered after a linear observation by
an arbitrary reporter precisely when it vanishes on the observation kernel.  The reporter need
not be linear, continuous, or otherwise structured. -/
theorem d4BM_linearReporter_factorsThrough_iff_ker_le
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (f : V →ₗ[ℂ] W) (g : V →ₗ[ℂ] ℂ) :
    (∃ reporter : W → ℂ, ∀ x, reporter (f x) = g x) ↔
      LinearMap.ker f ≤ LinearMap.ker g := by
  constructor
  · rintro ⟨reporter, hreporter⟩ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    calc
      g x = reporter (f x) := (hreporter x).symm
      _ = reporter (f 0) := by rw [hx, map_zero]
      _ = g 0 := hreporter 0
      _ = 0 := map_zero g
  · intro hker
    classical
    let reporter : W → ℂ := fun w =>
      if hw : ∃ x, f x = w then g (Classical.choose hw) else 0
    refine ⟨reporter, ?_⟩
    intro x
    have hx : ∃ y : V, f y = f x := Exists.intro x rfl
    change (if hw : ∃ y : V, f y = f x then g (Classical.choose hw) else 0) = g x
    rw [dif_pos hx]
    have hdiff : Classical.choose hx - x ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, Classical.choose_spec hx, sub_self]
    have hg := hker hdiff
    rw [LinearMap.mem_ker, map_sub] at hg
    exact sub_eq_zero.mp hg

/-- For this cusp specialization, existence of any pointwise reporter is exactly the stated
kernel inclusion. -/
theorem d4BM_cuspAnalyticFamilyFinitePart_factorization_iff_kernel :
    (∃ reporter : D4BMCuspHeightProfile → ℂ,
        ∀ F, reporter
            (d4BMCuspAffineHeightSpecialization
              (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
              (d4BMCuspProjectingResonanceParameter.s - 1 / 2) F) =
          d4BMCuspAnalyticFamilyFinitePart F) ↔
      LinearMap.ker
          (d4BMCuspAffineHeightSpecialization
            (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
            (d4BMCuspProjectingResonanceParameter.s - 1 / 2)) ≤
        LinearMap.ker d4BMCuspAnalyticFamilyFinitePartLinear := by
  exact d4BM_linearReporter_factorsThrough_iff_ker_le
    (f := d4BMCuspAffineHeightSpecialization
      (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
      (d4BMCuspProjectingResonanceParameter.s - 1 / 2))
    (g := d4BMCuspAnalyticFamilyFinitePartLinear)

/-- The explicit collision disproves the kernel inclusion required for descent. -/
theorem d4BM_cuspSpecialization_ker_not_le_finitePart_ker :
    ¬ LinearMap.ker
          (d4BMCuspAffineHeightSpecialization
            (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
            (d4BMCuspProjectingResonanceParameter.s - 1 / 2)) ≤
        LinearMap.ker d4BMCuspAnalyticFamilyFinitePartLinear := by
  intro hker
  have hmem := hker d4BM_cuspSpecializationCollision_mem_ker
  rw [LinearMap.mem_ker] at hmem
  rw [d4BM_cuspSpecializationCollision_finitePart_eq_one] at hmem
  norm_num at hmem

/-- **Pointwise specialization no-go.**  No reporter on specialized height functions can recover
the corpus analytic-family finite part on all affine cusp families at the actual chamber point
`s = 2`, `t = 4`.  This is closed and does not assume reporter linearity. -/
theorem d4BM_cuspAnalyticFamilyFinitePart_not_factorThrough_specializedHeight :
    ¬ ∃ reporter : D4BMCuspHeightProfile → ℂ,
        ∀ F, reporter
            (d4BMCuspAffineHeightSpecialization
              (d4BMCuspRepeatedResonanceParameter.s - 1 / 2)
              (d4BMCuspProjectingResonanceParameter.s - 1 / 2) F) =
          d4BMCuspAnalyticFamilyFinitePart F := by
  rw [d4BM_cuspAnalyticFamilyFinitePart_factorization_iff_kernel]
  exact d4BM_cuspSpecialization_ker_not_le_finitePart_ker

end


end RHTower
