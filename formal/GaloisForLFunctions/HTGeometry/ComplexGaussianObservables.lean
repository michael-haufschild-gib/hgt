/-
# Standard complex Gaussian observables

The standard complex Gaussian measure on `κ → ℂ` is the Lebesgue measure weighted by
`∏ⱼ e^{-‖gⱼ‖²}/π`.  It is nonzero and absolutely continuous with respect to Lebesgue measure, so
it gives no mass to a proper complex subspace.

Consequently a finite complex combination of the linear observables `g ↦ ∑ⱼ wᵢⱼ gⱼ` vanishes almost
surely exactly when the same combination of the coefficient vectors `wᵢ` vanishes: Gaussian linear
observables carry exactly the linear matroid of their coefficient rows.
-/
import Mathlib

open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The density of the standard complex Gaussian vector. -/
noncomputable def complexGaussianDensity (κ : Type*) [Fintype κ] (g : κ → ℂ) : ℝ :=
  ∏ j : κ, Real.exp (-(‖g j‖ ^ 2)) / Real.pi

omit [DecidableEq κ] in
theorem complexGaussianDensity_pos (g : κ → ℂ) : 0 < complexGaussianDensity κ g := by
  rw [complexGaussianDensity]
  refine Finset.prod_pos ?_
  intro j _
  positivity

omit [DecidableEq κ] in
theorem continuous_complexGaussianDensity :
    Continuous (complexGaussianDensity κ) := by
  unfold complexGaussianDensity
  fun_prop

/-- The standard complex Gaussian measure on `κ → ℂ`. -/
noncomputable def complexGaussian (κ : Type*) [Fintype κ] : Measure (κ → ℂ) :=
  volume.withDensity (fun g => ENNReal.ofReal (complexGaussianDensity κ g))

omit [DecidableEq κ] in
theorem complexGaussian_absolutelyContinuous :
    complexGaussian κ ≪ (volume : Measure (κ → ℂ)) :=
  withDensity_absolutelyContinuous _ _

omit [DecidableEq κ] in
theorem complexGaussian_ne_zero : complexGaussian κ ≠ 0 := by
  intro h
  have huniv : complexGaussian κ Set.univ = 0 := by rw [h]; simp
  rw [complexGaussian, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_eq_zero_iff] at huniv
  · have hzero : ∀ᵐ g : κ → ℂ, ENNReal.ofReal (complexGaussianDensity κ g) = 0 := by
      filter_upwards [huniv] with g hg using hg
    have hpos : ∀ g : κ → ℂ, ENNReal.ofReal (complexGaussianDensity κ g) ≠ 0 := by
      intro g
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact complexGaussianDensity_pos g
    have hae := (ae_iff.mp hzero)
    simp only [hpos, not_false_iff, Set.setOf_true] at hae
    have hvol : (0 : ENNReal) < volume (Set.univ : Set (κ → ℂ)) :=
      isOpen_univ.measure_pos volume Set.univ_nonempty
    exact absurd hae hvol.ne'
  · exact continuous_complexGaussianDensity.measurable.ennreal_ofReal

omit [DecidableEq κ] in
/-- Nondegeneracy: the Gaussian gives no mass to a proper complex subspace. -/
theorem complexGaussian_submodule_eq_zero (S : Submodule ℂ (κ → ℂ)) (hS : S ≠ ⊤) :
    complexGaussian κ (S : Set (κ → ℂ)) = 0 := by
  refine complexGaussian_absolutelyContinuous ?_
  have hR : (Submodule.restrictScalars ℝ S) ≠ ⊤ := by
    intro h
    refine hS (SetLike.ext' ?_)
    have hcoe : (Submodule.restrictScalars ℝ S : Set (κ → ℂ))
        = ((⊤ : Submodule ℝ (κ → ℂ)) : Set (κ → ℂ)) := by rw [h]
    simpa using hcoe
  exact Measure.addHaar_submodule _ _ hR

/-- **Gaussian linear observables have exactly the linear relations of their coefficient
vectors.**  A finite complex combination of the observables vanishes almost surely exactly when
the same combination of the coefficient vectors vanishes. -/
theorem ae_gaussian_linearCombination_eq_zero_iff
    {ι : Type*} [DecidableEq ι] (w : ι → κ → ℂ) (a : ι → ℂ) (J : Finset ι) :
    (∀ᵐ g : κ → ℂ ∂(complexGaussian κ), ∑ i ∈ J, a i * (∑ j : κ, w i j * g j) = 0) ↔
      ∑ i ∈ J, a i • w i = 0 := by
  set c : κ → ℂ := ∑ i ∈ J, a i • w i with hc
  have hexp : ∀ g : κ → ℂ, ∑ i ∈ J, a i * (∑ j : κ, w i j * g j) = ∑ j : κ, c j * g j := by
    intro g
    have h1 : ∀ i : ι, a i * (∑ j : κ, w i j * g j) = ∑ j : κ, a i * (w i j * g j) := by
      intro i
      rw [Finset.mul_sum]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    have hcj : c j = ∑ i ∈ J, a i * w i j := by
      rw [hc]
      simp [Finset.sum_apply]
    rw [hcj, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  constructor
  · intro h
    by_contra hne
    obtain ⟨j0, hj0⟩ : ∃ j0, c j0 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    set φ : (κ → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun g => ∑ j : κ, c j * g j
        map_add' := by
          intro g₁ g₂
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro r g
          simp [Finset.mul_sum, mul_comm, mul_assoc] } with hφ
    have hφne : LinearMap.ker φ ≠ ⊤ := by
      intro htop
      have : φ (Pi.single j0 1) = 0 := by
        have hmem : (Pi.single j0 (1 : ℂ)) ∈ LinearMap.ker φ := by rw [htop]; trivial
        simpa using hmem
      rw [hφ] at this
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [Finset.sum_eq_single j0] at this
      · simp at this
        exact hj0 this
      · intro b _ hb
        simp [hb]
      · intro hcon
        exact absurd (Finset.mem_univ j0) hcon
    have hker := complexGaussian_submodule_eq_zero (LinearMap.ker φ) hφne
    have hcomp : complexGaussian κ {g : κ → ℂ | ¬ (∑ j : κ, c j * g j = 0)} = 0 := by
      have := h
      simp only [hexp] at this
      exact ae_iff.mp this
    have huniv : complexGaussian κ Set.univ = 0 := by
      have hsub : (Set.univ : Set (κ → ℂ)) ⊆
          (LinearMap.ker φ : Set (κ → ℂ)) ∪ {g : κ → ℂ | ¬ (∑ j : κ, c j * g j = 0)} := by
        intro g _
        by_cases hg : ∑ j : κ, c j * g j = 0
        · exact Or.inl (by simpa [hφ] using hg)
        · exact Or.inr hg
      refine le_antisymm ?_ (zero_le)
      calc complexGaussian κ Set.univ
          ≤ complexGaussian κ ((LinearMap.ker φ : Set (κ → ℂ)) ∪
              {g : κ → ℂ | ¬ (∑ j : κ, c j * g j = 0)}) := measure_mono hsub
        _ ≤ complexGaussian κ (LinearMap.ker φ : Set (κ → ℂ)) +
              complexGaussian κ {g : κ → ℂ | ¬ (∑ j : κ, c j * g j = 0)} := measure_union_le _ _
        _ = 0 := by rw [hker, hcomp]; simp
    exact complexGaussian_ne_zero (by
      ext s hs
      simp only [Measure.coe_zero, Pi.zero_apply]
      exact le_antisymm (le_trans (measure_mono (Set.subset_univ s)) (le_of_eq huniv)) (zero_le))
  · intro h
    refine Filter.Eventually.of_forall ?_
    intro g
    have hc0 : c = 0 := h
    rw [hexp g, hc0]
    simp

end GaloisForLFunctions.HTGeometry
