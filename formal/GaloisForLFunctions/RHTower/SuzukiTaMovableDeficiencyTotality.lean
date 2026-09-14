import GaloisForLFunctions.RHTower.SuzukiTaMovableCompletedCovarianceCCMBridge
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace
open GaloisForLFunctions.HTGeometry

def suzukiTaRawDeficiencySpan (a : SuzukiPositiveAperture) :
    Submodule ℂ (SuzukiTaHilbert a) :=
  Submodule.span ℂ (Set.range (suzukiTaRawDeficiency a))

theorem suzukiTa_eq_zero_of_inner_rawDeficiency_eq_zero
    (a : SuzukiPositiveAperture) {x : SuzukiTaHilbert a}
    (hx : ∀ c : ℝ, inner ℂ (suzukiTaRawDeficiency a c) x = 0) :
    x = 0 := by
  let F : ℂ → ℂ := suzukiTaPhysicalFourier a x
  let G : ℂ → ℂ := fun z => F (z * I)
  have hGdiff : Differentiable ℂ G := by
    intro z
    exact ((differentiable_suzukiTaPhysicalFourier a x) _).comp z
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w * I) z)
  have hGzero : ∀ z : ℂ, G z = 0 := by
    intro z
    exact GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
      hGdiff (t₀ := 0) (r := 1) (by norm_num) (fun t _ht => by
        dsimp only [G, F]
        rw [suzukiTaPhysicalFourier_mul_I_eq_moment_neg,
          ← suzukiTaRawDeficiency_inner]
        exact hx (-t)) z
  have hFzero : ∀ z : ℂ, F z = 0 := by
    intro z
    have hz := hGzero (z * (-I))
    dsimp only [G] at hz
    simpa [mul_assoc] using hz
  let g : SoninL2 := suzukiApertureZeroExtendL2 (suzukiTaPhysicalEmbedding a x)
  have hfourier : ∀ w : ℝ,
      FourierTransform.fourier (suzukiCutoff a.1 g : ℝ → ℂ) w = 0 := by
    intro w
    rw [← suzukiCompactL2Fourier_real_eq_fourier a.1 g w]
    exact hFzero _
  have hae : (suzukiCutoff a.1 g : ℝ → ℂ) =ᵐ[volume] 0 :=
    integrable_ae_eq_zero_of_fourier_eq_zero
      (integrable_suzukiCutoff a.1 g) hfourier
  have hcut : suzukiCutoff a.1 g = 0 := by
    apply Lp.ext
    exact hae.trans (Lp.coeFn_zero ℂ 2 volume).symm
  have hg : g = 0 := by
    rw [suzukiApertureZeroExtendL2_cutoff] at hcut
    exact hcut
  have hembed : suzukiTaPhysicalEmbedding a x = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_suzukiApertureZeroExtendL2]
    change ‖g‖ = 0
    rw [hg, norm_zero]
  apply suzukiTaPhysicalEmbedding_injective a
  simpa using hembed

theorem suzukiTaRawDeficiencySpan_closure_eq_top
    (a : SuzukiPositiveAperture) :
    (suzukiTaRawDeficiencySpan a).topologicalClosure = ⊤ := by
  have horth : (suzukiTaRawDeficiencySpan a)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    apply suzukiTa_eq_zero_of_inner_rawDeficiency_eq_zero a
    intro c
    exact hx (suzukiTaRawDeficiency a c)
      (Submodule.subset_span (Set.mem_range_self c))
  calc
    (suzukiTaRawDeficiencySpan a).topologicalClosure =
        (suzukiTaRawDeficiencySpan a)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℂ (SuzukiTaHilbert a))ᗮ := by rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- Exact energy-space Riesz form of every CCM pole coordinate. -/
theorem ccmPolarCoordinate_suzukiTaToFormCLM
    (a : SuzukiPositiveAperture) (s : ℝ) (x : SuzukiTaHilbert a) :
    ccmPolarCoordinate a s (suzukiTaToFormCLM a x) =
      inner ℂ (suzukiTaRawDeficiency a s) x := by
  rw [suzukiTaRawDeficiency_inner]
  change inner ℂ (ccmPolarApertureVector a s)
      (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a x)) =
    inner ℂ (suzukiTaExponentialL2 a s) (suzukiTaPhysicalEmbedding a x)
  let e := suzukiApertureL2Equiv a
  have hpolar : e (suzukiTaExponentialL2 a s) = ccmPolarApertureVector a s := by
    apply Subtype.ext
    exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a s
  rw [← hpolar]
  rw [← e.apply_symm_apply
    (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a x))]
  rw [e.inner_map_map]
  rfl

/-- Two Suzuki energy deficiencies carrying the literal CCM pole coordinates. -/
def suzukiTaPolarDeficiencySubmodule (a : SuzukiPositiveAperture) :
    Submodule ℂ (SuzukiTaHilbert a) :=
  (ℂ ∙ suzukiTaRawDeficiency a (1 / 2)) ⊔
    (ℂ ∙ suzukiTaRawDeficiency a (-1 / 2))

/-- CCM pole constraints are exactly energy orthogonality to the two Suzuki deficiencies. -/
theorem isPolarConstrained_suzukiTaToFormCLM_iff
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) :
    IsPolarConstrained a (suzukiTaToFormCLM a x) ↔
      x ∈ (suzukiTaPolarDeficiencySubmodule a)ᗮ := by
  rw [show (suzukiTaPolarDeficiencySubmodule a)ᗮ =
      (ℂ ∙ suzukiTaRawDeficiency a (1 / 2))ᗮ ⊓
        (ℂ ∙ suzukiTaRawDeficiency a (-1 / 2))ᗮ by
    exact (Submodule.inf_orthogonal _ _).symm]
  simp only [Submodule.mem_inf,
    Submodule.mem_orthogonal_singleton_iff_inner_right]
  change (ccmPolarCoordinate a (1 / 2) (suzukiTaToFormCLM a x) = 0 ∧
      ccmPolarCoordinate a (-1 / 2) (suzukiTaToFormCLM a x) = 0) ↔ _
  rw [ccmPolarCoordinate_suzukiTaToFormCLM,
    ccmPolarCoordinate_suzukiTaToFormCLM]

def suzukiTaPolarConstrainedSubmodule (a : SuzukiPositiveAperture) :
    Submodule ℂ (SuzukiTaHilbert a) :=
  (suzukiTaPolarDeficiencySubmodule a)ᗮ

theorem suzukiTaPolarConstrainedSubmodule_isClosed
    (a : SuzukiPositiveAperture) :
    IsClosed (suzukiTaPolarConstrainedSubmodule a : Set (SuzukiTaHilbert a)) :=
  (suzukiTaPolarDeficiencySubmodule a).isClosed_orthogonal

noncomputable instance suzukiTaPolarConstrainedInnerProductSpace
    (a : SuzukiPositiveAperture) :
    InnerProductSpace ℂ (suzukiTaPolarConstrainedSubmodule a) :=
  Submodule.innerProductSpace (suzukiTaPolarConstrainedSubmodule a)

instance suzukiTaPolarConstrainedCompleteSpace (a : SuzukiPositiveAperture) :
    CompleteSpace (suzukiTaPolarConstrainedSubmodule a) :=
  (suzukiTaPolarConstrainedSubmodule_isClosed a).completeSpace_coe

/-- Canonical energy-orthogonal movable deficiency after retaining both pole charges. -/
def suzukiTaPolarConstrainedMovableDeficiency
    (a : SuzukiPositiveAperture) (c : ℝ) :
      suzukiTaPolarConstrainedSubmodule a :=
  (suzukiTaPolarConstrainedSubmodule a).orthogonalProjectionOnto
    (suzukiTaRawDeficiency a c)

def suzukiTaPolarConstrainedMovableDeficiencySpan
    (a : SuzukiPositiveAperture) :
    Submodule ℂ (suzukiTaPolarConstrainedSubmodule a) :=
  Submodule.span ℂ (Set.range (suzukiTaPolarConstrainedMovableDeficiency a))

/-- Projected movable deficiencies remain complete after exact two-pole constraint. -/
theorem suzukiTaPolarConstrainedMovableDeficiencySpan_closure_eq_top
    (a : SuzukiPositiveAperture) :
    (suzukiTaPolarConstrainedMovableDeficiencySpan a).topologicalClosure = ⊤ := by
  have horth : Submodule.orthogonal
      (suzukiTaPolarConstrainedMovableDeficiencySpan a) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    apply Subtype.ext
    apply suzukiTa_eq_zero_of_inner_rawDeficiency_eq_zero a
    intro c
    have hproj := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right y
      (suzukiTaRawDeficiency a c)
    rw [← hproj]
    have h := hy (suzukiTaPolarConstrainedMovableDeficiency a c)
      (Submodule.subset_span (Set.mem_range_self c))
    exact h
  calc
    (suzukiTaPolarConstrainedMovableDeficiencySpan a).topologicalClosure =
        Submodule.orthogonal (Submodule.orthogonal
          (suzukiTaPolarConstrainedMovableDeficiencySpan a)) :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = Submodule.orthogonal
        (⊥ : Submodule ℂ (suzukiTaPolarConstrainedSubmodule a)) := by
      rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- Energy/form equivalence maps the orthogonal two-pole sector onto the literal CCM sector. -/
theorem suzukiTaPolarConstrainedSubmodule_map_eq
    (a : SuzukiPositiveAperture) :
    (suzukiTaPolarConstrainedSubmodule a).map
        (suzukiTaEquivForm a).toLinearMap =
      ccmPolarConstraintSubmodule a := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (isPolarConstrained_suzukiTaToFormCLM_iff a x).2 hx
  · intro hu
    refine ⟨suzukiTaFromFormCLM a u, ?_, ?_⟩
    · apply (isPolarConstrained_suzukiTaToFormCLM_iff a _).1
      change IsPolarConstrained a u at hu
      simpa using hu
    · change suzukiTaToFormCLM a (suzukiTaFromFormCLM a u) = u
      exact suzukiTaToFormCLM_fromForm a u

/-- Exact topological equivalence between constrained Suzuki energy and CCM form sectors. -/
def suzukiTaPolarConstrainedEquivCCM (a : SuzukiPositiveAperture) :
    suzukiTaPolarConstrainedSubmodule a ≃L[ℂ] ccmPolarConstraintSubmodule a :=
  (suzukiTaEquivForm a).ofSubmodules _ _
    (suzukiTaPolarConstrainedSubmodule_map_eq a)

/-- Actual CCM source obtained by orthogonally removing precisely the two pole charges. -/
def suzukiTaPolarOrthogonalMovableCCMResponse
    (a : SuzukiPositiveAperture) (c : ℝ) : ccmPolarConstraintSubmodule a :=
  suzukiTaPolarConstrainedEquivCCM a
    (suzukiTaPolarConstrainedMovableDeficiency a c)

def suzukiTaPolarOrthogonalMovableCCMResponseSpan
    (a : SuzukiPositiveAperture) :
    Submodule ℂ (ccmPolarConstraintSubmodule a) :=
  Submodule.span ℂ (Set.range (suzukiTaPolarOrthogonalMovableCCMResponse a))

theorem suzukiTaPolarOrthogonalMovableCCMResponseSpan_eq_map
    (a : SuzukiPositiveAperture) :
    suzukiTaPolarOrthogonalMovableCCMResponseSpan a =
      (suzukiTaPolarConstrainedMovableDeficiencySpan a).map
        (suzukiTaPolarConstrainedEquivCCM a).toLinearMap := by
  rw [suzukiTaPolarOrthogonalMovableCCMResponseSpan,
    suzukiTaPolarConstrainedMovableDeficiencySpan, Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨suzukiTaPolarConstrainedMovableDeficiency a c, ⟨c, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩

/-- Orthogonally pole-corrected movable Suzuki sources are complete in literal CCM coordinates. -/
theorem suzukiTaPolarOrthogonalMovableCCMResponseSpan_closure_eq_top
    (a : SuzukiPositiveAperture) :
    (suzukiTaPolarOrthogonalMovableCCMResponseSpan a).topologicalClosure = ⊤ := by
  rw [suzukiTaPolarOrthogonalMovableCCMResponseSpan_eq_map]
  apply top_unique
  intro y _hy
  have hmap := Submodule.topologicalClosure_map
    (suzukiTaPolarConstrainedEquivCCM a).toContinuousLinearMap
    (suzukiTaPolarConstrainedMovableDeficiencySpan a)
  have hx : (suzukiTaPolarConstrainedEquivCCM a).symm y ∈
      (suzukiTaPolarConstrainedMovableDeficiencySpan a).topologicalClosure := by
    rw [suzukiTaPolarConstrainedMovableDeficiencySpan_closure_eq_top]
    exact Submodule.mem_top
  have himage := hmap ⟨_, hx, rfl⟩
  simpa using himage

/-- Exact completed-source diagonal in Suzuki energy coordinates. This holds on the whole energy
space, before imposing pole constraints or selecting movable sources. -/
theorem ccmRestrictedWeilSourceQuadratic_suzukiTaToFormCLM
    (a : SuzukiPositiveAperture) (x : SuzukiTaHilbert a) :
    ccmRestrictedWeilSourceQuadratic a (suzukiTaToFormCLM a x) =
      ‖x‖ ^ 2 -
        boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
          ‖suzukiTaPhysicalEmbedding a x‖ ^ 2 := by
  have h := inner_suzukiTa_eq a x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have hre := congrArg Complex.re h
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hre
  rw [suzukiWeilIntervalForm_self_re_eq_source] at hre
  change ‖x‖ * ‖x‖ =
      ccmRestrictedWeilSourceQuadratic a (suzukiTaToFormCLM a x) + _ at hre
  simp only [pow_two]
  linarith

/-- RH is equivalent to nonnegativity on finite linear combinations of the literal movable
Suzuki covariance family after energy-orthogonal removal of exactly the two pole charges. -/
theorem riemannHypothesis_iff_polarOrthogonalMovableCCMResponseSpan_nonnegative :
    RiemannHypothesis ↔
      ∀ (a : SuzukiPositiveAperture) (u : ccmPolarConstraintSubmodule a),
        u ∈ suzukiTaPolarOrthogonalMovableCCMResponseSpan a →
          0 ≤ ccmRestrictedWeilSourceQuadratic a u.1 := by
  constructor
  · intro hRH a u _hu
    have hground := (riemannHypothesis_iff_polarGroundEnergy_nonneg.mp hRH) a
    exact (mul_nonneg hground (sq_nonneg _)).trans
      (ccmRestrictedWeilPolarGroundEnergy_mul_le a u.1 u.2)
  · intro hspan
    apply riemannHypothesis_iff_polarGroundEnergy_nonneg.mpr
    intro a
    apply le_ccmRestrictedWeilPolarGroundEnergy_of_floor a
    intro u hu
    simp only [zero_mul]
    let v : ccmPolarConstraintSubmodule a := ⟨u, hu⟩
    have hclosed : IsClosed {w : ccmPolarConstraintSubmodule a |
        0 ≤ ccmRestrictedWeilSourceQuadratic a w.1} :=
      isClosed_le continuous_const
        ((continuous_ccmRestrictedWeilSourceQuadratic a).comp continuous_subtype_val)
    have hsub : (suzukiTaPolarOrthogonalMovableCCMResponseSpan a :
        Set (ccmPolarConstraintSubmodule a)) ⊆
        {w | 0 ≤ ccmRestrictedWeilSourceQuadratic a w.1} := by
      intro w hw
      exact hspan a w hw
    have hclosure : closure
        (suzukiTaPolarOrthogonalMovableCCMResponseSpan a :
          Set (ccmPolarConstraintSubmodule a)) ⊆
        {w | 0 ≤ ccmRestrictedWeilSourceQuadratic a w.1} :=
      closure_minimal hsub hclosed
    have hvclosure : v ∈ closure
        (suzukiTaPolarOrthogonalMovableCCMResponseSpan a :
          Set (ccmPolarConstraintSubmodule a)) := by
      rw [← Submodule.topologicalClosure_coe,
        suzukiTaPolarOrthogonalMovableCCMResponseSpan_closure_eq_top]
      exact Set.mem_univ v
    have hvnonneg := hclosure hvclosure
    change 0 ≤ ccmRestrictedWeilSourceQuadratic a v.1 at hvnonneg
    simpa only [v] using hvnonneg

/-- Exact RH-bearing remainder after movable Suzuki totality: a joint graph-energy bound on finite
linear combinations of the orthogonally pole-corrected deficiencies. Generatorwise positivity is
not substituted for this finite-span condition, so all signed cross-cancellation is retained. -/
theorem riemannHypothesis_iff_projectedMovableSuzukiEnergy_bound :
    RiemannHypothesis ↔
      ∀ (a : SuzukiPositiveAperture) (x : suzukiTaPolarConstrainedSubmodule a),
        x ∈ suzukiTaPolarConstrainedMovableDeficiencySpan a →
          boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
              ‖suzukiTaPhysicalEmbedding a x.1‖ ^ 2 ≤
            ‖x‖ ^ 2 := by
  constructor
  · intro hRH a x hx
    have hmem : suzukiTaPolarConstrainedEquivCCM a x ∈
        suzukiTaPolarOrthogonalMovableCCMResponseSpan a := by
      rw [suzukiTaPolarOrthogonalMovableCCMResponseSpan_eq_map]
      exact ⟨x, hx, rfl⟩
    have hq :=
      (riemannHypothesis_iff_polarOrthogonalMovableCCMResponseSpan_nonnegative.mp hRH)
        a (suzukiTaPolarConstrainedEquivCCM a x) hmem
    change 0 ≤ ccmRestrictedWeilSourceQuadratic a (suzukiTaToFormCLM a x.1) at hq
    rw [ccmRestrictedWeilSourceQuadratic_suzukiTaToFormCLM] at hq
    exact sub_nonneg.mp hq
  · intro henergy
    apply riemannHypothesis_iff_polarOrthogonalMovableCCMResponseSpan_nonnegative.mpr
    intro a u hu
    rw [suzukiTaPolarOrthogonalMovableCCMResponseSpan_eq_map] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    change 0 ≤ ccmRestrictedWeilSourceQuadratic a (suzukiTaToFormCLM a x.1)
    rw [ccmRestrictedWeilSourceQuadratic_suzukiTaToFormCLM]
    exact sub_nonneg.mpr (henergy a x hx)

end RHTower
