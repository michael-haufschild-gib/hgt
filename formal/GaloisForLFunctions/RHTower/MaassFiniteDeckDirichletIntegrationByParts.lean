import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
import GaloisForLFunctions.HTGeometry.ModularDirichletFormClosable

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace MaassCongruenceL2
noncomputable section

def component {N : ℕ} (F : ℍ → DeckSpace N) (q : Deck N) : ℍ → ℂ := fun z => F z q

theorem component_c1 {N : ℕ} (F : formPreDomain N) (q : Deck N) :
    GaloisForLFunctions.HTGeometry.IsChartC1 (component (F : ℍ → DeckSpace N) q) := by
  have h := ((EuclideanSpace.proj q).restrictScalars ℝ).contDiff.comp_contDiffOn
    (formPreDomain.c1 F)
  change ContDiffOn ℝ 1 (((EuclideanSpace.proj q).restrictScalars ℝ) ∘
    chartFun (F : ℍ → DeckSpace N)) GaloisForLFunctions.HTGeometry.upperSet
  exact h

theorem component_hypGradX {N : ℕ} (F : formPreDomain N) (q : Deck N) (z : ℍ) :
    GaloisForLFunctions.HTGeometry.hypGradX (component (F : ℍ → DeckSpace N) q) z =
      hypGradX (F : ℍ → DeckSpace N) z q := by
  have hc := component_c1 F q
  have hf := (formPreDomain.c1 F).differentiableOn one_ne_zero |>.differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hp := ((EuclideanSpace.proj q).restrictScalars ℝ).hasFDerivAt.comp (z : ℂ) hf.hasFDerivAt
  have h := congrArg (fun L => L (1 : ℂ)) hp.fderiv
  change (z.im : ℂ) * (fderiv ℝ (((EuclideanSpace.proj q).restrictScalars ℝ) ∘
    chartFun (F : ℍ → DeckSpace N)) (z : ℂ) 1) =
      ((z.im : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (z : ℂ) 1) q
  rw [h]
  rfl
end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace MaassCongruenceL2
noncomputable section

theorem component_hypGradY {N : ℕ} (F : formPreDomain N) (q : Deck N) (z : ℍ) :
    GaloisForLFunctions.HTGeometry.hypGradY (component (F : ℍ → DeckSpace N) q) z =
      hypGradY (F : ℍ → DeckSpace N) z q := by
  have hf := (formPreDomain.c1 F).differentiableOn one_ne_zero |>.differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have hp := ((EuclideanSpace.proj q).restrictScalars ℝ).hasFDerivAt.comp (z : ℂ) hf.hasFDerivAt
  have h := congrArg (fun L => L Complex.I) hp.fderiv
  change (z.im : ℂ) * (fderiv ℝ (((EuclideanSpace.proj q).restrictScalars ℝ) ∘
    chartFun (F : ℍ → DeckSpace N)) (z : ℂ) Complex.I) =
      ((z.im : ℂ) • fderiv ℝ (chartFun (F : ℍ → DeckSpace N)) (z : ℂ) Complex.I) q
  rw [h]
  rfl

/-- Scalar L² carrier for one finite-deck coordinate.  Keeping the named modular
carrier, rather than its reducible `Lp` presentation, lets scalar test functionals
compose without a change of carrier. -/
abbrev ComponentL2 := GaloisForLFunctions.HTGeometry.ModularL2

/-- Continuous L² projection to a single finite-deck coordinate. -/
def componentL2 (N : ℕ) (q : Deck N) : DeckL2 N →L[ℂ] ComponentL2 :=
  (EuclideanSpace.proj q).compLpL 2 cellMeasure

theorem component_memLp_of_memLp {N : ℕ} (F : ℍ → DeckSpace N)
    (hF : MemLp F 2 cellMeasure) (q : Deck N) :
    MemLp (component F q) 2 cellMeasure := by
  let V : DeckL2 N := toDeckL2 F hF
  let H : ComponentL2 := componentL2 N q V
  apply (memLp_congr_ae ?_).mp (Lp.memLp H)
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) q).coeFn_compLpL V,
    MemLp.coeFn_toLp hF] with z hH hV
  change (GaloisForLFunctions.HTGeometry.modularToLp H) z = _
  change ((componentL2 N q V : ComponentL2) : ℍ → ℂ) z = _
  rw [show ((componentL2 N q V : ComponentL2) : ℍ → ℂ) z =
    (EuclideanSpace.proj (𝕜 := ℂ) q) (V z) from hH]
  change (EuclideanSpace.proj (𝕜 := ℂ) q)
    ((toDeckL2 F hF) z) = _
  change (EuclideanSpace.proj (𝕜 := ℂ) q)
    ((MemLp.toLp F hF) z) = _
  rw [hV]
  rfl

theorem component_memLp {N : ℕ} (F : formPreDomain N) (q : Deck N) :
    MemLp (component (F : ℍ → DeckSpace N) q) 2 cellMeasure :=
  component_memLp_of_memLp (F : ℍ → DeckSpace N) (formPreDomain.memLp F) q

theorem componentL2_toModularL2 {N : ℕ} (F : ℍ → DeckSpace N)
    (hF : MemLp F 2 cellMeasure) (q : Deck N) :
    componentL2 N q (toDeckL2 F hF) =
      GaloisForLFunctions.HTGeometry.toModularL2 (component F q)
        (component_memLp_of_memLp F hF q) := by
  apply Lp.ext
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) q).coeFn_compLpL
      (toDeckL2 F hF), MemLp.coeFn_toLp hF,
    MemLp.coeFn_toLp (component_memLp_of_memLp F hF q)] with z hleft hsource hright
  change _ = (MemLp.toLp (component F q) (component_memLp_of_memLp F hF q)) z
  rw [hright]
  change ((EuclideanSpace.proj (𝕜 := ℂ) q).compLpL 2 cellMeasure)
    (toDeckL2 F hF) z = _
  rw [show _ = (EuclideanSpace.proj (𝕜 := ℂ) q)
    ((toDeckL2 F hF) z) from hleft]
  change (EuclideanSpace.proj (𝕜 := ℂ) q)
    ((MemLp.toLp F hF) z) = _
  rw [hsource]
  rfl

theorem component_testWeight_hypGradX {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hU : tsupport φ ⊆ GaloisForLFunctions.HTGeometry.fdoImage) :
    ∫ z in fd, (z.im : ℂ) * φ z * (hypGradX (F : ℍ → DeckSpace N) z q) ∂volume =
      - ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z 1) *
        (F : ℍ → DeckSpace N) z q ∂volume := by
  have h := GaloisForLFunctions.HTGeometry.setIntegral_fd_testWeight_hypGradX
    (component_c1 F q) hφ hs hU
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with z
    rw [component_hypGradX F q]
  · congr 1

theorem component_testWeight_hypGradY {N : ℕ} (F : formPreDomain N) (q : Deck N)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hU : tsupport φ ⊆ GaloisForLFunctions.HTGeometry.fdoImage) :
    ∫ z in fd, (z.im : ℂ) * φ z * (hypGradY (F : ℍ → DeckSpace N) z q) ∂volume =
      - ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ φ z Complex.I) *
        (F : ℍ → DeckSpace N) z q ∂volume := by
  have h := GaloisForLFunctions.HTGeometry.setIntegral_fd_testWeight_hypGradY
    (component_c1 F q) hφ hs hU
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with z
    rw [component_hypGradY F q]
  · congr 1

/-- The scalar interior test functional acting on one finite-deck coordinate
of a vector form triple. -/
def componentTestFunctional (N : ℕ) (q : Deck N)
    (T : GaloisForLFunctions.HTGeometry.InteriorTest) (i : Fin 3) (v : ℂ) :
    FormTriple N →L[ℂ] ℂ :=
  (GaloisForLFunctions.HTGeometry.pairing T.conjWeight T.memLp_conjWeight).comp
      ((componentL2 N q).comp (PiLp.proj 2 (fun _ : Fin 3 => DeckL2 N) i)) +
    (GaloisForLFunctions.HTGeometry.pairing (T.conjWeightD v) (T.memLp_conjWeightD v)).comp
      ((componentL2 N q).comp (PiLp.proj 2 (fun _ : Fin 3 => DeckL2 N) 0))

theorem componentTestFunctional_apply (N : ℕ) (q : Deck N)
    (T : GaloisForLFunctions.HTGeometry.InteriorTest) (i : Fin 3) (v : ℂ)
    (x : FormTriple N) :
    componentTestFunctional N q T i v x =
      GaloisForLFunctions.HTGeometry.pairing T.conjWeight T.memLp_conjWeight
        (componentL2 N q (x.ofLp i)) +
      GaloisForLFunctions.HTGeometry.pairing (T.conjWeightD v) (T.memLp_conjWeightD v)
        (componentL2 N q (x.ofLp 0)) := rfl

/-- The horizontal coordinate test functional vanishes on every embedded
finite-deck form. -/
theorem componentTestFunctional_formEmbeddingMap_X {N : ℕ} (F : formPreDomain N)
    (q : Deck N) (T : GaloisForLFunctions.HTGeometry.InteriorTest) :
    componentTestFunctional N q T 1 1 (formEmbeddingMap N F) = 0 := by
  rw [componentTestFunctional_apply, formEmbeddingMap_apply, formEmbeddingMap_apply,
    show formCoordinate N 1 F = toDeckL2 (hypGradX (F : ℍ → DeckSpace N))
      (formPreDomain.memLp_gradX F) from rfl,
    show formCoordinate N 0 F = toDeckL2 (F : ℍ → DeckSpace N)
      (formPreDomain.memLp F) from rfl,
    componentL2_toModularL2 (hypGradX (F : ℍ → DeckSpace N))
      (formPreDomain.memLp_gradX F) q,
    componentL2_toModularL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F) q]
  rw [GaloisForLFunctions.HTGeometry.pairing_toModularL2,
    GaloisForLFunctions.HTGeometry.pairing_toModularL2]
  have h := component_testWeight_hypGradX F q T.contDiff T.compact T.support_subset
  simp only [GaloisForLFunctions.HTGeometry.InteriorTest.conjWeight,
    GaloisForLFunctions.HTGeometry.InteriorTest.conjWeightD, Complex.conj_conj,
    GaloisForLFunctions.HTGeometry.InteriorTest.weight,
    GaloisForLFunctions.HTGeometry.InteriorTest.weightD]
  change (∫ z in fd, (z.im : ℂ) * T.φ z *
      (hypGradX (F : ℍ → DeckSpace N) z) q ∂volume) +
      ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ T.φ z 1) *
        (F : ℍ → DeckSpace N) z q ∂volume = 0
  rw [h, neg_add_cancel]

/-- The vertical coordinate test functional vanishes on every embedded
finite-deck form. -/
theorem componentTestFunctional_formEmbeddingMap_Y {N : ℕ} (F : formPreDomain N)
    (q : Deck N) (T : GaloisForLFunctions.HTGeometry.InteriorTest) :
    componentTestFunctional N q T 2 Complex.I (formEmbeddingMap N F) = 0 := by
  rw [componentTestFunctional_apply, formEmbeddingMap_apply, formEmbeddingMap_apply,
    show formCoordinate N 2 F = toDeckL2 (hypGradY (F : ℍ → DeckSpace N))
      (formPreDomain.memLp_gradY F) from rfl,
    show formCoordinate N 0 F = toDeckL2 (F : ℍ → DeckSpace N)
      (formPreDomain.memLp F) from rfl,
    componentL2_toModularL2 (hypGradY (F : ℍ → DeckSpace N))
      (formPreDomain.memLp_gradY F) q,
    componentL2_toModularL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F) q]
  rw [GaloisForLFunctions.HTGeometry.pairing_toModularL2,
    GaloisForLFunctions.HTGeometry.pairing_toModularL2]
  have h := component_testWeight_hypGradY F q T.contDiff T.compact T.support_subset
  simp only [GaloisForLFunctions.HTGeometry.InteriorTest.conjWeight,
    GaloisForLFunctions.HTGeometry.InteriorTest.conjWeightD, Complex.conj_conj,
    GaloisForLFunctions.HTGeometry.InteriorTest.weight,
    GaloisForLFunctions.HTGeometry.InteriorTest.weightD]
  change (∫ z in fd, (z.im : ℂ) * T.φ z *
      (hypGradY (F : ℍ → DeckSpace N) z) q ∂volume) +
      ∫ z in fd, (z.im : ℂ) * ((z.im : ℂ) * fderiv ℝ T.φ z Complex.I) *
        (F : ℍ → DeckSpace N) z q ∂volume = 0
  rw [h, neg_add_cancel]

/-- Finite-deck coordinate projections separate vector-valued `L²` classes. -/
theorem deckL2_eq_zero_of_forall_componentL2_eq_zero {N : ℕ} (V : DeckL2 N)
    (h : ∀ q : Deck N, componentL2 N q V = 0) : V = 0 := by
  have hzero : ∀ᵐ z ∂cellMeasure, ∀ q : Deck N,
      (GaloisForLFunctions.HTGeometry.modularToLp (componentL2 N q V)) z = 0 := by
    rw [ae_all_iff]
    intro q
    change ((componentL2 N q V : ComponentL2) : ℍ → ℂ) =ᵐ[cellMeasure] 0
    exact Lp.eq_zero_iff_ae_eq_zero.mp (h q)
  have hprojection : ∀ᵐ z ∂cellMeasure, ∀ q : Deck N,
      (GaloisForLFunctions.HTGeometry.modularToLp (componentL2 N q V)) z =
        (EuclideanSpace.proj (𝕜 := ℂ) q) (V z) := by
    rw [ae_all_iff]
    intro q
    exact (EuclideanSpace.proj (𝕜 := ℂ) q).coeFn_compLpL V
  apply Lp.ext
  filter_upwards [hzero, hprojection, Lp.coeFn_zero (DeckSpace N) 2 cellMeasure]
    with z hz hp hzeroLp
  apply PiLp.ext
  intro q
  have hq : (EuclideanSpace.proj (𝕜 := ℂ) q) (V z) = 0 := by
    rw [← hp q, hz q]
  rw [hzeroLp]
  simpa using hq

/-- The horizontal scalar coordinate constraint persists on the completed
finite-deck form domain. -/
theorem formDomainClosure_le_component_ker_X (N : ℕ) (q : Deck N)
    (T : GaloisForLFunctions.HTGeometry.InteriorTest) :
    formDomainClosure N ≤ LinearMap.ker
      (componentTestFunctional N q T 1 1 : FormTriple N →ₗ[ℂ] ℂ) := by
  refine Submodule.topologicalClosure_minimal _ ?_
    (componentTestFunctional N q T 1 1).isClosed_ker
  rintro _ ⟨F, rfl⟩
  exact componentTestFunctional_formEmbeddingMap_X F q T

/-- The vertical scalar coordinate constraint persists on the completed
finite-deck form domain. -/
theorem formDomainClosure_le_component_ker_Y (N : ℕ) (q : Deck N)
    (T : GaloisForLFunctions.HTGeometry.InteriorTest) :
    formDomainClosure N ≤ LinearMap.ker
      (componentTestFunctional N q T 2 Complex.I : FormTriple N →ₗ[ℂ] ℂ) := by
  refine Submodule.topologicalClosure_minimal _ ?_
    (componentTestFunctional N q T 2 Complex.I).isClosed_ker
  rintro _ ⟨F, rfl⟩
  exact componentTestFunctional_formEmbeddingMap_Y F q T

/-- Vanishing value coordinate forces both finite-deck derivative coordinates
to vanish; hence the completed finite-deck form has no hidden null vectors. -/
theorem formInclusion_eq_zero_imp {N : ℕ} {v : FormDomain N}
    (h0 : formInclusion N v = 0) : v = 0 := by
  change (v : FormTriple N).ofLp 0 = 0 at h0
  have h1 : (v : FormTriple N).ofLp 1 = 0 := by
    apply deckL2_eq_zero_of_forall_componentL2_eq_zero
    intro q
    apply GaloisForLFunctions.HTGeometry.eq_zero_of_forall_interiorTest
    intro T
    have hker := formDomainClosure_le_component_ker_X N q T v.2
    rw [LinearMap.mem_ker] at hker
    change componentTestFunctional N q T 1 1 v = 0 at hker
    rw [componentTestFunctional_apply, h0, map_zero, map_zero, add_zero,
      GaloisForLFunctions.HTGeometry.pairing_apply] at hker
    simpa [GaloisForLFunctions.HTGeometry.InteriorTest.conjWeight,
      Complex.conj_conj] using hker
  have h2 : (v : FormTriple N).ofLp 2 = 0 := by
    apply deckL2_eq_zero_of_forall_componentL2_eq_zero
    intro q
    apply GaloisForLFunctions.HTGeometry.eq_zero_of_forall_interiorTest
    intro T
    have hker := formDomainClosure_le_component_ker_Y N q T v.2
    rw [LinearMap.mem_ker] at hker
    change componentTestFunctional N q T 2 Complex.I v = 0 at hker
    rw [componentTestFunctional_apply, h0, map_zero, map_zero, add_zero,
      GaloisForLFunctions.HTGeometry.pairing_apply] at hker
    simpa [GaloisForLFunctions.HTGeometry.InteriorTest.conjWeight,
      Complex.conj_conj] using hker
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- **Closability of the finite-deck equivariant Dirichlet form.** -/
theorem formInclusion_injective (N : ℕ) : Function.Injective (formInclusion N) := by
  intro v w hvw
  have hzero := formInclusion_eq_zero_imp (N := N) (v := v - w) (by
    rw [map_sub, hvw, sub_self])
  exact sub_eq_zero.mp hzero

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
