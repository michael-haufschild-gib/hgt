import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ClopenHodgeTraceCoordinate
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.Trace

/-! A correspondence contributes to the Hodge trace only through source components
whose two images lie in the same target component. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

namespace GlobalTheory.SchemeCohomology

/-- Each member of a disjoint open cover is closed. -/
theorem isClosed_of_disjoint_open_cover {X : Scheme} {I : Type*} (U : I → X.Opens)
    (hdis : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) (hcov : iSup U = ⊤) (i : I) :
    IsClosed (U i : Set X) := by
  have e : (U i : Set X)ᶜ = ⋃ j ∈ {j | j ≠ i}, (U j : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · intro hx
      have hm : x ∈ iSup U := by rw [hcov]; trivial
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hm
      exact ⟨j, fun e => hx (e ▸ hj), hj⟩
    · rintro ⟨j, hji, hj⟩ hi
      have hm : x ∈ U j ⊓ U i := ⟨hj, hi⟩
      rw [hdis j i hji] at hm
      exact hm
  rw [← isOpen_compl_iff, e]
  exact isOpen_biUnion fun j _ => (U j).isOpen

/-- An integral source maps into one member of a clopen partition. -/
theorem exists_le_preimage_component {X Y : Scheme} {I : Type*}
    (f : Y ⟶ X) (W : Y.Opens) [IsIntegral W.toScheme] (V : I → X.Opens)
    (hcl : ∀ i, IsClosed (V i : Set X)) (hcov : iSup V = ⊤) :
    ∃ i, W ≤ f ⁻¹ᵁ V i := by
  let ξ := genericPoint W.toScheme
  have hm : f (W.ι ξ) ∈ iSup V := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hm
  refine ⟨i, fun y hy => ?_⟩
  have hspec : f (W.ι ξ) ⤳ f y :=
    (genericPoint_specializes (⟨y, hy⟩ : W.toScheme)).map (W.ι ≫ f).continuous
  exact closure_minimal (Set.singleton_subset_iff.mpr hi) (hcl i)
    (specializes_iff_mem_closure.mp hspec)

private theorem hodgePullback_congr_map {k : Type} [CommRing k] {X Y : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
    {f g : Y ⟶ X} (e : f = g) (hf : f ≫ s = t) (hg : g ≫ s = t) (p q : ℕ) :
    hodgePullback hf p q = hodgePullback hg p q := by
  subst g
  rfl

/-- Factoring each leg through its target component factors the Hodge operator
through restriction to the second component and trace from the first. -/
theorem hodgeCorrespondence_factor {k : Type} [CommRing k] {X Y X₁ X₂ : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
    {f₁ f₂ : Y ⟶ X} [IsFinite f₁] [Etale f₁]
    {i₁ : X₁ ⟶ X} [IsFinite i₁] [Etale i₁] {i₂ : X₂ ⟶ X}
    {g₁ : Y ⟶ X₁} [IsFinite g₁] [Etale g₁] {g₂ : Y ⟶ X₂}
    (e₁ : g₁ ≫ i₁ = f₁) (e₂ : g₂ ≫ i₂ = f₂) (h₁ : f₁ ≫ s = t) (h₂ : f₂ ≫ s = t)
    (a₁ : g₁ ≫ (i₁ ≫ s) = t) (a₂ : g₂ ≫ (i₂ ≫ s) = t) (p q : ℕ) :
    hodgeTrace h₁ p q ∘ₗ hodgePullback h₂ p q =
      hodgeTrace (f := i₁) rfl p q ∘ₗ
        (hodgeTrace a₁ p q ∘ₗ hodgePullback a₂ p q) ∘ₗ
        hodgePullback (s := s) (f := i₂) rfl p q := by
  let h₁' : (g₁ ≫ i₁) ≫ s = t := by rw [e₁]; exact h₁
  let h₂' : (g₂ ≫ i₂) ≫ s = t := by rw [e₂]; exact h₂
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [hodgePullback_comp (f := i₂) (g := g₂) rfl a₂ h₂',
    hodgePullback_congr_map e₂ h₂' h₂,
    ← hodgeTrace_congr e₁ h₁' h₁,
    hodgeTrace_trans (f := i₁) (g := g₁) rfl a₁ h₁']

section TraceBlocks

variable {k : Type} [Field k] {X : Scheme.{0}} {I : Type} [Fintype I] [DecidableEq I]
  (s : X ⟶ Spec (CommRingCat.of k)) (V : I → X.Opens)
  (hcl : ∀ i, IsClosed (V i : Set X))
  (hdis : ∀ i j, i ≠ j → V i ⊓ V j = ⊥) (hcov : iSup V = ⊤)
  (p q : ℕ) [FiniteDimensional k (HodgeCohomology s p q)]
  [∀ i, FiniteDimensional k (HodgeCohomology ((V i).ι ≫ s) p q)]
  [∀ i, IsClosedImmersion (V i).ι]

private theorem clopenTraceBlock (i j : I)
    (T : HodgeCohomology ((V j).ι ≫ s) p q →ₗ[k] HodgeCohomology ((V i).ι ≫ s) p q) :
    LinearMap.trace k _ (hodgeTrace (s := s) (f := (V i).ι) rfl p q ∘ₗ T ∘ₗ
        hodgePullback (s := s) (f := (V j).ι) rfl p q) =
      LinearMap.trace k _
        ((LinearMap.proj j ∘ₗ LinearMap.single k (fun i =>
          HodgeCohomology ((V i).ι ≫ s) p q) i) ∘ₗ T) := by
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  have he : hodgePullback (s := s) (f := (V j).ι) rfl p q ∘ₗ
      hodgeTrace (s := s) (f := (V i).ι) rfl p q =
    LinearMap.proj j ∘ₗ LinearMap.single k (fun a => HodgeCohomology ((V a).ι ≫ s) p q) i := by
    apply LinearMap.ext
    intro z
    exact congrFun (hodgeClopenEquiv_trace s V hcl hdis hcov p q i z) j
  rw [← LinearMap.comp_assoc, he]

/-- The trace of a block crossing two different clopen components vanishes. -/
theorem trace_clopen_off_diagonal {i j : I} (hij : i ≠ j)
    (T : HodgeCohomology ((V j).ι ≫ s) p q →ₗ[k] HodgeCohomology ((V i).ι ≫ s) p q) :
    LinearMap.trace k _ (hodgeTrace (s := s) (f := (V i).ι) rfl p q ∘ₗ T ∘ₗ
        hodgePullback (s := s) (f := (V j).ι) rfl p q) = 0 := by
  rw [clopenTraceBlock s V hcl hdis hcov p q, LinearMap.proj_comp_single_ne _ _ j i hij.symm,
    LinearMap.zero_comp, map_zero]

/-- The trace of a diagonal block is its trace on that component. -/
theorem trace_clopen_diagonal (i : I)
    (T : Module.End k (HodgeCohomology ((V i).ι ≫ s) p q)) :
    LinearMap.trace k _ (hodgeTrace (s := s) (f := (V i).ι) rfl p q ∘ₗ T ∘ₗ
        hodgePullback (s := s) (f := (V i).ι) rfl p q) = LinearMap.trace k _ T := by
  rw [clopenTraceBlock s V hcl hdis hcov p q, LinearMap.proj_comp_single_same,
    LinearMap.id_comp]

end TraceBlocks

end GlobalTheory.SchemeCohomology
