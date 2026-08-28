import GaloisForLFunctions.HTGeometry.CoefficientDominatedRefinementCollapse
import GaloisForLFunctions.HTGeometry.SerialObserverFormationCharge
import GaloisForLFunctions.HTGeometry.TernaryFormationDualityHodge
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.CategoryTheory.Abelian.Exact

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HigherAritySerialObserverFormation

open CoefficientDominatedRefinementCollapse

set_option linter.unusedSectionVars false

universe uR uI uE

variable (k : Type uR) [Field k] (ι : Type uI) [Fintype ι] [LinearOrder ι]
variable (E : Type uE) [AddCommGroup E] [Module k E]

def coefficientComplex (C : Coeff k ι E) : ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of
    (fun p => ModuleCat.of k (Chains k ι E C p))
    (fun p => ModuleCat.ofHom (boundary k ι E C (p := p)))
    (fun p => by
      apply ModuleCat.hom_ext
      exact boundary_sq k ι E C (p := p))

theorem coefficientBoundary_range_le_ker (C : Coeff k ι E) (p : ℕ) :
    LinearMap.range (boundary k ι E C (p := p + 1)) ≤
      LinearMap.ker (boundary k ι E C (p := p)) := by
  rw [LinearMap.range_le_ker_iff]
  exact boundary_sq k ι E C (p := p)

variable (E' : Type uE) [AddCommGroup E'] [Module k E']

def coefficientComplexMap {C : Coeff k ι E} {C' : Coeff k ι E'}
    (F : CoeffMorphism k ι E C E' C') :
    coefficientComplex k ι E C ⟶ coefficientComplex k ι E' C' :=
  ChainComplex.ofHom
    (fun p => ModuleCat.ofHom (coeffMap k ι E C E' C' F (p := p)))
    (fun p => by
      apply ModuleCat.hom_ext
      simp only [coefficientComplex, ChainComplex.of_d, ModuleCat.hom_comp,
        ModuleCat.hom_ofHom]
      exact coeffMap_comm_boundary k ι E C E' C' F (p := p))

variable (S : SerialFormationCoefficients k ι E)

def erasureShortComplex :
    ShortComplex (ChainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk
    (coefficientComplexMap k ι E E
      (coefficientInclusion k ι E S.kernel_le_upstream))
    (coefficientComplexMap k ι E E S.eraseMap)
    (by
      ext p
      rename_i x
      change coeffMap k ι E S.F_L E S.F_ML S.eraseMap
          (coeffMap k ι E S.K_M_over_L E S.F_L
            (coefficientInclusion k ι E S.kernel_le_upstream) x) = 0
      apply LinearMap.mem_ker.mp
      rw [← S.erase_exact p]
      exact ⟨x, rfl⟩)

theorem erasure_shortExact : (erasureShortComplex k ι E S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact
      (coeffMap k ι E S.K_M_over_L E S.F_L
        (coefficientInclusion k ι E S.kernel_le_upstream) (p := p))
      (coeffMap k ι E S.F_L E S.F_ML S.eraseMap (p := p))
    rw [LinearMap.exact_iff]
    exact (S.erase_exact p).symm
  · change Function.Injective
      (coeffMap k ι E S.K_M_over_L E S.F_L
        (coefficientInclusion k ι E S.kernel_le_upstream) (p := p))
    exact coefficientInclusion_injective k ι E S.kernel_le_upstream (p := p)
  · change Function.Surjective
      (coeffMap k ι E S.F_L E S.F_ML S.eraseMap (p := p))
    exact S.erase_surjective p

variable {P Q : Coeff k ι E} (h : CoeffLE k ι E P Q)

def retentionInclusion : coefficientComplex k ι E P ⟶ coefficientComplex k ι E Q :=
  coefficientComplexMap k ι E E (coefficientInclusion k ι E h)

instance retentionInclusion_mono : Mono (retentionInclusion k ι E h) :=
  HomologicalComplex.mono_of_mono_f _ fun p =>
    (ModuleCat.mono_iff_injective _).2
      (coefficientInclusion_injective k ι E h (p := p))

def retentionShortComplex : ShortComplex (ChainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk (retentionInclusion k ι E h)
    (cokernel.π (retentionInclusion k ι E h))
    (cokernel.condition (retentionInclusion k ι E h))

theorem retention_shortExact : (retentionShortComplex k ι E h).ShortExact := by
  refine ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel (retentionInclusion k ι E h)) ?_ ?_
  · change Mono (retentionInclusion k ι E h)
    exact retentionInclusion_mono k ι E h
  · change Epi (cokernel.π (retentionInclusion k ι E h))
    infer_instance

variable (V : Type uE) [AddCommGroup V] [Module k V]

def familyIntersection (W : ι → Submodule k V) (s : Finset ι) : Submodule k V :=
  ⨅ i, ⨅ (_ : i ∈ s), W i

def familyJoin (W : ι → Submodule k V) : Submodule k V :=
  ⨆ i, W i

theorem familyIntersection_anti (W : ι → Submodule k V) {s t : Finset ι}
    (h : t ⊆ s) : familyIntersection k ι V W s ≤ familyIntersection k ι V W t := by
  intro x hx
  simp only [familyIntersection, Submodule.mem_iInf] at hx ⊢
  intro i hi
  exact hx i (h hi)

theorem familyIntersection_le_leg (W : ι → Submodule k V) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : familyIntersection k ι V W s ≤ W i := by
  intro x hx
  simp only [familyIntersection, Submodule.mem_iInf] at hx
  exact hx i hi

def formationObject (W : ι → Submodule k V) (s : Finset ι) : Submodule k V :=
  if s.Nonempty then familyIntersection k ι V W s else familyJoin k ι V W

def formationCoeff (W : ι → Submodule k V) : Coeff k ι V where
  obj := formationObject k ι V W
  anti := by
    intro s t h
    by_cases ht : t.Nonempty
    · have hs : s.Nonempty := ht.mono h
      simp only [formationObject, if_pos hs, if_pos ht]
      exact familyIntersection_anti k ι V W h
    · simp only [formationObject, ht, if_false]
      by_cases hs : s.Nonempty
      · rw [if_pos hs]
        rcases hs with ⟨i, hi⟩
        exact (familyIntersection_le_leg k ι V W hi).trans (le_iSup W i)
      · rw [if_neg hs]

def imageCoeff (C : Coeff k ι V) (f : V →ₗ[k] E) : Coeff k ι E where
  obj s := (C.obj s).map f
  anti := fun h => Submodule.map_mono (C.anti h)

def kernelCoeff (C : Coeff k ι V) (f : V →ₗ[k] E) : Coeff k ι V where
  obj s := C.obj s ⊓ LinearMap.ker f
  anti := fun h => inf_le_inf (C.anti h) le_rfl

theorem kernelCoeffLE (C : Coeff k ι V) (f : V →ₗ[k] E) :
    CoeffLE k ι V (kernelCoeff k ι E V C f) C :=
  fun _ => inf_le_left

def imageCoeffMorphism (C : Coeff k ι V) (f : V →ₗ[k] E) :
    CoeffMorphism k ι V C E (imageCoeff k ι E V C f) where
  map := f
  map_obj _ x hx := ⟨x, hx, rfl⟩

theorem imageCoeffMap_surjective (C : Coeff k ι V) (f : V →ₗ[k] E) (p : ℕ) :
    Function.Surjective
      (coeffMap k ι V C E (imageCoeff k ι E V C f)
        (imageCoeffMorphism k ι E V C f) (p := p)) := by
  intro y
  have hy := (mem_chainSubmodule_iff k ι E (imageCoeff k ι E V C f) y.1).mp y.2
  choose x hxC hfx using fun s => hy s
  let xAmb : AmbientChains ι V p :=
    ∑ s : Simplex ι p, DirectSum.lof k (Simplex ι p) (fun _ => V) s (x s)
  have hcomp (s : Simplex ι p) :
      DirectSum.component k (Simplex ι p) (fun _ => V) s xAmb = x s := by
    rw [← DirectSum.apply_eq_component]
    change (DirectSum.linearEquivFunOnFintype k (Simplex ι p) (fun _ => V) xAmb) s = x s
    simp only [xAmb, map_sum, DirectSum.linearEquivFunOnFintype_lof]
    rw [Finset.univ_sum_single]
  have hxAmb : xAmb ∈ chainSubmodule k ι V C p := by
    rw [mem_chainSubmodule_iff]
    intro s
    rw [hcomp s]
    exact hxC s
  refine ⟨⟨xAmb, hxAmb⟩, ?_⟩
  apply Subtype.ext
  change ambientCoeffMap k ι V C E (imageCoeff k ι E V C f)
      (imageCoeffMorphism k ι E V C f) xAmb = y.1
  calc
    _ = ∑ s : Simplex ι p,
        DirectSum.lof k (Simplex ι p) (fun _ => E) s (f (x s)) := by
      simp [xAmb, ambientCoeffMap, imageCoeffMorphism]
    _ = ∑ s : Simplex ι p,
        DirectSum.lof k (Simplex ι p) (fun _ => E) s
          (DirectSum.component k (Simplex ι p) (fun _ => E) s y.1) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [hfx s]
    _ = y.1 := sum_lof_component k ι E y.1

theorem ambientCoeffMap_eq_sum {C : Coeff k ι V} {C' : Coeff k ι E}
    (F : CoeffMorphism k ι V C E C') {p : ℕ} (x : AmbientChains ι V p) :
    ambientCoeffMap k ι V C E C' F x =
      ∑ s : Simplex ι p,
        DirectSum.lof k (Simplex ι p) (fun _ => E) s
          (F.map (DirectSum.component k (Simplex ι p) (fun _ => V) s x)) := by
  calc
    _ = ambientCoeffMap k ι V C E C' F
        (∑ s : Simplex ι p,
          DirectSum.lof k (Simplex ι p) (fun _ => V) s
            (DirectSum.component k (Simplex ι p) (fun _ => V) s x)) := by
      exact congrArg (ambientCoeffMap k ι V C E C' F)
        (sum_lof_component k ι V x).symm
    _ = _ := by simp [ambientCoeffMap]

theorem component_ambientCoeffMap {C : Coeff k ι V} {C' : Coeff k ι E}
    (F : CoeffMorphism k ι V C E C') {p : ℕ} (x : AmbientChains ι V p)
    (s : Simplex ι p) :
    DirectSum.component k (Simplex ι p) (fun _ => E) s
        (ambientCoeffMap k ι V C E C' F x) =
      F.map (DirectSum.component k (Simplex ι p) (fun _ => V) s x) := by
  rw [ambientCoeffMap_eq_sum k ι E V F x]
  rw [← DirectSum.apply_eq_component]
  change (DirectSum.linearEquivFunOnFintype k (Simplex ι p) (fun _ => E)
    (∑ t : Simplex ι p,
      DirectSum.lof k (Simplex ι p) (fun _ => E) t
        (F.map (DirectSum.component k (Simplex ι p) (fun _ => V) t x)))) s = _
  simp only [map_sum, DirectSum.linearEquivFunOnFintype_lof]
  have hsum := congrFun (Finset.univ_sum_single fun t : Simplex ι p =>
    F.map (DirectSum.component k (Simplex ι p) (fun _ => V) t x)) s
  exact hsum

theorem kernel_image_chain_exact (C : Coeff k ι V) (f : V →ₗ[k] E) (p : ℕ) :
    LinearMap.range
        (coeffMap k ι V (kernelCoeff k ι E V C f) V C
          (coefficientInclusion k ι V (kernelCoeffLE k ι E V C f)) (p := p)) =
      LinearMap.ker
        (coeffMap k ι V C E (imageCoeff k ι E V C f)
          (imageCoeffMorphism k ι E V C f) (p := p)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change ambientCoeffMap k ι V C E (imageCoeff k ι E V C f)
        (imageCoeffMorphism k ι E V C f)
        (ambientCoeffMap k ι V (kernelCoeff k ι E V C f) V C
          (coefficientInclusion k ι V (kernelCoeffLE k ι E V C f)) x.1) = 0
    rw [ambientCoeffMap_inclusion_eq_id k ι V (kernelCoeffLE k ι E V C f)]
    rw [ambientCoeffMap_eq_sum k ι E V (imageCoeffMorphism k ι E V C f)]
    apply Finset.sum_eq_zero
    intro s _
    have hs := (mem_chainSubmodule_iff k ι V (kernelCoeff k ι E V C f) x.1).mp x.2 s
    have hz : f (DirectSum.component k (Simplex ι p) (fun _ => V) s x.1) = 0 :=
      LinearMap.mem_ker.mp hs.2
    simp [imageCoeffMorphism, hz]
  · intro x hx
    have hxC := (mem_chainSubmodule_iff k ι V C x.1).mp x.2
    have hxzero (s : Simplex ι p) :
        f (DirectSum.component k (Simplex ι p) (fun _ => V) s x.1) = 0 := by
      have hval := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      have hs := congrArg
        (DirectSum.component k (Simplex ι p) (fun _ => E) s) hval
      change DirectSum.component k (Simplex ι p) (fun _ => E) s
          (ambientCoeffMap k ι V C E (imageCoeff k ι E V C f)
            (imageCoeffMorphism k ι E V C f) x.1) = 0 at hs
      rw [component_ambientCoeffMap k ι E V
        (imageCoeffMorphism k ι E V C f) x.1 s] at hs
      simpa [imageCoeffMorphism] using hs
    have hxK : x.1 ∈ chainSubmodule k ι V (kernelCoeff k ι E V C f) p := by
      rw [mem_chainSubmodule_iff]
      intro s
      exact ⟨hxC s, hxzero s⟩
    refine ⟨⟨x.1, hxK⟩, ?_⟩
    apply Subtype.ext
    exact LinearMap.congr_fun
      (ambientCoeffMap_inclusion_eq_id k ι V (kernelCoeffLE k ι E V C f)) x.1

def observerErasureShortComplex (C : Coeff k ι V) (f : V →ₗ[k] E) :
    ShortComplex (ChainComplex (ModuleCat k) ℕ) :=
  ShortComplex.mk
    (coefficientComplexMap k ι V V
      (coefficientInclusion k ι V (kernelCoeffLE k ι E V C f)))
    (coefficientComplexMap k ι V E (imageCoeffMorphism k ι E V C f))
    (by
      ext p
      rename_i x
      change coeffMap k ι V C E (imageCoeff k ι E V C f)
          (imageCoeffMorphism k ι E V C f)
          (coeffMap k ι V (kernelCoeff k ι E V C f) V C
            (coefficientInclusion k ι V (kernelCoeffLE k ι E V C f)) x) = 0
      apply LinearMap.mem_ker.mp
      rw [← kernel_image_chain_exact k ι E V C f p]
      exact ⟨x, rfl⟩)

theorem observerErasure_shortExact (C : Coeff k ι V) (f : V →ₗ[k] E) :
    (observerErasureShortComplex k ι E V C f).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro p
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact
      (coeffMap k ι V (kernelCoeff k ι E V C f) V C
        (coefficientInclusion k ι V (kernelCoeffLE k ι E V C f)) (p := p))
      (coeffMap k ι V C E (imageCoeff k ι E V C f)
        (imageCoeffMorphism k ι E V C f) (p := p))
    rw [LinearMap.exact_iff]
    exact (kernel_image_chain_exact k ι E V C f p).symm
  · change Function.Injective
      (coeffMap k ι V (kernelCoeff k ι E V C f) V C
        (coefficientInclusion k ι V (kernelCoeffLE k ι E V C f)) (p := p))
    exact coefficientInclusion_injective k ι V (kernelCoeffLE k ι E V C f)
  · change Function.Surjective
      (coeffMap k ι V C E (imageCoeff k ι E V C f)
        (imageCoeffMorphism k ι E V C f) (p := p))
    exact imageCoeffMap_surjective k ι E V C f p

variable (Z : Type uE) [AddCommGroup Z] [Module k Z]

def upstreamCoeff (W : ι → Submodule k V) (L : V →ₗ[k] E) : Coeff k ι E :=
  imageCoeff k ι E V (formationCoeff k ι V W) L

def compositeCoeff (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    Coeff k ι Z :=
  imageCoeff k ι Z E (upstreamCoeff k ι E V W L) M

theorem map_familyIntersection_le (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (s : Finset ι) :
    (familyIntersection k ι V W s).map L ≤
      familyIntersection k ι E (fun i => (W i).map L) s := by
  refine le_iInf fun i => le_iInf fun hi => ?_
  exact Submodule.map_mono (familyIntersection_le_leg k ι V W hi)

def retainedObject (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z)
    (s : Finset ι) : Submodule k Z :=
  if s.Nonempty then
    (familyIntersection k ι E (fun i => (W i).map L) s).map M
  else
    (compositeCoeff k ι E V Z W L M).obj s

def retainedCoeff (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    Coeff k ι Z where
  obj := retainedObject k ι E V Z W L M
  anti := by
    intro s t h
    by_cases ht : t.Nonempty
    · have hs : s.Nonempty := ht.mono h
      simp only [retainedObject, if_pos hs, if_pos ht]
      exact Submodule.map_mono (familyIntersection_anti k ι E _ h)
    · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      simp only [retainedObject, Finset.not_nonempty_empty, if_false]
      by_cases hs : s.Nonempty
      · rw [if_pos hs]
        rcases hs with ⟨i, hi⟩
        change (familyIntersection k ι E (fun j => (W j).map L) s).map M ≤
          ((familyJoin k ι V W).map L).map M
        apply Submodule.map_mono
        exact (familyIntersection_le_leg k ι E (fun j => (W j).map L) hi).trans
          (Submodule.map_mono (le_iSup W i))
      · rw [if_neg hs]
        have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        exact le_rfl

theorem directCoeffLE (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    CoeffLE k ι Z (compositeCoeff k ι E V Z W L M)
      (retainedCoeff k ι E V Z W L M) := by
  intro s
  by_cases hs : s.Nonempty
  · simp only [compositeCoeff, upstreamCoeff, imageCoeff, formationCoeff,
      formationObject, retainedCoeff, retainedObject, if_pos hs]
    exact Submodule.map_mono (map_familyIntersection_le k ι E V W L s)
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [retainedCoeff, retainedObject]

def serialErasureShortComplex (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) : ShortComplex (ChainComplex (ModuleCat k) ℕ) :=
  observerErasureShortComplex k ι Z E (upstreamCoeff k ι E V W L) M

theorem serialErasure_shortExact (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) : (serialErasureShortComplex k ι E V Z W L M).ShortExact :=
  observerErasure_shortExact k ι Z E (upstreamCoeff k ι E V W L) M

def serialRetentionShortComplex (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) : ShortComplex (ChainComplex (ModuleCat k) ℕ) :=
  retentionShortComplex k ι Z (directCoeffLE k ι E V Z W L M)

theorem serialRetention_shortExact (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) : (serialRetentionShortComplex k ι E V Z W L M).ShortExact :=
  retention_shortExact k ι Z (directCoeffLE k ι E V Z W L M)

noncomputable def serialErasureConnecting (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) (p : ℕ) :
    (serialErasureShortComplex k ι E V Z W L M).X₃.homology (p + 1) ⟶
      (serialErasureShortComplex k ι E V Z W L M).X₁.homology p :=
  (serialErasure_shortExact k ι E V Z W L M).δ (p + 1) p (by simp)

theorem serialErasure_exact_sameDegree (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) (p : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (serialErasureShortComplex k ι E V Z W L M).f p)
      (HomologicalComplex.homologyMap
        (serialErasureShortComplex k ι E V Z W L M).g p)
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          (serialErasureShortComplex k ι E V Z W L M).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (serialErasure_shortExact k ι E V Z W L M).homology_exact₂ p

theorem serialErasure_exact_toConnecting (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) (p : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (serialErasureShortComplex k ι E V Z W L M).g (p + 1))
      (serialErasureConnecting k ι E V Z W L M p)
      (by
        exact (serialErasure_shortExact k ι E V Z W L M).comp_δ
          (p + 1) p (by simp))).Exact := by
  simpa [serialErasureConnecting] using
    (serialErasure_shortExact k ι E V Z W L M).homology_exact₃ (p + 1) p (by simp)

theorem serialErasure_exact_fromConnecting (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) (p : ℕ) :
    (ShortComplex.mk
      (serialErasureConnecting k ι E V Z W L M p)
      (HomologicalComplex.homologyMap
        (serialErasureShortComplex k ι E V Z W L M).f p)
      (by
        exact (serialErasure_shortExact k ι E V Z W L M).δ_comp
          (p + 1) p (by simp))).Exact := by
  simpa [serialErasureConnecting] using
    (serialErasure_shortExact k ι E V Z W L M).homology_exact₁ (p + 1) p (by simp)

noncomputable def serialRetentionConnecting (W : ι → Submodule k V)
    (L : V →ₗ[k] E) (M : E →ₗ[k] Z) (p : ℕ) :
    (serialRetentionShortComplex k ι E V Z W L M).X₃.homology (p + 1) ⟶
      (serialRetentionShortComplex k ι E V Z W L M).X₁.homology p :=
  (serialRetention_shortExact k ι E V Z W L M).δ (p + 1) p (by simp)

theorem serialRetention_exact_sameDegree (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) (p : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (serialRetentionShortComplex k ι E V Z W L M).f p)
      (HomologicalComplex.homologyMap
        (serialRetentionShortComplex k ι E V Z W L M).g p)
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          (serialRetentionShortComplex k ι E V Z W L M).zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  (serialRetention_shortExact k ι E V Z W L M).homology_exact₂ p

theorem serialRetention_exact_toConnecting (W : ι → Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) (p : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (serialRetentionShortComplex k ι E V Z W L M).g (p + 1))
      (serialRetentionConnecting k ι E V Z W L M p)
      (by
        exact (serialRetention_shortExact k ι E V Z W L M).comp_δ
          (p + 1) p (by simp))).Exact := by
  simpa [serialRetentionConnecting] using
    (serialRetention_shortExact k ι E V Z W L M).homology_exact₃ (p + 1) p (by simp)

theorem serialRetention_exact_fromConnecting (W : ι → Submodule k V)
    (L : V →ₗ[k] E) (M : E →ₗ[k] Z) (p : ℕ) :
    (ShortComplex.mk
      (serialRetentionConnecting k ι E V Z W L M p)
      (HomologicalComplex.homologyMap
        (serialRetentionShortComplex k ι E V Z W L M).f p)
      (by
        exact (serialRetention_shortExact k ι E V Z W L M).δ_comp
          (p + 1) p (by simp))).Exact := by
  simpa [serialRetentionConnecting] using
    (serialRetention_shortExact k ι E V Z W L M).homology_exact₁ (p + 1) p (by simp)

theorem twoLeg_serialObserver_fiveTerm_exact (A B : Submodule k V) (L : V →ₗ[k] E)
    (M : E →ₗ[k] Z) :
    Function.Injective (GaloisForLFunctions.HTGeometry.erasedToOverlap M L A B)
      ∧ LinearMap.range (GaloisForLFunctions.HTGeometry.erasedToOverlap M L A B) =
        LinearMap.ker (GaloisForLFunctions.HTGeometry.overlapPush M L A B)
      ∧ LinearMap.range (GaloisForLFunctions.HTGeometry.overlapPush M L A B) =
        LinearMap.ker (GaloisForLFunctions.HTGeometry.overlapProject M L A B)
      ∧ Function.Surjective (GaloisForLFunctions.HTGeometry.overlapProject M L A B) :=
  GaloisForLFunctions.HTGeometry.serialObserver_exact M L A B

theorem connecting_natural
    {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat k) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (p : ℕ) :
    hS₁.δ (p + 1) p (by simp) ≫ HomologicalComplex.homologyMap φ.τ₁ p =
      HomologicalComplex.homologyMap φ.τ₃ (p + 1) ≫ hS₂.δ (p + 1) p (by simp) :=
  HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ (p + 1) p (by simp)

theorem erasureConnecting_natural
    {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat k) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (p : ℕ) :
    hS₁.δ (p + 1) p (by simp) ≫ HomologicalComplex.homologyMap φ.τ₁ p =
      HomologicalComplex.homologyMap φ.τ₃ (p + 1) ≫ hS₂.δ (p + 1) p (by simp) :=
  connecting_natural k φ hS₁ hS₂ p

theorem retentionConnecting_natural
    {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat k) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (p : ℕ) :
    hS₁.δ (p + 1) p (by simp) ≫ HomologicalComplex.homologyMap φ.τ₁ p =
      HomologicalComplex.homologyMap φ.τ₃ (p + 1) ≫ hS₂.δ (p + 1) p (by simp) :=
  connecting_natural k φ hS₁ hS₂ p

def InjectiveOnTop (C : Coeff k ι V) (f : V →ₗ[k] E) : Prop :=
  Set.InjOn f (C.obj ∅)

theorem coefficient_obj_le_top (C : Coeff k ι V) (s : Finset ι) :
    C.obj s ≤ C.obj ∅ :=
  C.anti (Finset.empty_subset s)

theorem kernelCoeff_obj_eq_bot_of_injectiveOnTop
    (C : Coeff k ι V) (f : V →ₗ[k] E) (hinj : InjectiveOnTop k ι E V C f)
    (s : Finset ι) : (kernelCoeff k ι E V C f).obj s = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_bot]
    apply hinj (coefficient_obj_le_top k ι V C s hx.1) (Submodule.zero_mem _)
    simpa using LinearMap.mem_ker.mp hx.2
  · exact bot_le

theorem coeffMap_injective_of_injectiveOnTop
    (C : Coeff k ι V) (f : V →ₗ[k] E) (hinj : InjectiveOnTop k ι E V C f)
    (p : ℕ) :
    Function.Injective
      (coeffMap k ι V C E (imageCoeff k ι E V C f)
        (imageCoeffMorphism k ι E V C f) (p := p)) := by
  intro x y hxy
  apply Subtype.ext
  apply (DirectSum.linearEquivFunOnFintype k (Simplex ι p) (fun _ => V)).injective
  funext s
  have hxC := (mem_chainSubmodule_iff k ι V C x.1).mp x.2 s
  have hyC := (mem_chainSubmodule_iff k ι V C y.1).mp y.2 s
  apply hinj
    (coefficient_obj_le_top k ι V C s (hxC))
    (coefficient_obj_le_top k ι V C s (hyC))
  have hval := congrArg Subtype.val hxy
  have hs := congrArg
    (DirectSum.component k (Simplex ι p) (fun _ => E) s) hval
  change DirectSum.component k (Simplex ι p) (fun _ => E) s
      (ambientCoeffMap k ι V C E (imageCoeff k ι E V C f)
        (imageCoeffMorphism k ι E V C f) x.1) =
    DirectSum.component k (Simplex ι p) (fun _ => E) s
      (ambientCoeffMap k ι V C E (imageCoeff k ι E V C f)
        (imageCoeffMorphism k ι E V C f) y.1) at hs
  simpa [component_ambientCoeffMap, imageCoeffMorphism] using hs

theorem neutralCoefficientComplexMap_isIso
    (C : Coeff k ι V) (f : V →ₗ[k] E) (hinj : InjectiveOnTop k ι E V C f) :
    IsIso (coefficientComplexMap k ι V E (imageCoeffMorphism k ι E V C f)) := by
  let F := coefficientComplexMap k ι V E (imageCoeffMorphism k ι E V C f)
  letI (p : ℕ) : IsIso (F.f p) :=
    (ConcreteCategory.isIso_iff_bijective (F.f p)).mpr
      ⟨coeffMap_injective_of_injectiveOnTop k ι E V C f hinj p,
        imageCoeffMap_surjective k ι E V C f p⟩
  exact HomologicalComplex.Hom.isIso_of_components F

theorem neutralHomologyMap_isIso
    (C : Coeff k ι V) (f : V →ₗ[k] E) (hinj : InjectiveOnTop k ι E V C f)
    (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (coefficientComplexMap k ι V E (imageCoeffMorphism k ι E V C f)) p) := by
  letI := neutralCoefficientComplexMap_isIso k ι E V C f hinj
  infer_instance

theorem map_familyIntersection_eq_of_injectiveOnJoin
    (W : ι → Submodule k V) (f : V →ₗ[k] E)
    (hinj : Set.InjOn f (familyJoin k ι V W)) {s : Finset ι} (hs : s.Nonempty) :
    (familyIntersection k ι V W s).map f =
      familyIntersection k ι E (fun i => (W i).map f) s := by
  apply le_antisymm (map_familyIntersection_le k ι E V W f s)
  intro x hx
  rcases hs with ⟨i₀, hi₀⟩
  have hxAll : ∀ i, ∀ (_ : i ∈ s), x ∈ (W i).map f := by
    simpa [familyIntersection] using hx
  have hx₀ := hxAll i₀ hi₀
  rcases hx₀ with ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  have hyAll : ∀ i, ∀ (_ : i ∈ s), y ∈ W i := by
    intro i hi
    have hxi := hxAll i hi
    rcases hxi with ⟨z, hz, heq⟩
    have hyJoin : y ∈ familyJoin k ι V W := (le_iSup W i₀) hy
    have hzJoin : z ∈ familyJoin k ι V W := (le_iSup W i) hz
    simpa [hinj hyJoin hzJoin heq.symm] using hz
  simpa [familyIntersection] using hyAll

theorem serialNeutral_kernel_zero
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z)
    (hinj : Set.InjOn M ((familyJoin k ι V W).map L)) (s : Finset ι) :
    (kernelCoeff k ι Z E (upstreamCoeff k ι E V W L) M).obj s = ⊥ := by
  apply kernelCoeff_obj_eq_bot_of_injectiveOnTop
  intro x hx y hy hxy
  exact hinj (by simpa [upstreamCoeff, imageCoeff, formationCoeff, formationObject] using hx)
    (by simpa [upstreamCoeff, imageCoeff, formationCoeff, formationObject] using hy) hxy

theorem serialNeutral_intersections
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z)
    (hinj : Set.InjOn M ((familyJoin k ι V W).map L))
    {s : Finset ι} (hs : s.Nonempty) :
    (familyIntersection k ι E (fun i => (W i).map L) s).map M =
      familyIntersection k ι Z (fun i => ((W i).map L).map M) s := by
  refine map_familyIntersection_eq_of_injectiveOnJoin k ι Z E
    (fun i => (W i).map L) M ?_ hs
  intro x hx y hy hxy
  apply hinj
  · exact iSup_le (fun i => Submodule.map_mono (le_iSup W i)) hx
  · exact iSup_le (fun i => Submodule.map_mono (le_iSup W i)) hy
  · exact hxy

noncomputable def submoduleMapEquivOfInjOn
    (S : Submodule k V) (f : V →ₗ[k] E) (hinj : Set.InjOn f S) :
    S ≃ₗ[k] S.map f := by
  let fS : S →ₗ[k] S.map f :=
    (f.domRestrict S).codRestrict (S.map f) (fun x => Submodule.mem_map_of_mem x.2)
  exact LinearEquiv.ofBijective fS ⟨
    (fun x y hxy => by
      apply Subtype.ext
      apply hinj x.2 y.2
      exact congrArg Subtype.val hxy),
    (fun y => by
      rcases y.2 with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy)⟩

noncomputable def subquotientMapEquivOfInjOn
    (S N : Submodule k V) (hNS : N ≤ S) (f : V →ₗ[k] E)
    (hinj : Set.InjOn f S) :
    (↥S ⧸ Submodule.comap S.subtype N) ≃ₗ[k]
      (↥(S.map f) ⧸ Submodule.comap (S.map f).subtype (N.map f)) :=
  Submodule.Quotient.equiv
    (Submodule.comap S.subtype N)
    (Submodule.comap (S.map f).subtype (N.map f))
    (submoduleMapEquivOfInjOn k E V S f hinj)
    (by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        change f y.1 ∈ N.map f
        exact Submodule.mem_map_of_mem hy
      · intro x hx
        change (x : E) ∈ N.map f at hx
        rcases hx with ⟨v, hv, hvx⟩
        let vS : S := ⟨v, hNS hv⟩
        refine ⟨vS, hv, ?_⟩
        apply Subtype.ext
        exact hvx)

noncomputable def serialNeutral_comparisonQuotientEquiv
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z)
    (hinj : Set.InjOn M ((familyJoin k ι V W).map L))
    {s : Finset ι} (hs : s.Nonempty) :
    let S := familyIntersection k ι E (fun i => (W i).map L) s
    let N := (familyIntersection k ι V W s).map L
    (↥S ⧸ Submodule.comap S.subtype N) ≃ₗ[k]
      (↥(S.map M) ⧸ Submodule.comap (S.map M).subtype (N.map M)) := by
  dsimp only
  apply subquotientMapEquivOfInjOn k Z E
    (familyIntersection k ι E (fun i => (W i).map L) s)
    ((familyIntersection k ι V W s).map L)
    (map_familyIntersection_le k ι E V W L s) M
  rcases hs with ⟨i₀, hi₀⟩
  intro x hx y hy hxy
  apply hinj
  · exact ((familyIntersection_le_leg k ι E (fun i => (W i).map L) hi₀).trans
      (Submodule.map_mono (le_iSup W i₀))) hx
  · exact ((familyIntersection_le_leg k ι E (fun i => (W i).map L) hi₀).trans
      (Submodule.map_mono (le_iSup W i₀))) hy
  · exact hxy

theorem serialNeutral_chainMap_isIso
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z)
    (hinj : Set.InjOn M ((familyJoin k ι V W).map L)) :
    IsIso (coefficientComplexMap k ι E Z
      (imageCoeffMorphism k ι Z E (upstreamCoeff k ι E V W L) M)) := by
  apply neutralCoefficientComplexMap_isIso
  intro x hx y hy hxy
  exact hinj (by simpa [upstreamCoeff, imageCoeff, formationCoeff, formationObject] using hx)
    (by simpa [upstreamCoeff, imageCoeff, formationCoeff, formationObject] using hy) hxy

theorem serialNeutral_homologyMap_isIso
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z)
    (hinj : Set.InjOn M ((familyJoin k ι V W).map L)) (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (coefficientComplexMap k ι E Z
        (imageCoeffMorphism k ι Z E (upstreamCoeff k ι E V W L) M)) p) := by
  letI := serialNeutral_chainMap_isIso k ι E V Z W L M hinj
  infer_instance

theorem finrank_middle_of_exact
    {A B D : Type uE} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B]
    [AddCommGroup D] [Module k D]
    (f : A →ₗ[k] B) (g : B →ₗ[k] D)
    (hexact : LinearMap.range f = LinearMap.ker g) :
    Module.finrank k B =
      Module.finrank k (LinearMap.range f) + Module.finrank k (LinearMap.range g) := by
  have hrank := LinearMap.finrank_range_add_finrank_ker g
  rw [← hexact] at hrank
  exact hrank.symm.trans (Nat.add_comm _ _)

noncomputable def homologyBoundedEuler
    (K : ChainComplex (ModuleCat k) ℕ) (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.range n, ((-1 : ℤ) ^ p) * Module.finrank k (K.homology p)

noncomputable def connectingRank
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact) (p : ℕ) : ℕ :=
  Module.finrank k (LinearMap.range (hT.δ (p + 1) p (by simp)).hom)

theorem homologyEuler_point_zero
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact)
    (hfin₁ : FiniteDimensional k (T.X₁.homology 0))
    (hfin₂ : FiniteDimensional k (T.X₂.homology 0)) :
    (Module.finrank k (T.X₁.homology 0) : ℤ) -
        Module.finrank k (T.X₂.homology 0) +
      Module.finrank k (T.X₃.homology 0) = connectingRank k T hT 0 := by
  letI := hfin₁
  letI := hfin₂
  let δ := (hT.δ 1 0 (by simp)).hom
  let f := (HomologicalComplex.homologyMap T.f 0).hom
  let g := (HomologicalComplex.homologyMap T.g 0).hom
  have hA := finrank_middle_of_exact k δ f
    (hT.homology_exact₁ 1 0 (by simp)).moduleCat_range_eq_ker
  have hB := finrank_middle_of_exact k f g
    (hT.homology_exact₂ 0).moduleCat_range_eq_ker
  haveI : Epi (T.g.f 0) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp hT 0).epi_g
  haveI : Epi (HomologicalComplex.homologyMap T.g 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel T.g 0 (fun j hj => by simp at hj)
  have hsurj : Function.Surjective g := (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hC : Module.finrank k (T.X₃.homology 0) =
      Module.finrank k (LinearMap.range g) := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  change (Module.finrank k (T.X₁.homology 0) : ℤ) -
      Module.finrank k (T.X₂.homology 0) + Module.finrank k (T.X₃.homology 0) =
    Module.finrank k (LinearMap.range δ)
  omega

theorem homologyEuler_point_succ
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact) (p : ℕ)
    (hfin₁ : FiniteDimensional k (T.X₁.homology (p + 1)))
    (hfin₂ : FiniteDimensional k (T.X₂.homology (p + 1)))
    (hfin₃ : FiniteDimensional k (T.X₃.homology (p + 1))) :
    (Module.finrank k (T.X₁.homology (p + 1)) : ℤ) -
        Module.finrank k (T.X₂.homology (p + 1)) +
      Module.finrank k (T.X₃.homology (p + 1)) =
        connectingRank k T hT (p + 1) + connectingRank k T hT p := by
  letI := hfin₁
  letI := hfin₂
  letI := hfin₃
  let δnext := (hT.δ (p + 2) (p + 1) (by simp)).hom
  let f := (HomologicalComplex.homologyMap T.f (p + 1)).hom
  let g := (HomologicalComplex.homologyMap T.g (p + 1)).hom
  let δprev := (hT.δ (p + 1) p (by simp)).hom
  have hA := finrank_middle_of_exact k δnext f
    (hT.homology_exact₁ (p + 2) (p + 1) (by simp)).moduleCat_range_eq_ker
  have hB := finrank_middle_of_exact k f g
    (hT.homology_exact₂ (p + 1)).moduleCat_range_eq_ker
  have hC := finrank_middle_of_exact k g δprev
    (hT.homology_exact₃ (p + 1) p (by simp)).moduleCat_range_eq_ker
  change (Module.finrank k (T.X₁.homology (p + 1)) : ℤ) -
      Module.finrank k (T.X₂.homology (p + 1)) +
        Module.finrank k (T.X₃.homology (p + 1)) =
    Module.finrank k (LinearMap.range δnext) + Module.finrank k (LinearMap.range δprev)
  omega

noncomputable def homologyEulerDefect
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (n : ℕ) : ℤ :=
  homologyBoundedEuler k T.X₁ n - homologyBoundedEuler k T.X₂ n +
    homologyBoundedEuler k T.X₃ n

theorem homologyEulerDefect_succ
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (n : ℕ) :
    homologyEulerDefect k T (n + 1) = homologyEulerDefect k T n +
      ((-1 : ℤ) ^ n) *
        ((Module.finrank k (T.X₁.homology n) : ℤ) -
          Module.finrank k (T.X₂.homology n) + Module.finrank k (T.X₃.homology n)) := by
  simp only [homologyEulerDefect, homologyBoundedEuler, Finset.sum_range_succ]
  ring

theorem homologyEulerDefect_eq_connectingRank
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact)
    (hfin₁ : ∀ p, FiniteDimensional k (T.X₁.homology p))
    (hfin₂ : ∀ p, FiniteDimensional k (T.X₂.homology p))
    (hfin₃ : ∀ p, FiniteDimensional k (T.X₃.homology p)) (n : ℕ) :
    homologyEulerDefect k T (n + 1) =
      ((-1 : ℤ) ^ n) * connectingRank k T hT n := by
  induction n with
  | zero =>
      rw [homologyEulerDefect_succ, homologyEuler_point_zero k T hT
        (hfin₁ 0) (hfin₂ 0)]
      simp [homologyEulerDefect, homologyBoundedEuler]
  | succ n ih =>
      rw [homologyEulerDefect_succ, ih,
        homologyEuler_point_succ k T hT n (hfin₁ (n + 1)) (hfin₂ (n + 1))
          (hfin₃ (n + 1))]
      rw [pow_succ]
      ring

theorem shortExact_homologyEuler_of_topConnecting_zero
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact)
    (hfin₁ : ∀ p, FiniteDimensional k (T.X₁.homology p))
    (hfin₂ : ∀ p, FiniteDimensional k (T.X₂.homology p))
    (hfin₃ : ∀ p, FiniteDimensional k (T.X₃.homology p)) (n : ℕ)
    (htop : connectingRank k T hT n = 0) :
    homologyBoundedEuler k T.X₂ (n + 1) =
      homologyBoundedEuler k T.X₁ (n + 1) + homologyBoundedEuler k T.X₃ (n + 1) := by
  have h := homologyEulerDefect_eq_connectingRank k T hT hfin₁ hfin₂ hfin₃ n
  rw [htop] at h
  norm_num at h
  unfold homologyEulerDefect at h
  omega

theorem no_simplex_above_card (s : Simplex ι (Fintype.card ι + 1)) : False := by
  have hle := s.1.card_le_univ
  omega

theorem chains_subsingleton_above_card (C : Coeff k ι E) :
    Subsingleton (Chains k ι E C (Fintype.card ι + 1)) := by
  constructor
  intro x y
  apply Subtype.ext
  apply (DirectSum.linearEquivFunOnFintype k
    (Simplex ι (Fintype.card ι + 1)) (fun _ => E)).injective
  funext s
  exact (no_simplex_above_card ι s).elim

theorem coefficientComplex_isZero_above_card (C : Coeff k ι E) :
    IsZero ((coefficientComplex k ι E C).X (Fintype.card ι + 1)) := by
  change IsZero (ModuleCat.of k (Chains k ι E C (Fintype.card ι + 1)))
  letI : Subsingleton (Chains k ι E C (Fintype.card ι + 1)) :=
    chains_subsingleton_above_card k ι E C
  exact ModuleCat.isZero_of_subsingleton _

theorem coefficientComplex_homology_isZero_above_card (C : Coeff k ι E) :
    IsZero ((coefficientComplex k ι E C).homology (Fintype.card ι + 1)) :=
  ShortComplex.isZero_homology_of_isZero_X₂
    ((coefficientComplex k ι E C).sc (Fintype.card ι + 1))
    (coefficientComplex_isZero_above_card k ι E C)

theorem connectingRank_eq_zero_of_isZero_source
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact) (p : ℕ)
    (hzero : IsZero (T.X₃.homology (p + 1))) : connectingRank k T hT p = 0 := by
  have hδ : hT.δ (p + 1) p (by simp) = 0 := hzero.eq_of_src _ _
  have hδhom := congrArg ModuleCat.Hom.hom hδ
  change Module.finrank k
    (LinearMap.range (hT.δ (p + 1) p (by simp)).hom) = 0
  rw [hδhom]
  rw [ModuleCat.hom_zero, LinearMap.range_zero, finrank_bot]

theorem finiteDimensional_homology_of_finite
    (K : ChainComplex (ModuleCat k) ℕ) (p : ℕ) [FiniteDimensional k (K.X p)] :
    FiniteDimensional k (K.homology p) := by
  let S := K.sc p
  letI : FiniteDimensional k S.X₂ := by
    change FiniteDimensional k (K.X p)
    infer_instance
  letI : FiniteDimensional k S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional k
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact FiniteDimensional.of_injective S.moduleCatHomologyIso.hom.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

theorem serialErasure_topConnecting_zero
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    connectingRank k (serialErasureShortComplex k ι E V Z W L M)
      (serialErasure_shortExact k ι E V Z W L M) (Fintype.card ι) = 0 := by
  apply connectingRank_eq_zero_of_isZero_source
  change IsZero
    ((coefficientComplex k ι Z (compositeCoeff k ι E V Z W L M)).homology
      (Fintype.card ι + 1))
  exact coefficientComplex_homology_isZero_above_card k ι Z _

theorem serialRetention_topObject_isZero
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    IsZero ((serialRetentionShortComplex k ι E V Z W L M).X₃.X
      (Fintype.card ι + 1)) := by
  let T := serialRetentionShortComplex k ι E V Z W L M
  letI : Epi (T.g.f (Fintype.card ι + 1)) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp
      (serialRetention_shortExact k ι E V Z W L M) (Fintype.card ι + 1)).epi_g
  apply IsZero.of_epi (T.g.f (Fintype.card ι + 1))
  change IsZero
    ((coefficientComplex k ι Z (retainedCoeff k ι E V Z W L M)).X
      (Fintype.card ι + 1))
  exact coefficientComplex_isZero_above_card k ι Z _

theorem serialRetention_topConnecting_zero
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    connectingRank k (serialRetentionShortComplex k ι E V Z W L M)
      (serialRetention_shortExact k ι E V Z W L M) (Fintype.card ι) = 0 := by
  apply connectingRank_eq_zero_of_isZero_source
  exact ShortComplex.isZero_homology_of_isZero_X₂
    ((serialRetentionShortComplex k ι E V Z W L M).X₃.sc (Fintype.card ι + 1))
    (serialRetention_topObject_isZero k ι E V Z W L M)

theorem serialErasure_homologyEuler [FiniteDimensional k E] [FiniteDimensional k Z]
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    homologyBoundedEuler k (serialErasureShortComplex k ι E V Z W L M).X₂
        (Fintype.card ι + 1) =
      homologyBoundedEuler k (serialErasureShortComplex k ι E V Z W L M).X₁
          (Fintype.card ι + 1) +
        homologyBoundedEuler k (serialErasureShortComplex k ι E V Z W L M).X₃
          (Fintype.card ι + 1) := by
  apply shortExact_homologyEuler_of_topConnecting_zero k _
    (serialErasure_shortExact k ι E V Z W L M)
    (fun p => by
      letI : FiniteDimensional k
          ((serialErasureShortComplex k ι E V Z W L M).X₁.X p) := by
        change FiniteDimensional k
          (Chains k ι E (kernelCoeff k ι Z E (upstreamCoeff k ι E V W L) M) p)
        infer_instance
      exact finiteDimensional_homology_of_finite k _ p)
    (fun p => by
      letI : FiniteDimensional k
          ((serialErasureShortComplex k ι E V Z W L M).X₂.X p) := by
        change FiniteDimensional k (Chains k ι E (upstreamCoeff k ι E V W L) p)
        infer_instance
      exact finiteDimensional_homology_of_finite k _ p)
    (fun p => by
      letI : FiniteDimensional k
          ((serialErasureShortComplex k ι E V Z W L M).X₃.X p) := by
        change FiniteDimensional k (Chains k ι Z (compositeCoeff k ι E V Z W L M) p)
        infer_instance
      exact finiteDimensional_homology_of_finite k _ p)
    (Fintype.card ι)
  exact serialErasure_topConnecting_zero k ι E V Z W L M

theorem serialRetention_homologyEuler [FiniteDimensional k Z]
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) :
    homologyBoundedEuler k (serialRetentionShortComplex k ι E V Z W L M).X₂
        (Fintype.card ι + 1) =
      homologyBoundedEuler k (serialRetentionShortComplex k ι E V Z W L M).X₁
          (Fintype.card ι + 1) +
        homologyBoundedEuler k (serialRetentionShortComplex k ι E V Z W L M).X₃
          (Fintype.card ι + 1) := by
  let T := serialRetentionShortComplex k ι E V Z W L M
  apply shortExact_homologyEuler_of_topConnecting_zero k T
    (serialRetention_shortExact k ι E V Z W L M)
    (fun p => by
      letI : FiniteDimensional k (T.X₁.X p) := by
        change FiniteDimensional k
          (Chains k ι Z (compositeCoeff k ι E V Z W L M) p)
        infer_instance
      exact finiteDimensional_homology_of_finite k T.X₁ p)
    (fun p => by
      letI : FiniteDimensional k (T.X₂.X p) := by
        change FiniteDimensional k
          (Chains k ι Z (retainedCoeff k ι E V Z W L M) p)
        infer_instance
      exact finiteDimensional_homology_of_finite k T.X₂ p)
    (fun p => by
      have hp := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp
        (serialRetention_shortExact k ι E V Z W L M) p
      letI : FiniteDimensional k (T.X₂.X p) := by
        change FiniteDimensional k
          (Chains k ι Z (retainedCoeff k ι E V Z W L M) p)
        infer_instance
      letI : FiniteDimensional k (T.X₃.X p) :=
        FiniteDimensional.of_surjective (T.g.f p).hom hp.moduleCat_surjective_g
      exact finiteDimensional_homology_of_finite k T.X₃ p)
    (Fintype.card ι)
  exact serialRetention_topConnecting_zero k ι E V Z W L M

theorem finrank_of_shortExact_linear
    {A B D : Type uE} [AddCommGroup A] [Module k A] [FiniteDimensional k A]
    [AddCommGroup B] [Module k B] [FiniteDimensional k B]
    [AddCommGroup D] [Module k D] [FiniteDimensional k D]
    (f : A →ₗ[k] B) (g : B →ₗ[k] D)
    (hexact : LinearMap.range f = LinearMap.ker g)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) :
    Module.finrank k B = Module.finrank k A + Module.finrank k D := by
  have hrank := LinearMap.finrank_range_add_finrank_ker g
  calc
    Module.finrank k B =
        Module.finrank k (LinearMap.range g) + Module.finrank k (LinearMap.ker g) :=
      hrank.symm
    _ = Module.finrank k D + Module.finrank k A := by
      rw [LinearMap.range_eq_top.mpr hsurj, ← hexact,
        LinearMap.finrank_range_of_inj hinj]
      simp
    _ = Module.finrank k A + Module.finrank k D := Nat.add_comm _ _

theorem observerErasure_degree_finrank [FiniteDimensional k V] [FiniteDimensional k E]
    (C : Coeff k ι V) (f : V →ₗ[k] E) (p : ℕ) :
    Module.finrank k (Chains k ι V C p) =
      Module.finrank k (Chains k ι V (kernelCoeff k ι E V C f) p) +
        Module.finrank k (Chains k ι E (imageCoeff k ι E V C f) p) := by
  exact finrank_of_shortExact_linear k
    (coeffMap k ι V (kernelCoeff k ι E V C f) V C
      (coefficientInclusion k ι V (kernelCoeffLE k ι E V C f)) (p := p))
    (coeffMap k ι V C E (imageCoeff k ι E V C f)
      (imageCoeffMorphism k ι E V C f) (p := p))
    (kernel_image_chain_exact k ι E V C f p)
    (coefficientInclusion_injective k ι V (kernelCoeffLE k ι E V C f))
    (imageCoeffMap_surjective k ι E V C f p)

noncomputable def boundedEuler (K : ChainComplex (ModuleCat k) ℕ) (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.range n, ((-1 : ℤ) ^ p) * Module.finrank k (K.X p)

theorem boundedEuler_add_of_degree_finrank
    (K₁ K₂ K₃ : ChainComplex (ModuleCat k) ℕ) (n : ℕ)
    (h : ∀ p < n, Module.finrank k (K₂.X p) =
      Module.finrank k (K₁.X p) + Module.finrank k (K₃.X p)) :
    boundedEuler k K₂ n = boundedEuler k K₁ n + boundedEuler k K₃ n := by
  simp only [boundedEuler, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [h p (Finset.mem_range.mp hp)]
  push_cast
  ring

theorem observerErasure_euler [FiniteDimensional k V] [FiniteDimensional k E]
    (C : Coeff k ι V) (f : V →ₗ[k] E) (n : ℕ) :
    boundedEuler k (coefficientComplex k ι V C) n =
      boundedEuler k (coefficientComplex k ι V (kernelCoeff k ι E V C f)) n +
        boundedEuler k (coefficientComplex k ι E (imageCoeff k ι E V C f)) n := by
  apply boundedEuler_add_of_degree_finrank
  intro p _
  exact observerErasure_degree_finrank k ι E V C f p

theorem chainShortExact_degree_finrank
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact) (p : ℕ)
    [FiniteDimensional k (T.X₁.X p)] [FiniteDimensional k (T.X₂.X p)]
    [FiniteDimensional k (T.X₃.X p)] :
    Module.finrank k (T.X₂.X p) =
      Module.finrank k (T.X₁.X p) + Module.finrank k (T.X₃.X p) := by
  have hp := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp hT p
  exact finrank_of_shortExact_linear k
    (T.f.f p).hom (T.g.f p).hom hp.exact.moduleCat_range_eq_ker
    hp.moduleCat_injective_f hp.moduleCat_surjective_g

theorem shortExact_boundedEuler
    (T : ShortComplex (ChainComplex (ModuleCat k) ℕ)) (hT : T.ShortExact) (n : ℕ)
    (hfin₁ : ∀ p, FiniteDimensional k (T.X₁.X p))
    (hfin₂ : ∀ p, FiniteDimensional k (T.X₂.X p))
    (hfin₃ : ∀ p, FiniteDimensional k (T.X₃.X p)) :
    boundedEuler k T.X₂ n = boundedEuler k T.X₁ n + boundedEuler k T.X₃ n := by
  apply boundedEuler_add_of_degree_finrank
  intro p _
  letI := hfin₁ p
  letI := hfin₂ p
  letI := hfin₃ p
  exact chainShortExact_degree_finrank k T hT p

theorem serialErasure_euler [FiniteDimensional k E] [FiniteDimensional k Z]
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) (n : ℕ) :
    boundedEuler k (serialErasureShortComplex k ι E V Z W L M).X₂ n =
      boundedEuler k (serialErasureShortComplex k ι E V Z W L M).X₁ n +
        boundedEuler k (serialErasureShortComplex k ι E V Z W L M).X₃ n :=
  observerErasure_euler k ι Z E (upstreamCoeff k ι E V W L) M n

theorem serialRetention_euler [FiniteDimensional k Z]
    (W : ι → Submodule k V) (L : V →ₗ[k] E) (M : E →ₗ[k] Z) (n : ℕ) :
    boundedEuler k (serialRetentionShortComplex k ι E V Z W L M).X₂ n =
      boundedEuler k (serialRetentionShortComplex k ι E V Z W L M).X₁ n +
        boundedEuler k (serialRetentionShortComplex k ι E V Z W L M).X₃ n :=
  shortExact_boundedEuler k _ (serialRetention_shortExact k ι E V Z W L M) n
    (fun p => by
      change FiniteDimensional k
        (Chains k ι Z (compositeCoeff k ι E V Z W L M) p)
      infer_instance)
    (fun p => by
      change FiniteDimensional k
        (Chains k ι Z (retainedCoeff k ι E V Z W L M) p)
      infer_instance)
    (fun p => by
      let T := serialRetentionShortComplex k ι E V Z W L M
      have hp := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp
        (serialRetention_shortExact k ι E V Z W L M) p
      letI : FiniteDimensional k (T.X₂.X p) := by
        change FiniteDimensional k
          (Chains k ι Z (retainedCoeff k ι E V Z W L M) p)
        infer_instance
      exact FiniteDimensional.of_surjective (T.g.f p).hom hp.moduleCat_surjective_g)

section PositiveHodge

open scoped InnerProductSpace

variable {𝕜 : Type uR} [RCLike 𝕜]
variable {A B D : Type uE}
  [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [FiniteDimensional 𝕜 A]
  [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [FiniteDimensional 𝕜 B]
  [NormedAddCommGroup D] [InnerProductSpace 𝕜 D] [FiniteDimensional 𝕜 D]

noncomputable def positiveHodgeRealization
    (d₂ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] D)
    (h : LinearMap.range d₂ ≤ LinearMap.ker d₁) :
    ↥(LinearMap.ker (GaloisForLFunctions.HTGeometry.hodgeLaplacian d₂ d₁))
      ≃ₗ[𝕜] (↥(LinearMap.ker d₁) ⧸
        Submodule.comap (LinearMap.ker d₁).subtype (LinearMap.range d₂)) :=
  GaloisForLFunctions.HTGeometry.harmonicEquivHomology d₂ d₁ h

theorem positiveHodge_finrank
    (d₂ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] D)
    (h : LinearMap.range d₂ ≤ LinearMap.ker d₁) :
    Module.finrank 𝕜
        ↥(LinearMap.ker (GaloisForLFunctions.HTGeometry.hodgeLaplacian d₂ d₁)) =
      Module.finrank 𝕜 (↥(LinearMap.ker d₁) ⧸
        Submodule.comap (LinearMap.ker d₁).subtype (LinearMap.range d₂)) :=
  (positiveHodgeRealization d₂ d₁ h).finrank_eq

theorem positiveHodge_zeroRank_iff
    (d₂ : A →ₗ[𝕜] B) (d₁ : B →ₗ[𝕜] D)
    (h : LinearMap.range d₂ ≤ LinearMap.ker d₁) :
    Module.finrank 𝕜
        ↥(LinearMap.ker (GaloisForLFunctions.HTGeometry.hodgeLaplacian d₂ d₁)) = 0 ↔
      Module.finrank 𝕜 (↥(LinearMap.ker d₁) ⧸
        Submodule.comap (LinearMap.ker d₁).subtype (LinearMap.range d₂)) = 0 := by
  rw [positiveHodge_finrank d₂ d₁ h]

end PositiveHodge

end HigherAritySerialObserverFormation
