import GaloisForLFunctions.HTGeometry.ShilovEnvelopeCorrelationLaw

/-!
# Envelope correlations: pullback presentation and vertical extension

For a linear map `f : V →ₗ[𝕜] W` and boundary submodules `Js ≤ V`, `Jt ≤ W`, the *envelope
correlation* is the image of

`a ↦ (a + Js, f a + Jt) : V →ₗ[𝕜] (V ⧸ Js) × (W ⧸ Jt)`.

This module proves that this subdirect object is exactly the fibre product of the two envelopes
over the edge join `M = Jt ⊔ f(Js)`, that the two quotients of the edge join by its two generators
are the escape and deficit defects, and that the two vertical kernels of the correlation are the
escape defect and an extension of the deficit defect by the image of `ker f`.

Main results:

* `envelopeCorrelation_eq_correlationPullback`: the correlation is the fibre product
  `(V ⧸ Js) ×_{W ⧸ M} (W ⧸ Jt)`;
* `escapeEdgeQuotientEquiv`, `deficitEdgeQuotientEquiv`: the two edge-join quotients are the
  escape and deficit defects;
* `correlationSourceKernelEquivEscape`: the fibre over the zero source class is the escape defect;
* `correlationTargetKernelEquiv`, `ker_correlationDeficitMap`,
  `correlationDeficitMap_surjective`, `correlationVerticalTarget_exact`: the fibre over the zero
  target class is an extension of the deficit defect by the image of `ker f`;
* `exists_entrywise_correlation_lift_target`: every finite matrix over either envelope admits an
  entrywise correlation coupling.
-/

open Function

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {V W : Type v}
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

section Correlation

variable (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt : Submodule 𝕜 W)

/-- The canonical map `a ↦ (a + Js, f a + Jt)` into the product of the two envelopes. -/
def correlationMap : V →ₗ[𝕜] (V ⧸ Js) × (W ⧸ Jt) :=
  (Js.mkQ).prod (Jt.mkQ ∘ₗ f)

@[simp] theorem correlationMap_apply (a : V) :
    correlationMap f Js Jt a =
      ((Submodule.Quotient.mk a : V ⧸ Js), (Submodule.Quotient.mk (f a) : W ⧸ Jt)) :=
  rfl

/-- The envelope correlation attached to `f` and the two boundary submodules. -/
def envelopeCorrelation : Submodule 𝕜 ((V ⧸ Js) × (W ⧸ Jt)) :=
  LinearMap.range (correlationMap f Js Jt)

theorem mem_envelopeCorrelation_iff (p : (V ⧸ Js) × (W ⧸ Jt)) :
    p ∈ envelopeCorrelation f Js Jt ↔
      ∃ a : V,
        ((Submodule.Quotient.mk a : V ⧸ Js), (Submodule.Quotient.mk (f a) : W ⧸ Jt)) = p :=
  Iff.rfl

theorem correlationMap_mem (a : V) :
    correlationMap f Js Jt a ∈ envelopeCorrelation f Js Jt :=
  ⟨a, rfl⟩

/-- The kernel of the correlation map is `Js ∩ f⁻¹(Jt)`. -/
theorem ker_correlationMap :
    LinearMap.ker (correlationMap f Js Jt) = Js ⊓ Jt.comap f := by
  ext a
  constructor
  · intro ha
    have ha' : correlationMap f Js Jt a = 0 := ha
    rw [correlationMap_apply, Prod.ext_iff] at ha'
    refine ⟨?_, ?_⟩
    · exact (Submodule.Quotient.mk_eq_zero Js).mp ha'.1
    · exact Submodule.mem_comap.mpr ((Submodule.Quotient.mk_eq_zero Jt).mp ha'.2)
  · rintro ⟨h1, h2⟩
    show correlationMap f Js Jt a = 0
    rw [correlationMap_apply, Prod.ext_iff]
    exact ⟨(Submodule.Quotient.mk_eq_zero Js).mpr h1,
      (Submodule.Quotient.mk_eq_zero Jt).mpr (Submodule.mem_comap.mp h2)⟩

theorem source_le_comap_edgeJoin :
    Js ≤ Submodule.comap f (edgeJoin f Js Jt) := by
  rw [← Submodule.map_le_iff_le_comap]
  exact transported_le_edgeJoin f Js Jt

/-- Transport of the source envelope into the edge quotient. -/
def edgeProjSource : (V ⧸ Js) →ₗ[𝕜] W ⧸ edgeJoin f Js Jt :=
  Js.mapQ (edgeJoin f Js Jt) f (source_le_comap_edgeJoin f Js Jt)

/-- Projection of the target envelope onto the edge quotient. -/
def edgeProjTarget : (W ⧸ Jt) →ₗ[𝕜] W ⧸ edgeJoin f Js Jt :=
  Jt.mapQ (edgeJoin f Js Jt) LinearMap.id (fun _ hx =>
    Submodule.mem_comap.mpr (target_le_edgeJoin f Js Jt hx))

@[simp] theorem edgeProjSource_mk (a : V) :
    edgeProjSource f Js Jt (Submodule.Quotient.mk a) =
      (Submodule.Quotient.mk (f a) : W ⧸ edgeJoin f Js Jt) :=
  rfl

@[simp] theorem edgeProjTarget_mk (b : W) :
    edgeProjTarget f Js Jt (Submodule.Quotient.mk b) =
      (Submodule.Quotient.mk b : W ⧸ edgeJoin f Js Jt) :=
  rfl

theorem edgeProjSource_surjective (hf : Function.Surjective f) :
    Function.Surjective (edgeProjSource f Js Jt) := by
  intro z
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (edgeJoin f Js Jt) z
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Submodule.Quotient.mk a, hb⟩

theorem edgeProjTarget_surjective :
    Function.Surjective (edgeProjTarget f Js Jt) := by
  intro z
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (edgeJoin f Js Jt) z
  exact ⟨Submodule.Quotient.mk b, hb⟩

/-- The fibre product of the two envelopes over the edge quotient. -/
def correlationPullback : Submodule 𝕜 ((V ⧸ Js) × (W ⧸ Jt)) :=
  LinearMap.ker (edgeProjSource f Js Jt ∘ₗ LinearMap.fst 𝕜 (V ⧸ Js) (W ⧸ Jt)
    - edgeProjTarget f Js Jt ∘ₗ LinearMap.snd 𝕜 (V ⧸ Js) (W ⧸ Jt))

theorem mem_correlationPullback_iff (p : (V ⧸ Js) × (W ⧸ Jt)) :
    p ∈ correlationPullback f Js Jt ↔
      edgeProjSource f Js Jt p.1 = edgeProjTarget f Js Jt p.2 := by
  constructor
  · intro hp
    have hp' : (edgeProjSource f Js Jt ∘ₗ LinearMap.fst 𝕜 (V ⧸ Js) (W ⧸ Jt)
        - edgeProjTarget f Js Jt ∘ₗ LinearMap.snd 𝕜 (V ⧸ Js) (W ⧸ Jt)) p = 0 := hp
    rw [LinearMap.sub_apply] at hp'
    exact sub_eq_zero.mp hp'
  · intro hp
    show (edgeProjSource f Js Jt ∘ₗ LinearMap.fst 𝕜 (V ⧸ Js) (W ⧸ Jt)
        - edgeProjTarget f Js Jt ∘ₗ LinearMap.snd 𝕜 (V ⧸ Js) (W ⧸ Jt)) p = 0
    rw [LinearMap.sub_apply]
    exact sub_eq_zero.mpr hp

/-- The envelope correlation is exactly the fibre product of the two envelopes over the edge
quotient.  This is the pullback presentation of the correlation. -/
theorem envelopeCorrelation_eq_correlationPullback :
    envelopeCorrelation f Js Jt = correlationPullback f Js Jt := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    rw [mem_correlationPullback_iff]
    rfl
  · intro p hp
    rw [mem_correlationPullback_iff] at hp
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective Js p.1
    obtain ⟨b, hb⟩ := Submodule.mkQ_surjective Jt p.2
    have ha' : (Submodule.Quotient.mk a : V ⧸ Js) = p.1 := ha
    have hb' : (Submodule.Quotient.mk b : W ⧸ Jt) = p.2 := hb
    rw [← ha', ← hb', edgeProjSource_mk, edgeProjTarget_mk, Submodule.Quotient.eq] at hp
    obtain ⟨t, ht, w, hw, hsum⟩ := Submodule.mem_sup.mp hp
    obtain ⟨s, hs, hfs⟩ := Submodule.mem_map.mp hw
    refine ⟨a - s, ?_⟩
    have hfst : (Submodule.Quotient.mk (a - s) : V ⧸ Js) = p.1 := by
      rw [← ha', Submodule.Quotient.eq]
      simpa using Js.neg_mem hs
    have hsnd : (Submodule.Quotient.mk (f (a - s)) : W ⧸ Jt) = p.2 := by
      rw [← hb', Submodule.Quotient.eq, map_sub, hfs]
      have hregroup : f a - w - b = f a - b - w := by abel
      have hval : f a - w - b = t := by
        rw [hregroup, ← hsum]; abel
      rw [hval]
      exact ht
    exact Prod.ext hfst hsnd

/-- The edge join is the least submodule of the target containing the target boundary through
which the source envelope factors. -/
theorem edgeJoin_least (N : Submodule 𝕜 W) (h₁ : Jt ≤ N)
    (h₂ : Js ≤ Submodule.comap f N) :
    edgeJoin f Js Jt ≤ N :=
  sup_le h₁ (Submodule.map_le_iff_le_comap.mpr h₂)

end Correlation

section EdgeQuotients

variable (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt : Submodule 𝕜 W)

/-- Transported source boundary inside the edge join, modulo the target boundary. -/
def escapeToEdgeQuotient :
    (Js.map f) →ₗ[𝕜] RelativeQuotient Jt (edgeJoin f Js Jt) :=
  (Jt.comap (edgeJoin f Js Jt).subtype).mkQ ∘ₗ
    Submodule.inclusion (transported_le_edgeJoin f Js Jt)

theorem escapeToEdgeQuotient_surjective :
    Function.Surjective (escapeToEdgeQuotient f Js Jt) := by
  intro z
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (Jt.comap (edgeJoin f Js Jt).subtype) z
  obtain ⟨t, ht, w, hw, hsum⟩ := Submodule.mem_sup.mp m.2
  refine ⟨⟨w, hw⟩, ?_⟩
  have hm' : (Submodule.Quotient.mk m : RelativeQuotient Jt (edgeJoin f Js Jt)) = z := hm
  rw [← hm']
  show (Submodule.Quotient.mk (⟨w, transported_le_edgeJoin f Js Jt hw⟩ :
      (edgeJoin f Js Jt)) : RelativeQuotient Jt (edgeJoin f Js Jt)) = _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  show (w : W) - (m : W) ∈ Jt
  have : (w : W) - (m : W) = -t := by rw [← hsum]; abel
  rw [this]
  exact Jt.neg_mem ht

theorem ker_escapeToEdgeQuotient :
    LinearMap.ker (escapeToEdgeQuotient f Js Jt) = Jt.comap (Js.map f).subtype := by
  ext w
  constructor
  · intro hw
    have hw' : escapeToEdgeQuotient f Js Jt w = 0 := hw
    rw [escapeToEdgeQuotient] at hw'
    have := (Submodule.Quotient.mk_eq_zero (Jt.comap (edgeJoin f Js Jt).subtype)).mp hw'
    exact Submodule.mem_comap.mpr (Submodule.mem_comap.mp this)
  · intro hw
    show escapeToEdgeQuotient f Js Jt w = 0
    rw [escapeToEdgeQuotient]
    refine (Submodule.Quotient.mk_eq_zero (Jt.comap (edgeJoin f Js Jt).subtype)).mpr ?_
    exact Submodule.mem_comap.mpr (Submodule.mem_comap.mp hw)

/-- The edge join modulo the target boundary is the escape defect. -/
noncomputable def escapeEdgeQuotientEquiv :
    EscapeDefect f Js Jt ≃ₗ[𝕜] RelativeQuotient Jt (edgeJoin f Js Jt) :=
  (Submodule.quotEquivOfEq _ _ (ker_escapeToEdgeQuotient f Js Jt).symm).trans
    ((escapeToEdgeQuotient f Js Jt).quotKerEquivOfSurjective
      (escapeToEdgeQuotient_surjective f Js Jt))

/-- Target boundary inside the edge join, modulo the transported source boundary. -/
def deficitToEdgeQuotient :
    Jt →ₗ[𝕜] RelativeQuotient (Js.map f) (edgeJoin f Js Jt) :=
  ((Js.map f).comap (edgeJoin f Js Jt).subtype).mkQ ∘ₗ
    Submodule.inclusion (target_le_edgeJoin f Js Jt)

theorem deficitToEdgeQuotient_surjective :
    Function.Surjective (deficitToEdgeQuotient f Js Jt) := by
  intro z
  obtain ⟨m, hm⟩ := Submodule.mkQ_surjective ((Js.map f).comap (edgeJoin f Js Jt).subtype) z
  obtain ⟨t, ht, w, hw, hsum⟩ := Submodule.mem_sup.mp m.2
  refine ⟨⟨t, ht⟩, ?_⟩
  have hm' : (Submodule.Quotient.mk m :
      RelativeQuotient (Js.map f) (edgeJoin f Js Jt)) = z := hm
  rw [← hm']
  show (Submodule.Quotient.mk (⟨t, target_le_edgeJoin f Js Jt ht⟩ :
      (edgeJoin f Js Jt)) : RelativeQuotient (Js.map f) (edgeJoin f Js Jt)) = _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  show (t : W) - (m : W) ∈ Js.map f
  have : (t : W) - (m : W) = -w := by rw [← hsum]; abel
  rw [this]
  exact (Js.map f).neg_mem hw

theorem ker_deficitToEdgeQuotient :
    LinearMap.ker (deficitToEdgeQuotient f Js Jt) = (Js.map f).comap Jt.subtype := by
  ext t
  constructor
  · intro ht
    have ht' : deficitToEdgeQuotient f Js Jt t = 0 := ht
    rw [deficitToEdgeQuotient] at ht'
    have := (Submodule.Quotient.mk_eq_zero
      ((Js.map f).comap (edgeJoin f Js Jt).subtype)).mp ht'
    exact Submodule.mem_comap.mpr (Submodule.mem_comap.mp this)
  · intro ht
    show deficitToEdgeQuotient f Js Jt t = 0
    rw [deficitToEdgeQuotient]
    refine (Submodule.Quotient.mk_eq_zero
      ((Js.map f).comap (edgeJoin f Js Jt).subtype)).mpr ?_
    exact Submodule.mem_comap.mpr (Submodule.mem_comap.mp ht)

/-- The edge join modulo the transported source boundary is the deficit defect. -/
noncomputable def deficitEdgeQuotientEquiv :
    DeficitDefect f Js Jt ≃ₗ[𝕜] RelativeQuotient (Js.map f) (edgeJoin f Js Jt) :=
  (Submodule.quotEquivOfEq _ _ (ker_deficitToEdgeQuotient f Js Jt).symm).trans
    ((deficitToEdgeQuotient f Js Jt).quotKerEquivOfSurjective
      (deficitToEdgeQuotient_surjective f Js Jt))

end EdgeQuotients

section VerticalKernels

variable (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt : Submodule 𝕜 W)

/-- Part of the correlation lying over the zero source class. -/
def correlationSourceKernel : Submodule 𝕜 ((V ⧸ Js) × (W ⧸ Jt)) :=
  envelopeCorrelation f Js Jt ⊓ LinearMap.ker (LinearMap.fst 𝕜 (V ⧸ Js) (W ⧸ Jt))

/-- Part of the correlation lying over the zero target class. -/
def correlationTargetKernel : Submodule 𝕜 ((V ⧸ Js) × (W ⧸ Jt)) :=
  envelopeCorrelation f Js Jt ⊓ LinearMap.ker (LinearMap.snd 𝕜 (V ⧸ Js) (W ⧸ Jt))

theorem mem_correlationSourceKernel_iff (p : (V ⧸ Js) × (W ⧸ Jt)) :
    p ∈ correlationSourceKernel f Js Jt ↔
      p ∈ envelopeCorrelation f Js Jt ∧ p.1 = 0 :=
  Iff.rfl

theorem mem_correlationTargetKernel_iff (p : (V ⧸ Js) × (W ⧸ Jt)) :
    p ∈ correlationTargetKernel f Js Jt ↔
      p ∈ envelopeCorrelation f Js Jt ∧ p.2 = 0 :=
  Iff.rfl

/-- The edge join sits over the zero source class. -/
def edgeJoinToProduct : (edgeJoin f Js Jt) →ₗ[𝕜] (V ⧸ Js) × (W ⧸ Jt) :=
  (0 : (edgeJoin f Js Jt) →ₗ[𝕜] V ⧸ Js).prod (Jt.mkQ ∘ₗ (edgeJoin f Js Jt).subtype)

theorem range_edgeJoinToProduct :
    LinearMap.range (edgeJoinToProduct f Js Jt) = correlationSourceKernel f Js Jt := by
  apply le_antisymm
  · rintro p ⟨m, rfl⟩
    rw [mem_correlationSourceKernel_iff]
    refine ⟨?_, rfl⟩
    rw [envelopeCorrelation_eq_correlationPullback, mem_correlationPullback_iff]
    show edgeProjSource f Js Jt 0 = edgeProjTarget f Js Jt (Submodule.Quotient.mk (m : W))
    rw [map_zero, edgeProjTarget_mk]
    exact ((Submodule.Quotient.mk_eq_zero (edgeJoin f Js Jt)).mpr m.2).symm
  · intro p hp
    rw [mem_correlationSourceKernel_iff] at hp
    obtain ⟨hp₁, hfst⟩ := hp
    rw [envelopeCorrelation_eq_correlationPullback, mem_correlationPullback_iff, hfst,
      map_zero] at hp₁
    obtain ⟨b, hb⟩ := Submodule.mkQ_surjective Jt p.2
    have hb' : (Submodule.Quotient.mk b : W ⧸ Jt) = p.2 := hb
    rw [← hb', edgeProjTarget_mk] at hp₁
    have hbm : b ∈ edgeJoin f Js Jt :=
      (Submodule.Quotient.mk_eq_zero (edgeJoin f Js Jt)).mp hp₁.symm
    exact ⟨⟨b, hbm⟩, Prod.ext hfst.symm hb'⟩

theorem ker_edgeJoinToProduct :
    LinearMap.ker (edgeJoinToProduct f Js Jt) = Jt.comap (edgeJoin f Js Jt).subtype := by
  ext m
  constructor
  · intro hm
    have hm' : edgeJoinToProduct f Js Jt m = 0 := hm
    have : (Submodule.Quotient.mk (m : W) : W ⧸ Jt) = 0 := congrArg Prod.snd hm'
    exact Submodule.mem_comap.mpr ((Submodule.Quotient.mk_eq_zero Jt).mp this)
  · intro hm
    show edgeJoinToProduct f Js Jt m = 0
    refine Prod.ext rfl ?_
    show (Submodule.Quotient.mk (m : W) : W ⧸ Jt) = 0
    exact (Submodule.Quotient.mk_eq_zero Jt).mpr (Submodule.mem_comap.mp hm)

/-- The correlation fibre over the zero source class is the escape defect. -/
noncomputable def correlationSourceKernelEquivEscape :
    EscapeDefect f Js Jt ≃ₗ[𝕜] correlationSourceKernel f Js Jt :=
  (escapeEdgeQuotientEquiv f Js Jt).trans
    ((Submodule.quotEquivOfEq _ _ (ker_edgeJoinToProduct f Js Jt).symm).trans
      (((edgeJoinToProduct f Js Jt).quotKerEquivRange).trans
        (LinearEquiv.ofEq _ _ (range_edgeJoinToProduct f Js Jt))))

/-- The source lift domain sits over the zero target class. -/
def preimageToProduct : (Jt.comap f) →ₗ[𝕜] (V ⧸ Js) × (W ⧸ Jt) :=
  (Js.mkQ ∘ₗ (Jt.comap f).subtype).prod 0

theorem range_preimageToProduct :
    LinearMap.range (preimageToProduct f Js Jt) = correlationTargetKernel f Js Jt := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    rw [mem_correlationTargetKernel_iff]
    refine ⟨⟨(a : V), ?_⟩, rfl⟩
    refine Prod.ext rfl ?_
    show (Submodule.Quotient.mk (f (a : V)) : W ⧸ Jt) = 0
    exact (Submodule.Quotient.mk_eq_zero Jt).mpr (Submodule.mem_comap.mp a.2)
  · intro p hp
    rw [mem_correlationTargetKernel_iff] at hp
    obtain ⟨⟨a, ha⟩, hsnd⟩ := hp
    have ha1 : (Submodule.Quotient.mk a : V ⧸ Js) = p.1 := congrArg Prod.fst ha
    have ha2 : (Submodule.Quotient.mk (f a) : W ⧸ Jt) = p.2 := congrArg Prod.snd ha
    rw [hsnd] at ha2
    refine ⟨⟨a, Submodule.mem_comap.mpr ((Submodule.Quotient.mk_eq_zero Jt).mp ha2)⟩, ?_⟩
    exact Prod.ext ha1 hsnd.symm

theorem ker_preimageToProduct :
    LinearMap.ker (preimageToProduct f Js Jt) = Js.comap (Jt.comap f).subtype := by
  ext a
  constructor
  · intro ha
    have ha' : preimageToProduct f Js Jt a = 0 := ha
    have : (Submodule.Quotient.mk (a : V) : V ⧸ Js) = 0 := congrArg Prod.fst ha'
    exact Submodule.mem_comap.mpr ((Submodule.Quotient.mk_eq_zero Js).mp this)
  · intro ha
    show preimageToProduct f Js Jt a = 0
    refine Prod.ext ?_ rfl
    show (Submodule.Quotient.mk (a : V) : V ⧸ Js) = 0
    exact (Submodule.Quotient.mk_eq_zero Js).mpr (Submodule.mem_comap.mp ha)

/-- The correlation fibre over the zero target class is `f⁻¹(Jt)` modulo `Js ∩ f⁻¹(Jt)`. -/
noncomputable def correlationTargetKernelEquiv :
    RelativeQuotient Js (Jt.comap f) ≃ₗ[𝕜] correlationTargetKernel f Js Jt :=
  (Submodule.quotEquivOfEq _ _ (ker_preimageToProduct f Js Jt).symm).trans
    (((preimageToProduct f Js Jt).quotKerEquivRange).trans
      (LinearEquiv.ofEq _ _ (range_preimageToProduct f Js Jt)))

end VerticalKernels

section DeficitExtension

variable (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt : Submodule 𝕜 W)

/-- `a ↦ f a` from the source lift domain to the target boundary. -/
def targetLiftRestrict : (Jt.comap f) →ₗ[𝕜] Jt :=
  LinearMap.codRestrict Jt (f.domRestrict (Jt.comap f)) (fun a => Submodule.mem_comap.mp a.2)

@[simp] theorem targetLiftRestrict_coe (a : Jt.comap f) :
    ((targetLiftRestrict f Jt a : Jt) : W) = f (a : V) :=
  rfl

theorem targetLiftRestrict_surjective (hf : Function.Surjective f) :
    Function.Surjective (targetLiftRestrict f Jt) := by
  intro t
  obtain ⟨a, ha⟩ := hf (t : W)
  refine ⟨⟨a, Submodule.mem_comap.mpr (ha ▸ t.2)⟩, ?_⟩
  exact Subtype.ext (by simpa using ha)

/-- The deficit class of a source lift. -/
def targetLiftMap : (Jt.comap f) →ₗ[𝕜] DeficitDefect f Js Jt :=
  ((Js.map f).comap Jt.subtype).mkQ ∘ₗ targetLiftRestrict f Jt

theorem targetLiftMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (targetLiftMap f Js Jt) :=
  (Submodule.mkQ_surjective _).comp (targetLiftRestrict_surjective f Jt hf)

theorem ker_targetLiftMap :
    LinearMap.ker (targetLiftMap f Js Jt) =
      (Js ⊔ LinearMap.ker f).comap (Jt.comap f).subtype := by
  ext a
  constructor
  · intro ha
    have ha' : targetLiftMap f Js Jt a = 0 := ha
    have hmem : targetLiftRestrict f Jt a ∈ (Js.map f).comap Jt.subtype :=
      (Submodule.Quotient.mk_eq_zero _).mp ha'
    have hfa : f (a : V) ∈ Js.map f := Submodule.mem_comap.mp hmem
    obtain ⟨s, hs, hfs⟩ := Submodule.mem_map.mp hfa
    refine Submodule.mem_comap.mpr (Submodule.mem_sup.mpr ⟨s, hs, (a : V) - s, ?_, by abel⟩)
    rw [LinearMap.mem_ker, map_sub, hfs, sub_self]
  · intro ha
    have ha' : (a : V) ∈ Js ⊔ LinearMap.ker f := Submodule.mem_comap.mp ha
    obtain ⟨s, hs, k, hk, hsum⟩ := Submodule.mem_sup.mp ha'
    show targetLiftMap f Js Jt a = 0
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    refine Submodule.mem_comap.mpr ?_
    have : f (a : V) = f s := by
      rw [← hsum, map_add, (LinearMap.mem_ker.mp hk), add_zero]
    show f (a : V) ∈ Js.map f
    rw [this]
    exact Submodule.mem_map_of_mem hs

theorem source_le_ker_targetLiftMap :
    Js.comap (Jt.comap f).subtype ≤ LinearMap.ker (targetLiftMap f Js Jt) := by
  rw [ker_targetLiftMap]
  intro a ha
  exact Submodule.mem_comap.mpr
    ((le_sup_left : Js ≤ Js ⊔ LinearMap.ker f) (Submodule.mem_comap.mp ha))

/-- The deficit map on the correlation fibre over the zero target class. -/
def correlationDeficitMap :
    RelativeQuotient Js (Jt.comap f) →ₗ[𝕜] DeficitDefect f Js Jt :=
  (Js.comap (Jt.comap f).subtype).liftQ (targetLiftMap f Js Jt)
    (source_le_ker_targetLiftMap f Js Jt)

theorem correlationDeficitMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (correlationDeficitMap f Js Jt) := by
  intro d
  obtain ⟨a, ha⟩ := targetLiftMap_surjective f Js Jt hf d
  exact ⟨Submodule.Quotient.mk a, ha⟩

/-- Image of `ker f` inside the correlation fibre over the zero target class. -/
def correlationKernelImage : Submodule 𝕜 (RelativeQuotient Js (Jt.comap f)) :=
  Submodule.map (Js.comap (Jt.comap f).subtype).mkQ
    ((LinearMap.ker f).comap (Jt.comap f).subtype)

/-- The deficit map is killed exactly by the image of `ker f`. -/
theorem ker_correlationDeficitMap :
    LinearMap.ker (correlationDeficitMap f Js Jt) = correlationKernelImage f Js Jt := by
  apply le_antisymm
  · intro y hy
    obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (Js.comap (Jt.comap f).subtype) y
    have ha' : (Submodule.Quotient.mk a : RelativeQuotient Js (Jt.comap f)) = y := ha
    have hmem : a ∈ LinearMap.ker (targetLiftMap f Js Jt) := by
      have : correlationDeficitMap f Js Jt (Submodule.Quotient.mk a) = 0 := by
        rw [ha']; exact hy
      exact this
    rw [ker_targetLiftMap] at hmem
    obtain ⟨s, hs, k, hk, hsum⟩ := Submodule.mem_sup.mp (Submodule.mem_comap.mp hmem)
    have hkmem : k ∈ Jt.comap f :=
      Submodule.mem_comap.mpr (by rw [LinearMap.mem_ker.mp hk]; exact Jt.zero_mem)
    refine ⟨⟨k, hkmem⟩, Submodule.mem_comap.mpr hk, ?_⟩
    rw [← ha']
    show (Submodule.Quotient.mk (⟨k, hkmem⟩ : Jt.comap f) :
      RelativeQuotient Js (Jt.comap f)) = Submodule.Quotient.mk a
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_comap.mpr ?_
    show k - (a : V) ∈ Js
    have hsum' : s + k = (a : V) := hsum
    have hval : k - (a : V) = -s := by rw [← hsum']; abel
    rw [hval]
    exact Js.neg_mem hs
  · rintro y ⟨a, ha, rfl⟩
    show correlationDeficitMap f Js Jt (Submodule.Quotient.mk a) = 0
    show targetLiftMap f Js Jt a = 0
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    refine Submodule.mem_comap.mpr ?_
    show f (a : V) ∈ Js.map f
    have ha' : a ∈ Submodule.comap (Jt.comap f).subtype (LinearMap.ker f) := ha
    have hzero : f (a : V) = 0 := LinearMap.mem_ker.mp (Submodule.mem_comap.mp ha')
    rw [hzero]
    exact (Js.map f).zero_mem

/-- Vertical extension law: the correlation fibre over the zero target class is an extension of
the deficit defect by the image of `ker f`. -/
theorem correlationVerticalTarget_exact :
    Function.Exact (correlationKernelImage f Js Jt).subtype
      (correlationDeficitMap f Js Jt) := by
  rw [LinearMap.exact_iff, ker_correlationDeficitMap, Submodule.range_subtype]

end DeficitExtension

section MatrixCoupling

variable (f : V →ₗ[𝕜] W) (Js : Submodule 𝕜 V) (Jt : Submodule 𝕜 W)

/-- Every source-envelope matrix admits an entrywise correlation coupling. -/
theorem exists_entrywise_correlation_lift_source {ι : Type*} (b : Matrix ι ι (V ⧸ Js)) :
    ∃ a : Matrix ι ι ((V ⧸ Js) × (W ⧸ Jt)),
      (∀ i j, a i j ∈ envelopeCorrelation f Js Jt) ∧ ∀ i j, (a i j).1 = b i j := by
  classical
  have hchoice : ∀ i j, ∃ x : V, (Submodule.Quotient.mk x : V ⧸ Js) = b i j :=
    fun i j => Submodule.mkQ_surjective Js (b i j)
  refine ⟨fun i j => correlationMap f Js Jt (Classical.choose (hchoice i j)), ?_, ?_⟩
  · exact fun i j => correlationMap_mem f Js Jt _
  · exact fun i j => Classical.choose_spec (hchoice i j)

/-- Every target-envelope matrix admits an entrywise correlation coupling when `f` is onto. -/
theorem exists_entrywise_correlation_lift_target {ι : Type*} (hf : Function.Surjective f)
    (b : Matrix ι ι (W ⧸ Jt)) :
    ∃ a : Matrix ι ι ((V ⧸ Js) × (W ⧸ Jt)),
      (∀ i j, a i j ∈ envelopeCorrelation f Js Jt) ∧ ∀ i j, (a i j).2 = b i j := by
  classical
  have hchoice : ∀ i j, ∃ x : V, (Submodule.Quotient.mk (f x) : W ⧸ Jt) = b i j := by
    intro i j
    obtain ⟨w, hw⟩ := Submodule.mkQ_surjective Jt (b i j)
    obtain ⟨x, rfl⟩ := hf w
    exact ⟨x, hw⟩
  refine ⟨fun i j => correlationMap f Js Jt (Classical.choose (hchoice i j)), ?_, ?_⟩
  · exact fun i j => correlationMap_mem f Js Jt _
  · exact fun i j => Classical.choose_spec (hchoice i j)

end MatrixCoupling

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
