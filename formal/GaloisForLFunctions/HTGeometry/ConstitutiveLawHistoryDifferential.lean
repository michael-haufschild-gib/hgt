import GaloisForLFunctions.HTGeometry.ConstitutiveLawHistorySpectralMechanics

/-!
# The local law-history differential

For composable linear laws `X --f--> Y --g--> Z`, later erasure and earlier nonattainment meet in
the canonical map

`ker g → coker f`, `y ↦ [y]`.

This module proves the full kernel--cokernel exact sequence of the composition, the exact
classification of invertible composites, the split-transgression identification, and finite
index conservation.
-/

namespace GaloisForLFunctions.HTGeometry

open LawHistorySpectralMechanics

noncomputable section

universe u v w x

variable {k : Type u} {X : Type v} {Y : Type w} {Z : Type x}
variable [Field k]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup Y] [Module k Y]
variable [AddCommGroup Z] [Module k Z]

/-- The first law-history differential: a class erased by the later law is read modulo the
range attained by the earlier law. -/
def lawHistoryDifferential (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.ker g →ₗ[k] (Y ⧸ LinearMap.range f) :=
  (LinearMap.range f).mkQ.comp (LinearMap.ker g).subtype

@[simp]
theorem lawHistoryDifferential_apply
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) (y : LinearMap.ker g) :
    lawHistoryDifferential f g y = (LinearMap.range f).mkQ y.1 :=
  rfl

/-- The old kernel includes into the kernel of the composite. -/
def kernelToCompositeKernel (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.ker f →ₗ[k] LinearMap.ker (g.comp f) where
  toFun x := ⟨x.1, by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp x.2, map_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A kernel class of the composite is transported to the later kernel by the earlier law. -/
def compositeKernelToLaterKernel (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.ker (g.comp f) →ₗ[k] LinearMap.ker g where
  toFun x := ⟨f x.1, by
    rw [LinearMap.mem_ker]
    exact LinearMap.mem_ker.mp x.2⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Raw map from the earlier target into the cokernel of the composite. -/
def earlierCokerToCompositeRaw (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    Y →ₗ[k] (Z ⧸ LinearMap.range (g.comp f)) :=
  (LinearMap.range (g.comp f)).mkQ.comp g

theorem range_f_le_ker_earlierCokerToCompositeRaw
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.range f ≤ LinearMap.ker (earlierCokerToCompositeRaw f g) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  change (LinearMap.range (g.comp f)).mkQ (g (f x)) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

/-- The earlier cokernel maps to the composite cokernel by applying the later law. -/
def earlierCokerToCompositeCoker (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    (Y ⧸ LinearMap.range f) →ₗ[k] (Z ⧸ LinearMap.range (g.comp f)) :=
  Submodule.liftQ (LinearMap.range f) (earlierCokerToCompositeRaw f g)
    (range_f_le_ker_earlierCokerToCompositeRaw f g)

@[simp]
theorem earlierCokerToCompositeCoker_mkQ
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) (y : Y) :
    earlierCokerToCompositeCoker f g ((LinearMap.range f).mkQ y) =
      (LinearMap.range (g.comp f)).mkQ (g y) :=
  rfl

theorem kernelToCompositeKernel_injective (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    Function.Injective (kernelToCompositeKernel f g) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun q : LinearMap.ker (g.comp f) => q.1) hab)

theorem range_kernelToCompositeKernel_eq_ker
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.range (kernelToCompositeKernel f g) =
      LinearMap.ker (compositeKernelToLaterKernel f g) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact LinearMap.mem_ker.mp a.2
  · intro hx
    have hfx : f x.1 = 0 := by
      have := LinearMap.mem_ker.mp hx
      exact congrArg Subtype.val this
    refine ⟨⟨x.1, LinearMap.mem_ker.mpr hfx⟩, ?_⟩
    exact Subtype.ext rfl

theorem range_compositeKernelToLaterKernel_eq_ker
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.range (compositeKernelToLaterKernel f g) =
      LinearMap.ker (lawHistoryDifferential f g) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [LinearMap.mem_ker, lawHistoryDifferential_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x.1, rfl⟩
  · intro hy
    have hyRange : y.1 ∈ LinearMap.range f := by
      rw [LinearMap.mem_ker, lawHistoryDifferential_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact hy
    obtain ⟨x, hx⟩ := hyRange
    have hxComp : x ∈ LinearMap.ker (g.comp f) := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, hx]
      exact LinearMap.mem_ker.mp y.2
    refine ⟨⟨x, hxComp⟩, ?_⟩
    exact Subtype.ext hx

theorem range_lawHistoryDifferential_eq_ker
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.range (lawHistoryDifferential f g) =
      LinearMap.ker (earlierCokerToCompositeCoker f g) := by
  ext q
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    change (LinearMap.range (g.comp f)).mkQ (g y.1) = 0
    rw [LinearMap.mem_ker.mp y.2, Submodule.mkQ_apply]
    simp
  · intro hq
    induction q using Submodule.Quotient.induction_on with | _ y => ?_
    change earlierCokerToCompositeCoker f g ((LinearMap.range f).mkQ y) = 0 at hq
    rw [earlierCokerToCompositeCoker_mkQ, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨x, hx⟩ := hq
    let z : LinearMap.ker g := ⟨y - f x, by
      rw [LinearMap.mem_ker, map_sub]
      have : g (f x) = g y := by
        simpa only [LinearMap.comp_apply] using hx
      rw [this, sub_self]⟩
    refine ⟨z, ?_⟩
    change (LinearMap.range f).mkQ (y - f x) = (LinearMap.range f).mkQ y
    apply (Submodule.Quotient.eq _).2
    change (y - f x) - y ∈ LinearMap.range f
    refine ⟨-x, ?_⟩
    simp

theorem range_earlierCokerToCompositeCoker_eq_ker
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    LinearMap.range (earlierCokerToCompositeCoker f g) =
      LinearMap.ker (compositeToOuter f g) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    induction p using Submodule.Quotient.induction_on with | _ y => ?_
    change earlierCokerToCompositeCoker f g ((LinearMap.range f).mkQ y) ∈
      LinearMap.ker (compositeToOuter f g)
    rw [LinearMap.mem_ker, earlierCokerToCompositeCoker_mkQ,
      compositeToOuter_mkQ]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y, rfl⟩
  · intro hq
    induction q using Submodule.Quotient.induction_on with | _ z => ?_
    change (LinearMap.range (g.comp f)).mkQ z ∈ LinearMap.ker (compositeToOuter f g) at hq
    rw [LinearMap.mem_ker, compositeToOuter_mkQ, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨y, hy⟩ := hq
    refine ⟨(LinearMap.range f).mkQ y, ?_⟩
    rw [earlierCokerToCompositeCoker_mkQ]
    exact (Submodule.Quotient.eq _).2 (by
      change g y - z ∈ LinearMap.range (g.comp f)
      rw [hy, sub_self]
      exact Submodule.zero_mem _)

/-- Full exactness certificate for the local law-history differential. -/
theorem lawHistory_sevenTerm_exact
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    Function.Injective (kernelToCompositeKernel f g) ∧
      LinearMap.range (kernelToCompositeKernel f g) =
        LinearMap.ker (compositeKernelToLaterKernel f g) ∧
      LinearMap.range (compositeKernelToLaterKernel f g) =
        LinearMap.ker (lawHistoryDifferential f g) ∧
      LinearMap.range (lawHistoryDifferential f g) =
        LinearMap.ker (earlierCokerToCompositeCoker f g) ∧
      LinearMap.range (earlierCokerToCompositeCoker f g) =
        LinearMap.ker (compositeToOuter f g) ∧
      Function.Surjective (compositeToOuter f g) :=
  ⟨kernelToCompositeKernel_injective f g,
    range_kernelToCompositeKernel_eq_ker f g,
    range_compositeKernelToLaterKernel_eq_ker f g,
    range_lawHistoryDifferential_eq_ker f g,
    range_earlierCokerToCompositeCoker_eq_ker f g,
    compositeToOuter_surjective f g⟩

theorem lawHistoryDifferential_bijective_of_comp
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z)
    (hgf : Function.Bijective (g.comp f)) :
    Function.Bijective (lawHistoryDifferential f g) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have hmem : a.1 - b.1 ∈ LinearMap.range f := by
      change (LinearMap.range f).mkQ a.1 = (LinearMap.range f).mkQ b.1 at hab
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hab
      exact (Submodule.Quotient.eq _).1 hab
    obtain ⟨x, hx⟩ := hmem
    have hx0 : x = 0 := hgf.1 (by
      change g (f x) = g (f 0)
      rw [hx, map_sub, LinearMap.mem_ker.mp a.2, LinearMap.mem_ker.mp b.2,
        sub_self, map_zero, map_zero])
    have : a.1 - b.1 = 0 := by rw [← hx, hx0, map_zero]
    exact sub_eq_zero.mp this
  · intro q
    induction q using Submodule.Quotient.induction_on with | _ y => ?_
    obtain ⟨x, hx⟩ := hgf.2 (g y)
    let z : LinearMap.ker g := ⟨y - f x, by
      rw [LinearMap.mem_ker, map_sub]
      have : g (f x) = g y := by
        simpa only [LinearMap.comp_apply] using hx
      rw [this, sub_self]⟩
    refine ⟨z, ?_⟩
    change (LinearMap.range f).mkQ (y - f x) = (LinearMap.range f).mkQ y
    apply (Submodule.Quotient.eq _).2
    change (y - f x) - y ∈ LinearMap.range f
    refine ⟨-x, by simp⟩

theorem comp_bijective_of_lawHistoryDifferential
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hδ : Function.Bijective (lawHistoryDifferential f g)) :
    Function.Bijective (g.comp f) := by
  constructor
  · intro x y hxy
    have hdiff : x - y = 0 := by
      apply hf
      have hker : f (x - y) ∈ LinearMap.ker g := by
        have hgfxy : g (f x) = g (f y) := by
          simpa only [LinearMap.comp_apply] using hxy
        rw [LinearMap.mem_ker, map_sub, map_sub, hgfxy, sub_self]
      have hδzero : lawHistoryDifferential f g ⟨f (x - y), hker⟩ = 0 := by
        rw [lawHistoryDifferential_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact ⟨x - y, rfl⟩
      have hz : (⟨f (x - y), hker⟩ : LinearMap.ker g) = 0 :=
        hδ.1 (by simpa using hδzero)
      simpa using congrArg Subtype.val hz
    exact sub_eq_zero.mp hdiff
  · intro z
    obtain ⟨y, hy⟩ := hg z
    obtain ⟨a, ha⟩ := hδ.2 ((LinearMap.range f).mkQ y)
    have hmem : a.1 - y ∈ LinearMap.range f := by
      change (LinearMap.range f).mkQ a.1 = (LinearMap.range f).mkQ y at ha
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at ha
      exact (Submodule.Quotient.eq _).1 ha
    obtain ⟨x, hx⟩ := hmem
    refine ⟨-x, ?_⟩
    rw [LinearMap.comp_apply]
    calc
      g (f (-x)) = -g (f x) := by simp
      _ = -g (a.1 - y) := by rw [← hx]
      _ = z := by
        rw [map_sub, LinearMap.mem_ker.mp a.2, zero_sub, neg_neg, hy]

/-- Exact classification: local endpoint exactness plus bijective transgression is equivalent to
invertibility of the total law. -/
theorem comp_bijective_iff_boundary_and_transgression
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    Function.Bijective (g.comp f) ↔
      Function.Injective f ∧ Function.Surjective g ∧
        Function.Bijective (lawHistoryDifferential f g) := by
  constructor
  · intro hgf
    refine ⟨fun x y hxy => hgf.1 ?_, fun z => ?_, lawHistoryDifferential_bijective_of_comp f g hgf⟩
    · simpa only [LinearMap.comp_apply, hxy]
    · obtain ⟨x, hx⟩ := hgf.2 z
      exact ⟨f x, by simpa only [LinearMap.comp_apply] using hx⟩
  · rintro ⟨hf, hg, hδ⟩
    exact comp_bijective_of_lawHistoryDifferential f g hf hg hδ

theorem lawHistoryDifferential_eq_splitKernelToCokernel
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) :
    lawHistoryDifferential f g = splitKernelToCokernel f g :=
  rfl

/-- In a split history, the general differential is the inverse of the previously constructed
split transgression. -/
def splitLawHistoryDifferentialEquiv
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id) :
    LinearMap.ker g ≃ₗ[k] (Y ⧸ LinearMap.range f) :=
  (splitTransgressionEquiv f g hgf).symm

@[simp]
theorem splitLawHistoryDifferentialEquiv_apply
    (f : X →ₗ[k] Y) (g : Y →ₗ[k] X) (hgf : g.comp f = LinearMap.id)
    (y : LinearMap.ker g) :
    splitLawHistoryDifferentialEquiv f g hgf y = lawHistoryDifferential f g y :=
  rfl

section FiniteDimensional

variable [FiniteDimensional k X] [FiniteDimensional k Y] [FiniteDimensional k Z]

/-- Finite-dimensional kernel--cokernel index of a linear law. -/
def finiteLawIndex {U V : Type*} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [FiniteDimensional k U] [FiniteDimensional k V]
    (f : U →ₗ[k] V) : ℤ :=
  (Module.finrank k (LinearMap.ker f) : ℤ) -
    (Module.finrank k (V ⧸ LinearMap.range f) : ℤ)

theorem finiteLawIndex_eq_finrank_sub {U V : Type*} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [FiniteDimensional k U] [FiniteDimensional k V]
    (f : U →ₗ[k] V) :
    finiteLawIndex f = (Module.finrank k U : ℤ) - Module.finrank k V := by
  unfold finiteLawIndex
  have hr := f.finrank_range_add_finrank_ker
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  omega

/-- Finite index is conserved under law composition. -/
theorem finiteLawIndex_comp (f : X →ₗ[k] Y) (g : Y →ₗ[k] Z) :
    finiteLawIndex (g.comp f) = finiteLawIndex f + finiteLawIndex g := by
  rw [finiteLawIndex_eq_finrank_sub, finiteLawIndex_eq_finrank_sub,
    finiteLawIndex_eq_finrank_sub]
  omega

end FiniteDimensional

end


end GaloisForLFunctions.HTGeometry
