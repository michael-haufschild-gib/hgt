import GaloisForLFunctions.HTGeometry.RealTorusDualPeriodComponents
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The identity component of the real points of a real torus

Let `V` be a finite-dimensional real vector space, `Λ ⊆ V` a full `ℤ`-lattice stable under an
`ℝ`-linear involution `σ`, and `A = V / Λ` the associated real torus with real structure.  The
group of real points is `A^σ`, and this file identifies its **topological** identity component with
the image of the fixed subspace `V^σ`:

* `RealTorusTop.span_fixedLattice`: `Λ ∩ V^σ` spans `V^σ` over `ℝ` (apply the averaging projector
  `(1 + σ)/2` to a lattice expansion);
* `RealTorusTop.isCompact_imageFixed`: hence the image of `V^σ` in `A` is compact;
* `RealTorusTop.isConnected_imageFixed`: it is connected;
* `RealTorusTop.connectedComponent_eq`: therefore, being a closed finite-index subgroup of the real
  points, it is open and equals the identity component.

Combined with `RealTorus.quotEquivTateH1` this makes the count `#π₀(A(ℝ)) = #Ĥ¹(⟨σ⟩, Λ)` used in
Proposition 5.1 of Suzuki, *Duality invariance of Faltings heights, Hodge line bundles and global
periods* (arXiv:2504.04993) a statement about the genuine topological component group.
-/

namespace GaloisForLFunctions.HTGeometry.RealTorusTop

open Submodule LinearMap Module RealTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {σ : V →ₗ[ℝ] V} {Λ : Submodule ℤ V}

/-- The `σ`-fixed subspace of `V`, as an `ℝ`-subspace. -/
def fixedSpace (σ : V →ₗ[ℝ] V) : Submodule ℝ V := LinearMap.ker (σ - LinearMap.id)

theorem mem_fixedSpace {v : V} : v ∈ fixedSpace σ ↔ σ v = v := by
  simp [fixedSpace, LinearMap.mem_ker, sub_eq_zero]

/-- The fixed part of the lattice, as a `ℤ`-submodule of `V`. -/
def fixedLattice (σ : V →ₗ[ℝ] V) (Λ : Submodule ℤ V) : Submodule ℤ V :=
  Λ ⊓ (fixedSpace σ).restrictScalars ℤ

theorem mem_fixedLattice {v : V} : v ∈ fixedLattice σ Λ ↔ v ∈ Λ ∧ σ v = v := by
  simp [fixedLattice, mem_fixedSpace]

theorem fixedLattice_le : fixedLattice σ Λ ≤ Λ := inf_le_left

theorem average_mem_span (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (v : V) :
    ((2 : ℝ)⁻¹ • (σ v + v)) ∈ Submodule.span ℝ ((fixedLattice σ Λ : Submodule ℤ V) : Set V) := by
  have hv : v ∈ Submodule.span ℝ ((Λ : Set V)) := by
    rw [IsZLattice.span_top (K := ℝ) (L := Λ)]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      refine mem_fixedLattice.mpr ⟨Λ.add_mem (hΛ x hx) hx, ?_⟩
      rw [map_add, hσ]
      abel
  | zero => simp
  | add x y _ _ hx hy =>
      have : (2 : ℝ)⁻¹ • (σ (x + y) + (x + y))
          = (2 : ℝ)⁻¹ • (σ x + x) + (2 : ℝ)⁻¹ • (σ y + y) := by
        rw [map_add]; module
      rw [this]
      exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      have : (2 : ℝ)⁻¹ • (σ (c • x) + c • x) = c • ((2 : ℝ)⁻¹ • (σ x + x)) := by
        rw [map_smul]; module
      rw [this]
      exact Submodule.smul_mem _ _ hx

/-- **`Λ ∩ V^σ` spans `V^σ`.** -/
theorem span_fixedLattice (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Submodule.span ℝ ((fixedLattice σ Λ : Submodule ℤ V) : Set V) = fixedSpace σ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact mem_fixedSpace.mpr (mem_fixedLattice.mp hx).2
  · intro v hv
    have hfix : σ v = v := mem_fixedSpace.mp hv
    have hrepr : v = (2 : ℝ)⁻¹ • (σ v + v) := by rw [hfix]; module
    rw [hrepr]
    exact average_mem_span hσ hΛ v


/-! ### The image of the fixed subspace in the torus -/

/-- The real torus `V / Λ`, as a topological group. -/
abbrev Torus (Λ : Submodule ℤ V) : Type _ := V ⧸ Λ.toAddSubgroup

/-- The quotient map `V → V / Λ`. -/
abbrev torusMk (Λ : Submodule ℤ V) : V →+ Torus Λ := QuotientAddGroup.mk' Λ.toAddSubgroup

theorem coe_mem_of_mem_spanZ_basis {E : Type*} [AddCommGroup E]
    (f : E →ₗ[ℤ] V) (N : Submodule ℤ V) {s : Set E} (hs : ∀ x ∈ s, f x ∈ N)
    {w : E} (hw : w ∈ Submodule.span ℤ s) : f w ∈ N := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact N.add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact N.smul_mem c hx

/-- **The image of `V^σ` in the torus is compact.**  It is the image of the closure of a
fundamental domain for the lattice `Λ ∩ V^σ`, which spans `V^σ`. -/
theorem isCompact_imageFixed (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    IsCompact ((torusMk Λ) '' ((fixedSpace σ : Submodule ℝ V) : Set V)) := by
  classical
  set E := (fixedSpace σ : Submodule ℝ V)
  set T : Set E := {x : E | (x : V) ∈ fixedLattice σ Λ} with hT
  have hspanT : Submodule.span ℝ T = ⊤ := by
    refine top_le_iff.mp ?_
    intro x _
    have hx : (x : V) ∈ fixedSpace σ := x.2
    rw [← span_fixedLattice hσ hΛ] at hx
    have hmap : Submodule.map E.subtype (Submodule.span ℝ T)
        = Submodule.span ℝ ((fixedLattice σ Λ : Submodule ℤ V) : Set V) := by
      rw [Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hy
        exact ⟨⟨y, mem_fixedSpace.mpr (mem_fixedLattice.mp hy).2⟩, hy, rfl⟩
    have : (x : V) ∈ Submodule.map E.subtype (Submodule.span ℝ T) := by rw [hmap]; exact hx
    obtain ⟨z, hz, hzx⟩ := this
    have : z = x := Subtype.ext hzx
    exact this ▸ hz
  obtain ⟨s, hsT, hspans, hli⟩ := exists_linearIndependent ℝ T
  haveI : Finite ↥s := hli.finite
  haveI : Fintype ↥s := Fintype.ofFinite _
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range (Subtype.val : ↥s → E)) := by
    rw [Subtype.range_coe, hspans, hspanT]
  set b : Basis ↥s ℝ E := Basis.mk hli htop with hb
  have hbcoe : ∀ i : ↥s, ((b i : E) : V) ∈ fixedLattice σ Λ := by
    intro i
    rw [hb, Basis.mk_apply]
    exact hsT i.2
  set F := ZSpan.fundamentalDomain b with hF
  have hKcompact : IsCompact (closure F) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  have himg : (torusMk Λ) '' ((E : Set V))
      = (torusMk Λ) '' ((Subtype.val : E → V) '' closure F) := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b ⟨v, hv⟩
      refine ⟨((w +ᵥ (⟨v, hv⟩ : E) : E) : V), ⟨_, subset_closure hw, rfl⟩, ?_⟩
      have hwΛ : ((w : E) : V) ∈ Λ := by
        refine coe_mem_of_mem_spanZ_basis (E.subtype.restrictScalars ℤ) Λ ?_ w.2
        rintro x ⟨i, rfl⟩
        exact fixedLattice_le (hbcoe i)
      have : ((w +ᵥ (⟨v, hv⟩ : E) : E) : V) = ((w : E) : V) + v := rfl
      rw [this]
      simp only [QuotientAddGroup.mk'_apply]
      exact (QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using Λ.neg_mem hwΛ)).symm
    · rintro _ ⟨v, ⟨x, -, rfl⟩, rfl⟩
      exact ⟨(x : V), x.2, rfl⟩
  rw [himg]
  exact (hKcompact.image continuous_subtype_val).image continuous_quotient_mk'

/-! ### The real points and their identity component -/

/-- The involution induced on the torus. -/
def torusSigma (σ : V →ₗ[ℝ] V) (Λ : Submodule ℤ V) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    Torus Λ →+ Torus Λ :=
  QuotientAddGroup.map Λ.toAddSubgroup Λ.toAddSubgroup
    ((σ.restrictScalars ℤ).toAddMonoidHom) (fun x hx => hΛ x hx)

@[simp] theorem torusSigma_mk (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) (v : V) :
    torusSigma σ Λ hΛ (torusMk Λ v) = torusMk Λ (σ v) := rfl

/-- The subgroup of real points `A^σ` of the torus. -/
def realPoints (σ : V →ₗ[ℝ] V) (Λ : Submodule ℤ V) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    AddSubgroup (Torus Λ) :=
  AddMonoidHom.eqLocus (torusSigma σ Λ hΛ) (AddMonoidHom.id (Torus Λ))

/-- The image of the fixed subspace `V^σ` in the torus. -/
def imageFixed (σ : V →ₗ[ℝ] V) (Λ : Submodule ℤ V) : AddSubgroup (Torus Λ) :=
  AddSubgroup.map (torusMk Λ) (fixedSpace σ).toAddSubgroup

theorem coe_imageFixed :
    ((imageFixed σ Λ : AddSubgroup (Torus Λ)) : Set (Torus Λ))
      = (torusMk Λ) '' ((fixedSpace σ : Submodule ℝ V) : Set V) := rfl

theorem mem_realPoints_mk (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) (v : V) :
    torusMk Λ v ∈ realPoints σ Λ hΛ ↔ v ∈ RealTorus.realLocus σ Λ := by
  show torusSigma σ Λ hΛ (torusMk Λ v) = torusMk Λ v ↔ _
  rw [torusSigma_mk, RealTorus.mem_realLocus]
  show (QuotientAddGroup.mk' Λ.toAddSubgroup) (σ v) = (QuotientAddGroup.mk' Λ.toAddSubgroup) v ↔ _
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_iff_sub_mem]
  rfl

theorem imageFixed_le_realPoints (hΛ : ∀ x ∈ Λ, σ x ∈ Λ) :
    imageFixed σ Λ ≤ realPoints σ Λ hΛ := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_realPoints_mk hΛ, RealTorus.mem_realLocus, mem_fixedSpace.mp hv, sub_self]
  exact Λ.zero_mem

theorem exists_realLocus_of_mem_realPoints (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    {a : Torus Λ} (ha : a ∈ realPoints σ Λ hΛ) :
    ∃ v ∈ RealTorus.realLocus σ Λ, torusMk Λ v = a := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) a
  exact ⟨v, (mem_realPoints_mk hΛ v).mp ha, rfl⟩

/-- **The topological component group of `A(ℝ)` is `Ĥ¹(⟨σ⟩, Λ)`.**  The natural map from the
algebraic component group `W / (V^σ + Λ)` to `A^σ / image(V^σ)` is a bijection. -/
theorem card_quotient_realPoints (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ] :
    Nat.card (↥(realPoints σ Λ hΛ) ⧸ (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ))
      = Nat.card (InvolutionTate.H1 (RealTorus.sigmaLat σ Λ hΛ)) := by
  classical
  set W := RealTorus.realLocus σ Λ with hW
  set P := Submodule.comap W.subtype (RealTorus.fixedPart σ ⊔ Λ) with hP
  set g : W → (↥(realPoints σ Λ hΛ) ⧸ (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) :=
    fun w => QuotientAddGroup.mk
      ⟨torusMk Λ (w : V), (mem_realPoints_mk hΛ (w : V)).mpr w.2⟩ with hg
  have hkey : ∀ a b : W, g a = g b ↔ torusMk Λ (a : V) - torusMk Λ (b : V) ∈ imageFixed σ Λ := by
    intro a b
    rw [hg]
    constructor
    · intro h
      have h2 := QuotientAddGroup.eq_iff_sub_mem.mp h
      rwa [AddSubgroup.mem_addSubgroupOf] at h2
    · intro h
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      rwa [AddSubgroup.mem_addSubgroupOf]
  have hgwd : ∀ a b : W, a - b ∈ P → g a = g b := by
    intro a b hab
    obtain ⟨f, hf, l, hl, hfl⟩ := Submodule.mem_sup.mp (Submodule.mem_comap.mp hab)
    have hcoe : ((a : V) - (b : V)) = f + l := hfl.symm
    rw [hkey]
    have hdiff : torusMk Λ (a : V) - torusMk Λ (b : V) = torusMk Λ f := by
      rw [← map_sub, hcoe, map_add]
      have hlmk : torusMk Λ l = 0 := (QuotientAddGroup.eq_zero_iff l).mpr hl
      rw [hlmk, add_zero]
    rw [hdiff]
    exact ⟨f, mem_fixedSpace.mpr (RealTorus.mem_fixedPart.mp hf), rfl⟩
  have hginj : ∀ a b : W, g a = g b → a - b ∈ P := by
    intro a b hab
    obtain ⟨f, hf, hfeq⟩ := (hkey a b).mp hab
    rw [hP, Submodule.mem_comap, Submodule.mem_sup]
    refine ⟨f, RealTorus.mem_fixedPart.mpr (mem_fixedSpace.mp hf), ((a : V) - (b : V)) - f, ?_,
      by show f + (((a : V) - (b : V)) - f) = ((a - b : W) : V); simp⟩
    refine (QuotientAddGroup.eq_zero_iff (N := Λ.toAddSubgroup) _).mp ?_
    show torusMk Λ (((a : V) - (b : V)) - f) = 0
    rw [map_sub, map_sub]
    rw [show torusMk Λ f = torusMk Λ (a : V) - torusMk Λ (b : V) from hfeq]
    abel
  have hlift := fun (a b : W) (hab : P.quotientRel a b) =>
    hgwd a b ((Submodule.quotientRel_def P).mp hab)
  have hsurj : Function.Surjective (Quotient.lift g hlift) := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective
      (s := (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) y
    obtain ⟨v, hv, hva⟩ := exists_realLocus_of_mem_realPoints hΛ a.2
    refine ⟨Submodule.Quotient.mk ⟨v, hv⟩, ?_⟩
    have hsub : (⟨torusMk Λ v, (mem_realPoints_mk hΛ v).mpr hv⟩ : ↥(realPoints σ Λ hΛ)) = a :=
      Subtype.ext hva
    show QuotientAddGroup.mk (⟨torusMk Λ v, (mem_realPoints_mk hΛ v).mpr hv⟩
        : ↥(realPoints σ Λ hΛ)) = QuotientAddGroup.mk a
    rw [hsub]
  have hinj : Function.Injective (Quotient.lift g hlift) := by
    refine fun q q' h => ?_
    induction q using Quotient.inductionOn with
    | _ a =>
      induction q' using Quotient.inductionOn with
      | _ b =>
        exact (Submodule.Quotient.eq P).mpr (hginj a b h)
  have hcard : Nat.card (↥(RealTorus.realLocus σ Λ) ⧸
        Submodule.comap (RealTorus.realLocus σ Λ).subtype (RealTorus.fixedPart σ ⊔ Λ))
      = Nat.card (↥(realPoints σ Λ hΛ) ⧸ (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) :=
    Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  rw [← hcard]
  exact RealTorus.card_quot_eq_card_tateH1 hσ hΛ

theorem finite_quotient_realPoints (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ] :
    Finite (↥(realPoints σ Λ hΛ) ⧸ (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_quotient_realPoints hσ hΛ]
  exact InvolutionTate.card_H1_ne_zero (RealTorus.sigmaLat_involutive hσ hΛ)

/-- **The image of `V^σ` is the identity component of the real points.**  It is compact (hence
closed), of finite index (hence open), and connected. -/
theorem connectedComponent_eq (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    connectedComponent (0 : ↥(realPoints σ Λ hΛ))
      = (((imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) : Set ↥(realPoints σ Λ hΛ)) := by
  haveI hΛclosed : IsClosed (Λ.toAddSubgroup : Set V) := AddSubgroup.isClosed_of_discrete
  have hcompact : IsCompact ((imageFixed σ Λ : AddSubgroup (Torus Λ)) : Set (Torus Λ)) := by
    rw [coe_imageFixed]
    exact isCompact_imageFixed hσ hΛ
  have hclosedA : IsClosed ((imageFixed σ Λ : AddSubgroup (Torus Λ)) : Set (Torus Λ)) :=
    hcompact.isClosed
  have hclosed : IsClosed (((imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ) :
      AddSubgroup ↥(realPoints σ Λ hΛ)) : Set ↥(realPoints σ Λ hΛ)) :=
    hclosedA.preimage continuous_subtype_val
  haveI : Finite (↥(realPoints σ Λ hΛ) ⧸ (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) :=
    finite_quotient_realPoints hσ hΛ
  haveI : ((imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)).FiniteIndex :=
    AddSubgroup.finiteIndex_of_finite_quotient
  have hopen := AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ hclosed
  have hpre : IsPreconnected (((imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ) :
      AddSubgroup ↥(realPoints σ Λ hΛ)) : Set ↥(realPoints σ Λ hΛ)) := by
    rw [← Topology.IsInducing.isPreconnected_image
      (f := (Subtype.val : ↥(realPoints σ Λ hΛ) → Torus Λ)) Topology.IsInducing.subtypeVal]
    have himg : (Subtype.val : ↥(realPoints σ Λ hΛ) → Torus Λ) ''
        (((imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) : Set _)
        = ((imageFixed σ Λ : AddSubgroup (Torus Λ)) : Set (Torus Λ)) := by
      have hcoe : (((imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ)) : Set _)
          = (Subtype.val : ↥(realPoints σ Λ hΛ) → Torus Λ) ⁻¹'
            ((imageFixed σ Λ : AddSubgroup (Torus Λ)) : Set (Torus Λ)) := rfl
      rw [hcoe, Set.image_preimage_eq_inter_range, Subtype.range_coe]
      exact Set.inter_eq_left.mpr (imageFixed_le_realPoints hΛ)
    rw [himg, coe_imageFixed]
    exact ((fixedSpace σ).convex.isPreconnected).image _ continuous_quotient_mk'.continuousOn
  apply le_antisymm
  · exact IsClopen.connectedComponent_subset ⟨hclosed, hopen⟩ (zero_mem _)
  · exact hpre.subset_connectedComponent (zero_mem _)

/-- **Suzuki, Proposition 5.1, topological form.**  The component group of `A(ℝ)` — the quotient of
the real points by their identity component, which by `connectedComponent_eq` is the image of
`V^σ` — has the same cardinality as the corresponding invariant `Ĥ¹(-σ^∨, Λ^∨)` of the dual torus,
provided the fixed lattice has half the total rank (as it does for a complex torus with a real
structure). -/
theorem card_piZero_eq_card_H1_neg_dual (hσ : ∀ x, σ (σ x) = x) (hΛ : ∀ x ∈ Λ, σ x ∈ Λ)
    [DiscreteTopology Λ]
    (hbal : 2 * Module.finrank ℤ (InvolutionTate.plusPart (RealTorus.sigmaLat σ Λ hΛ))
      = Module.finrank ℤ Λ) :
    Nat.card (↥(realPoints σ Λ hΛ) ⧸ (imageFixed σ Λ).addSubgroupOf (realPoints σ Λ hΛ))
      = Nat.card (InvolutionTate.H1
          (-(InvolutionTate.dualInvolution (RealTorus.sigmaLat σ Λ hΛ)))) := by
  rw [card_quotient_realPoints hσ hΛ]
  exact InvolutionTate.card_H1_eq_card_H1_neg_dualInvolution_of_two_mul
    (RealTorus.sigmaLat_involutive hσ hΛ) hbal

end GaloisForLFunctions.HTGeometry.RealTorusTop
