import GaloisForLFunctions.HTGeometry.SiteSupportedLocalHamiltonian
import GaloisForLFunctions.HTGeometry.LocalExtensionMatrixChart

/-!
# Adjoining one site to a site-factorized network

Growing a finite quantum network by one site turns the carrier
`(∀ w ≠ v, A w) × A v` into `∀ w, A w`.  This file records that exchange as an
explicit equivalence and transports the three kinds of operator produced by a
leaf extension:

* an inherited operator tensored with the identity keeps its old site packet;
* the identity tensored with a new local operator is supported on the new site;
* an inherited one-site operator tensored with a new local operator is
  supported on the new interaction edge.

The consequence is that the whole inherited local Hamiltonian space embeds into
the enlarged one, and that a leaf Hamiltonian is a graph-local Hamiltonian of
the enlarged interaction graph.
-/

open scoped Kronecker BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] (A : V → Type*)
    [∀ v, DecidableEq (A v)]

/-- Split the site product into the remaining sites and one distinguished
local factor. -/
def leafSiteEquiv (v : V) :
    ((∀ w : {w : V // w ≠ v}, A w.1) × A v) ≃ (∀ w : V, A w) :=
  (Equiv.prodComm _ _).trans (Equiv.piSplitAt v A).symm

omit [Fintype V] [∀ v, DecidableEq (A v)] in
@[simp] theorem leafSiteEquiv_symm_apply (v : V) (x : ∀ w, A w) :
    (leafSiteEquiv A v).symm x = ((fun w : {w : V // w ≠ v} => x w.1), x v) :=
  rfl

/-- Read a two-factor operator on the enlarged site product. -/
def leafTransport (v : V)
    (N : Matrix ((∀ w : {w : V // w ≠ v}, A w.1) × A v)
      ((∀ w : {w : V // w ≠ v}, A w.1) × A v) ℂ) :
    Matrix (∀ w : V, A w) (∀ w : V, A w) ℂ :=
  Matrix.reindex (leafSiteEquiv A v) (leafSiteEquiv A v) N

omit [Fintype V] [∀ v, DecidableEq (A v)] in
theorem leafTransport_layerMatrixCoupling_apply (v : V)
    (H : Matrix (∀ w : {w : V // w ≠ v}, A w.1)
      (∀ w : {w : V // w ≠ v}, A w.1) ℂ)
    (M : Matrix (A v) (A v) ℂ) (x y : ∀ w, A w) :
    leafTransport A v (layerMatrixCoupling H M) x y =
      H (fun w => x w.1) (fun w => y w.1) * M (x v) (y v) := rfl

omit [Fintype V] [∀ v, DecidableEq (A v)] in
theorem leafTransport_add (v : V) (N N' : Matrix _ _ ℂ) :
    leafTransport A v (N + N') = leafTransport A v N + leafTransport A v N' :=
  rfl

omit [Fintype V] [∀ v, DecidableEq (A v)] in
theorem leafTransport_smul (v : V) (c : ℝ) (N : Matrix _ _ ℂ) :
    leafTransport A v (c • N) = c • leafTransport A v N := rfl

omit [Fintype V] [∀ v, DecidableEq (A v)] in
theorem leafTransport_conjTranspose (v : V) (N : Matrix _ _ ℂ) :
    (leafTransport A v N)ᴴ = leafTransport A v Nᴴ := rfl

theorem layerMatrixCoupling_conjTranspose
    {α ρ : Type*} (H : Matrix α α ℂ) (M : Matrix ρ ρ ℂ) :
    (layerMatrixCoupling H M)ᴴ = layerMatrixCoupling Hᴴ Mᴴ := by
  ext x y
  simp [layerMatrixCoupling, Matrix.conjTranspose_apply]

theorem layerMatrixCoupling_add_left
    {α ρ : Type*} (H H' : Matrix α α ℂ) (M : Matrix ρ ρ ℂ) :
    layerMatrixCoupling (H + H') M =
      layerMatrixCoupling H M + layerMatrixCoupling H' M := by
  ext x y
  simp [layerMatrixCoupling, add_mul]

theorem layerMatrixCoupling_smul_left
    {α ρ : Type*} (c : ℝ) (H : Matrix α α ℂ) (M : Matrix ρ ρ ℂ) :
    layerMatrixCoupling (c • H) M = c • layerMatrixCoupling H M := by
  ext x y
  simp only [layerMatrixCoupling, Matrix.smul_apply, Complex.real_smul]
  ring

/-- Image in the enlarged site set of a packet of remaining sites. -/
def deletedSiteImage (v : V) (S : Finset {w : V // w ≠ v}) : Finset V :=
  S.map ⟨Subtype.val, Subtype.val_injective⟩

variable {A}

omit [Fintype V] [DecidableEq V] [∀ v, DecidableEq (A v)] in
theorem mem_deletedSiteImage_iff {v : V} {S : Finset {w : V // w ≠ v}}
    {w : {w : V // w ≠ v}} : w.1 ∈ deletedSiteImage v S ↔ w ∈ S := by
  simp [deletedSiteImage]

omit [Fintype V] [DecidableEq V] [∀ v, DecidableEq (A v)] in
theorem notMem_deletedSiteImage_self (v : V) (S : Finset {w : V // w ≠ v}) :
    v ∉ deletedSiteImage v S := by
  simp only [deletedSiteImage, Finset.mem_map, Function.Embedding.coeFn_mk]
  rintro ⟨w, -, hw⟩
  exact w.2 hw

omit [Fintype V] [DecidableEq V] [∀ v, DecidableEq (A v)] in
theorem notMem_deletedSiteImage_of_ne {v : V} {S : Finset {w : V // w ≠ v}}
    {w : V} (hw : w ≠ v) (hwS : (⟨w, hw⟩ : {w : V // w ≠ v}) ∉ S) :
    w ∉ deletedSiteImage v S := by
  intro hmem
  exact hwS (mem_deletedSiteImage_iff.mp hmem)

omit [Fintype V] [DecidableEq V] [∀ v, DecidableEq (A v)] in
theorem deletedSiteImage_singleton (v : V) (u : {w : V // w ≠ v}) :
    deletedSiteImage v {u} = {u.1} := by
  simp [deletedSiteImage]

omit [Fintype V] [∀ v, DecidableEq (A v)] in
theorem deletedSiteImage_pair (v : V) (u u' : {w : V // w ≠ v}) :
    deletedSiteImage v {u, u'} = {u.1, u'.1} := by
  simp [deletedSiteImage]

omit [Fintype V] [DecidableEq V] [∀ v, DecidableEq (A v)] in
theorem deletedSiteImage_empty (v : V) :
    deletedSiteImage v (∅ : Finset {w : V // w ≠ v}) = ∅ := by
  simp [deletedSiteImage]

/-- The identity operator is supported on the empty packet. -/
theorem isSiteSupported_one {ι : Type*} {B : ι → Type*} [Fintype ι]
    [DecidableEq ι] [∀ i, DecidableEq (B i)] :
    IsSiteSupported (A := B) (∅ : Finset ι) 1 := by
  classical
  constructor
  · rintro x y ⟨w, -, hne⟩
    have hxy : x ≠ y := fun h => hne (congrFun h w)
    simp [hxy]
  · intro x y x' y' _ _ h₃ h₄
    have hxy : x = y := funext fun w => h₃ w (Finset.notMem_empty w)
    have hxy' : x' = y' := funext fun w => h₄ w (Finset.notMem_empty w)
    subst hxy
    subst hxy'
    simp

omit [Fintype V] in
/-- An inherited operator tensored with the identity keeps its site packet. -/
theorem isSiteSupported_leafTransport_id {v : V}
    {S : Finset {w : V // w ≠ v}}
    {H : Matrix (∀ w : {w : V // w ≠ v}, A w.1)
      (∀ w : {w : V // w ≠ v}, A w.1) ℂ}
    (hH : IsSiteSupported S H) :
    IsSiteSupported (deletedSiteImage v S)
      (leafTransport A v (layerMatrixCoupling H 1)) := by
  classical
  constructor
  · rintro x y ⟨w, hwS, hne⟩
    rw [leafTransport_layerMatrixCoupling_apply]
    by_cases hwv : w = v
    · subst hwv
      simp [hne]
    · have : H (fun u => x u.1) (fun u => y u.1) = 0 :=
        hH.1 _ _ ⟨⟨w, hwv⟩, fun hmem => hwS (mem_deletedSiteImage_iff.mpr hmem),
          hne⟩
      simp [this]
  · intro x y x' y' h₁ h₂ h₃ h₄
    have hv : x v = y v := h₃ v (notMem_deletedSiteImage_self v S)
    have hv' : x' v = y' v := h₄ v (notMem_deletedSiteImage_self v S)
    have hHeq : H (fun u => x u.1) (fun u => y u.1) =
        H (fun u => x' u.1) (fun u => y' u.1) := by
      refine hH.2 _ _ _ _ ?_ ?_ ?_ ?_
      · exact fun u hu => h₁ u.1 (mem_deletedSiteImage_iff.mpr hu)
      · exact fun u hu => h₂ u.1 (mem_deletedSiteImage_iff.mpr hu)
      · exact fun u hu => h₃ u.1 (notMem_deletedSiteImage_of_ne u.2 hu)
      · exact fun u hu => h₄ u.1 (notMem_deletedSiteImage_of_ne u.2 hu)
    rw [leafTransport_layerMatrixCoupling_apply,
      leafTransport_layerMatrixCoupling_apply, hHeq]
    simp [Matrix.one_apply, hv, hv']

omit [Fintype V] [∀ v, DecidableEq (A v)] in
/-- An inherited operator tensored with a new local operator gains exactly the
new site. -/
theorem isSiteSupported_leafTransport {v : V}
    {S : Finset {w : V // w ≠ v}}
    {H : Matrix (∀ w : {w : V // w ≠ v}, A w.1)
      (∀ w : {w : V // w ≠ v}, A w.1) ℂ}
    (hH : IsSiteSupported S H) (M : Matrix (A v) (A v) ℂ) :
    IsSiteSupported (insert v (deletedSiteImage v S))
      (leafTransport A v (layerMatrixCoupling H M)) := by
  classical
  constructor
  · rintro x y ⟨w, hwS, hne⟩
    have hwv : w ≠ v := fun h => hwS (by simp [h])
    have hwimg : w ∉ deletedSiteImage v S := fun h => hwS (by simp [h])
    have : H (fun u => x u.1) (fun u => y u.1) = 0 :=
      hH.1 _ _ ⟨⟨w, hwv⟩, fun hmem =>
        hwimg (mem_deletedSiteImage_iff.mpr hmem), hne⟩
    rw [leafTransport_layerMatrixCoupling_apply, this, zero_mul]
  · intro x y x' y' h₁ h₂ h₃ h₄
    have hv : x v = x' v := h₁ v (Finset.mem_insert_self v _)
    have hvy : y v = y' v := h₂ v (Finset.mem_insert_self v _)
    have hHeq : H (fun u => x u.1) (fun u => y u.1) =
        H (fun u => x' u.1) (fun u => y' u.1) := by
      refine hH.2 _ _ _ _ ?_ ?_ ?_ ?_
      · exact fun u hu => h₁ u.1
          (Finset.mem_insert_of_mem (mem_deletedSiteImage_iff.mpr hu))
      · exact fun u hu => h₂ u.1
          (Finset.mem_insert_of_mem (mem_deletedSiteImage_iff.mpr hu))
      · intro u hu
        refine h₃ u.1 ?_
        simp only [Finset.mem_insert, not_or]
        exact ⟨u.2, notMem_deletedSiteImage_of_ne u.2 hu⟩
      · intro u hu
        refine h₄ u.1 ?_
        simp only [Finset.mem_insert, not_or]
        exact ⟨u.2, notMem_deletedSiteImage_of_ne u.2 hu⟩
    rw [leafTransport_layerMatrixCoupling_apply,
      leafTransport_layerMatrixCoupling_apply, hHeq, hv, hvy]

/-- A purely new local operator is supported on the new site. -/
theorem isSiteSupported_leafTransport_newSite (v : V)
    (M : Matrix (A v) (A v) ℂ) :
    IsSiteSupported {v}
      (leafTransport A v (layerMatrixCoupling 1 M)) := by
  have h := isSiteSupported_leafTransport
    (A := A) (v := v) (S := (∅ : Finset {w : V // w ≠ v}))
    (H := 1) isSiteSupported_one M
  have himg : insert v (deletedSiteImage v (∅ : Finset {w : V // w ≠ v}))
      = ({v} : Finset V) := by
    rw [deletedSiteImage_empty]
    simp
  rwa [himg] at h

variable (A)

omit [Fintype V] in
/-- **Inherited local Hamiltonians stay local.**  The whole local Hamiltonian
space of the remaining sites embeds into that of the enlarged network, as long
as every inherited interaction edge survives. -/
theorem leafTransport_mem_siteFactorLocalSubmodule (v : V)
    {oldG : SimpleGraph {w : V // w ≠ v}} {G : SimpleGraph V}
    (hcompat : ∀ a b : {w : V // w ≠ v}, oldG.Adj a b → G.Adj a.1 b.1)
    {H : Matrix (∀ w : {w : V // w ≠ v}, A w.1)
      (∀ w : {w : V // w ≠ v}, A w.1) ℂ}
    (hH : H ∈ siteFactorLocalSubmodule (fun w : {w : V // w ≠ v} => A w.1) oldG) :
    leafTransport A v (layerMatrixCoupling H 1) ∈
      siteFactorLocalSubmodule A G := by
  classical
  induction hH using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨hHermitian, hcase⟩ := hX
      have hherm : (leafTransport A v (layerMatrixCoupling X 1)).IsHermitian := by
        show (leafTransport A v (layerMatrixCoupling X 1))ᴴ = _
        rw [leafTransport_conjTranspose, layerMatrixCoupling_conjTranspose,
          hHermitian, Matrix.conjTranspose_one]
      rcases hcase with ⟨u, hu⟩ | ⟨u, u', huu', hsupp⟩
      · refine mem_siteFactorLocalSubmodule_of_oneSite A G hherm u.1 ?_
        have := isSiteSupported_leafTransport_id (A := A) hu
        rwa [deletedSiteImage_singleton] at this
      · refine mem_siteFactorLocalSubmodule_of_edge A G hherm
          (hcompat u u' huu') ?_
        have := isSiteSupported_leafTransport_id (A := A) hsupp
        rwa [deletedSiteImage_pair] at this
  | zero =>
      have : leafTransport A v (layerMatrixCoupling (0 : Matrix _ _ ℂ) 1) = 0 := by
        ext x y
        rw [leafTransport_layerMatrixCoupling_apply]
        simp
      rw [this]
      exact Submodule.zero_mem _
  | add X Y _ _ hXmem hYmem =>
      rw [layerMatrixCoupling_add_left, leafTransport_add]
      exact Submodule.add_mem _ hXmem hYmem
  | smul c X _ hXmem =>
      rw [layerMatrixCoupling_smul_left, leafTransport_smul]
      exact Submodule.smul_mem _ c hXmem

omit [Fintype V] in
/-- **Inherited interaction terms stay interaction terms.**  The whole term span
of the remaining sites embeds into that of the enlarged network, as long as
every inherited interaction edge survives. -/
theorem leafTransport_mem_siteFactorTermSpan (v : V)
    {oldG : SimpleGraph {w : V // w ≠ v}} {G : SimpleGraph V}
    (hcompat : ∀ a b : {w : V // w ≠ v}, oldG.Adj a b → G.Adj a.1 b.1)
    {H : Matrix (∀ w : {w : V // w ≠ v}, A w.1)
      (∀ w : {w : V // w ≠ v}, A w.1) ℂ}
    (hH : H ∈ siteFactorTermSpan (fun w : {w : V // w ≠ v} => A w.1) oldG) :
    leafTransport A v (layerMatrixCoupling H 1) ∈ siteFactorTermSpan A G := by
  classical
  induction hH using Submodule.span_induction with
  | mem X hX =>
      refine Submodule.subset_span ?_
      rcases hX with ⟨u, hu⟩ | ⟨u, u', huu', hsupp⟩
      · refine Or.inl ⟨u.1, ?_⟩
        have := isSiteSupported_leafTransport_id (A := A) hu
        rwa [deletedSiteImage_singleton] at this
      · refine Or.inr ⟨u.1, u'.1, hcompat u u' huu', ?_⟩
        have := isSiteSupported_leafTransport_id (A := A) hsupp
        rwa [deletedSiteImage_pair] at this
  | zero =>
      have hzero :
          leafTransport A v (layerMatrixCoupling (0 : Matrix _ _ ℂ) 1) = 0 := by
        ext x y
        rw [leafTransport_layerMatrixCoupling_apply]
        simp
      rw [hzero]
      exact Submodule.zero_mem _
  | add X Y _ _ hXmem hYmem =>
      rw [layerMatrixCoupling_add_left, leafTransport_add]
      exact Submodule.add_mem _ hXmem hYmem
  | smul c X _ hXmem =>
      rw [layerMatrixCoupling_smul_left, leafTransport_smul]
      exact Submodule.smul_mem _ c hXmem

/-- A purely new local operator is an interaction term of the enlarged
network. -/
theorem isGraphLocalTerm_leafTransport_newSite (v : V) (G : SimpleGraph V)
    (M : Matrix (A v) (A v) ℂ) :
    IsGraphLocalTerm A G (leafTransport A v (layerMatrixCoupling 1 M)) :=
  Or.inl ⟨v, isSiteSupported_leafTransport_newSite (A := A) v M⟩

omit [Fintype V] [∀ v, DecidableEq (A v)] in
/-- An inherited one-site operator coupled to a new local operator is an
interaction term along the new edge. -/
theorem isGraphLocalTerm_leafTransport_edge (v : V) {G : SimpleGraph V}
    {u : {w : V // w ≠ v}}
    {P : Matrix (∀ w : {w : V // w ≠ v}, A w.1)
      (∀ w : {w : V // w ≠ v}, A w.1) ℂ}
    (hP : IsSiteSupported {u} P) (hadj : G.Adj u.1 v)
    (M : Matrix (A v) (A v) ℂ) :
    IsGraphLocalTerm A G (leafTransport A v (layerMatrixCoupling P M)) := by
  refine Or.inr ⟨u.1, v, hadj, ?_⟩
  have hsupp := isSiteSupported_leafTransport (A := A) hP M
  rw [deletedSiteImage_singleton] at hsupp
  have hset : insert v ({u.1} : Finset V) = {u.1, v} := by
    ext w
    simp [or_comm]
  rwa [hset] at hsupp

/-- Split a two-site product into its two named local factors. -/
def twoSiteEquiv {a b : V} (hab : a ≠ b) (huniv : ∀ w : V, w = a ∨ w = b) :
    (A a × A b) ≃ (∀ w : V, A w) := by
  letI : Unique {w : V // w ≠ b} :=
    { default := ⟨a, hab⟩
      uniq := fun x => Subtype.ext ((huniv x.1).resolve_right x.2) }
  exact (Equiv.prodCongr
      (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm
      (Equiv.refl (A b))).trans (leafSiteEquiv A b)

omit [Fintype V] in
/-- The first named factor of a two-site product carries one-site operators. -/
theorem isSiteSupported_twoSiteEquiv_left {a b : V} (hab : a ≠ b)
    (huniv : ∀ w : V, w = a ∨ w = b) (M : Matrix (A a) (A a) ℂ) :
    IsSiteSupported {a}
      (Matrix.reindex (twoSiteEquiv A hab huniv) (twoSiteEquiv A hab huniv)
        (layerMatrixCoupling M 1)) := by
  letI : Unique {w : V // w ≠ b} :=
    { default := ⟨a, hab⟩
      uniq := fun x => Subtype.ext ((huniv x.1).resolve_right x.2) }
  have hstep :
      Matrix.reindex (twoSiteEquiv A hab huniv) (twoSiteEquiv A hab huniv)
          (layerMatrixCoupling M 1) =
        leafTransport A b (layerMatrixCoupling
          (Matrix.reindex
            (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm
            (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm M) 1) :=
    rfl
  rw [hstep]
  have hsupp := isSiteSupported_leafTransport_id (A := A)
    (S := ({default} : Finset {w : V // w ≠ b}))
    (H := Matrix.reindex
      (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm
      (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm M)
    (IsSiteSupported.of_forall_mem
      (A := fun w : {w : V // w ≠ b} => A w.1)
      (fun w => by
        simp only [Finset.mem_singleton]
        exact Subsingleton.elim _ _) _)
  rwa [deletedSiteImage_singleton] at hsupp

/-- The second named factor of a two-site product carries one-site
operators. -/
theorem isSiteSupported_twoSiteEquiv_right {a b : V} (hab : a ≠ b)
    (huniv : ∀ w : V, w = a ∨ w = b) (N : Matrix (A b) (A b) ℂ) :
    IsSiteSupported {b}
      (Matrix.reindex (twoSiteEquiv A hab huniv) (twoSiteEquiv A hab huniv)
        (layerMatrixCoupling 1 N)) := by
  letI : Unique {w : V // w ≠ b} :=
    { default := ⟨a, hab⟩
      uniq := fun x => Subtype.ext ((huniv x.1).resolve_right x.2) }
  have hstep :
      Matrix.reindex (twoSiteEquiv A hab huniv) (twoSiteEquiv A hab huniv)
          (layerMatrixCoupling 1 N) =
        leafTransport A b (layerMatrixCoupling
          (Matrix.reindex
            (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm
            (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm
            (1 : Matrix (A a) (A a) ℂ)) N) :=
    rfl
  have hone :
      Matrix.reindex
          (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm
          (Equiv.piUnique (fun w : {w : V // w ≠ b} => A w.1)).symm
          (1 : Matrix (A a) (A a) ℂ) = 1 :=
    Matrix.submatrix_one_equiv _
  rw [hstep, hone]
  exact isSiteSupported_leafTransport_newSite (A := A) b N

end

end GaloisForLFunctions.HTGeometry
