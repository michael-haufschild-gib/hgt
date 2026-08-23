import GaloisForLFunctions.RHTower.DeningerDynSysFrobeniusClopen

/-!
# The Frobenius operators are open and closed maps

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 7.3 (`t9`), last
assertion.

When every section over an affine open is a `ν`-th power — which is what Deninger's setting
supplies, the scheme being integrally closed in a radically closed field — the evaluation of a
section factors through the Frobenius operator,

`eval U (gᶰ) P = eval U g (F_ν P)` ,

so `F_ν` is inducing on each affine trace.  Being injective with open and closed range it is
therefore an open embedding and a closed embedding, hence an open and a closed map.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C] [TopologicalSpace C]

/-- **Deninger, §7.**  Every section over `U` is a `ν`-th power. -/
def DeningerSectionsDivisible (X : Scheme.{u}) (U : X.Opens) (ν : ℕ) : Prop :=
  ∀ f : Γ(X, U), ∃ g : Γ(X, U), g ^ ν = f

/-- The points over `U`, topologized by pulling back along the Frobenius operator. -/
def DeningerCharOverPull (X : Scheme.{u}) (C : Type u) [Field C] (U : X.Opens) (_ν : ℕ) :
    Type u := DeningerCharOver X C U

/-- The two descriptions have the same underlying set. -/
def deningerCharOverPullEquiv (U : X.Opens) (ν : ℕ) :
    DeningerCharOverPull X C U ν ≃ DeningerCharOver X C U := Equiv.refl _

noncomputable instance deningerCharOverPullTopology (U : X.Opens) (ν : ℕ) :
    TopologicalSpace (DeningerCharOverPull X C U ν) :=
  TopologicalSpace.induced
    (fun P : DeningerCharOverPull X C U ν =>
      deningerCharOverFrobenius ν (deningerCharOverPullEquiv U ν P)) inferInstance

variable [ContinuousMul C]

theorem deningerCharOverPull_continuous_toPull (U : X.Opens) {ν : ℕ} (hν : 0 < ν) :
    Continuous (fun P : DeningerCharOver X C U =>
      (deningerCharOverPullEquiv U ν).symm P) := by
  rw [continuous_induced_rng]
  exact deningerCharOverFrobenius_continuous hν U

omit [ContinuousMul C] in
theorem deningerCharOverPull_continuous_ofPull {U : X.Opens} {ν : ℕ} (hν : 0 < ν)
    (hdiv : DeningerSectionsDivisible X U ν) :
    Continuous (fun P : DeningerCharOverPull X C U ν => deningerCharOverPullEquiv U ν P) := by
  rw [continuous_induced_rng]
  refine continuous_pi fun f => ?_
  obtain ⟨g, hg⟩ := hdiv f
  have hfrob : Continuous (fun P : DeningerCharOverPull X C U ν =>
      deningerCharOverFrobenius ν (deningerCharOverPullEquiv U ν P)) := continuous_induced_dom
  have hfun : (fun P : DeningerCharOverPull X C U ν =>
      deningerCharEval U f (deningerCharOverPullEquiv U ν P).val)
      = fun P : DeningerCharOverPull X C U ν =>
        deningerCharEval U g
          (deningerCharOverFrobenius ν (deningerCharOverPullEquiv U ν P)).val := by
    funext P
    rw [← hg, deningerCharEval_pow U g ν _ (deningerCharOverPullEquiv U ν P).mem]
    exact (deningerCharEval_frobenius U g hν (deningerCharOverPullEquiv U ν P).val).symm
  show Continuous fun P : DeningerCharOverPull X C U ν =>
    deningerCharEval U f (deningerCharOverPullEquiv U ν P).val
  rw [hfun]
  exact (deningerCharEval_continuous U g).comp hfrob

/-- **Deninger, Lemma 7.3 (`t9`).**  Under divisibility the Frobenius operator on the trace over
an open subset is inducing. -/
theorem deningerCharOverFrobenius_isInducing {U : X.Opens} {ν : ℕ} (hν : 0 < ν)
    (hdiv : DeningerSectionsDivisible X U ν) :
    Topology.IsInducing (deningerCharOverFrobenius (X := X) (C := C) ν (U := U)) := by
  refine ⟨le_antisymm ?_ ?_⟩
  · exact continuous_iff_le_induced.1 (deningerCharOverFrobenius_continuous hν U)
  · intro a ha
    exact (deningerCharOverPull_continuous_ofPull hν hdiv).isOpen_preimage a ha

omit [TopologicalSpace C] [ContinuousMul C] in
theorem deningerCharOverFrobenius_range {U : X.Opens} {ν : ℕ} (hν : 0 < ν)
    (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    (hroots : DeningerRootsFromSections X U ν) :
    Set.range (deningerCharOverFrobenius (X := X) (C := C) ν (U := U))
      = deningerCharOverKillsRoots U ν := by
  rw [← deningerCharOver_preimage_range hν halg hroots]
  ext Q
  simp only [Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.val, rfl⟩
  · rintro ⟨R, hR⟩
    have hR1 : R.1 ∈ U := by
      have : (deningerCharFrobenius ν R).1 = R.1 := rfl
      rw [hR] at this
      rw [← this]
      exact Q.mem
    exact ⟨⟨R, hR1⟩, Subtype.ext hR⟩

omit [TopologicalSpace C] [ContinuousMul C] in
theorem deningerCharOverFrobenius_injective {U : X.Opens} {ν : ℕ} (hν : 0 < ν)
    (halg : ∀ x : X, IsAlgClosed (X.residueField x)) :
    Function.Injective (deningerCharOverFrobenius (X := X) (C := C) ν (U := U)) := by
  intro P Q h
  exact Subtype.ext (deningerCharFrobenius_injective halg hν (congrArg Subtype.val h))

variable [T1Space C]

/-- **Deninger, Lemma 7.3 (`t9`).**  On the trace over an affine open the Frobenius operator is
an open embedding. -/
theorem deningerCharOverFrobenius_isOpenEmbedding {U : X.Opens} [IsDomain Γ(X, U)] {ν : ℕ}
    (hν : 0 < ν) (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    (hroots : DeningerRootsFromSections X U ν) (hdiv : DeningerSectionsDivisible X U ν) :
    Topology.IsOpenEmbedding (deningerCharOverFrobenius (X := X) (C := C) ν (U := U)) := by
  refine ⟨⟨deningerCharOverFrobenius_isInducing hν hdiv,
    deningerCharOverFrobenius_injective hν halg⟩, ?_⟩
  rw [deningerCharOverFrobenius_range hν halg hroots]
  exact (deningerCharOverKillsRoots_isClopen hν).2

/-- **Deninger, Lemma 7.3 (`t9`).**  On the trace over an affine open the Frobenius operator is
a closed embedding. -/
theorem deningerCharOverFrobenius_isClosedEmbedding {U : X.Opens} [IsDomain Γ(X, U)] {ν : ℕ}
    (hν : 0 < ν) (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    (hroots : DeningerRootsFromSections X U ν) (hdiv : DeningerSectionsDivisible X U ν) :
    Topology.IsClosedEmbedding (deningerCharOverFrobenius (X := X) (C := C) ν (U := U)) := by
  refine ⟨⟨deningerCharOverFrobenius_isInducing hν hdiv,
    deningerCharOverFrobenius_injective hν halg⟩, ?_⟩
  rw [deningerCharOverFrobenius_range hν halg hroots]
  exact (deningerCharOverKillsRoots_isClopen hν).1

omit [TopologicalSpace C] [ContinuousMul C] [T1Space C] in
theorem deningerCharOver_preimage_image {U : X.Opens} {ν : ℕ}
    (W : Set (DeningerCharPoints X C)) :
    (DeningerCharOver.val (X := X) (C := C) (U := U)) ⁻¹'
        (deningerCharFrobenius (X := X) (C := C) ν '' W)
      = (deningerCharOverFrobenius (X := X) (C := C) ν (U := U)) ''
        ((DeningerCharOver.val (X := X) (C := C) (U := U)) ⁻¹' W) := by
  ext Q
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨P, hPW, hPQ⟩
    have hPU : P.1 ∈ U := by
      have : (deningerCharFrobenius ν P).1 = P.1 := rfl
      rw [hPQ] at this
      rw [← this]
      exact Q.mem
    exact ⟨⟨P, hPU⟩, hPW, Subtype.ext hPQ⟩
  · rintro ⟨R, hRW, hRQ⟩
    exact ⟨R.val, hRW, congrArg Subtype.val hRQ⟩

/-- **Deninger, Lemma 7.3 (`t9`).**  The Frobenius operators on `X̂ (C)` are open maps. -/
theorem deningerCharFrobenius_isOpenMap {ν : ℕ} (hν : 0 < ν)
    (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    (hdom : ∀ U : X.affineOpens, IsDomain Γ(X, U.1))
    (hroots : ∀ U : X.affineOpens, DeningerRootsFromSections X U.1 ν)
    (hdiv : ∀ U : X.affineOpens, DeningerSectionsDivisible X U.1 ν) :
    IsOpenMap (deningerCharFrobenius (X := X) (C := C) ν) := by
  intro W hW
  rw [deningerCharPoints_isOpen_iff]
  intro U
  haveI := hdom U
  rw [deningerCharOver_preimage_image]
  exact (deningerCharOverFrobenius_isOpenEmbedding hν halg (hroots U) (hdiv U)).isOpenMap _
    ((deningerCharOverVal_continuous U).isOpen_preimage W hW)

/-- **Deninger, Lemma 7.3 (`t9`).**  The Frobenius operators on `X̂ (C)` are closed maps. -/
theorem deningerCharFrobenius_isClosedMap {ν : ℕ} (hν : 0 < ν)
    (halg : ∀ x : X, IsAlgClosed (X.residueField x))
    (hdom : ∀ U : X.affineOpens, IsDomain Γ(X, U.1))
    (hroots : ∀ U : X.affineOpens, DeningerRootsFromSections X U.1 ν)
    (hdiv : ∀ U : X.affineOpens, DeningerSectionsDivisible X U.1 ν) :
    IsClosedMap (deningerCharFrobenius (X := X) (C := C) ν) := by
  intro A hA
  rw [← isOpen_compl_iff, deningerCharPoints_isOpen_iff]
  intro U
  haveI := hdom U
  rw [Set.preimage_compl, deningerCharOver_preimage_image]
  have hcl := (deningerCharOverFrobenius_isClosedEmbedding hν halg (hroots U)
    (hdiv U)).isClosedMap _ (hA.preimage (deningerCharOverVal_continuous U))
  exact hcl.isOpen_compl

end RHTower
