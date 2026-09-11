import GaloisForLFunctions.HTGeometry.ModuleLengthTower
import GaloisForLFunctions.HTGeometry.DifferentialVariationalBlockEstimate

/-!
# The signed index of two commensurable integral submodules

The slope theory that the boundary pair of the variational building still needs rests on a degree,
and the degree rests on an index: how much bigger one integral lattice is than another.  This leaf
builds that index and proves the two properties that make it a degree.

* **Finiteness.**  `DiffOp.relLength M N` is the length of `N/(M ⊓ N)`.  It is finite as soon as some
  uniformizer power carries `N` into `M` and `N` is finitely generated, because then the layer is a
  finitely generated module killed by a uniformizer power — and such modules have finite length by
  `DiffOp.length_ne_top_of_fg_of_uniformizer_pow_smul_eq_zero`.
* **The cocycle property.**  Measured from a *common* sublattice `Q`, the index
  `relIndex Q M N = length(N/Q) - length(M/Q)` is a cocycle for free.  The content is that it does
  not depend on `Q`, which is `DiffOp.relIndex_base_independent`.

The proof of base independence never intersects two finitely generated modules — which would need a
Noetherian hypothesis on the noncommutative valuation ring.  The common refinement of two base
sublattices `Q₁, Q₂` is instead the *scaling* `π^j Q₁`, which lies inside `Q₁` because `π^j` is
integral and inside `Q₂` by commensurability.  `DiffOp.uniformizerScaleSubmodule` packages that
scaling as the image of a semilinear map, so finite generation is automatic.

Also proved here, because mathlib lacks it: `Module.length_quotient_comap_subtype`, the transport of
a two-step relative length along the canonical identification `↥(comap C.subtype B) ≃ ↥B`.  Together
with `Module.length_quotient_add_length_quotient` it gives
`relLength A B + relLength B D = relLength A D`, the tower additivity the refinement argument runs on.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Transport of a two-step relative length along the canonical identification of a comapped
submodule with the submodule itself. -/
theorem Module.length_quotient_comap_subtype {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A B C : Submodule R M) (hBC : B ≤ C) :
    Module.length R (↥(Submodule.comap C.subtype B) ⧸
        Submodule.comap (Submodule.comap C.subtype B).subtype (Submodule.comap C.subtype A)) =
      Module.length R (↥B ⧸ Submodule.comap B.subtype A) := by
  refine _root_.Module.length_eq_of_linearEquiv
    (Submodule.Quotient.equiv _ _ (Submodule.comapSubtypeEquivOfLe hBC) ?_)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨⟨y.1, hBC y.2⟩, y.2⟩, hy, rfl⟩

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Inner conjugation of the valuation ring is surjective. -/
instance DiffOp.ringHomSurjective_innerCompletedPseudoDiffOpIntegerEquiv
    (a : (DiffOp.CompletedPseudoDiffOp K)ˣ) :
    RingHomSurjective (DiffOp.innerCompletedPseudoDiffOpIntegerEquiv a).toRingHom :=
  ⟨(DiffOp.innerCompletedPseudoDiffOpIntegerEquiv a).surjective⟩

/-- The `π^k`-scaling of an integral submodule of the coordinate space. -/
def DiffOp.uniformizerScaleSubmodule {r : ℕ} (k : ℕ)
    (M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
  Submodule.map (DiffOp.leftMulCompletedPseudoIntegerVecSemilinearMap
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ))) M

theorem DiffOp.uniformizer_smul_mem_uniformizerScaleSubmodule {r : ℕ} (k : ℕ)
    (M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K))
    {v : Fin r → DiffOp.CompletedPseudoDiffOp K} (hv : v ∈ M) :
    ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈
      DiffOp.uniformizerScaleSubmodule k M :=
  ⟨v, hv, rfl⟩

theorem DiffOp.uniformizerScaleSubmodule_le {r : ℕ} (k : ℕ)
    (M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    DiffOp.uniformizerScaleSubmodule k M ≤ M := by
  rintro _ ⟨m, hm, rfl⟩
  exact DiffOp.uniformizer_smul_mem_submodule M k hm

theorem DiffOp.uniformizerScaleSubmodule_fg {r : ℕ} (k : ℕ)
    {M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)} (hM : M.FG) :
    (DiffOp.uniformizerScaleSubmodule k M).FG :=
  hM.map _

theorem DiffOp.uniformizerScaleSubmodule_le_of_smul_mem {r : ℕ} (k : ℕ)
    (M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (h : ∀ v ∈ M, ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ N) :
    DiffOp.uniformizerScaleSubmodule k M ≤ N := by
  rintro _ ⟨m, hm, rfl⟩
  exact h m hm

/-- The length of `N` above `M`: the length of `N/(M ⊓ N)`. -/
def DiffOp.relLength {r : ℕ}
    (M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) : ℕ∞ :=
  Module.length (DiffOp.CompletedPseudoDiffOpInteger (K := K))
    (↥N ⧸ Submodule.comap N.subtype M)

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Finiteness of the relative length.**  If a uniformizer power pushes `N` into `M`, the layer
between them has finite length. -/
theorem DiffOp.relLength_ne_top {r : ℕ}
    (M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) (hN : N.FG) (k : ℕ)
    (hk : ∀ v ∈ N, ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ M) :
    DiffOp.relLength M N ≠ ⊤ := by
  classical
  haveI : Module.Finite (DiffOp.CompletedPseudoDiffOpInteger (K := K)) ↥N :=
    ⟨(Submodule.fg_top N).2 hN⟩
  haveI : Module.Finite (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (↥N ⧸ Submodule.comap N.subtype M) :=
    Module.Finite.quotient _ _
  have hfg : (⊤ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (↥N ⧸ Submodule.comap N.subtype M)).FG := Module.finite_def.mp inferInstance
  have hkill : ∀ v ∈ (⊤ : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (↥N ⧸ Submodule.comap N.subtype M)),
      (DiffOp.uniformizerInteger (K := K)) ^ k • v = 0 := by
    intro v _
    induction v using Submodule.Quotient.induction_on with
    | H x =>
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      show ((DiffOp.uniformizerInteger (K := K) ^ k • x : ↥N) :
        Fin r → DiffOp.CompletedPseudoDiffOp K) ∈ M
      rw [Submodule.coe_smul]
      have hcoe : ((DiffOp.uniformizerInteger (K := K) ^ k :
            DiffOp.CompletedPseudoDiffOpInteger (K := K)) :
            DiffOp.CompletedPseudoDiffOp K) • ((x : Fin r → DiffOp.CompletedPseudoDiffOp K)) =
          ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (k : ℤ) :
            (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • (x : Fin r →
              DiffOp.CompletedPseudoDiffOp K) := by
        rw [DiffOp.coe_uniformizerInteger_pow]
      rw [show (DiffOp.uniformizerInteger (K := K) ^ k) •
          ((x : Fin r → DiffOp.CompletedPseudoDiffOp K)) = _ from hcoe]
      exact hk _ x.2
  have hlen := DiffOp.length_ne_top_of_fg_of_uniformizer_pow_smul_eq_zero (K := K) k _ hfg hkill
  rwa [_root_.Module.length_eq_of_linearEquiv (Submodule.topEquiv)] at hlen

/-- **Relative length is additive along a tower.** -/
theorem DiffOp.relLength_tower {r : ℕ}
    (A B D : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) (hAB : A ≤ B) (hBD : B ≤ D) :
    DiffOp.relLength A B + DiffOp.relLength B D = DiffOp.relLength A D := by
  have key := _root_.Module.length_quotient_add_length_quotient
    (Submodule.comap D.subtype A) (Submodule.comap D.subtype B) (Submodule.comap_mono hAB)
  rw [DiffOp.relLength, DiffOp.relLength, DiffOp.relLength, ← key,
    Module.length_quotient_comap_subtype A B D hBD]

/-- The signed index of `M` and `N` measured from a common sublattice `Q`. -/
def DiffOp.relIndex {r : ℕ}
    (Q M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) : ℤ :=
  ((DiffOp.relLength Q N).toNat : ℤ) - ((DiffOp.relLength Q M).toNat : ℤ)

/-- The index measured from a common sublattice is a cocycle, by construction. -/
theorem DiffOp.relIndex_add {r : ℕ}
    (Q M N P : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    DiffOp.relIndex Q M N + DiffOp.relIndex Q N P = DiffOp.relIndex Q M P := by
  simp only [DiffOp.relIndex]
  ring

@[simp] theorem DiffOp.relIndex_self {r : ℕ}
    (Q M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    DiffOp.relIndex Q M M = 0 := by
  simp [DiffOp.relIndex]

theorem DiffOp.relIndex_swap {r : ℕ}
    (Q M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    DiffOp.relIndex Q N M = -DiffOp.relIndex Q M N := by
  simp only [DiffOp.relIndex]
  ring

/-- **Refining the base sublattice does not change the index.** -/
theorem DiffOp.relIndex_of_le {r : ℕ}
    (Q' Q M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hQ' : Q' ≤ Q) (hQM : Q ≤ M) (hQN : Q ≤ N)
    (hfin : DiffOp.relLength Q' Q ≠ ⊤)
    (hfinM : DiffOp.relLength Q M ≠ ⊤) (hfinN : DiffOp.relLength Q N ≠ ⊤) :
    DiffOp.relIndex Q' M N = DiffOp.relIndex Q M N := by
  have htowM := DiffOp.relLength_tower Q' Q M hQ' hQM
  have htowN := DiffOp.relLength_tower Q' Q N hQ' hQN
  simp only [DiffOp.relIndex, ← htowM, ← htowN,
    ENat.toNat_add hfin hfinM, ENat.toNat_add hfin hfinN]
  push_cast
  ring

theorem DiffOp.uniformizerScaleSubmodule_antitone {r : ℕ} {k k' : ℕ} (h : k ≤ k')
    (M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) :
    DiffOp.uniformizerScaleSubmodule k' M ≤ DiffOp.uniformizerScaleSubmodule k M := by
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (((k' - k : ℕ) : ℕ) : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • m,
    DiffOp.uniformizer_smul_mem_submodule M (k' - k) hm, ?_⟩
  show ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k : ℕ) : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
      (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (((k' - k : ℕ) : ℕ) : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • m) = _
  rw [smul_smul, ← Units.val_mul, ← zpow_add,
    show ((k : ℕ) : ℤ) + (((k' - k : ℕ) : ℕ) : ℤ) = ((k' : ℕ) : ℤ) from by omega]
  rfl

/-- Finiteness of the layer above a uniformizer scaling. -/
theorem DiffOp.relLength_uniformizerScale_ne_top {r : ℕ} (k j : ℕ)
    (M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) (hN : N.FG)
    (hj : ∀ v ∈ N, ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (j : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v ∈ M) :
    DiffOp.relLength (DiffOp.uniformizerScaleSubmodule k M) N ≠ ⊤ := by
  refine DiffOp.relLength_ne_top _ N hN (k + j) fun v hv => ?_
  have hstep : ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k + j : ℕ) : ℤ) :
      (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v =
      ((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((k : ℕ) : ℤ) :
        (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) •
        (((DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ ((j : ℕ) : ℤ) :
          (DiffOp.CompletedPseudoDiffOp K)ˣ) : DiffOp.CompletedPseudoDiffOp K) • v) := by
    rw [smul_smul, ← Units.val_mul, ← zpow_add,
      show ((k : ℕ) : ℤ) + ((j : ℕ) : ℤ) = ((k + j : ℕ) : ℤ) from by push_cast; ring]
  rw [hstep]
  exact DiffOp.uniformizer_smul_mem_uniformizerScaleSubmodule k M (hj v hv)

/-- Finiteness of the layer of a module above its own uniformizer scaling. -/
theorem DiffOp.relLength_self_uniformizerScale_ne_top {r : ℕ} (k : ℕ)
    (M : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K)) (hM : M.FG) :
    DiffOp.relLength (DiffOp.uniformizerScaleSubmodule k M) M ≠ ⊤ :=
  DiffOp.relLength_ne_top _ M hM k fun _ hv =>
    DiffOp.uniformizer_smul_mem_uniformizerScaleSubmodule k M hv

/-- **The index does not depend on the base sublattice.** -/
theorem DiffOp.relIndex_base_independent {r : ℕ}
    (Q₁ Q₂ M N : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
      (Fin r → DiffOp.CompletedPseudoDiffOp K))
    (hQ₁ : Q₁.FG) (hQ₂ : Q₂.FG) (hM : M.FG) (hN : N.FG)
    (hQ₁M : Q₁ ≤ M) (hQ₁N : Q₁ ≤ N) (hQ₂M : Q₂ ≤ M) (hQ₂N : Q₂ ≤ N)
    (hMQ₁ : (M : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
      Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        (Q₁ : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)))
    (hNQ₁ : (N : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
      Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        (Q₁ : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)))
    (hMQ₂ : (M : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
      Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        (Q₂ : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)))
    (hNQ₂ : (N : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) ⊆
      Submodule.span (DiffOp.CompletedPseudoDiffOp K)
        (Q₂ : Set (Fin r → DiffOp.CompletedPseudoDiffOp K))) :
    DiffOp.relIndex Q₁ M N = DiffOp.relIndex Q₂ M N := by
  classical
  obtain ⟨j, hj⟩ := DiffOp.exists_uniformizer_smul_le Q₂ Q₁ hQ₁
    (fun v hv => hMQ₂ (hQ₁M hv))
  obtain ⟨a, ha⟩ := DiffOp.exists_uniformizer_smul_le Q₁ Q₂ hQ₂
    (fun v hv => hMQ₁ (hQ₂M hv))
  obtain ⟨mQ₁, hmQ₁⟩ := DiffOp.exists_uniformizer_smul_le Q₁ M hM hMQ₁
  obtain ⟨nQ₁, hnQ₁⟩ := DiffOp.exists_uniformizer_smul_le Q₁ N hN hNQ₁
  obtain ⟨mQ₂, hmQ₂⟩ := DiffOp.exists_uniformizer_smul_le Q₂ M hM hMQ₂
  obtain ⟨nQ₂, hnQ₂⟩ := DiffOp.exists_uniformizer_smul_le Q₂ N hN hNQ₂
  set Q₃ := DiffOp.uniformizerScaleSubmodule j Q₁ with hQ₃
  have hQ₃Q₁ : Q₃ ≤ Q₁ := DiffOp.uniformizerScaleSubmodule_le j Q₁
  have hQ₃Q₂ : Q₃ ≤ Q₂ := DiffOp.uniformizerScaleSubmodule_le_of_smul_mem j Q₁ Q₂ hj
  have h1 : DiffOp.relIndex Q₃ M N = DiffOp.relIndex Q₁ M N :=
    DiffOp.relIndex_of_le Q₃ Q₁ M N hQ₃Q₁ hQ₁M hQ₁N
      (DiffOp.relLength_self_uniformizerScale_ne_top j Q₁ hQ₁)
      (DiffOp.relLength_ne_top Q₁ M hM mQ₁ hmQ₁)
      (DiffOp.relLength_ne_top Q₁ N hN nQ₁ hnQ₁)
  have h2 : DiffOp.relIndex Q₃ M N = DiffOp.relIndex Q₂ M N :=
    DiffOp.relIndex_of_le Q₃ Q₂ M N hQ₃Q₂ hQ₂M hQ₂N
      (DiffOp.relLength_uniformizerScale_ne_top j a Q₁ Q₂ hQ₂ ha)
      (DiffOp.relLength_ne_top Q₂ M hM mQ₂ hmQ₂)
      (DiffOp.relLength_ne_top Q₂ N hN nQ₂ hnQ₂)
  rw [← h1, h2]

end

end GaloisForLFunctions.HTGeometry
