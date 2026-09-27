import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpThreePartDecomposition

/-!
# The index of two lattices and the degree of a semilinear automorphism

For finitely generated integral submodules `M`, `N` of a finite-dimensional completed skew vector
space with the same skew span, the **index** `DiffOp.latticeIndex M N` is the signed length
`length(N / M ⊓ N) - length(M / M ⊓ N)`.  The valuation ring is Noetherian, so `M ⊓ N` is again finitely
generated and both layers have finite length.

* `DiffOp.layerLength A B = length(B / A ⊓ B)`, additive along towers (`DiffOp.layerLength_tower`) and
  finite when a uniformizer power pushes `B` into `A` (`DiffOp.layerLength_ne_top`).
* `DiffOp.length_eq_of_semilinearEquiv` — module length is invariant under semilinear equivalences over
  a ring automorphism, since length is the Krull dimension of the submodule lattice and a semilinear
  equivalence induces an order isomorphism of submodule lattices.  Consequently a
  uniformizer-semilinear automorphism preserves layer lengths (`DiffOp.layerLength_semilinearImage`)
  and indices (`DiffOp.latticeIndex_semilinearImage`).
* `DiffOp.latticeIndex_eq_of_le` — the index may be computed from any common finite-colength base, so
  it is a cocycle (`DiffOp.latticeIndex_add`).
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

/-- Module length is invariant under semilinear equivalences over a ring automorphism. -/
theorem length_eq_of_semilinearEquiv {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] N) : Module.length R M = Module.length R N := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)

/-- A semilinear automorphism of the ambient module preserves the length of every layer. -/
theorem length_quotient_map_semilinearEquiv {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {σ σ' : R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (e : M ≃ₛₗ[σ] M)
    (A B : Submodule R M) :
    Module.length R (↥(B.map e.toLinearMap) ⧸ Submodule.comap (B.map e.toLinearMap).subtype (A.map e.toLinearMap)) =
      Module.length R (↥B ⧸ Submodule.comap B.subtype A) := by
  let f : ↥B →ₛₗ[σ] ↥(B.map e.toLinearMap) :=
    (e.toLinearMap).restrict (p := B) (q := B.map e.toLinearMap) fun x hx => Submodule.mem_map_of_mem hx
  let g : ↥(B.map e.toLinearMap) →ₛₗ[σ'] ↥B :=
    (e.symm.toLinearMap).restrict (p := B.map e.toLinearMap) (q := B) fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      simpa using hx
  have hf : Submodule.comap B.subtype A ≤
      Submodule.comap f (Submodule.comap (B.map e.toLinearMap).subtype (A.map e.toLinearMap)) := fun x hx =>
    Submodule.mem_map_of_mem (f := e.toLinearMap) hx
  have hg : Submodule.comap (B.map e.toLinearMap).subtype (A.map e.toLinearMap) ≤
      Submodule.comap g (Submodule.comap B.subtype A) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 hy
    change e.symm (y : M) ∈ A
    rw [show (y : M) = e x from hxy.symm, LinearEquiv.symm_apply_apply]
    exact hx
  let F := (Submodule.comap B.subtype A).mapQ _ f hf
  let G := (Submodule.comap (B.map e.toLinearMap).subtype (A.map e.toLinearMap)).mapQ _ g hg
  have hFG : F.comp G = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rw [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
      congr 1
      ext
      exact e.apply_symm_apply _
  have hGF : G.comp F = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.comp_apply, Submodule.mapQ_apply, Submodule.mapQ_apply, LinearMap.id_apply]
      congr 1
      ext
      exact e.symm_apply_apply _
  exact (length_eq_of_semilinearEquiv (LinearEquiv.ofLinear F G hFG hGF)).symm

/-- A uniformizer ring automorphism restricts to the valuation ring. -/
def IsUniformizerRingAut.integerEquiv {ρ : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K}
    (hρ : IsUniformizerRingAut ρ) :
    CompletedPseudoDiffOpInteger (K := K) ≃+* CompletedPseudoDiffOpInteger (K := K) where
  toFun a := ⟨ρ (a : CompletedPseudoDiffOp K), hρ.1 _ a.2⟩
  invFun a := ⟨ρ.symm (a : CompletedPseudoDiffOp K), hρ.2.1 _ a.2⟩
  left_inv a := Subtype.ext (ρ.symm_apply_apply (a : CompletedPseudoDiffOp K))
  right_inv a := Subtype.ext (ρ.apply_symm_apply (a : CompletedPseudoDiffOp K))
  map_mul' a b := Subtype.ext (_root_.map_mul ρ (a : CompletedPseudoDiffOp K) b)
  map_add' a b := Subtype.ext (_root_.map_add ρ (a : CompletedPseudoDiffOp K) b)

theorem IsUniformizerRingAut.coe_integerEquiv {ρ : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K}
    (hρ : IsUniformizerRingAut ρ) (a : CompletedPseudoDiffOpInteger (K := K)) :
    ((hρ.integerEquiv a : CompletedPseudoDiffOpInteger (K := K)) : CompletedPseudoDiffOp K) =
      ρ (a : CompletedPseudoDiffOp K) := rfl

theorem IsUniformizerRingAut.coe_integerEquiv_symm
    {ρ : CompletedPseudoDiffOp K ≃+* CompletedPseudoDiffOp K}
    (hρ : IsUniformizerRingAut ρ) (a : CompletedPseudoDiffOpInteger (K := K)) :
    ((hρ.integerEquiv.symm a : CompletedPseudoDiffOpInteger (K := K)) : CompletedPseudoDiffOp K) =
      ρ.symm (a : CompletedPseudoDiffOp K) := rfl

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

/-- The length of the layer `B / (A ⊓ B)`. -/
def layerLength (A B : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) : ℕ∞ :=
  Module.length (CompletedPseudoDiffOpInteger (K := K)) (↥B ⧸ Submodule.comap B.subtype A)

/-- **Layer lengths are additive along towers.** -/
theorem layerLength_tower {A B D : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hAB : A ≤ B) (hBD : B ≤ D) :
    layerLength A B + layerLength B D = layerLength A D := by
  have key := _root_.Module.length_quotient_add_length_quotient
    (Submodule.comap D.subtype A) (Submodule.comap D.subtype B) (Submodule.comap_mono hAB)
  rw [layerLength, layerLength, layerLength, ← key,
    Module.length_quotient_comap_subtype A B D hBD]

theorem layerLength_self (A : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    layerLength A A = 0 := by
  rw [layerLength, Module.length_eq_zero_iff]
  refine ⟨fun y z => ?_⟩
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.Quotient.eq]
      exact Submodule.sub_mem _ y.2 z.2

/-- **Finiteness of a layer.**  If a uniformizer power pushes a finitely generated `B` into `A`, the
layer between them has finite length. -/
theorem layerLength_ne_top {A B : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hB : B.FG) {k : ℕ} (hk : uniformizerDilate (k : ℤ) B ≤ A) : layerLength A B ≠ ⊤ := by
  classical
  haveI : Module.Finite (CompletedPseudoDiffOpInteger (K := K)) ↥B :=
    ⟨(Submodule.fg_top B).2 hB⟩
  haveI : Module.Finite (CompletedPseudoDiffOpInteger (K := K))
      (↥B ⧸ Submodule.comap B.subtype A) := Module.Finite.quotient _ _
  have hfg : (⊤ : Submodule (CompletedPseudoDiffOpInteger (K := K))
      (↥B ⧸ Submodule.comap B.subtype A)).FG := Module.finite_def.mp inferInstance
  have hkill : ∀ v ∈ (⊤ : Submodule (CompletedPseudoDiffOpInteger (K := K))
      (↥B ⧸ Submodule.comap B.subtype A)), (uniformizerInteger (K := K)) ^ k • v = 0 := by
    intro v _
    induction v using Submodule.Quotient.induction_on with
    | H x =>
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      change ((uniformizerInteger (K := K) ^ k • x : ↥B) : E) ∈ A
      rw [Submodule.coe_smul, integer_smul_eq, coe_uniformizerInteger_pow]
      exact hk (smul_mem_uniformizerDilate (k : ℤ) x.2)
  have hlen := length_ne_top_of_fg_of_uniformizer_pow_smul_eq_zero (K := K) k _ hfg hkill
  rwa [_root_.Module.length_eq_of_linearEquiv (Submodule.topEquiv)] at hlen

/-- A uniformizer-semilinear automorphism preserves layer lengths. -/
theorem layerLength_semilinearImage {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    (A B : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    layerLength (semilinearImage S hS A) (semilinearImage S hS B) = layerLength A B := by
  obtain ⟨ρ, hρ, hSρ⟩ := hS
  letI := RingHomInvPair.of_ringEquiv hρ.integerEquiv
  letI := RingHomInvPair.of_ringEquiv_symm hρ.integerEquiv
  let e : E ≃ₛₗ[(hρ.integerEquiv : CompletedPseudoDiffOpInteger (K := K) →+*
      CompletedPseudoDiffOpInteger (K := K))] E :=
    { toFun := S
      invFun := fun y => S⁻¹ y
      map_add' := _root_.map_add S
      map_smul' := fun a x => by
        rw [integer_smul_eq, integer_smul_eq, hSρ]
        rfl
      left_inv := fun x => S.symm_apply_apply x
      right_inv := fun y => S.apply_symm_apply y }
  have hmap : ∀ C : Submodule (CompletedPseudoDiffOpInteger (K := K)) E,
      C.map e.toLinearMap = semilinearImage S ⟨ρ, hρ, hSρ⟩ C := by
    intro C
    ext y
    rw [Submodule.mem_map, mem_semilinearImage_iff_exists]
    rfl
  rw [layerLength, layerLength, ← hmap A, ← hmap B]
  exact length_quotient_map_semilinearEquiv e A B

theorem semilinearImage_inf {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    (M N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    semilinearImage S hS (M ⊓ N) = semilinearImage S hS M ⊓ semilinearImage S hS N := by
  ext y
  simp only [Submodule.mem_inf, mem_semilinearImage]

theorem semilinearImage_uniformizerSMulAut (k : ℤ)
    (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) :
    semilinearImage (uniformizerSMulAut (K := K) (E := E) k)
      (isUniformizerSemilinear_uniformizerSMulAut k) M = uniformizerDilate k M := by
  ext y
  rw [mem_semilinearImage_iff_exists, mem_uniformizerDilate_iff_exists]
  rfl

/-- `M` is a lattice of the subspace `W`: finitely generated, with skew span `W`. -/
def IsLatticeOf (M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E)
    (W : Submodule (CompletedPseudoDiffOp K) E) : Prop :=
  M.FG ∧ Submodule.span (CompletedPseudoDiffOp K) (M : Set E) = W

namespace IsLatticeOf

variable {M N P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
  {W : Submodule (CompletedPseudoDiffOp K) E}

theorem le_restrictScalars (hM : IsLatticeOf M W) :
    M ≤ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := fun x hx => by
  rw [← hM.2]
  exact Submodule.subset_span hx

theorem exists_uniformizerDilate_le (hM : IsLatticeOf M W) (hN : IsLatticeOf N W) :
    ∃ k : ℕ, uniformizerDilate (k : ℤ) M ≤ N := by
  obtain ⟨k, hk⟩ := exists_nat_le_uniformizerDilate_of_fg (M := N) hM.1 (by
    rw [hN.2]
    exact fun x hx => hM.le_restrictScalars hx)
  exact ⟨k, uniformizerDilate_le_iff.2 hk⟩

theorem inf (hM : IsLatticeOf M W) (hN : IsLatticeOf N W) : IsLatticeOf (M ⊓ N) W := by
  refine ⟨hM.1.of_le inf_le_left, le_antisymm ?_ ?_⟩
  · rw [← hM.2]
    exact Submodule.span_mono inf_le_left
  · obtain ⟨k, hk⟩ := hM.exists_uniformizerDilate_le hN
    have hdil : uniformizerDilate (k : ℤ) M ≤ M := by
      have := uniformizerDilate_antitone M (show (0 : ℤ) ≤ k by positivity)
      rwa [uniformizerDilate_zero] at this
    have hle : uniformizerDilate (k : ℤ) M ≤ M ⊓ N := le_inf hdil hk
    calc W = Submodule.span (CompletedPseudoDiffOp K) (uniformizerDilate (k : ℤ) M : Set E) := by
          rw [span_uniformizerDilate, hM.2]
      _ ≤ Submodule.span (CompletedPseudoDiffOp K) ((M ⊓ N : Submodule _ E) : Set E) :=
          Submodule.span_mono hle

theorem uniformizerDilate' (hM : IsLatticeOf M W) (k : ℤ) :
    IsLatticeOf (uniformizerDilate k M) W :=
  ⟨uniformizerDilate_fg k hM.1, by rw [span_uniformizerDilate, hM.2]⟩

theorem semilinearImage' {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    (hM : IsLatticeOf M W) :
    IsLatticeOf (semilinearImage S hS M) (semilinearSubspaceImage S hS W) :=
  ⟨semilinearImage_fg hM.1, by rw [span_semilinearImage, hM.2]⟩

theorem layerLength_ne_top' (hM : IsLatticeOf M W) (hN : IsLatticeOf N W) :
    layerLength N M ≠ ⊤ := by
  obtain ⟨k, hk⟩ := hM.exists_uniformizerDilate_le hN
  exact DiffOp.layerLength_ne_top hM.1 hk

end IsLatticeOf

/-- The signed index `length(N / M ⊓ N) - length(M / M ⊓ N)`. -/
def latticeIndex (M N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E) : ℤ :=
  ((layerLength (M ⊓ N) N).toNat : ℤ) - ((layerLength (M ⊓ N) M).toNat : ℤ)

/-- **The index from any common base.** -/
theorem latticeIndex_eq_of_le {M N Q : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hQM : Q ≤ M) (hQN : Q ≤ N) (hM : layerLength Q M ≠ ⊤) (hN : layerLength Q N ≠ ⊤) :
    latticeIndex M N = ((layerLength Q N).toNat : ℤ) - ((layerLength Q M).toNat : ℤ) := by
  have hQ : Q ≤ M ⊓ N := le_inf hQM hQN
  have h1 := layerLength_tower hQ (inf_le_left : M ⊓ N ≤ M)
  have h2 := layerLength_tower hQ (inf_le_right : M ⊓ N ≤ N)
  have hfin0 : layerLength Q (M ⊓ N) ≠ ⊤ := fun h => hM (by rw [← h1, h, top_add])
  have hfin1 : layerLength (M ⊓ N) M ≠ ⊤ := fun h => hM (by rw [← h1, h, add_top])
  have hfin2 : layerLength (M ⊓ N) N ≠ ⊤ := fun h => hN (by rw [← h2, h, add_top])
  rw [latticeIndex, ← h1, ← h2, ENat.toNat_add hfin0 hfin1, ENat.toNat_add hfin0 hfin2]
  push_cast
  ring

variable {W : Submodule (CompletedPseudoDiffOp K) E}
  {M N P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}

/-- **The index is a cocycle.** -/
theorem latticeIndex_add (hM : IsLatticeOf M W) (hN : IsLatticeOf N W) (hP : IsLatticeOf P W) :
    latticeIndex M N + latticeIndex N P = latticeIndex M P := by
  have hQ : IsLatticeOf (M ⊓ N ⊓ P) W := (hM.inf hN).inf hP
  have hQM : M ⊓ N ⊓ P ≤ M := inf_le_left.trans inf_le_left
  have hQN : M ⊓ N ⊓ P ≤ N := inf_le_left.trans inf_le_right
  have hQP : M ⊓ N ⊓ P ≤ P := inf_le_right
  rw [latticeIndex_eq_of_le hQM hQN (hM.layerLength_ne_top' hQ) (hN.layerLength_ne_top' hQ),
    latticeIndex_eq_of_le hQN hQP (hN.layerLength_ne_top' hQ) (hP.layerLength_ne_top' hQ),
    latticeIndex_eq_of_le hQM hQP (hM.layerLength_ne_top' hQ) (hP.layerLength_ne_top' hQ)]
  ring

theorem latticeIndex_swap : latticeIndex N M = -latticeIndex M N := by
  rw [latticeIndex, latticeIndex, inf_comm]
  ring

@[simp] theorem latticeIndex_self : latticeIndex M M = 0 := by
  rw [latticeIndex]
  ring

/-- **The index is invariant under uniformizer-semilinear automorphisms.** -/
theorem latticeIndex_semilinearImage {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S) :
    latticeIndex (semilinearImage S hS M) (semilinearImage S hS N) = latticeIndex M N := by
  rw [latticeIndex, latticeIndex, ← semilinearImage_inf, layerLength_semilinearImage,
    layerLength_semilinearImage]

omit [Module (CompletedPseudoDiffOp K) E] in
/-- The first uniformizer-power ideal consists of the elements of positive valuation. -/
theorem mem_completedPseudoDiffOpUniformizerPower_one_iff (x : CompletedPseudoDiffOpInteger (K := K)) :
    x ∈ completedPseudoDiffOpUniformizerPower (K := K) 1 ↔
      (1 : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (x : CompletedPseudoDiffOp K) := by
  have hπ : (completedPseudoDiffOpUniformizerInteger (K := K) : CompletedPseudoDiffOp K) =
      uniformizerZPow (K := K) 1 := by
    rw [completedPseudoDiffOpUniformizerInteger_coe, uniformizerZPow, zpow_one]
  rw [completedPseudoDiffOpUniformizerPower, pow_one, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    change (1 : WithTop ℤ) ≤ completedPseudoDiffOpAddValue
      ((a : CompletedPseudoDiffOp K) * (completedPseudoDiffOpUniformizerInteger (K := K) :
        CompletedPseudoDiffOp K))
    rw [hπ, completedPseudoDiffOpAddValue_mul, completedPseudoDiffOpAddValue_uniformizerZPow]
    have ha := (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).1 a.2
    calc (1 : WithTop ℤ) = 0 + ((1 : ℤ) : WithTop ℤ) := by simp
      _ ≤ completedPseudoDiffOpAddValue (a : CompletedPseudoDiffOp K) + ((1 : ℤ) : WithTop ℤ) :=
        add_le_add ha le_rfl
  · intro hx
    have hint : (x : CompletedPseudoDiffOp K) * uniformizerZPow (K := K) (-1) ∈
        CompletedPseudoDiffOpInteger (K := K) := by
      rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg, completedPseudoDiffOpAddValue_mul,
        completedPseudoDiffOpAddValue_uniformizerZPow]
      generalize completedPseudoDiffOpAddValue (x : CompletedPseudoDiffOp K) = t at hx ⊢
      induction t using WithTop.recTopCoe with
      | top => exact le_top
      | coe n =>
          have hn : (1 : ℤ) ≤ n := by exact_mod_cast hx
          rw [← WithTop.coe_add]
          exact_mod_cast (show (0 : ℤ) ≤ n + -1 by omega)
    refine ⟨⟨_, hint⟩, Subtype.ext ?_⟩
    change (x : CompletedPseudoDiffOp K) * uniformizerZPow (K := K) (-1) *
      (completedPseudoDiffOpUniformizerInteger (K := K) : CompletedPseudoDiffOp K) = x
    rw [hπ, mul_assoc, uniformizerZPow_neg_mul, mul_one]

section Coordinates

variable {d : ℕ} {e : Fin d → E}
  {c : E →ₗ[CompletedPseudoDiffOp K] (Fin d → CompletedPseudoDiffOp K)}

/-- A coordinate family is a basis of its subspace, so its size is the dimension. -/
theorem finrank_eq_of_coordinates (he : ∀ i, e i ∈ W) (hsum : ∀ x ∈ W, ∑ i, c x i • e i = x)
    (hδ : ∀ i j, c (e j) i = (Pi.single j 1 : Fin d → CompletedPseudoDiffOp K) i) :
    Module.finrank (CompletedPseudoDiffOp K) W = d := by
  classical
  have hli : LinearIndependent (CompletedPseudoDiffOp K) e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun y => c y i) hg
    simp only [coordinate_sum_smul hδ, _root_.map_zero, Pi.zero_apply] at this
    exact this
  have hspan : Submodule.span (CompletedPseudoDiffOp K) (Set.range e) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact he i
    · intro x hx
      rw [← hsum x hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]

/-- The layer `Λ / ϖΛ` of a coordinate lattice has length equal to the dimension. -/
theorem layerLength_uniformizerDilate_one_span_range (he : ∀ i, e i ∈ W)
    (hsum : ∀ x ∈ W, ∑ i, c x i • e i = x)
    (hδ : ∀ i j, c (e j) i = (Pi.single j 1 : Fin d → CompletedPseudoDiffOp K) i) :
    layerLength (uniformizerDilate 1
        (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)))
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) = d := by
  classical
  have hcoord : ∀ y ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e),
      ∀ i, c y i ∈ CompletedPseudoDiffOpInteger (K := K) := by
    intro y hy i
    have h0 : y ∈ uniformizerDilate (0 : ℤ)
        (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) := by
      rwa [uniformizerDilate_zero]
    have := ((mem_uniformizerDilate_span_iff he hsum hδ 0 y).1 h0).2 i
    exact (mem_completedPseudoDiffOpInteger_iff_addValue_nonneg _).2 (by exact_mod_cast this)
  have hΛW : ∀ y ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e), y ∈ W := by
    intro y hy
    have h0 : y ∈ uniformizerDilate (0 : ℤ)
        (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) := by
      rwa [uniformizerDilate_zero]
    exact ((mem_uniformizerDilate_span_iff he hsum hδ 0 y).1 h0).1
  let φ : ↥(Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) ≃ₗ[
      CompletedPseudoDiffOpInteger (K := K)] (Fin d → CompletedPseudoDiffOpInteger (K := K)) :=
    { toFun := fun y i => ⟨c y i, hcoord y y.2 i⟩
      invFun := fun v => ⟨∑ i, (v i : CompletedPseudoDiffOp K) • e i,
        sum_smul_mem_span_of_integer he hsum hδ _ fun i => (v i).2⟩
      map_add' := fun y z => by
        funext i
        apply Subtype.ext
        change c ((y : E) + z) i = c y i + c z i
        rw [_root_.map_add, Pi.add_apply]
      map_smul' := fun a y => by
        funext i
        apply Subtype.ext
        change c ((a : CompletedPseudoDiffOp K) • (y : E)) i = (a : CompletedPseudoDiffOp K) * c y i
        rw [c.map_smul, Pi.smul_apply, smul_eq_mul]
      left_inv := fun y => Subtype.ext (hsum y (hΛW y y.2))
      right_inv := fun v => funext fun i => Subtype.ext (coordinate_sum_smul hδ _ i) }
  have hmap : (Submodule.comap
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)).subtype
      (uniformizerDilate 1
        (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)))).map φ.toLinearMap =
      completedPseudoDiffOpUniformizerPowerPi (K := K) (fun _ : Fin d => 1) := by
    ext v
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.coe_subtype]
    change (∑ i, (v i : CompletedPseudoDiffOp K) • e i) ∈ uniformizerDilate 1 _ ↔ _
    rw [mem_uniformizerDilate_span_iff he hsum hδ]
    simp only [coordinate_sum_smul hδ]
    constructor
    · rintro ⟨_, hv⟩ i _
      exact (mem_completedPseudoDiffOpUniformizerPower_one_iff _).2 (by exact_mod_cast hv i)
    · intro hv
      refine ⟨sum_mem_of_coordinates he _, fun i => ?_⟩
      exact_mod_cast (mem_completedPseudoDiffOpUniformizerPower_one_iff _).1 (hv i (Set.mem_univ i))
  rw [layerLength, (Submodule.Quotient.equiv _ _ φ hmap).length_eq,
    completedPseudoDiffOpUniformizerPowerPiQuotient_length]
  simp

end Coordinates

/-- For `A ≤ B`, the index is the length of the layer. -/
theorem latticeIndex_of_le {A B : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (h : A ≤ B) : latticeIndex A B = ((layerLength A B).toNat : ℤ) := by
  rw [latticeIndex, inf_eq_left.2 h, layerLength_self]
  simp

/-- **Second isomorphism theorem for layers.**  If `A ≤ B` and `B ⊓ C ≤ A`, adding `C` to both
does not change the layer. -/
theorem layerLength_sup_right {A B C : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hAB : A ≤ B) (hBC : B ⊓ C ≤ A) : layerLength (A ⊔ C) (B ⊔ C) = layerLength A B := by
  have hinf : B ⊓ (A ⊔ C) = A := by
    rw [sup_comm A C, ← inf_sup_assoc_of_le C hAB]
    exact sup_eq_right.2 hBC
  have hsup : B ⊔ (A ⊔ C) = B ⊔ C := by
    rw [← sup_assoc, sup_eq_left.2 hAB]
  have hcomap : Submodule.comap B.subtype B ⊓ Submodule.comap B.subtype (A ⊔ C) =
      Submodule.comap B.subtype A := by
    ext x
    simp only [Submodule.mem_inf, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨_, h⟩
      have hx : (x : E) ∈ B ⊓ (A ⊔ C) := ⟨x.2, h⟩
      rwa [hinf] at hx
    · intro h
      exact ⟨x.2, Submodule.mem_sup_left h⟩
  have key := (LinearMap.quotientInfEquivSupQuotient B (A ⊔ C)).length_eq
  rw [hcomap] at key
  rw [layerLength, layerLength, key, hsup]

/-- **Layers add over a direct sum.** -/
theorem layerLength_sup_sup {A₁ B₁ A₂ B₂ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) (hB : B₁ ⊓ B₂ = ⊥) :
    layerLength (A₁ ⊔ A₂) (B₁ ⊔ B₂) = layerLength A₁ B₁ + layerLength A₂ B₂ := by
  have hstep1 : layerLength (A₁ ⊔ A₂) (B₁ ⊔ A₂) = layerLength A₁ B₁ :=
    layerLength_sup_right h₁ (by
      calc B₁ ⊓ A₂ ≤ B₁ ⊓ B₂ := inf_le_inf_left _ h₂
        _ = ⊥ := hB
        _ ≤ A₁ := bot_le)
  have hstep2 : layerLength (B₁ ⊔ A₂) (B₁ ⊔ B₂) = layerLength A₂ B₂ := by
    rw [sup_comm B₁ A₂, sup_comm B₁ B₂]
    exact layerLength_sup_right h₂ (by rw [inf_comm, hB]; exact bot_le)
  rw [← layerLength_tower (sup_le_sup_right h₁ _) (sup_le_sup_left h₂ _), hstep1, hstep2]

section Degree

variable [FiniteDimensional (CompletedPseudoDiffOp K) E]

theorem exists_isLatticeOf (W : Submodule (CompletedPseudoDiffOp K) E) :
    ∃ M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, IsLatticeOf M W := by
  classical
  obtain ⟨d, e, c, he, hsum, hδ⟩ := exists_coordinates W
  exact ⟨_, ⟨Finset.univ.image e, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩,
    span_span_range_eq he hsum⟩

/-- **The index of a uniformizer layer is the dimension.** -/
theorem latticeIndex_uniformizerDilate_one (hM : IsLatticeOf M W) :
    latticeIndex M (uniformizerDilate 1 M) = -(Module.finrank (CompletedPseudoDiffOp K) W : ℤ) := by
  classical
  obtain ⟨d, e, c, he, hsum, hδ⟩ := exists_coordinates W
  have hΛ : IsLatticeOf (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) W :=
    ⟨⟨Finset.univ.image e, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩,
      span_span_range_eq he hsum⟩
  have hdilΛ := hΛ.uniformizerDilate' 1
  have hdilM := hM.uniformizerDilate' 1
  have htrans : latticeIndex (uniformizerDilate 1
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)))
      (uniformizerDilate 1 M) =
      latticeIndex (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) M := by
    rw [← semilinearImage_uniformizerSMulAut, ← semilinearImage_uniformizerSMulAut,
      latticeIndex_semilinearImage]
  have hcoc1 := latticeIndex_add hM hΛ hdilΛ
  have hcoc2 := latticeIndex_add hM hdilΛ hdilM
  have hle : uniformizerDilate 1
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e)) ≤
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) := by
    have := uniformizerDilate_antitone
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e))
      (show (0 : ℤ) ≤ 1 by norm_num)
    rwa [uniformizerDilate_zero] at this
  have hΛlayer : latticeIndex (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e))
      (uniformizerDilate 1 (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e))) =
      -(d : ℤ) := by
    rw [latticeIndex_eq_of_le hle le_rfl (hΛ.layerLength_ne_top' hdilΛ)
      (hdilΛ.layerLength_ne_top' hdilΛ), layerLength_self,
      layerLength_uniformizerDilate_one_span_range he hsum hδ]
    simp
  rw [finrank_eq_of_coordinates he hsum hδ]
  rw [← hcoc2, ← hcoc1, hΛlayer, htrans, latticeIndex_swap (M := M)]
  ring

/-- The index of a uniformizer dilation. -/
theorem latticeIndex_uniformizerDilate (hM : IsLatticeOf M W) (k : ℤ) :
    latticeIndex M (uniformizerDilate k M) =
      -k * (Module.finrank (CompletedPseudoDiffOp K) W : ℤ) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have h1 := latticeIndex_add hM (hM.uniformizerDilate' k) (hM.uniformizerDilate' (k + 1))
      have h2 := latticeIndex_uniformizerDilate_one (hM.uniformizerDilate' k)
      rw [uniformizerDilate_uniformizerDilate, add_comm (1 : ℤ)] at h2
      rw [← h1, ih, h2]
      ring
  | pred k ih =>
      have h1 := latticeIndex_add hM (hM.uniformizerDilate' (-k)) (hM.uniformizerDilate' (-k - 1))
      have h2 := latticeIndex_uniformizerDilate_one (hM.uniformizerDilate' (-k - 1))
      rw [uniformizerDilate_uniformizerDilate, show 1 + (-(k : ℤ) - 1) = -k by ring] at h2
      rw [latticeIndex_swap] at h2
      rw [← h1, ih, show -(k : ℤ) - 1 = -(k : ℤ) - 1 from rfl]
      linarith

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- **The index adds over a direct sum of subspaces.** -/
theorem latticeIndex_sup_sup {W₁ W₂ : Submodule (CompletedPseudoDiffOp K) E} (hW : W₁ ⊓ W₂ = ⊥)
    {M₁ N₁ M₂ N₂ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hM₁ : IsLatticeOf M₁ W₁) (hN₁ : IsLatticeOf N₁ W₁) (hM₂ : IsLatticeOf M₂ W₂)
    (hN₂ : IsLatticeOf N₂ W₂) :
    latticeIndex (M₁ ⊔ M₂) (N₁ ⊔ N₂) = latticeIndex M₁ N₁ + latticeIndex M₂ N₂ := by
  have hdisj : ∀ {X Y : Submodule (CompletedPseudoDiffOpInteger (K := K)) E},
      IsLatticeOf X W₁ → IsLatticeOf Y W₂ → X ⊓ Y = ⊥ := by
    intro X Y hX hY
    rw [eq_bot_iff]
    rintro x ⟨hx, hy⟩
    have : x ∈ W₁ ⊓ W₂ := ⟨hX.le_restrictScalars hx, hY.le_restrictScalars hy⟩
    rw [hW] at this
    exact this
  have hQ₁ := hM₁.inf hN₁
  have hQ₂ := hM₂.inf hN₂
  have hLM := layerLength_sup_sup (inf_le_left : M₁ ⊓ N₁ ≤ M₁) (inf_le_left : M₂ ⊓ N₂ ≤ M₂)
    (hdisj hM₁ hM₂)
  have hLN := layerLength_sup_sup (inf_le_right : M₁ ⊓ N₁ ≤ N₁) (inf_le_right : M₂ ⊓ N₂ ≤ N₂)
    (hdisj hN₁ hN₂)
  have f1 := hM₁.layerLength_ne_top' hQ₁
  have f2 := hM₂.layerLength_ne_top' hQ₂
  have f3 := hN₁.layerLength_ne_top' hQ₁
  have f4 := hN₂.layerLength_ne_top' hQ₂
  rw [latticeIndex_eq_of_le (Q := (M₁ ⊓ N₁) ⊔ (M₂ ⊓ N₂))
      (sup_le_sup inf_le_left inf_le_left) (sup_le_sup inf_le_right inf_le_right)
      (by rw [hLM]; exact WithTop.add_ne_top.2 ⟨f1, f2⟩)
      (by rw [hLN]; exact WithTop.add_ne_top.2 ⟨f3, f4⟩),
    hLM, hLN, ENat.toNat_add f1 f2, ENat.toNat_add f3 f4, latticeIndex, latticeIndex]
  push_cast
  ring

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem isLatticeOf_sup {W₁ W₂ : Submodule (CompletedPseudoDiffOp K) E}
    {M₁ M₂ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    (hM₁ : IsLatticeOf M₁ W₁) (hM₂ : IsLatticeOf M₂ W₂) : IsLatticeOf (M₁ ⊔ M₂) (W₁ ⊔ W₂) :=
  ⟨hM₁.1.sup hM₂.1, by
    rw [← hM₁.2, ← hM₂.2]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      exact Submodule.add_mem_sup (Submodule.subset_span hy) (Submodule.subset_span hz)
    · exact sup_le (Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left))
        (Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_right))⟩

variable {S T : E ≃ₗ[ℤ] E}

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem semilinearSubspaceImage_eq_of_forall (hS : IsUniformizerSemilinear (K := K) S)
    (hW : ∀ x ∈ W, S x ∈ W) (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) : semilinearSubspaceImage S hS W = W := by
  ext y
  rw [mem_semilinearSubspaceImage]
  constructor
  · intro hy
    have := hW _ hy
    rwa [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at this
  · exact hW' y

/-- The degree of a uniformizer-semilinear automorphism on a subspace: the index between a lattice
of the subspace and its image. -/
def semilinearDegree (S : E ≃ₗ[ℤ] E) (hS : IsUniformizerSemilinear (K := K) S)
    (W : Submodule (CompletedPseudoDiffOp K) E) : ℤ :=
  latticeIndex (Classical.choose (exists_isLatticeOf W))
    (semilinearImage S hS (Classical.choose (exists_isLatticeOf W)))

/-- **The degree does not depend on the lattice.** -/
theorem semilinearDegree_eq (hS : IsUniformizerSemilinear (K := K) S)
    (hW : ∀ x ∈ W, S x ∈ W) (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) (hM : IsLatticeOf M W) :
    semilinearDegree S hS W = latticeIndex M (semilinearImage S hS M) := by
  have h0 := Classical.choose_spec (exists_isLatticeOf W)
  have hWeq := semilinearSubspaceImage_eq_of_forall hS hW hW'
  have hS0 : IsLatticeOf (semilinearImage S hS (Classical.choose (exists_isLatticeOf W))) W := by
    have := h0.semilinearImage' hS
    rwa [hWeq] at this
  have hSM : IsLatticeOf (semilinearImage S hS M) W := by
    have := hM.semilinearImage' hS
    rwa [hWeq] at this
  have c1 := latticeIndex_add h0 hM hSM
  have c2 := latticeIndex_add h0 hSM hS0
  have htr := latticeIndex_semilinearImage (M := M)
    (N := Classical.choose (exists_isLatticeOf W)) hS
  rw [semilinearDegree, ← c2, ← c1, htr, latticeIndex_swap (M := M)]
  ring

/-- **The degree is additive under composition.** -/
theorem semilinearDegree_mul (hS : IsUniformizerSemilinear (K := K) S)
    (hT : IsUniformizerSemilinear (K := K) T)
    (hSW : ∀ x ∈ W, S x ∈ W) (hSW' : ∀ x ∈ W, S⁻¹ x ∈ W)
    (hTW : ∀ x ∈ W, T x ∈ W) (hTW' : ∀ x ∈ W, T⁻¹ x ∈ W) :
    semilinearDegree (S * T) (hS.mul hT) W = semilinearDegree S hS W + semilinearDegree T hT W := by
  obtain ⟨M, hM⟩ := exists_isLatticeOf W
  have hSTW : ∀ x ∈ W, (S * T) x ∈ W := fun x hx => hSW _ (hTW x hx)
  have hSTW' : ∀ x ∈ W, (S * T)⁻¹ x ∈ W := fun x hx => by
    rw [mul_inv_rev, LinearEquiv.mul_apply]
    exact hTW' _ (hSW' x hx)
  have hTM : IsLatticeOf (semilinearImage T hT M) W := by
    have := hM.semilinearImage' hT
    rwa [semilinearSubspaceImage_eq_of_forall hT hTW hTW'] at this
  have hSM : IsLatticeOf (semilinearImage S hS M) W := by
    have := hM.semilinearImage' hS
    rwa [semilinearSubspaceImage_eq_of_forall hS hSW hSW'] at this
  have hSTM : IsLatticeOf (semilinearImage S hS (semilinearImage T hT M)) W := by
    have := hTM.semilinearImage' hS
    rwa [semilinearSubspaceImage_eq_of_forall hS hSW hSW'] at this
  rw [semilinearDegree_eq (hS.mul hT) hSTW hSTW' hM, semilinearDegree_eq hS hSW hSW' hM,
    semilinearDegree_eq hT hTW hTW' hM, semilinearImage_mul (hT := hS) (hS := hT),
    ← latticeIndex_add hM hSM hSTM, latticeIndex_semilinearImage hS]

/-- The degree of a uniformizer scaling. -/
theorem semilinearDegree_uniformizerSMulAut (k : ℤ) :
    semilinearDegree (uniformizerSMulAut (K := K) (E := E) k)
      (isUniformizerSemilinear_uniformizerSMulAut k) W =
      -k * (Module.finrank (CompletedPseudoDiffOp K) W : ℤ) := by
  obtain ⟨M, hM⟩ := exists_isLatticeOf W
  rw [semilinearDegree_eq _ (fun x hx => W.smul_mem _ hx) (fun x hx => W.smul_mem _ hx) hM,
    semilinearImage_uniformizerSMulAut, latticeIndex_uniformizerDilate hM]

/-- **The degree adds over a stable direct sum.** -/
theorem semilinearDegree_sup (hS : IsUniformizerSemilinear (K := K) S)
    {W₁ W₂ : Submodule (CompletedPseudoDiffOp K) E} (hW : W₁ ⊓ W₂ = ⊥)
    (h₁ : ∀ x ∈ W₁, S x ∈ W₁) (h₁' : ∀ x ∈ W₁, S⁻¹ x ∈ W₁)
    (h₂ : ∀ x ∈ W₂, S x ∈ W₂) (h₂' : ∀ x ∈ W₂, S⁻¹ x ∈ W₂) :
    semilinearDegree S hS (W₁ ⊔ W₂) = semilinearDegree S hS W₁ + semilinearDegree S hS W₂ := by
  obtain ⟨M₁, hM₁⟩ := exists_isLatticeOf W₁
  obtain ⟨M₂, hM₂⟩ := exists_isLatticeOf W₂
  have hS₁ : IsLatticeOf (semilinearImage S hS M₁) W₁ := by
    have := hM₁.semilinearImage' hS
    rwa [semilinearSubspaceImage_eq_of_forall hS h₁ h₁'] at this
  have hS₂ : IsLatticeOf (semilinearImage S hS M₂) W₂ := by
    have := hM₂.semilinearImage' hS
    rwa [semilinearSubspaceImage_eq_of_forall hS h₂ h₂'] at this
  have hsup : ∀ x ∈ W₁ ⊔ W₂, S x ∈ W₁ ⊔ W₂ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [_root_.map_add]
    exact Submodule.add_mem_sup (h₁ y hy) (h₂ z hz)
  have hsup' : ∀ x ∈ W₁ ⊔ W₂, S⁻¹ x ∈ W₁ ⊔ W₂ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [_root_.map_add]
    exact Submodule.add_mem_sup (h₁' y hy) (h₂' z hz)
  rw [semilinearDegree_eq hS hsup hsup' (isLatticeOf_sup hM₁ hM₂), semilinearImage_sup,
    latticeIndex_sup_sup hW hM₁ hS₁ hM₂ hS₂, semilinearDegree_eq hS h₁ h₁' hM₁,
    semilinearDegree_eq hS h₂ h₂' hM₂]

/-- A stable lattice forces degree zero. -/
theorem semilinearDegree_eq_zero_of_stable (hS : IsUniformizerSemilinear (K := K) S)
    (hW : ∀ x ∈ W, S x ∈ W) (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) (hM : IsLatticeOf M W)
    (hSM : semilinearImage S hS M = M) : semilinearDegree S hS W = 0 := by
  rw [semilinearDegree_eq hS hW hW' hM, hSM, latticeIndex_self]

/-- **A uniformly expanded lattice forces positive degree.** -/
theorem semilinearDegree_pos_of_expanding (hS : IsUniformizerSemilinear (K := K) S)
    (hW : ∀ x ∈ W, S x ∈ W) (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) (hW0 : W ≠ ⊥) (hM : IsLatticeOf M W)
    {m : ℕ} (hexp : uniformizerDilate (-1) M ≤ semilinearImage (S ^ m) (hS.pow m) M) :
    0 < semilinearDegree S hS W := by
  have hpow : ∀ n : ℕ, semilinearDegree (S ^ n) (hS.pow n) W = n * semilinearDegree S hS W := by
    intro n
    induction n with
    | zero =>
        rw [semilinearDegree_eq (hS.pow 0) (fun x hx => by rwa [pow_zero])
          (fun x hx => by rwa [pow_zero, inv_one]) hM, semilinearImage_pow_zero, latticeIndex_self]
        simp
    | succ n ih =>
        have hn := semilinearDegree_mul (hS.pow n) hS
          (pow_apply_mem_of_forall hW n) (fun x hx => by
            rw [← inv_pow]
            exact pow_apply_mem_of_forall hW' n x hx) hW hW'
        have heq : semilinearDegree (S ^ (n + 1)) (hS.pow (n + 1)) W =
            semilinearDegree (S ^ n * S) ((hS.pow n).mul hS) W := by
          congr 1
        rw [heq, hn, ih]
        push_cast
        ring
  have hMn : IsLatticeOf (uniformizerDilate (-1) M) W := hM.uniformizerDilate' (-1)
  have hSmM : IsLatticeOf (semilinearImage (S ^ m) (hS.pow m) M) W := by
    have := hM.semilinearImage' (hS.pow m)
    rwa [semilinearSubspaceImage_eq_of_forall (hS.pow m) (pow_apply_mem_of_forall hW m)
      (fun x hx => by rw [← inv_pow]; exact pow_apply_mem_of_forall hW' m x hx)] at this
  have hdeg := semilinearDegree_eq (hS.pow m) (pow_apply_mem_of_forall hW m)
    (fun x hx => by rw [← inv_pow]; exact pow_apply_mem_of_forall hW' m x hx) hM
  have hsplit := latticeIndex_add hM hMn hSmM
  rw [latticeIndex_uniformizerDilate hM, latticeIndex_of_le hexp] at hsplit
  have hdim : 0 < Module.finrank (CompletedPseudoDiffOp K) W :=
    Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hW0)
  have hmdeg : (m : ℤ) * semilinearDegree S hS W ≥ Module.finrank (CompletedPseudoDiffOp K) W := by
    rw [← hpow m, hdeg, ← hsplit]
    have : (0 : ℤ) ≤ ((layerLength (uniformizerDilate (-1) M)
      (semilinearImage (S ^ m) (hS.pow m) M)).toNat : ℤ) := Nat.cast_nonneg _
    linarith
  by_contra hle
  push Not at hle
  have : (m : ℤ) * semilinearDegree S hS W ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hle
  have hdimZ : (0 : ℤ) < Module.finrank (CompletedPseudoDiffOp K) W := by exact_mod_cast hdim
  linarith

end Degree

end

end DiffOp

end GaloisForLFunctions.HTGeometry
