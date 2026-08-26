import GaloisForLFunctions.RHTower.ResidualReplicaOptimalDesignTransportLaw
import GaloisForLFunctions.HTGeometry.PolynomialCircuitReplicaHilbertLaw
import GaloisForLFunctions.HTGeometry.HaferkampContinuousCircuitImageCompactness

/-!
# Polynomial residual rank for the complete continuous circuit image

Every subfamily of the exact-depth continuous two-qubit circuit image retains
the polynomial occupied-replica rank bound after canonical coordinate
reindexing and scalar-return excision.  This permits an arbitrarily fine
finite internal net without paying its cardinality in the coarea budget.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinate reindexing preserves occupied replica rank exactly. -/
theorem finrank_replicaTargetSpan_reindex
    {C alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : alpha ≃ beta) (r : ℕ) (target : C → alpha → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r
        (fun c b => target c (e.symm b))) =
      Module.finrank ℂ (replicaTargetSpan r target) := by
  let erIndex : (Fin r → alpha) ≃ (Fin r → beta) :=
    Equiv.piCongrRight (fun _ : Fin r => e)
  let er : EuclideanSpace ℂ (Fin r → alpha) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin r → beta) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ erIndex
  have hpure (c : C) : er (finitePureTensorPowerEuclidean r (target c)) =
      finitePureTensorPowerEuclidean r (fun b => target c (e.symm b)) := by
    ext x
    rfl
  have hmap : Submodule.map er.toLinearEquiv.toLinearMap
      (replicaTargetSpan r target) =
        replicaTargetSpan r (fun c b => target c (e.symm b)) := by
    unfold replicaTargetSpan
    rw [Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨u, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, hpure c⟩
    · rintro ⟨c, rfl⟩
      exact ⟨finitePureTensorPowerEuclidean r (target c),
        ⟨c, rfl⟩, hpure c⟩
  have heq := (er.toLinearEquiv.submoduleMap
    (replicaTargetSpan r target)).finrank_eq
  rw [hmap] at heq
  exact heq.symm

end


end GaloisForLFunctions.HTGeometry

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every subfamily of the complete exact-depth circuit image inherits its
polynomial Choi replica-rank ceiling. -/
theorem finrank_replicaTargetSpan_exactCircuitImage_choi_le
    {C : Type*} {n s : ℕ}
    (U : C → Matrix.unitaryGroup (Fin n → Bool) ℂ)
    (hU : ∀ c, U c ∈ TwoQubitArchitecture.circuitImageExact n s)
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r (fun c =>
        (GaloisForLFunctions.RHTower.choiVector
          (U c : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).ofLp)) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  classical
  have hrep : ∀ c, ∃ (A : TwoQubitArchitecture n s)
      (gates : Fin s → Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      A.contraction gates = U c := by
    intro c
    rw [TwoQubitArchitecture.circuitImageExact] at hU
    simp only [Set.mem_iUnion, Set.mem_range] at hU
    exact hU c
  choose A gates hAgates using hrep
  let pos : C → TwoQubitCircuit.twoQubitCircuitArchitectureIndex n s :=
    fun c k => (A c).sites (Fin.rev k)
  let G : C → Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    fun c k => ((A c).gateLift (Fin.rev k) (gates c (Fin.rev k)) :
      Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
  have hG : ∀ c k, TwoQubitCircuit.IsTwoQubitGate
      (pos c k).1 (pos c k).2 (G c k) := by
    intro c k
    exact twoQubitLift_isTwoQubitGate _ _ _ _
  have hprod : ∀ c, (List.ofFn (G c)).prod =
      (U c : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by
    intro c
    let f : Fin s → Matrix.unitaryGroup (Fin n → Bool) ℂ :=
      fun k => (A c).gateLift k (gates c k)
    let val : Matrix.unitaryGroup (Fin n → Bool) ℂ →
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ := fun V => V
    have hcoeprod (l : List (Matrix.unitaryGroup (Fin n → Bool) ℂ)) :
        ((l.prod : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
          (l.map val).prod := by
      induction l with
      | nil => rfl
      | cons V l ih =>
          simp only [List.prod_cons, List.map_cons]
          change (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
              ((l.prod : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
                Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
            (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
              (l.map val).prod
          rw [ih]
    have hword := congrArg Subtype.val (hAgates c)
    change ((A c).contraction (gates c) :
      Matrix.unitaryGroup (Fin n → Bool) ℂ).1 = _ at hword
    rw [TwoQubitArchitecture.contraction] at hword
    change (((List.ofFn f).reverse.prod :
      Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ) = _ at hword
    calc
      (List.ofFn (G c)).prod =
          ((List.ofFn f).reverse.map val).prod := by
        change (List.ofFn (fun k => (f (Fin.rev k) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ))).prod = _
        apply congrArg List.prod
        rw [List.map_reverse, List.map_ofFn]
        exact ofFn_comp_finRev (fun k => val (f k))
      _ = (((List.ofFn f).reverse.prod :
          Matrix.unitaryGroup (Fin n → Bool) ℂ) :
            Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := (hcoeprod _).symm
      _ = _ := hword
  have hbound :=
    TwoQubitCircuit.finrank_replicaTargetSpan_twoQubitCircuitChoi_complete_le
      pos G hG r
  have htarget : (fun c =>
      (GaloisForLFunctions.RHTower.choiVector
        (U c : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).ofLp) =
      (fun c p => (List.ofFn (G c)).prod p.1 p.2 /
        Real.sqrt (Fintype.card (Fin n → Bool))) := by
    funext c p
    rw [hprod c]
    rfl
  rw [← htarget] at hbound
  exact hbound

/-- Canonical finite-coordinate reindexing preserves the exact-depth Choi
replica-rank ceiling. -/
theorem finrank_replicaTargetSpan_exactCircuitImage_reindexedChoi_le
    {C : Type*} {n s : ℕ}
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (hU : ∀ c, U c ∈ TwoQubitArchitecture.circuitImageExact n s)
    (r : ℕ) :
    Module.finrank ℂ (replicaTargetSpan r (fun c =>
        (GaloisForLFunctions.RHTower.choiVector
          (finiteGaussianHermitianPencilReindexedEndpoint (U c) :
            Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin n))))
              (Fin (Fintype.card (FiniteQubitConfiguration (Fin n)))) ℂ)).ofLp)) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  let e := Fintype.equivFin (FiniteQubitConfiguration (Fin n))
  let ep : (FiniteQubitConfiguration (Fin n) ×
      FiniteQubitConfiguration (Fin n)) ≃
      (Fin (Fintype.card (FiniteQubitConfiguration (Fin n))) ×
        Fin (Fintype.card (FiniteQubitConfiguration (Fin n)))) :=
    Equiv.prodCongr e e
  let target := fun c =>
    (GaloisForLFunctions.RHTower.choiVector
      (U c : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)).ofLp
  have hreindex := GaloisForLFunctions.HTGeometry.finrank_replicaTargetSpan_reindex
    ep r target
  have htarget : (fun c =>
      (GaloisForLFunctions.RHTower.choiVector
        (finiteGaussianHermitianPencilReindexedEndpoint (U c) :
          Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin n))))
            (Fin (Fintype.card (FiniteQubitConfiguration (Fin n)))) ℂ)).ofLp) =
      (fun c b => target c (ep.symm b)) := by
    funext c b
    change (Matrix.reindexAlgEquiv ℂ ℂ e
      (U c : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)) b.1 b.2 /
        (Real.sqrt (Fintype.card
          (Fin (Fintype.card (FiniteQubitConfiguration (Fin n))))) : ℂ) =
      (U c : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) (e.symm b.1) (e.symm b.2) /
        (Real.sqrt (Fintype.card
          (FiniteQubitConfiguration (Fin n))) : ℂ)
    simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Fintype.card_fin, Matrix.submatrix_apply]
  rw [htarget, hreindex]
  exact finrank_replicaTargetSpan_exactCircuitImage_choi_le U hU r

/-- Return-excised residual rank has the same exact-depth polynomial ceiling. -/
theorem finrank_physicalResidual_exactCircuitImage_le
    {C : Type*} {n s : ℕ}
    (U : C → Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ)
    (hU : ∀ c, U c ∈ TwoQubitArchitecture.circuitImageExact n s)
    (r : ℕ) :
    Module.finrank ℂ
        (replicaTargetSpan r (physicalUnitaryChoiResidualTarget
          (fun c => finiteGaussianHermitianPencilReindexedEndpoint (U c)))) ≤
      (n * n) ^ s * (r * s + 1) ^ (s * 16) := by
  exact (finrank_physicalUnitaryChoiResidualTarget_le_choi r
    (fun c => finiteGaussianHermitianPencilReindexedEndpoint (U c))).trans
      (finrank_replicaTargetSpan_exactCircuitImage_reindexedChoi_le U hU r)

end

end RHTower
