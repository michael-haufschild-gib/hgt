import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect

/-!
# Shilov envelope-correlation law: algebraic core

This module formalizes the unconditional linear-algebraic core of the Shilov
envelope-correlation law. Relational representatives are sequences coherent modulo the joins of
vertex submodules and their transported successors. Their mismatch defines a class in degree-one
migration cohomology. The main theorem proves the resulting short exact sequence.

No operator-system, positivity, topology, closed-range, or Shilov-minimality assertion is encoded
as an axiom or structure field.
-/

open Function

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {V W : Type v}
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup W] [Module 𝕜 W]

/-- Minimal target submodule containing the target boundary and transported source boundary. -/
def edgeJoin (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W) : Submodule 𝕜 W :=
  Jtarget ⊔ Jsource.map f

theorem target_le_edgeJoin (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W) :
    Jtarget ≤ edgeJoin f Jsource Jtarget :=
  le_sup_left

theorem transported_le_edgeJoin (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget : Submodule 𝕜 W) :
    Jsource.map f ≤ edgeJoin f Jsource Jtarget :=
  le_sup_right

theorem edgeJoin_le_iff (f : V →ₗ[𝕜] W) (Jsource : Submodule 𝕜 V)
    (Jtarget N : Submodule 𝕜 W) :
    edgeJoin f Jsource Jtarget ≤ N ↔
      Jtarget ≤ N ∧ Jsource.map f ≤ N := by
  exact sup_le_iff

theorem edgeJoin_eq_target_iff_escapeFree (f : V →ₗ[𝕜] W)
    (Jsource : Submodule 𝕜 V) (Jtarget : Submodule 𝕜 W) :
    edgeJoin f Jsource Jtarget = Jtarget ↔
      EscapeFree f Jsource Jtarget := by
  rw [edgeJoin, sup_eq_left]
  rfl

section Migration

variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]

/-- Edge join in an inverse path. -/
def migrationEdge (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (n : ℕ) : Submodule 𝕜 (A n) :=
  edgeJoin (bond n) (J (n + 1)) (J n)

theorem vertex_le_migrationEdge
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (n : ℕ) :
    J n ≤ migrationEdge A bond J n :=
  le_sup_left

theorem transported_le_migrationEdge
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) (n : ℕ) :
    (J (n + 1)).map (bond n) ≤ migrationEdge A bond J n :=
  le_sup_right

/-- Vertex perturbations have edge-valued mismatch. -/
def migrationDifference
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    (∀ n, J n) →ₗ[𝕜] (∀ n, migrationEdge A bond J n) where
  toFun j n :=
    ⟨bond n (j (n + 1)) - j n, by
      apply (migrationEdge A bond J n).sub_mem
      · exact (transported_le_migrationEdge A bond J n)
          (Submodule.mem_map_of_mem (j (n + 1)).2)
      · exact (vertex_le_migrationEdge A bond J n) (j n).2⟩
  map_add' x y := by
    funext n
    apply Subtype.ext
    change bond n (x (n + 1) + y (n + 1)) - (x n + y n) =
      (bond n (x (n + 1)) - x n) + (bond n (y (n + 1)) - y n)
    rw [map_add]
    abel
  map_smul' c x := by
    funext n
    apply Subtype.ext
    change bond n (c • x (n + 1)) - c • x n =
      c • (bond n (x (n + 1)) - x n)
    simp only [map_smul, smul_sub]

/-- Algebraic degree-one migration cohomology. -/
abbrev MigrationCohomologyOne
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) : Type v :=
  (∀ n, migrationEdge A bond J n) ⧸
    LinearMap.range (migrationDifference A bond J)

/-- Sequences satisfying the envelope-correlation condition. -/
abbrev RelationalRepresentative
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :=
  compatibleModuloSubmodule A bond (migrationEdge A bond J)

/-- Coordinatewise vertex-boundary perturbations inside relational representatives. -/
def relationalVertexProductSubmodule
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    Submodule 𝕜 (RelationalRepresentative A bond J) :=
  (productSubmodule A J).comap
    (compatibleModuloSubmodule A bond (migrationEdge A bond J)).subtype

/-- Compatible correlation classes modulo changes of vertex representatives. -/
abbrev RelationalClassSpace
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) : Type v :=
  RelationalRepresentative A bond J ⧸
    relationalVertexProductSubmodule A bond J

/-- Edge-valued mismatch of a relational representative. -/
abbrev relationalBoundary
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :=
  representativeBoundary A bond (migrationEdge A bond J)

/-- Connecting map from relational classes to migration cohomology. -/
def migrationConnectingMap
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    RelationalClassSpace A bond J →ₗ[𝕜]
      MigrationCohomologyOne A bond J :=
  (relationalVertexProductSubmodule A bond J).mapQ
    (LinearMap.range (migrationDifference A bond J))
    (relationalBoundary A bond J) (by
      intro x hx
      change x.1 ∈ productSubmodule A J at hx
      rw [Submodule.mem_pi] at hx
      let j : ∀ n, J n :=
        fun n => ⟨x.1 n, hx n (Set.mem_univ n)⟩
      refine ⟨j, ?_⟩
      funext n
      apply Subtype.ext
      rfl)

/-- Coherent ambient sequences define relational classes. -/
def coherentRelationalClassMap
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    InverseLimit A bond →ₗ[𝕜] RelationalClassSpace A bond J :=
  (relationalVertexProductSubmodule A bond J).mkQ.comp
    (coherentRepresentative A bond (migrationEdge A bond J))

/-- Canonical comparison from the local boundary quotient to correlation classes. -/
def localMigrationComparison
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    LocalBoundaryQuotient A bond J →ₗ[𝕜]
      RelationalClassSpace A bond J :=
  (inverseLimitBoundarySubmodule A bond J).liftQ
    (coherentRelationalClassMap A bond J) (by
      intro x hx
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk
        (coherentRepresentative A bond (migrationEdge A bond J) x) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change x.1 ∈ productSubmodule A J at hx
      exact hx)

theorem localMigrationComparison_injective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    Function.Injective (localMigrationComparison A bond J) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_bot]
    induction y using Submodule.Quotient.induction_on with
    | _ x =>
      change coherentRelationalClassMap A bond J x = 0 at hy
      change Submodule.Quotient.mk
        (coherentRepresentative A bond (migrationEdge A bond J) x) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      rw [Submodule.Quotient.mk_eq_zero]
      change x.1 ∈ productSubmodule A J
      exact hy
  · exact bot_le

/-- Exactness at relational classes. -/
theorem localMigrationSequence_exact
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n)) :
    Function.Exact (localMigrationComparison A bond J)
      (migrationConnectingMap A bond J) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ b =>
    constructor
    · intro hy
      change Submodule.Quotient.mk (relationalBoundary A bond J b) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      rcases hy with ⟨j, hj⟩
      let a : ∀ n, A n := fun n => b.1 n - j n
      have hcoh : ∀ n, bond n (a (n + 1)) = a n := by
        intro n
        have hn := congrFun hj n
        have hn' := congrArg Subtype.val hn
        change bond n (j (n + 1)) - j n =
          bond n (b.1 (n + 1)) - b.1 n at hn'
        change bond n (b.1 (n + 1) - j (n + 1)) = b.1 n - j n
        rw [map_sub]
        rw [sub_eq_sub_iff_add_eq_add]
        rw [sub_eq_sub_iff_add_eq_add] at hn'
        simpa only [add_comm] using hn'.symm
      have hker : inverseDifference A bond a = 0 := by
        funext n
        change a n - bond n (a (n + 1)) = 0
        rw [hcoh]
        exact sub_self _
      let aLim : InverseLimit A bond := ⟨a, hker⟩
      refine ⟨Submodule.Quotient.mk aLim, ?_⟩
      change Submodule.Quotient.mk
        (coherentRepresentative A bond (migrationEdge A bond J) aLim) =
          Submodule.Quotient.mk b
      rw [Submodule.Quotient.eq]
      change (fun n => a n - b.1 n) ∈ productSubmodule A J
      rw [Submodule.mem_pi]
      intro n _
      change b.1 n - (j n : A n) - b.1 n ∈ J n
      convert (J n).neg_mem (j n).2 using 1
      abel
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with
      | _ a =>
        rw [← hz]
        change Submodule.Quotient.mk
          (relationalBoundary A bond J
            (coherentRepresentative A bond (migrationEdge A bond J) a)) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        have hzero : relationalBoundary A bond J
            (coherentRepresentative A bond (migrationEdge A bond J) a) = 0 := by
          funext n
          apply Subtype.ext
          have hn := congrFun a.property n
          change a.1 n - bond n (a.1 (n + 1)) = 0 at hn
          change bond n (a.1 (n + 1)) - a.1 n = 0
          rw [sub_eq_zero]
          exact (sub_eq_zero.mp hn).symm
        rw [hzero]
        exact (LinearMap.range (migrationDifference A bond J)).zero_mem

/-- Surjective ambient bonds make the connecting map onto. -/
theorem migrationConnectingMap_surjective
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Function.Surjective (migrationConnectingMap A bond J) := by
  classical
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ c =>
    let step : ∀ n, A n → A (n + 1) :=
      fun n x => Classical.choose (hsurj n (x + (c n : A n)))
    let b : ∀ n, A n := fun n => Nat.rec 0 (fun k xk => step k xk) n
    have hstep (n : ℕ) : bond n (step n (b n)) = b n + (c n : A n) :=
      Classical.choose_spec (hsurj n (b n + (c n : A n)))
    have hmod : ∀ n,
        bond n (b (n + 1)) - b n ∈ migrationEdge A bond J n := by
      intro n
      rw [show b (n + 1) = step n (b n) by rfl, hstep]
      simpa only [add_sub_cancel_left] using (c n).2
    let br : RelationalRepresentative A bond J := ⟨b, hmod⟩
    refine ⟨Submodule.Quotient.mk br, ?_⟩
    change Submodule.Quotient.mk (relationalBoundary A bond J br) =
      Submodule.Quotient.mk c
    apply congrArg Submodule.Quotient.mk
    funext n
    apply Subtype.ext
    change bond n (b (n + 1)) - b n = (c n : A n)
    rw [show b (n + 1) = step n (b n) by rfl, hstep]
    exact add_sub_cancel_left _ _

/-- Unconditional algebraic correlation-migration short exact law. -/
theorem localMigrationSequence_shortExact
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    Function.Injective (localMigrationComparison A bond J) ∧
      Function.Exact (localMigrationComparison A bond J)
        (migrationConnectingMap A bond J) ∧
      Function.Surjective (migrationConnectingMap A bond J) :=
  ⟨localMigrationComparison_injective A bond J,
    localMigrationSequence_exact A bond J,
    migrationConnectingMap_surjective A bond J hsurj⟩

end Migration

end BoundaryMigration
end GaloisForLFunctions.HTGeometry
