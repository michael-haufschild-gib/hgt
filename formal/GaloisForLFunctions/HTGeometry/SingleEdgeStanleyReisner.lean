import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Algebra.Prod

/-!
# The Stanley–Reisner boundary of the single-edge complex

The isolated (fully discrete) boundary model glues every vertex axis at a common origin and kills
every product of distinct coordinates.  The next combinatorial type, the first with a genuine face
of positive dimension, is the **single-edge complex** on `n + 2` vertices: one edge `{0, 1}` and
`n` remaining isolated vertices.

Its Stanley–Reisner ring is `F[x₀, …, x_{n+1}] / (xᵢxⱼ : {i,j} ∉ Δ)`.  The single edge `{0,1}` is a
face, so `x₀ x₁` survives; every other product of distinct coordinates dies.  We realize this ring
concretely as the subalgebra of

`MvPolynomial (Fin 2) F × (Fin n → Polynomial F)`

whose members share a common constant term: the free two-variable block carries the edge `{0,1}`,
the `n` one-variable axes carry the isolated vertices, and the gluing identifies all constant terms
at the common origin.

This file builds the ring, its coordinate generators, and the defining incidence relations — the
edge product is nonzero (`{0,1}` is a face) while every nonedge product vanishes — the first
non-discrete input toward the general Hochster strand equivalence.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F : Type*} [Field F] {n : ℕ}

/-- The Stanley–Reisner boundary of the single-edge complex on `n + 2` vertices: a free
two-variable block on the edge `{0,1}` together with `n` isolated one-variable axes, glued at the
common constant term. -/
def singleEdgeBoundarySubring (F : Type*) [Field F] (n : ℕ) :
    Subalgebra F (MvPolynomial (Fin 2) F × (Fin n → Polynomial F)) where
  carrier := {q | ∀ k, (q.2 k).coeff 0 = MvPolynomial.constantCoeff q.1}
  zero_mem' := by intro k; simp
  one_mem' := by intro k; simp
  add_mem' := by
    intro p q hp hq k
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Polynomial.coeff_add, map_add]
    rw [hp k, hq k]
  mul_mem' := by
    intro p q hp hq k
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Polynomial.mul_coeff_zero, map_mul]
    rw [hp k, hq k]
  algebraMap_mem' := by
    intro c k
    simp [Prod.algebraMap_apply, MvPolynomial.algebraMap_eq]

/-- The coordinate of an edge vertex `b ∈ {0,1}`, living in the free two-variable edge block. -/
def singleEdgeX {F : Type*} [Field F] {n : ℕ} (b : Fin 2) :
    singleEdgeBoundarySubring F n :=
  ⟨(MvPolynomial.X b, 0), by intro k; simp⟩

/-- The coordinate of the isolated vertex `k ∈ Fin n` (vertex `k + 2`). -/
def singleEdgeIsoX {F : Type*} [Field F] {n : ℕ} (k : Fin n) :
    singleEdgeBoundarySubring F n :=
  ⟨(0, fun j => if j = k then Polynomial.X else 0), by
    intro j; by_cases h : j = k <;> simp [h]⟩

@[simp]
theorem singleEdgeX_val {F : Type*} [Field F] {n : ℕ} (b : Fin 2) :
    (singleEdgeX (F := F) (n := n) b : MvPolynomial (Fin 2) F × (Fin n → Polynomial F))
      = (MvPolynomial.X b, 0) := rfl

@[simp]
theorem singleEdgeIsoX_val {F : Type*} [Field F] {n : ℕ} (k : Fin n) :
    (singleEdgeIsoX (F := F) k : MvPolynomial (Fin 2) F × (Fin n → Polynomial F))
      = (0, fun j => if j = k then Polynomial.X else 0) := rfl

/-- **The edge `{0,1}` is a face:** the product of its two coordinates is nonzero.  This is the one
surviving product that distinguishes the single-edge complex from the fully discrete one. -/
theorem singleEdgeX_mul_edgeX_ne_zero {F : Type*} [Field F] {n : ℕ} :
    singleEdgeX (F := F) (n := n) 0 * singleEdgeX 1 ≠ 0 := by
  intro h
  have hval : ((singleEdgeX (F := F) (n := n) 0 * singleEdgeX 1 :
      singleEdgeBoundarySubring F n) :
        MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1 = 0 := by
    rw [h]; rfl
  rw [Subalgebra.coe_mul, singleEdgeX_val, singleEdgeX_val, Prod.fst_mul] at hval
  have hne : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) F) ≠ 0 := by
    intro hz
    have := congrArg (MvPolynomial.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) hz
    simp [MvPolynomial.coeff_X'] at this
  exact hne hval

/-- A nonedge `{b, k+2}` between an edge vertex and an isolated vertex: its product vanishes. -/
@[simp]
theorem singleEdgeX_mul_isoX_eq_zero {F : Type*} [Field F] {n : ℕ} (b : Fin 2) (k : Fin n) :
    singleEdgeX (F := F) b * singleEdgeIsoX k = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, singleEdgeX_val, singleEdgeIsoX_val]
  ext <;> simp

/-- A nonedge `{k+2, l+2}` between two distinct isolated vertices: its product vanishes. -/
@[simp]
theorem singleEdgeIsoX_mul_isoX_eq_zero {F : Type*} [Field F] {n : ℕ} {k l : Fin n}
    (hkl : k ≠ l) :
    singleEdgeIsoX (F := F) k * singleEdgeIsoX l = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, singleEdgeIsoX_val, singleEdgeIsoX_val]
  refine Prod.ext (by simp) ?_
  funext j
  by_cases hjk : j = k
  · subst hjk
    simp [hkl]
  · simp [hjk]

/-- The coordinate at each of the `n + 2` vertices, indexed as `Fin 2 ⊕ Fin n`: the two edge
vertices `{0,1}` and the `n` isolated vertices. -/
def singleEdgeVertexX {F : Type*} [Field F] {n : ℕ} :
    Fin 2 ⊕ Fin n → singleEdgeBoundarySubring F n :=
  Sum.elim singleEdgeX singleEdgeIsoX

@[simp]
theorem singleEdgeVertexX_inl {F : Type*} [Field F] {n : ℕ} (b : Fin 2) :
    singleEdgeVertexX (F := F) (n := n) (Sum.inl b) = singleEdgeX b := rfl

@[simp]
theorem singleEdgeVertexX_inr {F : Type*} [Field F] {n : ℕ} (k : Fin n) :
    singleEdgeVertexX (F := F) (Sum.inr k) = singleEdgeIsoX k := rfl

/-- The first Koszul relation of the single-edge coordinate family. -/
def singleEdgeKoszulRelation {F : Type*} [Field F] {n : ℕ}
    (a : Fin 2 ⊕ Fin n → singleEdgeBoundarySubring F n) : singleEdgeBoundarySubring F n :=
  ∑ v, a v * singleEdgeVertexX v

/-- The base-to-component disconnect cycle joining the edge component (via edge vertex `0`) to the
isolated vertex `k`.  The `n` choices of `k` enumerate every non-base connected component of the
single-edge complex. -/
def singleEdgeDisconnectCycle {F : Type*} [Field F] {n : ℕ} (k : Fin n) :
    Fin 2 ⊕ Fin n → singleEdgeBoundarySubring F n :=
  fun v => if v = Sum.inl 0 then singleEdgeIsoX k else 0

/-- **Every base-to-isolated cycle is a first Koszul cycle.**  The single-edge complex on `n + 2`
vertices therefore carries `n` reduced-`H⁰` Hochster classes, one per non-base component, matching
the `n + 1` connected components (reduced `H̃⁰` dimension `n`). -/
theorem singleEdgeKoszulRelation_disconnectCycle {F : Type*} [Field F] {n : ℕ} (k : Fin n) :
    singleEdgeKoszulRelation (singleEdgeDisconnectCycle (F := F) k) = 0 := by
  classical
  rw [singleEdgeKoszulRelation]
  rw [Finset.sum_eq_single (Sum.inl 0)]
  · rw [singleEdgeDisconnectCycle, if_pos rfl, singleEdgeVertexX_inl, mul_comm]
    exact singleEdgeX_mul_isoX_eq_zero 0 k
  · intro v _ hv
    rw [singleEdgeDisconnectCycle, if_neg hv, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end GaloisForLFunctions
