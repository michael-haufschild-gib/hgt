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

/-- The isolated-axis-`k` entry of a vertex coordinate: `X` exactly on the isolated vertex `k`. -/
theorem singleEdgeVertexX_coe_snd {F : Type*} [Field F] {n : ℕ}
    (j : Fin 2 ⊕ Fin n) (k : Fin n) :
    ((singleEdgeVertexX (F := F) j :
        MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).2) k
      = if j = Sum.inr k then Polynomial.X else 0 := by
  cases j with
  | inl b => simp [singleEdgeVertexX]
  | inr m =>
    simp only [singleEdgeVertexX, Sum.elim_inr, singleEdgeIsoX_val]
    by_cases h : k = m
    · subst h; simp
    · rw [if_neg h, if_neg (by simpa [Sum.inr.injEq] using fun hc => h hc.symm)]

/-- The edge-block part of a vertex coordinate: `X b` on edge vertex `b`, zero on isolated
vertices. -/
theorem singleEdgeVertexX_coe_fst {F : Type*} [Field F] {n : ℕ} (j : Fin 2 ⊕ Fin n) :
    (singleEdgeVertexX (F := F) j :
        MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1
      = Sum.elim (fun b => (MvPolynomial.X b : MvPolynomial (Fin 2) F)) (fun _ => 0) j := by
  cases j with
  | inl b => simp [singleEdgeVertexX]
  | inr m => simp [singleEdgeVertexX]

/-- Multiplying a ring element by a vertex coordinate and reading the isolated-axis-`k` linear
coefficient selects the constant coefficient exactly on the isolated vertex `k`. -/
theorem singleEdge_mul_vertexX_snd_coeff_one {F : Type*} [Field F] {n : ℕ}
    (r : singleEdgeBoundarySubring F n) (j : Fin 2 ⊕ Fin n) (k : Fin n) :
    (((r * singleEdgeVertexX j :
        singleEdgeBoundarySubring F n) :
        MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).2 k).coeff 1
      = if j = Sum.inr k
          then ((r : MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).2 k).coeff 0 else 0 := by
  rw [Subalgebra.coe_mul, Prod.snd_mul, Pi.mul_apply, singleEdgeVertexX_coe_snd]
  by_cases h : j = Sum.inr k
  · rw [if_pos h, if_pos h, Polynomial.coeff_mul_X]
  · rw [if_neg h, if_neg h, mul_zero, Polynomial.coeff_zero]

/-- Multiplying a ring element by a vertex coordinate and reading the `x₀` edge coefficient selects
the constant coefficient exactly on the base edge vertex `0`. -/
theorem singleEdge_mul_vertexX_fst_coeff {F : Type*} [Field F] {n : ℕ}
    (r : singleEdgeBoundarySubring F n) (j : Fin 2 ⊕ Fin n) :
    MvPolynomial.coeff (Finsupp.single 0 1)
        ((r * singleEdgeVertexX j :
          singleEdgeBoundarySubring F n) :
          MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1
      = if j = Sum.inl 0
          then MvPolynomial.constantCoeff
            (r : MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1 else 0 := by
  rw [Subalgebra.coe_mul, Prod.fst_mul, singleEdgeVertexX_coe_fst]
  cases j with
  | inl b =>
    rw [Sum.elim_inl]
    by_cases hb : b = 0
    · subst hb
      rw [if_pos rfl, show (Finsupp.single (0 : Fin 2) 1) = 0 + Finsupp.single 0 1 by simp,
        MvPolynomial.coeff_mul_X]
      rfl
    · rw [if_neg (show (Sum.inl b : Fin 2 ⊕ Fin n) ≠ Sum.inl 0 by simp [hb]),
        MvPolynomial.coeff_mul_X',
        if_neg (by rw [Finsupp.mem_support_single]; rintro ⟨h, -⟩; exact hb h)]
  | inr m => simp

/-- The first Koszul boundary submodule (trivial syzygies), written order-free via the
antisymmetrization of an arbitrary coefficient field `c`. -/
def singleEdgeKoszulBoundary {F : Type*} [Field F] {n : ℕ}
    (c : (Fin 2 ⊕ Fin n) → (Fin 2 ⊕ Fin n) → singleEdgeBoundarySubring F n)
    (i : Fin 2 ⊕ Fin n) : singleEdgeBoundarySubring F n :=
  ∑ j, (c i j - c j i) * singleEdgeVertexX j

/-- The reduced-`H⁰` coefficient detector attached to the non-base isolated component `k`: it reads
the isolated-axis-`k` linear coefficient at the base edge vertex, plus the symmetric `x₀` edge
coefficient at the isolated vertex `k`. -/
def singleEdgeH0DetectorAt {F : Type*} [Field F] {n : ℕ} (k : Fin n) :
    ((Fin 2 ⊕ Fin n) → singleEdgeBoundarySubring F n) →ₗ[F] F where
  toFun a :=
    (((a (Sum.inl 0) : singleEdgeBoundarySubring F n) :
        MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).2 k).coeff 1
      + MvPolynomial.coeff (Finsupp.single 0 1)
          ((a (Sum.inr k) : singleEdgeBoundarySubring F n) :
            MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1
  map_add' a b := by
    simp only [Pi.add_apply, Subalgebra.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      Polynomial.coeff_add, MvPolynomial.coeff_add]
    ring
  map_smul' c a := by
    simp only [Pi.smul_apply, Subalgebra.coe_smul, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
      Polynomial.coeff_smul, MvPolynomial.coeff_smul, smul_eq_mul, RingHom.id_apply]
    ring

/-- **Kronecker duality.**  The component detectors form the dual family to the base-to-isolated
disconnect cycles. -/
@[simp]
theorem singleEdgeH0DetectorAt_disconnectCycle {F : Type*} [Field F] {n : ℕ} (k l : Fin n) :
    singleEdgeH0DetectorAt (F := F) k (singleEdgeDisconnectCycle l)
      = if k = l then 1 else 0 := by
  by_cases h : k = l
  · subst h
    simp [singleEdgeH0DetectorAt, singleEdgeDisconnectCycle, singleEdgeIsoX]
  · rw [if_neg h]
    simp [singleEdgeH0DetectorAt, singleEdgeDisconnectCycle, singleEdgeIsoX, h]

/-- **Boundary annihilation.**  Every first Koszul boundary vanishes under every component detector:
the symmetric detector cancels the antisymmetric syzygy. -/
@[simp]
theorem singleEdgeH0DetectorAt_boundary {F : Type*} [Field F] {n : ℕ} (k : Fin n)
    (c : (Fin 2 ⊕ Fin n) → (Fin 2 ⊕ Fin n) → singleEdgeBoundarySubring F n) :
    singleEdgeH0DetectorAt (F := F) k (singleEdgeKoszulBoundary c) = 0 := by
  classical
  have hsnd : ∀ i : Fin 2 ⊕ Fin n,
      (((singleEdgeKoszulBoundary c i :
          singleEdgeBoundarySubring F n) :
          MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).2 k).coeff 1
        = MvPolynomial.constantCoeff
            ((c i (Sum.inr k) - c (Sum.inr k) i :
              singleEdgeBoundarySubring F n) :
              MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1 := by
    intro i
    rw [singleEdgeKoszulBoundary, AddSubmonoidClass.coe_finsetSum, Prod.snd_sum,
      Finset.sum_apply, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (Sum.inr k)]
    · rw [singleEdge_mul_vertexX_snd_coeff_one, if_pos rfl]
      exact (c i (Sum.inr k) - c (Sum.inr k) i).2 k
    · intro j _ hj
      rw [singleEdge_mul_vertexX_snd_coeff_one, if_neg hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hfst : ∀ i : Fin 2 ⊕ Fin n,
      MvPolynomial.coeff (Finsupp.single 0 1)
          ((singleEdgeKoszulBoundary c i :
            singleEdgeBoundarySubring F n) :
            MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1
        = MvPolynomial.constantCoeff
            ((c i (Sum.inl 0) - c (Sum.inl 0) i :
              singleEdgeBoundarySubring F n) :
              MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1 := by
    intro i
    rw [singleEdgeKoszulBoundary, AddSubmonoidClass.coe_finsetSum, Prod.fst_sum,
      MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single (Sum.inl 0)]
    · rw [singleEdge_mul_vertexX_fst_coeff, if_pos rfl]
    · intro j _ hj
      rw [singleEdge_mul_vertexX_fst_coeff, if_neg hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  show (((singleEdgeKoszulBoundary c (Sum.inl 0) :
      singleEdgeBoundarySubring F n) :
      MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).2 k).coeff 1
      + MvPolynomial.coeff (Finsupp.single 0 1)
          ((singleEdgeKoszulBoundary c (Sum.inr k) :
            singleEdgeBoundarySubring F n) :
            MvPolynomial (Fin 2) F × (Fin n → Polynomial F)).1 = 0
  rw [hsnd (Sum.inl 0), hfst (Sum.inr k), Subalgebra.coe_sub, Subalgebra.coe_sub,
    Prod.fst_sub, Prod.fst_sub, map_sub, map_sub]
  ring

/-- **Single-edge Hochster class.**  The base-to-isolated disconnect cycle for component `k` is a
first Koszul cycle that is not a boundary: the single-edge complex carries a nonzero first Koszul
class for every isolated component. -/
theorem singleEdgeDisconnectCycle_not_koszulBoundary {F : Type*} [Field F] {n : ℕ} (k : Fin n) :
    ¬ ∃ c : (Fin 2 ⊕ Fin n) → (Fin 2 ⊕ Fin n) → singleEdgeBoundarySubring F n,
      singleEdgeKoszulBoundary c = singleEdgeDisconnectCycle k := by
  rintro ⟨c, hc⟩
  have h := congrArg (singleEdgeH0DetectorAt (F := F) k) hc
  rw [singleEdgeH0DetectorAt_boundary, singleEdgeH0DetectorAt_disconnectCycle, if_pos rfl] at h
  exact one_ne_zero h.symm

/-- **Full single-edge reduced-`H⁰` family.**  The `n` base-to-isolated disconnect cycles are
linearly independent modulo first Koszul boundaries, so the first Koszul quotient of the single-edge
complex contains the full reduced-`H̃⁰` rank `n`. -/
theorem singleEdgeDisconnectCycle_independent_mod_koszulBoundary {F : Type*} [Field F] {n : ℕ}
    (a : Fin n → F)
    (c : (Fin 2 ⊕ Fin n) → (Fin 2 ⊕ Fin n) → singleEdgeBoundarySubring F n)
    (h : singleEdgeKoszulBoundary c = ∑ l, a l • singleEdgeDisconnectCycle l) :
    ∀ l, a l = 0 := by
  intro l
  have hdet := congrArg (singleEdgeH0DetectorAt (F := F) l) h
  simp only [singleEdgeH0DetectorAt_boundary, map_sum, map_smul,
    singleEdgeH0DetectorAt_disconnectCycle, smul_eq_mul] at hdet
  simpa using hdet.symm

end

end GaloisForLFunctions
