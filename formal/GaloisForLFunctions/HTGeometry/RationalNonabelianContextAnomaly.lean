import GaloisForLFunctions.HTGeometry.ContextOrderPSDHierarchy
import GaloisForLFunctions.HTGeometry.GramRealizationFirewall

/-!
# Rational non-Abelian anomalies at every context order

This file constructs, for every `r`, one exact rational kernel on `r + 4` contexts with three
internal directions per context (presented as a `1 ⊕ 2` direct sum). Every maximal proper
context restriction is positive semidefinite, while the full kernel is not. The same kernel
contains a positive semidefinite two-direction Wilson sector with two triangle loops whose
commutator is nonzero.

Thus arbitrarily high-order positivity obstructions coexist with genuinely noncommuting loop
data in one finite rational construction. No perturbation, approximation, genericity argument,
spectral computation, or external axiom is used.
-/

open Matrix
open scoped ComplexOrder Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 200000
set_option maxRecDepth 4000

/-- Block-diagonal direct sum of two context kernels. -/
def contextBlockSum {I J : Type*} [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (D : Matrix J J ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks A 0 0 D

/-- A complex block-diagonal kernel is positive semidefinite exactly when both blocks are. -/
theorem contextBlockSum_posSemidef_iff {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {A : Matrix I I ℂ} {D : Matrix J J ℂ} :
    (contextBlockSum A D).PosSemidef ↔ A.PosSemidef ∧ D.PosSemidef := by
  constructor
  · intro h
    have hA := h.submatrix (Sum.inl : I → I ⊕ J)
    have hD := h.submatrix (Sum.inr : J → I ⊕ J)
    change A.PosSemidef at hA
    change D.PosSemidef at hD
    exact ⟨hA, hD⟩
  rintro ⟨hA, hD⟩
  obtain ⟨v, hv⟩ := exists_innerGramMatrix_of_posSemidef hA
  obtain ⟨w, hw⟩ := exists_innerGramMatrix_of_posSemidef hD
  let u : I ⊕ J → EuclideanSpace ℂ (I ⊕ J)
    | Sum.inl i => WithLp.toLp 2 (Sum.elim (v i).ofLp (fun _ => 0))
    | Sum.inr j => WithLp.toLp 2 (Sum.elim (fun _ => 0) (w j).ofLp)
  have heq : contextBlockSum A D = innerGramMatrix u := by
    ext x y
    cases x <;> cases y <;>
      simp [contextBlockSum, Matrix.fromBlocks, innerGramMatrix, u,
        PiLp.inner_apply, Fintype.sum_sum_type, hv, hw]
  rw [heq]
  exact posSemidef_innerGramMatrix u

/-- Four-dimensional rational frame producing the noncommuting two-direction sector. -/
def rationalWilsonFrame {r : ℕ} (i : Fin (r + 4)) (a : Fin 2) :
    EuclideanSpace ℂ (Fin 4) :=
  WithLp.toLp 2 <| fun q =>
    if i.val = 2 then
      if a.val = 0 then ![(3 / 5 : ℂ), 0, (4 / 5 : ℂ), 0] q
      else ![0, 0, 0, 1] q
    else if i.val = 3 then
      if a.val = 0 then ![(9 / 25 : ℂ), (12 / 25 : ℂ), (4 / 5 : ℂ), 0] q
      else ![0, 0, 0, 1] q
    else
      if a.val = 0 then ![1, 0, 0, 0] q
      else ![0, 1, 0, 0] q

/-- Positive semidefinite Gram kernel of the rational Wilson frame. -/
def rationalWilsonGram (r : ℕ) :
    Matrix (Fin (r + 4) × Fin 2) (Fin (r + 4) × Fin 2) ℂ :=
  innerGramMatrix fun p => rationalWilsonFrame p.1 p.2

theorem rationalWilsonGram_posSemidef (r : ℕ) :
    (rationalWilsonGram r).PosSemidef :=
  posSemidef_innerGramMatrix _

/-- Link matrix from context `i` to context `j`. -/
def rationalWilsonLink (r : ℕ) (i j : Fin (r + 4)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (rationalWilsonGram r).submatrix (fun a => (i, a)) (fun b => (j, b))

def rationalWilsonA : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(3 / 5 : ℂ), 0; 0, 0]

def rationalWilsonB : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(9 / 25 : ℂ), 0; (12 / 25 : ℂ), 0]

theorem rationalWilsonLink_zero_one (r : ℕ) :
    rationalWilsonLink r 0 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rationalWilsonLink, rationalWilsonGram, innerGramMatrix, rationalWilsonFrame,
      PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_four, Matrix.one_apply,
      Matrix.cons_val] <;> simp only [Matrix.cons_val] <;>
      norm_num [starRingEnd_apply, star_natCast]

theorem rationalWilsonLink_one_two (r : ℕ) :
    rationalWilsonLink r 1 2 = rationalWilsonA := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rationalWilsonLink, rationalWilsonGram, innerGramMatrix, rationalWilsonFrame,
      rationalWilsonA, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_four,
      Matrix.cons_val] <;> simp only [Matrix.cons_val] <;>
      norm_num [starRingEnd_apply, star_natCast]

theorem rationalWilsonLink_two_zero (r : ℕ) :
    rationalWilsonLink r 2 0 = rationalWilsonA := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rationalWilsonLink, rationalWilsonGram, innerGramMatrix, rationalWilsonFrame,
      rationalWilsonA, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_four,
      Matrix.cons_val] <;> simp only [Matrix.cons_val] <;>
      norm_num [starRingEnd_apply, star_natCast]

theorem rationalWilsonLink_one_three (r : ℕ) :
    rationalWilsonLink r 1 3 = rationalWilsonB := by
  have h3 : 3 % (r + 4) = 3 := Nat.mod_eq_of_lt (by omega)
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rationalWilsonLink, rationalWilsonGram, innerGramMatrix, rationalWilsonFrame,
      rationalWilsonB, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_four,
      Matrix.cons_val, h3] <;> simp only [Matrix.cons_val] <;>
      norm_num [starRingEnd_apply, star_natCast]

theorem rationalWilsonLink_three_zero (r : ℕ) :
    rationalWilsonLink r 3 0 = rationalWilsonBᴴ := by
  have h3 : 3 % (r + 4) = 3 := Nat.mod_eq_of_lt (by omega)
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [rationalWilsonLink, rationalWilsonGram, innerGramMatrix, rationalWilsonFrame,
      rationalWilsonB, Matrix.conjTranspose_apply, PiLp.inner_apply, RCLike.inner_apply,
      Fin.sum_univ_four, Matrix.cons_val, h3] <;> simp only [Matrix.cons_val] <;>
      norm_num [starRingEnd_apply, star_natCast]

/-- Wilson product around the triangle `0 → 1 → 2 → 0`. -/
def rationalWilsonLoopX (r : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rationalWilsonLink r 0 1 * rationalWilsonLink r 1 2 * rationalWilsonLink r 2 0

/-- Wilson product around the triangle `0 → 1 → 3 → 0`. -/
def rationalWilsonLoopY (r : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rationalWilsonLink r 0 1 * rationalWilsonLink r 1 3 * rationalWilsonLink r 3 0

/-- The two rational Wilson loops do not commute, at every context order. -/
theorem rationalWilsonLoops_commutator_ne_zero (r : ℕ) :
    rationalWilsonLoopX r * rationalWilsonLoopY r -
      rationalWilsonLoopY r * rationalWilsonLoopX r ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  rw [rationalWilsonLoopX, rationalWilsonLoopY,
    rationalWilsonLink_zero_one, rationalWilsonLink_one_two,
    rationalWilsonLink_two_zero, rationalWilsonLink_one_three,
    rationalWilsonLink_three_zero] at h01
  simp only [rationalWilsonA, rationalWilsonB, Matrix.sub_apply, Matrix.zero_apply,
    Matrix.one_mul] at h01
  simp only [Fin.sum_univ_two, Matrix.mul_apply, Matrix.conjTranspose_apply] at h01
  norm_num [starRingEnd_apply, star_natCast] at h01

/-- Direct sum of the balanced scalar obstruction and rational Wilson Gram sector. -/
def rationalNonabelianContextAnomaly (r : ℕ) :
    Matrix (Fin (r + 4) ⊕ (Fin (r + 4) × Fin 2))
      (Fin (r + 4) ⊕ (Fin (r + 4) × Fin 2)) ℂ :=
  contextBlockSum
    (contextOrderKernel (balancedContextScale (r + 1)))
    (rationalWilsonGram r)

/-- Reindex all three internal directions along a context map. -/
def contextOccurrenceEmbedding {r : ℕ} {K : Type*} (e : K → Fin (r + 4)) :
    K ⊕ (K × Fin 2) → Fin (r + 4) ⊕ (Fin (r + 4) × Fin 2)
  | Sum.inl i => Sum.inl (e i)
  | Sum.inr p => Sum.inr (e p.1, p.2)

/-- The noncommuting Wilson Gram kernel is a principal sector of the same anomaly kernel. -/
theorem rationalNonabelianContextAnomaly_wilsonSector (r : ℕ) :
    (rationalNonabelianContextAnomaly r).submatrix
        (Sum.inr : Fin (r + 4) × Fin 2 →
          Fin (r + 4) ⊕ (Fin (r + 4) × Fin 2)) Sum.inr =
      rationalWilsonGram r := by
  rfl

theorem rationalNonabelianContextAnomaly_submatrix
    {r : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (e : K → Fin (r + 4)) :
    (rationalNonabelianContextAnomaly r).submatrix
        (contextOccurrenceEmbedding e) (contextOccurrenceEmbedding e) =
      contextBlockSum
        ((contextOrderKernel (balancedContextScale (r + 1))).submatrix e e)
        ((rationalWilsonGram r).submatrix
          (fun p : K × Fin 2 => (e p.1, p.2))
          (fun p : K × Fin 2 => (e p.1, p.2))) := by
  ext x y
  cases x <;> cases y <;> rfl

/-- Every maximal proper context of the combined three-direction kernel is positive semidefinite. -/
theorem rationalNonabelianContextAnomaly_every_maximalProper_posSemidef
    (r : ℕ) (e : Fin (r + 3) ↪ Fin (r + 4)) :
    ((rationalNonabelianContextAnomaly r).submatrix
      (contextOccurrenceEmbedding e) (contextOccurrenceEmbedding e)).PosSemidef := by
  rw [rationalNonabelianContextAnomaly_submatrix]
  rw [contextBlockSum_posSemidef_iff]
  exact ⟨balancedContext_every_maximalProperContext_posSemidef (r + 1) e,
    (rationalWilsonGram_posSemidef r).submatrix _⟩

/-- The full combined kernel is not positive semidefinite, at every order. -/
theorem rationalNonabelianContextAnomaly_global_not_posSemidef (r : ℕ) :
    ¬ (rationalNonabelianContextAnomaly r).PosSemidef := by
  intro h
  have hscalar := h.submatrix (Sum.inl : Fin (r + 4) →
    Fin (r + 4) ⊕ (Fin (r + 4) × Fin 2))
  change (contextOrderKernel (ι := Fin (r + 4))
    (balancedContextScale (r + 1))).PosSemidef at hscalar
  let e : Fin (r + 1 + 3) ≃ Fin (r + 4) := finCongr (by omega)
  have hsmall := hscalar.submatrix e
  have heq := contextOrderKernel_submatrix (balancedContextScale (r + 1)) e.toEmbedding
  change ((contextOrderKernel (balancedContextScale (r + 1))).submatrix
    e.toEmbedding e.toEmbedding).PosSemidef at hsmall
  rw [heq] at hsmall
  apply balancedContext_global_not_posSemidef (r + 1)
  exact hsmall

/-- **All-order rational non-Abelian anomaly law.** For every `r`, one explicit rational kernel
on `r + 4` contexts has positive semidefinite restrictions to every maximal proper context, fails
positive semidefiniteness globally, and contains a positive semidefinite principal Wilson sector
with two noncommuting triangle loops. -/
theorem exists_rational_nonabelian_context_anomaly (r : ℕ) :
    (∀ e : Fin (r + 3) ↪ Fin (r + 4),
      ((rationalNonabelianContextAnomaly r).submatrix
        (contextOccurrenceEmbedding e) (contextOccurrenceEmbedding e)).PosSemidef) ∧
    ¬ (rationalNonabelianContextAnomaly r).PosSemidef ∧
    (rationalNonabelianContextAnomaly r).submatrix
        (Sum.inr : Fin (r + 4) × Fin 2 →
          Fin (r + 4) ⊕ (Fin (r + 4) × Fin 2)) Sum.inr = rationalWilsonGram r ∧
    rationalWilsonLoopX r * rationalWilsonLoopY r -
      rationalWilsonLoopY r * rationalWilsonLoopX r ≠ 0 := by
  exact ⟨rationalNonabelianContextAnomaly_every_maximalProper_posSemidef r,
    rationalNonabelianContextAnomaly_global_not_posSemidef r,
    rationalNonabelianContextAnomaly_wilsonSector r,
    rationalWilsonLoops_commutator_ne_zero r⟩

end

end GaloisForLFunctions.HTGeometry
