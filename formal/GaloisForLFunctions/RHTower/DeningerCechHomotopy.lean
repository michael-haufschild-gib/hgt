import GaloisForLFunctions.RHTower.DeningerCechSplit
import Mathlib.Data.Fin.Tuple.Basic
import GaloisForLFunctions.HTGeometry.CechFineAcyclicModule

/-!
# The contracting homotopy of a fine Čech complex in every degree

Multiplying by a partition of unity subordinate to the cover contracts the Čech complex: the
operator that averages a cochain over its first index, each term extended by zero, is a homotopy
between the identity and zero in every positive degree.

The identity is the simplicial computation.  The faces of an index tuple with a prepended index are
the tuple itself, in the zeroth place, and the faces of the original tuple with the index still
prepended elsewhere; so the two composites cancel except for the term carrying the total mass of
the partition, which is one.

* `deningerCechD` : the Čech differential.
* `deningerCechK` : the averaging homotopy.
* `deningerCech_homotopy` : `δK + Kδ = id` in every degree.
* `deningerCech_exact` : hence every cocycle is a coboundary.
-/

namespace RHTower

open Set Topology
open scoped Classical

section CechHomotopy

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- Čech cochains of a cover, as functions of an index tuple. -/
abbrev DeningerCechCochain (X ι : Type*) (q : ℕ) := (Fin (q + 1) → ι) → X → ℝ

/-- The Čech differential: the alternating sum over the faces of the index tuple. -/
noncomputable def deningerCechD {q : ℕ} (c : DeningerCechCochain X ι q) :
    DeningerCechCochain X ι (q + 1) :=
  fun σ x => ∑ r : Fin (q + 2), (-1 : ℝ) ^ (r : ℕ) * c (σ ∘ Fin.succAbove r) x

/-- The contracting homotopy: average over a prepended index against the partition of unity, each
term extended by zero. -/
noncomputable def deningerCechK (U : ι → Set X) (ρ : ι → X → ℝ) {q : ℕ}
    (c : DeningerCechCochain X ι (q + 1)) : DeningerCechCochain X ι q :=
  fun σ x => ∑ k : ι, deningerExtendByZero (U k) (ρ k) (c (Fin.cons k σ)) x

/-- With the support condition the extension by zero is pointwise the product. -/
theorem deningerExtendByZero_apply {U : Set X} {ρ : X → ℝ} (hsupp : tsupport ρ ⊆ U)
    (f : X → ℝ) (x : X) : deningerExtendByZero U ρ f x = ρ x * f x := by
  by_cases hx : x ∈ U
  · exact deningerExtendByZero_eq_of_mem hx
  · rw [deningerExtendByZero_eq_zero hx, deningerExtendByZero_bump_zero hsupp hx, zero_mul]

omit [Fintype ι] in
/-- The zeroth face of a tuple with a prepended index is the tuple itself. -/
theorem deningerFace_zero {q : ℕ} (k : ι) (σ : Fin (q + 1) → ι) :
    (Fin.cons k σ : Fin (q + 2) → ι) ∘ Fin.succAbove 0 = σ := by
  funext s
  simp

omit [Fintype ι] in
/-- The later faces of a tuple with a prepended index keep the prepended index. -/
theorem deningerFace_succ {q : ℕ} (k : ι) (σ : Fin (q + 2) → ι) (r : Fin (q + 2)) :
    (Fin.cons k σ : Fin (q + 3) → ι) ∘ Fin.succAbove r.succ
      = Fin.cons k (σ ∘ Fin.succAbove r) :=
  _root_.HTGeometry.cechFace_succ k σ r

omit [TopologicalSpace X] [Fintype ι] in
/-- The differential of a cochain, evaluated on a tuple with a prepended index, separates the
zeroth face from the rest. -/
theorem deningerCechD_cons {q : ℕ} (c : DeningerCechCochain X ι (q + 1)) (k : ι)
    (σ : Fin (q + 2) → ι) (x : X) :
    deningerCechD c (Fin.cons k σ) x
      = c σ x - ∑ r : Fin (q + 2), (-1 : ℝ) ^ (r : ℕ) * c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
  rw [deningerCechD, Fin.sum_univ_succ]
  have hzero : (Fin.cons k σ : Fin (q + 3) → ι) ∘ Fin.succAbove 0 = σ := deningerFace_zero k σ
  rw [hzero]
  have hrest : ∀ r : Fin (q + 2),
      (-1 : ℝ) ^ ((r.succ : Fin (q + 3)) : ℕ)
          * c ((Fin.cons k σ : Fin (q + 3) → ι) ∘ Fin.succAbove r.succ) x
        = -((-1 : ℝ) ^ (r : ℕ) * c (Fin.cons k (σ ∘ Fin.succAbove r)) x) := by
    intro r
    rw [deningerFace_succ k σ r]
    have hpow : ((r.succ : Fin (q + 3)) : ℕ) = (r : ℕ) + 1 := rfl
    rw [hpow, pow_succ]
    ring
  rw [Finset.sum_congr rfl fun r _ => hrest r, Finset.sum_neg_distrib]
  simp only [Fin.val_zero, pow_zero, one_mul]
  ring

/-- **The averaging operator is a contracting homotopy.**  In every degree the two composites add
up to the identity, because the partition of unity has total mass one. -/
theorem deningerCech_homotopy {U : ι → Set X} {ρ : ι → X → ℝ}
    (hρsupp : ∀ i, tsupport (ρ i) ⊆ U i) (hρsum : ∀ x, ∑ i : ι, ρ i x = 1)
    {q : ℕ} (c : DeningerCechCochain X ι (q + 1)) (σ : Fin (q + 2) → ι) (x : X) :
    deningerCechD (deningerCechK U ρ c) σ x + deningerCechK U ρ (deningerCechD c) σ x = c σ x := by
  have hK : ∀ (d : DeningerCechCochain X ι (q + 2)) (τ : Fin (q + 2) → ι),
      deningerCechK U ρ d τ x = ∑ k : ι, ρ k x * d (Fin.cons k τ) x := by
    intro d τ
    exact Finset.sum_congr rfl fun k _ => deningerExtendByZero_apply (hρsupp k) _ x
  have hK' : ∀ τ : Fin (q + 1) → ι, deningerCechK U ρ c τ x
      = ∑ k : ι, ρ k x * c (Fin.cons k τ) x := fun τ =>
    Finset.sum_congr rfl fun k _ => deningerExtendByZero_apply (hρsupp k) _ x
  have hfirst : deningerCechD (deningerCechK U ρ c) σ x
      = ∑ r : Fin (q + 2), (-1 : ℝ) ^ (r : ℕ)
          * ∑ k : ι, ρ k x * c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
    rw [deningerCechD]
    exact Finset.sum_congr rfl fun r _ => by rw [hK' (σ ∘ Fin.succAbove r)]
  have hsecond : deningerCechK U ρ (deningerCechD c) σ x
      = ∑ k : ι, ρ k x * c σ x
        - ∑ k : ι, ρ k x * ∑ r : Fin (q + 2),
            (-1 : ℝ) ^ (r : ℕ) * c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
    rw [hK (deningerCechD c) σ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [deningerCechD_cons c k σ x, mul_sub]
  rw [hfirst, hsecond]
  have hswap : ∑ r : Fin (q + 2), (-1 : ℝ) ^ (r : ℕ)
        * ∑ k : ι, ρ k x * c (Fin.cons k (σ ∘ Fin.succAbove r)) x
      = ∑ k : ι, ρ k x * ∑ r : Fin (q + 2),
          (-1 : ℝ) ^ (r : ℕ) * c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
    calc ∑ r : Fin (q + 2), (-1 : ℝ) ^ (r : ℕ)
          * ∑ k : ι, ρ k x * c (Fin.cons k (σ ∘ Fin.succAbove r)) x
        = ∑ r : Fin (q + 2), ∑ k : ι,
            (-1 : ℝ) ^ (r : ℕ) * (ρ k x * c (Fin.cons k (σ ∘ Fin.succAbove r)) x) := by
          exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]
      _ = ∑ k : ι, ∑ r : Fin (q + 2),
            (-1 : ℝ) ^ (r : ℕ) * (ρ k x * c (Fin.cons k (σ ∘ Fin.succAbove r)) x) :=
          Finset.sum_comm
      _ = ∑ k : ι, ρ k x * ∑ r : Fin (q + 2),
            (-1 : ℝ) ^ (r : ℕ) * c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ => by ring
  rw [hswap, ← Finset.sum_mul, hρsum x, one_mul]
  ring

/-- **Every cocycle is a coboundary.**  The homotopy exhibits the splitting. -/
theorem deningerCech_exact {U : ι → Set X} {ρ : ι → X → ℝ}
    (hρsupp : ∀ i, tsupport (ρ i) ⊆ U i) (hρsum : ∀ x, ∑ i : ι, ρ i x = 1)
    {q : ℕ} (c : DeningerCechCochain X ι (q + 1))
    (hc : ∀ (σ : Fin (q + 3) → ι) (x : X), deningerCechD c σ x = 0) :
    ∀ (σ : Fin (q + 2) → ι) (x : X), deningerCechD (deningerCechK U ρ c) σ x = c σ x := by
  intro σ x
  have h := deningerCech_homotopy hρsupp hρsum c σ x
  have hzero : deningerCechK U ρ (deningerCechD c) σ x = 0 := by
    rw [deningerCechK]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [deningerExtendByZero_apply (hρsupp k), hc, mul_zero]
  rw [hzero, add_zero] at h
  exact h

end CechHomotopy

end RHTower
