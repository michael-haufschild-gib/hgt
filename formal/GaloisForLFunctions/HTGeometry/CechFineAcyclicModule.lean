import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Module

/-!
# A fine coefficient has no higher Čech cohomology, with coefficients in a module

Multiplying by a partition of unity subordinate to the cover contracts the Čech complex: the
operator that averages a cochain over a prepended index, each term extended by zero, is a homotopy
between the identity and zero in every positive degree.  The computation is simplicial — the faces
of an index tuple with a prepended index are the tuple itself in the zeroth place and the faces of
the original tuple with the index still prepended elsewhere — so the two composites cancel except
for the term carrying the total mass of the partition, which is one.

`RHTower.DeningerCechHomotopy` proves this for real-valued cochains.  The proof uses nothing but
scalar multiplication and finite sums, so it is carried out here for cochains valued in an arbitrary
real module, which is the generality the sheaves of smooth forms need.

* `HTGeometry.CechCochain` : cochains of a cover valued in a module.
* `HTGeometry.cechD` : the Čech differential.
* `HTGeometry.cechK` : the averaging homotopy.
* `HTGeometry.cech_homotopy` : `δK + Kδ = id` in every degree.
* `HTGeometry.cech_exact` : hence every cocycle is a coboundary.
-/

namespace HTGeometry

section Module

variable {X ι M : Type*} [TopologicalSpace X] [Fintype ι]
  [AddCommGroup M] [Module ℝ M]

/-- Čech cochains of a cover, valued in a module. -/
abbrev CechCochain (X ι M : Type*) (q : ℕ) := (Fin (q + 1) → ι) → X → M

/-- Extension by zero of a cochain multiplied by a bump. -/
noncomputable def cechExtendZero (U : Set X) (ρ : X → ℝ) (f : X → M) (x : X) : M :=
  Set.indicator U (fun y => ρ y • f y) x

/-- With the support condition the extension by zero is pointwise the scalar multiple. -/
theorem cechExtendZero_apply {U : Set X} {ρ : X → ℝ} (hsupp : tsupport ρ ⊆ U)
    (f : X → M) (x : X) : cechExtendZero U ρ f x = ρ x • f x := by
  by_cases hx : x ∈ U
  · rw [cechExtendZero, Set.indicator_of_mem hx]
  · have hρ : ρ x = 0 := by
      by_contra hne
      exact hx (hsupp (subset_tsupport ρ hne))
    rw [cechExtendZero, Set.indicator_of_notMem hx, hρ, zero_smul]

/-- The Čech differential: the alternating sum over the faces of the index tuple. -/
noncomputable def cechD {q : ℕ} (c : CechCochain X ι M q) : CechCochain X ι M (q + 1) :=
  fun σ x => ∑ r : Fin (q + 2), ((-1 : ℝ) ^ (r : ℕ)) • c (σ ∘ Fin.succAbove r) x

/-- The contracting homotopy: average over a prepended index against the partition of unity. -/
noncomputable def cechK (U : ι → Set X) (ρ : ι → X → ℝ) {q : ℕ}
    (c : CechCochain X ι M (q + 1)) : CechCochain X ι M q :=
  fun σ x => ∑ k : ι, cechExtendZero (U k) (ρ k) (c (Fin.cons k σ)) x

omit [Fintype ι] [TopologicalSpace X] in
/-- The zeroth face of a tuple with a prepended index is the tuple itself. -/
theorem cechFace_zero {q : ℕ} (k : ι) (σ : Fin (q + 1) → ι) :
    (Fin.cons k σ : Fin (q + 2) → ι) ∘ Fin.succAbove 0 = σ := by
  funext s
  simp

omit [Fintype ι] [TopologicalSpace X] in
/-- The later faces of a tuple with a prepended index keep the prepended index. -/
theorem cechFace_succ {q : ℕ} (k : ι) (σ : Fin (q + 2) → ι) (r : Fin (q + 2)) :
    (Fin.cons k σ : Fin (q + 3) → ι) ∘ Fin.succAbove r.succ
      = Fin.cons k (σ ∘ Fin.succAbove r) := by
  funext s
  refine Fin.cases ?_ (fun t => ?_) s
  · simp
  · simp only [Function.comp_apply, Fin.succ_succAbove_succ, Fin.cons_succ]

omit [TopologicalSpace X] [Fintype ι] in
/-- The differential on a tuple with a prepended index separates the zeroth face. -/
theorem cechD_cons {q : ℕ} (c : CechCochain X ι M (q + 1)) (k : ι)
    (σ : Fin (q + 2) → ι) (x : X) :
    cechD c (Fin.cons k σ) x
      = c σ x - ∑ r : Fin (q + 2),
          ((-1 : ℝ) ^ (r : ℕ)) • c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
  rw [cechD, Fin.sum_univ_succ, cechFace_zero k σ]
  have hrest : ∀ r : Fin (q + 2),
      ((-1 : ℝ) ^ ((r.succ : Fin (q + 3)) : ℕ))
          • c ((Fin.cons k σ : Fin (q + 3) → ι) ∘ Fin.succAbove r.succ) x
        = -(((-1 : ℝ) ^ (r : ℕ)) • c (Fin.cons k (σ ∘ Fin.succAbove r)) x) := by
    intro r
    rw [cechFace_succ k σ r]
    have hpow : ((r.succ : Fin (q + 3)) : ℕ) = (r : ℕ) + 1 := rfl
    rw [hpow, pow_succ]
    module
  rw [Finset.sum_congr rfl fun r _ => hrest r, Finset.sum_neg_distrib]
  simp only [Fin.val_zero, pow_zero, one_smul]
  abel

/-- **The averaging operator is a contracting homotopy.**  In every degree the two composites add
up to the identity, because the partition of unity has total mass one. -/
theorem cech_homotopy {U : ι → Set X} {ρ : ι → X → ℝ}
    (hρsupp : ∀ i, tsupport (ρ i) ⊆ U i) (hρsum : ∀ x, ∑ i : ι, ρ i x = 1)
    {q : ℕ} (c : CechCochain X ι M (q + 1)) (σ : Fin (q + 2) → ι) (x : X) :
    cechD (cechK U ρ c) σ x + cechK U ρ (cechD c) σ x = c σ x := by
  have hK : ∀ (d : CechCochain X ι M (q + 2)) (τ : Fin (q + 2) → ι),
      cechK U ρ d τ x = ∑ k : ι, ρ k x • d (Fin.cons k τ) x := fun d τ =>
    Finset.sum_congr rfl fun k _ => cechExtendZero_apply (hρsupp k) _ x
  have hK' : ∀ τ : Fin (q + 1) → ι, cechK U ρ c τ x
      = ∑ k : ι, ρ k x • c (Fin.cons k τ) x := fun τ =>
    Finset.sum_congr rfl fun k _ => cechExtendZero_apply (hρsupp k) _ x
  have hfirst : cechD (cechK U ρ c) σ x
      = ∑ r : Fin (q + 2), ((-1 : ℝ) ^ (r : ℕ))
          • ∑ k : ι, ρ k x • c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
    rw [cechD]
    exact Finset.sum_congr rfl fun r _ => by rw [hK' (σ ∘ Fin.succAbove r)]
  have hsecond : cechK U ρ (cechD c) σ x
      = ∑ k : ι, ρ k x • c σ x
        - ∑ k : ι, ρ k x • ∑ r : Fin (q + 2),
            ((-1 : ℝ) ^ (r : ℕ)) • c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
    rw [hK (cechD c) σ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cechD_cons c k σ x, smul_sub]
  rw [hfirst, hsecond]
  have hswap : ∑ r : Fin (q + 2), ((-1 : ℝ) ^ (r : ℕ))
        • ∑ k : ι, ρ k x • c (Fin.cons k (σ ∘ Fin.succAbove r)) x
      = ∑ k : ι, ρ k x • ∑ r : Fin (q + 2),
          ((-1 : ℝ) ^ (r : ℕ)) • c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
    calc ∑ r : Fin (q + 2), ((-1 : ℝ) ^ (r : ℕ))
          • ∑ k : ι, ρ k x • c (Fin.cons k (σ ∘ Fin.succAbove r)) x
        = ∑ r : Fin (q + 2), ∑ k : ι,
            ((-1 : ℝ) ^ (r : ℕ)) • (ρ k x • c (Fin.cons k (σ ∘ Fin.succAbove r)) x) :=
          Finset.sum_congr rfl fun r _ => by rw [Finset.smul_sum]
      _ = ∑ k : ι, ∑ r : Fin (q + 2),
            ((-1 : ℝ) ^ (r : ℕ)) • (ρ k x • c (Fin.cons k (σ ∘ Fin.succAbove r)) x) :=
          Finset.sum_comm
      _ = ∑ k : ι, ρ k x • ∑ r : Fin (q + 2),
            ((-1 : ℝ) ^ (r : ℕ)) • c (Fin.cons k (σ ∘ Fin.succAbove r)) x := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun r _ => by
            rw [smul_comm]
  have hmass : ∑ k : ι, ρ k x • c σ x = c σ x := by
    have h := map_sum (LinearMap.toSpanSingleton ℝ M (c σ x)) (fun k => ρ k x) Finset.univ
    simp only [LinearMap.toSpanSingleton_apply] at h
    rw [← h, hρsum x, one_smul]
  rw [hswap, hmass]
  abel

/-- **Every cocycle is a coboundary.**  The homotopy exhibits the splitting. -/
theorem cech_exact {U : ι → Set X} {ρ : ι → X → ℝ}
    (hρsupp : ∀ i, tsupport (ρ i) ⊆ U i) (hρsum : ∀ x, ∑ i : ι, ρ i x = 1)
    {q : ℕ} (c : CechCochain X ι M (q + 1))
    (hc : ∀ (σ : Fin (q + 3) → ι) (x : X), cechD c σ x = 0) :
    ∀ (σ : Fin (q + 2) → ι) (x : X), cechD (cechK U ρ c) σ x = c σ x := by
  intro σ x
  have h := cech_homotopy hρsupp hρsum c σ x
  have hzero : cechK U ρ (cechD c) σ x = 0 := by
    rw [cechK]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [cechExtendZero_apply (hρsupp k), hc, smul_zero]
  rw [hzero, add_zero] at h
  exact h

end Module

end HTGeometry
