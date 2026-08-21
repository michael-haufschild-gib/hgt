import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# The lattices `Λ_y`, the flow `g_t` and very well multiplicatively approximable vectors

This file sets up the objects of Kleinbock–Margulis §1–2.

For `y ∈ ℝⁿ` the lattice `Λ_y = u_y ℤ^{n+1}` is the image of the standard lattice under the
unipotent matrix `u_y = ((1, yᵀ), (0, Iₙ))`, so that its elements are the vectors
`(q · y + p, q₁, …, qₙ)` with `p ∈ ℤ`, `q ∈ ℤⁿ`.  The diagonal semigroup
`g_t = diag(e^t, e^{-t₁}, …, e^{-tₙ})`, `t = ∑ tᵢ`, acts on the space of lattices, and

`δ(Λ) = inf { ‖v‖ : v ∈ Λ, v ≠ 0 }`

measures how far `Λ` is from infinity in the sense of Mahler's compactness criterion.

A vector `y` is *very well multiplicatively approximable* when for some `ε > 0` there are
infinitely many `q ∈ ℤⁿ` with `|q · y + p| · Π₊(q) ≤ Π₊(q)^{-ε}` for some `p ∈ ℤ`, where
`Π₊(q) = ∏ᵢ max(|qᵢ|, 1)`.

## Main definitions

* `PiPlus` — the product `Π₊`.
* `VWMA` — very well multiplicatively approximable vectors (1.1M).
* `unipotentMat`, `flowMat` — the matrices `u_y` and `g_t`.
* `latticeDelta` — the function `δ` of (1.6).
-/

open Matrix Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {n k : ℕ}

/-! ### The product `Π₊` -/

/-- `Π₊(q) = ∏ᵢ max(|qᵢ|, 1)`. -/
noncomputable def PiPlus (q : Fin n → ℤ) : ℝ := ∏ i, max |(q i : ℝ)| 1

theorem one_le_prod_max (q : Fin n → ℤ) (s : Finset (Fin n)) :
    1 ≤ ∏ i ∈ s, max |(q i : ℝ)| 1 := by
  calc (1:ℝ) = ∏ _i ∈ s, (1:ℝ) := by simp
    _ ≤ ∏ i ∈ s, max |(q i : ℝ)| 1 :=
        Finset.prod_le_prod (fun i _ => zero_le_one) (fun i _ => le_max_right _ _)

theorem one_le_PiPlus (q : Fin n → ℤ) : 1 ≤ PiPlus q := one_le_prod_max q Finset.univ

theorem PiPlus_pos (q : Fin n → ℤ) : 0 < PiPlus q := lt_of_lt_of_le zero_lt_one (one_le_PiPlus q)

theorem abs_le_PiPlus_factor (q : Fin n → ℤ) (i : Fin n) : |(q i : ℝ)| ≤ max |(q i : ℝ)| 1 :=
  le_max_left _ _

/-- If the coordinates of `q` are bounded then so is `Π₊(q)`; hence sublevel sets of `Π₊` are
finite. -/
theorem finite_PiPlus_le (M : ℝ) : {q : Fin n → ℤ | PiPlus q ≤ M}.Finite := by
  classical
  have hsub : {q : Fin n → ℤ | PiPlus q ≤ M} ⊆ {q : Fin n → ℤ | ∀ i, |q i| ≤ ⌈M⌉} := by
    intro q hq i
    have h1 : max |(q i : ℝ)| 1 ≤ PiPlus q := by
      rw [PiPlus, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_right _ _))
        (one_le_prod_max q _)
    have h2 : |(q i : ℝ)| ≤ M := le_trans (le_trans (le_max_left _ _) h1) hq
    have h3 : |(q i : ℝ)| ≤ (⌈M⌉ : ℝ) := le_trans h2 (Int.le_ceil M)
    have : ((|q i| : ℤ) : ℝ) ≤ ((⌈M⌉ : ℤ) : ℝ) := by push_cast; simpa using h3
    exact_mod_cast this
  refine Set.Finite.subset ?_ hsub
  have : {q : Fin n → ℤ | ∀ i, |q i| ≤ ⌈M⌉} ⊆
      Set.pi Set.univ fun _ : Fin n => (Set.Icc (-⌈M⌉) ⌈M⌉ : Set ℤ) := by
    intro q hq i _
    exact abs_le.mp (hq i)
  refine Set.Finite.subset (Set.Finite.pi fun _ => Set.finite_Icc _ _) this

/-! ### Very well multiplicatively approximable vectors -/

/-- The linear form `q · y`. -/
noncomputable def dotProd (q : Fin n → ℤ) (y : Fin n → ℝ) : ℝ := ∑ i, (q i : ℝ) * y i

/-- **(1.1M).**  `y` is very well multiplicatively approximable: for some `ε > 0` there are
infinitely many `q ∈ ℤⁿ` admitting `p ∈ ℤ` with `|q · y + p| · Π₊(q) ≤ Π₊(q)^{-ε}`. -/
def VWMA (y : Fin n → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    {q : Fin n → ℤ | ∃ p : ℤ,
      |dotProd q y + (p : ℝ)| * PiPlus q ≤ PiPlus q ^ (-ε)}.Infinite

/-! ### The matrices `u_y` and `g_t` -/

/-- The unipotent matrix `u_y = ((1, yᵀ), (0, Iₙ))`. -/
noncomputable def unipotentMat (y : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = 0 then Fin.cases (1 : ℝ) (fun j' => y j') j else if i = j then 1 else 0

/-- The diagonal matrix `g_t = diag(e^{t}, e^{-t₁}, …, e^{-tₙ})` with `t = ∑ tᵢ`. -/
noncomputable def flowMat (t : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (Fin.cons (Real.exp (∑ i, t i)) fun i => Real.exp (-(t i)))

/-- The lattice vector `(q · y + p, q₁, …, qₙ)` of (2.1). -/
noncomputable def latticeVec (y : Fin n → ℝ) (p : ℤ) (q : Fin n → ℤ) : Fin (n + 1) → ℝ :=
  Fin.cons (dotProd q y + (p : ℝ)) fun i => (q i : ℝ)

theorem unipotentMat_mulVec (y : Fin n → ℝ) (p : ℤ) (q : Fin n → ℤ) :
    (unipotentMat y).mulVec (Fin.cons (p : ℝ) fun i => (q i : ℝ)) = latticeVec y p q := by
  classical
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [mulVec, dotProduct, unipotentMat, Matrix.of_apply, latticeVec,
      Fin.cons_zero, dotProd]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cons_zero, Fin.cases_succ, Fin.cons_succ]
    rw [add_comm]
    congr 1
    all_goals first
      | exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      | norm_num
  · have h0 : (Fin.succ i' : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i'
    simp only [mulVec, dotProduct, unipotentMat, Matrix.of_apply, if_neg h0, latticeVec,
      Fin.cons_succ]
    rw [Finset.sum_eq_single (Fin.succ i')]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem flowMat_mulVec (t : Fin n → ℝ) (v : Fin (n + 1) → ℝ) :
    (flowMat t).mulVec v
      = Fin.cons (Real.exp (∑ i, t i) * v 0) fun i => Real.exp (-(t i)) * v i.succ := by
  funext i
  rw [flowMat, mulVec_diagonal]
  refine Fin.cases ?_ (fun i' => ?_) i <;> simp

/-! ### The function `δ` -/

/-- `δ(A ℤ^k) = inf { ‖A v‖ : v ∈ ℤ^k, v ≠ 0 }`. -/
noncomputable def latticeDelta (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  sInf {c : ℝ | ∃ v : Fin k → ℤ, v ≠ 0 ∧ c = ‖A.mulVec fun i => (v i : ℝ)‖}

theorem latticeDelta_nonneg (A : Matrix (Fin k) (Fin k) ℝ) : 0 ≤ latticeDelta A := by
  refine Real.sInf_nonneg ?_
  rintro c ⟨v, -, rfl⟩
  exact norm_nonneg _

theorem latticeDelta_le (A : Matrix (Fin k) (Fin k) ℝ) {v : Fin k → ℤ} (hv : v ≠ 0) :
    latticeDelta A ≤ ‖A.mulVec fun i => (v i : ℝ)‖ :=
  csInf_le ⟨0, by rintro c ⟨w, -, rfl⟩; exact norm_nonneg _⟩ ⟨v, hv, rfl⟩

theorem nonempty_latticeDelta_set (A : Matrix (Fin k) (Fin k) ℝ) (hk : 0 < k) :
    {c : ℝ | ∃ v : Fin k → ℤ, v ≠ 0 ∧ c = ‖A.mulVec fun i => (v i : ℝ)‖}.Nonempty := by
  classical
  refine ⟨_, fun i => if i = ⟨0, hk⟩ then (1:ℤ) else 0, ?_, rfl⟩
  intro hcon
  have := congrFun hcon ⟨0, hk⟩
  simp at this

/-- If `δ(Aℤ^k) < ε` then some nonzero integer vector has image of norm `< ε`. -/
theorem exists_of_latticeDelta_lt {A : Matrix (Fin k) (Fin k) ℝ} {ε : ℝ} (hk : 0 < k)
    (h : latticeDelta A < ε) :
    ∃ v : Fin k → ℤ, v ≠ 0 ∧ ‖A.mulVec fun i => (v i : ℝ)‖ < ε := by
  obtain ⟨c, ⟨v, hv, rfl⟩, hc⟩ := exists_lt_of_csInf_lt (nonempty_latticeDelta_set A hk) h
  exact ⟨v, hv, hc⟩

/-- Conversely, a uniform lower bound on all nonzero lattice vectors bounds `δ` from below. -/
theorem le_latticeDelta {A : Matrix (Fin k) (Fin k) ℝ} {ε : ℝ} (hk : 0 < k)
    (h : ∀ v : Fin k → ℤ, v ≠ 0 → ε ≤ ‖A.mulVec fun i => (v i : ℝ)‖) : ε ≤ latticeDelta A := by
  refine le_csInf (nonempty_latticeDelta_set A hk) ?_
  rintro c ⟨v, hv, rfl⟩
  exact h v hv

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
