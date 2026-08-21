import GaloisForLFunctions.HTGeometry.KleinbockMargulis.WedgeNorm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Plücker coordinates determine the span

For a linearly independent tuple `V` of vectors of a vector space `K^k`, the span of `V` is
exactly the set of `x` annihilating all the `(j+1)`-fold Plücker coordinates of `V` together with
`x`.  Since those coordinates are linear in `x` with coefficients the Plücker coordinates of `V`,
the span is determined by the Plücker vector of `V`.

Both inclusions come from one elementary row operation.  Subtracting from the last row the
combination expressing `x` in terms of `V` is realised by a lower triangular matrix of determinant
one, so it changes no Plücker coordinate; it makes the last row zero in one direction, and in the
other direction it reduces the vanishing of the minors to Cramer's rule.

## Main results

* `plucker_snoc_eq_zero_of_mem_span` — one inclusion.
* `mem_span_of_plucker_snoc_eq_zero` — the converse (Cramer's rule).
* `exists_plucker_ne_zero` — an independent tuple has a nonvanishing maximal minor.
-/

open Matrix Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {K : Type*} [Field K] {m k : ℕ}

/-! ### The row operation -/

/-- The identity matrix with the last row replaced by `(-c₁, …, -c_m, 1)`: it subtracts the
combination `∑ cₐ Vₐ` from the last row of a tuple. -/
def rowOpMatrix (c : Fin m → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of fun a b =>
    if a = Fin.last m then (Fin.snoc (fun b' => -c b') (1 : K) : Fin (m + 1) → K) b
    else if a = b then 1 else 0

theorem rowOpMatrix_det (c : Fin m → K) : (rowOpMatrix c).det = 1 := by
  classical
  have htri : (rowOpMatrix c).BlockTriangular OrderDual.toDual := by
    intro a b hab
    have hlt : a < b := OrderDual.toDual_lt_toDual.mp hab
    have ha : a ≠ Fin.last m := by
      intro h
      subst h
      exact absurd hlt (not_lt.mpr (Fin.le_last b))
    simp [rowOpMatrix, ha, ne_of_lt hlt]
  rw [Matrix.det_of_lowerTriangular _ htri]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = Fin.last m
  · subst ha
    simp [rowOpMatrix]
  · simp [rowOpMatrix, ha]

theorem rowOpMatrix_apply (c : Fin m → K) (V : Fin m → (Fin k → K)) (x : Fin k → K) :
    (fun a d => ∑ b, rowOpMatrix c a b * (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) b d)
      = Fin.snoc V (fun d => x d - ∑ a, c a * V a d) := by
  classical
  funext a d
  induction a using Fin.lastCases with
  | last =>
    have hrow : ∀ b : Fin (m + 1),
        rowOpMatrix c (Fin.last m) b * (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) b d
          = (Fin.snoc (fun b' => -(c b') * V b' d) (x d) : Fin (m + 1) → K) b := by
      intro b
      induction b using Fin.lastCases with
      | last => simp [rowOpMatrix]
      | cast b' => simp [rowOpMatrix]
    rw [Finset.sum_congr rfl fun b _ => hrow b, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have key : ∑ b' : Fin m, -(c b') * V b' d = -(∑ a, c a * V a d) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b' _ => by ring
    rw [key]
    ring
  | cast a' =>
    have ha : (Fin.castSucc a' : Fin (m + 1)) ≠ Fin.last m := (Fin.castSucc_lt_last a').ne
    simp only [Fin.snoc_castSucc, rowOpMatrix, Matrix.of_apply, if_neg ha]
    rw [Finset.sum_eq_single (Fin.castSucc a')]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The row operation preserves all Plücker coordinates. -/
theorem plucker_snoc_sub (c : Fin m → K) (V : Fin m → (Fin k → K)) (x : Fin k → K)
    (τ : Fin (m + 1) → Fin k) :
    plucker (Fin.snoc V (fun d => x d - ∑ a, c a * V a d)) τ
      = plucker (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) τ := by
  rw [← rowOpMatrix_apply c V x, plucker_matrix_mul, rowOpMatrix_det, one_mul]

/-! ### The two inclusions -/

/-- If `x` lies in the span of `V` then all the `(j+1)`-fold Plücker coordinates vanish. -/
theorem plucker_snoc_eq_zero_of_mem_span {V : Fin m → (Fin k → K)} {x : Fin k → K}
    (hx : x ∈ Submodule.span K (Set.range V)) (τ : Fin (m + 1) → Fin k) :
    plucker (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) τ = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin m → K, x = fun d => ∑ a, c a * V a d := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    refine ⟨c, ?_⟩
    funext d
    rw [← hc]
    simp [Finset.sum_apply]
  rw [← plucker_snoc_sub c V x τ]
  have hzero : (fun d => x d - ∑ a, c a * V a d) = fun _ => (0 : K) := by
    funext d
    rw [hc]
    simp
  rw [hzero, plucker]
  refine Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) fun b => ?_
  simp

/-- **Cramer's rule.**  If some maximal minor of `V` is nonzero and all `(j+1)`-fold Plücker
coordinates of `V` together with `x` vanish, then `x` lies in the span of `V`. -/
theorem mem_span_of_plucker_snoc_eq_zero {V : Fin m → (Fin k → K)} {x : Fin k → K}
    {τ₀ : Fin m → Fin k} (hτ₀ : plucker V τ₀ ≠ 0)
    (h : ∀ τ : Fin (m + 1) → Fin k, plucker (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) τ = 0) :
    x ∈ Submodule.span K (Set.range V) := by
  classical
  set M : Matrix (Fin m) (Fin m) K := Matrix.of fun a b => V a (τ₀ b) with hM
  have hMunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hτ₀
  set c : Fin m → K := (fun b => x (τ₀ b)) ᵥ* M⁻¹ with hc
  have hcM : ∀ b, ∑ a, c a * V a (τ₀ b) = x (τ₀ b) := by
    intro b
    have hvm : c ᵥ* M = fun b => x (τ₀ b) := by
      rw [hc, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hMunit, Matrix.vecMul_one]
    simpa [Matrix.vecMul, dotProduct, hM] using congrFun hvm b
  set z : Fin k → K := fun d => x d - ∑ a, c a * V a d with hz
  have hzdef : ∀ d, z d = x d - ∑ a, c a * V a d := fun d => rfl
  have hzero : ∀ b, z (τ₀ b) = 0 := by
    intro b
    rw [hzdef, hcM b, sub_self]
  have hzall : ∀ i : Fin k, z i = 0 := by
    intro i
    have h1 : plucker (Fin.snoc V z : Fin (m + 1) → (Fin k → K)) (Fin.snoc τ₀ i) = 0 := by
      rw [hz, plucker_snoc_sub c V x (Fin.snoc τ₀ i)]
      exact h _
    rw [plucker, Matrix.det_succ_row _ (Fin.last m)] at h1
    rw [Finset.sum_eq_single (Fin.last m)] at h1
    · have h3 : (Matrix.of fun a b' => (Fin.snoc V z : Fin (m + 1) → (Fin k → K)) a
          ((Fin.snoc τ₀ i : Fin (m + 1) → Fin k) b')) (Fin.last m) (Fin.last m) = z i := by
        simp
      have h4 : ((Matrix.of fun a b' => (Fin.snoc V z : Fin (m + 1) → (Fin k → K)) a
          ((Fin.snoc τ₀ i : Fin (m + 1) → Fin k) b')).submatrix
          (Fin.last m).succAbove (Fin.last m).succAbove).det = plucker V τ₀ := by
        rw [plucker]
        congr 1
        ext a' b'
        simp [Fin.succAbove_last]
      rw [h3, h4] at h1
      have h5 : ((-1 : K) ^ ((Fin.last m : ℕ) + ((Fin.last m : Fin (m + 1)) : ℕ))) ≠ 0 := by
        simp
      rcases mul_eq_zero.mp h1 with hh | hh
      · rcases mul_eq_zero.mp hh with hh' | hh'
        · exact absurd hh' h5
        · exact hh'
      · exact absurd hh hτ₀
    · intro b _ hb
      revert hb
      induction b using Fin.lastCases with
      | last => intro hb; exact absurd rfl hb
      | cast b' =>
        intro _
        simp only [Matrix.of_apply, Fin.snoc_last, Fin.snoc_castSucc]
        rw [hzero b']
        ring
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hxeq : x = fun d => ∑ a, c a * V a d := by
    funext d
    show x d = ∑ a, c a * V a d
    have hd : x d - ∑ a, c a * V a d = 0 := hzall d
    exact sub_eq_zero.mp hd
  have hfun : (fun d => ∑ a, c a * V a d) = ∑ a, c a • V a := by
    funext d
    simp [Finset.sum_apply]
  rw [hxeq, hfun]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/-- An independent tuple has a nonvanishing maximal minor. -/
theorem exists_plucker_ne_zero :
    ∀ {m : ℕ} {V : Fin m → (Fin k → K)}, LinearIndependent K V →
      ∃ τ : Fin m → Fin k, plucker V τ ≠ 0 := by
  intro m
  induction m with
  | zero => intro V _; exact ⟨fun i => i.elim0, by simp⟩
  | succ m ih =>
    intro V hV
    have hV' : LinearIndependent K (fun a : Fin m => V (Fin.castSucc a)) :=
      hV.comp _ (Fin.castSucc_injective m)
    obtain ⟨τ', hτ'⟩ := ih hV'
    by_contra hcon
    push Not at hcon
    have hsnoc : (Fin.snoc (fun a : Fin m => V (Fin.castSucc a)) (V (Fin.last m))
        : Fin (m + 1) → (Fin k → K)) = V := by
      funext a
      induction a using Fin.lastCases with
      | last => simp
      | cast a' => simp
    have hmem : V (Fin.last m) ∈
        Submodule.span K (Set.range fun a : Fin m => V (Fin.castSucc a)) := by
      refine mem_span_of_plucker_snoc_eq_zero hτ' fun τ => ?_
      rw [hsnoc]
      exact hcon τ
    have hnot : V (Fin.last m) ∉
        Submodule.span K (V '' (Set.range (Fin.castSucc : Fin m → Fin (m + 1)))) := by
      refine hV.notMem_span_image ?_
      rintro ⟨a, ha⟩
      exact absurd ha (Fin.castSucc_lt_last a).ne
    refine hnot ?_
    have himg : V '' (Set.range (Fin.castSucc : Fin m → Fin (m + 1)))
        = Set.range fun a : Fin m => V (Fin.castSucc a) := by
      rw [← Set.range_comp]
      rfl
    rw [himg]
    exact hmem


/-! ### The span is determined by the Plücker coordinates -/

/-- Laplace expansion of a `(j+1)`-fold Plücker coordinate along the adjoined vector: it is a
linear form in `x` whose coefficients are the Plücker coordinates of `V`. -/
theorem plucker_snoc_expand (V : Fin m → (Fin k → K)) (x : Fin k → K) (τ : Fin (m + 1) → Fin k) :
    plucker (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) τ
      = ∑ b : Fin (m + 1), (-1) ^ ((m : ℕ) + (b : ℕ)) * x (τ b)
          * plucker V fun b' => τ (b.succAbove b') := by
  classical
  rw [plucker, Matrix.det_succ_row _ (Fin.last m)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hval : ((Fin.last m : Fin (m + 1)) : ℕ) = m := Fin.val_last m
  have hentry : (Matrix.of fun a b'' => (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) a (τ b''))
      (Fin.last m) b = x (τ b) := by simp
  have hminor : ((Matrix.of fun a b'' => (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) a (τ b'')).submatrix
      (Fin.last m).succAbove b.succAbove).det = plucker V fun b' => τ (b.succAbove b') := by
    rw [plucker]
    congr 1
    ext a' b'
    simp [Fin.succAbove_last]
  rw [hentry, hminor, hval]

/-- For an independent tuple, membership in the span is exactly the vanishing of all the
`(j+1)`-fold Plücker coordinates. -/
theorem mem_span_iff_plucker {V : Fin m → (Fin k → K)} (hV : LinearIndependent K V)
    (x : Fin k → K) :
    x ∈ Submodule.span K (Set.range V) ↔ ∀ τ : Fin (m + 1) → Fin k,
      plucker (Fin.snoc V x : Fin (m + 1) → (Fin k → K)) τ = 0 := by
  obtain ⟨τ₀, hτ₀⟩ := exists_plucker_ne_zero hV
  exact ⟨fun hx => plucker_snoc_eq_zero_of_mem_span hx, mem_span_of_plucker_snoc_eq_zero hτ₀⟩

/-- Two independent tuples of the same length with the same Plücker coordinates span the same
subspace. -/
theorem span_eq_of_plucker_eq {j j' : ℕ} {V : Fin j → (Fin k → K)} {V' : Fin j' → (Fin k → K)}
    (hV : LinearIndependent K V) (hV' : LinearIndependent K V') (hjj : j = j')
    (h : ∀ σ : Fin j → Fin k, plucker V σ = plucker V' fun b => σ (Fin.cast hjj.symm b)) :
    Submodule.span K (Set.range V) = Submodule.span K (Set.range V') := by
  subst hjj
  have h' : ∀ σ : Fin j → Fin k, plucker V σ = plucker V' σ := by
    intro σ
    simpa using h σ
  have key : ∀ (x : Fin k → K) (τ : Fin (j + 1) → Fin k),
      plucker (Fin.snoc V x : Fin (j + 1) → (Fin k → K)) τ
        = plucker (Fin.snoc V' x : Fin (j + 1) → (Fin k → K)) τ := by
    intro x τ
    rw [plucker_snoc_expand, plucker_snoc_expand]
    exact Finset.sum_congr rfl fun b _ => by rw [h' _]
  ext x
  rw [mem_span_iff_plucker hV, mem_span_iff_plucker hV']
  constructor
  · intro hx τ
    rw [← key]
    exact hx τ
  · intro hx τ
    rw [key]
    exact hx τ

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
