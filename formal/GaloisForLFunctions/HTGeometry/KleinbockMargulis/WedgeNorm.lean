import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Plücker coordinates and the supremum norm on exterior powers

For a `j`-tuple `V` of vectors of `ℝ^k` the *Plücker coordinates* are the `j × j` minors
`plucker V σ = det (V a (σ b))`, indexed by arbitrary maps `σ : Fin j → Fin k` (the minors with
non-injective `σ` vanish, and permuting `σ` only changes a sign, so nothing is lost by not
restricting to increasing `σ`).  The *wedge norm* `wedgeNorm V` is the largest of them in absolute
value; this is the norm `‖v₁ ∧ … ∧ v_j‖` used in Kleinbock–Margulis §5, where the norm on the
exterior algebra is the supremum of the coordinates in the standard basis.

## Main results

* `plucker_matrix_mul` — Plücker coordinates transform by `det T` under a change of the tuple.
* `plucker_mulVec` — the expansion `plucker (A ∘ V) σ = ∑_f (∏_b A_{σ b, f b}) · plucker V f`,
  obtained from the multilinearity of the determinant in its rows.  Its immediate consequence
  `wedgeNorm_mulVec_le` is the properness of `Γ ↦ ‖AΓ‖`.
* `wedgeNorm_snoc_le` — `‖w ∧ v‖ ≤ (j+1) ‖w‖ ‖v‖`, the estimate behind Lemma 5.1.
-/

open Matrix Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {j k : ℕ}

/-! ### Plücker coordinates -/

/-- The `σ`-th Plücker coordinate (a `j × j` minor) of a `j`-tuple of vectors in `R^k`. -/
def plucker {R : Type*} [CommRing R] (V : Fin j → (Fin k → R)) (σ : Fin j → Fin k) : R :=
  Matrix.det (Matrix.of fun a b => V a (σ b))

@[simp] theorem plucker_zero {R : Type*} [CommRing R] (V : Fin 0 → (Fin k → R))
    (σ : Fin 0 → Fin k) : plucker V σ = 1 := by
  simp [plucker]

/-- Replacing the tuple `V` by `T • V` multiplies every Plücker coordinate by `det T`. -/
theorem plucker_matrix_mul {R : Type*} [CommRing R] (T : Matrix (Fin j) (Fin j) R)
    (V : Fin j → (Fin k → R)) (σ : Fin j → Fin k) :
    plucker (fun a c => ∑ b, T a b * V b c) σ = T.det * plucker V σ := by
  have h : (Matrix.of fun a b => (fun a c => ∑ b, T a b * V b c) a (σ b))
      = T * Matrix.of fun a b => V a (σ b) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [plucker, h, Matrix.det_mul, plucker]

/-! ### The wedge norm -/

/-- `‖v₁ ∧ … ∧ v_j‖`: the largest Plücker coordinate in absolute value. -/
noncomputable def wedgeNorm (V : Fin j → (Fin k → ℝ)) : ℝ := ⨆ σ : Fin j → Fin k, |plucker V σ|

theorem bddAbove_plucker (V : Fin j → (Fin k → ℝ)) :
    BddAbove (Set.range fun σ : Fin j → Fin k => |plucker V σ|) :=
  (Set.finite_range _).bddAbove

theorem le_wedgeNorm (V : Fin j → (Fin k → ℝ)) (σ : Fin j → Fin k) :
    |plucker V σ| ≤ wedgeNorm V :=
  le_ciSup (bddAbove_plucker V) σ

theorem wedgeNorm_le {V : Fin j → (Fin k → ℝ)} {c : ℝ} [Nonempty (Fin j → Fin k)]
    (h : ∀ σ, |plucker V σ| ≤ c) : wedgeNorm V ≤ c :=
  ciSup_le h

theorem wedgeNorm_nonneg [Nonempty (Fin j → Fin k)] (V : Fin j → (Fin k → ℝ)) :
    0 ≤ wedgeNorm V :=
  le_trans (abs_nonneg _) (le_wedgeNorm V (Classical.arbitrary _))

@[simp] theorem wedgeNorm_zero (V : Fin 0 → (Fin k → ℝ)) : wedgeNorm V = 1 := by
  have : (fun σ : Fin 0 → Fin k => |plucker V σ|) = fun _ => (1:ℝ) := by
    funext σ; simp
  rw [wedgeNorm, this, ciSup_const]

/-- A change of the tuple with `|det T| ≥ 1` cannot decrease the wedge norm. -/
theorem wedgeNorm_le_matrix_mul [Nonempty (Fin j → Fin k)] {T : Matrix (Fin j) (Fin j) ℝ}
    (hT : 1 ≤ |T.det|) (V : Fin j → (Fin k → ℝ)) :
    wedgeNorm V ≤ wedgeNorm (fun a c => ∑ b, T a b * V b c) := by
  refine wedgeNorm_le fun σ => ?_
  have h1 : |plucker V σ| ≤ |T.det| * |plucker V σ| := le_mul_of_one_le_left (abs_nonneg _) hT
  have h2 : |T.det| * |plucker V σ| = |plucker (fun a c => ∑ b, T a b * V b c) σ| := by
    rw [plucker_matrix_mul, abs_mul]
  rw [h2] at h1
  exact le_trans h1 (le_wedgeNorm _ σ)

/-! ### The image of a tuple under a matrix -/

/-- **Expansion of a minor of `A · V`.**  The determinant is multilinear in its rows, so a
`j × j` minor of the tuple `A ∘ V` is a combination of the Plücker coordinates of `V` with
coefficients the products of entries of `A`. -/
theorem plucker_mulVec (A : Matrix (Fin k) (Fin k) ℝ) (V : Fin j → (Fin k → ℝ))
    (σ : Fin j → Fin k) :
    plucker (fun a => A.mulVec (V a)) σ
      = ∑ f : Fin j → Fin k, (∏ b, A (σ b) (f b)) * plucker V f := by
  classical
  set D : MultilinearMap ℝ (fun _ : Fin j => (Fin j → ℝ)) ℝ :=
    (Matrix.detRowAlternating : (Fin j → ℝ) [⋀^Fin j]→ₗ[ℝ] ℝ).toMultilinearMap with hD
  have hDapp : ∀ R : Fin j → (Fin j → ℝ), D R = Matrix.det (Matrix.of fun b a => R b a) := by
    intro R
    rfl
  have h1 : plucker (fun a => A.mulVec (V a)) σ
      = D fun b => ∑ c : Fin k, A (σ b) c • (fun a : Fin j => V a c) := by
    rw [hDapp, plucker, ← Matrix.det_transpose]
    congr 1
    ext b a
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, hDapp, smul_eq_mul]
  congr 1
  rw [plucker, ← Matrix.det_transpose]
  rfl

/-- **Properness.**  If all entries of `A` are at most `M` in absolute value then the wedge norm
of `A ∘ V` is at most `k^j M^j` times that of `V`. -/
theorem wedgeNorm_mulVec_le [Nonempty (Fin j → Fin k)] {A : Matrix (Fin k) (Fin k) ℝ} {M : ℝ}
    (hM : ∀ i l, |A i l| ≤ M) (hM0 : 0 ≤ M) (V : Fin j → (Fin k → ℝ)) :
    wedgeNorm (fun a => A.mulVec (V a)) ≤ (k : ℝ) ^ j * M ^ j * wedgeNorm V := by
  classical
  refine wedgeNorm_le fun σ => ?_
  rw [plucker_mulVec]
  calc |∑ f : Fin j → Fin k, (∏ b, A (σ b) (f b)) * plucker V f|
      ≤ ∑ f : Fin j → Fin k, |(∏ b, A (σ b) (f b)) * plucker V f| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f : Fin j → Fin k, M ^ j * wedgeNorm V := by
        refine Finset.sum_le_sum fun f _ => ?_
        rw [abs_mul, Finset.abs_prod]
        refine mul_le_mul ?_ (le_wedgeNorm V f) (abs_nonneg _) (by positivity)
        calc ∏ b, |A (σ b) (f b)| ≤ ∏ _b : Fin j, M :=
              Finset.prod_le_prod (fun b _ => abs_nonneg _) fun b _ => hM _ _
          _ = M ^ j := by simp
    _ = (k : ℝ) ^ j * M ^ j * wedgeNorm V := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ### Adjoining a vector -/

/-- **The estimate behind Lemma 5.1.**  `‖w ∧ v‖ ≤ (j+1) ‖w‖ ‖v‖`, by Laplace expansion of the
`(j+1) × (j+1)` minors along the last row. -/
theorem wedgeNorm_snoc_le [Nonempty (Fin j → Fin k)] [Nonempty (Fin (j + 1) → Fin k)]
    (V : Fin j → (Fin k → ℝ)) (v : Fin k → ℝ) :
    wedgeNorm (Fin.snoc V v) ≤ ((j : ℝ) + 1) * wedgeNorm V * ‖v‖ := by
  classical
  refine wedgeNorm_le fun σ => ?_
  have hexp := Matrix.det_succ_row
    (Matrix.of fun a b => (Fin.snoc V v : Fin (j + 1) → (Fin k → ℝ)) a (σ b)) (Fin.last j)
  rw [plucker, hexp]
  calc |∑ b : Fin (j + 1), (-1 : ℝ) ^ ((Fin.last j : ℕ) + (b : ℕ))
          * (Matrix.of fun a b => (Fin.snoc V v : Fin (j + 1) → (Fin k → ℝ)) a (σ b))
            (Fin.last j) b
          * ((Matrix.of fun a b => (Fin.snoc V v : Fin (j + 1) → (Fin k → ℝ)) a (σ b)).submatrix
              (Fin.last j).succAbove b.succAbove).det|
      ≤ ∑ b : Fin (j + 1), |(-1 : ℝ) ^ ((Fin.last j : ℕ) + (b : ℕ))
          * (Matrix.of fun a b => (Fin.snoc V v : Fin (j + 1) → (Fin k → ℝ)) a (σ b))
            (Fin.last j) b
          * ((Matrix.of fun a b => (Fin.snoc V v : Fin (j + 1) → (Fin k → ℝ)) a (σ b)).submatrix
              (Fin.last j).succAbove b.succAbove).det| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b : Fin (j + 1), ‖v‖ * wedgeNorm V := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h1 : (Matrix.of fun a b => (Fin.snoc V v : Fin (j + 1) → (Fin k → ℝ)) a (σ b))
            (Fin.last j) b = v (σ b) := by simp
        have h2 : ((Matrix.of fun a b => (Fin.snoc V v : Fin (j + 1) → (Fin k → ℝ)) a (σ b)).submatrix
            (Fin.last j).succAbove b.succAbove).det = plucker V fun b' => σ (b.succAbove b') := by
          rw [plucker]
          congr 1
          ext a' b'
          simp [Fin.succAbove_last]
        rw [h1, h2, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        exact mul_le_mul (norm_le_pi_norm v (σ b)) (le_wedgeNorm V _) (abs_nonneg _)
          (norm_nonneg _)
    _ = ((j : ℝ) + 1) * wedgeNorm V * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
