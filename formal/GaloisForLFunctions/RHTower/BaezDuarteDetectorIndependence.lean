import GaloisForLFunctions.RHTower.BaezDuarteDetectorGram
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The detectors are independent, so the Cauchy kernel is positive definite

`BaezDuarteDetectorGram` identifies the corpus's `rightHalfPlaneHardyCauchyGram` as the Gram matrix of the
Mellin detector vectors.  Mathlib's Gram theory (`Matrix.posDef_gram_iff_linearIndependent`) then converts
a statement about the matrix into a statement about the vectors, and the vectors are easy to handle: a
vanishing combination of detectors, tested against another detector, is a partial-fraction identity

`∑_i a_i / (c_i − t) = 0`  for every `t` in the half-plane,  `c_i = 1 − conj s_i`,

and clearing denominators turns it into a polynomial vanishing on an infinite set.  Evaluating that
polynomial at `c_k` isolates `a_k`.

Consequences, all unconditional:

* `linearIndependent_bdDetector` — detectors at distinct points of `Re s < ½` are linearly independent;
* `rightHalfPlaneHardyCauchyGram_eq_gram` — the identification, as a matrix equation;
* **`rightHalfPlaneHardyCauchyGram_posDef`** — the Cauchy kernel `1/(w_i + conj w_j)` at *distinct* points
  with `Re w > 0` is positive **definite**, not merely semidefinite as
  `rightHalfPlaneHardyCauchyGram_posSemidef` states;
* `det_rightHalfPlaneHardyCauchyGram_ne_zero` — hence nonsingular.  This is the nonvanishing of the
  Cauchy determinant, obtained without the determinant formula (mathlib has no Cauchy determinant).

For the Nyman--Beurling floor this says the many-zero bound is nondegenerate: `n` distinct zeros give `n`
linearly independent detectors, so an orthonormal family of full size exists inside their span and every
zero contributes to `bdTarget_dist_floor_orthonormal`.
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace RHTower

/-- The pole locations attached to a family of detector parameters. -/
private def polePoint (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

private theorem polePoint_injective {n : ℕ} {s : Fin n → ℂ} (hinj : Function.Injective s) :
    Function.Injective (fun i => polePoint (s i)) := by
  intro i j hij
  simp only [polePoint, sub_right_inj] at hij
  exact hinj ((starRingEnd ℂ).injective hij)

/-- The half-plane `Re t < ½` is infinite. -/
private theorem infinite_halfPlane : {t : ℂ | t.re < 1 / 2}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((-(k : ℝ) : ℝ) : ℂ)) ?_ ?_
  · intro a b hab
    simp only [Complex.ofReal_inj, neg_inj, Nat.cast_inj] at hab
    exact hab
  · intro k
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

/-- **The detectors at distinct points are linearly independent.** -/
theorem linearIndependent_bdDetector {n : ℕ} (s : Fin n → ℂ) (hs : ∀ i, (s i).re < 1 / 2)
    (hinj : Function.Injective s) :
    LinearIndependent ℂ (fun i => bdDetector (hs i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a hcomb
  set c : Fin n → ℂ := fun i => polePoint (s i) with hc
  have hcinj : Function.Injective c := polePoint_injective hinj
  have hcre : ∀ i, 1 / 2 < (c i).re := by
    intro i
    have := hs i
    simp only [hc, polePoint, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  -- pairing a vanishing combination with another detector
  have hsum : ∀ t : ℂ, (ht : t.re < 1 / 2) → ∑ i, a i / (c i - t) = 0 := by
    intro t ht
    have h0 : inner ℂ (bdDetector ht) (∑ i, a i • bdDetector (hs i)) = 0 := by
      rw [hcomb, inner_zero_right]
    rw [inner_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, inner_bdDetector_bdDetector ht (hs i)]
    simp only [hc, polePoint]
    ring
  -- the cleared polynomial
  set Q : Polynomial ℂ :=
    ∑ i : Fin n, Polynomial.C (a i) *
      ∏ j ∈ Finset.univ.erase i, (Polynomial.C (c j) - Polynomial.X) with hQ
  have hQeval : ∀ t : ℂ,
      Polynomial.eval t Q = ∑ i : Fin n, a i * ∏ j ∈ Finset.univ.erase i, (c j - t) := by
    intro t
    rw [hQ, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Polynomial.eval_prod]
  have hroots : ∀ t : ℂ, t.re < 1 / 2 → Polynomial.eval t Q = 0 := by
    intro t ht
    have hne : ∀ j, c j - t ≠ 0 := by
      intro j hj
      have hre : (c j - t).re = 0 := by rw [hj, Complex.zero_re]
      rw [Complex.sub_re] at hre
      have := hcre j
      linarith
    have hmul := congrArg (fun z : ℂ => z * ∏ j : Fin n, (c j - t)) (hsum t ht)
    simp only [zero_mul, Finset.sum_mul] at hmul
    rw [hQeval t, ← hmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hprod : (∏ j ∈ Finset.univ.erase i, (c j - t)) * (c i - t)
        = ∏ j : Fin n, (c j - t) :=
      Finset.prod_erase_mul Finset.univ (fun j => c j - t) (Finset.mem_univ i)
    have hi := hne i
    rw [← hprod]
    field_simp
  have hQzero : Q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot Q ?_
    refine Set.Infinite.mono ?_ infinite_halfPlane
    intro t ht
    exact hroots t ht
  -- evaluating at a pole isolates one coefficient
  intro k
  have hevalk : Polynomial.eval (c k) Q = a k * ∏ j ∈ Finset.univ.erase k, (c j - c k) := by
    rw [hQeval (c k)]
    refine Finset.sum_eq_single k (fun i _ hik => ?_) (fun hk => absurd (Finset.mem_univ k) hk)
    have hmem : k ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ k⟩
    rw [Finset.prod_eq_zero hmem (by ring), mul_zero]
  rw [hQzero] at hevalk
  simp only [Polynomial.eval_zero] at hevalk
  have hprodne : (∏ j ∈ Finset.univ.erase k, (c j - c k)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr fun h => hjk (hcinj h)
  exact (mul_eq_zero.mp hevalk.symm).resolve_right hprodne

/-! ## Consequences for the Cauchy kernel -/

/-- The corpus's Cauchy kernel is the Gram matrix of the detectors, as a matrix equation. -/
theorem rightHalfPlaneHardyCauchyGram_eq_gram {n : ℕ} (w : Fin n → ℂ) (hw : ∀ i, 0 < (w i).re)
    (hs : ∀ i, ((1 : ℂ) / 2 - w i).re < 1 / 2) :
    rightHalfPlaneHardyCauchyGram w = Matrix.gram ℂ (fun i => bdDetector (hs i)) := by
  ext i j
  rw [Matrix.gram_apply, ← inner_bdDetector_eq_cauchyGram w hw i j]

private theorem half_sub_re_lt {w : ℂ} (hw : 0 < w.re) : ((1 : ℂ) / 2 - w).re < 1 / 2 := by
  rw [Complex.sub_re]
  norm_num
  linarith

/-- **The Cauchy kernel at distinct points is positive definite.**  The corpus proves positive
*semi*definiteness by an explicit boundary integral; distinctness upgrades it, structurally, through the
linear independence of the detectors. -/
theorem rightHalfPlaneHardyCauchyGram_posDef {n : ℕ} (w : Fin n → ℂ) (hw : ∀ i, 0 < (w i).re)
    (hinj : Function.Injective w) :
    (rightHalfPlaneHardyCauchyGram w).PosDef := by
  have hs : ∀ i, ((1 : ℂ) / 2 - w i).re < 1 / 2 := fun i => half_sub_re_lt (hw i)
  rw [rightHalfPlaneHardyCauchyGram_eq_gram w hw hs]
  refine Matrix.posDef_gram_iff_linearIndependent.mpr ?_
  refine linearIndependent_bdDetector (fun i => (1 : ℂ) / 2 - w i) hs ?_
  intro i j hij
  exact hinj (by linear_combination -hij)

/-- Hence the Cauchy determinant does not vanish — without the determinant formula. -/
theorem det_rightHalfPlaneHardyCauchyGram_ne_zero {n : ℕ} (w : Fin n → ℂ)
    (hw : ∀ i, 0 < (w i).re) (hinj : Function.Injective w) :
    (rightHalfPlaneHardyCauchyGram w).det ≠ 0 := by
  have hs : ∀ i, ((1 : ℂ) / 2 - w i).re < 1 / 2 := fun i => half_sub_re_lt (hw i)
  rw [rightHalfPlaneHardyCauchyGram_eq_gram w hw hs]
  refine Matrix.det_gram_ne_zero_iff_linearIndependent.mpr ?_
  refine linearIndependent_bdDetector (fun i => (1 : ℂ) / 2 - w i) hs ?_
  intro i j hij
  exact hinj (by linear_combination -hij)

/-- The detectors at distinct zeta zeros in the right half of the strip are linearly independent, so the
many-zero floor is nondegenerate. -/
theorem linearIndependent_bdDetector_zeros {n : ℕ} (ρ : Fin n → ℂ)
    (hρ : ∀ j, 1 / 2 < (ρ j).re) (hinj : Function.Injective ρ) :
    LinearIndependent ℂ (fun j => bdDetector (one_sub_re_lt (hρ j))) := by
  refine linearIndependent_bdDetector (fun j => 1 - ρ j) (fun j => one_sub_re_lt (hρ j)) ?_
  intro i j hij
  exact hinj (by linear_combination -hij)

end RHTower

end
