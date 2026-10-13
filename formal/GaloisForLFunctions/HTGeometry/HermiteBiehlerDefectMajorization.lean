import GaloisForLFunctions.HTGeometry.RealPartProductRealization

/-!
# Hermite–Biehler with defects: height majorization for any deeper-partner matching

Let `E(z) = ∏_j (z − α_j)(z − β_j) · ∏_k (z − w_k)` with every `w_k` in the closed lower
half-plane, and each pair `(α_j, β_j)` with `Im α_j + Im β_j < 0` (the partner `β_j` lies deeper
below the axis than `α_j` lies above it; `α_j` may be anywhere).  Put

`v_j = Im(α_j β_j) / (Im α_j + Im β_j)`,   `R_j = (v_j − α_j)(v_j − β_j)`;

`v_j` is the real point where `(v − α_j)(v − β_j)` is real, so `R_j` is real, and
`R_j = |v_j − α_j| |v_j − β_j|` when positive.  Then the real polynomial `(E + E^#)/2`, whose real
restriction is `Re E`, satisfies for every `σ ≥ 0`

`Σ_{roots w} (Im w − σ)_+ ≤ Σ_j (√R_j − σ)_+`
(`sum_roots_hermiteBiehlerDefect_le`).

So the heights of the nonreal zeros of `Re E` are weakly submajorized by the geometric means
`√(|v_j − α_j| |v_j − β_j|)` of any matching of the upper roots to deeper lower roots.  For a
vertically aligned pair `α = x + iη`, `β = x − iη'` (`η' > η`) one gets `v = x`, `R = ηη'`, the
cosine-step case.  With no pairs this is the Hermite–Biehler theorem: `Re E` is real-rooted.

**Proof.**  `(z − α)(z − β) = (z − x)(z − v) + R + i c (z − v)` with `c = −(Im α + Im β) > 0` and
`x = Re(α + β) − v` (`pairFactor_eq`), and `z − w = z − Re w + i(−Im w)`; this is the data of the
general realization `realPartMatrixGen`, so `sum_roots_realPartGen_im_sub_pos_le` applies.
-/

open Polynomial Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m l : ℕ}

/-- The real node `v = Im(αβ)/(Im α + Im β)` of a pair. -/
def pairNode (α β : ℂ) : ℝ := (α * β).im / (α.im + β.im)

/-- The second centre `x = Re(α + β) − v`. -/
def pairCentre (α β : ℂ) : ℝ := (α + β).re - pairNode α β

/-- The depth gap `c = −(Im α + Im β)`. -/
def pairGap (α β : ℂ) : ℝ := -(α.im + β.im)

/-- The coupling `R = (v − α)(v − β)` (a real number). -/
def pairCoupling (α β : ℂ) : ℝ := (((pairNode α β : ℂ) - α) * ((pairNode α β : ℂ) - β)).re

theorem im_pairCoupling_eq_zero {α β : ℂ} (h : α.im + β.im ≠ 0) :
    (((pairNode α β : ℂ) - α) * ((pairNode α β : ℂ) - β)).im = 0 := by
  simp only [pairNode, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im]
  field_simp
  ring

/-- **The pair factor in realization form.** -/
theorem pairFactor_eval (α β : ℂ) (h : α.im + β.im ≠ 0) (ε : ℂ) (hε : ε = I ∨ ε = -I) (z : ℂ) :
    (z - (if ε = I then α else (starRingEnd ℂ) α)) * (z - (if ε = I then β else (starRingEnd ℂ) β)) =
      (z - pairCentre α β) * (z - pairNode α β) + pairCoupling α β +
        ε * pairGap α β * (z - pairNode α β) := by
  have hR : ((pairCoupling α β : ℝ) : ℂ) = ((pairNode α β : ℂ) - α) * ((pairNode α β : ℂ) - β) := by
    apply Complex.ext
    · simp [pairCoupling]
    · rw [Complex.ofReal_im, im_pairCoupling_eq_zero h]
  have hv : (pairNode α β : ℝ) * (α.im + β.im) = (α * β).im := by
    rw [pairNode]; field_simp
  rw [Complex.mul_im] at hv
  rcases hε with rfl | rfl
  · simp only [if_true]
    rw [hR]
    apply Complex.ext <;> simp [pairCentre, pairGap, Complex.mul_re, Complex.mul_im] <;> ring
  · have hne : (-I : ℂ) ≠ I := by
      intro h'; have := congrArg Complex.im h'; simp at this; norm_num at this
    simp only [hne, if_false]
    rw [hR]
    apply Complex.ext
    · simp [pairCentre, pairGap, Complex.mul_re, Complex.mul_im]; ring
    · simp [pairCentre, pairGap, Complex.mul_re, Complex.mul_im]; linear_combination 2 * hv

/-- **Height majorization for Hermite–Biehler defects.** -/
theorem sum_roots_hermiteBiehlerDefect_le (α β : Fin m → ℂ) (hdeep : ∀ j, (α j).im + (β j).im < 0)
    (w : Fin l → ℂ) (hw : ∀ k, (w k).im ≤ 0) {σ : ℝ} (hσ : 0 ≤ σ) :
    ((C (1 / 2 : ℂ) *
        ((∏ j, (X - C (α j)) * (X - C (β j))) * ∏ k, (X - C (w k)) +
          ((∏ j, (X - C (α j)) * (X - C (β j))) * ∏ k, (X - C (w k))).map (starRingEnd ℂ))).roots.map
        fun z => max (z.im - σ) 0).sum ≤
      ∑ j, max (Real.sqrt (pairCoupling (α j) (β j)) - σ) 0 := by
  set x : Fin m → ℝ := fun j => pairCentre (α j) (β j)
  set v : Fin m → ℝ := fun j => pairNode (α j) (β j)
  set R : Fin m → ℝ := fun j => pairCoupling (α j) (β j)
  set c : Fin m → ℝ := fun j => pairGap (α j) (β j)
  set s : Fin l → ℝ := fun k => (w k).re
  set t : Fin l → ℝ := fun k => -(w k).im
  have hc : ∀ j, 0 ≤ c j := fun j => by simp only [c, pairGap]; linarith [hdeep j]
  have ht : ∀ k, 0 ≤ t k := fun k => by simp only [t]; linarith [hw k]
  have hne : ∀ j, (α j).im + (β j).im ≠ 0 := fun j => (hdeep j).ne
  have hE : (∏ j, (X - C (α j)) * (X - C (β j))) * ∏ k, (X - C (w k)) =
      realPartFactorGen x v R c s t I := by
    apply Polynomial.funext
    intro z
    rw [eval_realPartFactorGen]
    simp only [eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have := pairFactor_eval (α j) (β j) (hne j) I (Or.inl rfl) z
      simpa using this
    · refine Finset.prod_congr rfl fun k _ => ?_
      apply Complex.ext <;> simp [s, t, sub_eq_add_neg]
  have hEc : ((∏ j, (X - C (α j)) * (X - C (β j))) * ∏ k, (X - C (w k))).map (starRingEnd ℂ) =
      realPartFactorGen x v R c s t (-I) := by
    apply Polynomial.funext
    intro z
    rw [eval_realPartFactorGen]
    simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C,
      eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have hne' : (-I : ℂ) ≠ I := by
        intro h'; have := congrArg Complex.im h'; simp at this; norm_num at this
      have := pairFactor_eval (α j) (β j) (hne j) (-I) (Or.inr rfl) z
      simp only [hne', if_false] at this
      simpa using this
    · refine Finset.prod_congr rfl fun k _ => ?_
      apply Complex.ext <;> simp [s, t, sub_eq_add_neg]
  rw [hEc, hE]
  exact sum_roots_realPartGen_im_sub_pos_le x v R c s t hc ht hσ

end

end GaloisForLFunctions.HTGeometry
