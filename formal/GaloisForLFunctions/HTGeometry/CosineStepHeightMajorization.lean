import GaloisForLFunctions.HTGeometry.RealPartProductRealization
import GaloisForLFunctions.HTGeometry.ShiftAverageNonrealCount
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Height majorization for the cosine step

Let `p = κ ∏_j ((X − x_j)² + y_j²) ∏_k (X − r_k)` be a real polynomial (`pairRootPoly`; every real
polynomial has this form) and `a ≥ 0`.  The roots `w` of the cosine step
`cos(aD)p = (p(z + ia) + p(z − ia))/2` (`shiftAvg a p`) satisfy, for every `σ ≥ 0`,

`Σ_w (Im w − σ)_+ ≤ Σ_j (√(y_j² − a²) − σ)_+`
(`sum_roots_shiftAvg_im_sub_pos_le`),

i.e. the heights of the upper roots are weakly submajorised by the numbers `√(y_j² − a²)` over the
pairs deeper than `a` (`√` of a negative number is `0`).  Integrating over `σ`:

`Σ_{Im w > 0} (Im w)² ≤ Σ_j (y_j² − a²)_+`
(`sum_roots_shiftAvg_sq_im_le`).

This is the cosine imaginary-energy law with its top-`j` refinement.  De Bruijn's strip theorem is
the case `j = 1` of the majorization.

**Proof.**  `p(z ± ia) = κ E_±(z)` with pair factors `(z − x_j)² + (y_j² − a²) ± 2ia (z − x_j)` and
linear factors `z − r_k ± ia` (`map_shiftAvg_pairRootPoly`); the realization of
`RealPartProductRealization` and the pair-coupled Ky Fan bound give the majorization.  The squared
form follows from `(h⁺)²/2 = ∫₀^M (h − σ)_+ dσ` (`integral_max_sub_zero`).
-/

open Polynomial Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m l : ℕ}

/-- The factored real polynomial `κ ∏ ((X − x_j)² + y_j²) ∏ (X − r_k)`. -/
def pairRootPoly (κ : ℝ) (x y : Fin m → ℝ) (r : Fin l → ℝ) : ℝ[X] :=
  C κ * (∏ j, ((X - C (x j)) ^ 2 + C (y j ^ 2))) * ∏ k, (X - C (r k))

theorem eval_map_pairRootPoly (κ : ℝ) (x y : Fin m → ℝ) (r : Fin l → ℝ) (w : ℂ) :
    ((pairRootPoly κ x y r).map ofRealHom).eval w =
      κ * (∏ j, ((w - x j) ^ 2 + (y j : ℂ) ^ 2)) * ∏ k, (w - r k) := by
  simp [pairRootPoly, Polynomial.map_prod, eval_prod]

/-- **The cosine step of `pairRootPoly` is the real part of a shifted product.** -/
theorem map_shiftAvg_pairRootPoly (κ : ℝ) (x y : Fin m → ℝ) (r : Fin l → ℝ) (a : ℝ) :
    (shiftAvg a (pairRootPoly κ x y r)).map ofRealHom =
      C (κ : ℂ) * (C (1 / 2 : ℂ) *
        (realPartFactor x (fun j => y j ^ 2 - a ^ 2) (fun _ => 2 * a) r (fun _ => a) I +
          realPartFactor x (fun j => y j ^ 2 - a ^ 2) (fun _ => 2 * a) r (fun _ => a) (-I))) := by
  apply Polynomial.funext
  intro z
  rw [eval_map_shiftAvg, eval_map_pairRootPoly, eval_map_pairRootPoly]
  simp only [eval_mul, eval_C, eval_add, eval_realPartFactor]
  have h1 : ∏ j, ((z + a * I - x j) ^ 2 + (y j : ℂ) ^ 2) =
      ∏ j, ((z - x j) ^ 2 + ((y j ^ 2 - a ^ 2 : ℝ) : ℂ) + I * ((2 * a : ℝ) : ℂ) * (z - x j)) :=
    Finset.prod_congr rfl fun j _ => by push_cast; linear_combination (a : ℂ) ^ 2 * I_sq
  have h2 : ∏ j, ((z - a * I - x j) ^ 2 + (y j : ℂ) ^ 2) =
      ∏ j, ((z - x j) ^ 2 + ((y j ^ 2 - a ^ 2 : ℝ) : ℂ) + -I * ((2 * a : ℝ) : ℂ) * (z - x j)) :=
    Finset.prod_congr rfl fun j _ => by push_cast; linear_combination (a : ℂ) ^ 2 * I_sq
  have h3 : ∏ k, (z + a * I - r k) = ∏ k, (z - r k + I * ((a : ℝ) : ℂ)) :=
    Finset.prod_congr rfl fun k _ => by ring
  have h4 : ∏ k, (z - a * I - r k) = ∏ k, (z - r k + -I * ((a : ℝ) : ℂ)) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [h1, h2, h3, h4]
  ring

/-- **Height majorization for the cosine step.** -/
theorem sum_roots_shiftAvg_im_sub_pos_le (κ : ℝ) (hκ : κ ≠ 0) (x y : Fin m → ℝ) (r : Fin l → ℝ)
    {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 ≤ σ) :
    (((shiftAvg a (pairRootPoly κ x y r)).map ofRealHom).roots.map
        fun w => max (w.im - σ) 0).sum ≤ ∑ j, max (Real.sqrt (y j ^ 2 - a ^ 2) - σ) 0 := by
  rw [map_shiftAvg_pairRootPoly, roots_C_mul _ (by exact_mod_cast hκ)]
  exact sum_roots_realPart_im_sub_pos_le x (fun j => y j ^ 2 - a ^ 2) (fun _ => 2 * a) r
    (fun _ => a) (fun _ => by linarith) (fun _ => ha) hσ

/-- `∫₀^M (h − σ)_+ dσ = (h⁺)²/2` for `h ≤ M`, `0 ≤ M`. -/
theorem integral_max_sub_zero {h M : ℝ} (hM : h ≤ M) (hM0 : 0 ≤ M) :
    ∫ σ in (0 : ℝ)..M, max (h - σ) 0 = (max h 0) ^ 2 / 2 := by
  have hcont : Continuous fun σ : ℝ => max (h - σ) 0 := by fun_prop
  rcases le_total h 0 with h0 | h0
  · rw [max_eq_right h0]
    have : Set.EqOn (fun σ : ℝ => max (h - σ) 0) (fun _ => (0 : ℝ)) (Set.uIcc 0 M) := by
      intro σ hσ
      rw [Set.uIcc_of_le hM0] at hσ
      exact max_eq_right (by linarith [hσ.1])
    rw [intervalIntegral.integral_congr this]
    simp
  · rw [max_eq_left h0, ← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 h) (hcont.intervalIntegrable h M)]
    have e1 : Set.EqOn (fun σ : ℝ => max (h - σ) 0) (fun σ => h - σ) (Set.uIcc 0 h) := by
      intro σ hσ
      rw [Set.uIcc_of_le h0] at hσ
      exact max_eq_left (by linarith [hσ.2])
    have e2 : Set.EqOn (fun σ : ℝ => max (h - σ) 0) (fun _ => (0 : ℝ)) (Set.uIcc h M) := by
      intro σ hσ
      rw [Set.uIcc_of_le hM] at hσ
      exact max_eq_right (by linarith [hσ.1])
    rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      intervalIntegral.integral_const, integral_id]
    simp
    ring

/-- **Weak majorization controls squares.**  If `Σ_{h∈s} (h − σ)_+ ≤ Σ_j (ρ_j − σ)_+` for all
`σ ≥ 0`, then `Σ_{h∈s} (h⁺)² ≤ Σ_j ρ_j²` (`ρ_j ≥ 0`). -/
theorem sum_sq_le_of_forall_sum_max_sub_le (s : Multiset ℝ) (ρ : Fin m → ℝ) (hρ : ∀ j, 0 ≤ ρ j)
    (h : ∀ σ, 0 ≤ σ → (s.map fun h => max (h - σ) 0).sum ≤ ∑ j, max (ρ j - σ) 0) :
    (s.map fun h => (max h 0) ^ 2).sum ≤ ∑ j, ρ j ^ 2 := by
  set M : ℝ := (s.map fun h => |h|).sum + ∑ j, ρ j with hMdef
  have hS0 : 0 ≤ (s.map fun h => |h|).sum :=
    Multiset.sum_nonneg fun z hz => by
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hz; exact abs_nonneg w
  have hρ0 : 0 ≤ ∑ j, ρ j := Finset.sum_nonneg fun j _ => hρ j
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith
  have hsM : ∀ w ∈ s, w ≤ M := by
    intro w hw
    have h1 : |w| ≤ (s.map fun h => |h|).sum :=
      Multiset.single_le_sum (fun z hz => by
        obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hz; exact abs_nonneg u) _
        (Multiset.mem_map_of_mem _ hw)
    have := le_abs_self w
    rw [hMdef]; linarith
  have hρM : ∀ j, ρ j ≤ M := by
    intro j
    have : ρ j ≤ ∑ j, ρ j := Finset.single_le_sum (fun i _ => hρ i) (Finset.mem_univ j)
    rw [hMdef]; linarith
  -- integrate the hypothesis over `[0, M]`
  have hcontL : ∀ t : Multiset ℝ, Continuous fun σ : ℝ => (t.map fun h => max (h - σ) 0).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp; fun_prop
    | cons w t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (by fun_prop : Continuous fun σ : ℝ => max (w - σ) 0).add ih
  have hintL : ∀ t : Multiset ℝ, (∀ w ∈ t, w ≤ M) →
      ∫ σ in (0 : ℝ)..M, (t.map fun h => max (h - σ) 0).sum =
        (t.map fun h => (max h 0) ^ 2 / 2).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intro _; simp
    | cons w t ih =>
      intro ht
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous fun σ : ℝ => max (w - σ) 0).intervalIntegrable 0 M)
        ((hcontL t).intervalIntegrable 0 M),
        integral_max_sub_zero (ht w (Multiset.mem_cons_self w t)) hM0,
        ih fun u hu => ht u (Multiset.mem_cons_of_mem hu)]
  have hcontR : Continuous fun σ : ℝ => ∑ j, max (ρ j - σ) 0 := by fun_prop
  have hintR : ∫ σ in (0 : ℝ)..M, ∑ j, max (ρ j - σ) 0 = ∑ j, ρ j ^ 2 / 2 := by
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (by fun_prop : Continuous fun σ : ℝ => max (ρ j - σ) 0).intervalIntegrable 0 M]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_max_sub_zero (hρM j) hM0, max_eq_left (hρ j)]
  have hmono : ∫ σ in (0 : ℝ)..M, (s.map fun h => max (h - σ) 0).sum ≤
      ∫ σ in (0 : ℝ)..M, ∑ j, max (ρ j - σ) 0 :=
    intervalIntegral.integral_mono_on hM0 ((hcontL s).intervalIntegrable 0 M)
      (hcontR.intervalIntegrable 0 M) fun σ hσ => h σ hσ.1
  rw [hintL s hsM, hintR] at hmono
  have e1 : (s.map fun h => (max h 0) ^ 2 / 2).sum = (s.map fun h => (max h 0) ^ 2).sum / 2 := by
    rw [Multiset.sum_map_div]
  rw [e1, ← Finset.sum_div] at hmono
  linarith

/-- **The cosine imaginary-energy law (CSS+).**  `Σ_{Im w > 0} (Im w)² ≤ Σ_j (y_j² − a²)_+` over
the roots of `cos(aD)p`. -/
theorem sum_roots_shiftAvg_sq_im_le (κ : ℝ) (hκ : κ ≠ 0) (x y : Fin m → ℝ) (r : Fin l → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    (((shiftAvg a (pairRootPoly κ x y r)).map ofRealHom).roots.map
        fun w => (max w.im 0) ^ 2).sum ≤ ∑ j, max (y j ^ 2 - a ^ 2) 0 := by
  have h := sum_sq_le_of_forall_sum_max_sub_le
    (((shiftAvg a (pairRootPoly κ x y r)).map ofRealHom).roots.map Complex.im)
    (fun j => Real.sqrt (y j ^ 2 - a ^ 2)) (fun j => Real.sqrt_nonneg _)
    (fun σ hσ => by
      rw [Multiset.map_map]
      exact sum_roots_shiftAvg_im_sub_pos_le κ hκ x y r ha hσ)
  rw [Multiset.map_map] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rcases le_total 0 (y j ^ 2 - a ^ 2) with h0 | h0
  · rw [Real.sq_sqrt h0, max_eq_left h0]
  · rw [Real.sqrt_eq_zero'.mpr h0, max_eq_right h0]; ring

end

end GaloisForLFunctions.HTGeometry
