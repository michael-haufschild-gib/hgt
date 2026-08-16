import GaloisForLFunctions.HTGeometry.SiegelChartAssembly

/-!
# The algebraic relation produced by a Siegel count

The last link.  Where the chart denominators do not vanish, the vanishing of the cleared
combinations is the vanishing of the combination of the quotients, and that combination is the
evaluation of a polynomial whose coefficients are the ones the count produced.  Since the
coefficient vector is nonzero the polynomial is nonzero, so the count really does witness an
algebraic relation among the given functions on the union of the small polydiscs.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {n m : ℕ} {ι : Type*} [Fintype ι]

/-- The combination depends on the functions only through their values at the point. -/
theorem siegelCombination_congr {E : Type*} (g h : Fin (n + 1) → E → ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (w : E) (hgh : ∀ k, g k w = h k w) :
    siegelCombination g a w = siegelCombination h a w := by
  simp only [siegelCombination]
  refine Finset.sum_congr rfl fun β _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hgh k]

/-- **The Siegel count produces a nonzero algebraic relation.**  On the small polydiscs of a chart
family, a nonzero polynomial annihilates the given functions. -/
theorem exists_ne_zero_poly_eval_eq_zero [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hA : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (A i k)) (hB : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (B i k))
    (c : ι → (Fin n → ℂ)) {R r C : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (hcomp : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (M : ℝ),
      (∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
          ‖siegelHomCombination (A i) (B i) m a (c i + y)‖ ≤ M) →
      ∀ (i : ι) (t : Fin n → ℝ),
        ‖siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)‖ ≤ C * M)
    (hlt : C * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) < 1)
    (f : Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hden : ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ∀ k, B i k (c i + y) ≠ 0)
    (hquot : ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ∀ k,
      f k (c i + y) = A i k (c i + y) / B i k (c i + y)) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
        MvPolynomial.eval (fun k => f k (c i + y)) P = 0 := by
  obtain ⟨a, ha, hvan⟩ :=
    exists_ne_zero_chart_vanishing (N := N) A B hA hB c hR hr hrR hcount hcomp hlt
  refine ⟨siegelPoly a, siegelPoly_ne_zero ha, ?_⟩
  intro i y hy
  have hquotvan : siegelCombination
      (fun k w => A i k w / B i k w) a (c i + y) = 0 :=
    siegelCombination_eq_zero_of_hom_eq_zero (A i) (B i) a (c i + y) (hden i y hy) (hvan i y hy)
  have hcong : siegelCombination f a (c i + y)
      = siegelCombination (fun k w => A i k w / B i k w) a (c i + y) :=
    siegelCombination_congr f (fun k w => A i k w / B i k w) a (c i + y)
      (fun k => hquot i y hy k)
  rw [eval_siegelPoly_eq_siegelCombination, hcong, hquotvan]

end GaloisForLFunctions.HTGeometry
