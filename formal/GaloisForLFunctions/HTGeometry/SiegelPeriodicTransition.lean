import GaloisForLFunctions.HTGeometry.SiegelLatticeTransition
import GaloisForLFunctions.HTGeometry.SiegelAlgebraicRelation

/-!
# Discharging the period from a transition

A torus point is congruent to a point of some small polydisc, so the transition that a chartwise
Siegel argument needs comes with a translation by a period.  Periodicity of the chart data removes
it: the cleared combination takes the same value at the translated point as at the point of the
polydisc.

What is left after the period is discharged is exactly the transition structure the chart comparison
consumes — a bounded factor relating the value on the large torus to a value on a small polydisc —
so the whole chain from the lattice geometry to a nonzero algebraic relation composes.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n m : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- **Periodicity discharges the period of a transition.** -/
theorem htrans_of_periodic_transfer (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (c : ι → (Fin n → ℂ)) {r R C : ℝ} (a : (Fin (n + 1) → Fin (m + 1)) → ℂ)
    (hmove : ∀ (i : ι) (t : Fin n → ℝ), ∃ (j : ι) (y : Fin n → ℂ) (p : Fin n → ℂ) (u : ℂ),
      ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧
      (∀ k w, A j k (w + p) = A j k w) ∧ (∀ k w, B j k (w + p) = B j k w) ∧
      siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
        = u * siegelHomCombination (A j) (B j) m a (c j + y + p)) :
    ∀ (i : ι) (t : Fin n → ℝ), ∃ (j : ι) (y : Fin n → ℂ) (u : ℂ),
      ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧
      siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
        = u * siegelHomCombination (A j) (B j) m a (c j + y) := by
  intro i t
  obtain ⟨j, y, p, u, hy, hu, hAper, hBper, heq⟩ := hmove i t
  refine ⟨j, y, u, hy, hu, ?_⟩
  rw [heq, siegelHomCombination_periodic (A j) (B j) a hAper hBper]

/-- **The chartwise assembly with the period discharged.** -/
theorem exists_ne_zero_chart_vanishing_of_periodic [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hA : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (A i k)) (hB : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (B i k))
    (c : ι → (Fin n → ℂ)) {R r C : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hC : 0 ≤ C)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (hmove : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (i : ι) (t : Fin n → ℝ),
      ∃ (j : ι) (y : Fin n → ℂ) (p : Fin n → ℂ) (u : ℂ), ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧
        (∀ k w, A j k (w + p) = A j k w) ∧ (∀ k w, B j k (w + p) = B j k w) ∧
        siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
          = u * siegelHomCombination (A j) (B j) m a (c j + y + p))
    (hlt : C * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) < 1) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
        siegelHomCombination (A i) (B i) m a (c i + y) = 0 :=
  exists_ne_zero_chart_vanishing_of_transition (N := N) A B hA hB c hR hr hrR hC hcount
    (fun a => htrans_of_periodic_transfer A B c a (hmove a)) hlt

/-- **The full chain.**  From the periodic transition structure to a nonzero algebraic relation
among the chart quotients on the small polydiscs. -/
theorem exists_ne_zero_poly_eval_eq_zero_of_periodic [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hA : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (A i k)) (hB : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (B i k))
    (c : ι → (Fin n → ℂ)) {R r C : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hC : 0 ≤ C)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (hmove : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (i : ι) (t : Fin n → ℝ),
      ∃ (j : ι) (y : Fin n → ℂ) (p : Fin n → ℂ) (u : ℂ), ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧
        (∀ k w, A j k (w + p) = A j k w) ∧ (∀ k w, B j k (w + p) = B j k w) ∧
        siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
          = u * siegelHomCombination (A j) (B j) m a (c j + y + p))
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
    exists_ne_zero_chart_vanishing_of_periodic (N := N) A B hA hB c hR hr hrR hC hcount hmove hlt
  refine ⟨siegelPoly a, siegelPoly_ne_zero ha, ?_⟩
  intro i y hy
  have hquotvan : siegelCombination (fun k w => A i k w / B i k w) a (c i + y) = 0 :=
    siegelCombination_eq_zero_of_hom_eq_zero (A i) (B i) a (c i + y) (hden i y hy) (hvan i y hy)
  have hcong : siegelCombination f a (c i + y)
      = siegelCombination (fun k w => A i k w / B i k w) a (c i + y) :=
    siegelCombination_congr f (fun k w => A i k w / B i k w) a (c i + y)
      (fun k => hquot i y hy k)
  rw [eval_siegelPoly_eq_siegelCombination, hcong, hquotvan]

end GaloisForLFunctions.HTGeometry
