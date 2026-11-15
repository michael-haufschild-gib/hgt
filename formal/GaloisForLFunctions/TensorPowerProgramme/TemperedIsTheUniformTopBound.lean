import GaloisForLFunctions.TensorPowerProgramme.APolarizedBaseWhoseAdamsSquaresContinueIsPure

/-!
# Tempered is the uniform top bound

The uniformity stage of the tensor-power route asks for constants and top bounds uniform in the
period. For a polarized base the top bound `1` of every Adams power is exactly temperedness:

* **Tempered data have top bound one** (`adamsPoleLaw_of_norm_eq_one`). If every parameter at a
  point of positive weight is unitary and the base series `Σ_{x,n} λ(x) N(x)^{−ns}` converges on
  `Re s > 1`, the Rankin–Selberg square of every Adams power converges on `Re s > 1`, with
  coefficients at most `(2g)²λ(x)` uniformly in the power.
* **Top bound one for all powers is temperedness** (`adamsPoleLaw_iff`): with
  `norm_eq_one_of_adamsPoleLaw`, the pole law of the Adams squares holds iff every parameter at a
  point of positive weight is unitary.

So a uniform top bound is never a by-product of a family of growing degree: it is the Ramanujan
property of its members. A route that needs the top bound `1` for all periods needs tempered
members at all periods.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

variable {ι : Type*} {g : ℕ}

/-- A unitary parameter has Adams traces of size at most `2g`. -/
theorem norm_adamsTrace_le {α : ι → Fin g → ℂ} {x : ι} (hx : ∀ i, ‖α x i‖ = 1) (m n : ℕ) :
    ‖adamsTrace α m n x‖ ≤ 2 * g := by
  rw [adamsTrace]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖(α x i) ^ (m * n) + (α x i)⁻¹ ^ (m * n)‖ ≤ ∑ _i : Fin g, (2 : ℝ) :=
        Finset.sum_le_sum fun i _ => by
          refine (norm_add_le _ _).trans ?_
          rw [norm_pow, norm_pow, norm_inv, hx i]
          norm_num
    _ = 2 * g := by simp [mul_comm]

/-- **Tempered data have top bound one for every Adams power.** -/
theorem adamsPoleLaw_of_norm_eq_one {ℓ lam : ι → ℝ} {α : ι → Fin g → ℂ} (hℓ : ∀ x, 0 ≤ ℓ x)
    (hlam : ∀ x, 0 ≤ lam x)
    (hbase : ∀ σ : ℝ, 1 < σ →
      Summable (gdTwistTerm (fun p : ι × ℕ => lam p.1) (levelFreq ℓ) σ 0))
    (hpure : ∀ x, 0 < lam x → ∀ i, ‖α x i‖ = 1) : AdamsPoleLaw ℓ lam α := by
  intro m _
  have ha := adamsSquareCoeff_nonneg hlam α m
  have hf := levelFreq_nonneg hℓ
  -- the square coefficients are at most (2g)² λ(x)
  have hcoef : ∀ p : ι × ℕ, adamsSquareCoeff lam α m p ≤ (2 * g) ^ 2 * lam p.1 := by
    intro p
    rcases (hlam p.1).lt_or_eq with hp | hp
    · have ht := norm_adamsTrace_le (hpure p.1 hp) m (p.2 + 1)
      have hre : |(adamsTrace α m (p.2 + 1) p.1).re| ≤ 2 * g :=
        (Complex.abs_re_le_norm _).trans ht
      rw [adamsSquareCoeff, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (hlam _)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hre 2
    · rw [adamsSquareCoeff, ← hp]
      simp
  have hsum : ∀ σ : ℝ, 1 < σ →
      Summable (gdTwistTerm (adamsSquareCoeff lam α m) (levelFreq ℓ) σ 0) := fun σ hσ =>
    Summable.of_nonneg_of_le (gdTwistTerm_nonneg ha hf σ 0) (fun p => by
      simp only [gdTwistTerm, pow_zero, mul_one]
      calc adamsSquareCoeff lam α m p * Real.exp (-(σ * levelFreq ℓ p))
          ≤ (2 * g) ^ 2 * lam p.1 * Real.exp (-(σ * levelFreq ℓ p)) :=
            mul_le_mul_of_nonneg_right (hcoef p) (Real.exp_pos _).le
        _ = (2 * g) ^ 2 * (lam p.1 * Real.exp (-(σ * levelFreq ℓ p))) := by ring)
      (by simpa [gdTwistTerm] using (hbase σ hσ).mul_left ((2 * g) ^ 2))
  refine ⟨2, hsum 2 (by norm_num), gdSeries (adamsSquareCoeff lam α m) (levelFreq ℓ),
    fun s hs => ?_, fun s _ => rfl⟩
  have hs1 : 1 < s.re := hs
  exact (RHTower.differentiableAt_gdSeries ha hf (hsum ((1 + s.re) / 2) (by linarith))
    (by linarith)).differentiableWithinAt

/-- **Top bound one for every Adams power is temperedness.** -/
theorem adamsPoleLaw_iff {ℓ lam : ι → ℝ} {α : ι → Fin g → ℂ} (hℓ : ∀ x, 0 ≤ ℓ x)
    (hlam : ∀ x, 0 ≤ lam x) (hα : ∀ x i, α x i ≠ 0)
    (hreal : ∀ m n x, (adamsTrace α m n x).im = 0)
    (hbase : ∀ σ : ℝ, 1 < σ →
      Summable (gdTwistTerm (fun p : ι × ℕ => lam p.1) (levelFreq ℓ) σ 0)) :
    AdamsPoleLaw ℓ lam α ↔ ∀ x, 0 < lam x → ∀ i, ‖α x i‖ = 1 :=
  ⟨fun h _ hx i => norm_eq_one_of_adamsPoleLaw hℓ hlam hα hreal h hx i,
    adamsPoleLaw_of_norm_eq_one hℓ hlam hbase⟩

end GaloisForLFunctions.TensorPowerProgramme
