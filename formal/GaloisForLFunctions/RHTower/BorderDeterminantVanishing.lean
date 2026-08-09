import GaloisForLFunctions.RHTower.FiniteSectionBorderDeterminant
import GaloisForLFunctions.RHTower.SamplingDeterminant

/-!
# Vanishing at every sample is a relation among the row functions

`FiniteSectionBorderDeterminant` shows that one nonvanishing bordered determinant certifies a positive
Báez-Duarte distance.  The remaining question is whether such a sample exists, and `SamplingDeterminant`
answers it in the only way available: a determinant vanishing at *every* sample is a linear relation among
the row functions.

The rows are the functions on the open strip

`Fᵢ(s) = −(θᵢ^s − θᵢ)·ζ(s)/s` for `i < N`,  `F_N(s) = 1/s`,

and `sampledBorderMatrix` is their evaluation matrix.  Hence

**`exists_relation_of_forall_det_eq_zero` — if every bordered determinant vanishes there are coefficients
`c`, not all zero, with `(∑ᵢ cᵢ(θᵢ^s − θᵢ))·ζ(s) = c_N` at every point of the strip.**

Read forwards instead, this is the reusable interface: `bdDist_pos_of_linearIndependent_borderRowFun` says a
positive distance follows from linear independence of the pairing functions alone, so another family inherits
the route by proving independence for its own pairings.

So a finite section escapes every determinant certificate only if the Müntz system `θ^s − θ` inverts `ζ` by
a *single* relation valid on the whole strip — not merely sample by sample. That is a rigid identity between
`ζ` and an entire function, which is what the next step contradicts.
-/

open Complex

noncomputable section

namespace RHTower

/-- The open strip `½ < Re s < 1`, as the domain of the row functions. -/
abbrev StripPoint := {s : ℂ // 1 / 2 < s.re ∧ s.re < 1}

/-- The row functions of the bordered matrix: the `N` generator pairings, then the target pairing. -/
def borderRowFun {N : ℕ} (θ : Fin N → ℝ) : Fin (N + 1) → (StripPoint → ℂ) :=
  (Fin.snoc
    (fun (i : Fin N) (s : StripPoint) =>
      -(((θ i : ℝ) : ℂ) ^ (s : ℂ) - ((θ i : ℝ) : ℂ)) * (riemannZeta (s : ℂ) / (s : ℂ)))
    (fun (s : StripPoint) => 1 / (s : ℂ)) : Fin (N + 1) → (StripPoint → ℂ))

theorem borderRowFun_castSucc {N : ℕ} (θ : Fin N → ℝ) (i : Fin N) (s : StripPoint) :
    borderRowFun θ i.castSucc s
      = -(((θ i : ℝ) : ℂ) ^ (s : ℂ) - ((θ i : ℝ) : ℂ)) * (riemannZeta (s : ℂ) / (s : ℂ)) := by
  simp [borderRowFun]

theorem borderRowFun_last {N : ℕ} (θ : Fin N → ℝ) (s : StripPoint) :
    borderRowFun θ (Fin.last N) s = 1 / (s : ℂ) := by
  simp [borderRowFun]

/-- The evaluation matrix of the row functions is the bordered matrix of sampled pairings. -/
theorem matrix_borderRowFun_eq_sampledBorderMatrix {N : ℕ} (θ : Fin N → ℝ)
    (x : Fin (N + 1) → StripPoint) :
    (Matrix.of fun i j => borderRowFun θ i (x j))
      = sampledBorderMatrix θ fun j => ((x j : ℂ)) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ ?_ i
  · rw [Matrix.of_apply, borderRowFun_last, sampledBorderMatrix_last]
  · intro i'
    rw [Matrix.of_apply, borderRowFun_castSucc, sampledBorderMatrix_castSucc]

/-- If every bordered determinant vanishes, the row functions are linearly dependent. -/
theorem not_linearIndependent_borderRowFun {N : ℕ} (θ : Fin N → ℝ)
    (h : ∀ ρ : Fin (N + 1) → ℂ, (∀ j, 1 / 2 < (ρ j).re) → (∀ j, (ρ j).re < 1) →
      (sampledBorderMatrix θ ρ).det = 0) :
    ¬ LinearIndependent ℂ (borderRowFun θ) := by
  refine not_linearIndependent_of_forall_det_eq_zero _ fun x => ?_
  rw [matrix_borderRowFun_eq_sampledBorderMatrix θ x]
  exact h _ (fun j => (x j).2.1) (fun j => (x j).2.2)

/-- **A single relation on the whole strip.**  A linear dependence among the pairing functions is, after
clearing the `1/s`, one fixed coefficient vector inverting `ζ` against the Müntz system at every point of the
strip. -/
theorem muentz_relation_of_not_linearIndependent {N : ℕ} (θ : Fin N → ℝ)
    (h : ¬ LinearIndependent ℂ (borderRowFun θ)) :
    ∃ c : Fin (N + 1) → ℂ, (∃ i, c i ≠ 0) ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))) * riemannZeta s
        = c (Fin.last N) := by
  obtain ⟨c, hrel, hne⟩ := Fintype.not_linearIndependent_iff.1 h
  refine ⟨c, hne, fun s hs hs1 => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    norm_num at hs
  -- evaluate the relation at the point `s`
  have hval : (∑ i : Fin N, c i.castSucc *
        (-(((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ)) * (riemannZeta s / s)))
      + c (Fin.last N) * (1 / s) = 0 := by
    have h0 := congrFun hrel ⟨s, hs, hs1⟩
    rw [Fin.sum_univ_castSucc] at h0
    simpa [Pi.add_apply, Finset.sum_apply, borderRowFun_castSucc, borderRowFun_last] using h0
  have hsum : ∑ i : Fin N, c i.castSucc *
        (-(((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ)) * (riemannZeta s / s))
      = (∑ i : Fin N, -(c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))))
          * (riemannZeta s / s) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum] at hval
  have hneg : (∑ i : Fin N, -(c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))))
      = -(∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))) := by
    simp
  rw [hneg] at hval
  field_simp at hval
  linear_combination -hval

/-- If every bordered determinant vanishes, one fixed coefficient vector inverts `ζ` on the whole strip. -/
theorem exists_relation_of_forall_det_eq_zero {N : ℕ} (θ : Fin N → ℝ)
    (h : ∀ ρ : Fin (N + 1) → ℂ, (∀ j, 1 / 2 < (ρ j).re) → (∀ j, (ρ j).re < 1) →
      (sampledBorderMatrix θ ρ).det = 0) :
    ∃ c : Fin (N + 1) → ℂ, (∃ i, c i ≠ 0) ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))) * riemannZeta s
        = c (Fin.last N) :=
  muentz_relation_of_not_linearIndependent θ (not_linearIndependent_borderRowFun θ h)

/-- **The abstract obstruction.**  Linear independence of the sampled pairing functions is exactly what a
positive distance needs: sampling turns it into a nonvanishing bordered determinant, which certifies the
floor.  A family other than Báez-Duarte's inherits the whole route by supplying this one hypothesis for its
own pairing functions. -/
theorem bdDist_pos_of_linearIndependent_borderRowFun {N : ℕ} (θ : Fin N → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (hli : LinearIndependent ℂ (borderRowFun θ)) :
    0 < bdDist θ := by
  obtain ⟨x, hx⟩ := exists_det_ne_zero_of_linearIndependent (borderRowFun θ) hli
  rw [matrix_borderRowFun_eq_sampledBorderMatrix θ x] at hx
  exact bdDist_pos_of_det_ne_zero θ hθ _ (fun j => (x j).2.1) (fun j => (x j).2.2) hx

end RHTower

end
