import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheArchimedeanGermSurvivesOnItsPolarHyperplane

/-!
# The pole node completes the archimedean germ

The lattice germ survives renormalization only on the polar-neutral hyperplane `Σ c_i = 0`: its
counterterm is the rank-one polar mode. Adjoining one node that carries the polar mode removes the
constraint. In the shifted germ `Σ_{k ≥ 1} r^k/(k + x + y)`, the node `x = 0` is the order-one
torsion orbit `{1}` — the arithmetic point — whose self-energy `Σ_{k≥1} r^k/k = −log(1 − r)` is
exactly the archimedean divergence. Spending the hyperplane constraint on that node gives a kernel
that is positive on all vectors:

`Σ_{i,j} c_i c_j (H(x_i) + H(x_j) − H(x_i + x_j)) ≥ 0`,  `H(x) = ψ(1 + x) + γ`

(`harmonicKernel_nonneg`), the harmonic-number kernel, equal to
`∫_0^1 (1 − t^x)(1 − t^y)/(1 − t) dt`. This is the matched cancellation available between the two
germs: the polar divergence of the archimedean place is cancelled by the self-energy of the
arithmetic point, and positivity survives on the whole space.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

/-- The harmonic-number function `H(x) = ψ(1 + x) + γ`. -/
def harmonicFn (x : ℝ) : ℝ := (Complex.digamma ((1 + x : ℝ) : ℂ)).re + Real.eulerMascheroniConstant

/-- **The pole node completes the archimedean germ**: the harmonic-number kernel
`H(x) + H(y) − H(x + y)` is positive semidefinite on `x ≥ 0`. -/
theorem harmonicKernel_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (harmonicFn (x i) + harmonicFn (x j) - harmonicFn (x i + x j)) := by
  -- Nodes `1/2` (the pole node) and `x_i + 1/2`; coefficients `−Σ c` and `c`.
  set S : ℝ := ∑ i, c i
  set z : Fin (n + 1) → ℝ := Fin.cons (1 / 2) fun i => x i + 1 / 2
  set C : Fin (n + 1) → ℝ := Fin.cons (-S) c
  have hz : ∀ a, 0 < z a := fun a => by
    refine Fin.cases ?_ (fun i => ?_) a
    · simp [z]
    · simp only [z, Fin.cons_succ]; linarith [hx i]
  have hC : ∑ a, C a = 0 := by simp [C, Fin.sum_univ_succ, S]
  have h := neg_digamma_hankel_nonneg hz hC
  set ψ : ℝ → ℝ := fun t => (Complex.digamma (t : ℂ)).re
  have hψ1 : ψ 1 = -Real.eulerMascheroniConstant := by simp [ψ, Complex.digamma_one]
  simp only [Fin.sum_univ_succ, C, z, Fin.cons_zero, Fin.cons_succ] at h
  -- Collect the expansion in terms of `ψ`.
  have e1 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  have e2 : ∀ i, (1 / 2 : ℝ) + (x i + 1 / 2) = 1 + x i := fun i => by ring
  have e3 : ∀ i, (x i + 1 / 2 : ℝ) + 1 / 2 = 1 + x i := fun i => by ring
  have e4 : ∀ i j, (x i + 1 / 2 : ℝ) + (x j + 1 / 2) = 1 + (x i + x j) := fun i j => by ring
  simp only [e1, e2, e3, e4] at h
  change 0 ≤ -S * -S * -ψ 1 + ∑ j, -S * c j * -ψ (1 + x j) +
    ∑ i, (c i * -S * -ψ (1 + x i) + ∑ j, c i * c j * -ψ (1 + (x i + x j))) at h
  rw [hψ1] at h
  -- Expand the harmonic kernel into the same three sums.
  have hterm : ∀ i j, c i * c j * (harmonicFn (x i) + harmonicFn (x j) - harmonicFn (x i + x j)) =
      c i * c j * ψ (1 + x i) + c i * c j * ψ (1 + x j) - c i * c j * ψ (1 + (x i + x j)) +
        Real.eulerMascheroniConstant * (c i * c j) := fun i j => by
    simp only [harmonicFn, ψ, show (1 + (x i + x j) : ℝ) = 1 + x i + x j by ring]
    ring
  have h1 : ∑ i, ∑ j, c i * c j * ψ (1 + x i) = (∑ i, c i * ψ (1 + x i)) * S := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, c i * c j * ψ (1 + x j) = S * ∑ j, c j * ψ (1 + x j) := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have h3 : ∑ i, ∑ j, c i * c j = S * S := by rw [sum_mul_sum]
  have h4 : ∑ i, ∑ j, Real.eulerMascheroniConstant * (c i * c j) =
      Real.eulerMascheroniConstant * (S * S) := by
    rw [← h3, mul_sum]
    exact sum_congr rfl fun i _ => by rw [mul_sum]
  have hlhs : ∑ i, ∑ j, c i * c j *
      (harmonicFn (x i) + harmonicFn (x j) - harmonicFn (x i + x j)) =
      (∑ i, c i * ψ (1 + x i)) * S + S * ∑ j, c j * ψ (1 + x j) -
        ∑ i, ∑ j, c i * c j * ψ (1 + (x i + x j)) + Real.eulerMascheroniConstant * (S * S) := by
    rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => hterm i j]
    simp only [sum_add_distrib, sum_sub_distrib]
    rw [h1, h2, h4]
  have r1 : ∑ j, -S * c j * -ψ (1 + x j) = S * ∑ j, c j * ψ (1 + x j) := by
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have r2 : ∑ i, (c i * -S * -ψ (1 + x i) + ∑ j, c i * c j * -ψ (1 + (x i + x j))) =
      (∑ i, c i * ψ (1 + x i)) * S - ∑ i, ∑ j, c i * c j * ψ (1 + (x i + x j)) := by
    have ha : ∑ i, c i * -S * -ψ (1 + x i) = (∑ i, c i * ψ (1 + x i)) * S := by
      rw [sum_mul]
      exact sum_congr rfl fun i _ => by ring
    have hb : ∑ i, ∑ j, c i * c j * -ψ (1 + (x i + x j)) =
        -∑ i, ∑ j, c i * c j * ψ (1 + (x i + x j)) := by
      simp only [mul_neg, sum_neg_distrib]
    rw [sum_add_distrib, ha, hb]
    ring
  rw [r1, r2] at h
  rw [hlhs]
  linarith

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
