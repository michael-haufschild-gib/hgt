import GaloisForLFunctions.HTGeometry.ExponentialSumDA

/-!
# Quadratic physical-character osculation

For a quadratic binomial constraint, substitution along the physical exponential arc has a sharp
two-phase contact law.  Unequal tangent products give the expected order two.  Equal nonzero
products cancel that jet, and unequal source sums force exact order three.  Thus the first positive
tangency excess is a curvature invariant, not an artefact of a chosen presentation.

The Hankel conic source `(1, α, α²)` realizes the excess-one phase.  It can at the same time be
linearly independent over `ℚ`, so arithmetic source independence and complex-algebraic incidence
are genuinely different layers of the same physical-character object.
-/

open Complex Finset

namespace GaloisForLFunctions

noncomputable section

private theorem analyticOrderAt_eq_nat_of_jets
    {f : ℂ → ℂ} {n : ℕ} (hf : AnalyticAt ℂ f 0)
    (hzero : ∀ i < n, iteratedDeriv i f 0 = 0)
    (hnonzero : iteratedDeriv n f 0 ≠ 0) :
    analyticOrderAt f 0 = n := by
  have hge : (n : ℕ∞) ≤ analyticOrderAt f 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).2 hzero
  have hnot : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f 0 := by
    intro hge'
    exact hnonzero
      ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).1 hge' n (by omega))
  have hfin : analyticOrderAt f 0 ≠ ⊤ := by
    intro htop
    apply hnot
    rw [htop]
    simp
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hm] at hge hnot ⊢
  have hmge : n ≤ m := by exact_mod_cast hge
  have hmnot : ¬ n + 1 ≤ m := by
    intro hm'
    apply hnot
    exact_mod_cast hm'
  have hmn : m = n := by omega
  exact_mod_cast hmn

def quadraticBinomialPhysicalCoefficients : Fin 6 → ℂ := ![1, -1, -1, -1, 1, 1]

def quadraticBinomialPhysicalFrequencies (a b c d : ℂ) : Fin 6 → ℂ :=
  ![a + b, a, b, c + d, c, d]

/-- The physical pullback of the quadratic binomial with source pairs `(a,b)` and `(c,d)`. -/
def quadraticBinomialPhysicalPullback (a b c d z : ℂ) : ℂ :=
  ∑ i : Fin 6, quadraticBinomialPhysicalCoefficients i *
    Complex.exp (quadraticBinomialPhysicalFrequencies a b c d i * z)

theorem quadraticBinomialPhysicalPullback_eq_relation (a b c d z : ℂ) :
    quadraticBinomialPhysicalPullback a b c d z =
      (Complex.exp (a * z) - 1) * (Complex.exp (b * z) - 1) -
        (Complex.exp (c * z) - 1) * (Complex.exp (d * z) - 1) := by
  simp [quadraticBinomialPhysicalPullback, quadraticBinomialPhysicalCoefficients,
    quadraticBinomialPhysicalFrequencies, Fin.sum_univ_succ]
  rw [show Complex.exp ((a + b) * z) = Complex.exp (a * z) * Complex.exp (b * z) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  rw [show Complex.exp ((c + d) * z) = Complex.exp (c * z) * Complex.exp (d * z) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

theorem iteratedDeriv_quadraticBinomialPhysicalPullback
    (a b c d : ℂ) (n : ℕ) :
    iteratedDeriv n (quadraticBinomialPhysicalPullback a b c d) 0 =
      (a + b) ^ n - a ^ n - b ^ n - (c + d) ^ n + c ^ n + d ^ n := by
  rw [show quadraticBinomialPhysicalPullback a b c d = fun z =>
      ∑ i ∈ Finset.univ, quadraticBinomialPhysicalCoefficients i *
        Complex.exp (quadraticBinomialPhysicalFrequencies a b c d i * z) by
    funext z
    simp [quadraticBinomialPhysicalPullback]]
  rw [iteratedDeriv_finset_expSum]
  simp [quadraticBinomialPhysicalCoefficients, quadraticBinomialPhysicalFrequencies,
    Fin.sum_univ_succ]
  ring

@[simp] theorem iteratedDeriv_quadraticBinomialPhysicalPullback_zero
    (a b c d : ℂ) :
    iteratedDeriv 0 (quadraticBinomialPhysicalPullback a b c d) 0 = 0 := by
  rw [iteratedDeriv_quadraticBinomialPhysicalPullback]
  ring

@[simp] theorem iteratedDeriv_quadraticBinomialPhysicalPullback_one
    (a b c d : ℂ) :
    iteratedDeriv 1 (quadraticBinomialPhysicalPullback a b c d) 0 = 0 := by
  rw [iteratedDeriv_quadraticBinomialPhysicalPullback]
  ring

theorem iteratedDeriv_quadraticBinomialPhysicalPullback_two
    (a b c d : ℂ) :
    iteratedDeriv 2 (quadraticBinomialPhysicalPullback a b c d) 0 =
      2 * (a * b - c * d) := by
  rw [iteratedDeriv_quadraticBinomialPhysicalPullback]
  ring

theorem iteratedDeriv_quadraticBinomialPhysicalPullback_three_of_product_eq
    (a b c d : ℂ) (hprod : a * b = c * d) :
    iteratedDeriv 3 (quadraticBinomialPhysicalPullback a b c d) 0 =
      3 * (a * b) * (a + b - c - d) := by
  rw [iteratedDeriv_quadraticBinomialPhysicalPullback]
  calc
    (a + b) ^ 3 - a ^ 3 - b ^ 3 - (c + d) ^ 3 + c ^ 3 + d ^ 3 =
        3 * (a * b) * (a + b) - 3 * (c * d) * (c + d) := by ring
    _ = 3 * (a * b) * (a + b - c - d) := by rw [← hprod]; ring

theorem analyticAt_quadraticBinomialPhysicalPullback (a b c d z : ℂ) :
    AnalyticAt ℂ (quadraticBinomialPhysicalPullback a b c d) z := by
  unfold quadraticBinomialPhysicalPullback
  fun_prop

/-- A quadratic binomial meets the physical exponential arc at the expected source height two
when its tangent products differ. -/
theorem analyticOrderAt_quadraticBinomialPhysicalPullback_eq_two
    (a b c d : ℂ) (hprod : a * b ≠ c * d) :
    analyticOrderAt (quadraticBinomialPhysicalPullback a b c d) 0 = 2 := by
  apply analyticOrderAt_eq_nat_of_jets (analyticAt_quadraticBinomialPhysicalPullback a b c d 0)
  · intro i hi
    interval_cases i <;> simp
  · rw [iteratedDeriv_quadraticBinomialPhysicalPullback_two]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hprod)

/-- **Quadratic physical-osculation phase law.**  Matching tangent products cancel the quadratic
jet.  If the common product is nonzero and the source sums differ, the physical contact order is
exactly three: the quadratic constraint acquires tangency excess one. -/
theorem analyticOrderAt_quadraticBinomialPhysicalPullback_eq_three
    (a b c d : ℂ) (hprod : a * b = c * d) (hprod0 : a * b ≠ 0)
    (hsum : a + b ≠ c + d) :
    analyticOrderAt (quadraticBinomialPhysicalPullback a b c d) 0 = 3 := by
  apply analyticOrderAt_eq_nat_of_jets (analyticAt_quadraticBinomialPhysicalPullback a b c d 0)
  · intro i hi
    interval_cases i <;> simp [iteratedDeriv_quadraticBinomialPhysicalPullback_two, hprod]
  · rw [iteratedDeriv_quadraticBinomialPhysicalPullback_three_of_product_eq a b c d hprod]
    have hdiff : a + b - c - d = (a + b) - (c + d) := by ring
    rw [hdiff]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hprod0) (sub_ne_zero.mpr hsum)

def conicPhysicalCoefficients : Fin 5 → ℂ := ![1, -2, -1, 1, 1]

def conicPhysicalFrequencies (α : ℂ) : Fin 5 → ℂ :=
  ![2 * α, α, 1 + α ^ 2, 1, α ^ 2]

/-- The physical pullback of the Hankel conic relation `x₁² - x₀x₂`. -/
def conicPhysicalPullback (α z : ℂ) : ℂ :=
  ∑ i : Fin 5, conicPhysicalCoefficients i *
    Complex.exp (conicPhysicalFrequencies α i * z)

theorem conicPhysicalPullback_eq_hankelRelation (α z : ℂ) :
    conicPhysicalPullback α z =
      (Complex.exp (α * z) - 1) ^ 2 -
        (Complex.exp z - 1) * (Complex.exp (α ^ 2 * z) - 1) := by
  simp [conicPhysicalPullback, conicPhysicalCoefficients, conicPhysicalFrequencies,
    Fin.sum_univ_succ]
  rw [show Complex.exp ((2 * α) * z) = Complex.exp (α * z) ^ 2 by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring]
  rw [show Complex.exp ((1 + α ^ 2) * z) =
      Complex.exp z * Complex.exp (α ^ 2 * z) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  ring

theorem iteratedDeriv_conicPhysicalPullback (α : ℂ) (n : ℕ) :
    iteratedDeriv n (conicPhysicalPullback α) 0 =
      (2 * α) ^ n - 2 * α ^ n - (1 + α ^ 2) ^ n + 1 + (α ^ 2) ^ n := by
  rw [show conicPhysicalPullback α = fun z =>
      ∑ i ∈ Finset.univ, conicPhysicalCoefficients i *
        Complex.exp (conicPhysicalFrequencies α i * z) by
    funext z
    simp [conicPhysicalPullback]]
  rw [iteratedDeriv_finset_expSum]
  simp [conicPhysicalCoefficients, conicPhysicalFrequencies, Fin.sum_univ_succ]
  ring

@[simp] theorem iteratedDeriv_conicPhysicalPullback_zero (α : ℂ) :
    iteratedDeriv 0 (conicPhysicalPullback α) 0 = 0 := by
  rw [iteratedDeriv_conicPhysicalPullback]
  ring

@[simp] theorem iteratedDeriv_conicPhysicalPullback_one (α : ℂ) :
    iteratedDeriv 1 (conicPhysicalPullback α) 0 = 0 := by
  rw [iteratedDeriv_conicPhysicalPullback]
  ring

@[simp] theorem iteratedDeriv_conicPhysicalPullback_two (α : ℂ) :
    iteratedDeriv 2 (conicPhysicalPullback α) 0 = 0 := by
  rw [iteratedDeriv_conicPhysicalPullback]
  ring

theorem iteratedDeriv_conicPhysicalPullback_three (α : ℂ) :
    iteratedDeriv 3 (conicPhysicalPullback α) 0 = -3 * α ^ 2 * (α - 1) ^ 2 := by
  rw [iteratedDeriv_conicPhysicalPullback]
  ring

theorem analyticAt_conicPhysicalPullback (α z : ℂ) :
    AnalyticAt ℂ (conicPhysicalPullback α) z := by
  unfold conicPhysicalPullback
  fun_prop

/-- The Hankel conic has exact physical tangency excess one away from the collapsed sources
`α = 0,1`. -/
theorem analyticOrderAt_conicPhysicalPullback_eq_three
    (α : ℂ) (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    analyticOrderAt (conicPhysicalPullback α) 0 = 3 := by
  apply analyticOrderAt_eq_nat_of_jets (analyticAt_conicPhysicalPullback α 0)
  · intro i hi
    interval_cases i <;> simp
  · rw [iteratedDeriv_conicPhysicalPullback_three]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hα0))
      (pow_ne_zero 2 (sub_ne_zero.mpr hα1))

def conicRankThreeSource (α : ℂ) : Fin 3 → ℂ := ![1, α, α ^ 2]

/-- A rank-three arithmetically independent source can simultaneously lie on the complex Hankel
conic and have physical tangency excess one. -/
theorem analyticOrderAt_conicPhysicalPullback_eq_three_of_rankThree
    (α : ℂ) (hlin : LinearIndependent ℚ (conicRankThreeSource α)) :
    analyticOrderAt (conicPhysicalPullback α) 0 = 3 := by
  apply analyticOrderAt_conicPhysicalPullback_eq_three
  · simpa [conicRankThreeSource] using hlin.ne_zero (1 : Fin 3)
  · intro hα1
    have h01 : (0 : Fin 3) = 1 := hlin.injective (by simp [conicRankThreeSource, hα1])
    norm_num at h01

end

end GaloisForLFunctions
