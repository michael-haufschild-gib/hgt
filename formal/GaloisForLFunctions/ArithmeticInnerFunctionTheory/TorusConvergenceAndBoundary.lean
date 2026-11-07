import GaloisForLFunctions.ArithmeticInnerFunctionTheory.CriticalStripArithmeticBernstein

/-!+# Convergence is essential to arithmetic torus positivity

The Chebyshev recurrence has a conserved quadratic form equal to one. Consequently its
characters cannot tend to zero. An amplitude bounded away from zero makes every nonempty
torus series nonsummable, so its totalized sum is zero. This distinguishes positivity of
convergent character expansions from inequalities involving an unrestricted `tsum`.
-/

open Filter Topology Finset Complex
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open GaloisForLFunctions.CompletedArithmeticForms (cosSum cosSum_add_two)

noncomputable section

/-- The quadratic invariant of the Chebyshev recurrence. -/
theorem cosSum_conserved_form (θ : ℝ) (k : ℕ) :
    cosSum θ (k + 1) ^ 2 + cosSum θ k ^ 2 -
      2 * Real.cos θ * cosSum θ (k + 1) * cosSum θ k = 1 := by
  induction k with
  | zero => simp only [zero_add, cosSum_zero, cosSum_one]; ring
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by omega, cosSum_add_two]
    nlinarith only [ih]

/-- At least one of each pair of adjacent characters has nonvanishing energy. -/
theorem cosSum_adjacent_energy (θ : ℝ) (k : ℕ) :
    1 / 2 ≤ cosSum θ (k + 1) ^ 2 + cosSum θ k ^ 2 := by
  have hc := Real.abs_cos_le_one θ
  have hm : |Real.cos θ * cosSum θ (k + 1) * cosSum θ k| ≤
      |cosSum θ (k + 1)| * |cosSum θ k| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (abs_nonneg _) hc) (abs_nonneg _)
  have hs := sq_nonneg (|cosSum θ (k + 1)| - |cosSum θ k|)
  have hi := cosSum_conserved_form θ k
  have hl := neg_abs_le (Real.cos θ * cosSum θ (k + 1) * cosSum θ k)
  nlinarith only [hm, hs, hi, hl, sq_abs (cosSum θ (k + 1)), sq_abs (cosSum θ k)]

/-- Chebyshev characters never tend to zero, including endpoint phases. -/
theorem cosSum_not_tendsto_zero (θ : ℝ) :
    ¬ Tendsto (cosSum θ) atTop (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun k => cosSum θ (k + 1)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr h
  have he := (h1.pow 2).add (h.pow 2)
  have hh := ge_of_tendsto' he (cosSum_adjacent_energy θ)
  norm_num at hh

/-- A character series with coefficients bounded away from zero cannot converge. -/
theorem not_summable_mul_cosSum_of_abs_floor {a : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (ha : ∀ k, c ≤ |a k|) (θ : ℝ) :
    ¬ Summable (fun k => a k * cosSum θ k) := by
  intro h
  have hs : Summable (fun k => cosSum θ k) := by
    refine Summable.of_norm_bounded (h.norm.div_const c) fun k => ?_
    rw [Real.norm_eq_abs, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      le_div_iff₀ hc]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (ha k) (abs_nonneg (cosSum θ k))
  exact cosSum_not_tendsto_zero θ hs.tendsto_atTop_zero

/-- Restriction to one coordinate detects nonsummability on every nonempty torus. -/
theorem torusSum_eq_zero_of_abs_floor {n : ℕ} (hn : 0 < n)
    {a : (Fin n → ℕ) → ℝ} {c : ℝ} (hc : 0 < c) (ha : ∀ k, c ≤ |a k|)
    (θ : Fin n → ℝ) : torusSum a θ = 0 := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let e : ℕ → Fin n → ℕ := fun k => Pi.single i k
  have he : Function.Injective e := by
    intro k l h
    have := congrFun h i
    simpa [e] using this
  have hχ (k : ℕ) : chiProd θ (e k) = cosSum (θ i) k := by
    rw [chiProd, Finset.prod_eq_single i]
    · simp [e]
    · intro j _ hji
      simp [e, Pi.single_eq_of_ne hji, cosSum_zero]
    · simp
  apply tsum_eq_zero_of_not_summable
  intro h
  have hs := h.comp_injective he
  have hs' : Summable (fun k => a (e k) * cosSum (θ i) k) := by
    simpa only [Function.comp_def, hχ] using hs
  exact not_summable_mul_cosSum_of_abs_floor hc (fun k => ha (e k)) (θ i) hs'

/-- For amplitudes bounded away from zero, unrestricted torus positivity records only
pointwise nonnegativity; every nonempty prime test is a divergent series. -/
theorem allBaseTorusPositive_iff_nonneg_of_abs_floor {f : ℝ → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : ∀ y, c ≤ |f y|) :
    IsAllBaseTorusPositive f ↔ ∀ y, 0 ≤ f y := by
  refine ⟨fun h => h.nonneg, ?_⟩
  intro h n p _ _ x θ
  cases n with
  | zero =>
    haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
    simpa [torusSum, tsum_fintype, ampl, chiProd] using h x
  | succ n =>
    have he := torusSum_eq_zero_of_abs_floor (Nat.succ_pos n)
      (a := ampl f (fun i => Real.log (p i)) x) hc (fun k => hf _) θ
    rw [he]

/-- A bounded positive oscillation satisfying the proposed left endpoint bound. -/
def boundaryOscillation (y : ℝ) : ℝ := 1 + Real.cos y / 2

theorem boundaryOscillation_bounds (y : ℝ) :
    1 / 2 ≤ boundaryOscillation y ∧ boundaryOscillation y ≤ 3 / 2 := by
  dsimp only [boundaryOscillation]
  constructor <;> linarith [Real.neg_one_le_cos y, Real.cos_le_one y]

theorem boundaryOscillation_torusPositive : IsAllBaseTorusPositive boundaryOscillation := by
  have hn (y : ℝ) : 0 ≤ boundaryOscillation y :=
    le_trans (by norm_num) (boundaryOscillation_bounds y).1
  exact (allBaseTorusPositive_iff_nonneg_of_abs_floor (by norm_num : (0 : ℝ) < 1 / 2)
    (fun y => by rw [abs_of_nonneg (hn y)]; exact (boundaryOscillation_bounds y).1)).mpr hn

/-- The two-point Hankel test at `π/2, 3π/2` is negative. -/
theorem boundaryOscillation_not_expConvex : ¬ IsExpConvexFrom 0 boundaryOscillation := by
  intro h
  have ht : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      0 ≤ (![Real.pi / 2, 3 * Real.pi / 2] : Fin 2 → ℝ) i := by
    intro i _
    fin_cases i <;> dsimp <;> positivity
  have hh := h (Fin 2) Finset.univ ![Real.pi / 2, 3 * Real.pi / 2]
    (![1, -1] : Fin 2 → ℂ) ht
  have hπ : Real.pi / 2 + Real.pi / 2 = Real.pi := by ring
  have h2π : Real.pi / 2 + 3 * Real.pi / 2 = 2 * Real.pi := by ring
  have h2π' : 3 * Real.pi / 2 + Real.pi / 2 = 2 * Real.pi := by ring
  have h3π : 3 * Real.pi / 2 + 3 * Real.pi / 2 = Real.pi + 2 * Real.pi := by ring
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, boundaryOscillation,
    zero_add, hπ, h2π, h2π', h3π] at hh
  norm_num [Real.cos_add] at hh

/-- The endpoint conjecture without a convergence requirement is false. -/
theorem exists_boundary_torusPositive_not_expConvex :
    ∃ f : ℝ → ℝ, Continuous f ∧ IsAllBaseTorusPositive f ∧
      (∀ y, y ≤ 0 → |f y| ≤ (3 / 2) * Real.exp (-y)) ∧
      ¬ IsExpConvexFrom 0 f := by
  refine ⟨boundaryOscillation, by unfold boundaryOscillation; fun_prop,
    boundaryOscillation_torusPositive, ?_, boundaryOscillation_not_expConvex⟩
  intro y hy
  have hb := boundaryOscillation_bounds y
  rw [abs_of_nonneg (by linarith : 0 ≤ boundaryOscillation y)]
  have he : 1 ≤ Real.exp (-y) := Real.one_le_exp_iff.mpr (neg_nonneg.mpr hy)
  nlinarith only [hb.2, he]

/-- Exponential damping can destroy unrestricted torus positivity at every rate in `(0,1]`.
The convergence hypothesis in the positive-kernel multiplication law is necessary. -/
theorem boundaryOscillation_damping_not_positive {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ¬ IsAllBaseTorusPositive (fun y => boundaryOscillation y * Real.exp (-α * y)) := by
  have h := (oscillatory_bernstein_dichotomy (ω := 1) one_ne_zero).1 α hα hα1
    (1 / 2) (by norm_num)
  simpa only [boundaryOscillation, one_mul, mul_one, div_eq_mul_inv, mul_comm] using h

/-- Positive oscillations can leave the unrestricted cone under small damping and re-enter
above the Euler abscissa. The re-entering amplitudes have genuine convergent character series. -/
theorem exists_oscillation_damping_reentry {α : ℝ} (hα : 1 < α) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      IsAllBaseTorusPositive (fun y => 1 + ε * Real.cos y) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 →
        ¬ IsAllBaseTorusPositive (fun y => Real.exp (-β * y) * (1 + ε * Real.cos y))) ∧
      IsAllBaseTorusPositive (fun y => Real.exp (-α * y) * (1 + ε * Real.cos y)) ∧
      ¬ IsExpConvexFrom 0 (fun y => Real.exp (-α * y) * (1 + ε * Real.cos y)) := by
  have hd := oscillatory_bernstein_dichotomy (ω := 1) one_ne_zero
  obtain ⟨ε₀, hε₀, hsuper⟩ := hd.2 α hα
  let ε := min ε₀ 1 / 2
  have hε : 0 < ε := div_pos (lt_min hε₀ one_pos) (by norm_num)
  have hε1 : ε < 1 := by dsimp [ε]; linarith [min_le_right ε₀ 1]
  have hε₀' : |ε| ≤ ε₀ := by
    rw [abs_of_pos hε]
    dsimp [ε]
    linarith [min_le_left ε₀ 1]
  obtain ⟨hpositive, hnot⟩ := hsuper ε hε.ne' hε₀'
  have hfloor (y : ℝ) : 1 - ε ≤ 1 + ε * Real.cos y := by
    nlinarith only [Real.neg_one_le_cos y, hε]
  have hnonneg (y : ℝ) : 0 ≤ 1 + ε * Real.cos y := by linarith [hfloor y]
  refine ⟨ε, hε, hε1, ?_, ?_, ?_, ?_⟩
  · exact (allBaseTorusPositive_iff_nonneg_of_abs_floor (by linarith : 0 < 1 - ε)
      (fun y => by rw [abs_of_nonneg (hnonneg y)]; exact hfloor y)).mpr hnonneg
  · intro β hβ hβ1
    simpa only [one_mul] using hd.1 β hβ hβ1 ε hε.ne'
  · intro n p hp hinj x θ
    simpa only [one_mul] using (hpositive n p hp hinj x θ).le
  · simpa only [one_mul] using hnot

#print axioms exists_boundary_torusPositive_not_expConvex
#print axioms allBaseTorusPositive_iff_nonneg_of_abs_floor
#print axioms boundaryOscillation_damping_not_positive
#print axioms exists_oscillation_damping_reentry

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
