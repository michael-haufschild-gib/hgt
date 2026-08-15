import Mathlib

/-!
# The exterior inverse-symbol block is not bounded below

Four exact mechanisms of the card are formalized on the Fourier side, where the card's own proof
lives.

*Positivity and injectivity.*  A nonnegative symbol gives a nonnegative quadratic form, and a
strictly positive symbol makes it vanish only on the zero vector — `(6a)`.

*The modulated wave packets.*  Translating the symbol by `n` and integrating against a fixed
integrable profile gives a sequence tending to `0` whenever the symbol tends to `0` at infinity and
is bounded.  This is the dominated-convergence computation `(8)`–`(9)`.

*No lower bound.*  A sequence of unit vectors whose images tend to zero refutes every lower bound —
`(6)`, `(10)`.

*Range incidence.*  The exterior datum exists exactly when the interior forcing lies in the range,
and is then unique by injectivity — `(12a)`–`(12b)`.

Plancherel, modulation covariance, the exterior compression `(5)` and the closed-range theorem are
cited parents and stay outside the Lean statement.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Positivity and injectivity on the Fourier side -/

/-- **Equation (6a), positivity.**  A nonnegative symbol gives a nonnegative quadratic form. -/
theorem symbol_quadratic_nonneg {m F : ℝ → ℝ} (hm : ∀ ξ, 0 ≤ m ξ) (hF : ∀ ξ, 0 ≤ F ξ) :
    0 ≤ ∫ ξ, m ξ * F ξ :=
  integral_nonneg fun ξ => mul_nonneg (hm ξ) (hF ξ)

/-- **Equation (6a), injectivity.**  With a strictly positive symbol the quadratic form vanishes
only for a vanishing Fourier profile. -/
theorem symbol_quadratic_eq_zero {m F : ℝ → ℝ} (hm : ∀ ξ, 0 < m ξ) (hF : ∀ ξ, 0 ≤ F ξ)
    (hint : Integrable (fun ξ => m ξ * F ξ)) (h : ∫ ξ, m ξ * F ξ = 0) :
    ∀ᵐ ξ, F ξ = 0 := by
  have hnn : 0 ≤ᵐ[volume] fun ξ => m ξ * F ξ :=
    Filter.Eventually.of_forall fun ξ => mul_nonneg (le_of_lt (hm ξ)) (hF ξ)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h
  filter_upwards [hzero] with ξ hξ
  have := mul_eq_zero.mp hξ
  rcases this with hm0 | hF0
  · exact absurd hm0 (ne_of_gt (hm ξ))
  · exact hF0

/-! ## The modulated wave packets -/

/-- **Equations (8)–(9).**  Translating a bounded symbol that decays at infinity against a fixed
integrable profile gives a sequence of energies tending to zero.  This is the exact
dominated-convergence step behind the fixed-support approximate null vectors. -/
theorem tendsto_integral_modulated_symbol {m g : ℝ → ℝ} {M : ℝ}
    (hmeas : Measurable m) (hbound : ∀ ξ, |m ξ| ≤ M)
    (h0 : Tendsto m atTop (nhds 0))
    (hg : Integrable g) (hgnn : ∀ η, 0 ≤ g η) :
    Tendsto (fun n : ℕ => ∫ η, (m (η + n)) ^ 2 * g η) atTop (nhds 0) := by
  have hgmeas : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  have hFmeas : ∀ n : ℕ, AEStronglyMeasurable (fun η => (m (η + n)) ^ 2 * g η) volume := by
    intro n
    refine AEStronglyMeasurable.mul ?_ hgmeas
    exact ((hmeas.comp (measurable_id.add_const _)).pow_const 2).aestronglyMeasurable
  have hboundInt : Integrable (fun η => M ^ 2 * g η) := hg.const_mul _
  have hdom : ∀ n : ℕ, ∀ᵐ η : ℝ, ‖(m (η + n)) ^ 2 * g η‖ ≤ M ^ 2 * g η := by
    intro n
    refine Filter.Eventually.of_forall fun η => ?_
    have h1 : (m (η + n)) ^ 2 ≤ M ^ 2 := by
      have habs := hbound (η + n)
      nlinarith [abs_nonneg (m (η + n)), sq_abs (m (η + n))]
    have h2 : 0 ≤ (m (η + n)) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h2 (hgnn η))]
    exact mul_le_mul_of_nonneg_right h1 (hgnn η)
  have hlim : ∀ᵐ η : ℝ, Tendsto (fun n : ℕ => (m (η + n)) ^ 2 * g η) atTop (nhds (0 * g η)) := by
    refine Filter.Eventually.of_forall fun η => ?_
    have hshift : Tendsto (fun n : ℕ => η + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have hm : Tendsto (fun n : ℕ => m (η + (n : ℝ))) atTop (nhds 0) := h0.comp hshift
    have hsq : Tendsto (fun n : ℕ => (m (η + (n : ℝ))) ^ 2) atTop (nhds (0 ^ 2)) := hm.pow 2
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at hsq
    exact hsq.mul_const (g η)
  have := tendsto_integral_of_dominated_convergence (fun η => M ^ 2 * g η) hFmeas hboundInt
    hdom hlim
  simpa using this

/-! ## No lower bound -/

/-- **Equations (6), (10).**  Unit vectors with vanishing images refute every lower bound. -/
theorem not_boundedBelow_of_tendsto_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {T : E → F} {f : ℕ → E} (hnorm : ∀ n, ‖f n‖ = 1)
    (h0 : Tendsto (fun n => ‖T (f n)‖) atTop (nhds 0)) :
    ¬ ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖T x‖ := by
  rintro ⟨c, hc, hlb⟩
  have hev := h0.eventually (gt_mem_nhds hc)
  obtain ⟨n, hn⟩ := hev.exists
  have := hlb (f n)
  rw [hnorm n, mul_one] at this
  exact absurd hn (not_lt.mpr this)

/-! ## Range incidence -/

/-- **Equations (12a)–(12b).**  With an injective operator, the exterior datum exists exactly when
the interior forcing lies in the range, and it is then unique. -/
theorem range_incidence {E F : Type*} [AddCommGroup E] [AddCommGroup F] {T : E → F}
    (hinj : Function.Injective T) (y : F) :
    (∃! x, T x = y) ↔ y ∈ Set.range T := by
  constructor
  · rintro ⟨x, hx, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx, fun z hz => hinj (hz.trans hx.symm)⟩

theorem range_incidence_unique {E F : Type*} [AddCommGroup E] [AddCommGroup F] {T : E → F}
    (hinj : Function.Injective T) {y : F} {x₁ x₂ : E} (h₁ : T x₁ = y) (h₂ : T x₂ = y) :
    x₁ = x₂ :=
  hinj (h₁.trans h₂.symm)

end GaloisForLFunctions.RHTower

end
