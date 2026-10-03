import GaloisForLFunctions.HTGeometry.PoissonGammaCoherentLadder
import GaloisForLFunctions.HTGeometry.MaximalMultiplicationSelfAdjoint

/-!
# The adjacent-sector creation law of the Gamma coherent ladder

* The degree-`k` Gram law is the `k`-th tensor power of the degree-one law:
  `⟨ψ_t^{(k)}, ψ_u^{(k)}⟩ = ⟨ψ_t^{(1)}, ψ_u^{(1)}⟩^k`, with `ψ_t^{(1)} = ℓ_t = √(2t) e^{-tr}`.
* **(PPTI.22)–(PPTI.23).**  The degree-two/degree-three mismatch is the fibrewise creation operator
  `R_t = M_{√(tr)}`: a positive self-adjoint (hence closed) multiplication operator whose domain
  contains `ψ_t^{(2)}` and which sends it to `ψ_t^{(3)}`.
* **(PPTI.29), kernel form.**  For two distinct clocks neither `K_2 - K_3` nor `K_3 - K_2` is a
  positive semidefinite kernel: both have zero diagonal and nonzero off-diagonal entry.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Tensor degree.**  The degree-`k` Gram law is the `k`-th power of the degree-one law. -/
theorem inner_gammaCoherentVector_eq_pow (k : ℕ) [NeZero k] {t u : ℝ} (ht : 0 < t)
    (hu : 0 < u) :
    ⟪gammaCoherentVector k ht, gammaCoherentVector k hu⟫_ℂ =
      ⟪gammaCoherentVector 1 ht, gammaCoherentVector 1 hu⟫_ℂ ^ k := by
  rw [inner_gammaCoherentVector, inner_gammaCoherentVector, pow_one]
  push_cast
  rfl

/-- The degree-one profile is the exponential `ℓ_t(r) = √(2t) e^{-tr}`. -/
theorem gammaCoherentProfile_one (t r : ℝ) :
    gammaCoherentProfile 1 t r = Real.sqrt (2 * t) * Real.exp (-(t * r)) := by
  simp [gammaCoherentProfile]

/-- The creator symbol `√(t r)`. -/
def adjacentCreatorSymbol (t : ℝ) (r : ℝ) : ℝ := Real.sqrt (t * r)

theorem measurable_adjacentCreatorSymbol (t : ℝ) : Measurable (adjacentCreatorSymbol t) :=
  (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)).measurable

/-- **(PPTI.23).**  The fibrewise creation operator `R_t = M_{√(tr)}` on `L²((0,∞), dr)`. -/
def adjacentCreator (t : ℝ) : HalfLineL2 →ₗ.[ℂ] HalfLineL2 :=
  maximalMul (volume.restrict (Ioi 0)) (adjacentCreatorSymbol t)

theorem adjacentCreator_isSelfAdjoint (t : ℝ) : IsSelfAdjoint (adjacentCreator t) :=
  maximalMul_isSelfAdjoint (measurable_adjacentCreatorSymbol t)

/-- `R_t` is closed. -/
theorem adjacentCreator_isClosed (t : ℝ) : (adjacentCreator t).IsClosed :=
  (adjacentCreator_isSelfAdjoint t).isClosed

/-- `R_t` is positive. -/
theorem adjacentCreator_nonneg (t : ℝ) (f : (adjacentCreator t).domain) :
    0 ≤ RCLike.re ⟪adjacentCreator t f, (f : HalfLineL2)⟫_ℂ := by
  rw [L2.inner_def, ← integral_re]
  · refine integral_nonneg_of_ae ?_
    filter_upwards [maximalMul_coeFn (adjacentCreatorSymbol t) f] with r hr
    have hr' : ((adjacentCreator t f : HalfLineL2) : ℝ → ℂ) r =
        ((adjacentCreatorSymbol t r : ℝ) : ℂ) * (f : HalfLineL2) r := hr
    simp only [Pi.zero_apply]
    rw [hr', ← smul_eq_mul, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K,
      RCLike.re_to_complex, Complex.re_ofReal_mul]
    refine mul_nonneg (Real.sqrt_nonneg _) ?_
    have h : ((‖(f : HalfLineL2) r‖ : ℂ) ^ 2).re = ‖(f : HalfLineL2) r‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact h ▸ sq_nonneg _
  · exact L2.integrable_inner _ _

/-- **(PPTI.22)–(PPTI.23).**  `ψ_t^{(2)}` lies in the domain of `R_t` and `R_t ψ_t^{(2)} = ψ_t^{(3)}`. -/
theorem adjacentCreator_gammaCoherent {t : ℝ} (ht : 0 < t) :
    ∃ h : gammaCoherentVector 2 ht ∈ (adjacentCreator t).domain,
      adjacentCreator t ⟨_, h⟩ = gammaCoherentVector 3 ht := by
  have hae : (fun r => ((adjacentCreatorSymbol t r : ℝ) : ℂ) *
      (gammaCoherentVector 2 ht : ℝ → ℂ) r) =ᵐ[volume.restrict (Ioi 0)]
        (gammaCoherentVector 3 ht : ℝ → ℂ) := by
    filter_upwards [gammaCoherentVector_ae 2 ht, gammaCoherentVector_ae 3 ht,
      ae_restrict_mem measurableSet_Ioi] with r h2 h3 hr
    rw [h2, h3, gammaCoherentProfile_three_eq ht hr, adjacentCreatorSymbol]
    push_cast
    ring
  have hmem : gammaCoherentVector 2 ht ∈ (adjacentCreator t).domain :=
    (memLp_congr_ae hae).2 (Lp.memLp _)
  refine ⟨hmem, Lp.ext ?_⟩
  exact (maximalMul_coeFn (adjacentCreatorSymbol t) ⟨_, hmem⟩).trans hae

/-- The coherent Gram kernel of degree `k`, `G_k(t,u) = (2√(tu)/(t+u))^k`. -/
def coherentGramKernel (k : ℕ) (t u : ℝ) : ℝ := (2 * Real.sqrt (t * u) / (t + u)) ^ k

theorem coherentGramKernel_self (k : ℕ) {t : ℝ} (ht : 0 < t) : coherentGramKernel k t t = 1 := by
  rw [coherentGramKernel, Real.sqrt_mul_self ht.le, show 2 * t / (t + t) = 1 by field_simp; ring,
    one_pow]

theorem coherentGram_base_lt_one {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (htu : t ≠ u) :
    0 < 2 * Real.sqrt (t * u) / (t + u) ∧ 2 * Real.sqrt (t * u) / (t + u) < 1 := by
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  have hs : Real.sqrt (t * u) * Real.sqrt (t * u) = t * u := Real.mul_self_sqrt (by positivity)
  have hsq : 0 < (t - u) ^ 2 := by
    have : t - u ≠ 0 := sub_ne_zero.2 htu
    positivity
  nlinarith [Real.sqrt_nonneg (t * u)]

/-- **(PPTI.29), kernel form.**  For distinct clocks, neither `K_2 - K_3` nor `K_3 - K_2` is a
positive semidefinite kernel on the two points `{t, u}`. -/
theorem not_posSemidef_coherentGramKernel_sub {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (htu : t ≠ u) :
    (∃ v : Fin 2 → ℝ, ∑ i, ∑ j, v i * v j *
        (coherentGramKernel 2 (![t, u] i) (![t, u] j) -
          coherentGramKernel 3 (![t, u] i) (![t, u] j)) < 0) ∧
      (∃ v : Fin 2 → ℝ, ∑ i, ∑ j, v i * v j *
        (coherentGramKernel 3 (![t, u] i) (![t, u] j) -
          coherentGramKernel 2 (![t, u] i) (![t, u] j)) < 0) := by
  obtain ⟨hg0, hg1⟩ := coherentGram_base_lt_one ht hu htu
  set g := 2 * Real.sqrt (t * u) / (t + u) with hg
  have hsym : coherentGramKernel 2 u t = coherentGramKernel 2 t u ∧
      coherentGramKernel 3 u t = coherentGramKernel 3 t u := by
    refine ⟨?_, ?_⟩ <;> simp only [coherentGramKernel, mul_comm u t, add_comm u t]
  have h2 : coherentGramKernel 2 t u = g ^ 2 := rfl
  have h3 : coherentGramKernel 3 t u = g ^ 3 := rfl
  have hc : 0 < g ^ 2 - g ^ 3 := by
    have : g ^ 3 < g ^ 2 := pow_lt_pow_right_of_lt_one₀ hg0 hg1 (by norm_num)
    linarith
  have hsum : ∀ (a b : ℝ), ∑ i, ∑ j, ![a, b] i * ![a, b] j *
      (coherentGramKernel 2 (![t, u] i) (![t, u] j) -
        coherentGramKernel 3 (![t, u] i) (![t, u] j)) = 2 * a * b * (g ^ 2 - g ^ 3) := by
    intro a b
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      coherentGramKernel_self _ ht, coherentGramKernel_self _ hu, hsym.1, hsym.2, h2, h3]
    ring
  have hsum' : ∀ (a b : ℝ), ∑ i, ∑ j, ![a, b] i * ![a, b] j *
      (coherentGramKernel 3 (![t, u] i) (![t, u] j) -
        coherentGramKernel 2 (![t, u] i) (![t, u] j)) = -(2 * a * b * (g ^ 2 - g ^ 3)) := by
    intro a b
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      coherentGramKernel_self _ ht, coherentGramKernel_self _ hu, hsym.1, hsym.2, h2, h3]
    ring
  refine ⟨⟨![1, -1], ?_⟩, ⟨![1, 1], ?_⟩⟩
  · rw [hsum]
    linarith
  · rw [hsum']
    linarith

end GaloisForLFunctions.HTGeometry
