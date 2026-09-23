import GaloisForLFunctions.HTGeometry.ExponentialFactorialRemainder
import GaloisForLFunctions.HTGeometry.GramPairingCauchySchwarz

/-!
# Taylor localisation: high Legendre modes carry no low frequencies

A square-integrable function `g` on `[-a, a]` orthogonal to every polynomial of degree `< N` has a
Fourier integral that vanishes to order `N` at the origin, quantitatively:

```
  |∫_{-a}^{a} g(x) e^{-ixξ} dx|² ≤ τ_N(a, ξ) · ∫_{-a}^{a} g²,
  τ_N(a, ξ) = 8 a^{2N+1} ξ^{2N} / ((N!)² (2N+1)),       whenever 2 a |ξ| ≤ N + 1.
```

Proof: subtract the degree-`< N` Taylor polynomial of the phase (which `g` does not see), bound the
remainder by the corpus's factorial estimate `2 (|x| |ξ|)^N / N!`, and apply Cauchy–Schwarz.

This is the lemma that confines the spectral mass of the high modes in the constrained-positivity
certificate: everything orthogonal to `Legendre_{<N}` has spectral mass at most
`(1/π) ∫_0^Ξ τ_N` below frequency `Ξ`, which is `~10⁻¹²` for `N ≈ 3.3 a Ξ`.
-/

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The Taylor localisation constant `τ_N(a, ξ) = 8 a^{2N+1} ξ^{2N} / ((N!)² (2N+1))`. -/
noncomputable def taylorLocalizationBound (a : ℝ) (N : ℕ) (ξ : ℝ) : ℝ :=
  8 * a ^ (2 * N + 1) * ξ ^ (2 * N) / ((Nat.factorial N : ℝ) ^ (2 : ℕ) * (2 * N + 1))

/-- The degree-`< N` Taylor polynomial of the phase `e^{-ixξ}` in the variable `x`. -/
noncomputable def expPhasePartialSum (N : ℕ) (ξ x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range N, ((Nat.factorial k : ℂ))⁻¹ • (-((x * ξ : ℝ) : ℂ) * Complex.I) ^ k

theorem continuous_expPhasePartialSum (N : ℕ) (ξ : ℝ) :
    Continuous fun x : ℝ => expPhasePartialSum N ξ x := by
  unfold expPhasePartialSum
  refine continuous_finsetSum _ (fun k _ => ?_)
  fun_prop

/-- The factorial remainder of the phase, pointwise. -/
theorem norm_exp_sub_expPhasePartialSum_le {N : ℕ} {ξ x : ℝ}
    (hN : 2 * (|x| * |ξ|) ≤ (N : ℝ) + 1) :
    ‖Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x‖ ≤
      2 * (|x| * |ξ|) ^ N / Nat.factorial N := by
  have hnorm : ‖-((x * ξ : ℝ) : ℂ) * Complex.I‖ ≤ |x| * |ξ| := by
    rw [norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul]
  have := norm_exp_sub_partialSum_le (A := ℂ) (-((x * ξ : ℝ) : ℂ) * Complex.I) N hnorm hN
  rw [Complex.exp_eq_exp_ℂ]
  exact this

/-- `∫_{-a}^{a} x^{2N} dx = 2 a^{2N+1} / (2N+1)`. -/
theorem integral_Icc_pow_even {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    (∫ x in Icc (-a) a, x ^ (2 * N)) = 2 * a ^ (2 * N + 1) / (2 * N + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_pow]
  have hodd : Odd (2 * N + 1) := odd_two_mul_add_one N
  rw [hodd.neg_pow]
  push_cast
  ring

/-- The squared remainder integrates to at most `τ_N(a, ξ)`. -/
theorem integral_norm_sq_exp_sub_expPhasePartialSum_le {a : ℝ} (ha : 0 ≤ a) (N : ℕ) {ξ : ℝ}
    (hN : 2 * (a * |ξ|) ≤ (N : ℝ) + 1) :
    (∫ x in Icc (-a) a,
      ‖Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x‖ ^ (2 : ℕ)) ≤
      taylorLocalizationBound a N ξ := by
  have hpt : ∀ x ∈ Icc (-a) a,
      ‖Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x‖ ^ (2 : ℕ) ≤
        4 * ξ ^ (2 * N) / (Nat.factorial N : ℝ) ^ (2 : ℕ) * x ^ (2 * N) := by
    intro x hx
    have hxa : |x| ≤ a := abs_le.2 ⟨hx.1, hx.2⟩
    have hN' : 2 * (|x| * |ξ|) ≤ (N : ℝ) + 1 := by
      have : |x| * |ξ| ≤ a * |ξ| := mul_le_mul_of_nonneg_right hxa (abs_nonneg _)
      linarith
    have h1 := norm_exp_sub_expPhasePartialSum_le hN'
    have h2 : (2 * (|x| * |ξ|) ^ N / Nat.factorial N) ^ (2 : ℕ) =
        4 * ξ ^ (2 * N) / (Nat.factorial N : ℝ) ^ (2 : ℕ) * x ^ (2 * N) := by
      have hx2 : |x| ^ (2 * N) = x ^ (2 * N) := by rw [pow_mul, sq_abs, ← pow_mul]
      have hξ2 : |ξ| ^ (2 * N) = ξ ^ (2 * N) := by rw [pow_mul, sq_abs, ← pow_mul]
      rw [div_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm N 2, hx2, hξ2]
      ring
    rw [← h2]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hcont : Continuous fun x : ℝ =>
      Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x :=
    (Complex.continuous_exp.comp (by fun_prop)).sub (continuous_expPhasePartialSum N ξ)
  calc (∫ x in Icc (-a) a,
        ‖Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x‖ ^ (2 : ℕ))
      ≤ ∫ x in Icc (-a) a, 4 * ξ ^ (2 * N) / (Nat.factorial N : ℝ) ^ (2 : ℕ) * x ^ (2 * N) := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Icc hpt
        · exact ((hcont.norm.pow 2)).integrableOn_Icc
        · exact (by fun_prop : Continuous fun x : ℝ =>
            4 * ξ ^ (2 * N) / (Nat.factorial N : ℝ) ^ (2 : ℕ) * x ^ (2 * N)).integrableOn_Icc
    _ = 4 * ξ ^ (2 * N) / (Nat.factorial N : ℝ) ^ (2 : ℕ) * (2 * a ^ (2 * N + 1) / (2 * N + 1)) := by
        rw [integral_const_mul, integral_Icc_pow_even ha]
    _ = taylorLocalizationBound a N ξ := by
        unfold taylorLocalizationBound
        have : (Nat.factorial N : ℝ) ≠ 0 := by positivity
        field_simp
        ring

/-- A square-integrable function on a bounded interval is integrable against every polynomial. -/
theorem integrableOn_mul_pow_of_sq {g : ℝ → ℝ} {a : ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict (Icc (-a) a)))
    (hg2 : IntegrableOn (fun x => g x ^ (2 : ℕ)) (Icc (-a) a)) (j : ℕ) :
    IntegrableOn (fun x => g x * x ^ j) (Icc (-a) a) := by
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-a) a) := continuous_const.integrableOn_Icc
  have hbound : IntegrableOn (fun x => (1 + g x ^ (2 : ℕ)) / 2 * |a| ^ j) (Icc (-a) a) :=
    ((hone.add hg2).div_const 2).mul_const _
  refine hbound.mono' (hgm.mul (by fun_prop : Continuous fun x : ℝ => x ^ j).aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have hxa : |x| ≤ |a| := by
    rw [abs_le]; constructor
    · have := hx.1; linarith [neg_abs_le a, le_abs_self a]
    · have := hx.2; linarith [le_abs_self a]
  have h1 : |g x| ≤ (1 + g x ^ (2 : ℕ)) / 2 := by nlinarith [sq_nonneg (|g x| - 1), sq_abs (g x)]
  have h2 : |x| ^ j ≤ |a| ^ j := pow_le_pow_left₀ (abs_nonneg _) hxa j
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Orthogonality to polynomials kills the Taylor polynomial of the phase. -/
theorem integral_mul_expPhasePartialSum_eq_zero {g : ℝ → ℝ} {a : ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict (Icc (-a) a)))
    (hg2 : IntegrableOn (fun x => g x ^ (2 : ℕ)) (Icc (-a) a)) (N : ℕ)
    (horth : ∀ j < N, (∫ x in Icc (-a) a, g x * x ^ j) = 0) (ξ : ℝ) :
    (∫ x in Icc (-a) a, (g x : ℂ) * expPhasePartialSum N ξ x) = 0 := by
  unfold expPhasePartialSum
  have hterm : ∀ k : ℕ, (fun x : ℝ => (g x : ℂ) *
      (((Nat.factorial k : ℂ))⁻¹ • (-((x * ξ : ℝ) : ℂ) * Complex.I) ^ k)) =
      fun x : ℝ => (((Nat.factorial k : ℂ))⁻¹ * (-(ξ : ℂ) * Complex.I) ^ k) *
        ((g x * x ^ k : ℝ) : ℂ) := by
    intro k
    funext x
    simp only [smul_eq_mul]
    push_cast
    ring
  have hint : ∀ k ∈ Finset.range N, Integrable (fun x : ℝ => (g x : ℂ) *
      (((Nat.factorial k : ℂ))⁻¹ • (-((x * ξ : ℝ) : ℂ) * Complex.I) ^ k))
      (volume.restrict (Icc (-a) a)) := by
    intro k _
    rw [hterm k]
    exact ((integrableOn_mul_pow_of_sq hgm hg2 k).ofReal).const_mul _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have hre : (∫ x in Icc (-a) a, ((g x * x ^ k : ℝ) : ℂ)) =
      ((∫ x in Icc (-a) a, g x * x ^ k : ℝ) : ℂ) := integral_ofReal
  rw [hterm k, integral_const_mul, hre, horth k (Finset.mem_range.1 hk)]
  simp

/-- An `L¹` function on the interval times a continuous function is integrable there. -/
theorem integrable_ofReal_mul_of_continuous {g : ℝ → ℝ} {a : ℝ} (hg1 : IntegrableOn g (Icc (-a) a))
    {φ : ℝ → ℂ} (hφ : Continuous φ) :
    Integrable (fun x : ℝ => (g x : ℂ) * φ x) (volume.restrict (Icc (-a) a)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ.continuousOn (s := Icc (-a) a))
  refine (hg1.norm.const_mul C).mono' ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg1.aestronglyMeasurable).mul
      hφ.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with x hx
    rw [norm_mul, Complex.norm_real, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)

/-- **Taylor localisation.**  For `g ∈ L²[-a, a]` orthogonal to all polynomials of degree `< N`
and `2 a |ξ| ≤ N + 1`,
`|∫ g(x) e^{-ixξ} dx|² ≤ τ_N(a, ξ) ∫ g²`. -/
theorem norm_fourierIntegral_sq_le_taylorLocalization {g : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hgm : AEStronglyMeasurable g (volume.restrict (Icc (-a) a)))
    (hg2 : IntegrableOn (fun x => g x ^ (2 : ℕ)) (Icc (-a) a)) (N : ℕ)
    (horth : ∀ j < N, (∫ x in Icc (-a) a, g x * x ^ j) = 0) {ξ : ℝ}
    (hN : 2 * (a * |ξ|) ≤ (N : ℝ) + 1) :
    ‖∫ x in Icc (-a) a, (g x : ℂ) * Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I)‖ ^ (2 : ℕ) ≤
      taylorLocalizationBound a N ξ * ∫ x in Icc (-a) a, g x ^ (2 : ℕ) := by
  have hg1 : IntegrableOn g (Icc (-a) a) := by
    simpa using integrableOn_mul_pow_of_sq hgm hg2 0
  have hecont : Continuous fun x : ℝ => Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp (by fun_prop)
  have hrcont : Continuous fun x : ℝ =>
      Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x :=
    hecont.sub (continuous_expPhasePartialSum N ξ)
  -- subtract the invisible Taylor polynomial
  have hsplit : (∫ x in Icc (-a) a, (g x : ℂ) * Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I)) =
      ∫ x in Icc (-a) a, (g x : ℂ) *
        (Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x) := by
    have hP := integral_mul_expPhasePartialSum_eq_zero hgm hg2 N horth ξ
    have hi1 := integrable_ofReal_mul_of_continuous hg1 hecont
    have hi2 := integrable_ofReal_mul_of_continuous hg1 (continuous_expPhasePartialSum N ξ)
    have : (∫ x in Icc (-a) a, (g x : ℂ) *
        (Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x)) =
        (∫ x in Icc (-a) a, (g x : ℂ) * Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I)) -
          ∫ x in Icc (-a) a, (g x : ℂ) * expPhasePartialSum N ξ x := by
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    rw [this, hP, sub_zero]
  -- Cauchy–Schwarz
  have hCS := norm_integral_mul_conj_sq_le (ν := volume.restrict (Icc (-a) a))
    (f := fun x : ℝ => (g x : ℂ))
    (g := fun x : ℝ => (starRingEnd ℂ)
      (Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x))
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hgm).norm)
    (hrcont.star.norm.aestronglyMeasurable)
    (by
      refine hg2.congr_fun ?_ measurableSet_Icc
      intro x _
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs])
    (by
      refine (hrcont.norm.pow 2).integrableOn_Icc.congr_fun ?_ measurableSet_Icc
      intro x _
      simp only [Pi.pow_apply, Complex.norm_conj])
  simp only [Complex.conj_conj, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_conj] at hCS
  rw [hsplit]
  calc ‖∫ x in Icc (-a) a, (g x : ℂ) *
        (Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x)‖ ^ (2 : ℕ)
      ≤ (∫ x in Icc (-a) a, g x ^ (2 : ℕ)) * ∫ x in Icc (-a) a,
          ‖Complex.exp (-((x * ξ : ℝ) : ℂ) * Complex.I) - expPhasePartialSum N ξ x‖ ^ (2 : ℕ) := hCS
    _ ≤ (∫ x in Icc (-a) a, g x ^ (2 : ℕ)) * taylorLocalizationBound a N ξ := by
        refine mul_le_mul_of_nonneg_left
          (integral_norm_sq_exp_sub_expPhasePartialSum_le ha N hN) ?_
        exact integral_nonneg fun x => sq_nonneg _
    _ = taylorLocalizationBound a N ξ * ∫ x in Icc (-a) a, g x ^ (2 : ℕ) := mul_comm _ _

end RHTower
