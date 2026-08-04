import GaloisForLFunctions.RHTower.Sieve.TriangularIntegralForm
import GaloisForLFunctions.RHTower.Sieve.LogWindowKernel

/-!
# Gallagher's lemma

Composing the exact overlap identity with the inversion of its kernel: in
`e^{2πiw(log n - log m)} = n^{2πiw} · conj(m^{2πiw})` the two indices separate, so the quadratic form
of `LogWindowKernel.lean` becomes a weighted mean of a Dirichlet polynomial,

    ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du = ∫_ℝ Re 𝓕(δ - |·|)₊(w) · |∑_n a_n n^{2πiw}|² dw ,

with a weight that is real, nonnegative and integrable.  This is the bridge from a short-interval
mean square to the Dirichlet polynomial: no arithmetic enters, only the Fourier pair of the
triangular kernel.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform Finset

/-- The Dirichlet polynomial in the additive variable. -/
noncomputable def logPoly (a : ℕ → ℂ) (s : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I)

theorem continuous_logPoly (a : ℕ → ℂ) (s : Finset ℕ) : Continuous (logPoly a s) := by
  refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)

/-- One term of the expanded mean square. -/
noncomputable def gallagherTerm (a : ℕ → ℂ) (δ : ℝ) (n m : ℕ) (w : ℝ) : ℂ :=
  (a n * (starRingEnd ℂ) (a m))
    * (Complex.exp (((2 * Real.pi * (w * (Real.log n - Real.log m)) : ℝ) : ℂ) * Complex.I)
        * 𝓕 (triC δ) w)

theorem integrable_gallagherTerm {δ : ℝ} (hδ : 0 < δ) (a : ℕ → ℂ) (n m : ℕ) :
    Integrable (gallagherTerm a δ n m) := by
  refine Integrable.const_mul ?_ _
  refine (integrable_fourier_triC hδ).bdd_mul (c := 1) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  · exact Filter.Eventually.of_forall fun w => le_of_eq (Complex.norm_exp_ofReal_mul_I _)

/-- The integral of one term is the exact kernel, weighted. -/
theorem integral_gallagherTerm {δ : ℝ} (hδ : 0 < δ) (a : ℕ → ℂ) (n m : ℕ) :
    (∫ w : ℝ, gallagherTerm a δ n m w)
      = (a n * (starRingEnd ℂ) (a m)) * triC δ (Real.log n - Real.log m) := by
  simp only [gallagherTerm]
  rw [integral_const_mul, ← triC_eq_integral hδ]

/-- The separated form of the phase attached to a pair of indices. -/
theorem phase_sub (w x y : ℝ) :
    Complex.exp (((2 * Real.pi * (w * (x - y)) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((2 * Real.pi * (w * x) : ℝ) : ℂ) * Complex.I)
        * (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * (w * y) : ℝ) : ℂ) * Complex.I)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The double sum of separated phases is the squared modulus of the polynomial. -/
theorem sum_phase_eq_normSq (a : ℕ → ℂ) (s : Finset ℕ) (w : ℝ) :
    (∑ n ∈ s, ∑ m ∈ s, (a n * (starRingEnd ℂ) (a m))
        * Complex.exp (((2 * Real.pi * (w * (Real.log n - Real.log m)) : ℝ) : ℂ) * Complex.I))
      = ((‖logPoly a s w‖ ^ 2 : ℝ) : ℂ) := by
  have hzc : ((‖logPoly a s w‖ ^ 2 : ℝ) : ℂ)
      = logPoly a s w * (starRingEnd ℂ) (logPoly a s w) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hzc, logPoly, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [phase_sub, map_mul]
  ring

/-- The summed integrand is the weight times the squared modulus. -/
theorem sum_gallagherTerm (a : ℕ → ℂ) (s : Finset ℕ) (δ : ℝ) (w : ℝ) :
    (∑ n ∈ s, ∑ m ∈ s, gallagherTerm a δ n m w)
      = 𝓕 (triC δ) w * ((‖logPoly a s w‖ ^ 2 : ℝ) : ℂ) := by
  rw [← sum_phase_eq_normSq a s w, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [gallagherTerm]
  ring

/-- Multiplying by a real number scales the real part. -/
theorem re_mul_ofReal (z : ℂ) (r : ℝ) : (z * (r : ℂ)).re = z.re * r := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Gallagher's lemma.**  The logarithmic short-interval mean square is a nonnegative weighted mean
of the Dirichlet polynomial. -/
theorem gallagher_identity (a : ℕ → ℂ) (s : Finset ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2)
      = ∫ w : ℝ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 := by
  classical
  have hGint : Integrable fun w : ℝ =>
      𝓕 (triC δ) w * ((‖logPoly a s w‖ ^ 2 : ℝ) : ℂ) := by
    have h : Integrable fun w : ℝ => ∑ n ∈ s, ∑ m ∈ s, gallagherTerm a δ n m w :=
      integrable_finsetSum _ fun n _ =>
        integrable_finsetSum _ fun m _ => integrable_gallagherTerm hδ a n m
    exact h.congr (Filter.Eventually.of_forall (sum_gallagherTerm a s δ))
  have hterm : ∀ n m : ℕ,
      (a n * (starRingEnd ℂ) (a m)).re * max (δ - |Real.log n - Real.log m|) 0
        = (∫ w : ℝ, gallagherTerm a δ n m w).re := by
    intro n m
    rw [integral_gallagherTerm hδ, triC, tri, re_mul_ofReal]
  rw [integral_normSq_logWindowSum a s δ]
  calc ∑ n ∈ s, ∑ m ∈ s,
        (a n * (starRingEnd ℂ) (a m)).re * max (δ - |Real.log n - Real.log m|) 0
      = ∑ n ∈ s, ∑ m ∈ s, (∫ w : ℝ, gallagherTerm a δ n m w).re :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => hterm n m
    _ = (∑ n ∈ s, ∑ m ∈ s, ∫ w : ℝ, gallagherTerm a δ n m w).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl fun n _ => (Complex.re_sum _ _).symm
    _ = (∫ w : ℝ, ∑ n ∈ s, ∑ m ∈ s, gallagherTerm a δ n m w).re := by
        rw [integral_finsetSum _ fun n _ =>
          integrable_finsetSum _ fun m _ => integrable_gallagherTerm hδ a n m]
        congr 1
        exact Finset.sum_congr rfl fun n _ =>
          (integral_finsetSum _ fun m _ => integrable_gallagherTerm hδ a n m).symm
    _ = (∫ w : ℝ, 𝓕 (triC δ) w * ((‖logPoly a s w‖ ^ 2 : ℝ) : ℂ)).re := by
        rw [integral_congr_ae (Filter.Eventually.of_forall (sum_gallagherTerm a s δ))]
    _ = ∫ w : ℝ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 := by
        have h := integral_re (μ := volume) hGint
        simp only [RCLike.re_to_complex] at h
        rw [← h]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        exact re_mul_ofReal _ _

/-- **The Gallagher weight has total mass `δ`.**  Its integral is the value of the triangular kernel
at the origin. -/
theorem integral_fourier_triC_re {δ : ℝ} (hδ : 0 < δ) :
    (∫ w : ℝ, (𝓕 (triC δ) w).re) = δ := by
  have h := integral_re (μ := volume) (integrable_fourier_triC hδ)
  simp only [RCLike.re_to_complex] at h
  rw [h]
  have h0 := triC_eq_integral hδ 0
  have hph : ∀ w : ℝ,
      Complex.exp (((2 * Real.pi * (w * (0 : ℝ)) : ℝ) : ℂ) * Complex.I) = 1 := by
    intro w
    norm_num
  simp only [hph, one_mul] at h0
  rw [← h0]
  simp [triC, tri, max_eq_left hδ.le]

theorem integrable_gallagher_weight_mul {δ : ℝ} (hδ : 0 < δ) (a : ℕ → ℂ) (s : Finset ℕ) :
    Integrable fun w : ℝ => (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 := by
  have hGint : Integrable fun w : ℝ =>
      𝓕 (triC δ) w * ((‖logPoly a s w‖ ^ 2 : ℝ) : ℂ) := by
    have h : Integrable fun w : ℝ => ∑ n ∈ s, ∑ m ∈ s, gallagherTerm a δ n m w :=
      integrable_finsetSum _ fun n _ =>
        integrable_finsetSum _ fun m _ => integrable_gallagherTerm hδ a n m
    exact h.congr (Filter.Eventually.of_forall (sum_gallagherTerm a s δ))
  exact hGint.re.congr (Filter.Eventually.of_forall fun w => re_mul_ofReal _ _)

/-- **Gallagher's mean value bound.**  A uniform bound on the Dirichlet polynomial bounds the
logarithmic short-interval mean square by `δ` times it. -/
theorem gallagher_le_of_sup (a : ℕ → ℂ) (s : Finset ℕ) {δ M : ℝ} (hδ : 0 < δ)
    (hbd : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2) ≤ M * δ := by
  rw [gallagher_identity a s hδ]
  have hmono : ∀ w : ℝ,
      (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 ≤ (𝓕 (triC δ) w).re * M :=
    fun w => mul_le_mul_of_nonneg_left (hbd w) (fourier_triC_re_nonneg hδ w)
  have hint2 : Integrable fun w : ℝ => (𝓕 (triC δ) w).re * M :=
    ((integrable_fourier_triC hδ).re).mul_const M
  refine le_trans (integral_mono (integrable_gallagher_weight_mul hδ a s) hint2
    (fun w => hmono w)) ?_
  rw [integral_mul_const, integral_fourier_triC_re hδ]
  ring_nf
  exact le_refl _

end RHTower.Sieve
