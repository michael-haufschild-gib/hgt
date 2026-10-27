import GaloisForLFunctions.ArithmeticPolarization.PositivityIsInheritedByTheLeadingLine

/-!
# Positive polar configurations are nonnegative exponential polynomials

A finite polar configuration `G(s) = Σ_{z ∈ S} c(z)/(s − z)` with real weights is the Laplace
transform of its exponential polynomial `w(t) = Σ_z c(z) e^{zt}`, whose real part is the scale
weight `polarScaleWeight S c t = Σ_z c(z) e^{Re z · t} cos(Im z · t)` (ACP).

* **Bochner direction** (`quadForm_polarSum_eq_integral`, `posDef_polarSum_of_scaleWeight_nonneg`): if the scale weight is
  nonnegative on `t > 0`, every vertical section `u ↦ Re G(σ + iu)` with `σ > Re z` for all `z ∈ S`
  is positive definite. The kernel is the Laplace integral
  `Σ_{i,j} w_i w_j Re G(σ + i(x_i − x_j)) = ∫_0^∞ e^{−σt} |Σ_i w_i e^{−i x_i t}|² Re w(t) dt`;
  no conjugation symmetry is needed.
* **Classification** (`posDef_polarSum_iff_scaleWeight_nonneg`): for a conjugation-symmetric
  configuration, positive-definite vertical sections on every `σ > σ₁` are equivalent to the
  nonnegativity of the scale weight on `(0, ∞)` (the forward direction is ACP's Post–Widder law).
* **Positivity reaches the leading abscissa** (`posDef_polarSum_above_leading`): positivity on
  `σ > σ₁` holds on every `σ` beyond the rightmost weighted point, however far `σ₁` lies to the
  right of it.

So the positive cone of completions with prescribed points is the cone of real weights whose
exponential polynomial is nonnegative on `(0, ∞)`: the leading-line law, its inheritance and the
Fejér barrier are statements about this cone.
-/

open Complex Finset Filter Topology Real MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry

/-- The exponential factorization of one kernel term at the point `r + iy`. -/
theorem exp_kernel_term' (σ r xi xj y t : ℝ) :
    Complex.exp (-(((σ - r : ℝ) : ℂ) + ((xi - xj - y : ℝ) : ℂ) * I) * t) =
      (Real.exp (-(σ * t)) : ℂ) * (Complex.exp (-((xi * t : ℝ) : ℂ) * I) *
        conj (Complex.exp (-((xj * t : ℝ) : ℂ) * I))) *
          ((Real.exp (r * t) : ℂ) * Complex.exp (((y * t : ℝ) : ℂ) * I)) := by
  rw [← Complex.exp_conj, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **The Laplace identity.** Every positive-definiteness sum of a vertical section right of the
configuration is `∫_0^∞ e^{−σt} |Σ_i w_i e^{−i x_i t}|² w(t) dt` with the scale weight `w`. -/
theorem quadForm_polarSum_eq_integral {S : Finset ℂ} {c : ℂ → ℝ} {σ : ℝ}
    (hS : ∀ z ∈ S, z.re < σ) {n : ℕ} (x w : Fin n → ℝ) :
    ∑ i, ∑ j, w i * w j * (polarSum S c ((σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(σ * t)) *
        Complex.normSq (∑ i, (w i : ℂ) * Complex.exp (-((x i * t : ℝ) : ℂ) * I)) *
          polarScaleWeight S c t := by
  set A : ℝ → ℂ := fun t => ∑ i, (w i : ℂ) * Complex.exp (-((x i * t : ℝ) : ℂ) * I)
  set B : ℝ → ℂ := fun t => ∑ z ∈ S, (c z : ℂ) *
    ((Real.exp (z.re * t) : ℂ) * Complex.exp (((z.im * t : ℝ) : ℂ) * I))
  set K : Fin n → Fin n → ℂ → ℂ := fun i j z =>
    ((σ - z.re : ℝ) : ℂ) + ((x i - x j - z.im : ℝ) : ℂ) * I
  -- every denominator is `(σ − Re z) + i(x_i − x_j − Im z)`, with positive real part on `S`
  have hden : ∀ (i j : Fin n) (z : ℂ),
      (σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I - z = K i j z := by
    intro i j z
    simp only [K]
    apply Complex.ext <;> simp
  have hre : ∀ (i j : Fin n) (z : ℂ), z ∈ S → 0 < (K i j z).re := by
    intro i j z hz
    simpa [K] using hS z hz
  have hint : ∀ (i j : Fin n) (z : ℂ), z ∈ S → IntegrableOn
      (fun t : ℝ => Complex.exp (-K i j z * (t : ℂ))) (Ioi 0) :=
    fun i j z hz => integrableOn_exp_neg (hre i j z hz)
  -- the integrand as a sum of kernel terms
  have hexp : ∀ t : ℝ, (Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t =
      ∑ i, ∑ j, ∑ z ∈ S, ((w i * w j : ℝ) : ℂ) * (c z : ℂ) *
        Complex.exp (-K i j z * (t : ℂ)) := by
    intro t
    simp only [A, B, K]
    rw [triple_expand]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun z _ => ?_
    rw [exp_kernel_term', map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hintS : ∀ (i j : Fin n), Integrable (fun t : ℝ => ∑ z ∈ S, ((w i * w j : ℝ) : ℂ) *
      (c z : ℂ) * Complex.exp (-K i j z * (t : ℂ))) (volume.restrict (Ioi 0)) :=
    fun i j => integrable_finsetSum _ fun z hz => (hint i j z hz).const_mul _
  have hlap : ∑ i, ∑ j, ((w i * w j : ℝ) : ℂ) * polarSum S c ((σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I) =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t := by
    rw [show (fun t : ℝ => (Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t) =
      fun t : ℝ => ∑ i, ∑ j, ∑ z ∈ S, ((w i * w j : ℝ) : ℂ) * (c z : ℂ) *
        Complex.exp (-K i j z * (t : ℂ)) from funext hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hintS i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hintS i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun z hz => (hint i j z hz).const_mul _, polarSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [integral_const_mul, ← inv_eq_integral_exp (hre i j z hz), ← hden i j z, div_eq_mul_inv]
    ring
  -- take real parts
  have hsum : ∑ i, ∑ j, w i * w j * (polarSum S c ((σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re =
      (∫ t in Ioi (0 : ℝ), (Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t).re := by
    rw [← hlap, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul]
  have hfun : ∀ t, ((Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t).re =
      Real.exp (-(σ * t)) * Complex.normSq (A t) * polarScaleWeight S c t := by
    intro t
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.re_ofReal_mul, polarScaleWeight]
    simp only [B, Complex.re_sum, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    refine congrArg _ (Finset.sum_congr rfl fun z _ => ?_)
    ring
  have hintR : Integrable (fun t : ℝ => (Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t)
      (volume.restrict (Ioi 0)) := by
    rw [show (fun t : ℝ => (Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t) =
        fun t : ℝ => ∑ i, ∑ j, ∑ z ∈ S, ((w i * w j : ℝ) : ℂ) * (c z : ℂ) *
          Complex.exp (-K i j z * (t : ℂ)) from funext hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hintS i j
  rw [hsum, show (∫ t in Ioi (0 : ℝ), (Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t).re =
    ∫ t in Ioi (0 : ℝ), ((Real.exp (-(σ * t)) : ℂ) * (A t * conj (A t)) * B t).re from
      (integral_re hintR).symm]
  exact integral_congr_ae (Filter.Eventually.of_forall hfun)

/-- **Bochner direction.** A nonnegative scale weight makes every vertical section to the right of
the configuration positive definite. -/
theorem posDef_polarSum_of_scaleWeight_nonneg {S : Finset ℂ} {c : ℂ → ℝ} {σ : ℝ}
    (hS : ∀ z ∈ S, z.re < σ) (hw : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t) :
    IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
  intro n x w
  have h := quadForm_polarSum_eq_integral (c := c) hS x w
  have hgoal : 0 ≤ ∑ i, ∑ j, w i * w j * (polarSum S c ((σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re := by
    rw [h]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)) (hw t ht)
  simpa only [Complex.ofReal_sub] using hgoal

/-- **Classification of positive polar configurations.** For a conjugation-symmetric configuration
in `Re z ≤ σ₁`, positive-definite vertical sections on every `σ > σ₁` are equivalent to a
nonnegative scale weight on `(0, ∞)`. -/
theorem posDef_polarSum_iff_scaleWeight_nonneg {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁) :
    (∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) ↔
      ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t :=
  ⟨fun hpd _ ht => posDef_polarSum_laplaceWeight_nonneg hS_conj hc_conj hS_re hpd ht,
    fun hw _ hσ => posDef_polarSum_of_scaleWeight_nonneg
      (fun z hz => (hS_re z hz).trans_lt hσ) hw⟩

/-- Points of weight zero do not change the configuration. -/
theorem polarSum_filter_ne_zero (S : Finset ℂ) (c : ℂ → ℝ) (s : ℂ) :
    polarSum (S.filter fun z => c z ≠ 0) c s = polarSum S c s := by
  rw [polarSum, polarSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : c z = 0 <;> simp [h]

theorem polarScaleWeight_filter_ne_zero (S : Finset ℂ) (c : ℂ → ℝ) (t : ℝ) :
    polarScaleWeight (S.filter fun z => c z ≠ 0) c t = polarScaleWeight S c t := by
  rw [polarScaleWeight, polarScaleWeight, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : c z = 0 <;> simp [h]

/-- **Positivity reaches the leading abscissa.** Positivity on `σ > σ₁` holds at every `σ` to the
right of all weighted points. -/
theorem posDef_polarSum_above_leading {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    {σ : ℝ} (hσ : ∀ z ∈ S, c z ≠ 0 → z.re < σ) :
    IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
  have hw := (posDef_polarSum_iff_scaleWeight_nonneg hS_conj hc_conj hS_re).mp hpd
  have h := posDef_polarSum_of_scaleWeight_nonneg (S := S.filter fun z => c z ≠ 0) (c := c)
    (σ := σ) (fun z hz => hσ z (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2)
    (fun t ht => by rw [polarScaleWeight_filter_ne_zero]; exact hw t ht)
  simpa only [polarSum_filter_ne_zero] using h

end GaloisForLFunctions.ArithmeticPolarization
