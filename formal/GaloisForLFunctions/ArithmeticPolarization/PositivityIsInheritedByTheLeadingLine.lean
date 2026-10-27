import GaloisForLFunctions.ArithmeticPolarization.TheLeadingLineIsPositive

/-!
# Positivity is inherited by the leading line

`TheLeadingLineIsPositive` shows that the leading line of a positive polar configuration carries a
nonnegative trigonometric sum. That is the only constraint:

* **One line** (`posDef_polarSum_of_line`): a finite polar configuration `Σ_z c(z)/(s − z)` on one
  vertical line `Re z = σ₀` has positive-definite vertical sections on every `σ > σ₀` as soon as
  `T(t) = Σ_z c(z) cos(Im z · t) ≥ 0` for `t > 0`. The kernel is the Laplace transform
  `Σ_{i,j} w_i w_j Re G(σ + i(x_i − x_j)) = ∫_0^∞ e^{−(σ−σ₀)t} |Σ_i w_i e^{−i x_i t}|² T(t) dt`.
* **Inheritance** (`posDef_leadingLine`): the leading line of a positive configuration is itself a
  positive configuration. Every positivity statement about the deepest line of a positive
  completion is therefore a statement about a single nonnegative trigonometric sum, and conversely
  every nonnegative trigonometric sum is the leading line of a positive configuration.
-/

open Complex Finset Filter Topology Real MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry

/-- `a⁻¹ = ∫_0^∞ e^{−at} dt` for `Re a > 0`. -/
theorem inv_eq_integral_exp {a : ℂ} (ha : 0 < a.re) :
    a⁻¹ = ∫ t in Ioi (0 : ℝ), Complex.exp (-a * t) := by
  rw [integral_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0]
  simp [neg_div, div_neg]

theorem integrableOn_exp_neg {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-a * t)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa using ha) 0

/-- The exponential factorization of one kernel term. -/
theorem exp_kernel_term (b xi xj y t : ℝ) :
    Complex.exp (-((b : ℂ) + ((xi - xj - y : ℝ) : ℂ) * I) * t) =
      (Real.exp (-(b * t)) : ℂ) * (Complex.exp (-((xi * t : ℝ) : ℂ) * I) *
        conj (Complex.exp (-((xj * t : ℝ) : ℂ) * I))) * Complex.exp (((y * t : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Expanding `E · |Σ u_i|² · Σ v_z` into a triple sum. -/
theorem triple_expand {n : ℕ} (E : ℂ) (u : Fin n → ℂ) (S : Finset ℂ) (v : ℂ → ℂ) :
    E * ((∑ i, u i) * conj (∑ j, u j)) * (∑ z ∈ S, v z) =
      ∑ i, ∑ j, ∑ z ∈ S, E * (u i * conj (u j)) * v z := by
  calc E * ((∑ i, u i) * conj (∑ j, u j)) * (∑ z ∈ S, v z)
      = ∑ z ∈ S, E * ((∑ i, u i) * conj (∑ j, u j)) * v z := Finset.mul_sum _ _ _
    _ = ∑ z ∈ S, ∑ i, ∑ j, E * (u i * conj (u j)) * v z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- **A configuration on one line is positive iff its trigonometric sum is.** -/
theorem posDef_polarSum_of_line {S : Finset ℂ} {c : ℂ → ℝ} {σ₀ : ℝ}
    (hline : ∀ z ∈ S, z.re = σ₀)
    (hT : ∀ t : ℝ, 0 < t → 0 ≤ ∑ z ∈ S, c z * Real.cos (z.im * t)) {σ : ℝ} (hσ : σ₀ < σ) :
    IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
  intro n x w
  set b := σ - σ₀ with hb
  have hb0 : 0 < b := by linarith
  set A : ℝ → ℂ := fun t => ∑ i, (w i : ℂ) * Complex.exp (-((x i * t : ℝ) : ℂ) * I)
  set B : ℝ → ℂ := fun t => ∑ z ∈ S, (c z : ℂ) * Complex.exp (((z.im * t : ℝ) : ℂ) * I)
  -- every denominator is `b + i(x_i − x_j − Im z)`
  have hden : ∀ (i j : Fin n) (z : ℂ), z ∈ S →
      (σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I - z = (b : ℂ) + ((x i - x j - z.im : ℝ) : ℂ) * I := by
    intro i j z hz
    have hz' : z = (σ₀ : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hline z hz]
    rw [hz']; simp only [hb]; push_cast; ring_nf; simp
  have hre : ∀ (i j : Fin n) (z : ℂ), 0 < ((b : ℂ) + ((x i - x j - z.im : ℝ) : ℂ) * I).re := by
    intro i j z; simpa using hb0
  -- the complex Laplace identity
  have hint : ∀ (i j : Fin n) (z : ℂ), IntegrableOn
      (fun t : ℝ => Complex.exp (-((b : ℂ) + ((x i - x j - z.im : ℝ) : ℂ) * I) * (t : ℂ)))
        (Ioi 0) :=
    fun i j z => integrableOn_exp_neg (hre i j z)
  -- the integrand as a sum of kernel terms
  have hexp : ∀ t : ℝ, (Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t =
      ∑ i, ∑ j, ∑ z ∈ S, ((w i * w j : ℝ) : ℂ) * (c z : ℂ) *
        Complex.exp (-((b : ℂ) + ((x i - x j - z.im : ℝ) : ℂ) * I) * (t : ℂ)) := by
    intro t
    simp only [A, B]
    rw [triple_expand]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun z _ => ?_
    rw [exp_kernel_term, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hlap : ∑ i, ∑ j, ((w i * w j : ℝ) : ℂ) * polarSum S c ((σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I) =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t := by
    rw [show (fun t : ℝ => (Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t) =
      fun t : ℝ => ∑ i, ∑ j, ∑ z ∈ S, ((w i * w j : ℝ) : ℂ) * (c z : ℂ) *
        Complex.exp (-((b : ℂ) + ((x i - x j - z.im : ℝ) : ℂ) * I) * (t : ℂ)) from funext hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun z _ => (hint i j z).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun z _ =>
      (hint i j z).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun z _ => (hint i j z).const_mul _, polarSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [integral_const_mul, ← inv_eq_integral_exp (hre i j z), ← hden i j z hz, div_eq_mul_inv]
    ring
  -- take real parts
  have hsum : ∑ i, ∑ j, w i * w j * (polarSum S c ((σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re =
      (∫ t in Ioi (0 : ℝ), (Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t).re := by
    rw [← hlap, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.re_ofReal_mul]
  have hfun : ∀ t, ((Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t).re =
      Real.exp (-(b * t)) * Complex.normSq (A t) * ∑ z ∈ S, c z * Real.cos (z.im * t) := by
    intro t
    rw [Complex.mul_conj, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    simp only [B, Complex.re_sum, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hintR : Integrable (fun t : ℝ => (Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t)
      (volume.restrict (Ioi 0)) := by
    rw [show (fun t : ℝ => (Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t) =
        fun t : ℝ => ∑ i, ∑ j, ∑ z ∈ S, ((w i * w j : ℝ) : ℂ) * (c z : ℂ) *
          Complex.exp (-((b : ℂ) + ((x i - x j - z.im : ℝ) : ℂ) * I) * (t : ℂ)) from funext hexp]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun z _ => (hint i j z).const_mul _
  have hgoal : 0 ≤ ∑ i, ∑ j, w i * w j * (polarSum S c ((σ : ℂ) + ((x i - x j : ℝ) : ℂ) * I)).re := by
    rw [hsum, show (∫ t in Ioi (0 : ℝ), (Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t).re =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-(b * t)) : ℂ) * (A t * conj (A t)) * B t).re from
        (integral_re hintR).symm]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    rw [hfun]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)) (hT t ht)
  simpa only [Complex.ofReal_sub] using hgoal

/-- **Inheritance.** The leading line of a positive configuration is a positive configuration. -/
theorem posDef_leadingLine {S : Finset ℂ} {c : ℂ → ℝ} {σ₁ σmax : ℝ}
    (hS_conj : ∀ z ∈ S, conj z ∈ S) (hc_conj : ∀ z ∈ S, c (conj z) = c z)
    (hS_re : ∀ z ∈ S, z.re ≤ σ₁)
    (hpd : ∀ σ : ℝ, σ₁ < σ → IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re)
    (hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ σmax) {σ : ℝ} (hσ : σmax < σ) :
    IsPosDef fun u : ℝ =>
      (polarSum (S.filter fun z => z.re = σmax) c ((σ : ℂ) + (u : ℂ) * I)).re :=
  posDef_polarSum_of_line (fun _ hz => (Finset.mem_filter.mp hz).2)
    (fun t _ => leadingSum_nonneg hS_conj hc_conj hS_re hpd hmax t) hσ

end GaloisForLFunctions.ArithmeticPolarization
