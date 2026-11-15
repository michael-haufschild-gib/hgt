import GaloisForLFunctions.RHTower.Sieve.DiscreteParseval
import GaloisForLFunctions.RHTower.Sieve.CoefficientExpansion
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PrimitiveRootProjectors

/-!
# Fourier coordinates for sextic phase filters

Exact discrete Parseval and primitive-root character projection give mutually
inverse coefficient and phase descriptions. The geometric row is a degree-five
polynomial divided by `1-Y⁶`; its filtered value is consequently an explicit
linear functional of the six Fourier coefficients.
-/

noncomputable section
open Finset Complex
open scoped Classical ComplexConjugate InnerProductSpace
namespace GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies

/-- Six Fourier coefficients evaluated on a sextic phase. -/
def sexticPolynomial (c : Fin 6 → ℂ) (ρ : ℂ) : ℂ :=
  ∑ j : Fin 6, c j * ρ ^ j.val

/-- Parseval expresses phase energy as the exact coefficient energy. -/
theorem sexticPolynomial_energy {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (c : Fin 6 → ℂ) :
    ∑ i : Fin 6, ‖sexticPolynomial c (ζ ^ i.val)‖ ^ 2 =
      6 * ∑ j : Fin 6, ‖c j‖ ^ 2 := by
  let x : EuclideanSpace ℂ (Fin 6) := WithLp.toLp 2 (fun j => conj (c j))
  have hi (i : Fin 6) :
      ⟪RHTower.Sieve.expRow 6 (ζ ^ i.val), x⟫_ℂ =
        conj (sexticPolynomial c (ζ ^ i.val)) := by
    rw [RHTower.Sieve.inner_expRow_apply, sexticPolynomial, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change conj ((ζ ^ i.val) ^ j.val) * conj (c j) =
      conj (c j * (ζ ^ i.val) ^ j.val)
    rw [map_mul, mul_comm]
  have hx : ‖x‖ ^ 2 = ∑ j : Fin 6, ‖c j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ‖conj (c j)‖ ^ 2 = _
    rw [norm_conj]
  have h := RHTower.Sieve.sum_norm_inner_expRow_root (by norm_num) hζ x
  simpa only [hi, norm_conj, hx, Nat.cast_ofNat] using h

/-- Fourier coefficients of six observed phase values. -/
def sexticCoefficients (ζ : ℂ) (f : Fin 6 → ℂ) (j : Fin 6) : ℂ :=
  (1 / 6 : ℂ) * ∑ i : Fin 6, f i / (ζ ^ i.val) ^ j.val

/-- The six character coordinates reconstruct every phase input. -/
theorem sexticPolynomial_coefficients {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (f : Fin 6 → ℂ) (i : Fin 6) :
    sexticPolynomial (sexticCoefficients ζ f) (ζ ^ i.val) = f i := by
  unfold sexticPolynomial sexticCoefficients
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have ht (k : Fin 6) :
      (∑ j : Fin 6, ((1 / 6 : ℂ) * (f k / (ζ ^ k.val) ^ j.val)) *
        (ζ ^ i.val) ^ j.val) = (f k / 6) * (if k = i then 6 else 0) := by
    have hs := ArithmeticHarmonicAnalysis.primitiveRoot_ratio_sum hζ k i
    rw [← Fin.sum_univ_eq_sum_range] at hs
    calc
      _ = (f k / 6) * ∑ j : Fin 6, (ζ ^ i.val / ζ ^ k.val) ^ j.val := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [div_pow]
        ring
      _ = _ := by simp only [hs, Nat.cast_ofNat]
  simp_rw [ht]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The Fourier coefficients have precisely one sixth of the observed phase energy. -/
theorem sexticCoefficients_energy {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (f : Fin 6 → ℂ) :
    ∑ i : Fin 6, ‖f i‖ ^ 2 = 6 * ∑ j : Fin 6, ‖sexticCoefficients ζ f j‖ ^ 2 := by
  simpa only [sexticPolynomial_coefficients hζ] using
    sexticPolynomial_energy hζ (sexticCoefficients ζ f)

/-- Character projection recovers each coefficient below degree six. -/
theorem sexticCoefficients_polynomial {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (c : Fin 6 → ℂ) (j : Fin 6) :
    sexticCoefficients ζ (fun i => sexticPolynomial c (ζ ^ i.val)) j = c j := by
  unfold sexticCoefficients sexticPolynomial
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]
  have ht (k : Fin 6) :
      (∑ i : Fin 6, (c k * (ζ ^ i.val) ^ k.val) / (ζ ^ i.val) ^ j.val) =
        c k * (if j = k then 6 else 0) := by
    have hs := ArithmeticHarmonicAnalysis.primitiveRoot_ratio_sum hζ j k
    rw [← Fin.sum_univ_eq_sum_range] at hs
    calc
      _ = c k * ∑ i : Fin 6, (ζ ^ k.val / ζ ^ j.val) ^ i.val := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [div_pow]
        simp only [← pow_mul, Nat.mul_comm i.val]
        ring
      _ = _ := by simp only [hs, Nat.cast_ofNat]
  simp_rw [ht]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- The normalized pairing of six phase weights and six observations. -/
def sexticReadout (w f : Fin 6 → ℂ) : ℂ := (1 / 6 : ℂ) * ∑ i, w i * f i

/-- The constant observation reads the zero Fourier coefficient. -/
theorem sexticReadout_one (ζ : ℂ) (w : Fin 6 → ℂ) :
    sexticReadout w (fun _ => 1) = sexticCoefficients ζ w 0 := by
  simp only [sexticReadout, sexticCoefficients, Fin.val_zero, pow_zero, div_one, mul_one]

/-- A positive monomial reads the complementary Fourier coefficient. -/
theorem sexticReadout_monomial {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (w : Fin 6 → ℂ)
    {k : ℕ} (hk : 0 < k) (hk6 : k ≤ 6) :
    sexticReadout w (fun i => (ζ ^ i.val) ^ k) =
      sexticCoefficients ζ w ⟨6 - k, by omega⟩ := by
  have hz : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  unfold sexticReadout sexticCoefficients
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  apply (eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hz))).mpr
  rw [mul_assoc, ← pow_add, show k + (6 - k) = 6 by omega,
    ← pow_mul, Nat.mul_comm i.val 6, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

/-- The mean of a polynomial below degree six is exactly its constant coefficient. -/
theorem sexticPolynomial_average {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6) (c : Fin 6 → ℂ) :
    (1 / 6 : ℂ) * ∑ i : Fin 6, sexticPolynomial c (ζ ^ i.val) = c 0 := by
  have h := sexticCoefficients_polynomial hζ c 0
  simpa only [sexticCoefficients, Fin.val_zero, pow_zero, div_one] using h

/-- Cubic row numerators may be multiplied by a quadratic without creating a
new constant mode on the six phases. -/
theorem sextic_average_cubic_mul_quadratic {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (a b c d u v : ℂ) :
    (1 / 6 : ℂ) * ∑ i : Fin 6,
      (a + b * ζ ^ i.val + c * (ζ ^ i.val) ^ 2 + d * (ζ ^ i.val) ^ 3) *
        (1 + u * ζ ^ i.val + v * (ζ ^ i.val) ^ 2) = a := by
  let coeff : Fin 6 → ℂ := ![a, b + a * u, c + b * u + a * v,
    d + c * u + b * v, d * u + c * v, d * v]
  have he (ρ : ℂ) : (a + b * ρ + c * ρ ^ 2 + d * ρ ^ 3) *
      (1 + u * ρ + v * ρ ^ 2) = sexticPolynomial coeff ρ := by
    simp only [sexticPolynomial, coeff, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
    ring
  simp_rw [he]
  simpa only [coeff, Matrix.cons_val_zero] using sexticPolynomial_average hζ coeff

/-- Exact polynomial expression for the geometric row, away from its six poles. -/
theorem sextic_geometric_expansion (ρ Y : ℂ) (hρ : ρ ^ 6 = 1) (hY : Y ^ 6 ≠ 1) :
    ρ * Y * (1 - ρ * Y)⁻¹ =
      (Y ^ 6 + Y * ρ + Y ^ 2 * ρ ^ 2 + Y ^ 3 * ρ ^ 3 +
        Y ^ 4 * ρ ^ 4 + Y ^ 5 * ρ ^ 5) / (1 - Y ^ 6) := by
  have hy : 1 - ρ * Y ≠ 0 := by
    intro h
    have he : ρ * Y = 1 := (sub_eq_zero.mp h).symm
    have hh := congrArg (fun z : ℂ => z ^ 6) he
    rw [mul_pow, hρ, one_mul, one_pow] at hh
    exact hY hh
  have hy6 : 1 - Y ^ 6 ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
  rw [← div_eq_mul_inv]
  apply (div_eq_div_iff hy hy6).mpr
  linear_combination Y ^ 6 * hρ

/-- Geometric cancellation is an explicit linear equation in all six Fourier
coefficients, with the phase information retained. -/
theorem sexticReadout_geometric {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 6)
    (w : Fin 6 → ℂ) (Y : ℂ) (hY : Y ^ 6 ≠ 1) :
    sexticReadout w (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) =
      (Y ^ 6 * sexticCoefficients ζ w 0 + Y * sexticCoefficients ζ w 5 +
        Y ^ 2 * sexticCoefficients ζ w 4 + Y ^ 3 * sexticCoefficients ζ w 3 +
        Y ^ 4 * sexticCoefficients ζ w 2 + Y ^ 5 * sexticCoefficients ζ w 1) /
          (1 - Y ^ 6) := by
  have hr (i : Fin 6) : (ζ ^ i.val) ^ 6 = 1 := by
    rw [← pow_mul, Nat.mul_comm i.val 6, pow_mul, hζ.pow_eq_one, one_pow]
  have he : sexticReadout w (fun i => ζ ^ i.val * Y * (1 - ζ ^ i.val * Y)⁻¹) =
      (Y ^ 6 * sexticReadout w (fun _ => 1) +
        Y * sexticReadout w (fun i => (ζ ^ i.val) ^ 1) +
        Y ^ 2 * sexticReadout w (fun i => (ζ ^ i.val) ^ 2) +
        Y ^ 3 * sexticReadout w (fun i => (ζ ^ i.val) ^ 3) +
        Y ^ 4 * sexticReadout w (fun i => (ζ ^ i.val) ^ 4) +
        Y ^ 5 * sexticReadout w (fun i => (ζ ^ i.val) ^ 5)) / (1 - Y ^ 6) := by
    simp_rw [sextic_geometric_expansion _ Y (hr _) hY]
    unfold sexticReadout
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    rw [← Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [he, sexticReadout_one ζ w]
  rw [sexticReadout_monomial hζ w (by norm_num : 0 < 1) (by norm_num),
    sexticReadout_monomial hζ w (by norm_num : 0 < 2) (by norm_num),
    sexticReadout_monomial hζ w (by norm_num : 0 < 3) (by norm_num),
    sexticReadout_monomial hζ w (by norm_num : 0 < 4) (by norm_num),
    sexticReadout_monomial hζ w (by norm_num : 0 < 5) (by norm_num)]

end GaloisForLFunctions.CoherenceTheoryOfReciprocityFamilies
