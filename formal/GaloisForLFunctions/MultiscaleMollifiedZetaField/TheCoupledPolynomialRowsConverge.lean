import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedPrincipalRowIsAProfileProduct
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Coupled shifted polynomial rows

Polynomial harmonic moments are their unit-interval integrals. Replacing
the two Möbius profiles therefore evaluates every fixed principal row at
the coupled shift, including varying normalized shifts and polynomial
logarithmic weights.
-/

open Filter MeasureTheory Set Topology Polynomial

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

theorem normalizedHarmonicArray_add (c N : ℕ) (f g : ℕ → ℝ) :
    normalizedHarmonicArray c N (fun d => f d + g d) =
      normalizedHarmonicArray c N f + normalizedHarmonicArray c N g := by
  simp only [normalizedHarmonicArray, add_div, Finset.sum_add_distrib]

theorem normalizedHarmonicArray_const_mul (c N : ℕ) (a : ℝ) (f : ℕ → ℝ) :
    normalizedHarmonicArray c N (fun d => a * f d) = a * normalizedHarmonicArray c N f := by
  simp only [normalizedHarmonicArray, mul_div_assoc, ← Finset.mul_sum]

theorem normalizedHarmonicArray_pow (c N j : ℕ) :
    normalizedHarmonicArray c N (fun d => (Real.log d / Real.log N) ^ j) =
      normalizedHarmonicLogMoment j c N := rfl

/-- Every polynomial harmonic average tends to its Lebesgue integral on the unit interval. -/
theorem tendsto_normalizedHarmonicArray_eval (p : ℝ[X]) {c : ℕ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => normalizedHarmonicArray c N
      (fun d => p.eval (Real.log d / Real.log N)))
      atTop (𝓝 (∫ t : ℝ in 0..1, p.eval t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add, normalizedHarmonicArray_add,
        intervalIntegral.integral_add p.continuous.intervalIntegrable q.continuous.intervalIntegrable] using hp.add hq
  | monomial j a =>
      simpa only [Polynomial.eval_monomial, normalizedHarmonicArray_const_mul,
        normalizedHarmonicArray_pow, intervalIntegral.integral_const_mul, integral_pow,
        one_pow, zero_pow (Nat.succ_ne_zero j), sub_zero, Nat.cast_add, Nat.cast_one]
        using (tendsto_normalizedHarmonicLogMoment j hc).const_mul a

/-- Harmonic products of polynomial Möbius profiles have the predicted integral,
with any fixed logarithmic weight and any convergent normalized shift. -/
theorem tendsto_polynomialProfile_harmonic_product (P Q : ℝ[X])
    (hP0 : P.eval 0 = 0) (hQ0 : Q.eval 0 = 0)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hac : a ≤ c) (hbc : b ≤ c)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (m : ℕ) :
    Tendsto (fun N : ℕ => normalizedHarmonicArray c N (fun d =>
      (Real.log d / Real.log N) ^ m *
        (normalizedShiftedMobiusProfile P.eval (Real.log N) (dilatedLogProfileCoordinate a N d) (v N) *
          normalizedShiftedMobiusProfile Q.eval (Real.log N) (dilatedLogProfileCoordinate b N d) (v N))))
      atTop (𝓝 (∫ t : ℝ in 0..1, t ^ m *
        ((P.derivative.eval (1 - t) - v₀ * P.eval (1 - t)) *
          (Q.derivative.eval (1 - t) - v₀ * Q.eval (1 - t))))) := by
  let R : ℝ[X] := X ^ m *
    ((P.derivative - C v₀ * P).comp (1 - X) * (Q.derivative - C v₀ * Q).comp (1 - X))
  have hR (t : ℝ) : R.eval t = t ^ m *
      ((P.derivative.eval (1 - t) - v₀ * P.eval (1 - t)) *
        (Q.derivative.eval (1 - t) - v₀ * Q.eval (1 - t))) := by
    simp only [R, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C]
  have hm := tendsto_normalizedHarmonicArray_eval R (ha.trans_le hac)
  simp_rw [hR] at hm
  have he := tendsto_harmonicMean_profile_product_error P.hasDerivAt P.derivative.hasDerivAt
    P.derivative.derivative.continuous hP0 Q.hasDerivAt Q.derivative.hasDerivAt
    Q.derivative.derivative.continuous hQ0 ha hb hac hbc hv m
  have hh := he.add hm
  simp only [zero_add] at hh
  convert hh using 1
  funext N
  simp only [normalizedHarmonicArray, mul_sub, sub_div, Finset.sum_sub_distrib]
  ring

/-- The exact coupled principal row has the shifted Selberg polynomial integral. -/
theorem tendsto_shiftedProfileHarmonicRow_coupled (P Q : ℝ[X])
    (hP0 : P.eval 0 = 0) (hQ0 : Q.eval 0 = 0)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {v : ℕ → ℝ} {v₀ : ℝ} (hv : Tendsto v atTop (𝓝 v₀)) (k : ℕ) :
    Tendsto (fun N : ℕ => shiftedProfileHarmonicRow P.eval Q.eval N a b (-2 * v N) (v N) k)
      atTop (𝓝 (∫ t : ℝ in 0..1, t ^ k *
        ((P.derivative.eval (1 - t) - v₀ * P.eval (1 - t)) *
          (Q.derivative.eval (1 - t) - v₀ * Q.eval (1 - t))))) := by
  have hprod := tendsto_polynomialProfile_harmonic_product P Q hP0 hQ0 ha hb
    (le_max_left a b) (le_max_right a b) hv k
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexponent : Tendsto (fun N : ℕ => v N * (Real.log a + Real.log b) / Real.log N)
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hv.mul
      (show Tendsto (fun N : ℕ => (Real.log a + Real.log b) / Real.log N) atTop (𝓝 0) from
        tendsto_const_nhds.div_atTop hlog)
  have hexp : Tendsto (fun N : ℕ => Real.exp (v N * (Real.log a + Real.log b) / Real.log N))
      atTop (𝓝 1) := by simpa only [Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp hexponent
  have hh := hexp.mul hprod
  simp only [one_mul] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (shiftedProfileHarmonicRow_coupled P.eval Q.eval (v N) k (by omega) ha hb).symm

end GaloisForLFunctions.MultiscaleMollifiedZetaField
