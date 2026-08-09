import GaloisForLFunctions.RHTower.ReverseBesselFixedFrequencyBlindness
import GaloisForLFunctions.RHTower.SquaredXiChebyshevWindow

/-!
# Positive integral representation of reverse-Bessel radial jets

The reverse-Bessel polynomial already used by the squared-Xi radial-jet construction has the exact
Gamma-moment representation

`B_n(x) = (1 / n!) ∫₀^∞ exp (-u) u^n (x + u / 2)^n du`.

The proof expands the positive kernel by the binomial theorem, evaluates each Gamma moment using
the project Gamma-integral infrastructure, and identifies the resulting coefficient with the
existing recursive radial-jet weight through its exact closed form.  Thus this representation is
connected to the actual HGT polynomial rather than a parallel definition.
-/

open scoped BigOperators
open Set MeasureTheory

namespace RHTower

noncomputable section

private theorem gamma_binomial_coefficient_eq_weight (n j : ℕ) (hj : j ≤ n) :
    (1 / (n.factorial : ℝ)) *
        ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j) * ((2 * n - j).factorial : ℝ)) =
      (squaredRadialJetWeight n j : ℝ) := by
  rw [Nat.cast_choose ℝ hj]
  have hbR := congrArg (fun q : ℚ => (q : ℝ))
    (squaredRadialJetWeight_eq_closedForm n j hj)
  norm_num [squaredRadialJetWeightClosedForm] at hbR
  rw [hbR]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hnj : ((n - j).factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem reverseBessel_integrand_expand (n : ℕ) (x u : ℝ) :
    Real.exp (-u) * u ^ n * (x + u / 2) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j) * x ^ j) *
          (u ^ (2 * n - j) * Real.exp (-u)) := by
  rw [add_pow x (u / 2) n, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hjmem => ?_)
  have hj : j ≤ n := by simpa using Finset.mem_range.mp hjmem
  have hpow : u ^ n * (u / 2) ^ (n - j) =
      u ^ (2 * n - j) / (2 : ℝ) ^ (n - j) := by
    rw [div_pow]
    field_simp
    rw [← pow_add]
    congr 1
    omega
  calc
    Real.exp (-u) * u ^ n * (x ^ j * (u / 2) ^ (n - j) * (n.choose j : ℝ)) =
        Real.exp (-u) * x ^ j * (n.choose j : ℝ) *
          (u ^ n * (u / 2) ^ (n - j)) := by ring
    _ = Real.exp (-u) * x ^ j * (n.choose j : ℝ) *
          (u ^ (2 * n - j) / (2 : ℝ) ^ (n - j)) := by rw [hpow]
    _ = ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j) * x ^ j) *
          (u ^ (2 * n - j) * Real.exp (-u)) := by ring

private theorem reverseBessel_integrand_integrable (n j : ℕ) :
    IntegrableOn
      (fun u : ℝ =>
        ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j)) *
          (u ^ (2 * n - j) * Real.exp (-u)))
      (Ioi (0 : ℝ)) := by
  have h := integrableOn_pow_mul_exp_neg_mul_Ioi (r := (1 : ℝ)) one_pos (2 * n - j)
  change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
  simpa using h.const_mul ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j))

private theorem integral_pow_mul_exp_neg_Ioi_one (k : ℕ) :
    ∫ u in Ioi (0 : ℝ), u ^ k * Real.exp (-u) = (k.factorial : ℝ) := by
  simpa using integral_pow_mul_exp_neg_mul_Ioi (r := (1 : ℝ)) one_pos k

/-- The reverse-Bessel integral kernel is strictly positive on the positive half-line whenever
the polynomial argument is nonnegative. -/
theorem reverseBessel_integrand_pos (n : ℕ) {x u : ℝ} (hx : 0 ≤ x) (hu : 0 < u) :
    0 < Real.exp (-u) * u ^ n * (x + u / 2) ^ n := by
  have hxu : 0 < x + u / 2 := by linarith
  positivity

/-- Exact positive integral representation of the reverse-Bessel radial polynomial:
`B_n(x) = (1/n!) ∫₀^∞ e⁻ᵘ uⁿ (x + u/2)ⁿ du`. -/
theorem reverseBesselPoly_eq_positiveIntegral (n : ℕ) (x : ℝ) :
    reverseBesselPoly n x =
      (1 / (n.factorial : ℝ)) *
        ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ n * (x + u / 2) ^ n := by
  have hcongr :
      (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ n * (x + u / 2) ^ n) =
        ∫ u in Ioi (0 : ℝ), ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j) * x ^ j) *
            (u ^ (2 * n - j) * Real.exp (-u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    exact reverseBessel_integrand_expand n x u
  rw [hcongr]
  rw [MeasureTheory.integral_finsetSum _ (fun j hjmem => ?_)]
  · unfold reverseBesselPoly
    rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl (fun j hjmem => ?_)).symm
    have hj : j ≤ n := by simpa using Finset.mem_range.mp hjmem
    rw [MeasureTheory.integral_const_mul, integral_pow_mul_exp_neg_Ioi_one]
    calc
      (1 / (n.factorial : ℝ)) *
          ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j) * x ^ j *
            ((2 * n - j).factorial : ℝ)) =
        ((1 / (n.factorial : ℝ)) *
          ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j) *
            ((2 * n - j).factorial : ℝ))) * x ^ j := by ring
      _ = (squaredRadialJetWeight n j : ℝ) * x ^ j := by
        rw [gamma_binomial_coefficient_eq_weight n j hj]
  · have hbase := reverseBessel_integrand_integrable n j
    change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbase.const_mul (x ^ j)

/-- The positive reverse-Bessel Gamma kernel is integrable on the positive ray.  This is the
analytic companion of `reverseBesselPoly_eq_positiveIntegral`, exposed for finite source
superpositions whose Gamma integrals must be exchanged with a coefficient sum. -/
theorem integrableOn_reverseBesselPositiveIntegrand (n : ℕ) (x : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-u) * u ^ n * (x + u / 2) ^ n)
      (Ioi (0 : ℝ)) := by
  have hsum : IntegrableOn
      (fun u : ℝ => ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) / (2 : ℝ) ^ (n - j) * x ^ j) *
          (u ^ (2 * n - j) * Real.exp (-u)))
      (Ioi (0 : ℝ)) := by
    exact integrable_finsetSum (Finset.range (n + 1)) fun j hj => by
      have hbase := reverseBessel_integrand_integrable n j
      change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
      simpa [mul_assoc, mul_left_comm, mul_comm] using hbase.const_mul (x ^ j)
  exact hsum.congr_fun
    (fun u _ => (reverseBessel_integrand_expand n x u).symm)
    measurableSet_Ioi

/-- The positive integral representation in particular certifies `B_n(x) > 0` for `x ≥ 0`. -/
theorem reverseBesselPoly_pos (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < reverseBesselPoly n x := by
  unfold reverseBesselPoly
  have hnonneg : ∀ j ∈ Finset.range (n + 1),
      0 ≤ (squaredRadialJetWeight n j : ℝ) * x ^ j := by
    intro j _
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
  have hzero : (0 : ℕ) ∈ Finset.range (n + 1) := by simp
  have hle : (squaredRadialJetWeight n 0 : ℝ) * x ^ 0 ≤
      ∑ j ∈ Finset.range (n + 1), (squaredRadialJetWeight n j : ℝ) * x ^ j :=
    Finset.single_le_sum hnonneg hzero
  have hw : 0 < (squaredRadialJetWeight n 0 : ℝ) * x ^ 0 := by
    simpa using weight_zero_pos n
  exact hw.trans_le hle

end

end RHTower
