import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDensityFormula
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeCone

/-!
# The completed source of the rational hard-edge test in density coordinates

The square of the rational hard-edge test is a finite combination of mass kernels,

`g_{a,p}(x)² = a²·∑_{k≥1} W_k (a² + x²)^{-k}`,   `W = X·p²`,

so the density form of the Euler-ray response transfers to it term by term.  The result is the
completed source formula

`∑_q g_{a,p}(α_q)² = 2·P(a,p) + (1/pi)·∫ g² theta − (1/pi)·∑_m Λ(m) m^{-1/2}·ĝ²(log m)`

with a nonnegative polar value `P(a,p) = a²·W((a² − 1/4)^{-1})`, the archimedean rate `theta`, and
the honest Fourier transform of `g²` in the prime term.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The mass-kernel expansion of the squared test -/

theorem eval_routeUHardEdgeWeilPoly_eq_sum (p : Polynomial ℝ) (u : ℝ) :
    (routeUHardEdgeWeilPoly p).eval u
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          (routeUHardEdgeWeilPoly p).coeff k * u ^ k := by
  rw [Polynomial.eval_eq_sum_range, Finset.range_eq_Ico,
    show Finset.Ico 0 ((routeUHardEdgeWeilPoly p).natDegree + 1)
        = insert 0 (Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree) by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]
      omega,
    Finset.sum_insert (by simp), routeUHardEdgeWeilPoly_coeff_zero]
  simp

theorem eval_routeUHardEdgeWeilPoly (p : Polynomial ℝ) (u : ℝ) :
    (routeUHardEdgeWeilPoly p).eval u = u * p.eval u ^ (2 : ℕ) := by
  rw [routeUHardEdgeWeilPoly]
  simp

theorem routeUHardEdgeRationalTest_sq_eq_sum {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) (x : ℝ) :
    routeUHardEdgeRationalTest a p x ^ (2 : ℕ)
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          (a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k) * (((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ k)⁻¹) := by
  have hpos : (0 : ℝ) < a ^ (2 : ℕ) + x ^ (2 : ℕ) := by positivity
  rw [routeUHardEdgeRationalTest_sq_eq ha p x, mul_assoc, ← eval_routeUHardEdgeWeilPoly p,
    eval_routeUHardEdgeWeilPoly_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inv_pow]
  ring

/-! ## The polar value -/

/-- The polar value of the squared rational hard-edge test. -/
def routeUHardEdgePolar (a : ℝ) (p : Polynomial ℝ) : ℝ :=
  a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).eval ((a ^ (2 : ℕ) - 1 / 4)⁻¹)

theorem routeUHardEdgePolar_nonneg {a : ℝ} (ha : 1 / 2 < a) (p : Polynomial ℝ) :
    0 ≤ routeUHardEdgePolar a p := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hpos : (0 : ℝ) < a ^ (2 : ℕ) - 1 / 4 := by nlinarith
  rw [routeUHardEdgePolar, eval_routeUHardEdgeWeilPoly]
  have hinv : (0 : ℝ) < (a ^ (2 : ℕ) - 1 / 4)⁻¹ := inv_pos.mpr hpos
  positivity

theorem routeUHardEdgePolar_eq_sum (a : ℝ) (p : Polynomial ℝ) :
    routeUHardEdgePolar a p
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          (a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k) * (((a ^ (2 : ℕ) - 1 / 4) ^ k)⁻¹) := by
  rw [routeUHardEdgePolar, eval_routeUHardEdgeWeilPoly_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inv_pow]
  ring


/-! ## Integrability of the density terms -/

theorem integrable_of_integrable_ofReal {f : ℝ → ℝ}
    (h : Integrable fun x : ℝ => ((f x : ℝ) : ℂ)) : Integrable f := by
  have h2 := Complex.reCLM.integrable_comp h
  simpa using h2

theorem integrable_routeUArchimedeanWeight_massKernel {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable fun x : ℝ =>
      routeUArchimedeanWeight x * ((((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (n + 1) : ℝ)) : ℂ)⁻¹ :=
  integrable_logWeight_mul_massKernel continuous_routeUArchimedeanWeight
    norm_routeUArchimedeanWeight_le n (by positivity)

theorem integrable_routeUArchimedeanRate_massKernel {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable fun x : ℝ => routeUArchimedeanRate x * (((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ (n + 1))⁻¹) := by
  refine integrable_of_integrable_ofReal ?_
  refine (integrable_routeUArchimedeanWeight_massKernel ha n).congr ?_
  filter_upwards with x
  simp only [routeUArchimedeanWeight]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]

theorem integrable_routeUArchimedeanRate_mul_testSq {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) :
    Integrable fun x : ℝ => routeUArchimedeanRate x * routeUHardEdgeRationalTest a p x ^ (2 : ℕ) := by
  have hsum : Integrable fun x : ℝ =>
      ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
        (a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k)
          * (routeUArchimedeanRate x * (((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ k)⁻¹)) := by
    refine integrable_finsetSum _ fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
    exact (integrable_routeUArchimedeanRate_massKernel ha j).const_mul _
  refine hsum.congr ?_
  filter_upwards with x
  rw [routeUHardEdgeRationalTest_sq_eq_sum ha p x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## The archimedean and prime terms as finite sums of moments -/

theorem integral_routeUArchimedeanRate_mul_testSq {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) :
    ((∫ x : ℝ, routeUArchimedeanRate x * routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          ((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
            * routeUArchimedeanMoment (k - 1) (a ^ (2 : ℕ)) := by
  have hcast : ((∫ x : ℝ, routeUArchimedeanRate x
        * routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ)
      = ∫ x : ℝ, ((routeUArchimedeanRate x
          * routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ) :=
    (_root_.integral_ofReal).symm
  rw [hcast]
  have hcongr : ∀ x : ℝ, ((routeUArchimedeanRate x
        * routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ)
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          ((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
            * (routeUArchimedeanWeight x * ((((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ k : ℝ)) : ℂ)⁻¹) := by
    intro x
    rw [routeUHardEdgeRationalTest_sq_eq_sum ha p x]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [routeUArchimedeanWeight]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [MeasureTheory.integral_const_mul, routeUArchimedeanMoment, massPairing,
      show k - 1 + 1 = k by omega]
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
    exact (integrable_routeUArchimedeanWeight_massKernel ha j).const_mul _

theorem routeUHardEdgeFourierSq_eq_massPairing_sum {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ)
    (L : ℝ) :
    routeUHardEdgeFourierSq a p L
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          ((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
            * massPairing (cauchyFourierWeight L) (k - 1) (a ^ (2 : ℕ)) := by
  have hcongr : ∀ x : ℝ, ((routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ)
        * Complex.exp (((-(L * x) : ℝ) : ℂ) * Complex.I)
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          ((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
            * (cauchyFourierWeight L x * ((((a ^ (2 : ℕ) + x ^ (2 : ℕ)) ^ k : ℝ)) : ℂ)⁻¹) := by
    intro x
    rw [routeUHardEdgeRationalTest_sq_eq_sum ha p x]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cauchyFourierWeight]
    push_cast
    ring
  rw [routeUHardEdgeFourierSq, MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall hcongr), MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [MeasureTheory.integral_const_mul, massPairing, show k - 1 + 1 = k by omega]
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
    exact ((integrable_logWeight_mul_massKernel (continuous_cauchyFourierWeight L)
      (cauchyFourierWeight_bound L) j (by positivity)).const_mul _)


theorem tsum_routeUPrimeFourier_eq_sum {a : ℝ} (ha : 1 / 2 < a) (p : Polynomial ℝ) :
    (∑' m : ℕ, ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)
        * routeUHardEdgeFourierSq a p (Real.log m))
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          ((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
            * routeUPrimeMoment (k - 1) (a ^ (2 : ℕ)) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hX : (1 : ℝ) / 4 < a ^ (2 : ℕ) := by nlinarith
  obtain ⟨X₀, hX₀lo, hX₀hi⟩ : ∃ X₀ : ℝ, 1 / 4 < X₀ ∧ X₀ < a ^ (2 : ℕ) :=
    ⟨(1 / 4 + a ^ (2 : ℕ)) / 2, by linarith, by linarith⟩
  obtain ⟨h, hh, hhX⟩ := exists_routeUPrimeAperture hX₀lo
  have hexpand : ∀ m : ℕ, ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)
      * routeUHardEdgeFourierSq a p (Real.log m)
      = ∑ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
          ((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
            * routeUPrimeTerm (k - 1) m (a ^ (2 : ℕ)) := by
    intro m
    rw [routeUHardEdgeFourierSq_eq_massPairing_sum ha0 p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [routeUPrimeTerm]
    ring
  rw [tsum_congr hexpand, Summable.tsum_finsetSum ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [tsum_mul_left, routeUPrimeMoment]
  · intro k _
    exact (summable_routeUPrimeTerm hh hhX (k - 1) hX₀hi).mul_left _

/-- **(CSHC.6) The completed source of the rational hard-edge test in density coordinates.** -/
theorem tsum_routeUHardEdgeRationalTestSq_eq_density {a : ℝ} (ha : 1 / 2 < a) (p : Polynomial ℝ) :
    (∑' q : XiZeroCopy, routeUHardEdgeRationalTestSq a p (xiSpectralPoint q))
      = 2 * ((routeUHardEdgePolar a p : ℝ) : ℂ)
        + (1 / (Real.pi : ℂ)) * ((∫ x : ℝ, routeUArchimedeanRate x
            * routeUHardEdgeRationalTest a p x ^ (2 : ℕ) : ℝ) : ℂ)
        - (1 / (Real.pi : ℂ)) * ∑' m : ℕ,
            ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)
              * routeUHardEdgeFourierSq a p (Real.log m) := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hX : (1 : ℝ) / 4 < a ^ (2 : ℕ) := by nlinarith
  rw [tsum_routeUHardEdgeRationalTestSq_eq_moments a p, Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.Icc 1 (routeUHardEdgeWeilPoly p).natDegree,
      ((a ^ (2 : ℕ) : ℝ) : ℂ) * ((((routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
          * xiResolventMoment (k - 1) (a ^ (2 : ℕ)))
        = ((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
              * (2 * ((((a ^ (2 : ℕ) - 1 / 4) ^ k : ℝ)) : ℂ)⁻¹)
          + (1 / (Real.pi : ℂ)) * (((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
              * routeUArchimedeanMoment (k - 1) (a ^ (2 : ℕ)))
          - (1 / (Real.pi : ℂ)) * (((a ^ (2 : ℕ) * (routeUHardEdgeWeilPoly p).coeff k : ℝ) : ℂ)
              * routeUPrimeMoment (k - 1) (a ^ (2 : ℕ))) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [xiResolventMoment_eq_routeUDensityMoment (k - 1) hX, routeUDensityMoment,
      show k - 1 + 1 = k by omega]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← tsum_routeUPrimeFourier_eq_sum ha p,
    ← integral_routeUArchimedeanRate_mul_testSq ha0 p]
  congr 2
  rw [routeUHardEdgePolar_eq_sum a p]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end RHTower

end
