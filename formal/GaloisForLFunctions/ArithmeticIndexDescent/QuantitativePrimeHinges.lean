import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewGrowthBound
import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpSelfRateOne

/-!
# Quantitative prime hinges

The explicit Chebyshev error transfers through the existing Abel kernel to a
explicit square-root logarithmic decay rate for the integrated prime source.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Set MeasureTheory
open RHTower
open GaloisForLFunctions.RHTower
namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- The integrated prime source has an explicit classical decay exponent. -/
theorem exists_screwPrimeSum_explicit_classical_rate :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ t : ℝ in atTop,
      |screwPrimeSum t - 4 * Real.exp (t / 2)| ≤
        M * Real.exp (t / 2 - (1 / 1920000 : ℝ) * Real.sqrt t) := by
  let c : ℝ := 1 / 960000
  have hc : 0 < c := by norm_num [c]
  obtain ⟨B, hB, hrateRaw⟩ :=
    Sieve.exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate
  have hrateEv : ∀ᶠ x : ℝ in atTop,
      |suzukiChebyshevError x| ≤ B * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    filter_upwards [hrateRaw] with x hx
    have he : -c * Real.sqrt (Real.log x) = -(Real.sqrt (Real.log x) / 960000) := by
      dsimp only [c]
      ring
    rw [suzukiChebyshevError, Chebyshev.psi_eq_sum_range, he]
    exact hx
  obtain ⟨D, hD, hlinear⟩ := exists_abs_suzukiChebyshevError_le_linear
  obtain ⟨x₀, hx₀all⟩ :=
    (hrateEv.and (eventually_ge_atTop (1 : ℝ))).exists_forall_of_atTop
  have hx₀ : 1 ≤ x₀ := (hx₀all x₀ le_rfl).2
  have hx₀pos : 0 < x₀ := zero_lt_one.trans_le hx₀
  let K : ℝ := Real.sqrt 2 * (5 + |Real.log 2|)
  have hK : 0 < K := by dsimp only [K]; positivity
  let M : ℝ := (8 * D + 4 * B) + 8 * K
  have hM : 0 < M := by
    dsimp only [M]
    positivity
  refine ⟨M, hM, ?_⟩
  have hc_rate : c / 2 = (1 / 1920000 : ℝ) := by norm_num [c]
  rw [← hc_rate]
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    eventually_ge_atTop (2 * Real.log 2),
    eventually_ge_atTop (2 * Real.log x₀),
    eventually_ge_atTop (16 * c ^ (2 : ℕ))] with t ht0 ht2raw htx₀ habsorb
  have ht2 : Real.log 2 ≤ t / 2 := by linarith only [ht2raw]
  have hthreshold : x₀ ≤ Real.exp (t / 2) := by
    rw [← Real.exp_log hx₀pos]
    exact Real.exp_le_exp.mpr (by linarith only [htx₀])
  have herr := abs_suzukiPrimeErrorIntegral_le hc hB hD.le hlinear
    (fun x hx => (hx₀all x hx).1) ht0 ht2 hthreshold habsorb
  have hdecomp := screwPrimeSum_eq_main_add_error (by linarith only [ht2raw, ht0] : Real.log 2 ≤ t)
  have hcorr :
      |Real.sqrt 2 * (4 + t - Real.log 2)| ≤ K * (t + 1) := by
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc
      |Real.sqrt 2 * (4 + t - Real.log 2)| =
          Real.sqrt 2 * |4 + t - Real.log 2| := by
        rw [abs_mul, abs_of_nonneg hs2]
      _ ≤ Real.sqrt 2 * (4 + t + |Real.log 2|) := by
        gcongr
        calc
          |4 + t - Real.log 2| ≤ |4 + t| + |Real.log 2| := abs_sub _ _
          _ = 4 + t + |Real.log 2| := by rw [abs_of_nonneg (by linarith only [ht0])]
      _ ≤ K * (t + 1) := by
        dsimp only [K]
        have hinside : 4 + t + |Real.log 2| ≤
            (5 + |Real.log 2|) * (t + 1) := by
          have hprod := mul_nonneg (abs_nonneg (Real.log 2)) ht0
          nlinarith only [ht0, hprod]
        calc
          Real.sqrt 2 * (4 + t + |Real.log 2|) ≤
              Real.sqrt 2 * ((5 + |Real.log 2|) * (t + 1)) :=
            mul_le_mul_of_nonneg_left hinside hs2
          _ = Real.sqrt 2 * (5 + |Real.log 2|) * (t + 1) := by ring
  have hpoly : t + 1 ≤ 8 * Real.exp (t / 8) := by
    have h := Real.add_one_le_exp (t / 8)
    nlinarith only [h]
  have hsqrtAbsorb : (c / 2) * Real.sqrt t ≤ t / 8 := by
    have h4c : 4 * c ≤ Real.sqrt t := by
      rw [Real.le_sqrt (by positivity) ht0]
      nlinarith only [habsorb]
    have hmul := mul_le_mul_of_nonneg_right h4c (Real.sqrt_nonneg t)
    rw [← pow_two, Real.sq_sqrt ht0] at hmul
    calc
      (c / 2) * Real.sqrt t = (4 * c * Real.sqrt t) / 8 := by ring
      _ ≤ t / 8 := div_le_div_of_nonneg_right hmul (by norm_num)
  have hcorrFinal :
      |Real.sqrt 2 * (4 + t - Real.log 2)| ≤
        8 * K * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
    calc
      |Real.sqrt 2 * (4 + t - Real.log 2)| ≤ K * (t + 1) := hcorr
      _ ≤ K * (8 * Real.exp (t / 8)) := mul_le_mul_of_nonneg_left hpoly hK.le
      _ = 8 * K * Real.exp (t / 8) := by ring
      _ ≤ 8 * K * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (by linarith only [hsqrtAbsorb, ht0])) (by positivity)
  rw [hdecomp]
  have hrewrite :
      (4 * Real.exp (t / 2) - Real.sqrt 2 * (4 + t - Real.log 2) +
          ∫ x : ℝ in Ioc 2 (Real.exp t),
            suzukiPrimeAbelKernel t x * suzukiChebyshevError x) -
          4 * Real.exp (t / 2) =
        (∫ x : ℝ in Ioc 2 (Real.exp t),
            suzukiPrimeAbelKernel t x * suzukiChebyshevError x) -
          Real.sqrt 2 * (4 + t - Real.log 2) := by ring
  rw [hrewrite]
  calc
    |(∫ x : ℝ in Ioc 2 (Real.exp t),
        suzukiPrimeAbelKernel t x * suzukiChebyshevError x) -
          Real.sqrt 2 * (4 + t - Real.log 2)| ≤
      |∫ x : ℝ in Ioc 2 (Real.exp t),
        suzukiPrimeAbelKernel t x * suzukiChebyshevError x| +
          |Real.sqrt 2 * (4 + t - Real.log 2)| := abs_sub _ _
    _ ≤ (8 * D + 4 * B) * Real.exp (t / 2 - (c / 2) * Real.sqrt t) +
        8 * K * Real.exp (t / 2 - (c / 2) * Real.sqrt t) :=
      add_le_add herr hcorrFinal
    _ = M * Real.exp (t / 2 - (c / 2) * Real.sqrt t) := by
      dsimp only [M]
      ring

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_screwPrimeSum_explicit_classical_rate
