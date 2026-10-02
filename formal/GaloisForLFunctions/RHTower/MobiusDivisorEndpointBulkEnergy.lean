import GaloisForLFunctions.RHTower.MobiusDivisorUniformLocalRegularity
import GaloisForLFunctions.RHTower.MobiusDivisorDilationMean

/-!
# A literal endpoint forces bulk physical energy

Uniform local source regularity propagates a negative endpoint onto an
interval ending at that same cutoff. The admitted whole-ray diagonal mean
therefore dominates a cubic function of the endpoint. No positivity of a
Mobius correlation or growing-core estimate is assumed.
-/

noncomputable section
open MeasureTheory Set Finset Filter
namespace RHTower

/-- The physical energy forced by a negative endpoint, uniformly over finite cores. -/
theorem mobiusDivisorDilationMean_endpoint_lower (P : Finset ℕ) (N : ℕ)
    (hN : 2 ≤ N) {B : ℝ} (hB : 0 < B)
    (hhead : mobiusDivisorContinuousHead P N ≤ -B) :
    B^3 / (192 * Real.sqrt N * (N : ℝ)^3) ≤ mobiusDivisorDilationMean P 1 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hsize : B ≤ 24 * Real.sqrt N * N := by
    have h := abs_mobiusDivisorContinuousHead_sub_le P N
      (x := N) (y := 0) le_rfl hN0.le
    rw [mobiusDivisorContinuousHead_eq_zero P (by norm_num : (0 : ℝ) ≤ 1),
      sub_zero, sub_zero, abs_of_nonneg hN0.le] at h
    exact (by linarith [neg_le_abs (mobiusDivisorContinuousHead P N)] :
      B ≤ |mobiusDivisorContinuousHead P N|).trans h
  let δ := B / (48 * Real.sqrt N)
  let a := (N : ℝ) - δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδN : δ ≤ (N : ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 48 * Real.sqrt (N : ℝ))).mpr
    nlinarith only [hsize]
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have haN : a ≤ (N : ℝ) := by dsimp [a]; linarith
  have hset : Ioc a (N : ℝ) ⊆ Ioi (1 : ℝ) := by
    intro x hx
    exact ha1.trans_lt hx.1
  have hlocal : ∀ x ∈ Ioc a (N : ℝ), mobiusDivisorContinuousHead P x ≤ -B/2 := by
    intro x hx
    have hd : |x-(N : ℝ)| ≤ δ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
      dsimp [a] at hx
      linarith [hx.1]
    have h := abs_mobiusDivisorContinuousHead_sub_le P N hx.2 le_rfl
    have hscale : 24 * Real.sqrt N * δ = B/2 := by
      dsimp [δ]
      field_simp
      ring
    have hh := h.trans (mul_le_mul_of_nonneg_left hd (by positivity))
    rw [hscale] at hh
    have := (abs_le.mp hh).2
    linarith
  let f : ℝ → ℝ := fun x => (mobiusDivisorContinuousHead P x)^2/x^3
  let K : ℝ := B^2/(4*(N : ℝ)^3)
  have hint : IntegrableOn f (Ioi (1 : ℝ)) := by
    simpa only [f, one_mul, pow_two] using
      integrable_mobiusDivisorDilationMean_kernel P (by norm_num : (0 : ℝ) < 1)
  have hpt : ∀ x ∈ Ioc a (N : ℝ), K ≤ f x := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans (hset hx)
    have hh := hlocal x hx
    have hsq : (B/2)^2 ≤ (mobiusDivisorContinuousHead P x)^2 := by
      have hh' : B/2 ≤ -mobiusDivisorContinuousHead P x := by linarith only [hh]
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ B/2) hh' 2
      nlinarith only [hp]
    have hden : x^3 ≤ (N : ℝ)^3 := pow_le_pow_left₀ hx0.le hx.2 3
    have hmul := mul_le_mul hsq hden (pow_nonneg hx0.le 3)
      (sq_nonneg (mobiusDivisorContinuousHead P x))
    dsimp [K, f]
    apply (div_le_div_iff₀ (by positivity : 0 < 4*(N : ℝ)^3) (pow_pos hx0 3)).mpr
    nlinarith only [hmul]
  have hmono : K*((N : ℝ)-a) ≤ ∫ x in Ioc a (N : ℝ), f x := by
    have hconst : IntegrableOn (fun _ : ℝ => K) (Ioc a (N : ℝ)) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hm := setIntegral_mono_on hconst (hint.mono_set hset) measurableSet_Ioc hpt
    have hvol : (volume : Measure ℝ).real (Ioc a (N : ℝ)) = (N : ℝ)-a := by
      simp [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal, sub_nonneg.mpr haN]
    simpa only [setIntegral_const, smul_eq_mul, hvol, mul_comm] using hm
  have hmass : (∫ x in Ioc a (N : ℝ), f x) ≤ ∫ x in Ioi (1 : ℝ), f x := by
    refine setIntegral_mono_set hint ?_ (Eventually.of_forall (fun x hx => hset hx))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans hx.le) 3)
  have heq : K*((N : ℝ)-a) = B^3 / (192 * Real.sqrt N * (N : ℝ)^3) := by
    dsimp [K, a, δ]
    field_simp
    ring
  rw [heq] at hmono
  exact hmono.trans (by simpa [mobiusDivisorDilationMean, f, one_mul, pow_two] using hmass)

end RHTower
