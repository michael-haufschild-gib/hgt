import GaloisForLFunctions.HagedornBootstrap.LetterCounting
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Hagedorn pole and time-ordered perturbation theory

**The pole.** Below the free Hagedorn point the letter function satisfies `0 ≤ z(y) < 1`, so the
words (ordered strings of letters) have the convergent generating function `Σ z^m = 1/(1 − z)`;
at and above `y_H` the series diverges. The confined free energy `−log(1 − z(y))` of the winding
mode `n = 1` blows up as `y ↑ y_H`: the Hagedorn temperature is a genuine singularity of the
confined phase.

**Divided differences.** In time-ordered perturbation theory the Euclidean time integrals turn
Boltzmann factors into divided differences:
`∫₀^β e^{−(β−τ)a} e^{−τb} dτ = (e^{−βa} − e^{−βb})/(b − a)` for `a ≠ b`, and `β e^{−βa}` for
degenerate intermediate states. The divided difference tends to `β e^{−βa}` as `b → a`; this is
how degenerate levels produce the explicit powers of `β` (the `β⟨h₄⟩` and `β²⟨h₂²⟩_conn/2`
terms of the cumulant expansion).

**Two loops.** The analytic two-loop Hagedorn coefficient
`(1/T_H⁽⁰⁾)(−86/√3 + 24 ln 12/ln(2 + √3))` equals `−(172/√3) ln(2 + √3) + 48 ln 12`: its
logarithm `ln(2 + √3)` is half the free inverse Hagedorn temperature.
-/

noncomputable section

open Real Filter Topology

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### The Hagedorn pole -/

theorem singleLetterZ_nonneg {y : ℝ} (h1 : y < 1) : 0 ≤ singleLetterZ y := by
  unfold singleLetterZ
  have : 0 < (1 - y) ^ 3 := pow_pos (by linarith) 3
  have : 0 ≤ 3 - y := by linarith
  positivity

/-- **Open words below the Hagedorn point:** `Σ_m z(y)^m = 1/(1 − z(y))`. -/
theorem hasSum_words {y : ℝ} (h0 : 0 ≤ y) (hy : y < hagedornY) :
    HasSum (fun m : ℕ => singleLetterZ y ^ m) (1 - singleLetterZ y)⁻¹ := by
  have h1 : y < 1 := hy.trans hagedornY_lt_one
  apply hasSum_geometric_of_lt_one (singleLetterZ_nonneg h1)
  exact (singleLetterZ_lt_one_iff h0 h1).mpr hy

/-- **At and above the Hagedorn point the word series diverges.** -/
theorem not_summable_words {y : ℝ} (hy : hagedornY ≤ y) (h1 : y < 1) :
    ¬ Summable (fun m : ℕ => singleLetterZ y ^ m) := by
  intro hs
  have h0 : 0 ≤ y := hagedornY_pos.le.trans hy
  have hz : 1 ≤ singleLetterZ y := by
    have := (singleLetterZ_lt_one_iff h0 h1).not.mpr (not_lt.mpr hy)
    linarith [not_lt.mp this]
  have ht := hs.tendsto_atTop_zero
  have hge : ∀ m : ℕ, 1 ≤ singleLetterZ y ^ m := fun m => one_le_pow₀ hz
  have := ge_of_tendsto' ht hge
  norm_num at this

theorem continuous_singleLetterZ_at {y : ℝ} (hy : y ≠ 1) : ContinuousAt singleLetterZ y :=
  (hasDerivAt_singleLetterZ hy).continuousAt

/-- **The confined free energy of the winding mode diverges at the Hagedorn point.** -/
theorem tendsto_confined_freeEnergy :
    Tendsto (fun y => -Real.log (1 - singleLetterZ y)) (𝓝[<] hagedornY) atTop := by
  have hcont : ContinuousAt (fun y => 1 - singleLetterZ y) hagedornY :=
    continuousAt_const.sub (continuous_singleLetterZ_at hagedornY_lt_one.ne)
  have hlim : Tendsto (fun y => 1 - singleLetterZ y) (𝓝[<] hagedornY) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio hagedornY))
      rwa [singleLetterZ_hagedornY, sub_self] at this
    · filter_upwards [Ioo_mem_nhdsLT hagedornY_pos] with y hy
      have := (singleLetterZ_lt_one_iff hy.1.le (hy.2.trans hagedornY_lt_one)).mpr hy.2
      simp only [Set.mem_Ioi]; linarith
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hlim)

/-! ### Divided differences of Boltzmann factors -/

/-- `∫₀^β e^{cτ} dτ = (e^{cβ} − 1)/c`. -/
theorem integral_exp_mul_of_ne {c : ℝ} (hc : c ≠ 0) (β : ℝ) :
    ∫ τ in (0 : ℝ)..β, Real.exp (c * τ) = (Real.exp (c * β) - 1) / c := by
  have hd : ∀ τ ∈ Set.uIcc (0 : ℝ) β, HasDerivAt (fun τ => Real.exp (c * τ) / c) (Real.exp (c * τ)) τ := by
    intro τ _
    have := ((hasDerivAt_id τ).const_mul c).exp.div_const c
    refine this.congr_deriv ?_
    simp only [id]; field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun τ => Real.exp (c * τ)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  ring

/-- **Duhamel kernel, non-degenerate:** `∫₀^β e^{−(β−τ)a} e^{−τb} dτ = (e^{−βa} − e^{−βb})/(b − a)`. -/
theorem duhamel_kernel {a b : ℝ} (hab : a ≠ b) (β : ℝ) :
    ∫ τ in (0 : ℝ)..β, Real.exp (-((β - τ) * a)) * Real.exp (-(τ * b)) =
      (Real.exp (-(β * a)) - Real.exp (-(β * b))) / (b - a) := by
  have hc : a - b ≠ 0 := sub_ne_zero.mpr hab
  have e : (fun τ => Real.exp (-((β - τ) * a)) * Real.exp (-(τ * b))) =
      fun τ => Real.exp (-(β * a)) * Real.exp ((a - b) * τ) := by
    funext τ; rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [e, intervalIntegral.integral_const_mul, integral_exp_mul_of_ne hc]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  rw [mul_div_assoc', mul_sub, ← Real.exp_add, show -(β * a) + (a - b) * β = -(β * b) by ring, mul_one]
  field_simp
  ring

/-- **Duhamel kernel, degenerate:** `∫₀^β e^{−(β−τ)a} e^{−τa} dτ = β e^{−βa}`. -/
theorem duhamel_kernel_degenerate (a β : ℝ) :
    ∫ τ in (0 : ℝ)..β, Real.exp (-((β - τ) * a)) * Real.exp (-(τ * a)) = β * Real.exp (-(β * a)) := by
  have e : (fun τ => Real.exp (-((β - τ) * a)) * Real.exp (-(τ * a))) = fun _ => Real.exp (-(β * a)) := by
    funext τ; rw [← Real.exp_add]; congr 1; ring
  rw [e, intervalIntegral.integral_const, smul_eq_mul, sub_zero]

/-- **Degenerate levels give a power of `β`:** the divided difference tends to `β e^{−βa}`. -/
theorem tendsto_duhamel_divided_difference (a β : ℝ) :
    Tendsto (fun b => (Real.exp (-(β * a)) - Real.exp (-(β * b))) / (b - a)) (𝓝[≠] a)
      (𝓝 (β * Real.exp (-(β * a)))) := by
  have hd : HasDerivAt (fun E => Real.exp (-(β * E))) (Real.exp (-(β * a)) * -β) a := by
    have := (((hasDerivAt_id a).const_mul β).neg).exp
    refine this.congr_deriv ?_
    simp
  have hs := hd.tendsto_slope
  have e : (fun b => (Real.exp (-(β * a)) - Real.exp (-(β * b))) / (b - a)) =
      fun b => -(slope (fun E => Real.exp (-(β * E))) a b) := by
    funext b; rw [slope_def_field]; ring
  rw [e, show β * Real.exp (-(β * a)) = -(Real.exp (-(β * a)) * -β) by ring]
  exact hs.neg

/-! ### The two-loop coefficient -/

/-- The two-loop Hagedorn coefficient in terms of the unit `2 + √3`. -/
theorem twoLoop_coefficient :
    hagedornBeta * (-86 / Real.sqrt 3 + 24 * Real.log 12 / Real.log (2 + Real.sqrt 3)) =
      -(172 / Real.sqrt 3) * Real.log (2 + Real.sqrt 3) + 48 * Real.log 12 := by
  rw [hagedornBeta_eq]
  have hpos : 0 < Real.log (2 + Real.sqrt 3) := Real.log_pos (by linarith [Real.sqrt_nonneg 3])
  field_simp
  ring

end GaloisForLFunctions.HagedornBootstrap
