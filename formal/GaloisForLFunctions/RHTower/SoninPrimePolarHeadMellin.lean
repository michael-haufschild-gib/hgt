import GaloisForLFunctions.RHTower.SoninPrimePolarCofinalGroundEnergy
import GaloisForLFunctions.RHTower.SoninDampedPrimePolarCurrent

/-!
# Head Mellin image of the unchanged prime–polar source

The physical head Mellin functional is continuous throughout `Re s > 1/2`.
It takes every original ground atom and polar cell to its literal scalar
Mellin term. Cofinal source admission therefore gives a holomorphic scalar
primitive with those exact finite arithmetic approximants.

The finite native energy is an explicit hypothesis, not a conclusion.
-/

noncomputable section

open MeasureTheory Set Filter Complex Topology
open scoped BigOperators

namespace RHTower

/-- The ground cutoff is the original interval indicator. -/
theorem soninCutoffMonomial_zero_eq_bandIndicator (a : ℝ) :
    soninCutoffMonomial a 0 = bandIndicator a := by
  apply Lp.ext
  filter_upwards [soninCutoffMonomial_ae a 0, bandIndicator_coeFn a] with x hx hy
  rw [hx, hy]
  simp

/-- Exact Mellin primitive of an entering ground interval. -/
theorem soninHeadMellin_soninGroundEntry {u : ℝ} (hu : 0 ≤ u)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    s * soninHeadMellin (soninGroundEntry 1 u) s = Complex.exp (-s * u) := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, zero_re] at hs
    linarith
  have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  rw [soninGroundEntry, soninCutoffMonomial_zero_eq_bandIndicator,
    ← soninHeadMellinCLM_apply s hs, map_smul, soninHeadMellinCLM_apply,
    soninHeadMellin_dilated_bandIndicator u hs, min_eq_right he]
  have hscale : (Real.exp (-u / 2) : ℂ) * (Real.exp (u / 2) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      show -u / 2 + u / 2 = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  have hpow : ((Real.exp (-u) : ℝ) : ℂ) ^ s = Complex.exp (-s * u) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    congr 1
    push_cast
    ring
  simp only [smul_eq_mul]
  rw [hpow]
  calc
    _ = ((Real.exp (-u / 2) : ℂ) * (Real.exp (u / 2) : ℂ)) *
        (s * (Complex.exp (-s * u) / s)) := by ring
    _ = _ := by rw [hscale, one_mul]; field_simp

/-- Literal scalar prime–polar cell assembly, including the original polar density. -/
def soninPrimePolarHeadScalar (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1),
    ((if (n + 2).Prime then Complex.exp (-s * Real.log (n + 2 : ℝ)) else 0) -
      ∫ u in Icc (Real.log (n + 2 : ℝ)) (Real.log (n + 3 : ℝ)),
        (((Real.exp u + 1) / u : ℝ) : ℂ) * Complex.exp (-s * u))

/-- Every original strong polar integral has its literal scalar Mellin image. -/
theorem soninHeadMellin_polarGroundCell {b R : ℝ} (hb : 0 < b)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    s * soninHeadMellin
      (∫ u in Icc b R,
        soninLogPolarDensity u • rayDilate (Real.exp u) (soninCutoffMonomial 1 0)) s =
      ∫ u in Icc b R, (((Real.exp u + 1) / u : ℝ) : ℂ) * Complex.exp (-s * u) := by
  have hd : ContinuousOn (fun u : ℝ => (((Real.exp u + 1) / u : ℝ) : ℂ)) (Icc b R) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hb.trans_le hu.1)
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hi := (hd.smul (continuous_soninGroundEntry 1).continuousOn).integrableOn_Icc
    (μ := volume)
  change IntegrableOn (fun u : ℝ => (((Real.exp u + 1) / u : ℝ) : ℂ) •
    soninGroundEntry 1 u) (Icc b R) volume at hi
  simp_rw [soninGroundEntry_polar_density]
  rw [← soninHeadMellinCLM_apply s hs,
    ← (soninHeadMellinCLM s hs).integral_comp_comm hi, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  rw [map_smul, soninHeadMellinCLM_apply, smul_eq_mul, mul_left_comm,
    soninHeadMellin_soninGroundEntry (hb.le.trans hu.1) hs]

/-- Exact finite arithmetic identity; no infinite-source exchange is used. -/
theorem soninHeadMellin_primePolarCellSource (N : ℕ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    s * soninHeadMellin (soninPrimePolarCellSource 1 N) s =
      soninPrimePolarHeadScalar N s := by
  rw [soninPrimePolarCellSource, ← soninHeadMellinCLM_apply s hs, map_sum,
    Finset.mul_sum, soninPrimePolarHeadScalar]
  apply Finset.sum_congr rfl
  intro n hn
  have hnlog : 0 < Real.log (n + 2 : ℝ) :=
    Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [map_sub, mul_sub]
  simp_rw [soninHeadMellinCLM_apply]
  rw [soninHeadMellin_polarGroundCell hnlog hs]
  congr 1
  by_cases hp : (n + 2).Prime
  · simp only [hp, if_true, soninHeadMellin_soninGroundEntry hnlog.le hs]
  · simp only [hp, if_false]
    rw [← soninHeadMellinCLM_apply s hs, map_zero, mul_zero]

/-- Holomorphic primitive on the physical half-plane, without a spectral denominator. -/
def soninSourceMellinPrimitive (f : SoninL2) (s : ℂ) : ℂ :=
  s * soninHeadMellin f s

theorem analyticOnNhd_soninSourceMellinPrimitive (f : SoninL2) :
    AnalyticOnNhd ℂ (soninSourceMellinPrimitive f) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  exact analyticAt_id.mul (analyticOnNhd_soninHeadMellin f s hs)

/-- The native Hilbert norm controls the primitive at every strict-right point. -/
theorem norm_soninSourceMellinPrimitive_le (f : SoninL2) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    ‖soninSourceMellinPrimitive f s‖ ≤ ‖s‖ * ‖soninHeadMellinCLM s hs‖ * ‖f‖ := by
  rw [soninSourceMellinPrimitive, norm_mul, ← soninHeadMellinCLM_apply s hs]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left ((soninHeadMellinCLM s hs).le_opNorm f) (norm_nonneg s)

/-- Strong source limits retain the entire finite arithmetic identity pointwise. -/
theorem soninPrimePolarHeadScalar_tendsto_of_source_limit
    {φ : ℕ → ℕ} {f : SoninL2}
    (hf : Tendsto (fun k => soninPrimePolarCellSource 1 (φ k)) atTop (𝓝 f))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (fun k => soninPrimePolarHeadScalar (φ k) s) atTop
      (𝓝 (soninSourceMellinPrimitive f s)) := by
  have hM := (soninHeadMellinCLM s hs).continuous.tendsto f
  have h := (show Tendsto (fun _ : ℕ => s) atTop (𝓝 s) from
    tendsto_const_nhds).mul (hM.comp hf)
  simpa only [Function.comp_apply, soninHeadMellinCLM_apply,
    soninHeadMellin_primePolarCellSource _ hs, soninSourceMellinPrimitive] using h

/-- Finite native energy produces a holomorphic primitive of the exact scalar cell assemblies. -/
theorem exists_soninSourceMellinPrimitive_of_energy
    (hE : Summable soninPrimePolarGridEnergy) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ ∃ f : SoninL2,
      AnalyticOnNhd ℂ (soninSourceMellinPrimitive f) {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 / 2 < s.re →
        Tendsto (fun k => soninPrimePolarHeadScalar (φ k) s) atTop
          (𝓝 (soninSourceMellinPrimitive f s)) := by
  obtain ⟨φ, hφ, f, hf⟩ :=
    (soninPrimePolarCellSource_cofinal_limit_iff_energy 1 (by norm_num)).mpr hE
  exact ⟨φ, hφ, f, analyticOnNhd_soninSourceMellinPrimitive f,
    fun _ hs => soninPrimePolarHeadScalar_tendsto_of_source_limit hf hs⟩

end RHTower
