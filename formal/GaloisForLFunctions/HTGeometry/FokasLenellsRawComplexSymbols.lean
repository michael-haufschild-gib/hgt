import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffComplexLimits

/-!
# The raw complex phase has an exact essential-boundedness gate

Every spectral value is entire in complex time. As actual multiplication
symbols, however, the raw derivative hierarchy belongs to L-infinity exactly
at zeroth order and real time. Any putative essential bound would uniformly
bound all cutoff operators, contradicting their proved norm divergence.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The literal raw complex-time phase and its pointwise derivative hierarchy. -/
def rawComplexSymbol (n : ℕ) (τ : ℂ) (z : ℝ) : ℂ :=
  (-(((2*z)⁻¹ : ℝ) : ℂ) * I)^n * Complex.exp (-τ * (((2*z)⁻¹ : ℝ) : ℂ) * I)

/-- The exact modulus retains both the reciprocal singularity and vertical exponential growth. -/
theorem norm_rawComplexSymbol (n : ℕ) (τ : ℂ) (z : ℝ) :
    ‖rawComplexSymbol n τ z‖ = |(2*z)⁻¹|^n * Real.exp (τ.im * (2*z)⁻¹) := by
  simp [rawComplexSymbol,norm_pow,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

/-- Every actual raw complex derivative symbol is measurable. -/
theorem measurable_rawComplexSymbol (n : ℕ) (τ : ℂ) : Measurable (rawComplexSymbol n τ) := by
  unfold rawComplexSymbol
  fun_prop

/-- At zeroth order and real time, the raw complex symbol is the original singular phase. -/
theorem rawComplexSymbol_zero_ofReal (t z : ℝ) : rawComplexSymbol 0 (t : ℂ) z = phase t z := by
  simp [rawComplexSymbol,phase,div_eq_mul_inv]

/-- Every fixed spectral value is entire in complex time, even though the operator family need not exist. -/
theorem rawComplexSymbol_analyticAt (n : ℕ) (τ : ℂ) (z : ℝ) :
    AnalyticAt ℂ (fun t => rawComplexSymbol n t z) τ := by
  unfold rawComplexSymbol
  fun_prop

/-- The literal pointwise time derivative is the next raw singular symbol. -/
theorem rawComplexSymbol_hasDerivAt (n : ℕ) (τ : ℂ) (z : ℝ) :
    HasDerivAt (fun t => rawComplexSymbol n t z) (rawComplexSymbol (n+1) τ z) τ := by
  have h := (((hasDerivAt_id τ).neg.mul_const ((((2*z)⁻¹ : ℝ) : ℂ))).mul_const I).cexp.const_mul
    ((-(((2*z)⁻¹ : ℝ) : ℂ) * I)^n)
  have he : rawComplexSymbol (n+1) τ z =
      (-(((2*z)⁻¹ : ℝ) : ℂ) * I)^n *
        (Complex.exp (-τ * (((2*z)⁻¹ : ℝ) : ℂ) * I) * (-1 * (((2*z)⁻¹ : ℝ) : ℂ) * I)) := by
    simp only [rawComplexSymbol,pow_succ]
    ring
  rw [he]
  exact h

/-- All pointwise iterated derivatives are the actual raw hierarchy. -/
theorem iteratedDeriv_rawComplexSymbol (n : ℕ) (z : ℝ) :
    iteratedDeriv n (fun τ => rawComplexSymbol 0 τ z) = fun τ => rawComplexSymbol n τ z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun τ => (rawComplexSymbol_hasDerivAt n τ z).deriv

/-- Every cutoff symbol is the actual raw symbol outside the cutoff and its exact frozen value inside. -/
theorem cutoffComplexSymbol_eq_raw_or_frozen (a z : ℝ) (n : ℕ) (τ : ℂ) :
    cutoffComplexSymbol a n τ z =
      if Real.exp a ≤ |z| then rawComplexSymbol n τ z else if n = 0 then 1 else 0 := by
  by_cases hz : z ∈ cutoffPhaseSet a
  · rw [if_pos (show Real.exp a ≤ |z| from hz),cutoffComplexSymbol,cutoffPhaseFrequency,indicator_of_mem hz]
    rfl
  · rw [if_neg (show ¬ Real.exp a ≤ |z| from hz),cutoffComplexSymbol,cutoffPhaseFrequency,indicator_of_notMem hz]
    cases n <;> simp

/-- The complete raw derivative hierarchy is essentially bounded exactly at zeroth order and real time. -/
theorem memLp_rawComplexSymbol_top_iff (n : ℕ) (τ : ℂ) :
    MemLp (rawComplexSymbol n τ) ∞ (volume : Measure ℝ) ↔ n = 0 ∧ τ.im = 0 := by
  constructor
  · intro hf
    let g : Lp ℂ ∞ (volume : Measure ℝ) := hf.toLp (rawComplexSymbol n τ)
    have hb : ∀ᵐ z ∂volume, ‖rawComplexSymbol n τ z‖ ≤ ‖g‖ := by
      have h := ae_le_lpNorm_exponent_top (Lp.memLp g)
      rw [← toReal_eLpNorm (Lp.memLp g).1,← Lp.norm_def] at h
      filter_upwards [h,hf.coeFn_toLp] with z hz he
      rwa [he] at hz
    apply (cutoffComplexOperator_uniform_norm_bound_iff n τ).1
    refine ⟨max ‖g‖ 1,fun a => ?_⟩
    change ‖lineLinftyMultiplier (cutoffComplexLinfty a n τ)‖ ≤ _
    rw [norm_lineLinftyMultiplier,Lp.norm_def,eLpNorm_exponent_top]
    apply ENNReal.toReal_le_of_le_ofReal (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right _ _))
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [cutoffComplexLinfty_ae a n τ,hb] with z hz hbz
    rw [hz,cutoffComplexSymbol_eq_raw_or_frozen]
    split_ifs with hmem hn
    · exact hbz.trans (le_max_left _ _)
    · simpa only [norm_one] using le_max_right ‖g‖ 1
    · simpa only [norm_zero] using le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right ‖g‖ 1)
  · rintro ⟨rfl,hi⟩
    have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he]
    apply memLp_top_of_bound (measurable_rawComplexSymbol 0 (τ.re : ℂ)).aestronglyMeasurable 1
    exact .of_forall fun z => by rw [rawComplexSymbol_zero_ofReal,norm_phase]

/-- Every cutoff derivative converges pointwise to the literal raw symbol, for all complex times. -/
theorem cutoffComplexSymbol_tendsto_raw (n : ℕ) (τ : ℂ) (z : ℝ) :
    Tendsto (fun a => cutoffComplexSymbol a n τ z) atBot (𝓝 (rawComplexSymbol n τ z)) := by
  apply tendsto_const_nhds.congr'
  by_cases hz : z = 0
  · subst z
    apply Eventually.of_forall
    intro a
    change rawComplexSymbol n τ 0 = cutoffComplexSymbol a n τ 0
    have hn : (0:ℝ) ∉ cutoffPhaseSet a := by
      change ¬ Real.exp a ≤ |(0:ℝ)|
      simpa using Real.exp_pos a
    rw [cutoffComplexSymbol_eq_raw_or_frozen,if_neg (show ¬ Real.exp a ≤ |(0:ℝ)| from hn)]
    cases n <;> simp [rawComplexSymbol]
  · filter_upwards [eventually_le_atBot (Real.log |z|)] with a ha
    have hp : 0 < |z| := abs_pos.mpr hz
    have hm : z ∈ cutoffPhaseSet a := by
      change Real.exp a ≤ |z|
      calc
        _ ≤ Real.exp (Real.log |z|) := Real.exp_le_exp.mpr ha
        _ = _ := Real.exp_log hp
    rw [cutoffComplexSymbol_eq_raw_or_frozen,if_pos (show Real.exp a ≤ |z| from hm)]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
