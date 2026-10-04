import GaloisForLFunctions.RHTower.ThetaChronologicalCausalJumps
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import GaloisForLFunctions.HTGeometry.TranslationModulus

/-!
# Singular deconvolution of the cutoff current

For `σ > 0` the finite signed measure `ν_σ = Σ_n μ(n) n^{−1−σ} δ_{−log n}` (constructed through its
Jordan decomposition into two atomic measures) convolves the weighted one-atom current
`φ_σ(y) = e^{σy} φ(y)` into the weighted cutoff current `C_σ(y) = e^{σy} C(y)`.  Convolution by
`φ_σ` is injective on finite signed measures (its Fourier transform `−G(σ+it)` never vanishes), so
`C_σ` determines `ν_σ`, whose atoms return `μ(n) = n^{1+σ} ν_σ({−log n})`, and the causal tail is
the singular readout `B(t) = ∫_{a < −log t} e^{−(σ+1/2)a} k(−a − log t) dν_σ(a)`.  The inverse is
unbounded: adjacent unit dipoles have total variation `2` but `‖λ_n * φ_σ‖₁ → 0`; and
`‖ν_σ‖_TV = ζ(1+σ)/ζ(2+2σ)` with `σ‖ν_σ‖_TV → 1/ζ(2)`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-! ## Atomic measures -/

theorem lintegral_atomicMeasure (c x : ℕ → ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y, g y ∂atomicMeasure c x = ∑' n, ENNReal.ofReal (c n) * g (x n) := by
  rw [atomicMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem integrable_atomicMeasure {E : Type*} [NormedAddCommGroup E] {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n)
    {x : ℕ → ℝ} {f : ℝ → E} (hf : AEStronglyMeasurable f (atomicMeasure c x))
    (hsum : Summable fun n => c n * ‖f (x n)‖) : Integrable f (atomicMeasure c x) := by
  refine ⟨hf, ?_⟩
  rw [HasFiniteIntegral, lintegral_atomicMeasure]
  have h : ∀ n, ENNReal.ofReal (c n) * ‖f (x n)‖ₑ = ENNReal.ofReal (c n * ‖f (x n)‖) := fun n => by
    rw [ENNReal.ofReal_mul (hc n), ofReal_norm]
  simp_rw [h]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hc n) (norm_nonneg _)) hsum]
  exact ENNReal.ofReal_lt_top

theorem integral_atomicMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {x : ℕ → ℝ} {f : ℝ → E}
    (hf : Integrable f (atomicMeasure c x)) :
    ∫ y, f y ∂atomicMeasure c x = ∑' n, c n • f (x n) := by
  rw [atomicMeasure, integral_sum_measure hf]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc n)]

/-! ## The deconvolution measure `ν_σ` -/

/-- `w_σ(n) = μ(n) n^{−1−σ}`. -/
def deconvWeight (σ : ℝ) (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-(1 + σ))

/-- The arithmetic log site `−log n`. -/
def deconvSite (n : ℕ) : ℝ := -Real.log n

/-- The positive part `Σ_n (w_σ(n))⁺ δ_{−log n}`. -/
def deconvPos (σ : ℝ) : Measure ℝ := atomicMeasure (fun n => max (deconvWeight σ n) 0) deconvSite

/-- The negative part `Σ_n (w_σ(n))⁻ δ_{−log n}`. -/
def deconvNeg (σ : ℝ) : Measure ℝ := atomicMeasure (fun n => max (-deconvWeight σ n) 0) deconvSite

theorem deconvWeight_zero (σ : ℝ) : deconvWeight σ 0 = 0 := by simp [deconvWeight]

theorem abs_deconvWeight (σ : ℝ) (n : ℕ) :
    |deconvWeight σ n| = (ArithmeticFunction.moebius n : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + σ)) := by
  rw [deconvWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  congr 1
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

theorem abs_deconvWeight_le (σ : ℝ) (n : ℕ) : |deconvWeight σ n| ≤ (n : ℝ) ^ (-(1 + σ)) := by
  rw [deconvWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc |(ArithmeticFunction.moebius n : ℝ)| * (n : ℝ) ^ (-(1 + σ))
      ≤ 1 * (n : ℝ) ^ (-(1 + σ)) :=
        mul_le_mul_of_nonneg_right hμ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := one_mul _

theorem summable_abs_deconvWeight {σ : ℝ} (hσ : 0 < σ) : Summable fun n => |deconvWeight σ n| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_deconvWeight_le σ)
    (Real.summable_nat_rpow.2 (by linarith))

theorem summable_deconvPos_weight {σ : ℝ} (hσ : 0 < σ) : Summable fun n => max (deconvWeight σ n) 0 :=
  Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
    (fun _ => max_le (le_abs_self _) (abs_nonneg _)) (summable_abs_deconvWeight hσ)

theorem summable_deconvNeg_weight {σ : ℝ} (hσ : 0 < σ) : Summable fun n => max (-deconvWeight σ n) 0 :=
  Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
    (fun _ => max_le (neg_le_abs _) (abs_nonneg _)) (summable_abs_deconvWeight hσ)

instance deconvPos_isFinite {σ : ℝ} [Fact (0 < σ)] : IsFiniteMeasure (deconvPos σ) :=
  isFiniteMeasure_atomicMeasure _ _ (fun _ => le_max_right _ _) (summable_deconvPos_weight Fact.out)

instance deconvNeg_isFinite {σ : ℝ} [Fact (0 < σ)] : IsFiniteMeasure (deconvNeg σ) :=
  isFiniteMeasure_atomicMeasure _ _ (fun _ => le_max_right _ _) (summable_deconvNeg_weight Fact.out)

theorem deconvSite_inj {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : deconvSite m = deconvSite n) : m = n :=
  log_natCast_injOn hm hn (neg_inj.1 h)

/-- The support set of the positive part. -/
def deconvPosSupport (σ : ℝ) : Set ℝ := deconvSite '' {n | 0 < deconvWeight σ n}

theorem measurableSet_deconvPosSupport (σ : ℝ) : MeasurableSet (deconvPosSupport σ) :=
  ((Set.countable_univ_iff.2 inferInstance).mono (subset_univ _) |>.image _).measurableSet

theorem deconvPos_compl_support (σ : ℝ) : deconvPos σ (deconvPosSupport σ)ᶜ = 0 := by
  rw [deconvPos, atomicMeasure_apply _ _ (measurableSet_deconvPosSupport σ).compl]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  by_cases hw : 0 < deconvWeight σ n
  · have : deconvSite n ∈ deconvPosSupport σ := ⟨n, hw, rfl⟩
    simp [this]
  · simp [max_eq_right (not_lt.1 hw)]

theorem deconvNeg_support (σ : ℝ) : deconvNeg σ (deconvPosSupport σ) = 0 := by
  rw [deconvNeg, atomicMeasure_apply _ _ (measurableSet_deconvPosSupport σ)]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  by_cases hmem : deconvSite n ∈ deconvPosSupport σ
  · obtain ⟨m, hm, hmn⟩ := hmem
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · simp [deconvWeight_zero] at hm
      · exact h
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [deconvWeight_zero]
    have := deconvSite_inj hm0 hn0 hmn
    subst this
    simp only [Set.mem_setOf_eq] at hm
    simp [max_eq_right (by linarith : -deconvWeight σ m ≤ 0)]
  · simp [hmem]

/-- **(15) The Jordan decomposition of `ν_σ`.** -/
def deconvJordan (σ : ℝ) [Fact (0 < σ)] : JordanDecomposition ℝ where
  posPart := deconvPos σ
  negPart := deconvNeg σ
  mutuallySingular := ⟨(deconvPosSupport σ)ᶜ, (measurableSet_deconvPosSupport σ).compl,
    deconvPos_compl_support σ, by rw [compl_compl]; exact deconvNeg_support σ⟩

/-- **(15) The finite signed measure `ν_σ = Σ_n μ(n) n^{−1−σ} δ_{−log n}`.** -/
def deconvMeasure (σ : ℝ) [Fact (0 < σ)] : SignedMeasure ℝ := (deconvJordan σ).toSignedMeasure

theorem deconvMeasure_eq (σ : ℝ) [Fact (0 < σ)] :
    deconvMeasure σ = (deconvPos σ).toSignedMeasure - (deconvNeg σ).toSignedMeasure := rfl

/-- The atom of the positive part at `−log n`. -/
theorem deconvPos_singleton (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    deconvPos σ {deconvSite n} = ENNReal.ofReal (max (deconvWeight σ n) 0) := by
  rw [deconvPos, atomicMeasure_apply _ _ (measurableSet_singleton _)]
  refine Eq.trans ?_ (tsum_pi_single n (ENNReal.ofReal (max (deconvWeight σ n) 0)))
  refine tsum_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [deconvWeight_zero, Pi.single_apply, hn.ne']
  by_cases hmn : m = n
  · subst hmn; simp
  · have : deconvSite m ∉ ({deconvSite n} : Set ℝ) := fun h => hmn (deconvSite_inj hm hn h)
    simp [this, hmn]

theorem deconvNeg_singleton (σ : ℝ) {n : ℕ} (hn : 0 < n) :
    deconvNeg σ {deconvSite n} = ENNReal.ofReal (max (-deconvWeight σ n) 0) := by
  rw [deconvNeg, atomicMeasure_apply _ _ (measurableSet_singleton _)]
  refine Eq.trans ?_ (tsum_pi_single n (ENNReal.ofReal (max (-deconvWeight σ n) 0)))
  refine tsum_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [deconvWeight_zero, Pi.single_apply, hn.ne']
  by_cases hmn : m = n
  · subst hmn; simp
  · have : deconvSite m ∉ ({deconvSite n} : Set ℝ) := fun h => hmn (deconvSite_inj hm hn h)
    simp [this, hmn]

/-- **The atom of `ν_σ` at `−log n` is `μ(n) n^{−1−σ}`.** -/
theorem deconvMeasure_singleton (σ : ℝ) [Fact (0 < σ)] {n : ℕ} (hn : 0 < n) :
    deconvMeasure σ {deconvSite n} = deconvWeight σ n := by
  rw [deconvMeasure_eq, sub_apply,
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton _),
    Measure.toSignedMeasure_apply_measurable (measurableSet_singleton _), measureReal_def, measureReal_def,
    deconvPos_singleton σ hn, deconvNeg_singleton σ hn, ENNReal.toReal_ofReal (le_max_right _ _),
    ENNReal.toReal_ofReal (le_max_right _ _)]
  rcases le_total 0 (deconvWeight σ n) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- **Coefficient recovery from the atoms.**  `μ(n) = n^{1+σ} ν_σ({−log n})`. -/
theorem moebius_eq_rpow_mul_deconvMeasure (σ : ℝ) [Fact (0 < σ)] {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius n : ℝ) = (n : ℝ) ^ (1 + σ) * deconvMeasure σ {deconvSite n} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [deconvMeasure_singleton σ hn, deconvWeight, mul_left_comm, ← Real.rpow_add hnR, add_neg_cancel,
    Real.rpow_zero, mul_one]

/-! ## (19) Total variation -/

/-- **(19a)** `‖ν_σ‖_TV = Σ_n μ(n)² n^{−1−σ}`. -/
theorem deconvMeasure_totalVariation_univ (σ : ℝ) [Fact (0 < σ)] :
    (deconvMeasure σ).totalVariation univ =
      ENNReal.ofReal (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + σ))) := by
  have hσ : 0 < σ := Fact.out
  rw [SignedMeasure.totalVariation, deconvMeasure, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  simp only [deconvJordan, Measure.add_apply, deconvPos, deconvNeg]
  rw [atomicMeasure_univ _ _ (fun _ => le_max_right _ _) (summable_deconvPos_weight hσ),
    atomicMeasure_univ _ _ (fun _ => le_max_right _ _) (summable_deconvNeg_weight hσ),
    ← ENNReal.ofReal_add (tsum_nonneg fun _ => le_max_right _ _) (tsum_nonneg fun _ => le_max_right _ _),
    ← (summable_deconvPos_weight hσ).tsum_add (summable_deconvNeg_weight hσ)]
  congr 1
  refine tsum_congr fun n => ?_
  rw [← abs_deconvWeight]
  rcases le_total 0 (deconvWeight σ n) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h, zero_add]

/-- **(19b)** `Σ_n μ(n)² n^{−1−σ} = ζ(1+σ)/ζ(2+2σ)`. -/
theorem tsum_moebius_sq_rpow_eq {σ : ℝ} (hσ : 0 < σ) :
    ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + σ)) : ℝ) : ℂ) =
      riemannZeta (1 + σ) / riemannZeta (2 + 2 * σ) := by
  have hs : 1 < ((1 + σ : ℝ) : ℂ).re := by simp; linarith
  have h := LSeries_squarefree_mul_riemannZeta_two_mul hs
  have hζ : riemannZeta (2 * ((1 + σ : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hL : LSeries (fun n => ((ArithmeticFunction.pmul (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
      ArithmeticFunction.moebius n : ℤ) : ℂ)) ((1 + σ : ℝ) : ℂ) =
      ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + σ)) : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn.ne', ArithmeticFunction.pmul_apply]
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    rw [Complex.ofReal_cpow hnR, div_eq_mul_inv, ← Complex.cpow_neg]
    push_cast
    ring
  rw [← hL, show (2 : ℂ) + 2 * σ = 2 * ((1 + σ : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) + σ = ((1 + σ : ℝ) : ℂ) by push_cast; ring, eq_div_iff hζ, h]

/-- **(19c)** `σ ‖ν_σ‖_TV → 1/ζ(2) = 6/π²` as `σ ↓ 0`. -/
theorem tendsto_mul_tsum_moebius_sq_rpow :
    Tendsto (fun σ : ℝ => σ * ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + σ)))
      (𝓝[>] 0) (𝓝 (6 / Real.pi ^ 2)) := by
  have hres := riemannZeta_residue_one
  have hmap : Tendsto (fun σ : ℝ => ((1 + σ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => ((1 + σ : ℝ) : ℂ)) (𝓝 0) (𝓝 ((1 + 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact (hσ : (0 : ℝ) < σ).ne' this
  have h1 := hres.comp hmap
  have h2 : Tendsto (fun σ : ℝ => riemannZeta (2 + 2 * ((σ : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (riemannZeta 2)) := by
    have hc : ContinuousAt riemannZeta 2 := (differentiableAt_riemannZeta (by norm_num)).continuousAt
    have : Tendsto (fun σ : ℝ => 2 + 2 * ((σ : ℝ) : ℂ)) (𝓝 0) (𝓝 2) := by
      have hcont : Continuous fun σ : ℝ => (2 : ℂ) + 2 * (σ : ℂ) := by fun_prop
      simpa using hcont.tendsto 0
    exact (hc.tendsto.comp this).mono_left nhdsWithin_le_nhds
  have h3 := h1.div h2 (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hζ2 : riemannZeta 2 = (Real.pi ^ 2 / 6 : ℝ) := by rw [riemannZeta_two]; push_cast; ring
  rw [hζ2] at h3
  have h4 : Tendsto (fun σ : ℝ => ((σ * ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 *
      (n : ℝ) ^ (-(1 + σ)) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (1 / ((Real.pi ^ 2 / 6 : ℝ) : ℂ))) := by
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    simp only [Pi.div_apply, Function.comp_apply]
    rw [Complex.ofReal_mul, tsum_moebius_sq_rpow_eq hσ]
    push_cast
    ring_nf
  have h5 := (Complex.continuous_re.tendsto _).comp h4
  simp only [Function.comp_def, Complex.ofReal_re] at h5
  convert h5 using 2
  rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  field_simp

/-! ## Weighted Gaussian atoms -/

/-- `e^{σy} ψ_Q(y)`. -/
def weightedAtom (σ : ℝ) (Q : Polynomial ℝ) (y : ℝ) : ℝ := Real.exp (σ * y) * gaussPolyAtom Q y

theorem gaussPolyAtom_add (P Q : Polynomial ℝ) (y : ℝ) :
    gaussPolyAtom (P + Q) y = gaussPolyAtom P y + gaussPolyAtom Q y := by
  simp only [gaussPolyAtom, Polynomial.eval_add]; ring

theorem gaussPolyAtom_C_mul (c : ℝ) (Q : Polynomial ℝ) (y : ℝ) :
    gaussPolyAtom (Polynomial.C c * Q) y = c * gaussPolyAtom Q y := by
  simp only [gaussPolyAtom, Polynomial.eval_mul, Polynomial.eval_C]; ring

theorem hasDerivAt_weightedAtom (σ : ℝ) (Q : Polynomial ℝ) (y : ℝ) :
    HasDerivAt (weightedAtom σ Q) (weightedAtom σ (Polynomial.C σ * Q + gaussPolyAtomStep Q) y) y := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (σ * y)) (Real.exp (σ * y) * σ) y :=
    ((hasDerivAt_id y).const_mul σ |>.congr_deriv (by simp)).exp
  refine (h1.fun_mul (hasDerivAt_gaussPolyAtom Q y)).congr_deriv ?_
  rw [weightedAtom, gaussPolyAtom_add, gaussPolyAtom_C_mul]
  ring

theorem continuous_weightedAtom (σ : ℝ) (Q : Polynomial ℝ) : Continuous (weightedAtom σ Q) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_weightedAtom σ Q y).continuousAt

theorem deriv_weightedAtom (σ : ℝ) (Q : Polynomial ℝ) :
    deriv (weightedAtom σ Q) = weightedAtom σ (Polynomial.C σ * Q + gaussPolyAtomStep Q) :=
  funext fun y => (hasDerivAt_weightedAtom σ Q y).deriv

theorem integrable_weightedAtom (Q : Polynomial ℝ) {σ : ℝ} (hσ : -3 < σ) : Integrable (weightedAtom σ Q) := by
  have h := (integrable_cexp_mul_gaussPolyAtom Q (z := (σ : ℂ)) (by simpa using hσ)).norm
  refine (integrable_norm_iff (continuous_weightedAtom σ Q).aestronglyMeasurable).1
    (h.congr (Eventually.of_forall fun y => ?_))
  simp only [weightedAtom, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  congr 2
  simp

theorem exists_abs_weightedAtom_le (Q : Polynomial ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ M : ℝ, ∀ y, |weightedAtom σ Q y| ≤ M := by
  obtain ⟨K, hK, hb⟩ := exists_abs_gaussPolyAtom_le_envelope Q
  refine ⟨K * (Real.exp ((3 + σ) ^ 2 / (2 * Real.pi)) + 1), fun y => ?_⟩
  rw [weightedAtom, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos _).le).trans ?_
  have hsplit : Real.exp (σ * y) * (K * (Real.exp (3 * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y))))) =
      K * (Real.exp ((3 + σ) * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))) := by
    rw [add_mul, Real.exp_add]; ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ hK
  rcases le_total 0 y with hy | hy
  · have hD : Real.exp ((3 + σ) * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y))) ≤
        Real.exp ((3 + σ) ^ 2 / (2 * Real.pi)) := by
      have h2 := exp_mul_exp_neg_le (2 * (3 + σ)) y hy
      have hsq : Real.exp ((3 + σ) * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y))) =
          Real.sqrt (Real.exp ((2 * (3 + σ)) * y) * Real.exp (-Real.pi * Real.exp (2 * y))) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
      rw [hsq, Real.sqrt_le_left (Real.exp_pos _).le, ← Real.exp_nat_mul]
      refine h2.trans (Real.exp_le_exp.2 ?_)
      have hπ := Real.pi_pos
      have h3 : (2 * (3 + σ)) ^ 2 / (8 * Real.pi) = (3 + σ) ^ 2 / (2 * Real.pi) := by field_simp; ring
      have h4 : 0 ≤ (3 + σ) ^ 2 / (2 * Real.pi) := by positivity
      rw [h3]; push_cast
      linarith
    linarith [Real.exp_pos ((3 + σ) ^ 2 / (2 * Real.pi))]
  · have h1 : Real.exp ((3 + σ) * y) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h2 : Real.exp (-(Real.pi / 2 * Real.exp (2 * y))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, Real.exp_pos (2 * y)])
    have := Real.exp_pos ((3 + σ) ^ 2 / (2 * Real.pi))
    nlinarith [mul_le_mul h1 h2 (Real.exp_pos _).le zero_le_one, Real.exp_pos ((3 + σ) * y),
      Real.exp_pos (-(Real.pi / 2 * Real.exp (2 * y)))]

/-- `φ_σ(y) = e^{σy} φ(y)`. -/
def weightedCutoffAtom (σ : ℝ) : ℝ → ℝ := weightedAtom σ cutoffAtomPoly

/-- `C_σ(y) = e^{σy} C(y)`. -/
def weightedCutoffCurrent (σ y : ℝ) : ℝ := Real.exp (σ * y) * cofinalBoundaryProfile y

theorem integrable_weightedCutoffCurrent {σ : ℝ} (hσ : 0 < σ) : Integrable (weightedCutoffCurrent σ) := by
  have h := ((integral_cexp_mul_cofinalBoundaryProfile (z := (σ : ℂ)) (by simpa using hσ)).1).norm
  refine (integrable_norm_iff ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    continuous_cofinalBoundaryProfile).aestronglyMeasurable).1 (h.congr (Eventually.of_forall fun y => ?_))
  simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp

/-! ## (16) The convolution identity -/

/-- Convolution `((μ₁ − μ₂) * f)(y) = ∫ f(y − a) dμ₁(a) − ∫ f(y − a) dμ₂(a)`. -/
def signedMeasureConv (μ₁ μ₂ : Measure ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ a, f (y - a) ∂μ₁ - ∫ a, f (y - a) ∂μ₂

theorem integral_atomic_deconv {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hcs : Summable c)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    Integrable f (atomicMeasure c deconvSite) ∧
      ∫ a, f a ∂atomicMeasure c deconvSite = ∑' n, c n * f (deconvSite n) := by
  have hint : Integrable f (atomicMeasure c deconvSite) := by
    refine integrable_atomicMeasure hc hf.aestronglyMeasurable
      (Summable.of_nonneg_of_le (fun n => mul_nonneg (hc n) (norm_nonneg _)) (fun n => ?_)
        (hcs.mul_right M))
    rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM _) (hc n)
  exact ⟨hint, by rw [integral_atomicMeasure hc hint]; rfl⟩

theorem deconvWeight_mul_weightedCutoffAtom (σ y : ℝ) (n : ℕ) :
    deconvWeight σ n * weightedCutoffAtom σ (y + Real.log n) =
      Real.exp (σ * y) * (moebiusInvWeight n * gaussPolyAtom cutoffAtomPoly (y + Real.log n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deconvWeight, moebiusInvWeight]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [deconvWeight, weightedCutoffAtom, weightedAtom, moebiusInvWeight, mul_add, Real.exp_add,
    show Real.exp (σ * Real.log n) = (n : ℝ) ^ σ by rw [Real.rpow_def_of_pos hnR, mul_comm],
    Real.rpow_neg hnR.le, Real.rpow_add hnR, Real.rpow_one]
  field_simp

/-- **(16) `C_σ = ν_σ * φ_σ`**, pointwise on `ℝ` (both sides are in `L¹`). -/
theorem signedMeasureConv_deconv_eq (σ : ℝ) [Fact (0 < σ)] (y : ℝ) :
    signedMeasureConv (deconvPos σ) (deconvNeg σ) (weightedCutoffAtom σ) y = weightedCutoffCurrent σ y := by
  have hσ : 0 < σ := Fact.out
  obtain ⟨M, hM⟩ := exists_abs_weightedAtom_le cutoffAtomPoly hσ.le
  have hf : Continuous fun a => weightedCutoffAtom σ (y - a) :=
    (continuous_weightedAtom σ _).comp (continuous_const.sub continuous_id)
  have hfM : ∀ a, |weightedCutoffAtom σ (y - a)| ≤ M := fun a => hM _
  obtain ⟨-, h1⟩ := integral_atomic_deconv (fun _ => le_max_right _ _) (summable_deconvPos_weight hσ) hf hfM
  obtain ⟨-, h2⟩ := integral_atomic_deconv (fun _ => le_max_right _ _) (summable_deconvNeg_weight hσ) hf hfM
  have hsite : ∀ n : ℕ, y - deconvSite n = y + Real.log n := fun n => by rw [deconvSite]; ring
  have hs : ∀ (c : ℕ → ℝ), (∀ n, |c n| ≤ |deconvWeight σ n|) →
      Summable fun n => c n * weightedCutoffAtom σ (y - deconvSite n) := fun c hc =>
    Summable.of_norm_bounded ((summable_abs_deconvWeight hσ).mul_right M) fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hc n) (hM _) (abs_nonneg _) (abs_nonneg _)
  have hp := hs (fun n => max (deconvWeight σ n) 0) fun n => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)
  have hn := hs (fun n => max (-deconvWeight σ n) 0) fun n => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (neg_le_abs _) (abs_nonneg _)
  rw [signedMeasureConv, deconvPos, deconvNeg, h1, h2, ← hp.tsum_sub hn, weightedCutoffCurrent,
    cofinalBoundaryProfile_eq_logShiftSeries, logShiftSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, hsite, deconvWeight_mul_weightedCutoffAtom]

/-! ## Injectivity of convolution by `φ_σ` -/

/-- The Fourier transform of `φ_σ` is `−G(σ + it)`. -/
theorem integral_cexp_mul_weightedCutoffAtom {σ : ℝ} (hσ : -3 < σ) (t : ℝ) :
    (∫ y : ℝ, Complex.exp (t * y * Complex.I) * (weightedCutoffAtom σ y : ℂ)) =
      -commutatorGammaFactor (σ + t * Complex.I) := by
  rw [← integral_cexp_mul_cutoffAtom (z := σ + t * Complex.I) (by simpa using hσ)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [weightedCutoffAtom, weightedAtom]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- **Convolution by `φ_σ` is injective on finite signed measures.**  If `(μ₁ − μ₂) * φ_σ` and
`(μ₁' − μ₂') * φ_σ` agree, then `μ₁ − μ₂ = μ₁' − μ₂'`. -/
theorem signedMeasureConv_weightedCutoffAtom_injective {σ : ℝ} (hσ : 0 ≤ σ)
    {μ₁ μ₂ μ₁' μ₂' : Measure ℝ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₁']
    [IsFiniteMeasure μ₂']
    (h : ∀ y, signedMeasureConv μ₁ μ₂ (weightedCutoffAtom σ) y =
      signedMeasureConv μ₁' μ₂' (weightedCutoffAtom σ) y) :
    μ₁.toSignedMeasure - μ₂.toSignedMeasure = μ₁'.toSignedMeasure - μ₂'.toSignedMeasure := by
  set f := weightedCutoffAtom σ
  obtain ⟨M, hM⟩ := exists_abs_weightedAtom_le cutoffAtomPoly hσ
  have hfc : Continuous f := continuous_weightedAtom σ _
  have hfi : Integrable f := integrable_weightedAtom cutoffAtomPoly (by linarith)
  have hint : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (y : ℝ), Integrable (fun a => f (y - a)) ν :=
    fun ν _ y => Integrable.of_bound (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable M
      (Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hM _)
  set m := μ₁ + μ₂'
  set m' := μ₁' + μ₂
  have hconv : ∀ y, ∫ a, f (y - a) ∂m = ∫ a, f (y - a) ∂m' := fun y => by
    rw [integral_add_measure (hint μ₁ y) (hint μ₂' y), integral_add_measure (hint μ₁' y) (hint μ₂ y)]
    have := h y
    rw [signedMeasureConv, signedMeasureConv] at this
    linarith
  -- Fourier transform of `m * f`
  have hfourier : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (t : ℝ),
      (∫ y : ℝ, Complex.exp (t * y * Complex.I) * ((∫ a, f (y - a) ∂ν : ℝ) : ℂ)) =
        charFun ν t * -commutatorGammaFactor (σ + t * Complex.I) := by
    intro ν _ t
    set F : ℝ × ℝ → ℂ := fun p => Complex.exp (t * p.1 * Complex.I) * (f (p.1 - p.2) : ℂ)
    have hFm : AEStronglyMeasurable F (volume.prod ν) :=
      (((Complex.continuous_exp.comp (((continuous_const.mul (Complex.continuous_ofReal.comp
        continuous_fst))).mul continuous_const)).mul (Complex.continuous_ofReal.comp
          (hfc.comp (continuous_fst.sub continuous_snd))))).aestronglyMeasurable
    have hnorm : ∀ a, (∫ y, ‖F (y, a)‖) = ∫ y, |f y| := fun a => by
      have : (fun y => ‖F (y, a)‖) = fun y => |f (y - a)| := by
        funext y
        simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [Complex.norm_exp]
        simp
      rw [this, integral_sub_right_eq_self (fun y => |f y|) a]
    have hFi : Integrable F (volume.prod ν) := by
      rw [integrable_prod_iff' hFm]
      refine ⟨Eventually.of_forall fun a => ?_, ?_⟩
      · refine (hfi.comp_sub_right a).norm.mono' ?_ (Eventually.of_forall fun y => ?_)
        · exact ((Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
              continuous_const)).mul (Complex.continuous_ofReal.comp
                (hfc.comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
        · simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
          simp
      · simp_rw [hnorm]
        exact integrable_const _
    have hswap := integral_integral_swap (f := fun y a => F (y, a)) hFi
    have hin : ∀ y : ℝ, (∫ a, F (y, a) ∂ν) =
        Complex.exp (t * y * Complex.I) * ((∫ a, f (y - a) ∂ν : ℝ) : ℂ) := fun y => by
      simp only [F]
      rw [integral_const_mul, integral_complex_ofReal]
    have hout : ∀ a : ℝ, (∫ y, F (y, a)) = Complex.exp (t * a * Complex.I) *
        -commutatorGammaFactor (σ + t * Complex.I) := fun a => by
      rw [← integral_cexp_mul_weightedCutoffAtom (by linarith) t, ← integral_const_mul]
      rw [← integral_sub_right_eq_self (fun y : ℝ => Complex.exp (t * a * Complex.I) *
        (Complex.exp (t * y * Complex.I) * (f y : ℂ))) a]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [F]
      rw [← mul_assoc, ← Complex.exp_add]
      push_cast
      ring_nf
    simp_rw [hin] at hswap
    rw [hswap]
    simp_rw [hout]
    rw [integral_mul_const, charFun_apply_real]
  have hG : ∀ t : ℝ, -commutatorGammaFactor (σ + t * Complex.I) ≠ 0 := fun t =>
    neg_ne_zero.2 (commutatorGammaFactor_ne_zero (by simp; linarith))
  have hchar : charFun m = charFun m' := by
    funext t
    have h1 := hfourier m t
    have h2 := hfourier m' t
    simp_rw [hconv] at h1
    rw [h1] at h2
    exact mul_right_cancel₀ (hG t) h2
  have hm : m = m' := Measure.ext_of_charFun hchar
  have hs : μ₁.toSignedMeasure + μ₂'.toSignedMeasure = μ₁'.toSignedMeasure + μ₂.toSignedMeasure := by
    rw [← Measure.toSignedMeasure_add, ← Measure.toSignedMeasure_add]
    exact Measure.toSignedMeasure_congr hm
  rw [sub_eq_sub_iff_add_eq_add, hs]

/-- **`C_σ` determines `ν_σ`.**  Any finite signed measure whose convolution with `φ_σ` is `C_σ` is
`ν_σ`. -/
theorem eq_deconvMeasure_of_conv (σ : ℝ) [Fact (0 < σ)] {μ₁ μ₂ : Measure ℝ} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (h : ∀ y, signedMeasureConv μ₁ μ₂ (weightedCutoffAtom σ) y = weightedCutoffCurrent σ y) :
    μ₁.toSignedMeasure - μ₂.toSignedMeasure = deconvMeasure σ := by
  rw [deconvMeasure_eq]
  exact signedMeasureConv_weightedCutoffAtom_injective (Fact.out : (0 : ℝ) < σ).le fun y => by
    rw [h y, signedMeasureConv_deconv_eq]

/-- **Divergent total variation at critical weight.**  `‖ν_σ‖_TV → ∞` as `σ ↓ 0`. -/
theorem tendsto_tsum_moebius_sq_rpow_atTop :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 * (n : ℝ) ^ (-(1 + σ)))
      (𝓝[>] 0) atTop := by
  have h := tendsto_mul_tsum_moebius_sq_rpow.pos_mul_atTop (by positivity) tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have : σ ≠ 0 := (hσ : (0 : ℝ) < σ).ne'
  field_simp

/-! ## (17) The singular causal readout -/

/-- The readout kernel `1_{a < −log t} e^{−(σ+1/2)a} k(−a − log t)`. -/
def causalReadoutKernel (σ t a : ℝ) : ℝ :=
  (Iio (-Real.log t)).indicator
    (fun a => Real.exp (-(σ + 1 / 2) * a) * thetaCuspFullSource (-a - Real.log t)) a

theorem measurable_causalReadoutKernel (σ t : ℝ) : Measurable (causalReadoutKernel σ t) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_thetaCuspFullSource.comp (continuous_neg.sub continuous_const))).measurable.indicator
      measurableSet_Iio

/-- Each atom of `ν_σ` reads off exactly one term of the causal tail. -/
theorem deconvWeight_mul_causalReadoutKernel (σ : ℝ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    deconvWeight σ n * causalReadoutKernel σ t (deconvSite n) = causalMobiusThetaTerm t n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [deconvWeight, causalMobiusThetaTerm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [causalReadoutKernel, causalMobiusThetaTerm, deconvSite]
  by_cases htn : t < n
  · have hmem : -Real.log n ∈ Iio (-Real.log t) := neg_lt_neg (Real.log_lt_log ht htn)
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show t ∈ Ioo 0 (n : ℝ) from ⟨ht, htn⟩),
      deconvWeight, neg_neg, Real.log_div hnR.ne' ht.ne',
      show Real.exp (-(σ + 1 / 2) * -Real.log n) = (n : ℝ) ^ (σ + 1 / 2) by
        rw [Real.rpow_def_of_pos hnR]; ring_nf]
    have : (n : ℝ) ^ (-(1 + σ)) * (n : ℝ) ^ (σ + 1 / 2) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hnR]; ring_nf
    rw [← this]; ring
  · have hmem : -Real.log n ∉ Iio (-Real.log t) := fun h =>
      htn (by
        have : Real.log t < Real.log n := neg_lt_neg_iff.1 h
        exact (Real.log_lt_log_iff ht hnR).1 this)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun h : t ∈ Ioo 0 (n : ℝ) => htn h.2),
      mul_zero]

/-- **(17) The singular readout.**  `B(t) = ∫_{a < −log t} e^{−(σ+1/2)a} k(−a − log t) dν_σ(a)`. -/
theorem causalMobiusThetaTail_eq_deconv_readout (σ : ℝ) [Fact (0 < σ)] {t : ℝ} (ht : 0 < t) :
    causalMobiusThetaTail t =
      ∫ a, causalReadoutKernel σ t a ∂deconvPos σ - ∫ a, causalReadoutKernel σ t a ∂deconvNeg σ := by
  have hσ : 0 < σ := Fact.out
  have habs := (summable_causalMobiusThetaTerm t).abs
  have hint : ∀ (c : ℕ → ℝ), (∀ n, 0 ≤ c n) → (∀ n, c n ≤ |deconvWeight σ n|) →
      Integrable (causalReadoutKernel σ t) (atomicMeasure c deconvSite) ∧
        Summable fun n => c n * causalReadoutKernel σ t (deconvSite n) := by
    intro c hc0 hc
    have hb : ∀ n, |c n * causalReadoutKernel σ t (deconvSite n)| ≤ |causalMobiusThetaTerm t n| := fun n => by
      rw [← deconvWeight_mul_causalReadoutKernel σ ht n, abs_mul, abs_mul, abs_of_nonneg (hc0 n)]
      exact mul_le_mul_of_nonneg_right (hc n) (abs_nonneg _)
    refine ⟨integrable_atomicMeasure hc0 (measurable_causalReadoutKernel σ t).aestronglyMeasurable
      (Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (norm_nonneg _)) (fun n => ?_) habs),
      Summable.of_norm_bounded habs fun n => by rw [Real.norm_eq_abs]; exact hb n⟩
    rw [Real.norm_eq_abs]
    calc c n * |causalReadoutKernel σ t (deconvSite n)|
        = |c n * causalReadoutKernel σ t (deconvSite n)| := by rw [abs_mul, abs_of_nonneg (hc0 n)]
      _ ≤ _ := hb n
  obtain ⟨hi1, hs1⟩ := hint (fun n => max (deconvWeight σ n) 0) (fun _ => le_max_right _ _)
    fun n => max_le (le_abs_self _) (abs_nonneg _)
  obtain ⟨hi2, hs2⟩ := hint (fun n => max (-deconvWeight σ n) 0) (fun _ => le_max_right _ _)
    fun n => max_le (neg_le_abs _) (abs_nonneg _)
  rw [deconvPos, deconvNeg, integral_atomicMeasure (fun _ => le_max_right _ _) hi1,
    integral_atomicMeasure (fun _ => le_max_right _ _) hi2]
  simp only [smul_eq_mul]
  rw [← hs1.tsum_sub hs2, causalMobiusThetaTail]
  refine tsum_congr fun n => ?_
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, deconvWeight_mul_causalReadoutKernel σ ht n]

/-! ## (18) The inverse is unbounded -/

/-- The unit dipole `λ_n = δ_{−log (n+1)} − δ_{−log (n+2)}` (indexed from `1`), as a Jordan
decomposition. -/
def unitDipoleJordan (n : ℕ) : JordanDecomposition ℝ where
  posPart := Measure.dirac (deconvSite (n + 1))
  negPart := Measure.dirac (deconvSite (n + 2))
  mutuallySingular := ⟨{deconvSite (n + 1)}ᶜ, (measurableSet_singleton _).compl, by
    rw [Measure.dirac_apply]; simp, by
    rw [compl_compl, Measure.dirac_apply]
    have : deconvSite (n + 2) ∉ ({deconvSite (n + 1)} : Set ℝ) := fun h =>
      absurd (deconvSite_inj (by omega) (by omega) h) (by omega)
    simp [this]⟩

/-- **`‖λ_n‖_TV = 2`.** -/
theorem unitDipole_totalVariation (n : ℕ) :
    (unitDipoleJordan n).toSignedMeasure.totalVariation univ = 2 := by
  rw [SignedMeasure.totalVariation, JordanDecomposition.toJordanDecomposition_toSignedMeasure]
  simp only [unitDipoleJordan, Measure.add_apply, measure_univ]
  norm_num

theorem signedMeasureConv_dirac (a b : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    signedMeasureConv (Measure.dirac a) (Measure.dirac b) f y = f (y - a) - f (y - b) := by
  rw [signedMeasureConv, integral_dirac, integral_dirac]

theorem tendsto_log_add_two_sub_log_add_one :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hle : ∀ n : ℕ, Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := fun n => by
    have h1 : (0 : ℝ) < n + 1 := by positivity
    rw [← Real.log_div (by positivity) h1.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    field_simp; ring
  have hge : ∀ n : ℕ, 0 ≤ Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) := fun n =>
    sub_nonneg.2 (Real.log_le_log (by positivity) (by linarith))
  exact squeeze_zero hge hle tendsto_one_div_add_atTop_nhds_zero_nat

/-- **(18)** `‖λ_n * φ_σ‖₁ → 0` by continuity of translation in `L¹`. -/
theorem tendsto_unitDipole_conv_L1 {σ : ℝ} (hσ : -3 < σ) :
    Tendsto (fun n : ℕ => ∫ y, |signedMeasureConv (Measure.dirac (deconvSite (n + 1)))
      (Measure.dirac (deconvSite (n + 2))) (weightedCutoffAtom σ) y|) atTop (𝓝 0) := by
  set f := weightedCutoffAtom σ
  have hfd : Differentiable ℝ f := fun y => (hasDerivAt_weightedAtom σ _ y).differentiableAt
  have hderiv : deriv f = weightedAtom σ (Polynomial.C σ * cutoffAtomPoly + gaussPolyAtomStep cutoffAtomPoly) :=
    deriv_weightedAtom σ _
  have hfc : Continuous (deriv f) := by rw [hderiv]; exact continuous_weightedAtom _ _
  have hfi' : Integrable (deriv f) := by rw [hderiv]; exact integrable_weightedAtom _ hσ
  have hfi : Integrable f := integrable_weightedAtom _ hσ
  set D : ℝ := ∫ x : ℝ, ‖deriv f x‖
  have hbound : ∀ n : ℕ, (∫ y, |signedMeasureConv (Measure.dirac (deconvSite (n + 1)))
      (Measure.dirac (deconvSite (n + 2))) f y|) ≤
        (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) * D := by
    intro n
    set h : ℝ := Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)
    have hh : 0 ≤ h := sub_nonneg.2 (Real.log_le_log (by positivity) (by linarith))
    have heq : (∫ y, |signedMeasureConv (Measure.dirac (deconvSite (n + 1)))
        (Measure.dirac (deconvSite (n + 2))) f y|) = ∫ x : ℝ, ‖f (x + h) - f x‖ := by
      simp_rw [signedMeasureConv_dirac, deconvSite]
      rw [← integral_add_right_eq_self (μ := volume)
        (fun x : ℝ => ‖f (x + h) - f x‖) (Real.log ((n : ℝ) + 1))]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs, h]
      push_cast
      rw [abs_sub_comm]
      congr 3 <;> ring
    rw [heq]
    exact GaloisForLFunctions.HTGeometry.integral_norm_translation_le f hfd hfc hfi' hh
      ((hfi.comp_add_right h).sub hfi).norm
  have hlim : Tendsto (fun n : ℕ => (Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1)) * D) atTop (𝓝 0) := by
    simpa using tendsto_log_add_two_sub_log_add_one.mul_const D
  exact squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) hbound hlim

/-- **No bounded inverse.**  There is no constant `C` with `‖λ‖_TV ≤ C ‖λ * φ_σ‖₁` even for the
unit dipoles at adjacent arithmetic log sites. -/
theorem not_exists_bounded_inverse_unitDipole {σ : ℝ} (hσ : -3 < σ) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, ((unitDipoleJordan n).toSignedMeasure.totalVariation univ).toReal ≤
      C * ∫ y, |signedMeasureConv (Measure.dirac (deconvSite (n + 1)))
        (Measure.dirac (deconvSite (n + 2))) (weightedCutoffAtom σ) y| := by
  rintro ⟨C, hC⟩
  have h := (tendsto_unitDipole_conv_L1 hσ).const_mul C
  rw [mul_zero] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  have := hC n
  rw [unitDipole_totalVariation] at this
  norm_num at this
  linarith

end

end RHTower
