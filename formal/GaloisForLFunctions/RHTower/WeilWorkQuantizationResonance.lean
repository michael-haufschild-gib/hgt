import GaloisForLFunctions.RHTower.WeilWorkQuantizationResonantTerms

/-!
# Arithmetic frequency resonances of the canonical Weil trace

Weil positivity supplies the summable Dirichlet coefficients, the open-strip
contour bounds and the actual measurable critical trace. Each linear
frequency therefore retains its unique arithmetic coefficient, with a
vanishing radial error. No boundary continuity, periodic representation or
frequency-separation premise is added to the source law.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist RightEdgeKernel IntegerMassRigidity HamburgerStability
  GaloisForLFunctions.HTGeometry

/-- Integer arithmetic resonance for a linear frequency multiplier. -/
def quantizationFrequencyResonates (ω : ℝ) (m n : ℕ) : Prop :=
  1 ≤ n ∧ Real.log n + ω / 2 = Real.log m

/-- A fixed frequency can resonate with at most one arithmetic coefficient. -/
theorem quantizationFrequencyResonates_unique {ω : ℝ} {m n k : ℕ}
    (hn : quantizationFrequencyResonates ω m n) (hk : quantizationFrequencyResonates ω m k) :
    n = k := by
  have hn1 := hn.1
  have hk1 := hk.1
  have he : Real.log n = Real.log k := by linarith [hn.2, hk.2]
  have he' := congrArg Real.exp he
  rw [Real.exp_log (by exact_mod_cast (show 0 < n by omega)),
    Real.exp_log (by exact_mod_cast (show 0 < k by omega))] at he'
  exact_mod_cast he'

/-- The actual forward coefficient at a shifted resonance, with its scaling retained. -/
def quantizationFrequencyResidue (lam : ℕ → ℝ) (ω : ℝ) (m : ℕ) : ℂ := by
  classical
  exact if h : ∃ n : ℕ, quantizationFrequencyResonates ω m n then
    ((Real.exp (ω / 4) : ℝ) : ℂ) * dirichletExp (lamLog lam) h.choose
  else 0

/-- Resolving the unique resonance does not alter its coefficient. -/
theorem quantizationFrequencyResidue_eq {lam : ℕ → ℝ} {ω : ℝ} {m n : ℕ}
    (hn : quantizationFrequencyResonates ω m n) :
    quantizationFrequencyResidue lam ω m =
      ((Real.exp (ω / 4) : ℝ) : ℂ) * dirichletExp (lamLog lam) n := by
  classical
  have hex : ∃ k : ℕ, quantizationFrequencyResonates ω m k := ⟨n, hn⟩
  simp only [quantizationFrequencyResidue, dif_pos hex]
  rw [quantizationFrequencyResonates_unique hex.choose_spec hn]

/-- The actual Dirichlet coefficients give a summable edge majorant. -/
theorem summable_quantization_forward_terms {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Summable fun n => ‖LSeries.term (dirichletExp (lamLog lam)) (((3 / 2 : ℝ) : ℂ)) n‖ := by
  have hsl := fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ
  exact (LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
    (lseriesSummable_of_le (norm_lamLog_le lam) hsl (by norm_num))).1.norm

/-- Shifted resonance coefficients have the source's exponential frequency majorant. -/
theorem exists_bound_quantizationFrequencyResidue {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω : ℝ,
      ‖quantizationFrequencyResidue lam ω m‖ ≤ K * Real.exp (|ω| / 2) := by
  classical
  let a := dirichletExp (lamLog lam)
  let S : ℝ := ∑' n, ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖
  let z : ℂ := (m : ℂ) ^ (-edgePt 0)
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (by exact_mod_cast (show m ≠ 0 by omega))))
  have hS : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨S / ‖z‖, div_nonneg hS hz.le, fun ω => ?_⟩
  by_cases hex : ∃ n : ℕ, quantizationFrequencyResonates ω m n
  · obtain ⟨n, hn⟩ := hex
    have ht := congrArg norm (quantization_twist_term_resonant a hm hn.1 hn.2 (edgePt 0))
    rw [norm_mul, norm_term_edgePt, norm_linTwist_edgePt] at ht
    have he : ‖quantizationFrequencyResidue lam ω m‖ * ‖z‖ =
        ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ * Real.exp (-(ω / 2)) := by
      rw [quantizationFrequencyResidue_eq hn]
      exact (norm_mul _ _).symm.trans ht.symm
    have hnS : ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ ≤ S :=
      (summable_quantization_forward_terms hW).le_tsum n (fun _ _ => norm_nonneg _)
    calc ‖quantizationFrequencyResidue lam ω m‖ ≤
        (S * Real.exp (|ω| / 2)) / ‖z‖ := by
          apply (le_div_iff₀ hz).mpr
          rw [he]
          gcongr
          linarith [neg_le_abs ω]
      _ = S / ‖z‖ * Real.exp (|ω| / 2) := by ring
  · simp only [quantizationFrequencyResidue, dif_neg hex, norm_zero]
    positivity

/-- Zero frequency recovers the ordinary arithmetic coefficient. -/
theorem quantizationFrequencyResidue_zero {lam : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m) :
    quantizationFrequencyResidue lam 0 m = dirichletExp (lamLog lam) m := by
  rw [quantizationFrequencyResidue_eq (show quantizationFrequencyResonates 0 m m from
    ⟨hm, by simp⟩)]
  simp

/-- The source contour displacement contributes no radial residue. -/
theorem tendsto_quantization_twist_contour_displacement {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (ω : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      ((∫ y in Iic (-2 : ℝ), linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
        (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I))) -
       ∫ y in Iic (-2 : ℝ), linTwist ω (edgePt y) *
        edgeIntegrand (quantizationCompletion hW) ((ε : ℂ) + (m : ℂ) * I) (edgePt y)))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hF⟩ := exists_norm_quantizationProdF_le hW
  let τ : ℝ → ℂ := fun ε => (ε : ℂ) + (m : ℂ) * I
  let K : ℝ := Real.exp (|ω| / 2) * C * 3 ^ (1 / 2 : ℝ) *
    (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1))
  have hlim : Tendsto (fun ε : ℝ => ε * K) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_id.tendsto (0 : ℝ)).mul_const K |>.mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hτre : (τ ε).re = ε := by simp [τ]
  have hτre0 : 0 < (τ ε).re := by rw [hτre]; exact hε.1
  have hτ1 : 1 ≤ ‖τ ε‖ := by
    have h := Complex.abs_im_le_norm (τ ε)
    have him : (τ ε).im = m := by simp [τ]
    rw [him, abs_of_nonneg (by positivity)] at h
    linarith
  have hτM : ‖τ ε‖ ≤ (m : ℝ) + 1 := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε.1] at h
    exact h.trans (by linarith [hε.2])
  have hsub := norm_quantization_twist_halfline_sub hW hC hF ω hτre0 hτ1 (B := -2) le_rfl
  have he : Real.exp (-(2 * ((τ ε).re / ‖τ ε‖))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg (by norm_num) (div_nonneg hτre0.le (norm_nonneg _)))
  have hbound : quantizationContourBound (Real.exp (|ω| / 2) * C) (1 / 2) (τ ε) (-2) ≤ K := by
    simp only [quantizationContourBound, abs_neg, abs_two]
    dsimp [K]
    norm_num only [show (1 + 2 : ℝ) = 3 by norm_num]
    calc _ ≤ Real.exp (|ω| / 2) * C * 3 ^ (1 / 2 : ℝ) *
        (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1) * 1) := by gcongr
      _ = _ := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
  exact mul_le_mul_of_nonneg_left (hsub.trans hbound) hε.1.le

/-- The actual right edge retains every shifted arithmetic resonance. -/
theorem tendsto_quantization_right_resonance {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (ω : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ =>
      (ε : ℂ) * (∫ y in Iic (-2 : ℝ), linTwist ω (edgePt y) *
        edgeIntegrand (quantizationCompletion hW) ((ε : ℂ) + (m : ℂ) * I) (edgePt y)) -
      quantizationFrequencyResidue lam ω m * ((ε : ℂ) *
        ∫ y in Iic (-2 : ℝ), (m : ℂ) ^ (-edgePt y) *
          offKernel ((ε : ℂ) + (m : ℂ) * I) (edgePt y)))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  let a := dirichletExp (lamLog lam)
  have hsl := fun σ hσ => WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW (σ := σ) hσ
  have hid := fun s hs => quantizationContinuation_eq_arch hW (s := s) hs
  have hGd := fun s hs => hasDerivAt_quantizationCompletion hW (s := s) hs
  have hG2 := quantizationCompletion_two hW
  have ha : Summable fun n => ‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) n‖ :=
    summable_quantization_forward_terms hW
  have hlim := tendsto_quantization_nonresonant_edge_sum ha ω hm (B := -2) (by norm_num)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
  have hτre : 0 < τ.re := by simpa [τ] using hε
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have him : τ.im = m := by simp [τ]
    rw [him, abs_of_nonneg (by positivity)] at h
    linarith
  have hs := (hasSum_twEdgeTerm hsl hid hGd hG2 ω hτre hτ1
    (B := -2) (by norm_num)).mul_left (ε : ℂ)
  simp only [edgeIntegrand_twistG] at hs
  by_cases hex : ∃ n : ℕ, quantizationFrequencyResonates ω m n
  · obtain ⟨n, hn⟩ := hex
    have heq : ∀ k : ℕ, (1 ≤ k ∧ Real.log k + ω / 2 = Real.log m) ↔ k = n := by
      intro k
      constructor
      · exact fun hk => quantizationFrequencyResonates_unique hk hn
      · intro hk; subst k; exact hn
    simp_rw [heq]
    rw [(hasSum_ite_sub_hasSum hs n).tsum_eq,
      quantizationFrequencyResidue_eq hn,
      quantization_twEdgeTerm_resonant _ hm hn.1 hn.2]
    ring
  · have hnone : ∀ n : ℕ, ¬(1 ≤ n ∧ Real.log n + ω / 2 = Real.log m) :=
      fun n hn => hex ⟨n, hn⟩
    simp only [hnone, if_false, quantizationFrequencyResidue, dif_neg hex,
      zero_mul, sub_zero]
    exact hs.tsum_eq

/-- An unconditional resonance law for the actual measurable source trace. -/
theorem tendsto_quantization_trace_resonance {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (ω : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun ε : ℝ =>
      (ε : ℂ) * (∫ y in Iic (-2 : ℝ), linTwist ω (((1 / 2 : ℝ) : ℂ) + y * I) *
        (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (m : ℂ) * I))) -
      quantizationFrequencyResidue lam ω m * ((ε : ℂ) *
        ∫ y in Iic (-2 : ℝ), (m : ℂ) ^ (-edgePt y) *
          offKernel ((ε : ℂ) + (m : ℂ) * I) (edgePt y)))
      (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_quantization_twist_contour_displacement hW ω hm).add
    (tendsto_quantization_right_resonance hW ω hm)
  simpa only [mul_sub, sub_add_sub_cancel, zero_add] using h

/-- The common right-edge kernel, with radial normalization. -/
def quantizationMainRadial (m : ℕ) (ε : ℝ) : ℂ :=
  (ε : ℂ) * ∫ y in Iic (-2 : ℝ), (m : ℂ) ^ (-edgePt y) *
    offKernel ((ε : ℂ) + (m : ℂ) * I) (edgePt y)

/-- Scaling removes the arithmetic index from the common radial kernel. -/
theorem quantizationMainRadial_scale {m : ℕ} (hm : 1 ≤ m) (ε : ℝ) :
    quantizationMainRadial m ε = quantizationMainRadial 1 (ε / m) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hτ0 : (((ε / m : ℝ) : ℂ) + I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
  have hτ : (ε : ℂ) + (m : ℂ) * I = (m : ℂ) * (((ε / m : ℝ) : ℂ) + I) := by
    push_cast
    field_simp
  unfold quantizationMainRadial
  simp only [Nat.cast_one, Complex.one_cpow, one_mul]
  rw [hτ]
  simp_rw [natCast_cpow_mul_offKernel_scale hm hτ0]
  rw [integral_const_mul]
  push_cast
  ring

/-- The common radial kernel remains bounded up to the critical edge. -/
theorem exists_bound_quantizationMainRadial {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖quantizationMainRadial m ε‖ ≤ K := by
  let a : ℕ → ℂ := fun _ => 1
  refine ⟨‖LSeries.term a (((3 / 2 : ℝ) : ℂ)) m‖ *
    (4 * Real.pi ^ (3 / 4 : ℝ) * ((m : ℝ) + 1) ^ 2), by positivity,
    fun ε hε hε1 => ?_⟩
  have h := norm_quantization_twEdgeTerm_radial_le a 0 hm hε hε1
    (B := -2) (by norm_num) m
  rw [quantization_twEdgeTerm_resonant a hm hm (by simp)] at h
  simpa [a, quantizationMainRadial] using h

end RHTower.WeilSpectral
