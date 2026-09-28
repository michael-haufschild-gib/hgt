import GaloisForLFunctions.RHTower.ThetaRenewalResonancePhase
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.HTGeometry.BoundedMultiplierNonclosedRange

/-!
# The nuclear boundary operator of the theta renewal loop

Along the positive simple critical ordinates `y_j` (`Ξ(2y_j) = 0`, `X'(y_j) ≠ 0`) the boundary
values `d_j = -X'(y_j)/v(y_j)` of the loop Pick kernel form an absolutely summable real sequence
(`|d_j| ≤ K e^{-y_j}/y_j`) with infinitely many entries of each sign. The diagonal operator
`diag(d_j)` on `ℓ²` is therefore trace class, injective, with dense but non-closed range and no
lower bound. The inverse loop `1/(1 - K)` has at `λ = i y_j` the residue `1/d_j`; these residues
grow faster than every power of `y_j`, take both signs above every height, and are not summable.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open scoped ComplexConjugate

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The positive simple critical ordinates and the boundary diagonal -/

/-- The positive simple critical ordinates `y_j > 0`, `Ξ(2y_j) = 0`, `X'(y_j) ≠ 0`. -/
def thetaSimpleOrdinates : Set ℝ := {y | 0 < y ∧ Xi (2 * y) = 0 ∧ thetaLoopSlope y ≠ 0}

/-- The boundary diagonal `d_j = -X'(y_j)/v(y_j)` on the simple ordinates. -/
def thetaBoundaryDiagonal (j : thetaSimpleOrdinates) : ℝ := thetaLoopBoundaryValue j

theorem thetaBoundaryDiagonal_ne_zero (j : thetaSimpleOrdinates) : thetaBoundaryDiagonal j ≠ 0 := by
  obtain ⟨hy0, -, hs⟩ := j.2
  have hv := thetaLoopCharge_pos hy0
  rw [thetaBoundaryDiagonal, thetaLoopBoundaryValue]
  exact div_ne_zero (neg_ne_zero.mpr hs) hv.ne'

/-- The ordinate `2y_j` is an `XiC`-zero, hence a spectral point of the xi divisor. -/
theorem exists_xiZeroCopy_of_ordinate (j : thetaSimpleOrdinates) :
    ∃ q : XiZeroCopy, xiSpectralPoint q = ((2 * (j : ℝ) : ℝ) : ℂ) := by
  rw [← XiC_eq_zero_iff_exists_xiZeroCopy, XiC_ofReal, j.2.2.1, ofReal_zero]

/-- A choice of divisor copy for each ordinate; injective. -/
def thetaOrdinateCopy (j : thetaSimpleOrdinates) : XiZeroCopy :=
  (exists_xiZeroCopy_of_ordinate j).choose

theorem xiSpectralPoint_thetaOrdinateCopy (j : thetaSimpleOrdinates) :
    xiSpectralPoint (thetaOrdinateCopy j) = ((2 * (j : ℝ) : ℝ) : ℂ) :=
  (exists_xiZeroCopy_of_ordinate j).choose_spec

theorem thetaOrdinateCopy_injective : Function.Injective thetaOrdinateCopy := by
  intro i j h
  have := congrArg xiSpectralPoint h
  rw [xiSpectralPoint_thetaOrdinateCopy, xiSpectralPoint_thetaOrdinateCopy] at this
  have h2 : 2 * (i : ℝ) = 2 * (j : ℝ) := by exact_mod_cast this
  exact Subtype.ext (by linarith)

/-- Only finitely many simple ordinates lie below any height. -/
theorem finite_thetaSimpleOrdinates_le (Y : ℝ) :
    {j : thetaSimpleOrdinates | (j : ℝ) ≤ Y}.Finite := by
  have hY : 0 < 2 * max Y 1 := by positivity
  have hfin : {q : XiZeroCopy | 1 / (2 * max Y 1) ^ 2 ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)}.Finite := by
    have h := xiSpectralPoint_inv_sq_summable.tendsto_cofinite_zero.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * max Y 1) ^ 2))
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun q hq => ?_
    simp only [mem_setOf_eq, not_lt] at hq ⊢
    exact hq
  refine (hfin.preimage (thetaOrdinateCopy_injective.injOn)).subset fun j hj => ?_
  simp only [mem_preimage, mem_setOf_eq]
  have hj0 : 0 < (j : ℝ) := j.2.1
  rw [xiSpectralPoint_thetaOrdinateCopy, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]
  have hjY : (j : ℝ) ≤ max Y 1 := le_trans hj (le_max_left _ _)
  gcongr

/-- Decay of the boundary diagonal: `|d(y)| ≤ K e^{-y}/y` for large `y`. -/
theorem exists_abs_thetaLoopBoundaryValue_le :
    ∃ K Y₁ : ℝ, 0 ≤ K ∧ 1 ≤ Y₁ ∧ ∀ y, Y₁ ≤ y →
      |thetaLoopBoundaryValue y| ≤ K * Real.exp (-y) / y := by
  have hc := thetaSeam_pos
  obtain ⟨C₂, hC₂, hXi'⟩ := exists_abs_deriv_Xi_le (δ := 1 / 2) (by norm_num)
    (by linarith [Real.pi_gt_three])
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp eventually_thetaLoopCharge_ge
  refine ⟨4 * C₂ / Θ 1, max Y₁ 1, by positivity, le_max_right _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : 0 < y := by linarith
  have hv := hY₁ y (le_trans (le_max_left _ _) hy)
  have hvpos := thetaLoopCharge_pos hy0
  have hd := hXi' (2 * y)
  rw [abs_of_pos (by linarith : 0 < 2 * y), show 1 / 2 * (2 * y) = y by ring] at hd
  rw [thetaLoopBoundaryValue, thetaLoopSlope_eq_deriv, abs_div, abs_neg, abs_mul, abs_two,
    abs_of_pos hvpos, div_le_iff₀ hvpos]
  calc 2 * |deriv Xi (2 * y)| ≤ 2 * (C₂ * Real.exp (-y)) := by gcongr
    _ = 4 * C₂ / Θ 1 * Real.exp (-y) / y * (Θ 1 / 2 * y) := by field_simp; ring
    _ ≤ 4 * C₂ / Θ 1 * Real.exp (-y) / y * thetaLoopCharge y := by gcongr

/-- **(15), trace class.** `∑_j |d_j| < ∞`. -/
theorem summable_abs_thetaBoundaryDiagonal : Summable fun j => |thetaBoundaryDiagonal j| := by
  obtain ⟨K, Y₁, hK, hY₁, hb⟩ := exists_abs_thetaLoopBoundaryValue_le
  have hg0 : Summable fun j : thetaSimpleOrdinates =>
      1 / ‖xiSpectralPoint (thetaOrdinateCopy j)‖ ^ (2 : ℕ) :=
    xiSpectralPoint_inv_sq_summable.comp_injective thetaOrdinateCopy_injective
  have hg : Summable fun j : thetaSimpleOrdinates =>
      4 * K * (1 / ‖xiSpectralPoint (thetaOrdinateCopy j)‖ ^ (2 : ℕ)) := hg0.mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  refine (finite_thetaSimpleOrdinates_le Y₁).subset fun j hj => ?_
  simp only [mem_setOf_eq] at hj ⊢
  by_contra hlt
  rw [not_le] at hlt
  apply hj
  have hy0 : 0 < (j : ℝ) := j.2.1
  have h2j : ‖xiSpectralPoint (thetaOrdinateCopy j)‖ = 2 * (j : ℝ) := by
    rw [xiSpectralPoint_thetaOrdinateCopy, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  rw [Real.norm_eq_abs, abs_abs, h2j, thetaBoundaryDiagonal]
  refine (hb j hlt.le).trans ?_
  have hE : Real.exp (-(j : ℝ)) ≤ 1 / (j : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hy0 (by linarith [Real.add_one_le_exp (j : ℝ)])
  calc K * Real.exp (-(j : ℝ)) / (j : ℝ) ≤ K * (1 / (j : ℝ)) / (j : ℝ) := by gcongr
    _ = 4 * K * (1 / (2 * (j : ℝ)) ^ 2) := by field_simp; ring

/-- `d_j → 0` along the ordinates. -/
theorem tendsto_thetaBoundaryDiagonal : Tendsto thetaBoundaryDiagonal cofinite (𝓝 0) := by
  have h := summable_abs_thetaBoundaryDiagonal.tendsto_cofinite_zero
  rw [tendsto_zero_iff_abs_tendsto_zero]; exact h

/-- **(15).** Infinitely many diagonal entries of each sign. -/
theorem infinite_thetaBoundaryDiagonal_sign {s : ℝ} (hs : s = 1 ∨ s = -1) :
    {j : thetaSimpleOrdinates | 0 < s * thetaBoundaryDiagonal j}.Infinite := by
  have hZ := infinite_zeros_boundaryValue_sign hs
  have himg : ((↑) : thetaSimpleOrdinates → ℝ) ''
      {j : thetaSimpleOrdinates | 0 < s * thetaBoundaryDiagonal j} =
      {y : ℝ | 0 < y ∧ Xi (2 * y) = 0 ∧ 0 < s * thetaLoopBoundaryValue y} := by
    ext y
    simp only [mem_image, mem_setOf_eq, thetaBoundaryDiagonal]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2.1, j.2.2.1, hj⟩
    · rintro ⟨hy0, hXi, hd⟩
      refine ⟨⟨y, hy0, hXi, fun h0 => ?_⟩, hd, rfl⟩
      rw [thetaLoopBoundaryValue, h0, neg_zero, zero_div, mul_zero] at hd
      exact lt_irrefl 0 hd
  intro hfin
  exact hZ (himg ▸ hfin.image _)

/-! ## The boundary operator `T e_j = d_j e_j` on `ℓ²` of the ordinates -/

instance : Countable thetaSimpleOrdinates := thetaOrdinateCopy_injective.countable

theorem infinite_thetaSimpleOrdinates : (univ : Set thetaSimpleOrdinates).Infinite := by
  intro h
  exact infinite_thetaBoundaryDiagonal_sign (s := 1) (Or.inl rfl) (h.subset (subset_univ _))

/-- The trace norm bound `D = ∑ |d_j|`. -/
def thetaBoundaryTraceNorm : ℝ := ∑' j, |thetaBoundaryDiagonal j|

theorem abs_thetaBoundaryDiagonal_le (j : thetaSimpleOrdinates) :
    ‖((thetaBoundaryDiagonal j : ℝ) : ℂ)‖ ≤ thetaBoundaryTraceNorm := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact summable_abs_thetaBoundaryDiagonal.le_tsum j fun _ _ => abs_nonneg _

theorem thetaBoundaryTraceNorm_nonneg : 0 ≤ thetaBoundaryTraceNorm :=
  tsum_nonneg fun _ => abs_nonneg _

theorem measurable_thetaBoundaryDiagonal :
    Measurable fun j : thetaSimpleOrdinates => ((thetaBoundaryDiagonal j : ℝ) : ℂ) :=
  measurable_of_countable _

/-- **(15).** The diagonal operator `T e_j = d_j e_j` on `ℓ²` of the simple ordinates. -/
def thetaBoundaryOperator :
    Lp ℂ 2 (Measure.count : Measure thetaSimpleOrdinates) →L[ℂ]
      Lp ℂ 2 (Measure.count : Measure thetaSimpleOrdinates) :=
  lpBoundedMulCLM measurable_thetaBoundaryDiagonal thetaBoundaryTraceNorm_nonneg
    abs_thetaBoundaryDiagonal_le

theorem thetaBoundaryOperator_coeFn (f : Lp ℂ 2 (Measure.count : Measure thetaSimpleOrdinates)) :
    ((thetaBoundaryOperator f : Lp ℂ 2 _) : thetaSimpleOrdinates → ℂ) =ᵐ[Measure.count]
      fun j => ((thetaBoundaryDiagonal j : ℝ) : ℂ) * (f : thetaSimpleOrdinates → ℂ) j :=
  lpBoundedMulCLM_coeFn _ _ _ f

/-- **(15).** `T` is injective. -/
theorem thetaBoundaryOperator_injective : Function.Injective thetaBoundaryOperator :=
  GaloisForLFunctions.HTGeometry.lpBoundedMulCLM_injective_general _ _ _ fun j => by
    exact_mod_cast thetaBoundaryDiagonal_ne_zero j

/-- **(15).** `T` has dense range. -/
theorem thetaBoundaryOperator_denseRange : DenseRange thetaBoundaryOperator :=
  GaloisForLFunctions.HTGeometry.denseRange_lpBoundedMulCLM _ _ _
    (fun j => Complex.conj_ofReal _) fun j => by exact_mod_cast thetaBoundaryDiagonal_ne_zero j

/-- **(15).** The range of `T` is not closed. -/
theorem not_isClosed_range_thetaBoundaryOperator :
    ¬ IsClosed (Set.range thetaBoundaryOperator) := by
  refine GaloisForLFunctions.HTGeometry.not_isClosed_range_lpBoundedMulCLM _ _ _
    thetaBoundaryOperator_injective fun c hc => ?_
  have hfin : {j : thetaSimpleOrdinates | c < |thetaBoundaryDiagonal j|}.Finite := by
    have h := summable_abs_thetaBoundaryDiagonal.tendsto_cofinite_zero.eventually
      (gt_mem_nhds hc)
    rw [Filter.eventually_cofinite] at h
    exact h.subset fun j hj => by
      simp only [mem_setOf_eq, not_lt]; exact le_of_lt hj
  obtain ⟨j₀, -, hj₀⟩ := (infinite_thetaSimpleOrdinates.sdiff hfin).nonempty
  refine ⟨{j₀}, measurableSet_singleton _, by simp, by simp, ?_⟩
  refine Eventually.of_forall fun j hj => ?_
  rw [mem_singleton_iff.mp hj, Complex.norm_real, Real.norm_eq_abs]
  simpa [not_lt] using hj₀

/-- **(15).** `T` is not bounded below: its inverse on the range is unbounded. -/
theorem not_exists_lowerBound_thetaBoundaryOperator :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ f, C * ‖f‖ ≤ ‖thetaBoundaryOperator f‖ := by
  rintro ⟨C, hC, hbd⟩
  apply not_isClosed_range_thetaBoundaryOperator
  have hanti := thetaBoundaryOperator.antilipschitz_of_bound (K := ⟨C⁻¹, by positivity⟩)
    fun f => by
      change ‖f‖ ≤ C⁻¹ * ‖thetaBoundaryOperator f‖
      rw [le_inv_mul_iff₀ hC]; exact hbd f
  exact hanti.isClosed_range thetaBoundaryOperator.uniformContinuous

/-! ## The inverse loop (16) -/

/-- **(16).** At each positive simple critical zero the inverse loop `1/(1 + K)` has a simple
pole with residue exactly `1/d_j`. -/
theorem tendsto_residue_thetaInverseLoop (j : thetaSimpleOrdinates) :
    Tendsto (fun lam => (lam - (j : ℝ) * I) * (1 / (1 + thetaLoopK lam)))
      (𝓝[≠] (((j : ℝ) : ℂ) * I)) (𝓝 ((1 / thetaBoundaryDiagonal j : ℝ) : ℂ)) := by
  rcases j with ⟨y, hy0, hXi, hs⟩
  set lj : ℂ := (y : ℂ) * I
  set f : ℂ → ℂ := fun lam => XiC (2 * I * lam)
  have hf0 : f lj = 0 := by
    simp only [f, lj]
    rw [show 2 * I * ((y : ℂ) * I) = -((2 * y : ℝ) : ℂ) by
      push_cast; linear_combination (2 * (y : ℂ)) * I_sq, XiC_even, XiC_ofReal, hXi, ofReal_zero]
  set f' : ℂ := -(I * (thetaLoopSlope y : ℂ))
  have hf : HasDerivAt f f' lj := by
    have h := (XiC_differentiable (2 * I * lj)).hasDerivAt.comp lj
      ((hasDerivAt_id lj).const_mul (2 * I))
    refine h.congr_deriv ?_
    rw [show 2 * I * lj = -((2 * y : ℝ) : ℂ) by
      simp only [lj]; push_cast; linear_combination (2 * (y : ℂ)) * I_sq, deriv_XiC_neg,
      ← deriv_Xi_eq_re]
    simp only [f', thetaLoopSlope_eq_deriv, mul_one]
    push_cast; ring
  have hf'0 : f' ≠ 0 := by
    refine neg_ne_zero.mpr (mul_ne_zero I_ne_zero ?_)
    exact_mod_cast hs
  have hslope := hasDerivAt_iff_tendsto_slope.mp hf
  have hA : ContinuousAt thetaLoopA lj := differentiable_thetaLoopA.continuous.continuousAt
  have hAv : thetaLoopA lj = (thetaLoopCharge y : ℂ) * I := by
    apply Complex.ext
    · simp only [lj, re_thetaLoopA_I_mul, hXi]; simp
    · simp [lj, thetaLoopCharge]
  have hlim : Tendsto (fun lam => thetaLoopA lam / slope f lj lam) (𝓝[≠] lj)
      (𝓝 (thetaLoopA lj / f')) :=
    (hA.tendsto.mono_left nhdsWithin_le_nhds).div hslope hf'0
  have hval : thetaLoopA lj / f' = ((1 / thetaLoopBoundaryValue y : ℝ) : ℂ) := by
    have hv := thetaLoopCharge_pos hy0
    rw [hAv, thetaLoopBoundaryValue]
    simp only [f']
    push_cast
    have hs' : (thetaLoopSlope y : ℂ) ≠ 0 := by exact_mod_cast hs
    have hv' : (thetaLoopCharge y : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  have hnear : ∀ᶠ lam in 𝓝[≠] lj, |lam.re| < 1 / 4 := by
    have hc : ContinuousAt (fun lam : ℂ => |lam.re|) lj := by fun_prop
    have h0 : |lj.re| < 1 / 4 := by simp [lj]
    exact nhdsWithin_le_nhds (hc.eventually (gt_mem_nhds h0))
  filter_upwards [hnear, self_mem_nhdsWithin] with lam hlam hne
  have hA0 := thetaLoopA_ne_zero hlam
  have hsub : lam - lj ≠ 0 := sub_ne_zero.mpr hne
  have hloop : 1 + thetaLoopK lam = f lam / thetaLoopA lam := by
    rw [XiC_two_I_mul_eq_loop hlam |> fun h => (show f lam = _ from h), mul_div_cancel_left₀ _ hA0]
  rw [slope_def_field, hf0, sub_zero, hloop, one_div_div]
  field_simp

/-- **(16), growth.** The residues `1/d_j` grow faster than every power of the ordinate. -/
theorem exists_pow_le_abs_inv_thetaBoundaryDiagonal (N : ℕ) :
    ∃ Y : ℝ, ∀ j : thetaSimpleOrdinates, Y ≤ (j : ℝ) →
      (j : ℝ) ^ N ≤ |1 / thetaBoundaryDiagonal j| := by
  obtain ⟨K, Y₁, hK, hY₁, hb⟩ := exists_abs_thetaLoopBoundaryValue_le
  have hlim := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  obtain ⟨Y₂, hY₂⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds
    (by positivity : (0 : ℝ) < 1 / (K + 1))))
  refine ⟨max Y₁ (max Y₂ 1), fun j hj => ?_⟩
  have hy1 : 1 ≤ (j : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hj
  have hy0 : 0 < (j : ℝ) := by linarith
  have hd := hb j (le_trans (le_max_left _ _) hj)
  have hdne := thetaBoundaryDiagonal_ne_zero j
  have hdpos : 0 < |thetaBoundaryDiagonal j| := abs_pos.mpr hdne
  have hp := hY₂ j (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hj)
  have hE := Real.exp_pos (-(j : ℝ))
  rw [abs_div, abs_one, le_div_iff₀ hdpos]
  change (j : ℝ) ^ N * |thetaLoopBoundaryValue j| ≤ 1
  calc (j : ℝ) ^ N * |thetaLoopBoundaryValue j| ≤ (j : ℝ) ^ N * (K * Real.exp (-(j : ℝ)) / j) := by
        gcongr
    _ ≤ (j : ℝ) ^ N * (K * Real.exp (-(j : ℝ))) :=
        mul_le_mul_of_nonneg_left (div_le_self (by positivity) hy1) (by positivity)
    _ = K * ((j : ℝ) ^ N * Real.exp (-(j : ℝ))) := by ring
    _ ≤ (K + 1) * (1 / (K + 1)) := by
        gcongr
        linarith
    _ = 1 := by field_simp

/-- **(16), signs.** Residues `1/d_j` of either sign occur above every height. -/
theorem exists_inv_thetaBoundaryDiagonal_sign_above {s : ℝ} (hs : s = 1 ∨ s = -1) (Y : ℝ) :
    ∃ j : thetaSimpleOrdinates, Y < (j : ℝ) ∧ 0 < s * (1 / thetaBoundaryDiagonal j) := by
  obtain ⟨j, hj, hjY⟩ := ((infinite_thetaBoundaryDiagonal_sign hs).sdiff
    (finite_thetaSimpleOrdinates_le Y)).nonempty
  simp only [Set.mem_setOf_eq, not_le] at hj hjY
  refine ⟨j, hjY, ?_⟩
  have hd := thetaBoundaryDiagonal_ne_zero j
  have : s * (1 / thetaBoundaryDiagonal j) = (s * thetaBoundaryDiagonal j) /
      thetaBoundaryDiagonal j ^ 2 := by field_simp
  rw [this]
  exact div_pos hj (by positivity)

/-- **(16).** No unweighted sum of the inverse-loop residues converges. -/
theorem not_summable_inv_thetaBoundaryDiagonal :
    ¬ Summable fun j : thetaSimpleOrdinates => 1 / thetaBoundaryDiagonal j := by
  intro hsum
  obtain ⟨Y, hY⟩ := exists_pow_le_abs_inv_thetaBoundaryDiagonal 0
  have hfin : {j : thetaSimpleOrdinates | ¬ |1 / thetaBoundaryDiagonal j| < 1}.Finite := by
    have h := hsum.tendsto_cofinite_zero
    rw [tendsto_zero_iff_abs_tendsto_zero] at h
    exact Filter.eventually_cofinite.mp (h.eventually (gt_mem_nhds one_pos))
  have hbig : {j : thetaSimpleOrdinates | Y < (j : ℝ)} ⊆
      {j : thetaSimpleOrdinates | ¬ |1 / thetaBoundaryDiagonal j| < 1} := fun j hj => by
    have := hY j (le_of_lt hj)
    simp only [pow_zero] at this
    simpa [not_lt] using this
  have hinf : {j : thetaSimpleOrdinates | Y < (j : ℝ)}.Infinite := by
    have h := infinite_thetaSimpleOrdinates.sdiff (finite_thetaSimpleOrdinates_le Y)
    refine h.mono fun j hj => ?_
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_le] at hj
    exact hj.2
  exact hinf (hfin.subset hbig)

end

end RHTower
