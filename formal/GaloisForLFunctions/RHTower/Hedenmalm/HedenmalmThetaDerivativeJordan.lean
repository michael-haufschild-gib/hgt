import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmShiftedSourceEquation
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaZeroHistoryNoGo
import GaloisForLFunctions.RHTower.ThetaPowerWeightedDerivativeHistory
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullDerivativeExponentialMoments

/-!
# Actual theta derivatives and both zero-Jordan chains

The literal complete-source derivatives belong to `L²(k⁻¹ dx)`. Their Lebesgue
integrals and two-ended limits identify their pinned primitives exactly. The
actual quantile inverse lowers this derivative family with coefficient `i`.
Orthogonal scalar removal retains a second infinite Jordan chain, dense range,
and an injective adjoint, obstructing every bounded injective symmetrizer.
The full and centered families are linearly independent; the full closed
history is invariant under the actual compact source inverse.
-/

open MeasureTheory Filter Set Topology Complex

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry HedenmalmQuantile HedenmalmHilbertSchmidt
  HedenmalmClosedWeightedDerivative

noncomputable section

attribute [local instance 2000] Real.measurableSpace
attribute [local instance 2000] NormedSpace.complexToReal

private abbrev H := Lp ℂ 2 unitIntervalMeasure
private abbrev HS := SourceSpace thetaSource
private abbrev μS := volume.withDensity (realDensity (sourceWeight thetaSource))

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The literal ordinary derivative, in complex source coordinates. -/
def thetaSourceDerivativeFunction (n : ℕ) (x : ℝ) : ℂ :=
  ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)

theorem continuous_thetaSourceDerivativeFunction (n : ℕ) :
    Continuous (thetaSourceDerivativeFunction n) :=
  Complex.continuous_ofReal.comp
    (contDiff_thetaCuspFullSource.continuous_iteratedDeriv n
      (by exact_mod_cast (ENat.coe_lt_top n).le))

theorem hasDerivAt_thetaSourceDerivativeFunction (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaSourceDerivativeFunction n) (thetaSourceDerivativeFunction (n + 1) x) x := by
  change HasDerivAt (fun y : ℝ => ((iteratedDeriv n thetaCuspFullSource y : ℝ) : ℂ))
    ((iteratedDeriv (n + 1) thetaCuspFullSource x : ℝ) : ℂ) x
  have h := (contDiff_thetaCuspFullSource.differentiable_iteratedDeriv n
    (by exact_mod_cast (ENat.coe_lt_top n)) x).hasDerivAt
  simpa only [← iteratedDeriv_succ] using h.ofReal_comp

theorem integrable_thetaSourceDerivativeFunction (n : ℕ) :
    Integrable (thetaSourceDerivativeFunction n) := by
  apply (integrable_norm_iff (continuous_thetaSourceDerivativeFunction n).aestronglyMeasurable).mp
  simpa [thetaSourceDerivativeFunction, Complex.norm_real, Real.norm_eq_abs] using
    integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource n 0

theorem thetaSourceDerivativeFunction_tendsto_atBot (n : ℕ) :
    Tendsto (thetaSourceDerivativeFunction n) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : ∀ᶠ x : ℝ in atBot,
      ‖thetaSourceDerivativeFunction n x‖ ≤
        finitePrimeThetaCuspWeightedDerivativeConstant n 0 * Real.exp x := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with x hx
    simpa [thetaSourceDerivativeFunction, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos hx] using exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource_le n 0 0 x
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hb
    (by simpa using (Real.tendsto_exp_atBot.const_mul
      (finitePrimeThetaCuspWeightedDerivativeConstant n 0)))

theorem thetaSourceDerivativeFunction_tendsto_atTop (n : ℕ) :
    Tendsto (thetaSourceDerivativeFunction n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : ∀ᶠ x : ℝ in atTop,
      ‖thetaSourceDerivativeFunction n x‖ ≤
        finitePrimeThetaCuspWeightedDerivativeConstant n 0 * Real.exp (-x) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simpa [thetaSourceDerivativeFunction, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx] using exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource_le n 0 0 x
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hb
    (by simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (finitePrimeThetaCuspWeightedDerivativeConstant n 0)))

theorem integral_thetaSourceDerivativeFunction_succ (n : ℕ) :
    (∫ x, thetaSourceDerivativeFunction (n + 1) x) = 0 :=
  integral_eq_zero_of_hasDerivAt_of_integrable
    (hasDerivAt_thetaSourceDerivativeFunction n)
    (integrable_thetaSourceDerivativeFunction (n + 1))
    (integrable_thetaSourceDerivativeFunction n)

theorem integral_Iic_thetaSourceDerivativeFunction_succ (n : ℕ) (x : ℝ) :
    (∫ y in Iic x, thetaSourceDerivativeFunction (n + 1) y) =
      thetaSourceDerivativeFunction n x := by
  simpa using integral_Iic_of_hasDerivAt_of_tendsto'
    (fun y _ => hasDerivAt_thetaSourceDerivativeFunction n y)
    (integrable_thetaSourceDerivativeFunction (n + 1)).integrableOn
    (thetaSourceDerivativeFunction_tendsto_atBot n)

theorem sourceInverse_thetaSourceDerivativeFunction_succ (n : ℕ) (x : ℝ) :
    sourceInverse thetaSource (thetaSourceDerivativeFunction (n + 1)) x =
      Complex.I * thetaSourceDerivativeFunction n x := by
  rw [sourceInverse, integral_thetaSourceDerivativeFunction_succ]
  simp only [zero_div, zero_mul, sub_zero]
  rw [integral_Iic_thetaSourceDerivativeFunction_succ]

theorem thetaSourceDerivativeFunction_memLp (n : ℕ) :
    MemLp (thetaSourceDerivativeFunction n) 2 μS := by
  change MemLp (fun x : ℝ => ((iteratedDeriv n thetaCuspFullSource x : ℝ) : ℂ)) 2
    (volume.withDensity (realDensity (sourceWeight thetaSource)))
  convert! thetaWeightedDerivative_memLp 1 (by norm_num) (by norm_num) n using 1
  congr 1
  funext x
  simp only [realDensity, sourceWeight, thetaSource_k]
  norm_num [Real.rpow_neg_one]

def thetaSourceDerivativeVector (n : ℕ) : HS :=
  (thetaSourceDerivativeFunction_memLp n).toLp (thetaSourceDerivativeFunction n)

theorem thetaSourceDerivativeVector_coe (n : ℕ) :
    (thetaSourceDerivativeVector n : ℝ → ℂ) =ᵐ[volume] thetaSourceDerivativeFunction n :=
  (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mp (thetaSourceDerivativeFunction_memLp n).coeFn_toLp

/-- Actual derivative vectors transported by the source's quantile unitary. -/
def thetaQuantileDerivativeVector (n : ℕ) : H :=
  quantileUnitary thetaSource (thetaSourceDerivativeVector n)

theorem thetaQuantileDerivativeVector_succ_mem_centered (n : ℕ) :
    thetaQuantileDerivativeVector (n + 1) ∈ thetaCentered := by
  rw [mem_thetaCentered_iff, thetaQuantileDerivativeVector, pinnedMean_quantileUnitary,
    integral_quantileTransform thetaSource
      (integrable_sourceSpace thetaSource _).aestronglyMeasurable,
    integral_congr_ae (thetaSourceDerivativeVector_coe (n + 1)),
    integral_thetaSourceDerivativeFunction_succ, zero_div]

theorem thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ (n : ℕ) :
    thetaCompactSourceInverse (thetaQuantileDerivativeVector (n + 1)) =
      Complex.I • thetaQuantileDerivativeVector n := by
  apply (quantileUnitary thetaSource).symm.injective
  have h := sourceInverse_ae_eq_quantileSymm_thetaCompactSourceInverse
    (thetaQuantileDerivativeVector (n + 1))
  have h' : sourceInverse thetaSource (fun x => thetaSourceDerivativeVector (n + 1) x)
      =ᵐ[volume] fun x => ((quantileUnitary thetaSource).symm
        (thetaCompactSourceInverse (thetaQuantileDerivativeVector (n + 1)))) x := by
    simpa [thetaQuantileDerivativeVector] using h
  have hsmul : ((Complex.I • thetaSourceDerivativeVector n : HS) : ℝ → ℂ)
      =ᵐ[volume] fun x => Complex.I * thetaSourceDerivativeFunction n x := by
    have hs := (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
      (sourceWeight_pos thetaSource)).mp (Lp.coeFn_smul Complex.I (thetaSourceDerivativeVector n))
    filter_upwards [hs, thetaSourceDerivativeVector_coe n] with x hx hdx
    simpa only [Pi.smul_apply, smul_eq_mul, hdx] using hx
  rw [map_smul]
  have hinv : (quantileUnitary thetaSource).symm (thetaQuantileDerivativeVector n) =
      thetaSourceDerivativeVector n := by simp [thetaQuantileDerivativeVector]
  rw [hinv]
  apply Lp.ext
  apply (withDensity_realDensity_ae_eq (measurable_sourceWeight thetaSource)
    (sourceWeight_pos thetaSource)).mpr
  filter_upwards [h', hsmul] with x hx hsx
  rw [← hx, hsx, sourceInverse_congr_ae thetaSource (thetaSourceDerivativeVector_coe (n + 1)),
    sourceInverse_thetaSourceDerivativeFunction_succ]


theorem thetaQuantileDerivativeVector_zero :
    thetaQuantileDerivativeVector 0 = (Real.sqrt thetaSource.mass : ℂ) • pinnedOne := by
  have hraw := (thetaSource.law_ae_eq).mpr (thetaSourceDerivativeVector_coe 0)
  have hQ := hraw.comp_tendsto
    (measurePreserving_quantile_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  apply Lp.ext
  filter_upwards [quantileUnitary_ae thetaSource (thetaSourceDerivativeVector 0), hQ,
    Lp.coeFn_smul (Real.sqrt thetaSource.mass : ℂ) pinnedOne, pinnedOne_coeFn]
    with t hU hQt hs hone
  change (quantileUnitary thetaSource (thetaSourceDerivativeVector 0) : ℝ → ℂ) t = _
  simp only [Function.comp_def] at hQt
  rw [hU, hQt, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hone]
  simp only [thetaSourceDerivativeFunction, iteratedDeriv_zero, thetaSource_k, mul_one]
  have hk : (thetaCuspFullSource (thetaSource.quantileFun t) : ℂ) ≠ 0 := by
    exact_mod_cast (thetaCuspFullSource_pos_all _).ne'
  field_simp

theorem thetaCompactSourceInverse_thetaQuantileDerivativeVector_zero :
    thetaCompactSourceInverse (thetaQuantileDerivativeVector 0) = 0 := by
  have hzero : thetaCompactSourceInverse pinnedOne = 0 := by
    change thetaKernelOperator pinnedOne = 0
    have hGinj : Function.Injective thetaMetricOperator :=
      metricOperator_injective thetaSource thetaMetricBound_nonneg norm_metricSymbol_thetaSource_le
    apply hGinj
    have h := congrArg (fun T : H →L[ℂ] H => T pinnedOne)
      thetaMetricOperator_mul_thetaKernelOperator
    simpa only [mul_apply_eq_comp, pinnedVolterraCLM_pinnedOne,
      map_zero, smul_apply, smul_zero] using h
  rw [thetaQuantileDerivativeVector_zero, map_smul, hzero, smul_zero]

theorem thetaQuantileDerivativeVector_ne_zero (n : ℕ) :
    thetaQuantileDerivativeVector n ≠ 0 := by
  induction n with
  | zero =>
      rw [thetaQuantileDerivativeVector_zero]
      exact smul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne')
        pinnedOne_ne_zero
  | succ n hn =>
      intro hzero
      have h := thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ n
      rw [hzero, map_zero] at h
      exact hn ((smul_eq_zero.mp h.symm).resolve_left Complex.I_ne_zero)

local instance : CompleteSpace thetaCentered := thetaCentered_isClosed.completeSpace_coe

/-- Orthogonal mean-zero quotient, identified with the closed mean-zero hyperplane. -/
def thetaOrthogonalCenteredInverse : thetaCentered →L[ℂ] thetaCentered :=
  thetaCentered.orthogonalProjectionOnto.comp thetaCenteredSourceInverse

/-- The actual derivative chain retained by the orthogonal scalar quotient. -/
def thetaCenteredDerivativeVector (n : ℕ) : thetaCentered :=
  ⟨thetaQuantileDerivativeVector (n + 1), thetaQuantileDerivativeVector_succ_mem_centered n⟩

theorem thetaCentered_orthogonalProjection_pinnedOne :
    thetaCentered.orthogonalProjectionOnto pinnedOne = 0 := by
  apply Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
  exact (Submodule.le_orthogonal_orthogonal (ℂ ∙ pinnedOne))
    (Submodule.mem_span_singleton_self pinnedOne)

theorem thetaOrthogonalCenteredInverse_thetaCenteredDerivativeVector_zero :
    thetaOrthogonalCenteredInverse (thetaCenteredDerivativeVector 0) = 0 := by
  change thetaCentered.orthogonalProjectionOnto
    (thetaCompactSourceInverse (thetaQuantileDerivativeVector (0 + 1))) = 0
  rw [thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ, map_smul,
    thetaQuantileDerivativeVector_zero, map_smul,
    thetaCentered_orthogonalProjection_pinnedOne, smul_zero, smul_zero]

theorem thetaOrthogonalCenteredInverse_thetaCenteredDerivativeVector_succ (n : ℕ) :
    thetaOrthogonalCenteredInverse (thetaCenteredDerivativeVector (n + 1)) =
      Complex.I • thetaCenteredDerivativeVector n := by
  change thetaCentered.orthogonalProjectionOnto
    (thetaCompactSourceInverse (thetaQuantileDerivativeVector ((n + 1) + 1))) = _
  rw [thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ, map_smul]
  congr 1
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (thetaCenteredDerivativeVector n)

theorem thetaCenteredDerivativeVector_ne_zero (n : ℕ) :
    thetaCenteredDerivativeVector n ≠ 0 := by
  intro hzero
  exact thetaQuantileDerivativeVector_ne_zero (n + 1)
    (congrArg (fun x : thetaCentered => (x : H)) hzero)

theorem thetaOrthogonalCenteredInverse_dense_range :
    Dense (thetaOrthogonalCenteredInverse.range : Set thetaCentered) := by
  have hB : DenseRange thetaCenteredSourceInverse := thetaCenteredSourceInverse_dense_range
  have hP : Function.Surjective thetaCentered.orthogonalProjectionOnto := by
    intro x
    exact ⟨(x : H), Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩
  exact hP.denseRange.comp hB thetaCentered.orthogonalProjectionOnto.continuous

theorem thetaOrthogonalCenteredInverse_adjoint_injective :
    Function.Injective thetaOrthogonalCenteredInverse.adjoint := by
  intro x y hxy
  apply thetaOrthogonalCenteredInverse_dense_range.eq_of_inner_left ℂ
  intro _ hk
  rcases hk with ⟨k, rfl⟩
  calc
    inner ℂ x (thetaOrthogonalCenteredInverse k) =
        inner ℂ (thetaOrthogonalCenteredInverse.adjoint x) k :=
      (thetaOrthogonalCenteredInverse.adjoint_inner_left k x).symm
    _ = inner ℂ (thetaOrthogonalCenteredInverse.adjoint y) k :=
      congrArg (fun z => inner ℂ z k) hxy
    _ = inner ℂ y (thetaOrthogonalCenteredInverse k) :=
      thetaOrthogonalCenteredInverse.adjoint_inner_left k y

/-- Dense range and the nonzero first derivative obstruct every bounded injective intertwiner. -/
theorem thetaOrthogonalCenteredInverse_no_injective_bounded_symmetrizer :
    ¬ ∃ G : thetaCentered →L[ℂ] thetaCentered,
      Function.Injective G ∧
        G.comp thetaOrthogonalCenteredInverse = thetaOrthogonalCenteredInverse.adjoint.comp G := by
  rintro ⟨G, hGinj, hsym⟩
  have heq := congrArg
    (fun T : thetaCentered →L[ℂ] thetaCentered => T (thetaCenteredDerivativeVector 0)) hsym
  have hzero : thetaOrthogonalCenteredInverse.adjoint (G (thetaCenteredDerivativeVector 0)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply,
      thetaOrthogonalCenteredInverse_thetaCenteredDerivativeVector_zero, map_zero] using heq.symm
  have hGzero : G (thetaCenteredDerivativeVector 0) = 0 :=
    thetaOrthogonalCenteredInverse_adjoint_injective (hzero.trans (map_zero _).symm)
  exact thetaCenteredDerivativeVector_ne_zero 0 (hGinj (hGzero.trans (map_zero _).symm))


theorem thetaCompactSourceInverse_pow_derivative_self (n : ℕ) :
    (thetaCompactSourceInverse ^ n) (thetaQuantileDerivativeVector n) =
      Complex.I ^ n • thetaQuantileDerivativeVector 0 := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ, mul_apply_eq_comp,
        thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ, map_smul,
        hn, smul_smul, pow_succ']

theorem thetaCompactSourceInverse_pow_derivative_eq_zero
    (n k : ℕ) (hk : n + 1 ≤ k) :
    (thetaCompactSourceInverse ^ k) (thetaQuantileDerivativeVector n) = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k hkrec =>
      cases n with
      | zero =>
          rw [pow_succ, mul_apply_eq_comp,
            thetaCompactSourceInverse_thetaQuantileDerivativeVector_zero, map_zero]
      | succ n =>
          rw [pow_succ, mul_apply_eq_comp,
            thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ, map_smul,
            hkrec n (by omega), smul_zero]

/-- Every finite part of the literal infinite zero-Jordan chain is linearly independent. -/
theorem linearIndependent_thetaQuantileDerivativeVector :
    LinearIndependent ℂ thetaQuantileDerivativeVector := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert n s hlt hs =>
      intro c hsum j hj
      have hn : n ∉ s := by
        intro hns
        exact (lt_irrefl n) (hlt n hns)
      have hpow := congrArg (fun f : H => (thetaCompactSourceInverse ^ n) f) hsum
      rw [Finset.sum_insert hn, map_add, map_smul, map_sum, map_zero,
        thetaCompactSourceInverse_pow_derivative_self] at hpow
      simp_rw [map_smul] at hpow
      have htail : (∑ i ∈ s, c i •
          (thetaCompactSourceInverse ^ n) (thetaQuantileDerivativeVector i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [thetaCompactSourceInverse_pow_derivative_eq_zero i n (by
          have := hlt i hi
          omega), smul_zero]
      rw [htail, add_zero] at hpow
      have hcn : c n = 0 := (smul_eq_zero.mp hpow).resolve_right
        (smul_ne_zero (pow_ne_zero n Complex.I_ne_zero) (thetaQuantileDerivativeVector_ne_zero 0))
      have hsump : (∑ i ∈ s, c i • thetaQuantileDerivativeVector i) = 0 := by
        simpa only [Finset.sum_insert hn, hcn, zero_smul, zero_add] using hsum
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact hcn
      · exact hs c hsump j hjs

theorem linearIndependent_thetaCenteredDerivativeVector :
    LinearIndependent ℂ thetaCenteredDerivativeVector := by
  have h : LinearIndependent ℂ (fun n => thetaQuantileDerivativeVector (n + 1)) :=
    linearIndependent_thetaQuantileDerivativeVector.comp (fun n => n + 1)
      (fun i j hij => Nat.add_right_cancel hij)
  exact LinearIndependent.of_comp thetaCentered.subtype h

/-- Closed derivative history in quantile coordinates. -/
def thetaQuantileDerivativeHistory : Submodule ℂ H :=
  (Submodule.span ℂ (range thetaQuantileDerivativeVector)).topologicalClosure

theorem thetaQuantileDerivativeVector_mem_history (n : ℕ) :
    thetaQuantileDerivativeVector n ∈ thetaQuantileDerivativeHistory :=
  (Submodule.span ℂ (range thetaQuantileDerivativeVector)).le_topologicalClosure
    (Submodule.subset_span ⟨n, rfl⟩)

theorem thetaQuantileDerivativeHistory_invariant {f : H}
    (hf : f ∈ thetaQuantileDerivativeHistory) :
    thetaCompactSourceInverse f ∈ thetaQuantileDerivativeHistory := by
  let S : Submodule ℂ H := Submodule.span ℂ (range thetaQuantileDerivativeVector)
  have hS : S ≤ thetaQuantileDerivativeHistory.comap thetaCompactSourceInverse.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change thetaCompactSourceInverse (thetaQuantileDerivativeVector n) ∈ thetaQuantileDerivativeHistory
    cases n with
    | zero =>
        rw [thetaCompactSourceInverse_thetaQuantileDerivativeVector_zero]
        exact thetaQuantileDerivativeHistory.zero_mem
    | succ n =>
        rw [thetaCompactSourceInverse_thetaQuantileDerivativeVector_succ]
        exact thetaQuantileDerivativeHistory.smul_mem Complex.I
          (thetaQuantileDerivativeVector_mem_history n)
  have hclosed : IsClosed
      (thetaQuantileDerivativeHistory.comap thetaCompactSourceInverse.toLinearMap : Set H) :=
    S.isClosed_topologicalClosure.preimage thetaCompactSourceInverse.continuous
  exact S.topologicalClosure_minimal hS hclosed hf

end

end RHTower.HedenmalmThetaSource
