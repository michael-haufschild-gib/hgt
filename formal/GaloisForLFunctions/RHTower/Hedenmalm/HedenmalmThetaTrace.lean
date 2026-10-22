import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace

/-!
# The trace invariant of the compressed source inverse

The source inverse of the Riemann source is Hilbert–Schmidt, so its square is a product of two
Hilbert–Schmidt operators.  The corpus trace layer therefore applies verbatim: the diagonal series
converges over every Hilbert basis, its sum is basis independent, it equals the Hilbert–Schmidt
pairing `⟨B†, B⟩_HS`, and it is bounded by `‖B‖²_HS`.  This makes the trace calibration of the
compressed-inverse card a well-posed identity.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt ContinuousLinearMap

local instance factTwoNeTopThetaTrace : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The source inverse of the Riemann source as an operator on the quantile space. -/
def thetaKernelOperator : Lp ℂ 2 unitIntervalMeasure →L[ℂ] Lp ℂ 2 unitIntervalMeasure :=
  kernelOperator (E := Lp ℂ 2 unitIntervalMeasure) unitIntervalMeasure
    (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)

theorem isHilbertSchmidt_thetaKernelOperator' :
    IsHilbertSchmidt thetaKernelOperator :=
  isHilbertSchmidt_thetaKernelOperator

/-- **The trace invariant `tr(B²)` of the compressed source inverse.** -/
def thetaTraceSq : ℂ := opTrace (thetaKernelOperator ∘L thetaKernelOperator)

/-- **The trace series converges over every Hilbert basis.** -/
theorem summable_thetaTraceSq_diag {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 unitIntervalMeasure)) :
    Summable (fun i => (inner ℂ (b i)
      ((thetaKernelOperator ∘L thetaKernelOperator) (b i)) : ℂ)) :=
  summable_inner_diag_comp isHilbertSchmidt_thetaKernelOperator'
    isHilbertSchmidt_thetaKernelOperator' b

/-- **The trace invariant is basis independent.** -/
theorem thetaTraceSq_eq_tsum_basis {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 unitIntervalMeasure)) :
    thetaTraceSq = ∑' i, (inner ℂ (b i)
      ((thetaKernelOperator ∘L thetaKernelOperator) (b i)) : ℂ) :=
  opTrace_comp_eq_tsum_basis isHilbertSchmidt_thetaKernelOperator'
    isHilbertSchmidt_thetaKernelOperator' b

/-- **The trace invariant is the Hilbert--Schmidt pairing of `B†` with `B`.** -/
theorem thetaTraceSq_eq_hsInner :
    thetaTraceSq = hsInner (ContinuousLinearMap.adjoint thetaKernelOperator) thetaKernelOperator :=
  opTrace_comp_eq_hsInner _ _

/-- **The trace invariant is bounded by the Hilbert--Schmidt energy.** -/
theorem norm_thetaTraceSq_le :
    ‖thetaTraceSq‖ ≤ hsNorm thetaKernelOperator * hsNorm thetaKernelOperator :=
  norm_opTrace_comp_le isHilbertSchmidt_thetaKernelOperator'
    isHilbertSchmidt_thetaKernelOperator'


/-- **The square of the source inverse is trace class**, by the factorization characterization of
the Schatten `S₁` ideal. -/
theorem isTraceClass_thetaKernelOperator_sq :
    IsTraceClass (thetaKernelOperator ∘L thetaKernelOperator) :=
  isHilbertSchmidt_thetaKernelOperator'.comp_isTraceClass
    isHilbertSchmidt_thetaKernelOperator'

/-- **The positive energy of the source inverse is trace class**, with trace the Hilbert--Schmidt
energy. -/
theorem isTraceClass_adjoint_comp_thetaKernelOperator :
    IsTraceClass (ContinuousLinearMap.adjoint thetaKernelOperator ∘L thetaKernelOperator) :=
  isHilbertSchmidt_thetaKernelOperator'.adjoint_comp_self_isTraceClass

theorem re_opTrace_adjoint_comp_thetaKernelOperator :
    RCLike.re (opTrace (ContinuousLinearMap.adjoint thetaKernelOperator ∘L thetaKernelOperator))
      = hsNormSq thetaKernelOperator :=
  re_opTrace_adjoint_comp_self isHilbertSchmidt_thetaKernelOperator'



/-- **The Hilbert--Schmidt energy of the Riemann source inverse in closed form.**
`‖B‖²_HS = M ∫ p(1-p)/k`, the theta-tail integral of the source card. -/
theorem hsNormSq_thetaKernelOperator :
    hsNormSq thetaKernelOperator
      = thetaSource.mass * ∫ x : ℝ, tailEnergyDensity thetaSource x := by
  have h1 : hsNormSq thetaKernelOperator
      = ‖pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource‖ ^ 2 := by
    rw [thetaKernelOperator, hsNormSq_kernelOperator_eq_norm_sq]
  rw [h1, HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hae : (fun t : ℝ =>
      ‖(pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource : ℝ →
        (Lp ℂ 2 unitIntervalMeasure →L[ℂ] ℂ)) t‖ ^ 2)
      =ᵐ[unitIntervalMeasure]
        fun t => quantileSpeed thetaSource t ^ 2 * (t * (1 - t)) := by
    filter_upwards [(memLp_pinnedKernelField thetaSource
        hasFiniteKernelEnergy_thetaSource).coeFn_toLp,
      ae_unitIntervalMeasure_mem_Ioo] with t hc ht
    show ‖(pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource : ℝ →
        (Lp ℂ 2 unitIntervalMeasure →L[ℂ] ℂ)) t‖ ^ 2 = _
    rw [pinnedKernelL2, hc, norm_pinnedKernelField, mul_pow, norm_sq_pinnedSliceVec ht]
  rw [integral_congr_ae hae]
  have hres : unitIntervalMeasure = (volume : Measure ℝ).restrict (Ioo 0 1) := by
    rw [unitIntervalMeasure, restrict_Ioo_eq_restrict_Icc]
  rw [hres]
  exact integral_quantileSpeed_sq_slice thetaSource



/-! ### The kernel slice energy as an explicit integral

First step of the kernel evaluation of `tr(B²)`: the row energy of the pinned kernel written as an
honest integral of the kernel function, rather than as a norm in `L²`. -/

theorem integral_norm_sq_pinnedKernelFun (S : PositiveDensitySource) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ u, ‖pinnedKernelFun S t u‖ ^ 2 ∂unitIntervalMeasure)
      = quantileSpeed S t ^ 2 * (t * (1 - t)) := by
  have hmem := memLp_pinnedKernelFun S (Set.Ioo_subset_Icc_self ht)
  have hnorm := norm_sq_lp_eq_integral (pinnedKernelVec S (Set.Ioo_subset_Icc_self ht))
  rw [norm_sq_pinnedKernelVec S ht] at hnorm
  have hcoe : (∫ u, ((‖(pinnedKernelVec S (Set.Ioo_subset_Icc_self ht) : ℝ → ℂ) u‖ ^ 2 : ℝ) : ℂ)
        ∂unitIntervalMeasure)
      = ((∫ u, ‖pinnedKernelFun S t u‖ ^ 2 ∂unitIntervalMeasure : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hmem] with u hu
    show ((‖(pinnedKernelVec S (Set.Ioo_subset_Icc_self ht) : ℝ → ℂ) u‖ ^ 2 : ℝ) : ℂ)
      = ((‖pinnedKernelFun S t u‖ ^ 2 : ℝ) : ℂ)
    rw [pinnedKernelVec, hu]
  rw [hcoe] at hnorm
  exact_mod_cast hnorm.symm



theorem measurable_quantileSpeed (S : PositiveDensitySource) :
    Measurable (quantileSpeed S) :=
  measurable_const.div ((S.continuous_k.measurable).comp S.measurable_quantileFun)

/-- The pinned kernel is jointly measurable on the square. -/
theorem measurable_uncurry_pinnedKernelFun (S : PositiveDensitySource) :
    Measurable (fun p : ℝ × ℝ => pinnedKernelFun S p.1 p.2) := by
  have hq : Measurable fun p : ℝ × ℝ => ((quantileSpeed S p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_quantileSpeed S).comp measurable_fst)
  have hslice : Measurable fun p : ℝ × ℝ => ((pinnedKernelSlice p.1 p.2 : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    refine Measurable.sub ?_ measurable_fst
    exact measurable_const.ite (measurableSet_le measurable_snd measurable_fst) measurable_const
  exact (measurable_const.mul hq).mul hslice



/-- **The pinned kernel is square integrable on the square.**  Tonelli in the `integrable_prod_iff`
form: the inner row energy is `q(t)² t(1-t)`, whose integrability is exactly the finite kernel
energy. -/
theorem integrable_sq_norm_uncurry_pinnedKernelFun (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    Integrable (fun p : ℝ × ℝ => ‖pinnedKernelFun S p.1 p.2‖ ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => ‖pinnedKernelFun S p.1 p.2‖ ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (((measurable_uncurry_pinnedKernelFun S).norm).pow_const 2).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
    exact (memLp_two_iff_integrable_sq_norm
      (memLp_pinnedKernelFun S (Set.Ioo_subset_Icc_self ht)).1).mp
      (memLp_pinnedKernelFun S (Set.Ioo_subset_Icc_self ht))
  · refine (hfin : Integrable _ _).congr ?_
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
    rw [← integral_norm_sq_pinnedKernelFun S ht]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show ‖pinnedKernelFun S t u‖ ^ 2 = ‖‖pinnedKernelFun S t u‖ ^ 2‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]



/-- **The tensor of two `L²` functions is `L²` on the square.** -/
theorem memLp_tensor (f g : Lp ℂ 2 unitIntervalMeasure) :
    MemLp (fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.2) * g p.1) 2
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
  have hfm : AEStronglyMeasurable (fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.2))
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).comp_snd
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (Lp.aestronglyMeasurable g).comp_fst
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (starRingEnd ℂ) (f p.2) * g p.1)
      (unitIntervalMeasure.prod unitIntervalMeasure) := hfm.mul hgm
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hfsq : Integrable (fun u : ℝ => ‖f u‖ ^ 2) unitIntervalMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hgsq : Integrable (fun t : ℝ => ‖g t‖ ^ 2) unitIntervalMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hpt : ∀ p : ℝ × ℝ, ‖(starRingEnd ℂ) (f p.2) * g p.1‖ ^ 2
      = ‖f p.2‖ ^ 2 * ‖g p.1‖ ^ 2 := by
    intro p
    rw [norm_mul, mul_pow, RCLike.norm_conj]
  have hsqm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => ‖(starRingEnd ℂ) (f p.2) * g p.1‖ ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (hmeas.norm).pow 2
  refine (MeasureTheory.integrable_prod_iff hsqm).mpr ⟨?_, ?_⟩
  · filter_upwards with t
    refine (hfsq.const_mul (‖g t‖ ^ 2)).congr ?_
    filter_upwards with u
    rw [hpt (t, u)]
    ring
  · refine (hgsq.const_mul (∫ u : ℝ, ‖f u‖ ^ 2 ∂unitIntervalMeasure)).congr ?_
    filter_upwards with t
    have hrw : ∀ u : ℝ, ‖‖(starRingEnd ℂ) (f (t, u).2) * g (t, u).1‖ ^ 2‖
        = ‖g t‖ ^ 2 * ‖f u‖ ^ 2 := by
      intro u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hpt (t, u)]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
      MeasureTheory.integral_const_mul]
    ring



/-- The transposed kernel is square integrable on the square. -/
theorem integrable_sq_norm_swap_pinnedKernelFun (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    Integrable (fun p : ℝ × ℝ => ‖pinnedKernelFun S p.2 p.1‖ ^ 2)
      (unitIntervalMeasure.prod unitIntervalMeasure) :=
  (integrable_sq_norm_uncurry_pinnedKernelFun S hfin).swap


/-- **Almost every transposed row of the pinned kernel is square integrable.**  This is what makes
the adjoint of the source inverse a kernel operator in its own right. -/
theorem ae_integrable_sq_norm_transpose_row (S : PositiveDensitySource)
    (hfin : HasFiniteKernelEnergy S) :
    ∀ᵐ t ∂unitIntervalMeasure,
      Integrable (fun u => ‖pinnedKernelFun S u t‖ ^ 2) unitIntervalMeasure :=
  (integrable_sq_norm_uncurry_pinnedKernelFun S hfin).prod_left_ae


/-- **The quantile space is separable.**  This is the gate for transporting the source inverse to
the coordinate (matrix) Hilbert--Schmidt model, where the regularized determinant lives. -/
theorem separableSpace_unitIntervalL2 :
    TopologicalSpace.SeparableSpace (Lp ℂ 2 unitIntervalMeasure) := inferInstance



/-! ### The coordinate model of the quantile space

Transporting the source inverse to `ℓ²` is what puts it in reach of the corpus regularized
determinant, which lives on Hilbert--Schmidt *kernels* rather than operators. -/

/-- The index set of the canonical Hilbert basis of the quantile space. -/
def thetaIndex : Type := (exists_hilbertBasis ℂ (Lp ℂ 2 unitIntervalMeasure)).choose

instance : Countable thetaIndex :=
  (ContinuousLinearMap.hsBasis ℂ (Lp ℂ 2 unitIntervalMeasure)).orthonormal.countable_index

noncomputable instance : DecidableEq thetaIndex := Classical.decEq _

/-- The coordinate isometry of the quantile space onto `ℓ²`. -/
noncomputable def thetaCoord :
    Lp ℂ 2 unitIntervalMeasure ≃ₗᵢ[ℂ] lp (fun _ : thetaIndex => ℂ) 2 :=
  (ContinuousLinearMap.hsBasis ℂ (Lp ℂ 2 unitIntervalMeasure)).repr

/-- The source inverse read in the coordinate model. -/
noncomputable def thetaKernelMatrixOperator :
    lp (fun _ : thetaIndex => ℂ) 2 →L[ℂ] lp (fun _ : thetaIndex => ℂ) 2 :=
  (thetaCoord.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (thetaKernelOperator.comp
      (thetaCoord.symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem isHilbertSchmidt_thetaKernelMatrixOperator :
    IsHilbertSchmidt thetaKernelMatrixOperator := by
  refine ((isHilbertSchmidt_thetaKernelOperator'.comp_right
    (thetaCoord.symm.toContinuousLinearEquiv.toContinuousLinearMap)).comp_left
    (thetaCoord.toContinuousLinearEquiv.toContinuousLinearMap))



/-- **The kernel matrix of the source inverse.**  A genuine Hilbert--Schmidt kernel on the index
set, so the corpus regularized determinant applies to it. -/
noncomputable def thetaKernelMatrix : thetaIndex × thetaIndex → ℂ :=
  HilbertSchmidt.matrixOf thetaKernelMatrixOperator

theorem isHS_thetaKernelMatrix : HilbertSchmidt.IsHS thetaKernelMatrix :=
  HilbertSchmidt.isHS_matrixOf isHilbertSchmidt_thetaKernelMatrixOperator

/-- **The regularized determinant of the source pencil is defined.**  This is the object of the
determinant clause: `det₂(1 - z B)` read in the coordinate model. -/
noncomputable def thetaFredholmDet (z : ℂ) : ℂ :=
  HilbertSchmidt.fredholmDet thetaKernelMatrix z

theorem thetaFredholmDet_ne_zero (z : ℂ) : thetaFredholmDet z ≠ 0 :=
  HilbertSchmidt.fredholmDet_ne_zero thetaKernelMatrix z



/-- **The determinant of the source pencil is holomorphic** on the disc where the Hilbert--Schmidt
norm controls the expansion. -/
theorem differentiableOn_thetaFredholmDet (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm thetaKernelMatrix < 1) :
    DifferentiableOn ℂ thetaFredholmDet (Metric.ball 0 r) :=
  HilbertSchmidt.fredholmDet_differentiableOn isHS_thetaKernelMatrix r hr

/-- **The Plemelj identity for the Riemann source.**  The logarithmic derivative of the regularized
determinant of the source pencil is the negative resolvent trace of the source inverse.  Identifying
that resolvent trace with `-Xi_C'/Xi_C` is exactly the determinant clause of the card. -/
theorem logDeriv_thetaFredholmDet (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm thetaKernelMatrix < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    logDeriv thetaFredholmDet z
      = - HilbertSchmidt.resolventTrace thetaKernelMatrix z :=
  HilbertSchmidt.logDeriv_fredholmDet isHS_thetaKernelMatrix r hr z hz


end HedenmalmThetaSource

end

end RHTower
