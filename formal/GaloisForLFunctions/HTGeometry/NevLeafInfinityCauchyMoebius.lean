import GaloisForLFunctions.HTGeometry.NevLeafCauchyMoebius

/-!
# The Cauchy transform of the leaf at infinity

The parameter at infinity is the point of the Möbius family where the denominator degenerates to
`B` alone.  At each finite level the truncated entries `Aₙ` and `Bₙ` are the same multiple of the
quasi-orthogonal pair attached to the parameter `βₙ^∞/αₙ^∞`, so the divided-difference identity for
the quadrature measure clears to

`Bₙ(z)·∫(x − z)⁻¹ dμₙ = −s₀·Aₙ(z)`.

The quadrature levels selected by `goodLevelInf` converge weakly to the leaf at infinity, so

`B(z)·∫(x − z)⁻¹ dν_∞ = −A(z)`,

and the determinant identity forbids `B(z)` from vanishing off the real axis.
-/

open scoped BigOperators
open MeasureTheory Filter Topology OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-! ## The leaf at infinity as a limit of quadrature levels -/

/-- The leaf at infinity is its own atomic part on the zero set of `B`. -/
theorem nevLeaf_infinity_eq_fiberMeasure (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    (nevLeaf h h0b h0 ∞ : Measure ℝ)
      = fiberMeasure (fun x => christoffelLimit s x)
          (nevMatrixDataInf h h0b).infinityDenominatorFiber := by
  have hcar := nevLeaf_infinity_carried h h0b h0
  have hbase := measure_eq_fiberMeasure_of_carried
    (nevLeaf h h0b h0 ∞ : Measure ℝ)
    (countable_infinityDenominatorFiber h h0b)
    (isClosed_infinityDenominatorFiber h h0b).measurableSet hcar
  rw [hbase, fiberMeasure, fiberMeasure]
  refine congrArg Measure.sum (funext fun p => ?_)
  rw [nevLeaf_infinity_atoms h h0b h0 p.2, ENNReal.toReal_ofReal (christoffelLimit_nonneg h _)]

/-- **The quadrature levels selected at infinity converge to the leaf at infinity.** -/
theorem exists_tendsto_quasiProbMeasure_nevLeafInf (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i => quasiProbMeasure h (goodLevelInf h (φ i)) (leafParamInf h (φ i)))
        atTop (𝓝 (nevLeaf h h0b h0 ∞)) := by
  obtain ⟨μ, φ, hφ, hlim, hmom, hcar⟩ := exists_leaf_infinity_approx h h0b
  have hmom' : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) := by
    intro k
    refine ⟨(hmom k).1, ?_⟩
    simpa [h0] using (hmom k).2
  have hset : (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ
      = {x : ℝ | nevBrealInf s x ≠ 0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.infinityDenominatorFiber,
      nevMatrixDataInf]
  have hcar' : (μ : Measure ℝ) (nevMatrixDataInf h h0b).infinityDenominatorFiberᶜ = 0 := by
    rw [hset]; exact hcar
  have hatoms : ∀ ξ ∈ (nevMatrixDataInf h h0b).infinityDenominatorFiber,
      (μ : Measure ℝ) {ξ} = ENNReal.ofReal (christoffelLimit s ξ) := by
    intro ξ hξmem
    have hξ : nevBrealInf s ξ = 0 := hξmem
    refine le_antisymm (measure_singleton_le_ofReal_christoffelLimit h hmom' ξ) ?_
    exact ofReal_christoffelLimit_le_leaf_infinity_singleton h h0b h0 hφ hlim hξ
  have hfiber : (μ : Measure ℝ)
      = fiberMeasure (fun x => christoffelLimit s x)
          (nevMatrixDataInf h h0b).infinityDenominatorFiber := by
    have hbase := measure_eq_fiberMeasure_of_carried (μ : Measure ℝ)
      (countable_infinityDenominatorFiber h h0b)
      (isClosed_infinityDenominatorFiber h h0b).measurableSet hcar'
    rw [hbase, fiberMeasure, fiberMeasure]
    refine congrArg Measure.sum (funext fun p => ?_)
    rw [hatoms p p.2, ENNReal.toReal_ofReal (christoffelLimit_nonneg h _)]
  have heq : μ = nevLeaf h h0b h0 ∞ := by
    refine MeasureTheory.ProbabilityMeasure.toMeasure_injective ?_
    rw [hfiber, nevLeaf_infinity_eq_fiberMeasure h h0b h0]
  exact ⟨φ, hφ, heq ▸ hlim⟩

/-! ## The truncated entries in the quasi-orthogonal basis at infinity -/

theorem ofReal_nevAlphaInf (s : ℕ → ℝ) (n : ℕ) :
    ((nevAlphaInf s n : ℝ) : ℂ) = secondKindC s n 0 := by
  rw [nevAlphaInf, secondKindC_at_zero]

theorem ofReal_nevBetaInf (s : ℕ → ℝ) (n : ℕ) :
    ((nevBetaInf s n : ℝ) : ℂ) = -secondKindC s (n + 1) 0 := by
  rw [nevBetaInf, secondKindC_at_zero]
  push_cast
  ring

/-- **The truncated `A` entry in the quasi-orthogonal basis at infinity.** -/
theorem nevAtruncC_closedInf (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    nevAtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        (((nevAlphaInf s n : ℝ) : ℂ) * secondKindC s (n + 1) z
          + ((nevBetaInf s n : ℝ) : ℂ) * secondKindC s n z) := by
  have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
    simpa using h.self_ne_zero (monicOrtho_ne_zero s n)
  rw [nevAtruncC_eq h n z, ofReal_nevAlphaInf, ofReal_nevBetaInf]
  field_simp
  ring

/-- **The truncated `B` entry in the quasi-orthogonal basis at infinity.** -/
theorem nevBtruncC_closedInf (h : PositiveMomentForm s) (n : ℕ) (z : ℂ) :
    nevBtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
        (((nevAlphaInf s n : ℝ) : ℂ) * monicOrthoC s (n + 1) z
          + ((nevBetaInf s n : ℝ) : ℂ) * monicOrthoC s n z) := by
  have hn : ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) ≠ 0 := by
    simpa using h.self_ne_zero (monicOrtho_ne_zero s n)
  rw [nevBtruncC_eq h n z, ofReal_nevAlphaInf, ofReal_nevBetaInf]
  field_simp
  ring

theorem nevAtruncC_eq_quasiInf (h : PositiveMomentForm s) (n : ℕ)
    (hα : nevAlphaInf s n ≠ 0) (z : ℂ) :
    nevAtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
          ((nevAlphaInf s n : ℝ) : ℂ) *
        Polynomial.aeval z (quasiSecondKind s n (nevBetaInf s n / nevAlphaInf s n)) := by
  have hαC : ((nevAlphaInf s n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [nevAtruncC_closedInf h n z, aeval_quasiSecondKind]
  push_cast
  field_simp

theorem nevBtruncC_eq_quasiInf (h : PositiveMomentForm s) (n : ℕ)
    (hα : nevAlphaInf s n ≠ 0) (z : ℂ) :
    nevBtruncC s n z
      = ((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
          ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
          ((nevAlphaInf s n : ℝ) : ℂ) *
        Polynomial.aeval z (quasiOrtho s n (nevBetaInf s n / nevAlphaInf s n)) := by
  have hαC : ((nevAlphaInf s n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [nevBtruncC_closedInf h n z, aeval_quasiOrtho]
  push_cast
  field_simp

/-! ## The finite stage and its limit -/

/-- **The finite-stage Nevanlinna identity at the parameter infinity.** -/
theorem nevTruncInf_cauchy_identity (h : PositiveMomentForm s) (n : ℕ)
    (hα : nevAlphaInf s n ≠ 0) {z : ℂ} (hz : z.im ≠ 0) :
    nevBtruncC s n z *
        ∫ x, ((x : ℂ) - z)⁻¹ ∂(quasiMeasure s n (nevBetaInf s n / nevAlphaInf s n))
      = -((s 0 : ℝ) : ℂ) * nevAtruncC s n z := by
  have hq := quasiMeasure_cauchy_identity_of_im_ne_zero h n
    (nevBetaInf s n / nevAlphaInf s n) hz
  rw [nevBtruncC_eq_quasiInf h n hα z, nevAtruncC_eq_quasiInf h n hα z, aeval_quasiSecondKind]
  linear_combination (((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
      ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
      ((nevAlphaInf s n : ℝ) : ℂ)) * hq

/-- **The Nevanlinna identity for the leaf at infinity.** -/
theorem nevInf_cauchy_identity_infty (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) {z : ℂ} (hz : z.im ≠ 0) :
    nevBinf s z * ∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 ∞ : Measure ℝ)
      = -nevAinf s z := by
  obtain ⟨S, P, _, _, hS, hP⟩ := id h0b
  obtain ⟨φ, hφ, hlim⟩ := exists_tendsto_quasiProbMeasure_nevLeafInf h h0b h0
  have hNtop : Tendsto (fun i => goodLevelInf h (φ i)) atTop atTop := by
    refine tendsto_atTop_mono (fun i => ?_) tendsto_id
    show i ≤ goodLevelInf h (φ i)
    have h1 : φ i + 1 ≤ goodLevelInf h (φ i) := goodLevelInf_ge h (φ i)
    have h2 : i ≤ φ i := hφ.le_apply
    omega
  have hcauchy : Tendsto (fun i => ∫ x, ((x : ℂ) - z)⁻¹
        ∂((quasiProbMeasure h (goodLevelInf h (φ i)) (leafParamInf h (φ i)) :
          ProbabilityMeasure ℝ) : Measure ℝ)) atTop
      (𝓝 (∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 ∞ : Measure ℝ))) :=
    tendsto_cauchyTransform_of_tendsto hlim hz
  have hA : Tendsto (fun i => nevAtruncC s (goodLevelInf h (φ i)) z) atTop
      (𝓝 (nevAinf s z)) := (tendsto_nevAtruncC h hS hP z).comp hNtop
  have hB : Tendsto (fun i => nevBtruncC s (goodLevelInf h (φ i)) z) atTop
      (𝓝 (nevBinf s z)) := (tendsto_nevBtruncC h hS hP z).comp hNtop
  have hLHS : Tendsto (fun i => nevBtruncC s (goodLevelInf h (φ i)) z *
        ∫ x, ((x : ℂ) - z)⁻¹
          ∂((quasiProbMeasure h (goodLevelInf h (φ i)) (leafParamInf h (φ i)) :
            ProbabilityMeasure ℝ) : Measure ℝ)) atTop
      (𝓝 (nevBinf s z * ∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 ∞ : Measure ℝ))) :=
    hB.mul hcauchy
  have hRHS : Tendsto (fun i => -((s 0 : ℝ) : ℂ) * nevAtruncC s (goodLevelInf h (φ i)) z) atTop
      (𝓝 (-((s 0 : ℝ) : ℂ) * nevAinf s z)) := hA.const_mul _
  have heq : ∀ i, nevBtruncC s (goodLevelInf h (φ i)) z *
        (∫ x, ((x : ℂ) - z)⁻¹
          ∂((quasiProbMeasure h (goodLevelInf h (φ i)) (leafParamInf h (φ i)) :
            ProbabilityMeasure ℝ) : Measure ℝ))
        = -((s 0 : ℝ) : ℂ) * nevAtruncC s (goodLevelInf h (φ i)) z := by
    intro i
    have hcoe : ((quasiProbMeasure h (goodLevelInf h (φ i)) (leafParamInf h (φ i)) :
          ProbabilityMeasure ℝ) : Measure ℝ)
        = quasiMeasure s (goodLevelInf h (φ i))
            (nevBetaInf s (goodLevelInf h (φ i)) / nevAlphaInf s (goodLevelInf h (φ i))) := by
      show quasiProb s (goodLevelInf h (φ i)) (leafParamInf h (φ i)) = _
      rw [quasiProb_eq_quasiMeasure h0]
      rfl
    rw [hcoe]
    exact nevTruncInf_cauchy_identity h _ (goodLevelInf_nevAlphaInf_ne_zero h (φ i)) hz
  have hmain := tendsto_nhds_unique (hLHS.congr heq) hRHS
  rw [h0] at hmain
  simpa using hmain

/-- **The entire `B` entry is nonzero off the real axis.** -/
theorem nevBinf_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {z : ℂ} (hz : z.im ≠ 0) : nevBinf s z ≠ 0 := by
  intro hB
  have hid := nevInf_cauchy_identity_infty h h0b h0 hz
  rw [hB, zero_mul] at hid
  have hAz : nevAinf s z = 0 := by linear_combination hid
  have hdet := nevAinf_mul_nevDinf_sub_nevBinf_mul_nevCinf h z h0b
    (boundedKernel_global h h0b z)
  rw [hAz, hB] at hdet
  have : (0 : ℂ) = 1 := by linear_combination hdet
  exact one_ne_zero this.symm

/-- **The Weyl-disc closed form at the parameter infinity.** -/
theorem cauchyTransform_nevLeafInf_eq_ratio (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) {z : ℂ} (hz : z.im ≠ 0) :
    ∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 ∞ : Measure ℝ)
      = -nevAinf s z / nevBinf s z := by
  have hB := nevBinf_ne_zero h h0b h0 hz
  rw [eq_div_iff hB, mul_comm]
  exact nevInf_cauchy_identity_infty h h0b h0 hz

end HTGeometry
