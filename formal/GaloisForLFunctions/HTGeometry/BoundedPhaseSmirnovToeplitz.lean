import GaloisForLFunctions.HTGeometry.BoundedRealHerglotz
import GaloisForLFunctions.HTGeometry.SectorCayleyMultiplier
import GaloisForLFunctions.HTGeometry.SmirnovToeplitzKernel

/-!
# Bounded-phase Smirnov Toeplitz elements

An arbitrary bounded measurable real circle phase is realized as the real boundary part of its
Herglotz transform.  The sector Cayley transform supplies two outer bounded factors; their
Smirnov quotient has exactly the prescribed phase reflection.  A fixed fourth monomial then
produces an actual nonzero Smirnov Toeplitz-kernel element.
-/

open Complex MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem circleCayley_measurableEmbedding : MeasurableEmbedding circleCayley :=
  continuous_circleCayley.measurableEmbedding injective_circleCayley

/-- Measurable inverse of the real Cayley embedding, extended arbitrarily at its single omitted
circle point. -/
noncomputable def circleCayleyInverse : Circle → ℝ :=
  circleCayley_measurableEmbedding.invFun

theorem measurable_circleCayleyInverse : Measurable circleCayleyInverse :=
  circleCayley_measurableEmbedding.measurable_invFun

@[simp] theorem circleCayleyInverse_circleCayley (x : ℝ) :
    circleCayleyInverse (circleCayley x) = x := by
  rw [circleCayleyInverse, MeasurableEmbedding.invFun]
  have hx : circleCayley x ∈ Set.range circleCayley := ⟨x, rfl⟩
  rw [dif_pos hx]
  simpa [circleCayley_measurableEmbedding] using
    circleCayley_measurableEmbedding.equivRange.symm_apply_apply x

/-- Every unit-circle point except `1` is a finite real Cayley value. -/
theorem exists_circleCayley_eq_of_ne_one
    (z : Circle) (hz : (z : ℂ) ≠ 1) :
    ∃ x : ℝ, circleCayley x = z := by
  let x : ℝ := -(z : ℂ).im / (1 - (z : ℂ).re)
  have hnormSq : (z : ℂ).re ^ (2 : ℕ) + (z : ℂ).im ^ (2 : ℕ) = 1 := by
    calc
      (z : ℂ).re ^ (2 : ℕ) + (z : ℂ).im ^ (2 : ℕ) = Complex.normSq (z : ℂ) := by
        rw [Complex.normSq_apply]
        ring
      _ = ‖(z : ℂ)‖ ^ (2 : ℕ) := (Complex.sq_norm _).symm
      _ = 1 := by rw [Circle.norm_coe]; norm_num
  have hre : 1 - (z : ℂ).re ≠ 0 := by
    intro hzero
    have hreOne : (z : ℂ).re = 1 := by linarith
    have himZero : (z : ℂ).im = 0 := by
      rw [hreOne] at hnormSq
      nlinarith
    apply hz
    apply Complex.ext
    · simpa [hreOne]
    · simpa [himZero]
  refine ⟨x, Subtype.ext ?_⟩
  rw [circleCayley_coe, realCayley]
  apply (div_eq_iff (real_add_I_ne_zero x)).2
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.ofReal_re, I_re, sub_zero,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_im,
      I_im, add_zero, zero_mul, mul_one]
    dsimp [x]
    field_simp [hre]
    ring
  · simp only [Complex.sub_im, Complex.ofReal_im, I_im, zero_sub,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      add_zero, mul_one]
    dsimp [x]
    field_simp [hre]
    nlinarith

/-- The measurable Cayley inverse is a right inverse away from the omitted point `1`. -/
@[simp] theorem circleCayley_circleCayleyInverse_of_ne_one
    (z : Circle) (hz : (z : ℂ) ≠ 1) :
    circleCayley (circleCayleyInverse z) = z := by
  obtain ⟨x, rfl⟩ := exists_circleCayley_eq_of_ne_one z hz
  rw [circleCayleyInverse_circleCayley]

theorem abs_arg_le_pi_div_two_of_re_nonneg {z : ℂ}
    (hz : z ≠ 0) (hre : 0 ≤ z.re) :
    |z.arg| ≤ Real.pi / 2 := by
  rw [abs_le]
  have hcos : 0 ≤ Real.cos z.arg := by
    rw [Complex.cos_arg hz]
    exact div_nonneg hre (norm_nonneg z)
  constructor
  · by_contra hlow
    rw [not_le] at hlow
    have hhalfMem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    have hnegMem : -z.arg ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · linarith [Real.pi_div_two_pos]
      · linarith [Complex.neg_pi_lt_arg z]
    have hlt := Real.strictAntiOn_cos hhalfMem hnegMem (by linarith)
    rw [Real.cos_pi_div_two, Real.cos_neg] at hlt
    linarith
  · by_contra hupp
    rw [not_le] at hupp
    have hhalfMem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    have hargMem : z.arg ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · linarith [Real.pi_div_two_pos]
      · exact Complex.arg_le_pi z
    have hlt := Real.strictAntiOn_cos hhalfMem hargMem hupp
    rw [Real.cos_pi_div_two] at hlt
    linarith

theorem exp_two_mul_I_mul_arg_eq_div_conj {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (2 * I * (z.arg : ℂ)) = z / (starRingEnd ℂ) z := by
  have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr hz).ne'
  have hp := Complex.norm_mul_exp_arg_mul_I z
  have harg : (starRingEnd ℂ) ((z.arg : ℂ) * I) =
      -(z.arg : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  symm
  calc
    z / (starRingEnd ℂ) z =
        ((‖z‖ : ℝ) : ℂ) * Complex.exp ((z.arg : ℂ) * I) /
          (starRingEnd ℂ)
            (((‖z‖ : ℝ) : ℂ) * Complex.exp ((z.arg : ℂ) * I)) := by
      rw [hp]
    _ = Complex.exp ((z.arg : ℂ) * I) /
        Complex.exp (-(z.arg : ℂ) * I) := by
      simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, harg]
      field_simp
    _ = Complex.exp (2 * I * (z.arg : ℂ)) := by
      rw [← Complex.exp_sub]
      congr 1
      ring

private theorem continuousAt_sectorCayleyValue {w : ℂ}
    (hw : |w.re| ≤ Real.pi / 2) :
    ContinuousAt sectorCayleyValue w := by
  have he : ContinuousAt sectorExponential w := by
    unfold sectorExponential
    fun_prop
  have hden : sectorExponential w + 1 ≠ 0 :=
    add_one_ne_zero_of_re_nonneg_sectorCayleyMultiplier (sectorExponential_re_nonneg hw)
  exact (he.sub continuousAt_const).div (he.add continuousAt_const) hden

/-- Boundary functional calculus for the sector Cayley multiplier. -/
theorem diskMultiplierBoundaryFun_sectorCayleyMultiplier_ae
    (H : HardyDisk)
    (hH : ∀ z : ℂ, ‖z‖ < 1 → |(hardyFun H z).re| ≤ Real.pi / 2)
    (hBoundary : ∀ᵐ z ∂circleLebesgue,
      |((hardyDiskBoundary H : Circle → ℂ) z).re| ≤ Real.pi / 2) :
    diskMultiplierBoundaryFun (sectorCayleyMultiplier H hH) =ᵐ[circleLebesgue]
      fun z => sectorCayleyValue ((hardyDiskBoundary H : Circle → ℂ) z) := by
  obtain ⟨base, hbase, hradial⟩ := exists_hardyDiskRadialBoundary_subseq_ae H
  obtain ⟨ns, hns, hschur⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono
      (sectorCayleyMultiplier H hH) hbase
  filter_upwards [hradial, hschur, hBoundary] with z hzH hzS hzBound
  apply tendsto_nhds_unique hzS
  have hzH' := hzH.comp hns.tendsto_atTop
  have hcalc := (continuousAt_sectorCayleyValue hzBound).tendsto.comp hzH'
  convert hcalc using 1
  funext i
  rfl

private theorem line_eventuallyEq_of_circle_eventuallyEq
    {f g : Circle → ℂ} (h : f =ᵐ[circleLebesgue] g) :
    (fun x => f (circleCayley x)) =ᵐ[volume]
      fun x => g (circleCayley x) := by
  have hweighted := h.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  exact (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted

/-- Real-line form of the sector-Cayley boundary functional calculus. -/
theorem diskMultiplierLineBoundary_sectorCayleyMultiplier_ae
    (H : HardyDisk)
    (hH : ∀ z : ℂ, ‖z‖ < 1 → |(hardyFun H z).re| ≤ Real.pi / 2)
    (hBoundary : ∀ᵐ z ∂circleLebesgue,
      |((hardyDiskBoundary H : Circle → ℂ) z).re| ≤ Real.pi / 2) :
    diskMultiplierLineBoundary (sectorCayleyMultiplier H hH) =ᵐ[volume]
      fun x => sectorCayleyValue
        ((hardyDiskBoundary H : Circle → ℂ) (circleCayley x)) := by
  have hcircle := line_eventuallyEq_of_circle_eventuallyEq
    (diskMultiplierBoundaryFun_sectorCayleyMultiplier_ae H hH hBoundary)
  filter_upwards [diskMultiplierLineBoundary_ae (sectorCayleyMultiplier H hH),
    hcircle] with x hrep hvalue
  rw [hrep, hvalue]

/-- The fourth disk monomial has its literal Cayley boundary on the real line. -/
theorem diskMultiplierLineBoundary_diskMonomialMultiplier_four_ae :
    diskMultiplierLineBoundary (diskMonomialMultiplier 4) =ᵐ[volume]
      fun x => (circleCayley x : ℂ) ^ (4 : ℕ) := by
  have hcircle : diskMultiplierBoundaryFun (diskMonomialMultiplier 4) =ᵐ[
      circleLebesgue] fun z => (z : ℂ) ^ (4 : ℕ) := by
    rw [diskMultiplierBoundaryFun, hardyOf_diskMonomialMultiplier,
      hardyDiskBoundary_single]
    exact circleMonomialLp_coeFn_ae circleLebesgue 4
  have hline := line_eventuallyEq_of_circle_eventuallyEq hcircle
  filter_upwards [diskMultiplierLineBoundary_ae (diskMonomialMultiplier 4), hline]
      with x hrep hvalue
  rw [hrep, hvalue]

/-! ## The outer quotient attached to bounded phase data -/

/-- Herglotz Hardy vector whose real boundary part is the prescribed bounded phase. -/
def boundedPhaseHardy (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : HardyDisk :=
  boundedRealHerglotzHardy b hb (Real.pi / 2) hbound

theorem boundedPhaseHardy_re_bound (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) (z : ℂ) (hz : ‖z‖ < 1) :
    |(hardyFun (boundedPhaseHardy b hb hbound) z).re| ≤ Real.pi / 2 :=
  abs_re_hardyFun_boundedRealHerglotzHardy_le b hb (Real.pi / 2) hbound hz

theorem boundedPhaseHardy_boundary_re_ae (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    ∀ᵐ z ∂circleLebesgue,
      ((hardyDiskBoundary (boundedPhaseHardy b hb hbound) : Circle → ℂ) z).re = b z :=
  hardyDiskBoundary_boundedRealHerglotz_re_ae b hb (Real.pi / 2) hbound

/-- Schur multiplier obtained from bounded phase data. -/
def boundedPhaseSchur (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : DiskMultiplier :=
  sectorCayleyMultiplier (boundedPhaseHardy b hb hbound)
    (boundedPhaseHardy_re_bound b hb hbound)

/-- Outer minus factor `1-S`. -/
def boundedPhaseMinus (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : DiskMultiplier :=
  (DiskMultiplier.const 1).sub (boundedPhaseSchur b hb hbound)

/-- Outer plus factor `1+S`. -/
def boundedPhasePlus (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : DiskMultiplier :=
  (DiskMultiplier.const 1).add (boundedPhaseSchur b hb hbound)

theorem isOuterDiskMultiplier_boundedPhaseMinus
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    IsOuterDiskMultiplier (boundedPhaseMinus b hb hbound) :=
  isOuterDiskMultiplier_one_sub_sectorCayleyMultiplier
    (boundedPhaseHardy b hb hbound) (boundedPhaseHardy_re_bound b hb hbound)

theorem isOuterDiskMultiplier_boundedPhasePlus
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    IsOuterDiskMultiplier (boundedPhasePlus b hb hbound) :=
  isOuterDiskMultiplier_one_add_sectorCayleyMultiplier
    (boundedPhaseHardy b hb hbound) (boundedPhaseHardy_re_bound b hb hbound)

/-- The outer quotient `(1+S)/(1-S)` has exactly the requested phase reflection. -/
theorem boundedPhaseOuterQuotient_phase_ae
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    ∀ᵐ x ∂volume,
      let E := diskMultiplierLineBoundary (boundedPhasePlus b hb hbound) x /
        diskMultiplierLineBoundary (boundedPhaseMinus b hb hbound) x
      E / (starRingEnd ℂ) E =
        Complex.exp (2 * I * (b (circleCayley x) : ℂ)) := by
  let H := boundedPhaseHardy b hb hbound
  let S := boundedPhaseSchur b hb hbound
  let P := boundedPhasePlus b hb hbound
  let D := boundedPhaseMinus b hb hbound
  have hreCircle := boundedPhaseHardy_boundary_re_ae b hb hbound
  have hstripCircle : ∀ᵐ z ∂circleLebesgue,
      |((hardyDiskBoundary H : Circle → ℂ) z).re| ≤ Real.pi / 2 := by
    filter_upwards [hreCircle] with z hz
    rw [hz]
    exact hbound z
  have hS : diskMultiplierLineBoundary S =ᵐ[volume]
      fun x => sectorCayleyValue
        ((hardyDiskBoundary H : Circle → ℂ) (circleCayley x)) :=
    diskMultiplierLineBoundary_sectorCayleyMultiplier_ae H
      (boundedPhaseHardy_re_bound b hb hbound) hstripCircle
  have hP := diskMultiplierLineBoundary_add_ae
    (DiskMultiplier.const 1) S
  have hD := diskMultiplierLineBoundary_sub_ae
    (DiskMultiplier.const 1) S
  have hOne := diskMultiplierLineBoundary_const_ae (1 : ℂ)
  have hreWeighted :=
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually
      hreCircle
  have hreWeightedEq :
      (fun x => ((hardyDiskBoundary (boundedPhaseHardy b hb hbound) : Circle → ℂ)
        (circleCayley x)).re) =ᵐ[
          (volume : Measure ℝ).withDensity (realDensity standardCauchyWeight)]
        fun x => b (circleCayley x) := hreWeighted
  have hreLine := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hreWeightedEq
  filter_upwards [hS, hP, hD, hOne, hreLine] with x hxS hxP hxD hxOne hxRe
  dsimp only
  have hxPD : diskMultiplierLineBoundary P x /
      diskMultiplierLineBoundary D x =
        sectorExponential
          ((hardyDiskBoundary H : Circle → ℂ) (circleCayley x)) := by
    change diskMultiplierLineBoundary ((DiskMultiplier.const 1).add S) x /
      diskMultiplierLineBoundary ((DiskMultiplier.const 1).sub S) x = _
    rw [hxP, hxD, hxOne, hxS]
    exact one_add_sectorCayleyValue_div_one_sub
      (by rw [hxRe]; exact hbound (circleCayley x))
  rw [hxPD, sectorExponential_div_conj, hxRe]

/-! ## Actual Smirnov Toeplitz-kernel element -/

/-- Toeplitz symbol carrying bounded phase `2b`, with the fixed fourth Cayley monomial removed. -/
def boundedPhaseToeplitzSymbol (b : Circle → ℝ) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) ((realCayley x) ^ (4 : ℕ)) *
    Complex.exp (2 * I * (b (circleCayley x) : ℂ))

theorem measurable_boundedPhaseToeplitzSymbol
    (b : Circle → ℝ) (hb : Measurable b) :
    Measurable (boundedPhaseToeplitzSymbol b) := by
  have hbLine : Measurable fun x : ℝ => b (circleCayley x) :=
    hb.comp continuous_circleCayley.measurable
  have hz : Measurable fun x : ℝ => realCayley x :=
    continuous_realCayley.measurable
  have hbComplex : Measurable fun x : ℝ => (b (circleCayley x) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp hbLine
  have harg : Measurable fun x : ℝ =>
      (2 * I : ℂ) * (b (circleCayley x) : ℂ) :=
    (measurable_const : Measurable fun _ : ℝ => (2 * I : ℂ)).mul hbComplex
  unfold boundedPhaseToeplitzSymbol
  exact (Complex.continuous_conj.measurable.comp (hz.pow_const 4)).mul
    (Complex.continuous_exp.measurable.comp harg)

/-- Forward Smirnov quotient `z⁴(1-S)/(1+S)`. -/
def boundedPhaseForward (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : DiskSmirnovBoundary where
  numerator := (diskMonomialMultiplier 4).mul (boundedPhaseMinus b hb hbound)
  denominator := boundedPhasePlus b hb hbound
  denominator_outer := isOuterDiskMultiplier_boundedPhasePlus b hb hbound

/-- Reflected Smirnov quotient `(1-S)/(1+S)`. -/
def boundedPhaseReflected (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) : DiskSmirnovBoundary where
  numerator := boundedPhaseMinus b hb hbound
  denominator := boundedPhasePlus b hb hbound
  denominator_outer := isOuterDiskMultiplier_boundedPhasePlus b hb hbound

/-- Every bounded measurable real phase produces an actual nonzero Smirnov Toeplitz-kernel
element.  This is the bounded-phase multiplier theorem needed by the Kapustin sign argument. -/
def boundedPhaseSmirnovToeplitzElement
    (b : Circle → ℝ) (hb : Measurable b)
    (hbound : ∀ z, |b z| ≤ Real.pi / 2) :
    SmirnovToeplitzKernelElement (boundedPhaseToeplitzSymbol b) where
  forward := boundedPhaseForward b hb hbound
  reflected := boundedPhaseReflected b hb hbound
  boundary_relation := by
    let B := diskMonomialMultiplier 4
    let D := boundedPhaseMinus b hb hbound
    let P := boundedPhasePlus b hb hbound
    have hmul := diskMultiplierLineBoundary_mul_ae B D
    have hB := diskMultiplierLineBoundary_diskMonomialMultiplier_four_ae
    have hphase := boundedPhaseOuterQuotient_phase_ae b hb hbound
    have hPne := diskMultiplierLineBoundary_ne_zero_ae P
      (isOuterDiskMultiplier_boundedPhasePlus b hb hbound).exists_nonzero
    have hDne := diskMultiplierLineBoundary_ne_zero_ae D
      (isOuterDiskMultiplier_boundedPhaseMinus b hb hbound).exists_nonzero
    filter_upwards [hmul, hB, hphase, hPne, hDne]
        with x hxMul hxB hxPhase hxP hxD
    dsimp only at hxPhase
    change diskMultiplierLineBoundary D x / diskMultiplierLineBoundary P x =
      (starRingEnd ℂ) (boundedPhaseToeplitzSymbol b x) *
        (starRingEnd ℂ)
          (diskMultiplierLineBoundary (B.mul D) x /
            diskMultiplierLineBoundary P x)
    rw [hxMul, hxB, circleCayley_coe, boundedPhaseToeplitzSymbol, ← hxPhase]
    let z : ℂ := (realCayley x) ^ (4 : ℕ)
    have hzUnit : (starRingEnd ℂ) z * z = 1 := by
      change (starRingEnd ℂ) ((realCayley x) ^ (4 : ℕ)) * (realCayley x) ^ (4 : ℕ) = 1
      rw [Complex.conj_mul', norm_pow, norm_realCayley]
      norm_num
    have hz : z ≠ 0 := by
      intro hzero
      rw [hzero] at hzUnit
      norm_num at hzUnit
    have hcP : (starRingEnd ℂ) (diskMultiplierLineBoundary P x) ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hxP
    have hcD : (starRingEnd ℂ) (diskMultiplierLineBoundary D x) ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hxD
    change diskMultiplierLineBoundary D x / diskMultiplierLineBoundary P x =
      (starRingEnd ℂ)
          ((starRingEnd ℂ) z *
            (diskMultiplierLineBoundary P x / diskMultiplierLineBoundary D x /
              (starRingEnd ℂ)
                (diskMultiplierLineBoundary P x / diskMultiplierLineBoundary D x))) *
        (starRingEnd ℂ)
          ((z * diskMultiplierLineBoundary D x) /
            diskMultiplierLineBoundary P x)
    simp only [map_mul, map_div₀, starRingEnd_self_apply]
    field_simp [hcP, hcD]
    rw [← hzUnit]
    ring
  forward_nonzero := by
    refine ⟨(1 / 2 : ℂ), ?_, ?_⟩
    · norm_num [Metric.mem_ball, dist_zero_right]
    · change (1 / 2 : ℂ) ^ (4 : ℕ) *
          (1 - sectorCayleyValue
            (hardyFun (boundedPhaseHardy b hb hbound) (1 / 2 : ℂ))) ≠ 0
      apply mul_ne_zero
      · norm_num
      · intro hzero
        have hpos := one_sub_sectorCayleyValue_re_pos
          (boundedPhaseHardy_re_bound b hb hbound (1 / 2 : ℂ) (by norm_num))
        rw [hzero] at hpos
        norm_num at hpos

end

end GaloisForLFunctions.HTGeometry
