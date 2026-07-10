import GaloisForLFunctions.RHTower.XiThetaReaderConditioning
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace
import GaloisForLFunctions.RHTower.CanonicalPerronMellinSeam

/-!
# The positive theta half is a canonical unit-radius Perron source

The completed theta source is two-sided, but its critical trace is the cosine transform of the
real positive half.  This file proves that the actual positive half, not an abstract surrogate,
belongs to the `L²` source space used by the Perron--Mellin seam.

The proof is quantitative.  The theta-square expansion and the square-atom majorant bound the
positive source by its boundary theta mass times `exp (-2u)`.  Since the source is already in
`L¹`, this uniform bound promotes it to `L²`.  Its strict positive support then gives Perron radius
exactly one: every variable-Perron source charge with `1 < n - δ` tends to zero down the negative
lines.  Thus reflection contributes the conjugate half of the critical cosine trace; it is not an
additional asymptotic Perron charge.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- The total theta-square mass at the reflection boundary `u = 0`. -/
def xiThetaPositiveBoundaryMass : ℝ := evenKernel 0 1 - 1

/-- The boundary theta mass is strictly positive. -/
theorem xiThetaPositiveBoundaryMass_pos : 0 < xiThetaPositiveBoundaryMass := by
  exact evenKernel_zero_sub_one_pos (by norm_num)

/-- The positive theta source has an explicit exponential envelope whose constant is its boundary
mass. -/
theorem xiThetaPositiveSource_norm_le_boundaryMass_mul_exp (u : ℝ) :
    ‖xiThetaPositiveSource u‖ ≤
      xiThetaPositiveBoundaryMass * Real.exp (-2 * u) := by
  by_cases hu : 0 < u
  · have hsU0 := hasSum_nat_cosKernel₀ 0 (Real.exp_pos u)
    have hsU : HasSum (fun k : ℕ =>
        2 * Real.exp (-Real.pi * (k + 1) ^ 2 * Real.exp u))
        (evenKernel 0 (Real.exp u) - 1) := by
      have hsU' : HasSum (fun k : ℕ =>
          2 * Real.exp (-Real.pi * (k + 1) ^ 2 * Real.exp u))
          (cosKernel (0 : UnitAddCircle) (Real.exp u) - 1) := by
        simpa using hsU0
      rwa [← congrFun evenKernel_eq_cosKernel_of_zero (Real.exp u)] at hsU'
    have hsAtom : HasSum (fun k : ℕ => thetaSquareLogAtom (k + 1) u)
        (Real.exp (u / 4) * (evenKernel 0 (Real.exp u) - 1)) := by
      simpa only [thetaSquareLogAtom, Nat.cast_add, Nat.cast_one, mul_assoc,
        mul_left_comm, mul_comm] using hsU.mul_left (Real.exp (u / 4))
    have hs10 := hasSum_nat_cosKernel₀ 0 (by norm_num : (0 : ℝ) < 1)
    have hs1 : HasSum (fun k : ℕ =>
        2 * Real.exp (-Real.pi * (k + 1) ^ 2)) xiThetaPositiveBoundaryMass := by
      have hs1' : HasSum (fun k : ℕ =>
          2 * Real.exp (-Real.pi * (k + 1) ^ 2 * 1))
          (cosKernel (0 : UnitAddCircle) 1 - 1) := by
        simpa using hs10
      rw [← congrFun evenKernel_eq_cosKernel_of_zero (1 : ℝ)] at hs1'
      simpa [xiThetaPositiveBoundaryMass] using hs1'
    have hsMajor : HasSum (fun k : ℕ =>
        (2 * Real.exp (-Real.pi * (k + 1) ^ 2)) * Real.exp (-2 * u))
        (xiThetaPositiveBoundaryMass * Real.exp (-2 * u)) := by
      simpa only using hs1.mul_right (Real.exp (-2 * u))
    have hterm : ∀ k : ℕ, thetaSquareLogAtom (k + 1) u ≤
        (2 * Real.exp (-Real.pi * (k + 1) ^ 2)) * Real.exp (-2 * u) := by
      intro k
      simpa only [Nat.cast_add, Nat.cast_one] using
        (thetaSquareLogAtom_le_exp_majorant (m := k + 1)
          (Nat.succ_le_succ (Nat.zero_le k)) hu.le)
    have hsumle : Real.exp (u / 4) * (evenKernel 0 (Real.exp u) - 1) ≤
        xiThetaPositiveBoundaryMass * Real.exp (-2 * u) := by
      rw [← hsAtom.tsum_eq, ← hsMajor.tsum_eq]
      exact hsAtom.summable.tsum_le_tsum hterm hsMajor.summable
    rw [xiThetaPositiveSource, indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu),
      xiThetaLogSource_eq_positiveFormula hu, xiThetaPositiveFormula, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (u / 4)),
      abs_of_pos (evenKernel_zero_sub_one_pos (Real.exp_pos u))]
    exact hsumle
  · have hnot : u ∉ Ioi (0 : ℝ) := hu
    rw [xiThetaPositiveSource, indicator_of_notMem hnot, norm_zero]
    exact mul_nonneg xiThetaPositiveBoundaryMass_pos.le (Real.exp_pos _).le

/-- The boundary theta mass is a global `L∞` bound for the positive source. -/
theorem xiThetaPositiveSource_norm_le_boundaryMass (u : ℝ) :
    ‖xiThetaPositiveSource u‖ ≤ xiThetaPositiveBoundaryMass := by
  by_cases hu : 0 < u
  · calc
      ‖xiThetaPositiveSource u‖ ≤
          xiThetaPositiveBoundaryMass * Real.exp (-2 * u) :=
        xiThetaPositiveSource_norm_le_boundaryMass_mul_exp u
      _ ≤ xiThetaPositiveBoundaryMass * 1 := by
        apply mul_le_mul_of_nonneg_left _ xiThetaPositiveBoundaryMass_pos.le
        exact Real.exp_le_one_iff.mpr (by linarith)
      _ = xiThetaPositiveBoundaryMass := mul_one _
  · have hnot : u ∉ Ioi (0 : ℝ) := hu
    rw [xiThetaPositiveSource, indicator_of_notMem hnot, norm_zero]
    exact xiThetaPositiveBoundaryMass_pos.le

/-- The actual positive theta half belongs to complex `L²(ℝ)`, with no source-existence
hypothesis. -/
theorem xiThetaPositiveSource_memLp_two :
    MemLp xiThetaPositiveSource 2 volume := by
  have hmeas : AEStronglyMeasurable xiThetaPositiveSource volume :=
    xiThetaPositiveSource_integrable.1
  have hdomInt : Integrable (fun u : ℝ =>
      xiThetaPositiveBoundaryMass * ‖xiThetaPositiveSource u‖) :=
    xiThetaPositiveSource_integrable.norm.const_mul xiThetaPositiveBoundaryMass
  have hsqInt : Integrable (fun u : ℝ => ‖xiThetaPositiveSource u‖ ^ 2) := by
    refine hdomInt.mono' (hmeas.norm.pow 2) ?_
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hnorm0 : 0 ≤ ‖xiThetaPositiveSource u‖ := norm_nonneg _
    nlinarith [xiThetaPositiveSource_norm_le_boundaryMass u]
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hsqInt

/-- The actual positive theta half as an element of the Perron source Hilbert space. -/
def xiThetaPositiveSourceL2 : SoninL2 :=
  xiThetaPositiveSource_memLp_two.toLp xiThetaPositiveSource

/-- The canonical `L²` class agrees almost everywhere with the explicit theta source. -/
theorem xiThetaPositiveSourceL2_ae :
    (fun u : ℝ => xiThetaPositiveSourceL2 u) =ᵐ[volume] xiThetaPositiveSource :=
  MemLp.coeFn_toLp xiThetaPositiveSource_memLp_two

/-- The canonical `L²` theta source discharges lower support at threshold zero. -/
theorem xiThetaPositiveSourceL2_hasAELowerSupport :
    HasAELowerSupport (fun u : ℝ => xiThetaPositiveSourceL2 u) 0 := by
  filter_upwards [xiThetaPositiveSourceL2_ae,
    xiThetaPositiveSource_hasAELowerSupport] with u hcoe hsupp
  intro hu
  rw [hcoe]
  exact hsupp hu

/-- Any `L²` source supported above zero has vanishing negative-line Perron charge beyond unit
radius.  This is the zero-threshold specialization of the general geometric source bound. -/
theorem zeroSupportedSourcePerronCharge_tendsto_zero
    (g : SoninL2) (hsupp : HasAELowerSupport (fun u : ℝ => g u) 0)
    {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hgap : 1 < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ =>
      negativeMellinSourcePerronCharge g 0 hsupp M n δ) atTop (𝓝 0) := by
  let H : ℕ → ℝ := fun _ => perronFlankL2Constant * ‖g‖
  have hH0 : ∀ᶠ M : ℕ in atTop, 0 ≤ H M := by
    exact Eventually.of_forall fun M => by
      dsimp [H]
      exact mul_nonneg perronFlankL2Constant_pos.le (norm_nonneg _)
  have hH : ∀ᶠ M : ℕ in atTop,
      H M ≤ (perronFlankL2Constant * ‖g‖) * (1 : ℝ) ^ M := by
    exact Eventually.of_forall fun M => by simp [H]
  have hDpos : 0 < perronSupportScaleAt n δ := lt_trans zero_lt_one hgap
  have hdecay : Tendsto (fun M : ℕ =>
      H M * perronSupportScaleAt n δ ^ (1 - (M : ℝ))) atTop (𝓝 0) :=
    tendsto_flank_product_of_geometric_envelope (by norm_num : (0 : ℝ) ≤ 1)
      hDpos hgap hH0 hH
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop 2] with M hM
    simpa only [H, Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, one_mul] using
      negativeMellinSourcePerronCharge_norm_le g 0 hsupp hn hM hδ0 hδn
  · simpa only [H, Nat.cast_zero, neg_zero, zero_mul, mul_zero,
      Real.exp_zero, one_mul] using hdecay

/-- Beyond unit Perron radius, the actual positive theta source carries asymptotically no
negative-line coefficient charge. -/
theorem xiThetaPositiveSourcePerronCharge_tendsto_zero
    {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ))
    (hgap : 1 < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ =>
      negativeMellinSourcePerronCharge xiThetaPositiveSourceL2 0
        xiThetaPositiveSourceL2_hasAELowerSupport M n δ) atTop (𝓝 0) :=
  zeroSupportedSourcePerronCharge_tendsto_zero xiThetaPositiveSourceL2
    xiThetaPositiveSourceL2_hasAELowerSupport hn hδ0 hδn hgap

/-- **Canonical theta-seam coefficient recovery.**  If a Dirichlet carrier has the completed
vertical `L²` energy and horizontal escape required by the Perron contour, its canonical defect
relative to the actual positive theta source recovers every coefficient beyond unit radius.  The
cross-line defect is constructed internally; no defect or abstract source-existence Prop remains. -/
theorem xiThetaPerronCanonicalSeamCoefficient_tendsto_coefficient_of_flankL2Energy
    {F : ℂ → ℂ} {c δ : ℝ} {coeff : ℕ → ℂ} {B : ℕ → ℝ}
    {n : ℕ}
    (henergy : HasPerronCarrierFlankL2Energy F B)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδn : δ < (n : ℝ))
    (hgap : 1 < perronSupportScaleAt n δ) :
    Tendsto (fun M : ℕ => perronMellinSeamCoefficient
      (canonicalCrossLineMellinDefect F xiThetaPositiveSourceL2 0
        xiThetaPositiveSourceL2_hasAELowerSupport) M n δ) atTop
      (𝓝 (coeff n)) := by
  let hsupp := xiThetaPositiveSourceL2_hasAELowerSupport
  let Δ := canonicalCrossLineMellinDefect F xiThetaPositiveSourceL2 0 hsupp
  let source : ℕ → ℂ := fun M =>
    negativeMellinSourcePerronCharge xiThetaPositiveSourceL2 0 hsupp M n δ
  have hsource : Tendsto source atTop (𝓝 0) := by
    simpa only [source, hsupp] using
      xiThetaPositiveSourcePerronCharge_tendsto_zero hn hδ0 hδn hgap
  have hdef : HasEventuallyCrossLineMellinDefect F xiThetaPositiveSourceL2 0 hsupp Δ :=
    hasEventuallyCrossLineMellinDefect_canonical hsupp
      (eventually_memLp_negativeLine_of_flankL2Energy hF henergy)
  have hvarEscape : HasVariablePerronBoundaryEscape F c n :=
    (hhorizontal.hasVariablePerronHorizontalEscape hF hc0 hn).hasVariablePerronBoundaryEscape
      hc0 hsum hF hFeq hn
  have hescape : ∀ᶠ M : ℕ in atTop, HasPerronBoundaryEscapeAt F c n δ M :=
    hvarEscape δ hδ0 hδ1 hδn
  have heq : ∀ᶠ M : ℕ in atTop,
      perronMellinSeamResidue Δ M n δ = coeff n * (δ : ℂ) - source M := by
    filter_upwards [hdef, hescape, eventually_ge_atTop 2] with M hMdef hMescape hM
    have hsplit := coefficient_eq_sourceCharge_add_seamResidue_of_defectAt
      hsupp hMdef hMescape hc0 hsum hF hFeq hn hM hδ0 hδ1 hδn
    dsimp only [source]
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hsplit.symm
  have hres : Tendsto (fun M : ℕ => perronMellinSeamResidue Δ M n δ) atTop
      (𝓝 (coeff n * (δ : ℂ))) := by
    have hlim : Tendsto (fun M => coeff n * (δ : ℂ) - source M) atTop
        (𝓝 (coeff n * (δ : ℂ))) := by
      simpa using tendsto_const_nhds.sub hsource
    exact hlim.congr' (heq.mono fun _ h => h.symm)
  have hδne : (δ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hδ0
  have hscaled := hres.const_mul (δ : ℂ)⁻¹
  have hval : (δ : ℂ)⁻¹ * (coeff n * (δ : ℂ)) = coeff n := by
    calc
      (δ : ℂ)⁻¹ * (coeff n * (δ : ℂ)) = coeff n * ((δ : ℂ)⁻¹ * (δ : ℂ)) := by ring
      _ = coeff n := by rw [inv_mul_cancel₀ hδne, mul_one]
  rw [hval] at hscaled
  simpa only [perronMellinSeamCoefficient, Δ, hsupp] using hscaled

end RHTower
