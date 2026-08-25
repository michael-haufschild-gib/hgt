import GaloisForLFunctions.HTGeometry.DominatedSeriesToLp
import GaloisForLFunctions.HTGeometry.GeneralizedSchurKernelRankProfile
import GaloisForLFunctions.HTGeometry.GoldenRuleAmplitude
import GaloisForLFunctions.HTGeometry.HardyDiskBoundary
import GaloisForLFunctions.HTGeometry.HardyDiskCyclic
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.HTGeometry.UnimodularMulLp
import GaloisForLFunctions.HTGeometry.MultiplierClosedGraph
import GaloisForLFunctions.HTGeometry.SzegoBoundaryH2

/-!
# Radial boundary values of bounded disk multipliers

Bounded analytic disk multipliers are evaluated on canonical cofinal circles.  Their literal
continuous radial values represent the coefficient-space radial synthesis, hence converge strongly
to the exact Riesz--Fischer boundary.  An almost-everywhere convergent subsequence then transfers
the analytic sup bound to that boundary representative.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal lp

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal radial value of a bounded disk multiplier on the circle. -/
def diskMultiplierRadialBoundaryFun (n : ℕ) (φ : DiskMultiplier) (z : Circle) : ℂ :=
  φ.fn ((hardyDiskAbelRadius n : ℂ) * (z : ℂ))

theorem memLp_diskMultiplierRadialBoundaryFun (n : ℕ) (φ : DiskMultiplier) :
    MemLp (diskMultiplierRadialBoundaryFun n φ) 2 circleLebesgue := by
  let r := hardyDiskAbelRadius n
  have harg : ∀ z : Circle, (r : ℂ) * (z : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    intro z
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
    simpa [r] using hardyDiskAbelRadius_lt_one n
  have hcont : Continuous (diskMultiplierRadialBoundaryFun n φ) := by
    change Continuous (φ.fn ∘ fun z : Circle => (r : ℂ) * (z : ℂ))
    exact φ.diff.continuousOn.comp_continuous
      (continuous_const.mul continuous_subtype_val) harg
  apply MemLp.of_bound hcont.aestronglyMeasurable φ.bd
  filter_upwards with z
  exact φ.bd_le _ (harg z)

/-- Literal radial evaluation and coefficient radial synthesis define the same circle (L²)
vector. -/
theorem diskMultiplierRadialBoundary_toLp_eq (n : ℕ) (φ : DiskMultiplier) :
    (memLp_diskMultiplierRadialBoundaryFun n φ).toLp
        (diskMultiplierRadialBoundaryFun n φ) =
      hardyDiskRadialBoundary n (hardyOf φ) := by
  let r := hardyDiskAbelRadius n
  let f := hardyOf φ
  let term : ℕ → Circle → ℂ := fun k z =>
    ((r : ℂ) ^ k * f k) * (z : ℂ) ^ k
  let g : ℕ → ℝ := fun k => ‖f‖ * r ^ k
  have hgsum : Summable g := by
    exact (summable_geometric_of_lt_one (hardyDiskAbelRadius_nonneg n)
      (hardyDiskAbelRadius_lt_one n)).mul_left ‖f‖
  have hgnn : ∀ k, 0 ≤ g k := fun k => by
    exact mul_nonneg (norm_nonneg _) (pow_nonneg (hardyDiskAbelRadius_nonneg n) _)
  have hbd : ∀ k, ∀ᵐ z ∂circleLebesgue, ‖term k z‖ ≤ g k := by
    intro k
    filter_upwards with z
    change ‖((r : ℂ) ^ k * f k) * (z : ℂ) ^ k‖ ≤ ‖f‖ * r ^ k
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
    simp only [Circle.norm_coe, one_pow, mul_one]
    simpa [mul_comm, r] using
      mul_le_mul_of_nonneg_right (hardyDisk_norm_coord_le f k)
        (pow_nonneg (hardyDiskAbelRadius_nonneg n) k)
  have hpt : ∀ᵐ z ∂circleLebesgue,
      HasSum (fun k => term k z) (diskMultiplierRadialBoundaryFun n φ z) := by
    filter_upwards with z
    have harg : ‖(r : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
      simpa [r] using hardyDiskAbelRadius_lt_one n
    have hs := (summable_hardyDisk_terms f harg).hasSum
    change HasSum (fun k => f k * ((r : ℂ) * (z : ℂ)) ^ k)
      (hardyFun f ((r : ℂ) * (z : ℂ))) at hs
    have hval : hardyFun f ((r : ℂ) * (z : ℂ)) =
        φ.fn ((r : ℂ) * (z : ℂ)) := hardyFun_hardyOf φ harg
    rw [hval] at hs
    change HasSum (fun k => term k z) (φ.fn ((r : ℂ) * (z : ℂ)))
    exact hs.congr_fun fun k => by
      change ((r : ℂ) ^ k * f k) * (z : ℂ) ^ k =
        f k * ((r : ℂ) * (z : ℂ)) ^ k
      rw [mul_pow]
      ring
  have hmem : ∀ k, MemLp (term k) 2 circleLebesgue := by
    intro k
    exact (circleMonomial_memLp circleLebesgue k).const_mul ((r : ℂ) ^ k * f k)
  have hactual := hasSum_toLp_of_ae_dominated hgsum hgnn hbd hpt hmem
    (memLp_diskMultiplierRadialBoundaryFun n φ)
  have htermLp : ∀ k,
      (hmem k).toLp (term k) =
        ((r : ℂ) ^ k * f k) • circleMonomialLp circleLebesgue k := by
    intro k
    apply Lp.ext
    filter_upwards [(hmem k).coeFn_toLp,
      Lp.coeFn_smul ((r : ℂ) ^ k * f k) (circleMonomialLp circleLebesgue k),
      circleMonomialLp_coeFn_ae circleLebesgue k] with z hz hsmul hmono
    rw [hz, hsmul]
    change term k z = ((r : ℂ) ^ k * f k) *
      ((circleMonomialLp circleLebesgue k : Circle → ℂ) z)
    rw [hmono]
  have hrcoeff : Memℓp (fun k => (r : ℂ) ^ k * f k) 2 := by
    have hrle : ∀ k, ‖(r : ℂ) ^ k‖ ≤ 1 := by
      intro k
      rw [norm_pow, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg n)]
      exact pow_le_one₀ (hardyDiskAbelRadius_nonneg n)
        (hardyDiskAbelRadius_lt_one n).le
    exact (lp.memℓp f).mono' (fun k => by
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hrle k) (norm_nonneg (f k)))
  have habstract := hasSum_circleMonomial_smul_circleRieszFischerOfNat
    (fun k => (r : ℂ) ^ k * f k) hrcoeff
  have hriesz :
      circleRieszFischerOfNat (fun k => (r : ℂ) ^ k * f k) hrcoeff =
        hardyDiskRadialBoundary n f := by
    rw [hardyDiskRadialBoundary, circleRieszFischerOfNat]
    congr 3
    funext k
    cases k with
    | ofNat k => simp [r, radialMult]
    | negSucc k => simp [radialMult]
  rw [hriesz] at habstract
  symm
  apply tendsto_nhds_unique habstract
  exact hactual.congr_fun fun k => (htermLp k).symm

/-- The exact Riesz--Fischer boundary representative of a bounded analytic multiplier. -/
def diskMultiplierBoundaryFun (φ : DiskMultiplier) : Circle → ℂ :=
  (hardyDiskBoundary (hardyOf φ) : Circle → ℂ)

private theorem aemeasurable_diskMultiplierBoundaryFun (φ : DiskMultiplier) :
    AEMeasurable (diskMultiplierBoundaryFun φ) circleLebesgue :=
  (Lp.aestronglyMeasurable (hardyDiskBoundary (hardyOf φ))).aemeasurable

/-- A measurable representative of the Riesz--Fischer boundary class. -/
def diskMultiplierBoundaryMeasurableRep (φ : DiskMultiplier) : Circle → ℂ :=
  AEMeasurable.mk (diskMultiplierBoundaryFun φ)
    (aemeasurable_diskMultiplierBoundaryFun φ)

theorem measurable_diskMultiplierBoundaryMeasurableRep (φ : DiskMultiplier) :
    Measurable (diskMultiplierBoundaryMeasurableRep φ) :=
  (aemeasurable_diskMultiplierBoundaryFun φ).measurable_mk

theorem diskMultiplierBoundaryMeasurableRep_ae (φ : DiskMultiplier) :
    diskMultiplierBoundaryMeasurableRep φ =ᵐ[circleLebesgue]
      diskMultiplierBoundaryFun φ :=
  (aemeasurable_diskMultiplierBoundaryFun φ).ae_eq_mk.symm

/-- Everywhere measurable and everywhere bounded representative of the multiplier boundary. -/
def diskMultiplierBoundarySymbol (φ : DiskMultiplier) (z : Circle) : ℂ :=
  if ‖diskMultiplierBoundaryMeasurableRep φ z‖ ≤ φ.bd then
    diskMultiplierBoundaryMeasurableRep φ z else 0

theorem measurable_diskMultiplierBoundarySymbol (φ : DiskMultiplier) :
    Measurable (diskMultiplierBoundarySymbol φ) := by
  apply Measurable.ite
  · exact measurableSet_le
      (measurable_diskMultiplierBoundaryMeasurableRep φ).norm measurable_const
  · exact measurable_diskMultiplierBoundaryMeasurableRep φ
  · exact measurable_const

theorem norm_diskMultiplierBoundarySymbol_le (φ : DiskMultiplier) (z : Circle) :
    ‖diskMultiplierBoundarySymbol φ z‖ ≤ φ.bd := by
  rw [diskMultiplierBoundarySymbol]
  split_ifs with h
  · exact h
  · simpa using φ.bd_nonneg

/-- Literal bounded circle multiplication by the analytic boundary symbol. -/
def diskMultiplierBoundaryMul (φ : DiskMultiplier) :
    Lp ℂ 2 circleLebesgue →L[ℂ] Lp ℂ 2 circleLebesgue :=
  lpBoundedMulCLM (p := 2) (μ := circleLebesgue)
    (measurable_diskMultiplierBoundarySymbol φ) φ.bd_nonneg
    (norm_diskMultiplierBoundarySymbol_le φ)

/-- A cofinal radial subsequence converges almost everywhere to the exact boundary representative. -/
theorem exists_diskMultiplierRadialBoundary_subseq_ae (φ : DiskMultiplier) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂circleLebesgue,
        Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) φ z)
          atTop (𝓝 (diskMultiplierBoundaryFun φ z)) := by
  have hL2 : Tendsto
      (fun n => (memLp_diskMultiplierRadialBoundaryFun n φ).toLp
        (diskMultiplierRadialBoundaryFun n φ))
      atTop (𝓝 (hardyDiskBoundary (hardyOf φ))) := by
    convert tendsto_hardyDiskRadialBoundary (hardyOf φ) using 1
    funext n
    exact diskMultiplierRadialBoundary_toLp_eq n φ
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto hL2
  have hcoe : ∀ᵐ z ∂circleLebesgue, ∀ i : ℕ,
      (((memLp_diskMultiplierRadialBoundaryFun (ns i) φ).toLp
        (diskMultiplierRadialBoundaryFun (ns i) φ) :
          Lp ℂ 2 circleLebesgue) : Circle → ℂ) z =
        diskMultiplierRadialBoundaryFun (ns i) φ z := by
    rw [ae_all_iff]
    intro i
    exact (memLp_diskMultiplierRadialBoundaryFun (ns i) φ).coeFn_toLp
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hcoe] with z hz hzc
  change Tendsto (fun i => diskMultiplierRadialBoundaryFun (ns i) φ z)
    atTop (𝓝 ((hardyDiskBoundary (hardyOf φ) : Circle → ℂ) z))
  convert hz using 1
  funext i
  exact (hzc i).symm

/-- The a.e. radial extraction remains available along any prescribed cofinal subsequence. -/
theorem exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono
    (φ : DiskMultiplier) {base : ℕ → ℕ} (hbase : StrictMono base) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂circleLebesgue,
        Tendsto (fun i => diskMultiplierRadialBoundaryFun (base (ns i)) φ z)
          atTop (𝓝 (diskMultiplierBoundaryFun φ z)) := by
  have hL2 : Tendsto
      (fun n => (memLp_diskMultiplierRadialBoundaryFun (base n) φ).toLp
        (diskMultiplierRadialBoundaryFun (base n) φ))
      atTop (𝓝 (hardyDiskBoundary (hardyOf φ))) := by
    have hradial := (tendsto_hardyDiskRadialBoundary (hardyOf φ)).comp
      hbase.tendsto_atTop
    convert hradial using 1
    funext n
    exact diskMultiplierRadialBoundary_toLp_eq (base n) φ
  obtain ⟨ns, hns, hae⟩ := exists_subseq_ae_tendsto hL2
  have hcoe : ∀ᵐ z ∂circleLebesgue, ∀ i : ℕ,
      (((memLp_diskMultiplierRadialBoundaryFun (base (ns i)) φ).toLp
        (diskMultiplierRadialBoundaryFun (base (ns i)) φ) :
          Lp ℂ 2 circleLebesgue) : Circle → ℂ) z =
        diskMultiplierRadialBoundaryFun (base (ns i)) φ z := by
    rw [ae_all_iff]
    intro i
    exact (memLp_diskMultiplierRadialBoundaryFun (base (ns i)) φ).coeFn_toLp
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae, hcoe] with z hz hzc
  change Tendsto (fun i => diskMultiplierRadialBoundaryFun (base (ns i)) φ z)
    atTop (𝓝 ((hardyDiskBoundary (hardyOf φ) : Circle → ℂ) z))
  convert hz using 1
  funext i
  exact (hzc i).symm

/-- Riesz--Fischer boundary values multiply exactly for bounded analytic multipliers. -/
theorem diskMultiplierBoundaryFun_mul_ae (φ ψ : DiskMultiplier) :
    diskMultiplierBoundaryFun (φ.mul ψ) =ᵐ[circleLebesgue]
      fun z => diskMultiplierBoundaryFun φ z * diskMultiplierBoundaryFun ψ z := by
  obtain ⟨nsφ, hnsφ, haeφ⟩ := exists_diskMultiplierRadialBoundary_subseq_ae φ
  obtain ⟨nsψ, hnsψ, haeψ⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono ψ hnsφ
  let base : ℕ → ℕ := fun i => nsφ (nsψ i)
  have hbase : StrictMono base := hnsφ.comp hnsψ
  obtain ⟨nsχ, hnsχ, haeχ⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono (φ.mul ψ) hbase
  have haeφ' : ∀ᵐ z ∂circleLebesgue,
      Tendsto (fun i => diskMultiplierRadialBoundaryFun (base (nsχ i)) φ z)
        atTop (𝓝 (diskMultiplierBoundaryFun φ z)) := by
    filter_upwards [haeφ] with z hz
    exact (hz.comp hnsψ.tendsto_atTop).comp hnsχ.tendsto_atTop
  have haeψ' : ∀ᵐ z ∂circleLebesgue,
      Tendsto (fun i => diskMultiplierRadialBoundaryFun (base (nsχ i)) ψ z)
        atTop (𝓝 (diskMultiplierBoundaryFun ψ z)) := by
    filter_upwards [haeψ] with z hz
    exact hz.comp hnsχ.tendsto_atTop
  filter_upwards [haeχ, haeφ', haeψ'] with z hχ hφ hψ
  have hprod := hφ.mul hψ
  apply tendsto_nhds_unique hχ
  convert hprod using 1
  funext i
  rfl

/-- The analytic sup bound passes to the exact boundary representative almost everywhere. -/
theorem ae_norm_diskMultiplierBoundaryFun_le (φ : DiskMultiplier) :
    ∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun φ z‖ ≤ φ.bd := by
  obtain ⟨ns, -, hae⟩ := exists_diskMultiplierRadialBoundary_subseq_ae φ
  filter_upwards [hae] with z hz
  have hnorm : Tendsto
      (fun i => ‖diskMultiplierRadialBoundaryFun (ns i) φ z‖)
      atTop (𝓝 ‖diskMultiplierBoundaryFun φ z‖) :=
    (continuous_norm.tendsto _).comp hz
  apply le_of_tendsto hnorm
  exact Eventually.of_forall fun i =>
    φ.bd_le _ (by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg (ns i)), Circle.norm_coe, mul_one]
      exact hardyDiskAbelRadius_lt_one (ns i))

theorem diskMultiplierBoundarySymbol_ae (φ : DiskMultiplier) :
    diskMultiplierBoundarySymbol φ =ᵐ[circleLebesgue]
      diskMultiplierBoundaryFun φ := by
  filter_upwards [diskMultiplierBoundaryMeasurableRep_ae φ,
    ae_norm_diskMultiplierBoundaryFun_le φ] with z hrep hbd
  rw [diskMultiplierBoundarySymbol, if_pos]
  · exact hrep
  · rwa [hrep]

theorem diskMultiplierBoundaryMul_coeFn (φ : DiskMultiplier)
    (f : Lp ℂ 2 circleLebesgue) :
    (diskMultiplierBoundaryMul φ f : Circle → ℂ) =ᵐ[circleLebesgue]
      fun z => diskMultiplierBoundaryFun φ z * (f : Circle → ℂ) z := by
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := circleLebesgue)
      (measurable_diskMultiplierBoundarySymbol φ) φ.bd_nonneg
      (norm_diskMultiplierBoundarySymbol_le φ) f,
    diskMultiplierBoundarySymbol_ae φ] with z hmul hsymbol
  change ((lpBoundedMulCLM (p := 2) (μ := circleLebesgue)
      (measurable_diskMultiplierBoundarySymbol φ) φ.bd_nonneg
      (norm_diskMultiplierBoundarySymbol_le φ) f : Lp ℂ 2 circleLebesgue) :
        Circle → ℂ) z = _
  rw [hmul, hsymbol]

/-- Circle boundary multiplication realizes analytic multiplication on bounded Hardy vectors. -/
theorem diskMultiplierBoundaryMul_apply_hardyOf (φ ψ : DiskMultiplier) :
    diskMultiplierBoundaryMul φ (hardyDiskBoundary (hardyOf ψ)) =
      hardyDiskBoundary (hardyOf (φ.mul ψ)) := by
  apply Lp.ext
  filter_upwards [diskMultiplierBoundaryMul_coeFn φ
      (hardyDiskBoundary (hardyOf ψ)),
    diskMultiplierBoundaryFun_mul_ae φ ψ] with z hmul hprod
  change (diskMultiplierBoundaryMul φ (hardyDiskBoundary (hardyOf ψ)) :
      Circle → ℂ) z = diskMultiplierBoundaryFun (φ.mul ψ) z
  rw [hmul, hprod]
  rfl

/-- An isometric multiplier with unit analytic bound has unimodular boundary almost everywhere. -/
theorem ae_norm_diskMultiplierBoundaryFun_eq_one (B : DiskMultiplier)
    (hBbd : B.bd = 1) (hB : HardyMultiplierIsometry B) :
    ∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun B z‖ = 1 := by
  let b : Lp ℂ 2 circleLebesgue := hardyDiskBoundary (hardyOf B)
  have honeNorm : ‖hardyOne‖ = 1 := by
    rw [hardyOne, lp.norm_single (by norm_num)]
    norm_num
  have hbNorm : ‖b‖ = 1 := by
    change ‖hardyDiskBoundary (hardyOf B)‖ = 1
    rw [LinearIsometry.norm_map, hardyOf, hB hardyOne, honeNorm]
  have hle : ∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun B z‖ ≤ 1 := by
    simpa [hBbd] using ae_norm_diskMultiplierBoundaryFun_le B
  let w : Circle → ℝ := fun z => 1 - ‖diskMultiplierBoundaryFun B z‖ ^ 2
  have hw0 : 0 ≤ᵐ[circleLebesgue] w := by
    filter_upwards [hle] with z hz
    dsimp [w]
    nlinarith [norm_nonneg (diskMultiplierBoundaryFun B z)]
  have hnormInt : Integrable
      (fun z => ‖diskMultiplierBoundaryFun B z‖ ^ 2) circleLebesgue := by
    have h := (Lp.memLp b).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [b, diskMultiplierBoundaryFun] using h
  have hconst : Integrable (fun _ : Circle => (1 : ℝ)) circleLebesgue :=
    integrable_const 1
  have hwInt : Integrable w circleLebesgue := hconst.sub hnormInt
  have hwIntegral : ∫ z, w z ∂circleLebesgue = 0 := by
    rw [integral_sub hconst hnormInt]
    change (∫ _a : Circle, (1 : ℝ) ∂circleLebesgue) -
      ∫ a : Circle, ‖(b : Circle → ℂ) a‖ ^ 2 ∂circleLebesgue = 0
    have hbInt := lpTwo_norm_sq_eq_integral b
    rw [hbNorm, one_pow] at hbInt
    rw [← hbInt]
    simp
  have hwae : w =ᵐ[circleLebesgue] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hw0 hwInt).mp hwIntegral
  filter_upwards [hwae] with z hz
  dsimp [w] at hz
  nlinarith [norm_nonneg (diskMultiplierBoundaryFun B z)]

/-! ## Exact multiplier intertwining on the full Hardy space -/

/-- The bounded analytic monomial `z ↦ z^n`. -/
def diskMonomialMultiplier (n : ℕ) : DiskMultiplier where
  fn := fun z => z ^ n
  diff := differentiableOn_id.pow n
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := fun z hz => by
    rw [norm_pow]
    have hle : ‖z‖ ≤ 1 := by
      exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hz)
    exact pow_le_one₀ (norm_nonneg z) hle

theorem hardyOf_diskMonomialMultiplier (n : ℕ) :
    hardyOf (diskMonomialMultiplier n) =
      (lp.single 2 n (1 : ℂ) : HardyDisk) := by
  refine hardyDisk_ext fun z hz => ?_
  rw [hardyFun_hardyOf (diskMonomialMultiplier n) hz,
    hardyFun_single n hz]
  rfl

/-- Boundary multiplication by a bounded analytic symbol intertwines the coefficient Hardy
multiplier on every Hardy vector. -/
theorem diskMultiplierBoundaryMul_apply (φ : DiskMultiplier) (f : HardyDisk) :
    diskMultiplierBoundaryMul φ (hardyDiskBoundary f) =
      hardyDiskBoundary (hardyMul φ f) := by
  let S : HardyDisk →L[ℂ] Lp ℂ 2 circleLebesgue :=
    (diskMultiplierBoundaryMul φ).comp hardyDiskBoundary.toContinuousLinearMap
  let T : HardyDisk →L[ℂ] Lp ℂ 2 circleLebesgue :=
    hardyDiskBoundary.toContinuousLinearMap.comp (hardyMul φ)
  have hsingle : ∀ n : ℕ,
      S (lp.single 2 n (1 : ℂ) : HardyDisk) =
        T (lp.single 2 n (1 : ℂ) : HardyDisk) := by
    intro n
    rw [← hardyOf_diskMonomialMultiplier n]
    change diskMultiplierBoundaryMul φ
        (hardyDiskBoundary (hardyOf (diskMonomialMultiplier n))) =
      hardyDiskBoundary (hardyMul φ (hardyOf (diskMonomialMultiplier n)))
    rw [diskMultiplierBoundaryMul_apply_hardyOf, hardyOf, hardyOf,
      hardyMul_mul]
  change S f = T f
  have hsum : HasSum (fun n : ℕ =>
      (lp.single 2 n (f n) : HardyDisk)) f :=
    lp.hasSum_single (by norm_num) f
  have hS := hsum.map S S.continuous
  have hT := hsum.map T T.continuous
  have hterm :
      (fun n : ℕ => S (lp.single 2 n (f n) : HardyDisk)) =
        fun n : ℕ => T (lp.single 2 n (f n) : HardyDisk) := by
    funext n
    have hsmul : (lp.single 2 n (f n) : HardyDisk) =
        (f n) • (lp.single 2 n (1 : ℂ) : HardyDisk) := by
      apply lp.ext
      funext m
      by_cases hmn : m = n
      · subst m
        simp
      · simp [lp.single_apply, hmn]
    rw [hsmul, map_smul, map_smul, hsingle n]
  change HasSum (fun n : ℕ => S (lp.single 2 n (f n) : HardyDisk)) (S f) at hS
  change HasSum (fun n : ℕ => T (lp.single 2 n (f n) : HardyDisk)) (T f) at hT
  rw [hterm] at hS
  exact hS.unique hT

/-- Conversely, an almost-everywhere unimodular analytic boundary makes Hardy multiplication an
isometry.  Together with `ae_norm_diskMultiplierBoundaryFun_eq_one`, this identifies inner
multipliers intrinsically from the exact Riesz--Fischer boundary representative. -/
theorem hardyMultiplierIsometry_of_ae_norm_boundary_eq_one
    (B : DiskMultiplier)
    (hB : ∀ᵐ z ∂circleLebesgue, ‖diskMultiplierBoundaryFun B z‖ = 1) :
    HardyMultiplierIsometry B := by
  have hsymbol : ∀ᵐ z ∂circleLebesgue,
      ‖diskMultiplierBoundarySymbol B z‖ = 1 := by
    filter_upwards [diskMultiplierBoundarySymbol_ae B, hB] with z heq hnorm
    rwa [heq]
  intro f
  let g : Circle →ₘ[circleLebesgue] ℂ :=
    AEEqFun.mk (diskMultiplierBoundarySymbol B)
      (measurable_diskMultiplierBoundarySymbol B).aestronglyMeasurable
  have hgrep : (g : Circle → ℂ) =ᵐ[circleLebesgue]
      diskMultiplierBoundarySymbol B := by
    exact MeasureTheory.AEEqFun.coeFn_mk _ _
  have hg : ∀ᵐ z ∂circleLebesgue, ‖g z‖ = 1 := by
    filter_upwards [hsymbol, hgrep] with z hz hgz
    rw [hgz]
    exact hz
  have heq : diskMultiplierBoundaryMul B (hardyDiskBoundary f) =
      mulLp hg (hardyDiskBoundary f) := by
    apply Subtype.ext
    rw [coe_mulLp]
    apply AEEqFun.ext
    filter_upwards [diskMultiplierBoundaryMul_coeFn B (hardyDiskBoundary f),
      diskMultiplierBoundarySymbol_ae B, hgrep,
      AEEqFun.coeFn_mul g ((hardyDiskBoundary f : Lp ℂ 2 circleLebesgue) :
        Circle →ₘ[circleLebesgue] ℂ)] with z hmul hsymbol hgrep hprod
    rw [hmul, ← hsymbol, hprod, Pi.mul_apply, hgrep]
  calc
    ‖hardyMul B f‖ = ‖hardyDiskBoundary (hardyMul B f)‖ :=
      (LinearIsometry.norm_map hardyDiskBoundary _).symm
    _ = ‖diskMultiplierBoundaryMul B (hardyDiskBoundary f)‖ := by
      rw [diskMultiplierBoundaryMul_apply]
    _ = ‖mulLp hg (hardyDiskBoundary f)‖ := congrArg norm heq
    _ = ‖hardyDiskBoundary f‖ := norm_mulLp hg _
    _ = ‖f‖ := LinearIsometry.norm_map hardyDiskBoundary f

end

end GaloisForLFunctions.HTGeometry
