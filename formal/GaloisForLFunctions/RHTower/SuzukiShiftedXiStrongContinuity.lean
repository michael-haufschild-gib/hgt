import GaloisForLFunctions.RHTower.SuzukiShiftedXiBoundaryFactorization
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity

open Complex Filter MeasureTheory Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

def suzukiShiftedXiBoundaryPinned (omega₀ omega : ℝ) (u : ℝ) : ℂ :=
  if suzukiCanonicalE omega₀ (u : ℂ) = 0 then
    suzukiShiftedXiBoundary omega₀ u
  else suzukiShiftedXiBoundary omega u

theorem measurable_suzukiShiftedXiBoundaryPinned (omega₀ omega : ℝ) :
    Measurable (suzukiShiftedXiBoundaryPinned omega₀ omega) := by
  have hE : Measurable (fun u : ℝ => suzukiCanonicalE omega₀ (u : ℂ)) :=
    ((differentiable_suzukiCanonicalE omega₀).continuous.comp
      Complex.continuous_ofReal).measurable
  exact Measurable.ite (hE (measurableSet_singleton 0))
    (measurable_suzukiShiftedXiBoundary omega₀)
    (measurable_suzukiShiftedXiBoundary omega)

theorem norm_suzukiShiftedXiBoundaryPinned (omega₀ omega u : ℝ) :
    ‖suzukiShiftedXiBoundaryPinned omega₀ omega u‖ = 1 := by
  by_cases h : suzukiCanonicalE omega₀ (u : ℂ) = 0
  · simp [suzukiShiftedXiBoundaryPinned, h, norm_suzukiShiftedXiBoundary]
  · simp [suzukiShiftedXiBoundaryPinned, h, norm_suzukiShiftedXiBoundary]

theorem suzukiShiftedXiBoundaryPinned_ae_eq (omega₀ omega : ℝ) :
    suzukiShiftedXiBoundaryPinned omega₀ omega =ᵐ[volume]
      suzukiShiftedXiBoundary omega := by
  have hne : ∀ᵐ u : ℝ, suzukiCanonicalE omega₀ (u : ℂ) ≠ 0 :=
    ae_iff.mpr (by
      simpa only [not_ne_iff] using volume_suzukiCanonicalE_real_zeroSet omega₀)
  filter_upwards [hne] with u hu
  simp [suzukiShiftedXiBoundaryPinned, hu]

private theorem continuousAt_suzukiCanonicalTheta_shift
    {omega₀ u : ℝ} (hE : suzukiCanonicalE omega₀ (u : ℂ) ≠ 0) :
    ContinuousAt (fun omega : ℝ => suzukiCanonicalTheta omega (u : ℂ)) omega₀ := by
  change ContinuousAt (fun omega : ℝ =>
    xi (1 / 2 - (omega : ℂ) - (u : ℂ) * I) /
      xi (1 / 2 + (omega : ℂ) - (u : ℂ) * I)) omega₀
  have hnum : Continuous (fun omega : ℝ =>
      xi (1 / 2 - (omega : ℂ) - (u : ℂ) * I)) :=
    xi_differentiable.continuous.comp (by fun_prop)
  have hden : Continuous (fun omega : ℝ =>
      xi (1 / 2 + (omega : ℂ) - (u : ℂ) * I)) :=
    xi_differentiable.continuous.comp (by fun_prop)
  exact hnum.continuousAt.div hden.continuousAt (by
    simpa [suzukiCanonicalE] using hE)

theorem tendsto_suzukiShiftedXiBoundaryPinned
    {ι : Type*} {l : Filter ι} {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : Tendsto omega l (𝓝 omega₀)) (u : ℝ) :
    Tendsto (fun i => suzukiShiftedXiBoundaryPinned omega₀ (omega i) u) l
      (𝓝 (suzukiShiftedXiBoundary omega₀ u)) := by
  by_cases hE : suzukiCanonicalE omega₀ (u : ℂ) = 0
  · simpa [suzukiShiftedXiBoundaryPinned, hE] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => suzukiShiftedXiBoundary omega₀ u) l
        (𝓝 (suzukiShiftedXiBoundary omega₀ u)))
  · have htheta := (continuousAt_suzukiCanonicalTheta_shift hE).tendsto.comp homega
    have hEcont : Tendsto (fun i => suzukiCanonicalE (omega i) (u : ℂ)) l
        (𝓝 (suzukiCanonicalE omega₀ (u : ℂ))) := by
      have hc : ContinuousAt (fun omega : ℝ => suzukiCanonicalE omega (u : ℂ)) omega₀ := by
        change ContinuousAt (fun omega : ℝ =>
          xi (1 / 2 + (omega : ℂ) - (u : ℂ) * I)) omega₀
        exact (xi_differentiable.continuous.comp (by fun_prop)).continuousAt
      exact hc.tendsto.comp homega
    have hev : ∀ᶠ i in l, suzukiCanonicalE (omega i) (u : ℂ) ≠ 0 := by
      have hopen : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
      have hmem : suzukiCanonicalE omega₀ (u : ℂ) ∈ ({0}ᶜ : Set ℂ) := by simpa
      have := hEcont.eventually (hopen.mem_nhds hmem)
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using this
    rw [suzukiShiftedXiBoundary_eq_of_ne hE]
    refine htheta.congr' ?_
    filter_upwards [hev] with i hi
    simp only [suzukiShiftedXiBoundaryPinned, hE, if_false]
    rw [suzukiShiftedXiBoundary_eq_of_ne hi]
    rfl

private theorem suzukiShiftedXiBoundaryMulUnitary_apply_eq_lpBoundedMulCLM
    (omega : ℝ) (f : RealLineL2) :
    suzukiShiftedXiBoundaryMulUnitary omega f =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (measurable_suzukiShiftedXiBoundary omega) zero_le_one
        (fun u => (norm_suzukiShiftedXiBoundary omega u).le) f := by
  apply Lp.ext
  filter_upwards [suzukiShiftedXiBoundaryMulUnitary_ae omega f,
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
      (measurable_suzukiShiftedXiBoundary omega) zero_le_one
      (fun u => (norm_suzukiShiftedXiBoundary omega u).le) f] with u hU hM
  rw [hU, hM]

private theorem suzukiShiftedXiBoundaryMulUnitary_apply_eq_lpPinned
    (omega₀ omega : ℝ) (f : RealLineL2) :
    suzukiShiftedXiBoundaryMulUnitary omega f =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (measurable_suzukiShiftedXiBoundaryPinned omega₀ omega) zero_le_one
        (fun u => (norm_suzukiShiftedXiBoundaryPinned omega₀ omega u).le) f := by
  rw [suzukiShiftedXiBoundaryMulUnitary_apply_eq_lpBoundedMulCLM]
  exact DFunLike.congr_fun
    (lpBoundedMulCLM_congr
      (measurable_suzukiShiftedXiBoundary omega)
      (measurable_suzukiShiftedXiBoundaryPinned omega₀ omega)
      zero_le_one (fun u => (norm_suzukiShiftedXiBoundary omega u).le)
      zero_le_one (fun u => (norm_suzukiShiftedXiBoundaryPinned omega₀ omega u).le)
      (suzukiShiftedXiBoundaryPinned_ae_eq omega₀ omega).symm) f

/-- Literal shifted-Xi boundary multiplication is strongly continuous in the shift parameter,
including at a boundary-zero layer. -/
theorem tendsto_suzukiShiftedXiBoundaryMulUnitary_apply
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : Tendsto omega l (𝓝 omega₀)) (f : RealLineL2) :
    Tendsto (fun i => suzukiShiftedXiBoundaryMulUnitary (omega i) f) l
      (𝓝 (suzukiShiftedXiBoundaryMulUnitary omega₀ f)) := by
  have hmul := tendsto_lpBoundedMulCLM_apply
    (μ := (volume : Measure ℝ))
    (φ := fun i => suzukiShiftedXiBoundaryPinned omega₀ (omega i))
    (ψ := suzukiShiftedXiBoundary omega₀)
    (fun i => measurable_suzukiShiftedXiBoundaryPinned omega₀ (omega i))
    (measurable_suzukiShiftedXiBoundary omega₀)
    zero_le_one
    (fun i u => (norm_suzukiShiftedXiBoundaryPinned omega₀ (omega i) u).le)
    (fun u => (norm_suzukiShiftedXiBoundary omega₀ u).le)
    (tendsto_suzukiShiftedXiBoundaryPinned homega) f
  convert hmul using 1
  · funext i
    exact suzukiShiftedXiBoundaryMulUnitary_apply_eq_lpPinned omega₀ (omega i) f
  · exact congrArg nhds
      (suzukiShiftedXiBoundaryMulUnitary_apply_eq_lpBoundedMulCLM omega₀ f)

/-- The literal anti-causal shifted-Xi leakage is strongly continuous in the shift. -/
theorem tendsto_suzukiShiftedXiHardyLeakage_apply
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : Tendsto omega l (𝓝 omega₀)) (f : UpperHardyL2) :
    Tendsto (fun i => suzukiShiftedXiHardyLeakage (omega i) f) l
      (𝓝 (suzukiShiftedXiHardyLeakage omega₀ f)) := by
  change Tendsto (fun i => LowerHardyL2.orthogonalProjectionOnto
      (suzukiShiftedXiBoundaryMulUnitary (omega i) (f : RealLineL2))) l
    (𝓝 (LowerHardyL2.orthogonalProjectionOnto
      (suzukiShiftedXiBoundaryMulUnitary omega₀ (f : RealLineL2))))
  exact LowerHardyL2.orthogonalProjectionOnto.continuous.continuousAt.tendsto.comp
    (tendsto_suzukiShiftedXiBoundaryMulUnitary_apply homega (f : RealLineL2))

theorem tendsto_suzukiShiftedXiDiskHardyLeakage_apply
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : Tendsto omega l (𝓝 omega₀)) (f : HardyDisk) :
    Tendsto (fun i => suzukiShiftedXiDiskHardyLeakage (omega i) f) l
      (𝓝 (suzukiShiftedXiDiskHardyLeakage omega₀ f)) := by
  exact tendsto_suzukiShiftedXiHardyLeakage_apply homega
    (hardyDiskLineCayleyCLM f)

theorem inner_suzukiShiftedXiDiskHardyLeakage_eq_inner_infiniteLeakageCore
    {omega : ℝ} (homega : 0 ≤ omega) (f g : HardyDisk) :
    inner ℂ (suzukiShiftedXiDiskHardyLeakage omega f)
        (suzukiShiftedXiDiskHardyLeakage omega g) =
      inner ℂ (xiShiftInfiniteLeakageCore homega f)
        (xiShiftInfiniteLeakageCore homega g) := by
  let A := xiShiftInfiniteSchurNumerator homega
  let B := xiShiftPoleBlaschkeMultiplier homega
  have hBbd : B.bd = 1 := rfl
  have hBiso : HardyMultiplierIsometry B :=
    xiShiftPoleBlaschkeMultiplier_isometry homega
  let Q := diskBoundaryInnerQuotientLeakage A B hBbd hBiso
  let M := modelSpaceLeakageCore (hardyMultiplierModelSpace B) (hardyMul A)
  have hL : suzukiShiftedXiHardyLeakage omega =
      xiShiftBoundaryFactorizationPhase homega • Q := by
    simpa [A, B, Q] using
      suzukiShiftedXiHardyLeakage_eq_phase_smul_innerQuotientLeakage homega
  have hQ : Q = (diskBoundaryModelEmbedding B hBbd hBiso).comp
      (M.comp hardyLineDiskCayleyCLM) := by
    exact diskBoundaryInnerQuotientLeakage_eq_modelEmbedding_comp A B hBbd hBiso
  change inner ℂ
      (suzukiShiftedXiHardyLeakage omega (hardyDiskLineCayleyCLM f))
      (suzukiShiftedXiHardyLeakage omega (hardyDiskLineCayleyCLM g)) = _
  rw [hL]
  simp only [smul_apply]
  rw [inner_smul_left, inner_smul_right]
  have hphase : (starRingEnd ℂ) (xiShiftBoundaryFactorizationPhase homega) *
      xiShiftBoundaryFactorizationPhase homega = 1 := by
    rw [mul_comm, Complex.mul_conj, ← Complex.sq_norm,
      norm_xiShiftBoundaryFactorizationPhase, one_pow]
    norm_num
  rw [← mul_assoc, hphase, one_mul]
  rw [hQ]
  simp only [ContinuousLinearMap.comp_apply,
    hardyLineDiskCayleyCLM_apply_hardyDiskLineCayleyCLM]
  have hemb := (diskBoundaryModelEmbeddingIsometry B hBbd hBiso).inner_map_map
    (M f) (M g)
  change inner ℂ (diskBoundaryModelEmbedding B hBbd hBiso (M f))
      (diskBoundaryModelEmbedding B hBbd hBiso (M g)) =
    inner ℂ (M f) (M g) at hemb
  rw [hemb]
  rfl

/-- Gram matrix of the literal complete shifted-Xi disk model-space leakage core. -/
def xiShiftInfiniteLeakageGram {n : ℕ} {omega : ℝ} (homega : 0 ≤ omega)
    (v : Fin n → HardyDisk) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => inner ℂ (xiShiftInfiniteLeakageCore homega (v j))
    (xiShiftInfiniteLeakageCore homega (v k))

/-- The persistent block of the literal complete shifted-Xi model core converges through a layer. -/
theorem tendsto_xiShiftInfiniteLeakageGram
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : Tendsto omega l (𝓝 omega₀))
    (hpos : ∀ i, 0 ≤ omega i) (hpos₀ : 0 ≤ omega₀)
    (v : Fin n → HardyDisk) :
    Tendsto (fun i => xiShiftInfiniteLeakageGram (hpos i) v) l
      (𝓝 (xiShiftInfiniteLeakageGram hpos₀ v)) := by
  change Tendsto (fun i j k =>
      inner ℂ (xiShiftInfiniteLeakageCore (hpos i) (v j))
        (xiShiftInfiniteLeakageCore (hpos i) (v k))) l
    (𝓝 (fun j k =>
      inner ℂ (xiShiftInfiniteLeakageCore hpos₀ (v j))
        (xiShiftInfiniteLeakageCore hpos₀ (v k))))
  rw [tendsto_pi_nhds]
  intro j
  rw [tendsto_pi_nhds]
  intro k
  have hactual := (tendsto_suzukiShiftedXiDiskHardyLeakage_apply homega (v j)).inner
    (𝕜 := ℂ) (tendsto_suzukiShiftedXiDiskHardyLeakage_apply homega (v k))
  convert hactual using 1
  · funext i
    exact (inner_suzukiShiftedXiDiskHardyLeakage_eq_inner_infiniteLeakageCore
      (hpos i) (v j) (v k)).symm
  · exact congrArg nhds
      (inner_suzukiShiftedXiDiskHardyLeakage_eq_inner_infiniteLeakageCore
        hpos₀ (v j) (v k)).symm

/-- Gram matrix of actual shifted-Xi leakage on a fixed finite persistent frame. -/
def suzukiShiftedXiPersistentLeakageGram {n : ℕ}
    (omega : ℝ) (v : Fin n → UpperHardyL2) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => inner ℂ (suzukiShiftedXiHardyLeakage omega (v j))
    (suzukiShiftedXiHardyLeakage omega (v k))

/-- Persistent finite Gram block converges through every isolated layer: this is the
finite-dimensional consequence of actual shifted-Xi strong continuity used in `(13)`--`(14)`. -/
theorem tendsto_suzukiShiftedXiPersistentLeakageGram
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {omega : ι → ℝ} {omega₀ : ℝ}
    (homega : Tendsto omega l (𝓝 omega₀))
    (v : Fin n → UpperHardyL2) :
    Tendsto (fun i => suzukiShiftedXiPersistentLeakageGram (omega i) v) l
      (𝓝 (suzukiShiftedXiPersistentLeakageGram omega₀ v)) := by
  change Tendsto (fun i j k =>
      inner ℂ (suzukiShiftedXiHardyLeakage (omega i) (v j))
        (suzukiShiftedXiHardyLeakage (omega i) (v k))) l
    (𝓝 (fun j k =>
      inner ℂ (suzukiShiftedXiHardyLeakage omega₀ (v j))
        (suzukiShiftedXiHardyLeakage omega₀ (v k))))
  rw [tendsto_pi_nhds]
  intro j
  rw [tendsto_pi_nhds]
  intro k
  exact (tendsto_suzukiShiftedXiHardyLeakage_apply homega (v j)).inner
    (tendsto_suzukiShiftedXiHardyLeakage_apply homega (v k))

end

end RHTower
