import GaloisForLFunctions.RHTower.SuzukiZeroSumIdentity
import GaloisForLFunctions.RHTower.SuzukiFGammaModelSpace
import GaloisForLFunctions.HTGeometry.BesselSaturation

noncomputable section

/-!
# `{F_γ}` is an orthonormal basis of the model space

This completes Proposition 4.1.  Orthonormality and the containment `F_γ ∈ K(Θ)` are already known;
what is added here is completeness, and with it Parseval's identity in `K(Θ_ξ)`.

The argument avoids Clark's theorem entirely.  For each `w` above the axis the reproducing kernel
`k_w` lies in `K(Θ)`, is reproduced by the family — `⟪k_w, F_γ⟫ = F_γ(w)` — and its squared values
at the zeros sum to `‖k_w‖²`, which is the zero-sum identity.  So Bessel's inequality is saturated
at `k_w`, and a saturated Bessel inequality forces orthogonality to everything the family
annihilates.  Since the kernels are total in `K(Θ)`, an element orthogonal to the whole family is
orthogonal to every `k_w`, hence zero.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The orthonormal family of Proposition 4.1, indexed by the support of the Xi divisor. -/
def suzukiFGammaFamily (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  suzukiFGammaLp hRH (xiSupportMult_pos ρ)
    (analyticOrderAt_xiRealSpectralPointSupport hRH ρ) (XiC_xiRealSpectralPointSupport hRH ρ)

theorem suzukiFGammaFamily_mem (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    suzukiFGammaFamily hRH ρ ∈ suzukiModelSpace :=
  suzukiFGammaLp_mem_suzukiModelSpace hRH _ _ _

theorem coeFn_suzukiFGammaFamily (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    ((suzukiFGammaFamily hRH ρ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun x : ℝ =>
        suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) ((x : ℝ) : ℂ) :=
  coeFn_suzukiFGammaLp hRH _ _ _

theorem norm_suzukiFGammaFamily (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    ‖suzukiFGammaFamily hRH ρ‖ = 1 :=
  norm_suzukiFGammaLp hRH _ _ _

theorem inner_suzukiFGammaFamily (hRH : RiemannHypothesis) {ρ σ : XiDivisorSupport}
    (hne : ρ ≠ σ) :
    (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiFGammaFamily hRH σ) : ℂ) = 0 := by
  refine inner_suzukiFGammaLp hRH _ _ _ _ _ _ ?_
  intro h
  exact hne (xiRealSpectralPointSupport_injective hRH h).symm

theorem orthonormal_suzukiFGammaFamily (hRH : RiemannHypothesis) :
    Orthonormal ℂ (suzukiFGammaFamily hRH) := by
  refine ⟨fun ρ => norm_suzukiFGammaFamily hRH ρ, ?_⟩
  intro ρ σ hne
  exact inner_suzukiFGammaFamily hRH hne

theorem differentiableAt_suzukiFGammaFun (hRH : RiemannHypothesis) {γ : ℝ} (m : ℕ)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (suzukiFGammaFun γ m) z := by
  have h : DifferentiableAt ℂ (fun ζ : ℂ =>
      ((Real.sqrt ((m : ℝ) / Real.pi) : ℝ) : ℂ) *
        (I * dslope suzukiHalfInner ((γ : ℝ) : ℂ) ζ)) z :=
    ((differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ hz).const_mul I).const_mul _
  exact h

theorem norm_suzukiFGammaFun_far (hRH : RiemannHypothesis) {γ : ℝ} (m : ℕ)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) {z : ℂ} (hz : 0 ≤ z.im)
    (hzR : 2 * ‖((γ : ℝ) : ℂ)‖ + 1 ≤ ‖z‖) :
    ‖suzukiFGammaFun γ m z‖ ≤ 2 * Real.sqrt ((m : ℝ) / Real.pi) / ‖z‖ := by
  have hc : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) / Real.pi) := Real.sqrt_nonneg _
  have hgn : (0 : ℝ) ≤ ‖((γ : ℝ) : ℂ)‖ := norm_nonneg _
  have hzn : 0 < ‖z‖ := by linarith
  have hhalf : ‖((γ : ℝ) : ℂ)‖ ≤ ‖z‖ / 2 := by linarith
  have hzg : ‖z‖ / 2 ≤ ‖z - ((γ : ℝ) : ℂ)‖ := by
    have h := norm_sub_norm_le z ((γ : ℝ) : ℂ)
    linarith
  have hzh : 0 < ‖z‖ / 2 := by linarith
  have hne : z ≠ ((γ : ℝ) : ℂ) := by
    intro h
    rw [h] at hzn hzg
    rw [sub_self, norm_zero] at hzg
    linarith
  calc ‖suzukiFGammaFun γ m z‖
      ≤ Real.sqrt ((m : ℝ) / Real.pi) / ‖z - ((γ : ℝ) : ℂ)‖ :=
        norm_suzukiFGammaFun_le hRH m hγ hz hne
    _ ≤ Real.sqrt ((m : ℝ) / Real.pi) / (‖z‖ / 2) := by gcongr
    _ = 2 * Real.sqrt ((m : ℝ) / Real.pi) / ‖z‖ := by field_simp

/-- **The kernel reproduces the orthonormal family.** -/
theorem inner_suzukiModelKernel_suzukiFGammaFamily (hRH : RiemannHypothesis) {w : ℂ}
    (hw : 0 < w.im) (ρ : XiDivisorSupport) :
    (inner ℂ ((memLp_suzukiModelKernel hRH hw).toLp _) (suzukiFGammaFamily hRH ρ) : ℂ)
      = suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ) w := by
  have hγ := XiC_xiRealSpectralPointSupport hRH ρ
  have hgn : (0 : ℝ) ≤ ‖((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ := norm_nonneg _
  refine inner_suzukiModelKernelLp_of_decay hRH hw (suzukiFGammaFamily_mem hRH ρ)
    (u := suzukiFGammaFun (xiRealSpectralPointSupport ρ) (xiSupportMult ρ))
    (M := 2 * Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi))
    (R := 2 * ‖((xiRealSpectralPointSupport ρ : ℝ) : ℂ)‖ + 1)
    (fun z hz => differentiableAt_suzukiFGammaFun hRH _ hγ hz) (by linarith)
    (fun z hz hzR => norm_suzukiFGammaFun_far hRH _ hγ hz hzR)
    (coeFn_suzukiFGammaFamily hRH ρ)

/-- **Parseval saturates on the reproducing kernel.** -/
theorem hasSum_normSq_inner_suzukiFGammaFamily_kernel (hRH : RiemannHypothesis) {w : ℂ}
    (hw : 0 < w.im) :
    HasSum (fun ρ : XiDivisorSupport =>
        ‖(inner ℂ (suzukiFGammaFamily hRH ρ)
          ((memLp_suzukiModelKernel hRH hw).toLp _) : ℂ)‖ ^ (2 : ℕ))
      (‖((memLp_suzukiModelKernel hRH hw).toLp
        (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)) : Lp ℂ 2 (volume : Measure ℝ))‖ ^ (2 : ℕ)) := by
  have hbase := hasSum_normSq_suzukiFGammaFun hRH hw
  have hself := inner_suzukiModelKernel_pair hRH hw hw
  have hnorm : ‖((memLp_suzukiModelKernel hRH hw).toLp
      (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)) : Lp ℂ 2 (volume : Measure ℝ))‖ ^ (2 : ℕ)
      = (suzukiModelKernel w w).re := by
    rw [← hself, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hnorm]
  refine hbase.congr_fun ?_
  intro ρ
  rw [← inner_conj_symm, RCLike.norm_conj,
    inner_suzukiModelKernel_suzukiFGammaFamily hRH hw ρ]


/-- **Completeness.**  An element of the model space orthogonal to the whole family vanishes. -/
theorem eq_zero_of_forall_inner_suzukiFGammaFamily (hRH : RiemannHypothesis)
    {y : Lp ℂ 2 (volume : Measure ℝ)} (hyK : y ∈ suzukiModelSpace)
    (hy : ∀ ρ : XiDivisorSupport, (inner ℂ (suzukiFGammaFamily hRH ρ) y : ℂ) = 0) :
    y = 0 := by
  refine eq_zero_of_inner_suzukiModelKernel_eq_zero hRH hyK ?_
  intro w hw
  exact inner_eq_zero_of_bessel_saturates (orthonormal_suzukiFGammaFamily hRH)
    (hasSum_normSq_inner_suzukiFGammaFamily_kernel hRH hw) hy

instance : CompleteSpace
    (suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
  isClosed_suzukiModelSpace.completeSpace_coe

/-- The family viewed inside the model space. -/
def suzukiFGammaVec (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
  ⟨suzukiFGammaFamily hRH ρ, suzukiFGammaFamily_mem hRH ρ⟩

theorem orthonormal_suzukiFGammaVec (hRH : RiemannHypothesis) :
    Orthonormal ℂ (suzukiFGammaVec hRH) := by
  refine ⟨fun ρ => ?_, ?_⟩
  · show ‖suzukiFGammaFamily hRH ρ‖ = 1
    exact norm_suzukiFGammaFamily hRH ρ
  · intro ρ σ hne
    show (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiFGammaFamily hRH σ) : ℂ) = 0
    exact inner_suzukiFGammaFamily hRH hne

theorem orthogonal_span_suzukiFGammaVec_eq_bot (hRH : RiemannHypothesis) :
    (Submodule.span ℂ (Set.range (suzukiFGammaVec hRH)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hzero : ∀ ρ : XiDivisorSupport,
      (inner ℂ (suzukiFGammaFamily hRH ρ)
        ((y : Lp ℂ 2 (volume : Measure ℝ))) : ℂ) = 0 := by
    intro ρ
    exact (Submodule.mem_orthogonal _ _).mp hy (suzukiFGammaVec hRH ρ)
      (Submodule.subset_span (Set.mem_range_self ρ))
  exact Submodule.coe_eq_zero.mp
    (eq_zero_of_forall_inner_suzukiFGammaFamily hRH y.2 hzero)

/-- **Proposition 4.1.**  Under the Riemann hypothesis the normalized reproducing vectors `F_γ`
form an orthonormal *basis* of the model space `K(Θ_ξ)`. -/
def suzukiFGammaHilbertBasis (hRH : RiemannHypothesis) :
    HilbertBasis XiDivisorSupport ℂ
      ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_suzukiFGammaVec hRH)
    (orthogonal_span_suzukiFGammaVec_eq_bot hRH)

theorem coe_suzukiFGammaHilbertBasis (hRH : RiemannHypothesis) :
    ⇑(suzukiFGammaHilbertBasis hRH) = suzukiFGammaVec hRH :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- **Parseval's identity in `K(Θ_ξ)`.** -/
theorem hasSum_normSq_inner_suzukiFGammaFamily (hRH : RiemannHypothesis)
    {y : Lp ℂ 2 (volume : Measure ℝ)} (hy : y ∈ suzukiModelSpace) :
    HasSum (fun ρ : XiDivisorSupport =>
      ‖(inner ℂ (suzukiFGammaFamily hRH ρ) y : ℂ)‖ ^ (2 : ℕ)) (‖y‖ ^ (2 : ℕ)) := by
  set Y : ↥(suzukiModelSpace : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) := ⟨y, hy⟩ with hY
  have hb := (suzukiFGammaHilbertBasis hRH).hasSum_inner_mul_inner Y Y
  have hcoe := coe_suzukiFGammaHilbertBasis hRH
  have hterm : ∀ ρ : XiDivisorSupport,
      (inner ℂ Y ((suzukiFGammaHilbertBasis hRH) ρ) : ℂ)
        * (inner ℂ ((suzukiFGammaHilbertBasis hRH) ρ) Y : ℂ)
      = (((‖(inner ℂ (suzukiFGammaFamily hRH ρ) y : ℂ)‖ ^ (2 : ℕ) : ℝ)) : ℂ) := by
    intro ρ
    rw [hcoe]
    have h1 : (inner ℂ ((suzukiFGammaVec hRH ρ)) Y : ℂ)
        = (inner ℂ (suzukiFGammaFamily hRH ρ) y : ℂ) := rfl
    have h2 : (inner ℂ Y ((suzukiFGammaVec hRH ρ)) : ℂ)
        = (starRingEnd ℂ) (inner ℂ (suzukiFGammaFamily hRH ρ) y : ℂ) := by
      rw [← h1]
      exact (inner_conj_symm (𝕜 := ℂ) Y (suzukiFGammaVec hRH ρ)).symm
    rw [h1, h2, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hb' : HasSum (fun ρ : XiDivisorSupport =>
      (((‖(inner ℂ (suzukiFGammaFamily hRH ρ) y : ℂ)‖ ^ (2 : ℕ) : ℝ)) : ℂ))
      (inner ℂ Y Y : ℂ) := by
    refine hb.congr_fun ?_
    intro ρ
    exact (hterm ρ).symm
  have hre := Complex.hasSum_re hb'
  have hval : (inner ℂ Y Y : ℂ).re = ‖y‖ ^ (2 : ℕ) := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := Y)
    rw [h]
    have hn : ‖Y‖ = ‖y‖ := rfl
    rw [hn]
    norm_cast
  rw [hval] at hre
  refine hre.congr_fun ?_
  intro ρ
  norm_cast


end RHTower
