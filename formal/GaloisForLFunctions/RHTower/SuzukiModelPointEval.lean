import GaloisForLFunctions.RHTower.SuzukiHalfInnerRealAxis
import GaloisForLFunctions.RHTower.SuzukiSpectralRestriction

noncomputable section

/-!
# Point evaluation on the model space

Suzuki writes `ψ̂(γ)` for the value at a spectral point of the Fourier transform of `ψ ∈ V(0)`.
For a square-integrable `ψ` that value is not the boundary value of an `L²` function; it is the
value of the analytic continuation.  This module gives it an unconditional meaning as the pairing
against the reproducing kernel of `K(Θ_ξ)`,

`ψ̂(w) = ⟪k_w, 𝖥ψ⟫`,  `k_w(x) = (i/2π)(1 - conj(Θ(w))Θ(x))/(x - conj w)`,

which is exactly the bounded point evaluation of the model space.  The kernel is square-integrable
at *every* zero of `A` — real or not — because there `Θ = -1`, so the numerator becomes
`1 + Θ(x) = 2A(x)/E(x)` and the whole kernel is `(i/π)` times the divided slope of `A/E`, which
`SuzukiHalfInnerRealAxis` puts in `L²(ℝ)` with no hypothesis.

Under RH the evaluation at a spectral point is precisely the corpus's `suzukiRestriction`: the
kernel there is the normalised basis vector `F_γ/√(π m_γ)`.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-! ## The kernel at a zero of `A` -/

/-- `Θ_ξ = -1` at every zero of `A`, multiple zeros included: the meromorphic representative
`2(A/E) - 1` takes the value `-1` there. -/
theorem suzukiThetaMero_eq_neg_one_of_XiC_zero {c : ℂ} (hc : XiC c = 0) :
    suzukiThetaMero c = -1 := by
  rw [suzukiThetaMero, suzukiHalfInner_eq_zero_of_XiC_zero hc]
  ring

theorem XiC_conj_eq_zero_of_XiC_zero {c : ℂ} (hc : XiC c = 0) :
    XiC ((starRingEnd ℂ) c) = 0 := by
  rw [XiC_conj, hc, map_zero]

/-- **At a zero of `A` the reproducing kernel is a divided slope.**  Since `Θ(c) = -1`, the
numerator `1 - conj(Θ(c))Θ(z)` is `1 + Θ(z) = 2A(z)/E(z)`, so the kernel is `(i/π)` times the
divided slope of `A/E` centred at `conj c`. -/
theorem suzukiModelKernel_of_XiC_zero {c : ℂ} (hc : XiC c = 0) {z : ℂ}
    (hz : z ≠ (starRingEnd ℂ) c) :
    suzukiModelKernel c z
      = (I / (Real.pi : ℂ)) * dslope suzukiHalfInner ((starRingEnd ℂ) c) z := by
  have hcc : XiC ((starRingEnd ℂ) c) = 0 := XiC_conj_eq_zero_of_XiC_zero hc
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [suzukiModelKernel, suzukiThetaMero_eq_neg_one_of_XiC_zero hc,
    dslope_suzukiHalfInner_apply hcc hz, suzukiThetaMero]
  field_simp
  simp only [map_neg, map_one]
  ring

/-- **The reproducing kernel at any zero of `A` is square-integrable**, with no appeal to RH. -/
theorem memLp_suzukiModelKernel_of_XiC_zero {c : ℂ} (hc : XiC c = 0) :
    MemLp (fun x : ℝ => suzukiModelKernel c ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hcc : XiC ((starRingEnd ℂ) c) = 0 := XiC_conj_eq_zero_of_XiC_zero hc
  have hbase : MemLp
      (fun x : ℝ => (I / (Real.pi : ℂ)) * dslope suzukiHalfInner ((starRingEnd ℂ) c) ((x : ℝ) : ℂ))
      2 (volume : Measure ℝ) := (memLp_dslope_suzukiHalfInner hcc).const_mul _
  have hnull : volume ({((starRingEnd ℂ) c).re} : Set ℝ) = 0 := by simp
  refine (memLp_congr_ae ?_).mpr hbase
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
  have hz : ((x : ℝ) : ℂ) ≠ (starRingEnd ℂ) c := by
    intro h
    exact hx (by simp only [Set.mem_singleton_iff, ← h, Complex.ofReal_re])
  exact suzukiModelKernel_of_XiC_zero hc hz

/-! ## The evaluation functional -/

open Classical in
/-- The reproducing kernel of `K(Θ_ξ)` at `w`, as an `L²` vector; the zero vector at those `w`
where the kernel is not square-integrable. -/
def suzukiModelKernelLp (w : ℂ) : Lp ℂ 2 (volume : Measure ℝ) :=
  if h : MemLp (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ)
    then h.toLp _ else 0

theorem suzukiModelKernelLp_eq {w : ℂ}
    (h : MemLp (fun x : ℝ => suzukiModelKernel w ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ)) :
    suzukiModelKernelLp w = h.toLp _ := by
  simp only [suzukiModelKernelLp, dif_pos h]

/-- **Point evaluation on the model space**, realised as the pairing against the reproducing
kernel.  This is Suzuki's `ψ̂(w)` for `ψ = 𝖥⁻¹F`. -/
def suzukiModelEval (F : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) : ℂ :=
  (inner ℂ (suzukiModelKernelLp w) F : ℂ)

@[simp] theorem suzukiModelEval_zero (w : ℂ) : suzukiModelEval 0 w = 0 := by
  simp [suzukiModelEval]

theorem suzukiModelEval_add (F G : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) :
    suzukiModelEval (F + G) w = suzukiModelEval F w + suzukiModelEval G w := by
  simp [suzukiModelEval, inner_add_right]

theorem suzukiModelEval_smul (a : ℂ) (F : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) :
    suzukiModelEval (a • F) w = a * suzukiModelEval F w := by
  simp [suzukiModelEval, inner_smul_right]

theorem suzukiModelEval_sub (F G : Lp ℂ 2 (volume : Measure ℝ)) (w : ℂ) :
    suzukiModelEval (F - G) w = suzukiModelEval F w - suzukiModelEval G w := by
  simp [suzukiModelEval, inner_sub_right]

/-! ## The evaluation at a real zero of `A` -/

theorem inv_sqrt_pi_mul_mul_sqrt_div {m : ℕ} (hm : 0 < m) :
    (Real.sqrt (Real.pi * m))⁻¹ * Real.sqrt ((m : ℝ) / Real.pi) = 1 / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  rw [Real.sqrt_mul hpi.le, Real.sqrt_div hmR.le]
  field_simp
  linarith [hpp]

/-- At a real zero of `A` the reproducing kernel is the normalised basis vector `F_γ/√(π m)`. -/
theorem suzukiModelKernel_ofReal_eq_suzukiFGammaFun {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) {z : ℂ} (hz : z ≠ ((γ : ℝ) : ℂ)) :
    suzukiModelKernel ((γ : ℝ) : ℂ) z
      = ((Real.sqrt (Real.pi * m) : ℝ) : ℂ)⁻¹ * suzukiFGammaFun γ m z := by
  have hconj : (starRingEnd ℂ) (((γ : ℝ)) : ℂ) = ((γ : ℝ) : ℂ) := Complex.conj_ofReal γ
  have hz' : z ≠ (starRingEnd ℂ) ((γ : ℝ) : ℂ) := by rwa [hconj]
  rw [suzukiModelKernel_of_XiC_zero hγ hz', hconj, suzukiFGammaFun]
  have hcast : ((Real.sqrt (Real.pi * m) : ℝ) : ℂ)⁻¹ * ((Real.sqrt ((m : ℝ) / Real.pi) : ℝ) : ℂ)
      = ((1 / Real.pi : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_sqrt_pi_mul_mul_sqrt_div hm]
  rw [← mul_assoc, hcast]
  push_cast
  ring

theorem suzukiModelKernelLp_ofReal (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    suzukiModelKernelLp ((γ : ℝ) : ℂ)
      = ((Real.sqrt (Real.pi * m) : ℝ) : ℂ)⁻¹ • suzukiFGammaLp hRH hm hord hγ := by
  have hmem := memLp_suzukiModelKernel_of_XiC_zero hγ
  rw [suzukiModelKernelLp_eq hmem]
  refine MeasureTheory.Lp.ext ?_
  have hnull : volume ({γ} : Set ℝ) = 0 := by simp
  filter_upwards [hmem.coeFn_toLp,
    MeasureTheory.Lp.coeFn_smul (((Real.sqrt (Real.pi * m) : ℝ) : ℂ))⁻¹
      (suzukiFGammaLp hRH hm hord hγ),
    coeFn_suzukiFGammaLp hRH hm hord hγ,
    MeasureTheory.compl_mem_ae_iff.mpr hnull] with x k1 k2 k3 k4
  rw [k1, k2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [k3]
  refine suzukiModelKernel_ofReal_eq_suzukiFGammaFun hm hγ ?_
  simp only [ne_eq, Complex.ofReal_inj]
  exact fun h => k4 (by simp [h])

theorem suzukiModelEval_ofReal (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0)
    (F : Lp ℂ 2 (volume : Measure ℝ)) :
    suzukiModelEval F ((γ : ℝ) : ℂ)
      = (inner ℂ (suzukiFGammaLp hRH hm hord hγ) F : ℂ)
          / ((Real.sqrt (Real.pi * m) : ℝ) : ℂ) := by
  rw [suzukiModelEval, suzukiModelKernelLp_ofReal hRH hm hord hγ, inner_smul_left]
  rw [map_inv₀, Complex.conj_ofReal, div_eq_inv_mul]

/-- **The evaluation at a spectral point is the corpus's restriction map.**  Under RH the
reproducing kernel at `γ_ρ` is `F_{γ_ρ}/√(π m_ρ)`. -/
theorem suzukiModelEval_xiSpectralPointSupport (hRH : RiemannHypothesis)
    (F : Lp ℂ 2 (volume : Measure ℝ)) (ρ : XiDivisorSupport) :
    suzukiModelEval F (xiSpectralPointSupport ρ) = suzukiRestriction hRH F ρ := by
  rw [← ofReal_xiRealSpectralPointSupport hRH ρ,
    suzukiModelEval_ofReal hRH (xiSupportMult_pos ρ)
      (analyticOrderAt_xiRealSpectralPointSupport hRH ρ) (XiC_xiRealSpectralPointSupport hRH ρ),
    suzukiRestriction, suzukiFGammaFamily, suzukiClarkWeight]

end RHTower
