import GaloisForLFunctions.RHTower.ProlateL2Operator
import GaloisForLFunctions.RHTower.CCMEndpointResponseIdentity
import GaloisForLFunctions.HTGeometry.SimpleEigenvalueCompactBranch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The band operator as a differentiable family, and its eigenvalue branch

The band operator of `ProlateL2Operator` depends on the aperture `c`, and this module differentiates
it: the derivative is the operator with the cosine kernel `cos (c (x - y))/pi`, the differentiation
happens in operator norm, and the family is `C¹`.  Combined with compactness and symmetry, the Kato
layer of `HTGeometry.SimpleEigenvalueCompactBranch` then produces, for every simple nonzero prolate
eigenvalue, a differentiable branch with a normalized eigenfunction and the Hellmann–Feynman
derivative

```text
nu'(c) = ⟪psi, (cosine-kernel operator) psi⟫.
```

Every estimate is a kernel estimate: the second-order bound
`|sinc(c+h) - sinc c - h cos(c u)/pi| <= h² |u|/pi` transfers to operator norm through
`norm_le_of_kernel_repr`, because a linear combination of kernel operators is the kernel operator of
the combination.  Nothing about prolate asymptotics is used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The cosine kernel: the aperture derivative of the smoothed sinc kernel. -/
def cosKernelContinuous (c : ℝ) :
    C(ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1, ℝ) where
  toFun z := Real.cos (c * ((z.1 : ℝ) - (z.2 : ℝ))) / Real.pi
  continuous_toFun := by fun_prop

/-- The cosine-kernel operator: the aperture derivative of the band operator. -/
def cosOperatorL2 (c : ℝ) : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  continuousKernelOperator (cosKernelContinuous c)

/-- Two points of `[-1, 1]` are at distance at most `2`. -/
theorem abs_sub_le_two (z : ClosedInterval (-1 : ℝ) 1 × ClosedInterval (-1 : ℝ) 1) :
    |(z.1 : ℝ) - (z.2 : ℝ)| ≤ 2 := by
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp z.1.2
  obtain ⟨h3, h4⟩ := Set.mem_Icc.mp z.2.2
  rw [abs_le]
  constructor <;> linarith

/-- **The second-order kernel bound**, uniformly on the square. -/
theorem norm_sincKernel_taylor_le (c h : ℝ) :
    ‖sincKernelContinuous (c + h) - sincKernelContinuous c - h • cosKernelContinuous c‖
      ≤ 2 * h ^ 2 / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => ?_
  have hval : (sincKernelContinuous (c + h) - sincKernelContinuous c
      - h • cosKernelContinuous c) z
      = sincSmooth (c + h) ((z.1 : ℝ) - (z.2 : ℝ)) - sincSmooth c ((z.1 : ℝ) - (z.2 : ℝ))
        - h * (Real.cos (c * ((z.1 : ℝ) - (z.2 : ℝ))) / Real.pi) := by
    simp [sincKernelContinuous, cosKernelContinuous, sincKernelSmooth]
  rw [Real.norm_eq_abs, hval]
  have hb := abs_sincSmooth_taylor_le c h ((z.1 : ℝ) - (z.2 : ℝ))
  have hu := abs_sub_le_two z
  refine hb.trans ?_
  have hnum : h ^ 2 * |(z.1 : ℝ) - (z.2 : ℝ)| ≤ 2 * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hu (sq_nonneg h)
    linarith
  gcongr

/-- **The second-order operator bound**: the band operator differs from its linearisation by
`O(h²)` in operator norm. -/
theorem norm_bandOperator_taylor_le (c h : ℝ) :
    ‖bandOperatorL2 (c + h) - bandOperatorL2 c - h • cosOperatorL2 c‖ ≤ 4 * h ^ 2 / Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hrepr := coeFn_comb_inner (sincKernelContinuous (c + h)) (sincKernelContinuous c)
    (cosKernelContinuous c) h
  have h1 := norm_le_of_kernel_repr (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
    (sincKernelContinuous (c + h) - sincKernelContinuous c - h • cosKernelContinuous c) _ hrepr
  have h2 := norm_sincKernel_taylor_le c h
  have hop : bandOperatorL2 (c + h) - bandOperatorL2 c - h • cosOperatorL2 c
      = continuousKernelOperator (sincKernelContinuous (c + h))
        - continuousKernelOperator (sincKernelContinuous c)
        - h • continuousKernelOperator (cosKernelContinuous c) := rfl
  rw [hop]
  refine h1.trans ?_
  have hb : (1 : ℝ) - (-1) = 2 := by norm_num
  rw [hb]
  have hfinal : ∀ x : ℝ, x ≤ 2 * h ^ 2 / Real.pi → 2 * x ≤ 4 * h ^ 2 / Real.pi := by
    intro x hx
    have hx2 : 2 * x ≤ 2 * (2 * h ^ 2 / Real.pi) := by linarith
    calc 2 * x ≤ 2 * (2 * h ^ 2 / Real.pi) := hx2
      _ = 4 * h ^ 2 / Real.pi := by ring
  exact hfinal _ h2

/-- **The band operator is differentiable in the aperture**, with the cosine-kernel operator as
derivative. -/
theorem hasDerivAt_bandOperatorL2 (c : ℝ) :
    HasDerivAt (fun t : ℝ => bandOperatorL2 t) (cosOperatorL2 c) c := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ : (0 : ℝ) < ε * Real.pi / 4 := by positivity
  filter_upwards [Metric.ball_mem_nhds c hδ] with t ht
  have hdist : |t - c| ≤ ε * Real.pi / 4 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ht.le
  have hkey : ‖bandOperatorL2 t - bandOperatorL2 c - (t - c) • cosOperatorL2 c‖
      ≤ 4 * (t - c) ^ 2 / Real.pi := by
    have h := norm_bandOperator_taylor_le c (t - c)
    have hct : c + (t - c) = t := by ring
    rwa [hct] at h
  refine hkey.trans ?_
  rw [Real.norm_eq_abs]
  have hsq : (t - c) ^ 2 = |t - c| * |t - c| := by
    rw [← sq_abs]
    ring
  rw [hsq, div_le_iff₀ hpi]
  nlinarith [abs_nonneg (t - c), hdist, hpi.le]

/-- The cosine-kernel operator is Lipschitz in the aperture. -/
theorem norm_cosOperatorL2_sub_le (c₁ c₂ : ℝ) :
    ‖cosOperatorL2 c₁ - cosOperatorL2 c₂‖ ≤ 4 / Real.pi * |c₁ - c₂| := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hk : ‖cosKernelContinuous c₁ - cosKernelContinuous c₂‖ ≤ 2 * |c₁ - c₂| / Real.pi := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun z => ?_
    have hu := abs_sub_le_two z
    have hcos : |Real.cos (c₁ * ((z.1 : ℝ) - (z.2 : ℝ)))
        - Real.cos (c₂ * ((z.1 : ℝ) - (z.2 : ℝ)))|
        ≤ |c₁ * ((z.1 : ℝ) - (z.2 : ℝ)) - c₂ * ((z.1 : ℝ) - (z.2 : ℝ))| := by
      have h := Real.lipschitzWith_cos.dist_le_mul (c₁ * ((z.1 : ℝ) - (z.2 : ℝ)))
        (c₂ * ((z.1 : ℝ) - (z.2 : ℝ)))
      simpa [Real.dist_eq] using h
    have hfac : |c₁ * ((z.1 : ℝ) - (z.2 : ℝ)) - c₂ * ((z.1 : ℝ) - (z.2 : ℝ))|
        = |c₁ - c₂| * |(z.1 : ℝ) - (z.2 : ℝ)| := by
      rw [← abs_mul]
      ring_nf
    have hval : (cosKernelContinuous c₁ - cosKernelContinuous c₂) z
        = Real.cos (c₁ * ((z.1 : ℝ) - (z.2 : ℝ))) / Real.pi
          - Real.cos (c₂ * ((z.1 : ℝ) - (z.2 : ℝ))) / Real.pi := by
      simp [cosKernelContinuous]
    rw [Real.norm_eq_abs, hval, div_sub_div_same, abs_div, abs_of_pos hpi]
    rw [div_le_div_iff₀ hpi hpi]
    have hstep : |Real.cos (c₁ * ((z.1 : ℝ) - (z.2 : ℝ)))
        - Real.cos (c₂ * ((z.1 : ℝ) - (z.2 : ℝ)))| ≤ |c₁ - c₂| * 2 := by
      refine hcos.trans ?_
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    nlinarith [hstep, hpi.le, abs_nonneg (c₁ - c₂)]
  have h := norm_continuousKernelOperator_sub_le (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
    (cosKernelContinuous c₁) (cosKernelContinuous c₂)
  have hop : cosOperatorL2 c₁ - cosOperatorL2 c₂
      = continuousKernelOperator (cosKernelContinuous c₁)
        - continuousKernelOperator (cosKernelContinuous c₂) := rfl
  rw [hop]
  refine h.trans ?_
  have hb : (1 : ℝ) - (-1) = 2 := by norm_num
  rw [hb]
  have hfinal : ∀ x : ℝ, x ≤ 2 * |c₁ - c₂| / Real.pi → 2 * x ≤ 4 / Real.pi * |c₁ - c₂| := by
    intro x hx
    have hx2 : 2 * x ≤ 2 * (2 * |c₁ - c₂| / Real.pi) := by linarith
    calc 2 * x ≤ 2 * (2 * |c₁ - c₂| / Real.pi) := hx2
      _ = 4 / Real.pi * |c₁ - c₂| := by ring
  exact hfinal _ hk

/-- The derivative family is continuous in the aperture. -/
theorem continuous_cosOperatorL2 : Continuous fun c : ℝ => cosOperatorL2 c := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlip : LipschitzWith (Real.toNNReal (4 / Real.pi)) fun c : ℝ => cosOperatorL2 c := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro c₁ c₂
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact norm_cosOperatorL2_sub_le c₁ c₂
  exact hlip.continuous

/-- The band family is `C¹` in the aperture. -/
theorem contDiff_bandOperatorL2 : ContDiff ℝ 1 fun c : ℝ => bandOperatorL2 c := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun c => (hasDerivAt_bandOperatorL2 c).differentiableAt, ?_⟩
  have hderiv : deriv (fun c : ℝ => bandOperatorL2 c) = fun c => cosOperatorL2 c :=
    funext fun c => (hasDerivAt_bandOperatorL2 c).deriv
  rw [hderiv]
  exact continuous_cosOperatorL2

/-- The band family is strictly differentiable in the aperture. -/
theorem hasStrictDerivAt_bandOperatorL2 (c : ℝ) :
    HasStrictDerivAt (fun t : ℝ => bandOperatorL2 t) (cosOperatorL2 c) c := by
  have h := contDiff_bandOperatorL2.hasStrictDerivAt (x := c) one_ne_zero
  rwa [(hasDerivAt_bandOperatorL2 c).deriv] at h

/-- **The band family is jointly strictly differentiable**, in the split form the branch theorem
consumes: the aperture direction moves by the cosine-kernel operator, the vector direction by the
band operator itself. -/
theorem hasStrictFDerivAt_bandOperatorL2_apply (c₀ : ℝ) (ψ₀ : RealIntervalL2 (-1 : ℝ) 1) :
    HasStrictFDerivAt (fun q : ℝ × RealIntervalL2 (-1 : ℝ) 1 => bandOperatorL2 q.1 q.2)
      (GaloisForLFunctions.HTGeometry.familyDeriv (bandOperatorL2 c₀) (cosOperatorL2 c₀ ψ₀))
      (c₀, ψ₀) := by
  have h1 : HasStrictFDerivAt
      (fun q : ℝ × RealIntervalL2 (-1 : ℝ) 1 => bandOperatorL2 q.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (cosOperatorL2 c₀)).comp
        (ContinuousLinearMap.fst ℝ ℝ (RealIntervalL2 (-1 : ℝ) 1))) (c₀, ψ₀) :=
    (hasStrictDerivAt_bandOperatorL2 c₀).hasStrictFDerivAt.comp (c₀, ψ₀) hasStrictFDerivAt_fst
  have h2 := h1.clm_apply
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (c₀, ψ₀)))
  have hEq : (bandOperatorL2 c₀).comp
        (ContinuousLinearMap.snd ℝ ℝ (RealIntervalL2 (-1 : ℝ) 1))
      + ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (cosOperatorL2 c₀)).comp
          (ContinuousLinearMap.fst ℝ ℝ (RealIntervalL2 (-1 : ℝ) 1))).flip ψ₀
      = GaloisForLFunctions.HTGeometry.familyDeriv (bandOperatorL2 c₀) (cosOperatorL2 c₀ ψ₀) := by
    refine ContinuousLinearMap.ext fun q => ?_
    simp [GaloisForLFunctions.HTGeometry.familyDeriv_apply, add_comm]
  rwa [hEq] at h2

/-- **The prolate eigenvalue branch.**  A simple nonzero eigenvalue of the band operator at aperture
`c_0`, with normalized eigenfunction `psi_0`, extends to a differentiable branch of normalized
eigenpairs, and the eigenvalue derivative is the expectation of the cosine-kernel operator:

```text
nu'(c_0) = ⟪psi_0, (cosine-kernel operator at c_0) psi_0⟫.
```

Unconditional: compactness and symmetry of the band operator are proved in `ProlateL2Operator`, the
family's strict differentiability just above, and the branch itself comes from the Fredholm
pseudo-inverse and the implicit function theorem. -/
theorem exists_bandOperatorL2_branch {c₀ ν₀ : ℝ} {ψ₀ : RealIntervalL2 (-1 : ℝ) 1}
    (heig : bandOperatorL2 c₀ ψ₀ = ν₀ • ψ₀) (hnorm : (inner ℝ ψ₀ ψ₀ : ℝ) = 1) (hν₀ : ν₀ ≠ 0)
    (hsimple : ∀ φ : RealIntervalL2 (-1 : ℝ) 1,
      bandOperatorL2 c₀ φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀) :
    ∃ (ψ : ℝ → RealIntervalL2 (-1 : ℝ) 1) (ν : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in nhds c₀, bandOperatorL2 c (ψ c) = ν c • ψ c ∧ (inner ℝ (ψ c) (ψ c) : ℝ) = 1) ∧
      HasDerivAt ν (inner ℝ ψ₀ (cosOperatorL2 c₀ ψ₀)) c₀ :=
  GaloisForLFunctions.HTGeometry.exists_normalized_branch_of_isCompactOperator
    (hasStrictFDerivAt_bandOperatorL2_apply c₀ ψ₀) (isCompactOperator_bandOperatorL2 c₀)
    (bandOperatorL2_symmetric c₀) heig hnorm hν₀ hsimple

end GaloisForLFunctions.RHTower

end
