import GaloisForLFunctions.RHTower.JointAncestryKroneckerLineCriterion

/-!
# The JAS zero kernel is holomorphic in the zero

At a point `w` of the finite prime torus (`‖w_p‖ = 1`) the zero-sum density of the dressed
aggregate is `Σ_ρ 𝒦_w(ρ)` with the zero kernel

`𝒦_w(s) = 1/(s(1 − s)) · ∏_{p ∈ P} [(1 − p^{−(s+c)} w_p)⁻¹ + (1 − p^{−(1−s+c)} w̄_p)⁻¹ − 1]`.

Both local parameters `p^{−(s+c)}` and `p^{−(1−s+c)}` are entire in `s`, and their product
`p^{−(1+2c)}` does not depend on `s`.  So `𝒦_w` is holomorphic on the dressed strip
`−c < Re s < 1 + c` away from `s = 0, 1` (`differentiableOn_jasZeroKernel`).

Consequences (maximum principle):

* on every circle around a point `s₀` of the strip some point carries a contribution of modulus
  at least `‖𝒦_w(s₀)‖` (`exists_mem_sphere_norm_jasZeroKernel_ge`);
* on every such circle some point has real part at least `Re 𝒦_w(s₀)`, and some point has real
  part at most `Re 𝒦_w(s₀)` (`exists_mem_sphere_re_jasZeroKernel_ge`,
  `exists_mem_sphere_re_jasZeroKernel_le`).

So no test point of the torus isolates a zero: whatever weight a test gives a zero at `s₀`, it
gives at least as much modulus, and at least as negative a real part, to some point of every small
circle around `s₀`.  A configuration of zeros placed at those points interferes with the zero at
`s₀` at that test point.  This is the precise sense in which point tests cannot separate near-tied
off-line zeros.
-/

open Complex Metric
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The JAS zero kernel at a torus point `w`. -/
def jasZeroKernel (c : ℝ) (P : Finset Nat.Primes) (w : ↥P → ℂ) (s : ℂ) : ℂ :=
  1 / (s * (1 - s)) * ∏ i : ↥P, jasHoloLocal (jasHoloA (s + c) i) (jasHoloB (s - c) i) (w i)

/-- The zero-sum density is the sum of the zero kernel over the Xi zeros. -/
theorem jasZeroSumDensity_eq_tsum_jasZeroKernel (c : ℝ) (P : Finset Nat.Primes) (w : ↥P → ℂ) :
    jasZeroSumDensity c P w = ∑' q : XiZeroCopy, jasZeroKernel c P w (q.1 : ℂ) := rfl

/-- The dressed strip with the poles of the weight removed. -/
def jasKernelDomain (c : ℝ) : Set ℂ := {s : ℂ | -c < s.re ∧ s.re < 1 + c ∧ s ≠ 0 ∧ s ≠ 1}

theorem isOpen_jasKernelDomain (c : ℝ) : IsOpen (jasKernelDomain c) := by
  have h1 : IsOpen {s : ℂ | -c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {s : ℂ | s.re < 1 + c} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {s : ℂ | s ≠ 0} := isOpen_ne
  have h4 : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  exact h1.inter (h2.inter (h3.inter h4))

theorem differentiable_jasHoloA_add (c : ℝ) (p : Nat.Primes) :
    Differentiable ℂ fun s : ℂ => jasHoloA (s + c) p := by
  unfold jasHoloA
  fun_prop

theorem differentiable_jasHoloB_sub (c : ℝ) (p : Nat.Primes) :
    Differentiable ℂ fun s : ℂ => jasHoloB (s - c) p := by
  unfold jasHoloB
  fun_prop

/-- Each local factor is holomorphic on the dressed strip. -/
theorem differentiableOn_jasHoloLocal_factor {c : ℝ} (p : Nat.Primes) {w : ℂ} (hw : ‖w‖ = 1) :
    DifferentiableOn ℂ (fun s : ℂ => jasHoloLocal (jasHoloA (s + c) p) (jasHoloB (s - c) p) w)
      {s : ℂ | -c < s.re ∧ s.re < 1 + c} := by
  intro s hs
  have hA : ‖jasHoloA (s + c) p‖ < 1 := norm_jasHoloA_dressed_lt_one (by linarith [hs.1]) p
  have hB : ‖jasHoloB (s - c) p‖ < 1 := norm_jasHoloB_dressed_lt_one (by linarith [hs.2]) p
  have hA' : 1 - jasHoloA (s + c) p * w ≠ 0 := by
    intro h
    have : ‖jasHoloA (s + c) p * w‖ = 1 := by
      rw [show jasHoloA (s + c) p * w = 1 by linear_combination -h]; simp
    rw [norm_mul, hw, mul_one] at this
    linarith
  have hB' : 1 - jasHoloB (s - c) p * conj w ≠ 0 := by
    intro h
    have : ‖jasHoloB (s - c) p * conj w‖ = 1 := by
      rw [show jasHoloB (s - c) p * conj w = 1 by linear_combination -h]; simp
    rw [norm_mul, Complex.norm_conj, hw, mul_one] at this
    linarith
  unfold jasHoloLocal
  have dA := (differentiable_jasHoloA_add c p) s
  have dB := (differentiable_jasHoloB_sub c p) s
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.sub (DifferentiableAt.add ?_ ?_) (differentiableAt_const _)
  · exact ((differentiableAt_const _).sub (dA.mul (differentiableAt_const _))).inv hA'
  · exact ((differentiableAt_const _).sub (dB.mul (differentiableAt_const _))).inv hB'

/-- **The zero kernel is holomorphic on the dressed strip.** -/
theorem differentiableOn_jasZeroKernel (c : ℝ) (P : Finset Nat.Primes) {w : ↥P → ℂ}
    (hw : ∀ i, ‖w i‖ = 1) : DifferentiableOn ℂ (jasZeroKernel c P w) (jasKernelDomain c) := by
  unfold jasZeroKernel
  refine DifferentiableOn.mul ?_ ?_
  · intro s hs
    have h0 : s * (1 - s) ≠ 0 := mul_ne_zero hs.2.2.1 (sub_ne_zero.mpr (Ne.symm hs.2.2.2))
    have hd : DifferentiableAt ℂ (fun s : ℂ => s * (1 - s)) s := by fun_prop
    exact ((differentiableAt_const (1 : ℂ)).div hd h0).differentiableWithinAt
  · have hsub : jasKernelDomain c ⊆ {s : ℂ | -c < s.re ∧ s.re < 1 + c} :=
      fun s hs => ⟨hs.1, hs.2.1⟩
    have h := DifferentiableOn.finsetProd (u := (Finset.univ : Finset ↥P)) fun i _ =>
      (differentiableOn_jasHoloLocal_factor (c := c) i.1 (hw i)).mono hsub
    rwa [Finset.prod_fn] at h

/-- Maximum principle on a circle for a function holomorphic on a neighbourhood of the disk. -/
theorem exists_mem_sphere_norm_ge_of_differentiableOn {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) {s₀ : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall s₀ r ⊆ U) :
    ∃ s ∈ sphere s₀ r, ‖f s₀‖ ≤ ‖f s‖ := by
  have hcont : ContinuousOn (fun s => ‖f s‖) (sphere s₀ r) :=
    ((hf.mono hball).continuousOn.mono sphere_subset_closedBall).norm
  obtain ⟨s₁, hs₁, hmax⟩ := (isCompact_sphere s₀ r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hcont
  refine ⟨s₁, hs₁, ?_⟩
  have hdc : DiffContOnCl ℂ f (ball s₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s₀ hr.ne']
    exact hf.mono hball
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
    (subset_closure (mem_ball_self hr))
  intro z hz
  rw [frontier_ball s₀ hr.ne'] at hz
  exact hmax hz

/-- **No test point isolates a zero in modulus.** -/
theorem exists_mem_sphere_norm_jasZeroKernel_ge (c : ℝ) (P : Finset Nat.Primes) {w : ↥P → ℂ}
    (hw : ∀ i, ‖w i‖ = 1) {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall s₀ r ⊆ jasKernelDomain c) :
    ∃ s ∈ sphere s₀ r, ‖jasZeroKernel c P w s₀‖ ≤ ‖jasZeroKernel c P w s‖ :=
  exists_mem_sphere_norm_ge_of_differentiableOn (differentiableOn_jasZeroKernel c P hw) hr hball

/-- **No test point isolates a zero in real part, from above.** -/
theorem exists_mem_sphere_re_jasZeroKernel_ge (c : ℝ) (P : Finset Nat.Primes) {w : ↥P → ℂ}
    (hw : ∀ i, ‖w i‖ = 1) {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall s₀ r ⊆ jasKernelDomain c) :
    ∃ s ∈ sphere s₀ r, (jasZeroKernel c P w s₀).re ≤ (jasZeroKernel c P w s).re := by
  have hd : DifferentiableOn ℂ (fun s => cexp (jasZeroKernel c P w s)) (jasKernelDomain c) :=
    (differentiableOn_jasZeroKernel c P hw).cexp
  obtain ⟨s, hs, hle⟩ := exists_mem_sphere_norm_ge_of_differentiableOn hd hr hball
  refine ⟨s, hs, ?_⟩
  rw [Complex.norm_exp, Complex.norm_exp] at hle
  exact Real.exp_le_exp.mp hle

/-- **No test point isolates a zero in real part, from below.** -/
theorem exists_mem_sphere_re_jasZeroKernel_le (c : ℝ) (P : Finset Nat.Primes) {w : ↥P → ℂ}
    (hw : ∀ i, ‖w i‖ = 1) {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : closedBall s₀ r ⊆ jasKernelDomain c) :
    ∃ s ∈ sphere s₀ r, (jasZeroKernel c P w s).re ≤ (jasZeroKernel c P w s₀).re := by
  have hd : DifferentiableOn ℂ (fun s => cexp (-jasZeroKernel c P w s)) (jasKernelDomain c) :=
    (differentiableOn_jasZeroKernel c P hw).neg.cexp
  obtain ⟨s, hs, hle⟩ := exists_mem_sphere_norm_ge_of_differentiableOn hd hr hball
  refine ⟨s, hs, ?_⟩
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, Complex.neg_re] at hle
  linarith [Real.exp_le_exp.mp hle]

end

end RHTower
