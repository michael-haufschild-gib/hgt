import GaloisForLFunctions.RHTower.CosDilationKernelPositivityRigidity

/-!
# The archimedean twist: a function and its cosine transform are never both inversion-symmetric

Let `f` be smooth and supported in `[α, β]` with `0 < α ≤ β`, and let
`Cf(w) = 2∫_0^∞ f(z) cos(2πzw) dz` (`halfLineCosTransform`).

**Theorem** (`eq_zero_of_inversionSymmetric_of_cosTransform_inversionSymmetric`).  If
`f(1/x) = x f(x)` and `Cf(1/x) = x Cf(x)` for every `x > 0`, then `f = 0`.

**Proof.**  Weight-one inversion symmetry is the reflection `𝓜g(1 − s) = 𝓜g(s)` of the Mellin
transform (`mellin_one_sub_of_inversionSymmetric`).  The local functional equation
`Γ_ℝ(½+iτ) 𝓜[Cf](½−iτ) = Γ_ℝ(½−iτ) 𝓜f(½+iτ)` (`Gammaℝ_mul_mellin_halfLineCosTransform`) at `τ`
and `−τ`, together with both reflections, gives
`𝓜f(½+iτ) (Γ_ℝ(½+iτ)² − Γ_ℝ(½−iτ)²) = 0` (`mellin_mul_twist_eq_zero`).  The ratio
`Γ_ℝ(½+iτ)/Γ_ℝ(½−iτ) = e^{2iθ(τ)}` is the Riemann–Siegel phase, so the bracket vanishes only
where `θ(τ) ∈ (π/2)ℤ`.  The entire function `Q(z) = Γ_ℝ(½−iz)^{−2} − Γ_ℝ(½+iz)^{−2}` is not
identically zero, because `Q(−i/4) = Γ_ℝ(¼)^{−2} − Γ_ℝ(¾)^{−2}` and `Γ_ℝ` is strictly decreasing on
`(0, 1)`.  Its real zeros are therefore isolated, `τ ↦ 𝓜f(½+iτ)` is continuous, and so `𝓜f`
vanishes on the whole critical line.  Hence `f = 0` (`eq_zero_of_mellin_criticalLine_eq_zero`).

**Reading for prime-blind positivity.**
* *PBAP data.*  For a test `f`, the kernel of prime-blind positivity is the dilation
  autocorrelation `A_f(x) = ∫ f(t) f(xt) dt`.  It is inversion-symmetric, its Mellin data on the
  critical line are `|𝓜f(½+it)|² ≥ 0`, and prime-blindness is pointwise: `A_f(n) = 0`.
* *Mayer data.*  The Gauss–Farey/Mayer recursion behind the rigidity of Fourier-blind cores needs a
  single function that is inversion-symmetric *and* whose Fourier transform carries the blindness
  conditions.  For `A_f` that function would be `C A_f`, whose Mellin data are
  `e^{2iθ(t)} |𝓜f(½+it)|²`.
* *The obstruction.*  By the theorem, `C A_f` is never inversion-symmetric unless `A_f = 0` (for
  smooth `A_f`).  The two structures are separated by the Riemann–Siegel phase, and they coexist
  only after the phase is absorbed by `ζ(½+it)²`, i.e. on `Ξ²`-divisible (null-face) tests.
* *Consequence.*  Transfer-operator gauges, which certify the sharp null-face rigidity thresholds,
  give no positivity-free certificate for the pole term of prime-blind positivity.
-/

open MeasureTheory Set Real Filter Topology Complex
open scoped ContDiff

namespace RHTower

noncomputable section

/-- Weight-one inversion symmetry `g(1/x) = x g(x)` reflects the Mellin transform about `½`. -/
theorem mellin_one_sub_of_inversionSymmetric {g : ℝ → ℂ}
    (hg : ∀ x : ℝ, 0 < x → g x⁻¹ = (x : ℂ) * g x) (s : ℂ) : mellin g (1 - s) = mellin g s := by
  have h1 := mellin_comp_inv g (s - 1)
  have h2 : mellin (fun t => g t⁻¹) (s - 1) =
      mellin (fun t => (t : ℂ) ^ (1 : ℂ) • g t) (s - 1) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Complex.cpow_one, smul_eq_mul, hg t ht]
  have h3 := mellin_cpow_smul g (s - 1) 1
  calc mellin g (1 - s) = mellin g (-(s - 1)) := by congr 1; ring
    _ = mellin (fun t => g t⁻¹) (s - 1) := h1.symm
    _ = mellin (fun t => (t : ℂ) ^ (1 : ℂ) • g t) (s - 1) := h2
    _ = mellin g (s - 1 + 1) := h3
    _ = mellin g s := by congr 1; ring

/-- `Γ_ℝ` at a real point. -/
theorem Gammaℝ_ofReal_eq (x : ℝ) :
    Gammaℝ (x : ℂ) = ((Real.pi ^ (-x / 2) * Real.Gamma (x / 2) : ℝ) : ℂ) := by
  rw [Gammaℝ_def, show -(x : ℂ) / 2 = ((-x / 2 : ℝ) : ℂ) by push_cast; ring,
    show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
  push_cast
  ring

variable {f : ℝ → ℝ}

/-- **The twist identity.**  If `f` and `Cf` are inversion-symmetric, then
`𝓜f(½+iτ) (Γ_ℝ(½+iτ)² − Γ_ℝ(½−iτ)²) = 0`. -/
theorem mellin_mul_twist_eq_zero (hf : ContDiff ℝ ∞ f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) (hinv : ∀ x, 0 < x → f x⁻¹ = x * f x)
    (hinvC : ∀ x, 0 < x → halfLineCosTransform f x⁻¹ = x * halfLineCosTransform f x)
    (τ : ℝ) :
    mellin (fun t => (f t : ℂ)) (cosKernelLinePt τ) *
      (Gammaℝ (cosKernelLinePt τ) ^ 2 - Gammaℝ (cosKernelLinePt (-τ)) ^ 2) = 0 := by
  have hF : ∀ x : ℝ, 0 < x → (fun t => (f t : ℂ)) x⁻¹ = (x : ℂ) * (fun t => (f t : ℂ)) x :=
    fun x hx => by simp only [hinv x hx, Complex.ofReal_mul]
  have hC : ∀ x : ℝ, 0 < x → (fun t => (halfLineCosTransform f t : ℂ)) x⁻¹ =
      (x : ℂ) * (fun t => (halfLineCosTransform f t : ℂ)) x :=
    fun x hx => by simp only [hinvC x hx, Complex.ofReal_mul]
  have pt : 1 - cosKernelLinePt τ = cosKernelLinePt (-τ) := by
    unfold cosKernelLinePt; push_cast; ring
  have sa : mellin (fun t => (f t : ℂ)) (cosKernelLinePt (-τ)) =
      mellin (fun t => (f t : ℂ)) (cosKernelLinePt τ) := by
    rw [← pt]; exact mellin_one_sub_of_inversionSymmetric hF _
  have sb : mellin (fun t => (halfLineCosTransform f t : ℂ)) (cosKernelLinePt (-τ)) =
      mellin (fun t => (halfLineCosTransform f t : ℂ)) (cosKernelLinePt τ) := by
    rw [← pt]; exact mellin_one_sub_of_inversionSymmetric hC _
  have e1 := Gammaℝ_mul_mellin_halfLineCosTransform hf hα hsupp τ
  have e2 := Gammaℝ_mul_mellin_halfLineCosTransform hf hα hsupp (-τ)
  rw [neg_neg] at e2
  rw [sb] at e1
  rw [sa] at e2
  linear_combination Gammaℝ (cosKernelLinePt (-τ)) * e1 - Gammaℝ (cosKernelLinePt τ) * e2

/-- **A function and its cosine transform are never both inversion-symmetric.** -/
theorem eq_zero_of_inversionSymmetric_of_cosTransform_inversionSymmetric (hf : ContDiff ℝ ∞ f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hinv : ∀ x, 0 < x → f x⁻¹ = x * f x)
    (hinvC : ∀ x, 0 < x → halfLineCosTransform f x⁻¹ = x * halfLineCosTransform f x)
    (y : ℝ) : f y = 0 := by
  set F : ℝ → ℂ := fun t => (f t : ℂ) with hFdef
  set Q : ℂ → ℂ := fun z => (Gammaℝ (1 / 2 + (-z) * I))⁻¹ ^ 2 - (Gammaℝ (1 / 2 + z * I))⁻¹ ^ 2
    with hQdef
  have hQd : Differentiable ℂ Q := by
    have h1 : Differentiable ℂ fun z : ℂ => (Gammaℝ (1 / 2 + (-z) * I))⁻¹ :=
      differentiable_Gammaℝ_inv.comp (by fun_prop)
    have h2 : Differentiable ℂ fun z : ℂ => (Gammaℝ (1 / 2 + z * I))⁻¹ :=
      differentiable_Gammaℝ_inv.comp (by fun_prop)
    exact (h1.pow 2).sub (h2.pow 2)
  -- `Q` is not identically zero
  have hQne : Q (-I / 4) ≠ 0 := by
    have a1 : (1 / 2 : ℂ) + -(-I / 4) * I = ((1 / 4 : ℝ) : ℂ) := by
      push_cast; linear_combination (1 / 4 : ℂ) * I_sq
    have a2 : (1 / 2 : ℂ) + (-I / 4) * I = ((3 / 4 : ℝ) : ℂ) := by
      push_cast; linear_combination (-1 / 4 : ℂ) * I_sq
    simp only [hQdef]
    rw [a1, a2, Gammaℝ_ofReal_eq, Gammaℝ_ofReal_eq]
    have g1 : Real.Gamma (3 / 4 / 2) < Real.Gamma (1 / 4 / 2) :=
      Real.Gamma_strictAntiOn_Ioc ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
        (by norm_num)
    have p1 : Real.pi ^ (-(3 / 4 : ℝ) / 2) < Real.pi ^ (-(1 / 4 : ℝ) / 2) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith [Real.pi_gt_three]) (by norm_num)
    have q1 : 0 < Real.Gamma (3 / 4 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have q2 : 0 < Real.pi ^ (-(3 / 4 : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    set u := Real.pi ^ (-(1 / 4 : ℝ) / 2) * Real.Gamma (1 / 4 / 2)
    set v := Real.pi ^ (-(3 / 4 : ℝ) / 2) * Real.Gamma (3 / 4 / 2)
    have hv : 0 < v := mul_pos q2 q1
    have huv : v < u := mul_lt_mul p1 g1.le q1 (le_trans q2.le p1.le)
    have hu : 0 < u := hv.trans huv
    have hlt : u⁻¹ ^ 2 < v⁻¹ ^ 2 := by
      have := inv_strictAnti₀ hv huv
      exact pow_lt_pow_left₀ this (inv_nonneg.mpr hu.le) two_ne_zero
    intro h
    have h' : ((u⁻¹ ^ 2 - v⁻¹ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have := Complex.ofReal_eq_zero.mp h'
    linarith
  -- on the real line `𝓜f(½+iτ) · Q(τ) = 0`
  have hreal : ∀ τ : ℝ, mellin F (cosKernelLinePt τ) * Q τ = 0 := by
    intro τ
    have h := mellin_mul_twist_eq_zero hf hα hsupp hinv hinvC τ
    have hp : Gammaℝ (cosKernelLinePt τ) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by simp [cosKernelLinePt])
    have hm : Gammaℝ (cosKernelLinePt (-τ)) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by simp [cosKernelLinePt])
    have e1 : (1 / 2 : ℂ) + (-(τ : ℂ)) * I = cosKernelLinePt (-τ) := by
      unfold cosKernelLinePt; push_cast; ring
    have e2 : (1 / 2 : ℂ) + (τ : ℂ) * I = cosKernelLinePt τ := rfl
    simp only [hQdef]
    rw [e1, e2]
    have key : (Gammaℝ (cosKernelLinePt (-τ)))⁻¹ ^ 2 - (Gammaℝ (cosKernelLinePt τ))⁻¹ ^ 2 =
        (Gammaℝ (cosKernelLinePt τ) ^ 2 - Gammaℝ (cosKernelLinePt (-τ)) ^ 2) *
          ((Gammaℝ (cosKernelLinePt τ) * Gammaℝ (cosKernelLinePt (-τ))) ^ 2)⁻¹ := by
      field_simp
    rw [key, ← mul_assoc, h, zero_mul]
  -- continuity of `τ ↦ 𝓜f(½+iτ)`
  have hFc : Continuous F := Complex.continuous_ofReal.comp hf.continuous
  have hd : ∀ s : ℂ, DifferentiableAt ℂ (mellin F) s := by
    intro s
    have hloc : LocallyIntegrableOn F (Ioi 0) := hFc.locallyIntegrable.locallyIntegrableOn _
    have htop : F =O[atTop] fun x : ℝ => x ^ (-(s.re + 1)) := by
      refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
      filter_upwards [eventually_gt_atTop β] with x hx
      have : f x = 0 := by
        by_contra h0
        linarith [(hsupp x h0).2]
      simp [hFdef, this]
    have hbot : F =O[𝓝[>] 0] fun x : ℝ => x ^ (-(s.re - 1)) := by
      refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
      filter_upwards [Ioo_mem_nhdsGT hα] with x hx
      have : f x = 0 := by
        by_contra h0
        linarith [(hsupp x h0).1, hx.2]
      simp [hFdef, this]
    exact mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hbot (by linarith)
  have hcont : Continuous fun τ : ℝ => mellin F (cosKernelLinePt τ) := by
    have hpt : Continuous fun τ : ℝ => cosKernelLinePt τ := by
      unfold cosKernelLinePt; fun_prop
    exact continuous_iff_continuousAt.2 fun τ => (hd _).continuousAt.comp hpt.continuousAt
  -- vanishing on the whole critical line
  have hzero : ∀ τ₀ : ℝ, mellin F (cosKernelLinePt τ₀) = 0 := by
    intro τ₀
    rcases (hQd.analyticAt (τ₀ : ℂ)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have hEq := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun z _ => hQd.analyticAt z) isPreconnected_univ (mem_univ _) h (mem_univ (-I / 4))
      exact hQne hEq
    · have ht : Tendsto (fun τ : ℝ => (τ : ℂ)) (𝓝[≠] τ₀) (𝓝[≠] (τ₀ : ℂ)) :=
        tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto τ₀).mono_left
          nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun τ hτ h' =>
            hτ (Complex.ofReal_injective h')⟩
      have hev : ∀ᶠ τ in 𝓝[≠] τ₀, mellin F (cosKernelLinePt τ) = 0 :=
        (ht.eventually h).mono fun τ hτ => (mul_eq_zero.mp (hreal τ)).resolve_right hτ
      have hlim1 : Tendsto (fun τ : ℝ => mellin F (cosKernelLinePt τ)) (𝓝[≠] τ₀)
          (𝓝 (mellin F (cosKernelLinePt τ₀))) :=
        (hcont.tendsto τ₀).mono_left nhdsWithin_le_nhds
      have hlim2 : Tendsto (fun τ : ℝ => mellin F (cosKernelLinePt τ)) (𝓝[≠] τ₀) (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun τ h => h.symm)
      exact tendsto_nhds_unique hlim1 hlim2
  exact eq_zero_of_mellin_criticalLine_eq_zero hf hα hαβ hsupp (fun t => hzero t) y

end

end RHTower
