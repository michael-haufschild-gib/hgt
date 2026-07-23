import GaloisForLFunctions.RHTower.WeightedEulerCarrierSeparation

/-!
# Carrier separation for functional-equation-paired differences

The two-carrier form of carrier separation: if two compactly carried
functionals have all carrier real parts at most `β`, and the difference of
their Fourier–Borel transforms decays at a rate `σ₀ > β` on the positive
ray, then the two transforms agree identically.

This is the separation statement for the functional-equation-odd difference
`B = A - R_*A`: the reflected functional is carried where the real parts stay
below the critical value, so a decay rate past the carrier ceiling forces the
paired transforms to coincide, and the odd part of the functional vanishes on
every exponential test.
-/

noncomputable section

namespace RHTower

open Complex Set

variable {K₁ K₂ : Type*} [TopologicalSpace K₁] [CompactSpace K₁]
  [TopologicalSpace K₂] [CompactSpace K₂]

/-- Growth bound for a Fourier–Borel transform. -/
theorem norm_compactFourierBorel_le_exp
    (L : C(K₁, ℂ) →L[ℂ] ℂ) (s : C(K₁, ℂ)) (z : ℂ) :
    ‖compactFourierBorel L s z‖ ≤ ‖L‖ * Real.exp (‖s‖ * ‖z‖) := by
  calc ‖compactFourierBorel L s z‖
      ≤ ‖L‖ * ‖compactExponentialTest s z‖ := L.le_opNorm _
    _ ≤ ‖L‖ * Real.exp (‖s‖ * ‖z‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
        apply (ContinuousMap.norm_le _ (Real.exp_nonneg _)).2
        intro k
        rw [compactExponentialTest_apply, Complex.norm_exp]
        apply Real.exp_le_exp.2
        calc (-z * s k).re ≤ ‖-z * s k‖ := Complex.re_le_norm _
          _ = ‖z‖ * ‖s k‖ := by rw [norm_mul, norm_neg]
          _ ≤ ‖z‖ * ‖s‖ := by
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
              exact s.norm_coe_le_norm k
          _ = ‖s‖ * ‖z‖ := mul_comm _ _

/-- Negative-ray growth bound from a carrier real-part ceiling. -/
theorem norm_compactFourierBorel_neg_ray_le
    (L : C(K₁, ℂ) →L[ℂ] ℂ) (s : C(K₁, ℂ)) {β : ℝ}
    (hre_ub : ∀ k, (s k).re ≤ β) {x : ℝ} (hx : x ≤ 0) :
    ‖compactFourierBorel L s (x : ℂ)‖ ≤ ‖L‖ * Real.exp (-(β * x)) := by
  calc ‖compactFourierBorel L s (x : ℂ)‖
      ≤ ‖L‖ * ‖compactExponentialTest s (x : ℂ)‖ := L.le_opNorm _
    _ ≤ ‖L‖ * Real.exp (-(β * x)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
        apply (ContinuousMap.norm_le _ (Real.exp_nonneg _)).2
        intro k
        rw [compactExponentialTest_apply, Complex.norm_exp]
        apply Real.exp_le_exp.2
        have hre : (-(x : ℂ) * s k).re = -x * (s k).re := by
          rw [show (-(x : ℂ)) = ((-x : ℝ) : ℂ) from by push_cast; ring,
            Complex.re_ofReal_mul]
        rw [hre]
        have hnx : 0 ≤ -x := by linarith
        calc -x * (s k).re ≤ -x * β :=
              mul_le_mul_of_nonneg_left (hre_ub k) hnx
          _ = -(β * x) := by ring

/-- **Two-carrier separation**: if both carrier real parts stay at most `β`
and the difference of Fourier–Borel transforms decays at a rate `σ₀ > β` on
the positive ray, the transforms agree identically. -/
theorem compactFourierBorel_sub_eq_zero_of_ray_decay
    (L₁ : C(K₁, ℂ) →L[ℂ] ℂ) (s₁ : C(K₁, ℂ))
    (L₂ : C(K₂, ℂ) →L[ℂ] ℂ) (s₂ : C(K₂, ℂ))
    {β σ₀ C : ℝ} (hβσ : β < σ₀)
    (hre₁ : ∀ k, (s₁ k).re ≤ β) (hre₂ : ∀ k, (s₂ k).re ≤ β)
    (hdecay : ∀ x : ℝ, 0 ≤ x →
      ‖compactFourierBorel L₁ s₁ (x : ℂ) - compactFourierBorel L₂ s₂ (x : ℂ)‖
        ≤ C * Real.exp (-(σ₀ * x))) :
    ∀ z : ℂ, compactFourierBorel L₁ s₁ z = compactFourierBorel L₂ s₂ z := by
  set F : ℂ → ℂ := fun z =>
    compactFourierBorel L₁ s₁ z - compactFourierBorel L₂ s₂ z with hF
  have hFdiff : Differentiable ℂ F := by
    apply Differentiable.sub
    · exact fun z => ((compactFourierBorel_analyticOnNhd L₁ s₁) z
        (Set.mem_univ z)).differentiableAt
    · exact fun z => ((compactFourierBorel_analyticOnNhd L₂ s₂) z
        (Set.mem_univ z)).differentiableAt
  set c : ℝ := (σ₀ + β) / 2 with hc
  set ε : ℝ := (σ₀ - β) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set g : ℂ → ℂ := fun z => F z * Complex.exp ((c : ℂ) * z) with hg
  have hgdiff : Differentiable ℂ g :=
    hFdiff.mul (Complex.differentiable_exp.comp (differentiable_id.const_mul _))
  set A₀ : ℝ := ‖L₁‖ + ‖L₂‖ with hA₀
  set M₀ : ℝ := max ‖s₁‖ ‖s₂‖ with hM₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hFgrow : ∀ z : ℂ, ‖F z‖ ≤ A₀ * Real.exp (M₀ * ‖z‖) := by
    intro z
    have h1 := norm_compactFourierBorel_le_exp L₁ s₁ z
    have h2 := norm_compactFourierBorel_le_exp L₂ s₂ z
    have e1 : Real.exp (‖s₁‖ * ‖z‖) ≤ Real.exp (M₀ * ‖z‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (norm_nonneg z))
    have e2 : Real.exp (‖s₂‖ * ‖z‖) ≤ Real.exp (M₀ * ‖z‖) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (norm_nonneg z))
    calc ‖F z‖ ≤ ‖compactFourierBorel L₁ s₁ z‖
        + ‖compactFourierBorel L₂ s₂ z‖ := norm_sub_le _ _
      _ ≤ ‖L₁‖ * Real.exp (M₀ * ‖z‖) + ‖L₂‖ * Real.exp (M₀ * ‖z‖) :=
          add_le_add
            (le_trans h1 (mul_le_mul_of_nonneg_left e1 (norm_nonneg L₁)))
            (le_trans h2 (mul_le_mul_of_nonneg_left e2 (norm_nonneg L₂)))
      _ = A₀ * Real.exp (M₀ * ‖z‖) := by rw [hA₀]; ring
  have hgrow : ∀ z : ℂ, ‖g z‖ ≤ A₀ * Real.exp ((M₀ + |c|) * ‖z‖) := by
    intro z
    simp only [hg]
    rw [norm_mul, Complex.norm_exp]
    have h2 : ((c : ℂ) * z).re ≤ |c| * ‖z‖ := by
      calc ((c : ℂ) * z).re ≤ ‖(c : ℂ) * z‖ := Complex.re_le_norm _
        _ = |c| * ‖z‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖F z‖ * Real.exp (((c : ℂ) * z).re)
        ≤ (A₀ * Real.exp (M₀ * ‖z‖)) * Real.exp (|c| * ‖z‖) :=
          mul_le_mul (hFgrow z) (Real.exp_le_exp.2 h2) (Real.exp_nonneg _)
            (by positivity)
      _ = A₀ * Real.exp ((M₀ + |c|) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hC0 : 0 ≤ C := by
    have h := hdecay 0 le_rfl
    have h0 := norm_nonneg (compactFourierBorel L₁ s₁ ((0:ℝ) : ℂ)
      - compactFourierBorel L₂ s₂ ((0:ℝ) : ℂ))
    have : Real.exp (-(σ₀ * 0)) = 1 := by norm_num
    nlinarith [le_trans h0 h]
  have hplus : ∀ x : ℝ, 0 ≤ x →
      ‖g (x : ℂ)‖ ≤ max C A₀ * Real.exp (-(ε * x)) := by
    intro x hx
    simp only [hg]
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    calc ‖F (x : ℂ)‖ * Real.exp (c * x)
        ≤ (C * Real.exp (-(σ₀ * x))) * Real.exp (c * x) :=
          mul_le_mul_of_nonneg_right (hdecay x hx) (Real.exp_nonneg _)
      _ = C * Real.exp (-(σ₀ * x) + c * x) := by
          rw [mul_assoc, ← Real.exp_add]
      _ = C * Real.exp (-(ε * x)) := by
          congr 2
          rw [hε, hc]
          ring
      _ ≤ max C A₀ * Real.exp (-(ε * x)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  have hminus : ∀ x : ℝ, x ≤ 0 →
      ‖g (x : ℂ)‖ ≤ max C A₀ * Real.exp (ε * x) := by
    intro x hx
    simp only [hg]
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    have hFx : ‖F (x : ℂ)‖ ≤ A₀ * Real.exp (-(β * x)) := by
      have h1 := norm_compactFourierBorel_neg_ray_le L₁ s₁ hre₁ hx
      have h2 := norm_compactFourierBorel_neg_ray_le L₂ s₂ hre₂ hx
      calc ‖F (x : ℂ)‖ ≤ ‖compactFourierBorel L₁ s₁ (x : ℂ)‖
          + ‖compactFourierBorel L₂ s₂ (x : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖L₁‖ * Real.exp (-(β * x)) + ‖L₂‖ * Real.exp (-(β * x)) :=
            add_le_add h1 h2
        _ = A₀ * Real.exp (-(β * x)) := by rw [hA₀]; ring
    calc ‖F (x : ℂ)‖ * Real.exp (c * x)
        ≤ (A₀ * Real.exp (-(β * x))) * Real.exp (c * x) :=
          mul_le_mul_of_nonneg_right hFx (Real.exp_nonneg _)
      _ = A₀ * Real.exp (-(β * x) + c * x) := by
          rw [mul_assoc, ← Real.exp_add]
      _ = A₀ * Real.exp (ε * x) := by
          congr 2
          rw [hε, hc]
          ring
      _ ≤ max C A₀ * Real.exp (ε * x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  have hτ0 : (0:ℝ) ≤ M₀ + |c| := by
    have : (0:ℝ) ≤ M₀ := le_trans (norm_nonneg s₁) (le_max_left _ _)
    positivity
  have hzero := eq_zero_of_two_ray_exponential_decay hgdiff hA₀0
    hτ0 hε0 hgrow hplus hminus
  intro z
  have hz := congrFun hzero z
  simp only [hg, Pi.zero_apply] at hz
  have hFz : F z = 0 :=
    (mul_eq_zero.1 hz).resolve_right (Complex.exp_ne_zero _)
  rw [hF] at hFz
  exact sub_eq_zero.1 hFz

end RHTower
