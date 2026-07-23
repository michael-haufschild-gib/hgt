import GaloisForLFunctions.RHTower.WeightedEulerPaleyWienerVanishing
import GaloisForLFunctions.RHTower.CompactCarrierPolynomialDetection

/-!
# Carrier separation from one-ray Fourier–Borel decay

A functional carried by a compact set whose carrier real parts stay below `β`
has Fourier–Borel transform growing at most like `e^{-βx}` on the negative
real ray.  If the transform additionally decays like `e^{-σ₀x}` on the
positive ray for some `σ₀ > β`, then multiplying by `e^{cz}` with
`c = (σ₀+β)/2` produces an entire function of exponential type decaying at
rate `(σ₀-β)/2` on both rays, and the Paley–Wiener vanishing theorem forces
the transform to vanish identically.  Every coordinate-power value of the
functional then vanishes by exponential-slope detection.

This is the separation step of the joint graph-decoupling argument: a decay
rate beyond every carrier real part pushes the minimal carrier out of the
carrier strip, so no nonzero functional survives.  Everything is
unconditional; the ray decay enters as an explicit hypothesis, produced
upstream by the prime-log oversampling lemma and the Möbius decay transfer.
-/

noncomputable section

namespace RHTower

open Complex Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- **Carrier separation**: a compactly carried functional whose carrier real
parts are at most `β` and whose Fourier–Borel transform decays at a rate
`σ₀ > β` on the positive ray has identically vanishing transform. -/
theorem compactFourierBorel_eq_zero_of_ray_decay
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {β σ₀ C : ℝ} (hβσ : β < σ₀)
    (hre_ub : ∀ k, (s k).re ≤ β)
    (hdecay : ∀ x : ℝ, 0 ≤ x →
      ‖compactFourierBorel L s (x : ℂ)‖ ≤ C * Real.exp (-(σ₀ * x))) :
    ∀ z : ℂ, compactFourierBorel L s z = 0 := by
  set F : ℂ → ℂ := compactFourierBorel L s with hF
  have hFdiff : Differentiable ℂ F := fun z =>
    ((compactFourierBorel_analyticOnNhd L s) z (Set.mem_univ z)).differentiableAt
  set c : ℝ := (σ₀ + β) / 2 with hc
  set ε : ℝ := (σ₀ - β) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set g : ℂ → ℂ := fun z => F z * Complex.exp ((c : ℂ) * z) with hg
  have hgdiff : Differentiable ℂ g :=
    hFdiff.mul (Complex.differentiable_exp.comp (differentiable_id.const_mul _))
  -- exponential-type growth of the multiplied transform
  have hFgrow : ∀ z : ℂ, ‖F z‖ ≤ ‖L‖ * Real.exp (‖s‖ * ‖z‖) := by
    intro z
    rw [hF]
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
  have hgrow : ∀ z : ℂ, ‖g z‖ ≤ ‖L‖ * Real.exp ((‖s‖ + |c|) * ‖z‖) := by
    intro z
    simp only [hg]
    rw [norm_mul, Complex.norm_exp]
    have h2 : ((c : ℂ) * z).re ≤ |c| * ‖z‖ := by
      calc ((c : ℂ) * z).re ≤ ‖(c : ℂ) * z‖ := Complex.re_le_norm _
        _ = |c| * ‖z‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖F z‖ * Real.exp (((c : ℂ) * z).re)
        ≤ (‖L‖ * Real.exp (‖s‖ * ‖z‖)) * Real.exp (|c| * ‖z‖) :=
          mul_le_mul (hFgrow z) (Real.exp_le_exp.2 h2) (Real.exp_nonneg _)
            (by positivity)
      _ = ‖L‖ * Real.exp ((‖s‖ + |c|) * ‖z‖) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  -- positive-ray decay of the multiplied transform
  have hplus : ∀ x : ℝ, 0 ≤ x →
      ‖g (x : ℂ)‖ ≤ max C ‖L‖ * Real.exp (-(ε * x)) := by
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
      _ ≤ max C ‖L‖ * Real.exp (-(ε * x)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  -- negative-ray decay from the carrier real-part ceiling
  have hminus : ∀ x : ℝ, x ≤ 0 →
      ‖g (x : ℂ)‖ ≤ max C ‖L‖ * Real.exp (ε * x) := by
    intro x hx
    simp only [hg]
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    have hFx : ‖F (x : ℂ)‖ ≤ ‖L‖ * Real.exp (-(β * x)) := by
      rw [hF]
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
    calc ‖F (x : ℂ)‖ * Real.exp (c * x)
        ≤ (‖L‖ * Real.exp (-(β * x))) * Real.exp (c * x) :=
          mul_le_mul_of_nonneg_right hFx (Real.exp_nonneg _)
      _ = ‖L‖ * Real.exp (-(β * x) + c * x) := by
          rw [mul_assoc, ← Real.exp_add]
      _ = ‖L‖ * Real.exp (ε * x) := by
          congr 2
          rw [hε, hc]
          ring
      _ ≤ max C ‖L‖ * Real.exp (ε * x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
  -- Paley–Wiener vanishing of the multiplied transform
  have hτ0 : (0:ℝ) ≤ ‖s‖ + |c| := by positivity
  have hzero := eq_zero_of_two_ray_exponential_decay hgdiff (norm_nonneg L)
    hτ0 hε0 hgrow hplus hminus
  intro z
  have hz := congrFun hzero z
  simp only [hg, Pi.zero_apply] at hz
  exact (mul_eq_zero.1 hz).resolve_right (Complex.exp_ne_zero _)

/-- **Coordinate-power separation**: under the same one-ray decay, every
coordinate-power value of the functional vanishes. -/
theorem map_coordinate_pow_eq_zero_of_ray_decay
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ))
    {β σ₀ C : ℝ} (hβσ : β < σ₀)
    (hre_ub : ∀ k, (s k).re ≤ β)
    (hdecay : ∀ x : ℝ, 0 ≤ x →
      ‖compactFourierBorel L s (x : ℂ)‖ ≤ C * Real.exp (-(σ₀ * x)))
    (N : ℕ) :
    L (s ^ N) = 0 :=
  map_coordinate_pow_eq_zero_of_fourierBorel_zero L s
    (compactFourierBorel_eq_zero_of_ray_decay L s hβσ hre_ub hdecay) N

end RHTower
