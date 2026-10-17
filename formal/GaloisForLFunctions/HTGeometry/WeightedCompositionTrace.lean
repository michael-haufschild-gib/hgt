import GaloisForLFunctions.HTGeometry.DiscHolomorphicFixedPoint
import GaloisForLFunctions.HTGeometry.DiscCoefficientExpansion
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The trace of a weighted composition operator on a disc

Let `Φ` be holomorphic on `D̄(c, R)` with `Φ(D̄(c, R)) ⊆ D̄(c, θR)`, `θ < 1`, and let `w` be holomorphic
on `D̄(c, R)`.  The operator `f ↦ w · f∘Φ` has the matrix `coeff_i(w ((Φ − c)/ρ)^j)` in the basis
`((z − c)/ρ)^j`.

**Theorem** (`hasSum_coeff_diag`).  Its diagonal sums to `w(p)/(1 − Φ′(p))`, `p` the fixed point of
`Φ`.

**Proof.**  `coeff_i(w ((Φ − c)/ρ)^i) = (2πi)⁻¹ ∮ w(z) q(z)^i/(z − c) dz` with `q = (Φ − c)/(z − c)`,
`|q| ≤ θ` on the circle; the geometric series sums to `(2πi)⁻¹ ∮ w(z)/(z − Φ(z)) dz`.  Write
`z − Φ(z) = (z − p) h(z)` with `h` the difference quotient.  It has no zero on the closed disc: `p` is
the only fixed point there (`exists_unique_fixedPoint`), no point of the circle is fixed, and
`h(p) = 1 − Φ′(p) ≠ 0` because `|Φ′(p)| < 1`.  Cauchy's formula evaluates the integral as
`w(p)/h(p)`.
-/

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DiscCoefficients

open DiscFixedPoint

/-- **The trace formula** for a weighted composition operator on a disc. -/
theorem hasSum_coeff_diag {c : ℂ} {R θ ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) {Φ w : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (closedBall c R))
    (hΦm : MapsTo Φ (closedBall c R) (closedBall c (θ * R)))
    (hw : DifferentiableOn ℂ w (closedBall c R)) {p : ℂ} (hp : p ∈ ball c R) (hfix : Φ p = p) :
    HasSum (fun i => coeff c R ρ i (fun z => w z * ((Φ z - c) / ρ) ^ i))
      (w p / (1 - deriv Φ p)) := by
  have hρC : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  -- the fixed point theorem on the open disc
  obtain ⟨p₀, -, -, huniq₀, hder₀⟩ := exists_unique_fixedPoint hR hθ0 hθ1
    (hΦ.mono ball_subset_closedBall) (hΦm.mono_left ball_subset_closedBall)
  have hpp₀ : p = p₀ := huniq₀ p hp hfix
  have hder : ‖deriv Φ p‖ ≤ contractionFactor θ := hpp₀ ▸ hder₀
  have huniq : ∀ q ∈ ball c R, Φ q = q → q = p := fun q hq hq' =>
    (huniq₀ q hq hq').trans hpp₀.symm
  have hκ := contractionFactor_lt_one hθ0 hθ1
  have hder1 : 1 - deriv Φ p ≠ 0 := by
    intro h
    have h1 : deriv Φ p = 1 := by linear_combination -h
    rw [h1, norm_one] at hder
    linarith
  -- the factorization `z − Φ z = (z − p) h(z)`
  set F : ℂ → ℂ := fun z => z - Φ z with hF
  set h : ℂ → ℂ := dslope F p with hh
  have hFd : DifferentiableOn ℂ F (closedBall c R) := differentiableOn_id.sub hΦ
  have hnhds : closedBall c R ∈ 𝓝 p :=
    mem_of_superset (isOpen_ball.mem_nhds hp) ball_subset_closedBall
  have hhd : DifferentiableOn ℂ h (closedBall c R) :=
    (Complex.differentiableOn_dslope hnhds).mpr hFd
  have hFp : F p = 0 := by simp only [hF, hfix, sub_self]
  have hfac : ∀ z, F z = (z - p) * h z := fun z => by
    have h1 := sub_smul_dslope F p z
    rw [smul_eq_mul, hFp, sub_zero] at h1
    exact h1.symm
  have hhp : h p = 1 - deriv Φ p := by
    rw [hh, dslope_same]
    have hd : HasDerivAt Φ (deriv Φ p) p := (differentiableAt_of_mem_ball hΦ hp).hasDerivAt
    exact ((hasDerivAt_id p).sub hd).deriv
  have hfixF : ∀ z, F z = 0 → Φ z = z := fun z hz => by
    simp only [hF] at hz; linear_combination -hz
  have hsphere : ∀ z ∈ sphere c R, F z ≠ 0 := by
    intro z hz hFz
    have h1 := hΦm (sphere_subset_closedBall hz)
    rw [mem_closedBall, dist_eq_norm, hfixF z hFz, norm_sub_eq_of_mem_sphere hz] at h1
    nlinarith
  have hne : ∀ z ∈ closedBall c R, h z ≠ 0 := by
    intro z hz
    rcases eq_or_ne z p with rfl | hzp
    · rw [hhp]; exact hder1
    · intro h0
      have hFz : F z = 0 := by rw [hfac, h0, mul_zero]
      rcases (mem_closedBall.mp hz).lt_or_eq with hlt | heq
      · exact hzp (huniq z (mem_ball.mpr hlt) (hfixF z hFz))
      · exact hsphere z (mem_sphere.mpr heq) hFz
  -- the geometric series under the integral
  obtain ⟨W, hW⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn
    (hw.continuousOn.mono sphere_subset_closedBall)
  have hW0 : 0 ≤ W := by
    have := hW (c + R) (by simp [abs_of_pos hR]); exact (norm_nonneg _).trans this
  set G : ℕ → ℂ → ℂ := fun i z => (z - c)⁻¹ * w z * ((Φ z - c) / (z - c)) ^ i with hG
  have hzc : ∀ z ∈ sphere c R, z - c ≠ 0 := fun z hz h0 => by
    have := norm_sub_eq_of_mem_sphere hz; rw [h0, norm_zero] at this; linarith
  have hq : ∀ z ∈ sphere c R, ‖(Φ z - c) / (z - c)‖ ≤ θ := fun z hz => by
    have h1 := hΦm (sphere_subset_closedBall hz)
    rw [mem_closedBall, dist_eq_norm] at h1
    rw [norm_div, norm_sub_eq_of_mem_sphere hz, div_le_iff₀ hR]
    exact h1
  have hGb : ∀ i, ∀ z ∈ sphere c R, ‖G i z‖ ≤ R⁻¹ * W * θ ^ i := by
    intro i z hz
    simp only [hG]
    rw [norm_mul, norm_mul, norm_inv, norm_sub_eq_of_mem_sphere hz, norm_pow]
    gcongr
    · exact hW z hz
    · exact hq z hz
  have hGc : ∀ i, ContinuousOn (G i) (sphere c R) := by
    intro i
    simp only [hG]
    have hinv : ContinuousOn (fun z : ℂ => (z - c)⁻¹) (sphere c R) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun z hz => hzc z hz
    exact (hinv.mul (hw.continuousOn.mono sphere_subset_closedBall)).mul
      (((hΦ.continuousOn.mono sphere_subset_closedBall).sub continuousOn_const).div
        (continuousOn_id.sub continuousOn_const) (fun z hz => hzc z hz) |>.pow i)
  have hGs : ∀ z ∈ sphere c R, HasSum (fun i => G i z) (w z / F z) := by
    intro z hz
    have hq1 : ‖(Φ z - c) / (z - c)‖ < 1 := lt_of_le_of_lt (hq z hz) hθ1
    have hgeo := (hasSum_geometric_of_norm_lt_one hq1).mul_left ((z - c)⁻¹ * w z)
    have hden : 1 - (Φ z - c) / (z - c) ≠ 0 := by
      intro h0
      have : (Φ z - c) / (z - c) = 1 := by linear_combination -h0
      rw [this, norm_one] at hq1; exact lt_irrefl _ hq1
    have e : (z - c)⁻¹ * w z * (1 - (Φ z - c) / (z - c))⁻¹ = w z / F z := by
      have hzc' := hzc z hz
      simp only [hF]
      field_simp
      ring
    rw [e] at hgeo
    exact hgeo
  have hsumu : Summable fun i => R⁻¹ * W * θ ^ i :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left _
  have hI := hasSum_circleIntegral_of_dominated hR.le hGc hsumu hGb hGs
  -- Cauchy's formula for `w / h`
  have hwh : DifferentiableOn ℂ (fun z => w z / h z) (closedBall c R) := hw.div hhd hne
  have hcauchy : (∮ z in C(c, R), (z - p)⁻¹ • (w z / h z)) = (2 * π * I) • (w p / h p) :=
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hp
      hwh.continuousOn fun x hx => differentiableAt_of_mem_ball hwh hx.1
  have hint : (∮ z in C(c, R), w z / F z) = ∮ z in C(c, R), (z - p)⁻¹ • (w z / h z) := by
    congr 1; funext z
    rw [hfac, smul_eq_mul, div_mul_eq_div_div_swap, div_eq_inv_mul (w z / h z)]
  rw [hint, hcauchy, hhp] at hI
  have hI2 := hI.mul_left (2 * π * I)⁻¹
  rw [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul] at hI2
  have e2 : (fun i => coeff c R ρ i (fun z => w z * ((Φ z - c) / ρ) ^ i)) =
      fun i => (2 * π * I)⁻¹ * ∮ z in C(c, R), G i z := by
    funext i
    unfold coeff cauchyCoeff
    have e3 : (fun z => (ρ : ℂ) ^ i * (((z - c) ^ (i + 1))⁻¹ * (w z * ((Φ z - c) / ρ) ^ i))) =
        G i := by
      funext z
      have hρi : (ρ : ℂ) ^ i * ((Φ z - c) / ρ) ^ i = (Φ z - c) ^ i := by
        rw [← mul_pow, mul_div_cancel₀ _ hρC]
      simp only [hG]
      calc (ρ : ℂ) ^ i * (((z - c) ^ (i + 1))⁻¹ * (w z * ((Φ z - c) / ρ) ^ i))
          = ((z - c) ^ (i + 1))⁻¹ * w z * ((ρ : ℂ) ^ i * ((Φ z - c) / ρ) ^ i) := by ring
        _ = (z - c)⁻¹ * w z * ((Φ z - c) / (z - c)) ^ i := by
          rw [hρi, div_pow, pow_succ, mul_inv]; ring
    rw [← e3, circleIntegral.integral_const_mul]
    ring
  rw [e2]
  exact hI2

end GaloisForLFunctions.HTGeometry.DiscCoefficients

end
