import GaloisForLFunctions.RHTower.CCM.CCMRectangularDirichletLandau

/-!
# Euler locality of the physical-diagonal chart

The physical diagonal `u ↦ σ + u(σ−1)` zooms at the Euler point as `σ ↓ 1`.
A fixed divisor point `ρ` with `Re ρ < 1` is pulled back to
`u_ρ = (ρ−σ)/(σ−1)`, on the anti-causal side but escaping to infinity, and
the anti-causal Hardy energy of an amplitude-`m` pole there is
`|m|²(σ−1)/(2(σ−Re ρ))`, which vanishes as `σ ↓ 1`.  Consequently every
finite part of the strict-right Xi divisor carries vanishing diagonal
anti-causal energy: the diagonal chart is finitely divisor-blind, and no
diagonal-limit energy bound can control the global anti-causal current.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Pullback of a divisor point through the physical diagonal `s = σ + u(σ−1)`. -/
def xiWardDiagonalPullback (sigma : ℝ) (rho : ℂ) : ℂ :=
  (rho - (sigma : ℂ)) / ((sigma : ℂ) - 1)

theorem xiWardDiagonalPullback_maps (sigma : ℝ) (rho : ℂ)
    (hsigma : 1 < sigma) :
    (sigma : ℂ) + xiWardDiagonalPullback sigma rho * ((sigma : ℂ) - 1) =
      rho := by
  have hne : ((sigma : ℂ) - 1) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re,
      Complex.zero_re] at hre
    linarith
  rw [xiWardDiagonalPullback]
  field_simp
  ring

/-- The pullback of a point left of the Euler edge is anti-causal. -/
theorem re_xiWardDiagonalPullback_neg {sigma : ℝ} {rho : ℂ}
    (hsigma : 1 < sigma) (hrho : rho.re < 1) :
    (xiWardDiagonalPullback sigma rho).re < 0 := by
  have hden : ((sigma : ℂ) - 1).im = 0 := by
    simp [Complex.sub_im]
  have hdenre : ((sigma : ℂ) - 1).re = sigma - 1 := by
    simp [Complex.sub_re]
  have hpos : 0 < sigma - 1 := by linarith
  rw [xiWardDiagonalPullback, Complex.div_re, hden, hdenre]
  have hnormSq : Complex.normSq ((sigma : ℂ) - 1) = (sigma - 1) ^ (2 : ℕ) := by
    rw [Complex.normSq_apply, hdenre, hden]
    ring
  rw [hnormSq]
  have hnum : (rho - (sigma : ℂ)).re = rho.re - sigma := by
    simp [Complex.sub_re]
  rw [hnum]
  have hnumneg : rho.re - sigma < 0 := by linarith
  have h2 : (0 : ℝ) < (sigma - 1) ^ (2 : ℕ) := by positivity
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
  have : (rho.re - sigma) * (sigma - 1) / (sigma - 1) ^ (2 : ℕ) < 0 := by
    apply div_neg_of_neg_of_pos _ h2
    exact mul_neg_of_neg_of_pos hnumneg hpos
  calc (rho.re - sigma) * (sigma - 1) / (sigma - 1) ^ (2 : ℕ) +
        rho.im * 0 / (sigma - 1) ^ (2 : ℕ)
      = (rho.re - sigma) * (sigma - 1) / (sigma - 1) ^ (2 : ℕ) := by ring
    _ < 0 := this

/-- Anti-causal Hardy self-energy of an amplitude-`m` pole at the diagonal
pullback of `ρ`: the Cauchy self-energy at reflected distance. -/
def xiWardDiagonalPoleEnergy (sigma : ℝ) (rho : ℂ) (m : ℝ) : ℝ :=
  m ^ (2 : ℕ) * (sigma - 1) / (2 * (sigma - rho.re))

theorem xiWardDiagonalPoleEnergy_eq_cauchySelfEnergy
    {sigma : ℝ} {rho : ℂ} (hsigma : 1 < sigma) (hrho : rho.re < 1)
    (m : ℝ) :
    xiWardDiagonalPoleEnergy sigma rho m =
      m ^ (2 : ℕ) / (2 * |(xiWardDiagonalPullback sigma rho).re|) := by
  have hre : (xiWardDiagonalPullback sigma rho).re =
      (rho.re - sigma) / (sigma - 1) := by
    have hden : ((sigma : ℂ) - 1).im = 0 := by simp [Complex.sub_im]
    have hdenre : ((sigma : ℂ) - 1).re = sigma - 1 := by
      simp [Complex.sub_re]
    rw [xiWardDiagonalPullback, Complex.div_re, hden, hdenre,
      Complex.normSq_apply, hdenre, hden]
    have hnum : (rho - (sigma : ℂ)).re = rho.re - sigma := by
      simp [Complex.sub_re]
    rw [hnum, Complex.sub_im, Complex.ofReal_im, sub_zero]
    have hpos : (0 : ℝ) < sigma - 1 := by linarith
    field_simp
    ring
  rw [hre]
  have hpos : (0 : ℝ) < sigma - 1 := by linarith
  have hneg : (rho.re - sigma) / (sigma - 1) < 0 := by
    apply div_neg_of_neg_of_pos _ hpos
    linarith
  rw [abs_of_neg hneg, xiWardDiagonalPoleEnergy]
  field_simp
  rw [show rho.re - sigma = -(sigma - rho.re) by ring, div_neg]
  ring

/-- **Euler-locality law**: the diagonal anti-causal energy of every fixed
divisor point vanishes as the diagonal collapses onto the Euler point. -/
theorem tendsto_xiWardDiagonalPoleEnergy_zero (rho : ℂ)
    (hrho : rho.re < 1) (m : ℝ) :
    Tendsto (fun sigma : ℝ => xiWardDiagonalPoleEnergy sigma rho m)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hnum : Tendsto (fun sigma : ℝ => m ^ (2 : ℕ) * (sigma - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have h1 : Tendsto (fun sigma : ℝ => m ^ (2 : ℕ) * (sigma - 1))
        (nhds 1) (nhds (m ^ (2 : ℕ) * (1 - 1))) :=
      (tendsto_id.sub_const 1).const_mul (m ^ (2 : ℕ))
    rw [show m ^ (2 : ℕ) * ((1 : ℝ) - 1) = 0 by ring] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun sigma : ℝ => 2 * (sigma - rho.re))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (2 * (1 - rho.re))) := by
    have h1 : Tendsto (fun sigma : ℝ => 2 * (sigma - rho.re))
        (nhds 1) (nhds (2 * (1 - rho.re))) :=
      (tendsto_id.sub_const rho.re).const_mul 2
    exact h1.mono_left nhdsWithin_le_nhds
  have hdenne : 2 * (1 - rho.re) ≠ 0 := by
    have : 0 < 1 - rho.re := by linarith
    positivity
  have := hnum.div hden hdenne
  simpa [xiWardDiagonalPoleEnergy, zero_div] using! this

/-- Instance on the actual strict-right Xi divisor: every copy sits left of
the Euler edge. -/
theorem xiRightCopy_re_lt_one (q : XiRightZeroCopy) :
    ((1 / 2 : ℂ) + xiRightCenteredZero q).re < 1 := by
  have h := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  simp only [Complex.add_re]
  norm_num
  linarith

/-- **Finite divisor blindness of the diagonal chart**: over every finite set
of strict-right copies, the total diagonal anti-causal energy vanishes in the
Euler limit.  No diagonal-limit energy bound can therefore control the global
anti-causal current, whose per-pair edge energy exceeds eight. -/
theorem tendsto_xiWardDiagonalDivisorEnergy_zero
    (F : Finset XiRightZeroCopy) (m : XiRightZeroCopy → ℝ) :
    Tendsto
      (fun sigma : ℝ => ∑ q ∈ F,
        xiWardDiagonalPoleEnergy sigma
          ((1 / 2 : ℂ) + xiRightCenteredZero q) (m q))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have h := tendsto_finsetSum F (fun q _ =>
    tendsto_xiWardDiagonalPoleEnergy_zero
      ((1 / 2 : ℂ) + xiRightCenteredZero q)
      (xiRightCopy_re_lt_one q) (m q))
  simpa using h

end

end RHTower
