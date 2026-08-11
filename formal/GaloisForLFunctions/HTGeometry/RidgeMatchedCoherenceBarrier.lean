import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Ridge-matched coherence barrier

Very small singular packets do not automatically create large regularized cross coherence.  If
one synthesis packet has unregularized Rayleigh energy at most `ε r`, Cauchy--Schwarz bounds its
coupling square by the exact visibility factor `ε / (1 + ε)`.  Crossing the Route-G threshold
`1 / 15` therefore forces both packets above the ridge-scale floor `r / 14`.

These are Hilbert-space inequalities.  No spectral, zero-spacing, simplicity, or arithmetic
premise is built into them.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H X Y : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

/-- Tikhonov energy of one synthesis coordinate. -/
def ridgeSynthesisEnergy (S : X →L[ℂ] H) (r : ℝ) (x : X) : ℝ :=
  ‖S x‖ ^ 2 + r * ‖x‖ ^ 2

/-- Squared Hilbert coupling is bounded by the product of the two synthesis energies. -/
theorem cross_inner_norm_sq_le
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (x : X) (y : Y) :
    ‖inner ℂ (A x) (C y)‖ ^ 2 ≤ ‖A x‖ ^ 2 * ‖C y‖ ^ 2 := by
  have hcs : ‖inner ℂ (A x) (C y)‖ ≤ ‖A x‖ * ‖C y‖ :=
    norm_inner_le_norm _ _
  have hcross : 0 ≤ ‖inner ℂ (A x) (C y)‖ := norm_nonneg _
  have hprod : 0 ≤ ‖A x‖ * ‖C y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_nonneg (sub_nonneg.mpr hcs) (add_nonneg hprod hcross)]

/-- A right packet whose unregularized synthesis energy is at most `ε r` times its coefficient
mass has normalized coupling square at most `ε / (1 + ε)`.  The division-free statement also
covers zero packets. -/
theorem cross_sq_visibility_le_right
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (r ε : ℝ) (x : X) (y : Y)
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hsmall : ‖C y‖ ^ 2 ≤ ε * r * ‖y‖ ^ 2) :
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2 ≤
      ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by
  have hcs := cross_inner_norm_sq_le A C x y
  have hA : ‖A x‖ ^ 2 ≤ ridgeSynthesisEnergy A r x := by
    simp only [ridgeSynthesisEnergy]
    nlinarith [mul_nonneg hr (sq_nonneg ‖x‖)]
  have hA0 : 0 ≤ ridgeSynthesisEnergy A r x :=
    (sq_nonneg ‖A x‖).trans hA
  have hC : (1 + ε) * ‖C y‖ ^ 2 ≤
      ε * ridgeSynthesisEnergy C r y := by
    simp only [ridgeSynthesisEnergy]
    nlinarith
  calc
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2
        ≤ (1 + ε) * (‖A x‖ ^ 2 * ‖C y‖ ^ 2) := by gcongr
    _ = ‖A x‖ ^ 2 * ((1 + ε) * ‖C y‖ ^ 2) := by ring
    _ ≤ ridgeSynthesisEnergy A r x *
        (ε * ridgeSynthesisEnergy C r y) := by gcongr
    _ = ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by ring

/-- Left-coordinate version of `cross_sq_visibility_le_right`. -/
theorem cross_sq_visibility_le_left
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (r ε : ℝ) (x : X) (y : Y)
    (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hsmall : ‖A x‖ ^ 2 ≤ ε * r * ‖x‖ ^ 2) :
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2 ≤
      ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by
  have h := cross_sq_visibility_le_right C A r ε y x hr hε hsmall
  calc
    (1 + ε) * ‖inner ℂ (A x) (C y)‖ ^ 2 =
        (1 + ε) * ‖inner ℂ (C y) (A x)‖ ^ 2 := by rw [norm_inner_symm]
    _ ≤ ε * ridgeSynthesisEnergy C r y * ridgeSynthesisEnergy A r x := h
    _ = ε * ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y := by ring

/-- Crossing the Suzuki high-assistance threshold forces both synthesis packets above the exact
ridge-scale floor `r / 14`. -/
theorem cross_sq_gt_oneFifteenth_forces_ridge_matched
    (A : X →L[ℂ] H) (C : Y →L[ℂ] H) (r : ℝ) (x : X) (y : Y)
    (hr : 0 ≤ r)
    (hcoh : ridgeSynthesisEnergy A r x * ridgeSynthesisEnergy C r y / 15 <
      ‖inner ℂ (A x) (C y)‖ ^ 2) :
    r * ‖x‖ ^ 2 / 14 < ‖A x‖ ^ 2 ∧
      r * ‖y‖ ^ 2 / 14 < ‖C y‖ ^ 2 := by
  constructor
  · by_contra h
    have hsmall : ‖A x‖ ^ 2 ≤ (1 / 14 : ℝ) * r * ‖x‖ ^ 2 := by
      have := le_of_not_gt h
      nlinarith
    have hvis := cross_sq_visibility_le_left A C r (1 / 14) x y hr (by norm_num) hsmall
    nlinarith
  · by_contra h
    have hsmall : ‖C y‖ ^ 2 ≤ (1 / 14 : ℝ) * r * ‖y‖ ^ 2 := by
      have := le_of_not_gt h
      nlinarith
    have hvis := cross_sq_visibility_le_right A C r (1 / 14) x y hr (by norm_num) hsmall
    nlinarith

/-- If a total cross interaction exceeds `theta` ridge units while its far part costs at most
`delta` ridge units, the intermediate collar carries the remaining coefficient mass.  Arithmetic
applications separately bound the two displayed component pairings. -/
theorem cross_coherence_forces_collar_mass
    (Bmid Bfar : Y →L[ℂ] X) (r theta delta C : ℝ)
    (x : X) (y yMid yFar : Y)
    (hmid : ‖inner ℂ (Bmid yMid) x‖ ≤ C * ‖yMid‖ * ‖x‖)
    (hfar : ‖inner ℂ (Bfar yFar) x‖ ≤ delta * r * ‖y‖ * ‖x‖)
    (hcoh : theta * r * ‖x‖ * ‖y‖ <
      ‖inner ℂ (Bmid yMid + Bfar yFar) x‖) :
    (theta - delta) * r * ‖y‖ < C * ‖yMid‖ := by
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    simp at hcoh
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hsplit : ‖inner ℂ (Bmid yMid + Bfar yFar) x‖ ≤
      C * ‖yMid‖ * ‖x‖ + delta * r * ‖y‖ * ‖x‖ := by
    calc
      ‖inner ℂ (Bmid yMid + Bfar yFar) x‖ =
          ‖inner ℂ (Bmid yMid) x + inner ℂ (Bfar yFar) x‖ := by rw [inner_add_left]
      _ ≤ ‖inner ℂ (Bmid yMid) x‖ + ‖inner ℂ (Bfar yFar) x‖ := norm_add_le _ _
      _ ≤ C * ‖yMid‖ * ‖x‖ + delta * r * ‖y‖ * ‖x‖ := add_le_add hmid hfar
  have hfact : ((theta - delta) * r * ‖y‖) * ‖x‖ <
      (C * ‖yMid‖) * ‖x‖ := by
    nlinarith [lt_of_lt_of_le hcoh hsplit]
  exact lt_of_mul_lt_mul_right hfact hxpos.le

omit [InnerProductSpace ℂ H] in
/-- A vector difference with squared norm above `1/16` has one component above `1/64`. -/
theorem oneSixteenth_lt_norm_sub_sq_split (p q : H)
    (hgain : 1 / 16 < ‖p - q‖ ^ 2) :
    1 / 64 < ‖p‖ ^ 2 ∨ 1 / 64 < ‖q‖ ^ 2 := by
  by_contra h
  rw [not_or] at h
  have hp := le_of_not_gt h.1
  have hq := le_of_not_gt h.2
  have hp' : ‖p‖ ≤ 1 / 8 := by nlinarith [norm_nonneg p]
  have hq' : ‖q‖ ≤ 1 / 8 := by nlinarith [norm_nonneg q]
  have htri : ‖p - q‖ ≤ ‖p‖ + ‖q‖ := norm_sub_le p q
  nlinarith [norm_nonneg (p - q)]

/-- If the direct-source part alone exceeds `1/64`, its resolvent envelope forces the normalized
Schur gap below `64 tau`. -/
theorem directSource_gain_forces_gap_lt
    {rho tau direct : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hdirect : 1 / 64 < direct)
    (henvelope : direct ≤ tau / (1 - rho ^ 2)) :
    1 - rho ^ 2 < 64 * tau := by
  have hden : 0 < 1 - rho ^ 2 := by nlinarith
  have hscaled : direct * (1 - rho ^ 2) ≤ tau :=
    (le_div_iff₀ hden).mp henvelope
  nlinarith

/-- The exact source-cyclic threshold: gain above `1/64`, low source mass at most `7/8`, and a
spectral envelope `beta / (1 - beta)` force `beta > 1/57`. -/
theorem sourceCyclic_sq_gt_oneFiftySeventh
    {beta ell gain : ℝ}
    (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hell : ell ≤ 7 / 8)
    (hgain : 1 / 64 < gain)
    (henvelope : gain ≤ beta * ell / (1 - beta)) :
    1 / 57 < beta := by
  have hden : 0 < 1 - beta := sub_pos.mpr hbeta1
  have hscaled : gain * (1 - beta) ≤ beta * ell :=
    (le_div_iff₀ hden).mp henvelope
  nlinarith

/-- Visibility of both packets plus an unregularized cross-capacity bound forces an exact lower
gap for normalized coherence.  `EL` and `EH` are the two regularized Rayleigh energies. -/
theorem coherence_capacity_gap
    {eta r C EL EH qL qH : ℝ}
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hEL0 : 0 ≤ EL)
    (hEL : EL = qL + r) (hEH : EH = qH + r)
    (hvisL : eta ^ 2 * EL ≤ qL) (hvisH : eta ^ 2 * EH ≤ qH)
    (hcapacity : eta ^ 2 * EL * EH ≤ C ^ 2) :
    eta * r ≤ C * (1 - eta ^ 2) := by
  have hgap : 0 ≤ 1 - eta ^ 2 := by nlinarith
  have hL : r ≤ (1 - eta ^ 2) * EL := by
    rw [hEL] at hvisL
    nlinarith
  have hH : r ≤ (1 - eta ^ 2) * EH := by
    rw [hEH] at hvisH
    nlinarith
  have hprod : r * r ≤
      ((1 - eta ^ 2) * EL) * ((1 - eta ^ 2) * EH) := by
    gcongr
  have hsq : (eta * r) ^ 2 ≤ (C * (1 - eta ^ 2)) ^ 2 := by
    calc
      (eta * r) ^ 2 = eta ^ 2 * (r * r) := by ring
      _ ≤ eta ^ 2 *
          (((1 - eta ^ 2) * EL) * ((1 - eta ^ 2) * EH)) := by gcongr
      _ = (1 - eta ^ 2) ^ 2 * (eta ^ 2 * EL * EH) := by ring
      _ ≤ (1 - eta ^ 2) ^ 2 * C ^ 2 := by gcongr
      _ = (C * (1 - eta ^ 2)) ^ 2 := by ring
  nlinarith [mul_nonneg heta hr, mul_nonneg hC hgap]

/-- The direct-tail amplification branch is incompatible with the capacity gap once
`256 C tau ≤ r` and coherence is at least `1/4`. -/
theorem directSource_branch_incompatible_with_capacity
    {eta r C tau : ℝ}
    (heta : 1 / 4 ≤ eta) (hr : 0 < r) (hC : 0 ≤ C)
    (hcapacity : eta * r ≤ C * (1 - eta ^ 2))
    (hdirect : 1 - eta ^ 2 < 64 * tau)
    (hsmall : 256 * C * tau ≤ r) : False := by
  have hetaPos : 0 < eta := lt_of_lt_of_le (by norm_num) heta
  have hCpos : 0 < C := by
    by_contra h
    have hC0 : C = 0 := le_antisymm (le_of_not_gt h) hC
    rw [hC0] at hcapacity
    nlinarith [mul_pos hetaPos hr]
  have hmul := mul_lt_mul_of_pos_left hdirect hCpos
  nlinarith

/-- At the exact band edge `1/113`, low source mass at most `7/8` contributes at most `1/128`
through the odds transform `t / (1 - t)`. -/
theorem sourceCyclic_lowBand_le_oneOneTwentyEight
    {ell low : ℝ}
    (hell : ell ≤ 7 / 8) (hlow : low ≤ ell / 112) :
    low ≤ 1 / 128 := by
  linarith

/-- If total source-cyclic gain is above `1/64`, its low band contributes at most `1/128`, and
the high-band density is bounded by `C / r`, then high-band source mass exceeds `r / (128 C)`. -/
theorem sourceCyclic_highBand_mass_gt
    {r C gain low high mass : ℝ}
    (hr : 0 < r) (hC : 0 < C)
    (hsplit : gain = low + high)
    (hgain : 1 / 64 < gain) (hlow : low ≤ 1 / 128)
    (hhigh : high ≤ C / r * mass) :
    r / (128 * C) < mass := by
  have hhigh' : 1 / 128 < high := by linarith
  have hden : 0 < 128 * C := mul_pos (by norm_num) hC
  have hcm : 1 / 128 < C / r * mass := lt_of_lt_of_le hhigh' hhigh
  have hmass : r / 128 < C * mass := by
    calc
      r / 128 = r * (1 / 128) := by ring
      _ < r * (C / r * mass) := mul_lt_mul_of_pos_left hcm hr
      _ = C * mass := by field_simp
  exact (div_lt_iff₀ hden).mpr (by nlinarith)

end GaloisForLFunctions.HTGeometry
