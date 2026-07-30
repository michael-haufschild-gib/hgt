import Mathlib
import GaloisForLFunctions.RHTower.MobiusGammaEulerDifferenceTailParity

/-!
# Asymptotic transport of the Gamma-Euler difference

The single Gamma-Euler central difference applied to the Gamma height characteristic
`φ_r(u) = cosh(u/2)^{-r}` transports the first surviving tail coefficient exactly: as `u → ∞`,
`exp((r/2+1)u) · D_{r,h}φ_r(u) → gammaEulerOneDifferenceNextCoefficient r h`
(`gammaEulerOneDifference_asymptotic`, the `k = 1` case of equation (4)).

The mechanism is the exact factorisation `cosh(v/2)^{-r} = 2^r exp(-rv/2)(1 + exp(-v))^{-r}`
(`cosh_half_rpow_factor`), which writes `D_{r,h}φ_r(u) = 2^r exp(-ru/2)·F(exp(-u))` for a fixed profile
`F` with `F 0 = 0` and `F'(0) = -r·d_{r,h}(r/2+1)` (the next-mode eigenvalue).  The leading `exp(-ru/2)`
mode is annihilated (`F 0 = 0`); the boundary slope `F(e)/e → F'(0)` then extracts the exact limit.
-/

open Real Filter Topology


namespace RHTower

theorem cosh_half_rpow_factor (r v : ℝ) :
    (Real.cosh (v / 2)) ^ (-r) = 2 ^ r * Real.exp (-r * v / 2) * (1 + Real.exp (-v)) ^ (-r) := by
  have hcosh : Real.cosh (v / 2) = Real.exp (v / 2) / 2 * (1 + Real.exp (-v)) := by
    rw [Real.cosh_eq]
    have : Real.exp (-(v / 2)) = Real.exp (v / 2) * Real.exp (-v) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  rw [hcosh, Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow (by positivity) (by norm_num)]
  rw [show ((Real.exp (v / 2)) ^ (-r)) = Real.exp (-r * v / 2) by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; ring_nf,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

theorem gammaEulerOneDifference_asymptotic (r h : ℝ) :
    Tendsto (fun u => Real.exp ((r / 2 + 1) * u) *
        gammaEulerCentralDifference r h (fun u => (Real.cosh (u / 2)) ^ (-r)) u)
      atTop (𝓝 (gammaEulerOneDifferenceNextCoefficient r h)) := by
  set eig := gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) with heig
  set F : ℝ → ℝ := fun e =>
    2 * Real.cosh (r * h / 2) * (1 + e) ^ (-r)
      - Real.exp (-r * h / 2) * (1 + e * Real.exp (-h)) ^ (-r)
      - Real.exp (r * h / 2) * (1 + e * Real.exp h) ^ (-r) with hFdef
  have hident : ∀ u, gammaEulerCentralDifference r h (fun u => (Real.cosh (u / 2)) ^ (-r)) u
      = 2 ^ r * Real.exp (-r * u / 2) * F (Real.exp (-u)) := by
    intro u
    show 2 * Real.cosh (r * h / 2) * (Real.cosh (u / 2)) ^ (-r)
      - (Real.cosh ((u + h) / 2)) ^ (-r) - (Real.cosh ((u - h) / 2)) ^ (-r) = _
    rw [cosh_half_rpow_factor r u, cosh_half_rpow_factor r (u + h), cosh_half_rpow_factor r (u - h),
      hFdef]
    simp only
    rw [show Real.exp (-r * (u + h) / 2) = Real.exp (-r * u / 2) * Real.exp (-r * h / 2) by
        rw [← Real.exp_add]; ring_nf,
      show Real.exp (-r * (u - h) / 2) = Real.exp (-r * u / 2) * Real.exp (r * h / 2) by
        rw [← Real.exp_add]; ring_nf,
      show Real.exp (-(u + h)) = Real.exp (-u) * Real.exp (-h) by rw [← Real.exp_add]; ring_nf,
      show Real.exp (-(u - h)) = Real.exp (-u) * Real.exp h by rw [← Real.exp_add]; ring_nf]
    ring
  have hterm : ∀ (c : ℝ), HasDerivAt (fun e => (1 + e * c) ^ (-r)) (-r * c) 0 := by
    intro c
    have hlin : HasDerivAt (fun e : ℝ => 1 + e * c) c 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const c).const_add 1
    have := (Real.hasDerivAt_rpow_const (p := -r) (Or.inl (by norm_num : (1:ℝ) + (0:ℝ) * c ≠ 0))).comp 0 hlin
    simpa using! this
  have e1 : Real.exp (-r * h / 2) * Real.exp (-h) = Real.exp (-((r / 2 + 1) * h)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (r * h / 2) * Real.exp h = Real.exp ((r / 2 + 1) * h) := by
    rw [← Real.exp_add]; congr 1; ring
  have heig_exp : eig = 2 * Real.cosh (r * h / 2)
      - Real.exp ((r / 2 + 1) * h) - Real.exp (-((r / 2 + 1) * h)) := by
    rw [heig, gammaEulerCentralDifferenceEigenvalue,
      show Real.cosh ((r / 2 + 1) * h)
        = (Real.exp ((r / 2 + 1) * h) + Real.exp (-((r / 2 + 1) * h))) / 2 from Real.cosh_eq _]
    ring
  have hd0 : HasDerivAt F (-r * eig) 0 := by
    have h1 := hterm 1
    simp only [mul_one] at h1
    have h1' := h1.const_mul (2 * Real.cosh (r * h / 2))
    have h2 := (hterm (Real.exp (-h))).const_mul (Real.exp (-r * h / 2))
    have h3 := (hterm (Real.exp h)).const_mul (Real.exp (r * h / 2))
    have hsum := (h1'.sub h2).sub h3
    rw [hFdef]
    convert! hsum using 1
    rw [heig_exp]
    linear_combination (-r) * e1 + (-r) * e2
  have hF0 : F 0 = 0 := by
    rw [hFdef]; simp only [zero_mul, add_zero, Real.one_rpow, mul_one]; rw [Real.cosh_eq]; ring
  have hslope : Tendsto (fun e => F e / e) (𝓝[≠] 0) (𝓝 (-r * eig)) := by
    have hs := (hasDerivAt_iff_tendsto_slope.mp hd0)
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    rw [slope_def_field, hF0, sub_zero, sub_zero]
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    · filter_upwards with u; exact (Real.exp_pos _).ne'
  have hcomp : Tendsto (fun u => F (Real.exp (-u)) / Real.exp (-u)) atTop (𝓝 (-r * eig)) :=
    hslope.comp hexp
  have hcoeff : gammaEulerOneDifferenceNextCoefficient r h = 2 ^ r * (-r * eig) := by
    rw [gammaEulerOneDifferenceNextCoefficient, gammaEulerTailScale, heig,
      show Real.exp (r * Real.log 2) = (2:ℝ) ^ r by rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf]
    ring
  rw [hcoeff]
  refine (hcomp.const_mul (2 ^ r)).congr (fun u => ?_)
  rw [hident u, show Real.exp (-u) = (Real.exp u)⁻¹ from by rw [← Real.exp_neg]]
  rw [show Real.exp ((r / 2 + 1) * u) * (2 ^ r * Real.exp (-r * u / 2) * F (Real.exp u)⁻¹)
      = 2 ^ r * (Real.exp ((r / 2 + 1) * u) * Real.exp (-r * u / 2)) * F (Real.exp u)⁻¹ by ring,
    ← Real.exp_add, show (r / 2 + 1) * u + -r * u / 2 = u by ring]
  field_simp

end RHTower
