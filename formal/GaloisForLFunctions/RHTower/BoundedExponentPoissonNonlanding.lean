import Mathlib
import GaloisForLFunctions.RHTower.BoundedExponentDilationOperator
import GaloisForLFunctions.RHTower.BoundedExponentMovingPole
import GaloisForLFunctions.RHTower.MeyerPoissonTest
import GaloisForLFunctions.RHTower.GammaDampedLaurentAtOne
import GaloisForLFunctions.RHTower.InfiniteDepthDilationLimit

/-!
# No finite exponent depth lands in Meyer's Poisson target

A function decaying faster than every power at both multiplicative ends of the ray has an
entire Mellin transform.  For the explicit source test `f(x) = x²(x² - 3/(2π))e^{-πx²}` the
depth-`M` dilation sum has Mellin transform `ζ(s)/ζ((M+1)s) · ℳf(s)` on `Re s > 1`.  Clearing
the zeta pole and the zeta zero turns this into an identity between two functions holomorphic
on the half-plane `Re s > -2`, which is convex and hence preconnected; the identity therefore
propagates to the travelling point `s_M = -2/(M+1)`.  There the left side vanishes, because the
depth dilation carries `s_M` onto the first trivial zero of `ζ`, while the right side does not,
because `ζ(s_M) ≠ 0` and `ℳf(s_M) ≠ 0`.  Hence no finite depth lands in the target space.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower

/-- Meyer's target space: rapid decay at both multiplicative ends of the ray. -/
structure RapidDecayRay (g : ℝ → ℂ) : Prop where
  contOn : ContinuousOn g (Ioi 0)
  decayTop : ∀ a : ℝ, g =O[atTop] fun x : ℝ => x ^ (-a)
  decayZero : ∀ b : ℝ, g =O[𝓝[>] 0] fun x : ℝ => x ^ (-b)

/-- Rapid decay at both ends makes the Mellin transform entire. -/
theorem differentiable_mellin_of_rapidDecayRay {g : ℝ → ℂ} (hg : RapidDecayRay g) :
    Differentiable ℂ (mellin g) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow
    (hg.contOn.locallyIntegrableOn measurableSet_Ioi)
    (hg.decayTop (s.re + 1)) (by linarith) (hg.decayZero (s.re - 1)) (by linarith)

/-! ## The entire multiple of zeta -/

/-- The entire function agreeing with `(s - 1) ζ(s)` away from the pole. -/
noncomputable def zetaEntire (s : ℂ) : ℂ :=
  (s - 1) * zetaPoleFree s + (Complex.Gammaℝ s)⁻¹

theorem differentiable_zetaEntire : Differentiable ℂ zetaEntire := by
  intro s
  exact (((differentiableAt_id).sub_const 1).mul (differentiable_zetaPoleFree s)).add
    (Complex.differentiable_Gammaℝ_inv s)

theorem zetaEntire_eq {s : ℂ} (hs : s ≠ 1) : zetaEntire s = (s - 1) * riemannZeta s := by
  have h : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hx : (s - 1) * (1 / (s - 1) / Complex.Gammaℝ s) = (Complex.Gammaℝ s)⁻¹ := by
    rcases eq_or_ne (Complex.Gammaℝ s) 0 with hg | hg
    · simp [hg]
    · field_simp
  rw [zetaEntire, zetaPoleFree, mul_sub, hx]
  ring

/-! ## The depth-`M` image of the explicit source test -/

/-- The depth-`M` bounded-exponent dilation of the explicit source test. -/
noncomputable def boundedExponentPoissonImage (M : ℕ) (x : ℝ) : ℂ :=
  mFreeDilationSum (M + 1) (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) x

/-- The archimedean part of the source test's Mellin transform. -/
noncomputable def meyerPoissonTestArch (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-(s + 4) / 2) * Complex.Gamma ((s + 2) / 2)

theorem meyerPoissonTestArch_ne_zero {s : ℂ} (hs : -2 < s.re) : meyerPoissonTestArch s ≠ 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  refine mul_ne_zero ?_ ?_
  · rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => hpi h.1
  · refine Complex.Gamma_ne_zero (fun m => ?_)
    refine ne_neg_natCast_of_zero_lt_re ?_ m
    have hwre : ((s + 2) / 2 : ℂ).re = (s.re + 2) / 2 := by
      rw [Complex.div_ofNat_re, Complex.add_re]
      norm_num
    rw [hwre]
    linarith

theorem differentiableAt_meyerPoissonTestArch {s : ℂ} (hs : -2 < s.re) :
    DifferentiableAt ℂ meyerPoissonTestArch s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_pi_ne_zero
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + 4) / 2)) s := by
    refine DifferentiableAt.const_cpow ?_ (Or.inl hpi)
    fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + 2) / 2)) s := by
    have hinner : DifferentiableAt ℂ (fun z : ℂ => (z + 2) / 2) s := by fun_prop
    have hGam : DifferentiableAt ℂ Complex.Gamma ((s + 2) / 2) := by
      refine Complex.differentiableAt_Gamma _ (fun m => ?_)
      refine ne_neg_natCast_of_zero_lt_re ?_ m
      have hwre : ((s + 2) / 2 : ℂ).re = (s.re + 2) / 2 := by
        rw [Complex.div_ofNat_re, Complex.add_re]
        norm_num
      rw [hwre]
      linarith
    exact hGam.comp s hinner
  exact h1.mul h2

theorem mellin_meyerPoissonTest_eq_arch {s : ℂ} (hs : -2 < s.re) :
    mellin (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) s
      = (s - 1) / 4 * meyerPoissonTestArch s := by
  rw [mellin_meyerPoissonTest hs, meyerPoissonTestArch, mul_assoc]

/-! ## The nonlanding theorem -/

/-- Cleared form of the depth-`M` Mellin identity: the left-hand side. -/
noncomputable def clearedLeft (M : ℕ) (s : ℂ) : ℂ :=
  mellin (boundedExponentPoissonImage M) s * zetaEntire (((M : ℂ) + 1) * s)

/-- Cleared form of the depth-`M` Mellin identity: the right-hand side. -/
noncomputable def clearedRight (M : ℕ) (s : ℂ) : ℂ :=
  zetaEntire s * (((M : ℂ) + 1) * s - 1) * meyerPoissonTestArch s / 4

theorem clearedLeft_eq_clearedRight_of_one_lt_re {M : ℕ} {s : ℂ} (hs : 1 < s.re) :
    clearedLeft M s = clearedRight M s := by
  have hk : ((M : ℂ) + 1) ≠ 0 := natCastAddOne_ne_zero M
  have hcast : (((M + 1 : ℕ) : ℂ)) = (M : ℂ) + 1 := by push_cast; ring
  have hkre : 1 < (((M : ℂ) + 1) * s).re := by
    have hre : (((M : ℂ) + 1) * s).re = ((M : ℝ) + 1) * s.re := by
      simp [Complex.mul_re]
    rw [hre]
    have hM : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) M
      linarith
    nlinarith
  have hzk : riemannZeta (((M : ℂ) + 1) * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hkre
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  have hks1 : ((M : ℂ) + 1) * s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hkre
    linarith
  have hs2 : -2 < s.re := by linarith
  have hmel : mellin (boundedExponentPoissonImage M) s
      = riemannZeta s / riemannZeta (((M : ℂ) + 1) * s) *
        mellin (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) s := by
    have hdef : boundedExponentPoissonImage M
        = mFreeDilationSum (M + 1) (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) := rfl
    rw [hdef, mellin_mFreeDilationSum (Nat.succ_ne_zero M) hs
      aestronglyMeasurable_meyerPoissonTest
      (integrableOn_rpow_mul_norm_meyerPoissonTest hs2), hcast]
  rw [clearedLeft, clearedRight, hmel, mellin_meyerPoissonTest_eq_arch hs2,
    zetaEntire_eq hks1, zetaEntire_eq hs1]
  field_simp

theorem analyticOnNhd_clearedRight (M : ℕ) :
    AnalyticOnNhd ℂ (clearedRight M) {s : ℂ | -2 < s.re} := by
  have hopen : IsOpen {s : ℂ | -2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro s hs
  have hs' : -2 < s.re := hs
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.div_const ?_ 4
  refine DifferentiableAt.mul ?_ (differentiableAt_meyerPoissonTestArch hs')
  exact (differentiable_zetaEntire s).mul (by fun_prop)

theorem analyticOnNhd_clearedLeft {M : ℕ}
    (hent : Differentiable ℂ (mellin (boundedExponentPoissonImage M))) :
    AnalyticOnNhd ℂ (clearedLeft M) {s : ℂ | -2 < s.re} := by
  have hopen : IsOpen {s : ℂ | -2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd ?_ hopen
  intro s _
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (hent s).mul ?_
  have hinner : DifferentiableAt ℂ (fun z : ℂ => ((M : ℂ) + 1) * z) s := by fun_prop
  exact (differentiable_zetaEntire (((M : ℂ) + 1) * s)).comp s hinner

/-- **No finite exponent depth lands in Meyer's Poisson target space.** -/
theorem not_rapidDecayRay_boundedExponentPoissonImage {M : ℕ} (hM : 1 ≤ M) :
    ¬ RapidDecayRay (boundedExponentPoissonImage M) := by
  intro hR
  have hent : Differentiable ℂ (mellin (boundedExponentPoissonImage M)) :=
    differentiable_mellin_of_rapidDecayRay hR
  set U : Set ℂ := {s : ℂ | -2 < s.re} with hU
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt (-2)).isPreconnected
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h2U : (2 : ℂ) ∈ U := by
    show -2 < (2 : ℂ).re
    norm_num
  have hagree : clearedLeft M =ᶠ[𝓝 (2 : ℂ)] clearedRight M := by
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hmem] with s hs
    exact clearedLeft_eq_clearedRight_of_one_lt_re hs
  have heq : EqOn (clearedLeft M) (clearedRight M) U :=
    (analyticOnNhd_clearedLeft hent).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_clearedRight M) hpre h2U hagree
  -- evaluate at the travelling pole
  have hpm : movingPolePoint M ∈ U := by
    show -2 < (movingPolePoint M).re
    rw [movingPolePoint_eq_ofReal, Complex.ofReal_re]
    have := neg_one_le_movingPolePoint_real hM
    linarith
  have hval := heq hpm
  have hleft : clearedLeft M (movingPolePoint M) = 0 := by
    rw [clearedLeft, succ_mul_movingPolePoint, zetaEntire_eq (by norm_num), riemannZeta_neg_two]
    ring
  have hright : clearedRight M (movingPolePoint M) ≠ 0 := by
    rw [clearedRight, succ_mul_movingPolePoint, zetaEntire_eq (movingPolePoint_ne_one M)]
    have hzm : riemannZeta (movingPolePoint M) ≠ 0 := riemannZeta_movingPolePoint_ne_zero hM
    have hsub : movingPolePoint M - 1 ≠ 0 := sub_ne_zero.mpr (movingPolePoint_ne_one M)
    have hre : -2 < (movingPolePoint M).re := hpm
    have harch : meyerPoissonTestArch (movingPolePoint M) ≠ 0 :=
      meyerPoissonTestArch_ne_zero hre
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hsub hzm) ?_) harch) (by norm_num)
    norm_num
  exact hright (hval ▸ hleft)

/-- **The bounded-exponent Poisson fracture.**  No finite exponent depth lands in the space of
functions decaying faster than every power at both multiplicative ends, yet the depth-truncated
dilations converge pointwise on the ray to the complete dilation sum. -/
theorem boundedExponentPoissonFracture {M : ℕ} (hM : 1 ≤ M) :
    ¬ RapidDecayRay (boundedExponentPoissonImage M) ∧
      ∀ x : ℝ, 0 < x →
        Tendsto (fun m : ℕ => mFreeDilationSum m
            (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) x)
          atTop (𝓝 (fullDilationSum (fun t : ℝ => ((meyerPoissonTest t : ℝ) : ℂ)) x)) :=
  ⟨not_rapidDecayRay_boundedExponentPoissonImage hM,
    fun _ hx => tendsto_meyerPoissonTest_dilation hx⟩

end RHTower
