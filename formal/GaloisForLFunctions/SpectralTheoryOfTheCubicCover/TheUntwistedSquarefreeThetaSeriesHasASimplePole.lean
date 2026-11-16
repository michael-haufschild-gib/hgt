import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUnramifiedThetaSquareHasADoublePole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheUnramifiedSquareFactorsThroughTheUntwistedSeries
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTwistedSquarefreeCombinationHasASimplePole
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The untwisted squarefree theta series has a simple pole

The unramified double pole loses one order under cube removal. The two
primary signs and their common frequency scale give the exact residue of
`M(s) S₁(s/2)`. Since `M(4/3)` is nonzero, this is also a simple pole of the
actual untwisted squarefree series after dividing by the Mellin factor.
-/

noncomputable section
open Filter Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein
  FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-- The common frequency scale of the two primary signs. -/
def unitFrequencyWeight (s : ℂ) : ℂ :=
  ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s)

private theorem unitFrequencyBase_ne_zero :
    ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  have hξ := norm_pos_iff.mpr (cuspFrequency_ne_zero 1 one_ne_zero)
  positivity

theorem unitFrequencyWeight_ne_zero (s : ℂ) : unitFrequencyWeight s ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl unitFrequencyBase_ne_zero)

theorem unitFrequencyWeight_differentiable : Differentiable ℂ unitFrequencyWeight := by
  intro s
  exact differentiableAt_id.neg.const_cpow (Or.inl unitFrequencyBase_ne_zero)

/-- The continuation of `M(s) S₁(s/2)` after removing the cube zeta factor. -/
def completedUntwistedS (s : ℂ) : ℂ :=
  (s - 4 / 3) * completedUnramified s / (2 * unitFrequencyWeight s * star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s)

theorem completedUntwistedS_eq (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    completedUntwistedS s = besselSqMellin s * twistedSquarefreeSeries 1 (s / 2) := by
  have hZ := sub_mul_cubeZeta (s := s) (by linarith)
  have hden : 2 * unitFrequencyWeight s * star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero s))
        (pow_ne_zero 2 scalar_star_ne_zero)) (by norm_num))
      (clearedCubeZeta_ne_zero (by linarith))
  unfold completedUntwistedS
  rw [completedUnramified_eq s hs4 hs hi, unramifiedSquare_eq_squarefree s hs4, div_eq_iff hden]
  change (s - 4 / 3) * (besselSqMellin s * (2 * unitFrequencyWeight s *
    (star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) *
      twistedSquarefreeSeries 1 (s / 2)))) = _
  linear_combination (besselSqMellin s * 2 * unitFrequencyWeight s * star rationalSourceThetaScalar ^ 2 *
    twistedSquarefreeSeries 1 (s / 2)) * hZ

theorem completedUntwistedS_differentiableAt (s : ℂ) (hs1 : 4 / 3 < s.re) (hs : s.re < 13 / 3)
    (hi : 0 < s.im) : DifferentiableAt ℂ completedUntwistedS s := by
  have hden : 2 * unitFrequencyWeight s * star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero s))
        (pow_ne_zero 2 scalar_star_ne_zero)) (by norm_num))
      (clearedCubeZeta_ne_zero hs1)
  unfold completedUntwistedS
  exact ((differentiableAt_id.sub_const _).mul
    (completedUnramified_differentiableAt s (by linarith) hs hi)).div
      (((((unitFrequencyWeight_differentiable s).const_mul 2).mul_const _).mul_const _).mul
      (clearedCubeZeta_differentiable s)) hden

theorem completedUntwistedS_differentiableAt_near :
    ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ completedUntwistedS s := by
  filter_upwards [completedUnramified_differentiableAt_near,
    nhdsWithin_le_nhds clearedCubeZeta_eventually_ne] with s hΛ hZ
  unfold completedUntwistedS
  exact ((differentiableAt_id.sub_const _).mul hΛ).div
    (((((unitFrequencyWeight_differentiable s).const_mul 2).mul_const _).mul_const _).mul
      (clearedCubeZeta_differentiable s))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero s))
        (pow_ne_zero 2 scalar_star_ne_zero)) (by norm_num)) hZ)
/-- The residue of `M(s) S₁(s/2)` at `s=4/3`. -/
abbrev untwistedSResidue : ℂ :=
  243 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 /
    (4 * unitFrequencyWeight (4 / 3) * star rationalSourceThetaScalar ^ 2 *
      DirichletCharacter.LFunction chi3D 1)

theorem untwistedSResidue_ne_zero : untwistedSResidue ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr
    Real.pi_ne_zero))) (pow_ne_zero 3 constantArithmeticResidue_ne_zero))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero _))
      (pow_ne_zero 2 scalar_star_ne_zero)) LFunction_chi3D_one_ne_zero)

theorem completedUntwistedS_simple_pole :
    Tendsto (fun s => (s - 4 / 3) * completedUntwistedS s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 untwistedSResidue) := by
  have hZ : Tendsto clearedCubeZeta (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (clearedCubeZeta (4 / 3))) :=
    ((clearedCubeZeta_differentiable _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hden0 : 2 * unitFrequencyWeight (4 / 3) * star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta (4 / 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (unitFrequencyWeight_ne_zero (4 / 3)))
        (pow_ne_zero 2 scalar_star_ne_zero)) (by norm_num))
      clearedCubeZeta_four_thirds_ne_zero
  have hA : Tendsto unitFrequencyWeight (𝓝[≠] (4 / 3 : ℂ))
      (𝓝 (unitFrequencyWeight (4 / 3))) :=
    (unitFrequencyWeight_differentiable _).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := completedUnramified_double_pole.div
    ((((tendsto_const_nhds.mul hA).mul_const _).mul_const _).mul hZ) hden0
  have hlim : 6 * (Real.pi : ℂ) * thetaCoeff ^ 2 * constantArithmeticResidue /
      (2 * unitFrequencyWeight (4 / 3) * star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta (4 / 3)) = untwistedSResidue := by
    have hL := LFunction_chi3D_one_ne_zero
    have hC := scalar_star_ne_zero
    have hA0 := unitFrequencyWeight_ne_zero (4 / 3)
    rw [clearedCubeZeta_four_thirds, thetaCoeff]
    field_simp
    ring
  rw [← hlim]
  refine h.congr fun s => ?_
  simp only [Pi.div_apply]
  unfold completedUntwistedS
  ring
/-- The completed untwisted series has a nonzero simple pole. -/
theorem untwistedS_scaled_simple_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * twistedSquarefreeSeries 1 (s / 2)) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 untwistedSResidue) ∧
      Tendsto (fun s => (s - 4 / 3) * (Λ s / besselSqMellin s)) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (untwistedSResidue / besselSqMellin (4 / 3))) ∧
      untwistedSResidue ≠ 0 := by
  have hM : Tendsto besselSqMellin (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (besselSqMellin (4 / 3))) :=
    ((besselSqMellin_differentiableAt _ (by norm_num)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  refine ⟨completedUntwistedS, completedUntwistedS_eq, completedUntwistedS_differentiableAt,
    completedUntwistedS_differentiableAt_near, completedUntwistedS_simple_pole, ?_, untwistedSResidue_ne_zero⟩
  refine (completedUntwistedS_simple_pole.div hM besselSqMellin_four_thirds_ne_zero).congr fun s => ?_
  simp only [Pi.div_apply]
  ring

/-- The actual squarefree series, with the Mellin factor removed and variable `w=s/2`. -/
def continuedUntwistedTheta (w : ℂ) : ℂ :=
  completedUntwistedS (2 * w) / besselSqMellin (2 * w)

/-- Its residue is `243π³r³/(8(4π|ξ₁|)^{-4/3} C̄² L(1,χ₋₃) M(4/3))`. -/
abbrev untwistedThetaResidue : ℂ :=
  untwistedSResidue / (2 * besselSqMellin (4 / 3))

theorem untwistedThetaResidue_ne_zero : untwistedThetaResidue ≠ 0 :=
  div_ne_zero untwistedSResidue_ne_zero
    (mul_ne_zero two_ne_zero besselSqMellin_four_thirds_ne_zero)

private theorem two_mul_punctured :
    Tendsto (fun w : ℂ => 2 * w) (𝓝[≠] (2 / 3 : ℂ)) (𝓝[≠] (4 / 3 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have ht : Tendsto (fun w : ℂ => 2 * w) (𝓝 (2 / 3 : ℂ)) (𝓝 (2 * (2 / 3 : ℂ))) :=
      (continuous_const.mul continuous_id).tendsto _
    rw [show (2 : ℂ) * (2 / 3) = 4 / 3 by norm_num] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    change w ≠ 2 / 3 at hw
    change 2 * w ≠ 4 / 3
    intro he
    apply hw
    linear_combination he / 2

/-- A single nonzero Mellin value excludes local vanishing throughout its half-plane. -/
theorem besselSqMellin_eventually_ne_zero (s : ℂ) (hs : 2 / 3 < s.re) :
    ∀ᶠ t in 𝓝[≠] s, besselSqMellin t ≠ 0 := by
  let U : Set ℂ := {s | 2 / 3 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ besselSqMellin U :=
    fun z hz => (besselSqMellin_differentiableAt z hz).differentiableWithinAt
  have hA := hD.analyticOnNhd hU
  have hc : Convex ℝ U := convex_halfSpace_gt ⟨fun _ _ => rfl, fun c z => by simp⟩ (2 / 3)
  rcases (hA s hs).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · have he := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc.isPreconnected hs hz
    exact False.elim (besselSqMellin_four_thirds_ne_zero (he (show (4 / 3 : ℂ) ∈ U by
      dsimp only [U]; norm_num)))
  · exact hz

theorem continuedUntwistedTheta_eq (w : ℂ) (hw : 2 < w.re) (hu : w.re < 13 / 6)
    (hi : 0 < w.im) (hM : besselSqMellin (2 * w) ≠ 0) :
    continuedUntwistedTheta w = twistedSquarefreeSeries 1 w := by
  have hr : (2 * w).re = 2 * w.re := by simp
  have him : (2 * w).im = 2 * w.im := by simp
  rw [continuedUntwistedTheta, completedUntwistedS_eq (2 * w)
    (by rw [hr]; linarith) (by rw [hr]; linarith) (by rw [him]; linarith)]
  rw [show (2 : ℂ) * w / 2 = w by ring, mul_comm]
  exact mul_div_cancel_right₀ _ hM

/-- The quotient agrees with the series as a meromorphic germ, including at Mellin zeros. -/
theorem continuedUntwistedTheta_eventually_eq (w : ℂ) (hw : 2 < w.re)
    (hu : w.re < 13 / 6) (hi : 0 < w.im) :
    continuedUntwistedTheta =ᶠ[𝓝[≠] w] twistedSquarefreeSeries 1 := by
  have hmap : Tendsto (fun z : ℂ => 2 * z) (𝓝[≠] w) (𝓝[≠] (2 * w)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.mul continuous_id).tendsto w).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z ≠ w at hz
      change 2 * z ≠ 2 * w
      exact fun he => hz (mul_left_cancel₀ two_ne_zero he)
  have hN : ∀ᶠ z : ℂ in 𝓝 w, 2 < z.re ∧ z.re < 13 / 6 ∧ 0 < z.im :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im))).mem_nhds ⟨hw, hu, hi⟩
  have hM := besselSqMellin_eventually_ne_zero (2 * w) (by
    have hr : (2 * w).re = 2 * w.re := by simp
    rw [hr]; linarith)
  filter_upwards [nhdsWithin_le_nhds hN, hmap.eventually hM] with z hz hMz
  exact continuedUntwistedTheta_eq z hz.1 hz.2.1 hz.2.2 hMz

/-- The connected upper strip joining absolute convergence to the pole. -/
def untwistedContinuationDomain : Set ℂ :=
  {w | 2 / 3 < w.re ∧ w.re < 13 / 6 ∧ 0 < w.im}

theorem continuedUntwistedTheta_meromorphic :
    MeromorphicOn continuedUntwistedTheta untwistedContinuationDomain := by
  have hU : IsOpen untwistedContinuationDomain :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im))
  have hΛ : DifferentiableOn ℂ (fun w : ℂ => completedUntwistedS (2 * w))
      untwistedContinuationDomain := by
    intro w hw
    have hr : (2 * w).re = 2 * w.re := by simp
    have hi : (2 * w).im = 2 * w.im := by simp
    exact ((completedUntwistedS_differentiableAt (2 * w)
      (by rw [hr]; linarith only [hw.1]) (by rw [hr]; linarith only [hw.2.1])
      (by rw [hi]; linarith only [hw.2.2])).comp w
        (differentiableAt_id.const_mul 2)).differentiableWithinAt
  have hM : DifferentiableOn ℂ (fun w : ℂ => besselSqMellin (2 * w))
      untwistedContinuationDomain := by
    intro w hw
    have hr : (2 * w).re = 2 * w.re := by simp
    exact ((besselSqMellin_differentiableAt (2 * w) (by rw [hr]; linarith only [hw.1])).comp w
      (differentiableAt_id.const_mul 2)).differentiableWithinAt
  exact (hΛ.analyticOnNhd hU).meromorphicOn.fun_div (hM.analyticOnNhd hU).meromorphicOn

/-- Removing `M` preserves holomorphy on a punctured neighbourhood of the pole. -/
theorem continuedUntwistedTheta_differentiableAt_near :
    ∀ᶠ w in 𝓝[≠] (2 / 3 : ℂ), DifferentiableAt ℂ continuedUntwistedTheta w := by
  have hM : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), besselSqMellin s ≠ 0 :=
    (besselSqMellin_differentiableAt _ (by norm_num)).continuousAt.eventually_ne
      besselSqMellin_four_thirds_ne_zero
  filter_upwards [two_mul_punctured.eventually completedUntwistedS_differentiableAt_near,
    two_mul_punctured.eventually (nhdsWithin_le_nhds hM),
    two_mul_punctured.eventually (nhdsWithin_le_nhds near_four_thirds)] with w hΛ hM hw
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 2 * w) w := differentiableAt_id.const_mul 2
  exact (hΛ.comp w hlin).div
    ((besselSqMellin_differentiableAt _ (by linarith only [hw.1])).comp w hlin) hM

/-- The actual untwisted squarefree theta series has a nonzero simple pole at `w=2/3`. -/
theorem continuedUntwistedTheta_simple_pole :
    Tendsto (fun w => (w - 2 / 3) * continuedUntwistedTheta w)
      (𝓝[≠] (2 / 3 : ℂ)) (𝓝 untwistedThetaResidue) := by
  have hM : Tendsto besselSqMellin (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (besselSqMellin (4 / 3))) :=
    (besselSqMellin_differentiableAt _ (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (completedUntwistedS_simple_pole.div hM besselSqMellin_four_thirds_ne_zero).comp
    two_mul_punctured
  have hscaled := h.div_const 2
  have he : (untwistedSResidue / besselSqMellin (4 / 3)) / 2 = untwistedThetaResidue := by
    dsimp only [untwistedThetaResidue]
    ring
  rw [he] at hscaled
  refine hscaled.congr fun w => ?_
  simp only [Function.comp_apply, Pi.div_apply, continuedUntwistedTheta]
  ring

/-- The untwisted series continues meromorphically to the upper strip and has
a nonzero simple pole at `2/3`; equality of germs also covers zeros of `M`. -/
theorem untwistedSquarefreeSeries_simple_pole :
    ∃ L : ℂ → ℂ,
      MeromorphicOn L untwistedContinuationDomain ∧
      (∀ w : ℂ, 2 < w.re → w.re < 13 / 6 → 0 < w.im →
        L =ᶠ[𝓝[≠] w] twistedSquarefreeSeries 1) ∧
      (∀ᶠ w in 𝓝[≠] (2 / 3 : ℂ), DifferentiableAt ℂ L w) ∧
      Tendsto (fun w => (w - 2 / 3) * L w) (𝓝[≠] (2 / 3 : ℂ))
        (𝓝 untwistedThetaResidue) ∧
      untwistedThetaResidue ≠ 0 :=
  ⟨continuedUntwistedTheta, continuedUntwistedTheta_meromorphic,
    continuedUntwistedTheta_eventually_eq, continuedUntwistedTheta_differentiableAt_near,
    continuedUntwistedTheta_simple_pole, untwistedThetaResidue_ne_zero⟩

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
