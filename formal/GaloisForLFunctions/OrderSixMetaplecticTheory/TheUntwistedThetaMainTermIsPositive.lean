import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicThetaFunctionIsConjugationSymmetric
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUntwistedThetaMainTermIsReal

/-!
# The main term of the untwisted theta series is positive

The Gaussian-smoothed untwisted sum `G(X) = Σ_A ((9/c_A)₃ \overline{G̃(c_A)})² φ(log(N A / X))` over
squarefree ideals has the main term `κ X^{2/3}` with `κ = e^{4/9} R` and
`R = 243π³r³ / (8 (4π|ξ₁|)^{−4/3} C̄² L(1, χ₋₃) M(4/3))`. Every factor is a positive real number:

* `C` is real and nonzero (`rationalSourceThetaScalar_star`), so `C̄² = C² > 0`;
* `r = (2/3) ρ_K / (3 · (9√3/2) · Z₀(2))`, and `Z₀(x) ≥ 1` for real `x > 1`;
* `L(1, χ₋₃) = (3/2) Z̃(4/3)`, where `Z̃(s) = (3/2)(s − 4/3) Z₀(3s/2 − 1)` is positive on the real ray
  `s > 4/3`; its limit at `4/3` is nonnegative and nonzero (`LFunction_chi3D_one_isPosReal`);
* `M(4/3) = ∫₀^∞ t^{1/3} K_{1/3}(t)² dt` is the integral of a positive function.

Hence `κ > 0` (`gaussianSmoothedUntwistedTheta_positive_main_term`): the unit phases
`((9/c)₃ \overline{G̃(c)})²` of the squared normalized cubic Gauss sums have a **positive** mean of exact
order `X^{2/3}` over squarefree moduli.
-/

noncomputable section

open Filter Topology MeasureTheory
open scoped Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  SpectralTheoryOfTheCubicCover FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-- `z` is a positive real number. -/
def IsPosReal (z : ℂ) : Prop := ∃ x : ℝ, 0 < x ∧ z = x

namespace IsPosReal

theorem ofReal {x : ℝ} (hx : 0 < x) : IsPosReal x := ⟨x, hx, rfl⟩

theorem mul {z w : ℂ} (hz : IsPosReal z) (hw : IsPosReal w) : IsPosReal (z * w) := by
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨x * y, mul_pos hx hy, by push_cast; ring⟩

theorem div {z w : ℂ} (hz : IsPosReal z) (hw : IsPosReal w) : IsPosReal (z / w) := by
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := hw
  exact ⟨x / y, div_pos hx hy, by push_cast; ring⟩

theorem pow {z : ℂ} (hz : IsPosReal z) (n : ℕ) : IsPosReal (z ^ n) := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x ^ n, pow_pos hx n, by push_cast; ring⟩

theorem re_pos {z : ℂ} (hz : IsPosReal z) : 0 < z.re := by
  obtain ⟨x, hx, rfl⟩ := hz
  rwa [Complex.ofReal_re]

theorem im_eq_zero {z : ℂ} (hz : IsPosReal z) : z.im = 0 := by
  obtain ⟨x, -, rfl⟩ := hz
  exact Complex.ofReal_im x

end IsPosReal

/-! ### The unramified zeta function on the real ray -/

theorem unramifiedNormWeight_real (x : ℝ) (I : Ideal O) :
    unramifiedNormWeight x I =
      ((if primaryIdealGenerator I = 0 then 0 else (Ideal.absNorm I : ℝ) ^ (-x) : ℝ) : ℂ) := by
  unfold unramifiedNormWeight
  simp only [MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs
  · simp
  · rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]

/-- `Z₀(x) ≥ 1` is a positive real number for real `x > 1`. -/
theorem unramifiedIdealZeta_isPosReal {x : ℝ} (hx : 1 < x) : IsPosReal (unramifiedIdealZeta x) := by
  let g : Ideal O → ℝ := fun I =>
    if primaryIdealGenerator I = 0 then 0 else (Ideal.absNorm I : ℝ) ^ (-x)
  have hg : ∀ I, unramifiedNormWeight x I = (g I : ℂ) := unramifiedNormWeight_real x
  have hnn : ∀ I, 0 ≤ g I := fun I => by
    dsimp only [g]
    split_ifs
    · exact le_rfl
    · positivity
  have hsum : Summable g := by
    refine (unramifiedNormWeight_summable_norm (x : ℂ) (by simpa using hx)).congr fun I => ?_
    rw [hg, Complex.norm_real, Real.norm_of_nonneg (hnn I)]
  have h1 : g 1 = 1 := by
    dsimp only [g]
    rw [primaryIdealGenerator_one, if_neg one_ne_zero, map_one, Nat.cast_one, Real.one_rpow]
  refine ⟨∑' I, g I, lt_of_lt_of_le one_pos (h1 ▸ hsum.le_tsum 1 fun j _ => hnn j), ?_⟩
  unfold unramifiedIdealZeta
  rw [Complex.ofReal_tsum]
  exact tsum_congr hg

theorem constantArithmeticResidue_isPosReal : IsPosReal constantArithmeticResidue := by
  have hZ := unramifiedIdealZeta_isPosReal (x := 2) (by norm_num)
  rw [Complex.ofReal_ofNat] at hZ
  have hρ : IsPosReal unramifiedZetaResidue :=
    (IsPosReal.div ⟨2, by norm_num, by norm_num⟩ ⟨3, by norm_num, by norm_num⟩).mul
      (IsPosReal.ofReal (NumberField.dedekindZeta_residue_pos K))
  exact hρ.div ((IsPosReal.mul ⟨3, by norm_num, by norm_num⟩ (IsPosReal.ofReal (by positivity))).mul hZ)

/-! ### `L(1, χ₋₃) > 0` -/

theorem clearedCubeZeta_isPosReal {s : ℝ} (hs : 4 / 3 < s) : IsPosReal (clearedCubeZeta s) := by
  have h := sub_mul_cubeZeta (s := (s : ℂ)) (by simpa using hs)
  have hz := unramifiedIdealZeta_isPosReal (x := 3 * (s / 2) - 1) (by linarith)
  rw [show ((3 * (s / 2) - 1 : ℝ) : ℂ) = 3 * ((s : ℂ) / 2) - 1 by push_cast; ring] at hz
  have hc : clearedCubeZeta s =
      (3 / 2 : ℂ) * (((s - 4 / 3 : ℝ) : ℂ) * unramifiedIdealZeta (3 * ((s : ℂ) / 2) - 1)) := by
    push_cast
    linear_combination (-(3 / 2 : ℂ)) * h
  rw [hc]
  exact IsPosReal.mul ⟨3 / 2, by norm_num, by norm_num⟩ ((IsPosReal.ofReal (by linarith)).mul hz)

/-- **`L(1, χ₋₃)` is a positive real number.** -/
theorem LFunction_chi3D_one_isPosReal : IsPosReal (DirichletCharacter.LFunction chi3D 1) := by
  have hS : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have hcont : Continuous fun s : ℝ => clearedCubeZeta s :=
    clearedCubeZeta_differentiable.continuous.comp Complex.continuous_ofReal
  have ht : Tendsto (fun s : ℝ => clearedCubeZeta s) (𝓝[>] (4 / 3 : ℝ)) (𝓝 (clearedCubeZeta (4 / 3))) := by
    have h := (hcont.tendsto (4 / 3)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (4 / 3 : ℝ)))
    simpa using h
  have hmem : clearedCubeZeta (4 / 3) ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    hS.mem_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => by
      obtain ⟨x, hx, he⟩ := clearedCubeZeta_isPosReal hs
      rw [he]
      exact ⟨Complex.ofReal_im x, by rw [Complex.ofReal_re]; exact hx.le⟩)
  have hpos : 0 < (clearedCubeZeta (4 / 3)).re := by
    rcases hmem.2.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext (by simp [← h]) (by simp [hmem.1])) clearedCubeZeta_four_thirds_ne_zero
  refine ⟨(3 / 2) * (clearedCubeZeta (4 / 3)).re, by positivity, ?_⟩
  have hL : DirichletCharacter.LFunction chi3D 1 = (3 / 2) * clearedCubeZeta (4 / 3) := by
    rw [clearedCubeZeta_four_thirds]
    ring
  rw [hL]
  conv_lhs => rw [← Complex.re_add_im (clearedCubeZeta (4 / 3)), hmem.1]
  push_cast
  ring

/-! ### `M(4/3) > 0` -/

theorem besselSqMellin_four_thirds_isPosReal : IsPosReal (besselSqMellin (4 / 3)) := by
  obtain ⟨c, hc, hK⟩ := schlafliBesselK_one_third_exp_lower
  have hconv := besselSqMellin_convergent (4 / 3) (by norm_num)
  have hpt : ∀ t : ℝ, 0 < t → ((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re =
      t ^ ((1 : ℝ) / 3) * (schlafliBesselK (1 / 3) t).re ^ 2 := by
    intro t ht
    have hK : schlafliBesselK (1 / 3) t = ((schlafliBesselK (1 / 3) t).re : ℂ) := by
      rw [schlafliBesselK_one_third_ofReal t ht, Complex.ofReal_re]
    have hc : (t : ℂ) ^ ((4 / 3 : ℂ) - 1) = ((t ^ ((1 : ℝ) / 3) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]
      norm_num
    rw [besselSq, hK, hc, smul_eq_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.ofReal_re]
  have hpos : ∀ t : ℝ, 0 < t → 0 < t ^ ((1 : ℝ) / 3) * (schlafliBesselK (1 / 3) t).re ^ 2 := by
    intro t ht
    have h1 := hK t ht
    have h2 : 0 < c * Real.exp (-9 * t / 4) := by positivity
    exact mul_pos (Real.rpow_pos_of_pos ht _) (pow_pos (h2.trans_le h1) 2)
  have hre : (∫ t in Set.Ioi (0 : ℝ), (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re)) =
      (besselSqMellin (4 / 3)).re := by
    have h1 := integral_re hconv
    simp only [RCLike.re_to_complex] at h1
    exact h1
  have hI : IntegrableOn (fun t : ℝ => (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re)) (Set.Ioi 0) := hconv.re
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun t : ℝ => (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      simp only [Pi.zero_apply]
      rw [hpt t ht]
      exact (hpos t ht).le
  have hsupp : Function.support (fun t : ℝ => (((t : ℂ) ^ ((4 / 3 : ℂ) - 1) • besselSq t).re)) ∩
      Set.Ioi 0 = Set.Ioi 0 := by
    refine Set.inter_eq_right.mpr fun t ht => ?_
    rw [Function.mem_support, hpt t ht]
    exact (hpos t ht).ne'
  have hlt := (setIntegral_pos_iff_support_of_nonneg_ae hnn hI).mpr (by
    rw [hsupp, Real.volume_Ioi]
    exact ENNReal.zero_lt_top)
  have hM : (starRingEnd ℂ) (besselSqMellin (4 / 3)) = besselSqMellin (4 / 3) := star_besselSqMellin_four_thirds
  exact ⟨(besselSqMellin (4 / 3)).re, hre ▸ hlt, (Complex.conj_eq_iff_re.mp hM).symm⟩

/-! ### The residue and the main term -/

theorem unitFrequencyWeight_isPosReal : IsPosReal (unitFrequencyWeight (4 / 3)) := by
  have hb : 0 < 4 * Real.pi * ‖cuspFrequency 1‖ := by
    have := norm_pos_iff.mpr (cuspFrequency_ne_zero 1 one_ne_zero)
    positivity
  refine ⟨(4 * Real.pi * ‖cuspFrequency 1‖) ^ (-(4 / 3) : ℝ), Real.rpow_pos_of_pos hb _, ?_⟩
  unfold unitFrequencyWeight
  rw [Complex.ofReal_cpow hb.le]
  congr 1
  push_cast
  ring

theorem star_sq_rationalSourceThetaScalar_isPosReal : IsPosReal (star rationalSourceThetaScalar ^ 2) := by
  have hC : (starRingEnd ℂ) rationalSourceThetaScalar = rationalSourceThetaScalar := rationalSourceThetaScalar_star
  have hre := (Complex.conj_eq_iff_re.mp hC).symm
  have hne : rationalSourceThetaScalar.re ≠ 0 := fun h => rationalSourceThetaScalar_ne_zero (by
    rw [hre, h, Complex.ofReal_zero])
  refine ⟨rationalSourceThetaScalar.re ^ 2, by positivity, ?_⟩
  rw [rationalSourceThetaScalar_star]
  nth_rw 1 [hre]
  push_cast
  ring

/-- **The residue of `S₁` at `2/3` is a positive real number.** -/
theorem untwistedThetaResidue_isPosReal : IsPosReal untwistedThetaResidue := by
  change IsPosReal (243 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3 /
    (4 * unitFrequencyWeight (4 / 3) * star rationalSourceThetaScalar ^ 2 * DirichletCharacter.LFunction chi3D 1) /
      (2 * besselSqMellin (4 / 3)))
  exact (((IsPosReal.mul ⟨243, by norm_num, by norm_num⟩ ((IsPosReal.ofReal Real.pi_pos).pow 3)).mul
    (constantArithmeticResidue_isPosReal.pow 3)).div
      (((IsPosReal.mul ⟨4, by norm_num, by norm_num⟩ unitFrequencyWeight_isPosReal).mul
        star_sq_rationalSourceThetaScalar_isPosReal).mul LFunction_chi3D_one_isPosReal)).div
    (IsPosReal.mul ⟨2, by norm_num, by norm_num⟩ besselSqMellin_four_thirds_isPosReal)

theorem thetaGaussianMainCoefficient_isPosReal : IsPosReal thetaGaussianMainCoefficient := by
  have he : Complex.exp ((2 / 3 : ℂ) ^ 2) = ((Real.exp (4 / 9) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    norm_num
  rw [thetaGaussianMainCoefficient, he]
  exact (IsPosReal.ofReal (Real.exp_pos _)).mul untwistedThetaResidue_isPosReal

/-- **Positive main term.** The smoothed untwisted theta sum is `κ X^{2/3} + O(X^{13/20})` with `κ > 0`. -/
theorem gaussianSmoothedUntwistedTheta_positive_main_term :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedUntwistedTheta X - ((κ * X ^ (2 / 3 : ℝ) : ℝ) : ℂ)‖ ≤ C * X ^ (13 / 20 : ℝ) := by
  obtain ⟨κ, hκ, he⟩ := thetaGaussianMainCoefficient_isPosReal
  obtain ⟨C, hC, hbound⟩ := gaussianSmoothedUntwistedTheta_main_term (13 / 20) (by norm_num) (by norm_num)
  refine ⟨κ, hκ, C, hC, fun X hX => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hpow : (X : ℂ) ^ (2 / 3 : ℂ) = ((X ^ (2 / 3 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hX0.le]
    norm_num
  have h := hbound X hX
  rw [he, hpow] at h
  convert h using 3
  push_cast
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
