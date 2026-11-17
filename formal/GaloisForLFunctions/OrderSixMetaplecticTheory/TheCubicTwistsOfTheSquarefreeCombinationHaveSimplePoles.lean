import GaloisForLFunctions.OrderSixMetaplecticTheory.TheTwistedThetaSquareFactorsThroughATwistedCubeFactor
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConjugateCubicTwistAtEveryOddPrimaryPrimeHasADoublePole
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheDilateCorrelationAtEveryPrimaryPrimeHasADoublePole
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTwistedSquarefreeCombinationHasASimplePole

/-!
# The cubic twists of the squarefree combination have simple poles

For a cubic character `φ` of `O/q` (`φ³ = 1`) the cube factor of `L_φ` is `Z₀` without its Euler factor at `q`:
`Z_{φ³}(z) = (1 − N(q)^{−z}) Z₀(z)` (`cubeZetaW_cubic`). So

`L_φ(s) = C̄² (1 − N(q)^{1−3s/2}) Z₀(3s/2 − 1) Q_φ(s)`,
`Q_φ(s) = Σ_{u,m} φ(uλ^m)(T(uλ^m)/T(1))²(4π|ξ_{uλ^m}|)^{−s} S^φ_{uλ^m}(s/2)`,

and a double pole of `M·L_φ` at `4/3` is a simple pole of `M·Q_φ`
(`twistCombination_simple_pole_of_double_pole`). Both cubic twists at an odd primary prime have the
double pole, so the squarefree Gauss-sum series twisted by `(·/q)₃` or by its conjugate keep a nonzero
residue at `w = 2/3` (`cubicTwistCombination_simple_pole`, `conjugateTwistCombination_simple_pole`):
neither cubic twist at a prime kills the main term of the family.
-/

noncomputable section

open Filter Topology UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### The cube factor of a cubic twist -/

theorem mulChar_cube_apply (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = 1) (x : P.Res) :
    φ x ^ 3 = if x = 0 then 0 else 1 := by
  split_ifs with hx
  · rw [hx, MulChar.map_zero]
    norm_num
  · rw [← MulChar.pow_apply' φ (by norm_num), hφ, MulChar.one_apply (Ne.isUnit hx)]

theorem primeIdeal_ne_zero : (Ideal.span {P.p} : Ideal O) ≠ 0 :=
  Ideal.span_singleton_eq_bot.not.mpr P.ne_zero

theorem dvd_gen_iff (B : Ideal O) (hB : primaryIdealGenerator B ≠ 0) :
    P.p ∣ primaryIdealGenerator B ↔ Ideal.span {P.p} ∣ B := by
  conv_rhs => rw [← (primaryIdealGenerator_spec B hB).1]
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton]

/-- **The cube factor of a cubic twist** is `Z₀` without its Euler factor at `q`. -/
theorem cubeZetaW_cubic (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = 1) (z : ℂ) (hz : 1 < z.re) :
    P.cubeZetaW φ z = (1 - unramifiedNormWeight z (Ideal.span {P.p})) * unramifiedIdealZeta z := by
  set Q : Ideal O := Ideal.span {P.p} with hQ
  set f : Ideal O → ℂ := fun B => if Q ∣ B then unramifiedNormWeight z B else 0 with hf
  have hs := unramifiedNormWeight_summable_norm z hz
  have hfs : Summable f := Summable.of_norm_bounded hs (fun B => by
    simp only [hf]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _)
  have hterm : ∀ B : Ideal O, unramifiedNormWeight z B * φ (P.res (primaryIdealGenerator B)) ^ 3 =
      unramifiedNormWeight z B - f B := by
    intro B
    by_cases hB : primaryIdealGenerator B = 0
    · simp only [hf, unramifiedNormWeight_of_bad z B hB, zero_mul, ite_self, sub_zero]
    · rw [P.mulChar_cube_apply φ hφ, P.res_eq_zero_iff, P.dvd_gen_iff B hB]
      simp only [hf]
      split_ifs <;> ring
  have hinj : Function.Injective (fun B' : Ideal O => Q * B') := fun a b h =>
    mul_left_cancel₀ P.primeIdeal_ne_zero h
  have hsupp : Function.support f ⊆ Set.range (fun B' : Ideal O => Q * B') := by
    intro B hB
    by_cases hd : Q ∣ B
    · obtain ⟨B', rfl⟩ := hd
      exact ⟨B', rfl⟩
    · exact absurd (by simp only [hf, if_neg hd]) hB
  have hQB : ∑' B : Ideal O, f B = unramifiedNormWeight z Q * unramifiedIdealZeta z := by
    rw [← hinj.tsum_eq hsupp, unramifiedIdealZeta, ← tsum_mul_left]
    refine tsum_congr fun B' => ?_
    simp only [hf, if_pos (dvd_mul_right Q B'), map_mul]
  rw [cubeZetaW, tsum_congr hterm, hs.of_norm.tsum_sub hfs, hQB, unramifiedIdealZeta]
  ring

/-! ### The Euler factor at `q` -/

/-- `E_q(s) = 1 − N(q)^{1 − 3s/2}`. -/
def eulerFactorQ (s : ℂ) : ℂ := 1 - unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p})

theorem primeIdeal_gen : primaryIdealGenerator (Ideal.span {P.p}) = P.p :=
  primaryIdealGenerator_span P.p P.ne_zero P.primary

theorem one_lt_absNorm : 1 < Ideal.absNorm (Ideal.span {P.p} : Ideal O) := by
  have h0 : Ideal.absNorm (Ideal.span {P.p} : Ideal O) ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr P.primeIdeal_ne_zero
  have h1 : Ideal.absNorm (Ideal.span {P.p} : Ideal O) ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff, Ideal.span_singleton_eq_top]
    exact P.prime.not_unit
  omega

theorem normWeight_primeIdeal (z : ℂ) :
    unramifiedNormWeight z (Ideal.span {P.p}) = (Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℂ) ^ (-z) := by
  rw [unramifiedNormWeight_of_good _ _ (by rw [P.primeIdeal_gen]; exact P.ne_zero)]

theorem eulerFactorQ_ne_zero {s : ℂ} (hs : 2 / 3 < s.re) : P.eulerFactorQ s ≠ 0 := by
  have hN : (1 : ℝ) < Ideal.absNorm (Ideal.span {P.p} : Ideal O) := by exact_mod_cast P.one_lt_absNorm
  have hlt : ‖unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p})‖ < 1 := by
    rw [P.normWeight_primeIdeal, Complex.norm_natCast_cpow_of_pos (by have := P.one_lt_absNorm; omega)]
    apply Real.rpow_lt_one_of_one_lt_of_neg hN
    rw [Complex.neg_re, cubeZeta_re]
    linarith
  intro h
  rw [eulerFactorQ, sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem eulerFactorQ_differentiable : Differentiable ℂ P.eulerFactorQ := by
  have hlin : Differentiable ℂ (fun s : ℂ => 3 * (s / 2) - 1) :=
    ((differentiable_id.div_const 2).const_mul 3).sub_const 1
  intro s
  exact (differentiableAt_const 1).sub
    (((unramifiedNormWeight_differentiable (Ideal.span {P.p})) _).comp s (hlin s))

theorem eulerFactorQ_four_thirds :
    P.eulerFactorQ (4 / 3) = 1 - ((Ideal.absNorm (Ideal.span {P.p} : Ideal O) : ℂ))⁻¹ := by
  rw [eulerFactorQ, show (3 : ℂ) * (4 / 3 / 2) - 1 = 1 by norm_num, P.normWeight_primeIdeal,
    Complex.cpow_neg_one]

/-! ### Double poles of `L_φ` are simple poles of `Q_φ` -/

/-- `Q_φ(s) = Σ_{u,m} φ(uλ^m)(T(uλ^m)/T(1))²(4π|ξ_{uλ^m}|)^{−s} S^φ_{uλ^m}(s/2)`. -/
def twistCombination (φ : MulChar P.Res ℂ) (s : ℂ) : ℂ :=
  ∑' u : Oˣ, ∑' m : ℕ, φ (P.res ((u : O) * lambda ^ m)) *
    (rationalSourceResidualFourierCoefficient ((u : O) * lambda ^ m) /
        rationalSourceResidualFourierCoefficient 1) ^ 2 *
      ((4 * Real.pi * ‖cuspFrequency ((u : O) * lambda ^ m)‖ : ℝ) : ℂ) ^ (-s) *
        P.twistedSquarefreeSeriesW φ ((u : O) * lambda ^ m) (s / 2)

/-- `(s − 4/3) L_φ(s) = C̄² (2/3) Z̃(s) E_q(s) Q_φ(s)` for `Re s > 4`. -/
theorem sub_mul_twistDirichlet (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = 1) (s : ℂ) (hs : 4 < s.re) :
    (s - 4 / 3) * P.twistDirichlet φ s =
      star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s * P.eulerFactorQ s *
        P.twistCombination φ s := by
  have hz : 1 < (3 * (s / 2) - 1).re := by rw [cubeZeta_re]; linarith
  have hZ := sub_mul_cubeZeta (s := s) (by linarith)
  have hL : P.twistDirichlet φ s = star rationalSourceThetaScalar ^ 2 * P.cubeZetaW φ (3 * (s / 2) - 1) *
      P.twistCombination φ s := P.twistDirichlet_eq_zeta_mul φ s hs
  rw [hL, P.cubeZetaW_cubic φ hφ _ hz]
  unfold eulerFactorQ
  linear_combination (star rationalSourceThetaScalar ^ 2 *
    (1 - unramifiedNormWeight (3 * (s / 2) - 1) (Ideal.span {P.p})) * P.twistCombination φ s) * hZ

/-- The denominator `C̄² (2/3) Z̃(s) E_q(s)`. -/
def combinationDenom (s : ℂ) : ℂ :=
  star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s * P.eulerFactorQ s

theorem combinationDenom_ne_zero {s : ℂ} (hs : 4 / 3 < s.re) : P.combinationDenom s ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
    (clearedCubeZeta_ne_zero hs)) (P.eulerFactorQ_ne_zero (by linarith))

theorem combinationDenom_four_thirds_ne_zero : P.combinationDenom (4 / 3) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (by norm_num))
    clearedCubeZeta_four_thirds_ne_zero) (P.eulerFactorQ_ne_zero (by norm_num))

theorem combinationDenom_differentiable : Differentiable ℂ P.combinationDenom := fun s =>
  (((differentiableAt_const _).mul (differentiableAt_const _)).mul (clearedCubeZeta_differentiable s)).mul
    (P.eulerFactorQ_differentiable s)

/-- **A double pole of `M·L_φ` is a simple pole of `M·Q_φ`.** For a cubic `φ`, if `M·L_φ`
continues to `{1 < Re s < 13/3, Im s > 0}` and a punctured neighbourhood of `4/3` with
`(s − 4/3)²M(s)L_φ(s) → c`, then `M·Q_φ` continues to `{4/3 < Re s < 13/3, Im s > 0}` and the
punctured neighbourhood with `(s − 4/3)M(s)Q_φ(s) → c/(C̄²(2/3)Z̃(4/3)E_q(4/3))`. -/
theorem twistCombination_simple_pole_of_double_pole (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = 1) (c : ℂ)
    (Λ : ℂ → ℂ)
    (hΛe : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * P.twistDirichlet φ s)
    (hΛd : ∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s)
    (hΛn : ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s)
    (hΛl : Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 c)) :
    ∃ ΛQ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → ΛQ s = besselSqMellin s * P.twistCombination φ s) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ ΛQ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ ΛQ s) ∧
      Tendsto (fun s => (s - 4 / 3) * ΛQ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (c / P.combinationDenom (4 / 3))) := by
  have hden_ev : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), P.combinationDenom s ≠ 0 :=
    (P.combinationDenom_differentiable _).continuousAt.eventually_ne P.combinationDenom_four_thirds_ne_zero
  refine ⟨fun s => (s - 4 / 3) * Λ s / P.combinationDenom s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_,
    ?_, ?_⟩
  · have hd := P.combinationDenom_ne_zero (s := s) (by linarith)
    have hL := P.sub_mul_twistDirichlet φ hφ s hs4
    show (s - 4 / 3) * Λ s / P.combinationDenom s = _
    rw [hΛe s hs4 hs hi, div_eq_iff hd]
    unfold combinationDenom
    linear_combination besselSqMellin s * hL
  · exact ((differentiableAt_id.sub_const _).mul (hΛd s (by linarith) hs hi)).div
      (P.combinationDenom_differentiable s) (P.combinationDenom_ne_zero hs1)
  · filter_upwards [hΛn, nhdsWithin_le_nhds hden_ev] with s h1 h2
    exact ((differentiableAt_id.sub_const _).mul h1).div (P.combinationDenom_differentiable s) h2
  · have hD : Tendsto P.combinationDenom (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.combinationDenom (4 / 3))) :=
      ((P.combinationDenom_differentiable _).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    refine (hΛl.div hD P.combinationDenom_four_thirds_ne_zero).congr fun s => ?_
    simp only [Pi.div_apply]
    ring

/-! ### The two cubic twists at an odd primary prime -/

theorem twistDirichlet_chi (s : ℂ) : P.twistDirichlet P.chi s = besselDirichlet P.twistCoeff s := by
  unfold twistDirichlet
  congr 1
  funext h
  rw [twistCoeff, P.chi_res]

theorem twistDirichlet_chi_inv (s : ℂ) :
    P.twistDirichlet P.chi⁻¹ s = besselDirichlet P.conjTwistCoeff s := by
  unfold twistDirichlet
  congr 1
  funext h
  rw [conjTwistCoeff, MulChar.inv_apply_eq_inv']

theorem chi_pow_three : P.chi ^ 3 = 1 := primeCubicMulChar_cube P.p P.prime P.primary

theorem chi_inv_pow_three : P.chi⁻¹ ^ 3 = 1 := by rw [inv_pow, P.chi_pow_three, inv_one]

/-- **The cubic twist of the squarefree combination has a simple pole.** For every primary prime `q`,
`M·Q_{χ_q}` continues to `{4/3 < Re s < 13/3, Im s > 0}` and a punctured neighbourhood of `4/3`, and
`(s − 4/3)M(s)Q_{χ_q}(s)` tends to a nonzero limit. -/
theorem cubicTwistCombination_simple_pole :
    ∃ (ΛQ : ℂ → ℂ) (R : ℂ),
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → ΛQ s = besselSqMellin s * P.twistCombination P.chi s) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ ΛQ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ ΛQ s) ∧
      Tendsto (fun s => (s - 4 / 3) * ΛQ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R) ∧ R ≠ 0 := by
  obtain ⟨Λ, hΛe, hΛd, hΛn, hΛl, hne⟩ := P.cubicTwistAtPrime_double_pole
  obtain ⟨ΛQ, h1, h2, h3, h4⟩ := P.twistCombination_simple_pole_of_double_pole P.chi P.chi_pow_three _ Λ
    (fun s hs4 hs hi => by rw [hΛe s hs4 hs hi, P.twistDirichlet_chi]) hΛd hΛn hΛl
  exact ⟨ΛQ, _, h1, h2, h3, h4, div_ne_zero hne P.combinationDenom_four_thirds_ne_zero⟩

/-- **The conjugate cubic twist of the squarefree combination has a simple pole.** For every odd primary
prime `q`, `M·Q_{χ̄_q}` continues to `{4/3 < Re s < 13/3, Im s > 0}` and a punctured neighbourhood of
`4/3`, and `(s − 4/3)M(s)Q_{χ̄_q}(s)` tends to a nonzero limit. -/
theorem conjugateTwistCombination_simple_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ (ΛQ : ℂ → ℂ) (R : ℂ),
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → ΛQ s = besselSqMellin s * P.twistCombination P.chi⁻¹ s) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ ΛQ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ ΛQ s) ∧
      Tendsto (fun s => (s - 4 / 3) * ΛQ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R) ∧ R ≠ 0 := by
  obtain ⟨Λ, hΛe, hΛd, hΛn, hΛl, hne⟩ := P.conjugateCubicTwist_double_pole h2
  obtain ⟨ΛQ, h1, h2', h3, h4⟩ := P.twistCombination_simple_pole_of_double_pole P.chi⁻¹ P.chi_inv_pow_three _ Λ
    (fun s hs4 hs hi => by rw [hΛe s hs4 hs hi, P.twistDirichlet_chi_inv]) hΛd hΛn hΛl
  exact ⟨ΛQ, _, h1, h2', h3, h4, div_ne_zero hne P.combinationDenom_four_thirds_ne_zero⟩

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
