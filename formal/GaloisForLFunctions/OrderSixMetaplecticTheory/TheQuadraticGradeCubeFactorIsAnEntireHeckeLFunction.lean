import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicTwistsOfTheSquarefreeCombinationHaveSimplePoles
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.HeckeLogarithmicDerivative
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.RayFamiliesAndPrimeRows

/-!
# The cube factor of the quadratic grade is an entire Hecke L-function

Let `q` be an odd primary prime with `λ_q(−1) = 1` (`N(q) ≡ 1 mod 4`; otherwise the quadratic grade
vanishes, `quadraticGrade_vanish_of_card`). Every unit of `O` is then a square up to `±1`, so `λ_q` is
trivial on the units and `B ↦ λ_q(gen B)` on unramified ideals is the Hecke character `λ̃` of modulus `(q)(λ)`
(`quadHecke`). For every `φ` with `φ³ = λ_q` (the sextic grade `λ, χλ, χ̄λ`) the cube factor of `L_φ` is
`Z_{φ³} = L(·, λ̃)` (`cubeZetaW_eq_LFunction`). It is entire and nonzero on `Re z ≥ 1`, so

`L_φ(s) = C̄² L(3s/2 − 1, λ̃) Q_φ(s)`

with a factor that is holomorphic and nonzero at `s = 4/3`. Hence `M·L_φ` and `M·Q_φ` have the same pole order at `4/3`
with leading coefficients in ratio `C̄² L(1, λ̃)` (`quadraticGrade_pole_transfer`,
`quadraticGrade_pole_transfer_symm`). In the cubic grade the cube factor carries the pole of `Z₀`
(`twistCombination_simple_pole_of_double_pole`); in the quadratic grade it carries none.
-/

noncomputable section

open Filter Topology UniqueFactorizationMonoid
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### `λ_q` on the units -/

theorem lam_cube (x : P.Res) : P.lam x ^ 3 = P.lam x := by
  by_cases hx : x = 0
  · rw [hx, MulChar.map_zero]
    norm_num
  · rw [pow_succ, P.lam_sq x hx, one_mul]

/-- `λ_q(u) = 1` for every unit when `λ_q(−1) = 1`: `u³ = ±1` and `λ_q(u)³ = λ_q(u)`. -/
theorem lam_unit (hlam : P.lam (-1) = 1) (u : Oˣ) : P.lam (P.res (u : O)) = 1 := by
  have h6 : ((u : O) ^ 3) ^ 2 = 1 := by
    rw [← pow_mul]
    exact CanonicalRowCompletion.unit_pow_six u
  have h3 : (u : O) ^ 3 = 1 ∨ (u : O) ^ 3 = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact h6)
  rw [← P.lam_cube, ← map_pow, ← map_pow]
  rcases h3 with h | h
  · rw [h, map_one, MulChar.map_one]
  · rw [h, map_neg, map_one, hlam]

/-! ### The Hecke character `λ̃` -/

theorem lambdaIdeal_prime : Prime (Ideal.span {lambda} : Ideal O) :=
  Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr residue_lambda_prime.ne_zero)
    ((Ideal.span_singleton_prime residue_lambda_prime.ne_zero).mpr residue_lambda_prime)

/-- `λ_q` as a Hecke character of modulus `(q)`. -/
def quadHeckeBase (hlam : P.lam (-1) = 1) : HeckeFamily.Character :=
  HeckeFamily.Character.ofResidue (Ideal.span {P.p}) P.primeIdeal_ne_zero P.lam (P.lam_unit hlam)

/-- **The Hecke character `λ̃`**: `λ_q` with the ramified prime `(λ)` removed. -/
def quadHecke (hlam : P.lam (-1) = 1) : HeckeFamily.Character :=
  (P.quadHeckeBase hlam).excludePrimes {Ideal.span {lambda}} (by
    intro Q hQ
    rw [Finset.mem_singleton.mp hQ]
    exact lambdaIdeal_prime)

theorem isCoprime_lambda_gen (I : Ideal O) (hI : primaryIdealGenerator I ≠ 0) :
    IsCoprime (primaryIdealGenerator I) lambda := by
  have h := ramified_isCoprime_gen 1 1 I hI
  simp only [Units.val_one, one_mul, pow_one] at h
  exact h.symm

theorem gen_ne_zero_of_isCoprime (I : Ideal O)
    (hc : IsCoprime I (Ideal.span {lambda})) : primaryIdealGenerator I ≠ 0 := by
  have hspan : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
    Ideal.span_singleton_generator I
  rw [← hspan, primaryIdealGenerator_span_ne_zero_iff]
  intro hd
  rw [← hspan, Ideal.isCoprime_span_singleton_iff] at hc
  exact (residue_lambda_prime.irreducible.coprime_iff_not_dvd.mp hc.symm) hd

/-- The coefficients of `λ̃`: `λ_q(gen I)` on unramified ideals, `0` otherwise. -/
theorem idealCoeff_quadHecke (hlam : P.lam (-1) = 1) (I : Ideal O) :
    HeckeFamily.idealCoeff (P.quadHecke hlam) I =
      if primaryIdealGenerator I = 0 then 0 else P.lam (P.res (primaryIdealGenerator I)) := by
  rw [quadHecke, HeckeFamily.idealCoeff_excludePrimes]
  simp only [Finset.mem_singleton, forall_eq]
  by_cases hI : primaryIdealGenerator I = 0
  · rw [if_pos hI]
    by_cases h0 : I = 0
    · simp only [h0, map_zero, ite_self]
    · rw [if_neg (fun hc => (gen_ne_zero_of_isCoprime I hc) hI)]
  · have hc : IsCoprime I (Ideal.span {lambda}) := by
      rw [← (primaryIdealGenerator_spec I hI).1, Ideal.isCoprime_span_singleton_iff]
      exact isCoprime_lambda_gen I hI
    rw [if_pos hc, if_neg hI]
    have h := HeckeFamily.idealCoeff_span (P.quadHeckeBase hlam) hI
    rw [(primaryIdealGenerator_spec I hI).1] at h
    rw [h]
    rfl

/-- `λ̃` is not principal: a residue `x'` with `λ_q(x') = −1`, coprime to `3q`, sees it. -/
theorem quadHecke_residue_ne_one (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) :
    (P.quadHecke hlam).residue ≠ 1 := by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (P.ringChar_ne_two h2)
  obtain ⟨k, hk⟩ := P.primary
  set x := P.lift a with hx
  set x' := P.p - x * lambda ^ 2 * k with hx'
  have hres : P.res x' = a := by
    have hk' : P.res (lambda ^ 2 * k) = -1 := by
      have := congrArg P.res hk
      rw [map_sub, P.res_p, map_one, zero_sub] at this
      rw [← this]
    rw [hx', map_sub, P.res_p, mul_assoc, map_mul, hk', hx, res_lift]
    ring
  have hlx : P.lam (P.res x') = -1 := by
    rw [hres]
    simp only [lam, MulChar.ringHomComp_apply, ha]
    norm_num
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, quadraticChar_zero] at ha
    norm_num at ha
  have hpx : IsCoprime x P.p := by
    have hnd : ¬ P.p ∣ x := by
      intro hd
      exact ha0 (by rw [← P.res_lift a, ← hx]; exact (P.res_eq_zero_iff x).mpr hd)
    exact (P.prime.irreducible.coprime_iff_not_dvd.mpr hnd).symm
  obtain ⟨s₁, t₁, hst⟩ := hpx
  have hcp : IsCoprime x' P.p :=
    ⟨s₁, t₁ - s₁ * (1 - x), by rw [hx']; linear_combination hst + s₁ * x * hk⟩
  have hcl : IsCoprime x' lambda :=
    ⟨1, -(lambda * k * (1 - x)), by rw [hx']; linear_combination hk⟩
  have hunit : IsUnit (Ideal.Quotient.mk (P.quadHecke hlam).modulus x') := by
    rw [IdealCharacter.isUnit_mk_iff_isCoprime]
    change IsCoprime (Ideal.span {x'}) (Ideal.span {P.p} * ∏ Q ∈ {Ideal.span {lambda}}, Q)
    rw [Finset.prod_singleton]
    exact IsCoprime.mul_right ((Ideal.isCoprime_span_singleton_iff _ _).mpr hcp)
      ((Ideal.isCoprime_span_singleton_iff _ _).mpr hcl)
  intro h1
  have he := HeckeFamily.elementCoeff_refineModulus (P.quadHeckeBase hlam) _
    (P.quadHecke hlam).modulus_ne_bot Ideal.mul_le_right x'
  change (P.quadHecke hlam).residue (Ideal.Quotient.mk (P.quadHecke hlam).modulus x') = _ at he
  rw [h1, MulChar.one_apply hunit, if_pos hunit] at he
  have : (1 : ℂ) = -1 := he.trans hlx
  norm_num at this

/-! ### The cube factor -/

/-- **The cube factor of the quadratic grade is `L(·, λ̃)`.** -/
theorem cubeZetaW_eq_LFunction (hlam : P.lam (-1) = 1) (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = P.lam)
    (z : ℂ) (hz : 1 < z.re) : P.cubeZetaW φ z = HeckeFamily.LFunction (P.quadHecke hlam) z := by
  rw [HeckeFamily.LFunction_eq_ideal_tsum _ hz, cubeZetaW]
  refine tsum_congr fun I => ?_
  rw [HeckeFamily.idealTerm, P.idealCoeff_quadHecke hlam]
  by_cases hI : primaryIdealGenerator I = 0
  · rw [unramifiedNormWeight_of_bad z I hI, if_pos hI, zero_mul, zero_div]
  · rw [if_neg hI, unramifiedNormWeight_of_good z I hI, ← MulChar.pow_apply' φ (by norm_num), hφ,
      Complex.cpow_neg, div_eq_mul_inv, mul_comm]

theorem chi_mul_lam_pow_three : (P.chi * P.lam) ^ 3 = P.lam := by
  rw [mul_pow, P.chi_pow_three, one_mul, pow_succ, P.lam_sq_eq_one, one_mul]

theorem chi_inv_mul_lam_pow_three : (P.chi⁻¹ * P.lam) ^ 3 = P.lam := by
  rw [mul_pow, P.chi_inv_pow_three, one_mul, pow_succ, P.lam_sq_eq_one, one_mul]

theorem lam_pow_three : P.lam ^ 3 = P.lam := by
  rw [pow_succ, P.lam_sq_eq_one, one_mul]

/-- `Z(s) = L(3s/2 − 1, λ̃)`. -/
def quadCubeFactor (hlam : P.lam (-1) = 1) (s : ℂ) : ℂ :=
  HeckeFamily.LFunction (P.quadHecke hlam) (3 * (s / 2) - 1)

theorem quadCubeFactor_differentiable (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) :
    Differentiable ℂ (P.quadCubeFactor hlam) := by
  have hlin : Differentiable ℂ (fun s : ℂ => 3 * (s / 2) - 1) :=
    ((differentiable_id.div_const 2).const_mul 3).sub_const 1
  exact (HeckeFamily.LFunction_entire_nonprincipal _ (P.quadHecke_residue_ne_one h2 hlam)).comp hlin

theorem quadCubeFactor_ne_zero (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) {s : ℂ}
    (hs : 4 / 3 ≤ s.re) : P.quadCubeFactor hlam s ≠ 0 :=
  HeckeFamily.LFunction_ne_zero_of_one_le_re _ (by rw [cubeZeta_re]; linarith)
    (Or.inr (P.quadHecke_residue_ne_one h2 hlam))

/-- **The grade factorization in the quadratic grade.** For `Re s > 4` and `φ³ = λ_q`,
`L_φ(s) = C̄² L(3s/2 − 1, λ̃) Q_φ(s)`. -/
theorem twistDirichlet_eq_quadCubeFactor (hlam : P.lam (-1) = 1) (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = P.lam)
    (s : ℂ) (hs : 4 < s.re) :
    P.twistDirichlet φ s = star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s *
      P.twistCombination φ s := by
  have hz : 1 < (3 * (s / 2) - 1).re := by rw [cubeZeta_re]; linarith
  have hL : P.twistDirichlet φ s = star rationalSourceThetaScalar ^ 2 * P.cubeZetaW φ (3 * (s / 2) - 1) *
      P.twistCombination φ s := P.twistDirichlet_eq_zeta_mul φ s hs
  rw [hL, P.cubeZetaW_eq_LFunction hlam φ hφ _ hz, quadCubeFactor]

/-! ### Pole orders agree -/

theorem quadDenom_ne_zero (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) {s : ℂ} (hs : 4 / 3 ≤ s.re) :
    star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 scalar_star_ne_zero) (P.quadCubeFactor_ne_zero h2 hlam hs)

theorem quadDenom_eventually_ne (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) :
    ∀ᶠ s in 𝓝 (4 / 3 : ℂ), star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s ≠ 0 :=
  (((differentiable_const _).mul (P.quadCubeFactor_differentiable h2 hlam)) _).continuousAt.eventually_ne
    (P.quadDenom_ne_zero h2 hlam (by norm_num))

theorem quadDenom_tendsto (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) :
    Tendsto (fun s => star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s) (𝓝[≠] (4 / 3 : ℂ))
      (𝓝 (star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam (4 / 3))) :=
  ((((differentiable_const _).mul (P.quadCubeFactor_differentiable h2 hlam)) _).continuousAt.tendsto).mono_left
    nhdsWithin_le_nhds

/-- **In the quadratic grade `Q_φ` inherits the pole of `L_φ`.** If `M·L_φ` continues to
`{4/3 < Re s < 13/3, Im s > 0}` and a punctured neighbourhood of `4/3` with `(s − 4/3)^k M(s)L_φ(s) → c`, then
`M·Q_φ` continues there with `(s − 4/3)^k M(s)Q_φ(s) → c/(C̄² L(1, λ̃))`. -/
theorem quadraticGrade_pole_transfer (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) (φ : MulChar P.Res ℂ)
    (hφ : φ ^ 3 = P.lam) (k : ℕ) (c : ℂ) (Λ : ℂ → ℂ)
    (hΛe : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * P.twistDirichlet φ s)
    (hΛd : ∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s)
    (hΛn : ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s)
    (hΛl : Tendsto (fun s => (s - 4 / 3) ^ k * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 c)) :
    ∃ ΛQ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → ΛQ s = besselSqMellin s * P.twistCombination φ s) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ ΛQ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ ΛQ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ k * ΛQ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (c / (star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam (4 / 3)))) := by
  have hDd : Differentiable ℂ (fun s => star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s) :=
    (differentiable_const _).mul (P.quadCubeFactor_differentiable h2 hlam)
  refine ⟨fun s => Λ s / (star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s),
    fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_⟩
  · have hd := P.quadDenom_ne_zero h2 hlam (s := s) (by linarith)
    show Λ s / _ = _
    rw [hΛe s hs4 hs hi, P.twistDirichlet_eq_quadCubeFactor hlam φ hφ s hs4, div_eq_iff hd]
    ring
  · exact (hΛd s hs1 hs hi).div (hDd s) (P.quadDenom_ne_zero h2 hlam hs1.le)
  · filter_upwards [hΛn, nhdsWithin_le_nhds (P.quadDenom_eventually_ne h2 hlam)] with s h1 h2'
    exact h1.div (hDd s) h2'
  · refine (hΛl.div (P.quadDenom_tendsto h2 hlam) (P.quadDenom_ne_zero h2 hlam (by norm_num))).congr
      fun s => ?_
    simp only [Pi.div_apply]
    ring

/-- **Conversely, `L_φ` inherits the pole of `Q_φ`**, with leading coefficient multiplied by `C̄² L(1, λ̃)`. -/
theorem quadraticGrade_pole_transfer_symm (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1)
    (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = P.lam) (k : ℕ) (c : ℂ) (ΛQ : ℂ → ℂ)
    (hQe : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → ΛQ s = besselSqMellin s * P.twistCombination φ s)
    (hQd : ∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ ΛQ s)
    (hQn : ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ ΛQ s)
    (hQl : Tendsto (fun s => (s - 4 / 3) ^ k * ΛQ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 c)) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * P.twistDirichlet φ s) ∧
      (∀ s : ℂ, 4 / 3 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ k * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam (4 / 3) * c)) := by
  have hDd : Differentiable ℂ (fun s => star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s) :=
    (differentiable_const _).mul (P.quadCubeFactor_differentiable h2 hlam)
  refine ⟨fun s => star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s * ΛQ s,
    fun s hs4 hs hi => ?_, fun s hs1 hs hi => (hDd s).mul (hQd s hs1 hs hi), ?_, ?_⟩
  · show _ * ΛQ s = _
    rw [hQe s hs4 hs hi, P.twistDirichlet_eq_quadCubeFactor hlam φ hφ s hs4]
    ring
  · filter_upwards [hQn] with s h1
    exact (hDd s).mul h1
  · refine ((P.quadDenom_tendsto h2 hlam).mul hQl).congr fun s => ?_
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
