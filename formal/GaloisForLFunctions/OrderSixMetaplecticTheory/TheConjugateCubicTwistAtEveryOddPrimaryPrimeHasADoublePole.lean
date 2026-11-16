import GaloisForLFunctions.OrderSixMetaplecticTheory.TheThetaSquareFactorsThroughTheCoprimeSquaresAndTheConjugateTwist
import GaloisForLFunctions.OrderSixMetaplecticTheory.ThePrimaryGeneratorEvaluatesTheFractionalJacobiPhase

/-!
# The conjugate cubic twist at every odd primary prime has a double pole

For an odd primary prime q (ρ = |q|, N = N(q) = ρ², J = −χ(4)q the cubic–quadratic Jacobi sum, g₁, g₂ the Gauss sums
of χ and χ²), substituting the Euler identity (1 − ρ²ρ^{−3s})D = D_{cop} + ρ^{−s}D_q and g₁D_q = ρ⁻²χ(9)⁻¹g₂²D_g into the
fractional-trace relation gives

M(s)A(s)D_g(s) = [simple pole] + NJ(1 − ρ^{2−3s}) M(s)D(s),
A(s) = N²χ(−4)χ(9)⁻¹N^{s−2} + NJρ^{−s}χ(9)⁻¹g₂²ρ⁻²g₁⁻¹   (`conjFactor`).

The two summands of A have absolute values ρ^{2Re s} and ρ^{2−Re s}, so A does not vanish on Re s > 2/3
(`conjFactor_ne_zero`). Hence (`conjugateTwist_double_pole`) the Gauss-weighted conjugate twist D_g has the double
pole with leading coefficient A(4/3)⁻¹ NJ(1 − N⁻¹)·108π³r³ ≠ 0, and since g(k) = χ(k)⁻¹g₁ (`conjugateCubicTwist_double_pole`):

**the conjugate cubic twist L_{χ̄_q}(s) = Σ_k χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s} keeps the double pole at every odd primary prime.**

Together with `cubicTwistAtPrime_double_pole` (the twist by χ_q) both cubic twists at q carry the double pole of the theta
square; the leading coefficient of the conjugate twist involves the Jacobi sum J of the cubic and the quadratic character
of O/q.
-/

noncomputable section

open Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- c₂ = χ(9)⁻¹g₂²ρ⁻². -/
def eulerGauss : ℂ := (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹

/-- A(s) = N²χ(−4)χ(9)⁻¹N^{s−2} + NJρ^{−s}c₂g₁⁻¹. -/
def conjFactor (s : ℂ) : ℂ :=
  P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2) +
    P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹

theorem conjFactor_differentiableAt (s : ℂ) : DifferentiableAt ℂ P.conjFactor s := by
  have hρ := P.rho_ne_zero
  have hρρ : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos P.norm_pos P.norm_pos).ne'
  have hQ : DifferentiableAt ℂ (fun s : ℂ => ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2)) s :=
    DifferentiableAt.const_cpow (f := fun s : ℂ => s - 2) (differentiableAt_id.sub_const 2) (Or.inl hρρ)
  have ht : DifferentiableAt ℂ (fun s : ℂ => ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) s :=
    DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg (Or.inl hρ)
  unfold conjFactor
  exact ((differentiableAt_const _).mul hQ).add
    ((((differentiableAt_const _).mul ht).mul (differentiableAt_const _)).mul (differentiableAt_const _))

theorem one_lt_rho : 1 < ‖ringComplex P.p‖ := by
  have h1 := P.one_le_norm
  refine lt_of_le_of_ne h1 fun h => P.rho_sq_ne_one ?_
  rw [← h]
  norm_num

theorem norm_normC : ‖P.normC‖ = ‖ringComplex P.p‖ ^ 2 := by
  rw [normC, Complex.norm_natCast, P.card_res_eq]

theorem four_ne_zero' (h2 : (2 : P.Res) ≠ 0) : (4 : P.Res) ≠ 0 := by
  have := mul_ne_zero h2 h2
  norm_num at this
  exact this

theorem norm_fracJacobi (h2 : (2 : P.Res) ≠ 0) : ‖P.fracJacobi‖ = ‖ringComplex P.p‖ := by
  rw [P.fracJacobi_eq_primary, norm_neg, norm_mul, P.norm_chi_eq_one _ (P.four_ne_zero' h2), one_mul]

theorem norm_eulerGauss : ‖P.eulerGauss‖ = 1 := by
  have hn := P.norm_pos
  rw [eulerGauss, norm_mul, norm_mul, norm_inv, norm_inv, P.norm_chi_eq_one _ P.nine_ne_zero', norm_pow, norm_pow,
    P.norm_gaussAt2_one, Complex.norm_real, Real.norm_of_nonneg hn.le]
  field_simp

/-- **A(s) does not vanish on Re s > 2/3.** -/
theorem conjFactor_ne_zero (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs : 2 / 3 < s.re) : P.conjFactor s ≠ 0 := by
  have hρ0 := P.norm_pos
  have hρ1 := P.one_lt_rho
  set ρ := ‖ringComplex P.p‖ with hρdef
  set σ := s.re
  have h4 : P.chi (-4) ≠ 0 := P.chi_ne_zero_of_ne _ (neg_ne_zero.mpr (P.four_ne_zero' h2))
  have hQn : ‖((ρ * ρ : ℝ) : ℂ) ^ (s - 2)‖ = ρ ^ (σ - 2) * ρ ^ (σ - 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hρ0 hρ0), Real.mul_rpow hρ0.le hρ0.le]
    simp [σ]
  have htn : ‖((ρ : ℝ) : ℂ) ^ (-s)‖ = ρ ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hρ0, Complex.neg_re]
  have n1 : ‖P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((ρ * ρ : ℝ) : ℂ) ^ (s - 2)‖ =
      ρ ^ (2 : ℝ) * ρ ^ (2 : ℝ) * ρ ^ (σ - 2) * ρ ^ (σ - 2) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, P.norm_normC, P.norm_chi_eq_one _ (neg_ne_zero.mpr
      (P.four_ne_zero' h2)), P.norm_chi_eq_one _ P.nine_ne_zero', hQn, Real.rpow_two]
    ring
  have n2 : ‖P.normC * P.fracJacobi * ((ρ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹‖ =
      ρ ^ (2 : ℝ) * ρ ^ (-σ) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, P.norm_normC, P.norm_fracJacobi h2, htn, P.norm_eulerGauss,
      P.norm_gaussAt_one, Real.rpow_two, ← hρdef]
    field_simp
  have hlt : ρ ^ (2 : ℝ) * ρ ^ (-σ) < ρ ^ (2 : ℝ) * ρ ^ (2 : ℝ) * ρ ^ (σ - 2) * ρ ^ (σ - 2) := by
    rw [← Real.rpow_add hρ0, ← Real.rpow_add hρ0, ← Real.rpow_add hρ0, ← Real.rpow_add hρ0]
    exact Real.rpow_lt_rpow_of_exponent_lt hρ1 (by linarith)
  intro h0
  have heq := congrArg norm (eq_neg_of_add_eq_zero_left h0)
  rw [norm_neg] at heq
  unfold conjFactor at h0
  have : ‖P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((ρ * ρ : ℝ) : ℂ) ^ (s - 2)‖ =
      ‖P.normC * P.fracJacobi * ((ρ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹‖ := by
    have e := eq_neg_of_add_eq_zero_left h0
    rw [e, norm_neg]
  rw [n1, n2] at this
  linarith


/-! ### The double pole -/

/-- The leading coefficient A(4/3)⁻¹ NJ(1 − ρ²ρ^{−4})·108π³r³ of the Gauss-weighted conjugate twist. -/
def conjLimit : ℂ :=
  (P.conjFactor (4 / 3))⁻¹ * (P.normC * P.fracJacobi *
    (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3) *
      (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3))

theorem eventually_re_gt : ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), 2 / 3 < s.re := by
  have h : ∀ᶠ s in 𝓝 (4 / 3 : ℂ), 2 / 3 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact h.filter_mono nhdsWithin_le_nhds

theorem conjLimit_ne_zero (h2 : (2 : P.Res) ≠ 0) : P.conjLimit ≠ 0 := by
  have hA0 := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
  have hN : P.normC ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hJ : P.fracJacobi ≠ 0 := fun h => h2 (P.fracJacobi_eq_zero_iff.mp h)
  have hE := P.one_sub_ne_zero (4 / 3) (by norm_num)
  have hr := constantArithmeticResidue_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact mul_ne_zero (inv_ne_zero hA0) (mul_ne_zero (mul_ne_zero (mul_ne_zero hN hJ) hE)
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hπ)) (pow_ne_zero 3 hr)))

/-- **The Gauss-weighted conjugate twist has the double pole.** -/
theorem conjugateTwist_double_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * besselDirichlet P.gaussCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 P.conjLimit) ∧ P.conjLimit ≠ 0 := by
  obtain ⟨Λr, hr_eq, hr_d, hr_n, hr_l⟩ := P.conjugateTwist_relation h2
  obtain ⟨Λ₀, h0_eq, h0_d, h0_n, h0_l, -⟩ := thetaSqDirichlet_double_pole
  set E : ℂ → ℂ := fun s => 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3 with hE
  have hρ := P.rho_ne_zero
  have hEd : ∀ s, DifferentiableAt ℂ E s := fun s =>
    (differentiableAt_const _).sub ((differentiableAt_const _).mul
      ((DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg (Or.inl hρ)).pow 3))
  have hAd := P.conjFactor_differentiableAt
  refine ⟨fun s => (P.conjFactor s)⁻¹ * (Λr s + P.normC * P.fracJacobi * E s * Λ₀ s), fun s hs4 hs hi => ?_,
    fun s hs1 hs hi => ?_, ?_, ?_, P.conjLimit_ne_zero h2⟩
  · have hA := P.conjFactor_ne_zero h2 s (by linarith)
    have heuler := P.thetaSq_euler s hs4
    have hgp := P.gaussDirichlet_pCoeff s
    have hg1 := P.gaussAt_one_ne_zero
    have hDp : besselDirichlet P.pCoeff s = P.eulerGauss * (P.gaussAt 1)⁻¹ * besselDirichlet P.gaussCoeff s := by
      rw [← inv_mul_cancel_left₀ hg1 (besselDirichlet P.pCoeff s), hgp, eulerGauss]
      ring
    show (P.conjFactor s)⁻¹ * (Λr s + P.normC * P.fracJacobi * E s * Λ₀ s) = _
    rw [hr_eq s hs4 hs hi, h0_eq s hs4 hs hi, inv_mul_eq_iff_eq_mul₀ hA, conjFactor]
    simp only [hE]
    linear_combination (besselSqMellin s * (P.normC * P.fracJacobi)) * heuler +
      (besselSqMellin s * (P.normC * P.fracJacobi) * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) * hDp
  · exact ((hAd s).inv (P.conjFactor_ne_zero h2 s (by linarith))).mul
      ((hr_d s hs1 hs hi).add (((differentiableAt_const _).mul (hEd s)).mul (h0_d s hs1 hs hi)))
  · filter_upwards [hr_n, h0_n, eventually_re_gt] with s h1 h2' h3
    exact ((hAd s).inv (P.conjFactor_ne_zero h2 s h3)).mul (h1.add (((differentiableAt_const _).mul (hEd s)).mul h2'))
  · have hA0 := P.conjFactor_ne_zero h2 (4 / 3) (by norm_num)
    have hAt : Tendsto (fun s => (P.conjFactor s)⁻¹) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.conjFactor (4 / 3))⁻¹) :=
      ((hAd (4 / 3)).continuousAt.tendsto.inv₀ hA0).mono_left nhdsWithin_le_nhds
    have hEt : Tendsto E (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (E (4 / 3))) :=
      (hEd (4 / 3)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hsum := hr_l.add ((hEt.const_mul (P.normC * P.fracJacobi)).mul h0_l)
    have hlim := hAt.mul hsum
    rw [zero_add] at hlim
    have hval : P.conjLimit = (P.conjFactor (4 / 3))⁻¹ * (P.normC * P.fracJacobi * E (4 / 3) *
        (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3)) := rfl
    rw [hval]
    exact hlim.congr' (Eventually.of_forall fun s => by ring)

/-! ### The conjugate cubic twist -/

/-- The conjugate cubic twist χ_q(k)⁻¹T(k)². -/
def conjTwistCoeff (h : O) : ℂ := (P.chi (P.res h))⁻¹ * rationalSourceResidualFourierCoefficient h ^ 2

theorem gaussDirichlet_eq_conjTwist (s : ℂ) :
    besselDirichlet P.gaussCoeff s = P.gaussAt 1 * besselDirichlet P.conjTwistCoeff s := by
  rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  split_ifs
  · ring
  · rw [gaussCoeff, P.gaussAt_eq h, conjTwistCoeff]
    ring

/-- **The conjugate cubic twist keeps the double pole.** For every odd primary prime q, M(s)L_{χ̄_q}(s),
L_{χ̄_q}(s) = Σ_k χ_q(k)⁻¹T(k)²(4π|ξ_k|)^{−s}, continues to {1 < Re s < 13/3, Im s > 0} and to a punctured
neighbourhood of 4/3, and (s − 4/3)²M(s)L_{χ̄_q}(s) → g₁⁻¹A(4/3)⁻¹NJ(1 − N(q)⁻¹)·108π³r³ ≠ 0. -/
theorem conjugateCubicTwist_double_pole (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet P.conjTwistCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 ((P.gaussAt 1)⁻¹ * P.conjLimit)) ∧
      (P.gaussAt 1)⁻¹ * P.conjLimit ≠ 0 := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl, hne⟩ := P.conjugateTwist_double_pole h2
  have hg1 := P.gaussAt_one_ne_zero
  refine ⟨fun s => (P.gaussAt 1)⁻¹ * Λ s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => (hΛd s hs1 hs hi).const_mul _,
    ?_, ?_, mul_ne_zero (inv_ne_zero hg1) hne⟩
  · show (P.gaussAt 1)⁻¹ * Λ s = _
    rw [hΛ s hs4 hs hi, P.gaussDirichlet_eq_conjTwist]
    field_simp
  · filter_upwards [hΛn] with s h
    exact h.const_mul _
  · refine (hΛl.const_mul (P.gaussAt 1)⁻¹).congr' (Eventually.of_forall fun s => ?_)
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
