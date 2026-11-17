import GaloisForLFunctions.OrderSixMetaplecticTheory.ContinuationsThroughTheUntwistedLayerHaveSmoothedMainTerms
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheUnitLayerSplitsOverTheCubicResidueClasses

/-!
# The unit layers at an odd prime have smoothed main terms

Let `q` be an odd primary prime, `N = N(q)`, `J = −χ_q(4)q` the Jacobi sum, `g₁` the cubic Gauss sum,
`A(s) = N²χ(−4)χ(9)⁻¹N^{s−2} + NJ|q|^{−s}c₂g₁⁻¹` and `E(s) = 1 − N^{1−3s/2}`. The fractional and the shifted fractional
traces at `q` leave bounded remainders `F`, `F^φ`; with their regularized pairings `Λ̃_F`, `Λ̃_{F^φ}` the unit layers of
the conjugate twist and of the principal character modulo `q` are, on `1 < Re w < 13/6` and `s = 2w`,

`S^{χ̄_q}_1(w) = g₁⁻¹A(s)⁻¹NJ·S₁(w) + (s − 4/3)β(s)(Λ̃_F − Λ̃_{F^φ})(s)`,
`S^{1_q}_1(w) = A(s)⁻¹N²χ(−4)χ(9)⁻¹N^{s−2}·S₁(w) − (s − 4/3)|q|^{−s}c₂β(s)(Λ̃_F − Λ̃_{F^φ})(s)`,

with one explicit factor `β` (`conjLayer_eq_upper`, `principalLayer_eq_upper`). Both identities come from one relation
between the traces (`conj_key`, `principal_key`): the remainder combination measures how far the conjugate twist and
the coprime squares are from the untwisted layer. Through the layer tool:

* `Σ_A χ̄_q(gen A)σ(A)g(log(N(A)/X)) = e^{4/9}NJ/(g₁A(4/3))·Res S₁·X^{2/3} + O(X^a)`
  (`conjugateUnitLayer_smoothed_main_term`);
* `Σ_{q∤gen A}σ(A)g(log(N(A)/X)) = e^{4/9}N²χ(−4)χ(9)⁻¹N^{−2/3}/A(4/3)·Res S₁·X^{2/3} + O(X^a)`
  (`principalUnitLayer_smoothed_main_term`);
* on each cubic residue class `χ_q(gen A) = c` the smoothed sum is `⅓` of the combination of the three
  (`classUnitLayer_smoothed_main_term`), the cubic twist coming from the Hecke trace at `q`;

for every `5/8 < a < 2/3`. So the bias `X^{2/3}` of the squared cubic Gauss sums splits over the cubic classes
modulo `q` with explicit weights, up to the remainder exponent of `S₁`.
-/

noncomputable section

open MeasureTheory Filter Function Topology Complex
open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `K(s) = N²χ(−4)χ(9)⁻¹N^{s−2}`. -/
def oddK (s : ℂ) : ℂ :=
  P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) * ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2)

/-- `E(s) = 1 − |q|²|q|^{−3s}`. -/
def oddE (s : ℂ) : ℂ := 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3

/-! ### Bounds -/

theorem norm_oddK (h2 : (2 : P.Res) ≠ 0) (s : ℂ) : ‖P.oddK s‖ = ‖ringComplex P.p‖ ^ (2 * s.re) := by
  have hρ0 := P.norm_pos
  have hQn : ‖((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 2)‖ =
      ‖ringComplex P.p‖ ^ (s.re - 2) * ‖ringComplex P.p‖ ^ (s.re - 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hρ0 hρ0), Real.mul_rpow hρ0.le hρ0.le]
    simp
  have e1 : ‖ringComplex P.p‖ ^ (2 * s.re) = (‖ringComplex P.p‖ ^ 2) ^ 2 *
      (‖ringComplex P.p‖ ^ (s.re - 2) * ‖ringComplex P.p‖ ^ (s.re - 2)) := by
    rw [← Real.rpow_add hρ0, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hρ0]
    congr 1
    push_cast
    ring
  rw [oddK, norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, P.norm_normC,
    P.norm_chi_eq_one _ (neg_ne_zero.mpr (P.four_ne_zero' h2)), P.norm_chi_eq_one _ P.nine_ne_zero', hQn, e1]
  ring

theorem norm_conjFactor_inv_le (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 2 / 3 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → ‖(P.conjFactor s)⁻¹‖ ≤ C := by
  have hρ0 := P.norm_pos
  have hρ1 := P.one_lt_rho
  have hgap : 0 < ‖ringComplex P.p‖ ^ (2 * a) - ‖ringComplex P.p‖ ^ (2 - a) :=
    sub_pos.mpr (Real.rpow_lt_rpow_of_exponent_lt hρ1 (by linarith))
  refine ⟨(‖ringComplex P.p‖ ^ (2 * a) - ‖ringComplex P.p‖ ^ (2 - a))⁻¹, (inv_pos.mpr hgap).le,
    fun s hs => ?_⟩
  have n2 : ‖P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹‖ =
      ‖ringComplex P.p‖ ^ (2 - s.re) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, P.norm_normC, P.norm_fracJacobi h2,
      Complex.norm_cpow_eq_rpow_re_of_pos hρ0, Complex.neg_re, P.norm_eulerGauss, P.norm_gaussAt_one,
      Real.rpow_sub hρ0, Real.rpow_two, Real.rpow_neg hρ0.le]
    field_simp
  have hlow : ‖ringComplex P.p‖ ^ (2 * a) - ‖ringComplex P.p‖ ^ (2 - a) ≤ ‖P.conjFactor s‖ := by
    have h1 : ‖ringComplex P.p‖ ^ (2 * a) ≤ ‖P.oddK s‖ := by
      rw [P.norm_oddK h2]
      exact Real.rpow_le_rpow_of_exponent_le hρ1.le (by linarith)
    have h2' : ‖ringComplex P.p‖ ^ (2 - s.re) ≤ ‖ringComplex P.p‖ ^ (2 - a) :=
      Real.rpow_le_rpow_of_exponent_le hρ1.le (by linarith)
    have := norm_sub_norm_le (P.oddK s)
      (-(P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹))
    rw [norm_neg, sub_neg_eq_add, n2] at this
    have hA : P.conjFactor s = P.oddK s +
        P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹ := rfl
    rw [hA]
    linarith
  rw [norm_inv]
  exact inv_anti₀ hgap hlow

theorem norm_oddE_le (s : ℂ) (hs : 2 / 3 < s.re) : ‖P.oddE s‖ ≤ 2 := by
  have h := P.norm_rho_cube_lt s hs
  have := norm_sub_le (1 : ℂ) ((‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)
  rw [norm_one] at this
  rw [oddE]
  linarith

theorem norm_rho_cpow_le (s : ℂ) (hs : 0 ≤ s.re) : ‖((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)‖ ≤ 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos P.norm_pos, Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos P.one_le_norm (by linarith)

/-- `|(2W(s)Den(s)M(s))⁻¹| ≤ K(1 + |w|)²e^{4π|Im w|}` at `s = 2w`. -/
theorem norm_unitDenom_inv_le (a : ℝ) (ha : 5 / 8 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖(2 * unitFrequencyWeight (2 * w) * P.combinationDenom (2 * w) * besselSqMellin (2 * w))⁻¹‖ ≤
        K * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|) := by
  obtain ⟨Ke, hKe, hke⟩ := P.norm_eulerFactorQ_inv_le (2 * a) (by linarith)
  obtain ⟨Kw, hKw, hkw⟩ := unitFrequencyWeight_inv_le 4
  obtain ⟨Kz, hKz, hkz⟩ := clearedCubeZeta_inv_vertical_bound (2 * a) (by linarith)
  obtain ⟨Km, hKm, hkm⟩ := besselSqMellin_inv_vertical_bound a 2 (by linarith)
  set c₀ : ℂ := (2 * (star rationalSourceThetaScalar ^ 2 * (2 / 3)))⁻¹ with hc₀
  refine ⟨‖c₀‖ * Kw * (4 * Kz) * Ke * Km, by positivity, fun w hwa hw2 hwi => ?_⟩
  have hr : (2 * w).re = 2 * w.re := by simp
  have hi : (2 * w).im = 2 * w.im := by simp
  have hi1 : 1 ≤ |(2 * w).im| := by rw [hi, abs_mul]; norm_num; linarith
  have hsa : 2 * a ≤ (2 * w).re := by rw [hr]; linarith
  have hs4 : (2 * w).re ≤ 4 := by rw [hr]; linarith
  have he : (2 * unitFrequencyWeight (2 * w) * P.combinationDenom (2 * w) * besselSqMellin (2 * w))⁻¹ =
      c₀ * (unitFrequencyWeight (2 * w))⁻¹ * (clearedCubeZeta (2 * w))⁻¹ * (P.eulerFactorQ (2 * w))⁻¹ *
        (besselSqMellin (2 * w))⁻¹ := by
    rw [combinationDenom, hc₀]
    simp only [mul_inv]
    ring
  have hz : ‖(clearedCubeZeta (2 * w))⁻¹‖ ≤ 4 * Kz * (1 + ‖w‖) ^ 2 := by
    refine (hkz _ hsa hi1).trans ?_
    have h := Complex.abs_im_le_norm w
    have h2 := mul_le_mul h h (abs_nonneg _) (norm_nonneg _)
    rw [hi, abs_mul, abs_two]
    nlinarith only [h, h2, abs_nonneg w.im, norm_nonneg w, hKz]
  have g1 := hkw _ (by linarith) hs4
  have g2 := hke _ hsa
  have g3 := hkm w hwa hw2 hwi
  rw [he, norm_mul, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ‖c₀‖ * Kw * (4 * Kz * (1 + ‖w‖) ^ 2) * Ke * (Km * Real.exp (4 * Real.pi * |w.im|)) := by gcongr
    _ = _ := by ring

/-! ### The relations between the traces -/

/-- **The conjugate relation.** `NJ·E·U + (2/3)vol⁻¹(Λ_F − Λ_{F^φ}) = g₁A·M·D₀^{χ̄}` on `4 < Re s < 13/3`, `Im s > 0`,
`U` the completed unramified square. -/
theorem conj_key (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    P.normC * P.fracJacobi * P.oddE s * completedUnramified s +
        (2 / 3) * (periodArea : ℂ)⁻¹ * ((P.fracRemainder_remainderData h2).pairing s -
          (P.shiftRemainder_remainderData h2).pairing s) =
      P.gaussAt 1 * P.conjFactor s * besselSqMellin s * besselDirichlet P.unramConjCoeff s := by
  have f₃ : (P.fracRemainder_remainderData h2).pairing s = periodArea * (besselSqMellin s *
      (P.oddK s * besselDirichlet P.gaussCoeff s - P.normC * P.fracJacobi * besselDirichlet P.coprimeCoeff s)) := by
    rw [← (P.fracRemainder_remainderData h2).pairing_eq s hs4 hs hi,
      P.integral_fracRemainder_mul_eisenstein h2 s hs4 hs]
    rfl
  have f₄ : (P.shiftRemainder_remainderData h2).pairing s = periodArea * (besselSqMellin s *
      (P.oddK s * besselDirichlet P.phGauss s - P.normC * P.fracJacobi * besselDirichlet P.phCoprime s)) := by
    rw [← (P.shiftRemainder_remainderData h2).pairing_eq s hs4 hs hi,
      P.integral_shiftRemainder_mul_eisenstein h2 s hs4 hs]
    rfl
  have t1 := completedThetaSq_eq s hs4 hs hi
  have t2 := completedTranslated_eq s hs4 hs hi
  have ce := P.coprime_euler s hs4
  have cpe := P.phCoprime_euler s hs4
  have f₇ := P.gaussDirichlet_eq_conjTwist s
  have f₈ := P.gaussDirichlet_eq_phConjTwist s
  have ts := P.conjTwist_sub_phased s hs4
  have f₀ : (periodArea : ℂ)⁻¹ * periodArea = 1 :=
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne')
  have e0 : P.gaussAt 1 * (P.gaussAt 1)⁻¹ = 1 := mul_inv_cancel₀ P.gaussAt_one_ne_zero
  have hA : P.conjFactor s = P.oddK s +
      P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹ := rfl
  rw [completedUnramified, hA, oddE]
  set M := besselSqMellin s
  set K := P.oddK s
  set nJ := P.normC * P.fracJacobi
  set t := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)
  set c₂ := P.eulerGauss
  set g₁ := P.gaussAt 1
  set E := 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * t ^ 3
  set v := (periodArea : ℂ)
  linear_combination (2 / 3) * nJ * E * t1 - (2 / 3) * nJ * E * t2 + (2 / 3) * v⁻¹ * f₃ - (2 / 3) * v⁻¹ * f₄ +
    (2 / 3) * M * ((K * besselDirichlet P.gaussCoeff s - nJ * besselDirichlet P.coprimeCoeff s) -
      (K * besselDirichlet P.phGauss s - nJ * besselDirichlet P.phCoprime s)) * f₀ -
    (2 / 3) * M * nJ * ce + (2 / 3) * M * nJ * cpe + (2 / 3) * M * K * f₇ - (2 / 3) * M * K * f₈ +
    (2 / 3) * M * (K * g₁ + nJ * t * c₂) * ts - M * nJ * t * c₂ * besselDirichlet P.unramConjCoeff s * e0

/-- **The principal relation.** `g₁K·E·U − |q|^{−s}c₂(2/3)vol⁻¹(Λ_F − Λ_{F^φ}) = g₁A·M·D₀^{1}`. -/
theorem principal_key (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    P.gaussAt 1 * P.oddK s * P.oddE s * completedUnramified s -
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss *
          ((2 / 3) * (periodArea : ℂ)⁻¹ * ((P.fracRemainder_remainderData h2).pairing s -
            (P.shiftRemainder_remainderData h2).pairing s)) =
      P.gaussAt 1 * P.conjFactor s * besselSqMellin s * besselDirichlet P.unramCoprimeCoeff s := by
  have ck := P.conj_key h2 s hs4 hs hi
  have t1 := completedThetaSq_eq s hs4 hs hi
  have t2 := completedTranslated_eq s hs4 hs hi
  have ce := P.coprime_euler s hs4
  have cpe := P.phCoprime_euler s hs4
  have ts := P.conjTwist_sub_phased s hs4
  have cs := P.coprime_sub_phased s hs4
  have e0 : P.gaussAt 1 * (P.gaussAt 1)⁻¹ = 1 := mul_inv_cancel₀ P.gaussAt_one_ne_zero
  have hA : P.conjFactor s = P.oddK s +
      P.normC * P.fracJacobi * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * (P.gaussAt 1)⁻¹ := rfl
  rw [hA, completedUnramified, oddE] at ck
  rw [hA, completedUnramified, oddE]
  set M := besselSqMellin s
  set K := P.oddK s
  set nJ := P.normC * P.fracJacobi
  set t := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)
  set c₂ := P.eulerGauss
  set g₁ := P.gaussAt 1
  set E := 1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * t ^ 3
  set B := g₁ * K + nJ * t * c₂
  linear_combination (-(t * c₂)) * ck +
    (-(nJ * t * c₂ * M * besselDirichlet P.unramCoprimeCoeff s) -
      t * c₂ * (nJ * t * c₂) * M * besselDirichlet P.unramConjCoeff s) * e0 +
    B * (2 / 3) * E * t1 - B * (2 / 3) * E * t2 + B * (2 / 3) * M * cs - B * (2 / 3) * M * ce +
    B * (2 / 3) * M * cpe + B * (2 / 3) * M * t * c₂ * ts

/-! ### The two continuations -/

/-- `β(s) = (2/3)vol⁻¹g₁⁻¹A(s)⁻¹(2W(s)Den(s)M(s))⁻¹`. -/
def conjBeta (s : ℂ) : ℂ :=
  (2 / 3) * (periodArea : ℂ)⁻¹ * (P.gaussAt 1)⁻¹ * (P.conjFactor s)⁻¹ *
    (2 * unitFrequencyWeight s * P.combinationDenom s * besselSqMellin s)⁻¹

/-- The weight `g₁⁻¹A(s)⁻¹NJ·E(s)/E_q(s)` of `S₁` in the conjugate unit layer. -/
def conjAlpha (s : ℂ) : ℂ :=
  (P.gaussAt 1)⁻¹ * (P.conjFactor s)⁻¹ * (P.normC * P.fracJacobi) * P.oddE s / P.eulerFactorQ s

/-- The weight `K(s)E(s)/(A(s)E_q(s))` of `S₁` in the principal unit layer. -/
def principalAlpha (s : ℂ) : ℂ := P.oddK s * P.oddE s / (P.conjFactor s * P.eulerFactorQ s)

/-- `−|q|^{−s}c₂β(s)`. -/
def principalBeta (s : ℂ) : ℂ := -(((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss) * P.conjBeta s

theorem oddK_differentiableAt (s : ℂ) : DifferentiableAt ℂ P.oddK s := by
  have hρρ : ((‖ringComplex P.p‖ * ‖ringComplex P.p‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos P.norm_pos P.norm_pos).ne'
  unfold oddK
  exact (differentiableAt_const _).mul
    (DifferentiableAt.const_cpow (f := fun s : ℂ => s - 2) (differentiableAt_id.sub_const 2) (Or.inl hρρ))

theorem rho_cpow_differentiableAt (s : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ => ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) s :=
  DifferentiableAt.const_cpow (f := fun s : ℂ => -s) differentiableAt_id.neg (Or.inl P.rho_ne_zero)

theorem oddE_differentiableAt (s : ℂ) : DifferentiableAt ℂ P.oddE s := by
  unfold oddE
  exact (differentiableAt_const _).sub ((differentiableAt_const _).mul ((P.rho_cpow_differentiableAt s).pow 3))

theorem conjBeta_differentiableAt (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs : 5 / 4 < s.re) :
    DifferentiableAt ℂ P.conjBeta s := by
  unfold conjBeta
  have hden : DifferentiableAt ℂ
      (fun s => (2 * unitFrequencyWeight s * P.combinationDenom s * besselSqMellin s)⁻¹) s :=
    ((((unitFrequencyWeight_differentiable s).const_mul 2).mul (P.combinationDenom_differentiable s)).mul
      (besselSqMellin_differentiableAt s (by linarith))).inv
      (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (unitFrequencyWeight_ne_zero s))
        (P.combinationDenom_ne_zero_of_five_fourths hs)) (besselSqMellin_ne_zero s (by linarith)))
  exact ((differentiableAt_const _).mul ((P.conjFactor_differentiableAt s).inv
    (P.conjFactor_ne_zero h2 s (by linarith)))).mul hden

theorem conjAlpha_differentiableAt (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs : 2 / 3 < s.re) :
    DifferentiableAt ℂ P.conjAlpha s := by
  unfold conjAlpha
  exact ((((differentiableAt_const _).mul ((P.conjFactor_differentiableAt s).inv
    (P.conjFactor_ne_zero h2 s hs))).mul_const _).mul (P.oddE_differentiableAt s)).div
      (P.eulerFactorQ_differentiable s) (P.eulerFactorQ_ne_zero hs)

theorem principalAlpha_differentiableAt (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs : 2 / 3 < s.re) :
    DifferentiableAt ℂ P.principalAlpha s := by
  unfold principalAlpha
  exact ((P.oddK_differentiableAt s).mul (P.oddE_differentiableAt s)).div
    ((P.conjFactor_differentiableAt s).mul (P.eulerFactorQ_differentiable s))
    (mul_ne_zero (P.conjFactor_ne_zero h2 s hs) (P.eulerFactorQ_ne_zero hs))

theorem principalBeta_differentiableAt (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs : 5 / 4 < s.re) :
    DifferentiableAt ℂ P.principalBeta s := by
  unfold principalBeta
  exact (((P.rho_cpow_differentiableAt s).mul_const _).neg).mul (P.conjBeta_differentiableAt h2 s hs)

/-- The regularized-to-actual reduction shared by both identities. -/
private theorem layer_reduce (h2 : (2 : P.Res) ≠ 0) (α β : ℂ → ℂ) (s : ℂ) (hs4 : 4 < s.re) (hi : 0 < s.im) :
    layerCont (P.fracRemainder_remainderData h2) (P.shiftRemainder_remainderData h2) α β (s / 2) =
      α s * ((s - 4 / 3) * completedUnramified s / (2 * unitFrequencyWeight s *
        star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s) / besselSqMellin s) +
      (s - 4 / 3) * β s * ((P.fracRemainder_remainderData h2).pairing s -
        (P.shiftRemainder_remainderData h2).pairing s) := by
  have hs2 : 2 * (s / 2) = s := by ring
  have hre : 5 / 8 < (s / 2).re := by
    rw [show (s / 2).re = s.re / 2 by simp]
    linarith
  have him : (s / 2).im ≠ 0 := by
    rw [show (s / 2).im = s.im / 2 by simp]
    exact div_ne_zero hi.ne' two_ne_zero
  rw [layerCont, hs2, regularizedUntwistedTheta_eq_nonreal _ hre him, continuedUntwistedTheta, hs2,
    completedUntwistedS, (P.fracRemainder_remainderData h2).regPairing_eq_of_im_ne s (by linarith) hi.ne',
    (P.shiftRemainder_remainderData h2).regPairing_eq_of_im_ne s (by linarith) hi.ne']

theorem conjLayer_eq_upper (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3)
    (hi : 0 < s.im) :
    layerCont (P.fracRemainder_remainderData h2) (P.shiftRemainder_remainderData h2) P.conjAlpha P.conjBeta (s / 2) =
      idealSeries (P.unitCoeff P.chi⁻¹) (s / 2) := by
  rw [P.idealSeries_unitCoeff, P.layer_reduce h2 _ _ s hs4 hi]
  have key := P.conj_key h2 s hs4 hs hi
  have hL := P.sub_mul_unramConj s hs4
  have hcd : P.combinationDenom s =
      star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s * P.eulerFactorQ s := rfl
  have hM0 : besselSqMellin s ≠ 0 := besselSqMellin_ne_zero s (by linarith)
  have hA0 : P.conjFactor s ≠ 0 := P.conjFactor_ne_zero h2 s (by linarith)
  have hg0 : P.gaussAt 1 ≠ 0 := P.gaussAt_one_ne_zero
  have hW0 : unitFrequencyWeight s ≠ 0 := unitFrequencyWeight_ne_zero s
  have hZ0 : clearedCubeZeta s ≠ 0 := clearedCubeZeta_ne_zero (by linarith)
  have hE0 : P.eulerFactorQ s ≠ 0 := P.eulerFactorQ_ne_zero (by linarith)
  have hC0 : star rationalSourceThetaScalar ^ 2 ≠ 0 := pow_ne_zero 2 scalar_star_ne_zero
  have hv0 : (periodArea : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  have hcd0 : P.combinationDenom s ≠ 0 := by
    rw [hcd]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hC0 (by norm_num)) hZ0) hE0
  set X := (P.fracRemainder_remainderData h2).pairing s - (P.shiftRemainder_remainderData h2).pairing s
  have hQ : P.gaussAt 1 * P.conjFactor s * (2 * unitFrequencyWeight s * P.combinationDenom s) *
      besselSqMellin s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hg0 hA0) (mul_ne_zero (mul_ne_zero two_ne_zero hW0) hcd0)) hM0
  have hform : P.conjAlpha s * ((s - 4 / 3) * completedUnramified s / (2 * unitFrequencyWeight s *
      star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s) / besselSqMellin s) +
      (s - 4 / 3) * P.conjBeta s * X =
        (s - 4 / 3) * (P.normC * P.fracJacobi * P.oddE s * completedUnramified s +
          (2 / 3) * (periodArea : ℂ)⁻¹ * X) /
          (P.gaussAt 1 * P.conjFactor s * (2 * unitFrequencyWeight s * P.combinationDenom s) *
            besselSqMellin s) := by
    rw [conjAlpha, conjBeta, hcd]
    field_simp
  rw [hform, key, div_eq_iff hQ]
  linear_combination (P.gaussAt 1 * P.conjFactor s * besselSqMellin s) * hL

theorem principalLayer_eq_upper (h2 : (2 : P.Res) ≠ 0) (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3)
    (hi : 0 < s.im) :
    layerCont (P.fracRemainder_remainderData h2) (P.shiftRemainder_remainderData h2) P.principalAlpha
      P.principalBeta (s / 2) = idealSeries (P.unitCoeff 1) (s / 2) := by
  rw [P.idealSeries_unitCoeff, P.layer_reduce h2 _ _ s hs4 hi]
  have key := P.principal_key h2 s hs4 hs hi
  have hL := P.sub_mul_unramCoprime s hs4
  have hcd : P.combinationDenom s =
      star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s * P.eulerFactorQ s := rfl
  have hM0 : besselSqMellin s ≠ 0 := besselSqMellin_ne_zero s (by linarith)
  have hA0 : P.conjFactor s ≠ 0 := P.conjFactor_ne_zero h2 s (by linarith)
  have hg0 : P.gaussAt 1 ≠ 0 := P.gaussAt_one_ne_zero
  have hW0 : unitFrequencyWeight s ≠ 0 := unitFrequencyWeight_ne_zero s
  have hZ0 : clearedCubeZeta s ≠ 0 := clearedCubeZeta_ne_zero (by linarith)
  have hE0 : P.eulerFactorQ s ≠ 0 := P.eulerFactorQ_ne_zero (by linarith)
  have hC0 : star rationalSourceThetaScalar ^ 2 ≠ 0 := pow_ne_zero 2 scalar_star_ne_zero
  have hv0 : (periodArea : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  have hcd0 : P.combinationDenom s ≠ 0 := by
    rw [hcd]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hC0 (by norm_num)) hZ0) hE0
  set X := (P.fracRemainder_remainderData h2).pairing s - (P.shiftRemainder_remainderData h2).pairing s
  have hQ : P.gaussAt 1 * P.conjFactor s * (2 * unitFrequencyWeight s * P.combinationDenom s) *
      besselSqMellin s ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hg0 hA0) (mul_ne_zero (mul_ne_zero two_ne_zero hW0) hcd0)) hM0
  have hform : P.principalAlpha s * ((s - 4 / 3) * completedUnramified s / (2 * unitFrequencyWeight s *
      star rationalSourceThetaScalar ^ 2 * (2 / 3) * clearedCubeZeta s) / besselSqMellin s) +
      (s - 4 / 3) * P.principalBeta s * X =
        (s - 4 / 3) * (P.gaussAt 1 * P.oddK s * P.oddE s * completedUnramified s -
          ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * P.eulerGauss * ((2 / 3) * (periodArea : ℂ)⁻¹ * X)) /
          (P.gaussAt 1 * P.conjFactor s * (2 * unitFrequencyWeight s * P.combinationDenom s) *
            besselSqMellin s) := by
    rw [principalAlpha, principalBeta, conjBeta, hcd]
    field_simp
    ring
  rw [hform, key, div_eq_iff hQ]
  linear_combination (P.gaussAt 1 * P.conjFactor s * besselSqMellin s) * hL

/-! ### The smoothed main terms -/

theorem conjAlpha_bound (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 1 / 3 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 2 * a ≤ s.re → s.re ≤ 4 → ‖P.conjAlpha s‖ ≤ K := by
  obtain ⟨KA, hKA, hkA⟩ := P.norm_conjFactor_inv_le h2 (2 * a) (by linarith)
  obtain ⟨KE, hKE, hkE⟩ := P.norm_eulerFactorQ_inv_le (2 * a) (by linarith)
  refine ⟨‖(P.gaussAt 1)⁻¹‖ * KA * ‖P.normC * P.fracJacobi‖ * 2 * KE, by positivity, fun s hs _ => ?_⟩
  rw [conjAlpha, div_eq_mul_inv, norm_mul, norm_mul, norm_mul, norm_mul]
  have g1 := hkA s hs
  have g2 := P.norm_oddE_le s (by linarith)
  have g3 := hkE s hs
  gcongr

theorem principalAlpha_bound (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 1 / 3 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 2 * a ≤ s.re → s.re ≤ 4 → ‖P.principalAlpha s‖ ≤ K := by
  obtain ⟨KA, hKA, hkA⟩ := P.norm_conjFactor_inv_le h2 (2 * a) (by linarith)
  obtain ⟨KE, hKE, hkE⟩ := P.norm_eulerFactorQ_inv_le (2 * a) (by linarith)
  refine ⟨‖ringComplex P.p‖ ^ (2 * 4 : ℝ) * 2 * KA * KE, by positivity, fun s hs hs4 => ?_⟩
  have hK : ‖P.oddK s‖ ≤ ‖ringComplex P.p‖ ^ (2 * 4 : ℝ) := by
    rw [P.norm_oddK h2]
    exact Real.rpow_le_rpow_of_exponent_le P.one_le_norm (by linarith)
  have g2 := P.norm_oddE_le s (by linarith)
  have g1 := hkA s hs
  have g3 := hkE s hs
  rw [principalAlpha, div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ‖ringComplex P.p‖ ^ (2 * 4 : ℝ) * 2 * (KA * KE) := by gcongr
    _ = _ := by ring

theorem conjBeta_bound (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 5 / 8 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖P.conjBeta (2 * w)‖ ≤ K * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|) := by
  obtain ⟨KA, hKA, hkA⟩ := P.norm_conjFactor_inv_le h2 (2 * a) (by linarith)
  obtain ⟨KD, hKD, hkD⟩ := P.norm_unitDenom_inv_le a ha
  refine ⟨‖(2 / 3 : ℂ) * (periodArea : ℂ)⁻¹ * (P.gaussAt 1)⁻¹‖ * KA * KD, by positivity,
    fun w hwa hw2 hwi => ?_⟩
  have hr : (2 * w).re = 2 * w.re := by simp
  have g1 := hkA (2 * w) (by rw [hr]; linarith)
  have g2 := hkD w hwa hw2 hwi
  rw [conjBeta, norm_mul, norm_mul]
  calc
    _ ≤ ‖(2 / 3 : ℂ) * (periodArea : ℂ)⁻¹ * (P.gaussAt 1)⁻¹‖ * KA *
        (KD * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|)) := by gcongr
    _ = _ := by ring

theorem principalBeta_bound (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 5 / 8 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im| →
      ‖P.principalBeta (2 * w)‖ ≤ K * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|) := by
  obtain ⟨K, hK, hk⟩ := P.conjBeta_bound h2 a ha
  refine ⟨K, hK, fun w hwa hw2 hwi => ?_⟩
  have hr : (2 * w).re = 2 * w.re := by simp
  have ht := P.norm_rho_cpow_le (2 * w) (by rw [hr]; linarith)
  rw [principalBeta, norm_mul, norm_neg, norm_mul, P.norm_eulerGauss, mul_one]
  calc
    _ ≤ 1 * (K * (1 + ‖w‖) ^ 2 * Real.exp (4 * Real.pi * |w.im|)) :=
      mul_le_mul ht (hk w hwa hw2 hwi) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-- `α(4/3) = NJ/(g₁A(4/3))`. -/
theorem conjAlpha_four_thirds :
    P.conjAlpha (4 / 3) = P.normC * P.fracJacobi / (P.gaussAt 1 * P.conjFactor (4 / 3)) := by
  have hE : P.oddE (4 / 3) = P.eulerFactorQ (4 / 3) := by rw [oddE, P.eulerFactorQ_four_thirds_eq]
  have hE0 : P.eulerFactorQ (4 / 3) ≠ 0 := P.eulerFactorQ_ne_zero (by norm_num)
  rw [conjAlpha, hE]
  field_simp

/-- `α(4/3) = N²χ(−4)χ(9)⁻¹N^{−2/3}/A(4/3)`. -/
theorem principalAlpha_four_thirds : P.principalAlpha (4 / 3) = P.oddK (4 / 3) / P.conjFactor (4 / 3) := by
  have hE : P.oddE (4 / 3) = P.eulerFactorQ (4 / 3) := by rw [oddE, P.eulerFactorQ_four_thirds_eq]
  have hE0 : P.eulerFactorQ (4 / 3) ≠ 0 := P.eulerFactorQ_ne_zero (by norm_num)
  rw [principalAlpha, hE]
  field_simp

/-- **The smoothed main term of the conjugate unit layer.** -/
theorem conjugateUnitLayer_smoothed_main_term (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 5 / 8 < a) (ha' : a < 2 / 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedSum (P.unitCoeff P.chi⁻¹) X - (X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) *
        (P.normC * P.fracJacobi / (P.gaussAt 1 * P.conjFactor (4 / 3)) * untwistedThetaResidue))‖ ≤ K * X ^ a := by
  rw [← P.conjAlpha_four_thirds]
  exact layerCont_smoothed_main_term _ _ _ _ (P.unitCoeff_bounded _)
    (fun s hs => P.conjAlpha_differentiableAt h2 s (by linarith)) (fun s hs => P.conjBeta_differentiableAt h2 s hs)
    (P.conjLayer_eq_upper h2) a ha ha' (P.conjAlpha_bound h2 a (by linarith)) (P.conjBeta_bound h2 a ha)

/-- **The smoothed main term of the principal unit layer.** -/
theorem principalUnitLayer_smoothed_main_term (h2 : (2 : P.Res) ≠ 0) (a : ℝ) (ha : 5 / 8 < a) (ha' : a < 2 / 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedSum (P.unitCoeff 1) X - (X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) *
        (P.oddK (4 / 3) / P.conjFactor (4 / 3) * untwistedThetaResidue))‖ ≤ K * X ^ a := by
  rw [← P.principalAlpha_four_thirds]
  exact layerCont_smoothed_main_term _ _ _ _ (P.unitCoeff_bounded _)
    (fun s hs => P.principalAlpha_differentiableAt h2 s (by linarith))
    (fun s hs => P.principalBeta_differentiableAt h2 s hs)
    (P.principalLayer_eq_upper h2) a ha ha' (P.principalAlpha_bound h2 a (by linarith)) (P.principalBeta_bound h2 a ha)

/-! ### The cubic residue classes -/

/-- `[χ_q(gen A) = c]·σ(A)`. -/
def classCoeff (c : ℂ) (A : Ideal O) : ℂ :=
  if Squarefree A ∧ primaryIdealGenerator A ≠ 0 then
    (if P.chi (P.res (primaryIdealGenerator A)) = c then (1 : ℂ) else 0) *
      (ringComplex (symbol 1 (primaryIdealGenerator A)) ^ 2 * thetaSquareWeight A) else 0

theorem classCoeff_eq (c : ℂ) (hc : c ^ 3 = 1) (A : Ideal O) :
    P.classCoeff c A = 1 / 3 * P.unitCoeff 1 A + 1 / 3 * c⁻¹ * P.unitCoeff P.chi A +
      1 / 3 * c⁻¹ ^ 2 * P.unitCoeff P.chi⁻¹ A := by
  unfold classCoeff unitCoeff
  by_cases h : Squarefree A ∧ primaryIdealGenerator A ≠ 0
  · simp only [if_pos h]
    rw [P.class_indicator c hc]
    ring
  · simp only [if_neg h]
    ring

/-- **The smoothed main term on a cubic residue class.** For an odd primary prime `q`, `c³ = 1` and
`5/8 < a < 2/3`: `Σ_{χ_q(gen A) = c}σ(A)g(log(N(A)/X)) = ⅓e^{4/9}(α₁ + c̄α_χ + c̄²α_χ̄)Res S₁·X^{2/3} + O(X^a)`. -/
theorem classUnitLayer_smoothed_main_term (h2 : (2 : P.Res) ≠ 0) (c : ℂ) (hc : c ^ 3 = 1) (a : ℝ)
    (ha : 5 / 8 < a) (ha' : a < 2 / 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X →
      ‖gaussianSmoothedSum (P.classCoeff c) X - (X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) *
        (1 / 3 * (P.principalAlpha (4 / 3) + c⁻¹ * P.unitWeight (4 / 3) + c⁻¹ ^ 2 * P.conjAlpha (4 / 3)) *
          untwistedThetaResidue))‖ ≤ K * X ^ a := by
  obtain ⟨K₁, hK₁, h₁⟩ := P.principalUnitLayer_smoothed_main_term h2 a ha ha'
  obtain ⟨K₂, hK₂, h₂⟩ := P.cubicUnitLayer_smoothed_main_term a ha ha'
  obtain ⟨K₃, hK₃, h₃⟩ := P.conjugateUnitLayer_smoothed_main_term h2 a ha ha'
  rw [← P.principalAlpha_four_thirds] at h₁
  rw [← P.conjAlpha_four_thirds] at h₃
  refine ⟨‖(1 / 3 : ℂ)‖ * K₁ + ‖(1 / 3 : ℂ) * c⁻¹‖ * K₂ + ‖(1 / 3 : ℂ) * c⁻¹ ^ 2‖ * K₃, by positivity,
    fun X hX => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hsum : gaussianSmoothedSum (P.classCoeff c) X = 1 / 3 * gaussianSmoothedSum (P.unitCoeff 1) X +
      1 / 3 * c⁻¹ * gaussianSmoothedSum P.cubicUnitCoeff X +
        1 / 3 * c⁻¹ ^ 2 * gaussianSmoothedSum (P.unitCoeff P.chi⁻¹) X := by
    rw [show P.classCoeff c = fun A => 1 / 3 * P.unitCoeff 1 A + 1 / 3 * c⁻¹ * P.unitCoeff P.chi A +
      1 / 3 * c⁻¹ ^ 2 * P.unitCoeff P.chi⁻¹ A from funext (P.classCoeff_eq c hc)]
    exact gaussianSmoothedSum_combination (P.unitCoeff_bounded _) (P.unitCoeff_bounded _)
      (P.unitCoeff_bounded _) _ _ _ hX0
  rw [hsum]
  set R := untwistedThetaResidue
  set Y := (X : ℂ) ^ (2 / 3 : ℂ) * Complex.exp ((2 / 3 : ℂ) ^ 2)
  have e₁ := h₁ X hX
  have e₂ := h₂ X hX
  have e₃ := h₃ X hX
  have hsplit : 1 / 3 * gaussianSmoothedSum (P.unitCoeff 1) X + 1 / 3 * c⁻¹ * gaussianSmoothedSum P.cubicUnitCoeff X +
      1 / 3 * c⁻¹ ^ 2 * gaussianSmoothedSum (P.unitCoeff P.chi⁻¹) X -
      (X : ℂ) ^ (2 / 3 : ℂ) * (Complex.exp ((2 / 3 : ℂ) ^ 2) *
        (1 / 3 * (P.principalAlpha (4 / 3) + c⁻¹ * P.unitWeight (4 / 3) + c⁻¹ ^ 2 * P.conjAlpha (4 / 3)) * R)) =
      1 / 3 * (gaussianSmoothedSum (P.unitCoeff 1) X - (X : ℂ) ^ (2 / 3 : ℂ) *
          (Complex.exp ((2 / 3 : ℂ) ^ 2) * (P.principalAlpha (4 / 3) * R))) +
        1 / 3 * c⁻¹ * (gaussianSmoothedSum P.cubicUnitCoeff X - (X : ℂ) ^ (2 / 3 : ℂ) *
          (Complex.exp ((2 / 3 : ℂ) ^ 2) * (P.unitWeight (4 / 3) * R))) +
        1 / 3 * c⁻¹ ^ 2 * (gaussianSmoothedSum (P.unitCoeff P.chi⁻¹) X - (X : ℂ) ^ (2 / 3 : ℂ) *
          (Complex.exp ((2 / 3 : ℂ) ^ 2) * (P.conjAlpha (4 / 3) * R))) := by ring
  rw [hsplit]
  calc
    _ ≤ ‖(1 / 3 : ℂ)‖ * (K₁ * X ^ a) + ‖(1 / 3 : ℂ) * c⁻¹‖ * (K₂ * X ^ a) +
        ‖(1 / 3 : ℂ) * c⁻¹ ^ 2‖ * (K₃ * X ^ a) := by
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left e₁ (norm_nonneg _)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left e₂ (norm_nonneg _)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left e₃ (norm_nonneg _)
    _ = _ := by ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
