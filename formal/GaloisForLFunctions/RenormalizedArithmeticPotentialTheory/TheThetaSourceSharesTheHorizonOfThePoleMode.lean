import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleModeMeetsTheZerosOnlyAtTheHorizon
import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionMellin
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The theta source shares the horizon of the atomic pole mode

Every theta atom is the seed atom `f₁ = thetaCuspSourceTerm · 1` translated to `−log n` with the
pole-mode weight `n^{-1/2}` (`thetaCuspSourceTerm_eq_poleMode`). The theta source truncated at
the horizon `N` is therefore the pole mode of the seed atom, mirrored. Its transform factors
(`paperFT_thetaHorizonSource`) as `f̂₁(z) Σ_{n≤N} n^{-1/2} e^{-iz log n}`, and at the spectral
point of a nontrivial zero `ρ` the Dirichlet factor is `X_N(ρ) = −B_N(ρ)`:

* **Theta horizon law** (`paperFT_thetaHorizonSource_gammaOf`):
  `ĥ_{Φ_N}(γ_ρ) = −f̂₁(γ_ρ) B_N(ρ)`.
* **The tail beyond the horizon** (`paperFT_thetaTail_gammaOf`): the complete source has
  transform `Ξ`, which vanishes at `γ_ρ`; hence the theta tail `Φ − Φ_N` has transform
  `f̂₁(γ_ρ) B_N(ρ)` there.

The atomic pole mode of `ThePoleModeMeetsTheZerosOnlyAtTheHorizon` carries `B_N(1 − ρ)` at the
same zero. Theta and atomic positivity read one and the same Euler–Maclaurin horizon boundary,
from the two sides of the functional equation.
-/

noncomputable section

open Complex Finset MeasureTheory

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticCastelnuovoSeveri Zeta23

/-- The theta source truncated at the horizon `N`. -/
def thetaHorizonSource (N : ℕ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 N, RHTower.thetaCuspSourceTerm x n

/-- `√n = exp(log n / 2)` for `n ≥ 1`. -/
theorem sqrt_natCast_eq_exp {n : ℕ} (hn : 1 ≤ n) : Real.sqrt n = Real.exp (Real.log n / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  ring_nf

/-- Every theta atom is the seed atom at `−log n` with pole-mode weight `n^{-1/2}`. -/
theorem thetaCuspSourceTerm_eq_poleMode {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    RHTower.thetaCuspSourceTerm x n =
      poleModeCoeff n * RHTower.thetaCuspSourceTerm (x + Real.log n) 1 := by
  rw [RHTower.thetaCuspSourceTerm_shift_one (by omega) x, poleModeCoeff,
    ← sqrt_natCast_eq_exp hn, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)), one_mul]

/-- The truncated theta source is the mirrored pole mode of the seed atom. -/
theorem thetaHorizonSource_eq (N : ℕ) (x : ℝ) :
    thetaHorizonSource N x =
      ∑ n ∈ Icc 1 N, poleModeCoeff n * RHTower.thetaCuspSourceTerm (x + Real.log n) 1 :=
  sum_congr rfl fun _ hn => thetaCuspSourceTerm_eq_poleMode (mem_Icc.mp hn).1 x

/-- The seed atom `f₁` as a complex test. -/
abbrev thetaSeedC : ℝ → ℂ := fun x => (RHTower.thetaCuspSourceTerm x 1 : ℂ)

/-- The transform of one theta atom: `n^{-1/2} e^{-iz log n} f̂₁(z)`. -/
theorem paperFT_thetaCuspSourceTerm {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    paperFT (fun x => (RHTower.thetaCuspSourceTerm x n : ℂ)) z =
      (poleModeCoeff n : ℂ) * cexp (-(I * z * (Real.log n : ℂ))) * paperFT thetaSeedC z := by
  have hfun : (fun x => (RHTower.thetaCuspSourceTerm x n : ℂ)) =
      fun x => (poleModeCoeff n : ℂ) *
        ArithmeticCastelnuovoSeveri.translate (-Real.log n) thetaSeedC x := by
    funext x
    simp only [ArithmeticCastelnuovoSeveri.translate, thetaSeedC, sub_neg_eq_add]
    rw [thetaCuspSourceTerm_eq_poleMode hn x]
    push_cast
    ring
  have hlin : paperFT (fun x => (poleModeCoeff n : ℂ) *
        ArithmeticCastelnuovoSeveri.translate (-Real.log n) thetaSeedC x) z =
      (poleModeCoeff n : ℂ) *
        paperFT (ArithmeticCastelnuovoSeveri.translate (-Real.log n) thetaSeedC) z := by
    unfold paperFT
    rw [← integral_const_mul]
    congr 1
    funext u
    ring
  rw [hfun, hlin, paperFT_translate]
  push_cast
  ring_nf

/-- Integrability of one theta atom against `e^{izu}` for `Im z < 5/2`. -/
theorem integrable_thetaCuspSourceTerm_mul_cexp {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z.im < 5 / 2) :
    Integrable fun u : ℝ => (RHTower.thetaCuspSourceTerm u n : ℂ) * cexp (I * z * u) := by
  have hw : -(5 / 2) < (I * z).re := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    linarith
  refine (RHTower.integrable_cexp_mul_thetaCuspSourceTerm (I * z) hw n (by omega)).congr ?_
  filter_upwards with u
  ring

/-- **Transform of the truncated theta source**: `f̂₁(z) Σ_{n≤N} n^{-1/2} e^{-iz log n}`. -/
theorem paperFT_thetaHorizonSource (N : ℕ) {z : ℂ} (hz : z.im < 5 / 2) :
    paperFT (fun x => (thetaHorizonSource N x : ℂ)) z =
      paperFT thetaSeedC z *
        ∑ n ∈ Icc 1 N, (poleModeCoeff n : ℂ) * cexp (-(I * z * (Real.log n : ℂ))) := by
  have hsum : (fun u : ℝ => (thetaHorizonSource N u : ℂ) * cexp (I * z * u)) =
      fun u => ∑ n ∈ Icc 1 N, (RHTower.thetaCuspSourceTerm u n : ℂ) * cexp (I * z * u) := by
    funext u
    simp only [thetaHorizonSource]
    push_cast
    rw [sum_mul]
  unfold paperFT
  rw [hsum, integral_finsetSum _ fun n hn =>
    integrable_thetaCuspSourceTerm_mul_cexp (mem_Icc.mp hn).1 hz, mul_sum]
  refine sum_congr rfl fun n hn => ?_
  have h := paperFT_thetaCuspSourceTerm (mem_Icc.mp hn).1 z
  unfold paperFT at h
  rw [h]
  ring

/-- The spectral point satisfies `I γ_ρ = ρ − 1/2`. -/
theorem I_mul_gammaOf (ρ : ℂ) : I * gammaOf ρ = ρ - 1 / 2 := by
  unfold gammaOf
  field_simp

/-- At a spectral point the theta Dirichlet factor is `X_N(ρ)`. -/
theorem sum_poleMode_cexp_gammaOf (N : ℕ) (ρ : ℂ) :
    ∑ n ∈ Icc 1 N, (poleModeCoeff n : ℂ) * cexp (-(I * gammaOf ρ * (Real.log n : ℂ))) =
      RHTower.dirichletPoly N ρ := by
  rw [RHTower.dirichletPoly]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [poleModeCoeff_eq_exp hn1, I_mul_gammaOf, ← Complex.exp_add, natCast_cpow_neg_eq_exp hn1]
  congr 1
  ring

theorem gammaOf_im_lt {ρ : ℂ} (h0 : 0 < ρ.re) : (gammaOf ρ).im < 5 / 2 := by
  have h : (gammaOf ρ).im = -(ρ.re - 1 / 2) := by
    simp [gammaOf, Complex.div_I]
  rw [h]
  linarith

/-- **Theta horizon law.** At every nontrivial zero the truncated theta source has transform
`−f̂₁(γ_ρ) B_N(ρ)`. -/
theorem paperFT_thetaHorizonSource_gammaOf {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) :
    paperFT (fun x => (thetaHorizonSource N x : ℂ)) (gammaOf ρ) =
      -(paperFT thetaSeedC (gammaOf ρ) * horizonBoundary N ρ) := by
  obtain ⟨hz, h0, h1, -, -, -, -⟩ := nontrivialZero_facts hρ
  rw [paperFT_thetaHorizonSource N (gammaOf_im_lt h0), sum_poleMode_cexp_gammaOf,
    dirichletPoly_eq_neg_horizonBoundary hN h0 h1 hz]
  ring

/-- The complete theta source has transform `Ξ(−z)`, which vanishes at every spectral point. -/
theorem paperFT_thetaCuspFullSource_gammaOf {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    paperFT (fun x => (RHTower.thetaCuspFullSource x : ℂ)) (gammaOf ρ) = 0 := by
  obtain ⟨-, -, -, hz', h0', -, -⟩ := nontrivialZero_facts hρ
  have hFL : paperFT (fun x => (RHTower.thetaCuspFullSource x : ℂ)) (gammaOf ρ) =
      RHTower.thetaCuspFourierLaplace (-gammaOf ρ) := by
    unfold paperFT RHTower.thetaCuspFourierLaplace RHTower.thetaCuspFourierLaplaceIntegrand
    congr 1
    funext x
    rw [mul_comm]
    congr 2
    ring
  have harg : (1 / 2 : ℂ) + -gammaOf ρ * I = 1 - ρ := by
    have := I_mul_gammaOf ρ
    linear_combination -this
  rw [hFL, RHTower.HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all, RHTower.XiC, harg]
  refine RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hz', fun n hn => ?_⟩
  have := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.natCast_re,
    Complex.one_re] at this
  norm_num at this
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Complex.sub_re, Complex.one_re] at h0'
  linarith

/-- **The theta tail carries the horizon boundary.** At every nontrivial zero the tail
`Φ − Φ_N` beyond the horizon has transform `f̂₁(γ_ρ) B_N(ρ)`. -/
theorem paperFT_thetaTail_gammaOf {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    paperFT (fun x => ((RHTower.thetaCuspFullSource x - thetaHorizonSource N x : ℝ) : ℂ))
        (gammaOf ρ) =
      paperFT thetaSeedC (gammaOf ρ) * horizonBoundary N ρ := by
  obtain ⟨-, h0, -, -, -, -, -⟩ := nontrivialZero_facts hρ
  have hz := gammaOf_im_lt h0
  have hfull : Integrable fun u : ℝ =>
      (RHTower.thetaCuspFullSource u : ℂ) * cexp (I * gammaOf ρ * u) := by
    refine (RHTower.HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceIntegrand_all
      (-gammaOf ρ)).congr ?_
    filter_upwards with u
    simp only [RHTower.thetaCuspFourierLaplaceIntegrand]
    rw [mul_comm]
    congr 2
    ring
  have htrunc : Integrable fun u : ℝ =>
      (thetaHorizonSource N u : ℂ) * cexp (I * gammaOf ρ * u) := by
    have : (fun u : ℝ => (thetaHorizonSource N u : ℂ) * cexp (I * gammaOf ρ * u)) =
        fun u => ∑ n ∈ Icc 1 N,
          (RHTower.thetaCuspSourceTerm u n : ℂ) * cexp (I * gammaOf ρ * u) := by
      funext u
      simp only [thetaHorizonSource]
      push_cast
      rw [sum_mul]
    rw [this]
    exact integrable_finsetSum _ fun n hn =>
      integrable_thetaCuspSourceTerm_mul_cexp (mem_Icc.mp hn).1 hz
  have hsplit : paperFT (fun x => ((RHTower.thetaCuspFullSource x - thetaHorizonSource N x : ℝ) : ℂ))
      (gammaOf ρ) =
      paperFT (fun x => (RHTower.thetaCuspFullSource x : ℂ)) (gammaOf ρ) -
        paperFT (fun x => (thetaHorizonSource N x : ℂ)) (gammaOf ρ) := by
    unfold paperFT
    rw [← integral_sub hfull htrunc]
    congr 1
    funext u
    push_cast
    ring
  rw [hsplit, paperFT_thetaCuspFullSource_gammaOf hρ, paperFT_thetaHorizonSource_gammaOf hN hρ]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
