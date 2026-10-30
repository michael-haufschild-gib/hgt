import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonChargeIsBlindToTheRealPartsOfTheZeros
import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiFirstDefectJet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingXiCayleyTarget
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# The aperture modes carry the theta aperture charge

For a real aperture `κ` the **aperture mode** has atomic coefficients `y_n = n^{κ−1}`; the pole mode
is `κ = 1/2`. Put `a = 1/2 − κ`. Its two zero-side Dirichlet factors are the partial zeta sums
`X_N(1 − ρ + a)` and `X_N(ρ + a)` (`Wsummand_apertureMode`), so for every C² compact atom and
every horizon

`Q(f_κ) = Re Σ_ρ m_ρ ĝ(γ_ρ) conj ĝ(conj γ_ρ) X_N(1−ρ+a) X_N(ρ+a)`   (`weilQuad_apertureMode_eq_tsum`).

For `0 ≤ a < 1/2` both arguments lie in `Re s > 0` and differ from `1`, so each factor is
`ζ − B_N` (`dirichletPoly_shift_eq`). The pole parts of the two horizon boundaries multiply to the
**aperture charge** (`emPole_mul_emPole_aperture`)

`N^{2κ} / (κ² − (ρ − 1/2)²)`,

which at `κ = 1/2` is the pole charge `N/(ρ(1−ρ))`. With `ρ − 1/2 = i t_ρ` this is
`N^{2κ}/(κ² + t_ρ²)`: summed over the zeros it is `N^{2κ} Re(ξ'/ξ)(1/2+κ)/κ`
(`tsum_apertureCharge_re_eq`), the theta center-mixed current at aperture `κ` on the real axis.
The aperture modes are the atomic realization of the theta apertures. The factors `ζ(ρ + a)` that
remain at `κ < 1/2` are where the zeros to the right of `1/2 + κ` enter.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri Zeta23

/-- The **aperture mode** coefficients `n^{κ−1}`. -/
def apertureModeCoeff (κ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (κ - 1)

theorem apertureModeCoeff_eq_exp (κ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ((apertureModeCoeff κ n : ℝ) : ℂ) = Complex.exp ((κ - 1 : ℝ) * (Real.log n : ℂ)) := by
  rw [apertureModeCoeff, Real.rpow_def_of_pos (by exact_mod_cast hn), Complex.ofReal_exp]
  push_cast
  ring_nf

/-- At the spectral point of `ρ` the aperture-mode Dirichlet factor is `X_N(1 − ρ + a)`. -/
theorem dirichletPoly_apertureMode_gammaOf (κ : ℝ) (N : ℕ) (ρ : ℂ) :
    dirichletPoly N (apertureModeCoeff κ) (gammaOf ρ) =
      RHTower.dirichletPoly N (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ)) := by
  rw [dirichletPoly_gammaOf, RHTower.dirichletPoly]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  rw [apertureModeCoeff_eq_exp κ hn1, ← Complex.exp_add, natCast_cpow_neg_eq_exp hn1]
  congr 1
  push_cast
  ring

/-- The conjugate aperture-mode Dirichlet factor is `X_N(ρ + a)`. -/
theorem conj_dirichletPoly_apertureMode_conj_gammaOf (κ : ℝ) (N : ℕ) (ρ : ℂ) :
    conj (dirichletPoly N (apertureModeCoeff κ) (conj (gammaOf ρ))) =
      RHTower.dirichletPoly N (ρ + ((1 / 2 - κ : ℝ) : ℂ)) := by
  rw [conj_gammaOf, dirichletPoly_apertureMode_gammaOf, sub_sub_cancel,
    show (starRingEnd ℂ) ρ + ((1 / 2 - κ : ℝ) : ℂ) =
      (starRingEnd ℂ) (ρ + ((1 / 2 - κ : ℝ) : ℂ)) by rw [map_add, Complex.conj_ofReal],
    conj_dirichletPoly_conj]

/-- **The zero-side summand of an aperture mode** at any point of the zero configuration. -/
theorem Wsummand_apertureMode {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (κ : ℝ) (N : ℕ) (ρ : ℂ) :
    zetaZeroConfig.Wsummand (cx (atomicTest N (apertureModeCoeff κ) g))
        (cx (atomicTest N (apertureModeCoeff κ) g)) ρ =
      (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        (RHTower.dirichletPoly N (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ)) *
          RHTower.dirichletPoly N (ρ + ((1 / 2 - κ : ℝ) : ℂ))) := by
  rw [Wsummand_atomicTest zetaZeroConfig hg hgc, dirichletPoly_apertureMode_gammaOf,
    conj_dirichletPoly_apertureMode_conj_gammaOf]

/-- **Aperture-mode horizon law.** For every C² compact atom, every horizon and every real
aperture, Weil's form of the aperture mode is the zero sum of the bump factor against the two
shifted partial zeta sums. -/
theorem weilQuad_apertureMode_eq_tsum {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (κ : ℝ) (N : ℕ) :
    weilQuad (atomicTest N (apertureModeCoeff κ) g) =
      (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
          (paperFT (cx g) (gammaOf ρ) * conj (paperFT (cx g) (conj (gammaOf ρ)))) *
        (RHTower.dirichletPoly N (1 - ρ + ((1 / 2 - κ : ℝ) : ℂ)) *
          RHTower.dirichletPoly N (ρ + ((1 / 2 - κ : ℝ) : ℂ)))).re := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu
  rw [LogCells.weilQuad_eq_zetaW (contDiff_atomicTest hg N (apertureModeCoeff κ))
    (hasCompactSupport_atomicTest hgsupp N (apertureModeCoeff κ)), ZeroConfig.W]
  congr 1
  exact tsum_congr fun ρ => Wsummand_apertureMode hg.continuous hgc κ N ρ

/-! ### The shifted factors are `ζ − B_N` -/

/-- A nontrivial zero is not real. -/
theorem im_ne_zero_of_isNontrivialZero {ρ : ℂ} (hρ : IsNontrivialZero ρ) : ρ.im ≠ 0 := by
  obtain ⟨hz, h0, h1⟩ := hρ
  intro him
  have hreal : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  exact RHTower.riemannZeta_real_strip_ne_zero h0 h1 (hreal ▸ hz)

/-- For `0 ≤ a` and a nontrivial zero, `ρ + a` lies in `Re s > 0` and is not `1`; the shifted
partial sum is `ζ − B_N` there. -/
theorem dirichletPoly_shift_eq {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 0 ≤ a) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) :
    RHTower.dirichletPoly N (ρ + (a : ℂ)) =
      riemannZeta (ρ + (a : ℂ)) - horizonBoundary N (ρ + (a : ℂ)) := by
  have him := im_ne_zero_of_isNontrivialZero hρ
  refine dirichletPoly_eq_riemannZeta_sub_horizonBoundary hN ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re]; linarith [hρ.2.1]
  · intro h
    apply him
    have := congrArg Complex.im h
    simpa using this

/-- The reflected shifted partial sum is `ζ − B_N` as well. -/
theorem dirichletPoly_reflect_shift_eq {N : ℕ} (hN : 1 ≤ N) {a : ℝ} (ha : 0 ≤ a) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) :
    RHTower.dirichletPoly N (1 - ρ + (a : ℂ)) =
      riemannZeta (1 - ρ + (a : ℂ)) - horizonBoundary N (1 - ρ + (a : ℂ)) := by
  have him := im_ne_zero_of_isNontrivialZero hρ
  refine dirichletPoly_eq_riemannZeta_sub_horizonBoundary hN ?_ ?_
  · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith [hρ.2.2]
  · intro h
    apply him
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im] at this
    linarith

/-! ### The aperture charge -/

/-- **The aperture charge.** The pole parts of the two shifted horizon boundaries multiply to
`N^{2κ}/(κ² − (s − 1/2)²)`, `a = 1/2 − κ`. -/
theorem emPole_mul_emPole_aperture {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) (s : ℂ) :
    RHTower.emPole N (s + ((1 / 2 - κ : ℝ) : ℂ)) *
        RHTower.emPole N (1 - s + ((1 / 2 - κ : ℝ) : ℂ)) =
      (N : ℂ) ^ ((2 * κ : ℝ) : ℂ) / (κ ^ 2 - (s - 1 / 2) ^ 2) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : (N : ℂ) ^ (1 - (s + ((1 / 2 - κ : ℝ) : ℂ))) *
      (N : ℂ) ^ (1 - (1 - s + ((1 / 2 - κ : ℝ) : ℂ))) = (N : ℂ) ^ ((2 * κ : ℝ) : ℂ) := by
    rw [← cpow_add _ _ hN0]
    congr 1
    push_cast
    ring
  unfold RHTower.emPole
  rw [div_mul_div_comm, hpow]
  congr 1
  push_cast
  ring

/-- With `ρ − 1/2 = i t` the aperture denominator is `κ² + t²`. -/
theorem aperture_denominator_eq (κ : ℝ) (q : RHTower.XiZeroCopy) :
    (κ : ℂ) ^ 2 - ((q.1 : ℂ) - 1 / 2) ^ 2 = (κ : ℂ) ^ 2 + RHTower.xiSpectralPoint q ^ 2 := by
  rw [RHTower.xiSpectralPoint]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The flat aperture charge is the theta current at aperture `κ`.** Summed over the zero copies,
`Re Σ 1/(κ² + t²) = Re(ξ'/ξ)(1/2 + κ)/κ`, positive for every `κ > 0`. -/
theorem tsum_apertureCharge_re_eq {κ : ℝ} (hκ : 0 < κ) :
    (∑' q : RHTower.XiZeroCopy,
        1 / ((κ : ℂ) ^ 2 + RHTower.xiSpectralPoint q ^ 2)).re =
      RHTower.xiRealLogDeriv κ / κ := by
  have h := RHTower.xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment hκ
  have hterm : ∀ q : RHTower.XiZeroCopy,
      RHTower.xiShiftedReciprocalSquare (κ ^ (2 : ℕ)) q ^ (0 + 1) =
        1 / ((κ : ℂ) ^ 2 + RHTower.xiSpectralPoint q ^ 2) := by
    intro q
    have ht : RHTower.xiSpectralPoint q ≠ 0 := RHTower.xiSpectralPoint_ne_zero q
    simp only [zero_add, pow_one, RHTower.xiShiftedReciprocalSquare,
      RHTower.xiZeroCopyReciprocalSquare]
    push_cast
    field_simp
    ring
  rw [RHTower.xiShiftedReciprocalMoment] at h
  simp_rw [hterm] at h
  rw [h]
  field_simp

theorem tsum_apertureCharge_re_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < (∑' q : RHTower.XiZeroCopy,
        1 / ((κ : ℂ) ^ 2 + RHTower.xiSpectralPoint q ^ 2)).re := by
  rw [tsum_apertureCharge_re_eq hκ]
  exact div_pos (RHTower.xiRealLogDeriv_pos hκ) hκ

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
