import GaloisForLFunctions.ConjugateDiagonalGeometry.GaussianLogarithmicAsymptotic
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogDerivativeGrowth
import GaloisForLFunctions.RHTower.ZetaNarrowCountControl

/-!
# Gaussian occurrences and the Xi divisor

Both zero indices retain the same analytic multiplicity. Their canonical
bijection transports the Lorentzian mass bound to the Gaussian explicit formula.
The explicit formula also transfers the arithmetic logarithmic main term to
the actual multiplicity-weighted zero sum.
-/

open Complex Filter Set Topology
noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open RiemannGaussian _root_.RHTower

/-- The distinct nontrivial zeta zeros are exactly the support of Xi's divisor. -/
def gaussianZeroSupportEquiv : NontrivialZetaZero ≃ XiDivisorSupport where
  toFun ρ := ⟨ρ.1, mem_xi_divisor_support_of_eq_zero
    ((xi_eq_zero_iff ρ.zero_lt_re ρ.2.2.2).mpr ρ.2.1)⟩
  invFun ρ := by
    have hξ := xi_eq_zero_of_mem_divisor_support ρ
    have hs := xi_zero_re_mem_open_unit hξ
    have hz := xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hξ
    refine ⟨ρ.1, hz.1, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      exact hz.2 n (by simpa only [neg_mul] using hn)
    · intro hone
      have hh := hs.2
      rw [hone, Complex.one_re] at hh
      exact (lt_irrefl (1 : ℝ)) hh
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem gaussianZeroSupportEquiv_coe (ρ : NontrivialZetaZero) :
    ((gaussianZeroSupportEquiv ρ : XiDivisorSupport) : ℂ) = ρ.1 := rfl

/-- The finite fibers agree in cardinality, including repeated zeros. -/
theorem gaussianZeroSupport_multiplicity (ρ : NontrivialZetaZero) :
    Int.toNat ((MeromorphicOn.divisor xi Set.univ)
      (gaussianZeroSupportEquiv ρ : ℂ)) = analyticZetaZeroMultiplicity ρ := by
  rw [gaussianZeroSupportEquiv_coe, toNat_divisor_xi_eq,
    xi_analyticOrderAt_eq_riemannZeta_of_mem_strip ⟨ρ.zero_lt_re, ρ.re_lt_one⟩]
  rfl

/-- The Gaussian occurrence index is the actual Xi divisor with its copies. -/
def gaussianZeroCopyEquiv :
    NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity ≃ XiZeroCopy :=
  Equiv.sigmaCongr gaussianZeroSupportEquiv
    (fun ρ => finCongr (gaussianZeroSupport_multiplicity ρ).symm)

@[simp] theorem gaussianZeroCopyEquiv_coe
    (q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) :
    ((gaussianZeroCopyEquiv q).1 : ℂ) = q.1.1 := rfl

/-- Lorentzian summability is independent of the choice of zero index. -/
theorem summable_gaussianZeroLorentz (T : ℝ) :
    Summable (fun q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      1 / (1 + (T - q.1.1.im) ^ 2)) := by
  exact (summable_lorentzMassTerm T).comp_injective gaussianZeroCopyEquiv.injective

/-- Exact transport of the Lorentzian mass, with every analytic multiplicity. -/
theorem tsum_gaussianZeroLorentz (T : ℝ) :
    (∑' q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      1 / (1 + (T - q.1.1.im) ^ 2)) = lorentzMass T := by
  exact gaussianZeroCopyEquiv.tsum_eq (lorentzMassTerm T)

/-- The real contribution of an occurrence records its horizontal depth and
its displacement from the Gaussian center. -/
theorem gaussianZeroSummand_re (ε T : ℝ)
    (q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) :
    (zetaGaussianZeroSummand analyticZetaZeroMultiplicity ε T q).re =
      offAxisSingleContribution ε T q.1.1.im (1 / 2 - q.1.1.re) := by
  have he : zetaSpectralCoordinate q.1.1 =
      ((zetaSpectralCoordinate q.1.1).re : ℂ) +
        ((zetaSpectralCoordinate q.1.1).im : ℂ) * I :=
    (Complex.re_add_im (zetaSpectralCoordinate q.1.1)).symm
  unfold zetaGaussianZeroSummand
  rw [he, complexTranslatedGaussian_re_eq_offAxisSingleContribution,
    zetaSpectralCoordinate_re, zetaSpectralCoordinate_im]

/-- A bounded ordinate window contains finitely many Gaussian occurrences,
including all multiplicity slots. -/
theorem finite_gaussianZeroCopies_near (T : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    {q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity |
      |q.1.1.im - T| ≤ R}.Finite := by
  let w : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity → ℝ :=
    fun q => 1 / (1 + (T - q.1.1.im) ^ 2)
  have hw : Summable w := summable_gaussianZeroLorentz T
  have hc : 0 < 1 / (1 + R ^ 2) := by positivity
  have he := hw.tendsto_cofinite_zero.eventually_lt_const hc
  have hfin := Filter.mem_cofinite.mp he
  apply hfin.subset
  intro q hq
  change ¬ w q < 1 / (1 + R ^ 2)
  apply not_lt.mpr
  have hs : (T - q.1.1.im) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs, abs_sub_comm]
    exact pow_le_pow_left₀ (abs_nonneg _) hq 2
  exact one_div_le_one_div_of_le (by positivity) (by linarith only [hs])

/-- The explicit Lorentzian majorant is at most a fixed multiple of `log T`
on the positive high-height ray. -/
theorem gaussianZeroLorentz_le_log {T : ℝ} (hT : 8 ≤ T) :
    (∑' q : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      1 / (1 + (T - q.1.1.im) ^ 2)) ≤
        (8 * (|xiLineTwoLogDerivConstant| + 2)) * Real.log T := by
  rw [tsum_gaussianZeroLorentz]
  have hl : 1 ≤ Real.log T := by
    have he : Real.exp 1 ≤ T := by
      have he := Real.exp_one_lt_d9
      linarith only [he, hT]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hlog : Real.log (|T| + 4) ≤ 2 * Real.log T := by
    rw [abs_of_nonneg (by linarith only [hT] : 0 ≤ T)]
    have hh := Real.log_le_log (by linarith only [hT] : 0 < T + 4)
      (show T + 4 ≤ 2 * T by linarith only [hT])
    rw [Real.log_mul (by norm_num) (by linarith only [hT] : T ≠ 0)] at hh
    have h2 : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [hh]
    linarith only [hh, h2, hl]
  have hC : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| * Real.log T := by
    have hh := mul_le_mul_of_nonneg_left hl (abs_nonneg xiLineTwoLogDerivConstant)
    simp only [mul_one] at hh
    exact (le_abs_self xiLineTwoLogDerivConstant).trans hh
  exact (lorentzMass_le_log T).trans (by nlinarith only [hlog, hC])

/-- The actual translated Gaussian zero sum has the logarithmic coefficient
predicted by its archimedean mass. -/
theorem tendsto_canonicalZetaGaussianZeroSum_log_normalized {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T => canonicalZetaGaussianZeroSum ε T / Real.log |T|)
      (Filter.comap abs atTop) (𝓝 (Real.sqrt (Real.pi / ε) / (2 * Real.pi))) := by
  have hh := (tendsto_gaussianArithmeticExplicitFormula_log_normalized hε).div_const 2
  convert hh using 1
  · funext T
    rw [gaussianArithmeticExplicitFormula_eq_canonical hε T]
    unfold canonicalZetaSymmetricGaussianZeroSum
    ring
  · congr 1
    rw [div_div, mul_comm Real.pi (2 : ℝ)]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussianZeroCopyEquiv
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tsum_gaussianZeroLorentz

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.gaussianZeroLorentz_le_log

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_canonicalZetaGaussianZeroSum_log_normalized
