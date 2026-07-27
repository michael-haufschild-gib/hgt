import GaloisForLFunctions.RHTower.MobiusPositiveExcursion
import GaloisForLFunctions.RHTower.TwistedMobiusZeroObstruction
import GaloisForLFunctions.RHTower.DirichletLZeroExistence

/-!
# Positive excursions of the twisted Hermitian convolution recur

At arbitrary primitive conductor the same dichotomy as at conductor one applies.  If the twisted
Hermitian mixed convolution coefficients were positive only finitely often, the positive part of the
radial series would be a polynomial, so the twisted source would be bounded near the boundary: decay
at exponent `0`.  The Mellin obstruction forbids that, because `L(·,χ)` has a zero strictly to the
right of `0`.

The zero supply is unconditional: it comes from the Hadamard argument for the completed L-function
together with the functional equation.
-/

open Complex
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace RHTower

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- **Finitely many positive twisted coefficients would bound the source.** -/
theorem twistedMobiusLaplaceDecay_zero_of_nonpos_outside (χ : DirichletCharacter ℂ N)
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ)
    (hS : ∀ M : ℕ, M ∉ S → (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re ≤ 0) :
    TwistedMobiusLaplaceDecay χ 0 := by
  classical
  set B : ℝ := ∑ M ∈ S, max ((mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re) 0 with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun M _ => le_max_right _ _
  refine ⟨B ^ ((2 * (k : ℝ))⁻¹), 1, Real.rpow_nonneg hB0 _, one_pos, ?_⟩
  intro x hx _
  set r : ℝ := Real.exp (-x) with hr
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    rw [hr]
    exact Real.exp_le_one_iff.mpr (by linarith)
  set bfun : ℕ → ℝ := fun M =>
    if M ∈ S then max ((mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re) 0 else 0 with hbdef
  have hbnonneg : ∀ M, 0 ≤ bfun M := by
    intro M
    rw [hbdef]
    by_cases hM : M ∈ S <;> simp [hM]
  have hupper : ∀ M : ℕ,
      (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re ≤ bfun M := by
    intro M
    rw [hbdef]
    by_cases hM : M ∈ S
    · simp only [hM, if_pos]
      exact le_max_left _ _
    · simp only [hM, if_neg, not_false_iff]
      exact hS M hM
  have hzero : ∀ M : ℕ, M ∉ S → bfun M * r ^ M = 0 := by
    intro M hM
    rw [hbdef]
    simp [hM]
  have hbsum : Summable fun M : ℕ => bfun M * r ^ M :=
    summable_of_ne_finset_zero hzero
  have htsum : (∑' M : ℕ, bfun M * r ^ M) ≤ B := by
    rw [tsum_eq_sum hzero, hBdef]
    refine Finset.sum_le_sum fun M hM => ?_
    have hrn : r ^ M ≤ 1 := pow_le_one₀ hr0 hr1
    have hbn : 0 ≤ bfun M := hbnonneg M
    calc bfun M * r ^ M ≤ bfun M * 1 := mul_le_mul_of_nonneg_left hrn hbn
      _ = bfun M := mul_one _
      _ = max ((mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re) 0 := by
          rw [hbdef]; simp [hM]
  have hR8 := norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper
    (↗χ * ↗μ) k r hr0 (summable_norm_twistedCoeff_mul_pow χ hx) bfun hupper hbsum
  have hbound : ‖(∑' M : ℕ, (↗χ * ↗μ) M * ((r : ℝ) : ℂ) ^ M) ^ k‖ ^ 2 ≤ B :=
    hR8.trans htsum
  have hroot := norm_le_rpow_of_norm_pow_sq_le hk hbound
  rw [twistedMobiusLaplaceTransform_eq_tsum_pow]
  refine hroot.trans (le_of_eq ?_)
  rw [neg_zero, Real.rpow_zero, mul_one]

/-- **Twisted positive excursions recur.**  For every order `k` and every finite set of indices,
some index outside it carries a positive twisted Hermitian coefficient. -/
theorem exists_notMem_pos_twistedMixedAdditiveConvolutionPower
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ) :
    ∃ M : ℕ, M ∉ S ∧ 0 < (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re := by
  by_contra hcon
  have hnp : ∀ M : ℕ, M ∉ S →
      (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re ≤ 0 := by
    intro M hM
    by_contra hpos
    exact hcon ⟨M, hM, not_le.mp hpos⟩
  obtain ⟨ρ, hre, hzero⟩ := exists_LFunction_eq_zero_pos_re hχ hprim
  exact not_twistedMobiusLaplaceDecay_of_LFunction_eq_zero hχ le_rfl hre hzero
    (twistedMobiusLaplaceDecay_zero_of_nonpos_outside χ hk S hnp)

/-- The set of indices carrying a positive twisted coefficient is infinite. -/
theorem infinite_pos_twistedMixedAdditiveConvolutionPower
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {k : ℕ} (hk : 0 < k) :
    {M : ℕ | 0 < (mixedAdditiveConvolutionPower (↗χ * ↗μ) k M).re}.Infinite := by
  intro hfin
  obtain ⟨M, hMmem, hMpos⟩ :=
    exists_notMem_pos_twistedMixedAdditiveConvolutionPower hχ hprim hk hfin.toFinset
  exact hMmem (hfin.mem_toFinset.mpr hMpos)

end RHTower
