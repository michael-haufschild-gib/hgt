import GaloisForLFunctions.InfiniteRankWeilTheory.TheExceptionalCoordinate
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerNormOneOffHasLinearCounting

/-!
# The calibration battery

Each step of infinite-rank Weil theory is tested against models in which some arithmetic structure
is present and the conclusion fails.

* **Fakes fail through the crude count.** A finite reflection-closed tower with an outer mode — the
  golden fake curve (`q = 5`, eigenvalues `φ^{±1}`, integral counts, rational zeta, functional
  equation), or any graph black hole without damping — has unbounded traces on every thick set of
  levels (`not_forall_thick_trace_le_of_outer`, `goldenDatum_not_thick_trace_bounded`). The functional
  equation and integrality are present; what fails is the crude count, which is exactly the step the
  curve proof gets from Stepanov.
* **Euler products do not give AAL.** The integer-norm Beurling one-off (integer norms, natural
  coefficients, an Euler product, linear counting, holomorphic on `Re s > ½`) has zero configuration on
  `Re s > ½` equal to one pair `3/5 ± iγ`: it satisfies ZAL and violates AAL
  (`integerNormOneOff_zal_not_aal`). What it lacks is the functional equation on `Re s = ½`.
* Together with `asymptoticAbscissaLaw_of_vertical_period` (periodic heads: AAL is automatic) and
  `not_asymptoticAbscissaLaw_coshModelZeros` (functional equation, order one, reality: AAL fails), this
  answers which exceptional-set bounds self-improve: none from the functional equation alone, none
  from an Euler product with positive coefficients and linear counting alone, every one under vertical
  periodicity.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- **A finite tower with an outer mode fails the crude count on every thick set.** -/
theorem not_forall_thick_trace_le_of_outer {ι : Type*} [Fintype ι] (z : ι → ℂ) {i : ι}
    (hi : 1 < ‖z i‖) {G : Set ℕ} (hG : Thick G) (C : ℝ) :
    ¬ ∀ ν ∈ G, ‖levelSum z (fun _ => 1) ν‖ ≤ C := by
  classical
  intro hbd
  have h0 := mergedWeight_eq_zero_of_thick_bound z (fun _ => (1 : ℂ)) Summable.of_finite
    zero_le_one (wellFoundedAbove_of_finite _ _) hG (C := C)
    (fun ν hν => by rw [one_pow, mul_one]; exact hbd ν hν) hi Finset.univ
    (fun _ _ => Finset.mem_univ _)
  have hpos : (0 : ℝ) < ((Finset.univ.filter fun l => z l = z i).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨i, by simp⟩
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h0
  exact hpos.ne' (by exact_mod_cast h0)

open ArithmeticCastelnuovoSeveri Real in
/-- **The golden fake fails the crude count.** Its traces `φʲ + φ⁻ʲ` are unbounded on every thick set
of levels. -/
theorem goldenDatum_not_thick_trace_bounded {G : Set ℕ} (hG : Thick G) (C : ℝ) :
    ¬ ∀ n ∈ G, |goldenDatum.trace n| ≤ C := by
  intro hbd
  have hφ : 1 < ‖goldenDatum.β 0‖ := by
    show 1 < ‖((goldenRatio : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_of_nonneg goldenRatio_pos.le]
    exact one_lt_goldenRatio
  refine not_forall_thick_trace_le_of_outer goldenDatum.toWeilTower.z hφ hG C fun n hn => ?_
  rw [levelSum_toWeilTower_one, goldenDatum.powerSum_eq_trace, Complex.norm_real, Real.norm_eq_abs]
  exact hbd n hn

open ArithmeticPositiveDuality.IntegerNormOneOff in
/-- **An Euler product with integer norms and linear counting violates AAL.** For every `γ` there is
an integer-norm Beurling system whose zero configuration on `Re s > ½` satisfies ZAL and violates AAL. -/
theorem integerNormOneOff_zal_not_aal (γ : ℝ) :
    ∃ q a : ℕ → ℕ, (∀ k, 2 ≤ q k) ∧ ∃ F : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasProd (fun k => (1 - cexp (-(s * Real.log (q k))))⁻¹) (F s) ∧
        LSeriesHasSum (fun n => (a n : ℂ)) s (F s)) ∧
      ZerosApproachLine (fun s : {s : ℂ // 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} => (s : ℂ)) ∧
      ¬ AsymptoticAbscissaLaw (fun s : {s : ℂ // 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} => (s : ℂ)) := by
  obtain ⟨q, a, hq, F, A, -, hF, -, -, hzeros⟩ := exists_integer_norm_linear_count_one_off γ
  have hfin : ∀ c : ℝ, {s : {s : ℂ // 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} | c < (s : ℂ).re}.Finite := by
    intro c
    refine ((Set.toFinite ({(3 / 5 : ℂ) + (γ : ℂ) * I, (3 / 5 : ℂ) - (γ : ℂ) * I} : Set ℂ)).preimage
      Subtype.val_injective.injOn).subset fun s _ => ?_
    have : (s : ℂ) ∈ {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} := s.2
    rw [hzeros] at this
    exact this
  refine ⟨q, a, hq, F, hF, fun h _ => hfin _, fun hA => ?_⟩
  have hmem : (3 / 5 : ℂ) + (γ : ℂ) * I ∈ {s : ℂ | 1 / 2 < s.re ∧ s ≠ 1 ∧ F s = 0} := by
    rw [hzeros]; exact Set.mem_insert _ _
  have := hA (1 / 20) (by norm_num) (hfin _) ⟨_, hmem⟩
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im] at this
  norm_num at this

end GaloisForLFunctions.InfiniteRankWeilTheory
