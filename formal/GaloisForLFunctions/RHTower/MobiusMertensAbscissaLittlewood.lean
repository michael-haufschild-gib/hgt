import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood

/-!
# Littlewood's Mertens bound at the zero abscissa

Zero-freeness right of a level `Θ ∈ [1/2, 1]` makes the regular reciprocal zeta holomorphic and
subpolynomially bounded on every strip strictly right of `Θ`.  Shifting the exact smoothed Perron
formula into those strips and applying the universal Littlewood law gives

`M(N) = O(N^(Θ + ε))`

for every positive `ε` (`mobiusMertens_subpower_of_zeroFree`).

At `Θ = zetaZeroAbscissa` the zero-free hypothesis is the unconditional
`riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`, so the classical Littlewood estimate at the true
zeta zero frontier is a theorem here (`mobiusMertens_subpower_zetaZeroAbscissa`).
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

open Sieve

/-- Right of a zero-free frontier the exact smoothed Möbius Perron formula may be shifted to every
line strictly right of `Θ`. -/
theorem mobius_perron_shift_of_zeroFree {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    {dl a N H : ℝ} (hdl : 0 < dl) (hdl1 : dl < 1) (ha : 0 < a)
    (hN : 0 < N) (hH : 0 < H) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) *
          ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
      ∫ y : ℝ, invZeta ((((Θ + dl : ℝ)) : ℂ) + (y : ℝ) * I) *
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((((Θ + dl : ℝ)) : ℂ) + (y : ℝ) * I) := by
  have hc : 0 < Θ + dl := by linarith
  have hc2 : Θ + dl ≤ 2 := by linarith
  obtain ⟨Kb, hKb, hFdiff, hFbd⟩ :=
    exists_invZeta_shift_data_of_zeroFree hΘ hΘ1 hzf hdl hdl1 ha (2 : ℝ)
  calc
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) *
          ((smoothWeight N H (n : ℝ) : ℝ) : ℂ)) =
        ∫ y : ℝ, invZeta ((2 : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((2 : ℂ) + (y : ℝ) * I) :=
      tsum_moebius_smoothWeight_eq_invZeta_integral hN hH (by norm_num)
    _ = ∫ y : ℝ, invZeta ((((Θ + dl : ℝ)) : ℂ) + (y : ℝ) * I) *
          mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((((Θ + dl : ℝ)) : ℂ) + (y : ℝ) * I) :=
      integral_mul_mellin_smoothWeight_shift hN hH hc hc2 hFdiff hKb ha.le hFbd

/-- **Littlewood's Mertens bound right of a zero-free frontier.** -/
theorem mobiusMertens_subpower_of_zeroFree {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (Θ + ε) := by
  have hsubpower := partialSumSeq_subpower_of_smoothPerron
    (b := fun n => (ArithmeticFunction.moebius n : ℂ)) (Θ := Θ)
    (fun n => by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n))
    (by linarith)
    (fun dl a hdl hdl1 ha => by
      obtain ⟨Kb, hKb, hFdiff, hFbd⟩ :=
        exists_invZeta_shift_data_of_zeroFree hΘ hΘ1 hzf hdl hdl1 ha (2 : ℝ)
      refine ⟨invZeta, Kb, hKb, ?_, ?_⟩
      · intro y
        have hline : (((Θ + dl : ℝ)) : ℂ) + (y : ℝ) * I ∈ verticalStrip (Θ + dl) 2 :=
          line_mem_verticalStrip le_rfl (by linarith) y
        simpa using hFbd _ hline
      · intro N H hN hH
        have hc : 0 < Θ + dl := by linarith
        have hc2 : Θ + dl ≤ 2 := by linarith
        refine ⟨integrable_mul_mellin_smoothWeight_line hN hH hc hFdiff.continuousOn
          hKb ha.le hFbd le_rfl hc2, ?_⟩
        exact mobius_perron_shift_of_zeroFree hΘ hΘ1 hzf hdl hdl1 ha hN hH)
  obtain ⟨C, hC, hbound⟩ := hsubpower ε hε
  refine ⟨C, hC.le, fun N => ?_⟩
  simpa [partialSumSeq, mobiusMertensPartialSum, mobiusComplexCoefficient] using hbound N

/-- **Littlewood's Mertens bound at the zeta zero abscissa**, unconditionally. -/
theorem mobiusMertens_subpower_zetaZeroAbscissa (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖mobiusMertensPartialSum N‖ ≤ C * ((N : ℝ) + 1) ^ (zetaZeroAbscissa + ε) :=
  mobiusMertens_subpower_of_zeroFree half_le_zetaZeroAbscissa zetaZeroAbscissa_le_one
    (fun _z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt hz) ε hε

end RHTower
