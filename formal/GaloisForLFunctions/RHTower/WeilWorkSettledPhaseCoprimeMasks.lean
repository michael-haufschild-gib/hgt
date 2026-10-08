import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeFourier
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDeletionMasks
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Coprime deletion respects the actual Dirichlet convolution and exponential

Only the canonical masked constant sequence is identified with a principal
Dirichlet L-function. No Euler product is assumed for the unknown source.
-/

open Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

def coprimePart (Q : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ := (coprimeMask Q n : ℂ) * f n

theorem coprimeMask_mul (Q a b : ℕ) :
    coprimeMask Q (a * b) = coprimeMask Q a * coprimeMask Q b := by
  unfold coprimeMask
  by_cases ha : a.Coprime Q
  · by_cases hb : b.Coprime Q
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨ha, hb⟩), if_pos ha, if_pos hb, one_mul]
    · have hab : ¬(a * b).Coprime Q := fun h => hb (Nat.coprime_mul_iff_left.mp h).2
      rw [if_neg hab, if_pos ha, if_neg hb, mul_zero]
  · have hab : ¬(a * b).Coprime Q := fun h => ha (Nat.coprime_mul_iff_left.mp h).1
    rw [if_neg hab, if_neg ha, zero_mul]

theorem norm_coprimePart_le (Q : ℕ) (f : ℕ → ℂ) (n : ℕ) :
    ‖coprimePart Q f n‖ ≤ ‖f n‖ := by
  by_cases hn : n.Coprime Q
  · simp only [coprimePart, coprimeMask, if_pos hn, Complex.ofReal_one, one_mul, le_refl]
  · simp only [coprimePart, coprimeMask, if_neg hn, Complex.ofReal_zero, zero_mul, norm_zero]
    exact norm_nonneg _

theorem summable_coprimePart (Q : ℕ) {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (coprimePart Q f) s :=
  hf.norm.of_norm_bounded fun n => LSeries.norm_term_le s (norm_coprimePart_le Q f n)

theorem coprimePart_convolution (Q : ℕ) (f g : ℕ → ℂ) :
    coprimePart Q (LSeries.convolution f g) =
      LSeries.convolution (coprimePart Q f) (coprimePart Q g) := by
  funext n
  simp only [coprimePart, LSeries.convolution_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hn := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have he : coprimeMask Q n = coprimeMask Q p.1 * coprimeMask Q p.2 :=
    hn ▸ coprimeMask_mul Q p.1 p.2
  rw [he]
  push_cast
  ring

theorem coprimePart_dirichletConvPow (Q : ℕ) (f : ℕ → ℂ) (k : ℕ) :
    coprimePart Q (dirichletConvPow f k) = dirichletConvPow (coprimePart Q f) k := by
  induction k with
  | zero =>
    funext n
    by_cases hn : n = 1
    · subst n
      simp [coprimePart, coprimeMask, dirichletConvPow]
    · simp [coprimePart, dirichletConvPow, hn]
  | succ k ih =>
    rw [dirichletConvPow_succ, coprimePart_convolution, ih, dirichletConvPow_succ]

theorem coprimePart_dirichletExp (Q : ℕ) (f : ℕ → ℂ) :
    coprimePart Q (dirichletExp f) = dirichletExp (coprimePart Q f) := by
  funext n
  have h (k : ℕ) := congrFun (coprimePart_dirichletConvPow Q f k) n
  change (coprimeMask Q n : ℂ) *
    (∑ k ∈ Finset.range (n + 1), dirichletConvPow f k n / (k.factorial : ℂ)) = _
  rw [Finset.mul_sum]
  unfold dirichletExp
  apply Finset.sum_congr rfl
  intro k _
  rw [← h k]
  dsimp only [coprimePart]
  ring

theorem coprimePart_one_eq_character (Q : ℕ) :
    coprimePart Q 1 = fun n : ℕ => (1 : DirichletCharacter ℂ Q) (n : ZMod Q) := by
  funext n
  by_cases hc : n.Coprime Q
  · have hu : IsUnit (n : ZMod Q) := (ZMod.isUnit_iff_coprime n Q).mpr hc
    simp only [coprimePart, coprimeMask, if_pos hc, Complex.ofReal_one, one_mul,
      Pi.one_apply, MulChar.one_apply hu]
  · have hu : ¬IsUnit (n : ZMod Q) := fun hu => hc ((ZMod.isUnit_iff_coprime n Q).mp hu)
    simp only [coprimePart, coprimeMask, if_neg hc, Complex.ofReal_zero, zero_mul,
      MulChar.map_nonunit _ hu]

theorem LSeries_coprimePart_one (Q : ℕ) [NeZero Q] {s : ℂ} (hs : 1 < s.re) :
    LSeries (coprimePart Q 1) s = DirichletCharacter.LFunctionTrivChar Q s := by
  rw [coprimePart_one_eq_character]
  exact (DirichletCharacter.LFunction_eq_LSeries 1 hs).symm

def sourceCoprimeDeviation (lam : ℕ → ℝ) (Q : ℕ) (s : ℂ) : ℂ :=
  LSeries (coprimePart Q
    (WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s

/-- The masked actual source convolution factors through the canonical principal character. -/
theorem LSeries_coprimePart_sourceSquareCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (Q : ℕ) [NeZero Q] {s : ℂ} (hs : 1 < s.re) :
    LSeries (coprimePart Q (sourceSquareCoeff lam)) s =
      sourceCoprimeDeviation lam Q s * DirichletCharacter.LFunctionTrivChar Q s ^ 2 := by
  have hd0 : LSeriesSummable
      (WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    LSeriesSummable.sub (WeilHerglotz.summable_term_lamC hW hs)
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
  have hd := summable_coprimePart Q hd0
  have h1 : LSeriesSummable (coprimePart Q (1 : ℕ → ℂ)) s :=
    summable_coprimePart Q (LSeriesSummable_one_iff.mpr hs)
  rw [sourceSquareCoeff, coprimePart_convolution, coprimePart_convolution,
    LSeries_convolution' (hd.convolution h1) h1, LSeries_convolution' hd h1,
    LSeries_coprimePart_one Q hs]
  change sourceCoprimeDeviation lam Q s * _ * _ = _
  ring

end RHTower.WeilSingularArithmetic
