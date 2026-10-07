import GaloisForLFunctions.HTGeometry.CosineInfiniteDiagonal
import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# The diagonal obstruction to rational reciprocal repairs

For a bivariate polynomial norm identity, regular normalization to 1 at a
diagonal point forces the positive diagonal sign. The descended cosine then
supplies infinitely many genuine, nonreal holomorphic 1-fibers. Diagonal
basepoints and the negative diagonal sign are explicitly outside this theorem.
-/

namespace GaloisForLFunctions.HTGeometry.RationalCosineDiagonalRepair

open Complex LabeledCosineDescent CosineInfiniteDiagonal

noncomputable section

abbrev Bivariate := MvPolynomial Bool ℂ

def eval (p : Bivariate) (x y : ℂ) : ℂ := MvPolynomial.eval (fun b => cond b y x) p

def diagonal (p : Bivariate) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X) p

theorem diagonal_eval (p : Bivariate) (x : ℂ) : (diagonal p).eval x = eval p x x := by
  change Polynomial.eval x (MvPolynomial.eval₂ _ _ p) = _
  rw [MvPolynomial.polynomial_eval_eval₂]
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id ℂ := by ext; simp
  rw [hc]
  simp only [Polynomial.eval_X]
  change MvPolynomial.eval₂ (RingHom.id ℂ) (fun _ : Bool => x) p =
    MvPolynomial.eval₂ (RingHom.id ℂ) (fun b => cond b x x) p
  congr 1
  funext b
  cases b <;> rfl

theorem diagonal_sign (p q : Bivariate)
    (hnorm : ∀ x y, eval p x y * eval p y x = eval q x y * eval q y x) :
    diagonal p = diagonal q ∨ diagonal p = -diagonal q := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  apply Polynomial.funext
  intro x
  simpa [Polynomial.eval_pow, diagonal_eval, pow_two] using hnorm x x

theorem diagonal_eq_of_regular_one (p q : Bivariate) (a : ℂ)
    (hnorm : ∀ x y, eval p x y * eval p y x = eval q x y * eval q y x)
    (hone : eval p a a = eval q a a) (hregular : eval q a a ≠ 0) :
    diagonal p = diagonal q := by
  rcases diagonal_sign p q hnorm with h | h
  · exact h
  · exfalso
    have he := congrArg (Polynomial.eval a) h
    simp only [Polynomial.eval_neg, diagonal_eval] at he
    apply hregular
    linear_combination (he - hone) / 2

def pullback (p : Bivariate) (w : ℂ) : ℂ := eval p (source w) (source (-w))

def repair (p q : Bivariate) (w : ℂ) : ℂ := pullback p w / pullback q w

theorem pullback_entire (p : Bivariate) : Differentiable ℂ (pullback p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    change Differentiable ℂ (fun w => MvPolynomial.eval _ (MvPolynomial.C c))
    simp only [MvPolynomial.eval_C]
    exact differentiable_const c
  | add p q hp hq =>
    change Differentiable ℂ (fun w => MvPolynomial.eval _ (p + q))
    simp only [map_add]
    exact hp.add hq
  | mul_X p b hp =>
    have hb : Differentiable ℂ (fun w => cond b (source (-w)) (source w)) := by
      cases b
      · exact source_entire
      · exact source_entire.comp (by fun_prop)
    change Differentiable ℂ (fun w => MvPolynomial.eval _ (p * MvPolynomial.X b))
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul hb

theorem infinite_off_real_one_fiber (p q : Bivariate) (a : ℂ)
    (hnorm : ∀ x y, eval p x y * eval p y x = eval q x y * eval q y x)
    (hone : eval p a a = eval q a a) (hregular : eval q a a ≠ 0) :
    Set.Infinite {w : ℂ | w.im ≠ 0 ∧ AnalyticAt ℂ (repair p q) w ∧ repair p q w = 1} := by
  have heq := diagonal_eq_of_regular_one p q a hnorm hone hregular
  have hq : diagonal q ≠ 0 := by
    intro hz
    apply hregular
    rw [← diagonal_eval, hz, Polynomial.eval_zero]
  apply (infinite_coincidences_avoiding (diagonal q) hq).mono
  rintro w ⟨hw, hc, hden⟩
  have hd : pullback q w ≠ 0 := by
    simpa only [diagonal_eval, pullback, ← hc] using hden
  have hn : pullback p w = pullback q w := by
    simp only [pullback, ← hc, ← diagonal_eval, heq]
  exact ⟨hw, (pullback_entire p |>.analyticAt w).div
    (pullback_entire q |>.analyticAt w) hd, (div_eq_one_iff_eq hd).mpr hn⟩

end

end GaloisForLFunctions.HTGeometry.RationalCosineDiagonalRepair
