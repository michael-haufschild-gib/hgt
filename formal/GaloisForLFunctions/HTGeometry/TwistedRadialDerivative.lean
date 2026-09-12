import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Twisted radial derivatives of rational-coefficient linear forms

A radial field carrying an envelope `E` with `E'/E = 2s/(r(r²−1))` has, for its coefficient `g`
(field `= E·g`), the twisted derivative `twist s g = g' + (2s/(r(r²−1))) g`: the plain derivative of
`E·g` is `E·twist s g`. Rational coefficients are written in Horner form over the monomial
denominator `r^p (r²−1)^q` (`ratCoef`); their derivative is explicit (`ratCoefDeriv`). The main
lemma `twist_linear` computes the twisted derivative of a linear form `∑ᵢ ratCoefᵢ · Xᵢ` in terms of
the twisted derivatives of the `Xᵢ`, and `twist_congr`/`twist_eventuallyEq_zero` transport the
twist along local equalities.
-/

namespace GaloisForLFunctions.HTGeometry.TwistedRadial

open Filter Topology
noncomputable section

/-- Horner evaluation of a coefficient list. -/
def horner : List ℂ → ℂ → ℂ
  | [], _ => 0
  | c :: cs, x => c + x * horner cs x

/-- Formal derivative of the Horner form. -/
def hornerDeriv : List ℂ → ℂ → ℂ
  | [], _ => 0
  | _ :: cs, x => horner cs x + x * hornerDeriv cs x

theorem hasDerivAt_horner (cs : List ℂ) (x : ℂ) :
    HasDerivAt (horner cs) (hornerDeriv cs x) x := by
  induction cs with
  | nil => simpa [horner, hornerDeriv] using hasDerivAt_const x (0 : ℂ)
  | cons c cs ih =>
    have h := ((hasDerivAt_id x).mul ih).const_add c
    simp only [id, one_mul] at h
    simpa [horner, hornerDeriv] using h

/-- Real-variable Horner evaluation. -/
theorem hasDerivAt_horner_real (cs : List ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => horner cs r) (hornerDeriv cs r) r :=
  (hasDerivAt_horner cs r).comp_ofReal

/-- Rational coefficient `horner cs r / (r^p (r²−1)^q)`. -/
def ratCoef (cs : List ℂ) (p q : ℕ) (r : ℝ) : ℂ :=
  horner cs r / ((r : ℂ) ^ p * ((r : ℂ) ^ 2 - 1) ^ q)

/-- Its derivative, over the denominator `r^(p+1) (r²−1)^(q+1)`. -/
def ratCoefDeriv (cs : List ℂ) (p q : ℕ) (r : ℝ) : ℂ :=
  (hornerDeriv cs r * r * ((r : ℂ) ^ 2 - 1) -
      horner cs r * ((p : ℂ) * ((r : ℂ) ^ 2 - 1) + 2 * (q : ℂ) * (r : ℂ) ^ 2)) /
    ((r : ℂ) ^ (p + 1) * ((r : ℂ) ^ 2 - 1) ^ (q + 1))

theorem hasDerivAt_ratCoef (cs : List ℂ) (p q : ℕ) {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (hf : (r : ℂ) ^ 2 - 1 ≠ 0) :
    HasDerivAt (ratCoef cs p q) (ratCoefDeriv cs p q r) r := by
  have hR : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have hD : HasDerivAt (fun r : ℝ => (r : ℂ) ^ p * ((r : ℂ) ^ 2 - 1) ^ q)
      ((p : ℂ) * (r : ℂ) ^ (p - 1) * 1 * ((r : ℂ) ^ 2 - 1) ^ q +
        (r : ℂ) ^ p * ((q : ℂ) * ((r : ℂ) ^ 2 - 1) ^ (q - 1) * ((2 : ℂ) * (r : ℂ) ^ (2 - 1) * 1 - 0))) r :=
    (hR.pow p).mul (((hR.pow 2).sub (hasDerivAt_const r (1 : ℂ))).pow q)
  have hden : (r : ℂ) ^ p * ((r : ℂ) ^ 2 - 1) ^ q ≠ 0 := mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hf)
  have h := (hasDerivAt_horner_real cs r).div hD hden
  refine h.congr_deriv ?_
  unfold ratCoefDeriv
  rcases p with _ | p <;> rcases q with _ | q
  all_goals simp only [Nat.cast_zero, zero_mul, Nat.cast_succ, Nat.succ_sub_one, pow_zero, Nat.zero_sub]
  all_goals field_simp
  all_goals ring

/-- The twisted radial derivative `g' + (2s/(r(r²−1))) g`. -/
def twist (s : ℂ) (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv g r + 2 * s / ((r : ℂ) * ((r : ℂ) ^ 2 - 1)) * g r

/-- Iterated twisted derivative. -/
def twistIter (s : ℂ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | k + 1, g => twist s (twistIter s k g)

@[simp] theorem twistIter_zero (s : ℂ) (g : ℝ → ℂ) : twistIter s 0 g = g := rfl

@[simp] theorem twistIter_succ (s : ℂ) (k : ℕ) (g : ℝ → ℂ) :
    twistIter s (k + 1) g = twist s (twistIter s k g) := rfl

theorem twist_congr (s : ℂ) {g h : ℝ → ℂ} {r : ℝ} (hgh : g =ᶠ[𝓝 r] h) :
    twist s g r = twist s h r := by
  unfold twist
  rw [hgh.deriv_eq, hgh.eq_of_nhds]

theorem twist_eventuallyEq_zero (s : ℂ) {g : ℝ → ℂ} {r : ℝ} (hg : g =ᶠ[𝓝 r] fun _ => 0) :
    twist s g r = 0 := by
  rw [twist_congr s hg]
  simp [twist]

/-- Twisted derivative of a rational-coefficient linear form. -/
theorem twist_linear (s : ℂ) {n : ℕ} (cs : Fin n → List ℂ) (p q : Fin n → ℕ) (X : Fin n → ℝ → ℂ)
    {r : ℝ} (hr : (r : ℂ) ≠ 0) (hf : (r : ℂ) ^ 2 - 1 ≠ 0)
    (hX : ∀ i, DifferentiableAt ℝ (X i) r) :
    twist s (fun r => ∑ i, ratCoef (cs i) (p i) (q i) r * X i r) r =
      ∑ i, (ratCoefDeriv (cs i) (p i) (q i) r * X i r +
        ratCoef (cs i) (p i) (q i) r * twist s (X i) r) := by
  have hd : HasDerivAt (fun r => ∑ i, ratCoef (cs i) (p i) (q i) r * X i r)
      (∑ i, (ratCoefDeriv (cs i) (p i) (q i) r * X i r +
        ratCoef (cs i) (p i) (q i) r * deriv (X i) r)) r :=
    HasDerivAt.fun_sum fun i _ => (hasDerivAt_ratCoef (cs i) (p i) (q i) hr hf).mul (hX i).hasDerivAt
  unfold twist
  rw [hd.deriv, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end
end GaloisForLFunctions.HTGeometry.TwistedRadial
