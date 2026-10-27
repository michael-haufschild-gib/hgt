import GaloisForLFunctions.ArithmeticIntersectionTheory.WeilsPrimeFunctionalIsTheFiniteIntersection
import GaloisForLFunctions.RHTower.WeilMarkovOneBoundState

/-!
# The polar part pairs the pole direction

On a log-atom test `f = Σ_{n ∈ S} x_n φ(· − log n)` Weil's explicit formula has three parts: the prime
functional, which is `‖φ‖² Σ_p Q_p(x)` (`WeilsPrimeFunctionalIsTheFiniteIntersection`), the polar part
`k̂(i/2) + k̂(−i/2)` and the archimedean `Γ`-part. This module computes the polar part.

* **Mellin values of a log-atom test** (`paperFT_logAtom_half`, `paperFT_logAtom_neg_half`):
  `f̂(i/2) = α Σ x_n n^{−1/2}` and `f̂(−i/2) = β Σ x_n n^{1/2}`, with `α = ∫ φ e^{−u/2}`, `β = ∫ φ e^{u/2}`.
* **The polar part is a rank-two form** (`weilPoleTerm_logAtom`):
  `k̂(i/2) + k̂(−i/2) = 2αβ (Σ x_n n^{−1/2})(Σ x_n n^{1/2})`. It pairs the **pole direction**
  `x_n = n^{−1/2}` — along which the prime form is unbounded (`not_exists_primeForm_le`) — with its dual
  `x_n = n^{1/2}`.
* **On the polar hyperplane the archimedean place pays alone**
  (`riemannHypothesis_gammaPart_ge_towers`): under RH, for log-atom cycles with `Σ x_n n^{−1/2} = 0`,
  `‖φ‖² Σ_p Q_p(x) ≤ Re(Γ-part)`.

So the sign problem on log-atom tests has two pieces: along the pole direction the polar part pays
for the towers; on the polar hyperplane the `Γ`-factor alone must, through the self-energy
`log(1/δ)` of the atoms (RHTower `SeparatedBump.levy_ge`).
-/

noncomputable section

open MeasureTheory Finset Complex
open scoped ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArithmeticIntersectionTheory

open ArithmeticEffectivityTheory

variable {φ : ℝ → ℝ} {δ : ℝ}

theorem integrable_translate_mul_exp (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (c s : ℝ) : Integrable fun u => φ (u - c) * Real.exp (s * u) := by
  have hcont : Continuous fun u => φ (u - c) * Real.exp (s * u) := by
    have := hφ.continuous; fun_prop
  refine hcont.integrable_of_hasCompactSupport ?_
  have hφc : HasCompactSupport φ := RHTower.SeparatedBump.hasCompactSupport_of_abs hφs
  exact (hφc.comp_homeomorph (Homeomorph.subRight c)).mul_right

/-- `∫ φ(u − c) e^{su} du = e^{sc} ∫ φ(v) e^{sv} dv`. -/
theorem integral_translate_mul_exp (c s : ℝ) :
    ∫ u, φ (u - c) * Real.exp (s * u) = Real.exp (s * c) * ∫ v, φ v * Real.exp (s * v) := by
  rw [← integral_const_mul, ← integral_sub_right_eq_self (fun v => Real.exp (s * c) *
    (φ v * Real.exp (s * v))) c]
  congr 1; funext u
  rw [show s * u = s * c + s * (u - c) by ring, Real.exp_add]
  ring

/-- The real Mellin value `∫ f(u) e^{su} du` of a log-atom test. -/
theorem integral_logAtom_mul_exp (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    (S : Finset ℕ) (x : ℕ → ℝ) (s : ℝ) :
    ∫ u, logAtomTest φ S x u * Real.exp (s * u) =
      (∑ n ∈ S, x n * Real.exp (s * Real.log n)) * ∫ v, φ v * Real.exp (s * v) := by
  unfold logAtomTest
  simp_rw [sum_mul]
  rw [integral_finsetSum _ fun n _ => ?_]
  · refine sum_congr rfl fun n _ => ?_
    rw [show (fun u => x n * φ (u - Real.log n) * Real.exp (s * u)) =
      fun u => x n * (φ (u - Real.log n) * Real.exp (s * u)) from funext fun u => by ring,
      integral_const_mul, integral_translate_mul_exp]
    ring
  · refine ((integrable_translate_mul_exp hφ hφs (Real.log n) s).const_mul (x n)).congr
      (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring

theorem exp_half_log {n : ℕ} (hn : 0 < n) : Real.exp (1 / 2 * Real.log n) = Real.sqrt n := by
  have hpos : 0 < Real.exp (1 / 2 * Real.log n) := Real.exp_pos _
  rw [← Real.sqrt_sq hpos.le, ← Real.exp_nat_mul]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * (1 / 2 * Real.log n) = Real.log n by push_cast; ring,
    Real.exp_log (by exact_mod_cast hn)]

theorem exp_neg_half_log {n : ℕ} (hn : 0 < n) : Real.exp (-1 / 2 * Real.log n) = 1 / Real.sqrt n := by
  rw [show -1 / 2 * Real.log n = -(1 / 2 * Real.log n) by ring, Real.exp_neg, exp_half_log hn,
    one_div]

/-- `f̂(s) = ∫ f(u) e^{isu}` at `s = ∓i/2` is the real Mellin value at `±½`. -/
theorem paperFT_ofReal_eq (f : ℝ → ℝ) (z : ℂ) (s : ℝ) (hz : I * z = (s : ℂ)) :
    Zeta23.paperFT (fun u => (f u : ℂ)) z = ((∫ u, f u * Real.exp (s * u) : ℝ) : ℂ) := by
  rw [Zeta23.paperFT, ← integral_complex_ofReal]
  congr 1; funext u
  rw [hz]
  push_cast
  rw [← ofReal_mul, ← ofReal_exp]

theorem paperFT_logAtom_half (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (x : ℕ → ℝ) :
    Zeta23.paperFT (fun u => (logAtomTest φ S x u : ℂ)) (I / 2) =
      (((∑ n ∈ S, x n / Real.sqrt n) * ∫ v, φ v * Real.exp (-1 / 2 * v) : ℝ) : ℂ) := by
  rw [paperFT_ofReal_eq _ _ (-1 / 2) (by rw [← mul_div_assoc, I_mul_I]; push_cast; ring),
    integral_logAtom_mul_exp hφ hφs]
  congr 2
  exact sum_congr rfl fun n hn => by rw [exp_neg_half_log (hS n hn), mul_one_div]

theorem paperFT_logAtom_neg_half (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (x : ℕ → ℝ) :
    Zeta23.paperFT (fun u => (logAtomTest φ S x u : ℂ)) (-I / 2) =
      (((∑ n ∈ S, x n * Real.sqrt n) * ∫ v, φ v * Real.exp (1 / 2 * v) : ℝ) : ℂ) := by
  rw [paperFT_ofReal_eq _ _ (1 / 2)
      (by rw [neg_div, mul_neg, ← mul_div_assoc, I_mul_I]; push_cast; ring),
    integral_logAtom_mul_exp hφ hφs]
  congr 2
  exact sum_congr rfl fun n hn => by rw [exp_half_log (hS n hn)]

/-- **The polar part of a log-atom test** is `2αβ (Σ x_n n^{−1/2})(Σ x_n n^{1/2})`. -/
theorem weilPoleTerm_logAtom (hφ : ContDiff ℝ 2 φ) (hφs : ∀ u, δ / 2 < |u| → φ u = 0)
    {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (x : ℕ → ℝ) :
    RHTower.weilPoleTerm (Zeta23.EF.weilTest (fun u => (logAtomTest φ S x u : ℂ))
      (fun u => (logAtomTest φ S x u : ℂ))) =
      ((2 * (∫ v, φ v * Real.exp (-1 / 2 * v)) * (∫ v, φ v * Real.exp (1 / 2 * v)) *
        (∑ n ∈ S, x n / Real.sqrt n) * (∑ n ∈ S, x n * Real.sqrt n) : ℝ) : ℂ) := by
  have hc : Continuous fun u => (logAtomTest φ S x u : ℂ) :=
    continuous_ofReal.comp (contDiff_logAtomTest hφ S x).continuous
  have hcs : HasCompactSupport fun u => (logAtomTest φ S x u : ℂ) :=
    (hasCompactSupport_logAtomTest hφs S x).comp_left ofReal_zero
  rw [RHTower.weilPoleTerm_weilTest_eq hc hcs, paperFT_logAtom_half hφ hφs hS,
    paperFT_logAtom_neg_half hφ hφs hS, conj_ofReal, conj_ofReal]
  push_cast; ring

/-- The `Γ`-part of Weil's explicit formula. -/
def gammaPart (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ)

theorem archPolarPart_eq (k : ℝ → ℂ) : archPolarPart k = RHTower.weilPoleTerm k + gammaPart k := by
  rfl

/-- **On the polar hyperplane the `Γ`-factor pays alone**: under RH, for log-atom cycles with
`Σ x_n n^{−1/2} = 0`, `‖φ‖² Σ_p Q_p(x) ≤ Re(Γ-part)`. -/
theorem riemannHypothesis_gammaPart_ge_towers (hRH : RiemannHypothesis) {S : Finset ℕ} {M : ℕ}
    (hd : LogAtomData φ δ S M) (x : ℕ → ℝ) (hpolar : ∑ n ∈ S, x n / Real.sqrt n = 0) :
    (∫ u, φ u ^ 2) * ∑ p ∈ (∏ n ∈ S, n).primeFactors, localForm S x p ≤
      (gammaPart (Zeta23.EF.weilTest (fun u => (logAtomTest φ S x u : ℂ))
        (fun u => (logAtomTest φ S x u : ℂ)))).re := by
  have h := riemannHypothesis_archPolar_ge_towers hRH hd x
  rw [archPolarPart_eq, add_re, weilPoleTerm_logAtom hd.contDiff hd.support hd.pos, hpolar] at h
  simpa using h

end GaloisForLFunctions.ArithmeticIntersectionTheory
