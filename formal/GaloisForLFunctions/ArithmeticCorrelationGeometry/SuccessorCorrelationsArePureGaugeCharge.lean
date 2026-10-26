import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant

/-!
# Successor correlations are pure gauge charge

A **pair form** `P(x) = Σ_{(m,n)} w(m,n) χ_x(m) χ̄_x(n)` reads a source along a finite set of pairs.
Its gauge mean keeps the diagonal pairs `m = n` (`integral_pairForm`), and its gauge mean square is
the **ratio energy**: the sum of `w(m,n) w̄(m',n')` over pairs of pairs with the same ratio
`m/n = m'/n'` (`integral_pairForm_mul_conj`). Multiplicative structure enters only through
coincidences of ratios.

For the successor correlation `C_h(a) = Σ_n a_n ā_{n+h}` of the twisted source:

* **Mean zero** (`integral_succCorr_twisted`). No pair `(n, n+h)` is diagonal.
* **Square-root variance** (`integral_normSq_succCorr_twisted`). Distinct successor pairs have
  distinct ratios, so the gauge mean square is `Σ_n |a_n|² |a_{n+h}|²`, a gauge-invariant
  quantity: the energy of the correlation is multiplicative information, its value is not.
* **Covariance across shifts** (`integral_succCorr_mul_conj_succCorr`). The correlations at shifts
  `h` and `h'` are coupled exactly along the pairs `n h' = n' h`, i.e. along the dilation that
  carries `(n, n+h)` onto `(n', n'+h')`. The gauge geometry of the successor family is a dilation
  correlation.

**Blindness** (`exists_twist_succCorr_large`, `exists_twist_re_succCorr_nonpos`). For every source
and every shift there are twists with the same moduli and the same value on every multiplicatively
coincident monomial (`MultiplicativeObservationIsGaugeInvariant`) whose shift-`h` correlation has
modulus at least `(Σ |a_n|² |a_{n+h}|²)^{1/2}`, and twists whose correlation has nonpositive real
part. Multiplicative data, and every positivity derived from them, cannot certify a successor
correlation below the square-root scale, nor its sign. A successor law must be prescribed by the
arithmetic source itself.
-/

open MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry

/-! ### Pair forms and the ratio energy -/

/-- The pair form `Σ_{(m,n) ∈ S} w(m,n) χ_x(m) χ̄_x(n)`. -/
def pairForm (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ) (x : GaugeTorus) : ℂ :=
  ∑ q ∈ S, w q * (twist x q.1 * conj (twist x q.2))

theorem continuous_pairForm (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ) : Continuous (pairForm S w) :=
  continuous_finsetSum _ fun q _ => continuous_const.mul
    ((continuous_twist q.1).mul (Complex.continuous_conj.comp (continuous_twist q.2)))

/-- **The gauge mean of a pair form keeps the diagonal pairs.** -/
theorem integral_pairForm {S : Finset (ℕ × ℕ)} (hS : ∀ q ∈ S, q.1 ≠ 0 ∧ q.2 ≠ 0)
    (w : ℕ × ℕ → ℂ) :
    ∫ x, pairForm S w x ∂gaugeHaar = ∑ q ∈ S with q.1 = q.2, w q := by
  simp only [pairForm]
  rw [integral_finsetSum _ fun q _ => (integrable_twist_mul_conj q.1 q.2).const_mul _,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_const_mul, integral_twist_mul_conj (hS q hq).1 (hS q hq).2]
  split_ifs <;> simp

/-- The product of two pair characters is the character of the cross products. -/
theorem pairChar_mul_conj (x : GaugeTorus) {m n m' n' : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hm' : m' ≠ 0) (hn' : n' ≠ 0) :
    twist x m * conj (twist x n) * conj (twist x m' * conj (twist x n')) =
      twist x (m * n') * conj (twist x (n * m')) := by
  rw [twist_mul x hm hn', twist_mul x hn hm']
  simp only [map_mul, Complex.conj_conj]
  ring

/-- **The gauge mean square of a pair form is its ratio energy.** -/
theorem integral_pairForm_mul_conj {S : Finset (ℕ × ℕ)} (hS : ∀ q ∈ S, q.1 ≠ 0 ∧ q.2 ≠ 0)
    (w : ℕ × ℕ → ℂ) :
    ∫ x, pairForm S w x * conj (pairForm S w x) ∂gaugeHaar =
      ∑ q ∈ S, ∑ q' ∈ S, if q.1 * q'.2 = q.2 * q'.1 then w q * conj (w q') else 0 := by
  have hexp : ∀ x, pairForm S w x * conj (pairForm S w x) =
      ∑ q ∈ S, ∑ q' ∈ S, w q * conj (w q') *
        (twist x (q.1 * q'.2) * conj (twist x (q.2 * q'.1))) := by
    intro x
    rw [pairForm, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun q' hq' => ?_
    rw [← pairChar_mul_conj x (hS q hq).1 (hS q hq).2 (hS q' hq').1 (hS q' hq').2, map_mul]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun q' _ =>
    (integrable_twist_mul_conj _ _).const_mul _]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_finsetSum _ fun q' _ => (integrable_twist_mul_conj _ _).const_mul _]
  refine Finset.sum_congr rfl fun q' hq' => ?_
  rw [integral_const_mul, integral_twist_mul_conj
    (mul_ne_zero (hS q hq).1 (hS q' hq').2) (mul_ne_zero (hS q hq).2 (hS q' hq').1)]
  split_ifs <;> simp

/-! ### Successor correlations -/

/-- The shift-`h` correlation `C_h(a) = Σ_{n ∈ s} a_n ā_{n+h}`. -/
def succCorr (s : Finset ℕ) (h : ℕ) (a : ℕ → ℂ) : ℂ := ∑ n ∈ s, a n * conj (a (n + h))

/-- The successor pairs `(n, n+h)` with the weights `a_n ā_{n+h}`: the pair-form presentation of
`C_h`. -/
theorem succCorr_twisted_eq_pairForm (s : Finset ℕ) (h : ℕ) (a : ℕ → ℂ) (x : GaugeTorus) :
    succCorr s h (twisted x a) =
      ∑ n ∈ s, a n * conj (a (n + h)) * (twist x n * conj (twist x (n + h))) := by
  rw [succCorr]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [twisted, map_mul]
  ring

theorem continuous_succCorr_twisted (s : Finset ℕ) (h : ℕ) (a : ℕ → ℂ) :
    Continuous fun x => succCorr s h (twisted x a) := by
  simp_rw [succCorr_twisted_eq_pairForm]
  exact continuous_finsetSum _ fun n _ => continuous_const.mul
    ((continuous_twist n).mul (Complex.continuous_conj.comp (continuous_twist (n + h))))

theorem integrable_succCorr_twisted (s : Finset ℕ) (h : ℕ) (a : ℕ → ℂ) :
    Integrable (fun x => succCorr s h (twisted x a)) gaugeHaar :=
  (continuous_succCorr_twisted s h a).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Successor correlations have gauge mean zero.** -/
theorem integral_succCorr_twisted {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {h : ℕ} (hh : h ≠ 0)
    (a : ℕ → ℂ) : ∫ x, succCorr s h (twisted x a) ∂gaugeHaar = 0 := by
  simp_rw [succCorr_twisted_eq_pairForm]
  rw [integral_finsetSum _ fun n _ => (integrable_twist_mul_conj _ _).const_mul _]
  refine Finset.sum_eq_zero fun n hn => ?_
  rw [integral_const_mul, integral_twist_mul_conj (hs n hn) (by omega), if_neg (by omega),
    mul_zero]

/-- **Covariance of successor correlations across shifts.** The correlations at shifts `h, h'` are
coupled exactly along the pairs `n h' = n' h`: the dilation carrying `(n, n+h)` onto `(n', n'+h')`. -/
theorem integral_succCorr_mul_conj_succCorr {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (h h' : ℕ)
    (a : ℕ → ℂ) :
    ∫ x, succCorr s h (twisted x a) * conj (succCorr s h' (twisted x a)) ∂gaugeHaar =
      ∑ n ∈ s, ∑ n' ∈ s, if n * h' = n' * h then
        a n * conj (a (n + h)) * conj (a n' * conj (a (n' + h'))) else 0 := by
  have hexp : ∀ x, succCorr s h (twisted x a) * conj (succCorr s h' (twisted x a)) =
      ∑ n ∈ s, ∑ n' ∈ s, a n * conj (a (n + h)) * conj (a n' * conj (a (n' + h'))) *
        (twist x (n * (n' + h')) * conj (twist x ((n + h) * n'))) := by
    intro x
    rw [succCorr_twisted_eq_pairForm, succCorr_twisted_eq_pairForm, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun n' hn' => ?_
    have hn0 := hs n hn
    have hn0' := hs n' hn'
    rw [← pairChar_mul_conj x hn0 (by omega) hn0' (by omega)]
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun n' _ =>
    (integrable_twist_mul_conj _ _).const_mul _]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_finsetSum _ fun n' _ => (integrable_twist_mul_conj _ _).const_mul _]
  refine Finset.sum_congr rfl fun n' hn' => ?_
  have hn0 := hs n hn
  have hn0' := hs n' hn'
  rw [integral_const_mul, integral_twist_mul_conj (mul_ne_zero hn0 (by omega))
    (mul_ne_zero (by omega) hn0')]
  have hiff : n * (n' + h') = (n + h) * n' ↔ n * h' = n' * h := by
    constructor <;> intro e <;> nlinarith [e]
  by_cases hc : n * h' = n' * h
  · rw [if_pos (hiff.mpr hc), if_pos hc, mul_one]
  · rw [if_neg (fun e => hc (hiff.mp e)), if_neg hc, mul_zero]

/-- **Square-root variance.** The gauge mean square of a successor correlation is the
gauge-invariant energy `Σ |a_n|² |a_{n+h}|²`. -/
theorem integral_normSq_succCorr_twisted {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {h : ℕ}
    (hh : h ≠ 0) (a : ℕ → ℂ) :
    ∫ x, ‖succCorr s h (twisted x a)‖ ^ 2 ∂gaugeHaar = ∑ n ∈ s, ‖a n‖ ^ 2 * ‖a (n + h)‖ ^ 2 := by
  have hcov := integral_succCorr_mul_conj_succCorr hs h h a
  have hdiag : ∀ n ∈ s, (∑ n' ∈ s, if n * h = n' * h then
      a n * conj (a (n + h)) * conj (a n' * conj (a (n' + h))) else 0) =
        (((‖a n‖ ^ 2 * ‖a (n + h)‖ ^ 2 : ℝ)) : ℂ) := by
    intro n hn
    rw [Finset.sum_eq_single n]
    · rw [if_pos rfl, map_mul, Complex.conj_conj]
      have e : a n * conj (a (n + h)) * (conj (a n) * a (n + h)) =
          (a n * conj (a n)) * (a (n + h) * conj (a (n + h))) := by ring
      rw [e, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    · intro n' _ hne
      rw [if_neg]
      intro e
      exact hne (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hh) e).symm
    · exact fun h => absurd hn h
  rw [Finset.sum_congr rfl hdiag] at hcov
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hcov
  rw [integral_complex_ofReal] at hcov
  exact_mod_cast hcov

/-! ### Blindness of multiplicative data to successor correlations -/

/-- **A twist with a square-root-size correlation.** Some twist of the source has the same moduli
and multiplicative data and a shift-`h` correlation of modulus at least
`(Σ |a_n|² |a_{n+h}|²)^{1/2}`. -/
theorem exists_twist_succCorr_large {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {h : ℕ} (hh : h ≠ 0)
    (a : ℕ → ℂ) :
    ∃ x : GaugeTorus, ∑ n ∈ s, ‖a n‖ ^ 2 * ‖a (n + h)‖ ^ 2 ≤ ‖succCorr s h (twisted x a)‖ ^ 2 := by
  have hint : Integrable (fun x => ‖succCorr s h (twisted x a)‖ ^ 2) gaugeHaar :=
    ((continuous_succCorr_twisted s h a).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨x, hx⟩ := exists_integral_le hint
  exact ⟨x, (integral_normSq_succCorr_twisted hs hh a).symm.le.trans hx⟩

/-- **A twist with a correlation of nonpositive real part.** The sign of a successor correlation is
not multiplicative information. -/
theorem exists_twist_re_succCorr_nonpos {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) {h : ℕ}
    (hh : h ≠ 0) (a : ℕ → ℂ) : ∃ x : GaugeTorus, (succCorr s h (twisted x a)).re ≤ 0 := by
  have hint := (integrable_succCorr_twisted s h a).re
  obtain ⟨x, hx⟩ := exists_le_integral hint
  refine ⟨x, hx.trans (le_of_eq ?_)⟩
  rw [integral_re (integrable_succCorr_twisted s h a), integral_succCorr_twisted hs hh,
    map_zero]

/-- Twisting keeps the moduli of a source. -/
theorem norm_twisted (x : GaugeTorus) (a : ℕ → ℂ) (n : ℕ) : ‖twisted x a n‖ = ‖a n‖ := by
  rw [twisted, norm_mul, norm_twist, one_mul]

/-- Twisting keeps every multiplicatively coincident monomial. -/
theorem monomial_twisted_of_prod_eq {k l : ℕ} {m : Fin k → ℕ} {n : Fin l → ℕ}
    (hm : ∀ i, m i ≠ 0) (hn : ∀ j, n j ≠ 0) (hmn : ∏ i, m i = ∏ j, n j) (a : ℕ → ℂ)
    (x : GaugeTorus) : monomial m n (twisted x a) = monomial m n a := by
  rw [monomial_twisted hm hn, hmn, twist_mul_conj_self, one_mul]

end GaloisForLFunctions.ArithmeticCorrelationGeometry
