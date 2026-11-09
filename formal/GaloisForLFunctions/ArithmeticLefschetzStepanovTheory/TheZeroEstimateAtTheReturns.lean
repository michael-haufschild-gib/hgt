import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovCountOfTheClosedPoints
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity

/-!
# The zero estimate at the returns

Stepanov's count needs a zero estimate for the auxiliary whose constants do not grow with the
number of logarithms involved. For an integer `P`-smooth auxiliary `A(s) = Σ_α c_α n_α^{−s}` of
length `N` and height `H = Σ |c_α|`, the shifted function `w ↦ A(it + w)` satisfies
`|A(it + w)| ≤ H N^{|w|}` at every height `t` (`norm_orbitFun_shift_le`): its growth depends on the
height and the length only, not on `|P|` or the number of terms. Jensen's formula then counts zeros
around any centre where `|A|` is not small; integrality supplies such centres at the returns.

* **At sign returns** (`zeroCount_le_of_sign_return`). At a `δ`-return to a sign vector `ε` with
  `F(ε) ≠ 0` and `δ L(F) ≤ 1/2`, the zeros of `A(it + ·)` in `|w| ≤ r` (`r ≥ 1`), counted with
  multiplicity, number at most `(log 2H + 2r log N)/log 2`.
* **At torsion returns** (`exists_dilate_zeroCount_le`). At a `δ`-return to a torsion point of order
  `m` where `F` does not vanish, with `mδL(F) ≤ 1/2`, some Frobenius dilate `at`, `a < m` prime to `m`,
  carries the same bound.

The estimate is uniform in the number of logarithms; what it cannot do is place the centres: they
sit where the prime orbit returns to the torsion, at heights fixed by Diophantine approximation.
-/

open Finset Complex Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-- The height `H = Σ_α |c_α|`. -/
def height (F : MvPolynomial P ℤ) : ℝ := ∑ α ∈ F.support, |((F.coeff α : ℤ) : ℝ)|

theorem one_le_height {F : MvPolynomial P ℤ} (hF : F ≠ 0) : 1 ≤ height F := by
  obtain ⟨α, hα⟩ := MvPolynomial.support_nonempty.mpr hF
  have h1 : (1 : ℝ) ≤ |((F.coeff α : ℤ) : ℝ)| := by
    have := MvPolynomial.mem_support_iff.mp hα
    exact_mod_cast Int.one_le_abs this
  exact h1.trans (single_le_sum (f := fun α => |((F.coeff α : ℤ) : ℝ)|)
    (fun _ _ => abs_nonneg _) hα)

/-- The frequency of a monomial is the logarithm of its integer. -/
theorem frequency_eq_log_weight (α : P →₀ ℕ) : frequency α = Real.log (weight α) := by
  rw [frequency, weight, Nat.cast_prod, Real.log_prod (fun p _ => by
    have := (p : Nat.Primes).2.pos; positivity)]
  refine sum_congr rfl fun p _ => ?_
  rw [Nat.cast_pow, Real.log_pow]

theorem frequency_le_log_length {F : MvPolynomial P ℤ} {α : P →₀ ℕ} (hα : α ∈ F.support) :
    frequency α ≤ Real.log (length F) := by
  rw [frequency_eq_log_weight]
  exact Real.log_le_log (by exact_mod_cast weight_pos α) (by exact_mod_cast le_sup (f := weight) hα)

theorem frequency_nonneg (α : P →₀ ℕ) : 0 ≤ frequency α :=
  sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast (p : Nat.Primes).2.one_lt.le))

/-- **Growth at every height.** `|A(it + w)| ≤ H N^{|w|}`. -/
theorem norm_orbitFun_shift_le (F : MvPolynomial P ℤ) (t : ℝ) (w : ℂ) :
    ‖orbitFun F (t * I + w)‖ ≤ height F * Real.exp (Real.log (length F) * ‖w‖) := by
  rw [orbitFun_eq_sum, height, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun α hα => ?_)
  rw [norm_mul, Complex.norm_intCast, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hre : (-(↑t * I + w) * (frequency α : ℂ)).re = -(w.re * frequency α) := by
    simp [Complex.mul_re]
  rw [hre]
  have h1 : -(w.re * frequency α) ≤ ‖w‖ * frequency α := by
    have := neg_abs_le w.re
    have := Complex.abs_re_le_norm w
    nlinarith [frequency_nonneg α]
  have h2 : ‖w‖ * frequency α ≤ ‖w‖ * Real.log (length F) :=
    mul_le_mul_of_nonneg_left (frequency_le_log_length hα) (norm_nonneg _)
  linarith

theorem differentiable_orbitFun_shift (F : MvPolynomial P ℤ) (t : ℝ) :
    Differentiable ℂ (fun w => orbitFun F (t * I + w)) :=
  (differentiable_orbitFun F).comp (differentiable_const _ |>.add differentiable_id)

/-- **Jensen with an integral centre.** If `|A(it)| ≥ 1/2`, the zeros of `A(it + ·)` in `|w| ≤ r`
number at most `(log 2H + 2r log N)/log 2`. -/
theorem zeroCount_le_of_half_le {F : MvPolynomial P ℤ} (hF : F ≠ 0) {t : ℝ}
    (hc : 1 / 2 ≤ ‖orbitValue F t‖) {r : ℝ} (hr : 1 ≤ r) :
    (↑(∑ᶠ u, (MeromorphicOn.divisor (fun w => orbitFun F (t * I + w)) (closedBall 0 r)) u) : ℝ) ≤
      (Real.log (2 * height F) + 2 * r * Real.log (length F)) / Real.log 2 := by
  have h0 : orbitFun F (t * I + 0) = orbitValue F t := by rw [add_zero, orbitFun_I_mul]
  have hne : (fun w => orbitFun F (t * I + w)) 0 ≠ 0 := by
    simp only [h0]
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  have hlen : 0 ≤ Real.log (length F) :=
    Real.log_nonneg (by exact_mod_cast one_le_length hF)
  have h := RHTower.exponentialType_zeroCount_le (differentiable_orbitFun_shift F t) hne hlen
    (one_le_height hF) (norm_orbitFun_shift_le F t) hr
  refine h.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos one_lt_two).le)
  simp only [h0, norm_zero, zero_add]
  have hH : 0 < height F := lt_of_lt_of_le one_pos (one_le_height hF)
  have hlog : -Real.log ‖orbitValue F t‖ ≤ Real.log 2 := by
    have hpos : 0 < ‖orbitValue F t‖ := lt_of_lt_of_le (by norm_num) hc
    have := Real.log_le_log (by norm_num) hc
    rw [one_div, Real.log_inv] at this
    linarith
  rw [Real.log_mul two_ne_zero hH.ne']
  linarith

/-- **The zero estimate at sign returns.** -/
theorem zeroCount_le_of_sign_return {F : MvPolynomial P ℤ} (hF : F ≠ 0) (ε : P → ℂ)
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) (hFε : MvPolynomial.aeval ε F ≠ 0) {t δ : ℝ}
    (hret : ∀ p, ‖orbitPoint P t p - ε p‖ ≤ δ) (hprec : δ * lipWeight F ≤ 1 / 2) {r : ℝ}
    (hr : 1 ≤ r) :
    (↑(∑ᶠ u, (MeromorphicOn.divisor (fun w => orbitFun F (t * I + w)) (closedBall 0 r)) u) : ℝ) ≤
      (Real.log (2 * height F) + 2 * r * Real.log (length F)) / Real.log 2 := by
  have h := one_sub_le_norm_orbitValue F ε hε hFε hret
  exact zeroCount_le_of_half_le hF (by linarith) hr

/-- **The zero estimate at torsion returns.** Some Frobenius dilate of every torsion return where
`F` does not vanish is a centre for the zero estimate. -/
theorem exists_dilate_zeroCount_le {m : ℕ} (hm : 0 < m) {F : MvPolynomial P ℤ} (hF : F ≠ 0)
    (b : P → ℕ) {μ : ℂ} (hμ : IsPrimitiveRoot μ m) {t δ : ℝ} (hδ : 0 ≤ δ)
    (hret : ∀ p, ‖orbitPoint P t p - μ ^ b p‖ ≤ δ)
    (hFμ : MvPolynomial.aeval (torsionPoint μ b) F ≠ 0) (hprec : m * δ * lipWeight F ≤ 1 / 2)
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ a ∈ (range m).filter (m.Coprime ·),
      (↑(∑ᶠ u, (MeromorphicOn.divisor (fun w => orbitFun F ((a * t : ℝ) * I + w))
        (closedBall 0 r)) u) : ℝ) ≤
        (Real.log (2 * height F) + 2 * r * Real.log (length F)) / Real.log 2 := by
  have hprod := one_le_prod_frobeniusOrbit hm F b hμ hret hFμ
  set s := (range m).filter (m.Coprime ·)
  have hex : ∃ a ∈ s, 1 ≤ ‖orbitValue F (a * t)‖ + a * δ * lipWeight F := by
    by_contra hcon
    push Not at hcon
    have hne : s.Nonempty := by
      rw [← card_pos, ← Nat.totient_eq_card_coprime]
      exact Nat.totient_pos.mpr hm
    obtain ⟨a₀, ha₀⟩ := hne
    have hnn : ∀ a ∈ s, 0 ≤ ‖orbitValue F (a * t)‖ + a * δ * lipWeight F := fun a _ =>
      add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ)
        (lipWeight_nonneg F))
    have hle : ∏ a ∈ s.erase a₀, (‖orbitValue F (a * t)‖ + a * δ * lipWeight F) ≤ 1 :=
      prod_le_one (fun a ha => hnn a (mem_of_mem_erase ha))
        (fun a ha => (hcon a (mem_of_mem_erase ha)).le)
    rw [← mul_prod_erase s _ ha₀] at hprod
    have h1 := mul_le_of_le_one_right (hnn a₀ ha₀) hle
    linarith [hcon a₀ ha₀]
  obtain ⟨a, ha, h1⟩ := hex
  refine ⟨a, ha, zeroCount_le_of_half_le hF ?_ hr⟩
  have ham : (a : ℝ) ≤ m := by
    have := (mem_range.mp (mem_filter.mp ha).1).le
    exact_mod_cast this
  have : (a : ℝ) * δ * lipWeight F ≤ m * δ * lipWeight F :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ham hδ) (lipWeight_nonneg F)
  linarith

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
