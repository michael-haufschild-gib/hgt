import GaloisForLFunctions.RHTower.ZetaTrivialZeroSimple

/-!
# Pair parity of zero ledgers and blindness of the Eisenstein constant term

Two elementary facts about how nontrivial zeros enter arithmetic identities.

**Pair parity.** The functional equation together with conjugation pairs a zero `½ + δ + iγ`
with `½ − δ + iγ`.  The sum of any function `φ` over such a pair is an even function of the
displacement `δ`, so its derivative in `δ` at `δ = 0` vanishes.  A "share ledger" `∑_ρ φ(ρ)`
with a fixed weight is therefore never first-order sensitive to whether its zeros lie on the
critical line.

**Eisenstein constant term.** The completed constant term
`a₀(y, s) = Λ(2s) y^s + Λ(2 − 2s) y^{1−s}` of the level-one real-analytic Eisenstein series never
vanishes at a half-zero `s = ρ/2` of the completed zeta function `Λ` with `Re s < ½`: the first
summand is zero there and the second is `Λ(2 − ρ) y^{1−ρ/2}` with `Re (2 − ρ) > 1`.  Theorems
locating the zeros of `a₀(y, ·)` on the critical line therefore carry no information about the
zeros of `Λ`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## Pair parity -/

/-- The sum of `φ` over the reflected pair `½ ± δ + iγ`, as a function of the displacement `δ`. -/
def pairLedger {E : Type*} [AddCommMonoid E] (φ : ℂ → E) (γ : ℝ) (δ : ℝ) : E :=
  φ ((1 / 2 : ℂ) + (δ : ℂ) + (γ : ℂ) * I) + φ ((1 / 2 : ℂ) - (δ : ℂ) + (γ : ℂ) * I)

/-- **Pair parity.** The pair ledger is an even function of the displacement. -/
theorem pairLedger_even {E : Type*} [AddCommMonoid E] (φ : ℂ → E) (γ : ℝ) :
    Function.Even (pairLedger φ γ) := by
  intro δ
  unfold pairLedger
  push_cast
  rw [add_comm]
  ring_nf

/-- **First-order blindness.** The derivative of the pair ledger at zero displacement vanishes,
for every `φ`, differentiable or not. -/
theorem deriv_pairLedger_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℂ → E) (γ : ℝ) : deriv (pairLedger φ γ) 0 = 0 := by
  have hfun : (fun δ : ℝ => pairLedger φ γ (-δ)) = pairLedger φ γ :=
    funext (pairLedger_even φ γ)
  have hd : deriv (pairLedger φ γ) 0 = -deriv (pairLedger φ γ) 0 := by
    have := deriv_comp_neg (pairLedger φ γ) 0
    rwa [hfun, neg_zero] at this
  have h2 : deriv (pairLedger φ γ) 0 + deriv (pairLedger φ γ) 0 = 0 := by
    nth_rewrite 2 [hd]
    exact add_neg_cancel _
  rw [← two_smul ℝ] at h2
  rcases smul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-! ## The Eisenstein constant term -/

/-- The completed constant term of the level-one Eisenstein series at height `y`. -/
def eisensteinConstantTerm (y : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta (2 * s) * (y : ℂ) ^ s
    + completedRiemannZeta (2 - 2 * s) * (y : ℂ) ^ (1 - s)

/-- The constant term is invariant under `s ↦ 1 − s`. -/
theorem eisensteinConstantTerm_one_sub (y : ℝ) (s : ℂ) :
    eisensteinConstantTerm y (1 - s) = eisensteinConstantTerm y s := by
  unfold eisensteinConstantTerm
  rw [show (2 : ℂ) * (1 - s) = 2 - 2 * s by ring, show (2 : ℂ) - (2 - 2 * s) = 2 * s by ring,
    show (1 : ℂ) - (1 - s) = s by ring, add_comm]

/-- **Blindness.** At a half-zero of the completed zeta function with `Re s < ½` the constant
term does not vanish. -/
theorem eisensteinConstantTerm_ne_zero_of_completedRiemannZeta_eq_zero {y : ℝ} (hy : 0 < y)
    {s : ℂ} (hs : s.re < 1 / 2) (h0 : completedRiemannZeta (2 * s) = 0) :
    eisensteinConstantTerm y s ≠ 0 := by
  unfold eisensteinConstantTerm
  rw [h0, zero_mul, zero_add]
  have hre : 1 ≤ (2 - 2 * s).re := by
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
      sub_zero]
    linarith
  have hΛ : completedRiemannZeta (2 - 2 * s) ≠ 0 :=
    _root_.RHTower.completedRiemannZeta_ne_zero_of_one_le_re hre
  have hy' : (y : ℂ) ^ (1 - s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push Not
    intro h
    exact absurd h (Complex.ofReal_ne_zero.2 hy.ne')
  exact mul_ne_zero hΛ hy'

/-- A zero of the constant term with `Re s < ½` is never a half-zero of `Λ`. -/
theorem completedRiemannZeta_ne_zero_of_eisensteinConstantTerm_eq_zero {y : ℝ} (hy : 0 < y)
    {s : ℂ} (hs : s.re < 1 / 2) (h : eisensteinConstantTerm y s = 0) :
    completedRiemannZeta (2 * s) ≠ 0 :=
  fun h0 => eisensteinConstantTerm_ne_zero_of_completedRiemannZeta_eq_zero hy hs h0 h

end

end GaloisForLFunctions.RHTower
