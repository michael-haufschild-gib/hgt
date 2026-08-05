import Mathlib
import GaloisForLFunctions.RHTower.GibbsTwoScalePositivity

/-!
# Two-scale positivity at level two

The two-scale positivity engine is verified at level two: for a pair `{q,r}` and the
dilated scales `(x, px)` with `p ≤ q`, the form `Re[P(z,x)·conj P(z,px)]` is positive on
the closed right half-plane.  Everything reduces to the single coefficient inequality
`b₁b₂ ≥ a₁c₂ + a₂c₁`, which holds by comparing Boltzmann energies **crosswise**:

  `q + rp ≤ p + qr`  ⟺ `(q−p)(r−1) ≥ 0`,
  `r + qp ≤ 1 + qrp` ⟺ `(r−1)(qp−1) ≥ 0`,

so the ordering constraint `p ≤ q` — adjoin primes in decreasing order — appears as the
factor `(q−p)`.  Through the engine this gives stability of the three-element gas at every
coupling, by a route that generalizes.
-/

namespace RHTower.GibbsGas

open Real

/-- The real part of a quadratic against a conjugate quadratic. -/
theorem re_mul_conj_quadratic (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) (z : ℂ) :
    ((((a₁ : ℝ) : ℂ) + z * ((b₁ : ℝ) : ℂ) + z ^ 2 * ((c₁ : ℝ) : ℂ))
        * (starRingEnd ℂ)
          (((a₂ : ℝ) : ℂ) + z * ((b₂ : ℝ) : ℂ) + z ^ 2 * ((c₂ : ℝ) : ℂ))).re
      = a₁ * a₂ + (a₁ * b₂ + a₂ * b₁) * z.re
        + (a₁ * c₂ + a₂ * c₁) * (z.re ^ 2 - z.im ^ 2)
        + b₁ * b₂ * (z.re ^ 2 + z.im ^ 2)
        + (b₁ * c₂ + b₂ * c₁) * ((z.re ^ 2 + z.im ^ 2) * z.re)
        + c₁ * c₂ * (z.re ^ 2 + z.im ^ 2) ^ 2 := by
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_two]
  ring

/-- **The level-two positivity criterion.**  For quadratics with positive coefficients,
`b₁b₂ ≥ a₁c₂ + a₂c₁` forces positivity of the two-scale form on the closed right
half-plane. -/
theorem re_mul_conj_quadratic_pos (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)
    (ha₁ : 0 < a₁) (hb₁ : 0 ≤ b₁) (hc₁ : 0 ≤ c₁)
    (ha₂ : 0 < a₂) (hb₂ : 0 ≤ b₂) (hc₂ : 0 ≤ c₂)
    (hdom : a₁ * c₂ + a₂ * c₁ ≤ b₁ * b₂)
    (z : ℂ) (hz : 0 ≤ z.re) :
    0 < ((((a₁ : ℝ) : ℂ) + z * ((b₁ : ℝ) : ℂ) + z ^ 2 * ((c₁ : ℝ) : ℂ))
        * (starRingEnd ℂ)
          (((a₂ : ℝ) : ℂ) + z * ((b₂ : ℝ) : ℂ) + z ^ 2 * ((c₂ : ℝ) : ℂ))).re := by
  rw [re_mul_conj_quadratic]
  have hE : (0 : ℝ) ≤ a₁ * c₂ + a₂ * c₁ :=
    add_nonneg (mul_nonneg ha₁.le hc₂) (mul_nonneg ha₂.le hc₁)
  have hmid : 0 ≤ (a₁ * c₂ + a₂ * c₁) * (z.re ^ 2 - z.im ^ 2)
      + b₁ * b₂ * (z.re ^ 2 + z.im ^ 2) := by
    have hstep : (a₁ * c₂ + a₂ * c₁) * (z.re ^ 2 + z.im ^ 2)
        ≤ b₁ * b₂ * (z.re ^ 2 + z.im ^ 2) :=
      mul_le_mul_of_nonneg_right hdom (by positivity)
    nlinarith [hstep, sq_nonneg z.re, hE]
  have h1 : 0 ≤ (a₁ * b₂ + a₂ * b₁) * z.re :=
    mul_nonneg (add_nonneg (mul_nonneg ha₁.le hb₂) (mul_nonneg ha₂.le hb₁)) hz
  have h2 : 0 ≤ (b₁ * c₂ + b₂ * c₁) * ((z.re ^ 2 + z.im ^ 2) * z.re) :=
    mul_nonneg (add_nonneg (mul_nonneg hb₁ hc₂) (mul_nonneg hb₂ hc₁))
      (mul_nonneg (by positivity) hz)
  have h3 : 0 ≤ c₁ * c₂ * (z.re ^ 2 + z.im ^ 2) ^ 2 := by positivity
  have h0 : 0 < a₁ * a₂ := mul_pos ha₁ ha₂
  linarith

/-- The pair gas in quadratic form. -/
theorem gibbsDiagC_pair_quadratic (q r : ℕ) (hqr : q ∉ ({r} : Finset ℕ))
    (x : ℝ) (z : ℂ) :
    gibbsDiagC {q, r} x z
      = ((Real.exp (-x) : ℝ) : ℂ)
        + z * ((Real.exp (-((r : ℝ) * x)) + Real.exp (-((q : ℝ) * x)) : ℝ) : ℂ)
        + z ^ 2 * ((Real.exp (-((r : ℝ) * ((q : ℝ) * x))) : ℝ) : ℂ) := by
  rw [show ({q, r} : Finset ℕ) = insert q {r} from rfl,
    gibbsDiagC_insert q {r} hqr, gibbsDiagC_singleton, gibbsDiagC_singleton]
  push_cast
  ring

/-- Boltzmann weights compare by total energy. -/
theorem exp_pair_le_of_le (u₁ u₂ v₁ v₂ : ℝ) (h : u₁ + u₂ ≤ v₁ + v₂) :
    Real.exp (-v₁) * Real.exp (-v₂) ≤ Real.exp (-u₁) * Real.exp (-u₂) := by
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **Level two of the engine.**  For `p ≤ q` the pair gas is two-scale positive at the
dilated pair of couplings. -/
theorem twoScalePositive_pair (p q r : ℕ) (hp1 : 1 ≤ p) (hpq : p ≤ q) (hr1 : 1 ≤ r)
    (hqr : q ∉ ({r} : Finset ℕ)) (x : ℝ) (hx : 0 ≤ x) :
    TwoScalePositive {q, r} x ((p : ℝ) * x) := by
  intro z hz
  rw [gibbsDiagC_pair_quadratic q r hqr, gibbsDiagC_pair_quadratic q r hqr]
  have hp' : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hpq' : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
  have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hq' : (1 : ℝ) ≤ (q : ℝ) := le_trans hp' hpq'
  -- the two crosswise energy comparisons
  have hcross₁ : Real.exp (-((q : ℝ) * x)) * Real.exp (-((r : ℝ) * ((p : ℝ) * x)))
      ≥ Real.exp (-((p : ℝ) * x))
        * Real.exp (-((r : ℝ) * ((q : ℝ) * x))) := by
    refine exp_pair_le_of_le _ _ _ _ ?_
    have hfac : (0 : ℝ) ≤ ((q : ℝ) - (p : ℝ)) * ((r : ℝ) - 1) * x :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hx
    nlinarith [hfac]
  have hcross₂ : Real.exp (-((r : ℝ) * x)) * Real.exp (-((q : ℝ) * ((p : ℝ) * x)))
      ≥ Real.exp (-x) * Real.exp (-((r : ℝ) * ((q : ℝ) * ((p : ℝ) * x)))) := by
    refine exp_pair_le_of_le _ _ _ _ ?_
    have hfac : (0 : ℝ) ≤ ((r : ℝ) - 1) * ((q : ℝ) * (p : ℝ) - 1) * x :=
      mul_nonneg (mul_nonneg (by linarith) (by nlinarith)) hx
    nlinarith [hfac]
  refine re_mul_conj_quadratic_pos _ _ _ _ _ _ (Real.exp_pos _) (by positivity)
    (Real.exp_pos _).le (Real.exp_pos _) (by positivity) (Real.exp_pos _).le ?_ z hz
  -- the dominance inequality, from the two crosswise comparisons
  have hrest₁ : (0 : ℝ) ≤ Real.exp (-((r : ℝ) * x))
      * Real.exp (-((r : ℝ) * ((p : ℝ) * x))) := by positivity
  have hrest₂ : (0 : ℝ) ≤ Real.exp (-((q : ℝ) * x))
      * Real.exp (-((q : ℝ) * ((p : ℝ) * x))) := by positivity
  nlinarith [hcross₁, hcross₂, hrest₁, hrest₂]

/-- **Stability of the three-element gas at every coupling**, via the engine: no zero in
the closed right half-plane. -/
theorem gibbsDiagC_triple_ne_zero (p q r : ℕ) (hp1 : 1 ≤ p) (hpq : p ≤ q) (hr1 : 1 ≤ r)
    (hqr : q ∉ ({r} : Finset ℕ)) (hp : p ∉ ({q, r} : Finset ℕ))
    (x : ℝ) (hx : 0 ≤ x) (z : ℂ) (hz : 0 ≤ z.re) :
    gibbsDiagC (insert p {q, r}) x z ≠ 0 :=
  gibbsDiagC_insert_ne_zero_of_twoScale p {q, r} hp x
    (twoScalePositive_pair p q r hp1 hpq hr1 hqr x hx) z hz

end RHTower.GibbsGas
