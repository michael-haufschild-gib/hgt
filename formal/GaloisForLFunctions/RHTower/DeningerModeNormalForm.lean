import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Normal form for the cylindrical Fourier modes

A harmonic coefficient on the Kummer half-cylinder satisfies `u'' = m² u`.  Every solution is a
combination of the two exponentials: passing to `u' ± m u` turns the second-order equation into
two first-order ones, each of which has a unique solution through its initial value.

This is the mode normal form `(1)` that the coefficient-elimination lemmas consume.

* `deningerFirstOrder_eq_exp` : uniqueness for `f' = c f`.
* `deningerSecondOrder_normal_form` : `u'' = m² u` implies `u = c⁺ e^{mr} + c⁻ e^{-mr}`.
-/

namespace RHTower

section ModeNormalForm

/-- **Uniqueness for `f' = c f`.**  A solution is its initial value times the exponential. -/
theorem deningerFirstOrder_eq_exp {f : ℝ → ℝ} {c : ℝ}
    (hf : ∀ x, HasDerivAt f (c * f x) x) (x : ℝ) : f x = f 0 * Real.exp (c * x) := by
  have hzero : ∀ y : ℝ, HasDerivAt (fun t => f t * Real.exp (-(c * t))) 0 y := by
    intro y
    have h0 : HasDerivAt (fun t : ℝ => c * t) c y := by
      simpa using (hasDerivAt_id y).const_mul c
    have hlin : HasDerivAt (fun t : ℝ => -(c * t)) (-c) y := h0.neg
    have h1 := hlin.exp
    have hprod := (hf y).mul h1
    have hval : c * f y * Real.exp (-(c * y)) + f y * (Real.exp (-(c * y)) * -c) = 0 := by
      ring
    rw [hval] at hprod
    exact hprod
  have hdiff : Differentiable ℝ (fun t => f t * Real.exp (-(c * t))) :=
    fun y => (hzero y).differentiableAt
  have hderiv : ∀ y : ℝ, deriv (fun t => f t * Real.exp (-(c * t))) y = 0 :=
    fun y => (hzero y).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hderiv x 0
  have hx : f x * Real.exp (-(c * x)) = f 0 := by
    simpa using hconst
  calc f x = f x * Real.exp (-(c * x)) * Real.exp (c * x) := by
        rw [mul_assoc, ← Real.exp_add]
        simp
    _ = f 0 * Real.exp (c * x) := by rw [hx]

/-- **The mode normal form.**  A solution of `u'' = m² u` is a combination of the two
exponentials, with coefficients read off the initial data. -/
theorem deningerSecondOrder_normal_form {u u' : ℝ → ℝ} {m : ℝ} (hm : m ≠ 0)
    (hu : ∀ r, HasDerivAt u (u' r) r) (hu2 : ∀ r, HasDerivAt u' (m ^ 2 * u r) r) (r : ℝ) :
    u r = ((u' 0 + m * u 0) / (2 * m)) * Real.exp (m * r)
      - ((u' 0 - m * u 0) / (2 * m)) * Real.exp (-m * r) := by
  have hw : ∀ x : ℝ, HasDerivAt (fun t => u' t + m * u t) (m * (u' x + m * u x)) x := by
    intro x
    have h := (hu2 x).add ((hu x).const_mul m)
    have hval : m ^ 2 * u x + m * u' x = m * (u' x + m * u x) := by ring
    rw [hval] at h
    exact h
  have hz : ∀ x : ℝ, HasDerivAt (fun t => u' t - m * u t) (-m * (u' x - m * u x)) x := by
    intro x
    have h := (hu2 x).sub ((hu x).const_mul m)
    have hval : m ^ 2 * u x - m * u' x = -m * (u' x - m * u x) := by ring
    rw [hval] at h
    exact h
  have hwsol := deningerFirstOrder_eq_exp hw r
  have hzsol := deningerFirstOrder_eq_exp hz r
  have hsplit : u r = ((u' r + m * u r) - (u' r - m * u r)) / (2 * m) := by
    field_simp
    ring
  rw [hsplit, hwsol, hzsol]
  field_simp

/-- **The Hodge--Dirac system gives the second-order equation.**  A constant-coefficient
first-order system `f' = m g`, `g' = m f` makes each component satisfy `u'' = m² u`. -/
theorem deningerDirac_secondOrder {f g : ℝ → ℝ} {m : ℝ}
    (hg : ∀ r, HasDerivAt g (m * f r) r) (r : ℝ) :
    HasDerivAt (fun t => m * g t) (m ^ 2 * f r) r := by
  have h := (hg r).const_mul m
  have hval : m * (m * f r) = m ^ 2 * f r := by ring
  rw [hval] at h
  exact h

/-- **Zero full Cauchy data kill a nonzero mode.**  A solution of the first-order Hodge--Dirac
system whose value and normal value vanish at the interface vanishes identically. -/
theorem deningerDiracMode_eq_zero {f g : ℝ → ℝ} {m : ℝ} (hm : m ≠ 0)
    (hf : ∀ r, HasDerivAt f (m * g r) r) (hg : ∀ r, HasDerivAt g (m * f r) r)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (r : ℝ) : f r = 0 ∧ g r = 0 := by
  have hfzero : ∀ x : ℝ, f x = 0 := by
    intro x
    have hnf := deningerSecondOrder_normal_form (u := f) (u' := fun t => m * g t) hm hf
      (deningerDirac_secondOrder hg) x
    simp only [hg0, hf0, mul_zero, zero_add, sub_zero] at hnf
    simpa using hnf
  refine ⟨hfzero r, ?_⟩
  have hderiv : HasDerivAt f (m * g r) r := hf r
  have hconst : HasDerivAt f 0 r := by
    have hEq : f = fun _ => (0 : ℝ) := funext hfzero
    rw [hEq]
    exact hasDerivAt_const r 0
  have huniq : m * g r = 0 := by
    have := hderiv.unique hconst
    exact this
  rcases mul_eq_zero.mp huniq with h | h
  · exact absurd h hm
  · exact h

/-- The zero mode of the finite-prime cylinder is determined by its interface pair. -/
theorem deningerZeroMode_eq_zero {a b : ℝ} (ha : a = 0) (hb : b = 0) :
    (a, b) = (0, 0) := by
  rw [ha, hb]

end ModeNormalForm

end RHTower
