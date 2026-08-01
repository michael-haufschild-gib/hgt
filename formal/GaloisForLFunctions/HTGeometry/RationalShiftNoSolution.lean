import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The rational shift equation of the Stirling tail

The derivative of the formal digamma expansion satisfies `τ(s+1) − τ(s) = −s^{-2}`.  A rational
solution of that equation is impossible: clearing denominators, the value at `0` forces a pole at `0`
or at `1`; every nonzero pole is followed by a pole one step up and every pole other than `1` is
preceded by a pole one step down, so the pole of largest real part is `0` while the pole of smallest
real part is `1` — incompatible.

This is the elementary pole-orbit argument behind the hypertranscendence of the Stirling tail: the
tail is not rational, so no differential-rational expression in the digamma tower can cancel to all
algebraic-logarithmic orders.

The meromorphic form of the same obstruction is `no_finitePole_solution_digammaShiftDerivative`,
which assumes the shift identity at every point of `ℂ`; the polynomial form below carries no
hypothesis at the poles.
-/

open Polynomial

namespace GaloisForLFunctions

/-- The unit shift `p(X) ↦ p(X + 1)` on polynomials. -/
noncomputable def shiftOne (p : ℂ[X]) : ℂ[X] := p.comp (X + 1)

@[simp] theorem eval_shiftOne (p : ℂ[X]) (a : ℂ) : (shiftOne p).eval a = p.eval (a + 1) := by
  simp [shiftOne, Polynomial.eval_comp]

theorem shiftOne_mul (p q : ℂ[X]) : shiftOne (p * q) = shiftOne p * shiftOne q := by
  simp [shiftOne, Polynomial.mul_comp]

theorem shiftOne_X_sub_C (a : ℂ) : shiftOne (X - C a) = X + 1 - C a := by
  simp [shiftOne, Polynomial.sub_comp]

theorem shiftOne_ne_zero {p : ℂ[X]} (hp : p ≠ 0) : shiftOne p ≠ 0 := by
  intro h
  apply hp
  have hcomp : (shiftOne p).comp (X - 1) = p := by
    simp [shiftOne, Polynomial.comp_assoc]
  rw [h] at hcomp
  simpa using hcomp.symm

/-- The cleared-denominator form of the shift equation `y(s+1) − y(s) = −1/s²`. -/
def IsShiftInvSqSolution (p q : ℂ[X]) : Prop :=
  X ^ 2 * (shiftOne p * q - p * shiftOne q) = -(q * shiftOne q)

theorem eval_of_solution {p q : ℂ[X]} (h : IsShiftInvSqSolution p q) (a : ℂ) :
    a ^ 2 * (p.eval (a + 1) * q.eval a - p.eval a * q.eval (a + 1))
      = -(q.eval a * q.eval (a + 1)) := by
  have := congrArg (fun r : ℂ[X] => r.eval a) h
  simpa using this

/-- **A reduced fraction cannot solve the shift equation.**  The equation forces `0` or `1` to be a
pole; every nonzero pole is followed by a pole one step up, and every pole other than `1` is preceded
by a pole one step down, so the poles of largest and smallest real part would have to be `0` and `1`
simultaneously. -/
theorem no_solution_of_coprime {p q : ℂ[X]} (hq : q ≠ 0) (hcop : IsCoprime p q)
    (h : IsShiftInvSqSolution p q) : False := by
  classical
  -- the value at zero forces a root at `0` or at `1`
  have h0 := eval_of_solution h 0
  have hroot01 : q.eval 0 = 0 ∨ q.eval 1 = 0 := by
    have hz : q.eval 0 * q.eval (0 + 1) = 0 := by
      linear_combination h0
    simpa using mul_eq_zero.mp hz
  -- coprime polynomials have no common root
  have hpq : ∀ a : ℂ, q.eval a = 0 → p.eval a ≠ 0 := by
    intro a ha hpa
    have hdvd : (X - C a) ∣ p := dvd_iff_isRoot.mpr hpa
    have hdvq : (X - C a) ∣ q := dvd_iff_isRoot.mpr ha
    have hunit : IsUnit (X - C a : ℂ[X]) := hcop.isUnit_of_dvd' hdvd hdvq
    have hdeg : (X - C a : ℂ[X]).degree = 0 := _root_.Polynomial.isUnit_iff_degree_eq_zero.mp hunit
    rw [Polynomial.degree_X_sub_C] at hdeg
    exact one_ne_zero hdeg
  -- roots propagate upwards and downwards
  have hup : ∀ a : ℂ, q.eval a = 0 → a ≠ 0 → q.eval (a + 1) = 0 := by
    intro a ha ha0
    have hev := eval_of_solution h a
    rw [ha] at hev
    have hz : a ^ 2 * (p.eval a * q.eval (a + 1)) = 0 := by linear_combination -hev
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1) ha0
    · rcases mul_eq_zero.mp h2 with h3 | h4
      · exact absurd h3 (hpq a ha)
      · exact h4
  have hdown : ∀ a : ℂ, q.eval a = 0 → a ≠ 1 → q.eval (a - 1) = 0 := by
    intro a ha ha1
    have hev := eval_of_solution h (a - 1)
    have hsub : a - 1 + 1 = a := by ring
    rw [hsub, ha] at hev
    have hz : (a - 1) ^ 2 * (p.eval a * q.eval (a - 1)) = 0 := by linear_combination hev
    rcases mul_eq_zero.mp hz with h1 | h2
    · have : a - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      exact absurd (by linear_combination this) ha1
    · rcases mul_eq_zero.mp h2 with h3 | h4
      · exact absurd h3 (hpq a ha)
      · exact h4
  -- the root set is finite and nonempty, and its extreme real parts collide
  set S : Finset ℂ := q.roots.toFinset with hS
  have hmemS : ∀ a : ℂ, a ∈ S ↔ q.eval a = 0 := by
    intro a
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_roots hq]
    exact Iff.rfl
  have hne : S.Nonempty := by
    rcases hroot01 with h1 | h1
    · exact ⟨0, (hmemS 0).mpr h1⟩
    · exact ⟨1, (hmemS 1).mpr h1⟩
  obtain ⟨a0, ha0S, hmax⟩ := S.exists_max_image (fun a : ℂ => a.re) hne
  obtain ⟨a1, ha1S, hmin⟩ := S.exists_min_image (fun a : ℂ => a.re) hne
  have ha0 : a0 = 0 := by
    by_contra hcon
    have hroot := hup a0 ((hmemS a0).mp ha0S) hcon
    have := hmax (a0 + 1) ((hmemS _).mpr hroot)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith
  have ha1 : a1 = 1 := by
    by_contra hcon
    have hroot := hdown a1 ((hmemS a1).mp ha1S) hcon
    have := hmin (a1 - 1) ((hmemS _).mpr hroot)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have hcontr := hmin a0 ha0S
  rw [ha0, ha1] at hcontr
  norm_num at hcontr

/-- The equation has no solution in any representation, by descent on a common root. -/
theorem no_shift_inv_sq_solution :
    ∀ (n : ℕ) (p q : ℂ[X]), q.natDegree = n → q ≠ 0 → ¬ IsShiftInvSqSolution p q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p q hdeg hq h
    classical
    by_cases hcop : IsCoprime p q
    · exact no_solution_of_coprime hq hcop h
    · -- a common root lets the equation descend
      have hgcd : ¬ IsUnit (EuclideanDomain.gcd p q) := fun hu =>
        hcop (_root_.EuclideanDomain.gcd_isUnit_iff.mp hu)
      have hgne : EuclideanDomain.gcd p q ≠ 0 := by
        intro h0
        exact hq (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
      have hdegpos : 0 < (EuclideanDomain.gcd p q).degree := by
        rcases lt_trichotomy (0 : WithBot ℕ) (EuclideanDomain.gcd p q).degree with hlt | heq | hgt
        · exact hlt
        · exact absurd (_root_.Polynomial.isUnit_iff_degree_eq_zero.mpr heq.symm) hgcd
        · exact absurd (Polynomial.degree_eq_bot.mp (by
            have := Polynomial.zero_le_degree_iff.mpr hgne
            exact absurd hgt (not_lt.mpr this))) hgne
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_root (k := ℂ) (EuclideanDomain.gcd p q)
        (ne_of_gt hdegpos)
      have hpa : p.eval a = 0 := by
        obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_left p q
        rw [hc, Polynomial.eval_mul, ha, zero_mul]
      have hqa : q.eval a = 0 := by
        obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_right p q
        rw [hc, Polynomial.eval_mul, ha, zero_mul]
      obtain ⟨p', hp'⟩ : (X - C a) ∣ p := dvd_iff_isRoot.mpr hpa
      obtain ⟨q', hq'⟩ : (X - C a) ∣ q := dvd_iff_isRoot.mpr hqa
      have hq'ne : q' ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hq'
        exact hq hq'
      have hfac : ((X : ℂ[X]) - C a) * (X + 1 - C a) ≠ 0 := by
        refine mul_ne_zero (Polynomial.X_sub_C_ne_zero a) ?_
        have hrw : (X : ℂ[X]) + 1 - C a = X - C (a - 1) := by
          rw [Polynomial.C_sub, Polynomial.C_1]
          ring
        rw [hrw]
        exact Polynomial.X_sub_C_ne_zero _
      have hsol' : IsShiftInvSqSolution p' q' := by
        rw [IsShiftInvSqSolution]
        refine mul_left_cancel₀ hfac ?_
        rw [hp', hq', IsShiftInvSqSolution, shiftOne_mul, shiftOne_mul, shiftOne_X_sub_C] at h
        linear_combination h
      have hdeglt : q'.natDegree < n := by
        have := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq'ne
        rw [hq'] at hdeg
        rw [this, Polynomial.natDegree_X_sub_C] at hdeg
        omega
      exact ih q'.natDegree hdeglt p' q' rfl hq'ne hsol'

/-- **The shift equation `y(s+1) − y(s) = −1/s²` has no rational solution.** -/
theorem no_rational_shift_inv_sq (p q : ℂ[X]) (hq : q ≠ 0) : ¬ IsShiftInvSqSolution p q :=
  no_shift_inv_sq_solution q.natDegree p q rfl hq

end GaloisForLFunctions
