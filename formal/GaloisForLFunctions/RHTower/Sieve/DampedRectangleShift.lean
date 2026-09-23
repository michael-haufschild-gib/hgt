import GaloisForLFunctions.RHTower.Sieve.DampedSmoothPerron
import GaloisForLFunctions.RHTower.Sieve.InvZetaProductShift

/-!
# The contour shift for the damped Dirichlet series

`Sieve/InvZetaRegular.integral_vertical_sub_eq_horizontal_rect` is generic: it needs only that the
integrand be differentiable on the rectangle.  The damped series' analytic continuation is `invZeta`
times the finite product of Euler corrections, and each correction is holomorphic wherever
`1 − p^{-s} ≠ 0`, which on `Re s ≥ c > 0` it is.  So the rectangle identity transfers with no new
contour work.
-/

namespace RHTower.Sieve

open Finset Complex GaloisForLFunctions.HTGeometry

noncomputable section

/-- The analytic continuation of the damped Möbius Dirichlet series. -/
def dampedInvZeta (P : Finset ℕ) (t : ℝ) (s : ℂ) : ℂ :=
  invZeta s * ∏ p ∈ P, dampedEulerFactor t p s

/-- The plain local factor is nonzero to the right of the imaginary axis. -/
theorem one_sub_cpow_ne_zero_of_pos_re {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  have hp1 : 1 ≤ p := by omega
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [RHTower.norm_natCast_cpow_zetaVerticalLineBound hp1, Complex.neg_re]
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  intro hcon
  have heq : (p : ℂ) ^ (-s) = 1 := by linear_combination -hcon
  rw [heq] at hnorm
  simp only [norm_one] at hnorm
  linarith [hnorm, hlt]

/-- A constant natural power is entire in the exponent. -/
theorem differentiable_natCast_cpow_neg {p : ℕ} (hp : 2 ≤ p) :
    Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) := by
  have hpne : ((p : ℕ) : ℂ) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast Nat.cast_ne_zero.2 (by omega)
  have hexp : (fun s : ℂ => (p : ℂ) ^ (-s))
      = fun s : ℂ => Complex.exp (Complex.log ((p : ℕ) : ℂ) * (-s)) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hpne]
  rw [hexp]
  exact Complex.differentiable_exp.comp (differentiable_neg.const_mul _)

/-- One Euler correction is holomorphic on the rectangle. -/
theorem differentiableOn_dampedEulerFactor_rect (t : ℝ) {p : ℕ} (hp : 2 ≤ p) {c d T : ℝ}
    (hc : 0 < c) (hcd : c ≤ d) :
    DifferentiableOn ℂ (fun s => dampedEulerFactor t p s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  have hpow := (differentiable_natCast_cpow_neg hp).differentiableOn
    (s := Set.uIcc c d ×ℂ Set.uIcc (-T) T)
  have hne : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    intro s hs
    have hre : s.re ∈ Set.uIcc c d := hs.1
    rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hre
    exact one_sub_cpow_ne_zero_of_pos_re hp (by linarith [hre.1])
  exact ((differentiableOn_const (1 : ℂ)).sub (hpow.const_mul ((t : ℝ) : ℂ))).div
    ((differentiableOn_const (1 : ℂ)).sub hpow) hne

/-- The finite Euler correction is holomorphic on the rectangle. -/
theorem differentiableOn_prod_dampedEulerFactor_rect {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q)
    (t : ℝ) {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    DifferentiableOn ℂ (fun s => ∏ p ∈ P, dampedEulerFactor t p s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert a Q ha ih =>
      have hfun : (fun s : ℂ => ∏ p ∈ insert a Q, dampedEulerFactor t p s)
          = fun s : ℂ => dampedEulerFactor t a s * ∏ p ∈ Q, dampedEulerFactor t p s := by
        funext s
        rw [Finset.prod_insert ha]
      rw [hfun]
      exact (differentiableOn_dampedEulerFactor_rect t
          (hP a (Finset.mem_insert_self a Q)) hc hcd).mul
        (ih (fun q hq => hP q (Finset.mem_insert_of_mem hq)))

/-- **The damped integrand is holomorphic on the rectangle.** -/
theorem differentiableOn_dampedInvZetaW_rect {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) (t : ℝ)
    {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ
      (fun s => dampedInvZeta P t s
        * mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  have hbase := differentiableOn_invZetaW_rect (N := N) hH hc hcd h
  have hprod := differentiableOn_prod_dampedEulerFactor_rect hP t (T := T) hc hcd
  have hfun : (fun s : ℂ => dampedInvZeta P t s
      * mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s)
      = fun s : ℂ => (invZeta s
          * mellin (fun x : ℝ => ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s)
        * ∏ p ∈ P, dampedEulerFactor t p s := by
    funext s
    rw [dampedInvZeta]
    ring
  rw [hfun]
  exact hbase.mul hprod

/-- **The rectangle identity for the damped integrand.** -/
theorem integral_dampedInvZetaW_vertical_sub_eq_horizontal_rect {P : Finset ℕ}
    (hP : ∀ q ∈ P, 2 ≤ q) (t : ℝ) {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    (Complex.I • (∫ y : ℝ in (-T)..T, dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T, dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, dampedInvZeta P t ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ =>
                ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, dampedInvZeta P t ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ =>
                ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T (differentiableOn_dampedInvZetaW_rect hP t hH hc hcd h)

end

end RHTower.Sieve
