import GaloisForLFunctions.SchwartzCompactPolynomialSeparation

/-!
# Smooth polynomial approximation on compact real intervals

Ordinary Weierstrass approximation can be upgraded to simultaneous approximation through every
prescribed finite derivative order.  The proof is constructive: approximate the derivative, take
an explicit anchored polynomial antiderivative, and use the mean-value inequality to recover the
zeroth-order estimate.
-/

open Filter Set
open scoped Polynomial Topology

noncomputable section

namespace Polynomial

/-- The coefficientwise real polynomial antiderivative with zero constant term. -/
def realAntiderivative (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => C (a / (n + 1 : ℝ)) * X ^ (n + 1)

theorem derivative_realAntiderivative (p : ℝ[X]) :
    derivative (realAntiderivative p) = p := by
  calc
    derivative (realAntiderivative p) =
        ∑ n ∈ p.support,
          derivative (C (p.coeff n / (n + 1 : ℝ)) * X ^ (n + 1)) := by
      rw [realAntiderivative, Polynomial.sum, derivative_sum]
    _ = ∑ n ∈ p.support, C (p.coeff n) * X ^ n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [derivative_C_mul_X_pow]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        C_mul_X_pow_eq_monomial]
      field_simp
    _ = p := by
      simpa only [Polynomial.sum] using p.sum_C_mul_X_pow_eq

theorem hasDerivAt_eval_realAntiderivative (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y => (realAntiderivative p).eval y) (p.eval x) x := by
  simpa [derivative_realAntiderivative] using
    (realAntiderivative p).hasDerivAt x

/-- Antiderivative of `p` taking the prescribed value `c` at the anchor `a`. -/
def anchoredRealAntiderivative (p : ℝ[X]) (a c : ℝ) : ℝ[X] :=
  C (c - (realAntiderivative p).eval a) + realAntiderivative p

@[simp] theorem eval_anchoredRealAntiderivative_anchor (p : ℝ[X]) (a c : ℝ) :
    (anchoredRealAntiderivative p a c).eval a = c := by
  simp [anchoredRealAntiderivative]

theorem derivative_anchoredRealAntiderivative (p : ℝ[X]) (a c : ℝ) :
    derivative (anchoredRealAntiderivative p a c) = p := by
  simp [anchoredRealAntiderivative, derivative_realAntiderivative]

theorem eval_anchoredRealAntiderivative_eq_add_integral
    (p : ℝ[X]) (a c x : ℝ) :
    (anchoredRealAntiderivative p a c).eval x = c + ∫ t in a..x, p.eval t := by
  have hFTC : ∫ t in a..x, p.eval t =
      (realAntiderivative p).eval x - (realAntiderivative p).eval a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _ht
      exact hasDerivAt_eval_realAntiderivative p t
    · exact (Polynomial.continuous _).intervalIntegrable _ _
  rw [hFTC]
  simp [anchoredRealAntiderivative]
  ring

/-- Analytic iterated derivatives of a polynomial evaluation agree with iterated formal
polynomial derivatives. -/
theorem iteratedDeriv_eval_eq_eval_iterateDerivative
    (P : ℝ[X]) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y => P.eval y) x = (derivative^[k] P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = k.succ by omega, Function.iterate_succ_apply]
      rw [show iteratedDeriv k.succ (fun y => P.eval y) =
          iteratedDeriv k (deriv fun y => P.eval y) by
            simpa using (iteratedDeriv_succ' (n := k) (f := fun y => P.eval y))]
      have hderiv : deriv (fun y => P.eval y) = fun y => P.derivative.eval y := by
        funext y
        exact (P.hasDerivAt y).deriv
      rw [hderiv, ih]

/-- **Smooth Weierstrass approximation.**  A smooth real function on a compact interval can be
simultaneously approximated, with one polynomial, through any prescribed finite derivative order.
-/
theorem exists_polynomial_near_contDiff_iteratedDeriv
    (N : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∃ P : ℝ[X], ∀ k : ℕ, k ≤ N → ∀ x ∈ Icc a b,
      |(derivative^[k] P).eval x - iteratedDeriv k f x| < ε := by
  induction N generalizing f ε with
  | zero =>
      obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn
        a b f hf.continuous.continuousOn ε hε
      refine ⟨P, ?_⟩
      intro k hk x hx
      have hk0 : k = 0 := by omega
      subst k
      simpa using hP x hx
  | succ N ih =>
      let δ : ℝ := ε / (1 + (b - a))
      have hden : 0 < 1 + (b - a) := by linarith
      have hδ : 0 < δ := div_pos hε hden
      have hf' : ContDiff ℝ (⊤ : ℕ∞) (deriv f) :=
        (contDiff_infty_iff_deriv.mp hf).2
      obtain ⟨Q, hQ⟩ := ih hf' hδ
      let P : ℝ[X] := anchoredRealAntiderivative Q a (f a)
      refine ⟨P, ?_⟩
      intro k hk x hx
      cases k with
      | zero =>
          let E : ℝ → ℝ := fun y => P.eval y - f y
          have hPderiv : derivative P = Q :=
            derivative_anchoredRealAntiderivative Q a (f a)
          have hEcont : ContinuousOn E (Icc a b) :=
            (P.continuous.sub hf.continuous).continuousOn
          have hEderiv : ∀ y ∈ Ico a b,
              HasDerivWithinAt E (Q.eval y - deriv f y) (Ici y) y := by
            intro y _hy
            have hPy := P.hasDerivAt y
            rw [hPderiv] at hPy
            exact (hPy.sub ((contDiff_infty_iff_deriv.mp hf).1 y |>.hasDerivAt)).hasDerivWithinAt
          have hbound : ∀ y ∈ Ico a b, ‖Q.eval y - deriv f y‖ ≤ δ := by
            intro y hy
            have hnear := hQ 0 (by omega) y (Ico_subset_Icc_self hy)
            simpa [Real.norm_eq_abs] using hnear.le
          have hmv := norm_image_sub_le_of_norm_deriv_right_le_segment
            hEcont hEderiv hbound x hx
          have hEa : E a = 0 := by
            simp [E, P, eval_anchoredRealAntiderivative_anchor]
          have hdeltaL : δ * (b - a) < ε := by
            dsimp [δ]
            rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
            nlinarith
          have hxa : x - a ≤ b - a := by linarith [hx.2]
          have hnonneg : 0 ≤ δ := hδ.le
          simpa [iteratedDeriv_zero, E, hEa, Real.norm_eq_abs] using
            lt_of_le_of_lt (hmv.trans (mul_le_mul_of_nonneg_left hxa hnonneg)) hdeltaL
      | succ j =>
          have hj : j ≤ N := by omega
          have hnear := hQ j hj x hx
          have hPderiv : derivative P = Q :=
            derivative_anchoredRealAntiderivative Q a (f a)
          rw [Function.iterate_succ_apply, hPderiv, iteratedDeriv_succ']
          have hδε : δ ≤ ε := by
            dsimp [δ]
            rw [div_le_iff₀ hden]
            nlinarith
          exact hnear.trans_le hδε

/-- Diagonal form of smooth Weierstrass approximation: one polynomial sequence converges through
every fixed derivative order, uniformly on the compact interval. -/
theorem exists_polynomial_sequence_eventually_near_all_iteratedDeriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ P : ℕ → ℝ[X], ∀ k : ℕ, ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ x ∈ Icc a b,
        |(derivative^[k] (P n)).eval x - iteratedDeriv k f x| < ε := by
  have hex : ∀ n : ℕ, ∃ P : ℝ[X], ∀ k : ℕ, k ≤ n → ∀ x ∈ Icc a b,
      |(derivative^[k] P).eval x - iteratedDeriv k f x| < (1 : ℝ) / (n + 1) := by
    intro n
    exact exists_polynomial_near_contDiff_iteratedDeriv n hf hab (by positivity)
  choose P hP using hex
  refine ⟨P, ?_⟩
  intro k ε hε
  have hrate : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε))
  have hk : ∀ᶠ n : ℕ in atTop, k ≤ n := eventually_ge_atTop k
  filter_upwards [hrate, hk] with n hn hkn
  intro x hx
  exact (hP n k hkn x hx).trans hn

end Polynomial
