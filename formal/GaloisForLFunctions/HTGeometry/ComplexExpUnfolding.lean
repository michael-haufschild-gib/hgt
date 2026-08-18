import GaloisForLFunctions.HTGeometry.PerPairGapUnbounded

/-!
# Unfolding an exponential polynomial

Write an exponent as `λ = Re λ + i Im λ`.  The character `t ↦ e^{λ t}` is the restriction to the
diagonal of the two-variable character

`(t, u) ↦ e^{(Re λ) t + i (Im λ) u}`,

which separates the growth variable from the phase variable.  The **unfolding** of an exponential
polynomial is the corresponding two-variable function; the polynomial is recovered on `u = t`.

The unfolding is well defined: it depends only on the function, not on the presentation.  That is
the content of this file — distinct complex exponents give linearly independent characters
(proved by iterated differentiation at the origin followed by Lagrange interpolation), so any
relation among characters descends to the same relation among unfolded characters.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The two-variable character underlying `t ↦ e^{λ t}`: the real part of the exponent acts on the
first variable, the imaginary part on the second. -/
noncomputable def unfoldChar (ν : ℂ) (t u : ℝ) : ℂ :=
  Complex.exp ((ν.re * t : ℝ) + Complex.I * ((ν.im * u : ℝ) : ℂ))

theorem unfoldChar_diag (ν : ℂ) (t : ℝ) : unfoldChar ν t t = Complex.exp (ν * t) := by
  rw [unfoldChar]
  congr 1
  apply Complex.ext <;> simp

theorem unfoldChar_conj (ν : ℂ) (t u : ℝ) :
    (starRingEnd ℂ) (unfoldChar ν t u) = unfoldChar ((starRingEnd ℂ) ν) t u := by
  rw [unfoldChar, unfoldChar, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

theorem unfoldChar_add (ν ν' : ℂ) (t u : ℝ) :
    unfoldChar (ν + ν') t u = unfoldChar ν t u * unfoldChar ν' t u := by
  rw [unfoldChar, unfoldChar, unfoldChar, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-! ## Independence of characters -/

theorem hasDerivAt_cexp_mul (y : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (y * s)) (y * Complex.exp (y * t)) t := by
  have hb : HasDerivAt (fun s : ℝ => (y * (s : ℂ))) y t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul y
  exact (hb.cexp).congr_deriv (by ring)

theorem iteratedDeriv_expCombo {S : Finset ℂ} (C : ℂ → ℂ) :
    ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => ∑ y ∈ S, C y * Complex.exp (y * t))
      = fun t : ℝ => ∑ y ∈ S, C y * y ^ k * Complex.exp (y * t) := by
  intro k
  induction k with
  | zero => funext t; simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hterm : ∀ y ∈ S, HasDerivAt (fun s : ℝ => C y * y ^ n * Complex.exp (y * s))
        (C y * y ^ (n + 1) * Complex.exp (y * t)) t := by
      intro y _
      refine ((hasDerivAt_cexp_mul y t).const_mul (C y * y ^ n)).congr_deriv ?_
      ring
    have hsum := HasDerivAt.sum hterm
    have heq : (fun t : ℝ => ∑ y ∈ S, C y * y ^ n * Complex.exp (y * t))
        = ∑ y ∈ S, (fun s : ℝ => C y * y ^ n * Complex.exp (y * s)) := by
      funext s
      simp [Finset.sum_apply]
    rw [heq]
    exact hsum.deriv

private theorem iteratedDeriv_zero_fun : ∀ k : ℕ,
    iteratedDeriv k (fun _ : ℝ => (0 : ℂ)) = fun _ : ℝ => (0 : ℂ) := by
  intro k
  induction k with
  | zero => funext t; simp
  | succ n ih => rw [iteratedDeriv_succ, ih]; funext t; simp

theorem sum_mul_pow_eq_zero {S : Finset ℂ} {C : ℂ → ℂ}
    (h : ∀ t : ℝ, ∑ y ∈ S, C y * Complex.exp (y * t) = 0) (k : ℕ) :
    ∑ y ∈ S, C y * y ^ k = 0 := by
  have hfun : (fun t : ℝ => ∑ y ∈ S, C y * Complex.exp (y * t)) = fun _ : ℝ => (0 : ℂ) :=
    funext h
  have hd := iteratedDeriv_expCombo (S := S) C k
  rw [hfun, iteratedDeriv_zero_fun k] at hd
  have := congrFun hd 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at this
  exact this.symm

/-- **Lagrange interpolation kills the moments.**  If every power moment of a finite family of
weights over distinct complex nodes vanishes, the weights vanish. -/
theorem coeff_eq_zero_of_forall_pow {S : Finset ℂ} {D : ℂ → ℂ}
    (h : ∀ k : ℕ, ∑ y ∈ S, D y * y ^ k = 0) : ∀ y ∈ S, D y = 0 := by
  classical
  intro y₀ hy₀
  set p : Polynomial ℂ := ∏ y ∈ S.erase y₀, (Polynomial.X - Polynomial.C y) with hp
  have hev : ∑ y ∈ S, D y * p.eval y = 0 := by
    have hexp : ∀ y : ℂ, D y * p.eval y
        = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (D y * y ^ i) := by
      intro y
      rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ S) => hexp y), Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [← Finset.mul_sum, h i, mul_zero]
  have hzero : ∀ y ∈ S.erase y₀, D y * p.eval y = 0 := by
    intro y hy
    have hpy : p.eval y = 0 := by
      rw [hp, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hy (by simp)
    rw [hpy, mul_zero]
  have hsplit : ∑ y ∈ S, D y * p.eval y = D y₀ * p.eval y₀ := by
    rw [← Finset.add_sum_erase S _ hy₀, Finset.sum_eq_zero hzero, add_zero]
  rw [hsplit] at hev
  have hne : p.eval y₀ ≠ 0 := by
    rw [hp, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr (fun y hy => ?_)
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    exact fun hcon => (Finset.ne_of_mem_erase hy) hcon.symm
  exact (mul_eq_zero.mp hev).resolve_right hne

/-- **Characters with distinct exponents are independent.**  A vanishing finite combination of
`t ↦ e^{y t}` over distinct complex `y` has all coefficients zero. -/
theorem exp_coeff_eq_zero {S : Finset ℂ} {C : ℂ → ℂ}
    (h : ∀ t : ℝ, ∑ y ∈ S, C y * Complex.exp (y * t) = 0) : ∀ y ∈ S, C y = 0 :=
  coeff_eq_zero_of_forall_pow (fun k => sum_mul_pow_eq_zero h k)

/-! ## The unfolding is well defined -/

/-- **Transfer of relations to the unfolding.**  A vanishing finite combination of characters
unfolds to a vanishing combination of two-variable characters — the coefficients need not be
attached to distinct exponents. -/
theorem unfold_eq_zero_of_eq_zero {ι : Type*} {S : Finset ι} {c : ι → ℂ} {ν : ι → ℂ}
    (h : ∀ t : ℝ, ∑ i ∈ S, c i * Complex.exp (ν i * t) = 0) :
    ∀ t u : ℝ, ∑ i ∈ S, c i * unfoldChar (ν i) t u = 0 := by
  classical
  set T : Finset ℂ := S.image ν with hT
  have hmaps : ∀ i ∈ S, ν i ∈ T := fun i hi => Finset.mem_image_of_mem ν hi
  set C : ℂ → ℂ := fun y => ∑ i ∈ S.filter (fun i => ν i = y), c i with hC
  have hgroup : ∀ g : ℂ → ℂ, ∑ i ∈ S, c i * g (ν i) = ∑ y ∈ T, C y * g y := by
    intro g
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun i => c i * g (ν i))]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hC, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.mp hi).2]
  have hzero : ∀ y ∈ T, C y = 0 := by
    refine exp_coeff_eq_zero (S := T) (C := C) (fun t => ?_)
    rw [← hgroup (fun y => Complex.exp (y * t))]
    exact h t
  intro t u
  rw [hgroup (fun y => unfoldChar y t u)]
  exact Finset.sum_eq_zero (fun y hy => by rw [hzero y hy, zero_mul])

end GaloisForLFunctions.HTGeometry
