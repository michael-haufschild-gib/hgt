import GaloisForLFunctions.Hypertranscendence

/-!
# Finite exponential sums are differentially algebraic

A finite `ℂ`-linear combination of exponentials `∑ᵢ aᵢ·exp(cᵢ·x)` satisfies the constant-coefficient
linear ODE `∏ᵢ(D − cᵢ)y = 0`, so it is **differentially algebraic** (`differentiallyAlgebraic_finset_expSum`).
In particular every finite truncation of a Hurwitz-type Dirichlet series
`∑_{n∈s} (n+a)^{−x} = ∑_{n∈s} exp(−x·log(n+a))` is differentially algebraic
(`differentiallyAlgebraic_hurwitzTruncation`): the escape from the differentially-algebraic class — the
hypertranscendence of the full `ζ(a, ·)` — can happen only in the infinite limit, never at any finite
stage.  This locates the frontier the `Hypertranscendental` notion sets up precisely at the passage to
the infinite sum.
-/

open Complex Finset GaloisForLFunctions

namespace GaloisForLFunctions

theorem iteratedDeriv_exp_linear (c : ℂ) (j : ℕ) (x : ℂ) :
    iteratedDeriv j (fun x => Complex.exp (c * x)) x = c ^ j * Complex.exp (c * x) := by
  induction j generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have : deriv (fun x => iteratedDeriv n (fun x => Complex.exp (c * x)) x) x
        = deriv (fun x => c ^ n * Complex.exp (c * x)) x := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards with y using ih y
    rw [this]
    have h1 : HasDerivAt (fun x : ℂ => c * x) c x := by simpa using (hasDerivAt_id x).const_mul c
    have hd : HasDerivAt (fun x : ℂ => Complex.exp (c * x)) (Complex.exp (c * x) * c) x := h1.cexp
    rw [(hd.const_mul (c ^ n)).deriv]; ring

theorem iteratedDeriv_finset_expSum (s : Finset ℕ) (a c : ℕ → ℂ) (j : ℕ) (x : ℂ) :
    iteratedDeriv j (fun x => ∑ i ∈ s, a i * Complex.exp (c i * x)) x
      = ∑ i ∈ s, a i * c i ^ j * Complex.exp (c i * x) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert m t hmt ih =>
    have hfun : (fun x => ∑ i ∈ insert m t, a i * Complex.exp (c i * x))
        = (fun x => a m * Complex.exp (c m * x)) + (fun x => ∑ i ∈ t, a i * Complex.exp (c i * x)) := by
      funext x; simp [Finset.sum_insert hmt]
    have hterm : iteratedDeriv j (fun x => a m * Complex.exp (c m * x)) x
        = a m * (c m) ^ j * Complex.exp (c m * x) := by
      rw [iteratedDeriv_const_mul (a m)
          (by fun_prop : ContDiffAt ℂ j (fun x => Complex.exp (c m * x)) x), iteratedDeriv_exp_linear]
      ring
    rw [hfun, iteratedDeriv_add
        (by fun_prop : ContDiffAt ℂ j (fun x => a m * Complex.exp (c m * x)) x)
        (by fun_prop : ContDiffAt ℂ j (fun x => ∑ i ∈ t, a i * Complex.exp (c i * x)) x),
        hterm, ih, Finset.sum_insert hmt]

open MvPolynomial in
theorem differentiallyAlgebraic_finset_expSum (s : Finset ℕ) (a c : ℕ → ℂ) :
    DifferentiallyAlgebraic (fun x => ∑ i ∈ s, a i * Complex.exp (c i * x)) := by
  set N := s.card with hN
  set p : Polynomial ℂ := ∏ i ∈ s, (Polynomial.X - Polynomial.C (c i)) with hp
  have hpmon : p.Monic := Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (c i))
  have hpdeg : p.natDegree = N := by
    rw [hp, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (c i))]
    simp [hN]
  refine ⟨N, ∑ j : Fin (N+1), MvPolynomial.C (p.coeff j) * MvPolynomial.X j.succ, ?_, ?_⟩
  · -- P ≠ 0
    intro hP0
    have hp1 : p.coeff N = 1 := by rw [← hpdeg]; exact hpmon.coeff_natDegree
    have hev := congrArg (MvPolynomial.eval
      (fun v : Fin (N+2) => if v = (Fin.last N).succ then (1:ℂ) else 0)) hP0
    rw [map_sum, map_zero] at hev
    rw [Finset.sum_eq_single (Fin.last N)] at hev
    · simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.val_last, hp1] at hev
      simp at hev
    · intro b _ hb
      simp [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- vanishes
    intro z
    rw [map_sum]
    have hjet : ∀ j : Fin (N+1),
        MvPolynomial.eval (Fin.cons z (fun j : Fin (N + 1) =>
            iteratedDeriv (j : ℕ) (fun x => ∑ i ∈ s, a i * Complex.exp (c i * x)) z))
          (MvPolynomial.C (p.coeff j) * MvPolynomial.X j.succ)
          = p.coeff j * iteratedDeriv (j : ℕ) (fun x => ∑ i ∈ s, a i * Complex.exp (c i * x)) z := by
      intro j
      rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.cons_succ]
    simp_rw [hjet, iteratedDeriv_finset_expSum]
    have : ∀ j : Fin (N+1), p.coeff (j:ℕ) * ∑ i ∈ s, a i * c i ^ (j:ℕ) * Complex.exp (c i * z)
        = ∑ i ∈ s, a i * (p.coeff (j:ℕ) * c i ^ (j:ℕ)) * Complex.exp (c i * z) := by
      intro j; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hroot : p.eval (c i) = 0 := by
      rw [hp, Polynomial.eval_prod]
      exact Finset.prod_eq_zero hi (by simp)
    have hsum : ∑ j : Fin (N+1), a i * (p.coeff (j:ℕ) * c i ^ (j:ℕ)) * Complex.exp (c i * z)
        = a i * Complex.exp (c i * z) * ∑ j : Fin (N+1), p.coeff (j:ℕ) * c i ^ (j:ℕ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsum]
    have heval : ∑ j : Fin (N+1), p.coeff (j:ℕ) * c i ^ (j:ℕ) = p.eval (c i) := by
      rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < N + 1)]
      rw [Finset.sum_range fun j => p.coeff j * c i ^ j]
    rw [heval, hroot, mul_zero]

/-- **Every finite truncation of a Hurwitz-type Dirichlet series is differentially algebraic.**  For a
finite index set `s`, the partial sum `∑_{n∈s} exp(−x·log(n+a)) = ∑_{n∈s} (n+a)^{−x}` is differentially
algebraic — the finite instance of `differentiallyAlgebraic_finset_expSum` with unit coefficients and
frequencies `cₙ = −log(n+a)`.  Hypertranscendence of the full Hurwitz zeta, if it holds, is a purely
infinite-limit phenomenon. -/
theorem differentiallyAlgebraic_hurwitzTruncation (a : ℝ) (s : Finset ℕ) :
    DifferentiallyAlgebraic (fun x => ∑ n ∈ s, Complex.exp (-x * (Real.log ((n : ℝ) + a) : ℂ))) := by
  have heq : (fun x => ∑ n ∈ s, Complex.exp (-x * (Real.log ((n : ℝ) + a) : ℂ)))
      = (fun x => ∑ n ∈ s, (1 : ℂ) * Complex.exp ((-(Real.log ((n : ℝ) + a) : ℂ)) * x)) := by
    funext x; refine Finset.sum_congr rfl (fun n _ => ?_); rw [one_mul]; congr 1; ring
  rw [heq]
  exact differentiallyAlgebraic_finset_expSum s (fun _ => 1) (fun n => -(Real.log ((n : ℝ) + a) : ℂ))

end GaloisForLFunctions
