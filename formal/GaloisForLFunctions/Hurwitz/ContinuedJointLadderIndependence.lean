import GaloisForLFunctions.Hurwitz.ContinuedJointLadderDeformationBridge

/-!
# Unrestricted joint continued-Hurwitz ladder independence

The product power-grid argument now consumes the unrestricted continued monodromy bridge.  The
result is algebraic independence of every finite rectangle of exponent-shifted continued Hurwitz
values, without a convergence-half-plane assumption.
-/

open Complex HurwitzZetaShift HurwitzOrbit

namespace HurwitzJointLadder

open HurwitzLadder HurwitzJointOrbit HurwitzZetaContinuation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Unrestricted joint continued-Hurwitz ladder independence.** -/
theorem continued_joint_hurwitz_ladder_independence
    {s : ι → ℂ}
    (hmono : Function.Injective (monomialValue (fun j => monoScalar (s j))))
    (N : ℕ) (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => continuedHzeta (s jk.1 + (jk.2 : ℕ)) a) P = 0) :
    P = 0 := by
  have h1 : ∀ a : ℂ, 0 < a.im →
      continuedJointRelA s N P (fun _ _ => 1) a = 0 := by
    intro a ha
    have hg : (fun jk : ι × Fin (N + 1) =>
        continuedDzeta (s jk.1) N (fun _ => 1) (jk.2 : ℕ) a) =
        fun jk => continuedHzeta (s jk.1 + (jk.2 : ℕ)) a := by
      funext jk
      exact continuedDzeta_one (s jk.1) N (jk.2 : ℕ) a
    rw [continuedJointRelA, hg]
    exact hrel a ha
  have hgrid := continuedJointRelA_grid P h1
  have hmap : ∀ a : ℂ, 0 < a.im → MvPolynomial.map (Polynomial.evalRingHom a) P = 0 := by
    intro a ha
    set w : (ι × Fin (N + 1)) → Fin (N + 1) → ℂ := fun jk n =>
      ((((n : ℕ) : ℂ)) + a) ^ (-(s jk.1 + (jk.2 : ℕ))) with hw
    set base : (ι × Fin (N + 1)) → ℂ := fun jk =>
      continuedHzeta (s jk.1 + (jk.2 : ℕ)) a -
        ∑ n : Fin (N + 1), w jk n with hbase
    have hdz : ∀ (c : ι → Fin (N + 1) → ℂ) (jk : ι × Fin (N + 1)),
        continuedDzeta (s jk.1) N (c jk.1) (jk.2 : ℕ) a =
          base jk + ∑ n : Fin (N + 1), w jk n * c jk.1 n := by
      intro c jk
      rw [continuedDzeta, hbase]
      have hterm : ∀ n : Fin (N + 1),
          (c jk.1 n - 1) *
              ((((n : ℕ) : ℂ) + a) ^ (-(s jk.1 + (jk.2 : ℕ)))) =
            w jk n * c jk.1 n - w jk n := by
        intro n
        rw [hw]
        ring
      rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_sub_distrib]
      ring
    set Pa : MvPolynomial (ι × Fin (N + 1)) ℂ :=
      MvPolynomial.map (Polynomial.evalRingHom a) P with hPa
    set sub : (ι × Fin (N + 1)) → MvPolynomial (ι × Fin (N + 1)) ℂ := fun jk =>
      MvPolynomial.C (base jk) +
        ∑ n : Fin (N + 1), MvPolynomial.C (w jk n) * MvPolynomial.X (jk.1, n) with hsub
    have heval : ∀ c : ι → Fin (N + 1) → ℂ,
        MvPolynomial.eval (fun jn => c jn.1 jn.2) (MvPolynomial.aeval sub Pa) =
          continuedJointRelA s N P c a := by
      intro c
      rw [eval_aeval_joint]
      have hsubeval :
          (fun jk => MvPolynomial.eval (fun jn => c jn.1 jn.2) (sub jk)) =
            fun jk => continuedDzeta (s jk.1) N (c jk.1) (jk.2 : ℕ) a := by
        funext jk
        rw [hsub]
        simp only [map_add, MvPolynomial.eval_C, map_sum, map_mul, MvPolynomial.eval_X]
        rw [hdz c jk]
      rw [hsubeval, hPa, MvPolynomial.eval_map]
      rfl
    have hΨ0 : MvPolynomial.aeval sub Pa = 0 := by
      apply mv_power_grid_zero (fun j => monoScalar (s j)) hmono (N + 1)
      intro m
      have he := heval (fun j n => monoScalar (s j) ^ m n)
      simpa using he.trans (hgrid m a ha)
    have hall : ∀ lam : ι → Fin (N + 1) → ℂ,
        continuedJointRelA s N P lam a = 0 := by
      intro lam
      rw [← heval lam, hΨ0, map_zero]
    have hy : ∀ y : (ι × Fin (N + 1)) → ℂ, MvPolynomial.eval y Pa = 0 := by
      intro y
      choose lam hlam using fun j : ι =>
        ladder_matrix_surjective (s := s j) ha N (fun k => y (j, k) - base (j, k))
      have hdzy : (fun jk =>
          continuedDzeta (s jk.1) N (lam jk.1) (jk.2 : ℕ) a) = y := by
        funext jk
        rw [hdz lam jk]
        have hk := hlam jk.1 jk.2
        rw [show (∑ n : Fin (N + 1), w jk n * lam jk.1 n) =
            y jk - base jk by simpa [hw] using hk]
        ring
      have hrel_lam := hall lam
      rw [continuedJointRelA,
        ← MvPolynomial.eval_map (Polynomial.evalRingHom a), hdzy] at hrel_lam
      exact hrel_lam
    refine MvPolynomial.funext (fun y => ?_)
    rw [hy y, map_zero]
  have hcoeff : ∀ d : (ι × Fin (N + 1)) →₀ ℕ, MvPolynomial.coeff d P = 0 := by
    intro d
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective
        (fun t : ℕ => (((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I) := by
      intro t₁ t₂ h
      have him := congrArg Complex.im h
      simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_one, mul_zero, add_zero] at him
      have ht : (t₁ : ℝ) = (t₂ : ℝ) := by linarith
      exact_mod_cast ht
    have hsub : Set.range (fun t : ℕ => (((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I) ⊆
        {x | Polynomial.IsRoot (MvPolynomial.coeff d P) x} := by
      rintro x ⟨t, rfl⟩
      have him : 0 < ((((t : ℝ) + 1 : ℝ) : ℂ) * Complex.I).im := by
        simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_one, mul_zero, add_zero]
        positivity
      have hm := hmap _ him
      have hc := congrArg (MvPolynomial.coeff d) hm
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at hc
      exact hc
    exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)
  exact MvPolynomial.ext _ _ (fun d => by rw [hcoeff d, MvPolynomial.coeff_zero])

/-- Augmented rational independence supplies unrestricted continued-ladder independence. -/
theorem continued_joint_hurwitz_ladder_independence_of_linearIndependent
    {s : ι → ℂ} (hsQ : LinearIndependent ℚ (exponentFamily s))
    (N : ℕ) (P : MvPolynomial (ι × Fin (N + 1)) (Polynomial ℂ))
    (hrel : ∀ a : ℂ, 0 < a.im →
      MvPolynomial.eval₂ (Polynomial.evalRingHom a)
        (fun jk => continuedHzeta (s jk.1 + (jk.2 : ℕ)) a) P = 0) :
    P = 0 :=
  continued_joint_hurwitz_ladder_independence
    (monomialValue_monoScalar_injective_of_linearIndependent s hsQ) N P hrel

end HurwitzJointLadder
