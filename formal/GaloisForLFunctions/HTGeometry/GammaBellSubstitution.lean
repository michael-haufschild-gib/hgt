import GaloisForLFunctions.HTGeometry.DigammaHypertranscendental

/-!
# The Bell substitution: Γ-jets as Γ times digamma-jet polynomials

Iterating `Γ' = ψ·Γ` expresses every derivative of `Γ` as `Γ` times a polynomial in the
digamma jets: `Γ⁽ᵏ⁾ = Γ·B_k(ψ, ψ', …, ψ⁽ᵏ⁻¹⁾)`, with `B_0 = 1` and the Bell recurrence
`B_{k+1} = ψ·B_k + (d/ds)B_k`.  This module builds the family structurally:

* `bellCore k : MvPolynomial (Fin k) ℂ` — the `k`-th Bell polynomial in its minimal jet
  frame, and the evaluation identity `gamma_iteratedDeriv_eq_bellCore` off the poles.
* `pderiv_last_bellCore`, `bellCore_succ_decomp` — the recursion is triangular:
  `B_{k+1} = x_k + (polynomial in x_0, …, x_{k-1})`.
* `exists_bellCore_solution` — triangularity makes the Bell value map pointwise surjective:
  every target jet vector is realized, by recursive back-substitution.  This is the step
  that transports nonzeroness of a differential polynomial through the Bell substitution.
* `bellAt` — the family renamed into a common jet frame.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

/-- The Bell polynomials of the logarithmic derivative in their minimal jet frames:
`B_0 = 1`, `B_{k+1} = x_0·B_k + Σ_j ∂_j B_k · x_{j+1}`. -/
def bellCore : (k : ℕ) → MvPolynomial (Fin k) ℂ
  | 0 => 1
  | k + 1 =>
      X 0 * rename Fin.castSucc (bellCore k)
        + ∑ j : Fin k, rename Fin.castSucc (pderiv j (bellCore k)) * X j.succ

theorem bellCore_zero : bellCore 0 = 1 := rfl

theorem bellCore_succ (k : ℕ) :
    bellCore (k + 1)
      = X 0 * rename Fin.castSucc (bellCore k)
        + ∑ j : Fin k, rename Fin.castSucc (pderiv j (bellCore k)) * X j.succ := rfl

/-! ## The evaluation identity -/

/-- **The Bell chain**: `Γ⁽ᵏ⁾(s) = Γ(s)·B_k(ψ(s), …, ψ⁽ᵏ⁻¹⁾(s))` off the poles. -/
theorem gamma_iteratedDeriv_eq_bellCore (k : ℕ) :
    ∀ s : ℂ, (∀ p : ℕ, s ≠ -(p : ℂ)) →
      iteratedDeriv k Complex.Gamma s
        = Complex.Gamma s
          * eval (fun j : Fin k => iteratedDeriv (j : ℕ) Complex.digamma s) (bellCore k)
    := by
  have hψ : (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma := by
    funext w
    rw [Complex.digamma_def, logDeriv_apply]
  induction k with
  | zero =>
      intro s _
      simp [bellCore_zero, iteratedDeriv_zero]
  | succ k ih =>
      intro s hs
      have hev : (iteratedDeriv k Complex.Gamma)
          =ᶠ[nhds s] (fun w => Complex.Gamma w
            * eval (fun j : Fin k => iteratedDeriv (j : ℕ) Complex.digamma w)
                (bellCore k)) := by
        filter_upwards [offPoles_isOpen.mem_nhds hs] with w hw
        exact ih w hw
      have hg : ∀ j : Fin k,
          HasDerivAt (fun w => iteratedDeriv (j : ℕ) Complex.digamma w)
            (iteratedDeriv ((j : ℕ) + 1) Complex.digamma s) s := by
        intro j
        have h1 := (analyticAt_iteratedDeriv_logDeriv (j : ℕ) s hs).differentiableAt
        rw [hψ] at h1
        have h2 := h1.hasDerivAt
        rw [show iteratedDeriv ((j : ℕ) + 1) Complex.digamma s
            = deriv (iteratedDeriv (j : ℕ) Complex.digamma) s from by
          rw [iteratedDeriv_succ]]
        exact h2
      have hchain := hasDerivAt_mvEval_jet (bellCore k)
        (fun j => fun w => iteratedDeriv (j : ℕ) Complex.digamma w)
        (fun j => iteratedDeriv ((j : ℕ) + 1) Complex.digamma s) s hg
      have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
        (analyticAt_Gamma s hs).differentiableAt.hasDerivAt
      have hRHS := hΓ.mul hchain
      have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
      have hgpsi : deriv Complex.Gamma s = Complex.Gamma s * Complex.digamma s := by
        have := congrFun hψ s
        rw [← this]
        field_simp
      rw [iteratedDeriv_succ, hev.deriv_eq.trans hRHS.deriv, hgpsi]
      rw [bellCore_succ]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_succ,
        Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero]
      ring

/-! ## Triangularity -/

theorem bellCore_one : bellCore 1 = X 0 := by
  rw [bellCore_succ, bellCore_zero]
  simp

theorem pderiv_notMem_rename_castSucc {k : ℕ} (q : MvPolynomial (Fin k) ℂ) :
    pderiv (Fin.last k) (rename Fin.castSucc q) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hmem
  have := vars_rename Fin.castSucc q hmem
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp this
  have hval := congrArg Fin.val hj
  simp only [Fin.val_castSucc, Fin.val_last] at hval
  have := j.isLt
  omega

theorem pderiv_last_bellCore : ∀ k : ℕ, pderiv (Fin.last k) (bellCore (k + 1)) = 1 := by
  intro k
  induction k with
  | zero =>
      rw [bellCore_one]
      rw [show (Fin.last 0) = 0 from rfl]
      simp
  | succ k ih =>
      rw [bellCore_succ]
      rw [map_add]
      have h1 : pderiv (Fin.last (k + 1))
          (X 0 * rename Fin.castSucc (bellCore (k + 1))) = 0 := by
        rw [pderiv_mul, pderiv_notMem_rename_castSucc, mul_zero, add_zero]
        rw [pderiv_X_of_ne, zero_mul]
        intro hEq
        have hval := congrArg Fin.val hEq
        simp only [Fin.val_last, Fin.val_zero] at hval
        omega
      have h2 : pderiv (Fin.last (k + 1))
          (∑ j : Fin (k + 1),
            rename Fin.castSucc (pderiv j (bellCore (k + 1))) * X j.succ) = 1 := by
        rw [map_sum]
        rw [Finset.sum_eq_single (Fin.last k)]
        · rw [pderiv_mul, pderiv_notMem_rename_castSucc, zero_mul, zero_add,
            Fin.succ_last, pderiv_X_self, mul_one, ih, map_one]
        · intro j _ hj
          rw [pderiv_mul, pderiv_notMem_rename_castSucc, zero_mul, zero_add,
            pderiv_X_of_ne, mul_zero]
          intro hEq
          apply hj
          apply Fin.ext
          have hval := congrArg Fin.val hEq
          simp only [Fin.val_succ, Fin.val_last] at hval
          simp only [Fin.val_last]
          omega
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [h1, h2, zero_add]

/-- **Triangular decomposition**: `B_{k+1} = x_k + (a polynomial in `x_0, …, x_{k-1}`)`. -/
theorem bellCore_succ_decomp (k : ℕ) :
    ∃ T : MvPolynomial (Fin k) ℂ,
      bellCore (k + 1) = X (Fin.last k) + rename Fin.castSucc T := by
  cases k with
  | zero =>
      refine ⟨0, ?_⟩
      rw [bellCore_one, map_zero, add_zero]
      rfl
  | succ k =>
      refine ⟨X 0 * bellCore (k + 1)
        + ∑ i : Fin k,
            pderiv (Fin.castSucc i) (bellCore (k + 1)) * X i.succ, ?_⟩
      rw [bellCore_succ]
      rw [Fin.sum_univ_castSucc
        (f := fun j : Fin (k + 1) =>
          rename Fin.castSucc (pderiv j (bellCore (k + 1))) * X j.succ)]
      rw [pderiv_last_bellCore, map_one, one_mul, Fin.succ_last]
      rw [map_add, map_mul, rename_X, map_sum]
      have hsum : ∀ i : Fin k,
          rename Fin.castSucc
              (pderiv (Fin.castSucc i) (bellCore (k + 1)) * X i.succ)
            = rename Fin.castSucc (pderiv (Fin.castSucc i) (bellCore (k + 1)))
              * X (Fin.castSucc i).succ := by
        intro i
        rw [map_mul, rename_X, Fin.succ_castSucc]
      rw [Finset.sum_congr rfl fun i _ => hsum i]
      have hX0 : (Fin.castSucc (0 : Fin (k + 1))) = 0 := rfl
      rw [hX0]
      ring

/-! ## Pointwise surjectivity of the Bell value map -/

/-- The recursive back-substitution vector: `vec (k+1)` extends `vec k` by the value that
makes the `(k+1)`-st Bell polynomial hit its target. -/
private def bellSolveVec (n : ℕ) (t : Fin (n + 1) → ℂ) : (k : ℕ) → (Fin k → ℂ)
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (bellSolveVec n t k)
      ((if h : k < n + 1 then t ⟨k, h⟩ else 0)
        - eval (bellSolveVec n t k) (Classical.choose (bellCore_succ_decomp k)))

private theorem bellSolveVec_coherent (n : ℕ) (t : Fin (n + 1) → ℂ) :
    ∀ (m k : ℕ) (h : k ≤ m) (i : Fin k),
      bellSolveVec n t m (Fin.castLE h i) = bellSolveVec n t k i := by
  intro m
  induction m with
  | zero =>
      intro k h i
      interval_cases k
      exact i.elim0
  | succ m ih =>
      intro k h i
      rcases Nat.lt_or_ge k (m + 1) with hk | hk
      · have hkm : k ≤ m := by omega
        have hcast : Fin.castLE h i = Fin.castSucc (Fin.castLE hkm i) := by
          apply Fin.ext
          simp
        rw [show bellSolveVec n t (m + 1)
            = Fin.snoc (bellSolveVec n t m)
              ((if h' : m < n + 1 then t ⟨m, h'⟩ else 0)
                - eval (bellSolveVec n t m)
                    (Classical.choose (bellCore_succ_decomp m))) from rfl]
        rw [hcast, Fin.snoc_castSucc]
        exact ih k hkm i
      · have hkeq : k = m + 1 := by omega
        subst hkeq
        rfl

/-- **Pointwise surjectivity of the Bell value map**: every target vector is realized by
some digamma-jet value vector — the triangular structure solves recursively. -/
theorem exists_bellCore_solution (n : ℕ) (t : Fin (n + 1) → ℂ) :
    ∃ w : Fin (n + 1) → ℂ, ∀ k : Fin (n + 1),
      eval (fun i : Fin ((k : ℕ) + 1) => w (Fin.castLE (by omega) i))
          (bellCore ((k : ℕ) + 1)) = t k := by
  refine ⟨bellSolveVec n t (n + 1), fun k => ?_⟩
  have hk1 : (k : ℕ) + 1 ≤ n + 1 := k.isLt
  have hvec : (fun i : Fin ((k : ℕ) + 1) =>
      bellSolveVec n t (n + 1) (Fin.castLE (by omega) i))
      = bellSolveVec n t ((k : ℕ) + 1) := by
    funext i
    exact bellSolveVec_coherent n t (n + 1) ((k : ℕ) + 1) hk1 i
  rw [hvec]
  obtain hT := Classical.choose_spec (bellCore_succ_decomp (k : ℕ))
  rw [hT]
  rw [map_add, eval_X, eval_rename]
  have hlast : bellSolveVec n t ((k : ℕ) + 1) (Fin.last (k : ℕ))
      = (if h : (k : ℕ) < n + 1 then t ⟨(k : ℕ), h⟩ else 0)
        - eval (bellSolveVec n t (k : ℕ))
            (Classical.choose (bellCore_succ_decomp (k : ℕ))) := by
    rw [show bellSolveVec n t ((k : ℕ) + 1)
        = Fin.snoc (bellSolveVec n t (k : ℕ))
          ((if h : (k : ℕ) < n + 1 then t ⟨(k : ℕ), h⟩ else 0)
            - eval (bellSolveVec n t (k : ℕ))
                (Classical.choose (bellCore_succ_decomp (k : ℕ)))) from rfl]
    rw [Fin.snoc_last]
  have hcomp : (bellSolveVec n t ((k : ℕ) + 1)) ∘ Fin.castSucc
      = bellSolveVec n t (k : ℕ) := by
    funext i
    rw [show bellSolveVec n t ((k : ℕ) + 1)
        = Fin.snoc (bellSolveVec n t (k : ℕ))
          ((if h : (k : ℕ) < n + 1 then t ⟨(k : ℕ), h⟩ else 0)
            - eval (bellSolveVec n t (k : ℕ))
                (Classical.choose (bellCore_succ_decomp (k : ℕ)))) from rfl]
    exact Fin.snoc_castSucc _ _ _
  rw [hlast, hcomp, dif_pos k.isLt]
  have : (⟨(k : ℕ), k.isLt⟩ : Fin (n + 1)) = k := Fin.ext rfl
  rw [this]
  ring

/-! ## The Bell family in a common jet frame -/

/-- The Bell polynomials renamed into the jet frame `Fin (n+1)`. -/
def bellAt (n k : ℕ) (h : k ≤ n + 1) : MvPolynomial (Fin (n + 1)) ℂ :=
  rename (Fin.castLE h) (bellCore k)

theorem gamma_iteratedDeriv_eq_bellAt {n : ℕ} (k : ℕ) (h : k ≤ n + 1) {s : ℂ}
    (hs : ∀ p : ℕ, s ≠ -(p : ℂ)) :
    iteratedDeriv k Complex.Gamma s
      = Complex.Gamma s * eval (digammaJet (n + 1) s) (bellAt n k h) := by
  rw [bellAt, eval_rename]
  rw [gamma_iteratedDeriv_eq_bellCore k s hs]
  congr 1

theorem exists_bellAt_solution (n : ℕ) (t : Fin (n + 1) → ℂ) :
    ∃ w : Fin (n + 1) → ℂ, ∀ k : Fin (n + 1),
      eval w (bellAt n ((k : ℕ) + 1) k.isLt) = t k := by
  obtain ⟨w, hw⟩ := exists_bellCore_solution n t
  refine ⟨w, fun k => ?_⟩
  rw [bellAt, eval_rename]
  exact hw k

end GaloisForLFunctions

end
