import GaloisForLFunctions.HTGeometry.ExponentialTowerModel
import GaloisForLFunctions.HTGeometry.DifferentialOrder

/-!
# The tower's jets are the model's jets

Evaluating the model at the analytic states intertwines the model derivation with complex
differentiation, so every jet of the tower is the evaluation of a polynomial jet.  Since the states
are algebraically independent, a nonzero model polynomial evaluates to a function that is not
identically zero.

Together these turn the analytic question — does the tower satisfy an algebraic differential equation
of low order? — into a question about polynomials: are the model jets algebraically independent?
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- Evaluation of the model at the tower states. -/
noncomputable def evalStates (z : ℂ) : MvPolynomial ℕ ℂ →+* ℂ :=
  MvPolynomial.eval (fun k => expTower k z)

@[simp] theorem evalStates_X (z : ℂ) (k : ℕ) : evalStates z (MvPolynomial.X k) = expTower k z := by
  simp [evalStates]

theorem differentiable_evalStates (P : MvPolynomial ℕ ℂ) :
    Differentiable ℂ (fun w => evalStates w P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun w => evalStates w (MvPolynomial.C a)) = fun _ : ℂ => a := by
        funext w; simp [evalStates]
      rw [hfun]
      exact differentiable_const a
  | add p q hp hq =>
      have hfun : (fun w => evalStates w (p + q))
          = fun w => evalStates w p + evalStates w q := by
        funext w; simp [map_add]
      rw [hfun]
      exact hp.add hq
  | mul_X p k hp =>
      have hfun : (fun w => evalStates w (p * MvPolynomial.X k))
          = fun w => evalStates w p * expTower k w := by
        funext w; simp [map_mul]
      rw [hfun]
      exact hp.mul (differentiable_expTower k)

/-- **The model derivation is complex differentiation.** -/
theorem deriv_evalStates (P : MvPolynomial ℕ ℂ) (z : ℂ) :
    deriv (fun w => evalStates w P) z = evalStates z (towerDerivation P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have h1 : (fun w => evalStates w (MvPolynomial.C a)) = fun _ : ℂ => a := by
        funext w; simp [evalStates]
      have h2 : towerDerivation (MvPolynomial.C a) = 0 := by
        rw [show (MvPolynomial.C a : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) a from rfl]
        exact towerDerivation.map_algebraMap a
      rw [h1, h2]
      simp
  | add p q hp hq =>
      have hfun : (fun w => evalStates w (p + q))
          = fun w => evalStates w p + evalStates w q := by
        funext w; simp [map_add]
      have h1 : HasDerivAt (fun w => evalStates w p) (evalStates z (towerDerivation p)) z := by
        rw [← hp]
        exact ((differentiable_evalStates p) z).hasDerivAt
      have h2 : HasDerivAt (fun w => evalStates w q) (evalStates z (towerDerivation q)) z := by
        rw [← hq]
        exact ((differentiable_evalStates q) z).hasDerivAt
      rw [hfun, map_add, map_add]
      exact (h1.add h2).deriv
  | mul_X p k hp =>
      have hfun : (fun w => evalStates w (p * MvPolynomial.X k))
          = fun w => evalStates w p * expTower k w := by
        funext w; simp [map_mul]
      have h1 : HasDerivAt (fun w => evalStates w p) (evalStates z (towerDerivation p)) z := by
        rw [← hp]
        exact ((differentiable_evalStates p) z).hasDerivAt
      have h2 : HasDerivAt (expTower k) (∏ i ∈ Finset.Icc 1 k, expTower i z) z := by
        rw [← deriv_expTower k z]
        exact ((differentiable_expTower k) z).hasDerivAt
      have hmon : evalStates z (towerMonomial k) = ∏ i ∈ Finset.Icc 1 k, expTower i z := by
        simp [evalStates, towerMonomial, map_prod]
      have hderiv : deriv (fun w => evalStates w p * expTower k w) z
          = evalStates z (towerDerivation p) * expTower k z
            + evalStates z p * ∏ i ∈ Finset.Icc 1 k, expTower i z := (h1.mul h2).deriv
      rw [hfun, hderiv, Derivation.leibniz, towerDerivation_X]
      simp only [map_add, evalStates_X, smul_eq_mul, map_mul]
      rw [hmon]
      ring

/-- The `i`-th jet of the model's `N`-th variable. -/
noncomputable def towerJet (N i : ℕ) : MvPolynomial ℕ ℂ :=
  (towerDerivation : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i] (MvPolynomial.X N)

@[simp] theorem towerJet_zero (N : ℕ) : towerJet N 0 = MvPolynomial.X N := rfl

theorem towerJet_succ (N i : ℕ) : towerJet N (i + 1) = towerDerivation (towerJet N i) := by
  rw [towerJet, towerJet, Function.iterate_succ_apply']

/-- **The analytic jets are the model jets.** -/
theorem evalStates_towerJet (N i : ℕ) (z : ℂ) :
    evalStates z (towerJet N i) = iteratedDeriv i (expTower N) z := by
  induction i generalizing z with
  | zero => simp [iteratedDeriv_zero]
  | succ i ih =>
      have hfun : iteratedDeriv i (expTower N) = fun w => evalStates w (towerJet N i) := by
        funext w; rw [ih w]
      rw [iteratedDeriv_succ, hfun, deriv_evalStates, towerJet_succ]

/-! ## Nonzero model polynomials give nonzero functions -/

/-- **A nonzero model polynomial does not vanish identically at the states.** -/
theorem exists_evalStates_ne_zero {Q : MvPolynomial ℕ ℂ} (hQ : Q ≠ 0) :
    ∃ z : ℂ, evalStates z Q ≠ 0 := by
  classical
  by_contra hcon
  have hall : ∀ z : ℂ, evalStates z Q = 0 := by
    intro z
    by_contra hz
    exact hcon ⟨z, hz⟩
  obtain ⟨n, f, hf, q, rfl⟩ := MvPolynomial.exists_fin_rename Q
  -- move the finitely many variables into an initial segment
  set M : ℕ := (Finset.univ.sup fun j : Fin n => f j) + 1 with hM
  have hlt : ∀ j : Fin n, f j < M := by
    intro j
    have : f j ≤ Finset.univ.sup fun j : Fin n => f j := Finset.le_sup (Finset.mem_univ j)
    omega
  set g : Fin n → Fin M := fun j => ⟨f j, hlt j⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have : f a = f b := by
      have := congrArg Fin.val hab
      simpa [hg] using this
    exact hf this
  have hq0 : q ≠ 0 := by
    intro h0
    exact hQ (by rw [h0, map_zero])
  have hrq : MvPolynomial.rename g q ≠ 0 := by
    intro h0
    exact hq0 (MvPolynomial.rename_injective _ hginj (by rw [h0, map_zero]))
  refine noRelation_entireCascade_of_transcendental M (fun _ => Complex.exp)
    (fun _ => transcendentalEntire_exp) _ hrq ?_
  intro z
  have hstate : ∀ j : Fin M,
      entireCascade (fun _ => Complex.exp) ((j : ℕ)) z = expTower (j : ℕ) z := fun _ => rfl
  rw [MvPolynomial.eval_rename]
  have hcomp : ((fun j : Fin M => entireCascade (fun _ => Complex.exp) ((j : ℕ)) z) ∘ g)
      = fun j : Fin n => expTower (f j) z := by
    funext j
    simp [hg, hstate]
  rw [hcomp]
  have hval := hall z
  have hrw : evalStates z (MvPolynomial.rename f q)
      = MvPolynomial.eval (fun j : Fin n => expTower (f j) z) q := by
    simp [evalStates, MvPolynomial.eval_rename]
    rfl
  rw [hrw] at hval
  exact hval

/-! ## The order bound from the model -/

/-- **No low-order equation from independent model jets.**  If the coordinate together with the first
`m+1` model jets of the `N`-th variable are algebraically independent, the tower satisfies no
algebraic differential equation of order `m`. -/
theorem not_differentiallyAlgebraicOfOrder_expTower {N m : ℕ}
    (hind : AlgebraicIndependent ℂ
      (Fin.cons (MvPolynomial.X (0 : ℕ)) (fun j : Fin (m + 1) => towerJet N (j : ℕ)) :
        Fin (m + 2) → MvPolynomial ℕ ℂ)) :
    ¬ DifferentiallyAlgebraicOfOrder (expTower N) m := by
  rintro ⟨P, hP0, hPz⟩
  set v : Fin (m + 2) → MvPolynomial ℕ ℂ :=
    Fin.cons (MvPolynomial.X (0 : ℕ)) (fun j : Fin (m + 1) => towerJet N (j : ℕ)) with hv
  have hQ0 : MvPolynomial.aeval v P ≠ 0 := by
    intro h0
    exact hP0 (hind (by rw [h0, map_zero]))
  obtain ⟨z, hz⟩ := exists_evalStates_ne_zero hQ0
  refine hz ?_
  have hcomp : (evalStates z).comp
        (MvPolynomial.aeval v : MvPolynomial (Fin (m + 2)) ℂ →ₐ[ℂ] MvPolynomial ℕ ℂ).toRingHom
      = (MvPolynomial.eval (fun i => evalStates z (v i)) :
          MvPolynomial (Fin (m + 2)) ℂ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [evalStates]
    · intro i; simp [evalStates]
  have hval : evalStates z (MvPolynomial.aeval v P)
      = MvPolynomial.eval (fun i => evalStates z (v i)) P := by
    have := RingHom.congr_fun hcomp P
    simpa using this
  rw [hval]
  have hvec : (fun i : Fin (m + 2) => evalStates z (v i))
      = Fin.cons z (fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) (expTower N) z) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [hv]
    · intro j
      simp [hv, evalStates_towerJet]
  rw [hvec]
  exact hPz z

end GaloisForLFunctions.HTGeometry
