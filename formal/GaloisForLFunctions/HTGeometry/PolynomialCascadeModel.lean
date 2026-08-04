import GaloisForLFunctions.HTGeometry.CascadeStateIndependence
import GaloisForLFunctions.HTGeometry.DifferentialOrder
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Cascades with a polynomial derivative law

A family of entire functions whose derivatives are *polynomials in the family itself* is modelled by a
derivation on `MvPolynomial ℕ ℂ`: evaluation at the family intertwines the model derivation with
complex differentiation, so every jet of every member is the evaluation of a polynomial jet.  If the
family is algebraically independent, a nonzero model polynomial evaluates to a function that is not
identically zero, and the analytic question "is there an algebraic differential equation of order `m`?"
becomes the polynomial question "are the model jets algebraically independent?".

The exponential cascades are the instances: `f' = a·f` gives the derivative law
`δ Y_{k+1} = a_k·Y_{k+1}·δ Y_k`, which is polynomial in the states.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Y : ℕ → ℂ → ℂ} {δ : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)}

/-- Evaluation of the model at the states. -/
noncomputable def evalAt (Y : ℕ → ℂ → ℂ) (z : ℂ) : MvPolynomial ℕ ℂ →+* ℂ :=
  MvPolynomial.eval (fun k => Y k z)

@[simp] theorem evalAt_X (Y : ℕ → ℂ → ℂ) (z : ℂ) (k : ℕ) :
    evalAt Y z (MvPolynomial.X k) = Y k z := by
  simp [evalAt]

theorem differentiable_evalAt (hY : ∀ k, Differentiable ℂ (Y k)) (P : MvPolynomial ℕ ℂ) :
    Differentiable ℂ (fun w => evalAt Y w P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun w => evalAt Y w (MvPolynomial.C a)) = fun _ : ℂ => a := by
        funext w; simp [evalAt]
      rw [hfun]
      exact differentiable_const a
  | add p q hp hq =>
      have hfun : (fun w => evalAt Y w (p + q))
          = fun w => evalAt Y w p + evalAt Y w q := by
        funext w; simp [map_add]
      rw [hfun]
      exact hp.add hq
  | mul_X p k hp =>
      have hfun : (fun w => evalAt Y w (p * MvPolynomial.X k))
          = fun w => evalAt Y w p * Y k w := by
        funext w; simp [map_mul]
      rw [hfun]
      exact hp.mul (hY k)

/-- **The model derivation is complex differentiation.**  It suffices that the law holds on the
variables. -/
theorem deriv_evalAt (hY : ∀ k, Differentiable ℂ (Y k))
    (hlaw : ∀ k z, deriv (Y k) z = evalAt Y z (δ (MvPolynomial.X k)))
    (P : MvPolynomial ℕ ℂ) (z : ℂ) :
    deriv (fun w => evalAt Y w P) z = evalAt Y z (δ P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have h1 : (fun w => evalAt Y w (MvPolynomial.C a)) = fun _ : ℂ => a := by
        funext w; simp [evalAt]
      have h2 : δ (MvPolynomial.C a) = 0 := by
        rw [show (MvPolynomial.C a : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) a from rfl]
        exact δ.map_algebraMap a
      rw [h1, h2]
      simp
  | add p q hp hq =>
      have hfun : (fun w => evalAt Y w (p + q))
          = fun w => evalAt Y w p + evalAt Y w q := by
        funext w; simp [map_add]
      have h1 : HasDerivAt (fun w => evalAt Y w p) (evalAt Y z (δ p)) z := by
        rw [← hp]
        exact ((differentiable_evalAt hY p) z).hasDerivAt
      have h2 : HasDerivAt (fun w => evalAt Y w q) (evalAt Y z (δ q)) z := by
        rw [← hq]
        exact ((differentiable_evalAt hY q) z).hasDerivAt
      rw [hfun, map_add, map_add]
      exact (h1.add h2).deriv
  | mul_X p k hp =>
      have hfun : (fun w => evalAt Y w (p * MvPolynomial.X k))
          = fun w => evalAt Y w p * Y k w := by
        funext w; simp [map_mul]
      have h1 : HasDerivAt (fun w => evalAt Y w p) (evalAt Y z (δ p)) z := by
        rw [← hp]
        exact ((differentiable_evalAt hY p) z).hasDerivAt
      have h2 : HasDerivAt (Y k) (evalAt Y z (δ (MvPolynomial.X k))) z := by
        rw [← hlaw k z]
        exact ((hY k) z).hasDerivAt
      have hderiv : deriv (fun w => evalAt Y w p * Y k w) z
          = evalAt Y z (δ p) * Y k z
            + evalAt Y z p * evalAt Y z (δ (MvPolynomial.X k)) := (h1.mul h2).deriv
      rw [hfun, hderiv, Derivation.leibniz]
      simp only [map_add, evalAt_X, smul_eq_mul, map_mul]
      ring

/-- The `i`-th model jet of the `N`-th variable. -/
noncomputable def modelJet (δ : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)) (N i : ℕ) :
    MvPolynomial ℕ ℂ :=
  ((δ : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N)

@[simp] theorem modelJet_zero (δ : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)) (N : ℕ) :
    modelJet δ N 0 = MvPolynomial.X N := rfl

theorem modelJet_succ (δ : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ)) (N i : ℕ) :
    modelJet δ N (i + 1) = δ (modelJet δ N i) := by
  rw [modelJet, modelJet, Function.iterate_succ_apply']

/-- **The analytic jets are the model jets.** -/
theorem evalAt_modelJet (hY : ∀ k, Differentiable ℂ (Y k))
    (hlaw : ∀ k z, deriv (Y k) z = evalAt Y z (δ (MvPolynomial.X k))) (N i : ℕ) (z : ℂ) :
    evalAt Y z (modelJet δ N i) = iteratedDeriv i (Y N) z := by
  induction i generalizing z with
  | zero => simp [iteratedDeriv_zero]
  | succ i ih =>
      have hfun : iteratedDeriv i (Y N) = fun w => evalAt Y w (modelJet δ N i) := by
        funext w; rw [ih w]
      rw [iteratedDeriv_succ, hfun, deriv_evalAt hY hlaw, modelJet_succ]

/-- **No low-order equation from independent model jets.** -/
theorem not_differentiallyAlgebraicOfOrder_of_model {N m : ℕ}
    (hY : ∀ k, Differentiable ℂ (Y k))
    (hlaw : ∀ k z, deriv (Y k) z = evalAt Y z (δ (MvPolynomial.X k)))
    (hind : ∀ Q : MvPolynomial ℕ ℂ, Q ≠ 0 → ∃ z : ℂ, evalAt Y z Q ≠ 0)
    (hjet : AlgebraicIndependent ℂ
      (Fin.cons (MvPolynomial.X (0 : ℕ)) (fun j : Fin (m + 1) => modelJet δ N (j : ℕ)) :
        Fin (m + 2) → MvPolynomial ℕ ℂ))
    (hzero : Y 0 = id) :
    ¬ DifferentiallyAlgebraicOfOrder (Y N) m := by
  rintro ⟨P, hP0, hPz⟩
  set v : Fin (m + 2) → MvPolynomial ℕ ℂ :=
    Fin.cons (MvPolynomial.X (0 : ℕ)) (fun j : Fin (m + 1) => modelJet δ N (j : ℕ)) with hv
  have hQ0 : MvPolynomial.aeval v P ≠ 0 := by
    intro h0
    exact hP0 (hjet (by rw [h0, map_zero]))
  obtain ⟨z, hz⟩ := hind _ hQ0
  refine hz ?_
  have hcomp : (evalAt Y z).comp
        (MvPolynomial.aeval v : MvPolynomial (Fin (m + 2)) ℂ →ₐ[ℂ] MvPolynomial ℕ ℂ).toRingHom
      = (MvPolynomial.eval (fun i => evalAt Y z (v i)) :
          MvPolynomial (Fin (m + 2)) ℂ →+* ℂ) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [evalAt]
    · intro i; simp [evalAt]
  have hval : evalAt Y z (MvPolynomial.aeval v P)
      = MvPolynomial.eval (fun i => evalAt Y z (v i)) P := by
    have := RingHom.congr_fun hcomp P
    simpa using this
  rw [hval]
  have hvec : (fun i : Fin (m + 2) => evalAt Y z (v i))
      = Fin.cons z (fun j : Fin (m + 1) => iteratedDeriv (j : ℕ) (Y N) z) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [hv, hzero]
    · intro j
      simp [hv, evalAt_modelJet hY hlaw]
  rw [hvec]
  exact hPz z


/-! ## The independence input, for any transcendental cascade -/

/-- **A nonzero model polynomial does not vanish identically at the states of a transcendental
cascade.** -/
theorem exists_evalAt_ne_zero_of_transcendental {f : ℕ → ℂ → ℂ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) {Q : MvPolynomial ℕ ℂ} (hQ : Q ≠ 0) :
    ∃ z : ℂ, evalAt (fun k => entireCascade f k) z Q ≠ 0 := by
  classical
  by_contra hcon
  have hall0 : ∀ z : ℂ, evalAt (fun k => entireCascade f k) z Q = 0 := by
    intro z
    by_contra hz
    exact hcon ⟨z, hz⟩
  obtain ⟨n, g, hg, q, rfl⟩ := MvPolynomial.exists_fin_rename Q
  set M : ℕ := (Finset.univ.sup fun j : Fin n => g j) + 1 with hM
  have hlt : ∀ j : Fin n, g j < M := by
    intro j
    have : g j ≤ Finset.univ.sup fun j : Fin n => g j := Finset.le_sup (Finset.mem_univ j)
    omega
  set h : Fin n → Fin M := fun j => ⟨g j, hlt j⟩ with hh
  have hhinj : Function.Injective h := by
    intro x y hxy
    have : g x = g y := by
      have := congrArg Fin.val hxy
      simpa [hh] using this
    exact hg this
  have hq0 : q ≠ 0 := by
    intro h0
    exact hQ (by rw [h0, map_zero])
  have hrq : MvPolynomial.rename h q ≠ 0 := by
    intro h0
    exact hq0 (MvPolynomial.rename_injective _ hhinj (by rw [h0, map_zero]))
  refine noRelation_entireCascade_of_transcendental M f hall _ hrq ?_
  intro z
  rw [MvPolynomial.eval_rename]
  have hcomp : ((fun j : Fin M => entireCascade f ((j : ℕ)) z) ∘ h)
      = fun j : Fin n => entireCascade f (g j) z := by
    funext j
    simp [hh]
  rw [hcomp]
  have hval := hall0 z
  have hrw : evalAt (fun k => entireCascade f k) z (MvPolynomial.rename g q)
      = MvPolynomial.eval (fun j : Fin n => entireCascade f (g j) z) q := by
    show MvPolynomial.eval (fun k => entireCascade f k z) (MvPolynomial.rename g q) = _
    rw [MvPolynomial.eval_rename]
    rfl
  rw [hrw] at hval
  exact hval

end GaloisForLFunctions.HTGeometry
