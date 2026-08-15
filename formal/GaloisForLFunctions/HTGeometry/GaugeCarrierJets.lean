import GaloisForLFunctions.HTGeometry.ExpJetJacobian
import GaloisForLFunctions.HTGeometry.EntireGaugeSpace
import GaloisForLFunctions.HTGeometry.HighDegreeJetFreedom

/-!
# Jets of a gauged source

For a fixed entire source `W` and an entire exponent `g`, the jets of `W·exp(g)` at a point are an
explicit function of the jets of `W` and of `g` there: the Leibniz matrix of the jets of `W` applied
to the truncated exponential jet map of the jets of `g`.

Both factors are invertible where `W` does not vanish, so perturbing `g` inside a polynomial degree
window moves the jet packet onto every prescribed target.  This is the analytic content of a
parametric jet argument for a gauge with a prescribed divisor.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Jets of sums, and of polynomials -/

theorem iteratedDeriv_add_entire {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => f w + g w) z = iteratedDeriv k f z + iteratedDeriv k g z := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
      have hstep : iteratedDeriv k (fun w => f w + g w)
          = fun w => iteratedDeriv k f w + iteratedDeriv k g w := funext ih
      rw [iteratedDeriv_succ, hstep, iteratedDeriv_succ, iteratedDeriv_succ]
      exact deriv_add (differentiable_iteratedDeriv_of_entire hf k z)
        (differentiable_iteratedDeriv_of_entire hg k z)

theorem iteratedDeriv_polynomial_eval_fun (k : ℕ) (P : Polynomial ℂ) :
    iteratedDeriv k (fun w => Polynomial.eval w P)
      = fun z => (Polynomial.derivative^[k] P).eval z := by
  induction k generalizing P with
  | zero => funext z; simp
  | succ k ih =>
      funext z
      rw [iteratedDeriv_succ, ih P, Function.iterate_succ_apply']
      exact Polynomial.deriv _

theorem iteratedDeriv_polynomial_eval (P : Polynomial ℂ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w => Polynomial.eval w P) z = (Polynomial.derivative^[k] P).eval z :=
  congrFun (iteratedDeriv_polynomial_eval_fun k P) z

/-! ### Evaluation only sees the jet levels present -/

/-- Evaluation on the jet subalgebra only depends on the jet slots it uses. -/
theorem eval_eq_of_mem_jetSub {l : ℕ} {B : MvPolynomial ℕ ℂ} (hB : B ∈ jetSub l)
    (u w : ℕ → ℂ) (h : ∀ k, 1 ≤ k → k ≤ l → u k = w k) :
    MvPolynomial.eval u B = MvPolynomial.eval w B := by
  induction hB using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, ⟨h1, h2⟩, rfl⟩ := hx
      rw [MvPolynomial.eval_X, MvPolynomial.eval_X]
      exact h i h1 h2
  | algebraMap r =>
      have hC : (algebraMap ℂ (MvPolynomial ℕ ℂ) r) = MvPolynomial.C r := rfl
      rw [hC, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

/-! ### The truncated jet vector of an entire function -/

/-- The jets of a function at a point, truncated at order `m`. -/
def gaugeJetVec (m : ℕ) (g : ℂ → ℂ) (z : ℂ) : Fin m → ℂ := fun k => iteratedDeriv (k : ℕ) g z

theorem jetExtend_gaugeJetVec {m : ℕ} (g : ℂ → ℂ) (z : ℂ) {k : ℕ} (hk : k < m) :
    jetExtend m (gaugeJetVec m g z) k = iteratedDeriv k g z := by
  rw [jetExtend_apply_lt _ hk]
  rfl

theorem gaugeJetVec_add {m : ℕ} {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (z : ℂ) : gaugeJetVec m (fun w => f w + g w) z = gaugeJetVec m f z + gaugeJetVec m g z := by
  funext k
  exact iteratedDeriv_add_entire hf hg (k : ℕ) z

/-- **The truncated exponential jet map computes the jets of an exponential.** -/
theorem expJetMap_gaugeJetVec {m : ℕ} {g : ℂ → ℂ} (hg : Differentiable ℂ g) (z : ℂ) (l : Fin m) :
    expJetMap m (gaugeJetVec m g z) (l : Fin m)
      = iteratedDeriv (l : ℕ) (fun w => Complex.exp (g w)) z := by
  rw [iteratedDeriv_exp_comp hg (l : ℕ) z, expJetMap]
  have h0 : jetExtend m (gaugeJetVec m g z) 0 = g z := by
    rw [jetExtend_gaugeJetVec g z (lt_of_le_of_lt (Nat.zero_le (l : ℕ)) l.2),
      iteratedDeriv_zero]
  rw [h0]
  congr 1
  refine eval_eq_of_mem_jetSub (expJetPoly_mem_jetSub (l : ℕ)) _ _ ?_
  intro k _ hk2
  exact jetExtend_gaugeJetVec g z (lt_of_le_of_lt hk2 l.2)

/-! ### The jets of a gauged source -/

theorem contDiffAt_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (m : ℕ) (z : ℂ) :
    ContDiffAt ℂ (m : ℕ) f z :=
  ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)).contDiffAt.of_le
    (by exact_mod_cast le_top)

/-- **The jets of `W·exp(g)` are the Leibniz matrix of the jets of `W` applied to the exponential
jet map of the jets of `g`.** -/
theorem iteratedDeriv_gaugeCarrier {m : ℕ} {W g : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hg : Differentiable ℂ g) (z : ℂ) (j : Fin m) :
    iteratedDeriv (j : ℕ) (fun w => W w * Complex.exp (g w)) z
      = ∑ l : Fin m, leibnizJetMatrix m (fun r => iteratedDeriv r W z) j l
          * expJetMap m (gaugeJetVec m g z) l := by
  have hexp : Differentiable ℂ fun w => Complex.exp (g w) := hg.cexp
  rw [iteratedDeriv_mul_eq_leibnizJetMatrix m (contDiffAt_of_entire hW m z)
    (contDiffAt_of_entire hexp m z) j]
  exact Finset.sum_congr rfl fun l _ => by rw [expJetMap_gaugeJetVec hg z l]

/-! ### Block maps on a product of jet spaces -/

/-- A map acting independently on each block of a finite product of jet spaces. -/
def blockJetMap {X : Type*} (m : ℕ) (E : X → (Fin m → ℂ) → (Fin m → ℂ))
    (v : X → Fin m → ℂ) : X → Fin m → ℂ := fun x => E x (v x)

/-- The block derivative of a block map. -/
def blockJetCLM {X : Type*} [Fintype X] (m : ℕ)
    (L : X → ((Fin m → ℂ) →L[ℝ] (Fin m → ℂ))) :
    ((X → Fin m → ℂ) →L[ℝ] (X → Fin m → ℂ)) :=
  ContinuousLinearMap.pi fun x => (L x).comp (ContinuousLinearMap.proj x)

theorem hasFDerivAt_blockJetMap {X : Type*} [Fintype X] (m : ℕ)
    (E : X → (Fin m → ℂ) → (Fin m → ℂ)) (L : X → ((Fin m → ℂ) →L[ℝ] (Fin m → ℂ)))
    (v : X → Fin m → ℂ) (hE : ∀ x, HasFDerivAt (E x) (L x) (v x)) :
    HasFDerivAt (blockJetMap m E) (blockJetCLM m L) v := by
  refine hasFDerivAt_pi.mpr fun x => ?_
  exact (hE x).comp v ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X => Fin m → ℂ)
    x).hasFDerivAt)

theorem surjective_blockJetCLM {X : Type*} [Fintype X] (m : ℕ)
    (L : X → ((Fin m → ℂ) →L[ℝ] (Fin m → ℂ))) (hL : ∀ x, Function.Surjective (L x)) :
    Function.Surjective (blockJetCLM m L) := by
  intro y
  choose w hw using fun x => hL x (y x)
  exact ⟨w, funext fun x => hw x⟩

end

end GaloisForLFunctions.HTGeometry
