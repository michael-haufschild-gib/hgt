import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import GaloisForLFunctions.Hypertranscendence

/-!
# Affine invariance of differential algebraicity

Differential algebraicity — and hence hypertranscendence — is invariant under affine
reparametrization of the domain.  Translating the variable (`z ↦ z + a`) or rescaling it
(`z ↦ c·z`, `c ≠ 0`) transports an annihilating differential polynomial through an explicit
polynomial substitution on the jet variables: the point slot moves by the affine map, and the
`j`-th jet slot picks up the chain-rule factor `c^j`.  The substitution is invertible (compose
with the inverse affine map), so nonzeroness of the annihilator is preserved.

* `DifferentiallyAlgebraic.comp_add_const`, `differentiallyAlgebraic_comp_add_const_iff`,
  `hypertranscendental_comp_add_const_iff` — translation invariance, unconditional.
* `DifferentiallyAlgebraic.comp_const_mul`, `differentiallyAlgebraic_comp_const_mul_iff`,
  `hypertranscendental_comp_const_mul_iff` — scaling invariance, for smooth functions (the
  chain-rule identity for iterated derivatives of `f(c·)` requires smoothness).

This is the "normalize the configuration" step used silently throughout the
hypertranscendence corpus: a distinguished point can be moved to the origin and a period can
be rescaled to `1` without changing the class of the function.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- `eval` composed with the substitution monad `bind₁`. -/
theorem eval_bind₁ {n : ℕ} (v : Fin n → ℂ) (σ : Fin n → MvPolynomial (Fin n) ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    eval v (bind₁ σ P) = eval (fun i => eval v (σ i)) P :=
  eval₂Hom_bind₁ (RingHom.id ℂ) v σ P

/-- Jet substitution of a translation: the point slot moves by `a`, the jet slots are fixed. -/
noncomputable def jetShiftSub (n : ℕ) (a : ℂ) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (X 0 + C a) (fun j => X j.succ)

/-- Translation invariance of differential algebraicity. -/
theorem DifferentiallyAlgebraic.comp_add_const {f : ℂ → ℂ}
    (hf : DifferentiallyAlgebraic f) (a : ℂ) :
    DifferentiallyAlgebraic (fun z => f (z + a)) := by
  obtain ⟨n, P, hP0, hPz⟩ := hf
  refine ⟨n, bind₁ (jetShiftSub n a) P, ?_, ?_⟩
  · intro h
    apply hP0
    have hback : bind₁ (jetShiftSub n (-a)) (bind₁ (jetShiftSub n a) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetShiftSub n (-a)) (jetShiftSub n a i))
          = (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          simp only [jetShiftSub, Fin.cases_zero, map_add, bind₁_X_right, bind₁_C_right]
          rw [map_neg]
          ring
        | succ j => simp only [jetShiftSub, Fin.cases_succ, bind₁_X_right]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, h, map_zero]
  · intro z
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (fun w => f (w + a)) z)
          (jetShiftSub n a i))
        = Fin.cons (z + a) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (z + a)) := by
      funext i
      induction i using Fin.cases with
      | zero => simp [jetShiftSub]
      | succ j =>
        simp only [jetShiftSub, Fin.cases_succ, eval_X, Fin.cons_succ]
        exact congrFun (iteratedDeriv_comp_add_const (j : ℕ) f a) z
    rw [hvec]
    exact hPz (z + a)

theorem differentiallyAlgebraic_comp_add_const_iff {f : ℂ → ℂ} (a : ℂ) :
    DifferentiallyAlgebraic (fun z => f (z + a)) ↔ DifferentiallyAlgebraic f := by
  constructor
  · intro h
    have h2 := h.comp_add_const (-a)
    have hfun : (fun z => (fun w => f (w + a)) (z + -a)) = f := by
      funext z
      show f (z + -a + a) = f z
      rw [show z + -a + a = z by ring]
    rwa [hfun] at h2
  · exact fun h => h.comp_add_const a

/-- Hypertranscendence is translation invariant. -/
theorem hypertranscendental_comp_add_const_iff {f : ℂ → ℂ} (a : ℂ) :
    Hypertranscendental (fun z => f (z + a)) ↔ Hypertranscendental f :=
  (differentiallyAlgebraic_comp_add_const_iff a).not

/-- Jet substitution of a rescaling: the point slot is multiplied by `c`, and the `j`-th jet
slot absorbs the chain-rule factor via `c⁻¹^j`. -/
noncomputable def jetScaleSub (n : ℕ) (c : ℂ) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (C c * X 0) (fun j => C (c⁻¹ ^ (j : ℕ)) * X j.succ)

/-- Scaling invariance of differential algebraicity for smooth functions. -/
theorem DifferentiallyAlgebraic.comp_const_mul {f : ℂ → ℂ}
    (hf : DifferentiallyAlgebraic f) (hsm : ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraic (fun z => f (c * z)) := by
  obtain ⟨n, P, hP0, hPz⟩ := hf
  refine ⟨n, bind₁ (jetScaleSub n c) P, ?_, ?_⟩
  · intro h
    apply hP0
    have hback : bind₁ (jetScaleSub n c⁻¹) (bind₁ (jetScaleSub n c) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetScaleSub n c⁻¹) (jetScaleSub n c i))
          = (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          simp only [jetScaleSub, Fin.cases_zero, map_mul, bind₁_X_right, bind₁_C_right]
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
        | succ j =>
          simp only [jetScaleSub, Fin.cases_succ, map_mul, bind₁_X_right, bind₁_C_right]
          rw [inv_inv, ← mul_assoc, ← map_mul, ← mul_pow, inv_mul_cancel₀ hc, one_pow,
            map_one, one_mul]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, h, map_zero]
  · intro z
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (fun w => f (c * w)) z)
          (jetScaleSub n c i))
        = Fin.cons (c * z) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (c * z)) := by
      funext i
      induction i using Fin.cases with
      | zero => simp [jetScaleSub]
      | succ j =>
        simp only [jetScaleSub, Fin.cases_succ, eval_mul, eval_C, eval_X, Fin.cons_succ]
        have hj : ContDiff ℂ ((j : ℕ) : WithTop ℕ∞) f :=
          hsm.of_le (by exact_mod_cast (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤))
        rw [congrFun (iteratedDeriv_comp_const_mul hj c) z, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hc, one_pow, one_mul]
    rw [hvec]
    exact hPz (c * z)

theorem differentiallyAlgebraic_comp_const_mul_iff {f : ℂ → ℂ}
    (hsm : ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraic (fun z => f (c * z)) ↔ DifferentiallyAlgebraic f := by
  constructor
  · intro h
    have hgsm : ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f (c * z)) :=
      hsm.comp (contDiff_const.mul contDiff_id)
    have h2 := h.comp_const_mul hgsm (inv_ne_zero hc)
    have hfun : (fun z => (fun w => f (c * w)) (c⁻¹ * z)) = f := by
      funext z
      show f (c * (c⁻¹ * z)) = f z
      rw [show c * (c⁻¹ * z) = z by field_simp]
    rwa [hfun] at h2
  · exact fun h => h.comp_const_mul hsm hc

/-- Hypertranscendence is scaling invariant for smooth functions. -/
theorem hypertranscendental_comp_const_mul_iff {f : ℂ → ℂ}
    (hsm : ContDiff ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {c : ℂ} (hc : c ≠ 0) :
    Hypertranscendental (fun z => f (c * z)) ↔ Hypertranscendental f :=
  (differentiallyAlgebraic_comp_const_mul_iff hsm hc).not

end GaloisForLFunctions
