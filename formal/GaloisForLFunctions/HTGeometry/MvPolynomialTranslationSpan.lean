import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.CharZero.Infinite

/-!
# Translation invariance of a multivariate polynomial is a linear condition

The directions along which a multivariate polynomial over a characteristic-zero field is
translation invariant form a linear subspace, not merely a subgroup.  The upgrade is the
one-variable rigidity applied along the affine line `x + t·v`: the restriction of `P` to that line
is a one-variable polynomial taking the same value at every nonnegative integer, hence constant,
hence `P` is invariant under `c·v` for every scalar `c`.

Consequently a polynomial invariant in enough directions to span the value space is constant.  A
single nonzero translation per coordinate suffices — no density and no infinitude of translations
is needed, because in characteristic zero a nonconstant polynomial is never periodic.

* `mvShift`, `eval_mvShift`, `mvShift_add`, `mvShift_zero`;
* `translationAddSubgroup`, `linePoly`, `eval_linePoly`;
* `mvShift_smul_of_mvShift`, `translationSubmodule`;
* `eq_C_of_translationSubmodule_eq_top`, `eq_C_of_span_translations_eq_top`;
* `eq_C_of_coordinate_shift_invariant`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace MvTranslation

noncomputable section

open MvPolynomial

variable {ι K : Type*} [Field K] [CharZero K]

/-- Translation of every variable of a multivariate polynomial by a vector. -/
def mvShift (v : ι → K) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  bind₁ fun i => X i + C (v i)

omit [CharZero K] in
@[simp] theorem mvShift_X (v : ι → K) (i : ι) : mvShift v (X i) = X i + C (v i) := by
  simp [mvShift]

omit [CharZero K] in
@[simp] theorem mvShift_C (v : ι → K) (c : K) : mvShift v (C c : MvPolynomial ι K) = C c := by
  simp [mvShift]

omit [CharZero K] in
/-- Shifting the polynomial shifts the evaluation point. -/
theorem eval_mvShift (v x : ι → K) (P : MvPolynomial ι K) :
    eval x (mvShift v P) = eval (fun i => x i + v i) P := by
  rw [mvShift]
  change (eval₂Hom (RingHom.id K) x) ((bind₁ fun i => X i + C (v i)) P) = _
  rw [eval₂Hom_bind₁]
  simp

omit [CharZero K] in
theorem mvShift_add (v w : ι → K) (P : MvPolynomial ι K) :
    mvShift v (mvShift w P) = mvShift (fun i => v i + w i) P := by
  change ((mvShift v).comp (mvShift w)) P = _
  congr 1
  ext i
  simp [mvShift]
  abel

omit [CharZero K] in
@[simp] theorem mvShift_zero (P : MvPolynomial ι K) : mvShift (fun _ : ι => (0 : K)) P = P := by
  rw [mvShift]
  simp

/-- The translation directions fixing a polynomial, as an additive subgroup. -/
def translationAddSubgroup (P : MvPolynomial ι K) : AddSubgroup (ι → K) where
  carrier := {v | mvShift v P = P}
  zero_mem' := mvShift_zero P
  add_mem' {v w} hv hw := by
    change mvShift (fun i => v i + w i) P = P
    rw [← mvShift_add]
    rw [(hw : mvShift w P = P)]
    exact hv
  neg_mem' {v} hv := by
    have h := congrArg (mvShift fun i => -v i) (hv : mvShift v P = P)
    rw [mvShift_add] at h
    have hz : (fun i => -v i + v i) = fun _ : ι => (0 : K) := by
      funext i
      ring
    rw [hz, mvShift_zero] at h
    show mvShift (-v) P = P
    exact h.symm

/-- The restriction of a multivariate polynomial to the affine line `x + t·v`. -/
def linePoly (x v : ι → K) (P : MvPolynomial ι K) : Polynomial K :=
  eval₂Hom Polynomial.C (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) P

omit [CharZero K] in
theorem eval_linePoly (x v : ι → K) (P : MvPolynomial ι K) (t : K) :
    (linePoly x v P).eval t = eval (fun i => x i + t * v i) P := by
  rw [linePoly]
  have h := map_eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))
    (Polynomial.evalRingHom t) P
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id K := by
    ext z
    simp
  have hg : (fun i => (Polynomial.evalRingHom t)
      (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))) = fun i => x i + t * v i := by
    funext i
    simp
    ring
  rw [hC, hg] at h
  change Polynomial.eval t (linePoly x v P) = eval₂ (RingHom.id K) (fun i => x i + t * v i) P at h
  rw [eval₂_id] at h
  exact h

/-- **Additive translation invariance upgrades to scalar invariance.**  The line restriction takes
the same value at every nonnegative integer, so it is a constant polynomial. -/
theorem mvShift_smul_of_mvShift (P : MvPolynomial ι K) {v : ι → K}
    (hv : mvShift v P = P) (c : K) : mvShift (fun i => c * v i) P = P := by
  apply MvPolynomial.funext
  intro x
  set R : Polynomial K := linePoly x v P - Polynomial.C (eval x P) with hR
  have hRzero : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective fun n : ℕ => (n : K) := Nat.cast_injective
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro t ⟨n, rfl⟩
    show Polynomial.eval ((n : K)) R = 0
    rw [hR, Polynomial.eval_sub, eval_linePoly, Polynomial.eval_C, sub_eq_zero]
    have hnmem : n • v ∈ translationAddSubgroup P :=
      (translationAddSubgroup P).nsmul_mem hv n
    have hnfun : n • v = fun i => (n : K) * v i := by
      funext i
      simp [nsmul_eq_mul]
    have hn : mvShift (fun i => (n : K) * v i) P = P := by
      rw [← hnfun]
      exact hnmem
    have he := congrArg (eval x) hn
    rw [eval_mvShift] at he
    exact he
  have hc := congrArg (Polynomial.eval c) hRzero
  rw [hR, Polynomial.eval_sub, eval_linePoly, Polynomial.eval_C, Polynomial.eval_zero,
    sub_eq_zero] at hc
  rw [eval_mvShift]
  exact hc

/-- The translation directions fixing a polynomial form a linear subspace. -/
def translationSubmodule (P : MvPolynomial ι K) : Submodule K (ι → K) where
  __ := translationAddSubgroup P
  smul_mem' c v hv := by
    change mvShift (fun i => c * v i) P = P
    exact mvShift_smul_of_mvShift P hv c

@[simp] theorem mem_translationSubmodule {P : MvPolynomial ι K} {v : ι → K} :
    v ∈ translationSubmodule P ↔ mvShift v P = P := Iff.rfl

/-- **A polynomial invariant in every direction is constant.** -/
theorem eq_C_of_translationSubmodule_eq_top {P : MvPolynomial ι K}
    (h : translationSubmodule P = ⊤) : P = C (eval (fun _ => (0 : K)) P) := by
  apply MvPolynomial.funext
  intro x
  have hx : mvShift x P = P := by
    have : x ∈ translationSubmodule P := by rw [h]; trivial
    exact this
  have he := congrArg (eval fun _ : ι => (0 : K)) hx
  rw [eval_mvShift] at he
  simp only [zero_add] at he
  simpa using he

/-- **A spanning set of invariance directions forces constancy.** -/
theorem eq_C_of_span_translations_eq_top {P : MvPolynomial ι K} {s : Set (ι → K)}
    (hs : Submodule.span K s = ⊤) (hinv : ∀ v ∈ s, mvShift v P = P) :
    P = C (eval (fun _ => (0 : K)) P) := by
  refine eq_C_of_translationSubmodule_eq_top ?_
  rw [eq_top_iff, ← hs]
  exact Submodule.span_le.mpr fun v hv => hinv v hv

/-- **One nonzero translation per coordinate already forces constancy.**  In characteristic zero a
nonconstant polynomial is never periodic, so no density of the translation group is required. -/
theorem eq_C_of_coordinate_shift_invariant [Fintype ι] [DecidableEq ι] {P : MvPolynomial ι K}
    {c : ι → K} (hc : ∀ i, c i ≠ 0) (h : ∀ i, mvShift (Pi.single i (c i)) P = P) :
    P = C (eval (fun _ => (0 : K)) P) := by
  refine eq_C_of_span_translations_eq_top
    (s := Set.range fun i => (Pi.single i (c i) : ι → K)) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have hsum : ∑ i : ι, (x i / c i) • (Pi.single i (c i) : ι → K) = x := by
      funext j
      rw [Finset.sum_apply]
      have : ∀ i : ι, ((x i / c i) • (Pi.single i (c i) : ι → K)) j
          = if j = i then x j else 0 := by
        intro i
        rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hji : j = i
        · subst hji
          rw [if_pos rfl, if_pos rfl, div_mul_cancel₀ _ (hc j)]
        · rw [if_neg hji, if_neg hji, mul_zero]
      rw [Finset.sum_congr rfl fun i _ => this i]
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rintro v ⟨i, rfl⟩
    exact h i

end

end MvTranslation

end GaloisForLFunctions.HTGeometry
