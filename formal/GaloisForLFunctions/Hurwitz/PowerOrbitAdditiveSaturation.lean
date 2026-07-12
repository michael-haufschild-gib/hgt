import GaloisForLFunctions.Hurwitz.MulticolumnPowerOrbit
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Additive saturation of coupled power orbits

The key strengthening beyond one-column toric density is additive.  A polynomial that vanishes on
all independent branch-power deformations has translation differences of strictly smaller degree.
Induction makes those differences identically zero.  The Vandermonde span of consecutive power
increments then supplies the individual branch directions, and their linear span fills the whole
value space.
-/

open Complex

namespace HurwitzJointOrbit

noncomputable section

/-- Translation of all variables of a multivariate polynomial by a vector. -/
def mvTranslate {σ : Type*} (v : σ → ℂ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  MvPolynomial.bind₁ (fun i => MvPolynomial.X i + MvPolynomial.C (v i))

@[simp]
theorem mvTranslate_C {σ : Type*} (v : σ → ℂ) (c : ℂ) :
    mvTranslate v (MvPolynomial.C c : MvPolynomial σ ℂ) = MvPolynomial.C c := by
  simp [mvTranslate]

@[simp]
theorem mvTranslate_X {σ : Type*} (v : σ → ℂ) (i : σ) :
    mvTranslate v (MvPolynomial.X i : MvPolynomial σ ℂ) =
      MvPolynomial.X i + MvPolynomial.C (v i) := by
  simp [mvTranslate]

theorem eval_mvTranslate {σ : Type*} (v x : σ → ℂ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (mvTranslate v P) =
      MvPolynomial.eval (fun i => x i + v i) P := by
  rw [mvTranslate]
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x
      (MvPolynomial.bind₁
        (fun i => MvPolynomial.X i + MvPolynomial.C (v i)) P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  simp

theorem mvTranslate_add {σ : Type*} (v w : σ → ℂ) (P : MvPolynomial σ ℂ) :
    mvTranslate v (mvTranslate w P) = mvTranslate (fun i => v i + w i) P := by
  change ((mvTranslate v).comp (mvTranslate w)) P = _
  congr 1
  ext i
  simp [mvTranslate]
  abel

@[simp]
theorem mvTranslate_zero {σ : Type*} (P : MvPolynomial σ ℂ) :
    mvTranslate (fun _ => 0) P = P := by
  rw [mvTranslate]
  simpa using MvPolynomial.bind₁_X_left P

/-- Translation directions fixing a polynomial, initially as an additive subgroup. -/
def translationInvariantAddSubgroup {σ : Type*} (P : MvPolynomial σ ℂ) :
    AddSubgroup (σ → ℂ) where
  carrier := {v | mvTranslate v P = P}
  zero_mem' := mvTranslate_zero P
  add_mem' {v w} hv hw := by
    change mvTranslate (fun i => v i + w i) P = P
    calc
      mvTranslate (fun i => v i + w i) P = mvTranslate v (mvTranslate w P) :=
        (mvTranslate_add v w P).symm
      _ = mvTranslate v P := by rw [hw]
      _ = P := hv
  neg_mem' {v} hv := by
    have h := congrArg (mvTranslate (fun i => -v i)) hv
    rw [mvTranslate_add] at h
    simpa using h.symm

/-- Restriction of a multivariate polynomial to the affine line `x + t v`. -/
def linePolynomial {σ : Type*} (x v : σ → ℂ) (P : MvPolynomial σ ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) P

theorem eval_linePolynomial {σ : Type*} (x v : σ → ℂ)
    (P : MvPolynomial σ ℂ) (t : ℂ) :
    (linePolynomial x v P).eval t =
      MvPolynomial.eval (fun i => x i + t * v i) P := by
  rw [linePolynomial]
  have h := MvPolynomial.map_eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))
    (Polynomial.evalRingHom t) P
  have hC : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id ℂ := by
    ext z
    simp
  have hg : (fun i => (Polynomial.evalRingHom t)
      (Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i))) =
      fun i => x i + t * v i := by
    funext i
    simp
    ring
  rw [hC, hg] at h
  change Polynomial.eval t (linePolynomial x v P) =
    MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => x i + t * v i) P at h
  rw [MvPolynomial.eval₂_id] at h
  exact h

/-- Additive translation invariance automatically extends to every complex scalar multiple of a
direction: the line restriction has all nonnegative integers as roots. -/
theorem mvTranslate_smul_eq_of_eq {σ : Type*} (P : MvPolynomial σ ℂ)
    (v : σ → ℂ) (hv : mvTranslate v P = P) (c : ℂ) :
    mvTranslate (fun i => c * v i) P = P := by
  apply MvPolynomial.funext
  intro x
  let R : Polynomial ℂ := linePolynomial x v P - Polynomial.C (MvPolynomial.eval x P)
  have hRzero : R = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinj : Function.Injective (fun n : ℕ => (n : ℂ)) := Nat.cast_injective
    refine (Set.infinite_range_of_injective hinj).mono ?_
    rintro t ⟨n, rfl⟩
    change Polynomial.eval (n : ℂ) R = 0
    dsimp only [R]
    rw [Polynomial.eval_sub, eval_linePolynomial,
      Polynomial.eval_C, sub_eq_zero]
    have hnmem : n • v ∈ translationInvariantAddSubgroup P :=
      (translationInvariantAddSubgroup P).nsmul_mem hv n
    have hnmem' : mvTranslate (n • v) P = P := hnmem
    have hnfun : n • v = fun i => (n : ℂ) * v i := by
      funext i
      simp [nsmul_eq_mul]
    rw [hnfun] at hnmem'
    have he := congrArg (MvPolynomial.eval x) hnmem'
    rw [eval_mvTranslate] at he
    exact he
  have hc := congrArg (Polynomial.eval c) hRzero
  dsimp only [R] at hc
  rw [Polynomial.eval_sub, eval_linePolynomial, Polynomial.eval_C,
    Polynomial.eval_zero, sub_eq_zero] at hc
  rw [eval_mvTranslate]
  exact hc

/-- Translation directions fixing a polynomial form a complex linear subspace. -/
def translationInvariantSubmodule {σ : Type*} (P : MvPolynomial σ ℂ) :
    Submodule ℂ (σ → ℂ) where
  __ := translationInvariantAddSubgroup P
  smul_mem' c v hv := by
    change mvTranslate (fun i => c * v i) P = P
    exact mvTranslate_smul_eq_of_eq P v hv c

/-- Affine translation does not increase total degree. -/
theorem totalDegree_mvTranslate_le {σ : Type*} (v : σ → ℂ)
    (P : MvPolynomial σ ℂ) :
    (mvTranslate v P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  apply Finset.sup_le
  intro d hd
  rw [mvTranslate, MvPolynomial.bind₁_monomial]
  calc
    (MvPolynomial.C (MvPolynomial.coeff d P) *
        ∏ i ∈ d.support,
          (MvPolynomial.X i + MvPolynomial.C (v i)) ^ d i).totalDegree ≤
      (∏ i ∈ d.support,
          (MvPolynomial.X i + MvPolynomial.C (v i)) ^ d i).totalDegree := by
        simpa using MvPolynomial.totalDegree_mul
          (MvPolynomial.C (MvPolynomial.coeff d P))
          (∏ i ∈ d.support,
            (MvPolynomial.X i + MvPolynomial.C (v i)) ^ d i)
    _ ≤ ∑ i ∈ d.support,
        ((MvPolynomial.X i + MvPolynomial.C (v i)) ^ d i).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ((MvPolynomial.X i + MvPolynomial.C (v i)) ^ d i).totalDegree ≤
            d i * (MvPolynomial.X i + MvPolynomial.C (v i)).totalDegree :=
          MvPolynomial.totalDegree_pow _ _
        _ ≤ d i * 1 := Nat.mul_le_mul_left _
          (MvPolynomial.totalDegree_add _ _ |>.trans
            (max_le (by simp) (by simp)))
        _ = d i := Nat.mul_one _
    _ = d.degree := by rw [Finsupp.degree_apply]
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

theorem pderiv_mvTranslate {σ : Type*} [DecidableEq σ]
    (v : σ → ℂ) (i : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv i (mvTranslate v P) =
      mvTranslate v (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      simp only [map_mul, mvTranslate_X,
        Derivation.leibniz, hP, map_add, MvPolynomial.pderiv_X,
        MvPolynomial.pderiv_C, smul_eq_mul]
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

/-- A partial derivative strictly lowers positive total degree. -/
theorem totalDegree_pderiv_lt {σ : Type*} [DecidableEq σ]
    (i : σ) (P : MvPolynomial σ ℂ) (hD : 0 < P.totalDegree) :
    (MvPolynomial.pderiv i P).totalDegree < P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_lt_iff hD]
  intro d hd
  rw [MvPolynomial.pderiv_monomial]
  by_cases hi : d i = 0
  · simp [hi, hD]
  · have hdrop : (d - Finsupp.single i 1).degree + 1 = d.degree := by
      simpa [Finsupp.degree_eq_weight_one] using
        (Finsupp.weight_sub_single_add (w := (1 : σ → ℕ)) hi)
    calc
      (MvPolynomial.monomial (d - Finsupp.single i 1)
          (MvPolynomial.coeff d P * d i)).totalDegree ≤
        (d - Finsupp.single i 1).degree :=
          MvPolynomial.totalDegree_monomial_le _ _
      _ < d.degree := by omega
      _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

/-- The coefficient immediately below a monomial in one coordinate derivative comes from that
unique monomial.  This is the coefficient-level injectivity needed to read top-degree terms from
partial derivatives. -/
theorem coeff_pderiv_pred {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℂ) (d : σ →₀ ℕ) (i : σ) (hi : d i ≠ 0) :
    MvPolynomial.coeff (d - Finsupp.single i 1) (MvPolynomial.pderiv i P) =
      MvPolynomial.coeff d P * d i := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, MvPolynomial.coeff_sum]
  by_cases hd : d ∈ P.support
  · rw [Finset.sum_eq_single d]
    · rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
      simp
    · intro e he hed
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
      by_cases hei : e i = 0
      · simp [hei]
      · have hne : e - Finsupp.single i 1 ≠ d - Finsupp.single i 1 := by
          intro hsub
          apply hed
          calc
            e = (e - Finsupp.single i 1) + Finsupp.single i 1 :=
              (Finsupp.sub_add_single_one_cancel hei).symm
            _ = (d - Finsupp.single i 1) + Finsupp.single i 1 := by rw [hsub]
            _ = d := Finsupp.sub_add_single_one_cancel hi
        simp [hne]
    · exact fun h => (h hd).elim
  · have hcd : MvPolynomial.coeff d P = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    rw [hcd, zero_mul]
    apply Finset.sum_eq_zero
    intro e he
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial]
    by_cases hei : e i = 0
    · simp [hei]
    · have hne : e - Finsupp.single i 1 ≠ d - Finsupp.single i 1 := by
        intro hsub
        apply hd
        have hed : e = d := by
          calc
            e = (e - Finsupp.single i 1) + Finsupp.single i 1 :=
              (Finsupp.sub_add_single_one_cancel hei).symm
            _ = (d - Finsupp.single i 1) + Finsupp.single i 1 := by rw [hsub]
            _ = d := Finsupp.sub_add_single_one_cancel hi
        simpa [hed] using he
      simp [hne]

/-- If every nonzero partial derivative lies strictly below degree `D - 1`, then the polynomial
itself lies strictly below degree `D`.  The zero-derivative alternative is stated explicitly because
`totalDegree 0 = 0`. -/
theorem totalDegree_lt_of_pderiv_small {σ : Type*} [Fintype σ]
    [DecidableEq σ] (Q : MvPolynomial σ ℂ) (D : ℕ) (hD : 0 < D)
    (hsmall : ∀ i : σ, MvPolynomial.pderiv i Q = 0 ∨
      (MvPolynomial.pderiv i Q).totalDegree < D - 1) :
    Q.totalDegree < D := by
  by_contra hnot
  have hDQ : D ≤ Q.totalDegree := Nat.le_of_not_gt hnot
  have hQ : Q ≠ 0 := by
    intro hzero
    rw [hzero, MvPolynomial.totalDegree_zero] at hDQ
    omega
  obtain ⟨d, hd, hdeg⟩ := Q.support.exists_mem_eq_sup
    (Finsupp.support_nonempty_iff.mpr hQ)
    (fun m : σ →₀ ℕ => Multiset.card (Finsupp.toMultiset m))
  have hdegree : d.degree = Q.totalDegree := by
    calc
      d.degree = d.sum (fun _ => id) := rfl
      _ = Multiset.card (Finsupp.toMultiset d) := (Finsupp.card_toMultiset d).symm
      _ = Q.support.sup
          (fun m : σ →₀ ℕ => Multiset.card (Finsupp.toMultiset m)) := hdeg.symm
      _ = Q.totalDegree := (MvPolynomial.totalDegree_eq Q).symm
  have hdpos : 0 < d.degree := by omega
  have hdne : d ≠ 0 := by
    intro hzero
    simp [hzero] at hdpos
  obtain ⟨i, hiSupp⟩ := Finsupp.support_nonempty_iff.mpr hdne
  have hi : d i ≠ 0 := Finsupp.mem_support_iff.mp hiSupp
  let e := d - Finsupp.single i 1
  have hcoeff : MvPolynomial.coeff e (MvPolynomial.pderiv i Q) ≠ 0 := by
    rw [show e = d - Finsupp.single i 1 by rfl,
      coeff_pderiv_pred Q d i hi]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) (by exact_mod_cast hi)
  have he : e ∈ (MvPolynomial.pderiv i Q).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hedegree : e.degree + 1 = d.degree := by
    dsimp only [e]
    simpa [Finsupp.degree_eq_weight_one] using
      (Finsupp.weight_sub_single_add (w := (1 : σ → ℕ)) hi)
  have hlarge : D - 1 ≤ (MvPolynomial.pderiv i Q).totalDegree := by
    calc
      D - 1 ≤ d.degree - 1 := Nat.sub_le_sub_right (hdegree ▸ hDQ) 1
      _ = e.degree := by omega
      _ ≤ (MvPolynomial.pderiv i Q).totalDegree := MvPolynomial.le_totalDegree he
  rcases hsmall i with hzero | hlt
  · exact hcoeff (by rw [hzero]; simp)
  · omega

/-- **Strict translation-degree drop.**  Translating a nonconstant multivariate polynomial and
subtracting the original cancels its entire top homogeneous part. -/
theorem totalDegree_mvTranslate_sub_lt {σ : Type*} [Fintype σ]
    [DecidableEq σ] (v : σ → ℂ) (P : MvPolynomial σ ℂ)
    (hP : 0 < P.totalDegree) :
    (mvTranslate v P - P).totalDegree < P.totalDegree := by
  generalize hD : P.totalDegree = D at hP ⊢
  induction D using Nat.strong_induction_on generalizing P with
  | h D ih =>
      apply totalDegree_lt_of_pderiv_small (mvTranslate v P - P) D hP
      intro i
      rw [map_sub, pderiv_mvTranslate]
      let R := MvPolynomial.pderiv i P
      change mvTranslate v R - R = 0 ∨ (mvTranslate v R - R).totalDegree < D - 1
      by_cases hRdegree : R.totalDegree = 0
      · left
        rw [(MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hRdegree), mvTranslate_C,
          sub_self]
      · right
        have hRlt : R.totalDegree < D := by
          dsimp only [R]
          rw [← hD]
          exact totalDegree_pderiv_lt i P (hD ▸ hP)
        have hdrop := ih R.totalDegree hRlt R rfl (Nat.pos_of_ne_zero hRdegree)
        omega

end

end HurwitzJointOrbit
