import GaloisForLFunctions.HTGeometry.QShiftField

/-!
# The algebraic q-increments

The jets of the logarithmic derivative of Jackson's multiplier are rational functions of `u = qᶻ`
alone:

`δ₀ = −(log q)·u/(1−u)`,  `δ_{j+1} = (log q)·u·∂_u δ_j`,

so `δ_j = A_j(u)/(1−u)^{j+1}` with `A_j(1) = −(log q)^{j+1}·j! ≠ 0`.  This file builds the
numerators `A_j`, the increments as elements of `ℂ(z,u)`, and the fact that any nonzero constant
combination of them has `u = 1` as its only complex pole — the hypothesis that turns the coboundary
obstruction into the elimination engine's residue condition.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxSynthPendingDepth 4

noncomputable section

/-- The logarithm of the nome, as a complex constant. -/
def qLog (q : RealEulerNome) : ℂ := (Real.log q.val : ℂ)

theorem qLog_ne_zero (q : RealEulerNome) : qLog q ≠ 0 := by
  rw [qLog]
  intro h0
  have hr : Real.log q.val = 0 := by
    exact_mod_cast h0
  have hneg : Real.log q.val < 0 := Real.log_neg q.pos q.lt_one
  rw [hr] at hneg
  exact absurd hneg (lt_irrefl 0)

/-- The numerators `A_j` of the algebraic increments. -/
def qIncrNum (q : RealEulerNome) : ℕ → Polynomial ℂ
  | 0 => -(Polynomial.C (qLog q)) * Polynomial.X
  | j + 1 =>
      Polynomial.C (qLog q) * Polynomial.X
        * (Polynomial.derivative (qIncrNum q j) * (1 - Polynomial.X)
          + Polynomial.C ((j : ℂ) + 1) * qIncrNum q j)

theorem qIncrNum_zero (q : RealEulerNome) :
    qIncrNum q 0 = -(Polynomial.C (qLog q)) * Polynomial.X := rfl

theorem qIncrNum_succ (q : RealEulerNome) (j : ℕ) :
    qIncrNum q (j + 1)
      = Polynomial.C (qLog q) * Polynomial.X
        * (Polynomial.derivative (qIncrNum q j) * (1 - Polynomial.X)
          + Polynomial.C ((j : ℂ) + 1) * qIncrNum q j) := rfl

/-- **The numerators do not vanish at `u = 1`:** `A_j(1) = −(log q)^{j+1}·j!`. -/
theorem qIncrNum_eval_one (q : RealEulerNome) (j : ℕ) :
    (qIncrNum q j).eval 1 = -(qLog q) ^ (j + 1) * (j.factorial : ℂ) := by
  induction j with
  | zero =>
    rw [qIncrNum_zero]
    simp
  | succ j ih =>
    rw [qIncrNum_succ]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_one, sub_self, mul_zero, zero_add]
    rw [ih, Nat.factorial_succ]
    push_cast
    ring

theorem qIncrNum_eval_one_ne_zero (q : RealEulerNome) (j : ℕ) : (qIncrNum q j).eval 1 ≠ 0 := by
  rw [qIncrNum_eval_one]
  refine mul_ne_zero ?_ ?_
  · exact neg_ne_zero.mpr (pow_ne_zero _ (qLog_ne_zero q))
  · exact_mod_cast Nat.factorial_ne_zero j

/-- The numerators, transported to polynomials over `ℂ(z)`. -/
def qIncrNumC (q : RealEulerNome) (j : ℕ) : Polynomial (RatFunc ℂ) :=
  (qIncrNum q j).map (algebraMap ℂ (RatFunc ℂ))

theorem evalConst_qIncrNumC (q : RealEulerNome) (j : ℕ) (c : ℂ) :
    evalConst (qIncrNumC q j) c = algebraMap ℂ (RatFunc ℂ) ((qIncrNum q j).eval c) := by
  rw [evalConst, qIncrNumC, Polynomial.eval_map, Polynomial.eval₂_at_apply]

theorem evalConst_qIncrNumC_one_ne_zero (q : RealEulerNome) (j : ℕ) :
    evalConst (qIncrNumC q j) 1 ≠ 0 := by
  rw [evalConst_qIncrNumC]
  intro h0
  exact qIncrNum_eval_one_ne_zero q j
    ((algebraMap ℂ (RatFunc ℂ)).injective (h0.trans (map_zero _).symm))

/-- The pole factor `(1 − u)^{j+1}`. -/
def qPoleFactor (j : ℕ) : Polynomial (RatFunc ℂ) := (1 - Polynomial.X) ^ (j + 1)

theorem qPoleFactor_ne_zero (j : ℕ) : qPoleFactor j ≠ 0 := by
  rw [qPoleFactor]
  refine pow_ne_zero _ ?_
  intro h0
  have hcoeff := congrArg (fun p => Polynomial.coeff p 0) h0
  simp at hcoeff

theorem evalConst_qPoleFactor (j : ℕ) (c : ℂ) :
    evalConst (qPoleFactor j) c = (1 - algebraMap ℂ (RatFunc ℂ) c) ^ (j + 1) := by
  rw [qPoleFactor, evalConst, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X]

theorem evalConst_qPoleFactor_eq_zero_iff (j : ℕ) (c : ℂ) :
    evalConst (qPoleFactor j) c = 0 ↔ c = 1 := by
  rw [evalConst_qPoleFactor]
  constructor
  · intro h0
    have hbase : (1 : RatFunc ℂ) - algebraMap ℂ (RatFunc ℂ) c = 0 := by
      exact pow_eq_zero_iff (n := j + 1) (by omega) |>.mp h0
    have hone : algebraMap ℂ (RatFunc ℂ) c = algebraMap ℂ (RatFunc ℂ) 1 := by
      rw [map_one]
      linear_combination -hbase
    exact (algebraMap ℂ (RatFunc ℂ)).injective hone
  · intro h1
    rw [h1, map_one, sub_self]
    exact zero_pow (by omega)

/-- **The algebraic increments** `δ_j = A_j(u)/(1−u)^{j+1}` inside `ℂ(z,u)`. -/
def qIncr (q : RealEulerNome) (j : ℕ) : RatFunc (RatFunc ℂ) :=
  algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qIncrNumC q j)
    / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qPoleFactor j)

/-! ## Combinations of the increments -/

theorem algebraMapPoly_ne_zero {A : Polynomial (RatFunc ℂ)} (hA : A ≠ 0) :
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) A ≠ 0 := fun h0 =>
  hA (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))

/-- The combined numerator of a constant combination of increments. -/
def qIncrCombNum (q : RealEulerNome) {m : ℕ} (c : Fin m → ℂ) (N : ℕ) : Polynomial (RatFunc ℂ) :=
  ∑ j : Fin m, Polynomial.C (algebraMap ℂ (RatFunc ℂ) (c j)) * qIncrNumC q j
    * (1 - Polynomial.X) ^ (N - (j : ℕ))

/-- **Common denominator.**  A constant combination of increments supported below `N` is a single
fraction with denominator `(1−u)^{N+1}`. -/
theorem qIncr_combination_eq (q : RealEulerNome) {m : ℕ} (c : Fin m → ℂ) (N : ℕ)
    (hmax : ∀ j : Fin m, c j ≠ 0 → (j : ℕ) ≤ N) :
    (∑ j : Fin m, algebraMap ℂ (RatFunc (RatFunc ℂ)) (c j) * qIncr q j)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qIncrCombNum q c N)
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qPoleFactor N) := by
  rw [qIncrCombNum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpole : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qPoleFactor N) ≠ 0 :=
    algebraMapPoly_ne_zero (qPoleFactor_ne_zero N)
  have hpolej : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      (qPoleFactor (j : ℕ)) ≠ 0 := algebraMapPoly_ne_zero (qPoleFactor_ne_zero _)
  by_cases hcj : c j = 0
  · rw [hcj]
    simp
  · have hjN : (j : ℕ) ≤ N := hmax j hcj
    have hfac : (1 - Polynomial.X : Polynomial (RatFunc ℂ)) ^ (N - (j : ℕ))
        * qPoleFactor (j : ℕ) = qPoleFactor N := by
      rw [qPoleFactor, qPoleFactor, ← pow_add]
      congr 1
      omega
    have hconst : algebraMap ℂ (RatFunc (RatFunc ℂ)) (c j)
        = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
          (Polynomial.C (algebraMap ℂ (RatFunc ℂ) (c j))) := by
      rw [algebraMap_polyC_qShiftField, ← IsScalarTower.algebraMap_apply]
    rw [qIncr, hconst, mul_div_assoc', div_eq_div_iff hpolej hpole, ← hfac]
    simp only [map_mul]
    ring

theorem evalConst_qIncrCombNum_one (q : RealEulerNome) {m : ℕ} (c : Fin m → ℂ) (N : Fin m)
    (hmax : ∀ j : Fin m, c j ≠ 0 → (j : ℕ) ≤ (N : ℕ)) :
    evalConst (qIncrCombNum q c (N : ℕ)) 1
      = algebraMap ℂ (RatFunc ℂ) (c N) * evalConst (qIncrNumC q (N : ℕ)) 1 := by
  rw [qIncrCombNum, evalConst, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single N]
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X]
    rw [Nat.sub_self, pow_zero, mul_one]
    rfl
  · intro j _ hjN
    by_cases hcj : c j = 0
    · rw [hcj]
      simp
    · have hjle : (j : ℕ) ≤ (N : ℕ) := hmax j hcj
      have hjlt : (j : ℕ) < (N : ℕ) := lt_of_le_of_ne hjle (fun h => hjN (Fin.ext h))
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_X]
      rw [show (1 : RatFunc ℂ) - algebraMap ℂ (RatFunc ℂ) 1 = 0 by rw [map_one, sub_self]]
      rw [zero_pow (by omega), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ N) hmem

theorem evalConst_dvd_zero {A B : Polynomial (RatFunc ℂ)} (hdvd : A ∣ B) {c : ℂ}
    (hA : evalConst A c = 0) : evalConst B c = 0 := by
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, evalConst_mul, hA, zero_mul]

/-- **The residue condition of the elimination engine.**  No nonzero constant combination of the
increments is a `σ`-coboundary. -/
theorem qIncr_not_coboundary (q : RealEulerNome) {m : ℕ} {w : RatFunc (RatFunc ℂ)}
    {c : Fin m → ℂ}
    (h : qShift q w - w
      = ∑ j : Fin m, algebraMap ℂ (RatFunc (RatFunc ℂ)) (c j) * qIncr q j) :
    ∀ j, c j = 0 := by
  classical
  by_contra hcon
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin m, c j ≠ 0 := by
    by_contra hall
    exact hcon fun j => not_not.mp fun hj => hall ⟨j, hj⟩
  set supp := Finset.univ.filter (fun j : Fin m => c j ≠ 0) with hsupp_def
  have hsuppne : supp.Nonempty := ⟨j₀, by rw [hsupp_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj₀⟩⟩
  obtain ⟨N, hNmem, hNmax⟩ := supp.exists_max_image (fun j : Fin m => (j : ℕ)) hsuppne
  have hcN : c N ≠ 0 := by
    have := hNmem
    rw [hsupp_def, Finset.mem_filter] at this
    exact this.2
  have hmax : ∀ j : Fin m, c j ≠ 0 → (j : ℕ) ≤ (N : ℕ) := by
    intro j hj
    exact hNmax j (by rw [hsupp_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩)
  set D : RatFunc (RatFunc ℂ) :=
    ∑ j : Fin m, algebraMap ℂ (RatFunc (RatFunc ℂ)) (c j) * qIncr q j with hD_def
  have hDrep : D = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (qIncrCombNum q c (N : ℕ))
      / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qPoleFactor (N : ℕ)) :=
    qIncr_combination_eq q c (N : ℕ) hmax
  -- the poles of `D` are contained in `{1}`
  have hdvd : D.denom ∣ qPoleFactor (N : ℕ) := by
    rw [hDrep]
    exact RatFunc.denom_div_dvd _ _
  have hDonly : ∀ c₀ : ℂ, evalConst D.denom c₀ = 0 → c₀ = 1 := by
    intro c₀ h0
    exact (evalConst_qPoleFactor_eq_zero_iff (N : ℕ) c₀).mp (evalConst_dvd_zero hdvd h0)
  -- `D` really has a pole at `1`
  have hpoleK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      (qPoleFactor (N : ℕ)) ≠ 0 := algebraMapPoly_ne_zero (qPoleFactor_ne_zero _)
  have hdenK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) D.denom ≠ 0 :=
    algebraMapPoly_ne_zero D.denom_ne_zero
  have hcross : qIncrCombNum q c (N : ℕ) * D.denom = D.num * qPoleFactor (N : ℕ) := by
    apply RatFunc.algebraMap_injective (RatFunc ℂ)
    have hnum : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) D.num
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) D.denom = D :=
      RatFunc.num_div_denom D
    have heq : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
          (qIncrCombNum q c (N : ℕ))
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qPoleFactor (N : ℕ))
        = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) D.num
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) D.denom := by
      rw [hnum, ← hDrep]
    rw [div_eq_div_iff hpoleK hdenK] at heq
    simp only [map_mul]
    linear_combination heq
  have hDpole : evalConst D.denom 1 = 0 := by
    have hev := congrArg (fun p => evalConst p 1) hcross
    simp only [evalConst_mul] at hev
    rw [(evalConst_qPoleFactor_eq_zero_iff (N : ℕ) 1).mpr rfl, mul_zero] at hev
    have hnum1 : evalConst (qIncrCombNum q c (N : ℕ)) 1 ≠ 0 := by
      rw [evalConst_qIncrCombNum_one q c N hmax]
      refine mul_ne_zero ?_ (evalConst_qIncrNumC_one_ne_zero q (N : ℕ))
      intro h0
      exact hcN ((algebraMap ℂ (RatFunc ℂ)).injective (h0.trans (map_zero _).symm))
    rcases mul_eq_zero.mp hev with h1 | h1
    · exact absurd h1 hnum1
    · exact h1
  exact qShift_sub_self_ne q w D hDpole hDonly (by rw [hD_def] at h ⊢; exact h)

end

end GaloisForLFunctions.HTGeometry
