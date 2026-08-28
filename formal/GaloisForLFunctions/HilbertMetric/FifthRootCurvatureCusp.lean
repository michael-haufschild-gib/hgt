import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationLocal

open Set

namespace HilbertMetric

noncomputable section

/-!
# Fifth-root divided-drop curvature at the coalesced endpoint

For an even smooth profile `f`, this module studies the exact curvature numerator governing
convexity of `x ↦ (f 0 - f √x)^(1/5)`.  Its first possible nonzero coalesced jet is the eighth,
and that jet is exactly the second--sixth Hankel determinant of `f`, up to a positive factor.
Consequently, a strict Hankel margin forces the fifth-root curvature numerator to be positive
on a punctured right neighborhood of the cusp.
-/

/-- Polynomial numerator controlling fifth-root divided-drop curvature. -/
def fifthRootDividedDropCurvatureNumerator (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  let A := f 0 - f t
  let f₁ := iteratedDeriv 1 f t
  let f₂ := iteratedDeriv 2 f t
  24 * A ^ 2 + 9 * t * A * f₁ + t ^ 2 * (-5 * A * f₂ - 4 * f₁ ^ 2)

/-- Even profiles have an even fifth-root curvature numerator. -/
theorem fifthRootDividedDropCurvatureNumerator_even
    {f : ℝ → ℝ} (heven : Function.Even f) :
    Function.Even (fifthRootDividedDropCurvatureNumerator f) := by
  have hfun : (fun x : ℝ => f (-x)) = f := funext heven
  have h₁neg (t : ℝ) :
      iteratedDeriv 1 f (-t) = -iteratedDeriv 1 f t := by
    have hcomp := iteratedDeriv_comp_neg 1 f t
    rw [hfun] at hcomp
    norm_num at hcomp
    simp only [iteratedDeriv_one]
    linarith
  have h₂neg (t : ℝ) :
      iteratedDeriv 2 f (-t) = iteratedDeriv 2 f t := by
    have hcomp := iteratedDeriv_comp_neg 2 f t
    rw [hfun] at hcomp
    norm_num at hcomp
    exact hcomp.symm
  intro t
  unfold fifthRootDividedDropCurvatureNumerator
  rw [heven, h₁neg, h₂neg]
  ring

private def fifthRootCurvatureJetProductAtZero (n : ℕ) (P Q : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * iteratedDeriv i P 0 * iteratedDeriv (n - i) Q 0

private theorem iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero
    {P Q : ℝ → ℝ} {n : ℕ}
    (hP : ContDiff ℝ n P) (hQ : ContDiff ℝ n Q) :
    iteratedDeriv n (P * Q) 0 = fifthRootCurvatureJetProductAtZero n P Q := by
  exact iteratedDeriv_mul hP.contDiffAt hQ.contDiffAt

private theorem contDiff_top_iteratedDeriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (k : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv k f) := by
  rw [contDiff_iff_iteratedDeriv]
  constructor
  · intro m _
    rw [show iteratedDeriv m (iteratedDeriv k f) =
      iteratedDeriv (m + k) f by
        simp only [iteratedDeriv_eq_iterate]
        rw [Function.iterate_add_apply]]
    exact hf.continuous_iteratedDeriv _ (by exact_mod_cast le_top)
  · intro m _
    rw [show iteratedDeriv m (iteratedDeriv k f) =
      iteratedDeriv (m + k) f by
        simp only [iteratedDeriv_eq_iterate]
        rw [Function.iterate_add_apply]]
    exact hf.differentiable_iteratedDeriv _ (by exact_mod_cast WithTop.coe_lt_top (m + k))

private theorem natCast_le_coe_enatTop (n : ℕ) :
    (n : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact WithTop.coe_le_coe.mpr (by exact_mod_cast le_top)

private theorem natCast_lt_coe_enatTop (n : ℕ) :
    (n : WithTop ℕ∞) < (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)

private theorem iteratedDeriv_zero_of_even_at_zero_of_odd
    {f : ℝ → ℝ} (heven : Function.Even f) {n : ℕ} (hn : Odd n) :
    iteratedDeriv n f 0 = 0 := by
  have hfun : (fun x : ℝ => f (-x)) = f := funext heven
  have hcomp := iteratedDeriv_comp_neg n f 0
  rw [hfun, neg_zero, hn.neg_one_pow] at hcomp
  simp only [neg_one_smul] at hcomp
  linarith

private theorem iteratedDeriv_id_mul_cusp
    (h : ℝ → ℝ) (hdiff : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m h)) :
    ∀ n : ℕ, iteratedDeriv (n + 1) (fun t => t * h t) =
      fun t => t * iteratedDeriv (n + 1) h t +
        (n + 1 : ℝ) * iteratedDeriv n h t := by
  intro n
  induction n with
  | zero =>
      rw [iteratedDeriv_one]
      funext t
      have hd : HasDerivAt (fun t : ℝ => t * h t)
          (1 * h t + t * deriv h t) t :=
        (hasDerivAt_id t).mul
          ((hdiff 0).differentiableAt.hasDerivAt.congr_deriv (by
            simp [iteratedDeriv_zero]))
      rw [hd.deriv]
      simp [iteratedDeriv_one, iteratedDeriv_zero]
      ring
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have hd : HasDerivAt
          (fun t : ℝ => t * iteratedDeriv (n + 1) h t +
            (n + 1 : ℝ) * iteratedDeriv n h t)
          ((1 * iteratedDeriv (n + 1) h t +
              t * deriv (iteratedDeriv (n + 1) h) t) +
            (n + 1 : ℝ) * deriv (iteratedDeriv n h) t) t :=
        ((hasDerivAt_id t).mul (hdiff (n + 1) t).hasDerivAt).add
          (((hdiff n) t).hasDerivAt.const_mul _)
      rw [hd.deriv, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
      push_cast
      ring

/-- The exact coalesced eighth jet is the second--sixth Hankel determinant times `1120`. -/
theorem iteratedDeriv_eight_fifthRootDividedDropCurvatureNumerator_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (heven : Function.Even f) :
    iteratedDeriv 8 (fifthRootDividedDropCurvatureNumerator f) 0 =
      1120 * (iteratedDeriv 2 f 0 * iteratedDeriv 6 f 0 -
        iteratedDeriv 4 f 0 ^ 2) := by
  let A : ℝ → ℝ := fun t => f 0 - f t
  let F₁ : ℝ → ℝ := iteratedDeriv 1 f
  let F₂ : ℝ → ℝ := iteratedDeriv 2 f
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A := by
    dsimp only [A]
    exact contDiff_const.sub hf
  have hF₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ := by
    exact contDiff_top_iteratedDeriv hf 1
  have hF₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ := by
    exact contDiff_top_iteratedDeriv hf 2
  have hAjet (n : ℕ) :
      iteratedDeriv n A 0 = if n = 0 then 0 else -iteratedDeriv n f 0 := by
    cases n with
    | zero => simp [A]
    | succ n =>
        rw [iteratedDeriv_const_sub (Nat.succ_pos n), iteratedDeriv_neg]
        rfl
  have hF₁jet (n : ℕ) :
      iteratedDeriv n F₁ 0 = iteratedDeriv (n + 1) f 0 := by
    dsimp only [F₁]
    simp only [iteratedDeriv_eq_iterate]
    rw [Function.iterate_add_apply]
  have hF₂jet (n : ℕ) :
      iteratedDeriv n F₂ 0 = iteratedDeriv (n + 2) f 0 := by
    dsimp only [F₂]
    simp only [iteratedDeriv_eq_iterate]
    rw [Function.iterate_add_apply]
  have hodd (n : ℕ) (hn : Odd n) : iteratedDeriv n f 0 = 0 := by
    exact iteratedDeriv_zero_of_even_at_zero_of_odd heven hn
  let E₁ : ℝ → ℝ := fun t => 24 * (A * A) t
  let E₂ : ℝ → ℝ := fun t => 9 * (t * ((A * F₁) t))
  let I : ℝ → ℝ := fun t => -5 * (A * F₂) t - 4 * (F₁ * F₁) t
  let E₃ : ℝ → ℝ := fun t => t * (t * I t)
  have hAA : ContDiff ℝ (↑(⊤ : ℕ∞)) (A * A) := hA.mul hA
  have hAF₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (A * F₁) := hA.mul hF₁
  have hAF₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (A * F₂) := hA.mul hF₂
  have hF₁F₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (F₁ * F₁) := hF₁.mul hF₁
  have hI : ContDiff ℝ (↑(⊤ : ℕ∞)) I := by
    dsimp only [I]
    fun_prop
  have hE₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) E₁ := by
    dsimp only [E₁]
    fun_prop
  have hE₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) E₂ := by
    dsimp only [E₂]
    fun_prop
  have hE₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) E₃ := by
    dsimp only [E₃]
    fun_prop
  have hAAjet (n : ℕ) : iteratedDeriv n (A * A) 0 = fifthRootCurvatureJetProductAtZero n A A :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hA.of_le (by exact_mod_cast le_top))
      (hA.of_le (by exact_mod_cast le_top))
  have hAF₁jet (n : ℕ) :
      iteratedDeriv n (A * F₁) 0 = fifthRootCurvatureJetProductAtZero n A F₁ :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hA.of_le (natCast_le_coe_enatTop n))
      (hF₁.of_le (natCast_le_coe_enatTop n))
  have hAF₂jet (n : ℕ) : iteratedDeriv n (A * F₂) 0 = fifthRootCurvatureJetProductAtZero n A F₂ :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hA.of_le (by exact_mod_cast le_top))
      (hF₂.of_le (by exact_mod_cast le_top))
  have hF₁F₁jet (n : ℕ) :
      iteratedDeriv n (F₁ * F₁) 0 = fifthRootCurvatureJetProductAtZero n F₁ F₁ :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hF₁.of_le (by exact_mod_cast le_top))
      (hF₁.of_le (by exact_mod_cast le_top))
  have hIjet (n : ℕ) :
      iteratedDeriv n I 0 =
        -5 * fifthRootCurvatureJetProductAtZero n A F₂ - 4 * fifthRootCurvatureJetProductAtZero n F₁ F₁ := by
    dsimp only [I]
    have hAF₂n : ContDiffAt ℝ n (A * F₂) 0 :=
      hAF₂.contDiffAt.of_le (natCast_le_coe_enatTop n)
    have hF₁F₁n : ContDiffAt ℝ n (F₁ * F₁) 0 :=
      hF₁F₁.contDiffAt.of_le (natCast_le_coe_enatTop n)
    have hleft : ContDiffAt ℝ n (fun t => -5 * (A * F₂) t) 0 := by
      fun_prop
    have hright : ContDiffAt ℝ n (fun t => 4 * (F₁ * F₁) t) 0 := by
      fun_prop
    change iteratedDeriv n
      ((fun t => -5 * (A * F₂) t) - fun t => 4 * (F₁ * F₁) t) 0 = _
    rw [iteratedDeriv_sub hleft hright,
      iteratedDeriv_const_mul (-5) hAF₂n,
      iteratedDeriv_const_mul 4 hF₁F₁n, hAF₂jet, hF₁F₁jet]
  have hE₁jet : iteratedDeriv 8 E₁ 0 = 24 * fifthRootCurvatureJetProductAtZero 8 A A := by
    dsimp only [E₁]
    rw [iteratedDeriv_const_mul 24
      (hAA.contDiffAt.of_le (natCast_le_coe_enatTop 8)), hAAjet]
  have hE₂jet :
      iteratedDeriv 8 E₂ 0 = 72 * fifthRootCurvatureJetProductAtZero 7 A F₁ := by
    dsimp only [E₂]
    have hcoordCont : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun t => t * (A * F₁) t) := by
      change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => t * (A t * F₁ t))
      fun_prop
    have hcoord := congrFun (iteratedDeriv_id_mul_cusp (A * F₁)
      (fun m => hAF₁.differentiable_iteratedDeriv m
        (natCast_lt_coe_enatTop m)) 7) 0
    have hcoord0 : iteratedDeriv 8 (fun t => t * (A * F₁) t) 0 =
        8 * fifthRootCurvatureJetProductAtZero 7 A F₁ := by
      norm_num at hcoord
      rw [hAF₁jet] at hcoord
      exact hcoord
    rw [iteratedDeriv_const_mul 9
      (hcoordCont.contDiffAt.of_le (natCast_le_coe_enatTop 8)), hcoord0]
    ring
  have hE₃jet : iteratedDeriv 8 E₃ 0 = 56 *
      (-5 * fifthRootCurvatureJetProductAtZero 6 A F₂ - 4 * fifthRootCurvatureJetProductAtZero 6 F₁ F₁) := by
    dsimp only [E₃]
    have hdiffI (m : ℕ) : Differentiable ℝ (iteratedDeriv m I) :=
      hI.differentiable_iteratedDeriv m
        (natCast_lt_coe_enatTop m)
    have hcoordI : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => t * I t) := by
      fun_prop
    have hinner := congrFun (iteratedDeriv_id_mul_cusp I hdiffI 6) 0
    have houter := congrFun (iteratedDeriv_id_mul_cusp (fun t => t * I t)
      (fun m => hcoordI.differentiable_iteratedDeriv m
        (natCast_lt_coe_enatTop m)) 7) 0
    norm_num at hinner houter
    calc
      iteratedDeriv 8 (fun t => t * (t * I t)) 0 =
          8 * iteratedDeriv 7 (fun t => t * I t) 0 := houter
      _ = 56 * iteratedDeriv 6 I 0 := by rw [hinner]; ring
      _ = _ := by rw [hIjet 6]
  rw [show fifthRootDividedDropCurvatureNumerator f = E₁ + E₂ + E₃ by
    funext t
    simp only [fifthRootDividedDropCurvatureNumerator, A, F₁, F₂, E₁, E₂, I, E₃,
      Pi.add_apply, Pi.mul_apply]
    ring]
  calc
    iteratedDeriv 8 (E₁ + E₂ + E₃) 0 =
        iteratedDeriv 8 (E₁ + E₂) 0 + iteratedDeriv 8 E₃ 0 := by
      exact iteratedDeriv_add
        ((hE₁.add hE₂).contDiffAt.of_le (natCast_le_coe_enatTop 8))
        (hE₃.contDiffAt.of_le (natCast_le_coe_enatTop 8))
    _ = (iteratedDeriv 8 E₁ 0 + iteratedDeriv 8 E₂ 0) +
        iteratedDeriv 8 E₃ 0 := by
      rw [iteratedDeriv_add
        (hE₁.contDiffAt.of_le (natCast_le_coe_enatTop 8))
        (hE₂.contDiffAt.of_le (natCast_le_coe_enatTop 8))]
    _ = _ := by
      rw [hE₁jet, hE₂jet, hE₃jet]
      norm_num [fifthRootCurvatureJetProductAtZero, Finset.sum_range_succ, Nat.choose,
        hAjet, hF₁jet, hF₂jet, hodd]
      ring

/-- Every curvature-numerator jet below order eight vanishes for an even smooth profile. -/
theorem iteratedDeriv_fifthRootDividedDropCurvatureNumerator_zero_of_lt_eight
    {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (heven : Function.Even f) {n : ℕ} (hn : n < 8) :
    iteratedDeriv n (fifthRootDividedDropCurvatureNumerator f) 0 = 0 := by
  by_cases hnodd : Odd n
  · exact iteratedDeriv_zero_of_even_at_zero_of_odd
      (fifthRootDividedDropCurvatureNumerator_even heven) hnodd
  have hnCases : n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 6 := by
    have hnEven : Even n := Nat.not_odd_iff_even.mp hnodd
    rcases hnEven with ⟨k, hk⟩
    omega
  let A : ℝ → ℝ := fun t => f 0 - f t
  let F₁ : ℝ → ℝ := iteratedDeriv 1 f
  let F₂ : ℝ → ℝ := iteratedDeriv 2 f
  let I : ℝ → ℝ := fun t => -5 * (A * F₂) t - 4 * (F₁ * F₁) t
  let E₁ : ℝ → ℝ := fun t => 24 * (A * A) t
  let E₂ : ℝ → ℝ := fun t => 9 * (t * ((A * F₁) t))
  let E₃ : ℝ → ℝ := fun t => t * (t * I t)
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞)) A := by
    dsimp only [A]
    exact contDiff_const.sub hf
  have hF₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁ :=
    contDiff_top_iteratedDeriv hf 1
  have hF₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂ :=
    contDiff_top_iteratedDeriv hf 2
  have hAA : ContDiff ℝ (↑(⊤ : ℕ∞)) (A * A) := hA.mul hA
  have hAF₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (A * F₁) := hA.mul hF₁
  have hAF₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (A * F₂) := hA.mul hF₂
  have hF₁F₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) (F₁ * F₁) := hF₁.mul hF₁
  have hI : ContDiff ℝ (↑(⊤ : ℕ∞)) I := by
    dsimp only [I]
    fun_prop
  have hE₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) E₁ := by
    dsimp only [E₁]
    fun_prop
  have hE₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) E₂ := by
    dsimp only [E₂]
    fun_prop
  have hE₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) E₃ := by
    dsimp only [E₃]
    fun_prop
  have hAjet (j : ℕ) :
      iteratedDeriv j A 0 = if j = 0 then 0 else -iteratedDeriv j f 0 := by
    cases j with
    | zero => simp [A]
    | succ j =>
        rw [iteratedDeriv_const_sub (Nat.succ_pos j), iteratedDeriv_neg]
        rfl
  have hF₁jet (j : ℕ) :
      iteratedDeriv j F₁ 0 = iteratedDeriv (j + 1) f 0 := by
    dsimp only [F₁]
    simp only [iteratedDeriv_eq_iterate]
    rw [Function.iterate_add_apply]
  have hF₂jet (j : ℕ) :
      iteratedDeriv j F₂ 0 = iteratedDeriv (j + 2) f 0 := by
    dsimp only [F₂]
    simp only [iteratedDeriv_eq_iterate]
    rw [Function.iterate_add_apply]
  have hodd (j : ℕ) (hj : Odd j) : iteratedDeriv j f 0 = 0 := by
    exact iteratedDeriv_zero_of_even_at_zero_of_odd heven hj
  have hAAjet (j : ℕ) :
      iteratedDeriv j (A * A) 0 = fifthRootCurvatureJetProductAtZero j A A :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hA.of_le (natCast_le_coe_enatTop j))
      (hA.of_le (natCast_le_coe_enatTop j))
  have hAF₁jet (j : ℕ) :
      iteratedDeriv j (A * F₁) 0 = fifthRootCurvatureJetProductAtZero j A F₁ :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hA.of_le (natCast_le_coe_enatTop j))
      (hF₁.of_le (natCast_le_coe_enatTop j))
  have hAF₂jet (j : ℕ) :
      iteratedDeriv j (A * F₂) 0 = fifthRootCurvatureJetProductAtZero j A F₂ :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hA.of_le (natCast_le_coe_enatTop j))
      (hF₂.of_le (natCast_le_coe_enatTop j))
  have hF₁F₁jet (j : ℕ) :
      iteratedDeriv j (F₁ * F₁) 0 = fifthRootCurvatureJetProductAtZero j F₁ F₁ :=
    iteratedDeriv_mul_zero_eq_fifthRootCurvatureJetProductAtZero (hF₁.of_le (natCast_le_coe_enatTop j))
      (hF₁.of_le (natCast_le_coe_enatTop j))
  have hIjet (j : ℕ) : iteratedDeriv j I 0 =
      -5 * fifthRootCurvatureJetProductAtZero j A F₂ - 4 * fifthRootCurvatureJetProductAtZero j F₁ F₁ := by
    have hAF₂j : ContDiffAt ℝ j (A * F₂) 0 :=
      hAF₂.contDiffAt.of_le (natCast_le_coe_enatTop j)
    have hF₁F₁j : ContDiffAt ℝ j (F₁ * F₁) 0 :=
      hF₁F₁.contDiffAt.of_le (natCast_le_coe_enatTop j)
    have hleft : ContDiffAt ℝ j (fun t => -5 * (A * F₂) t) 0 := by
      fun_prop
    have hright : ContDiffAt ℝ j (fun t => 4 * (F₁ * F₁) t) 0 := by
      fun_prop
    dsimp only [I]
    change iteratedDeriv j
      ((fun t => -5 * (A * F₂) t) - fun t => 4 * (F₁ * F₁) t) 0 = _
    rw [iteratedDeriv_sub hleft hright,
      iteratedDeriv_const_mul (-5) hAF₂j,
      iteratedDeriv_const_mul 4 hF₁F₁j, hAF₂jet, hF₁F₁jet]
  have hE₁jet : iteratedDeriv n E₁ 0 = 24 * fifthRootCurvatureJetProductAtZero n A A := by
    dsimp only [E₁]
    rw [iteratedDeriv_const_mul 24
      (hAA.contDiffAt.of_le (natCast_le_coe_enatTop n)), hAAjet]
  have hdiffAF₁ (j : ℕ) : Differentiable ℝ (iteratedDeriv j (A * F₁)) :=
    hAF₁.differentiable_iteratedDeriv j (natCast_lt_coe_enatTop j)
  have hE₂jet : iteratedDeriv n E₂ 0 =
      9 * (n : ℝ) * fifthRootCurvatureJetProductAtZero (n - 1) A F₁ := by
    cases n with
    | zero => simp [E₂]
    | succ k =>
        dsimp only [E₂]
        have hcoord := congrFun
          (iteratedDeriv_id_mul_cusp (A * F₁) hdiffAF₁ k) 0
        rw [hAF₁jet k] at hcoord
        have hcoordCont : ContDiff ℝ (↑(⊤ : ℕ∞))
            (fun t => t * (A * F₁) t) := by
          change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => t * (A t * F₁ t))
          fun_prop
        rw [iteratedDeriv_const_mul 9
          (hcoordCont.contDiffAt.of_le (natCast_le_coe_enatTop (k + 1))), hcoord]
        simp
        ring
  have hdiffI (j : ℕ) : Differentiable ℝ (iteratedDeriv j I) :=
    hI.differentiable_iteratedDeriv j (natCast_lt_coe_enatTop j)
  have hcoordI : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => t * I t) := by
    fun_prop
  have hdiffCoordI (j : ℕ) :
      Differentiable ℝ (iteratedDeriv j (fun t => t * I t)) :=
    hcoordI.differentiable_iteratedDeriv j (natCast_lt_coe_enatTop j)
  have hE₃jet : iteratedDeriv n E₃ 0 =
      (n : ℝ) * (n - 1 : ℕ) *
        (-5 * fifthRootCurvatureJetProductAtZero (n - 2) A F₂ -
          4 * fifthRootCurvatureJetProductAtZero (n - 2) F₁ F₁) := by
    cases n with
    | zero => simp [E₃]
    | succ k =>
        cases k with
        | zero =>
            dsimp only [E₃]
            have houter := congrFun
              (iteratedDeriv_id_mul_cusp (fun t => t * I t) hdiffCoordI 0) 0
            norm_num at houter ⊢
            exact houter
        | succ k =>
            dsimp only [E₃]
            have hinner := congrFun (iteratedDeriv_id_mul_cusp I hdiffI k) 0
            have houter := congrFun
              (iteratedDeriv_id_mul_cusp (fun t => t * I t) hdiffCoordI (k + 1)) 0
            norm_num at hinner houter ⊢
            rw [houter, hinner, hIjet]
            push_cast
            ring
  rw [show fifthRootDividedDropCurvatureNumerator f = E₁ + E₂ + E₃ by
    funext t
    simp only [fifthRootDividedDropCurvatureNumerator, A, F₁, F₂, E₁, E₂, I, E₃,
      Pi.add_apply, Pi.mul_apply]
    ring]
  calc
    iteratedDeriv n (E₁ + E₂ + E₃) 0 =
        iteratedDeriv n (E₁ + E₂) 0 + iteratedDeriv n E₃ 0 := by
      exact iteratedDeriv_add
        ((hE₁.add hE₂).contDiffAt.of_le (natCast_le_coe_enatTop n))
        (hE₃.contDiffAt.of_le (natCast_le_coe_enatTop n))
    _ = (iteratedDeriv n E₁ 0 + iteratedDeriv n E₂ 0) +
        iteratedDeriv n E₃ 0 := by
      rw [iteratedDeriv_add
        (hE₁.contDiffAt.of_le (natCast_le_coe_enatTop n))
        (hE₂.contDiffAt.of_le (natCast_le_coe_enatTop n))]
    _ = 0 := by
      rw [hE₁jet, hE₂jet, hE₃jet]
      rcases hnCases with rfl | rfl | rfl | rfl
      all_goals
        norm_num [fifthRootCurvatureJetProductAtZero, Finset.sum_range_succ, Nat.choose,
          hAjet, hF₁jet, hF₂jet, hodd]
      all_goals ring

/-- A strict second--sixth Hankel margin opens positive fifth-root curvature to the right. -/
theorem exists_fifthRootDividedDropCurvatureNumerator_pos_right
    {f : ℝ → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (heven : Function.Even f)
    (hHankel : 0 < iteratedDeriv 2 f 0 * iteratedDeriv 6 f 0 -
      iteratedDeriv 4 f 0 ^ 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < fifthRootDividedDropCurvatureNumerator f t := by
  let W := fifthRootDividedDropCurvatureNumerator f
  have hWtop : ContDiff ℝ (↑(⊤ : ℕ∞)) W := by
    dsimp only [W]
    unfold fifthRootDividedDropCurvatureNumerator
    have hF₁ := contDiff_top_iteratedDeriv hf 1
    have hF₂ := contDiff_top_iteratedDeriv hf 2
    fun_prop
  have hW : ContDiff ℝ 8 W := hWtop.of_le (natCast_le_coe_enatTop 8)
  have hchain : ∀ n : ℕ, n < 8 → ∀ x : ℝ,
      HasDerivAt (iteratedDeriv n W) (iteratedDeriv (n + 1) W x) x := by
    intro n hn x
    have hd := hW.differentiable_iteratedDeriv n (by exact_mod_cast hn)
    simpa only [iteratedDeriv_succ] using (hd x).hasDerivAt
  have hzero : ∀ n : ℕ, n < 8 → iteratedDeriv n W 0 = 0 := by
    intro n hn
    exact iteratedDeriv_fifthRootDividedDropCurvatureNumerator_zero_of_lt_eight
      hf heven hn
  have height : 0 < iteratedDeriv 8 W 0 := by
    rw [iteratedDeriv_eight_fifthRootDividedDropCurvatureNumerator_zero hf heven]
    positivity
  have hW8cont : Continuous (iteratedDeriv 8 W) :=
    hW.continuous_iteratedDeriv 8 (by norm_num)
  rcases exists_pos_right_of_secondJet_pos
      (hchain 6 (by norm_num)) (hchain 7 (by norm_num)) hW8cont
      (hzero 6 (by norm_num)) (hzero 7 (by norm_num)) height with
    ⟨delta, hdelta, hW6pos⟩
  have hW4pos : ∀ t : ℝ, 0 < t → t < delta →
      0 < iteratedDeriv 4 W t := by
    intro t ht htδ
    apply pos_right_of_secondJet_posOn
      (hchain 4 (by norm_num)) (hchain 5 (by norm_num))
      (hzero 4 (by norm_num)) (hzero 5 (by norm_num)) hdelta
    intro s hs
    have hs' : 0 < s ∧ s < delta := by
      simpa [interior_Icc, hdelta.ne'] using hs
    exact hW6pos s hs'.1 hs'.2
    · exact ht
    · exact htδ
  have hW2pos : ∀ t : ℝ, 0 < t → t < delta →
      0 < iteratedDeriv 2 W t := by
    intro t ht htδ
    apply pos_right_of_secondJet_posOn
      (hchain 2 (by norm_num)) (hchain 3 (by norm_num))
      (hzero 2 (by norm_num)) (hzero 3 (by norm_num)) hdelta
    intro s hs
    have hs' : 0 < s ∧ s < delta := by
      simpa [interior_Icc, hdelta.ne'] using hs
    exact hW4pos s hs'.1 hs'.2
    · exact ht
    · exact htδ
  refine ⟨delta, hdelta, ?_⟩
  intro t ht htδ
  apply pos_right_of_secondJet_posOn
    (hchain 0 (by norm_num)) (hchain 1 (by norm_num))
    (hzero 0 (by norm_num)) (hzero 1 (by norm_num)) hdelta
  intro s hs
  have hs' : 0 < s ∧ s < delta := by
    simpa [interior_Icc, hdelta.ne'] using hs
  exact hW2pos s hs'.1 hs'.2
  · exact ht
  · exact htδ

end

end HilbertMetric
