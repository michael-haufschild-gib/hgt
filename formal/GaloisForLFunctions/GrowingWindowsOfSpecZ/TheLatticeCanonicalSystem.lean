import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The lattice canonical system

Let `κ : ℤ → ℝ` be even. The **Toeplitz form** of size `n` is `T_n(x) = Σ_{i,j<n} κ(i − j)x_ix_j`: the
Gram form of `n` consecutive translates of one vector under an isometry, e.g. the translates of a
bump by a step `h` under Weil's form (`TheSchurParametersOfSpecZ`). The lattice window of size `n + 1`
is the window of size `n` with one new site `0` in front; the new site is the collar of the stage.

* **Predictor and prediction error.** A predictor of size `n` solves the normal equations
  `Σ_k κ(j − k)a_k = −κ(j + 1)` (`IsPredictor`); then `e_0 + Σ a_ke_{k+1}` is orthogonal to the old
  window, and its energy `E = κ(0) + Σ κ(k + 1)a_k` (`predErr`) is the margin of the new site.
* **One-collar decomposition** (`toeplitzForm_cons`): `T_{n+1}(x₀, x) = E·x₀² + T_n(x − x₀a)`.
* **Levinson recursion** (`levinson`). Starting from `E_0 = κ(0)`, the Schur parameter
  `β_n = κ(n + 1) + Σ_k κ(k + 1)a_{n−1−k}` and `E_{n+1} = E_n − β_n²/E_n`,
  `a' = (a − γJa, −γ)`, `γ = β_n/E_n`, produce the predictors of every size
  (`levinson_isPredictor`) as long as the margins do not vanish.
* **Positivity is the evolution** (`toeplitzForm_posDef_iff`): `T_{n+1}` is positive definite iff
  `E_0, …, E_n > 0`. Equivalently (`posDef_succ_iff_abs_schur_lt`) each new site is admitted iff
  `|β_n| < E_n`: the **prediction interval**. The newest datum enters linearly with coefficient one,
  `β_n = κ(n + 1) − π_n` (`schurParam_eq`), where the frozen prediction `π_n` and the margin `E_n`
  read only `κ(0), …, κ(n)` (`levinson_congr`). A kick that moves `κ(n + 1)` moves `β_n` by the same
  amount and nothing else.
* **Margins are products** (`levinsonErr_eq_prod`): `E_n = κ(0)∏_{k<n}(1 − γ_k²)`.
* **Degeneration** (`toeplitzForm_kernel_of_first_critical`): if `E_0, …, E_n > 0` and `E_{n+1} = 0`,
  then `T_{n+2}` is nonnegative, its kernel is the line through the Levinson vector `(1, a')`, whose
  last coefficient is `−γ_n = ∓1`, and which is a palindrome up to the sign `−γ_n`
  (`levinson_rev_of_critical`): the zero mode at a first critical lattice length is unique, has a
  definite reflection parity, and is nonzero at both ends.
-/

noncomputable section

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open Finset

variable (κ : ℤ → ℝ)

/-! ### Toeplitz forms, predictors, prediction errors -/

/-- The **Toeplitz form** of size `n`: `T_n(x) = Σ_{i,j<n} κ(i − j)x_ix_j`. -/
def toeplitzForm (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * x i * x j

/-- A **predictor** of size `n`: the normal equations `Σ_k κ(j − k)a_k = −κ(j + 1)`, i.e. the vector
`e_0 + Σ_k a_ke_{k+1}` is `T`-orthogonal to the sites `1, …, n`. -/
def IsPredictor (n : ℕ) (a : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, ∑ k : Fin n, κ ((j : ℤ) - k) * a k = -κ ((j : ℤ) + 1)

/-- The **prediction error** `E = κ(0) + Σ_k κ(k + 1)a_k`, the energy of `e_0 + Σ a_ke_{k+1}`. -/
def predErr (n : ℕ) (a : Fin n → ℝ) : ℝ := κ 0 + ∑ k : Fin n, κ ((k : ℤ) + 1) * a k

/-- The **Schur parameter** `β = κ(n + 1) + Σ_k κ(k + 1)a_{n−1−k}`: the coupling of the two corners
of the lattice window of size `n + 2` after both are made orthogonal to the interior. -/
def schurCoupling (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  κ ((n : ℤ) + 1) + ∑ k : Fin n, κ ((k : ℤ) + 1) * a (Fin.rev k)

/-- The **frozen prediction** `π = −Σ_k κ(k + 1)a_{n−1−k}` of the newest datum `κ(n + 1)`. -/
def frozenPrediction (n : ℕ) (a : Fin n → ℝ) : ℝ := -∑ k : Fin n, κ ((k : ℤ) + 1) * a (Fin.rev k)

theorem schurCoupling_eq (n : ℕ) (a : Fin n → ℝ) :
    schurCoupling κ n a = κ ((n : ℤ) + 1) - frozenPrediction κ n a := by
  simp only [schurCoupling, frozenPrediction]; ring

variable {κ}

/-- `κ` is even. -/
def IsEvenSeq (κ : ℤ → ℝ) : Prop := ∀ d, κ (-d) = κ d

/-! ### Sum bookkeeping -/

/-- Expansion of `T_n(x − x₀a)`. -/
theorem toeplitzForm_sub_smul (n : ℕ) (x a : Fin n → ℝ) (x₀ : ℝ) :
    toeplitzForm κ n (fun k => x k - x₀ * a k) =
      toeplitzForm κ n x - x₀ * ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * a i * x j -
        x₀ * ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * x i * a j +
          x₀ ^ 2 * ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * a i * a j := by
  simp only [toeplitzForm, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- With a predictor, `Σ_{i,j} κ(i − j)a_iy_j = −Σ_j κ(j + 1)y_j`. -/
theorem sum_pred_left (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a)
    (y : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * a i * y j = -∑ j : Fin n, κ ((j : ℤ) + 1) * y j := by
  rw [sum_comm, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := ha j
  calc ∑ i : Fin n, κ ((i : ℤ) - j) * a i * y j
      = (∑ i : Fin n, κ ((j : ℤ) - i) * a i) * y j := by
        rw [sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [← hκ, neg_sub]
    _ = -(κ ((j : ℤ) + 1) * y j) := by rw [h]; ring

/-- With a predictor, `Σ_{i,j} κ(i − j)y_ia_j = −Σ_i κ(i + 1)y_i`. -/
theorem sum_pred_right {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a) (y : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, κ ((i : ℤ) - j) * y i * a j = -∑ i : Fin n, κ ((i : ℤ) + 1) * y i := by
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  have h := ha i
  calc ∑ j : Fin n, κ ((i : ℤ) - j) * y i * a j
      = y i * ∑ j : Fin n, κ ((i : ℤ) - j) * a j := by
        rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
    _ = -(κ ((i : ℤ) + 1) * y i) := by rw [h]; ring

/-- The Toeplitz form of size `n + 1` with a new site in front. -/
theorem toeplitzForm_cons_expand (hκ : IsEvenSeq κ) (n : ℕ) (x₀ : ℝ) (x : Fin n → ℝ) :
    toeplitzForm κ (n + 1) (Fin.cons x₀ x) =
      κ 0 * x₀ ^ 2 + 2 * x₀ * ∑ j : Fin n, κ ((j : ℤ) + 1) * x j + toeplitzForm κ n x := by
  simp only [toeplitzForm, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Nat.cast_zero, Nat.cast_add, Nat.cast_one, sum_add_distrib]
  have e1 : ∀ j : Fin n, κ (0 - ((j : ℤ) + 1)) = κ ((j : ℤ) + 1) := fun j => by
    rw [zero_sub, hκ]
  have e2 : ∀ i j : Fin n, κ ((i : ℤ) + 1 - ((j : ℤ) + 1)) = κ ((i : ℤ) - j) := fun i j => by
    congr 1; ring
  simp only [e1, e2, sub_zero, sub_self]
  rw [show ∑ i : Fin n, κ ((i : ℤ) + 1) * x i * x₀ = x₀ * ∑ j : Fin n, κ ((j : ℤ) + 1) * x j by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring,
    show ∑ j : Fin n, κ ((j : ℤ) + 1) * x₀ * x j = x₀ * ∑ j : Fin n, κ ((j : ℤ) + 1) * x j by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by ring]
  ring

/-- A new site with zero amplitude adds nothing: `T_{n+1}(0, x) = T_n(x)`. -/
theorem toeplitzForm_cons_zero (hκ : IsEvenSeq κ) (n : ℕ) (x : Fin n → ℝ) :
    toeplitzForm κ (n + 1) (Fin.cons 0 x) = toeplitzForm κ n x := by
  rw [toeplitzForm_cons_expand hκ]; ring

/-! ### The one-collar decomposition -/

/-- **One-collar decomposition.** For a predictor `a` of size `n`,
`T_{n+1}(x₀, x) = E·x₀² + T_n(x − x₀a)`: the new site contributes its prediction error, the rest
is the old window evaluated on the residual. -/
theorem toeplitzForm_cons (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a)
    (x₀ : ℝ) (x : Fin n → ℝ) :
    toeplitzForm κ (n + 1) (Fin.cons x₀ x) =
      predErr κ n a * x₀ ^ 2 + toeplitzForm κ n (fun k => x k - x₀ * a k) := by
  rw [toeplitzForm_cons_expand hκ, toeplitzForm_sub_smul, sum_pred_left hκ ha,
    sum_pred_right ha, sum_pred_left hκ ha, predErr]
  ring

/-! ### The Levinson recursion -/

/-- The **Levinson recursion**: margin `E_n` and predictor `a^{(n)}` of every size, from
`E_0 = κ(0)` by `E_{n+1} = E_n − β_n²/E_n`, `a^{(n+1)} = (a − γJa, −γ)`, `γ = β_n/E_n`. -/
def levinson (κ : ℤ → ℝ) : (n : ℕ) → ℝ × (Fin n → ℝ)
  | 0 => (κ 0, Fin.elim0)
  | n + 1 =>
    let E := (levinson κ n).1
    let a := (levinson κ n).2
    let γ := schurCoupling κ n a / E
    (E - schurCoupling κ n a ^ 2 / E, Fin.snoc (fun k => a k - γ * a (Fin.rev k)) (-γ))

/-- The margin `E_n` of the lattice window of size `n + 1`. -/
def levinsonErr (κ : ℤ → ℝ) (n : ℕ) : ℝ := (levinson κ n).1

/-- The predictor `a^{(n)}` of size `n`. -/
def levinsonPred (κ : ℤ → ℝ) (n : ℕ) : Fin n → ℝ := (levinson κ n).2

/-- The Schur parameter `β_n`. -/
def schurParam (κ : ℤ → ℝ) (n : ℕ) : ℝ := schurCoupling κ n (levinsonPred κ n)

/-- The normalized Schur parameter (reflection coefficient) `γ_n = β_n/E_n`. -/
def reflCoeff (κ : ℤ → ℝ) (n : ℕ) : ℝ := schurParam κ n / levinsonErr κ n

theorem levinsonErr_zero : levinsonErr κ 0 = κ 0 := rfl

theorem levinsonErr_succ (n : ℕ) :
    levinsonErr κ (n + 1) = levinsonErr κ n - schurParam κ n ^ 2 / levinsonErr κ n := rfl

theorem levinsonPred_succ (n : ℕ) :
    levinsonPred κ (n + 1) = Fin.snoc (fun k => levinsonPred κ n k -
      reflCoeff κ n * levinsonPred κ n (Fin.rev k)) (-reflCoeff κ n) := rfl

/-- The reversed predictor solves the reversed normal equations:
`Σ_k κ(j − k)a_{n−1−k} = −κ(n − j)`. -/
theorem sum_rev_pred (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a)
    (j : Fin n) : ∑ k : Fin n, κ ((j : ℤ) - k) * a (Fin.rev k) = -κ ((n : ℤ) - j) := by
  have h := ha (Fin.rev j)
  rw [← Equiv.sum_comp Fin.revPerm] at h
  simp only [Fin.revPerm_apply, Fin.val_rev] at h
  have hj : (j : ℕ) < n := j.isLt
  have e : ∀ k : Fin n, κ (((n - (j + 1) : ℕ) : ℤ) - ((n - (k + 1) : ℕ) : ℤ)) =
      κ ((j : ℤ) - k) := fun k => by
    have hk : (k : ℕ) < n := k.isLt
    rw [← hκ]; congr 1; push_cast [Nat.cast_sub (by omega : j + 1 ≤ n),
      Nat.cast_sub (by omega : k + 1 ≤ n)]; ring
  simp only [e] at h
  rw [h]
  congr 2
  push_cast [Nat.cast_sub (by omega : j + 1 ≤ n)]
  ring

/-- `Σ_k κ(k + 1)a_{n−1−k} = Σ_k κ(n − k)a_k`. -/
theorem sum_rev_eq {n : ℕ} (a : Fin n → ℝ) :
    ∑ k : Fin n, κ ((k : ℤ) + 1) * a (Fin.rev k) = ∑ k : Fin n, κ ((n : ℤ) - k) * a k := by
  rw [← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun k _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hk : (k : ℕ) < n := k.isLt
  congr 2
  push_cast [Nat.cast_sub (by omega : k + 1 ≤ n)]
  ring

/-- **The Levinson step.** If `a` is a predictor of size `n` with margin `E ≠ 0`, then
`(a − γJa, −γ)`, `γ = β/E`, is a predictor of size `n + 1`, and its margin is `E − β²/E`. -/
theorem isPredictor_snoc (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a)
    (hE : predErr κ n a ≠ 0) :
    IsPredictor κ (n + 1) (Fin.snoc (fun k => a k - schurCoupling κ n a / predErr κ n a *
      a (Fin.rev k)) (-(schurCoupling κ n a / predErr κ n a))) := by
  set E := predErr κ n a with hEdef
  set β := schurCoupling κ n a with hβdef
  have hsplit : ∀ c : Fin n → ℝ, ∑ k : Fin n, c k * (a k - β / E * a (Fin.rev k)) =
      ∑ k : Fin n, c k * a k - β / E * ∑ k : Fin n, c k * a (Fin.rev k) := fun c => by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun k _ => by ring
  intro j
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · -- the new row `j = n`
    simp only [Fin.val_last, sub_self]
    rw [hsplit (fun k => κ ((n : ℤ) - k)), ← sum_rev_eq a]
    have hβ : ∑ k : Fin n, κ ((k : ℤ) + 1) * a (Fin.rev k) = β - κ ((n : ℤ) + 1) := by
      rw [hβdef, schurCoupling]; ring
    have hE' : ∑ k : Fin n, κ ((n : ℤ) - k) * a (Fin.rev k) = E - κ 0 := by
      rw [show ∑ k : Fin n, κ ((n : ℤ) - k) * a (Fin.rev k) =
          ∑ k : Fin n, κ ((k : ℤ) + 1) * a k by
        rw [← Equiv.sum_comp Fin.revPerm]
        refine sum_congr rfl fun k _ => ?_
        simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
        have hk : (k : ℕ) < n := k.isLt
        congr 2
        push_cast [Nat.cast_sub (by omega : k + 1 ≤ n)]
        ring]
      rw [hEdef, predErr]; ring
    rw [hβ, hE']
    field_simp
    ring
  · -- an old row `j < n`
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [hsplit (fun k => κ ((j : ℤ) - k)), ha j, sum_rev_pred hκ ha j]
    have : κ ((j : ℤ) - n) = κ ((n : ℤ) - j) := by rw [← hκ]; congr 1; ring
    rw [this]
    ring

/-- The margin after a Levinson step: `E' = E − β²/E`. -/
theorem predErr_snoc (hκ : IsEvenSeq κ) {n : ℕ} (a : Fin n → ℝ) :
    predErr κ (n + 1) (Fin.snoc (fun k => a k - schurCoupling κ n a / predErr κ n a *
      a (Fin.rev k)) (-(schurCoupling κ n a / predErr κ n a))) =
      predErr κ n a - schurCoupling κ n a ^ 2 / predErr κ n a := by
  have _ := hκ
  set E := predErr κ n a with hEdef
  set β := schurCoupling κ n a with hβdef
  have hs : ∑ k : Fin (n + 1), κ ((k : ℤ) + 1) *
      (Fin.snoc (fun k : Fin n => a k - β / E * a (Fin.rev k)) (-(β / E)) : Fin (n + 1) → ℝ) k =
      ∑ k : Fin n, κ ((k : ℤ) + 1) * a k -
        β / E * (κ ((n : ℤ) + 1) + ∑ k : Fin n, κ ((k : ℤ) + 1) * a (Fin.rev k)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
    have : ∑ k : Fin n, κ ((k : ℤ) + 1) * (a k - β / E * a (Fin.rev k)) =
        ∑ k : Fin n, κ ((k : ℤ) + 1) * a k -
          β / E * ∑ k : Fin n, κ ((k : ℤ) + 1) * a (Fin.rev k) := by
      rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun k _ => by ring
    rw [this]
    ring
  rw [predErr, hs]
  have h1 : E = κ 0 + ∑ k : Fin n, κ ((k : ℤ) + 1) * a k := hEdef
  have h2 : β = κ ((n : ℤ) + 1) + ∑ k : Fin n, κ ((k : ℤ) + 1) * a (Fin.rev k) := hβdef
  rw [← h2, h1]
  ring

/-- **The Levinson predictors are predictors** as long as the earlier margins do not vanish, and
`E_n` is their prediction error. -/
theorem levinson_spec (hκ : IsEvenSeq κ) :
    ∀ n : ℕ, (∀ k < n, levinsonErr κ k ≠ 0) →
      IsPredictor κ n (levinsonPred κ n) ∧ predErr κ n (levinsonPred κ n) = levinsonErr κ n
  | 0, _ => ⟨fun j => j.elim0, by simp [predErr, levinsonErr, levinson]⟩
  | n + 1, h => by
    obtain ⟨hp, he⟩ := levinson_spec hκ n fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hne : predErr κ n (levinsonPred κ n) ≠ 0 := he ▸ h n (Nat.lt_succ_self n)
    have hstep := isPredictor_snoc hκ hp hne
    have herr := predErr_snoc hκ (levinsonPred κ n)
    rw [he] at hstep herr
    exact ⟨hstep, herr⟩

theorem levinson_isPredictor (hκ : IsEvenSeq κ) {n : ℕ} (h : ∀ k < n, levinsonErr κ k ≠ 0) :
    IsPredictor κ n (levinsonPred κ n) := (levinson_spec hκ n h).1

theorem predErr_levinson (hκ : IsEvenSeq κ) {n : ℕ} (h : ∀ k < n, levinsonErr κ k ≠ 0) :
    predErr κ n (levinsonPred κ n) = levinsonErr κ n := (levinson_spec hκ n h).2

/-! ### Positivity is the evolution -/

/-- Positive definiteness of the Toeplitz form of size `n`. -/
def ToeplitzPosDef (κ : ℤ → ℝ) (n : ℕ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → 0 < toeplitzForm κ n x

/-- **The stage step on the lattice.** If the window of size `n` is positive definite and has a
predictor `a`, the window of size `n + 1` is positive definite iff the margin of the new site is
positive. -/
theorem posDef_succ_iff (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a) :
    ToeplitzPosDef κ (n + 1) ↔ ToeplitzPosDef κ n ∧ 0 < predErr κ n a := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, ?_⟩
    · have hne : (Fin.cons 0 x : Fin (n + 1) → ℝ) ≠ 0 := fun h0 =>
        hx (funext fun k => by simpa using congrFun h0 k.succ)
      have := h _ hne
      rwa [toeplitzForm_cons_zero hκ] at this
    · have hne : (Fin.cons 1 a : Fin (n + 1) → ℝ) ≠ 0 := fun h0 => by
        simpa using congrFun h0 0
      have := h _ hne
      rw [toeplitzForm_cons hκ ha] at this
      simp only [one_mul, sub_self, one_pow, mul_one] at this
      have hz : toeplitzForm κ n (fun _ => 0) = 0 := by simp [toeplitzForm]
      linarith
  · rintro ⟨h, hE⟩ y hy
    rw [← Fin.cons_self_tail y, toeplitzForm_cons hκ ha]
    by_cases h0 : y 0 = 0
    · have hres : (fun k => Fin.tail y k - y 0 * a k) ≠ 0 := by
        intro hc
        apply hy
        funext k
        refine Fin.cases h0 (fun k => ?_) k
        have := congrFun hc k
        simpa [h0, Fin.tail] using this
      have := h _ hres
      positivity
    · have h1 : 0 < predErr κ n a * y 0 ^ 2 := mul_pos hE (by positivity)
      have h2 : 0 ≤ toeplitzForm κ n (fun k => Fin.tail y k - y 0 * a k) := by
        by_cases hr : (fun k => Fin.tail y k - y 0 * a k) = 0
        · rw [hr]; simp [toeplitzForm]
        · exact (h _ hr).le
      linarith

/-- **Positivity is the Levinson evolution.** The lattice window of size `n + 1` is positive
definite iff the margins `E_0, …, E_n` are all positive. -/
theorem toeplitzForm_posDef_iff (hκ : IsEvenSeq κ) :
    ∀ n : ℕ, ToeplitzPosDef κ (n + 1) ↔ ∀ k ≤ n, 0 < levinsonErr κ k
  | 0 => by
    rw [posDef_succ_iff hκ (levinson_isPredictor hκ (n := 0) fun k hk => absurd hk (by omega)),
      predErr_levinson hκ (n := 0) fun k hk => absurd hk (by omega)]
    constructor
    · rintro ⟨_, h⟩ k hk
      rwa [Nat.le_zero.mp hk]
    · intro h
      exact ⟨fun x hx => absurd (funext fun k => k.elim0) hx, h 0 le_rfl⟩
  | n + 1 => by
    have ih := toeplitzForm_posDef_iff hκ n
    constructor
    · intro h
      have hn : ToeplitzPosDef κ (n + 1) := by
        intro x hx
        have hne : (Fin.cons 0 x : Fin (n + 2) → ℝ) ≠ 0 := fun h0 =>
          hx (funext fun k => by simpa using congrFun h0 k.succ)
        have := h _ hne
        rwa [toeplitzForm_cons_zero hκ] at this
      have hlow := ih.mp hn
      have hne : ∀ k < n + 1, levinsonErr κ k ≠ 0 := fun k hk => (hlow k (by omega)).ne'
      have hp := levinson_isPredictor hκ hne
      have hE := ((posDef_succ_iff hκ hp).mp h).2
      rw [predErr_levinson hκ hne] at hE
      intro k hk
      rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
      · exact hlow k (by omega)
      · rwa [show k = n + 1 by omega]
    · intro h
      have hlow : ∀ k ≤ n, 0 < levinsonErr κ k := fun k hk => h k (by omega)
      have hne : ∀ k < n + 1, levinsonErr κ k ≠ 0 := fun k hk => (hlow k (by omega)).ne'
      have hp := levinson_isPredictor hκ hne
      rw [posDef_succ_iff hκ hp, predErr_levinson hκ hne]
      exact ⟨ih.mpr hlow, h (n + 1) le_rfl⟩

/-- **The prediction interval.** If the lattice window of size `n + 1` is positive definite, the
window of size `n + 2` is positive definite iff `|β_n| < E_n`, i.e. iff the newest datum lies in
`(π_n − E_n, π_n + E_n)`. -/
theorem posDef_succ_iff_abs_schur_lt (hκ : IsEvenSeq κ) {n : ℕ} (h : ToeplitzPosDef κ (n + 1)) :
    ToeplitzPosDef κ (n + 2) ↔ |schurParam κ n| < levinsonErr κ n := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hE := hlow n le_rfl
  rw [toeplitzForm_posDef_iff hκ (n + 1)]
  constructor
  · intro h2
    have h3 := h2 (n + 1) le_rfl
    rw [levinsonErr_succ, sub_pos, div_lt_iff₀ hE, ← sq] at h3
    exact abs_lt_of_sq_lt_sq' h3 hE.le |>.2 |> fun h4 =>
      abs_lt.mpr ⟨(abs_lt_of_sq_lt_sq' h3 hE.le).1, h4⟩
  · intro h2 k hk
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · exact hlow k (by omega)
    · rw [show k = n + 1 by omega, levinsonErr_succ, sub_pos, div_lt_iff₀ hE, ← sq]
      exact sq_lt_sq' (abs_lt.mp h2).1 (abs_lt.mp h2).2

/-- **Kick law.** The newest datum `κ(n + 1)` enters the Schur parameter with coefficient one:
`β_n = κ(n + 1) − π_n`, the frozen prediction `π_n` being computed from the predictor of size `n`. -/
theorem schurParam_eq (n : ℕ) :
    schurParam κ n = κ ((n : ℤ) + 1) - frozenPrediction κ n (levinsonPred κ n) :=
  schurCoupling_eq κ n _

/-- **Causality.** The margin and predictor of size `n` read only `κ(0), …, κ(n)`. -/
theorem levinson_congr {κ' : ℤ → ℝ} :
    ∀ n : ℕ, (∀ d : ℕ, d ≤ n → κ d = κ' d) → levinson κ n = levinson κ' n
  | 0, h => by
    have h0 := h 0 le_rfl
    simp only [Nat.cast_zero] at h0
    simp only [levinson, h0]
  | n + 1, h => by
    have ih := levinson_congr n fun d hd => h d (by omega)
    have hc : schurCoupling κ n (levinson κ' n).2 = schurCoupling κ' n (levinson κ' n).2 := by
      simp only [schurCoupling]
      congr 1
      · exact_mod_cast h (n + 1) le_rfl
      · refine sum_congr rfl fun k _ => ?_
        have hk : (k : ℕ) < n := k.isLt
        congr 1
        exact_mod_cast h (k + 1) (by omega)
    simp only [levinson, hc, ih]

/-- **Margins are products**: `E_n = κ(0)∏_{k<n}(1 − γ_k²)` while the margins do not vanish. -/
theorem levinsonErr_eq_prod :
    ∀ n : ℕ, (∀ k < n, levinsonErr κ k ≠ 0) →
      levinsonErr κ n = κ 0 * ∏ k ∈ range n, (1 - reflCoeff κ k ^ 2)
  | 0, _ => by simp [levinsonErr_zero]
  | n + 1, h => by
    rw [levinsonErr_succ, prod_range_succ, ← mul_assoc,
      ← levinsonErr_eq_prod n fun k hk => h k (by omega)]
    have hE := h n (by omega)
    simp only [reflCoeff]
    field_simp

/-- One Levinson step multiplies the margin by `1 − γ_n²`. -/
theorem levinsonErr_succ_eq_mul {n : ℕ} (hE : levinsonErr κ n ≠ 0) :
    levinsonErr κ (n + 1) = levinsonErr κ n * (1 - reflCoeff κ n ^ 2) := by
  rw [levinsonErr_succ, reflCoeff]
  field_simp

/-- **Margins only decrease**: `E_{n+1} ≤ E_n` while `E_n > 0`. -/
theorem levinsonErr_succ_le {n : ℕ} (hE : 0 < levinsonErr κ n) :
    levinsonErr κ (n + 1) ≤ levinsonErr κ n := by
  rw [levinsonErr_succ]
  have : 0 ≤ schurParam κ n ^ 2 / levinsonErr κ n := div_nonneg (sq_nonneg _) hE.le
  linarith

/-- **All margins are positive iff `κ(0) > 0` and every reflection coefficient lies in `(−1, 1)`.** -/
theorem levinsonErr_pos_iff :
    (∀ n, 0 < levinsonErr κ n) ↔ 0 < κ 0 ∧ ∀ n, |reflCoeff κ n| < 1 := by
  constructor
  · intro h
    refine ⟨h 0, fun n => ?_⟩
    have h1 := h (n + 1)
    rw [levinsonErr_succ_eq_mul (h n).ne'] at h1
    have h2 : 0 < 1 - reflCoeff κ n ^ 2 := (pos_iff_pos_of_mul_pos h1).mp (h n)
    rw [← sq_lt_one_iff_abs_lt_one]
    linarith
  · rintro ⟨h0, hγ⟩ n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [levinsonErr_succ_eq_mul ih.ne']
      have := (sq_lt_one_iff_abs_lt_one _).mpr (hγ n)
      exact mul_pos ih (by linarith)

/-! ### The two-collar form of a lattice stage -/

/-- **Reflection symmetry** of the Toeplitz form: `T_n(x ∘ rev) = T_n(x)`. -/
theorem toeplitzForm_comp_rev (hκ : IsEvenSeq κ) (n : ℕ) (x : Fin n → ℝ) :
    toeplitzForm κ n (fun k => x (Fin.rev k)) = toeplitzForm κ n x := by
  simp only [toeplitzForm]
  rw [← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun j _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  rw [← hκ]
  congr 2
  push_cast [Nat.cast_sub (by omega : i + 1 ≤ n), Nat.cast_sub (by omega : j + 1 ≤ n)]
  ring_nf

/-- Reversing a vector with a last site moves that site to the front. -/
theorem snoc_comp_rev {n : ℕ} (x : Fin n → ℝ) (x₁ : ℝ) :
    (fun k => (Fin.snoc x x₁ : Fin (n + 1) → ℝ) (Fin.rev k)) =
      (Fin.cons x₁ (fun k => x (Fin.rev k)) : Fin (n + 1) → ℝ) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Fin.rev_zero]
  · have hr : Fin.rev k.succ = (Fin.rev k).castSucc := by
      ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
    rw [hr, Fin.snoc_castSucc, Fin.cons_succ]

/-- **Mirror one-collar decomposition**: a new site at the far end,
`T_{n+1}(x, x₁) = E·x₁² + T_n(x − x₁Ja)`. -/
theorem toeplitzForm_snoc (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ} (ha : IsPredictor κ n a)
    (x : Fin n → ℝ) (x₁ : ℝ) :
    toeplitzForm κ (n + 1) (Fin.snoc x x₁) =
      predErr κ n a * x₁ ^ 2 + toeplitzForm κ n (fun k => x k - x₁ * a (Fin.rev k)) := by
  rw [← toeplitzForm_comp_rev hκ, snoc_comp_rev, toeplitzForm_cons hκ ha,
    ← toeplitzForm_comp_rev hκ n (fun k => x k - x₁ * a (Fin.rev k))]
  simp only [Fin.rev_rev]

/-- **The two-collar decomposition of a lattice stage.** For a predictor `a` of size `n` with margin
`E ≠ 0` and Schur parameter `β`,
`T_{n+2}(x₀, x, x₁) = E x₀² + 2β x₀x₁ + E x₁² + T_n(x − x₀a − x₁Ja)`:
after the interior is projected out, the two collars carry the `2×2` form `[[E, β], [β, E]]`. -/
theorem toeplitzForm_two_collar (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ}
    (ha : IsPredictor κ n a) (hE : predErr κ n a ≠ 0) (x₀ x₁ : ℝ) (x : Fin n → ℝ) :
    toeplitzForm κ (n + 2) (Fin.cons x₀ (Fin.snoc x x₁)) =
      predErr κ n a * x₀ ^ 2 + 2 * schurCoupling κ n a * x₀ * x₁ + predErr κ n a * x₁ ^ 2 +
        toeplitzForm κ n (fun k => x k - x₀ * a k - x₁ * a (Fin.rev k)) := by
  rw [toeplitzForm_cons hκ (isPredictor_snoc hκ ha hE), predErr_snoc hκ a]
  set E := predErr κ n a
  set β := schurCoupling κ n a
  have hres : (fun k => (Fin.snoc x x₁ : Fin (n + 1) → ℝ) k - x₀ *
      (Fin.snoc (fun k => a k - β / E * a (Fin.rev k)) (-(β / E)) : Fin (n + 1) → ℝ) k) =
      Fin.snoc (fun k => x k - x₀ * (a k - β / E * a (Fin.rev k))) (x₁ + β / E * x₀) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp only [Fin.snoc_last]; ring
    · simp only [Fin.snoc_castSucc]
  rw [hres, toeplitzForm_snoc hκ ha]
  have hint : (fun k => x k - x₀ * (a k - β / E * a (Fin.rev k)) -
      (x₁ + β / E * x₀) * a (Fin.rev k)) = fun k => x k - x₀ * a k - x₁ * a (Fin.rev k) := by
    funext k; ring
  rw [hint]
  field_simp
  ring

/-- **The two-collar form of a lattice stage is `[[E, β], [β, E]]`.** If the interior window of size
`n` is nonnegative, the minimum of `T_{n+2}` over the interior with fixed collar amplitudes
`x₀, x₁` is `E x₀² + 2β x₀x₁ + E x₁²`, attained at `x = x₀a + x₁Ja`. -/
theorem twoCollar_isLeast (hκ : IsEvenSeq κ) {n : ℕ} {a : Fin n → ℝ}
    (ha : IsPredictor κ n a) (hE : predErr κ n a ≠ 0)
    (hint : ∀ z : Fin n → ℝ, 0 ≤ toeplitzForm κ n z) (x₀ x₁ : ℝ) :
    IsLeast (Set.range fun x : Fin n → ℝ => toeplitzForm κ (n + 2) (Fin.cons x₀ (Fin.snoc x x₁)))
      (predErr κ n a * x₀ ^ 2 + 2 * schurCoupling κ n a * x₀ * x₁ + predErr κ n a * x₁ ^ 2) := by
  refine ⟨⟨fun k => x₀ * a k + x₁ * a (Fin.rev k), ?_⟩, ?_⟩
  · simp only
    rw [toeplitzForm_two_collar hκ ha hE]
    have hz : toeplitzForm κ n (fun k => x₀ * a k + x₁ * a (Fin.rev k) - x₀ * a k -
        x₁ * a (Fin.rev k)) = 0 := by
      simp only [add_sub_cancel_left, sub_self]; simp [toeplitzForm]
    rw [hz, add_zero]
  · rintro _ ⟨x, rfl⟩
    simp only
    rw [toeplitzForm_two_collar hκ ha hE]
    linarith [hint (fun k => x k - x₀ * a k - x₁ * a (Fin.rev k))]

/-! ### Degeneration at a first critical length -/

/-- The **Levinson vector** `(1, a^{(n)})` of size `n + 1`. -/
def levinsonVec (κ : ℤ → ℝ) (n : ℕ) : Fin (n + 1) → ℝ := Fin.cons 1 (levinsonPred κ n)

/-- **Zero modes at a first critical lattice length.** If the window of size `n + 1` is positive
definite and the next margin vanishes, the window of size `n + 2` is nonnegative and its kernel is
the line through the Levinson vector. -/
theorem toeplitzForm_kernel_of_first_critical (hκ : IsEvenSeq κ) {n : ℕ}
    (h : ToeplitzPosDef κ (n + 1)) (h0 : levinsonErr κ (n + 1) = 0) :
    (∀ x : Fin (n + 2) → ℝ, 0 ≤ toeplitzForm κ (n + 2) x) ∧
      ∀ x : Fin (n + 2) → ℝ, toeplitzForm κ (n + 2) x = 0 ↔
        x = fun k => x 0 * levinsonVec κ (n + 1) k := by
  have hlow := (toeplitzForm_posDef_iff hκ n).mp h
  have hne : ∀ k < n + 1, levinsonErr κ k ≠ 0 := fun k hk => (hlow k (by omega)).ne'
  have hp := levinson_isPredictor hκ hne
  have hE := predErr_levinson hκ hne
  have key : ∀ x : Fin (n + 2) → ℝ, toeplitzForm κ (n + 2) x =
      toeplitzForm κ (n + 1) (fun k => Fin.tail x k - x 0 * levinsonPred κ (n + 1) k) := by
    intro x
    conv_lhs => rw [← Fin.cons_self_tail x]
    rw [toeplitzForm_cons hκ hp, hE, h0, zero_mul, zero_add]
  have hz : toeplitzForm κ (n + 1) (fun _ => 0) = 0 := by simp [toeplitzForm]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [key]
    by_cases hr : (fun k => Fin.tail x k - x 0 * levinsonPred κ (n + 1) k) = 0
    · rw [hr]; exact hz.ge
    · exact (h _ hr).le
  · rw [key]
    constructor
    · intro hq
      by_contra hc
      have hr : (fun k => Fin.tail x k - x 0 * levinsonPred κ (n + 1) k) ≠ 0 := by
        intro hr
        apply hc
        funext k
        refine Fin.cases (by simp [levinsonVec]) (fun k => ?_) k
        have := congrFun hr k
        simp only [Fin.tail, Pi.zero_apply, sub_eq_zero] at this
        simp [levinsonVec, this]
      exact (h _ hr).ne' hq
    · intro hx
      have : (fun k => Fin.tail x k - x 0 * levinsonPred κ (n + 1) k) = fun _ => 0 := by
        funext k
        rw [hx]
        simp [Fin.tail, levinsonVec]
      rw [this, hz]

/-- **The zero mode is a palindrome up to sign.** The Levinson vector of size `n + 2` built from a
reflection coefficient `γ` with `γ² = 1` satisfies `v_{n+1−k} = −γ·v_k`: at a first critical length
the zero mode has the reflection parity `−γ_n` and its two end coefficients are `1` and `−γ_n`. -/
theorem levinsonVec_rev_of_sq_eq_one {n : ℕ} (hγ : reflCoeff κ n ^ 2 = 1) (k : Fin (n + 2)) :
    levinsonVec κ (n + 1) (Fin.rev k) = -reflCoeff κ n * levinsonVec κ (n + 1) k := by
  set γ := reflCoeff κ n
  set a := levinsonPred κ n
  -- `v = (1, a − γJa, −γ)`
  have hv : ∀ k : Fin (n + 2), levinsonVec κ (n + 1) k =
      (Fin.cons (1 : ℝ) (Fin.snoc (fun j : Fin n => a j - γ * a (Fin.rev j)) (-γ) :
        Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ) k := fun k => by
    simp only [levinsonVec, levinsonPred_succ]; rfl
  refine Fin.cases ?_ (fun k => ?_) k
  · -- the left end maps to the right end
    rw [hv, hv, Fin.rev_zero, Fin.cons_zero]
    rw [show (Fin.last (n + 1) : Fin (n + 2)) = (Fin.last n).succ by rfl, Fin.cons_succ,
      Fin.snoc_last]
    ring
  · refine Fin.lastCases ?_ (fun j => ?_) k
    · rw [hv, hv, show (Fin.last n).succ = Fin.last (n + 1) from rfl, Fin.rev_last,
        Fin.cons_zero, show (Fin.last (n + 1) : Fin (n + 2)) = (Fin.last n).succ by rfl,
        Fin.cons_succ, Fin.snoc_last]
      nlinarith [hγ]
    · rw [hv, hv]
      have hr : Fin.rev (Fin.castSucc j).succ = (Fin.castSucc (Fin.rev j)).succ := by
        ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]; omega
      rw [hr, Fin.cons_succ, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.rev_rev]
      linear_combination (-a (Fin.rev j)) * hγ

/-- At a first critical length `|γ_n| = 1`. -/
theorem reflCoeff_sq_of_critical {n : ℕ} (hE : levinsonErr κ n ≠ 0)
    (h0 : levinsonErr κ (n + 1) = 0) : reflCoeff κ n ^ 2 = 1 := by
  rw [levinsonErr_succ] at h0
  simp only [reflCoeff]
  field_simp
  field_simp at h0
  linarith

end GaloisForLFunctions.GrowingWindowsOfSpecZ
