import Mathlib

/-!
# Gamma's opposite-variance jet clocks and their canonical factorial Fock polarization

On the `N`-dimensional raw-jet space `Fin N → ℂ` there are two source-defined infinitesimal
clocks:

* the **analytic derivative clock** `D_N` (`shiftOp`), the truncated jet shift
  `(D_N x)_j = x_{j+1}` with `(D_N x)_{N-1} = 0`;
* the **algebraic coordinate-multiplication clock** `A_N` (`createOp`), the Leibniz prolongation
  term `(A_N x)_j = j · x_{j-1}` with `(A_N x)_0 = 0`.

This file proves the finite polarization theory these two clocks force.

* `factorialForm_shiftOp_left` : the exact adjoint pair `⟪D_N x, y⟫_F = ⟪x, A_N y⟫_F` for the
  factorial polarization `⟪x,y⟫_{F,N} = ∑_j x_j conj(y_j)/j!`.
* `weightForm_forced_recurrence`, `weightForm_eq_div_factorial` : the factorial weights are the
  **unique** diagonal positive weights realizing that adjointness, up to one scalar: adjointness
  forces `w_j = w_0/j!`.  The metric is selected by the two source realizations themselves.
* `commutator_eq` : the canonical-commutation defect is an exact top-boundary charge,
  `[D_N, A_N] = I - N·P_top`.
* `factorialForm_boundaryCharge_eq`, `factorialForm_boundaryCharge_re_nonneg` :
  `I - [D_N, A_N] = N·P_top ≥ 0`, with the exact value `N‖x_{N-1}‖²/(N-1)!`.
* `taylorTranslate_eq_exp_series`, `shiftOp_iterate_eq_zero`,
  `taylorTranslate_coordVec_apply` : the finite Taylor translation `E_N = exp(D_N)` is the
  terminating exponential series of the nilpotent shift, with entries `1_{j≤k}/(k-j)!`.
* `factorialForm_taylorTranslate_left` : `E_N^* = exp(A_N)`.
* `factorialForm_coordMulOp_left` : `Z_N(z)^* = conj(z)·I + D_N` for `Z_N(z) = z·I + A_N`.
* `factorialForm_coordOne_self`, `factorialForm_taylorTranslate_coordOne_self` : the passivity
  no-go — `‖E_N e_1‖²_F = 2 > 1 = ‖e_1‖²_F`, so the canonical positive jet metric does **not**
  make finite Gamma translation contractive.
* `greenBoundaryExcess`, `greenBoundaryExcess_pos` : the exact Green boundary-excess identity.
  For a pure top-boundary input the translation gains precisely the positive factorial outgoing
  energy, so no positive metric retaining the orthogonal factorial split makes the raw colligation
  a contraction.

Weighted creation--annihilation adjoints, truncated canonical-commutation defects and factorial
Fock metrics are classical oscillator algebra.  Nothing here is an RH statement: the content is
that the positive metric and the positive boundary charge are *forced*, which isolates the
prime--archimedean incidence as the genuine open step.
-/


open Finset Complex

namespace GaloisForLFunctions.HTGeometry
namespace GammaFactorialFock

noncomputable section

variable {N : ℕ}

/-- Zero extension of a level-`N` raw jet to all jet orders. -/
def jetExt (x : Fin N → ℂ) : ℕ → ℂ := fun n => if h : n < N then x ⟨n, h⟩ else 0

lemma jetExt_of_lt {x : Fin N → ℂ} {n : ℕ} (h : n < N) : jetExt x n = x ⟨n, h⟩ := dif_pos h

lemma jetExt_of_le {x : Fin N → ℂ} {n : ℕ} (h : N ≤ n) : jetExt x n = 0 :=
  dif_neg (not_lt.mpr h)

@[simp] lemma jetExt_coe (x : Fin N → ℂ) (j : Fin N) : jetExt x (j : ℕ) = x j := by
  rw [jetExt_of_lt j.isLt]

/-- The analytic derivative clock `D_N`: the truncated jet shift. -/
def shiftOp (x : Fin N → ℂ) : Fin N → ℂ := fun j => jetExt x ((j : ℕ) + 1)

/-- The algebraic coordinate-multiplication clock `A_N`: the Leibniz prolongation term. -/
def createOp (x : Fin N → ℂ) : Fin N → ℂ := fun j => ((j : ℕ) : ℂ) * jetExt x ((j : ℕ) - 1)

@[simp] lemma jetExt_shiftOp (x : Fin N → ℂ) (n : ℕ) :
    jetExt (shiftOp x) n = jetExt x (n + 1) := by
  by_cases h : n < N
  · rw [jetExt_of_lt h]; rfl
  · rw [jetExt_of_le (not_lt.mp h), jetExt_of_le (by omega)]

lemma jetExt_createOp {x : Fin N → ℂ} {n : ℕ} (h : n < N) :
    jetExt (createOp x) n = (n : ℂ) * jetExt x (n - 1) := by
  rw [jetExt_of_lt h]; rfl

/-- The canonical factorial polarization `⟪x,y⟫_{F,N} = ∑_j x_j conj(y_j)/j!`. -/
def factorialForm (x y : Fin N → ℂ) : ℂ :=
  ∑ n ∈ range N, jetExt x n * (starRingEnd ℂ) (jetExt y n) / (Nat.factorial n : ℂ)

lemma factorialForm_eq_sum_fin (x y : Fin N → ℂ) :
    factorialForm x y
      = ∑ j : Fin N, x j * (starRingEnd ℂ) (y j) / (Nat.factorial (j : ℕ) : ℂ) := by
  rw [factorialForm,
    ← Fin.sum_univ_eq_sum_range
      (fun n => jetExt x n * (starRingEnd ℂ) (jetExt y n) / (Nat.factorial n : ℂ)) N]
  simp

lemma factorialForm_conj_symm (x y : Fin N → ℂ) :
    (starRingEnd ℂ) (factorialForm x y) = factorialForm y x := by
  rw [factorialForm, factorialForm, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_div₀, map_mul, Complex.conj_conj, Complex.conj_natCast]
  ring

/-- **The exact adjoint pair.**  `⟪D_N x, y⟫_F = ⟪x, A_N y⟫_F`. -/
theorem factorialForm_shiftOp_left (x y : Fin N → ℂ) :
    factorialForm (shiftOp x) y = factorialForm x (createOp y) := by
  cases N with
  | zero => simp [factorialForm]
  | succ M =>
    have hL : factorialForm (shiftOp x) y
        = ∑ n ∈ range M,
            jetExt x (n + 1) * (starRingEnd ℂ) (jetExt y n) / (Nat.factorial n : ℂ) := by
      rw [factorialForm]
      simp only [jetExt_shiftOp]
      rw [Finset.sum_range_succ, jetExt_of_le (le_refl (M + 1))]
      simp
    have hR : factorialForm x (createOp y)
        = ∑ n ∈ range M,
            jetExt x (n + 1) * (starRingEnd ℂ) (jetExt y n) / (Nat.factorial n : ℂ) := by
      rw [factorialForm]
      have hstep : ∀ n ∈ range (M + 1),
          jetExt x n * (starRingEnd ℂ) (jetExt (createOp y) n) / (Nat.factorial n : ℂ)
            = jetExt x n * ((n : ℂ) * (starRingEnd ℂ) (jetExt y (n - 1)))
                / (Nat.factorial n : ℂ) := by
        intro n hn
        rw [jetExt_createOp (Finset.mem_range.mp hn), map_mul, Complex.conj_natCast]
      rw [Finset.sum_congr rfl hstep, Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero, Nat.add_sub_cancel]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hfac : (Nat.factorial (n + 1) : ℂ) = ((n : ℂ) + 1) * (Nat.factorial n : ℂ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hne : ((n : ℂ) + 1) ≠ 0 := by
        have h0 : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [h0]; exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      have hfne : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      rw [hfac]
      field_simp
      push_cast
      ring
    rw [hL, hR]

/-- The conjugate form of the adjoint pair: `⟪A_N x, y⟫_F = ⟪x, D_N y⟫_F`. -/
theorem factorialForm_createOp_left (x y : Fin N → ℂ) :
    factorialForm (createOp x) y = factorialForm x (shiftOp y) := by
  have h := congrArg (starRingEnd ℂ) (factorialForm_shiftOp_left y x)
  rw [factorialForm_conj_symm, factorialForm_conj_symm] at h
  exact h.symm

/-! ### Uniqueness of the diagonal polarization -/

/-- A general diagonal sesquilinear weight form on the level-`N` jet space. -/
def weightForm (w : ℕ → ℂ) (x y : Fin N → ℂ) : ℂ :=
  ∑ n ∈ range N, jetExt x n * (starRingEnd ℂ) (jetExt y n) * w n

/-- The standard jet coordinate vector `e_k`. -/
def coordVec (k : ℕ) : Fin N → ℂ := fun j => if (j : ℕ) = k then 1 else 0

lemma jetExt_coordVec {k : ℕ} (hk : k < N) (n : ℕ) :
    jetExt (coordVec (N := N) k) n = if n = k then 1 else 0 := by
  by_cases h : n < N
  · rw [jetExt_of_lt h]; rfl
  · rw [jetExt_of_le (not_lt.mp h), if_neg (by omega)]

lemma weightForm_shiftOp_coord {w : ℕ → ℂ} {k : ℕ} (hk : k + 1 < N) :
    weightForm w (shiftOp (coordVec (N := N) (k + 1))) (coordVec (N := N) k) = w k := by
  have hkN : k < N := by omega
  rw [weightForm]
  rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hkN)]
  · simp only [jetExt_shiftOp, jetExt_coordVec hk, jetExt_coordVec hkN]
    simp
  · intro n hn hne
    simp only [jetExt_coordVec hkN, if_neg hne]
    simp

lemma weightForm_createOp_coord {w : ℕ → ℂ} {k : ℕ} (hk : k + 1 < N) :
    weightForm w (coordVec (N := N) (k + 1)) (createOp (coordVec (N := N) k))
      = ((k : ℂ) + 1) * w (k + 1) := by
  have hkN : k < N := by omega
  rw [weightForm]
  rw [Finset.sum_eq_single_of_mem (k + 1) (Finset.mem_range.mpr hk)]
  · rw [jetExt_createOp hk, jetExt_coordVec hk (k + 1)]
    simp only [Nat.add_sub_cancel, jetExt_coordVec hkN k, if_true,
      Complex.conj_natCast, mul_one, one_mul]
    push_cast
    ring
  · intro n hn hne
    rw [jetExt_coordVec hk n, if_neg hne]
    simp

/-- **The factorial weights are forced.**  Any diagonal weight making the two clocks adjoint
satisfies `w_k = (k+1) w_{k+1}`. -/
theorem weightForm_forced_recurrence {w : ℕ → ℂ}
    (hadj : ∀ x y : Fin N → ℂ, weightForm w (shiftOp x) y = weightForm w x (createOp y))
    {k : ℕ} (hk : k + 1 < N) : w k = ((k : ℂ) + 1) * w (k + 1) := by
  have h := hadj (coordVec (N := N) (k + 1)) (coordVec (N := N) k)
  rw [weightForm_shiftOp_coord hk, weightForm_createOp_coord hk] at h
  exact h

/-- **Uniqueness of the factorial polarization up to one positive scalar.**  Any diagonal weight
making the derivative clock and the coordinate-multiplication clock adjoint is `w_j = w_0 / j!`. -/
theorem weightForm_factorial_mul_eq {w : ℕ → ℂ}
    (hadj : ∀ x y : Fin N → ℂ, weightForm w (shiftOp x) y = weightForm w x (createOp y)) :
    ∀ {j : ℕ}, j < N → (Nat.factorial j : ℂ) * w j = w 0 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hmN : m + 1 < N := hm
    have hrec := weightForm_forced_recurrence hadj hmN
    have hih := ih (by omega)
    rw [Nat.factorial_succ]
    push_cast
    rw [← hih, hrec]
    ring

theorem weightForm_eq_div_factorial {w : ℕ → ℂ}
    (hadj : ∀ x y : Fin N → ℂ, weightForm w (shiftOp x) y = weightForm w x (createOp y))
    {j : ℕ} (hj : j < N) : w j = w 0 / (Nat.factorial j : ℂ) := by
  have h := weightForm_factorial_mul_eq hadj hj
  have hfne : (Nat.factorial j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  rw [eq_div_iff hfne, mul_comm]
  exact h

/-! ### The positive top-boundary charge -/

/-- The top-order coordinate projection `P_top`. -/
def topProj (x : Fin N → ℂ) : Fin N → ℂ := fun j => if (j : ℕ) + 1 = N then x j else 0

lemma jetExt_topProj (x : Fin N → ℂ) (n : ℕ) :
    jetExt (topProj x) n = if n + 1 = N then jetExt x n else 0 := by
  by_cases h : n < N
  · rw [jetExt_of_lt h, jetExt_of_lt h]; rfl
  · rw [jetExt_of_le (not_lt.mp h), if_neg (by omega)]

@[simp] lemma topProj_idem (x : Fin N → ℂ) : topProj (topProj x) = topProj x := by
  funext j
  simp only [topProj]
  by_cases h : (j : ℕ) + 1 = N <;> simp [h]

theorem createOp_shiftOp_apply (x : Fin N → ℂ) (j : Fin N) :
    createOp (shiftOp x) j = ((j : ℕ) : ℂ) * x j := by
  rw [createOp, jetExt_shiftOp]
  rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
  · rw [h]; simp
  · congr 1
    rw [Nat.sub_add_cancel h, jetExt_coe]

theorem shiftOp_createOp_apply (x : Fin N → ℂ) (j : Fin N) :
    shiftOp (createOp x) j
      = if (j : ℕ) + 1 = N then 0 else (((j : ℕ) : ℂ) + 1) * x j := by
  rw [shiftOp]
  by_cases h : (j : ℕ) + 1 = N
  · rw [if_pos h, jetExt_of_le (le_of_eq h.symm)]
  · have hlt : (j : ℕ) + 1 < N := by have := j.isLt; omega
    rw [if_neg h, jetExt_createOp hlt]
    simp only [Nat.add_sub_cancel, jetExt_coe]
    push_cast
    ring

/-- **The canonical-commutation defect is an exact top-boundary charge.**
`[D_N, A_N] = I - N · P_top`. -/
theorem commutator_eq (x : Fin N → ℂ) (j : Fin N) :
    shiftOp (createOp x) j - createOp (shiftOp x) j = x j - (N : ℂ) * topProj x j := by
  rw [shiftOp_createOp_apply, createOp_shiftOp_apply, topProj]
  by_cases h : (j : ℕ) + 1 = N
  · have hc : ((N : ℕ) : ℂ) = (((j : ℕ) + 1 : ℕ) : ℂ) := by rw [h]
    push_cast at hc
    rw [if_pos h, if_pos h, hc]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- `I - [D_N, A_N] = N · P_top`. -/
theorem one_sub_commutator_eq (x : Fin N → ℂ) (j : Fin N) :
    x j - (shiftOp (createOp x) j - createOp (shiftOp x) j) = (N : ℂ) * topProj x j := by
  rw [commutator_eq]; ring

lemma jetExt_const_mul (c : ℂ) (x : Fin N → ℂ) (n : ℕ) :
    jetExt (fun j => c * x j) n = c * jetExt x n := by
  by_cases h : n < N
  · rw [jetExt_of_lt h, jetExt_of_lt h]
  · rw [jetExt_of_le (not_lt.mp h), jetExt_of_le (not_lt.mp h), mul_zero]

lemma factorialForm_const_mul_left (c : ℂ) (x y : Fin N → ℂ) :
    factorialForm (fun j => c * x j) y = c * factorialForm x y := by
  rw [factorialForm, factorialForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [jetExt_const_mul]
  ring

/-- The exact value of the top-boundary charge form. -/
theorem factorialForm_topProj_self (x : Fin N → ℂ) :
    factorialForm (topProj x) x
      = (Complex.normSq (jetExt x (N - 1)) : ℂ) / (Nat.factorial (N - 1) : ℂ) := by
  cases N with
  | zero =>
    simp only [factorialForm, Finset.range_zero, Finset.sum_empty]
    rw [jetExt_of_le (by omega : (0 : ℕ) ≤ 0 - 1)]
    simp
  | succ M =>
    rw [factorialForm, Finset.sum_eq_single_of_mem M (Finset.mem_range.mpr (Nat.lt_succ_self M))]
    · rw [jetExt_topProj]
      simp only [Nat.add_sub_cancel, if_true]
      rw [Complex.mul_conj]
    · intro n hn hne
      rw [jetExt_topProj, if_neg (by omega)]
      simp

/-- **Positivity of the boundary charge.**  `I - [D_N, A_N] = N·P_top ≥ 0` for the factorial
polarization. -/
theorem factorialForm_boundaryCharge_eq (x : Fin N → ℂ) :
    factorialForm (fun j => x j - (shiftOp (createOp x) j - createOp (shiftOp x) j)) x
      = (N : ℂ) * ((Complex.normSq (jetExt x (N - 1)) : ℂ) / (Nat.factorial (N - 1) : ℂ)) := by
  have hfun : (fun j => x j - (shiftOp (createOp x) j - createOp (shiftOp x) j))
      = fun j => (N : ℂ) * topProj x j := by
    funext j; exact one_sub_commutator_eq x j
  rw [hfun, factorialForm_const_mul_left, factorialForm_topProj_self]

theorem factorialForm_boundaryCharge_re_nonneg (x : Fin N → ℂ) :
    0 ≤ (factorialForm (fun j => x j - (shiftOp (createOp x) j - createOp (shiftOp x) j)) x).re := by
  rw [factorialForm_boundaryCharge_eq]
  have h1 : (0 : ℝ) ≤ Complex.normSq (jetExt x (N - 1)) := Complex.normSq_nonneg _
  have h2 : (0 : ℝ) < (Nat.factorial (N - 1) : ℝ) := by positivity
  have hre : ((N : ℂ) * ((Complex.normSq (jetExt x (N - 1)) : ℂ)
      / (Nat.factorial (N - 1) : ℂ))).re
      = (N : ℝ) * (Complex.normSq (jetExt x (N - 1)) / (Nat.factorial (N - 1) : ℝ)) := by
    have hcast : ((Nat.factorial (N - 1) : ℕ) : ℂ) = ((Nat.factorial (N - 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, ← Complex.ofReal_div]
    simp
  rw [hre]
  positivity

/-! ### Linearity of the polarization -/

lemma jetExt_sum (s : Finset ℕ) (f : ℕ → Fin N → ℂ) (n : ℕ) :
    jetExt (∑ k ∈ s, f k) n = ∑ k ∈ s, jetExt (f k) n := by
  by_cases h : n < N
  · rw [jetExt_of_lt h, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => (jetExt_of_lt h).symm
  · rw [jetExt_of_le (not_lt.mp h)]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    exact jetExt_of_le (not_lt.mp h)

lemma jetExt_smul (c : ℂ) (x : Fin N → ℂ) (n : ℕ) : jetExt (c • x) n = c * jetExt x n := by
  by_cases h : n < N
  · rw [jetExt_of_lt h, jetExt_of_lt h]; rfl
  · rw [jetExt_of_le (not_lt.mp h), jetExt_of_le (not_lt.mp h), mul_zero]

lemma jetExt_add (x y : Fin N → ℂ) (n : ℕ) :
    jetExt (fun j => x j + y j) n = jetExt x n + jetExt y n := by
  by_cases h : n < N
  · rw [jetExt_of_lt h, jetExt_of_lt h, jetExt_of_lt h]
  · rw [jetExt_of_le (not_lt.mp h), jetExt_of_le (not_lt.mp h), jetExt_of_le (not_lt.mp h),
      add_zero]

lemma factorialForm_sum_left (s : Finset ℕ) (f : ℕ → Fin N → ℂ) (y : Fin N → ℂ) :
    factorialForm (∑ k ∈ s, f k) y = ∑ k ∈ s, factorialForm (f k) y := by
  simp only [factorialForm, jetExt_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_mul, Finset.sum_div]

lemma factorialForm_sum_right (x : Fin N → ℂ) (s : Finset ℕ) (f : ℕ → Fin N → ℂ) :
    factorialForm x (∑ k ∈ s, f k) = ∑ k ∈ s, factorialForm x (f k) := by
  simp only [factorialForm, jetExt_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]

lemma factorialForm_smul_left (c : ℂ) (x y : Fin N → ℂ) :
    factorialForm (c • x) y = c * factorialForm x y := by
  simp only [factorialForm, jetExt_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma factorialForm_smul_right (c : ℂ) (x y : Fin N → ℂ) :
    factorialForm x (c • y) = (starRingEnd ℂ) c * factorialForm x y := by
  simp only [factorialForm, jetExt_smul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma factorialForm_add_left (x₁ x₂ y : Fin N → ℂ) :
    factorialForm (fun j => x₁ j + x₂ j) y = factorialForm x₁ y + factorialForm x₂ y := by
  simp only [factorialForm, jetExt_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma factorialForm_add_right (x y₁ y₂ : Fin N → ℂ) :
    factorialForm x (fun j => y₁ j + y₂ j) = factorialForm x y₁ + factorialForm x y₂ := by
  simp only [factorialForm, jetExt_add, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma factorialForm_self_eq_sum_normSq (x : Fin N → ℂ) :
    factorialForm x x
      = ((∑ n ∈ range N, Complex.normSq (jetExt x n) / (Nat.factorial n : ℝ) : ℝ) : ℂ) := by
  rw [factorialForm, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.ofReal_div, ← Complex.mul_conj]
  norm_num

/-! ### Finite Taylor translation as the exponential of the derivative clock -/

/-- The finite Taylor translation `E_N = exp(D_N)`. -/
def taylorTranslate (x : Fin N → ℂ) : Fin N → ℂ :=
  fun j => ∑ n ∈ range N, jetExt x ((j : ℕ) + n) / (Nat.factorial n : ℂ)

lemma jetExt_shiftOp_iterate (n : ℕ) (x : Fin N → ℂ) (m : ℕ) :
    jetExt (shiftOp^[n] x) m = jetExt x (m + n) := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (shiftOp x), jetExt_shiftOp,
      show m + k + 1 = m + (k + 1) from by omega]

lemma shiftOp_iterate_apply (n : ℕ) (x : Fin N → ℂ) (j : Fin N) :
    (shiftOp^[n] x) j = jetExt x ((j : ℕ) + n) := by
  rw [← jetExt_coe (shiftOp^[n] x) j, jetExt_shiftOp_iterate]

/-- **Nilpotence of the derivative clock.**  `D_N^N = 0`. -/
theorem shiftOp_iterate_eq_zero (x : Fin N → ℂ) : shiftOp^[N] x = 0 := by
  funext j
  rw [shiftOp_iterate_apply, jetExt_of_le (by omega)]
  rfl

/-- **The Taylor translation is the terminating exponential series of the derivative clock.**
This is the precise content of `E_N = exp(D_N)` for the nilpotent jet shift. -/
theorem taylorTranslate_eq_exp_series (x : Fin N → ℂ) :
    taylorTranslate x = ∑ n ∈ range N, (Nat.factorial n : ℂ)⁻¹ • (shiftOp^[n] x) := by
  funext j
  rw [taylorTranslate, Finset.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Pi.smul_apply, shiftOp_iterate_apply, smul_eq_mul]
  ring

/-- **Matrix entries of the finite Taylor translation.**  `(E_N)_{j,k} = 1_{j ≤ k}/(k-j)!`. -/
theorem taylorTranslate_coordVec_apply {k : ℕ} (hk : k < N) (j : Fin N) :
    taylorTranslate (coordVec (N := N) k) j
      = if (j : ℕ) ≤ k then (Nat.factorial (k - (j : ℕ)) : ℂ)⁻¹ else 0 := by
  rw [taylorTranslate]
  by_cases hj : (j : ℕ) ≤ k
  · rw [if_pos hj]
    rw [Finset.sum_eq_single_of_mem (k - (j : ℕ)) (Finset.mem_range.mpr (by omega))]
    · rw [jetExt_coordVec hk, if_pos (by omega)]
      exact one_div _
    · intro n hn hne
      rw [jetExt_coordVec hk, if_neg (by omega)]
      simp
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [jetExt_coordVec hk, if_neg (by omega)]
    simp

/-- The exponential of the coordinate-multiplication clock, `exp(A_N)`. -/
def createExp (x : Fin N → ℂ) : Fin N → ℂ :=
  ∑ n ∈ range N, (Nat.factorial n : ℂ)⁻¹ • (createOp^[n] x)

lemma factorialForm_shiftOp_iterate_left (n : ℕ) (x y : Fin N → ℂ) :
    factorialForm (shiftOp^[n] x) y = factorialForm x (createOp^[n] y) := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (shiftOp x), factorialForm_shiftOp_left,
      Function.iterate_succ_apply']

/-- **`E_N^* = exp(A_N)`.**  The adjoint of the finite Taylor translation for the factorial
polarization is the exponential of the coordinate-multiplication clock. -/
theorem factorialForm_taylorTranslate_left (x y : Fin N → ℂ) :
    factorialForm (taylorTranslate x) y = factorialForm x (createExp y) := by
  rw [taylorTranslate_eq_exp_series, createExp, factorialForm_sum_left, factorialForm_sum_right]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [factorialForm_smul_left, factorialForm_smul_right, factorialForm_shiftOp_iterate_left,
    map_inv₀, Complex.conj_natCast]

/-- The coordinate-multiplication prolongation `Z_N(z) = z·I + A_N`. -/
def coordMulOp (z : ℂ) (x : Fin N → ℂ) : Fin N → ℂ := fun j => z * x j + createOp x j

/-- **`Z_N(z)^* = conj(z)·I + D_N`.** -/
theorem factorialForm_coordMulOp_left (z : ℂ) (x y : Fin N → ℂ) :
    factorialForm (coordMulOp z x) y
      = factorialForm x (fun j => (starRingEnd ℂ) z * y j + shiftOp y j) := by
  have hz : (fun j => z * x j) = z • x := rfl
  have hzy : (fun j => (starRingEnd ℂ) z * y j) = ((starRingEnd ℂ) z) • y := rfl
  have hop : coordMulOp z x = fun j => z * x j + createOp x j := rfl
  rw [hop, factorialForm_add_left, factorialForm_add_right, hz, hzy,
    factorialForm_smul_left, factorialForm_smul_right, Complex.conj_conj,
    factorialForm_createOp_left]

/-! ### The passivity no-go and the positive boundary excess -/

/-- **Passivity no-go, part one.**  `‖e_1‖²_F = 1`. -/
theorem factorialForm_coordOne_self (hN : 2 ≤ N) :
    factorialForm (coordVec (N := N) 1) (coordVec (N := N) 1) = 1 := by
  have h1 : (1 : ℕ) < N := by omega
  rw [factorialForm_self_eq_sum_normSq]
  have hsub : range 2 ⊆ range N := fun n hn =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hN)
  have hzero : ∀ n ∈ range N, n ∉ range 2 →
      Complex.normSq (jetExt (coordVec (N := N) 1) n) / (Nat.factorial n : ℝ) = 0 := by
    intro n _ hn
    have hn2 : 1 < n := by simpa using hn
    rw [jetExt_coordVec h1, if_neg (by omega)]
    simp
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [jetExt_coordVec h1]

/-- **Passivity no-go, part two.**  `‖E_N e_1‖²_F = 2 > 1`: the factorial metric does not make the
finite Gamma translation contractive. -/
theorem factorialForm_taylorTranslate_coordOne_self (hN : 2 ≤ N) :
    factorialForm (taylorTranslate (coordVec (N := N) 1)) (taylorTranslate (coordVec (N := N) 1))
      = 2 := by
  have h1 : (1 : ℕ) < N := by omega
  have hval : ∀ n : ℕ, n < N →
      jetExt (taylorTranslate (coordVec (N := N) 1)) n
        = if n ≤ 1 then (Nat.factorial (1 - n) : ℂ)⁻¹ else 0 := by
    intro n hn
    rw [jetExt_of_lt hn, taylorTranslate_coordVec_apply h1]
  rw [factorialForm_self_eq_sum_normSq]
  have hsub : range 2 ⊆ range N := fun n hn =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hN)
  have hzero : ∀ n ∈ range N, n ∉ range 2 →
      Complex.normSq (jetExt (taylorTranslate (coordVec (N := N) 1)) n)
        / (Nat.factorial n : ℝ) = 0 := by
    intro n hnN hn
    have hn2 : 1 < n := by simpa using hn
    rw [hval n (Finset.mem_range.mp hnN), if_neg (by omega)]
    simp
  rw [← Finset.sum_subset hsub hzero, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [hval 0 (by omega), hval 1 h1]
  norm_num

/-- **The Green boundary-excess law.**  For a pure top-boundary input `c·e_M` in the level-`M+1`
clock, the Taylor translation gains exactly the positive factorial outgoing energy. -/
theorem greenBoundaryExcess (M : ℕ) (c : ℂ) :
    factorialForm (N := M + 1) (taylorTranslate (c • coordVec M))
        (taylorTranslate (c • coordVec M))
      - factorialForm (N := M + 1) (c • coordVec M) (c • coordVec M)
      = ((Complex.normSq c *
          ∑ i ∈ range M, 1 / ((Nat.factorial (M - i) : ℝ) ^ (2 : ℕ) * (Nat.factorial i : ℝ)) : ℝ) : ℂ) := by
  have hM : M < M + 1 := Nat.lt_succ_self M
  have hsmul : taylorTranslate (c • coordVec (N := M + 1) M)
      = c • taylorTranslate (coordVec (N := M + 1) M) := by
    funext j
    rw [taylorTranslate, Pi.smul_apply, taylorTranslate, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [jetExt_smul]
    ring
  have hE : ∀ n : ℕ, n < M + 1 →
      jetExt (taylorTranslate (coordVec (N := M + 1) M)) n
        = (Nat.factorial (M - n) : ℂ)⁻¹ := by
    intro n hn
    rw [jetExt_of_lt hn, taylorTranslate_coordVec_apply hM, if_pos (by omega)]
  have hEnorm : ∀ n : ℕ, n < M + 1 →
      Complex.normSq (jetExt (c • taylorTranslate (coordVec (N := M + 1) M)) n)
        = Complex.normSq c * (1 / (Nat.factorial (M - n) : ℝ) ^ (2 : ℕ)) := by
    intro n hn
    rw [jetExt_smul, Complex.normSq_mul, hE n hn]
    congr 1
    have hcast : ((Nat.factorial (M - n) : ℂ))⁻¹ = (((Nat.factorial (M - n) : ℝ)⁻¹ : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.normSq_ofReal]
    ring
  have hbase : ∀ n : ℕ, n < M + 1 →
      Complex.normSq (jetExt (c • coordVec (N := M + 1) M) n)
        = if n = M then Complex.normSq c else 0 := by
    intro n hn
    rw [jetExt_smul, jetExt_coordVec hM, Complex.normSq_mul]
    by_cases h : n = M
    · rw [if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h]; simp
  rw [hsmul, factorialForm_self_eq_sum_normSq, factorialForm_self_eq_sum_normSq,
    ← Complex.ofReal_sub]
  congr 1
  have hsum1 : (∑ n ∈ range (M + 1),
      Complex.normSq (jetExt (c • taylorTranslate (coordVec (N := M + 1) M)) n)
        / (Nat.factorial n : ℝ))
      = ∑ n ∈ range (M + 1), Complex.normSq c *
          (1 / ((Nat.factorial (M - n) : ℝ) ^ (2 : ℕ) * (Nat.factorial n : ℝ))) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hEnorm n (Finset.mem_range.mp hn)]
    have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
    field_simp
  have hsum2 : (∑ n ∈ range (M + 1),
      Complex.normSq (jetExt (c • coordVec (N := M + 1) M) n) / (Nat.factorial n : ℝ))
      = Complex.normSq c / (Nat.factorial M : ℝ) := by
    rw [Finset.sum_eq_single_of_mem M (Finset.mem_range.mpr hM)]
    · rw [hbase M hM, if_pos rfl]
    · intro n hn hne
      rw [hbase n (Finset.mem_range.mp hn), if_neg hne]
      simp
  rw [hsum1, hsum2, Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_pow, one_mul]
  ring

theorem greenBoundaryExcess_pos {M : ℕ} (hM : 1 ≤ M) {c : ℂ} (hc : c ≠ 0) :
    0 < (factorialForm (N := M + 1) (taylorTranslate (c • coordVec M))
        (taylorTranslate (c • coordVec M))
      - factorialForm (N := M + 1) (c • coordVec M) (c • coordVec M)).re := by
  rw [greenBoundaryExcess, Complex.ofReal_re]
  have hcpos : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hsumpos : 0 < ∑ i ∈ range M,
      1 / ((Nat.factorial (M - i) : ℝ) ^ (2 : ℕ) * (Nat.factorial i : ℝ)) := by
    refine Finset.sum_pos (fun i _ => by positivity) ?_
    exact Finset.nonempty_range_iff.mpr (by omega)
  positivity

end

end GammaFactorialFock
end GaloisForLFunctions.HTGeometry
