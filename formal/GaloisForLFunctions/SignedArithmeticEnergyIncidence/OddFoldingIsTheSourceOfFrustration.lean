import GaloisForLFunctions.SignedArithmeticEnergyIncidence.FrustratedCyclesSpoilLocalPayment
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Odd folding is the source of frustration

A translation ledger charges the pair of positions `u, u'` by `−w(u − u')` with an even kernel
`w ≥ 0`: every overlap is aligned.  Sample it at mirror-symmetric points `±p_x`
(`mirrorCoupling`).  On even profiles the mirror pairs fold onto the half-line with charge
`−w(p_x − p_y) − w(p_x + p_y)` (`evenFold`); on odd profiles, `F(−u) = −F(u)`, with charge
`w(p_x + p_y) − w(p_x − p_y)` (`oddFold`): the reflected pair changes sign
(`incidenceEnergy_mirror_even`, `incidenceEnergy_mirror_odd`).

* **Even folding never frustrates** (`evenFold_aligned`, `evenFold_lossless`): even profiles of a
  translation ledger are aligned and locally payable whenever they are positive.
* **Odd folding frustrates exactly where the kernel grows** (`oddFold_pos_iff`): a folded overlap
  is anti-aligned iff `w(p_x + p_y) > w(p_x − p_y)`.  A kernel nonincreasing in `|u|` therefore
  folds to an aligned odd form (`oddFold_aligned_of_antitone`, `oddFold_lossless_of_antitone`).
* **The prime kernel folds into a frustrated triangle** (`oddFold_primeTriangle_pos`,
  `oddFold_primeTriangle_not_isBalanced`): for the von Mangoldt translation kernel
  `w(u) = Σ_n Λ(n) n^{−1/2} [e^{|u|} = n]` (`primeKernel`), the three positions with pairwise
  sums `log 2, log 3, log 5` have pairwise differences `log(5/3), log(5/2), log(3/2)`, which carry
  no charge; all three folded overlaps are anti-aligned, so the odd prime ledger is unbalanced
  and carries a compatible positive form that no local allocation pays
  (`exists_unpayable_odd_primeTriangle`).

The frustration of the prime ledger is thus produced by odd folding of a sparse kernel: an
even–odd balance, located at positions whose sums, not differences, are logarithms of prime
powers.
-/

open Finset ArithmeticFunction

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Mirror sampling and folding -/

/-- The sign `±1` of a side. -/
def sideSign (s : Bool) : ℝ := if s then 1 else -1

@[simp] theorem sideSign_true : sideSign true = 1 := rfl

@[simp] theorem sideSign_false : sideSign false = -1 := rfl

section Fold

variable {ι : Type*} [DecidableEq ι]

/-- A translation ledger sampled at the mirror points `±p_x`: budget `b_x`, overlap charge
`−w(position difference)`. -/
def mirrorCoupling (p : ι → ℝ) (w : ℝ → ℝ) (b : ι → ℝ) : Bool × ι → Bool × ι → ℝ := fun X Y =>
  if X = Y then b X.2 else -w (sideSign X.1 * p X.2 - sideSign Y.1 * p Y.2)

/-- The fold of the mirror ledger on odd profiles. -/
def oddFold (p : ι → ℝ) (w : ℝ → ℝ) (b : ι → ℝ) : ι → ι → ℝ := fun x y =>
  mirrorCoupling p w b (true, x) (true, y) - mirrorCoupling p w b (true, x) (false, y)

/-- The fold of the mirror ledger on even profiles. -/
def evenFold (p : ι → ℝ) (w : ℝ → ℝ) (b : ι → ℝ) : ι → ι → ℝ := fun x y =>
  mirrorCoupling p w b (true, x) (true, y) + mirrorCoupling p w b (true, x) (false, y)

variable {p : ι → ℝ} {w : ℝ → ℝ} {b : ι → ℝ}

theorem mirrorCoupling_false_false (hw : ∀ u, w (-u) = w u) (x y : ι) :
    mirrorCoupling p w b (false, x) (false, y) = mirrorCoupling p w b (true, x) (true, y) := by
  unfold mirrorCoupling
  simp only [Prod.mk.injEq, true_and, sideSign_true, sideSign_false]
  split_ifs
  · rfl
  · rw [show -1 * p x - -1 * p y = -(1 * p x - 1 * p y) by ring, hw]

theorem mirrorCoupling_false_true (hw : ∀ u, w (-u) = w u) (x y : ι) :
    mirrorCoupling p w b (false, x) (true, y) = mirrorCoupling p w b (true, x) (false, y) := by
  unfold mirrorCoupling
  simp only [Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and, if_false,
    sideSign_true, sideSign_false]
  rw [show -1 * p x - 1 * p y = -(1 * p x - -1 * p y) by ring, hw]

theorem oddFold_offDiag {x y : ι} (hxy : x ≠ y) :
    oddFold p w b x y = w (p x + p y) - w (p x - p y) := by
  unfold oddFold mirrorCoupling
  rw [if_neg fun h => hxy (Prod.ext_iff.1 h).2, if_neg fun h => Bool.noConfusion (Prod.ext_iff.1 h).1]
  simp only [sideSign_true, sideSign_false]
  rw [show 1 * p x - -1 * p y = p x + p y by ring, show 1 * p x - 1 * p y = p x - p y by ring]
  ring

theorem evenFold_offDiag {x y : ι} (hxy : x ≠ y) :
    evenFold p w b x y = -w (p x - p y) - w (p x + p y) := by
  unfold evenFold mirrorCoupling
  rw [if_neg fun h => hxy (Prod.ext_iff.1 h).2, if_neg fun h => Bool.noConfusion (Prod.ext_iff.1 h).1]
  simp only [sideSign_true, sideSign_false]
  rw [show 1 * p x - -1 * p y = p x + p y by ring, show 1 * p x - 1 * p y = p x - p y by ring]
  ring

theorem oddFold_isSymmetric (hw : ∀ u, w (-u) = w u) : IsSymmetricCoupling (oddFold p w b) := by
  intro x y
  by_cases hxy : x = y
  · rw [hxy]
  rw [oddFold_offDiag hxy, oddFold_offDiag (Ne.symm hxy), add_comm (p y),
    show p y - p x = -(p x - p y) by ring, hw]

theorem evenFold_isSymmetric (hw : ∀ u, w (-u) = w u) : IsSymmetricCoupling (evenFold p w b) := by
  intro x y
  by_cases hxy : x = y
  · rw [hxy]
  rw [evenFold_offDiag hxy, evenFold_offDiag (Ne.symm hxy), add_comm (p y),
    show p y - p x = -(p x - p y) by ring, hw]

/-- **Even folding never frustrates.** -/
theorem evenFold_aligned (hw0 : ∀ u, 0 ≤ w u) : HasNonpositiveOverlaps (evenFold p w b) := by
  intro x y hxy
  rw [evenFold_offDiag hxy]
  linarith [hw0 (p x - p y), hw0 (p x + p y)]

/-- **Odd folding frustrates exactly where the kernel grows.** -/
theorem oddFold_pos_iff {x y : ι} (hxy : x ≠ y) :
    0 < oddFold p w b x y ↔ w (p x - p y) < w (p x + p y) := by
  rw [oddFold_offDiag hxy, sub_pos]

/-- A kernel nonincreasing in `|u|` folds to an aligned odd form on the positive half-line. -/
theorem oddFold_aligned_of_antitone (hp : ∀ x, 0 < p x) (hmono : ∀ u u', |u| ≤ |u'| → w u' ≤ w u) :
    HasNonpositiveOverlaps (oddFold p w b) := by
  intro x y hxy
  rw [oddFold_offDiag hxy]
  have h1 := hp x
  have h2 := hp y
  have : |p x - p y| ≤ |p x + p y| := by
    rw [abs_of_pos (by linarith : 0 < p x + p y)]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  linarith [hmono _ _ this]

omit [DecidableEq ι] in
/-- Aligned forms are balanced. -/
theorem isBalanced_of_aligned {c : ι → ι → ℝ} (h : HasNonpositiveOverlaps c) : IsBalanced c :=
  ⟨fun _ => 1, fun _ => one_pow 2, fun i j hij => by
    simp only [switchCoupling, one_mul]; exact h i j hij⟩

variable [Fintype ι]

/-- On even profiles the mirror ledger is twice its even fold. -/
theorem incidenceEnergy_mirror_even (hw : ∀ u, w (-u) = w u) (f : ι → ℝ) :
    incidenceEnergy (mirrorCoupling p w b) (fun X => f X.2) =
      2 * incidenceEnergy (evenFold p w b) f := by
  unfold incidenceEnergy evenFold
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, mirrorCoupling_false_false hw,
    mirrorCoupling_false_true hw, ← sum_add_distrib, mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

/-- On odd profiles the mirror ledger is twice its odd fold. -/
theorem incidenceEnergy_mirror_odd (hw : ∀ u, w (-u) = w u) (f : ι → ℝ) :
    incidenceEnergy (mirrorCoupling p w b) (fun X => sideSign X.1 * f X.2) =
      2 * incidenceEnergy (oddFold p w b) f := by
  unfold incidenceEnergy oddFold
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sideSign_true, sideSign_false,
    mirrorCoupling_false_false hw, mirrorCoupling_false_true hw, ← sum_add_distrib, mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

/-- **Even profiles pay locally**: positivity of the mirror ledger on even profiles is local payment
of its even fold. -/
theorem evenFold_lossless (hw : ∀ u, w (-u) = w u) (hw0 : ∀ u, 0 ≤ w u) :
    (∀ f : ι → ℝ, 0 ≤ incidenceEnergy (mirrorCoupling p w b) (fun X => f X.2)) ↔
      LocallyPayable (evenFold p w b) := by
  rw [← nonneg_iff_locallyPayable_of_isBalanced (evenFold_isSymmetric hw)
    (isBalanced_of_aligned (evenFold_aligned hw0))]
  simp only [incidenceEnergy_mirror_even hw]
  exact forall_congr' fun f => by constructor <;> intro h <;> linarith

/-- **Odd profiles pay locally for antitone kernels.** -/
theorem oddFold_lossless_of_antitone (hw : ∀ u, w (-u) = w u) (hp : ∀ x, 0 < p x)
    (hmono : ∀ u u', |u| ≤ |u'| → w u' ≤ w u) :
    (∀ f : ι → ℝ, 0 ≤ incidenceEnergy (mirrorCoupling p w b) (fun X => sideSign X.1 * f X.2)) ↔
      LocallyPayable (oddFold p w b) := by
  rw [← nonneg_iff_locallyPayable_of_isBalanced (oddFold_isSymmetric hw)
    (isBalanced_of_aligned (oddFold_aligned_of_antitone hp hmono))]
  simp only [incidenceEnergy_mirror_odd hw]
  exact forall_congr' fun f => by constructor <;> intro h <;> linarith

end Fold

/-! ### The prime kernel -/

/-- The von Mangoldt translation kernel `w(u) = Σ_n Λ(n) n^{−1/2} [e^{|u|} = n]`. -/
def primeKernel (u : ℝ) : ℝ := ∑' n : ℕ, if Real.exp |u| = n then Λ n / Real.sqrt n else 0

theorem primeKernel_nonneg (u : ℝ) : 0 ≤ primeKernel u :=
  tsum_nonneg fun n => by
    split_ifs
    · exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_refl 0

theorem primeKernel_neg (u : ℝ) : primeKernel (-u) = primeKernel u := by
  simp only [primeKernel, abs_neg]

/-- Off the logarithms of the integers the prime kernel vanishes. -/
theorem primeKernel_eq_zero {u : ℝ} (h : ∀ n : ℕ, Real.exp |u| ≠ n) : primeKernel u = 0 := by
  unfold primeKernel
  rw [show (fun n : ℕ => if Real.exp |u| = n then Λ n / Real.sqrt n else 0) = fun _ => 0 from
    funext fun n => if_neg (h n), tsum_zero]

/-- At `log p` the prime kernel is `log p/√p`. -/
theorem primeKernel_log_prime {q : ℕ} (hq : q.Prime) :
    primeKernel (Real.log q) = Real.log q / Real.sqrt q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.one_lt.le)
  unfold primeKernel
  rw [abs_of_nonneg hlog, Real.exp_log hq0, tsum_eq_single q fun n hn => if_neg fun h =>
    hn (by exact_mod_cast h.symm), if_pos rfl, vonMangoldt_apply_prime hq]

/-- A real strictly between two consecutive integers is not an integer. -/
theorem ne_natCast_of_between {x : ℝ} {m : ℕ} (h1 : (m : ℝ) < x) (h2 : x < m + 1) (n : ℕ) :
    x ≠ n := by
  intro h
  rw [h] at h1 h2
  have a : m < n := by exact_mod_cast h1
  have b : n < m + 1 := by exact_mod_cast h2
  omega

/-! ### The frustrated prime triangle -/

/-- Three positions with pairwise sums `log 2`, `log 3`, `log 5`. -/
def primeTrianglePos : Fin 3 → ℝ :=
  ![(Real.log 2 + Real.log 5 - Real.log 3) / 2, (Real.log 2 + Real.log 3 - Real.log 5) / 2,
    (Real.log 3 + Real.log 5 - Real.log 2) / 2]

theorem primeTrianglePos_pos : ∀ x, 0 < primeTrianglePos x := by
  have l23 : Real.log 2 + Real.log 3 = Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l25 : Real.log 2 + Real.log 5 = Real.log 10 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l35 : Real.log 3 + Real.log 5 = Real.log 15 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have a : Real.log 3 < Real.log 10 := Real.log_lt_log (by norm_num) (by norm_num)
  have b : Real.log 5 < Real.log 6 := Real.log_lt_log (by norm_num) (by norm_num)
  have c : Real.log 2 < Real.log 15 := Real.log_lt_log (by norm_num) (by norm_num)
  intro x
  fin_cases x <;> simp only [primeTrianglePos, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> linarith

/-- The prime kernel vanishes at `log a − log b` when `a/b` lies strictly between consecutive
integers. -/
theorem primeKernel_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < a) {m : ℕ}
    (h1 : (m : ℝ) < a / b) (h2 : a / b < m + 1) : primeKernel (Real.log a - Real.log b) = 0 := by
  apply primeKernel_eq_zero
  have hpos : 0 ≤ Real.log a - Real.log b := by
    linarith [Real.log_lt_log hb hab]
  rw [abs_of_nonneg hpos, Real.exp_sub, Real.exp_log ha, Real.exp_log hb]
  exact ne_natCast_of_between h1 h2

/-- **All three folded overlaps of the prime triangle are anti-aligned.** -/
theorem oddFold_primeTriangle_pos (b : Fin 3 → ℝ) (x y : Fin 3) (hxy : x ≠ y) :
    0 < oddFold primeTrianglePos primeKernel b x y := by
  have k2 := primeKernel_log_prime Nat.prime_two
  have k3 := primeKernel_log_prime Nat.prime_three
  have k5 := primeKernel_log_prime Nat.prime_five
  push_cast at k2 k3 k5
  have p2 : 0 < Real.log 2 / Real.sqrt 2 := div_pos (Real.log_pos (by norm_num)) (by positivity)
  have p3 : 0 < Real.log 3 / Real.sqrt 3 := div_pos (Real.log_pos (by norm_num)) (by positivity)
  have p5 : 0 < Real.log 5 / Real.sqrt 5 := div_pos (Real.log_pos (by norm_num)) (by positivity)
  -- the differences `log(5/3)`, `log(5/2)`, `log(3/2)` carry no charge
  have z53 : primeKernel (Real.log 5 - Real.log 3) = 0 :=
    primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1) (by norm_num)
      (by norm_num)
  have z52 : primeKernel (Real.log 5 - Real.log 2) = 0 :=
    primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 2) (by norm_num)
      (by norm_num)
  have z32 : primeKernel (Real.log 3 - Real.log 2) = 0 :=
    primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1) (by norm_num)
      (by norm_num)
  have hsym : ∀ u, primeKernel (-u) = primeKernel u := primeKernel_neg
  rw [oddFold_offDiag hxy]
  fin_cases x <;> fin_cases y <;> simp only [primeTrianglePos, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hxy ⊢ <;> first
    | exact absurd rfl hxy
    | (rw [show (Real.log 2 + Real.log 5 - Real.log 3) / 2 + (Real.log 2 + Real.log 3 - Real.log 5) / 2
          = Real.log 2 by ring, show (Real.log 2 + Real.log 5 - Real.log 3) / 2 -
          (Real.log 2 + Real.log 3 - Real.log 5) / 2 = Real.log 5 - Real.log 3 by ring, k2, z53]
       linarith)
    | (rw [show (Real.log 2 + Real.log 3 - Real.log 5) / 2 + (Real.log 2 + Real.log 5 - Real.log 3) / 2
          = Real.log 2 by ring, show (Real.log 2 + Real.log 3 - Real.log 5) / 2 -
          (Real.log 2 + Real.log 5 - Real.log 3) / 2 = -(Real.log 5 - Real.log 3) by ring, k2,
          hsym, z53]
       linarith)
    | (rw [show (Real.log 2 + Real.log 3 - Real.log 5) / 2 + (Real.log 3 + Real.log 5 - Real.log 2) / 2
          = Real.log 3 by ring, show (Real.log 2 + Real.log 3 - Real.log 5) / 2 -
          (Real.log 3 + Real.log 5 - Real.log 2) / 2 = -(Real.log 5 - Real.log 2) by ring, k3,
          hsym, z52]
       linarith)
    | (rw [show (Real.log 3 + Real.log 5 - Real.log 2) / 2 + (Real.log 2 + Real.log 3 - Real.log 5) / 2
          = Real.log 3 by ring, show (Real.log 3 + Real.log 5 - Real.log 2) / 2 -
          (Real.log 2 + Real.log 3 - Real.log 5) / 2 = Real.log 5 - Real.log 2 by ring, k3, z52]
       linarith)
    | (rw [show (Real.log 3 + Real.log 5 - Real.log 2) / 2 + (Real.log 2 + Real.log 5 - Real.log 3) / 2
          = Real.log 5 by ring, show (Real.log 3 + Real.log 5 - Real.log 2) / 2 -
          (Real.log 2 + Real.log 5 - Real.log 3) / 2 = Real.log 3 - Real.log 2 by ring, k5, z32]
       linarith)
    | (rw [show (Real.log 2 + Real.log 5 - Real.log 3) / 2 + (Real.log 3 + Real.log 5 - Real.log 2) / 2
          = Real.log 5 by ring, show (Real.log 2 + Real.log 5 - Real.log 3) / 2 -
          (Real.log 3 + Real.log 5 - Real.log 2) / 2 = -(Real.log 3 - Real.log 2) by ring, k5,
          hsym, z32]
       linarith)

/-- **The odd prime ledger is frustrated**: its fold at the prime triangle is unbalanced, whatever
the budgets. -/
theorem oddFold_primeTriangle_not_isBalanced (b : Fin 3 → ℝ) :
    ¬ IsBalanced (oddFold primeTrianglePos primeKernel b) := by
  intro hb
  have hpos := oddFold_primeTriangle_pos b
  have h01 := hpos 0 1 (by decide)
  have h12 := hpos 1 2 (by decide)
  have h20 := hpos 2 0 (by decide)
  have hwalk : IsWalkFrom (oddFold primeTrianglePos primeKernel b) 0 [1, 2, 0] :=
    ⟨by decide, h01.ne', by decide, h12.ne', by decide, h20.ne', trivial⟩
  have h1 := alignedCycles_of_isBalanced hb 0 [1, 2, 0] hwalk rfl
  rw [walkHolonomy_triangle h01.ne' h12.ne' h20.ne',
    abs_of_pos (mul_pos (mul_pos h01 h12) h20), div_self (mul_pos (mul_pos h01 h12) h20).ne'] at h1
  norm_num at h1

/-- **The odd prime ledger carries an unpayable positive form**: some nonnegative form whose
overlaps carry the signs of the folded prime triangle is not locally payable. -/
theorem exists_unpayable_odd_primeTriangle (b : Fin 3 → ℝ) :
    ∃ c : Fin 3 → Fin 3 → ℝ, IsSymmetricCoupling c ∧
      SignCompatible (oddFold primeTrianglePos primeKernel b) c ∧
      (∀ f, 0 ≤ incidenceEnergy c f) ∧ ¬ LocallyPayable c :=
  exists_frustrated_witness (oddFold_isSymmetric primeKernel_neg)
    (oddFold_primeTriangle_not_isBalanced b)

/-- **Even profiles of the prime ledger pay locally** at every sampling. -/
theorem evenFold_prime_lossless {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (b : ι → ℝ) :
    (∀ f : ι → ℝ, 0 ≤ incidenceEnergy (mirrorCoupling p primeKernel b) (fun X => f X.2)) ↔
      LocallyPayable (evenFold p primeKernel b) :=
  evenFold_lossless primeKernel_neg primeKernel_nonneg

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
