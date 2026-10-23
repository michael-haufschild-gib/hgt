import GaloisForLFunctions.SignedArithmeticEnergyIncidence.BalancedIncidenceIsLocallyPayable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Chain lending and the capacity of a uniform train

A **chain** is the signed incidence form of a path of overlapping strips: budgets `d_k` at the
points `k < L` and overlap charges `e_k` between `k` and `k + 1`,
`E(f) = Σ_{k<L} d_k f_k² + 2 Σ_{k+1<L} e_k f_k f_{k+1}` (`incidenceEnergy_chainCoupling`).

* **Chains are balanced** (`chainCoupling_isBalanced`): switching by the running sign of the
  overlaps aligns every charge, whatever its sign.  Hence (`chain_nonneg_iff_locallyPayable`) a
  chain is positive exactly when it has a **lending ledger**: every point splits its budget between
  the two overlaps it meets so that each overlap is paid once.  This is the exact form of lending
  along nested strips.
* **The capacity of a uniform train.**  For the chain of `n + 1` equal points coupled by unit
  overlaps, the sine gauge `v_k = sin((k+1)θ)`, `θ = π/(n+2)`, solves `Cv = 0` for the budget
  `2 cos θ`; it is a positive supersolution, so (`uniformTrain_capacity`)
  `2 Σ_{k<n} f_k f_{k+1} ≤ 2 cos(π/(n+2)) Σ_{k≤n} f_k²`,
  with equality at the sine profile (`uniformTrain_capacity_attained`) and no smaller constant
  (`uniformTrain_capacity_sharp`).  A train of length `n + 1` therefore carries the full joint charge
  `2` of its overlaps only up to the deficit `2 (1 − cos(π/(n+2))) ≍ π²/(n+2)²`: long resonant trains
  attain the union bound, short ones cannot.
-/

open Finset Real

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Chain couplings -/

/-- Entry of the chain coupling with budgets `d` and overlap charges `e` (between `k` and
`k + 1`). -/
def chainEntry (d e : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i = j then d i else if i + 1 = j then e i else if j + 1 = i then e j else 0

/-- The chain coupling on `L` points. -/
def chainCoupling (L : ℕ) (d e : ℕ → ℝ) : Fin L → Fin L → ℝ := fun i j => chainEntry d e i j

theorem chainEntry_symm (d e : ℕ → ℝ) (i j : ℕ) : chainEntry d e i j = chainEntry d e j i := by
  unfold chainEntry
  by_cases h1 : i = j
  · subst h1; simp
  · have h1' : j ≠ i := Ne.symm h1
    by_cases h2 : i + 1 = j
    · have : ¬ j + 1 = i := by omega
      simp [h1, h1', h2, this]
    · by_cases h3 : j + 1 = i
      · simp [h1, h1', h2, h3]
      · simp [h1, h1', h2, h3]

theorem chainCoupling_isSymmetric (L : ℕ) (d e : ℕ → ℝ) :
    IsSymmetricCoupling (chainCoupling L d e) :=
  fun i j => chainEntry_symm d e i j

/-- The chain entry against a profile splits into the point, its right and its left neighbour. -/
theorem chainEntry_mul_eq (d e v : ℕ → ℝ) (i m : ℕ) :
    chainEntry d e i m * v m =
      (if m = i then d i * v i else 0) + (if m = i + 1 then e i * v (i + 1) else 0) +
        (if m + 1 = i then e m * v m else 0) := by
  unfold chainEntry
  rcases Nat.lt_trichotomy m i with hlt | rfl | hgt
  · have h1 : ¬ i = m := by omega
    have h2 : ¬ i + 1 = m := by omega
    have h4 : ¬ m = i := by omega
    have h5 : ¬ m = i + 1 := by omega
    by_cases h3 : m + 1 = i
    · simp only [h1, h2, h3, h4, h5, if_true, if_false]; ring
    · simp only [h1, h2, h3, h4, h5, if_false]; ring
  · have h2 : ¬ m + 1 = m := by omega
    have h5 : ¬ m = m + 1 := by omega
    simp only [h2, h5, if_true, if_false]; ring
  · have h1 : ¬ i = m := by omega
    have h3 : ¬ m + 1 = i := by omega
    have h4 : ¬ m = i := by omega
    by_cases h2 : i + 1 = m
    · subst h2
      simp only [h1, h3, h4, if_true, if_false]; ring
    · have h5 : ¬ m = i + 1 := fun h => h2 h.symm
      simp only [h1, h2, h3, h4, h5, if_false]; ring

/-- The action of a chain: `(Cv)_i = d_i v_i + e_i v_{i+1} [i+1 < L] + e_{i-1} v_{i-1} [i ≥ 1]`. -/
theorem couplingAction_chainCoupling (L : ℕ) (d e v : ℕ → ℝ) (i : Fin L) :
    couplingAction (chainCoupling L d e) (fun j => v j) i =
      d i * v i + (if (i : ℕ) + 1 < L then e i * v (i + 1) else 0) +
        ∑ m ∈ range L, if m + 1 = (i : ℕ) then e m * v m else 0 := by
  unfold couplingAction chainCoupling
  rw [Fin.sum_univ_eq_sum_range (fun m => chainEntry d e i m * v m) L]
  simp only [chainEntry_mul_eq, sum_add_distrib, sum_ite_eq', mem_range, i.isLt, if_true]

theorem sum_range_left_neighbour (L : ℕ) (e v : ℕ → ℝ) (i : ℕ) (hi : i < L) :
    (∑ m ∈ range L, if m + 1 = i then e m * v m else 0) =
      if 1 ≤ i then e (i - 1) * v (i - 1) else 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have : ∀ m, (m + 1 = k + 1) ↔ m = k := fun m => by omega
    simp only [this, sum_ite_eq', mem_range]
    simp [show k < L by omega]

/-- The energy of a chain. -/
theorem incidenceEnergy_chainCoupling (n : ℕ) (d e f : ℕ → ℝ) :
    incidenceEnergy (chainCoupling (n + 1) d e) (fun j => f j) =
      ∑ k ∈ range (n + 1), d k * f k ^ 2 + 2 * ∑ k ∈ range n, e k * f k * f (k + 1) := by
  rw [incidenceEnergy_eq_sum_mul_couplingAction]
  have hact : ∀ i : Fin (n + 1), couplingAction (chainCoupling (n + 1) d e) (fun j => f j) i =
      d i * f i + (if (i : ℕ) + 1 < n + 1 then e i * f (i + 1) else 0) +
        if 1 ≤ (i : ℕ) then e (i - 1) * f (i - 1) else 0 := by
    intro i
    rw [couplingAction_chainCoupling, sum_range_left_neighbour _ _ _ _ i.isLt]
  simp only [hact]
  rw [Fin.sum_univ_eq_sum_range (fun i => f i * (d i * f i +
    (if i + 1 < n + 1 then e i * f (i + 1) else 0) +
      if 1 ≤ i then e (i - 1) * f (i - 1) else 0)) (n + 1)]
  simp only [mul_add, sum_add_distrib]
  have hright : ∑ i ∈ range (n + 1), f i * (if i + 1 < n + 1 then e i * f (i + 1) else 0) =
      ∑ k ∈ range n, e k * f k * f (k + 1) := by
    rw [sum_range_succ]
    simp only [lt_irrefl, if_false, mul_zero, add_zero]
    refine sum_congr rfl fun k hk => ?_
    have : k + 1 < n + 1 := by simp at hk; omega
    simp only [this, if_true]
    ring
  have hleft : ∑ i ∈ range (n + 1), f i * (if 1 ≤ i then e (i - 1) * f (i - 1) else 0) =
      ∑ k ∈ range n, e k * f k * f (k + 1) := by
    rw [sum_range_succ']
    simp only [Nat.le_add_left, if_true, Nat.add_sub_cancel, nonpos_iff_eq_zero, one_ne_zero,
      if_false, mul_zero, add_zero]
    exact sum_congr rfl fun k _ => by ring
  rw [hright, hleft]
  have : ∀ i ∈ range (n + 1), f i * (d i * f i) = d i * f i ^ 2 := fun i _ => by ring
  rw [sum_congr rfl this]
  ring

/-! ### Chains are balanced -/

/-- The running sign of a chain's overlaps. -/
def chainSign (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => if e k ≤ 0 then chainSign e k else -chainSign e k

theorem chainSign_sq (e : ℕ → ℝ) (k : ℕ) : chainSign e k ^ 2 = 1 := by
  induction k with
  | zero => simp [chainSign]
  | succ k ih =>
    simp only [chainSign]
    split_ifs <;> simp [ih]

theorem chainSign_mul_succ_mul (e : ℕ → ℝ) (k : ℕ) :
    chainSign e k * chainSign e (k + 1) * e k ≤ 0 := by
  simp only [chainSign]
  split_ifs with h
  · rw [← sq, chainSign_sq, one_mul]; exact h
  · have : chainSign e k * -chainSign e k = -1 := by
      rw [mul_neg, ← sq, chainSign_sq]
    rw [this]
    linarith

/-- **Chains are balanced**: the running sign aligns every overlap. -/
theorem chainCoupling_isBalanced (L : ℕ) (d e : ℕ → ℝ) : IsBalanced (chainCoupling L d e) := by
  refine ⟨fun i => chainSign e i, fun i => chainSign_sq e i, fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [switchCoupling, chainCoupling, chainEntry, hij', if_false]
  by_cases h2 : (i : ℕ) + 1 = j
  · simp only [h2, if_true]
    rw [← h2]
    exact chainSign_mul_succ_mul e i
  · by_cases h3 : (j : ℕ) + 1 = i
    · simp only [h2, h3, if_true, if_false]
      rw [← h3, mul_comm (chainSign e (j + 1))]
      exact chainSign_mul_succ_mul e j
    · simp [h2, h3]

/-- **Chain lending duality.**  A chain is positive exactly when it has a lending ledger. -/
theorem chain_nonneg_iff_locallyPayable (L : ℕ) (d e : ℕ → ℝ) :
    (∀ f, 0 ≤ incidenceEnergy (chainCoupling L d e) f) ↔ LocallyPayable (chainCoupling L d e) :=
  nonneg_iff_locallyPayable_of_isBalanced (chainCoupling_isSymmetric L d e)
    (chainCoupling_isBalanced L d e)

/-! ### The capacity of a uniform train -/

/-- The sine gauge of a train of `n + 1` points: `sin((k+1) π/(n+2))`. -/
def trainSine (n : ℕ) (k : ℕ) : ℝ := Real.sin ((k + 1 : ℝ) * (π / (n + 2)))

theorem trainSine_pos (n : ℕ) {k : ℕ} (hk : k < n + 1) : 0 < trainSine n k := by
  unfold trainSine
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have hk' : (k : ℝ) + 1 < n + 2 := by exact_mod_cast (show k + 1 < n + 2 by omega)
    have hpos : (0 : ℝ) < n + 2 := by positivity
    calc ((k : ℝ) + 1) * (π / (n + 2)) < (n + 2) * (π / (n + 2)) :=
          mul_lt_mul_of_pos_right hk' (by positivity)
      _ = π := by field_simp

/-- The three-term identity `sin((k+2)θ) + sin(kθ) = 2 cos θ · sin((k+1)θ)`. -/
theorem sin_three_term (θ : ℝ) (k : ℕ) :
    Real.sin ((k + 2 : ℝ) * θ) + Real.sin ((k : ℝ) * θ) =
      2 * Real.cos θ * Real.sin ((k + 1 : ℝ) * θ) := by
  have h1 : (k + 2 : ℝ) * θ = (k + 1 : ℝ) * θ + θ := by ring
  have h2 : (k : ℝ) * θ = (k + 1 : ℝ) * θ - θ := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-- The sine gauge solves the train equation `2 cos θ · v_i = v_{i−1} + v_{i+1}` with the boundary
values `v_{−1} = v_{n+1} = 0`. -/
theorem couplingAction_uniformTrain_trainSine (n : ℕ) (i : Fin (n + 1)) :
    couplingAction (chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) fun _ => -1)
      (fun j => trainSine n j) i = 0 := by
  rw [couplingAction_chainCoupling, sum_range_left_neighbour _ _ _ _ i.isLt]
  set θ := π / ((n : ℝ) + 2) with hθ
  have h3 := sin_three_term θ i
  have hend : Real.sin (((n : ℝ) + 2) * θ) = 0 := by
    rw [hθ, mul_div_cancel₀ _ (by positivity : ((n : ℝ) + 2) ≠ 0), Real.sin_pi]
  unfold trainSine
  rw [← hθ]
  by_cases hr : (i : ℕ) + 1 < n + 1
  · by_cases hl : 1 ≤ (i : ℕ)
    · simp only [hr, hl, if_true]
      have e1 : ((((i : ℕ) + 1 : ℕ) : ℝ) + 1) * θ = ((i : ℝ) + 2) * θ := by push_cast; ring
      have e2 : ((((i : ℕ) - 1 : ℕ) : ℝ) + 1) * θ = (i : ℝ) * θ := by
        rw [Nat.cast_sub hl]; push_cast; ring
      rw [e1, e2]
      linarith
    · have hi0 : (i : ℕ) = 0 := by omega
      simp only [hr, hl, if_true, if_false]
      have h0 : Real.sin (((i : ℕ) : ℝ) * θ) = 0 := by rw [hi0]; simp
      have e1 : ((((i : ℕ) + 1 : ℕ) : ℝ) + 1) * θ = ((i : ℝ) + 2) * θ := by push_cast; ring
      rw [e1]
      linarith
  · have hin : (i : ℕ) = n := by have := i.isLt; omega
    have hl : 1 ≤ (i : ℕ) ∨ (i : ℕ) = 0 := by omega
    have hend' : Real.sin (((i : ℕ) + 2 : ℝ) * θ) = 0 := by rw [hin]; exact hend
    rcases hl with hl | hl
    · simp only [hr, hl, if_true, if_false]
      have e2 : ((((i : ℕ) - 1 : ℕ) : ℝ) + 1) * θ = (i : ℝ) * θ := by
        rw [Nat.cast_sub hl]; push_cast; ring
      rw [e2]
      linarith
    · have : ¬ 1 ≤ (i : ℕ) := by omega
      simp only [hr, this, if_false]
      have h0 : Real.sin (((i : ℕ) : ℝ) * θ) = 0 := by rw [hl]; simp
      linarith

/-- **Capacity of a uniform train.**  `2 Σ_{k<n} f_k f_{k+1} ≤ 2 cos(π/(n+2)) Σ_{k≤n} f_k²`. -/
theorem uniformTrain_capacity (n : ℕ) (f : ℕ → ℝ) :
    2 * ∑ k ∈ range n, f k * f (k + 1) ≤
      2 * Real.cos (π / (n + 2)) * ∑ k ∈ range (n + 1), f k ^ 2 := by
  have hpay : LocallyPayable
      (chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) fun _ => -1) := by
    refine locallyPayable_of_supersolution (chainCoupling_isSymmetric _ _ _) ?_
      (v := fun j => trainSine n j) (fun i => trainSine_pos n i.isLt)
      (fun i => (couplingAction_uniformTrain_trainSine n i).symm ▸ le_refl 0)
    intro i j hij
    have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp only [chainCoupling, chainEntry, hij', if_false]
    split_ifs <;> norm_num
  have h := incidenceEnergy_nonneg_of_locallyPayable (chainCoupling_isSymmetric _ _ _) hpay
    (fun j => f j)
  rw [incidenceEnergy_chainCoupling] at h
  simp only [← mul_sum] at h
  have e : ∑ k ∈ range n, -1 * f k * f (k + 1) = -∑ k ∈ range n, f k * f (k + 1) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun k _ => by ring
  rw [e] at h
  linarith

/-- The sine profile attains the capacity. -/
theorem uniformTrain_capacity_attained (n : ℕ) :
    2 * ∑ k ∈ range n, trainSine n k * trainSine n (k + 1) =
      2 * Real.cos (π / (n + 2)) * ∑ k ∈ range (n + 1), trainSine n k ^ 2 := by
  have h0 : incidenceEnergy
      (chainCoupling (n + 1) (fun _ => 2 * Real.cos (π / (n + 2))) fun _ => -1)
      (fun j => trainSine n j) = 0 := by
    rw [incidenceEnergy_eq_sum_mul_couplingAction]
    exact sum_eq_zero fun i _ => by rw [couplingAction_uniformTrain_trainSine, mul_zero]
  rw [incidenceEnergy_chainCoupling] at h0
  simp only [← mul_sum] at h0
  have e : ∑ k ∈ range n, -1 * trainSine n k * trainSine n (k + 1) =
      -∑ k ∈ range n, trainSine n k * trainSine n (k + 1) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun k _ => by ring
  rw [e] at h0
  linarith

/-- No constant below `2 cos(π/(n+2))` bounds the train charge. -/
theorem uniformTrain_capacity_sharp (n : ℕ) {c : ℝ} (hc : c < 2 * Real.cos (π / (n + 2))) :
    ∃ f : ℕ → ℝ, c * ∑ k ∈ range (n + 1), f k ^ 2 < 2 * ∑ k ∈ range n, f k * f (k + 1) := by
  refine ⟨trainSine n, ?_⟩
  rw [uniformTrain_capacity_attained]
  have hpos : 0 < ∑ k ∈ range (n + 1), trainSine n k ^ 2 := by
    refine sum_pos (fun k hk => ?_) ⟨0, by simp⟩
    exact pow_pos (trainSine_pos n (mem_range.mp hk)) 2
  exact mul_lt_mul_of_pos_right hc hpos

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
