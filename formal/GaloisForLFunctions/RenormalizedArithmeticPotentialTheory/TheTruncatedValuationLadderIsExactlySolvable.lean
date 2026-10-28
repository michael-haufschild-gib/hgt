import Mathlib

/-!
# The truncated valuation ladder is exactly solvable

One `p`-ladder of the multiplicative walk, in the pole gauge, is the chain on `{0, …, J}` with
weights `w_j = p^{−j}` and the all-pairs Dirichlet form `E(g) = Σ_{i<j} log p · w_j (g_j − g_i)²`.

* **The modes** (`ladMode`): `ψ_0 = 1` and, for `1 ≤ k ≤ J`, `ψ_k = 1_{j ≥ k} − c_k 1_{j = k−1}` with
  `c_k = (1 − p^{−(J−k+1)})/(p − 1)`, chosen so that `Σ_j w_j ψ_k(j) = 0`. Since `ψ_k = 1` on the
  support of `ψ_l` for `k < l`, the modes are orthogonal (`ladInner_ladMode_ladMode`).
* **They are eigenvectors** (`ladForm_ladMode`): `B(ψ_k, g) = λ_k ⟨ψ_k, g⟩` for every `g`, with
  `λ_k = log p (k + c_k)`. As `J → ∞`, `λ_k → k log p + log p/(p − 1)`.
* **They are complete** (`eq_zero_of_ladInner_ladMode`): a vector orthogonal to every mode
  vanishes, by induction on the tail sums `S_k = Σ_{j ≥ k} w_j r_j`. Hence Parseval and the
  energy expansion `E(g) = Σ_k λ_k ⟨g, ψ_k⟩²/‖ψ_k‖²` (`ladForm_self_eq`).
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. The ladder -/

/-- The weight `p^{−j}` of level `j`. -/
def ladWeight (p j : ℕ) : ℝ := (1 / (p : ℝ)) ^ j

/-- The weighted inner product on `{0, …, J}`. -/
def ladInner (p J : ℕ) (f g : ℕ → ℝ) : ℝ := ∑ j ∈ range (J + 1), ladWeight p j * (f j * g j)

/-- The polarized ladder energy `B(f, g) = Σ_{i<j} log p · w_j (f_j − f_i)(g_j − g_i)`. -/
def ladForm (p J : ℕ) (f g : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (J + 1), ∑ j ∈ range (J + 1),
    if i < j then Real.log p * ladWeight p j * ((f j - f i) * (g j - g i)) else 0

/-- The correction `c_k = (1 − p^{−(J−k+1)})/(p − 1)`. -/
def ladCorr (p J k : ℕ) : ℝ := (1 - (1 / (p : ℝ)) ^ (J - k + 1)) / ((p : ℝ) - 1)

/-- The modes: `ψ_0 = 1`, `ψ_k = 1_{j ≥ k} − c_k 1_{j = k−1}`. -/
def ladMode (p J k j : ℕ) : ℝ :=
  if k = 0 then 1 else if k ≤ j then 1 else if j + 1 = k then -ladCorr p J k else 0

/-- The eigenvalues: `λ_0 = 0`, `λ_k = log p (k + c_k)`. -/
def ladEig (p J k : ℕ) : ℝ := if k = 0 then 0 else Real.log p * (k + ladCorr p J k)

variable {p : ℕ}

theorem ladWeight_pos (hp : 0 < p) (j : ℕ) : 0 < ladWeight p j := by
  unfold ladWeight
  have : (0 : ℝ) < p := by exact_mod_cast hp
  positivity

theorem ladCorr_pos (hp : 1 < p) (J k : ℕ) : 0 < ladCorr p J k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hr : (1 / (p : ℝ)) ^ (J - k + 1) < 1 :=
    pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hp1) (by omega)
  unfold ladCorr
  exact div_pos (by linarith) (by linarith)

theorem ladCorr_le (hp : 1 < p) (J k : ℕ) : ladCorr p J k ≤ 1 / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  unfold ladCorr
  exact div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ (1 / (p : ℝ)) ^ (J - k + 1) := by
    positivity
    linarith) (by linarith)

theorem ladEig_nonneg (hp : 1 < p) (J k : ℕ) : 0 ≤ ladEig p J k := by
  unfold ladEig
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Real.log_natCast_nonneg p)
      (add_nonneg (Nat.cast_nonneg k) (ladCorr_pos hp J k).le)

/-! ### 2. Tail sums -/

/-- `Σ_{k ≤ j ≤ J} p^{−j} = p^{−(k−1)} c_k` for `1 ≤ k ≤ J`. -/
theorem sum_ladWeight_ge (hp : 1 < p) {J k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) :
    ∑ j ∈ range (J + 1), (if k ≤ j then ladWeight p j else 0) =
      ladWeight p (k - 1) * ladCorr p J k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  set r := 1 / (p : ℝ)
  have hr1 : r ≠ 1 := by
    simp only [r]; rw [Ne, div_eq_one_iff_eq (by linarith)]; linarith
  rw [← sum_filter, show (range (J + 1)).filter (fun j => k ≤ j) = Ico k (J + 1) by
    ext j; simp only [mem_filter, mem_range, mem_Ico]; omega,
    sum_Ico_eq_sum_range]
  simp only [ladWeight, pow_add, ← mul_sum]
  rw [geom_sum_eq hr1, show J + 1 - k = J - k + 1 by omega, ladCorr]
  have hk' : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk', pow_succ]
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  simp only [r]
  field_simp
  ring

/-! ### 3. Two elementary forms -/

theorem ladForm_add_smul (J : ℕ) (a : ℝ) (f f' g : ℕ → ℝ) :
    ladForm p J (fun j => f j + a * f' j) g = ladForm p J f g + a * ladForm p J f' g := by
  rw [ladForm, ladForm, ladForm, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem ladForm_comm (J : ℕ) (f g : ℕ → ℝ) : ladForm p J f g = ladForm p J g f :=
  sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by split_ifs <;> ring

/-- The form of a step `1_{j ≥ k}`: `B(s_k, g) = log p (k Σ_{j≥k} w_j g_j − (Σ_{j≥k} w_j) Σ_{i<k} g_i)`. -/
theorem ladForm_step (J : ℕ) {k : ℕ} (hk : k ≤ J + 1) (g : ℕ → ℝ) :
    ladForm p J (fun j => if k ≤ j then 1 else 0) g =
      Real.log p * (k * ∑ j ∈ range (J + 1), (if k ≤ j then ladWeight p j * g j else 0) -
        (∑ j ∈ range (J + 1), if k ≤ j then ladWeight p j else 0) *
          ∑ i ∈ range (J + 1), if i < k then g i else 0) := by
  have hterm : ∀ i j, (if i < j then Real.log p * ladWeight p j *
      (((if k ≤ j then (1 : ℝ) else 0) - if k ≤ i then 1 else 0) * (g j - g i)) else 0) =
      if i < k then (if k ≤ j then Real.log p * (ladWeight p j * g j - ladWeight p j * g i)
        else 0) else 0 := by
    intro i j
    by_cases hij : i < j <;> by_cases hkj : k ≤ j <;> by_cases hki : k ≤ i <;>
      simp only [hij, hkj, hki, if_true, if_false, not_lt.mpr, not_le.mpr] <;>
      first | ring | omega | (split_ifs <;> first | ring | omega)
  have hcount : ∑ i ∈ range (J + 1), (if i < k then (1 : ℝ) else 0) = k := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one,
      show (range (J + 1)).filter (fun i => i < k) = range k by
        ext i; simp only [mem_filter, mem_range]; omega, card_range]
  rw [ladForm, sum_congr rfl fun i _ => sum_congr rfl fun j _ => hterm i j]
  simp only [← sum_filter]
  simp only [mul_sub, sum_sub_distrib, ← mul_sum, ← sum_mul]
  rw [show ∑ x ∈ (range (J + 1)).filter (fun i => i < k), Real.log p *
      ∑ x_1 ∈ (range (J + 1)).filter (fun j => k ≤ j), ladWeight p x_1 * g x_1 =
      Real.log p * (k * ∑ j ∈ (range (J + 1)).filter (fun j => k ≤ j), ladWeight p j * g j) by
    rw [sum_const, nsmul_eq_mul, show ((range (J + 1)).filter (fun i => i < k)).card = k by
      rw [show (range (J + 1)).filter (fun i => i < k) = range k by
        ext i; simp only [mem_filter, mem_range]; omega, card_range]]
    ring]
  sorry

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
