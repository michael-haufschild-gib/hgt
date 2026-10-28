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
  have h0 : (0 : ℝ) ≤ (1 / (p : ℝ)) ^ (J - k + 1) := by positivity
  unfold ladCorr
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

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
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  generalize J - (k' + 1) + 1 = n
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr' : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have h1p : (1 : ℝ) - p ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp1)
  rw [pow_succ]
  simp only [r] at hr' ⊢
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

theorem ladForm_congr (J : ℕ) {f f' : ℕ → ℝ} (h : ∀ j ∈ range (J + 1), f j = f' j)
    (g : ℕ → ℝ) : ladForm p J f g = ladForm p J f' g :=
  sum_congr rfl fun i hi => sum_congr rfl fun j hj => by rw [h i hi, h j hj]

/-- Linearity in the first argument. -/
theorem ladForm_sum (J : ℕ) (s : Finset ℕ) (a : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) (g : ℕ → ℝ) :
    ladForm p J (fun j => ∑ k ∈ s, a k * φ k j) g = ∑ k ∈ s, a k * ladForm p J (φ k) g := by
  have h : ∀ i j, (if i < j then Real.log p * ladWeight p j *
      ((∑ k ∈ s, a k * φ k j - ∑ k ∈ s, a k * φ k i) * (g j - g i)) else 0) =
      ∑ k ∈ s, a k * (if i < j then Real.log p * ladWeight p j *
        ((φ k j - φ k i) * (g j - g i)) else 0) := by
    intro i j
    split_ifs
    · rw [← sum_sub_distrib, sum_mul, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    · simp
  simp only [ladForm, h, mul_sum]
  rw [sum_congr rfl fun i _ => sum_comm, sum_comm]

/-- The form of a step `1_{j ≥ k}`: `B(s_k, g) = log p (k G_k − T_k Σ_{i<k} g_i)`, with
`G_k = Σ_{j ≥ k} w_j g_j` and `T_k = Σ_{j ≥ k} w_j`. -/
theorem ladForm_step (J : ℕ) {k : ℕ} (hk : k ≤ J + 1) (g : ℕ → ℝ) :
    ladForm p J (fun j => if k ≤ j then 1 else 0) g =
      Real.log p * ((k : ℝ) * ∑ j ∈ Ico k (J + 1), ladWeight p j * g j -
        (∑ j ∈ Ico k (J + 1), ladWeight p j) * ∑ i ∈ range k, g i) := by
  have hterm : ∀ i ∈ range (J + 1), ∀ j ∈ range (J + 1),
      (if i < j then Real.log p * ladWeight p j *
        (((if k ≤ j then (1 : ℝ) else 0) - if k ≤ i then 1 else 0) * (g j - g i)) else 0) =
      if i < k then (if k ≤ j then Real.log p * (ladWeight p j * g j - g i * ladWeight p j)
        else 0) else 0 := by
    intro i _ j _
    split_ifs <;> first | (exfalso; omega) | ring
  rw [ladForm, sum_congr rfl fun i hi => sum_congr rfl fun j hj => hterm i hi j hj]
  have hIco : (range (J + 1)).filter (fun j => k ≤ j) = Ico k (J + 1) := by
    ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
  have hin : ∀ i, ∑ j ∈ range (J + 1), (if i < k then (if k ≤ j then
      Real.log p * (ladWeight p j * g j - g i * ladWeight p j) else 0) else 0) =
      if i < k then Real.log p * (∑ j ∈ Ico k (J + 1), ladWeight p j * g j -
        g i * ∑ j ∈ Ico k (J + 1), ladWeight p j) else 0 := by
    intro i
    by_cases hik : i < k
    · simp only [hik, if_true]
      rw [← sum_filter, hIco, ← mul_sum, sum_sub_distrib, ← mul_sum]
    · simp only [hik, if_false, sum_const_zero]
  rw [sum_congr rfl fun i _ => hin i, ← sum_filter,
    show (range (J + 1)).filter (fun i => i < k) = range k by
      ext i; simp only [mem_filter, mem_range]; omega,
    ← mul_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_mul]
  ring

/-- The form of a point `1_{j = m}`:
`B(e_m, g) = log p (w_m Σ_{i<m}(g_m − g_i) − Σ_{m<j≤J} w_j (g_j − g_m))`. -/
theorem ladForm_single (J : ℕ) {m : ℕ} (hm : m ≤ J) (g : ℕ → ℝ) :
    ladForm p J (fun j => if j = m then 1 else 0) g =
      Real.log p * (ladWeight p m * ∑ i ∈ range m, (g m - g i) -
        ∑ j ∈ Ioc m J, ladWeight p j * (g j - g m)) := by
  have hterm : ∀ i ∈ range (J + 1), ∀ j ∈ range (J + 1),
      (if i < j then Real.log p * ladWeight p j *
        (((if j = m then (1 : ℝ) else 0) - if i = m then 1 else 0) * (g j - g i)) else 0) =
      (if j = m then (if i < m then Real.log p * (ladWeight p m * (g m - g i)) else 0) else 0) -
        (if i = m then (if m < j then Real.log p * (ladWeight p j * (g j - g m)) else 0)
          else 0) := by
    intro i _ j _
    split_ifs <;> first | (exfalso; omega) | (subst_vars; ring)
  rw [ladForm, sum_congr rfl fun i hi => sum_congr rfl fun j hj => hterm i hi j hj]
  have hmJ : m ∈ range (J + 1) := mem_range.mpr (by omega)
  have h1 : ∑ i ∈ range (J + 1), ∑ j ∈ range (J + 1), (if j = m then (if i < m then
      Real.log p * (ladWeight p m * (g m - g i)) else 0) else 0) =
      ∑ i ∈ range (J + 1), (if i < m then Real.log p * (ladWeight p m * (g m - g i)) else 0) := by
    simp only [sum_ite_eq', hmJ, if_true]
  have h2 : ∑ i ∈ range (J + 1), ∑ j ∈ range (J + 1), (if i = m then (if m < j then
      Real.log p * (ladWeight p j * (g j - g m)) else 0) else 0) =
      ∑ j ∈ range (J + 1), (if m < j then Real.log p * (ladWeight p j * (g j - g m)) else 0) := by
    rw [sum_comm]
    simp only [sum_ite_eq', hmJ, if_true]
  simp only [sum_sub_distrib]
  rw [h1, h2, ← sum_filter, show (range (J + 1)).filter (fun i => i < m) = range m by
      ext i; simp only [mem_filter, mem_range]; omega, ← sum_filter,
    show (range (J + 1)).filter (fun j => m < j) = Ioc m J by
      ext j; simp only [mem_filter, mem_range, mem_Ioc]; omega, ← mul_sum, ← mul_sum, ← mul_sum,
    mul_sub, sum_sub_distrib]

/-! ### 4. The modes are orthogonal eigenvectors -/

/-- For `k ≥ 1`, `ψ_k = s_k − c_k e_{k−1}`. -/
theorem ladMode_eq {J k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    ladMode p J k j = (if k ≤ j then 1 else 0) + (-ladCorr p J k) * (if j = k - 1 then 1 else 0) := by
  unfold ladMode
  rw [if_neg (by omega)]
  by_cases h1 : k ≤ j
  · rw [if_pos h1, if_pos h1, if_neg (by omega)]; ring
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : j + 1 = k
    · rw [if_pos h2, if_pos (by omega)]; ring
    · rw [if_neg h2, if_neg (by omega)]; ring

/-- `⟨ψ_k, g⟩ = G_k − c_k w_{k−1} g_{k−1}` for `1 ≤ k ≤ J`. -/
theorem ladInner_ladMode (J : ℕ) {k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) (g : ℕ → ℝ) :
    ladInner p J (ladMode p J k) g = ∑ j ∈ Ico k (J + 1), ladWeight p j * g j -
      ladCorr p J k * ladWeight p (k - 1) * g (k - 1) := by
  rw [ladInner, sum_congr rfl fun j _ => by rw [ladMode_eq hk j]]
  have e : ∀ j, ladWeight p j * (((if k ≤ j then (1 : ℝ) else 0) +
      (-ladCorr p J k) * (if j = k - 1 then 1 else 0)) * g j) =
      (if k ≤ j then ladWeight p j * g j else 0) -
        ladCorr p J k * (if j = k - 1 then ladWeight p j * g j else 0) := fun j => by
    split_ifs <;> ring
  rw [sum_congr rfl fun j _ => e j, sum_sub_distrib, ← mul_sum, ← sum_filter,
    show (range (J + 1)).filter (fun j => k ≤ j) = Ico k (J + 1) by
      ext j; simp only [mem_filter, mem_range, mem_Ico]; omega,
    sum_ite_eq' (range (J + 1)) (k - 1), if_pos (mem_range.mpr (by omega))]
  ring

theorem sum_Ico_ladWeight (hp : 1 < p) {J k : ℕ} (hk : 1 ≤ k) (hkJ : k ≤ J) :
    ∑ j ∈ Ico k (J + 1), ladWeight p j = ladWeight p (k - 1) * ladCorr p J k := by
  rw [← sum_ladWeight_ge hp hk hkJ, ← sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range, mem_Ico]; omega

/-- **The modes are eigenvectors**: `B(ψ_k, g) = λ_k ⟨ψ_k, g⟩` for every `g`. -/
theorem ladForm_ladMode (hp : 1 < p) {J k : ℕ} (hkJ : k ≤ J) (g : ℕ → ℝ) :
    ladForm p J (ladMode p J k) g = ladEig p J k * ladInner p J (ladMode p J k) g := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [ladEig, if_pos rfl, zero_mul, ladForm]
    exact sum_eq_zero fun i _ => sum_eq_zero fun j _ => by simp [ladMode]
  have hk1 : 1 ≤ k := hk
  rw [show ladMode p J k = fun j => (if k ≤ j then 1 else 0) +
      (-ladCorr p J k) * (if j = k - 1 then 1 else 0) from funext (ladMode_eq hk1),
    ladForm_add_smul, ladForm_step J (by omega), ladForm_single J (by omega),
    ← show ladMode p J k = fun j => (if k ≤ j then 1 else 0) +
      (-ladCorr p J k) * (if j = k - 1 then 1 else 0) from funext (ladMode_eq hk1),
    ladInner_ladMode J hk1 hkJ, sum_Ico_ladWeight hp hk1 hkJ, ladEig, if_neg (by omega)]
  have hlo : ∑ i ∈ range k, g i = ∑ i ∈ range (k - 1), g i + g (k - 1) := by
    conv_lhs => rw [show k = k - 1 + 1 by omega]
    exact sum_range_succ g (k - 1)
  have hsub : ∑ i ∈ range (k - 1), (g (k - 1) - g i) = (k - 1 : ℕ) * g (k - 1) -
      ∑ i ∈ range (k - 1), g i := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hIoc : ∑ j ∈ Ioc (k - 1) J, ladWeight p j * (g j - g (k - 1)) =
      ∑ j ∈ Ico k (J + 1), ladWeight p j * g j - g (k - 1) * ∑ j ∈ Ico k (J + 1), ladWeight p j := by
    rw [show Ioc (k - 1) J = Ico k (J + 1) by ext j; simp only [mem_Ioc, mem_Ico]; omega,
      mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [hlo, hsub, hIoc, sum_Ico_ladWeight hp hk1 hkJ]
  push_cast [Nat.cast_sub hk1]
  ring

/-- For `k < l`, `ψ_k = 1` on the support of `ψ_l`. -/
theorem ladMode_mul_ladMode {J k l : ℕ} (hkl : k < l) (j : ℕ) :
    ladMode p J k j * ladMode p J l j = ladMode p J l j := by
  unfold ladMode
  rw [if_neg (show l ≠ 0 by omega)]
  by_cases hk0 : k = 0
  · simp [hk0]
  rw [if_neg hk0]
  split_ifs <;> first | (exfalso; omega) | ring

theorem ladInner_comm (J : ℕ) (f g : ℕ → ℝ) : ladInner p J f g = ladInner p J g f :=
  sum_congr rfl fun _ _ => by ring

/-- `⟨1, ψ_l⟩ = 0` for `1 ≤ l ≤ J`. -/
theorem ladInner_one_ladMode (hp : 1 < p) {J l : ℕ} (hl : 1 ≤ l) (hlJ : l ≤ J) :
    ladInner p J (ladMode p J l) (fun _ => 1) = 0 := by
  rw [ladInner_ladMode J hl hlJ]
  simp only [mul_one]
  rw [sum_Ico_ladWeight hp hl hlJ]
  ring

/-- **Orthogonality** of distinct modes. -/
theorem ladInner_ladMode_ladMode (hp : 1 < p) {J k l : ℕ} (hk : k ≤ J) (hl : l ≤ J) (hkl : k ≠ l) :
    ladInner p J (ladMode p J k) (ladMode p J l) = 0 := by
  wlog h : k < l generalizing k l
  · rw [ladInner_comm]; exact this hl hk (Ne.symm hkl) (by omega)
  rw [ladInner, sum_congr rfl fun j _ => by rw [ladMode_mul_ladMode h j]]
  have := ladInner_one_ladMode hp (show 1 ≤ l by omega) hl
  rw [ladInner] at this
  rw [← this]
  exact sum_congr rfl fun j _ => by ring

theorem ladInner_ladMode_self_pos (hp : 1 < p) {J k : ℕ} (hk : k ≤ J) :
    0 < ladInner p J (ladMode p J k) (ladMode p J k) := by
  have hk' : k ∈ range (J + 1) := mem_range.mpr (by omega)
  have h1 : ladMode p J k k = 1 := by unfold ladMode; split_ifs <;> first | rfl | (exfalso; omega)
  refine lt_of_lt_of_le ?_ (single_le_sum (f := fun j => ladWeight p j *
    (ladMode p J k j * ladMode p J k j)) (fun j _ => mul_nonneg (ladWeight_pos (by omega) j).le
      (mul_self_nonneg _)) hk')
  simp only [h1, mul_one]
  exact ladWeight_pos (by omega) k

/-! ### 5. Completeness and the expansion -/

/-- **Completeness**: a vector orthogonal to every mode vanishes on the ladder. -/
theorem eq_zero_of_ladInner_ladMode (hp : 1 < p) {J : ℕ} {r : ℕ → ℝ}
    (h : ∀ k ∈ range (J + 1), ladInner p J (ladMode p J k) r = 0) :
    ∀ j ∈ range (J + 1), r j = 0 := by
  set S : ℕ → ℝ := fun k => ∑ j ∈ Ico k (J + 1), ladWeight p j * r j
  have hS0 : S 0 = 0 := by
    have h0 : ∀ j, ladMode p J 0 j = 1 := fun j => by simp [ladMode]
    have := h 0 (mem_range.mpr (by omega))
    rw [ladInner] at this
    simp only [h0, one_mul] at this
    simp only [S]
    rw [← range_eq_Ico]
    exact this
  -- `S_k = 0` and `r_j = 0` below `k`, by induction
  have key : ∀ k, k ≤ J → S k = 0 ∧ ∀ j < k, r j = 0 := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨hS0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ k ih =>
      intro hk
      obtain ⟨hSk, hr⟩ := ih (by omega)
      have hmode := h (k + 1) (mem_range.mpr (by omega))
      rw [ladInner_ladMode J (by omega) hk, Nat.add_sub_cancel] at hmode
      have hsplit : S k = ladWeight p k * r k + S (k + 1) := by
        simp only [S]
        rw [sum_eq_sum_Ico_succ_bot (by omega)]
      have hc := ladCorr_pos hp J (k + 1)
      have hw := ladWeight_pos (show 0 < p by omega) k
      have hrk : ladWeight p k * r k = 0 := by
        have : ladWeight p k * r k * (1 + ladCorr p J (k + 1)) = 0 := by
          simp only [S] at hSk hsplit
          linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · linarith
      have hrk' : r k = 0 := by
        rcases mul_eq_zero.mp hrk with h' | h'
        · linarith
        · exact h'
      refine ⟨by simp only [S] at hSk hsplit ⊢; linarith, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h' | h'
      · exact hr j h'
      · rw [h']; exact hrk'
  intro j hj
  have hjJ : j ≤ J := by have := mem_range.mp hj; omega
  obtain ⟨hSJ, hr⟩ := key J le_rfl
  rcases Nat.lt_or_ge j J with h' | h'
  · exact hr j h'
  · have hjJ' : j = J := by omega
    subst hjJ'
    have : S j = ladWeight p j * r j := by
      simp only [S]
      rw [show Ico j (j + 1) = {j} from Nat.Ico_succ_singleton j, sum_singleton]
    have hw := ladWeight_pos (show 0 < p by omega) j
    rw [this] at hSJ
    rcases mul_eq_zero.mp hSJ with h'' | h''
    · linarith
    · exact h''

/-- The coefficient `⟨g, ψ_k⟩/‖ψ_k‖²`. -/
def ladCoeff (p J k : ℕ) (g : ℕ → ℝ) : ℝ :=
  ladInner p J (ladMode p J k) g / ladInner p J (ladMode p J k) (ladMode p J k)

/-- **The expansion** `g = Σ_k ⟨g, ψ_k⟩/‖ψ_k‖² ψ_k` on the ladder. -/
theorem ladExpansion (hp : 1 < p) (J : ℕ) (g : ℕ → ℝ) :
    ∀ j ∈ range (J + 1), g j = ∑ k ∈ range (J + 1), ladCoeff p J k g * ladMode p J k j := by
  have h := eq_zero_of_ladInner_ladMode hp (J := J)
    (r := fun j => g j - ∑ k ∈ range (J + 1), ladCoeff p J k g * ladMode p J k j) (fun l hl => ?_)
  · exact fun j hj => by have := h j hj; linarith
  have hlJ : l ≤ J := by have := mem_range.mp hl; omega
  have hlin : ladInner p J (ladMode p J l)
      (fun j => g j - ∑ k ∈ range (J + 1), ladCoeff p J k g * ladMode p J k j) =
      ladInner p J (ladMode p J l) g -
        ∑ k ∈ range (J + 1), ladCoeff p J k g * ladInner p J (ladMode p J l) (ladMode p J k) := by
    simp only [ladInner, mul_sub, sum_sub_distrib, mul_sum]
    rw [sum_comm]
    congr 1
    exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring
  rw [hlin, sum_eq_single l (fun k hk hkl => by
    rw [ladInner_ladMode_ladMode hp hlJ (by have := mem_range.mp hk; omega) (Ne.symm hkl),
      mul_zero]) (fun h' => absurd hl h'), ladCoeff,
    div_mul_cancel₀ _ (ladInner_ladMode_self_pos hp hlJ).ne']
  ring

/-- **Parseval**: `⟨g, g⟩ = Σ_k ⟨g, ψ_k⟩²/‖ψ_k‖²`. -/
theorem ladInner_self_eq (hp : 1 < p) (J : ℕ) (g : ℕ → ℝ) :
    ladInner p J g g = ∑ k ∈ range (J + 1), ladCoeff p J k g * ladInner p J (ladMode p J k) g := by
  have hexp := ladExpansion hp J g
  calc ladInner p J g g = ∑ j ∈ range (J + 1), ladWeight p j *
        ((∑ k ∈ range (J + 1), ladCoeff p J k g * ladMode p J k j) * g j) :=
        sum_congr rfl fun j hj => by rw [← hexp j hj]
    _ = _ := by
        simp only [ladInner, sum_mul, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun j _ => by ring

/-- **The energy expansion**: `E(g) = Σ_k λ_k ⟨g, ψ_k⟩²/‖ψ_k‖²`. -/
theorem ladForm_self_eq (hp : 1 < p) (J : ℕ) (g : ℕ → ℝ) :
    ladForm p J g g = ∑ k ∈ range (J + 1),
      ladEig p J k * (ladCoeff p J k g * ladInner p J (ladMode p J k) g) := by
  rw [ladForm_congr J (ladExpansion hp J g) g, ladForm_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [ladForm_ladMode hp (by have := mem_range.mp hk; omega)]
  ring

theorem ladInner_ladMode_eq_coeff (hp : 1 < p) {J k : ℕ} (hk : k ≤ J) (g : ℕ → ℝ) :
    ladInner p J (ladMode p J k) g = ladCoeff p J k g * ladInner p J (ladMode p J k) (ladMode p J k) := by
  rw [ladCoeff, div_mul_cancel₀ _ (ladInner_ladMode_self_pos hp hk).ne']

/-- **Coefficient Parseval**: `Σ_j w_j (Σ_k z_k ψ_k(j))² = Σ_k z_k² ‖ψ_k‖²`. -/
theorem sum_ladWeight_sq_sum (hp : 1 < p) (J : ℕ) (z : ℕ → ℝ) :
    ∑ j ∈ range (J + 1), ladWeight p j * (∑ k ∈ range (J + 1), z k * ladMode p J k j) ^ 2 =
      ∑ k ∈ range (J + 1), z k ^ 2 * ladInner p J (ladMode p J k) (ladMode p J k) := by
  have e : ∀ j, ladWeight p j * (∑ k ∈ range (J + 1), z k * ladMode p J k j) ^ 2 =
      ∑ k ∈ range (J + 1), ∑ l ∈ range (J + 1),
        z k * z l * (ladWeight p j * (ladMode p J k j * ladMode p J l j)) := fun j => by
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun k _ => by rw [mul_sum]; exact sum_congr rfl fun l _ => by ring
  rw [sum_congr rfl fun j _ => e j, sum_comm]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_comm, sum_eq_single k]
  · rw [← mul_sum, sq]; rfl
  · intro l hl hlk
    rw [← mul_sum, show ∑ j ∈ range (J + 1), ladWeight p j * (ladMode p J k j * ladMode p J l j) =
      ladInner p J (ladMode p J k) (ladMode p J l) from rfl,
      ladInner_ladMode_ladMode hp (by have := mem_range.mp hk; omega)
        (by have := mem_range.mp hl; omega) (Ne.symm hlk), mul_zero]
  · exact fun h => absurd hk h

/-- `λ_k ≤ log p (k + 1/(p − 1))`. -/
theorem ladEig_le (hp : 1 < p) (J k : ℕ) :
    ladEig p J k ≤ Real.log p * (k + 1 / ((p : ℝ) - 1)) := by
  unfold ladEig
  have hl := Real.log_natCast_nonneg p
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  split_ifs with hk
  · subst hk; simp only [Nat.cast_zero, zero_add]
    exact mul_nonneg hl (div_nonneg zero_le_one (by linarith))
  · exact mul_le_mul_of_nonneg_left (by linarith [ladCorr_le hp J k]) hl

/-- `λ_k ≥ log p (k + 1/(p − 1)) − log p · p^{−(J−k+1)}/(p − 1)` for `k ≥ 1`. -/
theorem ladEig_ge (hp : 1 < p) {J k : ℕ} (hk : 1 ≤ k) :
    Real.log p * (k + 1 / ((p : ℝ) - 1)) -
      Real.log p * ((1 / (p : ℝ)) ^ (J - k + 1) / ((p : ℝ) - 1)) ≤ ladEig p J k := by
  unfold ladEig ladCorr
  rw [if_neg (by omega)]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have : (1 - (1 / (p : ℝ)) ^ (J - k + 1)) / ((p : ℝ) - 1) =
      1 / ((p : ℝ) - 1) - (1 / (p : ℝ)) ^ (J - k + 1) / ((p : ℝ) - 1) := by ring
  rw [this]; ring_nf; exact le_rfl

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
