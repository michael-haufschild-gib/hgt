import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheMatchedPrimePlaceHasAHodgeIndexOnTheClasses

/-!
# The valuation tower is exactly solvable

On the `p`-adic classes the prime place, matched against the archimedean counterterm, is the
**valuation tower operator** (normalized class coordinates `b_j`, `q = p^{−1/2}`)

    (H_p b)_i = (i log p + γ_p + log p) b_i − log p Σ_j q^{|i − j|} b_j,

the valuation potential `i log p` plus the tower form (`TheArchimedeanPlacePaysTheTowerDeficit`).
In the pole gauge `b_j = q^j y_j` it is `γ` plus `log p` times the Dirichlet form
`Σ_{i < j} p^{−j}(y_i − y_j)²` of the measure `μ_j = p^{−j}`, and it is diagonalized by the
valuation filtration:

* **Exact eigenvectors** (`towerOp_pole`, `towerOp_step`): the pole profile `q^j` has eigenvalue `γ`;
  for `k ≥ 1` the valuation step `y = 1_{j ≥ k} − (p − 1)^{−1} 1_{j = k − 1}` has eigenvalue
  `γ_p + k log p`. The spectrum is `{γ} ∪ {γ_p + k log p : k ≥ 1}`: the first excitation costs
  `p log p/(p − 1)` above the pole, the later ones `log p` each.
* **The sharp gap at every depth** (`sum_cross_add_sharpGap_le_valuation`): the row slack of the
  valuation Gram, dropped in `TheMatchedPrimePlaceHasAHodgeIndexOnTheClasses`, is the mass of the
  deeper classes; kept, it completes the tower to total mass `p/(p − 1)` times the top mass.
* **The sharp Hodge index on the classes** (`eventually_atomicWeilForm_classCombination_sharpGap_le`):
  eventually in `M`, on every class combination of depth `≤ J`,
  `P_M(x) + (p/(p − 1) − η) log p |x|² ≤ (log M − γ + η)|x|² + (log p/|w_0|²) ℓ(x)²`; on the polar
  hyperplane the prime form lies `p log p/(p − 1)` below the pole, the first eigenvalue gap of
  `H_p`, uniformly in the depth.

At `p = 2` the gap is `2 log 2`, the observed distance between the two top eigenvalues of the atomic
prime form: the second eigenvector of the prime place is the first excitation of the `2`-adic tower.
-/

noncomputable section

open Filter Topology Finset Matrix

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticIntersectionTheory GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticLorentzianGeometry

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. Exact eigenvectors on the infinite tower -/

/-- The valuation tower operator in the pole gauge, as a generator:
`(L y)_i = Σ_{j ≤ i} (y_i − y_j) + Σ_{j > i} p^{−(j − i)} (y_i − y_j)`. In normalized coordinates
`H_p = γ + log p · L` (`towerOp_pole`, `towerOp_step`). The value below is `(H_p (q^· y))_i/q^i`. -/
def towerGaugeOp (p : ℕ) (y : ℕ → ℝ) (i : ℕ) : ℝ :=
  ((i : ℝ) * Real.log p + localEuler p + Real.log p) * y i -
    Real.log p * (∑ j ∈ range (i + 1), y j + ∑' k : ℕ, y (i + 1 + k) / (p : ℝ) ^ (k + 1))

variable {p : ℕ}

/-- `Σ_{k ≥ 0} p^{−(k+1)} = 1/(p − 1)`. -/
theorem tsum_inv_pow_succ (hp : 1 < (p : ℝ)) :
    HasSum (fun k : ℕ => 1 / (p : ℝ) ^ (k + 1)) (1 / ((p : ℝ) - 1)) := by
  have h0 : (0 : ℝ) ≤ 1 / p := by positivity
  have h1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 / (p : ℝ))
  have e1 : (fun k : ℕ => 1 / (p : ℝ) ^ (k + 1)) = fun i => 1 / (p : ℝ) * (1 / (p : ℝ)) ^ i := by
    funext k; rw [pow_succ, _root_.one_div_pow, one_div_mul_one_div, mul_comm]
  have e2 : 1 / ((p : ℝ) - 1) = 1 / (p : ℝ) * (1 - 1 / (p : ℝ))⁻¹ := by
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    have : (p : ℝ) ≠ 0 := by linarith
    field_simp
  rw [e1, e2]
  exact h

/-- `Σ_{t < d} p^{−(t+1)} = (1 − p^{−d})/(p − 1)`. -/
theorem sum_range_inv_pow_succ (hp : 1 < (p : ℝ)) (d : ℕ) :
    ∑ t ∈ range d, 1 / (p : ℝ) ^ (t + 1) = (1 - 1 / (p : ℝ) ^ d) / ((p : ℝ) - 1) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.sum_range_succ, ih, pow_succ]; field_simp; ring

/-- The geometric tail from `d` on: `Σ_{t ≥ d} p^{−(t+1)} = p^{−d}/(p − 1)`. -/
theorem hasSum_tail_inv_pow_succ (hp : 1 < (p : ℝ)) (d : ℕ) :
    HasSum (fun t : ℕ => if d ≤ t then 1 / (p : ℝ) ^ (t + 1) else 0)
      (1 / (p : ℝ) ^ d / ((p : ℝ) - 1)) := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hg := (hasSum_nat_add_iff' d).mpr (tsum_inv_pow_succ hp)
  rw [← hasSum_nat_add_iff' d, sum_eq_zero fun i hi => if_neg (by
    have := mem_range.mp hi; omega), sub_zero]
  have hf : (fun n : ℕ => if d ≤ n + d then 1 / (p : ℝ) ^ (n + d + 1) else 0) =
      fun n => 1 / (p : ℝ) ^ (n + d + 1) := funext fun n => if_pos (by omega)
  rw [hf]
  rw [sum_range_inv_pow_succ hp] at hg
  have e : 1 / ((p : ℝ) - 1) - (1 - 1 / (p : ℝ) ^ d) / ((p : ℝ) - 1) =
      1 / (p : ℝ) ^ d / ((p : ℝ) - 1) := by field_simp; ring
  rwa [e] at hg

/-- **The pole is the ground state**: `H_p q^· = γ q^·`, i.e. `L 1 = 0`. -/
theorem towerOp_pole (hp : 1 < (p : ℝ)) (i : ℕ) :
    towerGaugeOp p (fun _ => 1) i = γ := by
  unfold towerGaugeOp localEuler
  rw [(tsum_inv_pow_succ hp).tsum_eq]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- The `k`-th valuation step `y = 1_{j ≥ k} − (p − 1)^{−1} 1_{j = k − 1}`. -/
def valuationStep (p k : ℕ) (j : ℕ) : ℝ :=
  if k ≤ j then 1 else if j + 1 = k then -(1 / ((p : ℝ) - 1)) else 0

/-- **The valuation steps are eigenvectors**: `H_p(q^· y_k) = (γ_p + k log p) q^· y_k` for `k ≥ 1`. -/
theorem towerOp_step (hp : 1 < (p : ℝ)) {k : ℕ} (hk : 1 ≤ k) (i : ℕ) :
    towerGaugeOp p (valuationStep p k) i =
      (localEuler p + k * Real.log p) * valuationStep p k i := by
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hgeo := tsum_inv_pow_succ hp
  unfold towerGaugeOp
  rcases lt_trichotomy (i + 1) k with h | h | h
  · -- below the step: every term vanishes except the tail, which cancels
    have hyi : valuationStep p k i = 0 := by
      unfold valuationStep; rw [if_neg (by omega), if_neg (by omega)]
    have hlow : ∑ j ∈ range (i + 1), valuationStep p k j = 0 :=
      sum_eq_zero fun j hj => by
        have := mem_range.mp hj
        unfold valuationStep; rw [if_neg (by omega), if_neg (by omega)]
    -- the tail: `−(p−1)^{−1} p^{−(k−1−i)} + Σ_{j ≥ k} p^{−(j−i)} = 0`
    set d := k - (i + 1) with hd
    have htail : HasSum (fun t : ℕ => valuationStep p k (i + 1 + t) / (p : ℝ) ^ (t + 1)) 0 := by
      -- split at `t = d − 1`
      have hfun : (fun t : ℕ => valuationStep p k (i + 1 + t) / (p : ℝ) ^ (t + 1)) =
          fun t => (if t + 1 = d then -(1 / ((p : ℝ) - 1)) / (p : ℝ) ^ (t + 1) else 0) +
            (if d ≤ t then 1 / (p : ℝ) ^ (t + 1) else 0) := by
        funext t
        unfold valuationStep
        by_cases h1 : k ≤ i + 1 + t
        · rw [if_pos h1, if_neg (by omega), if_pos (by omega)]; ring
        · rw [if_neg h1]
          by_cases h2 : i + 1 + t + 1 = k
          · rw [if_pos h2, if_pos (by omega), if_neg (by omega)]; ring
          · rw [if_neg h2, if_neg (by omega), if_neg (by omega)]; ring
      rw [hfun]
      have hA : HasSum (fun t : ℕ => if t + 1 = d then -(1 / ((p : ℝ) - 1)) /
          (p : ℝ) ^ (t + 1) else 0) (-(1 / ((p : ℝ) - 1)) / (p : ℝ) ^ d) := by
        have hd1 : 1 ≤ d := by omega
        have h := hasSum_ite_eq (d - 1) (-(1 / ((p : ℝ) - 1)) / (p : ℝ) ^ d)
        refine h.congr_fun fun t => ?_
        by_cases ht : t + 1 = d
        · rw [if_pos ht, if_pos (by omega), ht]
        · rw [if_neg ht, if_neg (by omega)]
      have hB := hasSum_tail_inv_pow_succ hp d
      have hsum := hA.add hB
      have e : -(1 / ((p : ℝ) - 1)) / (p : ℝ) ^ d + 1 / (p : ℝ) ^ d / ((p : ℝ) - 1) = 0 := by ring
      rwa [e] at hsum
    rw [htail.tsum_eq, hlow, hyi]
    ring
  · -- the step itself, `i = k − 1`
    have hyi : valuationStep p k i = -(1 / ((p : ℝ) - 1)) := by
      unfold valuationStep; rw [if_neg (by omega), if_pos h]
    have hlow : ∑ j ∈ range (i + 1), valuationStep p k j = -(1 / ((p : ℝ) - 1)) := by
      rw [Finset.sum_range_succ, sum_eq_zero fun j hj => by
        have := mem_range.mp hj
        unfold valuationStep; rw [if_neg (by omega), if_neg (by omega)], hyi, zero_add]
    have htail : HasSum (fun t : ℕ => valuationStep p k (i + 1 + t) / (p : ℝ) ^ (t + 1))
        (1 / ((p : ℝ) - 1)) := by
      refine hgeo.congr_fun fun t => ?_
      unfold valuationStep
      rw [if_pos (by omega)]
    rw [htail.tsum_eq, hlow, hyi]
    have hik : (i : ℝ) + 1 = k := by exact_mod_cast h
    rw [← hik]
    ring
  · -- above the step
    have hyi : valuationStep p k i = 1 := by unfold valuationStep; rw [if_pos (by omega)]
    have hlow : ∑ j ∈ range (i + 1), valuationStep p k j =
        ((i : ℝ) + 1 - k) - 1 / ((p : ℝ) - 1) := by
      have hsplit := sum_range_add_sum_Ico (fun j => valuationStep p k j)
        (show k ≤ i + 1 by omega)
      rw [← hsplit]
      have hbelow : ∑ j ∈ range k, valuationStep p k j = -(1 / ((p : ℝ) - 1)) := by
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Finset.sum_range_succ, sum_eq_zero fun j hj => by
          have := mem_range.mp hj
          unfold valuationStep; rw [if_neg (by omega), if_neg (by omega)], zero_add]
        unfold valuationStep; rw [if_neg (by omega), if_pos rfl]
      have habove : ∑ j ∈ Ico k (i + 1), valuationStep p k j = (i : ℝ) + 1 - k := by
        rw [sum_congr rfl fun j hj => by
          have := (mem_Ico.mp hj).1
          unfold valuationStep; rw [if_pos this], sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hbelow, habove]; ring
    have htail : HasSum (fun t : ℕ => valuationStep p k (i + 1 + t) / (p : ℝ) ^ (t + 1))
        (1 / ((p : ℝ) - 1)) := by
      refine hgeo.congr_fun fun t => ?_
      unfold valuationStep
      rw [if_pos (by omega)]
    rw [htail.tsum_eq, hlow, hyi]
    unfold localEuler
    ring

/-! ### 2. The sharp gap: keep the mass of the deeper classes -/

variable {J : ℕ} {m : ℕ → ℝ}

/-- Descending masses: the tail of the tower plus the virtual tail beyond `j + K` is at most
`m_j/(p − 1)`. -/
theorem sum_range_shift_add_tail_le (hp : 1 < (p : ℝ)) (_hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m (j + 1) ≤ m j / p) (K : ℕ) :
    ∀ j, ∑ k ∈ range K, m (j + 1 + k) + m (j + K) / ((p : ℝ) - 1) ≤ m j / ((p : ℝ) - 1) := by
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  induction K with
  | zero => intro j; simp
  | succ K ih =>
    intro j
    rw [Finset.sum_range_succ']
    have h1 := ih (j + 1)
    have h2 := hm j
    simp only [add_zero]
    rw [sum_congr rfl fun k _ => by rw [show j + 1 + (k + 1) = j + 1 + 1 + k by ring],
      show j + (K + 1) = j + 1 + K by ring]
    calc ∑ k ∈ range K, m (j + 1 + 1 + k) + m (j + 1) + m (j + 1 + K) / ((p : ℝ) - 1)
        = (∑ k ∈ range K, m (j + 1 + 1 + k) + m (j + 1 + K) / ((p : ℝ) - 1)) + m (j + 1) := by
          ring
      _ ≤ m (j + 1) / ((p : ℝ) - 1) + m (j + 1) := add_le_add h1 le_rfl
      _ = m (j + 1) * p / ((p : ℝ) - 1) := by field_simp; ring
      _ ≤ m j / p * p / ((p : ℝ) - 1) := by gcongr
      _ = m j / ((p : ℝ) - 1) := by field_simp

/-- **The row slack of the valuation Gram is the deeper mass**: every row sum is at most
`−m_J/(p − 1)`. -/
theorem valuationGram_mulVec_one_le_tail (hp : 1 < (p : ℝ)) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m (j + 1) ≤ m j / p) (j : Fin (J + 1)) :
    (valuationGram p J m *ᵥ fun _ => (1 : ℝ)) j ≤ -(m J / ((p : ℝ) - 1)) := by
  have hj : (j : ℕ) ≤ J := Nat.lt_succ_iff.mp j.2
  simp only [mulVec, dotProduct, mul_one, valuationGram]
  set f : ℕ → ℝ := fun i => if i = (j : ℕ) then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)))
    else m (max (j : ℕ) i) with hf
  have hrw : ∑ x : Fin (J + 1), (if j = x then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)))
      else m (max (j : ℕ) x)) = ∑ i ∈ range (J + 1), f i := by
    rw [← Fin.sum_univ_eq_sum_range f]
    refine sum_congr rfl fun x _ => ?_
    simp only [hf]
    by_cases h : j = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'.symm))]
  rw [hrw, ← sum_range_add_sum_Ico f (by omega : (j : ℕ) ≤ J + 1),
    sum_eq_sum_Ico_succ_bot (by omega : (j : ℕ) < J + 1), sum_Ico_eq_sum_range]
  have hlow : ∑ i ∈ range (j : ℕ), f i = (j : ℝ) * m j := by
    have h : ∀ i ∈ range (j : ℕ), f i = m j := fun i hi => by
      have hi' : i < (j : ℕ) := mem_range.mp hi
      simp only [hf, if_neg hi'.ne, max_eq_left hi'.le]
    rw [sum_congr rfl h, sum_const, card_range, nsmul_eq_mul]
  have hhigh : ∑ k ∈ range (J + 1 - ((j : ℕ) + 1)), f ((j : ℕ) + 1 + k) =
      ∑ k ∈ range (J + 1 - ((j : ℕ) + 1)), m ((j : ℕ) + 1 + k) :=
    sum_congr rfl fun k _ => by
      simp only [hf, if_neg (by omega : (j : ℕ) + 1 + k ≠ j), max_eq_right (by omega :
        (j : ℕ) ≤ (j : ℕ) + 1 + k)]
  have htail := sum_range_shift_add_tail_le hp hm0 hm (J + 1 - ((j : ℕ) + 1)) j
  rw [show (j : ℕ) + (J + 1 - ((j : ℕ) + 1)) = J by omega] at htail
  rw [hlow, hhigh]
  simp only [hf, if_pos rfl]
  have : m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) = (j : ℝ) * m j + m j / ((p : ℝ) - 1) := by ring
  linarith

/-- **The valuation inequality with the complete tower.** With `S̃ = Σ_{j ≤ J} m_j + m_J/(p − 1)`,
`Σ_{j ≠ j'} a_j a_{j'} m_{max} + (S̃ Σ m_j a_j² − (Σ m_j a_j)²)/m_0 ≤ Σ_j a_j² m_j (j + 1/(p − 1))`. -/
theorem sum_cross_add_sharpGap_le_valuation (hp : 1 < (p : ℝ)) (hm0 : ∀ j, 0 ≤ m j)
    (hm : ∀ j, m (j + 1) ≤ m j / p) (htop : 0 < m 0) (a : Fin (J + 1) → ℝ) :
    ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        (if j = j' then 0 else a j * a j' * m (max (j : ℕ) j')) +
      (((∑ j : Fin (J + 1), m j) + m J / ((p : ℝ) - 1)) * ∑ j : Fin (J + 1), m j * a j ^ 2 -
          (∑ j : Fin (J + 1), m j * a j) ^ 2) / m 0 ≤
      ∑ j : Fin (J + 1), a j ^ 2 * (m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) := by
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  set G := valuationGram p J m
  have hG := valuationGram_isSymm (p := p) (J := J) (m := m)
  have hid := sum_rowSum_mul_sq_sub_qf hG a
  -- the row slack
  have hrow : ∑ j, rowSum G j * a j ^ 2 ≤ -(m J / ((p : ℝ) - 1)) * ∑ j, a j ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
      (valuationGram_mulVec_one_le_tail hp hm0 hm j) (sq_nonneg _)
  -- `Σ a_j² ≥ Σ (m_j/m_0) a_j²`
  have hmass : (m J / ((p : ℝ) - 1)) * (∑ j : Fin (J + 1), m j * a j ^ 2) / m 0 ≤
      (m J / ((p : ℝ) - 1)) * ∑ j : Fin (J + 1), a j ^ 2 := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hm0 J) hp1.le)
    rw [sum_div]
    refine sum_le_sum fun j _ => ?_
    rw [div_le_iff₀ htop]
    exact mul_le_mul_of_nonneg_right (le_zero_of_desc hp hm0 hm j) (sq_nonneg _) |>.trans_eq
      (by ring)
  have hlap : (1 / 2) * ∑ j : Fin (J + 1), ∑ k : Fin (J + 1),
      (m j / m 0) * m k * (a j - a k) ^ 2 ≤
      (1 / 2) * ∑ j, ∑ k, G j k * (a j - a k) ^ 2 := by
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => sum_le_sum fun k _ => ?_) (by norm_num)
    by_cases hjk : j = k
    · subst hjk; simp
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    simp only [G, valuationGram, if_neg hjk]
    rw [div_mul_eq_mul_div, div_le_iff₀ htop]
    rcases le_total (j : ℕ) k with h | h
    · rw [max_eq_right h]
      calc m j * m k ≤ m 0 * m k :=
            mul_le_mul_of_nonneg_right (le_zero_of_desc hp hm0 hm j) (hm0 _)
        _ = m k * m 0 := mul_comm _ _
    · rw [max_eq_left h]
      exact mul_le_mul_of_nonneg_left (le_zero_of_desc hp hm0 hm k) (hm0 _)
  have hgram := half_sum_mul_sq_sub a (fun j => m j)
  have hgram' : (1 / 2) * ∑ j : Fin (J + 1), ∑ k : Fin (J + 1),
      (m j / m 0) * m k * (a j - a k) ^ 2 =
      ((∑ j : Fin (J + 1), m j) * ∑ j : Fin (J + 1), m j * a j ^ 2 -
          (∑ j : Fin (J + 1), m j * a j) ^ 2) / m 0 := by
    rw [← hgram, mul_div_assoc, sum_div]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [sum_div]
    exact sum_congr rfl fun k _ => by field_simp
  have hrow' : ∀ j : Fin (J + 1), ∑ j', G j j' * a j' =
      ∑ j', (if j = j' then 0 else m (max (j : ℕ) j') * a j') -
        m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) * a j := by
    intro j
    have h : ∀ j', G j j' * a j' =
        (if j = j' then 0 else m (max (j : ℕ) j') * a j') +
          (if j = j' then -(m j * ((j : ℝ) + 1 / ((p : ℝ) - 1)) * a j') else 0) := by
      intro j'
      by_cases h : j = j'
      · subst h; simp [G, valuationGram]
      · simp [G, valuationGram, h]
    rw [sum_congr rfl fun j' _ => h j', sum_add_distrib, sum_ite_eq, if_pos (mem_univ j)]
    ring
  have hexp : qf G a =
      ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
        (if j = j' then 0 else a j * a j' * m (max (j : ℕ) j')) -
      ∑ j : Fin (J + 1), a j ^ 2 * (m j * ((j : ℝ) + 1 / ((p : ℝ) - 1))) := by
    simp only [qf, bil, dotProduct, mulVec]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [hrow' j, mul_sub, mul_sum]
    congr 1
    · refine sum_congr rfl fun j' _ => ?_
      split_ifs <;> ring
    · ring
  have hsplitS : (((∑ j : Fin (J + 1), m j) + m J / ((p : ℝ) - 1)) *
        ∑ j : Fin (J + 1), m j * a j ^ 2 - (∑ j : Fin (J + 1), m j * a j) ^ 2) / m 0 =
      ((∑ j : Fin (J + 1), m j) * ∑ j : Fin (J + 1), m j * a j ^ 2 -
          (∑ j : Fin (J + 1), m j * a j) ^ 2) / m 0 +
        (m J / ((p : ℝ) - 1)) * (∑ j : Fin (J + 1), m j * a j ^ 2) / m 0 := by
    field_simp; ring
  rw [hsplitS]
  linarith

/-! ### 3. The sharp Hodge index on the classes -/

/-- The completed tower mass: `Σ_{j ≤ J} |w_j|² + |w_J|²/(p − 1) ≥ (p/(p − 1) − η)|w_0|²`,
eventually. -/
theorem eventually_sum_classMass_add_tail_ge (hp : p.Prime) (J : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ M : ℕ in atTop,
      ((p : ℝ) / ((p : ℝ) - 1) - η) * classMass p 0 M ≤
        ∑ j : Fin (J + 1), classMass p j M + classMass p J M / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hlim : ∀ j : ℕ, Tendsto (fun M : ℕ => classMass p j M - 1 / (p : ℝ) ^ j * classMass p 0 M)
      atTop (𝓝 (-(classDensity p j * (j * Real.log p)))) := by
    intro j
    have h1 := tendsto_classMass_sub hp j
    have h0 := (tendsto_classMass_sub hp 0).const_mul (1 / (p : ℝ) ^ j)
    have h := h1.sub h0
    rw [mul_zero, sub_zero] at h
    have h' := h.add_const (-(classDensity p j * (j * Real.log p)))
    rw [zero_add] at h'
    refine h'.congr fun M => ?_
    have hδ : classDensity p j = 1 / (p : ℝ) ^ j * classDensity p 0 := by
      unfold classDensity; rw [pow_zero, div_one]; ring
    rw [hδ]; push_cast; ring
  set c : ℝ := ∑ j : Fin (J + 1), -(classDensity p j * (j * Real.log p)) +
    -(classDensity p J * (J * Real.log p)) / ((p : ℝ) - 1)
  -- the geometric identity `Σ_{j ≤ J} p^{−j} + p^{−J}/(p − 1) = p/(p − 1)`
  have hgeom : ∑ j : Fin (J + 1), 1 / (p : ℝ) ^ (j : ℕ) + 1 / (p : ℝ) ^ J / ((p : ℝ) - 1) =
      (p : ℝ) / ((p : ℝ) - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => 1 / (p : ℝ) ^ j)]
    induction J with
    | zero => simp; field_simp; ring
    | succ J ih =>
      rw [Finset.sum_range_succ, add_assoc, show 1 / (p : ℝ) ^ (J + 1) + 1 / (p : ℝ) ^ (J + 1) /
          ((p : ℝ) - 1) = 1 / (p : ℝ) ^ J / ((p : ℝ) - 1) by
        rw [pow_succ]; field_simp; ring]
      exact ih
  have hS : Tendsto (fun M : ℕ => ∑ j : Fin (J + 1), classMass p j M +
      classMass p J M / ((p : ℝ) - 1) - (p : ℝ) / ((p : ℝ) - 1) * classMass p 0 M) atTop (𝓝 c) := by
    have h1 := tendsto_finsetSum (univ : Finset (Fin (J + 1))) fun j _ => hlim j
    have h2 := (hlim J).div_const ((p : ℝ) - 1)
    refine (h1.add h2).congr fun M => ?_
    rw [← hgeom, add_mul, sum_mul, sum_sub_distrib]
    ring
  have h1 := hS.eventually (lt_mem_nhds (by linarith : c - 1 < c))
  have h2 := (tendsto_classMass_zero_atTop hp).eventually_ge_atTop ((1 - c) / η)
  filter_upwards [h1, h2] with M hM1 hM2
  rw [div_le_iff₀ hη] at hM2
  nlinarith

/-- **The sharp Hodge index of the matched prime place on the classes.** Eventually in `M`, every
class combination of depth `≤ J` satisfies
`P_M(x) + (p/(p − 1) − η) log p |x|² ≤ (log M − γ + η)|x|² + (log p/|w_0|²) ℓ(x)²`. -/
theorem eventually_atomicWeilForm_classCombination_sharpGap_le (hp : p.Prime) (J : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∀ a : Fin (J + 1) → ℝ,
      atomicWeilForm M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) +
          ((p : ℝ) / ((p : ℝ) - 1) - η) * Real.log p *
            ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 ≤
        (Real.log M - γ + η) *
            ∑ n ∈ Icc 1 M, (∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 +
          Real.log p / classMass p 0 M *
            polarFunctional M (fun n => ∑ j : Fin (J + 1), a j * classPole p j M n) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  obtain ⟨C, hC⟩ := exists_abs_atomicWeilForm_classCombination_finitePart_le hp J
    (η := η / 3) (by positivity)
  set C' : ℝ := max C 0
  have hev : ∀ j : Fin (J + 1), ∀ᶠ M : ℕ in atTop,
      classMass p j M ≤ classDensity p j * (Real.log M - j * Real.log p + localEuler p + η / 3) ∧
        3 * C' / η ≤ classMass p j M := by
    intro j
    have hδ := classDensity_pos hp j
    have ht := tendsto_classMass_sub hp j
    have h1 : ∀ᶠ M : ℕ in atTop, classMass p j M -
        classDensity p j * (Real.log M - j * Real.log p + localEuler p) <
          classDensity p j * (η / 3) :=
      ht.eventually (gt_mem_nhds (by positivity))
    have h2 : ∀ᶠ M : ℕ in atTop, -1 < classMass p j M -
        classDensity p j * (Real.log M - j * Real.log p + localEuler p) :=
      ht.eventually (lt_mem_nhds (by norm_num))
    have hlog : Tendsto (fun M : ℕ => classDensity p j * (Real.log M - j * Real.log p +
        localEuler p)) atTop atTop := by
      refine Tendsto.const_mul_atTop hδ ?_
      refine tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ ?_)
      exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h3 := hlog.eventually_ge_atTop (3 * C' / η + 1)
    filter_upwards [h1, h2, h3] with M hM1 hM2 hM3
    exact ⟨by nlinarith, by linarith⟩
  have hgapev := eventually_sum_classMass_add_tail_ge hp J hη
  have htop := (tendsto_classMass_zero_atTop hp).eventually_gt_atTop 0
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((eventually_all.mpr hev).and (hgapev.and htop))
  refine ⟨M₀, fun M hM a => ?_⟩
  obtain ⟨hmass, hgap, hm0pos⟩ := hM₀ M hM
  have hmm0 : ∀ j, 0 ≤ classMass p j M := fun j => classMass_nonneg p j M
  have hval := sum_cross_add_sharpGap_le_valuation (J := J) hp1 hmm0
    (fun j => classMass_succ_le hp j M) hm0pos a
  rw [sum_classCombination_sq (p := p) a M, polarFunctional_classCombination a M]
  have hfin := hC M a
  have hdiag : ∀ j : Fin (J + 1), (a j * classMass p j M) ^ 2 / classDensity p j ≤
      a j ^ 2 * classMass p j M * (Real.log M - j * Real.log p + localEuler p + η / 3) := by
    intro j
    have hδ := classDensity_pos hp j
    rw [div_le_iff₀ hδ]
    have e : (a j * classMass p j M) ^ 2 = a j ^ 2 * classMass p j M * classMass p j M := by ring
    rw [e]
    calc a j ^ 2 * classMass p j M * classMass p j M
        ≤ a j ^ 2 * classMass p j M *
            (classDensity p j * (Real.log M - j * Real.log p + localEuler p + η / 3)) :=
          mul_le_mul_of_nonneg_left (hmass j).1 (mul_nonneg (sq_nonneg _) (hmm0 j))
      _ = _ := by ring
  have hC' : ∀ j : Fin (J + 1), a j ^ 2 * (η / 3 * classMass p j M + C) ≤
      a j ^ 2 * (2 * η / 3 * classMass p j M) := by
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have h1 : C ≤ C' := le_max_left _ _
    have h2 : 3 * C' / η ≤ classMass p j M := (hmass j).2
    have h3 : C' ≤ η / 3 * classMass p j M := by
      rw [div_le_iff₀ hη] at h2; linarith
    linarith
  have hD := sum_le_sum fun j (_ : j ∈ univ) => hdiag j
  have hE := sum_le_sum fun j (_ : j ∈ univ) => hC' j
  set S : ℝ := ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M with hSdef
  set W : ℝ := ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M * j
  set L : ℝ := ∑ j : Fin (J + 1), a j * classMass p j M
  set T : ℝ := ∑ j : Fin (J + 1), classMass p j M + classMass p J M / ((p : ℝ) - 1)
  set X : ℝ := ∑ j : Fin (J + 1), ∑ j' : Fin (J + 1),
      (if j = j' then 0 else a j * a j' * classMass p (max (j : ℕ) j') M)
  have hsplit : ∑ j : Fin (J + 1), a j ^ 2 * classMass p j M *
      (Real.log M - j * Real.log p + localEuler p + η / 3) =
      (Real.log M + localEuler p + η / 3) * S - Real.log p * W := by
    rw [hSdef, mul_sum, mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring
  have hS' : ∑ j : Fin (J + 1), classMass p j M * a j ^ 2 = S :=
    sum_congr rfl fun j _ => by ring
  have hR : ∑ j : Fin (J + 1), a j ^ 2 * (classMass p j M * ((j : ℝ) + 1 / ((p : ℝ) - 1))) =
      W + 1 / ((p : ℝ) - 1) * S := by
    rw [hSdef, mul_sum, ← sum_add_distrib]; exact sum_congr rfl fun j _ => by ring
  have hL' : ∑ j : Fin (J + 1), classMass p j M * a j = L := sum_congr rfl fun j _ => mul_comm _ _
  rw [hS', hR, hL'] at hval
  have hsum2 : ∑ j : Fin (J + 1), a j ^ 2 * (2 * η / 3 * classMass p j M) = 2 * η / 3 * S := by
    rw [hSdef, mul_sum]; exact sum_congr rfl fun j _ => by ring
  have habs := (abs_le.mp (hfin.trans (hsum2 ▸ hE))).2
  have hm0 := hm0pos
  have hTS : ((p : ℝ) / ((p : ℝ) - 1) - η) * S ≤
      (T * S - L ^ 2) / classMass p 0 M + L ^ 2 / classMass p 0 M := by
    rw [← add_div, sub_add_cancel, le_div_iff₀ hm0]
    have hS0 : 0 ≤ S := sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hmm0 j)
    nlinarith [mul_le_mul_of_nonneg_right hgap hS0]
  have hpot : Real.log p * ((T * S - L ^ 2) / classMass p 0 M) ≥
      Real.log p * (((p : ℝ) / ((p : ℝ) - 1) - η) * S) - Real.log p / classMass p 0 M * L ^ 2 := by
    have := mul_le_mul_of_nonneg_left hTS hlogp.le
    rw [mul_add] at this
    have e : Real.log p * (L ^ 2 / classMass p 0 M) = Real.log p / classMass p 0 M * L ^ 2 := by
      ring
    linarith
  have hval2 := mul_le_mul_of_nonneg_left hval hlogp.le
  rw [mul_add, mul_add] at hval2
  unfold localEuler at hsplit habs hD
  have e2 : Real.log p * (1 / ((p : ℝ) - 1) * S) = Real.log p / ((p : ℝ) - 1) * S := by ring
  rw [e2] at hval2
  linarith [hD, hsplit, hval2, habs, hpot]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
