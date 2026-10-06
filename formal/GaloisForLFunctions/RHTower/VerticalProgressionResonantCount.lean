import GaloisForLFunctions.RHTower.VerticalProgressionResonantBounds

/-!
# Counting resonant ratios

For a coprime pair `c = (a, b)` put `λ(c) = log a − log b`. The ratio is `j`-resonant at width
`δ'` if `|λ(c) − 2πj/α| < δ'`.

* **Window count** (`card_window_le`): for `δ' ≤ 1`, the `j`-resonant pairs with `ab < W` number at
  most `2e³δ'W + 1`: they are reduced fractions with denominators `≤ √(We^{1−λ_j})` in a window
  of length `≤ 2e²δ' e^{λ_j}` (Farey spacing).
* **Range of `j`** (`abs_le_of_window`): a `j`-resonant pair with `ab < W` has
  `|j| ≤ (α/2π)(log W + 1)`.
* **All resonances** (`card_resonantSet_le`): the pairs with `ab < W` resonant for some `j`
  number at most `(2J + 1)(2e³δ'W + 1)`, `J = ⌊(α/2π)(log W + 1)⌋`.
-/

open Finset

namespace RHTower.VerticalAP

noncomputable section

/-- `λ(c) = log a − log b`. -/
def ratioLog (c : ℕ × ℕ) : ℝ := Real.log c.1 - Real.log c.2

/-- The `j`-resonant coprime pairs with `ab < W`. -/
def windowSet (α δ' W : ℝ) (j : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ⌊W⌋₊ ×ˢ Finset.Icc 1 ⌊W⌋₊).filter fun c =>
    Nat.Coprime c.1 c.2 ∧ ((c.1 * c.2 : ℕ) : ℝ) < W ∧
      |ratioLog c - 2 * Real.pi * j / α| < δ')

theorem mem_windowSet {α δ' W : ℝ} {j : ℤ} {c : ℕ × ℕ} :
    c ∈ windowSet α δ' W j ↔ 0 < c.1 ∧ 0 < c.2 ∧ Nat.Coprime c.1 c.2 ∧
      ((c.1 * c.2 : ℕ) : ℝ) < W ∧ |ratioLog c - 2 * Real.pi * j / α| < δ' := by
  unfold windowSet
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h2, _⟩, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hW : ((c.1 * c.2 : ℕ) : ℝ) < W := h4
    have e1 : c.1 ≤ c.1 * c.2 := Nat.le_mul_of_pos_right _ h2
    have e2 : c.2 ≤ c.1 * c.2 := Nat.le_mul_of_pos_left _ h1
    have hfl : c.1 * c.2 ≤ ⌊W⌋₊ := Nat.le_floor hW.le
    exact ⟨⟨⟨h1, e1.trans hfl⟩, h2, e2.trans hfl⟩, h3, h4, h5⟩

theorem exp_sub_exp_neg_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - Real.exp (-x) ≤ 2 * Real.exp 2 * x := by
  have h1 : Real.exp x - Real.exp (-x) ≤ Real.exp (2 * x) - 1 := by
    have : Real.exp (-x) * (Real.exp (2 * x) - 1) = Real.exp x - Real.exp (-x) := by
      rw [mul_sub, ← Real.exp_add, mul_one]; ring_nf
    rw [← this]
    have hle : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hnn : 0 ≤ Real.exp (2 * x) - 1 := by
      have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * x); linarith
    nlinarith
  have h2 : Real.exp (2 * x) - 1 ≤ 2 * x * Real.exp (2 * x) := by
    have := Real.add_one_le_exp (-(2 * x))
    have hpos := Real.exp_pos (2 * x)
    have e : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h3 : Real.exp (2 * x) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- **The window count** `#{j-resonant, ab < W} ≤ 2e³δ'W + 1`. -/
theorem card_window_le {α δ' W : ℝ} (hδ0 : 0 ≤ δ') (hδ1 : δ' ≤ 1) (hW : 0 ≤ W)
    (j : ℤ) : ((windowSet α δ' W j).card : ℝ) ≤ 2 * Real.exp 3 * δ' * W + 1 := by
  set lj : ℝ := 2 * Real.pi * j / α
  set B : ℕ := ⌊Real.sqrt (W * Real.exp (1 - lj))⌋₊
  have hwin := card_le_of_window (windowSet α δ' W j) (B := B) (lo := Real.exp (lj - δ'))
    (len := Real.exp (lj + δ') - Real.exp (lj - δ')) (by
      have := Real.exp_le_exp.mpr (by linarith : lj - δ' ≤ lj + δ'); linarith) (fun c hc => ?_)
  · refine hwin.trans ?_
    have hlen : Real.exp (lj + δ') - Real.exp (lj - δ') ≤ Real.exp lj * (2 * Real.exp 2 * δ') := by
      rw [Real.exp_add, Real.exp_sub, show Real.exp lj / Real.exp δ' = Real.exp lj * Real.exp (-δ')
        by rw [Real.exp_neg]; ring, ← mul_sub]
      exact mul_le_mul_of_nonneg_left (exp_sub_exp_neg_le hδ0 hδ1) (Real.exp_pos _).le
    have hB : (B : ℝ) ^ 2 ≤ W * Real.exp (1 - lj) := by
      have h1 : (B : ℝ) ≤ Real.sqrt (W * Real.exp (1 - lj)) := Nat.floor_le (Real.sqrt_nonneg _)
      calc (B : ℝ) ^ 2 ≤ Real.sqrt (W * Real.exp (1 - lj)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
        _ = W * Real.exp (1 - lj) := Real.sq_sqrt (by positivity)
    have hlen0 : 0 ≤ Real.exp (lj + δ') - Real.exp (lj - δ') := by
      have := Real.exp_le_exp.mpr (by linarith : lj - δ' ≤ lj + δ'); linarith
    calc (Real.exp (lj + δ') - Real.exp (lj - δ')) * (B : ℝ) ^ 2 + 1
        ≤ (Real.exp lj * (2 * Real.exp 2 * δ')) * (W * Real.exp (1 - lj)) + 1 := by
          gcongr
      _ = 2 * Real.exp 3 * δ' * W + 1 := by
          rw [show Real.exp 3 = Real.exp 2 * Real.exp lj * Real.exp (1 - lj) by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf]
          ring
  obtain ⟨ha, hb, hcop, hab, hlog⟩ := mem_windowSet.mp hc
  have haR : (0 : ℝ) < c.1 := by exact_mod_cast ha
  have hbR : (0 : ℝ) < c.2 := by exact_mod_cast hb
  have hratio : Real.log ((c.1 : ℝ) / c.2) = ratioLog c := by
    unfold ratioLog; rw [Real.log_div haR.ne' hbR.ne']
  have hlo : Real.exp (lj - δ') ≤ (c.1 : ℝ) / c.2 := by
    rw [← Real.exp_log (div_pos haR hbR), hratio]
    exact Real.exp_le_exp.mpr (by have := (abs_lt.mp hlog).1; linarith)
  have hhi : (c.1 : ℝ) / c.2 ≤ Real.exp (lj + δ') := by
    rw [← Real.exp_log (div_pos haR hbR), hratio]
    exact Real.exp_le_exp.mpr (by have := (abs_lt.mp hlog).2; linarith)
  refine ⟨hcop, hb, ?_, hlo, by linarith⟩
  -- `b² = ab/(a/b) < W e^{1 − λ_j}`
  apply Nat.le_floor
  rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity)]
  have hab' : (c.1 : ℝ) * c.2 < W := by exact_mod_cast hab
  have h1 : Real.exp (lj - 1) ≤ (c.1 : ℝ) / c.2 :=
    (Real.exp_le_exp.mpr (by linarith)).trans hlo
  have h2 : (c.2 : ℝ) ^ 2 = (c.1 : ℝ) * c.2 / ((c.1 : ℝ) / c.2) := by field_simp
  rw [h2, div_le_iff₀ (div_pos haR hbR)]
  have e : Real.exp (1 - lj) * Real.exp (lj - 1) = 1 := by rw [← Real.exp_add]; simp
  calc (c.1 : ℝ) * c.2 ≤ W := hab'.le
    _ = W * Real.exp (1 - lj) * Real.exp (lj - 1) := by rw [mul_assoc, e, mul_one]
    _ ≤ W * Real.exp (1 - lj) * ((c.1 : ℝ) / c.2) := by gcongr

/-- **The range of resonances.** -/
theorem abs_le_of_window {α δ' W : ℝ} (hα : 0 < α) (hδ1 : δ' ≤ 1) {j : ℤ} {c : ℕ × ℕ}
    (hc : c ∈ windowSet α δ' W j) : |(j : ℝ)| ≤ α / (2 * Real.pi) * (Real.log W + 1) := by
  obtain ⟨ha, hb, _, hab, hlog⟩ := mem_windowSet.mp hc
  have haR : (1 : ℝ) ≤ c.1 := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ c.2 := by exact_mod_cast hb
  have hlabs : |ratioLog c| ≤ Real.log ((c.1 * c.2 : ℕ) : ℝ) := by
    unfold ratioLog
    push_cast
    rw [Real.log_mul (by positivity) (by positivity)]
    have := Real.log_nonneg haR
    have := Real.log_nonneg hbR
    rw [abs_le]; constructor <;> linarith
  have hW : Real.log ((c.1 * c.2 : ℕ) : ℝ) < Real.log W := by
    have hp : (0 : ℝ) < ((c.1 * c.2 : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ha hb
    exact Real.log_lt_log hp hab
  have hj : |2 * Real.pi * j / α| ≤ Real.log W + 1 := by
    have := abs_sub_abs_le_abs_sub (2 * Real.pi * j / α) (ratioLog c)
    rw [abs_sub_comm] at hlog
    linarith
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hα,
    div_le_iff₀ hα] at hj
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

open Classical in
/-- The pairs with `ab < W` resonant for some `j ≠ 0`. -/
def resonantSet (α δ' W : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ⌊W⌋₊ ×ˢ Finset.Icc 1 ⌊W⌋₊).filter fun c =>
    Nat.Coprime c.1 c.2 ∧ ((c.1 * c.2 : ℕ) : ℝ) < W ∧
      ∃ j : ℤ, j ≠ 0 ∧ |ratioLog c - 2 * Real.pi * j / α| < δ')

/-- **All resonances below `W`** number at most `(2J + 1)(2e³δ'W + 1)`. -/
theorem card_resonantSet_le {α δ' W : ℝ} (hα : 0 < α) (hδ0 : 0 ≤ δ') (hδ1 : δ' ≤ 1)
    (hW : 0 ≤ W) :
    ((resonantSet α δ' W).card : ℝ) ≤
      (2 * ⌊α / (2 * Real.pi) * (Real.log W + 1)⌋₊ + 1) * (2 * Real.exp 3 * δ' * W + 1) := by
  set J : ℕ := ⌊α / (2 * Real.pi) * (Real.log W + 1)⌋₊
  have hsub : resonantSet α δ' W ⊆ (Finset.Icc (-(J : ℤ)) J).biUnion (windowSet α δ' W) := by
    intro c hc
    unfold resonantSet at hc
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hc
    obtain ⟨⟨⟨ha, _⟩, hb, _⟩, hcop, hab, j, _, hj⟩ := hc
    have hwin : c ∈ windowSet α δ' W j := mem_windowSet.mpr ⟨ha, hb, hcop, hab, hj⟩
    refine Finset.mem_biUnion.mpr ⟨j, ?_, hwin⟩
    have hJ := abs_le_of_window hα hδ1 hwin
    have hJ' : |j| ≤ (J : ℤ) := by
      have h0 : 0 ≤ α / (2 * Real.pi) * (Real.log W + 1) := (abs_nonneg _).trans hJ
      have h1 : ((|j| : ℤ) : ℝ) ≤ α / (2 * Real.pi) * (Real.log W + 1) := by
        rw [Int.cast_abs]; exact hJ
      have h2 : |j| ≤ ⌊α / (2 * Real.pi) * (Real.log W + 1)⌋ := Int.le_floor.mpr h1
      rw [← Int.natCast_floor_eq_floor h0] at h2
      exact h2
    rw [Finset.mem_Icc]
    exact abs_le.mp hJ'
  calc ((resonantSet α δ' W).card : ℝ)
      ≤ (((Finset.Icc (-(J : ℤ)) J).biUnion (windowSet α δ' W)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.Icc (-(J : ℤ)) J, ((windowSet α δ' W j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.Icc (-(J : ℤ)) J, (2 * Real.exp 3 * δ' * W + 1) :=
        Finset.sum_le_sum fun j _ => card_window_le hδ0 hδ1 hW j
    _ = (2 * J + 1) * (2 * Real.exp 3 * δ' * W + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
        congr 1
        rw [show (J : ℤ) + 1 - -(J : ℤ) = 2 * J + 1 by ring]
        norm_cast

theorem mem_resonantSet {α δ' W : ℝ} {c : ℕ × ℕ} :
    c ∈ resonantSet α δ' W ↔ 0 < c.1 ∧ 0 < c.2 ∧ Nat.Coprime c.1 c.2 ∧
      ((c.1 * c.2 : ℕ) : ℝ) < W ∧ ∃ j : ℤ, j ≠ 0 ∧ |ratioLog c - 2 * Real.pi * j / α| < δ' := by
  classical
  unfold resonantSet
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h2, _⟩, h3, h4, h5⟩; exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have e1 : c.1 ≤ c.1 * c.2 := Nat.le_mul_of_pos_right _ h2
    have e2 : c.2 ≤ c.1 * c.2 := Nat.le_mul_of_pos_left _ h1
    have hfl : c.1 * c.2 ≤ ⌊W⌋₊ := Nat.le_floor h4.le
    exact ⟨⟨⟨h1, e1.trans hfl⟩, h2, e2.trans hfl⟩, h3, h4, h5⟩

/-! ## Dyadic sums -/

theorem sum_pow_le_of_le {q Q : ℝ} (hq : 1 < q) (hQ : 0 ≤ Q) (I : Finset ℕ)
    (hI : ∀ i ∈ I, q ^ i ≤ Q) : ∑ i ∈ I, q ^ i ≤ Q * (q / (q - 1)) := by
  have h := sum_geometric_le_of_le (x₀ := 1) hq hQ (I.map Nat.castEmbedding) (by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    simpa [zpow_natCast] using hI i hi)
  simpa [Finset.sum_map, zpow_natCast] using h

theorem sum_pow_inv_le_of_le {q Q : ℝ} (hq : 1 < q) (hQ : 0 ≤ Q) (I : Finset ℕ)
    (hI : ∀ i ∈ I, (q ^ i)⁻¹ ≤ Q) : ∑ i ∈ I, (q ^ i)⁻¹ ≤ Q * (q / (q - 1)) := by
  have h := sum_geometric_neg_le_of_le (x₀ := 1) hq hQ (I.map Nat.castEmbedding) (by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    simpa [zpow_neg, zpow_natCast] using hI i hi)
  simpa [Finset.sum_map, zpow_neg, zpow_natCast] using h

theorem two_pow_rpow (i : ℕ) (s : ℝ) : ((2 : ℝ) ^ i) ^ s = ((2 : ℝ) ^ s) ^ i := by
  rw [← Real.rpow_natCast 2 i, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

theorem two_rpow_one_sub (s : ℝ) : (2 : ℝ) ^ (1 - s) = 2 / (2 : ℝ) ^ s := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_one]

/-- **The dyadic Farey sum.** For `0 < s < 1` and resonant pairs with `Y ≤ ab ≤ Z`,
`Σ (ab)^{−s} ≤ (2J + 1)(4e³δ' Z^{1−s} q₁ + 2^s Y^{−s} q₂)`. -/
theorem sum_resonant_rpow_le {α δ' Y Z s : ℝ} (hα : 0 < α) (hδ0 : 0 ≤ δ') (hδ1 : δ' ≤ 1)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (hs0 : 0 < s) (hs1 : s < 1) (S : Finset (ℕ × ℕ))
    (hS : ∀ c ∈ S, 0 < c.1 ∧ 0 < c.2 ∧ Nat.Coprime c.1 c.2 ∧
      (∃ j : ℤ, j ≠ 0 ∧ |ratioLog c - 2 * Real.pi * j / α| < δ') ∧
      Y ≤ ((c.1 * c.2 : ℕ) : ℝ) ∧ ((c.1 * c.2 : ℕ) : ℝ) ≤ Z) :
    ∑ c ∈ S, (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹ ≤
      (2 * ⌊α / (2 * Real.pi) * (Real.log (2 * Z) + 1)⌋₊ + 1) *
        (4 * Real.exp 3 * δ' * (Z ^ (1 - s) * ((2 : ℝ) ^ (1 - s) / ((2 : ℝ) ^ (1 - s) - 1))) +
          (2 : ℝ) ^ s * (Y ^ s)⁻¹ * ((2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1))) := by
  classical
  set J : ℕ := ⌊α / (2 * Real.pi) * (Real.log (2 * Z) + 1)⌋₊
  set r : ℝ := (2 : ℝ) ^ s with hr
  set lg : ℕ × ℕ → ℕ := fun c => Nat.log 2 (c.1 * c.2)
  have hZ0 : 0 < Z := by linarith
  have hq1 : 1 < (2 : ℝ) ^ (1 - s) := Real.one_lt_rpow (by norm_num) (by linarith)
  have hq2 : 1 < r := Real.one_lt_rpow (by norm_num) hs0
  have hr0 : 0 < r := by linarith
  have hbounds : ∀ c ∈ S, ((2 : ℝ) ^ lg c ≤ ((c.1 * c.2 : ℕ) : ℝ)) ∧
      ((c.1 * c.2 : ℕ) : ℝ) < (2 : ℝ) ^ (lg c + 1) := by
    intro c hc
    obtain ⟨ha, hb, -⟩ := hS c hc
    have hab : c.1 * c.2 ≠ 0 := Nat.mul_ne_zero ha.ne' hb.ne'
    exact ⟨by exact_mod_cast Nat.pow_log_le_self 2 hab,
      by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) _⟩
  set I := S.image lg
  rw [← Finset.sum_fiberwise_of_maps_to (g := lg) (t := I)
    (fun c hc => Finset.mem_image_of_mem lg hc)]
  have hblock : ∀ i ∈ I, ∑ c ∈ S with lg c = i, (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹ ≤
      (2 * J + 1) * (4 * Real.exp 3 * δ' * ((2 : ℝ) ^ (1 - s)) ^ i + (r ^ i)⁻¹) := by
    intro i hi
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hl0, hu0⟩ := hbounds c₀ hc₀
    have hZ2 : (2 : ℝ) ^ (lg c₀ + 1) ≤ 2 * Z := by
      rw [pow_succ]; linarith [(hS c₀ hc₀).2.2.2.2.2]
    have hsub : (S.filter fun c => lg c = lg c₀) ⊆ resonantSet α δ' ((2 : ℝ) ^ (lg c₀ + 1)) := by
      intro c hc
      obtain ⟨hcS, hci⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb, hcop, hres, -⟩ := hS c hcS
      exact mem_resonantSet.mpr ⟨ha, hb, hcop, by rw [← hci]; exact (hbounds c hcS).2, hres⟩
    have hcard := card_resonantSet_le hα hδ0 hδ1 (W := (2 : ℝ) ^ (lg c₀ + 1)) (by positivity)
    have hJ : ⌊α / (2 * Real.pi) * (Real.log ((2 : ℝ) ^ (lg c₀ + 1)) + 1)⌋₊ ≤ J := by
      apply Nat.floor_le_floor
      gcongr
    have hterm : ∀ c ∈ S.filter (fun c => lg c = lg c₀),
        (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹ ≤ (r ^ lg c₀)⁻¹ := by
      intro c hc
      obtain ⟨hcS, hci⟩ := Finset.mem_filter.mp hc
      have := (hbounds c hcS).1
      rw [hci] at this
      rw [hr, ← two_pow_rpow]
      exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) this hs0.le)
    have e : (2 : ℝ) ^ (lg c₀ + 1) * (r ^ lg c₀)⁻¹ = 2 * ((2 : ℝ) ^ (1 - s)) ^ lg c₀ := by
      rw [two_rpow_one_sub, ← hr, div_pow, pow_succ]
      field_simp
    calc ∑ c ∈ S with lg c = lg c₀, (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹
        ≤ ∑ c ∈ S with lg c = lg c₀, (r ^ lg c₀)⁻¹ := Finset.sum_le_sum hterm
      _ = ((S.filter fun c => lg c = lg c₀).card : ℝ) * (r ^ lg c₀)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * J + 1) * (2 * Real.exp 3 * δ' * (2 : ℝ) ^ (lg c₀ + 1) + 1)) * (r ^ lg c₀)⁻¹ := by
          gcongr
          calc ((S.filter fun c => lg c = lg c₀).card : ℝ)
              ≤ ((resonantSet α δ' ((2 : ℝ) ^ (lg c₀ + 1))).card : ℝ) := by
                exact_mod_cast Finset.card_le_card hsub
            _ ≤ _ := hcard
            _ ≤ _ := by
                gcongr
      _ = (2 * J + 1) * (4 * Real.exp 3 * δ' * ((2 : ℝ) ^ (1 - s)) ^ lg c₀ + (r ^ lg c₀)⁻¹) := by
          rw [show ((2 * J + 1) * (2 * Real.exp 3 * δ' * (2 : ℝ) ^ (lg c₀ + 1) + 1)) *
              (r ^ lg c₀)⁻¹ = (2 * J + 1) * (2 * Real.exp 3 * δ' * ((2 : ℝ) ^ (lg c₀ + 1) *
                (r ^ lg c₀)⁻¹) + (r ^ lg c₀)⁻¹) by ring, e]
          ring
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hJ0 : (0 : ℝ) ≤ 2 * J + 1 := by positivity
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hJ0
  · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine sum_pow_le_of_le hq1 (by positivity) I fun i hi => ?_
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
    rw [← two_pow_rpow]
    exact Real.rpow_le_rpow (by positivity) ((hbounds c hc).1.trans (hS c hc).2.2.2.2.2)
      (by linarith)
  · refine sum_pow_inv_le_of_le hq2 (by positivity) I fun i hi => ?_
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
    have hlt : Y ≤ (2 : ℝ) ^ (lg c + 1) := ((hS c hc).2.2.2.2.1).trans (hbounds c hc).2.le
    have h1 : Y ^ s ≤ r * r ^ lg c := by
      rw [hr, ← pow_succ', ← two_pow_rpow]
      exact Real.rpow_le_rpow (by linarith) hlt hs0.le
    have hYs : 0 < Y ^ s := Real.rpow_pos_of_pos (by linarith) s
    rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
    calc r⁻¹ * Y ^ s ≤ r⁻¹ * (r * r ^ lg c) := by gcongr
      _ = r ^ lg c := by field_simp

end

end RHTower.VerticalAP
