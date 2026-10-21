import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionPriceEulerAdditivity

/-!
# `log 6` is the decoupling length of the primes `2` and `3`

On the cone blind at every prime power except `2` and `3` the deletion price is exactly
`w₂ + w₃` (`w_p = log p/√p`), attained by the double pair `b ∗ (δ₀ ± δ_{log 2}) ∗ (δ₀ ± δ_{log 3})`,
whose cross lag `log 6` is free because `Λ(6) = 0` (`PrimePowerDeletionPriceAdditivity`). Here every
test of the combination is confined to an interval of length `L`.

**Theorem** (`abs_le_of_mem_twoThreeWindowDeviations`, `isGreatest_twoThreeWindowDeviations`,
`twoThree_price_jump`). On this cone, with all tests supported in intervals of length `L`:
* `|(A − W)/‖c‖²| ≤ 111/100` when `L ≤ log 6`;
* the exact range of `(A − W)/‖c‖²` is `[−(w₂ + w₃), w₂ + w₃]` when `L > log 6`;

and `111/100 < w₂ + w₃ ≈ 1.1244`. The price of `{2, 3}` jumps at `L = log 6`: the composite node is
never charged, yet the two prime prices add only on windows long enough to contain its lag.

**Mechanism.**
* On a window of length `L ≤ log 6` the lag graph `u ~ u ± log 2, u ± log 3` has degree at most two:
  a point of `[log 2, log 3)` (relative to the window) has its two `log 2`-neighbours and no
  `log 3`-neighbour, every other point has at most one neighbour of each kind. The components are
  paths in which the `w₃`-edges are separated by one or two `w₂`-edges, and the alternating pattern
  `w₂w₃w₂w₃…` that reaches `w₂ + w₃` breaks at every double `w₂`-vertex, whose neighbour sum is
  `2w₂ < w₂ + w₃`.
* The five-step weight `1, r, q, r, 1` on `[0, log(3/2))`, `[log(3/2), log 2)`, `[log 2, log 3)`,
  `[log 3, log 4)`, `[log 4, L)` with `q = 89/100`, `r = 207/200` is a Schur supersolution with
  constant `κ = 111/100` (`decouplingWeight_schur_le`): `2w₂ ≤ κq`, `w₂q + w₃r ≤ κ`, `w₂r + w₃ ≤ κr`.
* Above `log 6` the Euler train `Σ_{A⊆P} σ_A h_N(u − log m_A)` with a bump of index `N` lies in a
  window of length `log m_P + 1/(2(N+1))`; for every finite set of primes it attains the Euler price
  on every window longer than `log m_P` (`isGreatest_eulerWindowDeviations`).
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. The atoms of `2` and `3` -/

theorem log_three_near : 1.0986 < Real.log 3 ∧ Real.log 3 < 1.0987 := by
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 4 : ℝ)| < 1 by norm_num) 8
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, abs_le] at h
  have e : Real.log (3 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  constructor <;> linarith [h.1, h.2]

theorem atomTwo_near : 0.49 < atomTwo ∧ atomTwo < 0.4902 := by
  have s1 : (1.41421 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 2 < 1.41422 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have hs : 0 < Real.sqrt 2 := by linarith
  unfold atomTwo
  constructor
  · rw [lt_div_iff₀ hs]; nlinarith
  · rw [div_lt_iff₀ hs]; nlinarith

theorem atomThree_near : 0.6342 < atomThree ∧ atomThree < 0.6344 := by
  have s1 : (1.73205 : ℝ) < Real.sqrt 3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt 3 < 1.73206 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  obtain ⟨l1, l2⟩ := log_three_near
  have hs : 0 < Real.sqrt 3 := by linarith
  unfold atomThree
  constructor
  · rw [lt_div_iff₀ hs]; nlinarith
  · rw [div_lt_iff₀ hs]; nlinarith

/-! ### 2. The Schur supersolution below `log 6` -/

/-- The decoupling ceiling `κ = 111/100`. -/
def decouplingCeiling : ℝ := 111 / 100

/-- **The price drops below `log 6`**: `κ < w₂ + w₃`. -/
theorem decouplingCeiling_lt : decouplingCeiling < atomTwo + atomThree := by
  unfold decouplingCeiling; linarith [atomTwo_near.1, atomThree_near.1]

/-- The supersolution inequalities `2w₂ ≤ κq`, `w₂q + w₃r ≤ κ`, `w₂r + w₃ ≤ κr`. -/
theorem decoupling_inequalities :
    2 * atomTwo ≤ decouplingCeiling * (89 / 100) ∧
      atomTwo * (89 / 100) + atomThree * (207 / 200) ≤ decouplingCeiling ∧
      atomTwo * (207 / 200) + atomThree ≤ decouplingCeiling * (207 / 200) := by
  obtain ⟨-, a2⟩ := atomTwo_near
  obtain ⟨-, a3⟩ := atomThree_near
  unfold decouplingCeiling
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The five-step weight `1, r, q, r, 1` on `[0, log(3/2))`, `[log(3/2), log 2)`, `[log 2, log 3)`,
`[log 3, log 4)`, `[log 4, ∞)` (positions relative to `a`), `q = 89/100`, `r = 207/200`. -/
def decouplingWeight (a t : ℝ) : ℝ :=
  if t - a < Real.log 3 - Real.log 2 then 1
  else if t - a < Real.log 2 then 207 / 200
  else if t - a < Real.log 3 then 89 / 100
  else if t - a < 2 * Real.log 2 then 207 / 200
  else 1

theorem measurable_decouplingWeight (a : ℝ) : Measurable (decouplingWeight a) := by
  unfold decouplingWeight
  have hm : ∀ c : ℝ, MeasurableSet {t : ℝ | t - a < c} := fun c =>
    measurableSet_lt (measurable_id.sub_const a) measurable_const
  exact Measurable.ite (hm _) measurable_const <| Measurable.ite (hm _) measurable_const <|
    Measurable.ite (hm _) measurable_const <| Measurable.ite (hm _) measurable_const measurable_const

theorem decouplingWeight_ge (a t : ℝ) : 89 / 100 ≤ decouplingWeight a t := by
  unfold decouplingWeight; split_ifs <;> norm_num

theorem decouplingWeight_le (a t : ℝ) : decouplingWeight a t ≤ 207 / 200 := by
  unfold decouplingWeight; split_ifs <;> norm_num

/-- `log 2 < log 3 < 2 log 2` and `3 log 2 < 2 log 3`. -/
theorem log_two_three_order :
    0 < Real.log 2 ∧ Real.log 2 < Real.log 3 ∧ Real.log 3 < 2 * Real.log 2 ∧
      3 * Real.log 2 < 2 * Real.log 3 := by
  obtain ⟨h0, h23, h4, h98⟩ := log_relations
  refine ⟨h0, h23, ?_, h98⟩
  rw [← h4]
  exact Real.log_lt_log (by norm_num) (by norm_num)

theorem decouplingWeight_of_low {a t : ℝ} (h : t - a < Real.log 3 - Real.log 2) :
    decouplingWeight a t = 1 := by
  unfold decouplingWeight; rw [if_pos h]

theorem decouplingWeight_of_mid {a t : ℝ} (h1 : Real.log 2 ≤ t - a) (h2 : t - a < Real.log 3) :
    decouplingWeight a t = 89 / 100 := by
  obtain ⟨-, -, h34, -⟩ := log_two_three_order
  unfold decouplingWeight
  rw [if_neg (by linarith), if_neg (by linarith), if_pos h2]

theorem decouplingWeight_of_high {a t : ℝ} (h : 2 * Real.log 2 ≤ t - a) :
    decouplingWeight a t = 1 := by
  obtain ⟨h0, h23, h34, -⟩ := log_two_three_order
  unfold decouplingWeight
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]

/-- **The supersolution inequality.** On a window `(a, a + L)` with `L ≤ log 6`, the weighted
neighbour sum `Σ_s w_s (φ(t − s) + φ(t + s))/φ(t)` over the shifts `log 2`, `log 3` is at most
`κ = 111/100`. -/
theorem decouplingWeight_schur_le {a L t : ℝ} (hL : L ≤ Real.log 2 + Real.log 3)
    (ht : t ∈ Ioo a (a + L)) :
    atomTwo * ((Ioo a (a + L)).indicator (decouplingWeight a) (t - Real.log 2) /
          decouplingWeight a t +
        (Ioo a (a + L)).indicator (decouplingWeight a) (t + Real.log 2) / decouplingWeight a t) +
      atomThree * ((Ioo a (a + L)).indicator (decouplingWeight a) (t - Real.log 3) /
          decouplingWeight a t +
        (Ioo a (a + L)).indicator (decouplingWeight a) (t + Real.log 3) / decouplingWeight a t) ≤
      decouplingCeiling := by
  obtain ⟨h0, h23, h34, h98⟩ := log_two_three_order
  obtain ⟨n1, n2, n3⟩ := decoupling_inequalities
  obtain ⟨hta, htb⟩ := ht
  set φ := decouplingWeight a with hφ
  set I := Ioo a (a + L) with hI
  have hw2 := atomTwo_pos
  have hw3 := atomThree_pos
  have hφpos : 0 < φ t := lt_of_lt_of_le (by norm_num) (decouplingWeight_ge a t)
  have out : ∀ x, x ∉ I → I.indicator φ x = 0 := fun x hx => Set.indicator_of_notMem hx φ
  -- an indicator value is bounded by any bound of `φ` on the window
  have ind_le : ∀ x (v : ℝ), 0 ≤ v → (x ∈ I → φ x ≤ v) → I.indicator φ x ≤ v := by
    intro x v hv h
    by_cases hx : x ∈ I
    · rw [Set.indicator_of_mem hx]; exact h hx
    · rw [out x hx]; exact hv
  have ind_r : ∀ x, I.indicator φ x ≤ 207 / 200 := fun x =>
    ind_le x _ (by norm_num) fun _ => decouplingWeight_le a x
  -- it suffices to bound the numerator by `κ φ(t)`
  suffices key : atomTwo * (I.indicator φ (t - Real.log 2) + I.indicator φ (t + Real.log 2)) +
      atomThree * (I.indicator φ (t - Real.log 3) + I.indicator φ (t + Real.log 3)) ≤
      decouplingCeiling * φ t by
    have e : atomTwo * (I.indicator φ (t - Real.log 2) / φ t + I.indicator φ (t + Real.log 2) / φ t) +
        atomThree * (I.indicator φ (t - Real.log 3) / φ t + I.indicator φ (t + Real.log 3) / φ t) =
        (atomTwo * (I.indicator φ (t - Real.log 2) + I.indicator φ (t + Real.log 2)) +
          atomThree * (I.indicator φ (t - Real.log 3) + I.indicator φ (t + Real.log 3))) / φ t := by
      field_simp
    rw [e, div_le_iff₀ hφpos]
    exact key
  by_cases hA : t - a < Real.log 3 - Real.log 2
  · -- `[0, log(3/2))`: neighbours `+log 2 ∈ [log 2, log 3)` (weight `q`) and `+log 3`
    rw [show φ t = 1 from decouplingWeight_of_low hA,
      out (t - Real.log 2) (fun h => by linarith [h.1]),
      out (t - Real.log 3) (fun h => by linarith [h.1])]
    have e1 := ind_le (t + Real.log 2) (89 / 100) (by norm_num) fun _ =>
      (decouplingWeight_of_mid (by linarith) (by linarith)).le
    have e2 := ind_r (t + Real.log 3)
    nlinarith
  by_cases hB : t - a < Real.log 2
  · -- `[log(3/2), log 2)`: neighbours `+log 2` (weight `r`) and `+log 3 ≥ log 4` (weight `1`)
    have hφt : φ t = 207 / 200 := by
      simp only [hφ, decouplingWeight]; rw [if_neg hA, if_pos hB]
    rw [hφt, out (t - Real.log 2) (fun h => by linarith [h.1]),
      out (t - Real.log 3) (fun h => by linarith [h.1])]
    have e1 := ind_r (t + Real.log 2)
    have e2 := ind_le (t + Real.log 3) 1 (by norm_num) fun _ =>
      (decouplingWeight_of_high (by linarith)).le
    nlinarith
  by_cases hC : t - a < Real.log 3
  · -- `[log 2, log 3)`: two `log 2`-neighbours, both of weight `1`; no `log 3`-neighbour
    have hφt : φ t = 89 / 100 := decouplingWeight_of_mid (by linarith) hC
    rw [hφt, out (t - Real.log 3) (fun h => by linarith [h.1]),
      out (t + Real.log 3) (fun h => by linarith [h.2])]
    have e1 := ind_le (t - Real.log 2) 1 (by norm_num) fun _ =>
      (decouplingWeight_of_low (by linarith)).le
    have e2 := ind_le (t + Real.log 2) 1 (by norm_num) fun _ =>
      (decouplingWeight_of_high (by linarith)).le
    nlinarith
  by_cases hD : t - a < 2 * Real.log 2
  · -- `[log 3, log 4)`: neighbours `−log 2` (weight `r`) and `−log 3 < log(4/3)` (weight `1`)
    have hφt : φ t = 207 / 200 := by
      simp only [hφ, decouplingWeight]; rw [if_neg hA, if_neg hB, if_neg hC, if_pos hD]
    rw [hφt, out (t + Real.log 2) (fun h => by linarith [h.2]),
      out (t + Real.log 3) (fun h => by linarith [h.2])]
    have e1 := ind_r (t - Real.log 2)
    have e2 := ind_le (t - Real.log 3) 1 (by norm_num) fun _ =>
      (decouplingWeight_of_low (by linarith)).le
    nlinarith
  · -- `[log 4, L)`: neighbours `−log 2 ∈ [log 2, log 3)` (weight `q`) and `−log 3`
    rw [show φ t = 1 from decouplingWeight_of_high (by linarith),
      out (t + Real.log 2) (fun h => by linarith [h.2]),
      out (t + Real.log 3) (fun h => by linarith [h.2])]
    have e1 := ind_le (t - Real.log 2) (89 / 100) (by norm_num) fun _ =>
      (decouplingWeight_of_mid (by linarith) (by linarith)).le
    have e2 := ind_r (t - Real.log 3)
    nlinarith

/-! ### 3. The bound for one test and for the cone -/

/-- **The `{2, 3}` part of the prime side below `log 6`.** For a test supported in an interval of
length `L ≤ log 6`: `|w₂(k(log 2) + k(−log 2)) + w₃(k(log 3) + k(−log 3))| ≤ κ ∫ |f|²`. -/
theorem abs_twoThreeSide_le_of_window {f : WeilTestFn} {a L : ℝ}
    (hL : L ≤ Real.log 2 + Real.log 3) (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) :
    |atomTwo * ((EF.weilTest f.1 f.1 (Real.log 2)).re + (EF.weilTest f.1 f.1 (-Real.log 2)).re) +
        atomThree * ((EF.weilTest f.1 f.1 (Real.log 3)).re +
          (EF.weilTest f.1 f.1 (-Real.log 3)).re)| ≤ decouplingCeiling * ∫ u, ‖f.1 u‖ ^ 2 := by
  have hfc := f.2.1.continuous
  have hfs := f.2.2
  set φ := decouplingWeight a with hφ
  have hφm := measurable_decouplingWeight a
  have hm : (0 : ℝ) < 89 / 100 := by norm_num
  have hlo := decouplingWeight_ge a
  have hhi := decouplingWeight_le a
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ, F = fun s t => ‖f.1 t‖ ^ 2 *
      ((Ioo a (a + L)).indicator φ (t - s) / φ t + (Ioo a (a + L)).indicator φ (t + s) / φ t) :=
    ⟨_, rfl⟩
  have hS : ∀ s, 2 * |(EF.weilTest f.1 f.1 s).re| ≤ ∫ t, F s t := fun s => by
    rw [hF]; exact two_mul_abs_re_weilTest_le hfc hfs hsupp hφm hm hlo hhi s
  have hI : ∀ s, Integrable (F s) := fun s => by
    rw [hF]; exact integrable_schurIntegrand hfc hfs (measurableSet_Ioo (a := a) (b := a + L))
      hφm hm hlo hhi s
  have hneg : ∀ s, F (-s) = F s := fun s => by
    rw [hF]; funext t; simp only [sub_neg_eq_add, ← sub_eq_add_neg]; ring
  have hpair : ∀ s, |(EF.weilTest f.1 f.1 s).re| + |(EF.weilTest f.1 f.1 (-s)).re| ≤ ∫ t, F s t := by
    intro s
    have h1 := hS s
    have h2 := hS (-s)
    rw [hneg] at h2
    linarith
  have hw2 := atomTwo_pos
  have hw3 := atomThree_pos
  have hcs : HasCompactSupport (fun t => ‖f.1 t‖ ^ 2) :=
    hfs.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have hnorm : Integrable (fun t => ‖f.1 t‖ ^ 2) :=
    (hfc.norm.pow 2).integrable_of_hasCompactSupport hcs
  calc |atomTwo * ((EF.weilTest f.1 f.1 (Real.log 2)).re + (EF.weilTest f.1 f.1 (-Real.log 2)).re) +
        atomThree * ((EF.weilTest f.1 f.1 (Real.log 3)).re + (EF.weilTest f.1 f.1 (-Real.log 3)).re)|
      ≤ atomTwo * (∫ t, F (Real.log 2) t) + atomThree * ∫ t, F (Real.log 3) t := by
        have e2 := hpair (Real.log 2)
        have e3 := hpair (Real.log 3)
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hw2, abs_of_pos hw3]
        gcongr
        · exact (abs_add_le _ _).trans e2
        · exact (abs_add_le _ _).trans e3
    _ = ∫ t, (atomTwo * F (Real.log 2) t + atomThree * F (Real.log 3) t) := by
        rw [integral_add ((hI _).const_mul _) ((hI _).const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ ∫ t, decouplingCeiling * ‖f.1 t‖ ^ 2 := by
        refine integral_mono (((hI _).const_mul _).add ((hI _).const_mul _))
          (hnorm.const_mul _) fun t => ?_
        rw [hF]
        by_cases h0 : f.1 t = 0
        · simp [h0]
        have hb := decouplingWeight_schur_le hL (hsupp t h0)
        simp only
        have : atomTwo * (‖f.1 t‖ ^ 2 * ((Ioo a (a + L)).indicator φ (t - Real.log 2) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 2) / φ t)) +
            atomThree * (‖f.1 t‖ ^ 2 * ((Ioo a (a + L)).indicator φ (t - Real.log 3) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 3) / φ t)) =
            ‖f.1 t‖ ^ 2 * (atomTwo * ((Ioo a (a + L)).indicator φ (t - Real.log 2) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 2) / φ t) +
            atomThree * ((Ioo a (a + L)).indicator φ (t - Real.log 3) / φ t +
              (Ioo a (a + L)).indicator φ (t + Real.log 3) / φ t)) := by ring
        rw [this, mul_comm decouplingCeiling]
        exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = decouplingCeiling * ∫ u, ‖f.1 u‖ ^ 2 := integral_const_mul _ _

/-- The node value of a combination is the weighted sum of the node values of its tests. -/
theorem nodeAt_eq_sum (c : WeilTestFn →₀ ℝ) {n : ℕ} (hn : 2 ≤ n) :
    nodeAt c n = c.sum fun f t => t * logValue f.1 n := by
  rw [nodeAt, dif_pos hn, nodeVector_eq, linearCombination_apply, Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, logVector_apply, smul_eq_mul]

/-- The deviations `(A − W)/‖c‖²` on the cone blind at every prime power outside
`{p^{e(p)} : p ∈ P}`, with every test supported in an open interval of length `L`. -/
def eulerWindowDeviations (P : Finset ℕ) (e : ℕ → ℕ) (L : ℝ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (primePowerNodes \ ↑(eulerNodes P e)) c ∧
    (∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem eulerWindowDeviations_subset (P : Finset ℕ) (e : ℕ → ℕ) (L : ℝ) :
    eulerWindowDeviations P e L ⊆ eulerDeviations P e := by
  rintro x ⟨c, hc, hb, -, hpos, rfl⟩
  exact ⟨c, hc, hb, hpos, rfl⟩

theorem primes_two_three : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  exacts [Nat.prime_two, Nat.prime_three]

theorem eulerNodes_two_three : eulerNodes {2, 3} (fun _ => 1) = {2, 3} := by
  simp [eulerNodes]

theorem eulerPrice_two_three : eulerPrice {2, 3} (fun _ => 1) = atomTwo + atomThree := by
  rw [eulerPrice_eq primes_two_three fun _ _ => le_rfl, Finset.sum_pair (by norm_num)]
  simp [atomTwo, atomThree]

/-- **Below `log 6` the price of `{2, 3}` is at most `κ = 111/100`.** -/
theorem abs_le_of_mem_twoThreeWindowDeviations {L x : ℝ} (hL : L ≤ Real.log 6)
    (hx : x ∈ eulerWindowDeviations {2, 3} (fun _ => 1) L) : |x| ≤ decouplingCeiling := by
  obtain ⟨c, hc, hb, hs, hpos, rfl⟩ := hx
  have hL' : L ≤ Real.log 2 + Real.log 3 := by
    rwa [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)] at hL
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos, nodeArchEnergy_eq_weilEnergy_add_finset _ hb,
    add_sub_cancel_left, eulerNodes_two_three, Finset.sum_pair (by norm_num),
    nodeAt_eq_sum c le_rfl, nodeAt_eq_sum c (by norm_num), Finsupp.mul_sum, Finsupp.mul_sum,
    ← Finsupp.sum_add, WeilOneSided.massOf, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f hf => ?_)
  obtain ⟨a, ha⟩ := hs f hf
  have hbound := abs_twoThreeSide_le_of_window hL' ha
  have e : (ArithmeticFunction.vonMangoldt 2 : ℝ) * (c f * logValue f.1 2) +
      (ArithmeticFunction.vonMangoldt 3 : ℝ) * (c f * logValue f.1 3) =
      c f * (atomTwo * ((EF.weilTest f.1 f.1 (Real.log 2)).re +
          (EF.weilTest f.1 f.1 (-Real.log 2)).re) +
        atomThree * ((EF.weilTest f.1 f.1 (Real.log 3)).re +
          (EF.weilTest f.1 f.1 (-Real.log 3)).re)) := by
    simp only [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three, logValue, Nat.cast_ofNat,
      atomTwo, atomThree, Complex.add_re]
    ring
  rw [e, abs_mul, abs_of_nonneg (hc f)]
  calc c f * |_| ≤ c f * (decouplingCeiling * ∫ u, ‖f.1 u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (hc f)
    _ = decouplingCeiling * (c f * ∫ u, ‖f.1 u‖ ^ 2) := by ring

/-! ### 4. Euler trains with narrow bumps -/

/-- The Euler train `Σ_{A⊆P} σ_A h_N(u − log m_A)` with a bump of index `N`. -/
def wideTrain (N : ℕ) (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∑ A ∈ P.powerset, ((subSign σ A : ℝ) : ℂ) * narrowBumpC N (u - subLog e A)

theorem contDiff_wideTrain (N : ℕ) (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) :
    ContDiff ℝ 2 (wideTrain N P e σ) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (((contDiff_narrowBumpC _).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_wideTrain (N : ℕ) (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) :
    HasCompactSupport (wideTrain N P e σ) :=
  hasCompactSupport_finsetSum _ fun _ _ =>
    ((hasCompactSupport_narrowBumpC _).comp_homeomorph (Homeomorph.subRight _)).mul_left

/-- The Euler train as a Weil test. -/
def wideTrainTestFn (N : ℕ) (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) : WeilTestFn :=
  ⟨wideTrain N P e σ, contDiff_wideTrain N P e σ, hasCompactSupport_wideTrain N P e σ⟩

section WideTrain

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ} (he : ∀ p ∈ P, 1 ≤ e p)
  {σ : ℕ → ℝ} {N : ℕ} (hN : subProd e P ≤ N)

include hP hN in
/-- The autocorrelation of a narrow Euler train at `±log n` is the train coefficient times `∫ h²`. -/
theorem weilTest_wideTrain {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (wideTrain N P e σ) (wideTrain N P e σ) (s * Real.log n) =
      (trainCoeff P e σ (s * Real.log n) : ℂ) * ((∫ t, (narrowBump N t) ^ 2 : ℝ) : ℂ) := by
  refine weilTest_train_select _ (subSign σ) (subLog e) N _ fun A hA B hB hne => ?_
  refine lt_of_le_of_lt ?_ (iteratedPair_sep hP hn s hs A hA B hB hne)
  have : ((subProd e P : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

include hP he hN in
theorem massOf_single_wideTrainTestFn (hσ : ∀ p ∈ P, σ p ^ 2 = 1) :
    massOf (Finsupp.single (wideTrainTestFn N P e σ) 1) =
      (P.powerset.card : ℝ) * ∫ t, (narrowBump N t) ^ 2 := by
  have hk := weilTest_wideTrain hP hN (σ := σ) (e := e) le_rfl 1 (Or.inl rfl)
  rw [one_mul, trainCoeff_zero hP he hσ, Nat.cast_one, Real.log_one,
    RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  have hm : ∫ u, ‖wideTrain N P e σ u‖ ^ 2 =
      (P.powerset.card : ℝ) * ∫ t, (narrowBump N t) ^ 2 := by exact_mod_cast hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  exact hm

include hP he hN in
theorem blindOn_single_wideTrainTestFn :
    BlindOn (primePowerNodes \ ↑(eulerNodes P e)) (Finsupp.single (wideTrainTestFn N P e σ) 1) := by
  intro j ⟨hpp, hj⟩
  have hnot : ∀ p ∈ P, p ^ e p ≠ (j : ℕ) := fun p hp h =>
    hj (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p, hp, h⟩))
  have h0 := trainCoeff_log_eq_zero hP he (σ := σ) hpp hnot
  have e1 := weilTest_wideTrain hP hN (σ := σ) (e := e) hpp.one_lt.le 1 (Or.inl rfl)
  have e2 := weilTest_wideTrain hP hN (σ := σ) (e := e) hpp.one_lt.le (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul, trainCoeff_neg] at e2
  rw [nodeVector_single_test, logVector_apply]
  change logValue (wideTrain N P e σ) j = 0
  rw [logValue, e1, e2, h0]
  simp

include hP he hN in
theorem nodeAt_single_wideTrainTestFn (hσ : ∀ p ∈ P, σ p ^ 2 = 1) {r : ℕ} (hr : r ∈ P) :
    nodeAt (Finsupp.single (wideTrainTestFn N P e σ) 1) (r ^ e r) =
      σ r * massOf (Finsupp.single (wideTrainTestFn N P e σ) 1) /
        Real.sqrt ((r ^ e r : ℕ) : ℝ) := by
  have h2 := two_le_pow hP he hr
  have hc := trainCoeff_log_deleted hP he hσ (σ := σ) hr
  have e1 := weilTest_wideTrain hP hN (σ := σ) (e := e) (n := r ^ e r) (by omega) 1 (Or.inl rfl)
  have e2 := weilTest_wideTrain hP hN (σ := σ) (e := e) (n := r ^ e r) (by omega) (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul, trainCoeff_neg] at e2
  rw [nodeAt, dif_pos h2, nodeVector_single_test, logVector_apply,
    massOf_single_wideTrainTestFn hP he hN hσ, card_powerset_eq_two_mul hr]
  change logValue (wideTrain N P e σ) (r ^ e r) = _
  rw [logValue, e1, e2, hc, ← add_mul, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

include hP in
/-- The train lies in the window `(−ρ, −ρ + log m_P + 1/(2(N+1)))`, `ρ = 1/(4(N+1))`. -/
theorem wideTrain_support {u : ℝ} (hu : wideTrain N P e σ u ≠ 0) :
    u ∈ Ioo (-(1 / (4 * ((N : ℝ) + 1))))
      (-(1 / (4 * ((N : ℝ) + 1))) + (Real.log (subProd e P) + 1 / (2 * ((N : ℝ) + 1)))) := by
  obtain ⟨A, hA, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have hb : narrowBumpC N (u - subLog e A) ≠ 0 := fun h => hm (by rw [h, mul_zero])
  have hr : |u - subLog e A| < 1 / (4 * ((N : ℝ) + 1)) := by
    by_contra h
    push Not at h
    apply hb
    have := (narrowBump N).zero_of_le_dist (x := u - subLog e A) (by rw [Real.dist_eq, sub_zero]; exact h)
    simp only [narrowBumpC, this, Complex.ofReal_zero]
  have hAP := Finset.mem_powerset.mp hA
  have hApos := subProd_pos (e := e) fun p hp => hP p (hAP hp)
  have h0 : 0 ≤ subLog e A := Real.log_nonneg (by exact_mod_cast hApos)
  have h1 : subLog e A ≤ Real.log (subProd e P) :=
    Real.log_le_log (by exact_mod_cast hApos) (by exact_mod_cast subProd_le hP hAP)
  have e2 : 1 / (2 * ((N : ℝ) + 1)) = 2 * (1 / (4 * ((N : ℝ) + 1))) := by field_simp; ring
  rw [abs_lt] at hr
  constructor <;> linarith

end WideTrain

/-! ### 5. Exact prices on long windows and the jump at `log 6` -/

/-- **Euler prices are attained on every window longer than `log m_P`.** -/
theorem deviation_mem_eulerWindowDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) {L : ℝ} (hL : Real.log (subProd e P) < L) {s : ℝ} (hs : s ^ 2 = 1) :
    s * eulerPrice P e ∈ eulerWindowDeviations P e L := by
  classical
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (L - Real.log (subProd e P)))
  set N := max k (subProd e P) with hNdef
  have hN : subProd e P ≤ N := le_max_right _ _
  have hNL : Real.log (subProd e P) + 1 / (2 * ((N : ℝ) + 1)) < L := by
    have hpos : 0 < L - Real.log (subProd e P) := by linarith
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast le_max_left k (subProd e P)
    have : 1 / (2 * ((N : ℝ) + 1)) < L - Real.log (subProd e P) := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hk
      nlinarith
    linarith
  have hσ : ∀ p ∈ P, (fun _ : ℕ => s) p ^ 2 = 1 := fun _ _ => hs
  have hmass := massOf_single_wideTrainTestFn hP he hN hσ
  have hpos : 0 < massOf (Finsupp.single (wideTrainTestFn N P e fun _ => s) 1) := by
    rw [hmass]
    have : (0 : ℝ) < P.powerset.card := by exact_mod_cast Finset.card_pos.mpr ⟨∅, by simp⟩
    exact mul_pos this (integral_narrowBump_sq_pos _)
  have hb := blindOn_single_wideTrainTestFn hP he hN (σ := fun _ => s)
  refine ⟨_, fun f => ?_, hb, fun g hg => ?_, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hg
    split_ifs at hg with hfg
    · rw [← hfg]
      refine ⟨-(1 / (4 * ((N : ℝ) + 1))), fun u hu => ?_⟩
      have := wideTrain_support hP (N := N) (e := e) (σ := fun _ => s) hu
      exact ⟨this.1, this.2.trans (by linarith)⟩
    · exact absurd rfl hg
  · rw [nodeArchEnergy_eq_weilEnergy_add_finset _ hb, add_sub_cancel_left, eulerNodes,
      Finset.sum_image (injOn_eulerNodes hP he), eulerPrice, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [nodeAt_single_wideTrainTestFn hP he hN hσ hp]
    field_simp

/-- **The exact price on long windows: greatest deviation `Σ_{p∈P} Λ(m_p)/√m_p`.** -/
theorem isGreatest_eulerWindowDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) {L : ℝ} (hL : Real.log (subProd e P) < L) :
    IsGreatest (eulerWindowDeviations P e L) (eulerPrice P e) :=
  ⟨by simpa using deviation_mem_eulerWindowDeviations hP he hL (s := 1) (by norm_num),
    fun _ hx => (isGreatest_eulerDeviations hP he).2 (eulerWindowDeviations_subset P e L hx)⟩

/-- **The exact price on long windows: least deviation `−Σ_{p∈P} Λ(m_p)/√m_p`.** -/
theorem isLeast_eulerWindowDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) {L : ℝ} (hL : Real.log (subProd e P) < L) :
    IsLeast (eulerWindowDeviations P e L) (-eulerPrice P e) :=
  ⟨by simpa using deviation_mem_eulerWindowDeviations hP he hL (s := -1) (by norm_num),
    fun _ hx => (isLeast_eulerDeviations hP he).2 (eulerWindowDeviations_subset P e L hx)⟩

theorem subProd_two_three : subProd (fun _ => 1) ({2, 3} : Finset ℕ) = 6 := by
  simp [subProd]

/-- **Above `log 6` the prices of `2` and `3` add**: greatest deviation `w₂ + w₃`. -/
theorem isGreatest_twoThreeWindowDeviations {L : ℝ} (hL : Real.log 6 < L) :
    IsGreatest (eulerWindowDeviations {2, 3} (fun _ => 1) L) (atomTwo + atomThree) := by
  rw [← eulerPrice_two_three]
  exact isGreatest_eulerWindowDeviations primes_two_three (fun _ _ => le_rfl)
    (by rw [subProd_two_three]; exact_mod_cast hL)

/-- **Above `log 6`**: least deviation `−(w₂ + w₃)`. -/
theorem isLeast_twoThreeWindowDeviations {L : ℝ} (hL : Real.log 6 < L) :
    IsLeast (eulerWindowDeviations {2, 3} (fun _ => 1) L) (-(atomTwo + atomThree)) := by
  rw [← eulerPrice_two_three]
  exact isLeast_eulerWindowDeviations primes_two_three (fun _ _ => le_rfl)
    (by rw [subProd_two_three]; exact_mod_cast hL)

/-- **The price of `{2, 3}` jumps at `log 6`.** On windows of length `L ≤ log 6` the supremum of the
deviations is at most `111/100`; on every longer window it is `w₂ + w₃ > 111/100`. -/
theorem twoThree_price_jump {L L' : ℝ} (hL : L ≤ Real.log 6) (hL' : Real.log 6 < L') :
    sSup (eulerWindowDeviations {2, 3} (fun _ => 1) L) ≤ decouplingCeiling ∧
      decouplingCeiling < sSup (eulerWindowDeviations {2, 3} (fun _ => 1) L') := by
  refine ⟨Real.sSup_le (fun x hx => (le_abs_self x).trans
    (abs_le_of_mem_twoThreeWindowDeviations hL hx)) (by unfold decouplingCeiling; norm_num), ?_⟩
  rw [(isGreatest_twoThreeWindowDeviations hL').csSup_eq]
  exact decouplingCeiling_lt

end

end GaloisForLFunctions.BiScaleUncertainty
