import GaloisForLFunctions.RHTower.Sieve.HeathBrownPrimitiveRayMass

/-!
# Exact primitive-ray reindexing of Heath--Brown collision squares

Every positive lattice pair has a unique coprime direction and positive gcd scale.  Restricting
that equivalence to a bounded logarithmic collision square identifies its cardinality exactly with
the multiplicity-weighted primitive ray mass.  The final theorem combines this source reindexing
with the two-scale ray estimate and discharges cofactor ordering internally by coordinate swap.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Positive lattice pairs. -/
def HeathBrownPositivePair := {p : ℕ × ℕ // 0 < p.1 ∧ 0 < p.2}

/-- Positive coprime direction and positive common scale. -/
def HeathBrownPrimitiveRayIndex :=
  {p : ℕ × ℕ // 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2} × {k : ℕ // 0 < k}

/-- Reassemble a primitive direction and scale. -/
def heathBrownPrimitiveRayIndexToPositivePair
    (q : HeathBrownPrimitiveRayIndex) : HeathBrownPositivePair :=
  ⟨(q.1.1.1 * q.2.1, q.1.1.2 * q.2.1),
    ⟨Nat.mul_pos q.1.2.1 q.2.2, Nat.mul_pos q.1.2.2.1 q.2.2⟩⟩

/-- Extract gcd scale and coprime quotients. -/
def heathBrownPositivePairToPrimitiveRayIndex
    (p : HeathBrownPositivePair) : HeathBrownPrimitiveRayIndex :=
  let g := Nat.gcd p.1.1 p.1.2
  have hg : 0 < g := Nat.gcd_pos_of_pos_left p.1.2 p.2.1
  have hg1 : g ≤ p.1.1 := by
    dsimp [g]
    exact Nat.gcd_le_left p.1.2 p.2.1
  have hg2 : g ≤ p.1.2 := by
    dsimp [g]
    exact Nat.gcd_le_right p.1.1 p.2.2
  (⟨(p.1.1 / g, p.1.2 / g),
      ⟨Nat.div_pos hg1 hg,
        Nat.div_pos hg2 hg,
        Nat.coprime_div_gcd_div_gcd hg⟩⟩,
    ⟨g, hg⟩)

theorem heathBrownPrimitiveRayIndexToPositivePair_leftInverse :
    Function.LeftInverse heathBrownPositivePairToPrimitiveRayIndex
      heathBrownPrimitiveRayIndexToPositivePair := by
  rintro ⟨⟨⟨u1, u2⟩, hu1, hu2, hcop⟩, ⟨k, hk⟩⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · change (u1 * k) / Nat.gcd (u1 * k) (u2 * k) = u1
      rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
      simpa [Nat.mul_comm] using Nat.mul_div_cancel_left u1 hk
    · change (u2 * k) / Nat.gcd (u1 * k) (u2 * k) = u2
      rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
      simpa [Nat.mul_comm] using Nat.mul_div_cancel_left u2 hk
  · apply Subtype.ext
    change Nat.gcd (u1 * k) (u2 * k) = k
    rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]

theorem heathBrownPrimitiveRayIndexToPositivePair_rightInverse :
    Function.RightInverse heathBrownPositivePairToPrimitiveRayIndex
      heathBrownPrimitiveRayIndexToPositivePair := by
  rintro ⟨⟨n1, n2⟩, hn1, hn2⟩
  apply Subtype.ext
  apply Prod.ext
  · change n1 / Nat.gcd n1 n2 * Nat.gcd n1 n2 = n1
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left n1 n2)
  · change n2 / Nat.gcd n1 n2 * Nat.gcd n1 n2 = n2
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right n1 n2)

/-- Unique primitive-ray decomposition of every positive lattice pair. -/
def heathBrownPrimitiveRayIndexEquivPositivePair :
    HeathBrownPrimitiveRayIndex ≃ HeathBrownPositivePair where
  toFun := heathBrownPrimitiveRayIndexToPositivePair
  invFun := heathBrownPositivePairToPrimitiveRayIndex
  left_inv := heathBrownPrimitiveRayIndexToPositivePair_leftInverse
  right_inv := heathBrownPrimitiveRayIndexToPositivePair_rightInverse

/-- Common positive scaling cancels from the real ratio defining a logarithmic window. -/
theorem abs_log_ratio_mul_scale
    (m1 m2 : ℝ) {u1 u2 k : ℕ} (hk : 0 < k) :
    |Real.log ((m1 * ((k * u1 : ℕ) : ℝ)) / (m2 * ((k * u2 : ℕ) : ℝ)))| =
      |Real.log ((m1 * (u1 : ℝ)) / (m2 * (u2 : ℝ)))| := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  congr 2
  push_cast
  calc
    (m1 * ((k : ℝ) * (u1 : ℝ))) / (m2 * ((k : ℝ) * (u2 : ℝ))) =
        ((m1 * (u1 : ℝ)) * (k : ℝ)) / ((m2 * (u2 : ℝ)) * (k : ℝ)) := by ring
    _ = (m1 * (u1 : ℝ)) / (m2 * (u2 : ℝ)) := by
      exact mul_div_mul_right _ _ hkR

/-- Positive square pairs satisfying one logarithmic collision condition. -/
def heathBrownPositiveLogCollisionSquare
    (N : ℕ) (m1 m2 delta : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter fun p =>
    |Real.log ((m1 * (p.1 : ℝ)) / (m2 * (p.2 : ℝ)))| ≤ delta

theorem mem_heathBrownPositiveLogCollisionSquare
    {N : ℕ} {m1 m2 delta : ℝ} {p : ℕ × ℕ} :
    p ∈ heathBrownPositiveLogCollisionSquare N m1 m2 delta ↔
      1 ≤ p.1 ∧ p.1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 ≤ N ∧
        |Real.log ((m1 * (p.1 : ℝ)) / (m2 * (p.2 : ℝ)))| ≤ delta := by
  simp only [heathBrownPositiveLogCollisionSquare, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Finite primitive direction/scale indices for the same collision square. -/
def heathBrownPrimitiveLogRayIndexFinset
    (N : ℕ) (m1 m2 delta : ℝ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 N).sigma fun k =>
    (heathBrownPrimitiveLogWindow N m1 m2 delta).filter fun p =>
      k * heathBrownDirectionHeight p ≤ N

theorem mem_heathBrownPrimitiveLogRayIndexFinset
    {N : ℕ} {m1 m2 delta : ℝ} {q : Σ _ : ℕ, ℕ × ℕ} :
    q ∈ heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta ↔
      1 ≤ q.1 ∧ q.1 ≤ N ∧
        q.2 ∈ heathBrownPrimitiveLogWindow N m1 m2 delta ∧
          q.1 * heathBrownDirectionHeight q.2 ≤ N := by
  simp only [heathBrownPrimitiveLogRayIndexFinset, Finset.mem_sigma,
    Finset.mem_Icc, Finset.mem_filter]
  tauto

/-- Ray-index cardinality is exactly the multiplicity-weighted ray mass. -/
theorem card_heathBrownPrimitiveLogRayIndexFinset
    (N : ℕ) (m1 m2 delta : ℝ) :
    #(heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta) =
      heathBrownPrimitiveLogRayMass N m1 m2 delta := by
  rw [heathBrownPrimitiveLogRayIndexFinset, Finset.card_sigma]
  exact (heathBrownPrimitiveLogRayMass_layerCake N m1 m2 delta).symm

/-- Reassemble one finite ray index as a lattice pair. -/
def heathBrownLogRayIndexToPair (q : Σ _ : ℕ, ℕ × ℕ) : ℕ × ℕ :=
  (q.1 * q.2.1, q.1 * q.2.2)

/-- Extract the gcd scale and reduced direction from a positive lattice pair. -/
def heathBrownLogPairToRayIndex (p : ℕ × ℕ) : Σ _ : ℕ, ℕ × ℕ :=
  ⟨Nat.gcd p.1 p.2, (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)⟩

theorem heathBrownLogPairToRayIndex_leftInverse_of_mem
    {N : ℕ} {m1 m2 delta : ℝ} {q : Σ _ : ℕ, ℕ × ℕ}
    (hq : q ∈ heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta) :
    heathBrownLogPairToRayIndex (heathBrownLogRayIndexToPair q) = q := by
  have hq' := mem_heathBrownPrimitiveLogRayIndexFinset.mp hq
  have hp := mem_heathBrownPrimitiveLogWindow_height.mp hq'.2.2.1
  have hk : 0 < q.1 := hq'.1
  have hgcd : Nat.gcd (q.1 * q.2.1) (q.1 * q.2.2) = q.1 := by
    rw [Nat.gcd_mul_left, hp.2.2.2.1.gcd_eq_one, mul_one]
  apply Sigma.ext
  · exact hgcd
  · simp only [heathBrownLogPairToRayIndex, heathBrownLogRayIndexToPair, hgcd]
    apply heq_of_eq
    apply Prod.ext
    · exact Nat.mul_div_cancel_left q.2.1 hk
    · exact Nat.mul_div_cancel_left q.2.2 hk

theorem heathBrownLogPairToRayIndex_rightInverse_of_mem
    {N : ℕ} {m1 m2 delta : ℝ} {p : ℕ × ℕ}
    (_hp : p ∈ heathBrownPositiveLogCollisionSquare N m1 m2 delta) :
    heathBrownLogRayIndexToPair (heathBrownLogPairToRayIndex p) = p := by
  apply Prod.ext
  · exact Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
  · exact Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)

theorem heathBrownLogRayIndexToPair_mem
    {N : ℕ} {m1 m2 delta : ℝ} {q : Σ _ : ℕ, ℕ × ℕ}
    (hq : q ∈ heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta) :
    heathBrownLogRayIndexToPair q ∈
      heathBrownPositiveLogCollisionSquare N m1 m2 delta := by
  have hq' := mem_heathBrownPrimitiveLogRayIndexFinset.mp hq
  have hp := mem_heathBrownPrimitiveLogWindow_height.mp hq'.2.2.1
  apply mem_heathBrownPositiveLogCollisionSquare.mpr
  have h1 : q.1 * q.2.1 ≤ N :=
    (Nat.mul_le_mul_left q.1 (Nat.le_max_left _ _)).trans hq'.2.2.2
  have h2 : q.1 * q.2.2 ≤ N :=
    (Nat.mul_le_mul_left q.1 (Nat.le_max_right _ _)).trans hq'.2.2.2
  refine ⟨Nat.mul_pos hq'.1 hp.1, h1, Nat.mul_pos hq'.1 hp.2.1, h2, ?_⟩
  change |Real.log ((m1 * (((q.1 * q.2.1 : ℕ) : ℝ))) /
    (m2 * (((q.1 * q.2.2 : ℕ) : ℝ))))| ≤ delta
  rw [abs_log_ratio_mul_scale m1 m2 hq'.1]
  exact hp.2.2.2.2

theorem heathBrownLogPairToRayIndex_mem
    {N : ℕ} {m1 m2 delta : ℝ} {p : ℕ × ℕ}
    (hp : p ∈ heathBrownPositiveLogCollisionSquare N m1 m2 delta) :
    heathBrownLogPairToRayIndex p ∈
      heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta := by
  have hp' := mem_heathBrownPositiveLogCollisionSquare.mp hp
  let g := Nat.gcd p.1 p.2
  have hg : 0 < g := Nat.gcd_pos_of_pos_left p.2 hp'.1
  have hg1 : g ≤ p.1 := by
    dsimp [g]
    exact Nat.gcd_le_left p.2 (by omega)
  have hg2 : g ≤ p.2 := by
    dsimp [g]
    exact Nat.gcd_le_right p.1 (by omega)
  have hu1 : 0 < p.1 / g := Nat.div_pos hg1 hg
  have hu2 : 0 < p.2 / g := Nat.div_pos hg2 hg
  have hcop : Nat.Coprime (p.1 / g) (p.2 / g) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hmul1 : g * (p.1 / g) = p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
  have hmul2 : g * (p.2 / g) = p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
  have hheight : heathBrownDirectionHeight (p.1 / g, p.2 / g) ≤ N := by
    rw [heathBrownDirectionHeight, max_le_iff]
    exact ⟨(Nat.div_le_self p.1 g).trans hp'.2.1,
      (Nat.div_le_self p.2 g).trans hp'.2.2.2.1⟩
  have hlog :
      |Real.log ((m1 * ((p.1 / g : ℕ) : ℝ)) /
        (m2 * ((p.2 / g : ℕ) : ℝ)))| ≤ delta := by
    rw [← abs_log_ratio_mul_scale m1 m2 hg, hmul1, hmul2]
    exact hp'.2.2.2.2
  apply mem_heathBrownPrimitiveLogRayIndexFinset.mpr
  dsimp [heathBrownLogPairToRayIndex, g]
  refine ⟨hg, hg1.trans hp'.2.1, ?_, ?_⟩
  · apply mem_heathBrownPrimitiveLogWindow_height.mpr
    exact ⟨hu1, hu2, hheight, hcop, hlog⟩
  · change g * max (p.1 / g) (p.2 / g) ≤ N
    rcases le_total (p.1 / g) (p.2 / g) with hle | hle
    · rw [max_eq_right hle, hmul2]
      exact hp'.2.2.2.1
    · rw [max_eq_left hle, hmul1]
      exact hp'.2.1

/-- Exact finite bijection between the positive collision square and primitive direction/scale
indices. -/
theorem card_heathBrownPositiveLogCollisionSquare_eq_rayIndex
    (N : ℕ) (m1 m2 delta : ℝ) :
    #(heathBrownPositiveLogCollisionSquare N m1 m2 delta) =
      #(heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta) := by
  calc
    #(heathBrownPositiveLogCollisionSquare N m1 m2 delta) =
        ∑ p ∈ heathBrownPositiveLogCollisionSquare N m1 m2 delta, 1 := by simp
    _ = ∑ q ∈ heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta, 1 := by
      exact (Finset.sum_nbij'
        (i := heathBrownLogRayIndexToPair)
        (j := heathBrownLogPairToRayIndex)
        (fun q hq => heathBrownLogRayIndexToPair_mem hq)
        (fun p hp => heathBrownLogPairToRayIndex_mem hp)
        (fun q hq => heathBrownLogPairToRayIndex_leftInverse_of_mem hq)
        (fun p hp => heathBrownLogPairToRayIndex_rightInverse_of_mem hp)
        (fun q hq => rfl)).symm
    _ = #(heathBrownPrimitiveLogRayIndexFinset N m1 m2 delta) := by simp

/-- **Exact primitive-ray reindexing of a positive logarithmic collision square.** -/
theorem card_heathBrownPositiveLogCollisionSquare_eq_rayMass
    (N : ℕ) (m1 m2 delta : ℝ) :
    #(heathBrownPositiveLogCollisionSquare N m1 m2 delta) =
      heathBrownPrimitiveLogRayMass N m1 m2 delta := by
  rw [card_heathBrownPositiveLogCollisionSquare_eq_rayIndex,
    card_heathBrownPrimitiveLogRayIndexFinset]

/-- Difference-of-logs and log-ratio presentations agree for positive integer products. -/
theorem abs_log_natProducts_sub_eq_abs_log_ratio
    (m1 m2 : ℕ+) {n1 n2 : ℕ} (hn1 : 0 < n1) (hn2 : 0 < n2) :
    |Real.log (((m1 : ℕ) * n1 : ℕ) : ℝ) -
        Real.log (((m2 : ℕ) * n2 : ℕ) : ℝ)| =
      |Real.log ((((m1 : ℕ) : ℝ) * (n1 : ℝ)) /
        (((m2 : ℕ) : ℝ) * (n2 : ℝ)))| := by
  have h1 : (((m1 : ℕ) : ℝ) * (n1 : ℝ)) ≠ 0 := by positivity
  have h2 : (((m2 : ℕ) : ℝ) * (n2 : ℝ)) ≠ 0 := by positivity
  push_cast
  rw [Real.log_div h1 h2]

/-- Literal closed near-product collision square in Heath--Brown's difference-of-logs form. -/
def heathBrownPositiveProductLogCollisionSquare
    (N : ℕ) (m1 m2 : ℕ+) (delta : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter fun p =>
    |Real.log (((m1 : ℕ) * p.1 : ℕ) : ℝ) -
      Real.log (((m2 : ℕ) * p.2 : ℕ) : ℝ)| ≤ delta

/-- Source difference-of-logs collision square equals the ratio-form square exactly. -/
theorem heathBrownPositiveProductLogCollisionSquare_eq_ratio
    (N : ℕ) (m1 m2 : ℕ+) (delta : ℝ) :
    heathBrownPositiveProductLogCollisionSquare N m1 m2 delta =
      heathBrownPositiveLogCollisionSquare N (m1 : ℕ) (m2 : ℕ) delta := by
  apply Finset.filter_congr
  intro p hp
  have hp' := Finset.mem_product.mp hp
  have hn1 : 0 < p.1 := (Finset.mem_Icc.mp hp'.1).1
  have hn2 : 0 < p.2 := (Finset.mem_Icc.mp hp'.2).1
  rw [abs_log_natProducts_sub_eq_abs_log_ratio m1 m2 hn1 hn2]

/-- **Literal source collision-square reindexing.**  The difference-of-logs count is exactly the
primitive logarithmic ray mass. -/
theorem card_heathBrownPositiveProductLogCollisionSquare_eq_rayMass
    (N : ℕ) (m1 m2 : ℕ+) (delta : ℝ) :
    #(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) =
      heathBrownPrimitiveLogRayMass N (m1 : ℕ) (m2 : ℕ) delta := by
  rw [heathBrownPositiveProductLogCollisionSquare_eq_ratio,
    card_heathBrownPositiveLogCollisionSquare_eq_rayMass]

theorem prod_swap_mem_heathBrownPositiveProductLogCollisionSquare
    {N : ℕ} {m1 m2 : ℕ+} {delta : ℝ} {p : ℕ × ℕ} :
    p.swap ∈ heathBrownPositiveProductLogCollisionSquare N m2 m1 delta ↔
      p ∈ heathBrownPositiveProductLogCollisionSquare N m1 m2 delta := by
  simp only [heathBrownPositiveProductLogCollisionSquare, Finset.mem_filter,
    Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp2, hp1⟩, hlog⟩
    exact ⟨⟨hp1, hp2⟩, by simpa [abs_sub_comm] using hlog⟩
  · rintro ⟨⟨hp1, hp2⟩, hlog⟩
    exact ⟨⟨hp2, hp1⟩, by simpa [abs_sub_comm] using hlog⟩

/-- Swapping cofactor labels and dense coordinates preserves the literal collision count. -/
theorem card_heathBrownPositiveProductLogCollisionSquare_swap
    (N : ℕ) (m1 m2 : ℕ+) (delta : ℝ) :
    #(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) =
      #(heathBrownPositiveProductLogCollisionSquare N m2 m1 delta) := by
  calc
    #(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) =
        ∑ p ∈ heathBrownPositiveProductLogCollisionSquare N m1 m2 delta, 1 := by simp
    _ = ∑ p ∈ heathBrownPositiveProductLogCollisionSquare N m2 m1 delta, 1 := by
      exact (Finset.sum_nbij'
        (i := Prod.swap)
        (j := Prod.swap)
        (fun p hp => prod_swap_mem_heathBrownPositiveProductLogCollisionSquare.mpr hp)
        (fun p hp => prod_swap_mem_heathBrownPositiveProductLogCollisionSquare.mpr hp)
        (fun p hp => Prod.swap_swap p)
        (fun p hp => Prod.swap_swap p)
        (fun p hp => rfl)).symm
    _ = #(heathBrownPositiveProductLogCollisionSquare N m2 m1 delta) := by simp

/-- Ordered-cofactor form of the literal source two-scale collision inequality. -/
theorem cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_ordered
    {N N0 : ℕ} (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N)
    {m1 m2 : ℕ+} (hm : (m2 : ℕ) ≤ (m1 : ℕ))
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (#(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) : ℝ) ≤
      15 * delta * (N : ℝ) ^ (2 : ℕ) +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) := by
  rw [card_heathBrownPositiveProductLogCollisionSquare_eq_rayMass,
    card_heathBrownPositiveProductLogCollisionSquare_eq_rayMass]
  apply cast_heathBrownPrimitiveLogRayMass_le_twoScale hN0 hN0N
  · positivity
  · positivity
  · exact_mod_cast hm
  · exact hdelta0
  · exact hdelta1

/-- **Unconditional literal Heath--Brown two-scale collision inequality.**  Cofactor ordering is
discharged internally by swapping the two dense coordinates. -/
theorem cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale
    {N N0 : ℕ} (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N)
    (m1 m2 : ℕ+) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (#(heathBrownPositiveProductLogCollisionSquare N m1 m2 delta) : ℝ) ≤
      15 * delta * (N : ℝ) ^ (2 : ℕ) +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (#(heathBrownPositiveProductLogCollisionSquare N0 m1 m2 delta) : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) := by
  rcases le_total (m2 : ℕ) (m1 : ℕ) with hm | hm
  · exact cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_ordered
      hN0 hN0N hm hdelta0 hdelta1
  · rw [card_heathBrownPositiveProductLogCollisionSquare_swap N m1 m2,
      card_heathBrownPositiveProductLogCollisionSquare_swap N0 m1 m2]
    exact cast_card_heathBrownPositiveProductLogCollisionSquare_le_twoScale_ordered
      hN0 hN0N hm hdelta0 hdelta1

end

end RHTower.Sieve
