import GaloisForLFunctions.RHTower.Sieve.HeathBrownPrimitiveLogWindow
import GaloisForLFunctions.RHTower.SquarefreeLowerDensity
import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples

namespace RHTower.Sieve

open Finset

noncomputable section

theorem sum_natDiv_eq_sum_card_mul_le
    {alpha : Type*} [DecidableEq alpha] (S : Finset alpha)
    (height : alpha → ℕ) (hheight : ∀ x ∈ S, 0 < height x) (N : ℕ) :
    ∑ x ∈ S, N / height x =
      ∑ k ∈ Finset.Icc 1 N, #(S.filter fun x => k * height x ≤ N) := by
  classical
  have hpoint : ∀ x ∈ S, N / height x =
      ∑ k ∈ Finset.Icc 1 N, if k * height x ≤ N then 1 else 0 := by
    intro x hx
    have hpos := hheight x hx
    have hfilter : (Finset.Icc 1 N).filter (fun k => k * height x ≤ N) =
        Finset.Icc 1 (N / height x) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      rw [Nat.le_div_iff_mul_le hpos]
      constructor
      · rintro ⟨⟨hk1, _⟩, hkN⟩
        exact ⟨hk1, hkN⟩
      · rintro ⟨hk1, hkN⟩
        have hkmul : k ≤ k * height x := by
          exact Nat.le_mul_of_pos_right k hpos
        exact ⟨⟨hk1, hkmul.trans hkN⟩, hkN⟩
    rw [← Finset.sum_filter, hfilter]
    simp
  calc
    ∑ x ∈ S, N / height x =
        ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 N,
          if k * height x ≤ N then 1 else 0 := by
      exact Finset.sum_congr rfl hpoint
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ x ∈ S,
          if k * height x ≤ N then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 1 N, #(S.filter fun x => k * height x ≤ N) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      simp

/-- A layer-cake identity with a supplied upper bound for every quotient. -/
theorem sum_natDiv_eq_sum_card_mul_le_bounded
    {alpha : Type*} [DecidableEq alpha] (S : Finset alpha)
    (height : alpha → ℕ) (hheight : ∀ x ∈ S, 0 < height x)
    (N K : ℕ) (hquot : ∀ x ∈ S, N / height x ≤ K) :
    ∑ x ∈ S, N / height x =
      ∑ k ∈ Finset.Icc 1 K, #(S.filter fun x => k * height x ≤ N) := by
  classical
  have hpoint : ∀ x ∈ S, N / height x =
      ∑ k ∈ Finset.Icc 1 K, if k * height x ≤ N then 1 else 0 := by
    intro x hx
    have hpos := hheight x hx
    have hfilter : (Finset.Icc 1 K).filter (fun k => k * height x ≤ N) =
        Finset.Icc 1 (N / height x) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hk1, _⟩, hkmul⟩
        exact ⟨hk1, (Nat.le_div_iff_mul_le hpos).mpr hkmul⟩
      · rintro ⟨hk1, hkdiv⟩
        exact ⟨⟨hk1, hkdiv.trans (hquot x hx)⟩,
          (Nat.le_div_iff_mul_le hpos).mp hkdiv⟩
    rw [← Finset.sum_filter, hfilter]
    simp
  calc
    ∑ x ∈ S, N / height x =
        ∑ x ∈ S, ∑ k ∈ Finset.Icc 1 K,
          if k * height x ≤ N then 1 else 0 := by
      exact Finset.sum_congr rfl hpoint
    _ = ∑ k ∈ Finset.Icc 1 K, ∑ x ∈ S,
          if k * height x ≤ N then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 1 K, #(S.filter fun x => k * height x ≤ N) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      simp

/-- A uniform bound for the finite inverse-square mass beginning at one. -/
theorem sum_inv_sq_Icc_one_le {K : ℕ} (hK : 1 ≤ K) :
    ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 7 / 4 := by
  rcases hK.eq_or_lt with rfl | hK'
  · norm_num
  · have hK2 : 2 ≤ K := by omega
    have hsplit : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have htail := RHTower.sum_inv_sq_Icc_le hK2
    have hnonneg : (0 : ℝ) ≤ ((K : ℝ)⁻¹) := by positivity
    norm_num only [Nat.cast_one, one_pow, div_one]
    calc
      1 + ∑ k ∈ Finset.Icc 2 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤
          1 + (3 / 4 - 1 / (K : ℝ)) := by linarith
      _ ≤ 7 / 4 := by
        rw [one_div]
        linarith

/-- Height of a positive primitive direction. -/
def heathBrownDirectionHeight (p : ℕ × ℕ) : ℕ := max p.1 p.2

/-- Total number of positive lattice points on primitive collision rays of height at most `N`. -/
def heathBrownPrimitiveLogRayMass
    (N : ℕ) (m1 m2 delta : ℝ) : ℕ :=
  ∑ p ∈ heathBrownPrimitiveLogWindow N m1 m2 delta,
    N / heathBrownDirectionHeight p

theorem heathBrownDirectionHeight_pos_of_mem
    {N : ℕ} {m1 m2 delta : ℝ} {p : ℕ × ℕ}
    (hp : p ∈ heathBrownPrimitiveLogWindow N m1 m2 delta) :
    0 < heathBrownDirectionHeight p := by
  have hp' := mem_heathBrownPrimitiveSquare.mp
    (mem_heathBrownPrimitiveLogWindow.mp hp).1
  exact lt_of_lt_of_le hp'.1 (Nat.le_max_left _ _)

/-- Exact finite layer cake for primitive-ray multiplicity. -/
theorem heathBrownPrimitiveLogRayMass_layerCake
    (N : ℕ) (m1 m2 delta : ℝ) :
    heathBrownPrimitiveLogRayMass N m1 m2 delta =
      ∑ k ∈ Finset.Icc 1 N,
        #((heathBrownPrimitiveLogWindow N m1 m2 delta).filter fun p =>
          k * heathBrownDirectionHeight p ≤ N) := by
  exact sum_natDiv_eq_sum_card_mul_le _ _
    (fun p hp => heathBrownDirectionHeight_pos_of_mem hp) N

theorem mem_heathBrownPrimitiveLogWindow_height
    {N : ℕ} {m1 m2 delta : ℝ} {p : ℕ × ℕ} :
    p ∈ heathBrownPrimitiveLogWindow N m1 m2 delta ↔
      1 ≤ p.1 ∧ 1 ≤ p.2 ∧ heathBrownDirectionHeight p ≤ N ∧
        Nat.Coprime p.1 p.2 ∧
          |Real.log ((m1 * (p.1 : ℝ)) / (m2 * (p.2 : ℝ)))| ≤ delta := by
  rw [mem_heathBrownPrimitiveLogWindow, mem_heathBrownPrimitiveSquare]
  simp only [heathBrownDirectionHeight, max_le_iff]
  tauto

/-- Restricting a larger primitive window by height recovers the smaller window exactly. -/
theorem filter_heathBrownPrimitiveLogWindow_height_le
    {N N0 : ℕ} (hN0N : N0 ≤ N) (m1 m2 delta : ℝ) :
    (heathBrownPrimitiveLogWindow N m1 m2 delta).filter
        (fun p => heathBrownDirectionHeight p ≤ N0) =
      heathBrownPrimitiveLogWindow N0 m1 m2 delta := by
  ext p
  simp only [Finset.mem_filter, mem_heathBrownPrimitiveLogWindow_height]
  constructor
  · rintro ⟨⟨hp1, hp2, _, hcop, hlog⟩, hp0⟩
    exact ⟨hp1, hp2, hp0, hcop, hlog⟩
  · rintro ⟨hp1, hp2, hp0, hcop, hlog⟩
    exact ⟨⟨hp1, hp2, hp0.trans hN0N, hcop, hlog⟩, hp0⟩

/-- Low primitive rays at scale `N` are controlled by their multiplicity at scale `N0`, plus one
endpoint for each surviving direction. -/
theorem sum_low_primitiveLogWindow_natDiv_le
    {N N0 : ℕ} (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N)
    (m1 m2 delta : ℝ) :
    ∑ p ∈ (heathBrownPrimitiveLogWindow N m1 m2 delta).filter
        (fun p => heathBrownDirectionHeight p ≤ N0),
        N / heathBrownDirectionHeight p ≤
      (N / N0 + 1) *
        (heathBrownPrimitiveLogRayMass N0 m1 m2 delta +
          (heathBrownPrimitiveLogWindow N0 m1 m2 delta).card) := by
  rw [filter_heathBrownPrimitiveLogWindow_height_le hN0N]
  calc
    ∑ p ∈ heathBrownPrimitiveLogWindow N0 m1 m2 delta,
        N / heathBrownDirectionHeight p ≤
      ∑ p ∈ heathBrownPrimitiveLogWindow N0 m1 m2 delta,
        (N / N0 + 1) * (N0 / heathBrownDirectionHeight p + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hhpos := heathBrownDirectionHeight_pos_of_mem hp
      have hNlt : N < (N / N0 + 1) * N0 :=
        (Nat.div_lt_iff_lt_mul hN0).mp (Nat.lt_succ_self (N / N0))
      have hN0lt : N0 < (N0 / heathBrownDirectionHeight p + 1) *
          heathBrownDirectionHeight p :=
        (Nat.div_lt_iff_lt_mul hhpos).mp
          (Nat.lt_succ_self (N0 / heathBrownDirectionHeight p))
      have hprod : N < ((N / N0 + 1) *
          (N0 / heathBrownDirectionHeight p + 1)) *
            heathBrownDirectionHeight p := by
        calc
          N < (N / N0 + 1) * N0 := hNlt
          _ ≤ (N / N0 + 1) *
              ((N0 / heathBrownDirectionHeight p + 1) *
                heathBrownDirectionHeight p) :=
            Nat.mul_le_mul_left _ hN0lt.le
          _ = ((N / N0 + 1) *
              (N0 / heathBrownDirectionHeight p + 1)) *
                heathBrownDirectionHeight p := by simp only [Nat.mul_assoc]
      have hlt := (Nat.div_lt_iff_lt_mul hhpos).mpr hprod
      omega
    _ = (N / N0 + 1) *
        (heathBrownPrimitiveLogRayMass N0 m1 m2 delta +
          (heathBrownPrimitiveLogWindow N0 m1 m2 delta).card) := by
      simp_rw [Nat.mul_add]
      rw [Finset.sum_add_distrib]
      simp [heathBrownPrimitiveLogRayMass, Finset.mul_sum, Nat.mul_comm]

/-- Every multiplicity layer injects into the primitive logarithmic window at its quotient scale. -/
theorem card_filter_mul_height_le_primitiveLogWindow_le
    {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    {m1 m2 delta : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm : m2 ≤ m1)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (((heathBrownPrimitiveLogWindow N m1 m2 delta).filter fun p =>
        k * heathBrownDirectionHeight p ≤ N).card : ℝ) ≤
      4 * delta * ((N / k : ℕ) : ℝ) ^ 2 + 1 := by
  have hsub : (heathBrownPrimitiveLogWindow N m1 m2 delta).filter
      (fun p => k * heathBrownDirectionHeight p ≤ N) ⊆
        heathBrownPrimitiveLogWindow (N / k) m1 m2 delta := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hp' := mem_heathBrownPrimitiveLogWindow_height.mp hp.1
    apply mem_heathBrownPrimitiveLogWindow_height.mpr
    exact ⟨hp'.1, hp'.2.1,
      (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hp.2),
        hp'.2.2.2.1, hp'.2.2.2.2⟩
  have hcardNat := Finset.card_le_card hsub
  have hcardReal :
      ((((heathBrownPrimitiveLogWindow N m1 m2 delta).filter fun p =>
          k * heathBrownDirectionHeight p ≤ N).card : ℕ) : ℝ) ≤
        ((heathBrownPrimitiveLogWindow (N / k) m1 m2 delta).card : ℝ) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans (card_heathBrownPrimitiveLogWindow_le
    ((Nat.le_div_iff_mul_le hk).mpr (by simpa using hkN))
      hm1 hm2 hm hdelta0 hdelta1)

/-- High primitive rays have only `N/N0` nonempty multiplicity layers.  Primitive-window packing
and the finite inverse-square bound control all those layers with explicit constant seven. -/
theorem cast_sum_high_primitiveLogWindow_natDiv_le
    {N N0 : ℕ} (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N)
    {m1 m2 delta : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm : m2 ≤ m1)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ((∑ p ∈ (heathBrownPrimitiveLogWindow N m1 m2 delta).filter
        (fun p => N0 < heathBrownDirectionHeight p),
        N / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
      7 * delta * (N : ℝ) ^ 2 + (N / N0 : ℕ) := by
  let S := (heathBrownPrimitiveLogWindow N m1 m2 delta).filter
    (fun p => N0 < heathBrownDirectionHeight p)
  let K := N / N0
  have hK : 1 ≤ K := by
    dsimp [K]
    exact (Nat.le_div_iff_mul_le hN0).mpr (by simpa using hN0N)
  have hquot : ∀ p ∈ S, N / heathBrownDirectionHeight p ≤ K := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.div_le_div_left hp'.2.le hN0
  have hlayer :
      ∑ p ∈ S, N / heathBrownDirectionHeight p =
        ∑ k ∈ Finset.Icc 1 K,
          #(S.filter fun p => k * heathBrownDirectionHeight p ≤ N) :=
    sum_natDiv_eq_sum_card_mul_le_bounded S heathBrownDirectionHeight
      (fun p hp => heathBrownDirectionHeight_pos_of_mem (Finset.mem_filter.mp hp).1)
      N K hquot
  rw [show (∑ p ∈ (heathBrownPrimitiveLogWindow N m1 m2 delta).filter
      (fun p => N0 < heathBrownDirectionHeight p),
      N / heathBrownDirectionHeight p) = ∑ p ∈ S,
      N / heathBrownDirectionHeight p by rfl]
  rw [hlayer]
  push_cast
  calc
    ∑ k ∈ Finset.Icc 1 K,
        ((S.filter fun p => k * heathBrownDirectionHeight p ≤ N).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K,
        (4 * delta * ((N / k : ℕ) : ℝ) ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have hKN : K ≤ N := by
        dsimp [K]
        exact Nat.div_le_self N N0
      have hsub : S.filter (fun p => k * heathBrownDirectionHeight p ≤ N) ⊆
          (heathBrownPrimitiveLogWindow N m1 m2 delta).filter
            (fun p => k * heathBrownDirectionHeight p ≤ N) := by
        intro p hp
        simp only [S, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1.1, hp.2⟩
      have hcardNat := Finset.card_le_card hsub
      have hcardReal :
          ((S.filter fun p => k * heathBrownDirectionHeight p ≤ N).card : ℝ) ≤
            (((heathBrownPrimitiveLogWindow N m1 m2 delta).filter fun p =>
              k * heathBrownDirectionHeight p ≤ N).card : ℝ) := by
        exact_mod_cast hcardNat
      exact hcardReal.trans
        (card_filter_mul_height_le_primitiveLogWindow_le hk'.1
          (hk'.2.trans hKN) hm1 hm2 hm hdelta0 hdelta1)
    _ ≤ ∑ k ∈ Finset.Icc 1 K,
        (4 * delta * ((N : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2)) + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      have hfloor := (cast_div_bounds (n := N) hkpos).1
      have hfloor0 : (0 : ℝ) ≤ ((N / k : ℕ) : ℝ) := by positivity
      have hdiv0 : (0 : ℝ) ≤ (N : ℝ) / (k : ℝ) := by positivity
      have hsq : ((N / k : ℕ) : ℝ) ^ 2 ≤
          ((N : ℝ) / (k : ℝ)) ^ 2 := by nlinarith
      calc
        4 * delta * ((N / k : ℕ) : ℝ) ^ 2 + 1 ≤
            4 * delta * ((N : ℝ) / (k : ℝ)) ^ 2 + 1 := by
          gcongr
        _ = 4 * delta * ((N : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2)) + 1 := by
          ring
    _ = 4 * delta * (N : ℝ) ^ 2 *
          (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) + (K : ℝ) := by
      have hweighted :
          ∑ k ∈ Finset.Icc 1 K,
              4 * delta * ((N : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2)) =
            4 * delta * (N : ℝ) ^ 2 *
              ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      have hones : ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) = (K : ℝ) := by
        norm_cast
        simp
      rw [Finset.sum_add_distrib]
      rw [hweighted, hones]
    _ ≤ 4 * delta * (N : ℝ) ^ 2 * (7 / 4) + (K : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_one_le hK)
          (show 0 ≤ 4 * delta * (N : ℝ) ^ 2 by positivity))
        (le_refl (K : ℝ))
    _ = 7 * delta * (N : ℝ) ^ 2 + (N / N0 : ℕ) := by
      dsimp [K]
      ring

/-- **Heath--Brown two-scale primitive-ray inequality.**  The complete collision-ray mass at scale
`N` is bounded by an absolute `delta N²` term, the source's `N/N0` endpoint loss, and the smaller
scale ray mass.  No exceptional-direction premise is retained. -/
theorem cast_heathBrownPrimitiveLogRayMass_le_twoScale
    {N N0 : ℕ} (hN0 : 1 ≤ N0) (hN0N : N0 ≤ N)
    {m1 m2 delta : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm : m2 ≤ m1)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (heathBrownPrimitiveLogRayMass N m1 m2 delta : ℝ) ≤
      15 * delta * (N : ℝ) ^ 2 +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) := by
  let D := heathBrownPrimitiveLogWindow N m1 m2 delta
  let low := D.filter (fun p => heathBrownDirectionHeight p ≤ N0)
  let high := D.filter (fun p => N0 < heathBrownDirectionHeight p)
  let K := N / N0
  have hsplit :
      heathBrownPrimitiveLogRayMass N m1 m2 delta =
        (∑ p ∈ low, N / heathBrownDirectionHeight p) +
          ∑ p ∈ high, N / heathBrownDirectionHeight p := by
    have hrev :
        (∑ p ∈ low, N / heathBrownDirectionHeight p) +
            ∑ p ∈ high, N / heathBrownDirectionHeight p =
          heathBrownPrimitiveLogRayMass N m1 m2 delta := by
      dsimp [low, high, D, heathBrownPrimitiveLogRayMass]
      rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hle : heathBrownDirectionHeight p ≤ N0
      · have hnlt : ¬N0 < heathBrownDirectionHeight p := by omega
        simp [hle, hnlt]
      · have hlt : N0 < heathBrownDirectionHeight p := by omega
        simp [hle, hlt]
    exact hrev.symm
  have hlowNat := sum_low_primitiveLogWindow_natDiv_le hN0 hN0N m1 m2 delta
  have hlowCast :
      ((∑ p ∈ low, N / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
        ((K + 1 : ℕ) : ℝ) *
          ((heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
            ((heathBrownPrimitiveLogWindow N0 m1 m2 delta).card : ℝ)) := by
    dsimp [low, D, K]
    exact_mod_cast hlowNat
  have hcard := card_heathBrownPrimitiveLogWindow_le hN0
    hm1 hm2 hm hdelta0 hdelta1
  have hKN0 : (K + 1) * N0 ≤ 2 * N := by
    have hKmul : K * N0 ≤ N := by
      dsimp [K]
      exact Nat.div_mul_le_self N N0
    calc
      (K + 1) * N0 = K * N0 + N0 := by ring
      _ ≤ N + N := Nat.add_le_add hKmul hN0N
      _ = 2 * N := by ring
  have hscaleNat : (K + 1) * N0 ^ 2 ≤ 2 * N ^ 2 := by
    calc
      (K + 1) * N0 ^ 2 = ((K + 1) * N0) * N0 := by ring
      _ ≤ (2 * N) * N := Nat.mul_le_mul hKN0 hN0N
      _ = 2 * N ^ 2 := by ring
  have hscale : ((K + 1 : ℕ) : ℝ) * (N0 : ℝ) ^ 2 ≤
      2 * (N : ℝ) ^ 2 := by exact_mod_cast hscaleNat
  have hlow :
      ((∑ p ∈ low, N / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
        ((K + 1 : ℕ) : ℝ) *
            (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
          8 * delta * (N : ℝ) ^ 2 + ((K + 1 : ℕ) : ℝ) := by
    calc
      ((∑ p ∈ low, N / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
          ((K + 1 : ℕ) : ℝ) *
            ((heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
              ((heathBrownPrimitiveLogWindow N0 m1 m2 delta).card : ℝ)) := hlowCast
      _ ≤ ((K + 1 : ℕ) : ℝ) *
            ((heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
              (4 * delta * (N0 : ℝ) ^ 2 + 1)) := by
        gcongr
      _ = ((K + 1 : ℕ) : ℝ) *
            (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
          4 * delta * (((K + 1 : ℕ) : ℝ) * (N0 : ℝ) ^ 2) +
            ((K + 1 : ℕ) : ℝ) := by ring
      _ ≤ ((K + 1 : ℕ) : ℝ) *
            (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
          4 * delta * (2 * (N : ℝ) ^ 2) + ((K + 1 : ℕ) : ℝ) := by
        gcongr
      _ = ((K + 1 : ℕ) : ℝ) *
            (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
          8 * delta * (N : ℝ) ^ 2 + ((K + 1 : ℕ) : ℝ) := by ring
  have hhigh :
      ((∑ p ∈ high, N / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
        7 * delta * (N : ℝ) ^ 2 + (K : ℝ) := by
    dsimp [high, D, K]
    exact cast_sum_high_primitiveLogWindow_natDiv_le hN0 hN0N
      hm1 hm2 hm hdelta0 hdelta1
  rw [hsplit]
  rw [Nat.cast_add]
  calc
    ((∑ p ∈ low, N / heathBrownDirectionHeight p : ℕ) : ℝ) +
        ((∑ p ∈ high, N / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
      (((K + 1 : ℕ) : ℝ) *
          (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
        8 * delta * (N : ℝ) ^ 2 + ((K + 1 : ℕ) : ℝ)) +
        (7 * delta * (N : ℝ) ^ 2 + (K : ℝ)) := add_le_add hlow hhigh
    _ = 15 * delta * (N : ℝ) ^ 2 +
        ((N / N0 + 1 : ℕ) : ℝ) *
          (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
        ((2 * (N / N0) + 1 : ℕ) : ℝ) := by
      dsimp [K]
      push_cast
      ring

end

end RHTower.Sieve
