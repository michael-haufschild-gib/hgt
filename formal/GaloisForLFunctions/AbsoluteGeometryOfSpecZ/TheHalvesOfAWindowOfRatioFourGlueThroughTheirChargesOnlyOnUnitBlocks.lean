import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OnANarrowWindowThePotentialIsPositiveAndThereAreNoBoundStates

/-!
# The halves of a window of ratio four glue through their charges only on unit blocks

For primes and prime powers cut off at `Q ≥ 3`, the neutral window `(R, 4R]` splits into the two
dyadic halves `(R, 2R]` (size `R`) and `(2R, 4R]` (size `2R`) coupled by
`K_ij = blockWeight Q (R + i) (2R + j)`. Because `b < 4a` across the whole window `(R, 4R]`, all
contacts stabilize at `Q = 3` (`floorContact_eq_four_of_lt_four_mul`,
`neutralBlock_eq_four_of_lt_four_mul`).

* **Calibration on the raised model (`1 ≤ R`, `3 ≤ Q`).** Raising the potentials of `(R, 2R]` and
  `(2R, 4R]` by all cross-couplings (`u = v = 0` in `hermNegIndex_glued_le_neutralWindow_add`) makes
  every row sum of the left half strictly positive (`raised_left_mulVec_one_pos`), so the raised
  left half holds `0` bound states (`hermNegIndex_raised_left_ratio_four_eq_zero`), while the raised
  right half holds `1` bound state (`hermNegIndex_raised_right_ratio_four_eq_one`). Together they
  give `1` negative square in the raised zero-charge model (`hermNegIndex_glued_raised_zero_eq_one`).
* **Unit blocks (`R = 1`, `3 ≤ Q`).** On `(1, 2]` and `(2, 4]`, the zero-excess charges `u = (1)`
  and `v_j = blockWeight Q 1 (2 + j)` leave the lowered halves nonnegative on `ker u` and `ker v`
  with susceptibility product strictly above `8/5 > 1` (`exists_unit_blocks_gluing_ratio_four`),
  and achieve the global maximum of `(u · a)(v · b)` over all admissible charge pairs with
  nonnegative lowered kernels (`susceptibility_mul_le_unit_blocks_ratio_four`).
* **Universal rank-one obstruction (`2 ≤ R`, `3 ≤ Q`).** For every block size `R ≥ 2` (even or odd)
  and every admissible pair `u_i v_j ≤ K_ij`, the lowered glued form has at least two negative
  squares (`two_le_hermNegIndex_glued_lowered_ratio_four_of_two_le`), so no admissible charge pair
  with nonnegative lowered kernels achieves susceptibility product `≥ 1`
  (`not_exists_gluing_ratio_four_of_two_le`). Consequently, the two halves of `(R, 4R]` glue
  through rank-one charges if and only if `R = 1` (`halves_of_ratio_four_glue_iff_eq_one`).
* **Sub-unit admissibility and rank-two gluing at `R = 2` (`3 ≤ Q`).** On `(2, 4]` and `(4, 8]`,
  explicit rational charges still yield nonnegative lowered kernels and negative susceptibilities
  with `0 < (u · a)(v · b) < 1` (`exists_sub_unit_gluing_two_blocks_ratio_four`), while rank-two
  zero-excess charge matrices `U = 1` and `V_ji = K_ij` glue the two halves with exact negative
  index `1` (`hermNegIndex_gluedMatrix_two_blocks_ratio_four_eq_one`).
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Lower bounds on `γ` and `log π`, cutoff stabilization, and coarse refinement -/

theorem euler_mascheroni_gt : (0.577212 : ℝ) < Real.eulerMascheroniConstant := by
  have h := (RHTower.harmonic_mascheroni_geometric_bounds (n := 10) (by norm_num)).2
  have hh : ((harmonic 10 : ℚ) : ℝ) = 7381 / 2520 := by norm_num [harmonic]
  have h1011 : ((10 : ℝ) + 1) = 11 := by norm_num
  rw [hh, Nat.cast_ofNat, log_ten, h1011] at h
  linarith [Real.log_two_lt_d9, log_five_mem.2, log_eleven_mem.2]

theorem log_pi_gt : (1.144729 : ℝ) < Real.log Real.pi := by
  have h1 : Real.log 3.141592 < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) Real.pi_gt_d6
  have h2 : Real.log (3.141592 : ℝ) = Real.log 3 + Real.log (3141592 / 3000000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h3 := two_terms_le_log_div (y := 70796 / 3070796) (by norm_num) (by norm_num)
  rw [show ((1 : ℝ) + 70796 / 3070796) / (1 - 70796 / 3070796) = 3141592 / 3000000 by norm_num] at h3
  have h3' : (0.0461173 : ℝ) ≤ Real.log (3141592 / 3000000) := le_trans (by norm_num) h3
  linarith [log_three_mem.1]

private theorem neutralBlock_diag {a : ℕ} (ha : 1 ≤ a) (Q : ℕ) :
    neutralBlock Q a a = blockDensity a - blockJet a a := by
  rw [neutralBlock, blockMatrix_self ha]
  ring

/-- Evaluates concrete entries of `neutralBlock 4` and `blockWeight 4` on blocks up to `8` from
both above and below. -/
local macro "neutral_entry" : tactic =>
  `(tactic|
    (simp only [blockWeight, blockDegree, blockDensity, blockJet, xLogXDiff, xLogX]
     norm_num [log_two_pi, log_four, log_six, log_eight, log_nine, log_ten, log_twelve,
       log_fourteen, log_fifteen, log_sixteen]
     linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log_three_mem.1, log_three_mem.2,
       log_five_mem.1, log_five_mem.2, log_seven_mem.1, log_seven_mem.2, log_eleven_mem.1,
       log_eleven_mem.2, log_thirteen_mem.1, log_thirteen_mem.2, log_pi_lt, log_pi_gt,
       euler_mascheroni_gt,
       RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion]))

/-- On blocks with `b < 4a`, no floor map with `k ≥ 4` hits `a`, so `floorContact Q a b` stabilizes
at `Q = 3` (and agrees with `floorContact 4 a b`). -/
theorem floorContact_eq_four_of_lt_four_mul {Q a b : ℕ} (hQ : 3 ≤ Q) (_ha : 1 ≤ a)
    (hb : b < 4 * a) : floorContact Q a b = floorContact 4 a b := by
  have hsubQ : ({2, 3} : Finset ℕ) ⊆ Icc 2 Q := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsub4 : ({2, 3} : Finset ℕ) ⊆ Icc 2 4 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hzero : ∀ {M : ℕ}, ∀ k ∈ Icc 2 M, k ∉ ({2, 3} : Finset ℕ) →
      (if b / k = a then (Λ k : ℝ) / k else 0) = 0 := by
    intro M k hk hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    have hk4 : 4 ≤ k := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    have hdiv : b / k < a :=
      lt_of_le_of_lt (Nat.div_le_div_left hk4 (by norm_num)) (Nat.div_lt_of_lt_mul (by omega))
    exact if_neg (by omega)
  rw [floorContact, floorContact, ← Finset.sum_subset hsubQ fun k hk hn => hzero k hk hn,
    ← Finset.sum_subset hsub4 fun k hk hn => hzero k hk hn]

theorem neutralBlock_eq_four_of_lt_four_mul {Q a b : ℕ} (hQ : 3 ≤ Q) (ha : 1 ≤ a) (hb0 : 1 ≤ b)
    (hab4 : b < 4 * a) (hba4 : a < 4 * b) :
    neutralBlock Q a b = neutralBlock 4 a b := by
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · rw [neutralBlock_of_lt hlt, neutralBlock_of_lt hlt,
      floorContact_eq_four_of_lt_four_mul hQ ha hab4]
  · rw [neutralBlock, neutralBlock, blockMatrix_self ha, blockMatrix_self ha]
  · rw [neutralBlock_comm Q a b, neutralBlock_comm 4 a b, neutralBlock_of_lt hgt,
      neutralBlock_of_lt hgt, floorContact_eq_four_of_lt_four_mul hQ hb0 hba4]

theorem blockWeight_eq_four_of_lt_four_mul {Q a b : ℕ} (hQ : 3 ≤ Q) (ha : 1 ≤ a)
    (hab : a < b) (hb : b < 4 * a) : blockWeight Q a b = blockWeight 4 a b := by
  rw [blockWeight, blockWeight, neutralBlock_eq_four_of_lt_four_mul hQ ha (by omega) hb (by omega)]

/-- Enclosures of the six coarse entries `neutralBlock 4 a b` on `1 ≤ a ≤ b ≤ 3`. -/
theorem neutralBlock_four_coarse_bounds :
    (-1.1988 < neutralBlock 4 1 1 ∧ neutralBlock 4 1 1 < -1.1986) ∧
    (-1.1661 < neutralBlock 4 1 2 ∧ neutralBlock 4 1 2 < -1.1660) ∧
    (-1.0751 < neutralBlock 4 1 3 ∧ neutralBlock 4 1 3 < -1.0750) ∧
    (-0.6063 < neutralBlock 4 2 2 ∧ neutralBlock 4 2 2 < -0.6062) ∧
    (-0.7769 < neutralBlock 4 2 3 ∧ neutralBlock 4 2 3 < -0.7768) ∧
    (-0.2375 < neutralBlock 4 3 3 ∧ neutralBlock 4 3 3 < -0.2374) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [neutralBlock_diag (by norm_num)]
    constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]
    constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]
    constructor <;> neutral_entry
  · rw [neutralBlock_diag (by norm_num)]
    constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]
    constructor <;> neutral_entry
  · rw [neutralBlock_diag (by norm_num)]
    constructor <;> neutral_entry

/-- A vector constant on each of the three dyadic/coarse thirds `[R, 2R)`, `[2R, 3R)`, `[3R, 4R)`
evaluates `neutralBlock Q` to `R` times the `3 × 3` coarse form at `R = 1`. -/
theorem sum_neutralBlock_three_steps (Q : ℕ) {R : ℕ} (hR : 1 ≤ R) (s t₁ t₂ : ℝ) :
    ∑ p ∈ range (3 * R), ∑ q ∈ range (3 * R),
        (if p < R then s else if p < 2 * R then t₁ else t₂) *
          (if q < R then s else if q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + p) (R + q) =
      (R : ℝ) * (s ^ 2 * neutralBlock Q 1 1 + t₁ ^ 2 * neutralBlock Q 2 2 +
        t₂ ^ 2 * neutralBlock Q 3 3 + 2 * s * t₁ * neutralBlock Q 1 2 +
        2 * s * t₂ * neutralBlock Q 1 3 + 2 * t₁ * t₂ * neutralBlock Q 2 3) := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hs0 : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR').ne'
  have hsq : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR'.le
  let σ : ℕ → ℝ := fun j => if j = 0 then s else if j = 1 then t₁ else t₂
  have href := sum_neutralBlock_refine (R := 1) le_rfl hR Q 3 σ
  have hstep : ∀ p ∈ range (R * 3), refineStep R σ p =
      (if p < R then s else if p < 2 * R then t₁ else t₂) / Real.sqrt R := by
    intro p hp
    have hp3 : p < R * 3 := Finset.mem_range.mp hp
    obtain ⟨j, i, hi, rfl⟩ : ∃ j i, i < R ∧ p = R * j + i :=
      ⟨p / R, p % R, Nat.mod_lt _ hR, (Nat.div_add_mod p R).symm⟩
    have hj3 : j < 3 := by
      by_contra h
      have : R * 3 ≤ R * j := Nat.mul_le_mul_left R (by omega)
      omega
    rw [refineStep_mul_add hR σ j hi]
    interval_cases j
    · simp only [σ, ↓reduceIte, Nat.mul_zero, zero_add, if_pos hi]
    · have h1 : ¬R * 1 + i < R := by omega
      have h2 : R * 1 + i < 2 * R := by omega
      simp only [σ, one_ne_zero, ↓reduceIte, if_neg h1, if_pos h2]
    · have h1 : ¬R * 2 + i < R := by omega
      have h2 : ¬R * 2 + i < 2 * R := by omega
      simp only [σ, OfNat.ofNat_ne_zero, (by decide : (2 : ℕ) ≠ 1), ↓reduceIte, if_neg h1,
        if_neg h2]
  have hLHS : ∑ p ∈ range (R * 3), ∑ q ∈ range (R * 3),
      refineStep R σ p * refineStep R σ q * neutralBlock Q (R * 1 + p) (R * 1 + q) =
      (∑ p ∈ range (3 * R), ∑ q ∈ range (3 * R),
        (if p < R then s else if p < 2 * R then t₁ else t₂) *
          (if q < R then s else if q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + p) (R + q)) / R := by
    rw [show R * 3 = 3 * R by ring, Nat.mul_one, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hp' : p ∈ range (R * 3) := by rwa [show R * 3 = 3 * R by ring]
    have hq' : q ∈ range (R * 3) := by rwa [show R * 3 = 3 * R by ring]
    rw [hstep p hp', hstep q hq']
    have hdiv : ∀ a b : ℝ, a / Real.sqrt R * (b / Real.sqrt R) = a * b / R := fun a b => by
      rw [div_mul_div_comm, hsq]
    rw [hdiv]
    ring
  have hRHS : ∑ j ∈ range 3, ∑ l ∈ range 3, σ j * σ l * neutralBlock Q (1 + j) (1 + l) =
      s ^ 2 * neutralBlock Q 1 1 + t₁ ^ 2 * neutralBlock Q 2 2 + t₂ ^ 2 * neutralBlock Q 3 3 +
        2 * s * t₁ * neutralBlock Q 1 2 + 2 * s * t₂ * neutralBlock Q 1 3 +
        2 * t₁ * t₂ * neutralBlock Q 2 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, σ]
    norm_num
    rw [neutralBlock_comm Q 2 1, neutralBlock_comm Q 3 1, neutralBlock_comm Q 3 2]
    ring
  rw [hLHS, hRHS, div_eq_iff hR'.ne'] at href
  linarith

/-- Coarse cross-sums of `blockWeight` between `[R, 2R)` and `[2R, 3R)`, `[3R, 4R)`. -/
theorem sum_blockWeight_coarse_halves (Q : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    (∑ i ∈ range R, ∑ j ∈ range R, blockWeight Q (R + i) (2 * R + j) =
        (R : ℝ) * blockWeight Q 1 2) ∧
      (∑ i ∈ range R, ∑ j ∈ range R, blockWeight Q (R + i) (3 * R + j) =
        (R : ℝ) * blockWeight Q 1 3) := by
  have h100 := sum_neutralBlock_three_steps Q hR 1 0 0
  have h010 := sum_neutralBlock_three_steps Q hR 0 1 0
  have h001 := sum_neutralBlock_three_steps Q hR 0 0 1
  have h110 := sum_neutralBlock_three_steps Q hR 1 1 0
  have h101 := sum_neutralBlock_three_steps Q hR 1 0 1
  -- split `range (3 * R)` into three blocks of size `R`
  have hsplit : ∀ f : ℕ → ℝ, ∑ p ∈ range (3 * R), f p =
      (∑ i ∈ range R, f i) + (∑ i ∈ range R, f (R + i)) + ∑ i ∈ range R, f (2 * R + i) := by
    intro f
    rw [show 3 * R = R + R + R by ring, Finset.sum_range_add, Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [two_mul]
  have heval : ∀ s t₁ t₂ : ℝ,
      ∑ p ∈ range (3 * R), ∑ q ∈ range (3 * R),
        (if p < R then s else if p < 2 * R then t₁ else t₂) *
          (if q < R then s else if q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + p) (R + q) =
      s ^ 2 * (∑ i ∈ range R, ∑ l ∈ range R, neutralBlock Q (R + i) (R + l)) +
      t₁ ^ 2 * (∑ i ∈ range R, ∑ l ∈ range R, neutralBlock Q (2 * R + i) (2 * R + l)) +
      t₂ ^ 2 * (∑ i ∈ range R, ∑ l ∈ range R, neutralBlock Q (3 * R + i) (3 * R + l)) +
      2 * s * t₁ * (∑ i ∈ range R, ∑ j ∈ range R, neutralBlock Q (R + i) (2 * R + j)) +
      2 * s * t₂ * (∑ i ∈ range R, ∑ j ∈ range R, neutralBlock Q (R + i) (3 * R + j)) +
      2 * t₁ * t₂ * (∑ i ∈ range R, ∑ j ∈ range R, neutralBlock Q (2 * R + i) (3 * R + j)) := by
    intro s t₁ t₂
    rw [hsplit]
    simp only [hsplit]
    have c0 : ∀ i ∈ range R, (if i < R then s else if i < 2 * R then t₁ else t₂) = s :=
      fun i hi => if_pos (Finset.mem_range.mp hi)
    have c1 : ∀ i ∈ range R, (if R + i < R then s else if R + i < 2 * R then t₁ else t₂) = t₁ :=
      fun i hi => by
        have hi' := Finset.mem_range.mp hi
        rw [if_neg (by omega), if_pos (by omega)]
    have c2 : ∀ i ∈ range R,
        (if 2 * R + i < R then s else if 2 * R + i < 2 * R then t₁ else t₂) = t₂ :=
      fun i _ => by rw [if_neg (by omega), if_neg (by omega)]
    have addr : ∀ a b : ℕ, R + (a + b) = R + a + b := fun _ _ => by omega
    have add2r : ∀ i : ℕ, R + (2 * R + i) = 3 * R + i := fun _ => by omega
    have addr1 : ∀ i : ℕ, R + (R + i) = 2 * R + i := fun _ => by omega
    -- rewrite each of the 9 double sums cleanly
    have b00 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if i < R then s else if i < 2 * R then t₁ else t₂) *
          (if q < R then s else if q < 2 * R then t₁ else t₂) * neutralBlock Q (R + i) (R + q) =
        s ^ 2 * ∑ i ∈ range R, ∑ q ∈ range R, neutralBlock Q (R + i) (R + q) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => by rw [c0 i hi, c0 q hq]; ring
    have b01 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if i < R then s else if i < 2 * R then t₁ else t₂) *
          (if R + q < R then s else if R + q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + i) (R + (R + q)) =
        s * t₁ * ∑ i ∈ range R, ∑ q ∈ range R, neutralBlock Q (R + i) (2 * R + q) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => by rw [c0 i hi, c1 q hq, addr1]
    have b02 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if i < R then s else if i < 2 * R then t₁ else t₂) *
          (if 2 * R + q < R then s else if 2 * R + q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + i) (R + (2 * R + q)) =
        s * t₂ * ∑ i ∈ range R, ∑ q ∈ range R, neutralBlock Q (R + i) (3 * R + q) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => by rw [c0 i hi, c2 q hq, add2r]
    have b10 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if R + i < R then s else if R + i < 2 * R then t₁ else t₂) *
          (if q < R then s else if q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + (R + i)) (R + q) =
        s * t₁ * ∑ q ∈ range R, ∑ i ∈ range R, neutralBlock Q (R + q) (2 * R + i) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q hq => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => by
          rw [c1 i hi, c0 q hq, addr1, neutralBlock_comm Q (2 * R + i) (R + q)]
          ring
    have b11 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if R + i < R then s else if R + i < 2 * R then t₁ else t₂) *
          (if R + q < R then s else if R + q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + (R + i)) (R + (R + q)) =
        t₁ ^ 2 * ∑ i ∈ range R, ∑ q ∈ range R, neutralBlock Q (2 * R + i) (2 * R + q) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => by rw [c1 i hi, c1 q hq, addr1, addr1]; ring
    have b12 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if R + i < R then s else if R + i < 2 * R then t₁ else t₂) *
          (if 2 * R + q < R then s else if 2 * R + q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + (R + i)) (R + (2 * R + q)) =
        t₁ * t₂ * ∑ i ∈ range R, ∑ q ∈ range R, neutralBlock Q (2 * R + i) (3 * R + q) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => by rw [c1 i hi, c2 q hq, addr1, add2r]
    have b20 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if 2 * R + i < R then s else if 2 * R + i < 2 * R then t₁ else t₂) *
          (if q < R then s else if q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + (2 * R + i)) (R + q) =
        s * t₂ * ∑ q ∈ range R, ∑ i ∈ range R, neutralBlock Q (R + q) (3 * R + i) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q hq => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => by
          rw [c2 i hi, c0 q hq, add2r, neutralBlock_comm Q (3 * R + i) (R + q)]
          ring
    have b21 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if 2 * R + i < R then s else if 2 * R + i < 2 * R then t₁ else t₂) *
          (if R + q < R then s else if R + q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + (2 * R + i)) (R + (R + q)) =
        t₁ * t₂ * ∑ q ∈ range R, ∑ i ∈ range R, neutralBlock Q (2 * R + q) (3 * R + i) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q hq => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => by
          rw [c2 i hi, c1 q hq, add2r, addr1, neutralBlock_comm Q (3 * R + i) (2 * R + q)]
          ring
    have b22 : ∑ i ∈ range R, ∑ q ∈ range R,
        (if 2 * R + i < R then s else if 2 * R + i < 2 * R then t₁ else t₂) *
          (if 2 * R + q < R then s else if 2 * R + q < 2 * R then t₁ else t₂) *
          neutralBlock Q (R + (2 * R + i)) (R + (2 * R + q)) =
        t₂ ^ 2 * ∑ i ∈ range R, ∑ q ∈ range R, neutralBlock Q (3 * R + i) (3 * R + q) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i hi => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => by rw [c2 i hi, c2 q hq, add2r, add2r]; ring
    simp only [Finset.sum_add_distrib, b00, b01, b02, b10, b11, b12, b20, b21, b22]
    ring
  rw [heval] at h100 h010 h001 h110 h101
  have hn12 : ∑ i ∈ range R, ∑ j ∈ range R, neutralBlock Q (R + i) (2 * R + j) =
      (R : ℝ) * neutralBlock Q 1 2 := by linarith
  have hn13 : ∑ i ∈ range R, ∑ j ∈ range R, neutralBlock Q (R + i) (3 * R + j) =
      (R : ℝ) * neutralBlock Q 1 3 := by linarith
  have hw : ∀ B : ℕ, ∑ i ∈ range R, ∑ j ∈ range R, blockWeight Q (R + i) (B + j) =
      -∑ i ∈ range R, ∑ j ∈ range R, neutralBlock Q (R + i) (B + j) := by
    intro B
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => rfl
  rw [hw (2 * R), hw (3 * R), hn12, hn13, blockWeight, blockWeight]
  exact ⟨by ring, by ring⟩

/-! ### Calibration on the raised-potential model (`1 ≤ R`, `3 ≤ Q`) -/

private theorem log_poly_ratio_four_gt {u_t v_t : ℝ} (hu_t : 0 < u_t) (hv_t : 0 < v_t) :
    (3 * Real.log 3 + Real.log 5) + 2 * Real.log (4 * u_t + 3 * v_t) +
        Real.log u_t + 2 * Real.log v_t <
      2 * Real.log 2 + 2 * Real.log (2 * u_t + v_t) + Real.log (3 * u_t + 2 * v_t) +
        Real.log (6 * u_t + 5 * v_t) + Real.log (2 * u_t + 3 * v_t) := by
  have hpoly : 135 * ((4 * u_t + 3 * v_t) ^ 2 * u_t * v_t ^ 2) <
      4 * (2 * u_t + v_t) ^ 2 * (3 * u_t + 2 * v_t) * (6 * u_t + 5 * v_t) *
        (2 * u_t + 3 * v_t) := by
    have hid : 4 * (2 * u_t + v_t) ^ 2 * (3 * u_t + 2 * v_t) * (6 * u_t + 5 * v_t) *
        (2 * u_t + 3 * v_t) - 135 * ((4 * u_t + 3 * v_t) ^ 2 * u_t * v_t ^ 2) =
        (3 * u_t - v_t) ^ 2 *
          (64 * u_t ^ 3 + 298 * u_t ^ 2 * v_t + 339 * u_t * v_t ^ 2 + 113 * v_t ^ 3) +
          (6 * u_t ^ 4 * v_t + u_t ^ 3 * v_t ^ 2 + 7 * u_t ^ 2 * v_t ^ 3 +
            8 * u_t * v_t ^ 4 + 7 * v_t ^ 5) := by ring
    have hsq0 : 0 ≤ (3 * u_t - v_t) ^ 2 *
        (64 * u_t ^ 3 + 298 * u_t ^ 2 * v_t + 339 * u_t * v_t ^ 2 + 113 * v_t ^ 3) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    have hpos_rem : 0 < 6 * u_t ^ 4 * v_t + u_t ^ 3 * v_t ^ 2 + 7 * u_t ^ 2 * v_t ^ 3 +
        8 * u_t * v_t ^ 4 + 7 * v_t ^ 5 := by positivity
    linarith only [hid, hsq0, hpos_rem]
  have hlog_poly := Real.log_lt_log (by positivity) hpoly
  have h135 : Real.log (135 : ℝ) = 3 * Real.log 3 + Real.log 5 := by
    rw [show (135 : ℝ) = 3 ^ 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have hlog_lhs : Real.log (135 * ((4 * u_t + 3 * v_t) ^ 2 * u_t * v_t ^ 2)) =
      (3 * Real.log 3 + Real.log 5) + 2 * Real.log (4 * u_t + 3 * v_t) +
        Real.log u_t + 2 * Real.log v_t := by
    rw [Real.log_mul (by norm_num) (by positivity), h135,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hu_t.ne', Real.log_pow, Real.log_pow]
    push_cast; ring
  have hlog_rhs : Real.log (4 * (2 * u_t + v_t) ^ 2 * (3 * u_t + 2 * v_t) *
      (6 * u_t + 5 * v_t) * (2 * u_t + 3 * v_t)) =
      2 * Real.log 2 + 2 * Real.log (2 * u_t + v_t) + Real.log (3 * u_t + 2 * v_t) +
        Real.log (6 * u_t + 5 * v_t) + Real.log (2 * u_t + 3 * v_t) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), log_four, Real.log_pow]
    push_cast; ring
  rwa [hlog_lhs, hlog_rhs] at hlog_poly

/-- Every row sum of the left dyadic half `(R, 2R]` raised by its couplings to `(2R, 4R]` is
strictly positive. -/
theorem raised_left_mulVec_one_pos {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R) (i : Fin R) :
    0 < ((neutralWindow Q R R +
      diagonal fun i : Fin R => ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j)) *ᵥ
        fun _ => (1 : ℝ)) i := by
  have hrow : ((neutralWindow Q R R +
      diagonal fun i : Fin R => ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j)) *ᵥ
        fun _ => (1 : ℝ)) i =
      blockPotential Q R R i + ∑ j ∈ range (2 * R), blockWeight 4 (R + i) (2 * R + j) := by
    have h1 : ((neutralWindow Q R R +
        diagonal fun i : Fin R => ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j)) *ᵥ
          fun _ => (1 : ℝ)) i =
        (neutralWindow Q R R *ᵥ fun _ => (1 : ℝ)) i +
          ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j) := by
      simp only [mulVec, dotProduct, Matrix.add_apply, mul_one, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single i (fun l _ hli => Matrix.diagonal_apply_ne _ (Ne.symm hli))
        (fun h => absurd (Finset.mem_univ i) h), Matrix.diagonal_apply_eq]
    rw [h1, neutralWindow_mulVec_one,
      ← Fin.sum_univ_eq_sum_range (fun j => blockWeight 4 (R + i) (2 * R + j)) (2 * R)]
    congr 1
    exact Finset.sum_congr rfl fun j _ =>
      blockWeight_eq_four_of_lt_four_mul hQ (by omega) (by have := i.2; omega)
        (by have := j.2; omega)
  rw [hrow]
  by_cases hR1 : R = 1
  · subst hR1
    have hi0 : (i : ℕ) = 0 := by omega
    rw [blockPotential, hi0,
      show ∑ l ∈ range 1, neutralBlock Q (1 + 0) (1 + l) = neutralBlock Q 1 1 by simp,
      neutralBlock_eq_four_of_lt_four_mul hQ le_rfl le_rfl (by norm_num) (by norm_num)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have hbounds := neutralBlock_four_coarse_bounds
    simp only [blockWeight]
    linarith [hbounds.1.1, hbounds.2.1.2, hbounds.2.2.1.2]
  · have hR2 : 2 ≤ R := by omega
    have hiR : (i : ℕ) < R := i.2
    rw [blockPotential_eq_of_window le_rfl hiR,
      show R + (i : ℕ) + R + R = 3 * R + i by omega,
      show R + (i : ℕ) + R = 2 * R + i by omega]
    -- split `blockWeight 4` into `blockJet` and `floorContact 4`
    have hw_split : ∑ j ∈ range (2 * R), blockWeight 4 (R + i) (2 * R + j) =
        (∑ j ∈ range (2 * R), blockJet (R + i) (2 * R + j)) +
          ∑ j ∈ range (2 * R), floorContact 4 (R + i) (2 * R + j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      rw [blockWeight, neutralBlock_of_lt (by omega)]
      ring
    -- telescope `blockJet` across `[2R, 4R)`
    have hjet : ∑ j ∈ range (2 * R), blockJet (R + i) (2 * R + j) =
        (xLogXStep (5 * R + i) - xLogXStep (3 * R + i)) / 2 +
          (xLogXStep (3 * R - 1 - i) - xLogXStep (R - 1 - i)) / 2 := by
      have hterm : ∀ j ∈ range (2 * R), blockJet (R + i) (2 * R + j) =
          xLogXDiff (3 * R + i + j + 1) / 2 + xLogXDiff (R - 1 - i + j + 1) / 2 := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [blockJet, show R + (i : ℕ) + (2 * R + j) + 1 = 3 * R + i + j + 1 by omega,
          show 2 * R + j - (R + (i : ℕ)) = R - 1 - i + j + 1 by omega, add_div]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
        sum_range_xLogXDiff_add (3 * R + i) (2 * R),
        sum_range_xLogXDiff_add (R - 1 - i) (2 * R),
        show 3 * R + (i : ℕ) + 2 * R = 5 * R + i by omega,
        show R - 1 - (i : ℕ) + 2 * R = 3 * R - 1 - i by omega]
    -- keep the two `k = 2` floor contacts `j = 2i` and `j = 2i + 1`
    have hfc : Real.log 2 ≤ ∑ j ∈ range (2 * R), floorContact 4 (R + i) (2 * R + j) := by
      have hnonneg : ∀ j ∈ range (2 * R), 0 ≤ floorContact 4 (R + i) (2 * R + j) := by
        intro j _
        rw [floorContact_four]
        have h2 := Real.log_two_gt_d9
        have h3 := log_three_mem.1
        split_ifs <;> linarith
      have hsub : ({2 * (i : ℕ), 2 * (i : ℕ) + 1} : Finset ℕ) ⊆ range (2 * R) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
      have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hnonneg j hj
      rw [Finset.sum_pair (by omega)] at hle
      have hc0 : Real.log 2 / 2 ≤ floorContact 4 (R + i) (2 * R + 2 * (i : ℕ)) := by
        rw [floorContact_four, if_pos (by omega)]
        have h2 := Real.log_two_gt_d9
        have h3 := log_three_mem.1
        split_ifs <;> linarith
      have hc1 : Real.log 2 / 2 ≤ floorContact 4 (R + i) (2 * R + (2 * (i : ℕ) + 1)) := by
        rw [floorContact_four, if_pos (by omega)]
        have h2 := Real.log_two_gt_d9
        have h3 := log_three_mem.1
        split_ifs <;> linarith
      linarith
    rw [hw_split, hjet]
    have hρ : blockDensity (R + i) =
        xLogXStep (R + i) - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) := rfl
    rw [hρ]
    -- midpoint bounds on the seven `xLogXStep` evaluations
    have hb_Ri := log_add_half_sub_le_xLogXStep (n := R + i) (by omega)
    have hb_2Ri := log_add_half_sub_le_xLogXStep (n := 2 * R + i) (by omega)
    have hb_3Ri := xLogXStep_le_log_add_half (3 * R + i)
    have hb_5Ri := log_add_half_sub_le_xLogXStep (n := 5 * R + i) (by omega)
    have hb_i := xLogXStep_le_log_add_half i
    have hb_R1i := xLogXStep_le_log_add_half (R - 1 - i)
    have hb_3R1i := log_add_half_sub_le_xLogXStep (n := 3 * R - 1 - i) (by omega)
    -- homogeneous variables `u_t = i + 1/2 > 0` and `v_t = R - 1 - i + 1/2 > 0` (`u_t + v_t = R`)
    set u_t : ℝ := (i : ℝ) + 1 / 2
    set v_t : ℝ := ((R - 1 - (i : ℕ) : ℕ) : ℝ) + 1 / 2
    have hu_t : 0 < u_t := by positivity
    have hv_t : 0 < v_t := by positivity
    have huv_R : u_t + v_t = (R : ℝ) := by
      dsimp only [u_t, v_t]
      have hnat : (i : ℕ) + (R - 1 - (i : ℕ)) + 1 = R := by omega
      have hcast : (i : ℝ) + ((R - 1 - (i : ℕ) : ℕ) : ℝ) + 1 = (R : ℝ) := by exact_mod_cast hnat
      linarith
    have hm1 : ((R + (i : ℕ) : ℕ) : ℝ) + 1 / 2 = 2 * u_t + v_t := by
      push_cast; rw [← huv_R]; dsimp only [u_t]; ring
    have hm2 : ((2 * R + (i : ℕ) : ℕ) : ℝ) + 1 / 2 = 3 * u_t + 2 * v_t := by
      push_cast; rw [← huv_R]; dsimp only [u_t]; ring
    have hm3 : ((3 * R + (i : ℕ) : ℕ) : ℝ) + 1 / 2 = 4 * u_t + 3 * v_t := by
      push_cast; rw [← huv_R]; dsimp only [u_t]; ring
    have hm5 : ((5 * R + (i : ℕ) : ℕ) : ℝ) + 1 / 2 = 6 * u_t + 5 * v_t := by
      push_cast; rw [← huv_R]; dsimp only [u_t]; ring
    have hm31 : ((3 * R - 1 - (i : ℕ) : ℕ) : ℝ) + 1 / 2 = 2 * u_t + 3 * v_t := by
      have hnat : 3 * R - 1 - (i : ℕ) = 2 * R + (R - 1 - (i : ℕ)) := by omega
      rw [hnat]; push_cast; rw [← huv_R]; dsimp only [v_t]; ring
    have hlog_poly := log_poly_ratio_four_gt hu_t hv_t
    rw [hm1] at hb_Ri
    rw [hm2] at hb_2Ri
    rw [hm3] at hb_3Ri
    rw [hm5] at hb_5Ri
    rw [hm31] at hb_3R1i
    -- rational error bounds for `R ≥ 2`
    have he1 : 1 / ((4 * ((R + (i : ℕ) : ℕ) : ℝ) + 1) * (4 * ((R + (i : ℕ) : ℕ) : ℝ) + 3)) ≤
        1 / 99 := by
      have hge : (2 : ℝ) ≤ ((R + (i : ℕ) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ R + i by omega)
      exact one_div_le_one_div_of_le (by norm_num)
        (le_trans (by norm_num : (99 : ℝ) ≤ 9 * 11)
          (mul_le_mul (by linarith only [hge]) (by linarith only [hge]) (by norm_num) (by positivity)))
    have he2 : 1 / ((4 * ((2 * R + (i : ℕ) : ℕ) : ℝ) + 1) *
        (4 * ((2 * R + (i : ℕ) : ℕ) : ℝ) + 3)) ≤ 1 / 323 := by
      have hge : (4 : ℝ) ≤ ((2 * R + (i : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (show 4 ≤ 2 * R + i by omega)
      exact one_div_le_one_div_of_le (by norm_num)
        (le_trans (by norm_num : (323 : ℝ) ≤ 17 * 19)
          (mul_le_mul (by linarith only [hge]) (by linarith only [hge]) (by norm_num) (by positivity)))
    have he5 : 1 / ((4 * ((5 * R + (i : ℕ) : ℕ) : ℝ) + 1) *
        (4 * ((5 * R + (i : ℕ) : ℕ) : ℝ) + 3)) ≤ 1 / 1763 := by
      have hge : (10 : ℝ) ≤ ((5 * R + (i : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (show 10 ≤ 5 * R + i by omega)
      exact one_div_le_one_div_of_le (by norm_num)
        (le_trans (by norm_num : (1763 : ℝ) ≤ 41 * 43)
          (mul_le_mul (by linarith only [hge]) (by linarith only [hge]) (by norm_num) (by positivity)))
    have he31 : 1 / ((4 * ((3 * R - 1 - (i : ℕ) : ℕ) : ℝ) + 1) *
        (4 * ((3 * R - 1 - (i : ℕ) : ℕ) : ℝ) + 3)) ≤ 1 / 323 := by
      have hge : (4 : ℝ) ≤ ((3 * R - 1 - (i : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast (show 4 ≤ 3 * R - 1 - i by omega)
      exact one_div_le_one_div_of_le (by norm_num)
        (le_trans (by norm_num : (323 : ℝ) ≤ 17 * 19)
          (mul_le_mul (by linarith only [hge]) (by linarith only [hge]) (by norm_num) (by positivity)))
    have hγ := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
    have h2π : Real.log (2 * Real.pi) < Real.log 2 + 1.1447302 := by
      rw [log_two_pi]; linarith only [log_pi_lt]
    have hl2 := Real.log_two_lt_d9
    have hl3 := log_three_mem.1
    have hl5 := log_five_mem.1
    linarith only [hfc, hb_Ri, hb_2Ri, hb_3Ri, hb_5Ri, hb_i, hb_R1i, hb_3R1i, hlog_poly,
      he1, he2, he5, he31, hγ, h2π, hl2, hl3, hl5]

/-- **The left half `(R, 2R]` raised by all couplings to `(2R, 4R]` holds zero bound states.** -/
theorem hermNegIndex_raised_left_ratio_four_eq_zero {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R) :
    hermNegIndex ((neutralWindow Q R R +
      diagonal fun i : Fin R => ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j)).map (↑) :
        Matrix (Fin R) (Fin R) ℂ) = 0 := by
  set A_hi := neutralWindow Q R R +
    diagonal fun i : Fin R => ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j)
  have hsym : ∀ i l, A_hi i l = A_hi l i :=
    add_diagonal_symm (fun i l => neutralBlock_comm Q _ _) _
  have hoff : ∀ i l, i ≠ l → A_hi i l ≤ 0 := fun i l hil => by
    simp only [A_hi, Matrix.add_apply, Matrix.diagonal_apply_ne _ hil, add_zero]
    exact (neutralBlock_neg (fun heq => hil (Fin.ext (Nat.add_left_cancel heq))) Q).le
  have hnn : ∀ x : Fin R → ℝ, 0 ≤ bilin A_hi x x := fun x => by
    have h := sum_div_mul_mulVec_le A_hi hsym hoff (v := fun _ => (1 : ℝ)) (fun _ => one_pos) x
    refine le_trans (Finset.sum_nonneg fun i _ => ?_) h
    rw [div_one]
    exact mul_nonneg (sq_nonneg _) (raised_left_mulVec_one_pos hQ hR i).le
  refine ArithmeticCastelnuovoSeveri.negIndex_eq_zero_of_hermQuad_nonneg fun c => ?_
  rw [hermQuad_map_eq_bilin]
  exact add_nonneg (hnn _) (hnn _)

/-- **The right half `(2R, 4R]` raised by all couplings to `(R, 2R]` holds exactly one bound
state.** -/
theorem hermNegIndex_raised_right_ratio_four_eq_one {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R) :
    hermNegIndex ((neutralWindow Q (2 * R) (2 * R) +
      diagonal fun j : Fin (2 * R) => ∑ i : Fin R, blockWeight Q (R + i) (2 * R + j)).map (↑) :
        Matrix (Fin (2 * R)) (Fin (2 * R)) ℂ) = 1 := by
  set B_hi := neutralWindow Q (2 * R) (2 * R) +
    diagonal fun j : Fin (2 * R) => ∑ i : Fin R, blockWeight Q (R + i) (2 * R + j)
  -- upper bound `≤ 1` since `neutralWindow ≤ B_hi`
  have hle : hermNegIndex (B_hi.map (↑) : Matrix (Fin (2 * R)) (Fin (2 * R)) ℂ) ≤ 1 := by
    have hdom : hermNegIndex (B_hi.map (↑) : Matrix (Fin (2 * R)) (Fin (2 * R)) ℂ) ≤
        hermNegIndex ((neutralWindow Q (2 * R) (2 * R)).map (↑) :
          Matrix (Fin (2 * R)) (Fin (2 * R)) ℂ) :=
      HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun c => by
        rw [hermQuad_map_eq_bilin, hermQuad_map_eq_bilin]
        have hpt : ∀ y : Fin (2 * R) → ℝ, bilin (neutralWindow Q (2 * R) (2 * R)) y y ≤
            bilin B_hi y y := fun y => by
          rw [bilin_add_diagonal]
          have hd : 0 ≤ ∑ j : Fin (2 * R),
              (∑ i : Fin R, blockWeight Q (R + i) (2 * R + j)) * y j ^ 2 :=
            Finset.sum_nonneg fun j _ => mul_nonneg
              (Finset.sum_nonneg fun i _ => (blockWeight_pos (by have := i.2; omega) Q).le)
              (sq_nonneg _)
          linarith
        exact add_le_add (hpt _) (hpt _)
    rwa [hermNegIndex_neutralWindow_eq_one (by omega) le_rfl (by omega) (by omega)] at hdom
  -- lower bound `1 ≤` by evaluating `B_hi` on the constant vector `1`
  have hge : 1 ≤ hermNegIndex (B_hi.map (↑) : Matrix (Fin (2 * R)) (Fin (2 * R)) ℂ) := by
    by_contra hlt
    have h0 : hermNegIndex (B_hi.map (↑) : Matrix (Fin (2 * R)) (Fin (2 * R)) ℂ) = 0 := by omega
    have hnn := ArithmeticCastelnuovoSeveri.hermQuad_nonneg_of_negIndex_eq_zero h0
      (fun _ => ((1 : ℝ) : ℂ))
    rw [HeckeKreinToeplitz.hermQuad_map_ofReal_real, dotProduct_mulVec_eq_bilin,
      bilin_add_diagonal] at hnn
    have hB1 : bilin (neutralWindow Q (2 * R) (2 * R)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) =
        (2 * R : ℝ) * neutralBlock 4 1 1 := by
      have h1 : bilin (neutralWindow Q (2 * R) (2 * R)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) =
          ∑ j ∈ range (2 * R), ∑ l ∈ range (2 * R), neutralBlock Q (2 * R + j) (2 * R + l) := by
        simpa [bilin, neutralWindow] using
          sum_fin_windowMatrix_coe (neutralBlock Q) (2 * R) (2 * R) (fun _ => 1)
      rw [h1, sum_neutralBlock_dyadic Q (by omega),
        neutralBlock_eq_four_of_lt_four_mul hQ le_rfl le_rfl (by norm_num) (by norm_num)]
      push_cast; ring
    have hKsum : ∑ j : Fin (2 * R),
        (∑ i : Fin R, blockWeight Q (R + i) (2 * R + j)) * (1 : ℝ) ^ 2 =
        (R : ℝ) * (blockWeight 4 1 2 + blockWeight 4 1 3) := by
      simp only [one_pow, mul_one]
      rw [Finset.sum_comm]
      have hfin : ∑ i : Fin R, ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j) =
          ∑ i ∈ range R, ∑ j ∈ range (2 * R), blockWeight Q (R + i) (2 * R + j) := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun i => ∑ j ∈ range (2 * R), blockWeight Q (R + i) (2 * R + j)) R]
        exact Finset.sum_congr rfl fun i _ =>
          Fin.sum_univ_eq_sum_range (fun j => blockWeight Q (R + i) (2 * R + j)) (2 * R)
      rw [hfin]
      have hsplit : ∑ i ∈ range R, ∑ j ∈ range (2 * R), blockWeight Q (R + i) (2 * R + j) =
          (∑ i ∈ range R, ∑ j ∈ range R, blockWeight Q (R + i) (2 * R + j)) +
            ∑ i ∈ range R, ∑ j ∈ range R, blockWeight Q (R + i) (3 * R + j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [two_mul, Finset.sum_range_add]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by
          rw [show R + R + (R + j) = 3 * R + j by omega]
      rw [hsplit, (sum_blockWeight_coarse_halves Q hR).1, (sum_blockWeight_coarse_halves Q hR).2,
        blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num),
        blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num)]
      ring
    rw [hB1, hKsum] at hnn
    have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
    have hb := neutralBlock_four_coarse_bounds
    have hneg_coarse : 2 * neutralBlock 4 1 1 + blockWeight 4 1 2 + blockWeight 4 1 3 < 0 := by
      simp only [blockWeight]
      linarith [hb.1.2, hb.2.1.1, hb.2.2.1.1]
    have hprod_neg : (R : ℝ) * (2 * neutralBlock 4 1 1 + blockWeight 4 1 2 + blockWeight 4 1 3) <
        0 := mul_neg_of_pos_of_neg hRpos hneg_coarse
    linarith
  exact le_antisymm hle hge

/-- **Calibration theorem.** At zero charges `u = 0`, `v = 0`, the raised-potential glued model of
`(R, 2R]` and `(2R, 4R]` has negative index `1` for every `R ≥ 1` and `Q ≥ 3`. -/
theorem hermNegIndex_glued_raised_zero_eq_one {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R) :
    hermNegIndex ((glued
      (neutralWindow Q R R +
        diagonal (excessLeft
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j))
          (fun _ => 0) (fun _ => 0)))
      (neutralWindow Q (2 * R) (2 * R) +
        diagonal (excessRight
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j))
          (fun _ => 0) (fun _ => 0)))
      (fun _ => 0) (fun _ => 0)).map (↑) :
        Matrix (Fin R ⊕ Fin (2 * R)) (Fin R ⊕ Fin (2 * R)) ℂ) = 1 := by
  set K : Fin R → Fin (2 * R) → ℝ := fun i j => blockWeight Q (R + i) (2 * R + j)
  have eL : excessLeft K (fun _ => 0) (fun _ => 0) = fun i => ∑ j, K i j :=
    funext fun i => Finset.sum_congr rfl fun j _ => by rw [zero_mul, sub_zero]
  have eR : excessRight K (fun _ => 0) (fun _ => 0) = fun j => ∑ i, K i j :=
    funext fun j => Finset.sum_congr rfl fun i _ => by rw [zero_mul, sub_zero]
  rw [eL, eR]
  have hblocks : ((glued (neutralWindow Q R R + diagonal fun i => ∑ j, K i j)
      (neutralWindow Q (2 * R) (2 * R) + diagonal fun j => ∑ i, K i j)
      (fun _ => 0) (fun _ => 0)).map (↑) :
        Matrix (Fin R ⊕ Fin (2 * R)) (Fin R ⊕ Fin (2 * R)) ℂ) =
      fromBlocks ((neutralWindow Q R R + diagonal fun i => ∑ j, K i j).map (↑)) 0 0
        ((neutralWindow Q (2 * R) (2 * R) + diagonal fun j => ∑ i, K i j).map (↑)) := by
    ext (i | i) (j | j) <;> simp [glued]
  rw [hblocks, negIndex_fromBlocks_zero
    (isHermitian_map_ofReal (add_diagonal_symm (A := neutralWindow Q R R)
      (fun i l => neutralBlock_comm Q _ _) _))
    (isHermitian_map_ofReal (add_diagonal_symm (A := neutralWindow Q (2 * R) (2 * R))
      (fun j m => neutralBlock_comm Q _ _) _)),
    hermNegIndex_raised_left_ratio_four_eq_zero hQ hR,
    hermNegIndex_raised_right_ratio_four_eq_one hQ hR, zero_add]

/-! ### Unit blocks (`R = 1`, `3 ≤ Q`): existence and exact global maximum -/

private theorem unit_blocks_cramer_bounds
    {a00 b00 b01 b11 k00 k01 : ℝ}
    (hA00 : -1.1988 < a00 ∧ a00 < -1.1986)
    (hB00 : -0.6063 < b00 ∧ b00 < -0.6062)
    (hB01 : -0.7769 < b01 ∧ b01 < -0.7768)
    (hB11 : -0.2375 < b11 ∧ b11 < -0.2374)
    (hv0 : 1.1660 < k00 ∧ k00 < 1.1661)
    (hv1 : 1.0750 < k01 ∧ k01 < 1.0751) :
    ∃ x0 b0 b1 : ℝ,
      a00 * x0 = 1 ∧
      b00 * b0 + b01 * b1 = k00 ∧
      b01 * b0 + b11 * b1 = k01 ∧
      (b0 ≤ 0 ∧ b1 ≤ 0) ∧
      (∀ y0 y1 : ℝ, k00 * y0 + k01 * y1 = 0 → 0 ≤ b00 * y0 ^ 2 + 2 * b01 * y0 * y1 + b11 * y1 ^ 2) ∧
      x0 < 0 ∧ k00 * b0 + k01 * b1 < 0 ∧
      8 / 5 < x0 * (k00 * b0 + k01 * b1) ∧
      x0 = 1 / a00 := by
  have ha1 := hA00.1; have ha2 := hA00.2
  have hb01_1 := hB00.1; have hb01_2 := hB00.2
  have hbo1 := hB01.1; have hbo2 := hB01.2
  have hb11_1 := hB11.1; have hb11_2 := hB11.2
  have hk0_1 := hv0.1; have hk0_2 := hv0.2
  have hk1_1 := hv1.1; have hk1_2 := hv1.2
  have hdet_lo : -0.4601 < b00 * b11 - b01 ^ 2 := by
    have p2 : (-0.6062) * (-0.2374) < b00 * b11 := by nlinarith only [hb01_1, hb01_2, hb11_1, hb11_2]
    have p4 : b01 ^ 2 < (0.7769 : ℝ) ^ 2 := by nlinarith only [hbo1, hbo2]
    linarith only [p2, p4]
  have hdet_hi : b00 * b11 - b01 ^ 2 < -0.4590 := by
    have p1 : b00 * b11 < (-0.6063) * (-0.2375) := by nlinarith only [hb01_1, hb01_2, hb11_1, hb11_2]
    have p3 : (0.7768 : ℝ) ^ 2 < b01 ^ 2 := by nlinarith only [hbo1, hbo2]
    linarith only [p1, p3]
  have ha_ne : a00 ≠ 0 := by linarith only [ha2]
  have hdet_ne : b00 * b11 - b01 ^ 2 ≠ 0 := by linarith only [hdet_hi]
  have hqf_gt : (0.923 : ℝ) < b11 * k00 ^ 2 - 2 * b01 * k00 * k01 + b00 * k01 ^ 2 := by
    have q1 : (-0.6063) * (1.0751 : ℝ) ^ 2 < b00 * k01 ^ 2 := by
      nlinarith only [hb01_1, hk1_1, hk1_2]
    have q2 : 2 * 0.7768 * 1.1660 * 1.0750 < -2 * b01 * k00 * k01 := by
      have hk01_p : 1.1660 * 1.0750 < k00 * k01 := by nlinarith only [hk0_1, hk1_1]
      nlinarith only [hbo2, hk01_p]
    have q3 : (-0.2375) * (1.1661 : ℝ) ^ 2 < b11 * k00 ^ 2 := by
      nlinarith only [hb11_1, hk0_1, hk0_2]
    linarith only [q1, q2, q3]
  refine ⟨1 / a00,
    (b11 * k00 - b01 * k01) / (b00 * b11 - b01 ^ 2),
    (b00 * k01 - b01 * k00) / (b00 * b11 - b01 ^ 2),
    mul_one_div_cancel ha_ne, ?_, ?_, ⟨?_, ?_⟩, ?_,
    one_div_neg.mpr (by linarith only [ha2]), ?_, ?_, rfl⟩
  · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hdet_ne]; ring
  · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, div_eq_iff hdet_ne]; ring
  · have hnum : 0 < b11 * k00 - b01 * k01 := by
      have m1 : (-0.2375 : ℝ) * 1.1661 < b11 * k00 := by nlinarith only [hb11_1, hk0_1, hk0_2]
      have m2 : 0.7768 * 1.0750 < -b01 * k01 := by nlinarith only [hbo2, hk1_1]
      linarith only [m1, m2]
    exact (div_neg_of_pos_of_neg hnum (by linarith only [hdet_hi])).le
  · have hnum : 0 < b00 * k01 - b01 * k00 := by
      have m1 : (-0.6063 : ℝ) * 1.0751 < b00 * k01 := by nlinarith only [hb01_1, hk1_1, hk1_2]
      have m2 : 0.7768 * 1.1660 < -b01 * k00 := by nlinarith only [hbo2, hk0_1]
      linarith only [m1, m2]
    exact (div_neg_of_pos_of_neg hnum (by linarith only [hdet_hi])).le
  · intro y0 y1 hy
    have hy1 : k01 * y1 = -(k00 * y0) := by linarith only [hy]
    have h1 : k01 ^ 2 * (b00 * y0 ^ 2 + 2 * b01 * y0 * y1 + b11 * y1 ^ 2) =
        b00 * y0 ^ 2 * k01 ^ 2 + 2 * b01 * y0 * k01 * (k01 * y1) + b11 * (k01 * y1) ^ 2 := by ring
    have h2 : k01 ^ 2 * (b00 * y0 ^ 2 + 2 * b01 * y0 * y1 + b11 * y1 ^ 2) =
        y0 ^ 2 * (b11 * k00 ^ 2 - 2 * b01 * k00 * k01 + b00 * k01 ^ 2) := by
      rw [h1, hy1]; ring
    have hk1_pos : 0 < k01 ^ 2 := sq_pos_of_pos (by linarith only [hk1_1])
    have hrhs : 0 ≤ y0 ^ 2 * (b11 * k00 ^ 2 - 2 * b01 * k00 * k01 + b00 * k01 ^ 2) :=
      mul_nonneg (sq_nonneg _) (by linarith only [hqf_gt])
    rw [← h2] at hrhs
    exact nonneg_of_mul_nonneg_right hrhs hk1_pos
  · have hcb : k00 * ((b11 * k00 - b01 * k01) / (b00 * b11 - b01 ^ 2)) +
        k01 * ((b00 * k01 - b01 * k00) / (b00 * b11 - b01 ^ 2)) =
        (b11 * k00 ^ 2 - 2 * b01 * k00 * k01 + b00 * k01 ^ 2) / (b00 * b11 - b01 ^ 2) := by
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]; ring
    rw [hcb]
    exact div_neg_of_pos_of_neg (by linarith only [hqf_gt]) (by linarith only [hdet_hi])
  · have hcb : k00 * ((b11 * k00 - b01 * k01) / (b00 * b11 - b01 ^ 2)) +
        k01 * ((b00 * k01 - b01 * k00) / (b00 * b11 - b01 ^ 2)) =
        (b11 * k00 ^ 2 - 2 * b01 * k00 * k01 + b00 * k01 ^ 2) / (b00 * b11 - b01 ^ 2) := by
      rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]; ring
    rw [hcb, one_div_mul_eq_div, div_div, mul_comm (b00 * b11 - b01 ^ 2) a00,
      lt_div_iff₀ (mul_pos_of_neg_of_neg (by linarith only [ha2]) (by linarith only [hdet_hi]))]
    have hden_lt : a00 * (b00 * b11 - b01 ^ 2) < 1.1988 * 0.4601 := by
      nlinarith only [ha1, ha2, hdet_lo, hdet_hi]
    linarith only [hqf_gt, hden_lt]

private theorem exists_unit_blocks_gluing_aux
    (A : Matrix (Fin 1) (Fin 1) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) (K : Fin 1 → Fin 2 → ℝ)
    (hB10 : B 1 0 = B 0 1)
    (hA00 : -1.1988 < A 0 0 ∧ A 0 0 < -1.1986)
    (hB00 : -0.6063 < B 0 0 ∧ B 0 0 < -0.6062)
    (hB01 : -0.7769 < B 0 1 ∧ B 0 1 < -0.7768)
    (hB11 : -0.2375 < B 1 1 ∧ B 1 1 < -0.2374)
    (hv0 : 1.1660 < K 0 0 ∧ K 0 0 < 1.1661)
    (hv1 : 1.0750 < K 0 1 ∧ K 0 1 < 1.0751) :
    ∃ (u a : Fin 1 → ℝ) (v b : Fin 2 → ℝ),
      (∀ i j, u i * v j ≤ K i j) ∧
      (∀ i, ∑ l, (A - diagonal (excessLeft K u v)) i l * a l = u i) ∧
      (∀ j, ∑ m, (B - diagonal (excessRight K u v)) j m * b m = v j) ∧
      (∀ x, chargeOf u x = 0 → 0 ≤ bilin (A - diagonal (excessLeft K u v)) x x) ∧
      (∀ y, chargeOf v y = 0 → 0 ≤ bilin (B - diagonal (excessRight K u v)) y y) ∧
      chargeOf u a < 0 ∧ chargeOf v b < 0 ∧
      8 / 5 < chargeOf u a * chargeOf v b := by
  obtain ⟨x0, b0, b1, hx0, hb_row0, hb_row1, _, hkerB, hx0_neg, hvb_neg, hprod, _⟩ :=
    unit_blocks_cramer_bounds hA00 hB00 hB01 hB11 hv0 hv1
  refine ⟨fun _ => 1, fun _ => x0, fun j => K 0 j,
    fun j => if (j : ℕ) = 0 then b0 else b1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [Subsingleton.elim i 0, one_mul]
  · intro i
    rw [Subsingleton.elim i 0, Fin.sum_univ_one, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      excessLeft_fin_one_zero K, Pi.zero_apply, sub_zero]
    exact hx0
  · intro j
    rw [Fin.sum_univ_two, Matrix.sub_apply, Matrix.sub_apply, excessRight_fin_one_zero K]
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.diagonal_apply, Pi.zero_apply, ite_self, sub_zero,
        Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero]
      exact hb_row0
    · simp only [Fin.mk_one, Matrix.diagonal_apply, Pi.zero_apply, sub_zero,
        Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero, hB10]
      exact hb_row1
  · intro x hx
    rw [chargeOf, Fin.sum_univ_one, one_mul] at hx
    simp only [bilin, Fin.sum_univ_one, hx, zero_mul, le_rfl]
  · intro y hy
    rw [chargeOf, Fin.sum_univ_two] at hy
    rw [bilin_sub_diagonal, excessRight_fin_one_zero K]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, bilin, Fin.sum_univ_two,
      hB10]
    exact (hkerB (y 0) (y 1) hy).trans_eq (by ring)
  · rw [chargeOf, Fin.sum_univ_one, one_mul]; exact hx0_neg
  · rw [chargeOf, Fin.sum_univ_two]
    simpa only [Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero] using hvb_neg
  · rw [chargeOf, Fin.sum_univ_one, one_mul, chargeOf, Fin.sum_univ_two]
    simpa only [Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero] using hprod

/-- **On unit blocks (`R = 1`), the two halves `(1, 2]` and `(2, 4]` glue through their charges.**
Zero-excess charges `u = (1)` and `v_j = blockWeight Q 1 (2 + j)` give nonnegative lowered halves
on `ker u` and `ker v`, negative susceptibilities, and susceptibility product `> 8/5 > 1`. -/
theorem exists_unit_blocks_gluing_ratio_four {Q : ℕ} (hQ : 3 ≤ Q) :
    ∃ (u a : Fin 1 → ℝ) (v b : Fin 2 → ℝ),
      (∀ i j, u i * v j ≤ blockWeight Q (1 + i) (2 + j)) ∧
      (∀ i, ∑ l,
        (neutralWindow Q 1 1 -
          diagonal (excessLeft
            (fun (i : Fin 1) (j : Fin 2) => blockWeight Q (1 + i) (2 + j)) u v)) i l *
          a l = u i) ∧
      (∀ j, ∑ m,
        (neutralWindow Q 2 2 -
          diagonal (excessRight
            (fun (i : Fin 1) (j : Fin 2) => blockWeight Q (1 + i) (2 + j)) u v)) j m *
          b m = v j) ∧
      (∀ x, chargeOf u x = 0 →
        0 ≤ bilin (neutralWindow Q 1 1 -
          diagonal (excessLeft
            (fun (i : Fin 1) (j : Fin 2) => blockWeight Q (1 + i) (2 + j)) u v)) x x) ∧
      (∀ y, chargeOf v y = 0 →
        0 ≤ bilin (neutralWindow Q 2 2 -
          diagonal (excessRight
            (fun (i : Fin 1) (j : Fin 2) => blockWeight Q (1 + i) (2 + j)) u v)) y y) ∧
      chargeOf u a < 0 ∧ chargeOf v b < 0 ∧
      8 / 5 < chargeOf u a * chargeOf v b := by
  have hb := neutralBlock_four_coarse_bounds
  have hA00 : -1.1988 < neutralWindow Q 1 1 0 0 ∧ neutralWindow Q 1 1 0 0 < -1.1986 := by
    rw [show neutralWindow Q 1 1 0 0 = neutralBlock Q 1 1 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ le_rfl le_rfl (by norm_num) (by norm_num)]
    exact hb.1
  have hB00 : -0.6063 < neutralWindow Q 2 2 0 0 ∧ neutralWindow Q 2 2 0 0 < -0.6062 := by
    rw [show neutralWindow Q 2 2 0 0 = neutralBlock Q 2 2 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hb.2.2.2.1
  have hB01 : -0.7769 < neutralWindow Q 2 2 0 1 ∧ neutralWindow Q 2 2 0 1 < -0.7768 := by
    rw [show neutralWindow Q 2 2 0 1 = neutralBlock Q 2 3 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hb.2.2.2.2.1
  have hB11 : -0.2375 < neutralWindow Q 2 2 1 1 ∧ neutralWindow Q 2 2 1 1 < -0.2374 := by
    rw [show neutralWindow Q 2 2 1 1 = neutralBlock Q 3 3 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hb.2.2.2.2.2
  have hv0 : 1.1660 < blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((0 : Fin 2) : ℕ)) ∧
      blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((0 : Fin 2) : ℕ)) < 1.1661 := by
    simp only [Fin.val_zero, add_zero]
    rw [blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num), blockWeight]
    exact ⟨by linarith [hb.2.1.2], by linarith [hb.2.1.1]⟩
  have hv1 : 1.0750 < blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((1 : Fin 2) : ℕ)) ∧
      blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((1 : Fin 2) : ℕ)) < 1.0751 := by
    simp only [Fin.val_zero, Fin.val_one, add_zero]
    rw [blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num), blockWeight]
    exact ⟨by linarith [hb.2.2.1.2], by linarith [hb.2.2.1.1]⟩
  exact exists_unit_blocks_gluing_aux (neutralWindow Q 1 1) (neutralWindow Q 2 2)
    (fun i j => blockWeight Q (1 + i) (2 + j)) (neutralBlock_comm Q 3 2)
    hA00 hB00 hB01 hB11 hv0 hv1

private theorem susceptibility_mul_le_unit_blocks_aux
    (A : Matrix (Fin 1) (Fin 1) ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) (K : Fin 1 → Fin 2 → ℝ)
    (hB_symm : ∀ j m, B j m = B m j)
    (hA00 : -1.1988 < A 0 0 ∧ A 0 0 < -1.1986)
    (hB00 : -0.6063 < B 0 0 ∧ B 0 0 < -0.6062)
    (hB01 : -0.7769 < B 0 1 ∧ B 0 1 < -0.7768)
    (hB11 : -0.2375 < B 1 1 ∧ B 1 1 < -0.2374)
    (hv0 : 1.1660 < K 0 0 ∧ K 0 0 < 1.1661)
    (hv1 : 1.0750 < K 0 1 ∧ K 0 1 < 1.0751)
    {u a : Fin 1 → ℝ} {v b : Fin 2 → ℝ}
    (huv : ∀ i j, u i * v j ≤ K i j)
    (hAa : ∀ i, ∑ l, (A - diagonal (excessLeft K u v)) i l * a l = u i)
    (hBb : ∀ j, ∑ m, (B - diagonal (excessRight K u v)) j m * b m = v j)
    (hBpos : ∀ y, chargeOf v y = 0 → 0 ≤ bilin (B - diagonal (excessRight K u v)) y y) :
    ∃ b₀ : Fin 2 → ℝ,
      (∀ j, ∑ m, B j m * b₀ m = K 0 j) ∧
      chargeOf u a * chargeOf v b ≤ (1 / A 0 0) * chargeOf (K 0) b₀ := by
  obtain ⟨x0, b0, b1, _, hb_row0, hb_row1, hb_np, _, _, _, hprod, hx0_eq⟩ :=
    unit_blocks_cramer_bounds hA00 hB00 hB01 hB11 hv0 hv1
  have hBb₀ : ∀ j : Fin 2, ∑ m : Fin 2, B j m * (if (m : ℕ) = 0 then b0 else b1) = K 0 j := by
    intro j
    rw [Fin.sum_univ_two]
    fin_cases j
    · simpa only [Fin.zero_eta, Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero] using hb_row0
    · rw [Fin.mk_one, hB_symm 1 0]
      simpa only [Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero] using hb_row1
  have hb₀_nonpos : ∀ j : Fin 2, (if (j : ℕ) = 0 then b0 else b1) ≤ 0 := fun j => by
    fin_cases j
    · simpa only [Fin.zero_eta, Fin.val_zero, ↓reduceIte] using hb_np.1
    · simpa only [Fin.mk_one, Fin.val_one, one_ne_zero, ↓reduceIte] using hb_np.2
  have h1le : 1 ≤ (1 / A 0 0) * chargeOf (K 0) (fun j : Fin 2 => if (j : ℕ) = 0 then b0 else b1) := by
    rw [← hx0_eq, chargeOf, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, ↓reduceIte, one_ne_zero]
    linarith only [hprod]
  have ha00_neg : A 0 0 < 0 := lt_trans hA00.2 (by norm_num)
  exact ⟨fun j => if (j : ℕ) = 0 then b0 else b1, hBb₀,
    susceptibility_mul_le_of_fin_one ha00_neg hB_symm hBb₀ hb₀_nonpos h1le huv hBb hAa hBpos⟩

/-- **Exact global maximum of the susceptibility product on unit blocks (`R = 1`).** Every
admissible charge pair on `(1, 2]` and `(2, 4]` with nonnegative lowered kernels has susceptibility
product bounded above by the zero-excess value `(neutralBlock 4 1 1)⁻¹ (K₀ᵀ B⁻¹ K₀) ≈ 1.6777`. -/
theorem susceptibility_mul_le_unit_blocks_ratio_four {Q : ℕ} (hQ : 3 ≤ Q)
    {u a : Fin 1 → ℝ} {v b : Fin 2 → ℝ}
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (1 + i) (2 + j))
    (hAa : ∀ i, ∑ l,
      (neutralWindow Q 1 1 -
        diagonal (excessLeft
          (fun (i : Fin 1) (j : Fin 2) => blockWeight Q (1 + i) (2 + j)) u v)) i l * a l = u i)
    (hBb : ∀ j, ∑ m,
      (neutralWindow Q 2 2 -
        diagonal (excessRight
          (fun (i : Fin 1) (j : Fin 2) => blockWeight Q (1 + i) (2 + j)) u v)) j m * b m = v j)
    (hBpos : ∀ y, chargeOf v y = 0 →
      0 ≤ bilin (neutralWindow Q 2 2 -
        diagonal (excessRight
          (fun (i : Fin 1) (j : Fin 2) => blockWeight Q (1 + i) (2 + j)) u v)) y y) :
    ∃ b₀ : Fin 2 → ℝ,
      (∀ j, ∑ m, neutralWindow Q 2 2 j m * b₀ m = blockWeight Q 1 (2 + j)) ∧
      chargeOf u a * chargeOf v b ≤
        (1 / neutralWindow Q 1 1 0 0) *
          chargeOf (fun j : Fin 2 => blockWeight Q 1 (2 + j)) b₀ := by
  have hb := neutralBlock_four_coarse_bounds
  have hA00 : -1.1988 < neutralWindow Q 1 1 0 0 ∧ neutralWindow Q 1 1 0 0 < -1.1986 := by
    rw [show neutralWindow Q 1 1 0 0 = neutralBlock Q 1 1 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ le_rfl le_rfl (by norm_num) (by norm_num)]
    exact hb.1
  have hB00 : -0.6063 < neutralWindow Q 2 2 0 0 ∧ neutralWindow Q 2 2 0 0 < -0.6062 := by
    rw [show neutralWindow Q 2 2 0 0 = neutralBlock Q 2 2 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hb.2.2.2.1
  have hB01 : -0.7769 < neutralWindow Q 2 2 0 1 ∧ neutralWindow Q 2 2 0 1 < -0.7768 := by
    rw [show neutralWindow Q 2 2 0 1 = neutralBlock Q 2 3 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hb.2.2.2.2.1
  have hB11 : -0.2375 < neutralWindow Q 2 2 1 1 ∧ neutralWindow Q 2 2 1 1 < -0.2374 := by
    rw [show neutralWindow Q 2 2 1 1 = neutralBlock Q 3 3 from rfl,
      neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    exact hb.2.2.2.2.2
  have hv0 : 1.1660 < blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((0 : Fin 2) : ℕ)) ∧
      blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((0 : Fin 2) : ℕ)) < 1.1661 := by
    simp only [Fin.val_zero, add_zero]
    rw [blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num), blockWeight]
    exact ⟨by linarith [hb.2.1.2], by linarith [hb.2.1.1]⟩
  have hv1 : 1.0750 < blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((1 : Fin 2) : ℕ)) ∧
      blockWeight Q (1 + ((0 : Fin 1) : ℕ)) (2 + ((1 : Fin 2) : ℕ)) < 1.0751 := by
    simp only [Fin.val_zero, Fin.val_one, add_zero]
    rw [blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num), blockWeight]
    exact ⟨by linarith [hb.2.2.1.2], by linarith [hb.2.2.1.1]⟩
  obtain ⟨b₀, hBb₀, hle⟩ := susceptibility_mul_le_unit_blocks_aux
    (neutralWindow Q 1 1) (neutralWindow Q 2 2)
    (fun i j => blockWeight Q (1 + i) (2 + j)) (fun j m => neutralBlock_comm Q _ _)
    hA00 hB00 hB01 hB11 hv0 hv1 huv hAa hBb hBpos
  simp only [Fin.val_zero, add_zero] at hBb₀ hle
  exact ⟨b₀, hBb₀, hle⟩

/-! ### Universal rank-one obstruction (`2 ≤ R`, `3 ≤ Q`) -/

/-- Two vectors spanning a negative binary form certify `2 ≤ hermNegIndex`. -/
private theorem two_le_hermNegIndex_of_binary_plane {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ)
    (w₁ w₂ : ι → ℝ) {α γ c : ℝ}
    (h : ∀ s t : ℝ, bilin G (fun m => s * w₁ m + t * w₂ m) (fun m => s * w₁ m + t * w₂ m) ≤
      α * s ^ 2 + 2 * c * s * t + γ * t ^ 2)
    (hα : α < 0) (hdisc : c ^ 2 < α * γ) :
    2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) := by
  have hcard := card_le_hermNegIndex_of_real_neg (κ := Fin 2) G ![w₁, w₂] fun g hg => by
    have he : (fun m : ι => ∑ k : Fin 2, g k * (![w₁, w₂] : Fin 2 → ι → ℝ) k m) =
        fun m => g 0 * w₁ m + g 1 * w₂ m := by
      funext m; rw [Fin.sum_univ_two]; rfl
    rw [he]
    refine lt_of_le_of_lt (h (g 0) (g 1)) (quad_neg_of_disc hα (by linarith) ?_)
    by_contra hcon
    push Not at hcon
    exact hg (funext fun k => by fin_cases k; exact hcon.1; exact hcon.2)
  rwa [Fintype.card_fin] at hcard

/-- Exact difference between `coupled A B K` and `glued A_low B_low u v`. -/
theorem bilin_glued_lowered_eq_coupled_sub {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) (w : ι₁ ⊕ ι₂ → ℝ) :
    bilin (glued (A - diagonal (excessLeft K u v)) (B - diagonal (excessRight K u v)) u v) w w =
      bilin (coupled A B K) w w -
        ∑ i, ∑ j, (K i j - u i * v j) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 := by
  have hterm : ∀ i j, (K i j - u i * v j) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      (K i j - u i * v j) * w (Sum.inl i) ^ 2 + (K i j - u i * v j) * w (Sum.inr j) ^ 2 -
        2 * (w (Sum.inl i) * w (Sum.inr j) * K i j) +
          2 * (w (Sum.inl i) * w (Sum.inr j) * (u i * v j)) := fun _ _ => by ring
  have hexp : ∑ i, ∑ j, (K i j - u i * v j) * (w (Sum.inl i) - w (Sum.inr j)) ^ 2 =
      (∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inl i) ^ 2) +
        (∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inr j) ^ 2) -
        2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * K i j) +
          2 * (∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (u i * v j)) := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 : ∑ i, excessLeft K u v i * w (Sum.inl i) ^ 2 =
      ∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inl i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [excessLeft, Finset.sum_mul]
  have h2 : ∑ j, excessRight K u v j * w (Sum.inr j) ^ 2 =
      ∑ i, ∑ j, (K i j - u i * v j) * w (Sum.inr j) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [excessRight, Finset.sum_mul]
  have h3 : chargeOf u (fun i => w (Sum.inl i)) * chargeOf v (fun j => w (Sum.inr j)) =
      ∑ i, ∑ j, w (Sum.inl i) * w (Sum.inr j) * (u i * v j) := by
    rw [chargeOf, chargeOf, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [bilin_glued, bilin_coupled, bilin_sub_diagonal, bilin_sub_diagonal, h1, h2, h3]
  linarith

/-- For any admissible pair `u_i v_j ≤ K_ij` with `K ≥ 0` and any subset `S` of columns, there is
a pivot row `c` such that `(∑_i u_i)(∑_{j ∈ S} v_j) ≤ ∑_i ∑_{j ∈ S} min(K_cj, K_ij)`. -/
theorem exists_sum_mul_sum_le_sum_min {ι₁ ι₂ : Type*} [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂]
    {K : ι₁ → ι₂ → ℝ} (hK0 : ∀ i j, 0 ≤ K i j) {u : ι₁ → ℝ} {v : ι₂ → ℝ}
    (huv : ∀ i j, u i * v j ≤ K i j) (S : Finset ι₂) :
    ∃ c : ι₁, (∑ i, u i) * (∑ j ∈ S, v j) ≤ ∑ i, ∑ j ∈ S, min (K c j) (K i j) := by
  by_cases hpos : 0 < (∑ i, u i) * (∑ j ∈ S, v j)
  · set u₁ : ι₁ → ℝ := if 0 < ∑ i, u i then u else -u
    set v₁ : ι₂ → ℝ := if 0 < ∑ i, u i then v else -v
    have hprod_eq : (∑ i, u₁ i) * (∑ j ∈ S, v₁ j) = (∑ i, u i) * (∑ j ∈ S, v j) := by
      by_cases hu : 0 < ∑ i, u i
      · simp only [u₁, v₁, if_pos hu]
      · simp only [u₁, v₁, if_neg hu, Pi.neg_apply, Finset.sum_neg_distrib, neg_mul_neg]
    have hu₁_pos : 0 < ∑ i, u₁ i := by
      by_cases hu : 0 < ∑ i, u i
      · simpa [u₁, if_pos hu] using hu
      · simp only [u₁, if_neg hu, Pi.neg_apply, Finset.sum_neg_distrib]
        have hne : ∑ i, u i ≠ 0 := fun h0 => by rw [h0, zero_mul] at hpos; exact lt_irrefl 0 hpos
        linarith [lt_of_le_of_ne (not_lt.mp hu) hne]
    have hv₁_pos : 0 < ∑ j ∈ S, v₁ j := by
      rw [← hprod_eq] at hpos
      exact (mul_pos_iff_of_pos_left hu₁_pos).mp hpos
    have huv₁ : ∀ i j, u₁ i * v₁ j ≤ K i j := fun i j => by
      by_cases hu : 0 < ∑ i, u i
      · simpa [u₁, v₁, if_pos hu] using huv i j
      · simpa [u₁, v₁, if_neg hu] using huv i j
    set uₚ : ι₁ → ℝ := fun i => max (u₁ i) 0
    set vₚ : ι₂ → ℝ := fun j => max (v₁ j) 0
    have huvₚ : ∀ i j, uₚ i * vₚ j ≤ K i j := fun i j => by
      rcases le_total (u₁ i) 0 with hi | hi
      · rw [show uₚ i = 0 from max_eq_right hi, zero_mul]
        exact hK0 i j
      · rcases le_total (v₁ j) 0 with hj | hj
        · rw [show vₚ j = 0 from max_eq_right hj, mul_zero]
          exact hK0 i j
        · rw [show uₚ i = u₁ i from max_eq_left hi, show vₚ j = v₁ j from max_eq_left hj]
          exact huv₁ i j
    have hu_le : ∑ i, u₁ i ≤ ∑ i, uₚ i := Finset.sum_le_sum fun i _ => le_max_left _ _
    have hv_le : ∑ j ∈ S, v₁ j ≤ ∑ j ∈ S, vₚ j := Finset.sum_le_sum fun j _ => le_max_left _ _
    obtain ⟨c, _, hc_max⟩ := Finset.exists_max_image Finset.univ uₚ Finset.univ_nonempty
    have huc_pos : 0 < uₚ c := by
      by_contra hle
      have h0 : ∑ i, uₚ i ≤ 0 := Finset.sum_nonpos fun i hi =>
        (hc_max i hi).trans (not_lt.mp hle)
      linarith
    refine ⟨c, ?_⟩
    have hterm : ∀ i, ∀ j ∈ S, (uₚ i / uₚ c) * (uₚ c * vₚ j) ≤ min (K c j) (K i j) := by
      intro i j _
      have heq : (uₚ i / uₚ c) * (uₚ c * vₚ j) = uₚ i * vₚ j := by
        rw [div_mul_eq_mul_div, mul_left_comm, mul_div_cancel_left₀ _ huc_pos.ne']
      refine le_min ?_ (heq ▸ huvₚ i j)
      have hrat : uₚ i / uₚ c ≤ 1 := (div_le_one huc_pos).mpr (hc_max i (Finset.mem_univ i))
      calc (uₚ i / uₚ c) * (uₚ c * vₚ j)
          ≤ 1 * (uₚ c * vₚ j) :=
            mul_le_mul_of_nonneg_right hrat (mul_nonneg huc_pos.le (le_max_right _ _))
        _ = uₚ c * vₚ j := one_mul _
        _ ≤ K c j := huvₚ c j
    calc (∑ i, u i) * (∑ j ∈ S, v j)
        = (∑ i, u₁ i) * (∑ j ∈ S, v₁ j) := hprod_eq.symm
      _ ≤ (∑ i, uₚ i) * (∑ j ∈ S, vₚ j) :=
          mul_le_mul hu_le hv_le hv₁_pos.le (hu₁_pos.le.trans hu_le)
      _ = (∑ i, uₚ i / uₚ c) * (∑ j ∈ S, uₚ c * vₚ j) := by
          symm
          rw [← Finset.sum_div, ← Finset.mul_sum, div_mul_eq_mul_div, mul_left_comm,
            mul_div_cancel_left₀ _ huc_pos.ne']
      _ = ∑ i, ∑ j ∈ S, (uₚ i / uₚ c) * (uₚ c * vₚ j) := Finset.sum_mul_sum _ _ _ _
      _ ≤ ∑ i, ∑ j ∈ S, min (K c j) (K i j) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hterm i j hj
  · refine ⟨Classical.arbitrary ι₁, le_trans (not_lt.mp hpos) ?_⟩
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      le_min (hK0 _ j) (hK0 i j)

private theorem hasDerivAt_shift_mul_log_aux {u a : ℝ} (h : u + a ≠ 0) :
    HasDerivAt (fun x : ℝ => (x + a) * Real.log (x + a)) (Real.log (u + a) + 1) u := by
  have hb : HasDerivAt (fun x : ℝ => x + a) 1 u := (hasDerivAt_id u).add_const a
  have hl := (Real.hasDerivAt_log h).comp u hb
  have hfun : (Real.log ∘ fun x : ℝ => x + a) = fun x : ℝ => Real.log (x + a) := rfl
  rw [hfun] at hl
  exact (hb.mul hl).congr_deriv (by field_simp)

/-- Strict decrease of `xLogXDiff`: `xLogXDiff m < xLogXDiff n` whenever `1 ≤ n < m`. -/
theorem xLogXDiff_strictAnti {n m : ℕ} (hn : 1 ≤ n) (hnm : n < m) :
    xLogXDiff m < xLogXDiff n := by
  let f : ℝ → ℝ := fun u =>
    (u + 1) * Real.log (u + 1) - 2 * ((u + 0) * Real.log (u + 0)) +
      (u + (-1)) * Real.log (u + (-1))
  have hfd : ∀ {u : ℝ}, 1 < u →
      HasDerivAt f (Real.log (u + 1) - 2 * Real.log u + Real.log (u - 1)) u := by
    intro u hu
    have t1 := hasDerivAt_shift_mul_log_aux (u := u) (a := 1) (by linarith)
    have t2 := (hasDerivAt_shift_mul_log_aux (u := u) (a := 0) (by linarith)).const_mul 2
    have t3 := hasDerivAt_shift_mul_log_aux (u := u) (a := -1) (by linarith)
    exact ((t1.sub t2).add t3).congr_deriv (by
      rw [show u + (-1) = u - 1 by ring, add_zero]
      ring)
  have hanti : StrictAntiOn f (Set.Ici (2 : ℝ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici 2) ?_ ?_
    · intro u hu
      exact (hfd (by linarith [Set.mem_Ici.mp hu])).continuousAt.continuousWithinAt
    · intro u hu
      have hu1 : 1 < u := by linarith [Set.mem_Ici.mp (interior_subset hu)]
      rw [(hfd hu1).deriv]
      have hu_m1 : 0 < u - 1 := by linarith
      have hu_0 : 0 < u := by linarith
      have hu_p1 : 0 < u + 1 := by linarith
      have hlogs : Real.log (u + 1) - 2 * Real.log u + Real.log (u - 1) =
          Real.log ((u + 1) * (u - 1)) - Real.log (u ^ 2) := by
        rw [Real.log_mul hu_p1.ne' hu_m1.ne', Real.log_pow]
        push_cast
        ring
      rw [hlogs, sub_lt_zero]
      refine Real.log_lt_log (mul_pos hu_p1 hu_m1) ?_
      nlinarith
  have hfeval : ∀ {k : ℕ}, 2 ≤ k → xLogXDiff k = f k := by
    intro k hk
    simp only [xLogXDiff, xLogX, f]
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hc, show (k : ℝ) + (-1) = (k : ℝ) - 1 by ring, add_zero]
    push_cast
    ring
  have h12 : xLogXDiff 2 < xLogXDiff 1 := by
    have hv1 : xLogXDiff 1 = 2 * Real.log 2 := by simp [xLogXDiff, xLogX]
    have hv2 : xLogXDiff 2 = 3 * Real.log 3 - 4 * Real.log 2 := by
      simp only [xLogXDiff, xLogX]; norm_num [log_four]; ring
    rw [hv1, hv2]
    linarith [Real.log_two_gt_d9, log_three_mem.2]
  by_cases hn1 : n = 1
  · subst hn1
    by_cases hm2 : m = 2
    · subst hm2; exact h12
    · have hm3 : 2 < m := by omega
      have hfm : xLogXDiff m < xLogXDiff 2 := by
        rw [hfeval (by omega), hfeval le_rfl]
        exact hanti (Set.mem_Ici.mpr le_rfl) (show (2 : ℝ) ≤ m by exact_mod_cast hm3.le)
          (by exact_mod_cast hm3)
      exact hfm.trans h12
  · have hn2 : 2 ≤ n := by omega
    rw [hfeval (by omega), hfeval hn2]
    exact hanti (show (2 : ℝ) ≤ n by exact_mod_cast hn2)
      (show (2 : ℝ) ≤ m by exact_mod_cast (by omega : 2 ≤ m)) (by exact_mod_cast hnm)

/-- Upper bound on the jet increase as the lower block moves from `a₁` up to `a₂ < b`. -/
theorem blockJet_sub_lt_half_xLogXDiff {a₁ a₂ b : ℕ} (h12 : a₁ < a₂) (h2b : a₂ < b) :
    blockJet a₂ b - blockJet a₁ b < xLogXDiff (b - a₂) / 2 := by
  simp only [blockJet]
  have hsum : xLogXDiff (a₂ + b + 1) < xLogXDiff (a₁ + b + 1) :=
    xLogXDiff_strictAnti (by omega) (by omega)
  have hpos : 0 < xLogXDiff (b - a₁) := xLogXDiff_pos (by omega)
  linarith

/-- Decomposition of `blockWeight Q a b` for `1 ≤ a < b < 4a` and `3 ≤ Q` into the jet and the
floor contacts of `2` and `3`. -/
theorem blockWeight_eq_jet_add_contacts {Q a b : ℕ} (hQ : 3 ≤ Q) (ha : 1 ≤ a) (hab : a < b)
    (hb : b < 4 * a) :
    blockWeight Q a b = blockJet a b +
      (if b / 2 = a then Real.log 2 / 2 else 0) +
      (if b / 3 = a then Real.log 3 / 3 else 0) := by
  rw [blockWeight_eq_four_of_lt_four_mul hQ ha hab hb, blockWeight, neutralBlock_of_lt hab,
    floorContact_four, if_neg (show b / 4 ≠ a from ne_of_lt (Nat.div_lt_of_lt_mul (by omega)))]
  ring

/-- Total cross-weight between `(R, 2R]` and `(2R, 4R]` for `3 ≤ Q` and `1 ≤ R`. -/
theorem sum_blockWeight_halves_fin {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R) :
    ∑ i : Fin R, ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j) =
      (R : ℝ) * (blockWeight 4 1 2 + blockWeight 4 1 3) := by
  have hfin : ∑ i : Fin R, ∑ j : Fin (2 * R), blockWeight Q (R + i) (2 * R + j) =
      ∑ i ∈ range R, ∑ j ∈ range (2 * R), blockWeight Q (R + i) (2 * R + j) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => ∑ j ∈ range (2 * R), blockWeight Q (R + i) (2 * R + j)) R]
    exact Finset.sum_congr rfl fun i _ =>
      Fin.sum_univ_eq_sum_range (fun j => blockWeight Q (R + i) (2 * R + j)) (2 * R)
  rw [hfin]
  have hsplit : ∑ i ∈ range R, ∑ j ∈ range (2 * R), blockWeight Q (R + i) (2 * R + j) =
      (∑ i ∈ range R, ∑ j ∈ range R, blockWeight Q (R + i) (2 * R + j)) +
        ∑ i ∈ range R, ∑ j ∈ range R, blockWeight Q (R + i) (3 * R + j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [two_mul, Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by
      rw [show R + R + (R + j) = 3 * R + j by omega]
  rw [hsplit, (sum_blockWeight_coarse_halves Q hR).1, (sum_blockWeight_coarse_halves Q hR).2,
    blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num),
    blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num)]
  ring

/-- Evaluates `coupled (neutralWindow Q R R) (neutralWindow Q (2R) (2R)) K` on a step function
`σ : ℕ → ℝ` restricted to `[0, R)` and `[R, 3R)`. -/
theorem bilin_coupled_halves_of_nat (Q R : ℕ) (σ : ℕ → ℝ) :
    bilin (coupled (neutralWindow Q R R) (neutralWindow Q (2 * R) (2 * R))
      (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)))
      (Sum.elim (fun i : Fin R => σ i) (fun j : Fin (2 * R) => σ (R + j)))
      (Sum.elim (fun i : Fin R => σ i) (fun j : Fin (2 * R) => σ (R + j))) =
      ∑ p ∈ range (3 * R), ∑ q ∈ range (3 * R), σ p * σ q * neutralBlock Q (R + p) (R + q) := by
  have hsplit : ∀ f : ℕ → ℝ, ∑ p ∈ range (3 * R), f p =
      (∑ i ∈ range R, f i) + ∑ j ∈ range (2 * R), f (R + j) := by
    intro f
    rw [show 3 * R = R + 2 * R by omega, Finset.sum_range_add]
  rw [bilin_coupled, hsplit]
  simp only [Sum.elim_inl, Sum.elim_inr, hsplit, Finset.sum_add_distrib]
  have bAA : bilin (neutralWindow Q R R) (fun i : Fin R => σ i) (fun i : Fin R => σ i) =
      ∑ i ∈ range R, ∑ l ∈ range R, σ i * σ l * neutralBlock Q (R + i) (R + l) := by
    rw [← sum_fin_windowMatrix_coe (neutralBlock Q) R R σ]
    simp only [bilin, neutralWindow]
  have bBB : bilin (neutralWindow Q (2 * R) (2 * R)) (fun j : Fin (2 * R) => σ (R + j))
      (fun j : Fin (2 * R) => σ (R + j)) =
      ∑ j ∈ range (2 * R), ∑ m ∈ range (2 * R),
        σ (R + j) * σ (R + m) * neutralBlock Q (R + (R + j)) (R + (R + m)) := by
    have h1 : bilin (neutralWindow Q (2 * R) (2 * R)) (fun j : Fin (2 * R) => σ (R + j))
        (fun j : Fin (2 * R) => σ (R + j)) =
        ∑ j ∈ range (2 * R), ∑ m ∈ range (2 * R),
          σ (R + j) * σ (R + m) * neutralBlock Q (2 * R + j) (2 * R + m) := by
      rw [← sum_fin_windowMatrix_coe (neutralBlock Q) (2 * R) (2 * R) (fun j => σ (R + j))]
      simp only [bilin, neutralWindow]
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by
      rw [show 2 * R + j = R + (R + j) by omega, show 2 * R + m = R + (R + m) by omega]
  have bAB : ∑ i : Fin R, ∑ j : Fin (2 * R),
      σ i * σ (R + j) * blockWeight Q (R + i) (2 * R + j) =
      -∑ i ∈ range R, ∑ j ∈ range (2 * R),
        σ i * σ (R + j) * neutralBlock Q (R + i) (R + (R + j)) := by
    have hfin : ∑ i : Fin R, ∑ j : Fin (2 * R),
        σ i * σ (R + j) * blockWeight Q (R + i) (2 * R + j) =
        ∑ i ∈ range R, ∑ j ∈ range (2 * R),
          σ i * σ (R + j) * blockWeight Q (R + i) (2 * R + j) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => ∑ j ∈ range (2 * R), σ i * σ (R + j) * blockWeight Q (R + i) (2 * R + j)) R]
      exact Finset.sum_congr rfl fun i _ =>
        Fin.sum_univ_eq_sum_range
          (fun j => σ i * σ (R + j) * blockWeight Q (R + i) (2 * R + j)) (2 * R)
    rw [hfin, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blockWeight, show 2 * R + j = R + (R + j) by omega]
    ring
  have bBA : ∑ j ∈ range (2 * R), ∑ i ∈ range R,
      σ (R + j) * σ i * neutralBlock Q (R + (R + j)) (R + i) =
      ∑ i ∈ range R, ∑ j ∈ range (2 * R),
        σ i * σ (R + j) * neutralBlock Q (R + i) (R + (R + j)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [neutralBlock_comm Q (R + (R + j)) (R + i)]
    ring
  linarith

private theorem min_eq_sub_max_sub (a b : ℝ) : min a b = b - max 0 (b - a) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonneg.mpr h)]; ring
  · rw [min_eq_right h, max_eq_left (sub_nonpos.mpr h)]; ring

/-- Uniform contact-dispersion lower bound across `(R, 2R] × (2R, 4R]` for `R ≥ 4`. -/
theorem sav_ratio_four_ge_of_four_le {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 4 ≤ R) (c : Fin R) :
    (27 / 100 : ℝ) * R ≤
      ∑ j ∈ range (2 * R), ∑ i : Fin R,
        max 0 (blockWeight Q (R + i) (2 * R + j) - blockWeight Q (R + c) (2 * R + j)) := by
  let savCol : ℕ → ℝ := fun j =>
    ∑ i : Fin R, max 0 (blockWeight Q (R + i) (2 * R + j) - blockWeight Q (R + c) (2 * R + j))
  have hsav0 : ∀ j, 0 ≤ savCol j := fun _ => Finset.sum_nonneg fun _ _ => le_max_left 0 _
  have hsingle : ∀ {j : ℕ} (i : Fin R) {δ : ℝ},
      δ ≤ blockWeight Q (R + i) (2 * R + j) - blockWeight Q (R + c) (2 * R + j) →
      δ ≤ savCol j := by
    intro j i δ h
    have hm : δ ≤ max 0 (blockWeight Q (R + i) (2 * R + j) - blockWeight Q (R + c) (2 * R + j)) :=
      le_max_of_le_right h
    exact hm.trans (Finset.single_le_sum
      (f := fun k : Fin R => max 0 (blockWeight Q (R + k) (2 * R + j) - blockWeight Q (R + c) (2 * R + j)))
      (fun _ _ => le_max_left 0 _) (Finset.mem_univ i))
  have hpair : ∀ {j : ℕ} {i₁ i₂ : Fin R} (hne : i₁ ≠ i₂) {δ₁ δ₂ : ℝ},
      δ₁ ≤ blockWeight Q (R + i₁) (2 * R + j) - blockWeight Q (R + c) (2 * R + j) →
      δ₂ ≤ blockWeight Q (R + i₂) (2 * R + j) - blockWeight Q (R + c) (2 * R + j) →
      δ₁ + δ₂ ≤ savCol j := by
    intro j i₁ i₂ hne δ₁ δ₂ h1 h2
    have hsub : ({i₁, i₂} : Finset (Fin R)) ⊆ Finset.univ := Finset.subset_univ _
    have hp := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
      le_max_left 0 (blockWeight Q (R + i) (2 * R + j) - blockWeight Q (R + c) (2 * R + j))
    rw [Finset.sum_pair hne] at hp
    exact le_trans (add_le_add (le_max_of_le_right h1) (le_max_of_le_right h2)) hp
  have hlog2 : (0.3465 : ℝ) < Real.log 2 / 2 := by linarith [Real.log_two_gt_d9]
  have hlog3 : (0.3662 : ℝ) < Real.log 3 / 3 := by linarith [log_three_mem.1]
  have hc_lt : (c : ℕ) < R := c.2
  by_cases h2c : 2 * (c : ℕ) < R
  · set M : ℕ := min (2 * R) (R + 3 * (c : ℕ))
    set N : ℕ := min (2 * R) (R + 3 * (c : ℕ) + 3)
    set I₁ : Finset ℕ := Ico (2 * (c : ℕ) + 2) M
    set I₂ : Finset ℕ := Ico N (2 * R)
    have hI₁_bound : ∀ j ∈ I₁, (0.346 : ℝ) ≤ savCol j := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hj2R : j < 2 * R := lt_of_lt_of_le hj2 (min_le_left _ _)
      have hj3c : j < R + 3 * (c : ℕ) := lt_of_lt_of_le hj2 (min_le_right _ _)
      let i₂ : Fin R := ⟨j / 2, by omega⟩
      refine hsingle i₂ ?_
      rw [blockWeight_eq_jet_add_contacts hQ (by omega) (by show R + j / 2 < 2 * R + j; omega)
          (by show 2 * R + j < 4 * (R + j / 2); omega),
        blockWeight_eq_jet_add_contacts hQ (by omega) (by omega) (by omega)]
      have hc2 : (2 * R + j) / 2 = R + (i₂ : ℕ) := by show (2 * R + j) / 2 = R + j / 2; omega
      have hnc2 : (2 * R + j) / 2 ≠ R + (c : ℕ) := by omega
      have hnc3 : (2 * R + j) / 3 ≠ R + (c : ℕ) := by omega
      have hjet : blockJet (R + c) (2 * R + j) < blockJet (R + i₂) (2 * R + j) :=
        blockJet_lt_of_lt (by omega) (by show R + (c : ℕ) < R + j / 2; omega)
          (by show R + j / 2 < 2 * R + j; omega)
      have h3nn : 0 ≤ (if (2 * R + j) / 3 = R + (i₂ : ℕ) then Real.log 3 / 3 else 0) := by
        split_ifs <;> linarith
      rw [if_pos hc2, if_neg hnc2, if_neg hnc3]
      linarith
    have hI₂_bound : ∀ j ∈ I₂, (0.712 : ℝ) ≤ savCol j := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hjN : R + 3 * (c : ℕ) + 3 ≤ j := le_trans (by
        rcases le_total (2 * R) (R + 3 * (c : ℕ) + 3) with hle | hle
        · exfalso; have : min (2 * R) (R + 3 * (c : ℕ) + 3) = 2 * R := min_eq_left hle; omega
        · exact (min_eq_right hle).symm.le) hj1
      let i₂ : Fin R := ⟨j / 2, by omega⟩
      let i₃ : Fin R := ⟨(j - R) / 3, by omega⟩
      have hne : i₂ ≠ i₃ := fun heq => by
        have hval : j / 2 = (j - R) / 3 := congrArg Fin.val heq
        omega
      refine le_trans (by norm_num : (0.712 : ℝ) ≤ 0.346 + 0.366) (hpair hne ?_ ?_)
      · rw [blockWeight_eq_jet_add_contacts hQ (by omega) (by show R + j / 2 < 2 * R + j; omega)
            (by show 2 * R + j < 4 * (R + j / 2); omega),
          blockWeight_eq_jet_add_contacts hQ (by omega) (by omega) (by omega)]
        have hc2 : (2 * R + j) / 2 = R + (i₂ : ℕ) := by show (2 * R + j) / 2 = R + j / 2; omega
        have hnc2 : (2 * R + j) / 2 ≠ R + (c : ℕ) := by omega
        have hnc3 : (2 * R + j) / 3 ≠ R + (c : ℕ) := by omega
        have hjet : blockJet (R + c) (2 * R + j) < blockJet (R + i₂) (2 * R + j) :=
          blockJet_lt_of_lt (by omega) (by show R + (c : ℕ) < R + j / 2; omega)
            (by show R + j / 2 < 2 * R + j; omega)
        have h3nn : 0 ≤ (if (2 * R + j) / 3 = R + (i₂ : ℕ) then Real.log 3 / 3 else 0) := by
          split_ifs <;> linarith
        rw [if_pos hc2, if_neg hnc2, if_neg hnc3]
        linarith
      · rw [blockWeight_eq_jet_add_contacts hQ (by omega)
            (by show R + (j - R) / 3 < 2 * R + j; omega)
            (by show 2 * R + j < 4 * (R + (j - R) / 3); omega),
          blockWeight_eq_jet_add_contacts hQ (by omega) (by omega) (by omega)]
        have hc3 : (2 * R + j) / 3 = R + (i₃ : ℕ) := by
          show (2 * R + j) / 3 = R + (j - R) / 3; omega
        have hnc2 : (2 * R + j) / 2 ≠ R + (c : ℕ) := by omega
        have hnc3 : (2 * R + j) / 3 ≠ R + (c : ℕ) := by omega
        have hjet : blockJet (R + c) (2 * R + j) < blockJet (R + i₃) (2 * R + j) :=
          blockJet_lt_of_lt (by omega) (by show R + (c : ℕ) < R + (j - R) / 3; omega)
            (by show R + (j - R) / 3 < 2 * R + j; omega)
        have h2nn : 0 ≤ (if (2 * R + j) / 2 = R + (i₃ : ℕ) then Real.log 2 / 2 else 0) := by
          split_ifs <;> linarith
        rw [if_pos hc3, if_neg hnc2, if_neg hnc3]
        linarith
    have hdisj12 : Disjoint I₁ I₂ := Finset.disjoint_left.mpr fun j hj1 hj2 => by
      have h1 := (Finset.mem_Ico.mp hj1).2
      have h2 := (Finset.mem_Ico.mp hj2).1
      have hMN : M ≤ N := min_le_min le_rfl (by omega)
      omega
    by_cases hc0 : (c : ℕ) = 0
    · have hsub : I₁ ∪ I₂ ⊆ range (2 * R) := fun j hj => by
        rcases Finset.mem_union.mp hj with h1 | h2
        · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp h1).2 (min_le_left _ _))
        · exact Finset.mem_range.mpr (Finset.mem_Ico.mp h2).2
      have hsum_ge := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hsav0 j
      rw [Finset.sum_union hdisj12] at hsum_ge
      have hs1 : (I₁.card : ℝ) * 0.346 ≤ ∑ j ∈ I₁, savCol j := by
        simpa [nsmul_eq_mul] using Finset.sum_le_sum hI₁_bound
      have hs2 : (I₂.card : ℝ) * 0.712 ≤ ∑ j ∈ I₂, savCol j := by
        simpa [nsmul_eq_mul] using Finset.sum_le_sum hI₂_bound
      have hc1 : I₁.card = R - 2 := by
        simp only [I₁, M, hc0, Nat.mul_zero, zero_add, add_zero, Nat.card_Ico]
        omega
      have hc2 : I₂.card = R - 3 := by
        simp only [I₂, N, hc0, Nat.mul_zero, add_zero, Nat.card_Ico]
        omega
      rw [hc1, Nat.cast_sub (by omega)] at hs1
      rw [hc2, Nat.cast_sub (by omega)] at hs2
      have hRr : (4 : ℝ) ≤ R := by exact_mod_cast hR
      push_cast at hs1 hs2
      linarith
    · set I₀ : Finset ℕ := Ico 0 2
      have hI₀_bound : ∀ j ∈ I₀, (0.146 : ℝ) ≤ savCol j := by
        intro j hj
        have hj2 : j < 2 := (Finset.mem_Ico.mp hj).2
        let i₀ : Fin R := ⟨0, by omega⟩
        refine hsingle i₀ ?_
        rw [blockWeight_eq_jet_add_contacts hQ (by omega) (by show R + 0 < 2 * R + j; omega)
            (by show 2 * R + j < 4 * (R + 0); omega),
          blockWeight_eq_jet_add_contacts hQ (by omega) (by omega) (by omega)]
        have hc2 : (2 * R + j) / 2 = R + (i₀ : ℕ) := by show (2 * R + j) / 2 = R + 0; omega
        have hnc2 : (2 * R + j) / 2 ≠ R + (c : ℕ) := by omega
        have hnc3 : (2 * R + j) / 3 ≠ R + (c : ℕ) := by omega
        have hjet := blockJet_sub_lt_half_xLogXDiff (a₁ := R + 0) (a₂ := R + c) (b := 2 * R + j)
          (by omega) (by omega)
        have hd3 : 3 ≤ 2 * R + j - (R + (c : ℕ)) := by omega
        have hdiff_le : xLogXDiff (2 * R + j - (R + (c : ℕ))) ≤ 2 / 5 := by
          have hd_r : (3 : ℝ) ≤ (2 * R + j - (R + (c : ℕ)) : ℕ) := by exact_mod_cast hd3
          exact (xLogXDiff_le_two_div (by omega)).trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
        have h3nn : 0 ≤ (if (2 * R + j) / 3 = R + (i₀ : ℕ) then Real.log 3 / 3 else 0) := by
          split_ifs <;> linarith
        rw [if_pos hc2, if_neg hnc2, if_neg hnc3]
        linarith
      have hdisj01 : Disjoint I₀ I₁ := Finset.disjoint_left.mpr fun j hj0 hj1 => by
        have := (Finset.mem_Ico.mp hj0).2
        have := (Finset.mem_Ico.mp hj1).1
        omega
      have hdisj02 : Disjoint I₀ I₂ := Finset.disjoint_left.mpr fun j hj0 hj2 => by
        have := (Finset.mem_Ico.mp hj0).2
        have h2 := (Finset.mem_Ico.mp hj2).1
        have hN4 : 4 ≤ N := le_min (by omega) (by omega)
        omega
      have hsub : (I₀ ∪ I₁) ∪ I₂ ⊆ range (2 * R) := fun j hj => by
        rcases Finset.mem_union.mp hj with h01 | h2
        · rcases Finset.mem_union.mp h01 with h0 | h1
          · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp h0).2 (by omega))
          · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp h1).2 (min_le_left _ _))
        · exact Finset.mem_range.mpr (Finset.mem_Ico.mp h2).2
      have hsum_ge := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hsav0 j
      rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj02, hdisj12⟩),
        Finset.sum_union hdisj01] at hsum_ge
      have hs0 : (2 : ℝ) * 0.146 ≤ ∑ j ∈ I₀, savCol j := by
        have hc0_card : I₀.card = 2 := by simp [I₀]
        simpa [hc0_card, nsmul_eq_mul] using Finset.sum_le_sum hI₀_bound
      have hs1 : (I₁.card : ℝ) * 0.346 ≤ ∑ j ∈ I₁, savCol j := by
        simpa [nsmul_eq_mul] using Finset.sum_le_sum hI₁_bound
      have hs2 : (I₂.card : ℝ) * 0.712 ≤ ∑ j ∈ I₂, savCol j := by
        simpa [nsmul_eq_mul] using Finset.sum_le_sum hI₂_bound
      have hRr : (4 : ℝ) ≤ R := by exact_mod_cast hR
      by_cases hcase1 : R + 3 * (c : ℕ) + 3 ≤ 2 * R
      · have hc1 : I₁.card = R + (c : ℕ) - 2 := by simp only [I₁, M, Nat.card_Ico]; omega
        have hc2 : I₂.card = R - 3 * (c : ℕ) - 3 := by simp only [I₂, N, Nat.card_Ico]; omega
        have hc1_r : (I₁.card : ℝ) = (R : ℝ) + (c : ℕ) - 2 := by
          rw [hc1, Nat.cast_sub (by omega)]; push_cast; ring
        have hc2_r : (I₂.card : ℝ) = (R : ℝ) - 3 * (c : ℕ) - 3 := by
          have : R - 3 * (c : ℕ) - 3 = R - (3 * (c : ℕ) + 3) := by omega
          rw [hc2, this, Nat.cast_sub (by omega)]; push_cast; ring
        have hcr : (3 : ℝ) * (c : ℕ) + 3 ≤ R := by exact_mod_cast (by omega : 3 * (c : ℕ) + 3 ≤ R)
        rw [hc1_r] at hs1
        rw [hc2_r] at hs2
        linarith
      · have hs2_nn : (0 : ℝ) ≤ ∑ j ∈ I₂, savCol j := Finset.sum_nonneg fun j _ => hsav0 j
        by_cases hcase2 : R + 3 * (c : ℕ) ≤ 2 * R
        · have hc1 : I₁.card = R + (c : ℕ) - 2 := by simp only [I₁, M, Nat.card_Ico]; omega
          have hc1_r : (I₁.card : ℝ) = (R : ℝ) + (c : ℕ) - 2 := by
            rw [hc1, Nat.cast_sub (by omega)]; push_cast; ring
          have hcr : (R : ℝ) ≤ 3 * (c : ℕ) + 2 := by exact_mod_cast (by omega : R ≤ 3 * (c : ℕ) + 2)
          rw [hc1_r] at hs1
          linarith
        · have hc1 : I₁.card = 2 * R - (2 * (c : ℕ) + 2) := by
            simp only [I₁, M, Nat.card_Ico]; omega
          have hc1_r : (I₁.card : ℝ) = 2 * (R : ℝ) - 2 * (c : ℕ) - 2 := by
            rw [hc1, Nat.cast_sub (by omega)]; push_cast; ring
          have hcr : 2 * ((c : ℕ) : ℝ) + 1 ≤ R := by exact_mod_cast h2c
          rw [hc1_r] at hs1
          linarith
  · -- Subcase `R ≤ 2 * c`
    have hR2c : R ≤ 2 * (c : ℕ) := not_lt.mp h2c
    set J₁ : Finset ℕ := Ico 2 R
    set J₂ : Finset ℕ := ((Ico R (2 * R)).erase (2 * (c : ℕ))).erase (2 * (c : ℕ) + 1)
    have hJ₁_bound : ∀ j ∈ J₁, (0.146 : ℝ) ≤ savCol j := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      let i₂ : Fin R := ⟨j / 2, by omega⟩
      refine hsingle i₂ ?_
      rw [blockWeight_eq_jet_add_contacts hQ (by omega) (by show R + j / 2 < 2 * R + j; omega)
          (by show 2 * R + j < 4 * (R + j / 2); omega),
        blockWeight_eq_jet_add_contacts hQ (by omega) (by omega) (by omega)]
      have hc2 : (2 * R + j) / 2 = R + (i₂ : ℕ) := by show (2 * R + j) / 2 = R + j / 2; omega
      have hnc2 : (2 * R + j) / 2 ≠ R + (c : ℕ) := by omega
      have hnc3 : (2 * R + j) / 3 ≠ R + (c : ℕ) := by omega
      have hjet := blockJet_sub_lt_half_xLogXDiff (a₁ := R + i₂) (a₂ := R + c) (b := 2 * R + j)
        (by show R + j / 2 < R + (c : ℕ); omega) (by omega)
      have hd3 : 3 ≤ 2 * R + j - (R + (c : ℕ)) := by omega
      have hdiff_le : xLogXDiff (2 * R + j - (R + (c : ℕ))) ≤ 2 / 5 := by
        have hd_r : (3 : ℝ) ≤ (2 * R + j - (R + (c : ℕ)) : ℕ) := by exact_mod_cast hd3
        exact (xLogXDiff_le_two_div (by omega)).trans
          (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
      have h3nn : 0 ≤ (if (2 * R + j) / 3 = R + (i₂ : ℕ) then Real.log 3 / 3 else 0) := by
        split_ifs <;> linarith
      rw [if_pos hc2, if_neg hnc2, if_neg hnc3]
      linarith
    have hJ₂_bound : ∀ j ∈ J₂, (0.49 : ℝ) ≤ savCol j := by
      intro j hj
      obtain ⟨hne2, hj'⟩ := Finset.mem_erase.mp hj
      obtain ⟨hne1, hj''⟩ := Finset.mem_erase.mp hj'
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj''
      let i₂ : Fin R := ⟨j / 2, by omega⟩
      let i₃ : Fin R := ⟨(j - R) / 3, by omega⟩
      have hne : i₂ ≠ i₃ := fun heq => by
        have hval : j / 2 = (j - R) / 3 := congrArg Fin.val heq
        omega
      have hd5 : 5 ≤ 2 * R + j - (R + (c : ℕ)) := by omega
      have hdiff_le : xLogXDiff (2 * R + j - (R + (c : ℕ))) ≤ 2 / 9 := by
        have hd_r : (5 : ℝ) ≤ (2 * R + j - (R + (c : ℕ)) : ℕ) := by exact_mod_cast hd5
        exact (xLogXDiff_le_two_div (by omega)).trans
          (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith))
      refine le_trans (by norm_num : (0.49 : ℝ) ≤ 0.235 + 0.255) (hpair hne ?_ ?_)
      · rw [blockWeight_eq_jet_add_contacts hQ (by omega) (by show R + j / 2 < 2 * R + j; omega)
            (by show 2 * R + j < 4 * (R + j / 2); omega),
          blockWeight_eq_jet_add_contacts hQ (by omega) (by omega) (by omega)]
        have hc2 : (2 * R + j) / 2 = R + (i₂ : ℕ) := by show (2 * R + j) / 2 = R + j / 2; omega
        have hnc2 : (2 * R + j) / 2 ≠ R + (c : ℕ) := by omega
        have hnc3 : (2 * R + j) / 3 ≠ R + (c : ℕ) := by omega
        have hjet : -(1 / 9 : ℝ) < blockJet (R + i₂) (2 * R + j) - blockJet (R + c) (2 * R + j) := by
          rcases lt_trichotomy (j / 2) (c : ℕ) with hlt | heq | hgt
          · have hj' := blockJet_sub_lt_half_xLogXDiff (a₁ := R + i₂) (a₂ := R + c) (b := 2 * R + j)
              (by show R + j / 2 < R + (c : ℕ); omega) (by omega)
            linarith
          · omega
          · have hj' := blockJet_lt_of_lt (a₁ := R + c) (a₂ := R + i₂) (b := 2 * R + j)
              (by omega) (by show R + (c : ℕ) < R + j / 2; omega)
              (by show R + j / 2 < 2 * R + j; omega)
            linarith
        have h3nn : 0 ≤ (if (2 * R + j) / 3 = R + (i₂ : ℕ) then Real.log 3 / 3 else 0) := by
          split_ifs <;> linarith
        rw [if_pos hc2, if_neg hnc2, if_neg hnc3]
        linarith
      · rw [blockWeight_eq_jet_add_contacts hQ (by omega)
            (by show R + (j - R) / 3 < 2 * R + j; omega)
            (by show 2 * R + j < 4 * (R + (j - R) / 3); omega),
          blockWeight_eq_jet_add_contacts hQ (by omega) (by omega) (by omega)]
        have hc3 : (2 * R + j) / 3 = R + (i₃ : ℕ) := by
          show (2 * R + j) / 3 = R + (j - R) / 3; omega
        have hnc2 : (2 * R + j) / 2 ≠ R + (c : ℕ) := by omega
        have hnc3 : (2 * R + j) / 3 ≠ R + (c : ℕ) := by omega
        have hjet := blockJet_sub_lt_half_xLogXDiff (a₁ := R + i₃) (a₂ := R + c) (b := 2 * R + j)
          (by show R + (j - R) / 3 < R + (c : ℕ); omega) (by omega)
        have h2nn : 0 ≤ (if (2 * R + j) / 2 = R + (i₃ : ℕ) then Real.log 2 / 2 else 0) := by
          split_ifs <;> linarith
        rw [if_pos hc3, if_neg hnc2, if_neg hnc3]
        linarith
    have hdisj : Disjoint J₁ J₂ := Finset.disjoint_left.mpr fun j hj1 hj2 => by
      have h1 := (Finset.mem_Ico.mp hj1).2
      have h2 := (Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hj2).2).2).1
      omega
    have hsub : J₁ ∪ J₂ ⊆ range (2 * R) := fun j hj => by
      rcases Finset.mem_union.mp hj with h1 | h2
      · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp h1).2 (by omega))
      · exact Finset.mem_range.mpr
          (Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_erase.mp h2).2).2).2
    have hsum_ge := Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hsav0 j
    rw [Finset.sum_union hdisj] at hsum_ge
    have hs1 : (J₁.card : ℝ) * 0.146 ≤ ∑ j ∈ J₁, savCol j := by
      simpa [nsmul_eq_mul] using Finset.sum_le_sum hJ₁_bound
    have hs2 : (J₂.card : ℝ) * 0.49 ≤ ∑ j ∈ J₂, savCol j := by
      simpa [nsmul_eq_mul] using Finset.sum_le_sum hJ₂_bound
    have hc1 : J₁.card = R - 2 := by simp only [J₁, Nat.card_Ico]
    have hc2_ge : R - 2 ≤ J₂.card := by
      have e1 := Finset.pred_card_le_card_erase (s := Ico R (2 * R)) (a := 2 * (c : ℕ))
      have e2 := Finset.pred_card_le_card_erase
        (s := (Ico R (2 * R)).erase (2 * (c : ℕ))) (a := 2 * (c : ℕ) + 1)
      have hc0 : (Ico R (2 * R)).card = R := by simp only [Nat.card_Ico]; omega
      dsimp only [J₂]
      omega
    have hc1_r : (J₁.card : ℝ) = (R : ℝ) - 2 := by rw [hc1, Nat.cast_sub (by omega)]; push_cast; rfl
    have hc2_r : (R : ℝ) - 2 ≤ J₂.card := by
      have : ((R - 2 : ℕ) : ℝ) ≤ J₂.card := by exact_mod_cast hc2_ge
      rwa [Nat.cast_sub (by omega), Nat.cast_ofNat] at this
    have hRr : (4 : ℝ) ≤ R := by exact_mod_cast hR
    rw [hc1_r] at hs1
    nlinarith

private theorem coarse_plane_disc_of_bounds {R_r A₀ B₀ P : ℝ} (hRr : 4 ≤ R_r)
    (hA₀_1 : -3.4400 * R_r < A₀) (hA₀_2 : A₀ < -3.4396 * R_r)
    (hB₀_1 : -4.6388 * R_r < B₀) (hB₀_2 : B₀ < -4.6382 * R_r)
    (hP_ub : P < 1.9712 * R_r) :
    A₀ + P < 0 ∧ (-P) ^ 2 < (A₀ + P) * (B₀ + P) := by
  refine ⟨by linarith only [hRr, hA₀_2, hP_ub], ?_⟩
  have hR2 : 16 ≤ R_r ^ 2 := by nlinarith only [hRr]
  have halg : (A₀ + P) * (B₀ + P) - (-P) ^ 2 = A₀ * B₀ + (A₀ + B₀) * P := by ring
  have hAB : 3.4396 * 4.6382 * R_r ^ 2 < A₀ * B₀ := by
    nlinarith only [hRr, hA₀_1, hA₀_2, hB₀_1, hB₀_2]
  rcases le_or_gt P 0 with hP0 | hP0
  · have h1 : 0 ≤ (A₀ + B₀) * P :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith only [hRr, hA₀_2, hB₀_2]) hP0
    linarith only [hR2, halg, hAB, h1]
  · have h1 : -(8.0788 * 1.9712 : ℝ) * R_r ^ 2 < (A₀ + B₀) * P := by
      nlinarith only [hRr, hA₀_1, hA₀_2, hB₀_1, hB₀_2, hP0, hP_ub]
    linarith only [hR2, halg, hAB, h1]

/-- For every `R ≥ 4`, `3 ≤ Q`, and admissible charge pair `u_i v_j ≤ K_ij`, the lowered glued form
has at least two negative squares. -/
theorem two_le_hermNegIndex_glued_lowered_of_four_le {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 4 ≤ R)
    {u : Fin R → ℝ} {v : Fin (2 * R) → ℝ}
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (R + i) (2 * R + j)) :
    2 ≤ hermNegIndex ((glued
      (neutralWindow Q R R -
        diagonal (excessLeft
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v))
      (neutralWindow Q (2 * R) (2 * R) -
        diagonal (excessRight
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v))
      u v).map (↑) : Matrix (Fin R ⊕ Fin (2 * R)) (Fin R ⊕ Fin (2 * R)) ℂ) := by
  set K : Fin R → Fin (2 * R) → ℝ := fun i j => blockWeight Q (R + i) (2 * R + j)
  haveI : Nonempty (Fin R) := ⟨⟨0, by omega⟩⟩
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => (blockWeight_pos (by have := i.2; omega) Q).le
  obtain ⟨c, hc_min⟩ := exists_sum_mul_sum_le_sum_min hK0 huv Finset.univ
  set SK : ℝ := ∑ i : Fin R, ∑ j : Fin (2 * R), K i j
  have hSK : SK = (R : ℝ) * (blockWeight 4 1 2 + blockWeight 4 1 3) :=
    sum_blockWeight_halves_fin hQ (by omega)
  set P : ℝ := (∑ i, u i) * (∑ j, v j)
  have hP_le : P ≤ SK - (27 / 100 : ℝ) * R := by
    have hmin_eq : ∑ i : Fin R, ∑ j : Fin (2 * R), min (K c j) (K i j) =
        SK - ∑ j ∈ range (2 * R), ∑ i : Fin R,
          max 0 (blockWeight Q (R + i) (2 * R + j) - blockWeight Q (R + c) (2 * R + j)) := by
      simp only [min_eq_sub_max_sub, Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_comm]
      exact Fin.sum_univ_eq_sum_range (fun j => ∑ i : Fin R,
        max 0 (blockWeight Q (R + i) (2 * R + j) - blockWeight Q (R + c) (2 * R + j))) (2 * R)
    have hsav := sav_ratio_four_ge_of_four_le (Q := Q) hQ hR c
    linarith
  let w₁ : Fin R ⊕ Fin (2 * R) → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)
  let w₂ : Fin R ⊕ Fin (2 * R) → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)
  set A₀ : ℝ := (R : ℝ) * neutralBlock 4 1 1 - SK
  set B₀ : ℝ := (R : ℝ) * (neutralBlock 4 2 2 + neutralBlock 4 3 3 + 2 * neutralBlock 4 2 3) - SK
  refine two_le_hermNegIndex_of_binary_plane _ w₁ w₂ (α := A₀ + P) (γ := B₀ + P) (c := -P) ?_ ?_ ?_
  · intro s t
    have hw_eq : (fun m : Fin R ⊕ Fin (2 * R) => s * w₁ m + t * w₂ m) =
        Sum.elim (fun _ => s) (fun _ => t) := by
      funext x; rcases x with i | j <;> simp [w₁, w₂]
    rw [hw_eq, bilin_glued_lowered_eq_coupled_sub]
    let σ : ℕ → ℝ := fun p => if p < R then s else if p < 2 * R then t else t
    have hse : (Sum.elim (fun _ : Fin R => s) (fun _ : Fin (2 * R) => t)) =
        Sum.elim (fun i : Fin R => σ i) (fun j : Fin (2 * R) => σ (R + j)) := by
      funext x; rcases x with i | j
      · dsimp only [Sum.elim_inl, σ]
        rw [if_pos i.2]
      · have h1 : ¬R + (j : ℕ) < R := by omega
        dsimp only [Sum.elim_inr, σ]
        rw [if_neg h1]
        split_ifs <;> rfl
    rw [hse, bilin_coupled_halves_of_nat Q R σ]
    have hstep := sum_neutralBlock_three_steps Q (R := R) (by omega) s t t
    have hstep_eq : ∑ p ∈ range (3 * R), ∑ q ∈ range (3 * R), σ p * σ q * neutralBlock Q (R + p) (R + q) =
        (R : ℝ) * (s ^ 2 * neutralBlock 4 1 1 + t ^ 2 * (neutralBlock 4 2 2 + neutralBlock 4 3 3 +
          2 * neutralBlock 4 2 3) + 2 * s * t * (neutralBlock 4 1 2 + neutralBlock 4 1 3)) := by
      dsimp only [σ]
      rw [hstep,
        neutralBlock_eq_four_of_lt_four_mul hQ le_rfl le_rfl (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
      ring
    have hex_sum : ∑ i : Fin R, ∑ j : Fin (2 * R),
        (K i j - u i * v j) *
          (Sum.elim (fun i : Fin R => σ i) (fun j : Fin (2 * R) => σ (R + j)) (Sum.inl i) -
            Sum.elim (fun i : Fin R => σ i) (fun j : Fin (2 * R) => σ (R + j)) (Sum.inr j)) ^ 2 =
        (SK - P) * (s - t) ^ 2 := by
      have hdiff : ∀ (i : Fin R) (j : Fin (2 * R)),
          (Sum.elim (fun i : Fin R => σ i) (fun j : Fin (2 * R) => σ (R + j)) (Sum.inl i) -
            Sum.elim (fun i : Fin R => σ i) (fun j : Fin (2 * R) => σ (R + j)) (Sum.inr j)) =
          s - t := fun i j => by
        have h1 : ¬R + (j : ℕ) < R := by omega
        dsimp only [Sum.elim_inl, Sum.elim_inr, σ]
        rw [if_pos i.2, if_neg h1]
        split_ifs <;> rfl
      simp only [hdiff, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul_sum]
      rfl
    rw [hstep_eq, hex_sum]
    dsimp only [A₀, B₀]
    rw [hSK]
    simp only [blockWeight]
    exact le_of_eq (by ring)
  · have hb := neutralBlock_four_coarse_bounds
    have hRr : (4 : ℝ) ≤ R := by exact_mod_cast hR
    have hA₀_2 : A₀ < -3.4396 * R := by
      dsimp only [A₀]; rw [hSK]; simp only [blockWeight]
      have h1 := hb.1.2; have h2 := hb.2.1.2; have h3 := hb.2.2.1.2
      nlinarith only [hRr, h1, h2, h3]
    have hP_ub : P < 1.9712 * R := by
      rw [hSK] at hP_le; simp only [blockWeight] at hP_le
      have h2 := hb.2.1.1; have h3 := hb.2.2.1.1
      nlinarith only [hRr, hP_le, h2, h3]
    linarith only [hRr, hA₀_2, hP_ub]
  · have hb := neutralBlock_four_coarse_bounds
    have hRr : (4 : ℝ) ≤ R := by exact_mod_cast hR
    have hA₀_1 : -(3.4400 : ℝ) * R < A₀ := by
      dsimp only [A₀]; rw [hSK]; simp only [blockWeight]
      have h1 := hb.1.1; have h2 := hb.2.1.1; have h3 := hb.2.2.1.1
      nlinarith only [hRr, h1, h2, h3]
    have hA₀_2 : A₀ < -3.4396 * R := by
      dsimp only [A₀]; rw [hSK]; simp only [blockWeight]
      have h1 := hb.1.2; have h2 := hb.2.1.2; have h3 := hb.2.2.1.2
      nlinarith only [hRr, h1, h2, h3]
    have hB₀_1 : -(4.6388 : ℝ) * R < B₀ := by
      dsimp only [B₀]; rw [hSK]; simp only [blockWeight]
      have h1 := hb.2.2.2.1.1; have h2 := hb.2.2.2.2.1.1; have h3 := hb.2.2.2.2.2.1
      have h4 := hb.2.1.1; have h5 := hb.2.2.1.1
      nlinarith only [hRr, h1, h2, h3, h4, h5]
    have hB₀_2 : B₀ < -4.6382 * R := by
      dsimp only [B₀]; rw [hSK]; simp only [blockWeight]
      have h1 := hb.2.2.2.1.2; have h2 := hb.2.2.2.2.1.2; have h3 := hb.2.2.2.2.2.2
      have h4 := hb.2.1.2; have h5 := hb.2.2.1.2
      nlinarith only [hRr, h1, h2, h3, h4, h5]
    have hP_ub : P < 1.9712 * R := by
      rw [hSK] at hP_le; simp only [blockWeight] at hP_le
      have h2 := hb.2.1.1; have h3 := hb.2.2.1.1
      nlinarith only [hRr, hP_le, h2, h3]
    exact (coarse_plane_disc_of_bounds hRr hA₀_1 hA₀_2 hB₀_1 hB₀_2 hP_ub).2

/-- For `R = 3` and `3 ≤ Q`, the lowered glued form has at least two negative squares for every
admissible charge pair. -/
theorem two_le_hermNegIndex_glued_lowered_three {Q : ℕ} (hQ : 3 ≤ Q)
    {u : Fin 3 → ℝ} {v : Fin 6 → ℝ}
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (3 + i) (6 + j)) :
    2 ≤ hermNegIndex ((glued
      (neutralWindow Q 3 3 -
        diagonal (excessLeft
          (fun (i : Fin 3) (j : Fin 6) => blockWeight Q (3 + i) (6 + j)) u v))
      (neutralWindow Q 6 6 -
        diagonal (excessRight
          (fun (i : Fin 3) (j : Fin 6) => blockWeight Q (3 + i) (6 + j)) u v))
      u v).map (↑) : Matrix (Fin 3 ⊕ Fin 6) (Fin 3 ⊕ Fin 6) ℂ) := by
  set K : Fin 3 → Fin 6 → ℝ := fun i j => blockWeight Q (3 + i) (6 + j)
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => (blockWeight_pos (by have := i.2; omega) Q).le
  set S : Finset (Fin 6) := {0, 1, 2}
  obtain ⟨c, hc_min⟩ := exists_sum_mul_sum_le_sum_min hK0 huv S
  have hSK1 : ∑ i : Fin 3, ∑ j ∈ S, K i j = 3 * blockWeight 4 1 2 := by
    have h1 := (sum_blockWeight_coarse_halves Q (R := 3) (by norm_num)).1
    rw [blockWeight_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num),
      Nat.cast_ofNat] at h1
    have hS : ∀ i : Fin 3, ∑ j ∈ S, K i j = ∑ j ∈ range 3, blockWeight Q (3 + i) (6 + j) := by
      intro i
      have h0 : (0 : Fin 6) ∉ ({1, 2} : Finset (Fin 6)) := by decide
      have h12 : (1 : Fin 6) ∉ ({2} : Finset (Fin 6)) := by decide
      rw [show S = insert 0 (insert 1 {2}) from rfl, Finset.sum_insert h0, Finset.sum_insert h12,
        Finset.sum_singleton]
      simp only [K, Fin.val_zero, Fin.val_one, Fin.val_two, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
      ring
    simp only [hS]
    rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range 3, blockWeight Q (3 + i) (6 + j)) 3]
    exact h1
  have hsav_c : (0.52 : ℝ) ≤ ∑ i : Fin 3, ∑ j ∈ S, max 0 (K i j - K c j) := by
    have hpairS : ∀ {i₁ i₂ : Fin 3} {j₁ j₂ : Fin 6} (hj1 : j₁ ∈ S) (hj2 : j₂ ∈ S)
        (hne : (i₁, j₁) ≠ (i₂, j₂)) {δ₁ δ₂ : ℝ},
        δ₁ ≤ K i₁ j₁ - K c j₁ → δ₂ ≤ K i₂ j₂ - K c j₂ →
        δ₁ + δ₂ ≤ ∑ i : Fin 3, ∑ j ∈ S, max 0 (K i j - K c j) := by
      intro i₁ i₂ j₁ j₂ hj1 hj2 hne δ₁ δ₂ h1 h2
      rw [← Finset.sum_product']
      have hmem1 : (i₁, j₁) ∈ (Finset.univ : Finset (Fin 3)) ×ˢ S :=
        Finset.mem_product.mpr ⟨Finset.mem_univ _, hj1⟩
      have hmem2 : (i₂, j₂) ∈ (Finset.univ : Finset (Fin 3)) ×ˢ S :=
        Finset.mem_product.mpr ⟨Finset.mem_univ _, hj2⟩
      have hsub : ({(i₁, j₁), (i₂, j₂)} : Finset (Fin 3 × Fin 6)) ⊆ Finset.univ ×ˢ S :=
        fun p hp => by
          rcases Finset.mem_insert.mp hp with rfl | hp'
          · exact hmem1
          · rw [Finset.mem_singleton.mp hp']; exact hmem2
      have hp := Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
        le_max_left 0 (K p.1 p.2 - K c p.2)
      rw [Finset.sum_pair hne] at hp
      exact le_trans (add_le_add (le_max_of_le_right h1) (le_max_of_le_right h2)) hp
    have hK4 : ∀ (i : Fin 3) (j : Fin 6), (j : ℕ) < 3 →
        K i j = blockWeight 4 (3 + i) (6 + j) := fun i j hj =>
      blockWeight_eq_four_of_lt_four_mul hQ (by omega) (by omega) (by have := i.2; omega)
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by fin_cases c <;> simp) with rfl | rfl | rfl
    · refine le_trans (by norm_num : (0.52 : ℝ) ≤ 0.16 + 0.36)
        (hpairS (i₁ := 2) (j₁ := 0) (i₂ := 1) (j₂ := 2) (by decide) (by decide) (by decide) ?_ ?_)
      · rw [hK4 2 0 (by decide), hK4 0 0 (by decide)]
        simp only [Fin.val_two, Fin.val_zero, add_zero, blockWeight]
        rw [neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num),
          floorContact_four, floorContact_four]
        neutral_entry
      · rw [hK4 1 2 (by decide), hK4 0 2 (by decide)]
        simp only [Fin.val_one, Fin.val_two, Fin.val_zero, add_zero, blockWeight]
        rw [neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num),
          floorContact_four, floorContact_four]
        neutral_entry
    · refine le_trans (by norm_num : (0.52 : ℝ) ≤ 0.25 + 0.30)
        (hpairS (i₁ := 0) (j₁ := 0) (i₂ := 0) (j₂ := 1) (by decide) (by decide) (by decide) ?_ ?_)
      · rw [hK4 0 0 (by decide), hK4 1 0 (by decide)]
        simp only [Fin.val_zero, Fin.val_one, add_zero, blockWeight]
        rw [neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num),
          floorContact_four, floorContact_four]
        neutral_entry
      · rw [hK4 0 1 (by decide), hK4 1 1 (by decide)]
        simp only [Fin.val_zero, Fin.val_one, add_zero, blockWeight]
        rw [neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num),
          floorContact_four, floorContact_four]
        neutral_entry
    · refine le_trans (by norm_num : (0.52 : ℝ) ≤ 0.218 + 0.305)
        (hpairS (i₁ := 0) (j₁ := 1) (i₂ := 1) (j₂ := 2) (by decide) (by decide) (by decide) ?_ ?_)
      · rw [hK4 0 1 (by decide), hK4 2 1 (by decide)]
        simp only [Fin.val_zero, Fin.val_two, Fin.val_one, add_zero, blockWeight]
        rw [neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num),
          floorContact_four, floorContact_four]
        neutral_entry
      · rw [hK4 1 2 (by decide), hK4 2 2 (by decide)]
        simp only [Fin.val_one, Fin.val_two, blockWeight]
        rw [neutralBlock_of_lt (by norm_num), neutralBlock_of_lt (by norm_num),
          floorContact_four, floorContact_four]
        neutral_entry
  have hex_ge : (4.68 : ℝ) ≤ ∑ i : Fin 3, ∑ j ∈ S, 9 * (K i j - u i * v j) := by
    have hmin_eq : ∑ i : Fin 3, ∑ j ∈ S, min (K c j) (K i j) =
        (∑ i : Fin 3, ∑ j ∈ S, K i j) - ∑ i : Fin 3, ∑ j ∈ S, max 0 (K i j - K c j) := by
      simp only [min_eq_sub_max_sub, Finset.sum_sub_distrib]
    have hprod_eq : ∑ i : Fin 3, ∑ j ∈ S, (K i j - u i * v j) =
        (∑ i : Fin 3, ∑ j ∈ S, K i j) - (∑ i : Fin 3, u i) * (∑ j ∈ S, v j) := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_mul_sum]
    have h9 : ∑ i : Fin 3, ∑ j ∈ S, 9 * (K i j - u i * v j) =
        9 * ∑ i : Fin 3, ∑ j ∈ S, (K i j - u i * v j) := by
      simp only [← Finset.mul_sum]
    linarith
  let z₁ : Fin 3 ⊕ Fin 6 → ℝ := Sum.elim (fun _ => 1) (fun _ => 1)
  let z₂ : Fin 3 ⊕ Fin 6 → ℝ :=
    Sum.elim (fun _ => -1) (fun j : Fin 6 => if (j : ℕ) < 3 then 2 else 0)
  have hb := neutralBlock_four_coarse_bounds
  set α₀ : ℝ := 3 * (neutralBlock 4 1 1 + neutralBlock 4 2 2 + neutralBlock 4 3 3 +
    2 * neutralBlock 4 1 2 + 2 * neutralBlock 4 1 3 + 2 * neutralBlock 4 2 3)
  set c₀ : ℝ := 3 * (-neutralBlock 4 1 1 + 2 * neutralBlock 4 2 2 + neutralBlock 4 1 2 -
    neutralBlock 4 1 3 + 2 * neutralBlock 4 2 3)
  set γ₀ : ℝ := 3 * (neutralBlock 4 1 1 + 4 * neutralBlock 4 2 2 - 4 * neutralBlock 4 1 2)
  refine two_le_hermNegIndex_of_binary_plane _ z₁ z₂ (α := α₀) (γ := γ₀ - 4.68) (c := c₀) ?_ ?_ ?_
  · intro s t
    rw [bilin_glued_lowered_eq_coupled_sub]
    let σ : ℕ → ℝ := fun p => if p < 3 then s - t else if p < 6 then s + 2 * t else s
    have hse : (fun m : Fin 3 ⊕ Fin 6 => s * z₁ m + t * z₂ m) =
        Sum.elim (fun i : Fin 3 => σ i) (fun j : Fin 6 => σ (3 + j)) := by
      funext x; rcases x with i | j
      · simp only [z₁, z₂, Sum.elim_inl, σ, if_pos i.2]; ring
      · have h1 : ¬3 + (j : ℕ) < 3 := by omega
        by_cases hj3 : (j : ℕ) < 3
        · have h2 : 3 + (j : ℕ) < 6 := by omega
          simp only [z₁, z₂, Sum.elim_inr, σ, if_neg h1, if_pos hj3, if_pos h2]; ring
        · have h2 : ¬3 + (j : ℕ) < 6 := by omega
          simp only [z₁, z₂, Sum.elim_inr, σ, if_neg h1, if_neg hj3, if_neg h2]; ring
    have hcoup : bilin (coupled (neutralWindow Q 3 3) (neutralWindow Q 6 6) K)
        (fun m => s * z₁ m + t * z₂ m) (fun m => s * z₁ m + t * z₂ m) =
        α₀ * s ^ 2 + 2 * c₀ * s * t + γ₀ * t ^ 2 := by
      have h23 : 2 * 3 = 6 := by norm_num
      have h33 : 3 * 3 = 9 := by norm_num
      have hbc := bilin_coupled_halves_of_nat Q 3 σ
      rw [hse]
      change bilin (coupled (neutralWindow Q 3 3) (neutralWindow Q (2 * 3) (2 * 3))
        (fun (i : Fin 3) (j : Fin (2 * 3)) => blockWeight Q (3 + i) (2 * 3 + j))) _ _ = _
      rw [hbc]
      have hstep := sum_neutralBlock_three_steps Q (R := 3) (by norm_num) (s - t) (s + 2 * t) s
      dsimp only [σ]
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      rw [hstep,
        neutralBlock_eq_four_of_lt_four_mul hQ le_rfl le_rfl (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ le_rfl (by norm_num) (by norm_num) (by norm_num),
        neutralBlock_eq_four_of_lt_four_mul hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
      dsimp only [α₀, c₀, γ₀]
      norm_num
      ring
    have hex_sub : 4.68 * t ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 6,
        (K i j - u i * v j) *
          ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
            (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2 := by
      have hS_sub : ∑ i : Fin 3, ∑ j ∈ S,
          (K i j - u i * v j) *
            ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
              (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2 ≤
          ∑ i : Fin 3, ∑ j : Fin 6,
            (K i j - u i * v j) *
              ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
                (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun j _ _ =>
            mul_nonneg (sub_nonneg.mpr (huv i j)) (sq_nonneg _)
      have hS_eq : ∑ i : Fin 3, ∑ j ∈ S,
          (K i j - u i * v j) *
            ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
              (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2 =
          t ^ 2 * ∑ i : Fin 3, ∑ j ∈ S, 9 * (K i j - u i * v j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj3 : (j : ℕ) < 3 := by
          simp only [S, Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl <;> decide
        simp only [z₁, z₂, Sum.elim_inl, Sum.elim_inr, if_pos hj3]
        ring
      refine le_trans ?_ hS_sub
      rw [hS_eq]
      nlinarith [sq_nonneg t]
    rw [hcoup]
    linarith
  · dsimp only [α₀]
    linarith [hb.1.2, hb.2.2.2.1.2, hb.2.2.2.2.2.2, hb.2.1.2, hb.2.2.1.2, hb.2.2.2.2.1.2]
  · have hα : α₀ < -24.23 := by
      dsimp only [α₀]
      linarith [hb.1.2, hb.2.2.2.1.2, hb.2.2.2.2.2.2, hb.2.1.2, hb.2.2.1.2, hb.2.2.2.2.1.2]
    have hγ : γ₀ - 4.68 < -1.55 := by
      dsimp only [γ₀]
      linarith [hb.1.2, hb.2.2.2.1.2, hb.2.1.1]
    have hc1 : -4.98 < c₀ := by
      dsimp only [c₀]
      linarith [hb.1.2, hb.2.2.2.1.1, hb.2.1.1, hb.2.2.1.2, hb.2.2.2.2.1.1]
    have hc2 : c₀ < 0 := by
      dsimp only [c₀]
      linarith [hb.1.1, hb.2.2.2.1.2, hb.2.1.2, hb.2.2.1.1, hb.2.2.2.2.1.2]
    have hcsq : c₀ ^ 2 < 4.98 ^ 2 := by nlinarith
    have hprod : (24.23 : ℝ) * 1.55 < α₀ * (γ₀ - 4.68) := by nlinarith
    linarith

/-! ### Two blocks (`R = 2`, `3 ≤ Q`): obstruction, equivalence, sub-unit witness, and rank-two gluing -/

private structure FineBounds27 : Prop where
  n22_gt : -0.6063 < neutralBlock 4 2 2
  n22_lt : neutralBlock 4 2 2 < -0.6062
  n23_gt : -0.7769 < neutralBlock 4 2 3
  n23_lt : neutralBlock 4 2 3 < -0.7768
  n33_gt : -0.2375 < neutralBlock 4 3 3
  n33_lt : neutralBlock 4 3 3 < -0.2374
  n24_gt : -0.6802 < neutralBlock 4 2 4
  n24_lt : neutralBlock 4 2 4 < -0.6795
  n25_gt : -0.5795 < neutralBlock 4 2 5
  n25_lt : neutralBlock 4 2 5 < -0.5788
  n26_gt : -0.5486 < neutralBlock 4 2 6
  n26_lt : neutralBlock 4 2 6 < -0.5479
  n27_gt : -0.5173 < neutralBlock 4 2 7
  n27_lt : neutralBlock 4 2 7 < -0.5166
  n34_gt : -0.7562 < neutralBlock 4 3 4
  n34_lt : neutralBlock 4 3 4 < -0.7555
  n35_gt : -0.3176 < neutralBlock 4 3 5
  n35_lt : neutralBlock 4 3 5 < -0.3169
  n36_gt : -0.5669 < neutralBlock 4 3 6
  n36_lt : neutralBlock 4 3 6 < -0.5662
  n37_gt : -0.5188 < neutralBlock 4 3 7
  n37_lt : neutralBlock 4 3 7 < -0.5181
  n44_gt : 0.0309 < neutralBlock 4 4 4
  n44_lt : neutralBlock 4 4 4 < 0.0316
  n45_gt : -0.7436 < neutralBlock 4 4 5
  n45_lt : neutralBlock 4 4 5 < -0.7429
  n46_gt : -0.3075 < neutralBlock 4 4 6
  n46_lt : neutralBlock 4 4 6 < -0.3068
  n47_gt : -0.2120 < neutralBlock 4 4 7
  n47_lt : neutralBlock 4 4 7 < -0.2113
  n55_gt : 0.2424 < neutralBlock 4 5 5
  n55_lt : neutralBlock 4 5 5 < 0.2431
  n56_gt : -0.7352 < neutralBlock 4 5 6
  n56_lt : neutralBlock 4 5 6 < -0.7345
  n57_gt : -0.3005 < neutralBlock 4 5 7
  n57_lt : neutralBlock 4 5 7 < -0.2998
  n66_gt : 0.4169 < neutralBlock 4 6 6
  n66_lt : neutralBlock 4 6 6 < 0.4176
  n67_gt : -0.7292 < neutralBlock 4 6 7
  n67_lt : neutralBlock 4 6 7 < -0.7285
  n77_gt : 0.5654 < neutralBlock 4 7 7
  n77_lt : neutralBlock 4 7 7 < 0.5661

private theorem fineBounds_row2 :
    (-0.6802 < neutralBlock 4 2 4 ∧ neutralBlock 4 2 4 < -0.6795) ∧
    (-0.5795 < neutralBlock 4 2 5 ∧ neutralBlock 4 2 5 < -0.5788) ∧
    (-0.5486 < neutralBlock 4 2 6 ∧ neutralBlock 4 2 6 < -0.5479) ∧
    (-0.5173 < neutralBlock 4 2 7 ∧ neutralBlock 4 2 7 < -0.5166) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry

private theorem fineBounds_row3 :
    (-0.7562 < neutralBlock 4 3 4 ∧ neutralBlock 4 3 4 < -0.7555) ∧
    (-0.3176 < neutralBlock 4 3 5 ∧ neutralBlock 4 3 5 < -0.3169) ∧
    (-0.5669 < neutralBlock 4 3 6 ∧ neutralBlock 4 3 6 < -0.5662) ∧
    (-0.5188 < neutralBlock 4 3 7 ∧ neutralBlock 4 3 7 < -0.5181) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry

private theorem fineBounds_row4 :
    (0.0309 < neutralBlock 4 4 4 ∧ neutralBlock 4 4 4 < 0.0316) ∧
    (-0.7436 < neutralBlock 4 4 5 ∧ neutralBlock 4 4 5 < -0.7429) ∧
    (-0.3075 < neutralBlock 4 4 6 ∧ neutralBlock 4 4 6 < -0.3068) ∧
    (-0.2120 < neutralBlock 4 4 7 ∧ neutralBlock 4 4 7 < -0.2113) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [neutralBlock_diag (by norm_num)]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry

private theorem fineBounds_rows567 :
    (0.2424 < neutralBlock 4 5 5 ∧ neutralBlock 4 5 5 < 0.2431) ∧
    (-0.7352 < neutralBlock 4 5 6 ∧ neutralBlock 4 5 6 < -0.7345) ∧
    (-0.3005 < neutralBlock 4 5 7 ∧ neutralBlock 4 5 7 < -0.2998) ∧
    (0.4169 < neutralBlock 4 6 6 ∧ neutralBlock 4 6 6 < 0.4176) ∧
    (-0.7292 < neutralBlock 4 6 7 ∧ neutralBlock 4 6 7 < -0.7285) ∧
    (0.5654 < neutralBlock 4 7 7 ∧ neutralBlock 4 7 7 < 0.5661) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [neutralBlock_diag (by norm_num)]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_diag (by norm_num)]; constructor <;> neutral_entry
  · rw [neutralBlock_of_lt (by norm_num), floorContact_four]; constructor <;> neutral_entry
  · rw [neutralBlock_diag (by norm_num)]; constructor <;> neutral_entry

private theorem fineBounds27 : FineBounds27 := by
  have hc := neutralBlock_four_coarse_bounds
  have r2 := fineBounds_row2
  have r3 := fineBounds_row3
  have r4 := fineBounds_row4
  have r5 := fineBounds_rows567
  exact ⟨hc.2.2.2.1.1, hc.2.2.2.1.2, hc.2.2.2.2.1.1, hc.2.2.2.2.1.2,
    hc.2.2.2.2.2.1, hc.2.2.2.2.2.2,
    r2.1.1, r2.1.2, r2.2.1.1, r2.2.1.2, r2.2.2.1.1, r2.2.2.1.2, r2.2.2.2.1, r2.2.2.2.2,
    r3.1.1, r3.1.2, r3.2.1.1, r3.2.1.2, r3.2.2.1.1, r3.2.2.1.2, r3.2.2.2.1, r3.2.2.2.2,
    r4.1.1, r4.1.2, r4.2.1.1, r4.2.1.2, r4.2.2.1.1, r4.2.2.1.2, r4.2.2.2.1, r4.2.2.2.2,
    r5.1.1, r5.1.2, r5.2.1.1, r5.2.1.2, r5.2.2.1.1, r5.2.2.1.2,
    r5.2.2.2.1.1, r5.2.2.2.1.2, r5.2.2.2.2.1.1, r5.2.2.2.2.1.2, r5.2.2.2.2.2.1, r5.2.2.2.2.2.2⟩

private theorem neutralWindow_two_eq_four {Q : ℕ} (hQ : 3 ≤ Q) :
    neutralWindow Q 2 2 = neutralWindow 4 2 2 := by
  ext i l
  exact neutralBlock_eq_four_of_lt_four_mul hQ (by omega) (by omega)
    (by have := i.2; have := l.2; omega) (by have := i.2; have := l.2; omega)

private theorem neutralWindow_four_eq_four {Q : ℕ} (hQ : 3 ≤ Q) :
    neutralWindow Q 4 4 = neutralWindow 4 4 4 := by
  ext j m
  exact neutralBlock_eq_four_of_lt_four_mul hQ (by omega) (by omega)
    (by have := j.2; have := m.2; omega) (by have := j.2; have := m.2; omega)

private theorem blockWeight_two_four_eq_four {Q : ℕ} (hQ : 3 ≤ Q) :
    (fun (i : Fin 2) (j : Fin 4) => blockWeight Q (2 + i) (4 + j)) =
      fun (i : Fin 2) (j : Fin 4) => blockWeight 4 (2 + i) (4 + j) := by
  funext i j
  exact blockWeight_eq_four_of_lt_four_mul hQ (by omega) (by have := i.2; omega)
    (by have := i.2; have := j.2; omega)

private theorem sum_fin_four (f : Fin 4 → ℝ) :
    ∑ j : Fin 4, f j = f 0 + f 1 + f 2 + f 3 := by
  have h : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private theorem sum_fin_two_sum_fin_four (f : Fin 2 ⊕ Fin 4 → ℝ) :
    ∑ p : Fin 2 ⊕ Fin 4, f p =
      f (Sum.inl 0) + f (Sum.inl 1) + f (Sum.inr 0) + f (Sum.inr 1) +
        f (Sum.inr 2) + f (Sum.inr 3) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, sum_fin_four]
  ring

private def idx24 : Fin 2 ⊕ Fin 4 → ℕ
  | Sum.inl i => 2 + i
  | Sum.inr j => 4 + j

private theorem idx24_inl0 : idx24 (Sum.inl 0) = 2 := rfl
private theorem idx24_inl1 : idx24 (Sum.inl 1) = 3 := rfl
private theorem idx24_inr0 : idx24 (Sum.inr 0) = 4 := rfl
private theorem idx24_inr1 : idx24 (Sum.inr 1) = 5 := rfl
private theorem idx24_inr2 : idx24 (Sum.inr 2) = 6 := rfl
private theorem idx24_inr3 : idx24 (Sum.inr 3) = 7 := rfl

private abbrev c4Matrix : Matrix (Fin 2 ⊕ Fin 4) (Fin 2 ⊕ Fin 4) ℝ :=
  coupled (neutralWindow 4 2 2) (neutralWindow 4 4 4)
    (fun (i : Fin 2) (j : Fin 4) => blockWeight 4 (2 + i) (4 + j))

private theorem coupled_four_two_four_apply (p q : Fin 2 ⊕ Fin 4) :
    c4Matrix p q = neutralBlock 4 (idx24 p) (idx24 q) := by
  cases p with
  | inl i =>
    cases q with
    | inl l => rfl
    | inr j => simp [c4Matrix, coupled, idx24, blockWeight]
  | inr j =>
    cases q with
    | inl i => simp [c4Matrix, coupled, idx24, blockWeight, neutralBlock_comm 4 (4 + j) (2 + i)]
    | inr m => rfl

private def vec24 (a₀ a₁ b₀ b₁ b₂ b₃ : ℝ) : Fin 2 ⊕ Fin 4 → ℝ
  | Sum.inl i => if (i : ℕ) = 0 then a₀ else a₁
  | Sum.inr j =>
    if (j : ℕ) = 0 then b₀ else if (j : ℕ) = 1 then b₁ else if (j : ℕ) = 2 then b₂ else b₃

private theorem vec24_inl0 (a₀ a₁ b₀ b₁ b₂ b₃ : ℝ) :
    vec24 a₀ a₁ b₀ b₁ b₂ b₃ (Sum.inl 0) = a₀ := by simp [vec24]
private theorem vec24_inl1 (a₀ a₁ b₀ b₁ b₂ b₃ : ℝ) :
    vec24 a₀ a₁ b₀ b₁ b₂ b₃ (Sum.inl 1) = a₁ := by simp [vec24]
private theorem vec24_inr0 (a₀ a₁ b₀ b₁ b₂ b₃ : ℝ) :
    vec24 a₀ a₁ b₀ b₁ b₂ b₃ (Sum.inr 0) = b₀ := by simp [vec24]
private theorem vec24_inr1 (a₀ a₁ b₀ b₁ b₂ b₃ : ℝ) :
    vec24 a₀ a₁ b₀ b₁ b₂ b₃ (Sum.inr 1) = b₁ := by simp [vec24]
private theorem vec24_inr2 (a₀ a₁ b₀ b₁ b₂ b₃ : ℝ) :
    vec24 a₀ a₁ b₀ b₁ b₂ b₃ (Sum.inr 2) = b₂ := by simp [vec24]
private theorem vec24_inr3 (a₀ a₁ b₀ b₁ b₂ b₃ : ℝ) :
    vec24 a₀ a₁ b₀ b₁ b₂ b₃ (Sum.inr 3) = b₃ := by simp [vec24]

private theorem bilin_symm {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : ∀ p q, M p q = M q p) (x y : ι → ℝ) : bilin M x y = bilin M y x := by
  simp only [bilin]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hM q p]; ring

private theorem bilin_add_left {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    bilin M (fun p => x p + y p) z = bilin M x z + bilin M y z := by
  simp only [bilin, add_mul, Finset.sum_add_distrib]

private theorem bilin_add_right {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    bilin M x (fun p => y p + z p) = bilin M x y + bilin M x z := by
  simp only [bilin, mul_add, add_mul, Finset.sum_add_distrib]

private theorem bilin_smul_left {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (s : ℝ) (x y : ι → ℝ) :
    bilin M (fun p => s * x p) y = s * bilin M x y := by
  simp only [bilin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem bilin_smul_right {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (s : ℝ) (x y : ι → ℝ) :
    bilin M x (fun p => s * y p) = s * bilin M x y := by
  simp only [bilin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem bilin_comb_symm {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : ∀ p q, M p q = M q p) (z₁ z₂ : ι → ℝ) (s t : ℝ) :
    bilin M (fun p => s * z₁ p + t * z₂ p) (fun p => s * z₁ p + t * z₂ p) =
      bilin M z₁ z₁ * s ^ 2 + 2 * bilin M z₁ z₂ * s * t + bilin M z₂ z₂ * t ^ 2 := by
  simp only [bilin_add_left, bilin_add_right, bilin_smul_left, bilin_smul_right,
    bilin_symm hM z₂ z₁]
  ring

private theorem bilin_comb3_symm {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : ∀ p q, M p q = M q p) (e₀ e₁ e₂ : ι → ℝ) (t₀ t₁ t₂ : ℝ) :
    bilin M (fun p => t₀ * e₀ p + t₁ * e₁ p + t₂ * e₂ p)
      (fun p => t₀ * e₀ p + t₁ * e₁ p + t₂ * e₂ p) =
      bilin M e₀ e₀ * t₀ ^ 2 + bilin M e₁ e₁ * t₁ ^ 2 + bilin M e₂ e₂ * t₂ ^ 2 +
        2 * bilin M e₀ e₁ * t₀ * t₁ + 2 * bilin M e₀ e₂ * t₀ * t₂ +
        2 * bilin M e₁ e₂ * t₁ * t₂ := by
  simp only [bilin_add_left, bilin_add_right, bilin_smul_left, bilin_smul_right,
    bilin_symm hM e₁ e₀, bilin_symm hM e₂ e₀, bilin_symm hM e₂ e₁]
  ring

private theorem glued_lowered_neg {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₂ ι₂ ℝ)
    (K : ι₁ → ι₂ → ℝ) (u : ι₁ → ℝ) (v : ι₂ → ℝ) :
    glued (A - diagonal (excessLeft K (-u) (-v))) (B - diagonal (excessRight K (-u) (-v)))
      (-u) (-v) =
      glued (A - diagonal (excessLeft K u v)) (B - diagonal (excessRight K u v)) u v := by
  have eL : excessLeft K (-u) (-v) = excessLeft K u v :=
    funext fun i => Finset.sum_congr rfl fun j _ => by simp
  have eR : excessRight K (-u) (-v) = excessRight K u v :=
    funext fun j => Finset.sum_congr rfl fun i _ => by simp
  rw [eL, eR]
  ext (i | j) (l | m) <;> simp [glued]

private theorem c4_plane_left_bounds :
    bilin c4Matrix (vec24 1 1 1 1 1 1) (vec24 1 1 1 1 1 1) < -16.14 ∧
    (-2.60 < bilin c4Matrix (vec24 1 1 1 1 1 1) (vec24 (-2) 0 1 2 1 0) ∧
      bilin c4Matrix (vec24 1 1 1 1 1 1) (vec24 (-2) 0 1 2 1 0) < -2.57) ∧
    bilin c4Matrix (vec24 (-2) 0 1 2 1 0) (vec24 (-2) 0 1 2 1 0) < 2.03 := by
  have hb := fineBounds27
  refine ⟨?_, ?_, ?_⟩
  · rw [bilin]
    simp only [sum_fin_two_sum_fin_four, coupled_four_two_four_apply,
      idx24_inl0, idx24_inl1, idx24_inr0, idx24_inr1, idx24_inr2, idx24_inr3,
      vec24_inl0, vec24_inl1, vec24_inr0, vec24_inr1, vec24_inr2, vec24_inr3,
      neutralBlock_comm 4 3 2, neutralBlock_comm 4 4 2, neutralBlock_comm 4 4 3,
      neutralBlock_comm 4 5 2, neutralBlock_comm 4 5 3, neutralBlock_comm 4 5 4,
      neutralBlock_comm 4 6 2, neutralBlock_comm 4 6 3, neutralBlock_comm 4 6 4,
      neutralBlock_comm 4 6 5, neutralBlock_comm 4 7 2, neutralBlock_comm 4 7 3,
      neutralBlock_comm 4 7 4, neutralBlock_comm 4 7 5, neutralBlock_comm 4 7 6]
    linarith [hb.n22_lt, hb.n23_lt, hb.n33_lt, hb.n24_lt, hb.n25_lt, hb.n26_lt, hb.n27_lt,
      hb.n34_lt, hb.n35_lt, hb.n36_lt, hb.n37_lt, hb.n44_lt, hb.n45_lt, hb.n46_lt, hb.n47_lt,
      hb.n55_lt, hb.n56_lt, hb.n57_lt, hb.n66_lt, hb.n67_lt, hb.n77_lt]
  · rw [bilin]
    simp only [sum_fin_two_sum_fin_four, coupled_four_two_four_apply,
      idx24_inl0, idx24_inl1, idx24_inr0, idx24_inr1, idx24_inr2, idx24_inr3,
      vec24_inl0, vec24_inl1, vec24_inr0, vec24_inr1, vec24_inr2, vec24_inr3,
      neutralBlock_comm 4 3 2, neutralBlock_comm 4 4 2, neutralBlock_comm 4 4 3,
      neutralBlock_comm 4 5 2, neutralBlock_comm 4 5 3, neutralBlock_comm 4 5 4,
      neutralBlock_comm 4 6 2, neutralBlock_comm 4 6 3, neutralBlock_comm 4 6 4,
      neutralBlock_comm 4 6 5, neutralBlock_comm 4 7 2, neutralBlock_comm 4 7 3,
      neutralBlock_comm 4 7 4, neutralBlock_comm 4 7 5, neutralBlock_comm 4 7 6]
    constructor <;>
      linarith [hb.n22_gt, hb.n22_lt, hb.n23_gt, hb.n23_lt, hb.n33_gt, hb.n33_lt,
        hb.n24_gt, hb.n24_lt, hb.n25_gt, hb.n25_lt, hb.n26_gt, hb.n26_lt, hb.n27_gt, hb.n27_lt,
        hb.n34_gt, hb.n34_lt, hb.n35_gt, hb.n35_lt, hb.n36_gt, hb.n36_lt, hb.n37_gt, hb.n37_lt,
        hb.n44_gt, hb.n44_lt, hb.n45_gt, hb.n45_lt, hb.n46_gt, hb.n46_lt, hb.n47_gt, hb.n47_lt,
        hb.n55_gt, hb.n55_lt, hb.n56_gt, hb.n56_lt, hb.n57_gt, hb.n57_lt, hb.n66_gt, hb.n66_lt,
        hb.n67_gt, hb.n67_lt, hb.n77_gt, hb.n77_lt]
  · rw [bilin]
    simp only [sum_fin_two_sum_fin_four, coupled_four_two_four_apply,
      idx24_inl0, idx24_inl1, idx24_inr0, idx24_inr1, idx24_inr2, idx24_inr3,
      vec24_inl0, vec24_inl1, vec24_inr0, vec24_inr1, vec24_inr2, vec24_inr3,
      neutralBlock_comm 4 3 2, neutralBlock_comm 4 4 2, neutralBlock_comm 4 4 3,
      neutralBlock_comm 4 5 2, neutralBlock_comm 4 5 3, neutralBlock_comm 4 5 4,
      neutralBlock_comm 4 6 2, neutralBlock_comm 4 6 3, neutralBlock_comm 4 6 4,
      neutralBlock_comm 4 6 5, neutralBlock_comm 4 7 2, neutralBlock_comm 4 7 3,
      neutralBlock_comm 4 7 4, neutralBlock_comm 4 7 5, neutralBlock_comm 4 7 6]
    linarith [hb.n22_gt, hb.n22_lt, hb.n24_gt, hb.n24_lt, hb.n25_gt, hb.n25_lt,
      hb.n26_gt, hb.n26_lt, hb.n44_lt, hb.n45_lt, hb.n46_lt, hb.n55_lt, hb.n56_lt, hb.n66_lt]

private theorem c4_plane_right_bounds :
    (1.21 < bilin c4Matrix (vec24 1 1 1 1 1 1) (vec24 0 2 (-1) (-1) (-1) 0) ∧
      bilin c4Matrix (vec24 1 1 1 1 1 1) (vec24 0 2 (-1) (-1) (-1) 0) < 1.24) ∧
    bilin c4Matrix (vec24 0 2 (-1) (-1) (-1) 0) (vec24 0 2 (-1) (-1) (-1) 0) < 2.74 := by
  have hb := fineBounds27
  refine ⟨?_, ?_⟩
  · rw [bilin]
    simp only [sum_fin_two_sum_fin_four, coupled_four_two_four_apply,
      idx24_inl0, idx24_inl1, idx24_inr0, idx24_inr1, idx24_inr2, idx24_inr3,
      vec24_inl0, vec24_inl1, vec24_inr0, vec24_inr1, vec24_inr2, vec24_inr3,
      neutralBlock_comm 4 3 2, neutralBlock_comm 4 4 2, neutralBlock_comm 4 4 3,
      neutralBlock_comm 4 5 2, neutralBlock_comm 4 5 3, neutralBlock_comm 4 5 4,
      neutralBlock_comm 4 6 2, neutralBlock_comm 4 6 3, neutralBlock_comm 4 6 4,
      neutralBlock_comm 4 6 5, neutralBlock_comm 4 7 2, neutralBlock_comm 4 7 3,
      neutralBlock_comm 4 7 4, neutralBlock_comm 4 7 5, neutralBlock_comm 4 7 6]
    constructor <;>
      linarith [hb.n22_gt, hb.n22_lt, hb.n23_gt, hb.n23_lt, hb.n33_gt, hb.n33_lt,
        hb.n24_gt, hb.n24_lt, hb.n25_gt, hb.n25_lt, hb.n26_gt, hb.n26_lt, hb.n27_gt, hb.n27_lt,
        hb.n34_gt, hb.n34_lt, hb.n35_gt, hb.n35_lt, hb.n36_gt, hb.n36_lt, hb.n37_gt, hb.n37_lt,
        hb.n44_gt, hb.n44_lt, hb.n45_gt, hb.n45_lt, hb.n46_gt, hb.n46_lt, hb.n47_gt, hb.n47_lt,
        hb.n55_gt, hb.n55_lt, hb.n56_gt, hb.n56_lt, hb.n57_gt, hb.n57_lt, hb.n66_gt, hb.n66_lt,
        hb.n67_gt, hb.n67_lt, hb.n77_gt, hb.n77_lt]
  · rw [bilin]
    simp only [sum_fin_two_sum_fin_four, coupled_four_two_four_apply,
      idx24_inl0, idx24_inl1, idx24_inr0, idx24_inr1, idx24_inr2, idx24_inr3,
      vec24_inl0, vec24_inl1, vec24_inr0, vec24_inr1, vec24_inr2, vec24_inr3,
      neutralBlock_comm 4 3 2, neutralBlock_comm 4 4 2, neutralBlock_comm 4 4 3,
      neutralBlock_comm 4 5 2, neutralBlock_comm 4 5 3, neutralBlock_comm 4 5 4,
      neutralBlock_comm 4 6 2, neutralBlock_comm 4 6 3, neutralBlock_comm 4 6 4,
      neutralBlock_comm 4 6 5, neutralBlock_comm 4 7 2, neutralBlock_comm 4 7 3,
      neutralBlock_comm 4 7 4, neutralBlock_comm 4 7 5, neutralBlock_comm 4 7 6]
    linarith [hb.n33_lt, hb.n34_gt, hb.n34_lt, hb.n35_gt, hb.n35_lt, hb.n36_gt, hb.n36_lt,
      hb.n44_lt, hb.n45_lt, hb.n46_lt, hb.n55_lt, hb.n56_lt, hb.n66_lt]

private theorem two_le_hermNegIndex_glued_lowered_two_pos {u : Fin 2 → ℝ} {v : Fin 4 → ℝ}
    (hu0 : 0 < u 0) (hu1 : 0 < u 1)
    (huv : ∀ i j, u i * v j ≤ blockWeight 4 (2 + i) (4 + j)) :
    2 ≤ hermNegIndex ((glued
      (neutralWindow 4 2 2 -
        diagonal (excessLeft
          (fun (i : Fin 2) (j : Fin 4) => blockWeight 4 (2 + i) (4 + j)) u v))
      (neutralWindow 4 4 4 -
        diagonal (excessRight
          (fun (i : Fin 2) (j : Fin 4) => blockWeight 4 (2 + i) (4 + j)) u v))
      u v).map (↑) : Matrix (Fin 2 ⊕ Fin 4) (Fin 2 ⊕ Fin 4) ℂ) := by
  set K4 : Fin 2 → Fin 4 → ℝ := fun i j => blockWeight 4 (2 + i) (4 + j)
  have hC4_symm : ∀ p q, c4Matrix p q = c4Matrix q p := fun p q => by
    rw [coupled_four_two_four_apply, coupled_four_two_four_apply, neutralBlock_comm]
  have hb := fineBounds27
  let z₁ : Fin 2 ⊕ Fin 4 → ℝ := vec24 1 1 1 1 1 1
  have hz₁₁ : bilin c4Matrix z₁ z₁ < -16.14 := c4_plane_left_bounds.1
  rcases le_total (4 * u 0) (5 * u 1) with hrat | hrat
  · -- Subcase `4 u_0 ≤ 5 u_1`: keep `(i = 0, j = 1)` on `z₂ = [-2, 0 | 1, 2, 1, 0]`
    let z₂ : Fin 2 ⊕ Fin 4 → ℝ := vec24 (-2) 0 1 2 1 0
    have hz₁₂ : -2.60 < bilin c4Matrix z₁ z₂ ∧ bilin c4Matrix z₁ z₂ < -2.57 :=
      c4_plane_left_bounds.2.1
    have hz₂₂ : bilin c4Matrix z₂ z₂ < 2.03 := c4_plane_left_bounds.2.2
    have hex01 : (0.1818 : ℝ) ≤ K4 0 1 - u 0 * v 1 := by
      have hK01 : (0.5788 : ℝ) < K4 0 1 := by
        show (0.5788 : ℝ) < -neutralBlock 4 2 5
        linarith [hb.n25_lt]
      have hK11 : K4 1 1 < 0.3176 := by
        show -neutralBlock 4 3 5 < (0.3176 : ℝ)
        linarith [hb.n35_gt]
      have huv11 := huv 1 1
      rcases le_or_gt (v 1) 0 with hv1 | hv1
      · have hnp : u 0 * v 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu0.le hv1
        linarith
      · have hle : 4 * (u 0 * v 1) ≤ 5 * (u 1 * v 1) := by nlinarith
        linarith
    refine two_le_hermNegIndex_of_binary_plane _ z₁ z₂
      (α := bilin c4Matrix z₁ z₁) (γ := bilin c4Matrix z₂ z₂ - 2.90)
      (c := bilin c4Matrix z₁ z₂) ?_ ?_ ?_
    · intro s t
      rw [bilin_glued_lowered_eq_coupled_sub,
        show coupled (neutralWindow 4 2 2) (neutralWindow 4 4 4) K4 = c4Matrix from rfl,
        bilin_comb_symm hC4_symm]
      have hterm01 : 2.90 * t ^ 2 ≤
          ∑ i : Fin 2, ∑ j : Fin 4, (K4 i j - u i * v j) *
            ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
              (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2 := by
        let f : Fin 2 → Fin 4 → ℝ := fun i j => (K4 i j - u i * v j) *
          ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
            (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2
        have hf0 : ∀ i j, 0 ≤ f i j := fun i j =>
          mul_nonneg (sub_nonneg.mpr (huv i j)) (sq_nonneg _)
        have h1 : f 0 1 ≤ ∑ i : Fin 2, ∑ j : Fin 4, f i j :=
          (Finset.single_le_sum (f := f 0) (fun j _ => hf0 0 j) (Finset.mem_univ 1)).trans
            (Finset.single_le_sum (f := fun i : Fin 2 => ∑ j : Fin 4, f i j)
              (fun i _ => Finset.sum_nonneg fun j _ => hf0 i j) (Finset.mem_univ 0))
        dsimp only [f] at h1
        have hsq : ((s * z₁ (Sum.inl 0) + t * z₂ (Sum.inl 0)) -
            (s * z₁ (Sum.inr 1) + t * z₂ (Sum.inr 1))) ^ 2 = 16 * t ^ 2 := by
          simp only [z₁, z₂, vec24_inl0, vec24_inr1]
          ring
        rw [hsq] at h1
        nlinarith only [hex01, h1, sq_nonneg t]
      linarith
    · linarith
    · have hγ : bilin c4Matrix z₂ z₂ - 2.90 < -0.87 := by linarith
      have hcsq : (bilin c4Matrix z₁ z₂) ^ 2 < 2.60 ^ 2 := by nlinarith [hz₁₂.1, hz₁₂.2]
      have hprod : (16.14 : ℝ) * 0.87 < bilin c4Matrix z₁ z₁ * (bilin c4Matrix z₂ z₂ - 2.90) := by
        nlinarith
      linarith
  · -- Subcase `5 u_1 ≤ 4 u_0`: keep `(1, 0)` and `(1, 2)` on `z₂ = [0, 2 | -1, -1, -1, 0]`
    let z₂ : Fin 2 ⊕ Fin 4 → ℝ := vec24 0 2 (-1) (-1) (-1) 0
    have hz₁₂ : 1.21 < bilin c4Matrix z₁ z₂ ∧ bilin c4Matrix z₁ z₂ < 1.24 :=
      c4_plane_right_bounds.1
    have hz₂₂ : bilin c4Matrix z₂ z₂ < 2.74 := c4_plane_right_bounds.2
    have hex10 : (0.21 : ℝ) ≤ K4 1 0 - u 1 * v 0 := by
      have hK10 : (0.7555 : ℝ) < K4 1 0 := by
        show (0.7555 : ℝ) < -neutralBlock 4 3 4
        linarith [hb.n34_lt]
      have hK00 : K4 0 0 < 0.6802 := by
        show -neutralBlock 4 2 4 < (0.6802 : ℝ)
        linarith [hb.n24_gt]
      have huv00 := huv 0 0
      rcases le_or_gt (v 0) 0 with hv0 | hv0
      · have hnp : u 1 * v 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu1.le hv0
        linarith
      · have hle : 5 * (u 1 * v 0) ≤ 4 * (u 0 * v 0) := by nlinarith
        linarith
    have hex12 : (0.127 : ℝ) ≤ K4 1 2 - u 1 * v 2 := by
      have hK12 : (0.5662 : ℝ) < K4 1 2 := by
        show (0.5662 : ℝ) < -neutralBlock 4 3 6
        linarith [hb.n36_lt]
      have hK02 : K4 0 2 < 0.5486 := by
        show -neutralBlock 4 2 6 < (0.5486 : ℝ)
        linarith [hb.n26_gt]
      have huv02 := huv 0 2
      rcases le_or_gt (v 2) 0 with hv2 | hv2
      · have hnp : u 1 * v 2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu1.le hv2
        linarith
      · have hle : 5 * (u 1 * v 2) ≤ 4 * (u 0 * v 2) := by nlinarith
        linarith
    refine two_le_hermNegIndex_of_binary_plane _ z₁ z₂
      (α := bilin c4Matrix z₁ z₁) (γ := bilin c4Matrix z₂ z₂ - 3.03)
      (c := bilin c4Matrix z₁ z₂) ?_ ?_ ?_
    · intro s t
      rw [bilin_glued_lowered_eq_coupled_sub,
        show coupled (neutralWindow 4 2 2) (neutralWindow 4 4 4) K4 = c4Matrix from rfl,
        bilin_comb_symm hC4_symm]
      have hterms : 3.03 * t ^ 2 ≤
          ∑ i : Fin 2, ∑ j : Fin 4, (K4 i j - u i * v j) *
            ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
              (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2 := by
        let f : Fin 2 → Fin 4 → ℝ := fun i j => (K4 i j - u i * v j) *
          ((s * z₁ (Sum.inl i) + t * z₂ (Sum.inl i)) -
            (s * z₁ (Sum.inr j) + t * z₂ (Sum.inr j))) ^ 2
        have hrow1 : ∑ j : Fin 4, f 1 j ≤ ∑ i : Fin 2, ∑ j : Fin 4, f i j :=
          Finset.single_le_sum (f := fun i : Fin 2 => ∑ j : Fin 4, f i j)
            (fun i _ => Finset.sum_nonneg fun j _ =>
              mul_nonneg (sub_nonneg.mpr (huv i j)) (sq_nonneg _))
            (Finset.mem_univ 1)
        dsimp only [f] at hrow1
        rw [sum_fin_four] at hrow1
        have hnn1 : 0 ≤ (K4 1 1 - u 1 * v 1) *
            ((s * z₁ (Sum.inl 1) + t * z₂ (Sum.inl 1)) -
              (s * z₁ (Sum.inr 1) + t * z₂ (Sum.inr 1))) ^ 2 :=
          mul_nonneg (sub_nonneg.mpr (huv 1 1)) (sq_nonneg _)
        have hnn3 : 0 ≤ (K4 1 3 - u 1 * v 3) *
            ((s * z₁ (Sum.inl 1) + t * z₂ (Sum.inl 1)) -
              (s * z₁ (Sum.inr 3) + t * z₂ (Sum.inr 3))) ^ 2 :=
          mul_nonneg (sub_nonneg.mpr (huv 1 3)) (sq_nonneg _)
        have hsq0 : ((s * z₁ (Sum.inl 1) + t * z₂ (Sum.inl 1)) -
            (s * z₁ (Sum.inr 0) + t * z₂ (Sum.inr 0))) ^ 2 = 9 * t ^ 2 := by
          simp only [z₁, z₂, vec24_inl1, vec24_inr0]; ring
        have hsq2 : ((s * z₁ (Sum.inl 1) + t * z₂ (Sum.inl 1)) -
            (s * z₁ (Sum.inr 2) + t * z₂ (Sum.inr 2))) ^ 2 = 9 * t ^ 2 := by
          simp only [z₁, z₂, vec24_inl1, vec24_inr2]; ring
        rw [hsq0, hsq2] at hrow1
        have hp : 3.03 * t ^ 2 ≤ (K4 1 0 - u 1 * v 0) * (9 * t ^ 2) +
            (K4 1 2 - u 1 * v 2) * (9 * t ^ 2) := by nlinarith [sq_nonneg t]
        linarith
      linarith
    · linarith
    · have hγ : bilin c4Matrix z₂ z₂ - 3.03 < -0.29 := by linarith
      have hcsq : (bilin c4Matrix z₁ z₂) ^ 2 < 1.24 ^ 2 := by nlinarith [hz₁₂.1, hz₁₂.2]
      have hprod : (16.14 : ℝ) * 0.29 < bilin c4Matrix z₁ z₁ * (bilin c4Matrix z₂ z₂ - 3.03) := by
        nlinarith
      linarith

/-- For `R = 2` and `3 ≤ Q`, the lowered glued form has at least two negative squares for every
admissible charge pair. -/
theorem two_le_hermNegIndex_glued_lowered_two {Q : ℕ} (hQ : 3 ≤ Q)
    {u : Fin 2 → ℝ} {v : Fin 4 → ℝ}
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (2 + i) (4 + j)) :
    2 ≤ hermNegIndex ((glued
      (neutralWindow Q 2 2 -
        diagonal (excessLeft
          (fun (i : Fin 2) (j : Fin 4) => blockWeight Q (2 + i) (4 + j)) u v))
      (neutralWindow Q 4 4 -
        diagonal (excessRight
          (fun (i : Fin 2) (j : Fin 4) => blockWeight Q (2 + i) (4 + j)) u v))
      u v).map (↑) : Matrix (Fin 2 ⊕ Fin 4) (Fin 2 ⊕ Fin 4) ℂ) := by
  rw [neutralWindow_two_eq_four hQ, neutralWindow_four_eq_four hQ, blockWeight_two_four_eq_four hQ]
  have huv4 : ∀ i j, u i * v j ≤ blockWeight 4 (2 + i) (4 + j) := fun i j => by
    rw [← blockWeight_eq_four_of_lt_four_mul hQ (by omega) (by have := i.2; omega)
      (by have := i.2; have := j.2; omega)]
    exact huv i j
  rcases le_or_gt (u 0 * u 1) 0 with hsign | hsign
  · -- Opposite-sign or zero row charge: constant-on-halves plane
    set K4 : Fin 2 → Fin 4 → ℝ := fun i j => blockWeight 4 (2 + i) (4 + j)
    set SK : ℝ := ∑ i : Fin 2, ∑ j : Fin 4, K4 i j
    have hSK : SK = 2 * (blockWeight 4 1 2 + blockWeight 4 1 3) := by
      have h := sum_blockWeight_halves_fin (Q := 4) (R := 2) (by norm_num) (by norm_num)
      rw [Nat.cast_ofNat] at h
      exact h
    set P : ℝ := (∑ i : Fin 2, u i) * (∑ j : Fin 4, v j)
    have hP_le : P ≤ 2.33 := by
      have hf := fineBounds27
      rcases le_or_gt P 0 with hP0 | hP0
      · linarith
      · set u' : Fin 2 → ℝ := if 0 < u 0 + u 1 then u else -u
        set v' : Fin 4 → ℝ := if 0 < u 0 + u 1 then v else -v
        have hP_eq : (u' 0 + u' 1) * (∑ j : Fin 4, v' j) = P := by
          dsimp only [P]
          rw [Fin.sum_univ_two]
          by_cases hs : 0 < u 0 + u 1
          · simp [u', v', if_pos hs]
          · simp [u', v', if_neg hs, Finset.sum_neg_distrib]
            ring
        have hu'_sum : 0 < u' 0 + u' 1 := by
          by_cases hs : 0 < u 0 + u 1
          · simpa [u', if_pos hs] using hs
          · simp only [u', if_neg hs, Pi.neg_apply]
            have hne : u 0 + u 1 ≠ 0 := fun h0 => by
              dsimp only [P] at hP0
              rw [Fin.sum_univ_two, h0, zero_mul] at hP0
              exact lt_irrefl 0 hP0
            linarith [lt_of_le_of_ne (not_lt.mp hs) hne]
        have hu'_sign : u' 0 * u' 1 ≤ 0 := by
          by_cases hs : 0 < u 0 + u 1 <;> simpa [u', hs] using hsign
        have huv' : ∀ i j, u' i * v' j ≤ K4 i j := fun i j => by
          by_cases hs : 0 < u 0 + u 1 <;> simpa [u', v', hs] using huv4 i j
        have hK4_nn : ∀ i j, 0 ≤ K4 i j := fun i j => (blockWeight_pos (by omega) 4).le
        rw [← hP_eq, Finset.mul_sum, sum_fin_four]
        rcases le_or_gt (u' 1) 0 with hu1_le | hu1_gt
        · have hterm : ∀ j : Fin 4, (u' 0 + u' 1) * v' j ≤ K4 0 j := fun j => by
            rcases le_or_gt (v' j) 0 with hvj | hvj
            · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hu'_sum.le hvj) (hK4_nn 0 j)
            · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hvj.le) (huv' 0 j)
          have t0 := hterm 0; have t1 := hterm 1; have t2 := hterm 2; have t3 := hterm 3
          have k0 : K4 0 0 < 0.6802 := by show -neutralBlock 4 2 4 < 0.6802; linarith [hf.n24_gt]
          have k1 : K4 0 1 < 0.5795 := by show -neutralBlock 4 2 5 < 0.5795; linarith [hf.n25_gt]
          have k2 : K4 0 2 < 0.5486 := by show -neutralBlock 4 2 6 < 0.5486; linarith [hf.n26_gt]
          have k3 : K4 0 3 < 0.5173 := by show -neutralBlock 4 2 7 < 0.5173; linarith [hf.n27_gt]
          linarith
        · have hu0_le : u' 0 ≤ 0 := by nlinarith
          have hterm : ∀ j : Fin 4, (u' 0 + u' 1) * v' j ≤ K4 1 j := fun j => by
            rcases le_or_gt (v' j) 0 with hvj | hvj
            · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hu'_sum.le hvj) (hK4_nn 1 j)
            · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hvj.le) (huv' 1 j)
          have t0 := hterm 0; have t1 := hterm 1; have t2 := hterm 2; have t3 := hterm 3
          have k0 : K4 1 0 < 0.7562 := by show -neutralBlock 4 3 4 < 0.7562; linarith [hf.n34_gt]
          have k1 : K4 1 1 < 0.3176 := by show -neutralBlock 4 3 5 < 0.3176; linarith [hf.n35_gt]
          have k2 : K4 1 2 < 0.5669 := by show -neutralBlock 4 3 6 < 0.5669; linarith [hf.n36_gt]
          have k3 : K4 1 3 < 0.5188 := by show -neutralBlock 4 3 7 < 0.5188; linarith [hf.n37_gt]
          linarith
    let w₁ : Fin 2 ⊕ Fin 4 → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)
    let w₂ : Fin 2 ⊕ Fin 4 → ℝ := Sum.elim (fun _ => 0) (fun _ => 1)
    set A₀ : ℝ := 2 * neutralBlock 4 1 1 - SK
    set B₀ : ℝ := 2 * (neutralBlock 4 2 2 + neutralBlock 4 3 3 + 2 * neutralBlock 4 2 3) - SK
    refine two_le_hermNegIndex_of_binary_plane _ w₁ w₂
      (α := A₀ + P) (γ := B₀ + P) (c := -P) ?_ ?_ ?_
    · intro s t
      have hw_eq : (fun m : Fin 2 ⊕ Fin 4 => s * w₁ m + t * w₂ m) =
          Sum.elim (fun _ => s) (fun _ => t) := by
        funext x; rcases x with i | j <;> simp [w₁, w₂]
      rw [hw_eq, bilin_glued_lowered_eq_coupled_sub]
      let σ : ℕ → ℝ := fun p => if p < 2 then s else if p < 4 then t else t
      have hse : (Sum.elim (fun _ : Fin 2 => s) (fun _ : Fin 4 => t)) =
          Sum.elim (fun i : Fin 2 => σ i) (fun j : Fin 4 => σ (2 + j)) := by
        funext x; rcases x with i | j
        · dsimp only [Sum.elim_inl, σ]
          rw [if_pos i.2]
        · have h1 : ¬2 + (j : ℕ) < 2 := by omega
          dsimp only [Sum.elim_inr, σ]
          rw [if_neg h1]
          split_ifs <;> rfl
      have hcoup : bilin (coupled (neutralWindow 4 2 2) (neutralWindow 4 4 4) K4)
          (Sum.elim (fun i : Fin 2 => σ i) (fun j : Fin 4 => σ (2 + j)))
          (Sum.elim (fun i : Fin 2 => σ i) (fun j : Fin 4 => σ (2 + j))) =
          2 * (s ^ 2 * neutralBlock 4 1 1 +
            t ^ 2 * (neutralBlock 4 2 2 + neutralBlock 4 3 3 + 2 * neutralBlock 4 2 3) +
            2 * s * t * (neutralBlock 4 1 2 + neutralBlock 4 1 3)) := by
        have hbc := bilin_coupled_halves_of_nat 4 2 σ
        have hstep := sum_neutralBlock_three_steps 4 (R := 2) (by norm_num) s t t
        change bilin (coupled (neutralWindow 4 2 2) (neutralWindow 4 (2 * 2) (2 * 2))
          (fun (i : Fin 2) (j : Fin (2 * 2)) => blockWeight 4 (2 + i) (2 * 2 + j))) _ _ = _
        rw [hbc]
        dsimp only [σ]
        rw [show (4 : ℕ) = 2 * 2 by norm_num, hstep]
        norm_num
        ring
      have hex_sum : ∑ i : Fin 2, ∑ j : Fin 4,
          (K4 i j - u i * v j) *
            (Sum.elim (fun i : Fin 2 => σ i) (fun j : Fin 4 => σ (2 + j)) (Sum.inl i) -
              Sum.elim (fun i : Fin 2 => σ i) (fun j : Fin 4 => σ (2 + j)) (Sum.inr j)) ^ 2 =
          (SK - P) * (s - t) ^ 2 := by
        have hdiff : ∀ (i : Fin 2) (j : Fin 4),
            (Sum.elim (fun i : Fin 2 => σ i) (fun j : Fin 4 => σ (2 + j)) (Sum.inl i) -
              Sum.elim (fun i : Fin 2 => σ i) (fun j : Fin 4 => σ (2 + j)) (Sum.inr j)) =
            s - t := fun i j => by
          have h1 : ¬2 + (j : ℕ) < 2 := by omega
          dsimp only [Sum.elim_inl, Sum.elim_inr, σ]
          rw [if_pos i.2, if_neg h1]
          split_ifs <;> rfl
        simp only [hdiff, ← Finset.sum_mul, Finset.sum_sub_distrib, ← Finset.sum_mul_sum]
        rfl
      rw [hse, hcoup, hex_sum]
      dsimp only [A₀, B₀]
      rw [hSK]
      simp only [blockWeight]
      exact le_of_eq (by ring)
    · have hb := neutralBlock_four_coarse_bounds
      dsimp only [A₀]
      rw [hSK]
      simp only [blockWeight]
      linarith [hb.1.2, hb.2.1.2, hb.2.2.1.2]
    · have hb := neutralBlock_four_coarse_bounds
      have hA₀_b : -6.8800 < A₀ ∧ A₀ < -6.8792 := by
        dsimp only [A₀]; rw [hSK]; simp only [blockWeight]
        exact ⟨by linarith [hb.1.1, hb.2.1.1, hb.2.2.1.1],
          by linarith [hb.1.2, hb.2.1.2, hb.2.2.1.2]⟩
      have hB₀_b : -9.2776 < B₀ ∧ B₀ < -9.2764 := by
        dsimp only [B₀]; rw [hSK]; simp only [blockWeight]
        exact ⟨by linarith [hb.2.2.2.1.1, hb.2.2.2.2.1.1, hb.2.2.2.2.2.1, hb.2.1.1, hb.2.2.1.1],
          by linarith [hb.2.2.2.1.2, hb.2.2.2.2.1.2, hb.2.2.2.2.2.2, hb.2.1.2, hb.2.2.1.2]⟩
      have halg : (A₀ + P) * (B₀ + P) - (-P) ^ 2 = A₀ * B₀ + (A₀ + B₀) * P := by ring
      have hAB : 6.8792 * 9.2764 < A₀ * B₀ := by
        nlinarith [hA₀_b.1, hA₀_b.2, hB₀_b.1, hB₀_b.2]
      rcases le_or_gt P 0 with hP0 | hP0
      · have h1 : 0 ≤ (A₀ + B₀) * P :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith [hA₀_b.2, hB₀_b.2]) hP0
        linarith
      · have h1 : -(16.1576 * 2.33) < (A₀ + B₀) * P := by
          nlinarith [hA₀_b.1, hA₀_b.2, hB₀_b.1, hB₀_b.2]
        linarith
  · -- Same-sign nonzero row charges: WLOG `0 < u 0` and `0 < u 1`
    rcases lt_or_gt_of_ne (fun h0 : u 0 = 0 => by rw [h0, zero_mul] at hsign; exact lt_irrefl 0 hsign)
      with hu0 | hu0
    · have hu1 : u 1 < 0 := by nlinarith
      rw [← glued_lowered_neg]
      exact two_le_hermNegIndex_glued_lowered_two_pos (neg_pos.mpr hu0) (neg_pos.mpr hu1)
        fun i j => by simpa using huv4 i j
    · have hu1 : 0 < u 1 := by nlinarith
      exact two_le_hermNegIndex_glued_lowered_two_pos hu0 hu1 huv4

/-- **Universal negative-index obstruction (`2 ≤ R`, `3 ≤ Q`).** For every block size `R ≥ 2`
(even or odd) and every admissible charge pair `u_i v_j ≤ K_ij`, the product model of `(R, 2R]` and
`(2R, 4R]` with potentials lowered by the excess couplings has at least two negative squares. -/
theorem two_le_hermNegIndex_glued_lowered_ratio_four_of_two_le {Q R : ℕ} (hQ : 3 ≤ Q)
    (hR : 2 ≤ R) {u : Fin R → ℝ} {v : Fin (2 * R) → ℝ}
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (R + i) (2 * R + j)) :
    2 ≤ hermNegIndex ((glued
      (neutralWindow Q R R -
        diagonal (excessLeft
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v))
      (neutralWindow Q (2 * R) (2 * R) -
        diagonal (excessRight
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v))
      u v).map (↑) : Matrix (Fin R ⊕ Fin (2 * R)) (Fin R ⊕ Fin (2 * R)) ℂ) := by
  by_cases hR2 : R = 2
  · subst hR2
    exact two_le_hermNegIndex_glued_lowered_two hQ huv
  · by_cases hR3 : R = 3
    · subst hR3
      exact two_le_hermNegIndex_glued_lowered_three hQ huv
    · exact two_le_hermNegIndex_glued_lowered_of_four_le hQ (by omega) huv

/-- **Universal rank-one susceptibility obstruction (`2 ≤ R`, `3 ≤ Q`).** For every block size
`R ≥ 2` (even or odd), every admissible pair of charge vectors on `(R, 2R]` and `(2R, 4R]` whose
lowered halves are nonnegative on `ker u` and `ker v` has susceptibility product strictly below
`1`. -/
theorem not_exists_gluing_ratio_four_of_two_le {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 2 ≤ R)
    (u a : Fin R → ℝ) (v b : Fin (2 * R) → ℝ)
    (huv : ∀ i j, u i * v j ≤ blockWeight Q (R + i) (2 * R + j))
    (hAa : ∀ i, ∑ l,
      (neutralWindow Q R R -
        diagonal (excessLeft
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) i l *
        a l = u i)
    (hBb : ∀ j, ∑ m,
      (neutralWindow Q (2 * R) (2 * R) -
        diagonal (excessRight
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) j m *
        b m = v j)
    (hApos : ∀ x, chargeOf u x = 0 →
      0 ≤ bilin (neutralWindow Q R R -
        diagonal (excessLeft
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) x x)
    (hBpos : ∀ y, chargeOf v y = 0 →
      0 ≤ bilin (neutralWindow Q (2 * R) (2 * R) -
        diagonal (excessRight
          (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) y y) :
    chargeOf u a * chargeOf v b < 1 := by
  by_contra hge
  set K : Fin R → Fin (2 * R) → ℝ := fun i j => blockWeight Q (R + i) (2 * R + j)
  have hAneg : ∃ x₀ : Fin R → ℝ,
      bilin (neutralWindow Q R R - diagonal (excessLeft K u v)) x₀ x₀ < 0 := by
    refine ⟨fun _ => 1, ?_⟩
    rw [bilin_sub_diagonal]
    have h1 : bilin (neutralWindow Q R R) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) < 0 := by
      have heq : bilin (neutralWindow Q R R) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) =
          ∑ i ∈ range R, ∑ l ∈ range R, neutralBlock Q (R + i) (R + l) := by
        simpa [bilin, neutralWindow] using sum_fin_windowMatrix_coe (neutralBlock Q) R R (fun _ => 1)
      rw [heq]
      exact sum_neutralBlock_dyadic_neg Q (by omega)
    have h2 : 0 ≤ ∑ i : Fin R, excessLeft K u v i * (1 : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg
        (Finset.sum_nonneg fun j _ => sub_nonneg.mpr (huv i j)) (sq_nonneg _)
    linarith
  have hBneg : ∃ y₀ : Fin (2 * R) → ℝ,
      bilin (neutralWindow Q (2 * R) (2 * R) - diagonal (excessRight K u v)) y₀ y₀ < 0 := by
    refine ⟨fun _ => 1, ?_⟩
    rw [bilin_sub_diagonal]
    have h1 : bilin (neutralWindow Q (2 * R) (2 * R)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) < 0 := by
      have heq : bilin (neutralWindow Q (2 * R) (2 * R)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) =
          ∑ j ∈ range (2 * R), ∑ m ∈ range (2 * R), neutralBlock Q (2 * R + j) (2 * R + m) := by
        simpa [bilin, neutralWindow] using
          sum_fin_windowMatrix_coe (neutralBlock Q) (2 * R) (2 * R) (fun _ => 1)
      rw [heq]
      exact sum_neutralBlock_dyadic_neg Q (by omega)
    have h2 : 0 ≤ ∑ j : Fin (2 * R), excessRight K u v j * (1 : ℝ) ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg
        (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (huv i j)) (sq_nonneg _)
    linarith
  have h1 := hermNegIndex_glued_eq_one_of_exists_neg
    (sub_diagonal_symm (A := neutralWindow Q R R) (fun i l => neutralBlock_comm Q _ _) _)
    (sub_diagonal_symm (A := neutralWindow Q (2 * R) (2 * R))
      (fun j m => neutralBlock_comm Q _ _) _)
    hAa hBb hApos hBpos hAneg hBneg (not_lt.mp hge)
  have h2 := two_le_hermNegIndex_glued_lowered_ratio_four_of_two_le hQ hR huv
  dsimp only [K] at h1
  omega

/-- **Complete resolution of rank-one charge gluing on windows of ratio four (`1 ≤ R`, `3 ≤ Q`).**
The two halves `(R, 2R]` and `(2R, 4R]` admit charge vectors below the couplings whose lowered
halves are nonnegative on `ker u` and `ker v` with susceptibility product at least `1` if and only
if `R = 1`. -/
theorem halves_of_ratio_four_glue_iff_eq_one {Q R : ℕ} (hQ : 3 ≤ Q) (hR : 1 ≤ R) :
    (∃ (u a : Fin R → ℝ) (v b : Fin (2 * R) → ℝ),
      (∀ i j, u i * v j ≤ blockWeight Q (R + i) (2 * R + j)) ∧
      (∀ i, ∑ l,
        (neutralWindow Q R R -
          diagonal (excessLeft
            (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) i l *
          a l = u i) ∧
      (∀ j, ∑ m,
        (neutralWindow Q (2 * R) (2 * R) -
          diagonal (excessRight
            (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) j m *
          b m = v j) ∧
      (∀ x, chargeOf u x = 0 →
        0 ≤ bilin (neutralWindow Q R R -
          diagonal (excessLeft
            (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) x x) ∧
      (∀ y, chargeOf v y = 0 →
        0 ≤ bilin (neutralWindow Q (2 * R) (2 * R) -
          diagonal (excessRight
            (fun (i : Fin R) (j : Fin (2 * R)) => blockWeight Q (R + i) (2 * R + j)) u v)) y y) ∧
      1 ≤ chargeOf u a * chargeOf v b) ↔ R = 1 := by
  constructor
  · rintro ⟨u, a, v, b, huv, hAa, hBb, hApos, hBpos, h1⟩
    by_contra hne
    have hlt := not_exists_gluing_ratio_four_of_two_le hQ (by omega) u a v b huv hAa hBb hApos hBpos
    linarith
  · rintro rfl
    obtain ⟨u, a, v, b, huv, hAa, hBb, hApos, hBpos, _, _, hgt⟩ :=
      exists_unit_blocks_gluing_ratio_four hQ
    exact ⟨u, a, v, b, huv, hAa, hBb, hApos, hBpos, by linarith⟩

/-- Variational solvability and susceptibility bound for a Lorentzian form positive definite on
`ker w`. -/
private theorem exists_sol_and_chargeOf_bounds_of_ker_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : ∀ i l, M i l = M l i) {w : ι → ℝ} {C : ℝ} (hC : 0 < C)
    (hker : ∀ x : ι → ℝ, chargeOf w x = 0 → x ≠ 0 → 0 < bilin M x x)
    {y₁ : ι → ℝ} (hy₁ : chargeOf w y₁ = 1) (hMy₁ : bilin M y₁ y₁ < -C) :
    ∃ a : ι → ℝ, (∀ i, ∑ l, M i l * a l = w i) ∧ chargeOf w a < 0 ∧ -chargeOf w a < 1 / C := by
  have hker_nn : ∀ x : ι → ℝ, chargeOf w x = 0 → 0 ≤ bilin M x x := fun x hx => by
    by_cases hx0 : x = 0
    · subst hx0; simp [bilin]
    · exact (hker x hx hx0).le
  have hinj : Function.Injective M.mulVecLin := by
    intro p q hpq
    by_contra hne
    set z : ι → ℝ := p - q
    have hz_ne : z ≠ 0 := sub_ne_zero.mpr hne
    have hMz : M *ᵥ z = 0 := by
      rw [Matrix.mulVec_sub, show M *ᵥ p = M *ᵥ q from hpq, sub_self]
    have hrz : ∀ r : ι → ℝ, bilin M r z = 0 := fun r => by
      have h0 : r ⬝ᵥ (M *ᵥ z) = 0 := by rw [hMz, dotProduct_zero]
      have heq : r ⬝ᵥ (M *ᵥ z) = bilin M r z := by
        simp only [dotProduct, Matrix.mulVec, bilin, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
      linarith
    by_cases hwz : chargeOf w z = 0
    · linarith [hker z hwz hz_ne, hrz z]
    · set s : ℝ := chargeOf w z
      let x : ι → ℝ := fun i => s * y₁ i + (-1) * z i
      have hwx : chargeOf w x = 0 := by
        simp only [x, chargeOf, mul_add, Finset.sum_add_distrib]
        have hs1 : ∑ i, w i * (s * y₁ i) = s * chargeOf w y₁ := by
          rw [chargeOf, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        have hs2 : ∑ i, w i * ((-1) * z i) = -chargeOf w z := by
          rw [chargeOf, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hs1, hs2, hy₁]
        dsimp only [s]
        ring
      have hMx : bilin M x x = s ^ 2 * bilin M y₁ y₁ := by
        rw [bilin_comb_symm hM y₁ z s (-1), hrz y₁, hrz z]
        ring
      have hMx_neg : bilin M x x < 0 := by
        rw [hMx]
        exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hwz) (by linarith)
      linarith [hker_nn x hwx]
  obtain ⟨a, ha_mv⟩ := LinearMap.surjective_of_injective hinj w
  have hMa : ∀ i, ∑ l, M i l * a l = w i := fun i => by
    simpa [Matrix.mulVec, dotProduct] using congrFun ha_mv i
  have hα_le : chargeOf w a ≤ 0 :=
    chargeOf_nonpos_of_ker_nonneg_of_exists_neg hM hMa hker_nn ⟨y₁, by linarith⟩
  have hα_ne : chargeOf w a ≠ 0 := by
    intro h0
    by_cases ha0 : a = 0
    · have hw0 : ∀ i, w i = 0 := fun i => by simpa [ha0] using (hMa i).symm
      have : chargeOf w y₁ = 0 := by simp [chargeOf, hw0]
      linarith
    · have hpos := hker a h0 ha0
      rw [bilin_right_eq_chargeOf hMa a, h0] at hpos
      exact lt_irrefl 0 hpos
  have hα_lt : chargeOf w a < 0 := lt_of_le_of_ne hα_le hα_ne
  have hsub_nn := hker_nn (fun i => chargeOf w a * y₁ i - 1 * a i) (by
    rw [chargeOf_sub_smul, hy₁]; ring)
  rw [bilin_sub_smul hM hMa y₁ (chargeOf w a) 1, hy₁] at hsub_nn
  have hsq_pos : 0 < (chargeOf w a) ^ 2 := sq_pos_of_neg hα_lt
  have hmul_lt : (chargeOf w a) ^ 2 * bilin M y₁ y₁ < (chargeOf w a) ^ 2 * (-C) :=
    mul_lt_mul_of_pos_left hMy₁ hsq_pos
  have hprod_lt : C * (-chargeOf w a) < 1 := by nlinarith
  exact ⟨a, hMa, hα_lt, (lt_div_iff₀ hC).mpr (by linarith)⟩

private def vec4 (b₀ b₁ b₂ b₃ : ℝ) : Fin 4 → ℝ := fun j =>
  if (j : ℕ) = 0 then b₀ else if (j : ℕ) = 1 then b₁ else if (j : ℕ) = 2 then b₂ else b₃

private theorem vec4_0 (b₀ b₁ b₂ b₃ : ℝ) : vec4 b₀ b₁ b₂ b₃ 0 = b₀ := by simp [vec4]
private theorem vec4_1 (b₀ b₁ b₂ b₃ : ℝ) : vec4 b₀ b₁ b₂ b₃ 1 = b₁ := by simp [vec4]
private theorem vec4_2 (b₀ b₁ b₂ b₃ : ℝ) : vec4 b₀ b₁ b₂ b₃ 2 = b₂ := by simp [vec4]
private theorem vec4_3 (b₀ b₁ b₂ b₃ : ℝ) : vec4 b₀ b₁ b₂ b₃ 3 = b₃ := by simp [vec4]

private theorem fin2_val_0 : ((0 : Fin 2) : ℕ) = 0 := rfl
private theorem fin2_val_1 : ((1 : Fin 2) : ℕ) = 1 := rfl
private theorem fin4_val_0 : ((0 : Fin 4) : ℕ) = 0 := rfl
private theorem fin4_val_1 : ((1 : Fin 4) : ℕ) = 1 := rfl
private theorem fin4_val_2 : ((2 : Fin 4) : ℕ) = 2 := rfl
private theorem fin4_val_3 : ((3 : Fin 4) : ℕ) = 3 := rfl

private abbrev subUnitU : Fin 2 → ℝ := fun _ => 1
private abbrev subUnitV : Fin 4 → ℝ := vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2)
private abbrev subUnitB : Matrix (Fin 4) (Fin 4) ℝ :=
  neutralWindow 4 4 4 -
    diagonal (excessRight (fun (i : Fin 2) (j : Fin 4) => blockWeight 4 (2 + i) (4 + j))
      subUnitU subUnitV)

private theorem sub_unit_gram_diag :
    (2.28 < bilin subUnitB (vec4 0 0 1 (-1)) (vec4 0 0 1 (-1)) ∧
      bilin subUnitB (vec4 0 0 1 (-1)) (vec4 0 0 1 (-1)) < 2.30) ∧
    (11.53 < bilin subUnitB (vec4 3 0 (-4) 0) (vec4 3 0 (-4) 0) ∧
      bilin subUnitB (vec4 3 0 (-4) 0) (vec4 3 0 (-4) 0) < 11.61) ∧
    239.7 < bilin subUnitB (vec4 9 (-20) 0 0) (vec4 9 (-20) 0 0) := by
  have hb := fineBounds27
  refine ⟨?_, ?_, ?_⟩
  · rw [bilin_sub_diagonal, bilin]
    simp only [sum_fin_four, excessRight, Fin.sum_univ_two, subUnitU, subUnitV, blockWeight,
      vec4_0, vec4_1, vec4_2, vec4_3, neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num
    rw [neutralBlock_comm 4 7 6]
    constructor <;> linarith [hb.n66_gt, hb.n66_lt, hb.n67_gt, hb.n67_lt, hb.n77_gt, hb.n77_lt,
      hb.n26_gt, hb.n26_lt, hb.n36_gt, hb.n36_lt, hb.n27_gt, hb.n27_lt, hb.n37_gt, hb.n37_lt]
  · rw [bilin_sub_diagonal, bilin]
    simp only [sum_fin_four, excessRight, Fin.sum_univ_two, subUnitU, subUnitV, blockWeight,
      vec4_0, vec4_1, vec4_2, vec4_3, neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num
    rw [neutralBlock_comm 4 6 4]
    constructor <;> linarith [hb.n44_gt, hb.n44_lt, hb.n46_gt, hb.n46_lt, hb.n66_gt, hb.n66_lt,
      hb.n24_gt, hb.n24_lt, hb.n34_gt, hb.n34_lt, hb.n26_gt, hb.n26_lt, hb.n36_gt, hb.n36_lt]
  · rw [bilin_sub_diagonal, bilin]
    simp only [sum_fin_four, excessRight, Fin.sum_univ_two, subUnitU, subUnitV, blockWeight,
      vec4_0, vec4_1, vec4_2, vec4_3, neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num
    rw [neutralBlock_comm 4 5 4]
    linarith [hb.n44_gt, hb.n45_lt, hb.n55_gt, hb.n24_gt, hb.n34_gt, hb.n25_gt, hb.n35_gt]

private theorem sub_unit_gram_off :
    (-4.42 < bilin subUnitB (vec4 0 0 1 (-1)) (vec4 3 0 (-4) 0) ∧
      bilin subUnitB (vec4 0 0 1 (-1)) (vec4 3 0 (-4) 0) < -4.40) ∧
    (7.81 < bilin subUnitB (vec4 0 0 1 (-1)) (vec4 9 (-20) 0 0) ∧
      bilin subUnitB (vec4 0 0 1 (-1)) (vec4 9 (-20) 0 0) < 7.86) ∧
    (-5.15 < bilin subUnitB (vec4 3 0 (-4) 0) (vec4 9 (-20) 0 0) ∧
      bilin subUnitB (vec4 3 0 (-4) 0) (vec4 9 (-20) 0 0) < -4.96) := by
  have hb := fineBounds27
  refine ⟨?_, ?_, ?_⟩
  · rw [bilin]
    simp only [sum_fin_four, subUnitB, Matrix.sub_apply, Matrix.diagonal_apply, excessRight,
      Fin.sum_univ_two, subUnitU, subUnitV, blockWeight, vec4_0, vec4_1, vec4_2, vec4_3,
      neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num [Fin.ext_iff]
    rw [neutralBlock_comm 4 6 4, neutralBlock_comm 4 7 4, neutralBlock_comm 4 7 6]
    constructor <;> linarith [hb.n46_gt, hb.n46_lt, hb.n47_gt, hb.n47_lt, hb.n66_gt, hb.n66_lt,
      hb.n67_gt, hb.n67_lt, hb.n26_gt, hb.n26_lt, hb.n36_gt, hb.n36_lt]
  · rw [bilin]
    simp only [sum_fin_four, subUnitB, Matrix.sub_apply, Matrix.diagonal_apply, excessRight,
      Fin.sum_univ_two, subUnitU, subUnitV, blockWeight, vec4_0, vec4_1, vec4_2, vec4_3,
      neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num [Fin.ext_iff]
    rw [neutralBlock_comm 4 6 4, neutralBlock_comm 4 6 5, neutralBlock_comm 4 7 4,
      neutralBlock_comm 4 7 5]
    constructor <;> linarith [hb.n46_gt, hb.n46_lt, hb.n56_gt, hb.n56_lt, hb.n47_gt, hb.n47_lt,
      hb.n57_gt, hb.n57_lt]
  · rw [bilin]
    simp only [sum_fin_four, subUnitB, Matrix.sub_apply, Matrix.diagonal_apply, excessRight,
      Fin.sum_univ_two, subUnitU, subUnitV, blockWeight, vec4_0, vec4_1, vec4_2, vec4_3,
      neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num [Fin.ext_iff]
    rw [neutralBlock_comm 4 6 4, neutralBlock_comm 4 6 5]
    constructor <;> linarith [hb.n44_gt, hb.n44_lt, hb.n45_gt, hb.n45_lt, hb.n46_gt, hb.n46_lt,
      hb.n56_gt, hb.n56_lt, hb.n24_gt, hb.n24_lt, hb.n34_gt, hb.n34_lt]

private abbrev subUnitA : Matrix (Fin 2) (Fin 2) ℝ :=
  neutralWindow 4 2 2 -
    diagonal (excessLeft (fun (i : Fin 2) (j : Fin 4) => blockWeight 4 (2 + i) (4 + j))
      subUnitU subUnitV)

private theorem sub_unit_test_bounds :
    0.15 < bilin subUnitA (fun i => if (i : ℕ) = 0 then 1 else -1)
      (fun i => if (i : ℕ) = 0 then 1 else -1) ∧
    bilin subUnitA (fun i => if (i : ℕ) = 0 then 2 else -1)
      (fun i => if (i : ℕ) = 0 then 2 else -1) < -1 ∧
    bilin subUnitB (vec4 0 2 1 (-1 / 5)) (vec4 0 2 1 (-1 / 5)) < -2 := by
  have hb := fineBounds27
  refine ⟨?_, ?_, ?_⟩
  · rw [bilin_sub_diagonal, bilin]
    simp only [Fin.sum_univ_two, excessLeft, sum_fin_four, subUnitU, subUnitV,
      blockWeight, vec4_0, vec4_1, vec4_2, vec4_3, neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num
    rw [neutralBlock_comm 4 3 2]
    linarith [hb.n22_gt, hb.n23_lt, hb.n33_gt, hb.n24_gt, hb.n25_gt, hb.n26_gt, hb.n27_gt,
      hb.n34_gt, hb.n35_gt, hb.n36_gt, hb.n37_gt]
  · rw [bilin_sub_diagonal, bilin]
    simp only [Fin.sum_univ_two, excessLeft, sum_fin_four, subUnitU, subUnitV,
      blockWeight, vec4_0, vec4_1, vec4_2, vec4_3, neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num
    rw [neutralBlock_comm 4 3 2]
    linarith [hb.n22_lt, hb.n23_gt, hb.n33_lt, hb.n24_lt, hb.n25_lt, hb.n26_lt, hb.n27_lt,
      hb.n34_lt, hb.n35_lt, hb.n36_lt, hb.n37_lt]
  · rw [bilin_sub_diagonal, bilin]
    simp only [sum_fin_four, excessRight, Fin.sum_univ_two, subUnitU, subUnitV,
      blockWeight, vec4_0, vec4_1, vec4_2, vec4_3, neutralWindow, windowMatrix, Matrix.of_apply,
      fin2_val_0, fin2_val_1, fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3]
    norm_num
    rw [neutralBlock_comm 4 6 5, neutralBlock_comm 4 7 5, neutralBlock_comm 4 7 6]
    linarith [hb.n55_lt, hb.n56_lt, hb.n57_gt, hb.n66_lt, hb.n67_gt, hb.n77_lt,
      hb.n25_lt, hb.n35_lt, hb.n26_lt, hb.n36_lt, hb.n27_lt, hb.n37_lt]

private theorem gram3_pos_of_bounds
    {g₀₀ g₁₁ g₂₂ g₀₁ g₀₂ g₁₂ t₀ t₁ t₂ : ℝ}
    (hg00 : 2.28 < g₀₀ ∧ g₀₀ < 2.30)
    (hg11 : 11.53 < g₁₁ ∧ g₁₁ < 11.61)
    (hg22 : 239.7 < g₂₂)
    (hg01 : -4.42 < g₀₁ ∧ g₀₁ < -4.40)
    (hg02 : 7.81 < g₀₂ ∧ g₀₂ < 7.86)
    (hg12 : -5.15 < g₁₂ ∧ g₁₂ < -4.96)
    (hne : ¬(t₀ = 0 ∧ t₁ = 0 ∧ t₂ = 0)) :
    0 < g₀₀ * t₀ ^ 2 + g₁₁ * t₁ ^ 2 + g₂₂ * t₂ ^ 2 +
      2 * g₀₁ * t₀ * t₁ + 2 * g₀₂ * t₀ * t₂ + 2 * g₁₂ * t₁ * t₂ := by
  have hg00_1 := hg00.1; have hg00_2 := hg00.2
  have hg11_1 := hg11.1
  have hg01_1 := hg01.1; have hg01_2 := hg01.2
  have hg02_1 := hg02.1; have hg02_2 := hg02.2
  have hg12_1 := hg12.1; have hg12_2 := hg12.2
  have hd₂ : 6.75 < g₀₀ * g₁₁ - g₀₁ ^ 2 := by
    have p1 : 2.28 * 11.53 < g₀₀ * g₁₁ := by nlinarith only [hg00_1, hg11_1]
    have p2 : g₀₁ ^ 2 < 4.42 ^ 2 := by nlinarith only [hg01_1, hg01_2]
    linarith only [p1, p2]
  have hc12_1 : 22.5 < g₀₀ * g₁₂ - g₀₁ * g₀₂ := by
    have p1 : 2.30 * (-5.15) < g₀₀ * g₁₂ := by nlinarith only [hg00_1, hg00_2, hg12_1, hg12_2]
    have p3 : 4.40 * 7.81 < -g₀₁ * g₀₂ := by nlinarith only [hg01_1, hg01_2, hg02_1, hg02_2]
    linarith only [p1, p3]
  have hc12_2 : g₀₀ * g₁₂ - g₀₁ * g₀₂ < 23.5 := by
    have p2 : g₀₀ * g₁₂ < 2.28 * (-4.96) := by nlinarith only [hg00_1, hg00_2, hg12_1, hg12_2]
    have p4 : -g₀₁ * g₀₂ < 4.42 * 7.86 := by nlinarith only [hg01_1, hg01_2, hg02_1, hg02_2]
    linarith only [p2, p4]
  have hdet3 : 2700 < (g₀₀ * g₁₁ - g₀₁ ^ 2) * (g₀₀ * g₂₂ - g₀₂ ^ 2) -
      (g₀₀ * g₁₂ - g₀₁ * g₀₂) ^ 2 := by
    have p1 : 484 < g₀₀ * g₂₂ - g₀₂ ^ 2 := by
      have q1 : 2.28 * 239.7 < g₀₀ * g₂₂ := by nlinarith only [hg00_1, hg22]
      have q2 : g₀₂ ^ 2 < 7.86 ^ 2 := by nlinarith only [hg02_1, hg02_2]
      linarith only [q1, q2]
    have p2 : 6.75 * 484 < (g₀₀ * g₁₁ - g₀₁ ^ 2) * (g₀₀ * g₂₂ - g₀₂ ^ 2) := by
      nlinarith only [hd₂, p1]
    have p3 : (g₀₀ * g₁₂ - g₀₁ * g₀₂) ^ 2 < 23.5 ^ 2 := by nlinarith only [hc12_1, hc12_2]
    linarith only [p2, p3]
  have hid : (g₀₀ * g₁₁ - g₀₁ ^ 2) * g₀₀ *
      (g₀₀ * t₀ ^ 2 + g₁₁ * t₁ ^ 2 + g₂₂ * t₂ ^ 2 +
        2 * g₀₁ * t₀ * t₁ + 2 * g₀₂ * t₀ * t₂ + 2 * g₁₂ * t₁ * t₂) =
      (g₀₀ * g₁₁ - g₀₁ ^ 2) * (g₀₀ * t₀ + g₀₁ * t₁ + g₀₂ * t₂) ^ 2 +
        ((g₀₀ * g₁₁ - g₀₁ ^ 2) * t₁ + (g₀₀ * g₁₂ - g₀₁ * g₀₂) * t₂) ^ 2 +
        ((g₀₀ * g₁₁ - g₀₁ ^ 2) * (g₀₀ * g₂₂ - g₀₂ ^ 2) -
          (g₀₀ * g₁₂ - g₀₁ * g₀₂) ^ 2) * t₂ ^ 2 := by ring
  by_contra hnp
  have hle0 : (g₀₀ * g₁₁ - g₀₁ ^ 2) * g₀₀ *
      (g₀₀ * t₀ ^ 2 + g₁₁ * t₁ ^ 2 + g₂₂ * t₂ ^ 2 +
        2 * g₀₁ * t₀ * t₁ + 2 * g₀₂ * t₀ * t₂ + 2 * g₁₂ * t₁ * t₂) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by linarith only [hd₂]) (by linarith only [hg00_1])) (not_lt.mp hnp)
  rw [hid] at hle0
  have hs1 : 0 ≤ (g₀₀ * g₁₁ - g₀₁ ^ 2) * (g₀₀ * t₀ + g₀₁ * t₁ + g₀₂ * t₂) ^ 2 :=
    mul_nonneg (by linarith only [hd₂]) (sq_nonneg _)
  have hs2 : 0 ≤ ((g₀₀ * g₁₁ - g₀₁ ^ 2) * t₁ + (g₀₀ * g₁₂ - g₀₁ * g₀₂) * t₂) ^ 2 := sq_nonneg _
  have ht₂0 : t₂ = 0 := by
    have ht₂_sq : t₂ ^ 2 ≤ 0 := by nlinarith only [hle0, hs1, hs2, hdet3, sq_nonneg t₂]
    exact sq_eq_zero_iff.mp (le_antisymm ht₂_sq (sq_nonneg _))
  rw [ht₂0] at hle0 hs1
  simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)] at hle0 hs1
  have ht₁0 : t₁ = 0 := by
    have ht₁_sq : ((g₀₀ * g₁₁ - g₀₁ ^ 2) * t₁) ^ 2 ≤ 0 := by linarith only [hle0, hs1]
    have hd_t₁ : (g₀₀ * g₁₁ - g₀₁ ^ 2) * t₁ = 0 :=
      sq_eq_zero_iff.mp (le_antisymm ht₁_sq (sq_nonneg _))
    nlinarith only [hd₂, hd_t₁]
  rw [ht₁0] at hle0
  simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)] at hle0
  have ht₀0 : t₀ = 0 := by
    have ht₀_sq : (g₀₀ * t₀) ^ 2 ≤ 0 := by
      nlinarith only [hle0, hd₂, sq_nonneg (g₀₀ * t₀)]
    have hg_t₀ : g₀₀ * t₀ = 0 := sq_eq_zero_iff.mp (le_antisymm ht₀_sq (sq_nonneg _))
    nlinarith only [hg00_1, hg_t₀]
  exact hne ⟨ht₀0, ht₁0, ht₂0⟩

private theorem sub_unit_aux
    (A_low : Matrix (Fin 2) (Fin 2) ℝ) (B_low : Matrix (Fin 4) (Fin 4) ℝ)
    (hA_symm : ∀ i l, A_low i l = A_low l i)
    (hB_symm : ∀ j m, B_low j m = B_low m j)
    (heA : 0.15 < bilin A_low (fun i => if (i : ℕ) = 0 then 1 else -1)
      (fun i => if (i : ℕ) = 0 then 1 else -1))
    (hx₁ : bilin A_low (fun i => if (i : ℕ) = 0 then 2 else -1)
      (fun i => if (i : ℕ) = 0 then 2 else -1) < -1)
    (hy₁ : bilin B_low (vec4 0 2 1 (-1 / 5)) (vec4 0 2 1 (-1 / 5)) < -2)
    (hg00 : 2.28 < bilin B_low (vec4 0 0 1 (-1)) (vec4 0 0 1 (-1)) ∧
      bilin B_low (vec4 0 0 1 (-1)) (vec4 0 0 1 (-1)) < 2.30)
    (hg11 : 11.53 < bilin B_low (vec4 3 0 (-4) 0) (vec4 3 0 (-4) 0) ∧
      bilin B_low (vec4 3 0 (-4) 0) (vec4 3 0 (-4) 0) < 11.61)
    (hg22 : 239.7 < bilin B_low (vec4 9 (-20) 0 0) (vec4 9 (-20) 0 0))
    (hg01 : -4.42 < bilin B_low (vec4 0 0 1 (-1)) (vec4 3 0 (-4) 0) ∧
      bilin B_low (vec4 0 0 1 (-1)) (vec4 3 0 (-4) 0) < -4.40)
    (hg02 : 7.81 < bilin B_low (vec4 0 0 1 (-1)) (vec4 9 (-20) 0 0) ∧
      bilin B_low (vec4 0 0 1 (-1)) (vec4 9 (-20) 0 0) < 7.86)
    (hg12 : -5.15 < bilin B_low (vec4 3 0 (-4) 0) (vec4 9 (-20) 0 0) ∧
      bilin B_low (vec4 3 0 (-4) 0) (vec4 9 (-20) 0 0) < -4.96) :
    ∃ (a : Fin 2 → ℝ) (b : Fin 4 → ℝ),
      (∀ i, ∑ l, A_low i l * a l = subUnitU i) ∧
      (∀ j, ∑ m, B_low j m * b m = subUnitV j) ∧
      (∀ x, chargeOf subUnitU x = 0 → 0 ≤ bilin A_low x x) ∧
      (∀ y, chargeOf subUnitV y = 0 → 0 ≤ bilin B_low y y) ∧
      chargeOf subUnitU a < 0 ∧ chargeOf subUnitV b < 0 ∧
      0 < chargeOf subUnitU a * chargeOf subUnitV b ∧
      chargeOf subUnitU a * chargeOf subUnitV b < 1 / 2 := by
  have hA_ker : ∀ x : Fin 2 → ℝ, chargeOf subUnitU x = 0 → x ≠ 0 → 0 < bilin A_low x x := by
    intro x hx hx0
    have hx1 : x 1 = -x 0 := by
      rw [chargeOf, Fin.sum_univ_two] at hx
      dsimp only [subUnitU] at hx
      linarith only [hx]
    have hx0_ne : x 0 ≠ 0 := fun h0 => hx0 (funext fun i => by fin_cases i <;> simp [h0, hx1])
    have hxe : x = fun i : Fin 2 => x 0 * (if (i : ℕ) = 0 then 1 else -1) := funext fun i => by
      fin_cases i <;> simp [hx1]
    rw [hxe, bilin_smul_left, bilin_symm hA_symm (fun i => if (i : ℕ) = 0 then 1 else -1),
      bilin_smul_left]
    have hsq := sq_pos_of_ne_zero hx0_ne
    nlinarith only [heA, hsq]
  have hx₁_ch : chargeOf subUnitU (fun i : Fin 2 => if (i : ℕ) = 0 then 2 else -1) = 1 := by
    rw [chargeOf, Fin.sum_univ_two]; norm_num [subUnitU]
  obtain ⟨a, hAa, hα_neg, hα_ub⟩ :=
    exists_sol_and_chargeOf_bounds_of_ker_pos hA_symm one_pos hA_ker hx₁_ch hx₁
  have hB_ker : ∀ y : Fin 4 → ℝ, chargeOf subUnitV y = 0 → y ≠ 0 → 0 < bilin B_low y y := by
    intro y hy hy0
    rw [chargeOf, sum_fin_four, subUnitV, vec4_0, vec4_1, vec4_2, vec4_3] at hy
    let t₀ : ℝ := -y 3
    let t₂ : ℝ := -y 1 / 20
    let t₁ : ℝ := (y 0 - 9 * t₂) / 3
    have hy_eq : y = fun j =>
        t₀ * vec4 0 0 1 (-1) j + t₁ * vec4 3 0 (-4) 0 j + t₂ * vec4 9 (-20) 0 0 j :=
      funext fun j => by
        fin_cases j
        · simp only [Fin.zero_eta, vec4_0, t₀, t₁, t₂]; ring
        · simp only [Fin.mk_one, vec4_1, t₀, t₁, t₂]; ring
        · simp only [Fin.reduceFinMk, vec4_2, t₀, t₁, t₂]; linarith only [hy]
        · simp only [Fin.reduceFinMk, vec4_3, t₀, t₁, t₂]; ring
    have hne : ¬(t₀ = 0 ∧ t₁ = 0 ∧ t₂ = 0) := fun ⟨h0, h1, h2⟩ =>
      hy0 (by rw [hy_eq]; ext j; simp [h0, h1, h2])
    rw [hy_eq, bilin_comb3_symm hB_symm]
    exact gram3_pos_of_bounds hg00 hg11 hg22 hg01 hg02 hg12 hne
  have hy₁_ch : chargeOf subUnitV (vec4 0 2 1 (-1 / 5)) = 1 := by
    rw [chargeOf, sum_fin_four]
    simp only [subUnitV, vec4_0, vec4_1, vec4_2, vec4_3]
    norm_num
  obtain ⟨b, hBb, hβ_neg, hβ_ub⟩ :=
    exists_sol_and_chargeOf_bounds_of_ker_pos hB_symm (by norm_num : (0 : ℝ) < 2) hB_ker
      hy₁_ch hy₁
  refine ⟨a, b, hAa, hBb,
    fun x hx => if hx0 : x = 0 then by subst hx0; simp [bilin] else (hA_ker x hx hx0).le,
    fun y hy => if hy0 : y = 0 then by subst hy0; simp [bilin] else (hB_ker y hy hy0).le,
    hα_neg, hβ_neg, mul_pos_of_neg_of_neg hα_neg hβ_neg, ?_⟩
  have h1 : chargeOf subUnitU a * chargeOf subUnitV b =
      (-chargeOf subUnitU a) * (-chargeOf subUnitV b) := by ring
  rw [h1]
  have hp1 := neg_pos.mpr hα_neg
  have hp2 := neg_pos.mpr hβ_neg
  nlinarith only [hp1, hp2, hα_ub, hβ_ub]

/-- **Sub-unit gluing witness on two blocks (`R = 2`, `3 ≤ Q`).** The admissible domain on
`(2, 4]` and `(4, 8]` with nonnegative lowered kernels and negative susceptibilities is nonempty:
explicit rational charges achieve `0 < (u · a)(v · b) < 1/2 < 1`. -/
theorem exists_sub_unit_gluing_two_blocks_ratio_four {Q : ℕ} (hQ : 3 ≤ Q) :
    ∃ (u a : Fin 2 → ℝ) (v b : Fin 4 → ℝ),
      (∀ i j, u i * v j ≤ blockWeight Q (2 + i) (4 + j)) ∧
      (∀ i, ∑ l,
        (neutralWindow Q 2 2 -
          diagonal (excessLeft
            (fun (i : Fin 2) (j : Fin 4) => blockWeight Q (2 + i) (4 + j)) u v)) i l *
          a l = u i) ∧
      (∀ j, ∑ m,
        (neutralWindow Q 4 4 -
          diagonal (excessRight
            (fun (i : Fin 2) (j : Fin 4) => blockWeight Q (2 + i) (4 + j)) u v)) j m *
          b m = v j) ∧
      (∀ x, chargeOf u x = 0 →
        0 ≤ bilin (neutralWindow Q 2 2 -
          diagonal (excessLeft
            (fun (i : Fin 2) (j : Fin 4) => blockWeight Q (2 + i) (4 + j)) u v)) x x) ∧
      (∀ y, chargeOf v y = 0 →
        0 ≤ bilin (neutralWindow Q 4 4 -
          diagonal (excessRight
            (fun (i : Fin 2) (j : Fin 4) => blockWeight Q (2 + i) (4 + j)) u v)) y y) ∧
      chargeOf u a < 0 ∧ chargeOf v b < 0 ∧
      0 < chargeOf u a * chargeOf v b ∧ chargeOf u a * chargeOf v b < 1 / 2 := by
  rw [neutralWindow_two_eq_four hQ, neutralWindow_four_eq_four hQ, blockWeight_two_four_eq_four hQ]
  have hb := fineBounds27
  have huv : ∀ (i : Fin 2) (j : Fin 4), subUnitU i * subUnitV j ≤ blockWeight 4 (2 + i) (4 + j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 0 ≤ -neutralBlock 4 2 4
      rw [vec4_0]; linarith [hb.n24_lt]
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 1 ≤ -neutralBlock 4 2 5
      rw [vec4_1]; linarith [hb.n25_lt]
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 2 ≤ -neutralBlock 4 2 6
      rw [vec4_2]; linarith [hb.n26_lt]
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 3 ≤ -neutralBlock 4 2 7
      rw [vec4_3]; linarith [hb.n27_lt]
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 0 ≤ -neutralBlock 4 3 4
      rw [vec4_0]; linarith [hb.n34_lt]
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 1 ≤ -neutralBlock 4 3 5
      rw [vec4_1]; linarith [hb.n35_lt]
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 2 ≤ -neutralBlock 4 3 6
      rw [vec4_2]; linarith [hb.n36_lt]
    · show (1 : ℝ) * vec4 (2 / 3) (3 / 10) (1 / 2) (1 / 2) 3 ≤ -neutralBlock 4 3 7
      rw [vec4_3]; linarith [hb.n37_lt]
  have ht := sub_unit_test_bounds
  have hgd := sub_unit_gram_diag
  have hgo := sub_unit_gram_off
  obtain ⟨a, b, hAa, hBb, hAk, hBk, hα, hβ, hp0, hp1⟩ :=
    sub_unit_aux subUnitA subUnitB
      (sub_diagonal_symm (A := neutralWindow 4 2 2) (fun i l => neutralBlock_comm 4 _ _) _)
      (sub_diagonal_symm (A := neutralWindow 4 4 4) (fun j m => neutralBlock_comm 4 _ _) _)
      ht.1 ht.2.1 ht.2.2 hgd.1 hgd.2.1 hgd.2.2 hgo.1 hgo.2.1 hgo.2.2
  exact ⟨subUnitU, a, subUnitV, b, fun i j => by
    rw [blockWeight_eq_four_of_lt_four_mul hQ (by omega) (by have := i.2; omega)
      (by have := j.2; omega)]
    exact huv i j, hAa, hBb, hAk, hBk, hα, hβ, hp0, hp1⟩

/-- **Rank-two zero-excess gluing on two blocks (`R = 2`, `3 ≤ Q`).** While rank-one charges have
at least `2` negative squares everywhere on `(2, 4]` and `(4, 8]`, rank-two charge matrices
`U = 1` and `V_ji = K_ij` glue the two halves with zero excess and exact negative index `1`. -/
theorem hermNegIndex_gluedMatrix_two_blocks_ratio_four_eq_one {Q : ℕ} (hQ : 3 ≤ Q) :
    let K : Fin 2 → Fin 4 → ℝ := fun i j => blockWeight Q (2 + i) (4 + j)
    let U : Matrix (Fin 2) (Fin 2) ℝ := 1
    let V : Matrix (Fin 4) (Fin 2) ℝ := Matrix.of fun j i => K i j
    (∀ i j, (∑ k, U i k * V j k) ≤ K i j) ∧
      hermNegIndex ((gluedMatrix
        (neutralWindow Q 2 2 - diagonal (excessLeftMatrix K U V))
        (neutralWindow Q 4 4 - diagonal (excessRightMatrix K U V)) U V).map (↑) :
          Matrix (Fin 2 ⊕ Fin 4) (Fin 2 ⊕ Fin 4) ℂ) = 1 := by
  intro K U V
  have hUV : ∀ i j, ∑ k : Fin 2, U i k * V j k = K i j := fun i j => by
    rw [Finset.sum_eq_single i
      (fun k _ hki => by simp [U, Matrix.one_apply_ne (Ne.symm hki)])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp [U, V]
  refine ⟨fun i j => (hUV i j).le, ?_⟩
  have heL : excessLeftMatrix K U V = 0 := funext fun i =>
    Finset.sum_eq_zero fun j _ => by rw [hUV i j, sub_self]
  have heR : excessRightMatrix K U V = 0 := funext fun j =>
    Finset.sum_eq_zero fun i _ => by rw [hUV i j, sub_self]
  have hgm : gluedMatrix (neutralWindow Q 2 2 - diagonal (excessLeftMatrix K U V))
      (neutralWindow Q 4 4 - diagonal (excessRightMatrix K U V)) U V =
      coupled (neutralWindow Q 2 2) (neutralWindow Q 4 4) K := by
    have hd2 : (diagonal 0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := Matrix.diagonal_zero
    have hd4 : (diagonal 0 : Matrix (Fin 4) (Fin 4) ℝ) = 0 := Matrix.diagonal_zero
    rw [heL, heR, hd2, hd4, sub_zero, sub_zero, gluedMatrix]
    congr 1
    funext i j
    exact hUV i j
  rw [hgm, ← hermNegIndex_neutralWindow_add Q 2 2 4]
  have h24 : neutralWindow Q 2 6 = neutralWindow 4 2 6 := by
    ext p q
    exact neutralBlock_eq_four_of_lt_four_mul hQ (by omega) (by omega)
      (by have := p.2; have := q.2; omega) (by have := p.2; have := q.2; omega)
  rw [show 2 + 4 = 6 by rfl, h24]
  exact le_antisymm
    (hermNegIndex_neutralWindow_le_one_of_nonneg fun σ =>
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => sq_nonneg (σ j))).trans
        (sum_blockMatrix_four_fine_ge σ))
    (one_le_hermNegIndex_neutralWindow 4 (by norm_num) (by norm_num))

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
