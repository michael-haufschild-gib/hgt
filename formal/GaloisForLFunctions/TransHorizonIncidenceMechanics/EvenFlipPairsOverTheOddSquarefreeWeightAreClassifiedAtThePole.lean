import GaloisForLFunctions.TransHorizonIncidenceMechanics.FinitePerturbationsOfTheSmoothPowerAreDecidedAtThePole

/-!
# Even-flip pairs over the odd squarefree weight are classified at the pole

Let `o(d) = 1_{d odd squarefree} d^{-ε}` and `0 < ε ≤ 1/2`.

* **Pole law over `o`.** For a kernel `k` on `[1, J]`, the receiver of `k ⋆ o` is bounded **iff**
  `K(1 − ε) = Σ_j k(j) j^{-(1−ε)} = 0`. Sufficiency: `o = g ⋆ (1_{odd} d^{-ε})` with `g` critical
  Wiener, and `k ⋆ (1_{odd} d^{-ε})` is the damped sign weight of `k̃ ⋆ 1_{odd}`, whose partial sums
  `Σ_j k̃(j) ⌈⌊n/j⌋/2⌉ = ½ Σ_j k̃(j)⌊n/j⌋ + O(Σ|k̃|)` are bounded once the mean `½K(1 − ε)` vanishes.
  Necessity: the pole law of finite kernels with the odd squarefree drift.
* **Classification of the two-point pairs.** For `k = αδ₁ + βδ₂` the even flip of `k ⋆ o` is
  `k^♭ ⋆ o` with `k^♭ = (α + β)δ₁ − βδ₂`; the two weights have the same Ramanujan amplitudes. The pole
  values are `α + β 2^{ε−1}` and `α + β(1 − 2^{ε−1})`, whose difference is `β(1 − 2^{ε})`. Hence
  **`k ⋆ o` is paid iff `α = −2^{ε−1}β`, its flip iff `α = −(1 − 2^{ε−1})β`, and unless `α = β = 0`
  at most one member of an even-flip pair is paid.** The Fermi pair is the line `α = −2^{ε−1}β`.

The dilation `k ↦ 2k` acts on the two-point kernels by `(α, β) ↦ (α + β, −β)`; the receiver reads
only its effect on the value at the pole.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Commuting convolutions -/

/-- A function as an arithmetic function (forgetting its value at `0`). -/
def toAF (f : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else f n, by simp⟩

theorem dirichletConv_eq_toAF_mul (f g : ℕ → ℝ) (n : ℕ) :
    RHTower.dirichletConv f g n = (toAF f * toAF g) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [RHTower.dirichletConv]
  rw [mul_apply_eq_dirichletConv]
  unfold RHTower.dirichletConv
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hq0 : n / d ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  simp [toAF, hd0, hq0]

theorem toAF_dirichletConv (f g : ℕ → ℝ) : toAF (RHTower.dirichletConv f g) = toAF f * toAF g := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [← dirichletConv_eq_toAF_mul]; simp [toAF, hn]

/-- Dirichlet convolutions commute past each other: `k ⋆ (G ⋆ O) = G ⋆ (k ⋆ O)`. -/
theorem dirichletConv_left_comm (k G O : ℕ → ℝ) (n : ℕ) :
    RHTower.dirichletConv k (RHTower.dirichletConv G O) n =
      RHTower.dirichletConv G (RHTower.dirichletConv k O) n := by
  rw [dirichletConv_eq_toAF_mul, dirichletConv_eq_toAF_mul, toAF_dirichletConv, toAF_dirichletConv,
    mul_left_comm]

/-- `o = g ⋆ (1_{odd} d^{-ε})`. -/
theorem oddSqfWeight_eq (ε : ℝ) (n : ℕ) :
    oddSqfWeight ε n = RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε)
      (dampedSignWeight ⇑oddAF ε) n := by
  rw [← dampedSignWeight_dirichletConv, oddSqfWeight, oddSqfAF_eq]
  simp only [dampedSignWeight, mul_apply_eq_dirichletConv]

/-! ### Odd partial sums -/

theorem sum_Icc_oddAF (y : ℕ) : ∑ m ∈ Icc 1 y, oddAF m = (((y + 1) / 2 : ℕ) : ℝ) := by
  induction y with
  | zero => simp
  | succ y ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, oddAF_apply]
    by_cases h : 2 ∣ y + 1
    · rw [if_neg (not_not.mpr h), add_zero, show (y + 1 + 1) / 2 = (y + 1) / 2 by omega]
    · rw [if_pos h, show (y + 1 + 1) / 2 = (y + 1) / 2 + 1 by omega]; push_cast; ring

theorem abs_sum_Icc_oddAF_sub_le (y : ℕ) : |∑ m ∈ Icc 1 y, oddAF m - (y : ℝ) / 2| ≤ 1 / 2 := by
  rw [sum_Icc_oddAF]
  have h : 2 * ((y + 1) / 2) = y ∨ 2 * ((y + 1) / 2) = y + 1 := by omega
  have hc : (2 : ℝ) * (((y + 1) / 2 : ℕ) : ℝ) = y ∨ (2 : ℝ) * (((y + 1) / 2 : ℕ) : ℝ) = y + 1 := by
    rcases h with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  rw [abs_le]
  rcases hc with hc | hc <;> constructor <;> linarith

/-- **At a zero of the pole value, `k̃ ⋆ 1_{odd}` has bounded partial sums.** -/
theorem abs_sum_range_dirichletConv_oddAF_le {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    {ε : ℝ} (hK : poleValue k J ε = 0) (x : ℕ) :
    |∑ d ∈ range x, RHTower.dirichletConv (undampedKernel k ε) ⇑oddAF d| ≤
      ∑ j ∈ Icc 1 J, |undampedKernel k ε j| := by
  set k' := undampedKernel k ε
  set L := ∑ j ∈ Icc 1 J, |k' j|
  have hL : 0 ≤ L := sum_nonneg fun j _ => abs_nonneg _
  have hk'J : ∀ j, J < j → k' j = 0 := undampedKernel_support hkJ ε
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa using hL
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  rw [dampedSign_sum_range_succ_eq_add_Icc]
  have h0 : RHTower.dirichletConv k' ⇑oddAF 0 = 0 := by simp [RHTower.dirichletConv]
  rw [h0, zero_add]
  -- the floor transform of `k̃ ⋆ 1_{odd}` against `1`
  have hft := RHTower.floorTransform_comp k' ⇑oddAF (fun _ => (1 : ℝ)) n
  simp only [RHTower.floorTransform, mul_one] at hft
  rw [← hft]
  -- split off the mean `½ Σ_j k̃(j) ⌊n/j⌋`
  have hsplit : ∑ j ∈ Icc 1 n, k' j * ∑ m ∈ Icc 1 (n / j), oddAF m =
      ∑ j ∈ Icc 1 n, k' j * (∑ m ∈ Icc 1 (n / j), oddAF m - ((n / j : ℕ) : ℝ) / 2) +
        (1 / 2) * ∑ j ∈ Icc 1 n, k' j * ((n / j : ℕ) : ℝ) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hmean := abs_weightCenteredPrefix_finiteKernel_le hk'J n
  rw [sum_undampedKernel_div, hK, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    zero_mul, sub_zero] at hmean
  have hsub : ∑ j ∈ Icc 1 n, |k' j| ≤ L := by
    calc ∑ j ∈ Icc 1 n, |k' j| ≤ ∑ j ∈ Icc 1 (n + J), |k' j| :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (by omega))
            fun _ _ _ => abs_nonneg _
      _ = L := by
          refine (sum_subset (Icc_subset_Icc le_rfl (by omega)) fun j hj hjJ => ?_).symm
          have : J < j := by simp only [mem_Icc] at hj hjJ; omega
          rw [hk'J j this, abs_zero]
  have hfirst : |∑ j ∈ Icc 1 n, k' j * (∑ m ∈ Icc 1 (n / j), oddAF m - ((n / j : ℕ) : ℝ) / 2)| ≤
      L / 2 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Icc 1 n, |k' j * (∑ m ∈ Icc 1 (n / j), oddAF m - ((n / j : ℕ) : ℝ) / 2)|
        ≤ ∑ j ∈ Icc 1 n, |k' j| * (1 / 2) := sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_sum_Icc_oddAF_sub_le _) (abs_nonneg _)
      _ ≤ L / 2 := by rw [← sum_mul]; linarith
  rw [hsplit]
  calc |∑ j ∈ Icc 1 n, k' j * (∑ m ∈ Icc 1 (n / j), oddAF m - ((n / j : ℕ) : ℝ) / 2) +
        (1 / 2) * ∑ j ∈ Icc 1 n, k' j * ((n / j : ℕ) : ℝ)|
      ≤ L / 2 + (1 / 2) * L := by
        refine (abs_add_le _ _).trans (add_le_add hfirst ?_)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact mul_le_mul_of_nonneg_left hmean (by norm_num)
    _ = L := by ring

/-! ### The pole law over the odd squarefree weight -/

/-- **The pole law over `o`.** For `0 < ε ≤ 1/2` and `k` on `[1, J]`, the receiver of `k ⋆ o` is
bounded if and only if `Σ_j k(j) j^{-(1−ε)} = 0`. -/
theorem receiverBounded_dirichletConv_oddSqf_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ↔ poleValue k J ε = 0 := by
  have hD : 0 < RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  constructor
  · intro hB
    by_contra hK
    exact not_receiverBounded_dirichletConv_of_drift hε hε2 (oddSqfWeight_nonneg ε)
      (oddSqfWeight_mem_dampedClass ε) (by positivity) (eventually_oddSqfWeight_drift hε) hkJ hK hB
  · intro hK
    have hfun : RHTower.dirichletConv k (oddSqfWeight ε) =
        RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε)
          (dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) ⇑oddAF) ε) := by
      funext n
      have hk : RHTower.dirichletConv k (oddSqfWeight ε) n = RHTower.dirichletConv k
          (RHTower.dirichletConv (dampedSignWeight ⇑oddSqrtMoebius ε)
            (dampedSignWeight ⇑oddAF ε)) n := by
        unfold RHTower.dirichletConv
        exact sum_congr rfl fun d _ => by rw [oddSqfWeight_eq]; rfl
      rw [hk, dirichletConv_left_comm]
      congr 1
      funext m
      exact dirichletConv_damped_eq k _ ε m
    rw [hfun]
    set L := ∑ j ∈ Icc 1 J, |undampedKernel k ε j|
    have hL : 0 ≤ L := sum_nonneg fun j _ => abs_nonneg _
    -- the sign sequence is bounded by `L`
    have hsign : ∀ d, |RHTower.dirichletConv (undampedKernel k ε) ⇑oddAF d| ≤ L := fun d => by
      unfold RHTower.dirichletConv
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j ∈ d.divisors, |undampedKernel k ε j * oddAF (d / j)| ≤
            ∑ j ∈ d.divisors.filter (· ≤ J), |undampedKernel k ε j| := by
            rw [sum_filter]
            refine sum_le_sum fun j _ => ?_
            split_ifs with hj
            · rw [abs_mul]
              exact mul_le_of_le_one_right (abs_nonneg _) (by
                rw [oddAF_apply]; split_ifs <;> norm_num)
            · rw [undampedKernel_support hkJ ε j (by omega), zero_mul, abs_zero]
        _ ≤ L := sum_le_sum_of_subset_of_nonneg (fun j hj => by
              obtain ⟨hjd, hjJ⟩ := mem_filter.mp hj
              exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hjd, hjJ⟩) fun _ _ _ => abs_nonneg _
    have hs : Summable (fun d : ℕ =>
        |dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) ⇑oddAF) ε d / d|) := by
      refine ((Real.summable_nat_rpow.mpr (show -(1 + ε) < -1 by linarith)).mul_left L).of_nonneg_of_le
        (fun _ => abs_nonneg _) fun d => ?_
      rw [dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _),
        mul_comm]
      exact mul_le_mul_of_nonneg_right (hsign d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    exact receiverBounded_dirichletConv (criticalWiener_dampedOddSqrtMoebius hε) hs
      (exists_weightPronicEnergy_dampedSign_le hL hε (abs_sum_range_dirichletConv_oddAF_le hkJ hK))

/-! ### The two-point even-flip pairs -/

/-- The two-point kernel `αδ₁ + βδ₂`. -/
def twoPointKernel (α β : ℝ) (j : ℕ) : ℝ := if j = 1 then α else if j = 2 then β else 0

theorem twoPointKernel_support (α β : ℝ) :
    ∀ j, 2 < j → twoPointKernel α β j = 0 := fun j hj => by
  simp [twoPointKernel, show j ≠ 1 by omega, show j ≠ 2 by omega]

theorem poleValue_twoPointKernel (α β ε : ℝ) :
    poleValue (twoPointKernel α β) 2 ε = α + β * (2 : ℝ) ^ (ε - 1) := by
  rw [poleValue, show Icc 1 2 = ({1, 2} : Finset ℕ) by decide, sum_pair (by norm_num)]
  simp [twoPointKernel, show -(1 - ε) = ε - 1 by ring]

theorem dirichletConv_twoPointKernel_apply (α β ε : ℝ) {n : ℕ} (hn : n ≠ 0) :
    RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε) n =
      α * oddSqfWeight ε n + if 2 ∣ n then β * oddSqfWeight ε (n / 2) else 0 := by
  rw [dirichletConv_twoPoint (fun j h1 h2 => by simp [twoPointKernel, h1, h2]) _ hn]
  simp [twoPointKernel]

theorem dirichletConv_twoPointKernel_of_four_dvd (α β ε : ℝ) {n : ℕ} (h4 : 4 ∣ n) :
    RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε) n = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [RHTower.dirichletConv]
  have h2 : 2 ∣ n := Nat.dvd_trans (by norm_num) h4
  have h2' : 2 ∣ n / 2 := by omega
  rw [dirichletConv_twoPointKernel_apply α β ε hn, if_pos h2, oddSqfWeight_of_even h2,
    oddSqfWeight_of_even h2']
  ring

/-- **The even flip on two-point kernels is `(α, β) ↦ (α + β, −β)`.** -/
theorem dirichletConv_twoPointKernel_evenFlip (α β ε : ℝ) :
    RHTower.dirichletConv (twoPointKernel (α + β) (-β)) (oddSqfWeight ε) = fun d =>
      RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε) d +
        localFactorWeight (evenPartWeight
          (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε))) 2 2 d := by
  set c := RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)
  funext d
  rcases eq_or_ne d 0 with rfl | hd
  · simp [c, RHTower.dirichletConv, localFactorWeight, evenPartWeight]
  rw [dirichletConv_twoPointKernel_apply _ _ ε hd]
  simp only [c, localFactorWeight, evenPartWeight]
  rw [dirichletConv_twoPointKernel_apply α β ε hd]
  by_cases h2 : 2 ∣ d
  · have hodd : ¬ d % 2 = 1 := by omega
    simp only [h2, hodd, ↓reduceIte, oddSqfWeight_of_even h2]
    by_cases he : (d / 2) % 2 = 1
    · rw [if_pos he, Nat.mul_div_cancel' h2, dirichletConv_twoPointKernel_apply α β ε hd, if_pos h2,
        oddSqfWeight_of_even h2]
      ring
    · have h2' : 2 ∣ d / 2 := by omega
      rw [if_neg he, oddSqfWeight_of_even h2']
      ring
  · have hodd : d % 2 = 1 := by omega
    have h2d : 2 ∣ 2 * d := dvd_mul_right 2 d
    simp only [h2, hodd, ↓reduceIte]
    rw [dirichletConv_twoPointKernel_apply α β ε (by omega : 2 * d ≠ 0), if_pos h2d,
      oddSqfWeight_of_even h2d, Nat.mul_div_cancel_left d two_pos]
    ring

theorem dirichletConv_twoPointKernel_mem_dampedClass (α β : ℝ) {ε : ℝ} (hε1 : ε ≤ 1) :
    DampedClass (|α| + 2 * |β|) ε (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)) :=
  fun n => by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [RHTower.dirichletConv]; positivity
  rw [dirichletConv_twoPointKernel_apply α β ε hn]
  have hP : 0 ≤ (n : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have ho := oddSqfWeight_le ε n
  have ho0 := oddSqfWeight_nonneg ε n
  split_ifs with h2
  · rw [oddSqfWeight_of_even h2, mul_zero, zero_add, abs_mul,
      abs_of_nonneg (oddSqfWeight_nonneg ε _)]
    have hhalf : oddSqfWeight ε (n / 2) ≤ 2 * (n : ℝ) ^ (-ε) := by
      refine (oddSqfWeight_le ε _).trans ?_
      rw [Nat.cast_div h2 (by norm_num), Nat.cast_ofNat,
        Real.div_rpow (Nat.cast_nonneg n) (by norm_num), div_eq_mul_inv, ← Real.rpow_neg two_pos.le,
        neg_neg, mul_comm]
      have h2ε : (2 : ℝ) ^ ε ≤ 2 := by
        calc (2 : ℝ) ^ ε ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
          _ = 2 := Real.rpow_one 2
      exact mul_le_mul_of_nonneg_right h2ε hP
    calc |β| * oddSqfWeight ε (n / 2) ≤ |β| * (2 * (n : ℝ) ^ (-ε)) :=
          mul_le_mul_of_nonneg_left hhalf (abs_nonneg _)
      _ ≤ (|α| + 2 * |β|) * (n : ℝ) ^ (-ε) := by nlinarith [abs_nonneg α, abs_nonneg β]
  · rw [add_zero, abs_mul, abs_of_nonneg ho0]
    calc |α| * oddSqfWeight ε n ≤ |α| * (n : ℝ) ^ (-ε) := mul_le_mul_of_nonneg_left ho (abs_nonneg _)
      _ ≤ (|α| + 2 * |β|) * (n : ℝ) ^ (-ε) := by nlinarith [abs_nonneg α, abs_nonneg β]

/-- **The two-point even-flip pairs are classified at the pole.** For `0 < ε ≤ 1/2` and the
pair `c = (αδ₁ + βδ₂) ⋆ o`, `c^♭ = ((α + β)δ₁ − βδ₂) ⋆ o`: `c^♭` is the even flip of `c`, the two
have the same Ramanujan amplitudes, `c` is paid iff `α + 2^{ε−1}β = 0`, `c^♭` is paid iff
`α + (1 − 2^{ε−1})β = 0`, and both are paid only for `α = β = 0`. -/
theorem twoPoint_evenFlip_classification {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (α β : ℝ) :
    RHTower.dirichletConv (twoPointKernel (α + β) (-β)) (oddSqfWeight ε) = (fun d =>
      RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε) d +
        localFactorWeight (evenPartWeight
          (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε))) 2 2 d) ∧
    (∀ e, |weightRamanujanCoeff (RHTower.dirichletConv (twoPointKernel (α + β) (-β))
        (oddSqfWeight ε)) e| =
      |weightRamanujanCoeff (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)) e|) ∧
    (ReceiverBounded (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)) ↔
      α + β * (2 : ℝ) ^ (ε - 1) = 0) ∧
    (ReceiverBounded (RHTower.dirichletConv (twoPointKernel (α + β) (-β)) (oddSqfWeight ε)) ↔
      α + β * (1 - (2 : ℝ) ^ (ε - 1)) = 0) ∧
    (ReceiverBounded (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)) →
      ReceiverBounded (RHTower.dirichletConv (twoPointKernel (α + β) (-β)) (oddSqfWeight ε)) →
      α = 0 ∧ β = 0) := by
  have hflip := dirichletConv_twoPointKernel_evenFlip α β ε
  have hiff := receiverBounded_dirichletConv_oddSqf_iff hε hε2 (twoPointKernel_support α β)
  have hiff' := receiverBounded_dirichletConv_oddSqf_iff hε hε2 (twoPointKernel_support (α + β) (-β))
  rw [poleValue_twoPointKernel] at hiff hiff'
  have hiff'' : ReceiverBounded (RHTower.dirichletConv (twoPointKernel (α + β) (-β))
      (oddSqfWeight ε)) ↔ α + β * (1 - (2 : ℝ) ^ (ε - 1)) = 0 := by
    rw [hiff']; constructor <;> intro h <;> linarith
  refine ⟨hflip, fun e => ?_, hiff, hiff'', fun h1 h2 => ?_⟩
  · rw [hflip, weightRamanujanCoeff_evenFlip hε
      (dirichletConv_twoPointKernel_mem_dampedClass α β (by linarith))
      (fun m h => dirichletConv_twoPointKernel_of_four_dvd α β ε h) e, abs_mul]
    unfold evenSign
    split_ifs <;> simp
  · have e1 := hiff.mp h1
    have e2 := hiff''.mp h2
    have hpow : (2 : ℝ) ^ (ε - 1) ≠ 1 / 2 := by
      intro h
      have : (2 : ℝ) ^ (ε - 1) > (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at this
      linarith
    have hβ : β * (1 - 2 * (2 : ℝ) ^ (ε - 1)) = 0 := by linarith
    have hβ0 : β = 0 := by
      rcases mul_eq_zero.mp hβ with h | h
      · exact h
      · exact absurd (by linarith : (2 : ℝ) ^ (ε - 1) = 1 / 2) hpow
    exact ⟨by rw [hβ0] at e1; linarith, hβ0⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
