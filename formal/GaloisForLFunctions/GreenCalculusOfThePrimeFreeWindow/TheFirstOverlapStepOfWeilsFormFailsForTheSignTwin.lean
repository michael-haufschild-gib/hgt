import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheGroundEnergyOfAnApertureIsTheFloorOfWeilsFormOnTheWindowsInsideIt
import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheSliverBlocksOfTheGreenMatrixHaveALogarithmicDiagonalAndBulkDipoleCoupling
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity

/-!
# The first overlap step of Weil's form fails for the sign twin

The pencil of the prime two is Weil's form with the contact of two weighted by `w`:

  `𝔚_w = 𝔚 + (1 − w) C₂`,

`C₂` the form of the graph of the floor map of two on step packets, `2 (log 2/√2) ∫ f(u) f(u + log 2)`
on packets, `2 log 2 Σ c_m c_{2m}` on combs. `w = 1` is `ζ`; `w = −1` is its sign twin, with the
same jets and the same sizes of contacts.

* **The step packets of an aperture see the weight** (`pencilWeilForm_ge_of_stepFloor`,
  `exists_stepPacket_pencil_lt`): for every `w`, a floor of `𝔚_w` on the step packets of the
  windows inside the aperture `A`, at every block size, is a floor of `𝔚_w` on the `C²` tests of
  every aperture `A' < A`. A test of `𝔚_w` below a level gives a window inside `A`, a block size
  and a step packet below it.
* **The sign twin** (`exists_firstStep_window_signTwin_lt`): for every cutoff `Q ≥ 2` and every
  reweighting of the contacts with the weight `−1` at two, some window `(R, R + J]` of ratio at
  most `10609/5000`, at some block size, carries a step packet `σ` with
  `Σ σ_j σ_l W_ω(R + j, R + l) < −(1/1000) Σ σ_j²`.

On the same windows Weil's form of `ζ` is at least `(1/50000) Σ σ_j²`. The first overlap step in
the normal form of Weil's form therefore fails for the sign twin: a proof of it must use the sign
of the contact of two.

The transfer runs through the comb as for `w = 1`. The contact of two is a bounded form on the
comb (`abs_doubleContact_add_sub_le`), so the block averages carry it up to the mass of the rest;
on block functions of even block size it is exactly the graph of the floor map of two
(`two_log_two_mul_doubleContact_blockFunction`): half of a block is doubled into the block
`2(R + j)`, the other half into the next one; on the samples of a packet it is a Riemann sum of
`∫ f(u) f(u + log 2)` (`tendsto_doubleContact_sample`). The witness is the odd test of the
aperture `181/500` on which the Liouville twist of Weil's functional is negative.

The statement concerns Weil's form of the twin. Its neutral part differs by the pole plane, and
a second bound state of the twin inside the first step is not decided here.
-/

open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.HodgeTheoryOfAFixedPart (blockIndex blockMean sampleCoord crossConstant
  chebyshev)
open GaloisForLFunctions.SquareRootThreshold (liouvilleTwistedVonMangoldt)
open _root_.Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ### The contact of ratio two on a comb -/

/-- The contacts of ratio two of a divisor on a comb: the pairs `(m, 2m)` inside `S`. -/
def doubleContact (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ m ∈ S, if 2 * m ∈ S then c m * c (2 * m) else 0

/-- Doubling is injective: a nonnegative sum over the doubles inside `S` is at most the sum
over `S`. -/
theorem sum_ite_double_le (S : Finset ℕ) {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) :
    ∑ m ∈ S, (if 2 * m ∈ S then g (2 * m) else 0) ≤ ∑ n ∈ S, g n := by
  rw [← Finset.sum_filter]
  calc ∑ m ∈ S.filter (fun m => 2 * m ∈ S), g (2 * m)
      = ∑ n ∈ (S.filter fun m => 2 * m ∈ S).image (fun m => 2 * m), g n :=
        (Finset.sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm
    _ ≤ ∑ n ∈ S, g n :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
          exact (Finset.mem_filter.mp hm).2) fun n _ _ => hg n

/-- **The contact of two is a bounded form on the comb.** Adding `z` to a divisor `s` changes
the contact by at most `p Σ s_n² + (q + 1) Σ z_n²`, for all weights `p q = 1`. -/
theorem abs_doubleContact_add_sub_le (S : Finset ℕ) (s z : ℕ → ℝ) {p q : ℝ} (hp : 0 < p)
    (hq : 0 < q) (hpq : p * q = 1) :
    |doubleContact S (fun n => s n + z n) - doubleContact S s| ≤
      p * ∑ n ∈ S, s n ^ 2 + (q + 1) * ∑ n ∈ S, z n ^ 2 := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ n, g n = p / 2 * s n ^ 2 + (q / 2 + 1 / 2) * z n ^ 2 :=
    ⟨fun n => p / 2 * s n ^ 2 + (q / 2 + 1 / 2) * z n ^ 2, fun _ => rfl⟩
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    rw [hg]
    exact add_nonneg (mul_nonneg (half_pos hp).le (sq_nonneg _))
      (mul_nonneg (by linarith) (sq_nonneg _))
  -- `|ab| ≤ (p/2) a² + (q/2) b²`
  have key : ∀ a b : ℝ, |a * b| ≤ p / 2 * a ^ 2 + q / 2 * b ^ 2 := fun a b => by
    have h1 : q / 2 * (p * a - b) ^ 2 =
        p * q * (p / 2 * a ^ 2) - p * q * (a * b) + q / 2 * b ^ 2 := by ring
    have h2 : q / 2 * (p * a + b) ^ 2 =
        p * q * (p / 2 * a ^ 2) + p * q * (a * b) + q / 2 * b ^ 2 := by ring
    rw [hpq, one_mul, one_mul] at h1 h2
    have h3 := mul_nonneg (half_pos hq).le (sq_nonneg (p * a - b))
    have h4 := mul_nonneg (half_pos hq).le (sq_nonneg (p * a + b))
    rw [abs_le]
    constructor <;> linarith
  have key1 : ∀ a b : ℝ, |a * b| ≤ 1 / 2 * a ^ 2 + 1 / 2 * b ^ 2 := fun a b => by
    rw [abs_le]
    constructor <;> nlinarith only [sq_nonneg (a - b), sq_nonneg (a + b)]
  have hterm : ∀ m ∈ S,
      |(if 2 * m ∈ S then (s m + z m) * (s (2 * m) + z (2 * m)) else 0) -
        (if 2 * m ∈ S then s m * s (2 * m) else 0)| ≤
      g m + if 2 * m ∈ S then g (2 * m) else 0 := by
    intro m _
    split_ifs with h
    · have e : (s m + z m) * (s (2 * m) + z (2 * m)) - s m * s (2 * m) =
          s m * z (2 * m) + s (2 * m) * z m + z m * z (2 * m) := by ring
      have h1 := key (s m) (z (2 * m))
      have h2 := key (s (2 * m)) (z m)
      have h3 := key1 (z m) (z (2 * m))
      have h4 := abs_add_three (s m * z (2 * m)) (s (2 * m) * z m) (z m * z (2 * m))
      rw [e, hg m, hg (2 * m)]
      linarith
    · rw [sub_zero, abs_zero, add_zero]
      exact hg0 m
  show |∑ m ∈ S, (if 2 * m ∈ S then (s m + z m) * (s (2 * m) + z (2 * m)) else 0) -
      ∑ m ∈ S, (if 2 * m ∈ S then s m * s (2 * m) else 0)| ≤ _
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib]
  have h2 := sum_ite_double_le S hg0
  have h1 : ∑ n ∈ S, g n = p / 2 * ∑ n ∈ S, s n ^ 2 + (q / 2 + 1 / 2) * ∑ n ∈ S, z n ^ 2 := by
    rw [Finset.sum_congr rfl fun n _ => hg n, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
  linarith

/-- The contact of two of a divisor supported in a window is the contact on the window. -/
theorem doubleContact_of_subset {W S : Finset ℕ} {c : ℕ → ℝ} (hWS : W ⊆ S)
    (h0 : ∀ n ∈ S, n ∉ W → c n = 0) : doubleContact S c = doubleContact W c := by
  have h1 : ∑ m ∈ W, (if 2 * m ∈ S then c m * c (2 * m) else 0) =
      ∑ m ∈ S, (if 2 * m ∈ S then c m * c (2 * m) else 0) :=
    Finset.sum_subset hWS fun m hm hmW => by rw [h0 m hm hmW, zero_mul, ite_self]
  unfold doubleContact
  rw [← h1]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h2 : 2 * m ∈ W
  · rw [if_pos h2, if_pos (hWS h2)]
  · rw [if_neg h2]
    by_cases h3 : 2 * m ∈ S
    · rw [if_pos h3, h0 _ h3 h2, mul_zero]
    · rw [if_neg h3]

/-! ### Block functions: the graph of the floor map of two -/

/-- A point of the block `l` lies in the window iff `l < J`. -/
theorem blockPoint_mem_iff {B : ℕ} (N J l : ℕ) {a : ℕ} (ha : a < B) :
    N + 1 + B * l + a ∈ Ioc N (N + B * J) ↔ l < J := by
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨-, h⟩
    by_contra hl
    have h1 : B * J ≤ B * l := Nat.mul_le_mul_left B (not_lt.mp hl)
    omega
  · intro hl
    have h1 : B * (l + 1) ≤ B * J := Nat.mul_le_mul_left B hl
    have h2 : B * (l + 1) = B * l + B := by ring
    omega

/-- The contact of a point of the block `j` whose double lies in the block `l`. -/
theorem doubleTerm_blockFunction {B : ℕ} (hB : 0 < B) (N J : ℕ) (σ : ℕ → ℝ) {j l a a' : ℕ}
    (ha : a < B) (ha' : a' < B) (h2m : 2 * (N + 1 + B * j + a) = N + 1 + B * l + a') :
    (if 2 * (N + 1 + B * j + a) ∈ Ioc N (N + B * J) then
        σ (blockIndex N B (N + 1 + B * j + a)) * σ (blockIndex N B (2 * (N + 1 + B * j + a)))
      else 0) = σ j * if l < J then σ l else 0 := by
  rw [h2m, HodgeTheoryOfAFixedPart.blockIndex_add hB N j ha,
    HodgeTheoryOfAFixedPart.blockIndex_add hB N l ha']
  by_cases hl : l < J
  · rw [if_pos ((blockPoint_mem_iff N J l ha').mpr hl), if_pos hl]
  · rw [if_neg fun h => hl ((blockPoint_mem_iff N J l ha').mp h), if_neg hl, mul_zero]

/-- **The contact of two on a block function of even block size.** The first half of the block
`R + j` is doubled into the block `2(R + j)`, the second half into the block `2(R + j) + 1`. -/
theorem doubleContact_blockFunction {R b B N : ℕ} (hb : 1 ≤ b) (hB : B = 2 * b)
    (hN : N = R * B) (J : ℕ) (σ : ℕ → ℝ) :
    doubleContact (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) =
      b * ∑ j ∈ range J, σ j * ((if R + 2 * j < J then σ (R + 2 * j) else 0) +
        if R + 2 * j + 1 < J then σ (R + 2 * j + 1) else 0) := by
  have hB0 : 0 < B := by omega
  have hsplit : ∀ G : ℕ → ℝ,
      ∑ a ∈ range B, G a = ∑ a ∈ range b, G a + ∑ a ∈ range b, G (b + a) := fun G => by
    rw [hB, two_mul, Finset.sum_range_add]
  show ∑ m ∈ Ioc N (N + B * J), (if 2 * m ∈ Ioc N (N + B * J) then
      σ (blockIndex N B m) * σ (blockIndex N B (2 * m)) else 0) = _
  rw [HodgeTheoryOfAFixedPart.sum_Ioc_blocks, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsplit]
  have h1 : ∀ a ∈ range b, (if 2 * (N + 1 + B * j + a) ∈ Ioc N (N + B * J) then
      σ (blockIndex N B (N + 1 + B * j + a)) * σ (blockIndex N B (2 * (N + 1 + B * j + a)))
      else 0) = σ j * if R + 2 * j < J then σ (R + 2 * j) else 0 := fun a ha => by
    have ha' := Finset.mem_range.mp ha
    exact doubleTerm_blockFunction hB0 N J σ (a' := 2 * a + 1) (by omega) (by omega)
      (by rw [hN]; ring)
  have h2 : ∀ a ∈ range b, (if 2 * (N + 1 + B * j + (b + a)) ∈ Ioc N (N + B * J) then
      σ (blockIndex N B (N + 1 + B * j + (b + a))) *
        σ (blockIndex N B (2 * (N + 1 + B * j + (b + a)))) else 0) =
      σ j * if R + 2 * j + 1 < J then σ (R + 2 * j + 1) else 0 := fun a ha => by
    have ha' := Finset.mem_range.mp ha
    exact doubleTerm_blockFunction hB0 N J σ (a' := 2 * a + 1) (by omega) (by omega)
      (by rw [hN, hB]; ring)
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- The graph of the floor map of two joins a block to its two doubles. -/
theorem floorGraph_two_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    floorGraph 2 a b = (if b / 2 = a then Real.log 2 / 2 else 0) +
      if a / 2 = b then Real.log 2 / 2 else 0 := by
  have hΛ : (Λ 2 : ℝ) / ((2 : ℕ) : ℝ) = Real.log 2 / 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rcases le_total a b with h | h
  · rw [floorGraph_of_le 2 h, hΛ, if_neg (show ¬a / 2 = b by omega), add_zero]
  · rw [floorGraph_comm, floorGraph_of_le 2 h, hΛ, if_neg (show ¬b / 2 = a by omega), zero_add]

/-- **The form of the graph of the floor map of two on a window.** -/
theorem sum_sum_floorGraph_two {R : ℕ} (hR : 1 ≤ R) (J : ℕ) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph 2 (R + j) (R + l) =
      Real.log 2 * ∑ j ∈ range J, σ j * ((if R + 2 * j < J then σ (R + 2 * j) else 0) +
        if R + 2 * j + 1 < J then σ (R + 2 * j + 1) else 0) := by
  have hpt : ∀ j l : ℕ, σ j * σ l * floorGraph 2 (R + j) (R + l) =
      σ j * σ l * (if (R + l) / 2 = R + j then Real.log 2 / 2 else 0) +
        σ l * σ j * (if (R + j) / 2 = R + l then Real.log 2 / 2 else 0) := fun j l => by
    rw [floorGraph_two_eq (by omega) (by omega)]
    ring
  -- a row: the two doubles of the block `R + j`
  have hrow : ∀ j : ℕ,
      ∑ l ∈ range J, σ j * σ l * (if (R + l) / 2 = R + j then Real.log 2 / 2 else 0) =
        Real.log 2 / 2 * (σ j * ((if R + 2 * j < J then σ (R + 2 * j) else 0) +
          if R + 2 * j + 1 < J then σ (R + 2 * j + 1) else 0)) := fun j => by
    have hpt' : ∀ l ∈ range J,
        σ j * σ l * (if (R + l) / 2 = R + j then Real.log 2 / 2 else 0) =
          (if l = R + 2 * j then σ j * σ l * (Real.log 2 / 2) else 0) +
            if l = R + 2 * j + 1 then σ j * σ l * (Real.log 2 / 2) else 0 := fun l _ => by
      by_cases h1 : l = R + 2 * j
      · rw [if_pos (show (R + l) / 2 = R + j by omega), if_pos h1,
          if_neg (show ¬l = R + 2 * j + 1 by omega), add_zero]
      · by_cases h2 : l = R + 2 * j + 1
        · rw [if_pos (show (R + l) / 2 = R + j by omega), if_neg h1, if_pos h2, zero_add]
        · rw [if_neg (show ¬(R + l) / 2 = R + j by omega), if_neg h1, if_neg h2, mul_zero,
            add_zero]
    rw [Finset.sum_congr rfl hpt', Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    split_ifs <;> ring
  have hswap : ∑ j ∈ range J, ∑ l ∈ range J,
        σ l * σ j * (if (R + j) / 2 = R + l then Real.log 2 / 2 else 0) =
      ∑ j ∈ range J, ∑ l ∈ range J,
        σ j * σ l * (if (R + l) / 2 = R + j then Real.log 2 / 2 else 0) :=
    Finset.sum_comm
  calc ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph 2 (R + j) (R + l)
      = ∑ j ∈ range J, ∑ l ∈ range J,
            σ j * σ l * (if (R + l) / 2 = R + j then Real.log 2 / 2 else 0) +
          ∑ j ∈ range J, ∑ l ∈ range J,
            σ l * σ j * (if (R + j) / 2 = R + l then Real.log 2 / 2 else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => hpt j l
    _ = Real.log 2 * ∑ j ∈ range J, σ j * ((if R + 2 * j < J then σ (R + 2 * j) else 0) +
          if R + 2 * j + 1 < J then σ (R + 2 * j + 1) else 0) := by
        rw [hswap, Finset.sum_congr rfl fun j _ => hrow j, ← Finset.mul_sum]
        ring

/-- **On block functions of even block size the contact of two is the graph of the floor map
of two**, times the block size. -/
theorem two_log_two_mul_doubleContact_blockFunction {R b : ℕ} (hR : 1 ≤ R) (hb : 1 ≤ b)
    (J : ℕ) (σ : ℕ → ℝ) :
    2 * Real.log 2 * doubleContact (Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J))
        (fun n => σ (blockIndex (R * (2 * b)) (2 * b) n)) =
      ((2 * b : ℕ) : ℝ) *
        ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph 2 (R + j) (R + l) := by
  rw [doubleContact_blockFunction hb rfl rfl J σ, sum_sum_floorGraph_two hR J σ]
  push_cast
  ring

/-! ### The pencil of the prime two -/

/-- Weil's form on the step packets of `(R, R + J]` with the contact of two weighted by `w`:
`w = 1` is Weil's form, `w = −1` the sign twin. -/
def pencilStepForm (w : ℝ) (Q R J : ℕ) (σ : ℕ → ℝ) : ℝ :=
  packetForm Q (stepPacket R J σ) +
    (1 - w) * ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph 2 (R + j) (R + l)

/-- Weil's form on a comb with the contact of two weighted by `w`. -/
def pencilCombForm (w : ℝ) (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  HodgeTheoryOfAFixedPart.combForm S c + (1 - w) * (2 * Real.log 2 * doubleContact S c)

/-- The sum over the zeros of a packet with the contact of two weighted by `w`. -/
def pencilWeilForm (w : ℝ) (f : ℝ → ℝ) : ℝ :=
  zeroSum f + (1 - w) * (2 * (contactWeight 2 * packetAutocorr f (Real.log 2)))

theorem pencilStepForm_one (Q R J : ℕ) (σ : ℕ → ℝ) :
    pencilStepForm 1 Q R J σ = packetForm Q (stepPacket R J σ) := by
  rw [pencilStepForm, sub_self, zero_mul, add_zero]

theorem contactWeight_two : contactWeight 2 = Real.log 2 / Real.sqrt 2 := by
  rw [contactWeight, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- No floor map of `k ≥ 3` acts on a window of ratio at most three. -/
theorem sum_sum_floorGraph_eq_zero {R J k : ℕ} (hJ : R + J ≤ 3 * R) (hk : 3 ≤ k) (σ : ℕ → ℝ) :
    ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * floorGraph k (R + j) (R + l) = 0 :=
  Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun l hl => by
    have hj' := Finset.mem_range.mp hj
    have hl' := Finset.mem_range.mp hl
    rw [floorGraph_eq_zero_of_lt_three_mul hk (by omega), mul_zero]

/-- **In a window of ratio at most three Weil's form does not depend on the cutoff `Q ≥ 2`.** -/
theorem packetForm_stepPacket_eq_two {R J : ℕ} (hR : 1 ≤ R) (hJ : R + J ≤ 3 * R) {Q : ℕ}
    (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    packetForm Q (stepPacket R J σ) = packetForm 2 (stepPacket R J σ) := by
  induction Q, hQ using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    have h := packetForm_pred_sub (k := n + 1) (by omega) (stepPacket R J σ)
    rw [Nat.add_sub_cancel, contact_stepPacket_eq_sum_floorGraph hR (by omega) J σ,
      sum_sum_floorGraph_eq_zero hJ (by omega) σ] at h
    linarith

/-- **In a window of ratio at most three a reweighting of the contacts is the pencil at its
weight of the prime two.** -/
theorem reweightedPacketForm_stepPacket_eq_pencilStepForm {R J Q : ℕ} (hR : 1 ≤ R)
    (hJ : R + J ≤ 3 * R) (hQ : 2 ≤ Q) (ω : ℕ → ℝ) (σ : ℕ → ℝ) :
    reweightedPacketForm ω Q (stepPacket R J σ) = pencilStepForm (ω 2) Q R J σ := by
  have hsum : ∑ k ∈ Icc 2 Q,
        (1 - ω k) * (contactWeight k * packetAutocorr (stepPacket R J σ) (Real.log k)) =
      (1 - ω 2) *
        (contactWeight 2 * packetAutocorr (stepPacket R J σ) (Real.log ((2 : ℕ) : ℝ))) := by
    refine Finset.sum_eq_single_of_mem 2 (Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩) fun k hk hk2 => ?_
    have hk3 : 3 ≤ k := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    have h := contact_stepPacket_eq_sum_floorGraph hR (k := k) (by omega) J σ
    rw [sum_sum_floorGraph_eq_zero hJ hk3 σ] at h
    have h1 : contactWeight k * packetAutocorr (stepPacket R J σ) (Real.log k) = 0 := by
      linarith
    rw [h1, mul_zero]
  rw [reweightedPacketForm, hsum, pencilStepForm,
    ← contact_stepPacket_eq_sum_floorGraph hR (k := 2) le_rfl J σ]
  ring

/-! ### From the step packets of a window to its comb -/

/-- **A floor of the pencil on the step packets of a window is a floor on the block functions of
its comb**, at all large even block sizes and up to any `η > 0`. -/
theorem eventually_pencilCombForm_blockFunction_ge {R J Q : ℕ} (hR : 1 ≤ R)
    (hQ : R + J ≤ Q * R) (w : ℝ) {c η : ℝ} (hη : 0 < η)
    (hc : ∀ σ : ℕ → ℝ, c * ∑ j ∈ range J, σ j ^ 2 ≤ pencilStepForm w Q R J σ) :
    ∀ᶠ b : ℕ in atTop, ∀ σ : ℕ → ℝ,
      (c - η) * ∑ n ∈ Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J),
          σ (blockIndex (R * (2 * b)) (2 * b) n) ^ 2 ≤
        pencilCombForm w (Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J))
          fun n => σ (blockIndex (R * (2 * b)) (2 * b) n) := by
  have htend : Tendsto (fun b : ℕ => 2 * b) atTop atTop :=
    tendsto_atTop_mono (fun b => Nat.le_mul_of_pos_left b (by norm_num)) tendsto_id
  filter_upwards [htend.eventually
      (HodgeTheoryOfAFixedPart.eventually_packetForm_stepPacket_le_combForm hR hQ hη),
    eventually_ge_atTop 1] with b hb hb1 σ
  have h : ((2 * b : ℕ) : ℝ) * packetForm Q (stepPacket R J σ) ≤
      HodgeTheoryOfAFixedPart.combForm (Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J))
          (fun n => σ (blockIndex (R * (2 * b)) (2 * b) n)) +
        η * ∑ n ∈ Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J),
          σ (blockIndex (R * (2 * b)) (2 * b) n) ^ 2 := hb σ
  rw [sum_blockFunction_sq (by omega) σ] at h ⊢
  have hm := mul_le_mul_of_nonneg_left (hc σ)
    (Nat.cast_nonneg (2 * b) : (0 : ℝ) ≤ ((2 * b : ℕ) : ℝ))
  rw [pencilStepForm] at hm
  rw [pencilCombForm, two_log_two_mul_doubleContact_blockFunction hR hb1 J σ]
  nlinarith only [h, hm]

/-- The arithmetic of the residual: the block averages carry the floor, the counterterm pays the
rest of the divisor and the change of the contact of two. -/
theorem pencil_residual_bound {c η w M Z Cm Cd Dm Dd : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (hZ : 0 ≤ Z)
    (h1 : Cm - η * M + (|c| + |1 - w| * (2 * Real.log 2) *
      ((|1 - w| * (2 * Real.log 2) + 1) / η + 1)) * Z ≤ Cd)
    (h2 : (c - η) * M ≤ Cm + (1 - w) * (2 * Real.log 2 * Dm))
    (h3 : |Dd - Dm| ≤ η / (|1 - w| * (2 * Real.log 2) + 1) * M +
      ((|1 - w| * (2 * Real.log 2) + 1) / η + 1) * Z) :
    (c - 3 * η) * (M + Z) ≤ Cd + (1 - w) * (2 * Real.log 2 * Dd) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = |1 - w| * (2 * Real.log 2) := ⟨_, rfl⟩
  have hΔ : -(s * |Dd - Dm|) ≤
      (1 - w) * (2 * Real.log 2 * Dd) - (1 - w) * (2 * Real.log 2 * Dm) := by
    have e : (1 - w) * (2 * Real.log 2 * Dd) - (1 - w) * (2 * Real.log 2 * Dm) =
        (1 - w) * (2 * Real.log 2) * (Dd - Dm) := by ring
    have h := neg_abs_le ((1 - w) * (2 * Real.log 2) * (Dd - Dm))
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.log 2), ← hs] at h
    rw [e]
    exact h
  rw [← hs] at h1 h3
  have hs0 : 0 ≤ s := by
    rw [hs]
    exact mul_nonneg (abs_nonneg _) (by linarith)
  have hsΔ := mul_le_mul_of_nonneg_left h3 hs0
  have hsp : s * (η / (s + 1)) ≤ η := by
    have e : s * (η / (s + 1)) = η * (s / (s + 1)) := by ring
    rw [e]
    exact mul_le_of_le_one_right hη.le ((div_le_one (by linarith)).mpr (by linarith))
  have hspM := mul_le_mul_of_nonneg_right hsp hM
  have hcZ := mul_nonneg (show (0 : ℝ) ≤ |c| - c + 3 * η by linarith [le_abs_self c]) hZ
  nlinarith only [h1, h2, hΔ, hsΔ, hspM, hcZ]

/-- **A floor of the pencil on the step packets of a window is a floor on every divisor of its
comb**, at all large even block sizes and up to `3η`, once the window starts after `R` blocks
with `log R` above a constant of `Q`, `c`, `w`, `η`. -/
theorem eventually_pencilCombForm_ge_of_stepPacket_floor {R J Q : ℕ} (hR : 1 ≤ R)
    (hQ : R + J ≤ Q * R) (w : ℝ) {c η : ℝ} (hη : 0 < η)
    (hRlarge : crossConstant Q ^ 2 / η + (|c| + |1 - w| * (2 * Real.log 2) *
        ((|1 - w| * (2 * Real.log 2) + 1) / η + 1)) ≤
      Real.log R - (3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi)))
    (hc : ∀ σ : ℕ → ℝ, c * ∑ j ∈ range J, σ j ^ 2 ≤ pencilStepForm w Q R J σ) :
    ∀ᶠ b : ℕ in atTop, ∀ d : ℕ → ℝ,
      (c - 3 * η) * ∑ n ∈ Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J), d n ^ 2 ≤
        pencilCombForm w (Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J)) d := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs1 : 0 < |1 - w| * (2 * Real.log 2) + 1 := by
    have := mul_nonneg (abs_nonneg (1 - w)) (by linarith : (0 : ℝ) ≤ 2 * Real.log 2)
    linarith
  have hp : 0 < η / (|1 - w| * (2 * Real.log 2) + 1) := div_pos hη hs1
  have hq : 0 < (|1 - w| * (2 * Real.log 2) + 1) / η := div_pos hs1 hη
  have hpq : η / (|1 - w| * (2 * Real.log 2) + 1) *
      ((|1 - w| * (2 * Real.log 2) + 1) / η) = 1 := by
    rw [div_mul_div_comm, mul_comm η, div_self (mul_pos hs1 hη).ne']
  filter_upwards [eventually_pencilCombForm_blockFunction_ge hR hQ w hη hc,
    eventually_ge_atTop 1] with b hb hb1 d
  have hBpos : 0 < 2 * b := by omega
  have hBN : 2 * b ≤ R * (2 * b) := Nat.le_mul_of_pos_left (2 * b) hR
  have hQ' : R * (2 * b) + 2 * b * J ≤ Q * (R * (2 * b)) := by
    have h1 : R * (2 * b) + 2 * b * J = (R + J) * (2 * b) := by ring
    have h2 : Q * (R * (2 * b)) = Q * R * (2 * b) := by ring
    rw [h1, h2]
    exact Nat.mul_le_mul_right (2 * b) hQ
  have hdiv : R * (2 * b) / R = 2 * b := Nat.mul_div_cancel_left (2 * b) hR
  have hmargin := HodgeTheoryOfAFixedPart.log_sub_row_ge (N := R * (2 * b)) (M := 2 * b * J)
    (Q := Q) (R := R) hR (Nat.le_mul_of_pos_right R hBpos) hQ'
  rw [hdiv] at hmargin
  have h1 := combForm_ge_blockMean_add_residual hBpos hBN hQ' hη (hRlarge.trans hmargin) d
  have h2 := hb (blockMean (R * (2 * b)) (2 * b) J d)
  have h3 := abs_doubleContact_add_sub_le (Ioc (R * (2 * b)) (R * (2 * b) + 2 * b * J))
    (fun n => blockMean (R * (2 * b)) (2 * b) J d (blockIndex (R * (2 * b)) (2 * b) n))
    (fun n => d n - blockMean (R * (2 * b)) (2 * b) J d (blockIndex (R * (2 * b)) (2 * b) n))
    hp hq hpq
  have he : (fun n => blockMean (R * (2 * b)) (2 * b) J d (blockIndex (R * (2 * b)) (2 * b) n) +
      (d n - blockMean (R * (2 * b)) (2 * b) J d (blockIndex (R * (2 * b)) (2 * b) n))) = d := by
    funext n
    ring
  rw [he] at h3
  rw [pencilCombForm] at h2 ⊢
  rw [HodgeTheoryOfAFixedPart.sum_sq_eq_blockMean_add_residual hBpos (R * (2 * b)) J d]
  exact pencil_residual_bound hη (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) h1 h2 h3

/-! ### From the comb to the smooth packets inside the window -/

/-- A function that vanishes off `[0, b]` has its integral on `[0, b]`. -/
theorem intervalIntegral_eq_integral_of_eq_zero {g : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h0 : ∀ u, u ≤ 0 → g u = 0) (h1 : ∀ u, b < u → g u = 0) :
    ∫ u in (0 : ℝ)..b, g u = ∫ u, g u := by
  rw [intervalIntegral.integral_of_le hb]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with h | h
  · exact h0 u h
  · exact h1 u h

/-- **The contact of two on the samples of a packet** tends to the contact of two of the
packet: the pairs `(m, 2m)` are a Riemann sum of `∫ f(u) f(u + log 2)`. -/
theorem tendsto_doubleContact_sample {f : ℝ → ℝ} (hcont : Continuous f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ =>
        2 * Real.log 2 * doubleContact (Ioc N (N + 3 * K * N)) (sampleCoord f N)) atTop
      (𝓝 (2 * (contactWeight 2 * packetAutocorr f (Real.log 2)))) := by
  have hint : ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)),
      f u * f (u + Real.log ((2 : ℕ) : ℝ)) = packetAutocorr f (Real.log 2) := by
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hK3 : (K : ℝ) ≤ 1 + ((3 * K : ℕ) : ℝ) := by
      push_cast
      linarith
    rw [packetAutocorr, Nat.cast_ofNat]
    exact intervalIntegral_eq_integral_of_eq_zero (Real.log_nonneg (by linarith))
      (fun u hu => by rw [hsupp u (Or.inl (hu.trans h3.le)), zero_mul])
      (fun u hu => by
        rw [hsupp u (Or.inr ((Real.log_le_log hK' hK3).trans hu.le)), zero_mul])
  have hlim : 2 * (Real.log 2 / Real.sqrt 2) * packetAutocorr f (Real.log 2) =
      2 * (contactWeight 2 * packetAutocorr f (Real.log 2)) := by
    rw [contactWeight_two]
    ring
  have h := (tendsto_contactRow hcont (L := 3 * K) (by omega) (k := 2) (by norm_num)).const_mul
    (2 * (Real.log 2 / Real.sqrt 2))
  rw [hint, hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  show 2 * (Real.log 2 / Real.sqrt 2) * ∑ m ∈ Ioc N (N + 3 * K * N),
      degreeSample f N m * degreeSample f N (m * 2) / (m : ℝ) =
    2 * Real.log 2 * ∑ m ∈ Ioc N (N + 3 * K * N),
      (if 2 * m ∈ Ioc N (N + 3 * K * N) then sampleCoord f N m * sampleCoord f N (2 * m)
        else 0)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 := (Finset.mem_Ioc.mp hm).1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [mul_comm m 2]
  by_cases h2 : 2 * m ∈ Ioc N (N + 3 * K * N)
  · have e : (m : ℝ) = Real.sqrt m * Real.sqrt m := (Real.mul_self_sqrt hm0.le).symm
    have e2 : Real.sqrt ((2 * m : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt m := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
    have key : ∀ x y t : ℝ, 2 * (Real.log 2 / Real.sqrt 2) * (x * y / (t * t)) =
        2 * Real.log 2 * (x / t * (y / (Real.sqrt 2 * t))) := fun x y t => by ring
    rw [if_pos h2, sampleCoord, sampleCoord, e2,
      show degreeSample f N m * degreeSample f N (2 * m) / (m : ℝ) =
        degreeSample f N m * degreeSample f N (2 * m) / (Real.sqrt m * Real.sqrt m) by
          rw [← e]]
    exact key _ _ _
  · have hz : degreeSample f N (2 * m) = 0 :=
      HodgeTheoryOfAFixedPart.degreeSample_eq_zero_above hK hsupp hN (by
        rw [Finset.mem_Ioc] at h2
        omega)
    rw [if_neg h2, hz]
    ring

/-- **A floor of the pencil on the combs of a window is a floor of the pencil on the smooth
packets inside it.** -/
theorem mul_integral_sq_le_pencilWeilForm_of_eventually {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K r J : ℕ} (hK : 1 ≤ K) (hr : 1 ≤ r)
    (hJK : 3 * r + J ≤ K * r) (hlow : ∀ u, u ≤ Real.log 3 → f u = 0)
    (hhigh : ∀ u, Real.log (((3 * r + J : ℕ) : ℝ) / r) ≤ u → f u = 0) (w : ℝ) {γ : ℝ}
    (h : ∀ᶠ b : ℕ in atTop, ∀ d : ℕ → ℝ,
      γ * ∑ n ∈ Ioc (3 * r * (2 * b)) (3 * r * (2 * b) + 2 * b * J), d n ^ 2 ≤
        pencilCombForm w (Ioc (3 * r * (2 * b)) (3 * r * (2 * b) + 2 * b * J)) d) :
    γ * (∫ u, f u ^ 2) ≤ pencilWeilForm w f := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hratio0 : (0 : ℝ) < ((3 * r + J : ℕ) : ℝ) / r :=
    div_pos (by exact_mod_cast (by omega : 0 < 3 * r + J)) hr'
  have hratio : ((3 * r + J : ℕ) : ℝ) / r ≤ K := by
    rw [div_le_iff₀ hr']
    exact_mod_cast hJK
  have hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0 := by
    rintro u (hu | hu)
    · exact hlow u hu
    · exact hhigh u ((Real.log_le_log hratio0 hratio).trans hu)
  have htend : Tendsto (fun b : ℕ => r * (2 * b)) atTop atTop :=
    tendsto_atTop_mono (fun b => (Nat.le_mul_of_pos_left b (by norm_num : 0 < 2)).trans
      (Nat.le_mul_of_pos_left (2 * b) hr)) tendsto_id
  have hZ := (HodgeTheoryOfAFixedPart.tendsto_combForm_sample hf hfc hK hsupp).comp htend
  have hD := ((tendsto_doubleContact_sample hf.continuous hK hsupp).comp htend).const_mul
    (1 - w)
  have hI := ((HodgeTheoryOfAFixedPart.tendsto_sum_sq_sampleCoord hf.continuous hK).comp
    htend).const_mul γ
  have hint : ∫ u in (0 : ℝ)..Real.log (1 + ((3 * K : ℕ) : ℝ)), f u ^ 2 = ∫ u, f u ^ 2 := by
    have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have hK3 : (K : ℝ) ≤ 1 + ((3 * K : ℕ) : ℝ) := by
      push_cast
      linarith
    exact intervalIntegral_sq_eq_integral (Real.log_nonneg (by linarith))
      (fun u hu => hlow u (hu.trans h3.le))
      (fun u hu => hsupp u (Or.inr ((Real.log_le_log hK' hK3).trans hu.le)))
  rw [hint] at hI
  unfold pencilWeilForm
  refine le_of_tendsto_of_tendsto hI (hZ.add hD) ?_
  filter_upwards [h, eventually_ge_atTop 1] with b hb hb1
  show γ * ∑ n ∈ Ioc (r * (2 * b)) (r * (2 * b) + 3 * K * (r * (2 * b))),
      sampleCoord f (r * (2 * b)) n ^ 2 ≤
    HodgeTheoryOfAFixedPart.combForm (Ioc (r * (2 * b)) (r * (2 * b) + 3 * K * (r * (2 * b))))
        (sampleCoord f (r * (2 * b))) +
      (1 - w) * (2 * Real.log 2 * doubleContact
        (Ioc (r * (2 * b)) (r * (2 * b) + 3 * K * (r * (2 * b)))) (sampleCoord f (r * (2 * b))))
  have hWS := window_subset_sampleComb hJK (2 * b)
  have h0 : ∀ n ∈ Ioc (r * (2 * b)) (r * (2 * b) + 3 * K * (r * (2 * b))),
      n ∉ Ioc (3 * r * (2 * b)) (3 * r * (2 * b) + 2 * b * J) →
        sampleCoord f (r * (2 * b)) n = 0 :=
    fun n hn hnW => sampleCoord_eq_zero_off_window hr (by omega) hlow hhigh
      (Finset.mem_Ioc.mp hn).1 hnW
  have hmass : ∑ n ∈ Ioc (r * (2 * b)) (r * (2 * b) + 3 * K * (r * (2 * b))),
        sampleCoord f (r * (2 * b)) n ^ 2 =
      ∑ n ∈ Ioc (3 * r * (2 * b)) (3 * r * (2 * b) + 2 * b * J),
        sampleCoord f (r * (2 * b)) n ^ 2 :=
    (Finset.sum_subset hWS fun n hn hnW => by rw [h0 n hn hnW]; ring).symm
  rw [combForm_of_subset hWS h0, doubleContact_of_subset hWS h0, hmass]
  exact hb _

/-! ### The floor of the pencil on the step packets of an aperture -/

/-- The pencil at the weight `w` has the floor `c` on the step packets of the windows inside the
aperture `A`, at every block size. -/
def PencilStepFloor (w : ℝ) (Q : ℕ) (A c : ℝ) : Prop :=
  ∀ R J : ℕ, 1 ≤ R → Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A → ∀ σ : ℕ → ℝ,
    c * ∑ j ∈ range J, σ j ^ 2 ≤ pencilStepForm w Q R J σ

/-- **The step packets of an aperture see the weight of the prime two.** A floor of the pencil
on the step packets of the windows inside `A`, at every block size, is a floor of the pencil on
the `C²` tests of every aperture `A' < A`. -/
theorem pencilWeilForm_ge_of_stepFloor {w : ℝ} {Q : ℕ} {A c : ℝ} (hQ : Real.exp (2 * A) ≤ Q)
    (h : PencilStepFloor w Q A c) {A' : ℝ} (hA' : 0 < A') (hA : A' < A) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFz : ∀ x, A' < |x| → F x = 0) :
    c * (∫ x, F x ^ 2) ≤ pencilWeilForm w F := by
  have hFc : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -A') (b := A'))
      fun x hx => by
        rw [Set.mem_Icc, ← abs_le]
        by_contra hlt
        exact hx (hFz x (not_le.mp hlt))
  have hQ1 : 1 ≤ Q := by
    have h1 : (0 : ℝ) < Q := (Real.exp_pos _).trans_le hQ
    exact_mod_cast h1
  -- the test moved to `(log 3, log 3 + ℓ)`, `2A' < ℓ < 2A`
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = A' + A := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = Real.log 3 + ℓ / 2 := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun u => F (u - τ) := ⟨_, rfl⟩
  have hfu : ∀ u, f u = F (u - τ) := fun u => by rw [hfdef]
  have hf : ContDiff ℝ 2 f := by
    rw [hfdef]
    exact hF.comp (contDiff_id.sub contDiff_const)
  have hfc : HasCompactSupport f := by
    rw [hfdef]
    exact hFc.comp_homeomorph (Homeomorph.subRight τ)
  have hlow : ∀ u, u ≤ Real.log 3 → f u = 0 := fun u hu => by
    rw [hfu]
    exact hFz _ (lt_of_lt_of_le (by linarith) (neg_le_abs (u - τ)))
  have hhigh' : ∀ u, Real.log 3 + ℓ ≤ u → f u = 0 := fun u hu => by
    rw [hfu]
    exact hFz _ (lt_of_lt_of_le (by linarith) (le_abs_self (u - τ)))
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ u, f u ^ 2 := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact integral_nonneg fun u => sq_nonneg _
  -- the floor up to `3η`, on a window that starts after `3r` blocks
  have key : ∀ η : ℝ, 0 < η → (c - 3 * η) * I ≤ pencilWeilForm w f := by
    intro η hη
    obtain ⟨r, J, hr1, hrT, hwin, hcover⟩ := exists_window_inside_aperture (A := A) (ℓ := ℓ)
      (by linarith) (by linarith) (crossConstant Q ^ 2 / η + (|c| + |1 - w| * (2 * Real.log 2) *
        ((|1 - w| * (2 * Real.log 2) + 1) / η + 1)) +
        (3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi)))
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr1
    have hQwin : 3 * r + J ≤ Q * (3 * r) := (window_lt_of_log_lt (by omega) hwin hQ).le
    have hJK : 3 * r + J ≤ 3 * Q * r := hQwin.trans (le_of_eq (by ring))
    have hhigh : ∀ u, Real.log (((3 * r + J : ℕ) : ℝ) / r) ≤ u → f u = 0 :=
      fun u hu => hhigh' u (hcover.trans hu)
    have hRlarge : crossConstant Q ^ 2 / η + (|c| + |1 - w| * (2 * Real.log 2) *
          ((|1 - w| * (2 * Real.log 2) + 1) / η + 1)) ≤
        Real.log ((3 * r : ℕ) : ℝ) -
          (3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi)) := by
      have h1 := (Real.le_log_iff_exp_le hr').mpr hrT
      have h2 : Real.log r ≤ Real.log ((3 * r : ℕ) : ℝ) :=
        Real.log_le_log hr' (by push_cast; linarith)
      linarith
    have hev := eventually_pencilCombForm_ge_of_stepPacket_floor (R := 3 * r) (J := J)
      (by omega) hQwin w hη hRlarge (h (3 * r) J (by omega) hwin)
    rw [hI]
    exact mul_integral_sq_le_pencilWeilForm_of_eventually hf hfc (K := 3 * Q) (by omega) hr1
      hJK hlow hhigh w hev
  -- `η → 0`
  have hfin : c * I ≤ pencilWeilForm w f := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hI1 : (0 : ℝ) < I + 1 := by linarith
    obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (3 * (I + 1)) := ⟨_, rfl⟩
    have hη : 0 < η := by
      rw [hηdef]
      positivity
    have h2 : 3 * η * I ≤ ε := by
      have h3 : 3 * η * I = ε * (I / (I + 1)) := by
        rw [hηdef]
        field_simp
      rw [h3]
      exact mul_le_of_le_one_right hε.le ((div_le_one hI1).mpr (by linarith))
    linarith [key η hη]
  -- back to the test
  have hP : pencilWeilForm w f = pencilWeilForm w F := by
    rw [hfdef, pencilWeilForm, pencilWeilForm, zeroSum_translate hF hFc τ,
      packetAutocorr_translate]
  have hmass : I = ∫ x, F x ^ 2 := by
    rw [hI]
    simp only [hfu]
    exact integral_sub_right_eq_self (fun u => F u ^ 2) τ
  rw [← hmass, ← hP]
  exact hfin

/-- **A test below a level gives a step packet below it.** If the pencil at the weight `w` is
below `c ∫ F²` on a `C²` test of the aperture `A' < A`, some window inside `A`, at some block
size, carries a step packet on which the pencil is below `c Σ σ_j²`. -/
theorem exists_stepPacket_pencil_lt {w : ℝ} {Q : ℕ} {A c : ℝ} (hQ : Real.exp (2 * A) ≤ Q)
    {A' : ℝ} (hA' : 0 < A') (hA : A' < A) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFz : ∀ x, A' < |x| → F x = 0) (hlt : pencilWeilForm w F < c * ∫ x, F x ^ 2) :
    ∃ R J : ℕ, 1 ≤ R ∧ Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * A ∧
      ∃ σ : ℕ → ℝ, pencilStepForm w Q R J σ < c * ∑ j ∈ range J, σ j ^ 2 := by
  by_contra hne
  refine absurd (pencilWeilForm_ge_of_stepFloor hQ (fun R J hR hwin σ => ?_) hA' hA hF hFz)
    (not_le.mpr hlt)
  by_contra hσ
  exact hne ⟨R, J, hR, hwin, σ, not_le.mp hσ⟩

/-! ### The sign twin -/

/-- **Below `log 3` the Liouville twist of Weil's functional is the pencil at the weight `−1`.**
On a real test supported in `[−B, B]`, `2B < log 3`, the twist reverses the contact of two and
nothing else. -/
theorem re_weilFullFunctional_liouville_eq_pencilWeilForm {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) {B : ℝ} (hB : B + B < Real.log 3)
    (hFz : ∀ x, B < |x| → F x = 0) :
    (_root_.RHTower.weilFullFunctional liouvilleTwistedVonMangoldt
      (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re = pencilWeilForm (-1) F := by
  have hs : tsupport (fun x => (F x : ℂ)) ⊆ Set.Icc (-B) B := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    rw [Set.mem_Icc, ← abs_le]
    by_contra hlt
    exact hx (by simp [hFz x (not_le.mp hlt)])
  have hk := _root_.RHTower.tsupport_weilTest_subset_add hs hs
  have hdiff := SquareRootThreshold.weilFullFunctional_sub_eq_atom_two hk hB
    liouvilleTwistedVonMangoldt (fun n => (Λ n : ℝ))
  have hΛ2 : (Λ 2 : ℝ) = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hre := congrArg Complex.re hdiff
  rw [Complex.sub_re, Complex.re_ofReal_mul, weilTest_packet, weilTest_packet, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_re, packetAutocorr_neg,
    ← zeroSum_eq_weilFullFunctional hF hFc] at hre
  rw [pencilWeilForm, contactWeight_two]
  linear_combination hre + 2 * packetAutocorr F (Real.log 2) / Real.sqrt 2 * hΛ2 -
    2 * packetAutocorr F (Real.log 2) / Real.sqrt 2 *
      SquareRootThreshold.liouvilleTwistedVonMangoldt_two

/-- **Inside the aperture `37/100` the pencil of the sign twin is below `−1/1000`.** Some window
`(R, R + J]` with `log((R + J)/R) < 2 · 37/100`, at some block size, carries a step packet on
which Weil's form with the contact of two reversed is less than `−(1/1000) Σ σ_j²`. -/
theorem exists_window_signTwin_pencil_lt :
    ∃ R J : ℕ, 1 ≤ R ∧ Real.log ((R + J : ℕ) : ℝ) - Real.log R < 2 * (37 / 100) ∧
      ∃ σ : ℕ → ℝ, pencilStepForm (-1) 3 R J σ < -(1 / 1000) * ∑ j ∈ range J, σ j ^ 2 := by
  obtain ⟨F, hF, hFc, -, hsupp, -, -, hneg⟩ :=
    SelectivePositivityAndThresholdLaws.exists_odd_smooth_threeHundredSixtyTwoThousandths_zeta_pos_liouville_neg
  have hexp : Real.exp (2 * (37 / 100)) ≤ ((3 : ℕ) : ℝ) := by
    have h1 := Real.exp_le_exp.mpr (show (2 * (37 / 100) : ℝ) ≤ 1 by norm_num)
    have h2 := Real.exp_one_lt_d9
    push_cast
    linarith
  have hlog3 : (181 / 500 + 181 / 500 : ℝ) < Real.log 3 := by
    have h1 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  rw [re_weilFullFunctional_liouville_eq_pencilWeilForm hF hFc hlog3 hsupp] at hneg
  exact exists_stepPacket_pencil_lt hexp (by norm_num) (by norm_num) hF hsupp hneg

/-- **The first overlap step of Weil's form fails for the sign twin.** For every cutoff `Q ≥ 2`
and every reweighting `ω` of the contacts with `ω(2) = −1`, some window `(R, R + J]` of ratio at
most `10609/5000`, at some block size, carries a step packet on which the reweighted block matrix
is less than `−(1/1000) Σ σ_j²`. -/
theorem exists_firstStep_window_signTwin_lt {Q : ℕ} (hQ : 2 ≤ Q) {ω : ℕ → ℝ}
    (hω : ω 2 = -1) :
    ∃ R J : ℕ, 1 ≤ R ∧ 5000 * (R + J) ≤ 10609 * R ∧ ∃ σ : ℕ → ℝ,
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * reweightedBlock ω Q (R + j) (R + l) <
        -(1 / 1000) * ∑ j ∈ range J, σ j ^ 2 := by
  obtain ⟨R, J, hR, hwin, σ, hσ⟩ := exists_window_signTwin_pencil_lt
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  -- `2 · 37/100 ≤ log(10609/5000)`: the window lies in the range of the first step
  have hlog : (2 * (37 / 100) : ℝ) ≤ Real.log (10609 / 5000) := by
    have h1 : Real.log (10609 / 5000 : ℝ) = Real.log 2 + Real.log (10609 / 10000) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      congr 1
      norm_num
    have h2 := Real.log_two_gt_d9
    have h3 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 10609 / 10000 by norm_num)
    have h4 : (1 : ℝ) - (10609 / 10000)⁻¹ = 609 / 10609 := by norm_num
    rw [h4] at h3
    rw [h1]
    linarith
  have hpos : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < R + J)
  have hlt : Real.log ((R + J : ℕ) : ℝ) < Real.log (10609 / 5000 * R) := by
    rw [Real.log_mul (by norm_num) hR'.ne']
    linarith
  have hlt' : ((R + J : ℕ) : ℝ) < 10609 / 5000 * R :=
    (Real.log_lt_log_iff hpos (mul_pos (by norm_num) hR')).mp hlt
  have hnat : 5000 * (R + J) < 10609 * R := by
    have h5 : (5000 : ℝ) * ((R + J : ℕ) : ℝ) < 10609 * R := by linarith
    exact_mod_cast h5
  have hJ3 : R + J ≤ 3 * R := by omega
  refine ⟨R, J, hR, hnat.le, σ, ?_⟩
  rw [← reweightedPacketForm_stepPacket hR ω Q J σ,
    reweightedPacketForm_stepPacket_eq_pencilStepForm hR hJ3 hQ ω σ, hω, pencilStepForm,
    packetForm_stepPacket_eq_two hR hJ3 hQ σ,
    ← packetForm_stepPacket_eq_two hR hJ3 (show 2 ≤ 3 by norm_num) σ]
  exact hσ

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow
