import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheRateOfTheMarginBoundsTheAbscissaOfTheZeros
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheExponentOfTheWindowMatricesBoundsTheAbscissaOfTheZeros

/-!
# The rate of the margin of the window matrices bounds the abscissa of the zeros

The margin of a window `(R, (3K + 1)R]` at block size is the second eigenvalue of its neutral
matrix `N_W`. Its binding energy is of order `√K`. A margin that sinks more slowly confines the
zeros:

  **if `N_W + C K^θ` has at most one negative square for every window of ratio `3K + 1`, with
  `θ < ½`, every zero has `|Re ρ − ½| ≤ θ`** (`zetaZeroWidth_le_of_neutralWindow_marginRate`).

In terms of the Doob chain: a Poincaré inequality `gap ≥ μ − C ρ^θ` for all windows, with a loss
`ρ^θ = o(μ)`, is a zero-free strip. This is the finite-scale form of
`zetaZeroWidth_le_of_marginRate`.

The plane is that of the binding state and the antisymmetric state of the two ends, transferred
from infinite block size to the window matrices in three steps, each a one-sided bound valid on
all divisors at once:

* **samples** (`tendsto_combNeutral_sample`): on the samples of a packet the neutral part of the
  comb, `−D·D = 𝔚 − 2 d₁ d₂`, tends to `Z(f) − 2 A(f) B(f)`, and the norm to `∫ f²`;
* **block averages** (`combNeutral_blockMean_le`): replacing a divisor by its block averages
  raises the neutral part by at most `(ε + 5 · 3K/R) Σ c_n²` once the blocks are short (HFP), the
  pole moving by the cross term `2 d₂(s) d₁(z)` of a block function and a divisor of vanishing
  block sums;
* **block functions** (`eventually_abs_combNeutral_sub_le`): on the divisors constant on the
  blocks the neutral part of the comb, per point of a block, tends to the window matrix, uniformly
  in the coefficients: the full forms by AGZ, the degrees by `H_{(a+1)B} − H_{aB} → log((a+1)/a)`.

Both forms of the plane are quadratic in its coordinates (`combNeutral_lin`), so the limits are
uniform on it, and a plane on which the smooth form lies below `−C K^θ` times the mass gives two
negative squares of `N_W + C K^θ`.
-/

open Finset Filter Topology MeasureTheory Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.HodgeTheoryOfAFixedPart (blockIndex blockMean combBilin degOne degTwo
  sampleCoord)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.SquareRootThreshold (lagStructure evenCoeff)
open Zeta23

local notation "combW" => GaloisForLFunctions.HodgeTheoryOfAFixedPart.combForm

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### The neutral part of the comb -/

/-- The neutral part of Weil's form on the comb, `−D·D`. -/
def combNeutral (S : Finset ℕ) (c : ℕ → ℝ) : ℝ := -combBilin S c c

theorem combNeutral_eq (S : Finset ℕ) (c : ℕ → ℝ) :
    combNeutral S c = combW S c - 2 * (degOne S c * degTwo S c) := by
  rw [combNeutral, ← HodgeTheoryOfAFixedPart.formBilin_self, HodgeTheoryOfAFixedPart.formBilin]
  ring

theorem degOne_lin (S : Finset ℕ) (a b : ℝ) (c e : ℕ → ℝ) :
    degOne S (fun n => a * c n + b * e n) = a * degOne S c + b * degOne S e := by
  simp only [HodgeTheoryOfAFixedPart.degOne, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem degTwo_lin (S : Finset ℕ) (a b : ℝ) (c e : ℕ → ℝ) :
    degTwo S (fun n => a * c n + b * e n) = a * degTwo S c + b * degTwo S e := by
  simp only [HodgeTheoryOfAFixedPart.degTwo, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Weil's form on the comb on a combination of two divisors. -/
theorem combForm_lin (S : Finset ℕ) (a b : ℝ) (c e : ℕ → ℝ) :
    combW S (fun n => a * c n + b * e n) =
      a ^ 2 * combW S c + a * b * (HodgeTheoryOfAFixedPart.formBilin S c e +
        HodgeTheoryOfAFixedPart.formBilin S e c) + b ^ 2 * combW S e := by
  rw [← HodgeTheoryOfAFixedPart.formBilin_self,
    formBilin_add_left S (fun n => a * c n) (fun n => b * e n),
    formBilin_add_right S (fun n => a * c n), formBilin_add_right S (fun n => b * e n),
    formBilin_const_mul_left S a c, formBilin_const_mul_left S a c,
    formBilin_const_mul_left S b e, formBilin_const_mul_left S b e,
    formBilin_const_mul_right S a c c, formBilin_const_mul_right S b c e,
    formBilin_const_mul_right S a e c, formBilin_const_mul_right S b e e,
    HodgeTheoryOfAFixedPart.formBilin_self, HodgeTheoryOfAFixedPart.formBilin_self]
  ring

/-- **The neutral part of the comb is a quadratic form**: on `a c + b e` it is
`a² N(c) + ab (N(c + e) − N(c) − N(e)) + b² N(e)`. -/
theorem combNeutral_lin (S : Finset ℕ) (a b : ℝ) (c e : ℕ → ℝ) :
    combNeutral S (fun n => a * c n + b * e n) =
      a ^ 2 * combNeutral S c + a * b * (combNeutral S (fun n => c n + e n) -
        combNeutral S c - combNeutral S e) + b ^ 2 * combNeutral S e := by
  have h1 := combForm_lin S a b c e
  have h2 := combForm_lin S 1 1 c e
  have e1 : (fun n => 1 * c n + 1 * e n) = fun n => c n + e n := funext fun n => by ring
  rw [e1] at h2
  have d1 := degOne_lin S a b c e
  have d2 := degTwo_lin S a b c e
  have d3 := degOne_lin S 1 1 c e
  have d4 := degTwo_lin S 1 1 c e
  rw [e1] at d3 d4
  rw [combNeutral_eq, combNeutral_eq, combNeutral_eq, combNeutral_eq, h1, h2, d1, d2, d3, d4]
  ring

/-- The norm of a combination of two divisors. -/
theorem sum_sq_lin (S : Finset ℕ) (a b : ℝ) (c e : ℕ → ℝ) :
    ∑ n ∈ S, (a * c n + b * e n) ^ 2 =
      a ^ 2 * ∑ n ∈ S, c n ^ 2 + a * b * (∑ n ∈ S, (c n + e n) ^ 2 - ∑ n ∈ S, c n ^ 2 -
        ∑ n ∈ S, e n ^ 2) + b ^ 2 * ∑ n ∈ S, e n ^ 2 := by
  have h : ∀ n, (a * c n + b * e n) ^ 2 = a ^ 2 * c n ^ 2 +
      a * b * ((c n + e n) ^ 2 - c n ^ 2 - e n ^ 2) + b ^ 2 * e n ^ 2 := fun n => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem combNeutral_smul (S : Finset ℕ) (t : ℝ) (c : ℕ → ℝ) :
    combNeutral S (fun n => t * c n) = t ^ 2 * combNeutral S c := by
  have h := combNeutral_lin S t 0 c c
  simp only [zero_mul, add_zero, mul_zero, sq] at h
  rw [h]
  ring

/-! ### Divisors constant on blocks -/

theorem sum_Ioc_eq_sum_range (f : ℕ → ℝ) (M B : ℕ) :
    ∑ n ∈ Ioc M (M + B), f n = ∑ a ∈ range B, f (M + 1 + a) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [show M + (B + 1) = M + B + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih,
      Finset.sum_range_succ, show M + B + 1 = M + 1 + B by ring]

/-- A sum against a divisor constant on the blocks, block by block. -/
theorem sum_blockFunction_mul {B : ℕ} (hB : 0 < B) (N J : ℕ) (σ w : ℕ → ℝ) :
    ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) * w n =
      ∑ j ∈ range J, σ j * ∑ a ∈ range B, w (N + 1 + B * j + a) := by
  rw [HodgeTheoryOfAFixedPart.sum_Ioc_blocks]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hidx : blockIndex N B (N + 1 + B * j + a) = j := by
    unfold HodgeTheoryOfAFixedPart.blockIndex
    rw [show N + 1 + B * j + a - N - 1 = B * j + a by omega, Nat.mul_add_div hB,
      Nat.div_eq_of_lt (Finset.mem_range.mp ha), add_zero]
  rw [hidx]

theorem degTwo_blockFunction {B : ℕ} (hB : 0 < B) (N J : ℕ) (σ : ℕ → ℝ) :
    degTwo (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) = B * ∑ j ∈ range J, σ j := by
  have h := sum_blockFunction_mul hB N J σ (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  show ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) = _
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem degOne_blockFunction {B : ℕ} (hB : 0 < B) (N J : ℕ) (σ : ℕ → ℝ) :
    degOne (Ioc N (N + B * J)) (fun n => σ (blockIndex N B n)) =
      ∑ j ∈ range J, σ j * (harm (N + B * j + B) - harm (N + B * j)) := by
  have h := sum_blockFunction_mul hB N J σ (fun n => 1 / (n : ℝ))
  have e : ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) / (n : ℝ) =
      ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) * (1 / (n : ℝ)) :=
    Finset.sum_congr rfl fun n _ => by ring
  show ∑ n ∈ Ioc N (N + B * J), σ (blockIndex N B n) / (n : ℝ) = _
  rw [e, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sum_Ioc_one_div (by omega : N + B * j ≤ N + B * j + B), sum_Ioc_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show N + 1 + B * j + a = N + B * j + 1 + a by ring]

/-- The harmonic sums of the blocks of `(RB, (R + J)B]` tend to the degrees of the blocks. -/
theorem tendsto_harm_block {R : ℕ} (hR : 1 ≤ R) (j : ℕ) :
    Tendsto (fun B : ℕ => harm (R * B + B * j + B) - harm (R * B + B * j)) atTop
      (𝓝 (blockDegree (R + j))) := by
  have h := tendsto_harm_mul_sub (a := R + j) (b := R + j + 1) (by omega) (by omega)
  refine h.congr fun B => ?_
  rw [show (R + j + 1) * B = R * B + B * j + B by ring, show (R + j) * B = R * B + B * j by ring]

/-- **On divisors constant on the blocks the neutral part of the comb tends to the window
matrix**, per point of a block, uniformly in the coefficients. -/
theorem eventually_abs_combNeutral_sub_le {R J Q : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ B : ℕ in atTop, ∀ σ : ℕ → ℝ,
      |combNeutral (Ioc (R * B) (R * B + B * J)) (fun n => σ (blockIndex (R * B) B n)) / B -
          ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l)| ≤
        η * ∑ j ∈ range J, σ j ^ 2 := by
  have hev := eventually_abs_combForm_nested_sub_le (s := range (J + 1)) (x := fun j => R + j)
    (X := R + J) (Q := Q) hR (nested_bounds R J) hQ (η := η / 8) (by positivity)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / (4 * ((J : ℝ) + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδJ : δ * (4 * ((J : ℝ) + 1)) = η := by
    rw [hδ]; exact div_mul_cancel₀ η (by positivity)
  have hharm : ∀ᶠ B : ℕ in atTop, ∀ j ∈ range J,
      |harm (R * B + B * j + B) - harm (R * B + B * j) - blockDegree (R + j)| ≤ δ := by
    rw [Filter.eventually_all_finset]
    intro j _
    filter_upwards [(Metric.tendsto_nhds.mp (tendsto_harm_block hR j)) δ hδ0] with B hB
    rw [Real.dist_eq] at hB
    exact hB.le
  filter_upwards [hev, hharm, eventually_ge_atTop 1] with B hB hH hB1 σ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB1
  -- the full forms
  have h := hB (nestedCoeff J σ)
  have hwin : (R + J) * B = R * B + B * J := by ring
  have hc : combW (Ioc (R * B) (R * B + B * J)) (fun n => ∑ j ∈ range (J + 1),
        nestedCoeff J σ j * windowDivisor (R * B) ((R + j) * B) n) =
      combW (Ioc (R * B) (R * B + B * J)) fun n => σ (blockIndex (R * B) B n) :=
    (combForm_congr fun n hn => blockFunction_eq_nested (by omega) σ hn).symm
  rw [hwin, hc, ← stepPacket_eq_nested hR J σ, packetForm_stepPacket_eq_sum_blockMatrix hR,
    sum_blockMatrix_eq_charges_add_neutral] at h
  have hsq := mul_le_mul_of_nonneg_left (sum_nestedCoeff_sq_le J σ)
    (by positivity : (0 : ℝ) ≤ η / 8)
  have hm : 0 ≤ ∑ j ∈ range J, σ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the degrees
  rw [combNeutral_eq, degTwo_blockFunction (by omega) (R * B) J σ,
    degOne_blockFunction (by omega) (R * B) J σ]
  have hdiv : 2 * ((∑ j ∈ range J, σ j * (harm (R * B + B * j + B) - harm (R * B + B * j))) *
      (B * ∑ j ∈ range J, σ j)) / B =
      2 * (∑ j ∈ range J, σ j * (harm (R * B + B * j + B) - harm (R * B + B * j))) *
        ∑ j ∈ range J, σ j := by
    rw [div_eq_iff hB0.ne']; ring
  rw [sub_div, hdiv]
  -- the pole term moves by at most `2δJ Σ σ²`
  have hdiff : |∑ j ∈ range J, σ j * (harm (R * B + B * j + B) - harm (R * B + B * j)) -
      ∑ j ∈ range J, σ j * blockDegree (R + j)| ≤ δ * ∑ j ∈ range J, |σ j| := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [← mul_sub, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hH j hj) (abs_nonneg _)
  have hl1 : (∑ j ∈ range J, |σ j|) ^ 2 ≤ J * ∑ j ∈ range J, σ j ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range J) (f := fun j => |σ j|)
    simpa [Finset.card_range, sq_abs] using this
  have habs : |∑ j ∈ range J, σ j| ≤ ∑ j ∈ range J, |σ j| := Finset.abs_sum_le_sum_abs _ _
  have hpole : |2 * (∑ j ∈ range J, σ j * (harm (R * B + B * j + B) - harm (R * B + B * j))) *
        ∑ j ∈ range J, σ j - 2 * (∑ j ∈ range J, σ j) *
          ∑ j ∈ range J, σ j * blockDegree (R + j)| ≤ η / 2 * ∑ j ∈ range J, σ j ^ 2 := by
    have e : 2 * (∑ j ∈ range J, σ j * (harm (R * B + B * j + B) - harm (R * B + B * j))) *
          ∑ j ∈ range J, σ j - 2 * (∑ j ∈ range J, σ j) *
            ∑ j ∈ range J, σ j * blockDegree (R + j) =
        2 * (∑ j ∈ range J, σ j) * (∑ j ∈ range J,
          σ j * (harm (R * B + B * j + B) - harm (R * B + B * j)) -
            ∑ j ∈ range J, σ j * blockDegree (R + j)) := by ring
    rw [e, abs_mul, abs_mul, abs_two]
    have hA : 0 ≤ ∑ j ∈ range J, |σ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h1 := mul_le_mul habs hdiff (abs_nonneg _) hA
    have h2 : (∑ j ∈ range J, |σ j|) * (δ * ∑ j ∈ range J, |σ j|) ≤
        δ * (J * ∑ j ∈ range J, σ j ^ 2) := by
      have := mul_le_mul_of_nonneg_left hl1 hδ0.le
      nlinarith
    have hJm : 0 ≤ (J : ℝ) * ∑ j ∈ range J, σ j ^ 2 := mul_nonneg (Nat.cast_nonneg _) hm
    have h3 : 2 * (δ * (J * ∑ j ∈ range J, σ j ^ 2)) ≤ η / 2 * ∑ j ∈ range J, σ j ^ 2 := by
      have : 2 * δ * (J : ℝ) ≤ η / 2 := by nlinarith
      nlinarith
    nlinarith
  rw [abs_le] at hpole h ⊢
  constructor <;> nlinarith [hpole.1, hpole.2, h.1, h.2]

/-! ### Block averages -/

/-- **Block averages raise the neutral part of the comb by a small multiple of the norm**: the
full form by HFP, and the pole by the cross term of the block averages with the divisor of
vanishing block sums. -/
theorem combNeutral_blockMean_le {N B J Q : ℕ} (hB : 0 < B) (hBN : B ≤ N)
    (hQ : N + B * J ≤ Q * N) {ε : ℝ} (hε : 0 < ε)
    (hμ : HodgeTheoryOfAFixedPart.crossConstant Q ^ 2 / ε ≤ Real.log ((N : ℝ) / (2 * Real.pi)) -
      (harm (2 * B) + 2 + ((B * J : ℕ) : ℝ) / (4 * N) + 2 * HodgeTheoryOfAFixedPart.chebyshev Q))
    (c : ℕ → ℝ) :
    combNeutral (Ioc N (N + B * J)) (fun n => blockMean N B J c (blockIndex N B n)) ≤
      combNeutral (Ioc N (N + B * J)) c +
        (ε + 5 * ((B : ℝ) * ((B * J : ℕ) : ℝ) / (N : ℝ) ^ 2)) *
          ∑ n ∈ Ioc N (N + B * J), c n ^ 2 := by
  have hN : 0 < N := lt_of_lt_of_le hB hBN
  have h1 := HodgeTheoryOfAFixedPart.combForm_ge_blockMean hB hBN hQ hε hμ c
  have hzero := HodgeTheoryOfAFixedPart.sum_filter_sub_blockMean hB N J c
  have hd2 : degTwo (Ioc N (N + B * J)) c =
      degTwo (Ioc N (N + B * J)) (fun n => blockMean N B J c (blockIndex N B n)) := by
    have h0 := HodgeTheoryOfAFixedPart.sum_blockFunction_mul_eq_zero N B (Ioc N (N + B * J))
      (fun _ => 1) (fun n => c n - blockMean N B J c (blockIndex N B n)) hzero
    simp only [one_mul, Finset.sum_sub_distrib] at h0
    show ∑ n ∈ Ioc N (N + B * J), c n =
      ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n)
    linarith
  have hd1 : degOne (Ioc N (N + B * J)) c =
      degOne (Ioc N (N + B * J)) (fun n => blockMean N B J c (blockIndex N B n)) +
        degOne (Ioc N (N + B * J)) (fun n => c n - blockMean N B J c (blockIndex N B n)) := by
    simp only [HodgeTheoryOfAFixedPart.degOne, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hcross := HodgeTheoryOfAFixedPart.two_mul_abs_degTwo_mul_degOne_le (M := B * J) hN hB
    (S := Ioc N (N + B * J)) subset_rfl (fun n => blockMean N B J c (blockIndex N B n))
    (fun n => c n - blockMean N B J c (blockIndex N B n)) hzero one_pos (one_mul 1)
  have hbm := HodgeTheoryOfAFixedPart.sum_blockMean_sq_le hB N J c
  have hz : ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 ≤
      4 * ∑ n ∈ Ioc N (N + B * J), c n ^ 2 := by
    have hpt : ∀ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2 ≤
        2 * c n ^ 2 + 2 * blockMean N B J c (blockIndex N B n) ^ 2 := fun n _ => by
      nlinarith [sq_nonneg (c n + blockMean N B J c (blockIndex N B n))]
    calc ∑ n ∈ Ioc N (N + B * J), (c n - blockMean N B J c (blockIndex N B n)) ^ 2
        ≤ ∑ n ∈ Ioc N (N + B * J), (2 * c n ^ 2 + 2 * blockMean N B J c (blockIndex N B n) ^ 2) :=
          Finset.sum_le_sum hpt
      _ = 2 * ∑ n ∈ Ioc N (N + B * J), c n ^ 2 +
            2 * ∑ n ∈ Ioc N (N + B * J), blockMean N B J c (blockIndex N B n) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 4 * ∑ n ∈ Ioc N (N + B * J), c n ^ 2 := by linarith
  have hK0 : 0 ≤ (B : ℝ) * ((B * J : ℕ) : ℝ) / (N : ℝ) ^ 2 := by positivity
  have hc0 : 0 ≤ ∑ n ∈ Ioc N (N + B * J), c n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK := mul_le_mul_of_nonneg_left (show 1 * ∑ n ∈ Ioc N (N + B * J),
      blockMean N B J c (blockIndex N B n) ^ 2 + 1 * ∑ n ∈ Ioc N (N + B * J),
        (c n - blockMean N B J c (blockIndex N B n)) ^ 2 ≤
      5 * ∑ n ∈ Ioc N (N + B * J), c n ^ 2 by linarith) hK0
  have hab := le_abs_self (degTwo (Ioc N (N + B * J))
      (fun n => blockMean N B J c (blockIndex N B n)) *
    degOne (Ioc N (N + B * J)) (fun n => c n - blockMean N B J c (blockIndex N B n)))
  rw [combNeutral_eq, combNeutral_eq, hd1, ← hd2]
  rw [← hd2] at hab hcross
  nlinarith

/-! ### Samples of packets -/

theorem sampleCoord_lin (f g : ℝ → ℝ) (a b : ℝ) (N : ℕ) :
    sampleCoord (fun u => a * f u + b * g u) N = fun n => a * sampleCoord f N n +
      b * sampleCoord g N n := by
  funext n
  simp only [HodgeTheoryOfAFixedPart.sampleCoord, degreeSample]
  ring

/-- **On the samples of a packet the neutral part of the comb tends to `Z(f) − 2 A(f) B(f)`.** -/
theorem tendsto_combNeutral_sample {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {K : ℕ} (hK : 1 ≤ K) (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => combNeutral (Ioc N (N + 3 * K * N)) (sampleCoord f N)) atTop
      (𝓝 (zeroSum f - 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2)))) := by
  have h1 := HodgeTheoryOfAFixedPart.tendsto_combForm_sample hf hfc hK hsupp
  have h2 := (HodgeTheoryOfAFixedPart.tendsto_degOne_mul_degTwo_sample hf.continuous hK
    hsupp).const_mul 2
  refine (h1.sub h2).congr fun N => ?_
  rw [combNeutral_eq]

theorem tendsto_sum_sq_sample {f : ℝ → ℝ} (hf : Continuous f) {K : ℕ} (hK : 1 ≤ K)
    (hsupp : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc N (N + 3 * K * N), sampleCoord f N n ^ 2) atTop
      (𝓝 (∫ u, f u ^ 2)) := by
  have h := HodgeTheoryOfAFixedPart.tendsto_sum_sq_sampleCoord hf hK
  rwa [HodgeTheoryOfAFixedPart.intervalIntegral_window_eq (G := fun u => f u ^ 2) hK
    fun u hu => by rw [hsupp u hu]; ring] at h

/-! ### The smooth plane -/

/-- The neutral form of a smooth packet, by its zeros and its charges. -/
def smoothNeutral (f : ℝ → ℝ) : ℝ :=
  zeroSum f - 2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))

/-- On a packet of the window the smooth neutral form is the neutral form. -/
theorem smoothNeutral_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ} (hv : ∀ u, L < |u| → f u = 0)
    {Q : ℕ} (hQ : Real.exp (2 * L) < Q) : smoothNeutral f = neutralForm Q f := by
  unfold smoothNeutral neutralForm
  rw [zeroSum_eq_packetForm hf (hasCompactSupport_of_vanishing hv)
    (packetAutocorr_log_eq_zero_of_vanishing hv hQ)]

theorem integral_translate_mul_exp (f : ℝ → ℝ) (τ s : ℝ) :
    ∫ u, f (u - τ) * Real.exp (s * u) = Real.exp (s * τ) * ∫ u, f u * Real.exp (s * u) := by
  have h := integral_comp_add_mul_exp f (-τ) s
  rw [show -(s * -τ) = s * τ by ring] at h
  rw [← h]
  congr 1
  funext u
  rw [sub_eq_add_neg]

/-- The smooth neutral form is invariant under translation: the sum over the zeros is, and the
two charges are multiplied by `e^{∓τ/2}`. -/
theorem smoothNeutral_translate {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ}
    (hv : ∀ u, L < |u| → f u = 0) (τ : ℝ) :
    smoothNeutral (fun u => f (u - τ)) = smoothNeutral f := by
  obtain ⟨Q, hQ⟩ := exists_nat_gt (Real.exp (2 * L))
  have hvt : ∀ u, u < τ - L ∨ τ + L < u → f (u - τ) = 0 := fun u hu => hv _ (by
    rcases hu with h | h
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
    · exact lt_of_lt_of_le (by linarith) (le_abs_self _))
  have hct : HasCompactSupport fun u => f (u - τ) :=
    HasCompactSupport.intro (isCompact_Icc (a := τ - L) (b := τ + L)) fun u hu => hvt u (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      exact hu)
  have hQt : ∀ n : ℕ, Q < n → packetAutocorr (fun u => f (u - τ)) (Real.log n) = 0 := by
    intro n hn
    have hn' : Real.exp (2 * L) < n := hQ.trans (by exact_mod_cast hn)
    have hlog : 2 * L < Real.log n :=
      (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < n by omega))).mpr hn'
    exact packetAutocorr_eq_zero_of_vanishing_off hvt (by linarith)
  have hz : zeroSum (fun u => f (u - τ)) = zeroSum f := by
    rw [zeroSum_eq_packetForm (f := fun u => f (u - τ)) (hf.comp (contDiff_id.sub contDiff_const))
      hct hQt,
      packetForm_translate,
      ← zeroSum_eq_packetForm hf (hasCompactSupport_of_vanishing hv)
        (packetAutocorr_log_eq_zero_of_vanishing hv hQ)]
  have hA : ∫ u, f (u - τ) * Real.exp (-u / 2) =
      Real.exp (-1 / 2 * τ) * ∫ u, f u * Real.exp (-u / 2) := by
    have h := integral_translate_mul_exp f τ (-1 / 2)
    rw [show (fun u => f (u - τ) * Real.exp (-u / 2)) =
        fun u => f (u - τ) * Real.exp (-1 / 2 * u) from
          funext fun u => by rw [show -u / 2 = -1 / 2 * u by ring],
      show (fun u => f u * Real.exp (-u / 2)) = fun u => f u * Real.exp (-1 / 2 * u) from
          funext fun u => by rw [show -u / 2 = -1 / 2 * u by ring]]
    exact h
  have hB : ∫ u, f (u - τ) * Real.exp (u / 2) =
      Real.exp (1 / 2 * τ) * ∫ u, f u * Real.exp (u / 2) := by
    have h := integral_translate_mul_exp f τ (1 / 2)
    rw [show (fun u => f (u - τ) * Real.exp (u / 2)) =
        fun u => f (u - τ) * Real.exp (1 / 2 * u) from
          funext fun u => by rw [show u / 2 = 1 / 2 * u by ring],
      show (fun u => f u * Real.exp (u / 2)) = fun u => f u * Real.exp (1 / 2 * u) from
          funext fun u => by rw [show u / 2 = 1 / 2 * u by ring]]
    exact h
  have he : Real.exp (-1 / 2 * τ) * Real.exp (1 / 2 * τ) = 1 := by
    rw [← Real.exp_add, show -1 / 2 * τ + 1 / 2 * τ = 0 by ring, Real.exp_zero]
  unfold smoothNeutral
  rw [hz, hA, hB]
  linear_combination (-2 * ((∫ u, f u * Real.exp (-u / 2)) * ∫ u, f u * Real.exp (u / 2))) * he

/-- The shift that moves the states of lag `v` to the right of `log 3`. -/
def stateShift (v : ℝ) : ℝ := Real.log 3 + 6 + |v| / 2

theorem shiftedOdd_eq (v : ℝ) : shiftedOdd v = fun u => twoEndOdd v (u - stateShift v) := rfl

theorem vanishing_twoEndSpline (v : ℝ) :
    ∀ u, 5 + |v| / 2 < |u| → twoEndSpline v u = 0 ∧ twoEndOdd v u = 0 := fun u hu =>
  ⟨twoEndSpline_eq_zero v (by linarith), twoEndOdd_eq_zero v hu⟩

/-- **The smooth plane at lag `v`**: the neutral forms of the binding state and of the
antisymmetric state, and of their sum, which is the sum of the two. -/
theorem smoothNeutral_plane (v : ℝ) :
    smoothNeutral (fun u => twoEndSpline v (u - stateShift v)) =
        2 * (lagStructure zetaZeroConfig (cx spline) 0).re +
          2 * (lagStructure zetaZeroConfig (cx spline) v).re -
            2 * ((Real.exp (v / 4) + Real.exp (-(v / 4))) * splineCharge) ^ 2 ∧
      smoothNeutral (shiftedOdd v) =
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re -
          2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re ∧
      smoothNeutral (fun u => twoEndSpline v (u - stateShift v) + shiftedOdd v u) =
        smoothNeutral (fun u => twoEndSpline v (u - stateShift v)) +
          smoothNeutral (shiftedOdd v) := by
  have hvan := vanishing_twoEndSpline v
  have hvx : ∀ u, 5 + |v| / 2 < |u| → twoEndSpline v u = 0 := fun u hu => (hvan u hu).1
  have hvy : ∀ u, 5 + |v| / 2 < |u| → twoEndOdd v u = 0 := fun u hu => (hvan u hu).2
  have hvs : ∀ u, 5 + |v| / 2 < |u| → twoEndSpline v u + 1 * twoEndOdd v u = 0 := fun u hu => by
    rw [hvx u hu, hvy u hu]; ring
  obtain ⟨Q, hQ⟩ := exists_nat_gt (Real.exp (2 * (5 + |v| / 2)))
  have hx := smoothNeutral_translate (contDiff_twoEndSpline v) hvx (stateShift v)
  have hy := smoothNeutral_translate (contDiff_twoEndOdd v) hvy (stateShift v)
  have hs := smoothNeutral_translate ((contDiff_twoEndSpline v).add
    (contDiff_const.mul (contDiff_twoEndOdd v))) hvs (stateShift v)
  have hx0 : smoothNeutral (twoEndSpline v) = 2 * (lagStructure zetaZeroConfig (cx spline) 0).re +
      2 * (lagStructure zetaZeroConfig (cx spline) v).re -
        2 * ((Real.exp (v / 4) + Real.exp (-(v / 4))) * splineCharge) ^ 2 := by
    obtain ⟨hA, hB⟩ := charges_twoEndSpline v
    unfold smoothNeutral
    rw [zeroSum_twoEndSpline, hA, hB]
    ring
  have hy0 : smoothNeutral (twoEndOdd v) =
      2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re -
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re := by
    rw [smoothNeutral_eq (contDiff_twoEndOdd v) hvy hQ,
      neutralForm_twoEndOdd v (packetAutocorr_log_eq_zero_of_vanishing hvy hQ)]
  have hs0 : smoothNeutral (fun u => twoEndSpline v u + 1 * twoEndOdd v u) =
      smoothNeutral (twoEndSpline v) + smoothNeutral (twoEndOdd v) := by
    rw [smoothNeutral_eq ((contDiff_twoEndSpline v).add
        (contDiff_const.mul (contDiff_twoEndOdd v))) hvs hQ,
      smoothNeutral_eq (contDiff_twoEndSpline v) hvx hQ,
      smoothNeutral_eq (contDiff_twoEndOdd v) hvy hQ,
      neutralForm_even_add_odd_charged (contDiff_twoEndSpline v) (contDiff_twoEndOdd v) hvan
        (twoEndSpline_neg v) (twoEndOdd_neg v) (charge_twoEndOdd v) hQ 1]
    ring
  refine ⟨hx.trans hx0, ?_, ?_⟩
  · rw [shiftedOdd_eq, hy, hy0]
  · have e : (fun u => twoEndSpline v (u - stateShift v) + shiftedOdd v u) =
        fun u => twoEndSpline v (u - stateShift v) + 1 * twoEndOdd v (u - stateShift v) := by
      funext u; simp only [shiftedOdd_eq]; ring
    rw [e, hs, hs0, ← hx, ← hy, ← shiftedOdd_eq]

/-- The masses of the smooth plane. -/
theorem integral_plane_sq (v : ℝ) :
    ∫ u, (twoEndSpline v (u - stateShift v) + shiftedOdd v u) ^ 2 =
      (∫ u, twoEndSpline v (u - stateShift v) ^ 2) + ∫ u, shiftedOdd v u ^ 2 := by
  have h := integral_even_add_odd_sq (contDiff_twoEndSpline v).continuous
    (contDiff_twoEndOdd v).continuous (vanishing_twoEndSpline v) (twoEndSpline_neg v)
    (twoEndOdd_neg v) 1 1
  simp only [one_mul, one_pow] at h
  simp only [shiftedOdd_eq]
  rw [integral_comp_sub_sq (fun u => twoEndSpline v u + twoEndOdd v u) (stateShift v),
    integral_comp_sub_sq (twoEndSpline v) (stateShift v),
    integral_comp_sub_sq (twoEndOdd v) (stateShift v), h]

/-! ### The theorem -/

/-- **The tail of the rate law**: a bound `2 Re S(v) ≤ 2 Re S(0) + E e^{θ v}` from some lag on
gives the zero width `θ`; below that lag `2 Re S(v) ≤ K e^{v/2}` is bounded. -/
theorem zetaZeroWidth_le_of_eventually_lag_le {θ V E : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (h : ∀ v : ℝ, max V 0 ≤ v →
      2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) v).re ≤
        2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re + E * Real.exp (θ * v)) :
    SquareRootThreshold.zetaZeroWidth ≤ θ := by
  obtain ⟨S0, hS0⟩ : ∃ S, S = 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re :=
    ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (cx poleFreeProfile) z‖ :=
    ⟨_, rfl⟩
  refine (zetaZeroWidth_le_iff_twoEndOdd_rate hθ0 hθ).mpr
    ⟨|E| + |S0| + K * Real.exp (|V| / 2), fun v hv Q hQ => ?_⟩
  rw [neutralForm_twoEndOdd v hQ, ← hS0]
  have he1 : 1 ≤ Real.exp (θ * v) := Real.one_le_exp (mul_nonneg hθ0 hv)
  have hK0 : 0 ≤ K := by rw [hK]; exact tsum_nonneg fun _ => norm_nonneg _
  have hKV : 0 ≤ K * Real.exp (|V| / 2) := mul_nonneg hK0 (Real.exp_pos _).le
  have hS1 : |S0| ≤ |S0| * Real.exp (θ * v) := le_mul_of_one_le_right (abs_nonneg _) he1
  have hK1 : K * Real.exp (|V| / 2) ≤ K * Real.exp (|V| / 2) * Real.exp (θ * v) :=
    le_mul_of_one_le_right hKV he1
  have hE1 : E * Real.exp (θ * v) ≤ |E| * Real.exp (θ * v) :=
    mul_le_mul_of_nonneg_right (le_abs_self E) (Real.exp_pos _).le
  have hrhs : (|E| + |S0| + K * Real.exp (|V| / 2)) * Real.exp (θ * v) =
      |E| * Real.exp (θ * v) + |S0| * Real.exp (θ * v) +
        K * Real.exp (|V| / 2) * Real.exp (θ * v) := by ring
  rw [hrhs]
  have h0 : 0 ≤ |E| * Real.exp (θ * v) := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have h0' : 0 ≤ K * Real.exp (|V| / 2) * Real.exp (θ * v) := mul_nonneg hKV (Real.exp_pos _).le
  rcases le_or_gt (max V 0) v with hvV | hvV
  · have := h v hvV
    rw [← hS0] at this
    linarith [le_abs_self S0, neg_abs_le S0]
  · have h1 := SquareRootThreshold.two_re_lagStructure_le_mul_exp zetaZeroConfig
      SquareRootThreshold.temperedConfig_zetaZeroConfig contDiff_cx_poleFreeProfile
      cx_poleFreeProfile_support (τ := 1 / 2)
      (fun z hz => SquareRootThreshold.re_le_of_evenCoeff_ne_zero hz) hv
    rw [← hK] at h1
    have h2 : K * Real.exp (1 / 2 * v) ≤ K * Real.exp (|V| / 2) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK0
      rcases lt_max_iff.mp hvV with h3 | h3
      · linarith [le_abs_self V]
      · linarith
    linarith [le_abs_self S0, neg_abs_le S0]

/-- The form of the neutral part of a window plus `C` on a vector. -/
theorem sum_fin_neutralWindow_add_diag (Q R J : ℕ) (C : ℝ) (x : ℕ → ℝ) :
    ∑ i : Fin J, ∑ j : Fin J, x i * x j *
        (neutralWindow Q R J + Matrix.diagonal fun _ => C : Matrix (Fin J) (Fin J) ℝ) i j =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * neutralBlock Q (R + j) (R + l) +
        C * ∑ j ∈ range J, x j ^ 2 := by
  have hdiag : ∀ i : Fin J, ∑ j : Fin J, x i * x j * Matrix.diagonal (fun _ => C) i j =
      C * x i ^ 2 := fun i => by
    rw [Finset.sum_eq_single i
      (fun j _ hj => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)]
    simp only [Matrix.diagonal_apply_eq]
    ring
  have hsplit : ∑ i : Fin J, ∑ j : Fin J, x i * x j *
      (neutralWindow Q R J + Matrix.diagonal fun _ => C : Matrix (Fin J) (Fin J) ℝ) i j =
      ∑ i : Fin J, ∑ j : Fin J, x i * x j * neutralWindow Q R J i j +
        ∑ i : Fin J, C * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hdiag i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.add_apply]
    ring
  have hN : ∑ i : Fin J, ∑ j : Fin J, x i * x j * neutralWindow Q R J i j =
      ∑ j ∈ range J, ∑ l ∈ range J, x j * x l * neutralBlock Q (R + j) (R + l) :=
    sum_fin_windowMatrix_coe (neutralBlock Q) R J x
  rw [hsplit, hN, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => x i ^ 2) J]

theorem blockMean_lin (N B J : ℕ) (a b : ℝ) (c e : ℕ → ℝ) (j : ℕ) :
    blockMean N B J (fun n => a * c n + b * e n) j =
      a * blockMean N B J c j + b * blockMean N B J e j := by
  simp only [HodgeTheoryOfAFixedPart.blockMean, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **The margin of the window matrices at rate `θ < ½` confines the zeros**: if for every
window `(R, (3K + 1)R]` the neutral part plus `C K^θ` has at most one negative square, every zero
of `ζ` has `|Re ρ − ½| ≤ θ`. -/
theorem zetaZeroWidth_le_of_neutralWindow_marginRate {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (h : ∀ K R : ℕ, 1 ≤ K → 1 ≤ R →
      hermNegIndex ((neutralWindow (3 * K + 1) R (3 * K * R) +
        Matrix.diagonal fun _ => C * (K : ℝ) ^ θ).map (↑) :
          Matrix (Fin (3 * K * R)) (Fin (3 * K * R)) ℂ) ≤ 1) :
    SquareRootThreshold.zetaZeroWidth ≤ θ := by
  -- constants
  obtain ⟨S0, hS0⟩ : ∃ S, S = 2 * (lagStructure zetaZeroConfig (cx poleFreeProfile) 0).re :=
    ⟨_, rfl⟩
  obtain ⟨T0, hT0⟩ : ∃ S, S = 2 * (lagStructure zetaZeroConfig (cx spline) 0).re := ⟨_, rfl⟩
  obtain ⟨m₀, hm₀⟩ : ∃ m, m = ∫ u, poleFreeProfile u ^ 2 := ⟨_, rfl⟩
  obtain ⟨mU, hmU⟩ : ∃ m, m = ∫ u, spline u ^ 2 := ⟨_, rfl⟩
  have hm₀0 : 0 ≤ m₀ := by rw [hm₀]; exact integral_nonneg fun u => sq_nonneg _
  have hmU0 : 0 ≤ mU := by rw [hmU]; exact integral_nonneg fun u => sq_nonneg _
  obtain ⟨Bθ, hBθ⟩ : ∃ B, B = (2 * Real.exp (Real.log 3 + 12)) ^ θ := ⟨_, rfl⟩
  have hBθ0 : 0 ≤ Bθ := by rw [hBθ]; positivity
  obtain ⟨E, hE⟩ : ∃ E, E = |C| * Bθ := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hA2 : 0 < 2 * splineCharge ^ 2 := by
    have := pow_pos (abs_pos.mpr splineCharge_ne_zero) 2
    rw [_root_.sq_abs] at this
    linarith
  -- the binding state is eventually deeper than the allowed margin
  have hdeep : ∀ᶠ v : ℝ in atTop,
      T0 + 2 * (lagStructure zetaZeroConfig (cx spline) v).re + 4 * E * mU * Real.exp (θ * v) <
        2 * splineCharge ^ 2 * Real.exp (v / 2) := by
    have h1 := tendsto_two_re_lagStructure_mul_exp contDiff_cx_spline cx_spline_support
    have h2 : Tendsto (fun v : ℝ => Real.exp (-(v / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num))
    have h3 : Tendsto (fun v : ℝ => Real.exp (-((1 / 2 - θ) * v))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by linarith))
    have hF := ((h2.const_mul T0).add h1).add (h3.const_mul (4 * E * mU))
    simp only [mul_zero, add_zero] at hF
    filter_upwards [hF.eventually (gt_mem_nhds hA2)] with v hv
    have hv' : T0 * Real.exp (-(v / 2)) +
        2 * (lagStructure zetaZeroConfig (cx spline) v).re * Real.exp (-(v / 2)) +
        4 * E * mU * Real.exp (-((1 / 2 - θ) * v)) < 2 * splineCharge ^ 2 := hv
    have he : 0 < Real.exp (v / 2) := Real.exp_pos _
    have e1 : Real.exp (-(v / 2)) * Real.exp (v / 2) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have e2 : Real.exp (-((1 / 2 - θ) * v)) * Real.exp (v / 2) = Real.exp (θ * v) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmul := mul_lt_mul_of_pos_right hv' he
    have e3 : (T0 * Real.exp (-(v / 2)) +
          2 * (lagStructure zetaZeroConfig (cx spline) v).re * Real.exp (-(v / 2)) +
          4 * E * mU * Real.exp (-((1 / 2 - θ) * v))) * Real.exp (v / 2) =
        T0 + 2 * (lagStructure zetaZeroConfig (cx spline) v).re +
          4 * E * mU * Real.exp (θ * v) := by
      rw [← e2]
      linear_combination (T0 + 2 * (lagStructure zetaZeroConfig (cx spline) v).re) * e1
    rw [e3] at hmul
    linarith
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp hdeep
  refine zetaZeroWidth_le_of_eventually_lag_le hθ0 hθ (V := V₁) (E := 4 * E * m₀) fun v hv => ?_
  rw [← hS0]
  have hv0 : 0 ≤ v := (le_max_right _ _).trans hv
  have hvV : V₁ ≤ v := (le_max_left _ _).trans hv
  by_contra hcon
  push Not at hcon
  obtain ⟨K, hK1, hKlog, hKle⟩ := exists_ratio_le hv0
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- the allowed depth at ratio `3K + 1`
  obtain ⟨D, hD⟩ : ∃ D, D = |C| * (K : ℝ) ^ θ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hK0 θ)
  have hDE : D ≤ E * Real.exp (θ * v) := by
    have hKθ : (K : ℝ) ^ θ ≤ Bθ * Real.exp (θ * v) := by
      calc (K : ℝ) ^ θ ≤ (2 * Real.exp (Real.log 3 + 12) * Real.exp v) ^ θ :=
            Real.rpow_le_rpow hK0 hKle hθ0
        _ = Bθ * Real.exp (θ * v) := by
            rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, hBθ, ← Real.exp_mul,
              mul_comm v θ]
    rw [hD, hE, mul_assoc]
    exact mul_le_mul_of_nonneg_left hKθ (abs_nonneg C)
  -- the smooth plane
  obtain ⟨hNg, hNo, hNs⟩ := smoothNeutral_plane v
  have hmass := integral_plane_sq v
  have hmg : ∫ u, twoEndSpline v (u - stateShift v) ^ 2 ≤ 4 * mU := by
    rw [integral_comp_sub_sq (twoEndSpline v) (stateShift v), hmU]
    exact integral_twoEndSpline_sq_le v
  have hmo : ∫ u, shiftedOdd v u ^ 2 ≤ 4 * m₀ := by
    simp only [shiftedOdd_eq]
    rw [integral_comp_sub_sq (twoEndOdd v) (stateShift v), hm₀]
    exact integral_twoEndOdd_sq_le v
  have hmg0 : 0 ≤ ∫ u, twoEndSpline v (u - stateShift v) ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  have hmo0 : 0 ≤ ∫ u, shiftedOdd v u ^ 2 := integral_nonneg fun u => sq_nonneg _
  -- the two diagonal entries are below `−D` times the mass
  have hcosh : Real.exp (v / 2) ≤ (Real.exp (v / 4) + Real.exp (-(v / 4))) ^ 2 := by
    have h1 : Real.exp (v / 2) = Real.exp (v / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h1]
    have := Real.exp_pos (-(v / 4))
    have := Real.exp_pos (v / 4)
    nlinarith
  obtain ⟨δg, hδg⟩ : ∃ δ, δ = -(smoothNeutral (fun u => twoEndSpline v (u - stateShift v)) +
      D * ∫ u, twoEndSpline v (u - stateShift v) ^ 2) := ⟨_, rfl⟩
  obtain ⟨δo, hδo⟩ : ∃ δ, δ = -(smoothNeutral (shiftedOdd v) + D * ∫ u, shiftedOdd v u ^ 2) :=
    ⟨_, rfl⟩
  have hδg0 : 0 < δg := by
    have h1 := hV₁ v hvV
    have h2 := mul_le_mul_of_nonneg_left hcosh (sq_nonneg splineCharge)
    have h3 : D * ∫ u, twoEndSpline v (u - stateShift v) ^ 2 ≤
        4 * E * mU * Real.exp (θ * v) := by
      have := mul_le_mul hDE hmg hmg0 (mul_nonneg hE0 (Real.exp_pos _).le)
      linarith
    rw [hδg, hNg, ← hT0]
    nlinarith
  have hδo0 : 0 < δo := by
    have h3 : D * ∫ u, shiftedOdd v u ^ 2 ≤ 4 * E * m₀ * Real.exp (θ * v) := by
      have := mul_le_mul hDE hmo hmo0 (mul_nonneg hE0 (Real.exp_pos _).le)
      linarith
    rw [hδo, hNo, ← hS0]
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min δg δo := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hδg0 hδo0
  have hδgδ : δ ≤ δg := by rw [hδ]; exact min_le_left _ _
  have hδoδ : δ ≤ δo := by rw [hδ]; exact min_le_right _ _
  obtain ⟨Mm, hMm⟩ : ∃ M, M = (∫ u, twoEndSpline v (u - stateShift v) ^ 2) +
      (∫ u, shiftedOdd v u ^ 2) + 1 := ⟨_, rfl⟩
  have hMm1 : 1 ≤ Mm := by rw [hMm]; linarith
  obtain ⟨ε, hε⟩ : ∃ ε, ε = δ / (8 * Mm) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  -- the supports
  have hshift : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u →
      5 + |v| / 2 < |u - stateShift v| := fun u hu => by
    unfold stateShift
    have hv' := abs_nonneg v
    rcases hu with h1 | h1
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
    · exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  have hsg : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → twoEndSpline v (u - stateShift v) = 0 :=
    fun u hu => (vanishing_twoEndSpline v _ (hshift u hu)).1
  have hso : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → shiftedOdd v u = 0 := fun u hu => by
    rw [shiftedOdd_eq]; exact (vanishing_twoEndSpline v _ (hshift u hu)).2
  have hss : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u →
      twoEndSpline v (u - stateShift v) + shiftedOdd v u = 0 := fun u hu => by
    rw [hsg u hu, hso u hu, add_zero]
  have hcs : ∀ {f : ℝ → ℝ}, (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
      HasCompactSupport f := fun {f} hf =>
    HasCompactSupport.intro (isCompact_Icc (a := Real.log 3) (b := Real.log K)) fun u hu => hf u (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h1 | h1
      · exact Or.inl h1.le
      · exact Or.inr h1.le)
  have hcg : ContDiff ℝ 2 fun u => twoEndSpline v (u - stateShift v) :=
    (contDiff_twoEndSpline v).comp (contDiff_id.sub contDiff_const)
  have hco : ContDiff ℝ 2 (shiftedOdd v) := contDiff_shiftedOdd v
  have hcsum : ContDiff ℝ 2 fun u => twoEndSpline v (u - stateShift v) + shiftedOdd v u :=
    hcg.add hco
  -- the block count: short blocks for the averages, a small pole cross term
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ, E₀ = HodgeTheoryOfAFixedPart.crossConstant (3 * K + 1) ^ 2 / ε +
      (3 + ((3 * K + 1 : ℕ) : ℝ) / 4 + 2 * HodgeTheoryOfAFixedPart.chebyshev (3 * K + 1) +
        Real.log (4 * Real.pi)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = ⌈Real.exp E₀⌉₊ + ⌈120 * (K : ℝ) * Mm / δ⌉₊ + 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by omega
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hRlog : E₀ ≤ Real.log R := by
    rw [Real.le_log_iff_exp_le hR0]
    calc Real.exp E₀ ≤ ⌈Real.exp E₀⌉₊ := Nat.le_ceil _
      _ ≤ R := by exact_mod_cast (show ⌈Real.exp E₀⌉₊ ≤ R by omega)
  have hRK : 15 * (K : ℝ) / R ≤ δ / (8 * Mm) := by
    have h1 : 120 * (K : ℝ) * Mm / δ ≤ R := by
      calc 120 * (K : ℝ) * Mm / δ ≤ ⌈120 * (K : ℝ) * Mm / δ⌉₊ := Nat.le_ceil _
        _ ≤ R := by exact_mod_cast (show ⌈120 * (K : ℝ) * Mm / δ⌉₊ ≤ R by omega)
    rw [div_le_iff₀ hδ0] at h1
    rw [div_le_div_iff₀ hR0 (by positivity)]
    linarith
  have hQR : R + 3 * K * R ≤ (3 * K + 1) * R := le_of_eq (by ring)
  obtain ⟨η, hη⟩ : ∃ η, η = δ / (8 * Mm) := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hBlock := eventually_abs_combNeutral_sub_le hR1 hQR hη0
  -- the samples along the scales `RB`
  have htN : Tendsto (fun B : ℕ => R * B) atTop atTop :=
    tendsto_atTop_mono (fun B => Nat.le_mul_of_pos_left B (by omega)) tendsto_id
  have hw : ∀ B : ℕ, R * B + 3 * K * (R * B) = R * B + B * (3 * K * R) := fun B => by ring
  have hlimN : ∀ {f : ℝ → ℝ}, ContDiff ℝ 2 f →
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
      Tendsto (fun B : ℕ => combNeutral (Ioc (R * B) (R * B + B * (3 * K * R)))
        (sampleCoord f (R * B))) atTop (𝓝 (smoothNeutral f)) := fun {f} hf hsf => by
    refine ((tendsto_combNeutral_sample hf (hcs hsf) hK1 hsf).comp htN).congr fun B => ?_
    show combNeutral (Ioc (R * B) (R * B + 3 * K * (R * B))) (sampleCoord f (R * B)) = _
    rw [hw B]
  have hlimM : ∀ {f : ℝ → ℝ}, ContDiff ℝ 2 f →
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u = 0) →
      Tendsto (fun B : ℕ => ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)),
        sampleCoord f (R * B) n ^ 2) atTop (𝓝 (∫ u, f u ^ 2)) := fun {f} hf hsf => by
    refine ((tendsto_sum_sq_sample hf.continuous hK1 hsf).comp htN).congr fun B => ?_
    show ∑ n ∈ Ioc (R * B) (R * B + 3 * K * (R * B)), sampleCoord f (R * B) n ^ 2 = _
    rw [hw B]
  obtain ⟨e₀, he₀⟩ : ∃ e, e = δ / (10 * (1 + D + δ)) := ⟨_, rfl⟩
  have he₀0 : 0 < e₀ := by rw [he₀]; positivity
  have hnear : ∀ {x : ℕ → ℝ} {l : ℝ}, Tendsto x atTop (𝓝 l) → ∀ᶠ B in atTop, |x B - l| ≤ e₀ :=
    fun {x l} hx => by
      filter_upwards [(Metric.tendsto_nhds.mp hx) e₀ he₀0] with B hB
      rw [Real.dist_eq] at hB
      exact hB.le
  obtain ⟨B, hBB, hg1, ho1, hs1, hg2, ho2, hs2, hB1⟩ := (hBlock.and ((hnear (hlimN hcg hsg)).and
    ((hnear (hlimN hco hso)).and ((hnear (hlimN hcsum hss)).and ((hnear (hlimM hcg hsg)).and
      ((hnear (hlimM hco hso)).and ((hnear (hlimM hcsum hss)).and
        (eventually_ge_atTop 1)))))))).exists
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  -- the plane on the window `(R, (3K + 1)R]`
  obtain ⟨cg, hcg'⟩ : ∃ c, c = sampleCoord (fun u => twoEndSpline v (u - stateShift v)) (R * B) :=
    ⟨_, rfl⟩
  obtain ⟨co, hco'⟩ : ∃ c, c = sampleCoord (shiftedOdd v) (R * B) := ⟨_, rfl⟩
  have hcsum' : sampleCoord (fun u => twoEndSpline v (u - stateShift v) + shiftedOdd v u) (R * B) =
      fun n => cg n + co n := by
    rw [hcg', hco']
    funext n
    simp only [HodgeTheoryOfAFixedPart.sampleCoord, degreeSample]
    ring
  rw [← hcg'] at hg1 hg2
  rw [← hco'] at ho1 ho2
  rw [hcsum'] at hs1 hs2
  rw [hNs] at hs1
  rw [hmass] at hs2
  refine absurd (h K R hK1 hR1) (not_le.mpr (lt_of_lt_of_le one_lt_two ?_))
  refine two_le_hermNegIndex_of_plane _
    (fun i : Fin (3 * K * R) => Real.sqrt B * blockMean (R * B) B (3 * K * R) cg (i : ℕ))
    (fun i : Fin (3 * K * R) => Real.sqrt B * blockMean (R * B) B (3 * K * R) co (i : ℕ))
    fun s t hst => ?_
  -- the coordinates of the packet `s g + t o`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun n => s * cg n + t * co n := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, x = fun j => Real.sqrt B * blockMean (R * B) B (3 * K * R) c j :=
    ⟨_, rfl⟩
  have hxlin : ∀ j : ℕ, s * (Real.sqrt B * blockMean (R * B) B (3 * K * R) cg j) +
      t * (Real.sqrt B * blockMean (R * B) B (3 * K * R) co j) = x j := fun j => by
    rw [hx, hc]
    simp only
    rw [blockMean_lin]
    ring
  simp only [hxlin]
  rw [sum_fin_neutralWindow_add_diag]
  -- the window matrix against the comb, and the block averages against the samples
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0.le
  have hbf : (fun n => x (blockIndex (R * B) B n)) =
      fun n => Real.sqrt B * blockMean (R * B) B (3 * K * R) c (blockIndex (R * B) B n) := by
    rw [hx]
  have hBl := hBB x
  rw [hbf, combNeutral_smul, hsB] at hBl
  have hdivB : (B : ℝ) * combNeutral (Ioc (R * B) (R * B + B * (3 * K * R)))
      (fun n => blockMean (R * B) B (3 * K * R) c (blockIndex (R * B) B n)) / B =
      combNeutral (Ioc (R * B) (R * B + B * (3 * K * R)))
        (fun n => blockMean (R * B) B (3 * K * R) c (blockIndex (R * B) B n)) := by
    rw [mul_div_cancel_left₀ _ hB0.ne']
  rw [hdivB] at hBl
  have hRB : R ≤ R * B := Nat.le_mul_of_pos_right R hBpos
  have hdiv : R * B / R = B := Nat.mul_div_cancel_left B (by omega)
  have hμ := HodgeTheoryOfAFixedPart.log_sub_row_ge (M := B * (3 * K * R)) (Q := 3 * K + 1)
    (by omega : 0 < R) hRB (le_of_eq (by ring))
  rw [hdiv] at hμ
  have hA := combNeutral_blockMean_le (N := R * B) (J := 3 * K * R) (Q := 3 * K + 1) hBpos
    (Nat.le_mul_of_pos_left B (by omega)) (le_of_eq (by ring)) hε0 (by
      have : HodgeTheoryOfAFixedPart.crossConstant (3 * K + 1) ^ 2 / ε ≤
          Real.log R - (3 + ((3 * K + 1 : ℕ) : ℝ) / 4 +
            2 * HodgeTheoryOfAFixedPart.chebyshev (3 * K + 1) + Real.log (4 * Real.pi)) := by
        rw [hE₀] at hRlog; linarith
      exact this.trans hμ) c
  have hKK : (B : ℝ) * ((B * (3 * K * R) : ℕ) : ℝ) / ((R * B : ℕ) : ℝ) ^ 2 = 3 * K / R := by
    have hRBne : ((R * B : ℕ) : ℝ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (by exact_mod_cast (Nat.mul_pos (by omega) hBpos).ne')
    rw [div_eq_div_iff hRBne hR0.ne']
    push_cast
    ring
  rw [hKK] at hA
  -- the norm of the coordinates
  have hxsq : ∑ j ∈ range (3 * K * R), x j ^ 2 ≤
      ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), c n ^ 2 := by
    have h1 : ∑ j ∈ range (3 * K * R), x j ^ 2 =
        ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)),
          blockMean (R * B) B (3 * K * R) c (blockIndex (R * B) B n) ^ 2 := by
      rw [sum_blockFunction_sq hBpos, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx]
      show (Real.sqrt B * blockMean (R * B) B (3 * K * R) c j) ^ 2 = _
      rw [mul_pow, hsB]
    rw [h1]
    exact HodgeTheoryOfAFixedPart.sum_blockMean_sq_le hBpos (R * B) (3 * K * R) c
  have hx0 : 0 ≤ ∑ j ∈ range (3 * K * R), x j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), c n ^ 2 := ⟨_, rfl⟩
  rw [← hX] at hA hxsq
  have hX0 : 0 ≤ X := by rw [hX]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- the quadratic forms in `(s, t)`
  have hcN : combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) c =
      s ^ 2 * combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) cg +
        s * t * (combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) (fun n => cg n + co n) -
          combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) cg -
            combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) co) +
        t ^ 2 * combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) co := by
    rw [hc]; exact combNeutral_lin _ s t cg co
  have hXl : X = s ^ 2 * ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), cg n ^ 2 +
      s * t * (∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), (cg n + co n) ^ 2 -
        ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), cg n ^ 2 -
          ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), co n ^ 2) +
      t ^ 2 * ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), co n ^ 2 := by
    rw [hX, hc]; exact sum_sq_lin _ s t cg co
  -- the size of the errors
  have hst2 : 2 * |s * t| ≤ s ^ 2 + t ^ 2 := by
    rw [abs_mul]; nlinarith [sq_nonneg (|s| - |t|), sq_abs s, sq_abs t]
  have hpos : 0 < s ^ 2 + t ^ 2 := by
    rcases hst with h0 | h0
    · have := pow_pos (abs_pos.mpr h0) 2; rw [_root_.sq_abs] at this; nlinarith [sq_nonneg t]
    · have := pow_pos (abs_pos.mpr h0) 2; rw [_root_.sq_abs] at this; nlinarith [sq_nonneg s]
  rw [abs_le] at hg1 ho1 hs1 hg2 ho2 hs2 hBl
  have hcross1 : s * t * (combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) (fun n => cg n + co n) -
      combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) cg -
        combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) co) ≤
      3 * e₀ * |s * t| := by
    have hb : |combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) (fun n => cg n + co n) -
        combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) cg -
          combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) co| ≤ 3 * e₀ := by
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ |s * t * _| := le_abs_self _
      _ = |s * t| * |_| := abs_mul _ _
      _ ≤ |s * t| * (3 * e₀) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = 3 * e₀ * |s * t| := by ring
  have hcross2 : s * t * (∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), (cg n + co n) ^ 2 -
      ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), cg n ^ 2 -
        ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), co n ^ 2) ≤ 3 * e₀ * |s * t| := by
    have hb : |∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), (cg n + co n) ^ 2 -
        ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), cg n ^ 2 -
          ∑ n ∈ Ioc (R * B) (R * B + B * (3 * K * R)), co n ^ 2| ≤ 3 * e₀ := by
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ |s * t * _| := le_abs_self _
      _ = |s * t| * |_| := abs_mul _ _
      _ ≤ |s * t| * (3 * e₀) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = 3 * e₀ * |s * t| := by ring
  -- the comparison chain
  obtain ⟨Ng, hNgd⟩ : ∃ N, N = smoothNeutral (fun u => twoEndSpline v (u - stateShift v)) :=
    ⟨_, rfl⟩
  obtain ⟨No, hNod⟩ : ∃ N, N = smoothNeutral (shiftedOdd v) := ⟨_, rfl⟩
  obtain ⟨mg, hmgd⟩ : ∃ m, m = ∫ u, twoEndSpline v (u - stateShift v) ^ 2 := ⟨_, rfl⟩
  obtain ⟨mo, hmod⟩ : ∃ m, m = ∫ u, shiftedOdd v u ^ 2 := ⟨_, rfl⟩
  rw [← hNgd] at hg1 hs1 hδg
  rw [← hNod] at ho1 hs1 hδo
  rw [← hmgd] at hg2 hs2 hδg hMm hmg0
  rw [← hmod] at ho2 hs2 hδo hMm hmo0
  have hCD : C * (K : ℝ) ^ θ ≤ D := by
    rw [hD]; exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hK0 θ)
  obtain ⟨lam, hlam⟩ : ∃ l, l = ε + 5 * (3 * (K : ℝ) / R) + η := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hlamM : lam * Mm ≤ 3 * δ / 8 := by
    have hMm0 : Mm ≠ 0 := (by linarith : (0 : ℝ) < Mm).ne'
    have h1 : 5 * (3 * (K : ℝ) / R) = 15 * (K : ℝ) / R := by ring
    have h2 : δ / (8 * Mm) * Mm = δ / 8 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hMm0]
    have hεM : ε * Mm = δ / 8 := by rw [hε]; exact h2
    have hηM : η * Mm = δ / 8 := by rw [hη]; exact h2
    have h3 := mul_le_mul_of_nonneg_right hRK (by linarith : (0 : ℝ) ≤ Mm)
    rw [h2] at h3
    rw [hlam, h1]
    nlinarith
  have hlamδ : lam ≤ δ := by
    have : lam ≤ lam * Mm := le_mul_of_one_le_right hlam0 hMm1
    linarith
  have he₀b : 5 / 2 * e₀ * (1 + D + lam) ≤ δ / 4 := by
    have h1 : e₀ * (1 + D + δ) = δ / 10 := by
      rw [he₀, div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt (by linarith : (0 : ℝ) < 1 + D + δ))]
    have h2 : e₀ * (1 + D + lam) ≤ e₀ * (1 + D + δ) :=
      mul_le_mul_of_nonneg_left (by linarith) he₀0.le
    linarith
  -- assemble: the form on the packet is below `−(3/8) δ (s² + t²)`
  have hstep : ∑ j ∈ range (3 * K * R), ∑ l ∈ range (3 * K * R),
        x j * x l * neutralBlock (3 * K + 1) (R + j) (R + l) +
      C * (K : ℝ) ^ θ * ∑ j ∈ range (3 * K * R), x j ^ 2 ≤
      combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) c + (D + lam) * X := by
    have h1 := mul_le_mul_of_nonneg_right hCD hx0
    have h2 := mul_le_mul_of_nonneg_left hxsq (by linarith : (0 : ℝ) ≤ η + D)
    rw [hlam]
    nlinarith [hBl.1, hBl.2, hA]
  have hcNb : combNeutral (Ioc (R * B) (R * B + B * (3 * K * R))) c ≤
      s ^ 2 * Ng + t ^ 2 * No + 5 / 2 * e₀ * (s ^ 2 + t ^ 2) := by
    rw [hcN]
    have h1 := mul_le_mul_of_nonneg_left hg1.2 (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_left ho1.2 (sq_nonneg t)
    have h3 := mul_le_mul_of_nonneg_left hst2 he₀0.le
    nlinarith [hcross1]
  have hXb : X ≤ s ^ 2 * mg + t ^ 2 * mo + 5 / 2 * e₀ * (s ^ 2 + t ^ 2) := by
    rw [hXl]
    have h1 := mul_le_mul_of_nonneg_left hg2.2 (sq_nonneg s)
    have h2 := mul_le_mul_of_nonneg_left ho2.2 (sq_nonneg t)
    have h3 := mul_le_mul_of_nonneg_left hst2 he₀0.le
    nlinarith [hcross2]
  have hDX := mul_le_mul_of_nonneg_left hXb (by linarith : (0 : ℝ) ≤ D + lam)
  have hg' : s ^ 2 * (Ng + D * mg) ≤ -(δ * s ^ 2) := by
    have := mul_le_mul_of_nonneg_left (show Ng + D * mg ≤ -δ by linarith) (sq_nonneg s)
    linarith
  have ho' : t ^ 2 * (No + D * mo) ≤ -(δ * t ^ 2) := by
    have := mul_le_mul_of_nonneg_left (show No + D * mo ≤ -δ by linarith) (sq_nonneg t)
    linarith
  have hlm : lam * (s ^ 2 * mg + t ^ 2 * mo) ≤ 3 * δ / 8 * (s ^ 2 + t ^ 2) := by
    have h1 : s ^ 2 * mg + t ^ 2 * mo ≤ Mm * (s ^ 2 + t ^ 2) := by
      have hmgM : mg ≤ Mm := by linarith
      have hmoM : mo ≤ Mm := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hmgM (sq_nonneg s),
        mul_le_mul_of_nonneg_left hmoM (sq_nonneg t)]
    have h2 := mul_le_mul_of_nonneg_left h1 hlam0
    have h3 := mul_le_mul_of_nonneg_right hlamM (by positivity : (0 : ℝ) ≤ s ^ 2 + t ^ 2)
    nlinarith
  have he' := mul_le_mul_of_nonneg_right he₀b (by positivity : (0 : ℝ) ≤ s ^ 2 + t ^ 2)
  have hfin := mul_pos hδ0 hpos
  nlinarith

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
