import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheIndexOfTheNeutralPartIsOnePlusTheNumberOfZerosRightOfTheLine
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheStepPacketsOfAWindowFormATowerUnderRefinement
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheInequalityAtFiniteScaleIsDecidedOnBlockAverages
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# The step-packet matrices of a ratio are decided on coarse blocks

Fix a ratio `Q` and a window `(R, R + J]` with `R + J ≤ QR`. Its refinement by `m` is the window
`(mR, mR + mJ]` on unit blocks. A step function on the fine blocks is the refinement of a step
function on the coarse blocks plus a part whose sum over each coarse block vanishes
(`IsCoarseNeutral`); the two parts are orthogonal (`sum_sq_refine_add`). With
`E_Q = 3 + Q/4 + 2ψ(Q) + log 4π` and `C_Q = 12 + 2Q + 2ψ(Q)`:

* **Coercivity** (`packetForm_coarseNeutral_ge`): `𝔚_Q(ζ) ≥ (log R − E_Q) Σ ζ_i²` on the
  coarse-neutral step packets.
* **Cross term** (`packetForm_refineStep_add_ge`): for `pq = 1`,
  `𝔚_Q(τ + ζ) ≥ 𝔚_Q(τ) − C_Q p Σ τ_j² + (log R − E_Q − C_Q q) Σ ζ_i²`.
* **Rate** (`packetForm_refined_ge_of_margin`): a margin `μ` of `𝔚_Q` on the blocks above `R`
  is a margin `μ − ε` on every refinement as soon as `log R ≥ E_Q + C_Q²/ε + μ`. The margins
  decrease along the tower; from the scale `R` on they decrease by at most
  `C_Q²/(log R − E_Q − μ)`. A positive margin `μ₀` at one scale `R` with
  `log R ≥ E_Q + 2C_Q²/μ₀ + μ₀` is a margin `μ₀/2` at every refinement
  (`packetForm_refined_ge_half_of_margin`): the sign of `𝔚_Q` with a margin on all step packets
  of a window is a statement about one matrix.
* **Index** (`hermNegIndex_blockWindow_refined_le`, `hermNegIndex_blockWindow_le_uniform`): for
  `log R ≥ E_Q` the block matrix of every refinement has at most `J` negative squares, and at
  every block size the block matrices of ratio at most `Q` have at most `(Q − 1)⌈e^{E_Q}⌉`
  negative squares.

The proofs are on the comb. Above the scale `mRB` take blocks of `mB` points: Weil's form is
coercive on the divisors with vanishing block sums, and the cross term with a divisor constant
on blocks is bounded, both uniformly in `B`. Divide by `B` and let `B → ∞`.
-/

open Finset Filter Topology Matrix
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (blockIndex chebyshev crossConstant crossConstant_pos)

local notation "combW" => HodgeTheoryOfAFixedPart.combForm

/-- The excess of the row of the pairing over the logarithm of the coarse scale:
`E_Q = 3 + Q/4 + 2ψ(Q) + log 4π`. -/
def rowExcess (Q : ℕ) : ℝ := 3 + (Q : ℝ) / 4 + 2 * chebyshev Q + Real.log (4 * Real.pi)

/-- A step function on fine blocks is neutral on coarse blocks: its sum over each group of `m`
consecutive blocks vanishes. -/
def IsCoarseNeutral (m : ℕ) (ζ : ℕ → ℝ) : Prop := ∀ j : ℕ, ∑ i ∈ range m, ζ (m * j + i) = 0

/-! ### Fine and coarse blocks on the comb -/

/-- The coarse block of a degree point is the coarse block of its fine block. -/
theorem blockIndex_mul (N B m n : ℕ) : blockIndex N (B * m) n = blockIndex N B n / m := by
  rw [HodgeTheoryOfAFixedPart.blockIndex, HodgeTheoryOfAFixedPart.blockIndex,
    Nat.div_div_eq_div_mul]

/-- The fine block of the point at position `a` of the coarse block `j`. -/
theorem blockIndex_coarse_add {B : ℕ} (hB : 0 < B) (N m j a : ℕ) :
    blockIndex N B (N + 1 + B * m * j + a) = m * j + a / B := by
  have h : N + 1 + B * m * j + a - N - 1 = B * (m * j) + a := by
    rw [Nat.mul_assoc]
    omega
  rw [HodgeTheoryOfAFixedPart.blockIndex, h, Nat.mul_add_div hB]

/-- A sum over `Bm` consecutive indices of a function of the quotient by `B`. -/
theorem sum_range_mul_div {B : ℕ} (hB : 0 < B) (m : ℕ) (g : ℕ → ℝ) :
    ∑ a ∈ range (B * m), g (a / B) = B * ∑ i ∈ range m, g i := by
  rw [sum_range_mul_eq B m, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ b ∈ range B, g ((B * i + b) / B) = g i := fun b hb => by
    rw [Nat.mul_add_div hB, Nat.div_eq_of_lt (Finset.mem_range.mp hb), add_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- A coarse-neutral step function, read on the fine blocks of `B` points, has vanishing sums
over the coarse blocks of `Bm` points. -/
theorem sum_filter_coarseNeutral {B m : ℕ} (hB : 0 < B) (hm : 0 < m) {ζ : ℕ → ℝ}
    (hζ : IsCoarseNeutral m ζ) (N J j : ℕ) :
    ∑ n ∈ (Ioc N (N + B * m * J)).filter (fun n => blockIndex N (B * m) n = j),
      ζ (blockIndex N B n) = 0 := by
  rw [HodgeTheoryOfAFixedPart.sum_filter_blockIndex (Nat.mul_pos hB hm) N J
    (fun n => ζ (blockIndex N B n)) j]
  by_cases hj : j < J
  · rw [if_pos hj]
    simp only [blockIndex_coarse_add hB]
    rw [sum_range_mul_div hB m (fun i => ζ (m * j + i)), hζ j, mul_zero]
  · rw [if_neg hj]

/-- The scale `N = mRB` with coarse blocks of `Bm` points. -/
theorem coarse_scale_facts {R m J Q B N : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hB : 1 ≤ B)
    (hQ : R + J ≤ Q * R) (hN : N = m * R * B) :
    R ≤ N ∧ B * m ≤ N ∧ N + B * m * J ≤ Q * N ∧ N / R = B * m := by
  subst hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc R = 1 * R * 1 := by ring
      _ ≤ m * R * B := Nat.mul_le_mul (Nat.mul_le_mul hm le_rfl) hB
  · calc B * m = m * 1 * B := by ring
      _ ≤ m * R * B := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hR) le_rfl
  · calc m * R * B + B * m * J = (R + J) * (m * B) := by ring
      _ ≤ Q * R * (m * B) := Nat.mul_le_mul_right _ hQ
      _ = Q * (m * R * B) := by ring
  · rw [show m * R * B = R * (B * m) by ring]
    exact Nat.mul_div_cancel_left _ hR

/-- **Coercivity on the comb.** Above the scale `N = mRB`, Weil's form of a coarse-neutral step
function on blocks of `B` points is at least `(log R − E_Q) Σ ζ²`. -/
theorem combForm_coarseNeutral_ge {R m J Q B N : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hB : 1 ≤ B)
    (hQ : R + J ≤ Q * R) (hN : N = m * R * B) {ζ : ℕ → ℝ} (hζ : IsCoarseNeutral m ζ) :
    (Real.log R - rowExcess Q) * ∑ n ∈ Ioc N (N + B * (m * J)), ζ (blockIndex N B n) ^ 2 ≤
      combW (Ioc N (N + B * (m * J))) (fun n => ζ (blockIndex N B n)) := by
  obtain ⟨hRN, -, hQN, hdiv⟩ := coarse_scale_facts hR hm hB hQ hN
  have hNpos : 0 < N := lt_of_lt_of_le hR hRN
  rw [(Nat.mul_assoc B m J).symm]
  have hzero : ∀ j : ℕ, ∑ n ∈ (Ioc N (N + B * m * J)).filter
      (fun n => blockIndex N (B * m) n = j), ζ (blockIndex N B n) = 0 :=
    fun j => sum_filter_coarseNeutral hB hm hζ N J j
  have hpair := HodgeTheoryOfAFixedPart.combPairing_le_of_blockSum_eq_zero hNpos
    (Nat.mul_pos hB hm) hQN (Finset.Subset.refl _) (fun n => ζ (blockIndex N B n)) hzero
  have hrow := HodgeTheoryOfAFixedPart.log_sub_row_ge (M := B * m * J) hR hRN hQN
  rw [hdiv] at hrow
  have hz0 : 0 ≤ ∑ n ∈ Ioc N (N + B * m * J), ζ (blockIndex N B n) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [HodgeTheoryOfAFixedPart.combForm,
    HodgeTheoryOfAFixedPart.degTwo_eq_zero_of_blockSum_eq_zero N (B * m) _ _ hzero, mul_zero,
    mul_zero, zero_sub]
  unfold rowExcess
  linarith [mul_le_mul_of_nonneg_right hrow hz0]

/-- **A coarse part and a neutral part on the comb.** Above the scale `N = mRB`, for a step
function `τ` on the coarse blocks, a coarse-neutral step function `ζ` on the fine blocks and
`pq = 1`: `𝔚(τ + ζ) ≥ 𝔚(τ) − C_Q p Σ τ² + (log R − E_Q − C_Q q) Σ ζ²`. -/
theorem combForm_coarse_add_ge {R m J Q B N : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hB : 1 ≤ B)
    (hQ : R + J ≤ Q * R) (hN : N = m * R * B) (τ : ℕ → ℝ) {ζ : ℕ → ℝ}
    (hζ : IsCoarseNeutral m ζ) {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) :
    combW (Ioc N (N + B * (m * J))) (fun n => τ (blockIndex N B n / m)) -
        crossConstant Q * p * ∑ n ∈ Ioc N (N + B * (m * J)), τ (blockIndex N B n / m) ^ 2 +
        (Real.log R - rowExcess Q - crossConstant Q * q) *
          ∑ n ∈ Ioc N (N + B * (m * J)), ζ (blockIndex N B n) ^ 2 ≤
      combW (Ioc N (N + B * (m * J)))
        (fun n => τ (blockIndex N B n / m) + ζ (blockIndex N B n)) := by
  have hco := combForm_coarseNeutral_ge hR hm hB hQ hN hζ
  obtain ⟨-, hBN, hQN, -⟩ := coarse_scale_facts hR hm hB hQ hN
  rw [(Nat.mul_assoc B m J).symm] at hco ⊢
  simp only [← blockIndex_mul]
  have hzero : ∀ j : ℕ, ∑ n ∈ (Ioc N (N + B * m * J)).filter
      (fun n => blockIndex N (B * m) n = j), ζ (blockIndex N B n) = 0 :=
    fun j => sum_filter_coarseNeutral hB hm hζ N J j
  have hcross := HodgeTheoryOfAFixedPart.two_mul_abs_formBilin_le (Nat.mul_pos hB hm) hBN hQN τ
    (fun n => ζ (blockIndex N B n)) hzero hp hpq
  rw [HodgeTheoryOfAFixedPart.combForm_add (Ioc N (N + B * m * J))
    (fun n => τ (blockIndex N (B * m) n)) (fun n => ζ (blockIndex N B n))]
  have hneg := neg_abs_le (HodgeTheoryOfAFixedPart.formBilin (Ioc N (N + B * m * J))
    (fun n => τ (blockIndex N (B * m) n)) (fun n => ζ (blockIndex N B n)))
  linarith

/-! ### Step packets -/

section Packets

variable {R m J Q : ℕ}

theorem refined_window (hR : 1 ≤ R) (hm : 1 ≤ m) (hQ : R + J ≤ Q * R) :
    1 ≤ m * R ∧ m * R + m * J ≤ Q * (m * R) :=
  ⟨Nat.mul_pos hm hR, by
    calc m * R + m * J = m * (R + J) := by ring
      _ ≤ m * (Q * R) := Nat.mul_le_mul_left m hQ
      _ = Q * (m * R) := by ring⟩

/-- Division of a comb inequality by the block size. -/
theorem div_block_identity {B : ℝ} (hB : B ≠ 0) (X a T c Z : ℝ) :
    (X - a * (B * T) + c * (B * Z)) / B = X / B - a * T + c * Z := by
  field_simp

/-- **Coercivity.** On the step packets of the refined window whose sums over the coarse blocks
vanish, `𝔚_Q ≥ (log R − E_Q) Σ ζ_i²`. -/
theorem packetForm_coarseNeutral_ge (hR : 1 ≤ R) (hm : 1 ≤ m) (hQ : R + J ≤ Q * R)
    {ζ : ℕ → ℝ} (hζ : IsCoarseNeutral m ζ) :
    (Real.log R - rowExcess Q) * ∑ i ∈ range (m * J), ζ i ^ 2 ≤
      packetForm Q (stepPacket (m * R) (m * J) ζ) := by
  obtain ⟨hmR, hQ'⟩ := refined_window hR hm hQ
  refine ge_of_tendsto (tendsto_combForm_blockFunction_div hmR hQ' ζ)
    (Filter.eventually_atTop.mpr ⟨1, fun B hB => ?_⟩)
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have h := combForm_coarseNeutral_ge hR hm hB hQ rfl hζ
  rw [sum_blockFunction_sq (R := m * R) (J := m * J) hB ζ] at h
  rw [le_div_iff₀ hB']
  linarith

/-- **A coarse part and a neutral part.** For a step function `τ` on the coarse blocks, read on
the fine blocks, a coarse-neutral `ζ` and `pq = 1`:
`𝔚_Q(τ + ζ) ≥ 𝔚_Q(τ) − C_Q p Σ τ² + (log R − E_Q − C_Q q) Σ ζ²`. -/
theorem packetForm_coarse_add_ge (hR : 1 ≤ R) (hm : 1 ≤ m) (hQ : R + J ≤ Q * R) (τ : ℕ → ℝ)
    {ζ : ℕ → ℝ} (hζ : IsCoarseNeutral m ζ) {p q : ℝ} (hp : 0 < p) (hpq : p * q = 1) :
    packetForm Q (stepPacket (m * R) (m * J) fun i => τ (i / m)) -
        crossConstant Q * p * ∑ i ∈ range (m * J), τ (i / m) ^ 2 +
        (Real.log R - rowExcess Q - crossConstant Q * q) * ∑ i ∈ range (m * J), ζ i ^ 2 ≤
      packetForm Q (stepPacket (m * R) (m * J) fun i => τ (i / m) + ζ i) := by
  obtain ⟨hmR, hQ'⟩ := refined_window hR hm hQ
  have h1 := tendsto_combForm_blockFunction_div hmR hQ' (fun i => τ (i / m))
  have h2 := tendsto_combForm_blockFunction_div hmR hQ' (fun i => τ (i / m) + ζ i)
  have key : ∀ B : ℕ, 1 ≤ B →
      combW (Ioc (m * R * B) (m * R * B + B * (m * J)))
            (fun n => τ (blockIndex (m * R * B) B n / m)) / B -
          crossConstant Q * p * ∑ i ∈ range (m * J), τ (i / m) ^ 2 +
          (Real.log R - rowExcess Q - crossConstant Q * q) * ∑ i ∈ range (m * J), ζ i ^ 2 ≤
        combW (Ioc (m * R * B) (m * R * B + B * (m * J)))
          (fun n => τ (blockIndex (m * R * B) B n / m) + ζ (blockIndex (m * R * B) B n)) / B := by
    intro B hB
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have h := combForm_coarse_add_ge hR hm hB hQ rfl τ hζ hp hpq
    have e1 := sum_blockFunction_sq (R := m * R) (J := m * J) hB (fun i => τ (i / m))
    have e2 := sum_blockFunction_sq (R := m * R) (J := m * J) hB ζ
    beta_reduce at e1
    rw [e1, e2] at h
    have hd := div_le_div_of_nonneg_right h hB'.le
    rwa [div_block_identity hB'.ne'] at hd
  exact le_of_tendsto_of_tendsto ((h1.sub tendsto_const_nhds).add tendsto_const_nhds) h2
    (Filter.eventually_atTop.mpr ⟨1, key⟩)

/-- **The cross term on step packets.** For a step function `τ` on the blocks above `R`, a
coarse-neutral `ζ` on the blocks of the refined window and `pq = 1`:
`𝔚_Q(τ + ζ) ≥ 𝔚_Q(τ) − C_Q p Σ τ_j² + (log R − E_Q − C_Q q) Σ ζ_i²`. -/
theorem packetForm_refineStep_add_ge (hR : 1 ≤ R) (hm : 1 ≤ m) (hQ : R + J ≤ Q * R)
    (τ : ℕ → ℝ) {ζ : ℕ → ℝ} (hζ : IsCoarseNeutral m ζ) {p q : ℝ} (hp : 0 < p)
    (hpq : p * q = 1) :
    packetForm Q (stepPacket R J τ) - crossConstant Q * p * ∑ j ∈ range J, τ j ^ 2 +
        (Real.log R - rowExcess Q - crossConstant Q * q) * ∑ i ∈ range (m * J), ζ i ^ 2 ≤
      packetForm Q (stepPacket (m * R) (m * J) fun i => refineStep m τ i + ζ i) := by
  have h := packetForm_coarse_add_ge hR hm hQ (fun j => τ j / Real.sqrt m) hζ hp hpq
  rw [← packetForm_stepPacket_refine hR hm Q J τ, ← sum_refineStep_sq hm J τ]
  exact h

/-! ### The orthogonal decomposition of a fine step function -/

/-- A refined coarse step function is orthogonal to a coarse-neutral one. -/
theorem sum_refineStep_mul_eq_zero (hm : 1 ≤ m) (J : ℕ) (τ : ℕ → ℝ) {ζ : ℕ → ℝ}
    (hζ : IsCoarseNeutral m ζ) : ∑ i ∈ range (m * J), refineStep m τ i * ζ i = 0 := by
  rw [sum_range_mul_eq]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h : ∀ i ∈ range m, refineStep m τ (m * j + i) * ζ (m * j + i) =
      τ j / Real.sqrt m * ζ (m * j + i) := fun i hi => by
    rw [refineStep_mul_add hm τ j (Finset.mem_range.mp hi)]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, hζ j, mul_zero]

/-- The mass of a refined coarse part plus a neutral part. -/
theorem sum_sq_refine_add (hm : 1 ≤ m) (J : ℕ) (τ : ℕ → ℝ) {ζ : ℕ → ℝ}
    (hζ : IsCoarseNeutral m ζ) :
    ∑ i ∈ range (m * J), (refineStep m τ i + ζ i) ^ 2 =
      ∑ j ∈ range J, τ j ^ 2 + ∑ i ∈ range (m * J), ζ i ^ 2 := by
  have hexp : ∑ i ∈ range (m * J), (refineStep m τ i + ζ i) ^ 2 =
      ∑ i ∈ range (m * J), refineStep m τ i ^ 2 +
        2 * ∑ i ∈ range (m * J), refineStep m τ i * ζ i + ∑ i ∈ range (m * J), ζ i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, sum_refineStep_mul_eq_zero hm J τ hζ, sum_refineStep_sq hm J τ]
  ring

/-- The sums of a fine step function over the coarse blocks, divided by `√m`: the coarse step
function whose refinement is the block average. -/
def coarseMean (m : ℕ) (σ : ℕ → ℝ) (j : ℕ) : ℝ := (∑ i ∈ range m, σ (m * j + i)) / Real.sqrt m

/-- A fine step function minus its block averages is coarse-neutral. -/
theorem isCoarseNeutral_sub_refine (hm : 1 ≤ m) (σ : ℕ → ℝ) :
    IsCoarseNeutral m fun i => σ i - refineStep m (coarseMean m σ) i := by
  intro j
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  have hs0 : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm').ne'
  have h : ∀ i ∈ range m, σ (m * j + i) - refineStep m (coarseMean m σ) (m * j + i) =
      σ (m * j + i) - coarseMean m σ j / Real.sqrt m := fun i hi => by
    rw [refineStep_mul_add hm _ j (Finset.mem_range.mp hi)]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, coarseMean, div_div, hs]
  field_simp
  ring

/-! ### The margins along the tower -/

/-- **The margin of a refinement, in the two parts.** If `𝔚_Q ≥ μ Σ τ_j²` on the step packets of
the blocks above `R` and `log R ≥ E_Q + C_Q²/ε + μ`, then on the refined window
`𝔚_Q(τ + ζ) ≥ (μ − ε) Σ (τ + ζ)_i²` for every coarse `τ` and coarse-neutral `ζ`. -/
theorem packetForm_refine_add_ge_of_margin (hR : 1 ≤ R) (hm : 1 ≤ m) (hQ : R + J ≤ Q * R)
    {μ ε : ℝ} (hε : 0 < ε)
    (hμ : ∀ τ : ℕ → ℝ, μ * ∑ j ∈ range J, τ j ^ 2 ≤ packetForm Q (stepPacket R J τ))
    (hlog : rowExcess Q + crossConstant Q ^ 2 / ε + μ ≤ Real.log R) (τ : ℕ → ℝ) {ζ : ℕ → ℝ}
    (hζ : IsCoarseNeutral m ζ) :
    (μ - ε) * ∑ i ∈ range (m * J), (refineStep m τ i + ζ i) ^ 2 ≤
      packetForm Q (stepPacket (m * R) (m * J) fun i => refineStep m τ i + ζ i) := by
  have hC := crossConstant_pos Q
  have hF := packetForm_refineStep_add_ge hR hm hQ τ hζ (p := ε / crossConstant Q)
    (q := crossConstant Q / ε) (div_pos hε hC)
    (by rw [div_mul_div_comm, mul_comm ε, div_self (mul_pos hC hε).ne'])
  have h1 : crossConstant Q * (ε / crossConstant Q) = ε := by field_simp
  have h2 : crossConstant Q * (crossConstant Q / ε) = crossConstant Q ^ 2 / ε := by ring
  rw [h1, h2] at hF
  have hZ0 : 0 ≤ ∑ i ∈ range (m * J), ζ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hμτ := hμ τ
  rw [sum_sq_refine_add hm J τ hζ]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤
    Real.log R - rowExcess Q - crossConstant Q ^ 2 / ε - (μ - ε)) hZ0]

/-- **The margins of the tower decrease at a logarithmic rate.** If `𝔚_Q ≥ μ Σ τ_j²` on the step
packets of the `J` blocks above `R` and `log R ≥ E_Q + C_Q²/ε + μ`, then `𝔚_Q ≥ (μ − ε) Σ σ_i²`
on the step packets of every refinement of the window. -/
theorem packetForm_refined_ge_of_margin (hR : 1 ≤ R) (hm : 1 ≤ m) (hQ : R + J ≤ Q * R)
    {μ ε : ℝ} (hε : 0 < ε)
    (hμ : ∀ τ : ℕ → ℝ, μ * ∑ j ∈ range J, τ j ^ 2 ≤ packetForm Q (stepPacket R J τ))
    (hlog : rowExcess Q + crossConstant Q ^ 2 / ε + μ ≤ Real.log R) (σ : ℕ → ℝ) :
    (μ - ε) * ∑ i ∈ range (m * J), σ i ^ 2 ≤ packetForm Q (stepPacket (m * R) (m * J) σ) := by
  have h := packetForm_refine_add_ge_of_margin hR hm hQ hε hμ hlog (coarseMean m σ)
    (isCoarseNeutral_sub_refine hm σ)
  have key : ∀ i, refineStep m (coarseMean m σ) i + (σ i - refineStep m (coarseMean m σ) i) =
      σ i := fun i => by ring
  simpa only [key] using h

/-- **One matrix decides the sign with a margin.** A margin `μ₀ > 0` of `𝔚_Q` on the step
packets of the blocks above one scale `R` with `log R ≥ E_Q + 2C_Q²/μ₀ + μ₀` is a margin `μ₀/2`
on the step packets of every refinement of the window. -/
theorem packetForm_refined_ge_half_of_margin (hR : 1 ≤ R) (hm : 1 ≤ m) (hQ : R + J ≤ Q * R)
    {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hμ : ∀ τ : ℕ → ℝ, μ₀ * ∑ j ∈ range J, τ j ^ 2 ≤ packetForm Q (stepPacket R J τ))
    (hlog : rowExcess Q + 2 * crossConstant Q ^ 2 / μ₀ + μ₀ ≤ Real.log R) (σ : ℕ → ℝ) :
    μ₀ / 2 * ∑ i ∈ range (m * J), σ i ^ 2 ≤ packetForm Q (stepPacket (m * R) (m * J) σ) := by
  have he : crossConstant Q ^ 2 / (μ₀ / 2) = 2 * crossConstant Q ^ 2 / μ₀ := by
    field_simp
  have h := packetForm_refined_ge_of_margin hR hm hQ (half_pos hμ₀) hμ
    (by rw [he]; exact hlog) σ
  rwa [show μ₀ - μ₀ / 2 = μ₀ / 2 by ring] at h

end Packets

/-! ### The index -/

theorem complexExtend_of_not_lt {J : ℕ} (c : Fin J → ℂ) {n : ℕ} (h : ¬ n < J) :
    complexExtend J c n = 0 :=
  dif_neg h

/-- The sum of complex block values over the coarse block `j`. -/
def coarseSum (m J j : ℕ) : (Fin (m * J) → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i ∈ range m, (LinearMap.proj (m * j + i) : (ℕ → ℂ) →ₗ[ℂ] ℂ).comp (complexExtend (m * J))

theorem coarseSum_apply (m J j : ℕ) (x : Fin (m * J) → ℂ) :
    coarseSum m J j x = ∑ i ∈ range m, complexExtend (m * J) x (m * j + i) := by
  simp [coarseSum, LinearMap.sum_apply]

/-- Complex block values with vanishing coarse sums have coarse-neutral real and imaginary
parts. -/
theorem isCoarseNeutral_re_im {m J : ℕ} {x : Fin (m * J) → ℂ}
    (hx : ∀ j : Fin J, coarseSum m J j x = 0) :
    IsCoarseNeutral m (fun n => (complexExtend (m * J) x n).re) ∧
      IsCoarseNeutral m (fun n => (complexExtend (m * J) x n).im) := by
  have hzero : ∀ j : ℕ, ∑ i ∈ range m, complexExtend (m * J) x (m * j + i) = 0 := by
    intro j
    by_cases hj : j < J
    · rw [← coarseSum_apply]
      exact hx ⟨j, hj⟩
    · refine Finset.sum_eq_zero fun i _ => complexExtend_of_not_lt x ?_
      have := Nat.mul_le_mul_left m (not_lt.mp hj)
      omega
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have h := congrArg Complex.re (hzero j)
    rwa [Complex.re_sum, Complex.zero_re] at h
  · have h := congrArg Complex.im (hzero j)
    rwa [Complex.im_sum, Complex.zero_im] at h

/-- **The index of a refinement.** If `log R ≥ E_Q`, the block matrix of every refinement of
the window of `J` blocks above `R` has at most `J` negative squares: it is nonnegative on the
block values with vanishing sums over the coarse blocks. -/
theorem hermNegIndex_blockWindow_refined_le {R m J Q : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m)
    (hQ : R + J ≤ Q * R) (hlog : rowExcess Q ≤ Real.log R) :
    hermNegIndex ((blockWindow Q (m * R) (m * J)).map (↑) :
      Matrix (Fin (m * J)) (Fin (m * J)) ℂ) ≤ J := by
  have hmR : 1 ≤ m * R := Nat.mul_pos hm hR
  have key : ∀ x : Fin (m * J) → ℂ, (∀ j : Fin J, coarseSum m J j x = 0) →
      0 ≤ hermQuad ((blockWindow Q (m * R) (m * J)).map (↑) :
        Matrix (Fin (m * J)) (Fin (m * J)) ℂ) x := by
    intro x hx
    obtain ⟨hre, him⟩ := isCoarseNeutral_re_im hx
    have hrest := hermQuad_blockWindow_restrict hmR Q (m * J) (complexExtend (m * J) x)
    rw [show (fun i : Fin (m * J) => complexExtend (m * J) x i) = x from
      funext (complexExtend_coe x)] at hrest
    rw [hrest]
    have h1 := packetForm_coarseNeutral_ge hR hm hQ hre
    have h2 := packetForm_coarseNeutral_ge hR hm hQ him
    have hs1 : 0 ≤ ∑ i ∈ range (m * J), (complexExtend (m * J) x i).re ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs2 : 0 ≤ ∑ i ∈ range (m * J), (complexExtend (m * J) x i).im ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith [mul_nonneg (sub_nonneg.mpr hlog) hs1, mul_nonneg (sub_nonneg.mpr hlog) hs2]
  have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
    (fun j : Fin J => coarseSum m J j) key
  rwa [Fintype.card_fin] at h

/-- Refinement of complex block values: the value of a block on each of its `m` parts, divided
by `√m`. -/
def complexRefine (m J : ℕ) : (Fin J → ℂ) →ₗ[ℂ] (Fin (m * J) → ℂ) where
  toFun c i := complexExtend J c ((i : ℕ) / m) / (Real.sqrt m : ℂ)
  map_add' c d := by
    ext i
    simp only [map_add, Pi.add_apply, add_div]
  map_smul' a c := by
    ext i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc]

/-- **Refinement does not lower the index.** -/
theorem hermNegIndex_blockWindow_le_refined {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m)
    (Q J : ℕ) :
    hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex ((blockWindow Q (m * R) (m * J)).map (↑) :
        Matrix (Fin (m * J)) (Fin (m * J)) ℂ) := by
  have hmR : 1 ≤ m * R := Nat.mul_pos hm hR
  refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_eq _ _ (complexRefine m J) fun c => ?_
  have hfine := hermQuad_blockWindow_restrict hmR Q (m * J)
    (fun n => complexExtend J c (n / m) / (Real.sqrt m : ℂ))
  have hcoarse := hermQuad_blockWindow_restrict hR Q J (complexExtend J c)
  rw [show (fun i : Fin J => complexExtend J c i) = c from funext (complexExtend_coe c)]
    at hcoarse
  have hre : (fun n : ℕ => (complexExtend J c (n / m) / (Real.sqrt m : ℂ)).re) =
      refineStep m fun n => (complexExtend J c n).re :=
    funext fun n => Complex.div_ofReal_re _ _
  have him : (fun n : ℕ => (complexExtend J c (n / m) / (Real.sqrt m : ℂ)).im) =
      refineStep m fun n => (complexExtend J c n).im :=
    funext fun n => Complex.div_ofReal_im _ _
  rw [hre, him, packetForm_stepPacket_refine hR hm, packetForm_stepPacket_refine hR hm,
    ← hcoarse] at hfine
  exact hfine

/-- A step packet does not change when blocks with the value zero are added. -/
theorem stepPacket_eq_of_le {J J' : ℕ} (hJ : J ≤ J') (R : ℕ) {σ : ℕ → ℝ}
    (hσ : ∀ i, J ≤ i → σ i = 0) : stepPacket R J' σ = stepPacket R J σ := by
  funext u
  rw [stepPacket, stepPacket]
  refine (Finset.sum_subset (Finset.range_mono hJ) fun i _ hi => ?_).symm
  rw [hσ i (not_lt.mp fun h => hi (Finset.mem_range.mpr h)), zero_mul]

/-- Complex block values of a window, extended by zero to a longer window. -/
def complexPad (J J' : ℕ) : (Fin J → ℂ) →ₗ[ℂ] (Fin J' → ℂ) where
  toFun c i := complexExtend J c i
  map_add' c d := by
    ext i
    simp only [map_add, Pi.add_apply]
  map_smul' a c := by
    ext i
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

/-- **A longer window above the same scale has at least the index.** -/
theorem hermNegIndex_blockWindow_mono {R : ℕ} (hR : 1 ≤ R) (Q : ℕ) {J J' : ℕ} (hJ : J ≤ J') :
    hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      hermNegIndex ((blockWindow Q R J').map (↑) : Matrix (Fin J') (Fin J') ℂ) := by
  refine HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_eq _ _ (complexPad J J') fun c => ?_
  have hlong := hermQuad_blockWindow_restrict hR Q J' (complexExtend J c)
  have hshort := hermQuad_blockWindow_restrict hR Q J (complexExtend J c)
  rw [show (fun i : Fin J => complexExtend J c i) = c from funext (complexExtend_coe c)]
    at hshort
  have hre : ∀ i, J ≤ i → (complexExtend J c i).re = 0 := fun i hi => by
    rw [complexExtend_of_not_lt c (not_lt.mpr hi), Complex.zero_re]
  have him : ∀ i, J ≤ i → (complexExtend J c i).im = 0 := fun i hi => by
    rw [complexExtend_of_not_lt c (not_lt.mpr hi), Complex.zero_im]
  rw [stepPacket_eq_of_le hJ R hre, stepPacket_eq_of_le hJ R him, ← hshort] at hlong
  exact hlong

/-- **The index at a ratio is bounded at every block size.** The block matrix of a window
`(R, R + J]` of ratio at most `Q` has at most `(Q − 1)⌈e^{E_Q}⌉` negative squares, whatever the
block size. -/
theorem hermNegIndex_blockWindow_le_uniform {Q R J : ℕ} (hR : 1 ≤ R) (hQ : R + J ≤ Q * R) :
    hermNegIndex ((blockWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤
      (Q - 1) * ⌈Real.exp (rowExcess Q)⌉₊ := by
  obtain ⟨k, rfl⟩ : ∃ k, Q = k + 1 := by
    rcases Q with _ | k
    · rw [Nat.zero_mul] at hQ
      omega
    · exact ⟨k, rfl⟩
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, R₀ = ⌈Real.exp (rowExcess (k + 1))⌉₊ := ⟨_, rfl⟩
  rw [← hR₀, Nat.add_sub_cancel]
  have hR₀pos : 1 ≤ R₀ := by
    rw [hR₀]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hlog : rowExcess (k + 1) ≤ Real.log R₀ := by
    rw [Real.le_log_iff_exp_le (by exact_mod_cast hR₀pos), hR₀]
    exact Nat.le_ceil _
  have hJ : J ≤ k * R := by
    have e : (k + 1) * R = k * R + R := by ring
    omega
  have hpad : R₀ * J ≤ R * (k * R₀) := by
    calc R₀ * J ≤ R₀ * (k * R) := Nat.mul_le_mul_left _ hJ
      _ = R * (k * R₀) := by ring
  -- refine by `R₀`, extend the window to `k R₀` coarse blocks of `R` fine blocks
  have h1 := hermNegIndex_blockWindow_le_refined hR hR₀pos (k + 1) J
  have h2 := hermNegIndex_blockWindow_mono (R := R₀ * R) (Nat.mul_pos hR₀pos hR) (k + 1) hpad
  have h3 := hermNegIndex_blockWindow_refined_le (R := R₀) (m := R) (J := k * R₀) (Q := k + 1)
    hR₀pos hR (le_of_eq (by ring)) hlog
  rw [Nat.mul_comm R₀ R] at h1 h2
  exact h1.trans (h2.trans h3)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
