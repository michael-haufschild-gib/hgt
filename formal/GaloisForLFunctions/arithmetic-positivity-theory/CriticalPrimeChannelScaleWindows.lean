import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalCompleteFormHighScalePositivity
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare

/-!
# The critical prime channel on scale windows

A **scale window** `[M, LM]` contains many dyadic blocks. On it the critical prime channel obeys a
logarithmic law in the width `L`:

`|∑_r Λ(r) r^{-1/2} ac(log r)| ≤ C_W (3 + log L) ∑ b_n²`.

Two harmonic regimes combine.

* **Uniform regime.** For every finite family, the rows and columns of the cross-scale kernel are
  spaced sums, so each harmonic bilinear form costs `O(∑ b_n²)`. This uses the Schur test for the
  smooth parts and the Montgomery–Vaughan bound for the jump kernel. Every dilation correlation is
  therefore `O(∑ b_n²)`, with no decay in `r`.
* **Window regime.** If `lr ≥ 8Lk`, every kernel argument has size `≥ qM/2`, which costs
  `O(L/(lr))`. Below that line the harmonic weight pays `1/√k ≤ √(8L/r)`. Each dilation correlation
  with `r ≥ L` is therefore `O(√(L/r) ∑ b_n²)`.

Since `min(1, √(L/r)) ≤ (L/r)^ε` and `∑ Λ(r) r^{-1-ε} ≤ 6(1+ε)/ε`, the choice `ε = 1/(2 + log L)`
gives the logarithm.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### Scale windows and support-agnostic kernel bounds -/

/-- A finite family lives in the **scale window** `[M, L M]`. -/
def ScaleWindow (S : Finset ℕ) (M L : ℕ) : Prop := ∀ n ∈ S, M ≤ n + 1 ∧ n + 1 ≤ L * M

/-- Row/column bound `A + 4B(12/11)²(π²/3)` of the cross-scale kernel at harmonics `≥ 1`. -/
def crossSpacedBound (A B : ℝ) : ℝ := A + 4 * B * (12 / 11) ^ 2 * (Real.pi ^ 2 / 3)

private theorem sum_abs_spaced_branch_le {F : ℝ → ℝ} {A B : ℝ} (hA : ∀ f, |F f| ≤ A)
    (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) (S : Finset ℕ) {q : ℝ} (hq : 1 ≤ q)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : ℝ) (j : Bool) :
    ∑ n ∈ S, |F (x - σ * (q * scaleBranch j n))| ≤ crossSpacedBound A B := by
  have hq0 : 0 < q := by linarith
  have h := sum_abs_le_of_spaced hA hB hB0 S (fun n => σ * (q * scaleBranch j n)) x
    (s := 11 / 12 * q) (by positivity) fun m _ m' _ => by
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul, abs_of_pos hq0]
      have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
      rw [hσ1, one_mul]
      calc 11 / 12 * q * |(m : ℝ) - m'| = q * (11 / 12 * |(m : ℝ) - m'|) := by ring
        _ ≤ q * |scaleBranch j m - scaleBranch j m'| :=
            mul_le_mul_of_nonneg_left (scaleBranch_spacing j m m') hq0.le
  refine h.trans ?_
  unfold crossSpacedBound
  have : 4 * B / (11 / 12 * q) ^ 2 ≤ 4 * B * (12 / 11) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (11 / 12 * q) ^ 2 * (12 / 11) ^ 2 := by nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 3)
  linarith

/-- **Support-agnostic cross-kernel bound.** For harmonic frequencies `p, q ≥ 1` and every finite
family, `|∑_{n,n'} b_n b_{n'} K_F(p, q; n, n')| ≤ 4 (A + 4B(12/11)²π²/3) ∑ b_n²`: rows and
columns of the kernel are spaced sums. -/
theorem abs_bilinear_dyadicCrossKernel_le_uniform {F : ℝ → ℝ} {A B : ℝ} (hA : ∀ f, |F f| ≤ A)
    (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) (S : Finset ℕ) {p q : ℝ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (b : ℕ → ℝ) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel F p q n n'| ≤
      4 * crossSpacedBound A B * ∑ n ∈ S, b n ^ 2 := by
  have hA' : ∀ f, |(fun f => F (-f)) f| ≤ A := fun f => hA _
  have hB' : ∀ f, f ≠ 0 → |(fun f => F (-f)) f| ≤ B / f ^ 2 := fun f hf => by
    have := hB (-f) (neg_ne_zero.mpr hf); rwa [neg_sq] at this
  have hK (n n' : ℕ) : |dyadicCrossKernel F p q n n'| ≤ ∑ i : Bool, ∑ j : Bool,
      (|F (p * scaleBranch i n - q * scaleBranch j n')| +
        |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2 := by
    unfold dyadicCrossKernel
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have hs : |scaleBranchSign i * scaleBranchSign j| = 1 := by
      unfold scaleBranchSign; cases i <;> cases j <;> norm_num
    rw [abs_mul, hs, one_mul, abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  refine abs_bilinear_le_of_row_col S b _ (fun n _ => ?_) (fun n' _ => ?_)
  · refine (Finset.sum_le_sum fun n' _ => hK n n').trans ?_
    rw [Finset.sum_comm]
    calc ∑ i : Bool, ∑ n' ∈ S, ∑ j : Bool, (|F (p * scaleBranch i n - q * scaleBranch j n')| +
          |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2
        = ∑ i : Bool, ∑ j : Bool, (∑ n' ∈ S, |F (p * scaleBranch i n - 1 * (q * scaleBranch j n'))| +
          ∑ n' ∈ S, |F (p * scaleBranch i n - (-1) * (q * scaleBranch j n'))|) / 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun n' _ => ?_
          congr 3 <;> ring_nf
      _ ≤ ∑ _i : Bool, ∑ _j : Bool, (crossSpacedBound A B + crossSpacedBound A B) / 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          gcongr
          · exact sum_abs_spaced_branch_le hA hB hB0 S hq 1 (Or.inl rfl) _ j
          · exact sum_abs_spaced_branch_le hA hB hB0 S hq (-1) (Or.inr rfl) _ j
      _ = 4 * crossSpacedBound A B := by simp only [Fintype.sum_bool]; ring
  · refine (Finset.sum_le_sum fun n _ => hK n n').trans ?_
    rw [Finset.sum_comm]
    calc ∑ i : Bool, ∑ n ∈ S, ∑ j : Bool, (|F (p * scaleBranch i n - q * scaleBranch j n')| +
          |F (p * scaleBranch i n + q * scaleBranch j n')|) / 2
        = ∑ i : Bool, ∑ j : Bool, (∑ n ∈ S, |(fun f => F (-f)) (q * scaleBranch j n' -
            1 * (p * scaleBranch i n))| + ∑ n ∈ S, |(fun f => F (-f)) (-(q * scaleBranch j n') -
            1 * (p * scaleBranch i n))|) / 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          refine Finset.sum_congr rfl fun n _ => ?_
          simp only
          congr 3 <;> ring_nf
      _ ≤ ∑ _i : Bool, ∑ _j : Bool, (crossSpacedBound A B + crossSpacedBound A B) / 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          gcongr
          · exact sum_abs_spaced_branch_le hA' hB' hB0 S hp 1 (Or.inl rfl) _ i
          · exact sum_abs_spaced_branch_le hA' hB' hB0 S hp 1 (Or.inl rfl) _ i
      _ = 4 * crossSpacedBound A B := by simp only [Fintype.sum_bool]; ring

private theorem sum_sum_bool_swap (S : Finset ℕ) (T : Bool → Bool → ℕ → ℕ → ℝ) :
    ∑ n ∈ S, ∑ n' ∈ S, ∑ i : Bool, ∑ j : Bool, T i j n n' =
      ∑ i : Bool, ∑ j : Bool, ∑ n ∈ S, ∑ n' ∈ S, T i j n n' := by
  simp only [Fintype.sum_bool, Finset.sum_add_distrib]

/-- **Support-agnostic jump cross-kernel bound.** For `p, q ≥ 1` and every finite family,
`|∑ b_n b_{n'} K_j(p, q; n, n')| ≤ 4 c_J ∑ b_n²` by Montgomery–Vaughan on every branch pair. -/
theorem abs_bilinear_dyadicCrossKernel_jump_le_uniform (S : Finset ℕ) {p q : ℝ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) (b : ℕ → ℝ) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n'| ≤
      4 * (1 + 13 / (Real.pi * (11 / 12))) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  set c := 1 + 13 / (Real.pi * (11 / 12))
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK (n n' : ℕ) : dyadicCrossKernel dyadicJumpKernel p q n n' = ∑ i : Bool, ∑ j : Bool,
      scaleBranchSign i * scaleBranchSign j / 2 *
        (dyadicJumpKernel (p * scaleBranch i n - q * scaleBranch j n') +
          dyadicJumpKernel (p * scaleBranch i n - -(q * scaleBranch j n'))) := by
    unfold dyadicCrossKernel
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sub_neg_eq_add]; ring
  have hexp : ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n' =
      ∑ i : Bool, ∑ j : Bool, scaleBranchSign i * scaleBranchSign j / 2 *
        ((∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicJumpKernel (p * scaleBranch i n - q * scaleBranch j n')) +
         (∑ n ∈ S, ∑ n' ∈ S, b n * b n' *
            dyadicJumpKernel (p * scaleBranch i n - -(q * scaleBranch j n')))) := by
    simp only [hK, Finset.mul_sum]
    rw [sum_sum_bool_swap]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
    ring
  have hsgn (i j : Bool) : |scaleBranchSign i * scaleBranchSign j / 2| = 1 / 2 := by
    unfold scaleBranchSign; cases i <;> cases j <;> norm_num
  have hI (i j : Bool) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
      |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicJumpKernel (p * scaleBranch i n - σ * (q * scaleBranch j n'))| ≤
        c * E := by
    refine abs_bilinear_dyadicJumpKernel_le b (by norm_num) (dilated_scaleBranch_sep hp i S)
      fun n hn m hm hnm => ?_
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
    rw [← mul_sub, abs_mul, hσ1, one_mul]
    exact dilated_scaleBranch_sep hq j S n hn m hm hnm
  rw [hexp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Bool, |∑ j : Bool, _| ≤ ∑ _i : Bool, ∑ _j : Bool, 1 / 2 * (c * E + c * E) := by
        refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, hsgn]
        gcongr
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · simpa only [one_mul] using hI i j 1 (Or.inl rfl)
        · simpa only [neg_mul, one_mul] using hI i j (-1) (Or.inr rfl)
    _ = 4 * c * E := by simp only [Fintype.sum_bool]; ring

private theorem card_le_of_scaleWindow {S : Finset ℕ} {M L : ℕ} (hS : ScaleWindow S M L) :
    (S.card : ℝ) ≤ L * M := by
  have : S ⊆ Finset.range (L * M) := fun n hn => Finset.mem_range.mpr (by have := (hS n hn).2; omega)
  exact_mod_cast (Finset.card_le_card this).trans (by simp)

private theorem scaleBranch_mem_window {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hS : ScaleWindow S M L) (i : Bool) {n : ℕ} (hn : n ∈ S) :
    (M : ℝ) ≤ scaleBranch i n ∧ scaleBranch i n ≤ 2 * L * M := by
  have hb := scaleBranch_bounds i n
  have h1 : (M : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (hS n hn).1
  have h2 : ((n + 1 : ℕ) : ℝ) ≤ L * M := by exact_mod_cast (hS n hn).2
  have hLM : (1 : ℝ) ≤ L * M := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  constructor <;> linarith [hb.1, hb.2]

/-- Far from resonance every kernel argument has size at least `qM/2`. -/
private theorem far_args {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L)
    {p q : ℝ} (hp : 1 ≤ p) (hfar : 8 * L * p ≤ q) (i j : Bool) {n n' : ℕ} (hn : n ∈ S) (hn' : n' ∈ S) :
    q * M / 2 ≤ |p * scaleBranch i n - q * scaleBranch j n'| ∧
      q * M / 2 ≤ |p * scaleBranch i n + q * scaleBranch j n'| := by
  have hx := scaleBranch_mem_window hM hL hS i hn
  have hy := scaleBranch_mem_window hM hL hS j hn'
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hq0 : 0 < q := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  constructor
  · rw [abs_sub_comm]
    refine le_abs.mpr (Or.inl ?_)
    have : p * scaleBranch i n ≤ q * M / 4 := by
      calc p * scaleBranch i n ≤ p * (2 * L * M) := by nlinarith [hx.2]
        _ = 2 * L * p * M := by ring
        _ ≤ q / 4 * M := by nlinarith
        _ = q * M / 4 := by ring
    nlinarith [hy.1]
  · refine le_abs.mpr (Or.inl ?_)
    nlinarith [hx.1, hy.1]

/-- **Far kernel bound on a window.** If `q ≥ 8Lp` then `|∑ b b K_F(p, q)| ≤ (16 L B/q²) ∑ b_n²`. -/
theorem abs_bilinear_dyadicCrossKernel_le_far {F : ℝ → ℝ} {B : ℝ}
    (hB : ∀ f, f ≠ 0 → |F f| ≤ B / f ^ 2) (hB0 : 0 ≤ B) {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M)
    (hL : 1 ≤ L) (hS : ScaleWindow S M L) {p q : ℝ} (hp : 1 ≤ p) (hfar : 8 * L * p ≤ q) (b : ℕ → ℝ) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel F p q n n'| ≤
      16 * L * B / q ^ 2 * ∑ n ∈ S, b n ^ 2 := by
  have hM0 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq0 : 0 < q := by nlinarith
  have hF (z : ℝ) (hz : q * M / 2 ≤ |z|) : |F z| ≤ 4 * B / (q ^ 2 * M ^ 2) := by
    have hz0 : z ≠ 0 := fun h => by rw [h, abs_zero] at hz; nlinarith
    refine (hB z hz0).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (q * M / 2) ^ 2 ≤ z ^ 2 := by
      rw [← sq_abs z]; exact pow_le_pow_left₀ (by positivity) hz 2
    nlinarith
  have hK (n : ℕ) (hn : n ∈ S) (n' : ℕ) (hn' : n' ∈ S) :
      |dyadicCrossKernel F p q n n'| ≤ 16 * B / (q ^ 2 * M ^ 2) := by
    unfold dyadicCrossKernel
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Bool, |∑ j : Bool, _| ≤ ∑ _i : Bool, ∑ _j : Bool, 4 * B / (q ^ 2 * M ^ 2) := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)
          have hs : |scaleBranchSign i * scaleBranchSign j| = 1 := by
            unfold scaleBranchSign; cases i <;> cases j <;> norm_num
          obtain ⟨h1, h2⟩ := far_args hM hL hS hp hfar i j hn hn'
          rw [abs_mul, hs, one_mul, abs_div, abs_two]
          calc |F (p * scaleBranch i n - q * scaleBranch j n') +
                F (p * scaleBranch i n + q * scaleBranch j n')| / 2 ≤
                (4 * B / (q ^ 2 * M ^ 2) + 4 * B / (q ^ 2 * M ^ 2)) / 2 := by
                gcongr
                exact (abs_add_le _ _).trans (add_le_add (hF _ h1) (hF _ h2))
            _ = 4 * B / (q ^ 2 * M ^ 2) := by ring
      _ = 16 * B / (q ^ 2 * M ^ 2) := by simp only [Fintype.sum_bool]; ring
  set E := ∑ n ∈ S, b n ^ 2
  have hcs : (∑ n ∈ S, |b n|) ^ 2 ≤ S.card * E := by
    simpa only [sq_abs] using (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |b i|))
  have hcard := card_le_of_scaleWindow hS
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel F p q n n'| ≤
        ∑ n ∈ S, ∑ n' ∈ S, |b n| * |b n'| * (16 * B / (q ^ 2 * M ^ 2)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' hn' => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hK n hn n' hn') (by positivity)
    _ = (∑ n ∈ S, |b n|) ^ 2 * (16 * B / (q ^ 2 * M ^ 2)) := by
        rw [show (∑ n ∈ S, |b n|) ^ 2 = (∑ n ∈ S, |b n|) * ∑ n ∈ S, |b n| from sq _,
          Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_mul]
    _ ≤ (L * M * E) * (16 * B / (q ^ 2 * M ^ 2)) := by
        gcongr
        exact hcs.trans (mul_le_mul_of_nonneg_right hcard hE)
    _ ≤ 16 * L * B / q ^ 2 * E := by
        rw [show L * M * E * (16 * B / (q ^ 2 * M ^ 2)) = 16 * L * B / q ^ 2 * E * (1 / M) by
          field_simp]
        have : 1 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
        have h0 : 0 ≤ 16 * L * B / q ^ 2 * E := by positivity
        nlinarith

/-- **Far jump bound on a window.** If `q ≥ 8Lp` then `|∑ b b K_j(p, q)| ≤ (4L/(πq)) ∑ b_n²`. -/
theorem abs_bilinear_dyadicCrossKernel_jump_le_far {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M)
    (hL : 1 ≤ L) (hS : ScaleWindow S M L) {p q : ℝ} (hp : 1 ≤ p) (hfar : 8 * L * p ≤ q) (b : ℕ → ℝ) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n'| ≤
      4 * L / (Real.pi * q) * ∑ n ∈ S, b n ^ 2 := by
  have hM0 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq0 : 0 < q := by nlinarith
  have hF (z : ℝ) (hz : q * M / 2 ≤ |z|) : |dyadicJumpKernel z| ≤ 1 / (Real.pi * q * M) := by
    have hz0 : z ≠ 0 := fun h => by rw [h, abs_zero] at hz; nlinarith
    refine (abs_dyadicJumpKernel_le_inv hz0).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  have hK (n : ℕ) (hn : n ∈ S) (n' : ℕ) (hn' : n' ∈ S) :
      |dyadicCrossKernel dyadicJumpKernel p q n n'| ≤ 4 / (Real.pi * q * M) := by
    unfold dyadicCrossKernel
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Bool, |∑ j : Bool, _| ≤ ∑ _i : Bool, ∑ _j : Bool, 1 / (Real.pi * q * M) := by
          refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)
          have hs : |scaleBranchSign i * scaleBranchSign j| = 1 := by
            unfold scaleBranchSign; cases i <;> cases j <;> norm_num
          obtain ⟨h1, h2⟩ := far_args hM hL hS hp hfar i j hn hn'
          rw [abs_mul, hs, one_mul, abs_div, abs_two]
          calc |dyadicJumpKernel (p * scaleBranch i n - q * scaleBranch j n') +
                dyadicJumpKernel (p * scaleBranch i n + q * scaleBranch j n')| / 2 ≤
                (1 / (Real.pi * q * M) + 1 / (Real.pi * q * M)) / 2 := by
                gcongr
                exact (abs_add_le _ _).trans (add_le_add (hF _ h1) (hF _ h2))
            _ = 1 / (Real.pi * q * M) := by ring
      _ = 4 / (Real.pi * q * M) := by simp only [Fintype.sum_bool]; ring
  set E := ∑ n ∈ S, b n ^ 2
  have hcs : (∑ n ∈ S, |b n|) ^ 2 ≤ S.card * E := by
    simpa only [sq_abs] using (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |b i|))
  have hcard := card_le_of_scaleWindow hS
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n'| ≤
        ∑ n ∈ S, ∑ n' ∈ S, |b n| * |b n'| * (4 / (Real.pi * q * M)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n' hn' => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hK n hn n' hn') (by positivity)
    _ = (∑ n ∈ S, |b n|) ^ 2 * (4 / (Real.pi * q * M)) := by
        rw [show (∑ n ∈ S, |b n|) ^ 2 = (∑ n ∈ S, |b n|) * ∑ n ∈ S, |b n| from sq _,
          Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_mul]
    _ ≤ (L * M * E) * (4 / (Real.pi * q * M)) := by
        gcongr
        exact hcs.trans (mul_le_mul_of_nonneg_right hcard hE)
    _ = 4 * L / (Real.pi * q) * E := by field_simp

/-! ### Uniform and window-decaying dilation bounds -/

private theorem summable_inv_sq_prod : Summable fun p : ℕ × ℕ => 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) :=
  Summable.mul_of_nonneg (f := fun l : ℕ => 1 / (l : ℝ) ^ 2) (g := fun l : ℕ => 1 / (l : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.mpr one_lt_two) (Real.summable_one_div_nat_pow.mpr one_lt_two)
    (fun _ => by positivity) (fun _ => by positivity)

private theorem summable_inv_sqrt_prod :
    Summable fun p : ℕ × ℕ => 1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2) :=
  Summable.mul_of_nonneg (f := fun k : ℕ => 1 / ((k : ℝ) * Real.sqrt k))
    (g := fun l : ℕ => 1 / (l : ℝ) ^ 2) summable_inv_mul_sqrt
    (Real.summable_one_div_nat_pow.mpr one_lt_two) (fun _ => by positivity) (fun _ => by positivity)

private theorem tsum_inv_sq_prod :
    ∑' p : ℕ × ℕ, 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) = (Real.pi ^ 2 / 6) ^ 2 := by
  have hz2 : Summable fun l : ℕ => 1 / (l : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hn2 : Summable fun l : ℕ => ‖1 / (l : ℝ) ^ 2‖ := hz2.abs.congr fun l => (Real.norm_eq_abs _).symm
  rw [← tsum_mul_tsum_of_summable_norm hn2 hn2, hasSum_zeta_two.tsum_eq]
  ring

/-- **Uniform harmonic bound.** If every harmonic bilinear form at `(k, lr)` is at most `U ∑ b_n²`,
then `|∫_{v>1} φ B_b(v) B_b(rv)| ≤ (4/π⁴) U (π²/6)² ∑ b_n²`, for every finite family. -/
theorem abs_integral_weight_dilate_le_of_uniform {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1))
    (S : Finset ℕ) (b : ℕ → ℝ) (r : ℕ) {U : ℝ} (hU0 : 0 ≤ U)
    (hU : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → |∑ n ∈ S, ∑ n' ∈ S, b n * b n' *
      dyadicCrossKernel (weightCosineTransform φ) k ((l * r : ℕ) : ℝ) n n'| ≤ U * ∑ n ∈ S, b n ^ 2) :
    |∫ v in Ioi 1, φ v * (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      4 / Real.pi ^ 4 * (U * (Real.pi ^ 2 / 6) ^ 2) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have h := abs_integral_weight_realPhaseCombination_dilate_le_of_bilinear hφ S b r
    (μ := fun p => U * E * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)))
    (summable_inv_sq_prod.mul_left (U * E)) (fun p => by positivity) fun p hk hl => by
      have := hU p.1 p.2 hk hl
      calc 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) * |_| ≤
            1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) * (U * E) := by gcongr
        _ = _ := by ring
  refine h.trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_inv_sq_prod]
  ring

/-- **Window-decaying harmonic bound.** On a scale window `[M, LM]` and for `r ≥ L`, if the harmonic
bilinear forms are at most `U ∑ b²` always and at most `V (L/(lr)) ∑ b²` when `lr ≥ 8Lk`, then
`|∫_{v>1} φ B_b(v)B_b(rv)| ≤ (4/π⁴) √(L/r) (√8 U Z_{3/2} Z_2 + V Z_2²) ∑ b_n²`. -/
theorem abs_integral_weight_dilate_le_of_window {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1))
    (S : Finset ℕ) (b : ℕ → ℝ) {L r : ℕ} (hL : 1 ≤ L) (hr : L ≤ r) {U V : ℝ} (hU0 : 0 ≤ U)
    (hV0 : 0 ≤ V)
    (hU : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → |∑ n ∈ S, ∑ n' ∈ S, b n * b n' *
      dyadicCrossKernel (weightCosineTransform φ) k ((l * r : ℕ) : ℝ) n n'| ≤ U * ∑ n ∈ S, b n ^ 2)
    (hV : ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → 8 * (L : ℝ) * k ≤ ((l * r : ℕ) : ℝ) →
      |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform φ) k
        ((l * r : ℕ) : ℝ) n n'| ≤ V * (L / ((l * r : ℕ) : ℝ)) * ∑ n ∈ S, b n ^ 2) :
    |∫ v in Ioi 1, φ v * (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      4 / Real.pi ^ 4 * (Real.sqrt (L / r) * (Real.sqrt 8 * U *
        ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
          V * (Real.pi ^ 2 / 6) ^ 2)) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hr0 : (L : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < r := by linarith
  set ρ := Real.sqrt (L / r)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  set m : ℕ × ℕ → ℝ := fun p => Real.sqrt 8 * U * (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) +
    V * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2))
  have hm : Summable m := (summable_inv_sqrt_prod.mul_left _).add (summable_inv_sq_prod.mul_left _)
  have hm0 (p : ℕ × ℕ) : 0 ≤ m p := by simp only [m]; positivity
  have h := abs_integral_weight_realPhaseCombination_dilate_le_of_bilinear hφ S b r
    (μ := fun p => ρ * E * m p) (hm.mul_left (ρ * E)) (fun p => by have := hm0 p; positivity)
    fun p hk hl => by
      have hk0 : (1 : ℝ) ≤ p.1 := by exact_mod_cast hk
      have hl0 : (1 : ℝ) ≤ p.2 := by exact_mod_cast hl
      have hq : ((p.2 * r : ℕ) : ℝ) = p.2 * r := by push_cast; ring
      have hsk : 0 < Real.sqrt p.1 := Real.sqrt_pos.mpr (by linarith)
      have hw : 0 ≤ 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) := by positivity
      by_cases hfar : 8 * (L : ℝ) * p.1 ≤ ((p.2 * r : ℕ) : ℝ)
      · have hb := hV p.1 p.2 hk hl hfar
        have hLq : (L : ℝ) / ((p.2 * r : ℕ) : ℝ) ≤ ρ := by
          rw [hq]
          have h1 : (L : ℝ) / (p.2 * r) ≤ L / r := by
            gcongr; nlinarith
          have h2 : (L : ℝ) / r ≤ Real.sqrt (L / r) := by
            have h3 : (L : ℝ) / r ≤ 1 := by rw [div_le_one hrpos]; exact hr0
            have h4 : 0 ≤ (L : ℝ) / r := by positivity
            calc (L : ℝ) / r = Real.sqrt ((L / r) ^ 2) := (Real.sqrt_sq h4).symm
              _ ≤ Real.sqrt (L / r) := Real.sqrt_le_sqrt (by nlinarith)
          exact h1.trans h2
        calc 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) * |_| ≤
              1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) * (V * ρ * E) := by
              refine mul_le_mul_of_nonneg_left (hb.trans ?_) hw
              gcongr
          _ ≤ ρ * E * m p := by
              simp only [m]
              have : 0 ≤ Real.sqrt 8 * U * (1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / (p.2 : ℝ) ^ 2)) := by
                positivity
              nlinarith [mul_nonneg (mul_nonneg hρ0 hE) this]
      · push Not at hfar
        have hb := hU p.1 p.2 hk hl
        have htrade : 1 / (p.1 : ℝ) ^ 2 ≤ 1 / ((p.1 : ℝ) * Real.sqrt p.1) * (Real.sqrt 8 * ρ) := by
          have hsq : 1 / Real.sqrt p.1 ≤ Real.sqrt 8 * ρ := by
            rw [div_le_iff₀ hsk, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
            rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
            refine Real.sqrt_le_sqrt ?_
            rw [hq] at hfar
            have : (r : ℝ) ≤ p.2 * r := by nlinarith
            rw [show (8 : ℝ) * ((L : ℝ) / r) * (p.1 : ℝ) = 8 * L * p.1 / r by ring, le_div_iff₀ hrpos]
            linarith
          have hkk : (p.1 : ℝ) ^ 2 = p.1 * Real.sqrt p.1 * Real.sqrt p.1 := by
            rw [mul_assoc, Real.mul_self_sqrt (by linarith)]; ring
          calc 1 / (p.1 : ℝ) ^ 2 = 1 / ((p.1 : ℝ) * Real.sqrt p.1) * (1 / Real.sqrt p.1) := by
                rw [hkk]; field_simp
            _ ≤ _ := by gcongr
        calc 1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) * |_| ≤
              1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2) * (U * E) := by gcongr
          _ ≤ 1 / ((p.1 : ℝ) * Real.sqrt p.1) * (Real.sqrt 8 * ρ) * (1 / (p.2 : ℝ) ^ 2) * (U * E) := by
              gcongr
          _ ≤ ρ * E * m p := by
              simp only [m]
              have : 0 ≤ V * (1 / (p.1 : ℝ) ^ 2 * (1 / (p.2 : ℝ) ^ 2)) := by positivity
              nlinarith [mul_nonneg (mul_nonneg hρ0 hE) this]
  refine h.trans (le_of_eq ?_)
  have hz2 : Summable fun l : ℕ => 1 / (l : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hn1 : Summable fun k : ℕ => ‖1 / ((k : ℝ) * Real.sqrt k)‖ :=
    summable_inv_mul_sqrt.abs.congr fun k => (Real.norm_eq_abs _).symm
  have hn2 : Summable fun l : ℕ => ‖1 / (l : ℝ) ^ 2‖ := hz2.abs.congr fun l => (Real.norm_eq_abs _).symm
  rw [tsum_mul_left, Summable.tsum_add (summable_inv_sqrt_prod.mul_left _) (summable_inv_sq_prod.mul_left _),
    tsum_mul_left, tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hn1 hn2, tsum_inv_sq_prod]
  ring

/-! ### The critical prime channel on scale windows -/

/-- Uniform harmonic constant of the collar weight. -/
def windowCollarUniform : ℝ := 4 * crossSpacedBound criticalCollarMass criticalCollarCurvature

/-- Uniform harmonic constant of the endpoint weight (jump plus remainder). -/
def windowEndpointUniform : ℝ :=
  4 * (1 + 13 / (Real.pi * (11 / 12))) + 4 * crossSpacedBound criticalEndpointMass criticalEndpointCurvature

/-- Far harmonic constant of the collar and endpoint weights together. -/
def windowFarConstant : ℝ := 16 * criticalCollarCurvature + (4 / Real.pi + 16 * criticalEndpointCurvature)

/-- The window constant `K_W` of the critical dilation correlations. -/
def criticalWindowConstant : ℝ :=
  (windowCollarUniform + windowEndpointUniform) * (Real.pi ^ 2 / 6) ^ 2 +
    (Real.sqrt 8 * (windowCollarUniform + windowEndpointUniform) *
      ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
      windowFarConstant * (Real.pi ^ 2 / 6) ^ 2)

private theorem collarMass_nonneg : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _

private theorem endpointMass_nonneg : 0 ≤ criticalEndpointMass :=
  (abs_nonneg _).trans (abs_criticalEndpointRemainder_le 0)

private theorem crossSpacedBound_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ crossSpacedBound A B := by
  unfold crossSpacedBound; positivity

theorem windowCollarUniform_nonneg : 0 ≤ windowCollarUniform := by
  unfold windowCollarUniform
  have := crossSpacedBound_nonneg collarMass_nonneg criticalCollarCurvature_nonneg
  positivity

theorem windowEndpointUniform_nonneg : 0 ≤ windowEndpointUniform := by
  unfold windowEndpointUniform
  have := crossSpacedBound_nonneg endpointMass_nonneg criticalEndpointCurvature_nonneg
  positivity

theorem windowFarConstant_nonneg : 0 ≤ windowFarConstant := by
  unfold windowFarConstant
  have := criticalCollarCurvature_nonneg
  have := criticalEndpointCurvature_nonneg
  positivity

theorem criticalWindowConstant_nonneg : 0 ≤ criticalWindowConstant := by
  unfold criticalWindowConstant
  have := windowCollarUniform_nonneg
  have := windowEndpointUniform_nonneg
  have := windowFarConstant_nonneg
  have h1 : 0 ≤ ∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k) := tsum_nonneg fun _ => by positivity
  have h2 : 0 ≤ ∑' l : ℕ, 1 / (l : ℝ) ^ 2 := tsum_nonneg fun _ => by positivity
  positivity

private theorem endpoint_split :
    weightCosineTransform criticalEndpointWeight =
      fun f => dyadicJumpKernel f + criticalEndpointRemainder f := by
  funext f; unfold criticalEndpointRemainder; ring

private theorem bilinear_endpoint_split (S : Finset ℕ) (b : ℕ → ℝ) (p q : ℝ) :
    ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform criticalEndpointWeight) p q n n' =
      ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel dyadicJumpKernel p q n n' +
      ∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel criticalEndpointRemainder p q n n' := by
  rw [endpoint_split, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [dyadicCrossKernel_add]; ring

private theorem collar_uniform (S : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) (k l : ℕ) (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform criticalCollarWeight) k
      ((l * r : ℕ) : ℝ) n n'| ≤ windowCollarUniform * ∑ n ∈ S, b n ^ 2 :=
  abs_bilinear_dyadicCrossKernel_le_uniform abs_weightCosineTransform_criticalCollarWeight_le
    (fun f hf => abs_weightCosineTransform_criticalCollarWeight_le_div_sq hf) criticalCollarCurvature_nonneg
    S (by exact_mod_cast hk) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)) b

private theorem endpoint_uniform (S : Finset ℕ) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) (k l : ℕ) (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform criticalEndpointWeight) k
      ((l * r : ℕ) : ℝ) n n'| ≤ windowEndpointUniform * ∑ n ∈ S, b n ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq1 : (1 : ℝ) ≤ ((l * r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [bilinear_endpoint_split]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_bilinear_dyadicCrossKernel_jump_le_uniform S hk1 hq1 b
  have h2 := abs_bilinear_dyadicCrossKernel_le_uniform abs_criticalEndpointRemainder_le
    (fun f hf => abs_criticalEndpointRemainder_le_div_sq hf) criticalEndpointCurvature_nonneg S hk1 hq1 b
  unfold windowEndpointUniform
  linarith

private theorem collar_far {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L)
    (b : ℕ → ℝ) {r : ℕ} (k l : ℕ) (hk : 1 ≤ k) (hfar : 8 * (L : ℝ) * k ≤ ((l * r : ℕ) : ℝ)) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform criticalCollarWeight) k
      ((l * r : ℕ) : ℝ) n n'| ≤
      16 * criticalCollarCurvature * (L / ((l * r : ℕ) : ℝ)) * ∑ n ∈ S, b n ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq1 : (1 : ℝ) ≤ ((l * r : ℕ) : ℝ) := by nlinarith
  have h := abs_bilinear_dyadicCrossKernel_le_far
    (fun f hf => abs_weightCosineTransform_criticalCollarWeight_le_div_sq hf) criticalCollarCurvature_nonneg
    hM hL hS hk1 hfar b
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hB := criticalCollarCurvature_nonneg
  rw [show 16 * (L : ℝ) * criticalCollarCurvature / ((l * r : ℕ) : ℝ) ^ 2 =
    16 * criticalCollarCurvature * (L / ((l * r : ℕ) : ℝ)) * (1 / ((l * r : ℕ) : ℝ)) by field_simp]
  have : 1 / ((l * r : ℕ) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq1
  have h0 : 0 ≤ 16 * criticalCollarCurvature * (L / ((l * r : ℕ) : ℝ)) := by positivity
  nlinarith

private theorem endpoint_far {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L) (hS : ScaleWindow S M L)
    (b : ℕ → ℝ) {r : ℕ} (k l : ℕ) (hk : 1 ≤ k) (hfar : 8 * (L : ℝ) * k ≤ ((l * r : ℕ) : ℝ)) :
    |∑ n ∈ S, ∑ n' ∈ S, b n * b n' * dyadicCrossKernel (weightCosineTransform criticalEndpointWeight) k
      ((l * r : ℕ) : ℝ) n n'| ≤
      (4 / Real.pi + 16 * criticalEndpointCurvature) * (L / ((l * r : ℕ) : ℝ)) * ∑ n ∈ S, b n ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hq1 : (1 : ℝ) ≤ ((l * r : ℕ) : ℝ) := by nlinarith
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [bilinear_endpoint_split]
  refine (abs_add_le _ _).trans ?_
  have h1 := abs_bilinear_dyadicCrossKernel_jump_le_far hM hL hS hk1 hfar b
  have h2 := abs_bilinear_dyadicCrossKernel_le_far (fun f hf => abs_criticalEndpointRemainder_le_div_sq hf)
    criticalEndpointCurvature_nonneg hM hL hS hk1 hfar b
  have hB := criticalEndpointCurvature_nonneg
  have e1 : 4 * (L : ℝ) / (Real.pi * ((l * r : ℕ) : ℝ)) * E = 4 / Real.pi * (L / ((l * r : ℕ) : ℝ)) * E := by
    field_simp
  have e2 : 16 * (L : ℝ) * criticalEndpointCurvature / ((l * r : ℕ) : ℝ) ^ 2 * E =
      16 * criticalEndpointCurvature * (L / ((l * r : ℕ) : ℝ)) * E * (1 / ((l * r : ℕ) : ℝ)) := by
    field_simp
  have hinv : 1 / ((l * r : ℕ) : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hq1
  have h0 : 0 ≤ 16 * criticalEndpointCurvature * (L / ((l * r : ℕ) : ℝ)) * E := by positivity
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

/-- **Critical dilation correlations on a scale window.** For every family on a window `[M, LM]`
and every `r ≥ 1`, the collared and endpoint correlations together satisfy
`|∫ψ B_b B_b(r·) + ∫φ_e B_b B_b(r·)| ≤ (4/π⁴) K_W min(1, √(L/r)) ∑ b_n²`. -/
theorem abs_criticalWindowCorrelation_le {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hS : ScaleWindow S M L) (b : ℕ → ℝ) {r : ℕ} (hr : 1 ≤ r) :
    |(∫ v in Ioi 1, criticalCollarWeight v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v))) +
      ∫ v in Ioi 1, criticalEndpointWeight v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v))| ≤
      4 / Real.pi ^ 4 * (criticalWindowConstant * min 1 (Real.sqrt (L / r))) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU1 := windowCollarUniform_nonneg
  have hU2 := windowEndpointUniform_nonneg
  have hV := windowFarConstant_nonneg
  have hZ1 : 0 ≤ (∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2 :=
    mul_nonneg (tsum_nonneg fun _ => by positivity) (tsum_nonneg fun _ => by positivity)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  refine (abs_add_le _ _).trans ?_
  rcases le_or_gt L r with hLr | hLr
  · have hc := abs_integral_weight_dilate_le_of_window integrableOn_criticalCollarWeight S b hL hLr
      hU1 (by have := criticalCollarCurvature_nonneg; positivity : (0 : ℝ) ≤ 16 * criticalCollarCurvature)
      (fun k l hk hl => collar_uniform S b hr k l hk hl)
      (fun k l hk _ hfar => collar_far hM hL hS b k l hk hfar)
    have he := abs_integral_weight_dilate_le_of_window integrableOn_criticalEndpointWeight S b hL hLr
      hU2 (by have := criticalEndpointCurvature_nonneg; positivity :
        (0 : ℝ) ≤ 4 / Real.pi + 16 * criticalEndpointCurvature)
      (fun k l hk hl => endpoint_uniform S b hr k l hk hl)
      (fun k l hk _ hfar => endpoint_far hM hL hS b k l hk hfar)
    have hmin : min 1 (Real.sqrt (L / r)) = Real.sqrt (L / r) := by
      refine min_eq_right ?_
      rw [Real.sqrt_le_one]
      rw [div_le_one hrpos]; exact_mod_cast hLr
    rw [hmin]
    refine (add_le_add hc he).trans ?_
    unfold criticalWindowConstant windowFarConstant
    have hρ : 0 ≤ Real.sqrt (L / r) := Real.sqrt_nonneg _
    have hpi : 0 < 4 / Real.pi ^ 4 := by positivity
    have hU : 0 ≤ (windowCollarUniform + windowEndpointUniform) * (Real.pi ^ 2 / 6) ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hpi.le hρ) hU) hE]
  · have hc := abs_integral_weight_dilate_le_of_uniform integrableOn_criticalCollarWeight S b r hU1
      (fun k l hk hl => collar_uniform S b hr k l hk hl)
    have he := abs_integral_weight_dilate_le_of_uniform integrableOn_criticalEndpointWeight S b r hU2
      (fun k l hk hl => endpoint_uniform S b hr k l hk hl)
    have hmin : min 1 (Real.sqrt (L / r)) = 1 := by
      refine min_eq_left ?_
      rw [Real.one_le_sqrt, one_le_div hrpos]; exact_mod_cast hLr.le
    rw [hmin, mul_one]
    refine (add_le_add hc he).trans ?_
    unfold criticalWindowConstant
    have hpi : 0 < 4 / Real.pi ^ 4 := by positivity
    have hrest : 0 ≤ Real.sqrt 8 * (windowCollarUniform + windowEndpointUniform) *
        ((∑' k : ℕ, 1 / ((k : ℝ) * Real.sqrt k)) * ∑' l : ℕ, 1 / (l : ℝ) ^ 2) +
        windowFarConstant * (Real.pi ^ 2 / 6) ^ 2 := by positivity
    nlinarith [mul_nonneg (mul_nonneg hpi.le hrest) hE]

/-- Slope `(4/π⁴) K_W · 6e` of the logarithmic window law of the critical prime channel. -/
def criticalWindowPrimeSlope : ℝ := 4 / Real.pi ^ 4 * criticalWindowConstant * (6 * Real.exp 1)

private theorem min_sqrt_le_rpow {L r ε : ℝ} (hL : 0 < L) (hr : 0 < r) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    min 1 (Real.sqrt (L / r)) ≤ (L / r) ^ ε := by
  rcases le_or_gt r L with h | h
  · exact (min_le_left _ _).trans (Real.one_le_rpow (by rw [le_div_iff₀ hr]; linarith) hε0)
  · refine (min_le_right _ _).trans ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hr]; linarith) hε

/-- **Logarithmic window law of the critical prime channel.** For every family on a scale window
`[M, LM]` and every real coefficient vector,
`|∑_r Λ(r) r^{-1/2} ac(log r)| ≤ C_W (3 + log L) ∑ b_n²`. Dilations `r ≤ L` cost a uniform amount
each, dilations `r > L` decay like `√(L/r)`, and `∑ Λ(r) r^{-1-ε} ≤ 6(1+ε)/ε` at
`ε = 1/(2 + log L)` turns both into one logarithm. -/
theorem abs_criticalPrimeEnergy_le_of_window {S : Finset ℕ} {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hS : ScaleWindow S M L) (b : ℕ → ℝ) :
    |criticalPrimeEnergy S b| ≤ criticalWindowPrimeSlope * (3 + Real.log L) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by exact_mod_cast hL)
  set ε := 1 / (2 + Real.log L)
  have hε0 : 0 < ε := by positivity
  have hε : ε ≤ 1 / 2 := by
    unfold ε; exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  set C := 4 / Real.pi ^ 4 * criticalWindowConstant * E
  have hC : 0 ≤ C := by have := criticalWindowConstant_nonneg; positivity
  have hs : (1 : ℝ) < 1 + ε := by linarith
  have hsum := RHTower.summable_vonMangoldt_div_rpow_mertensVonMangoldtEulerConstant hs
  have hbd (r : ℕ) : |criticalPrimeAtom S b r| ≤
      C * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)) := by
    unfold criticalPrimeAtom
    split_ifs with hr
    · have hr0 : (0 : ℝ) < r := by positivity
      have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
      have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := r))
      have hw := abs_criticalWindowCorrelation_le hM hL hS b (r := r) (by omega)
      have hmin := min_sqrt_le_rpow hL0 hr0 hε0.le hε
      rw [integral_criticalFactorialSource_mul_dilate_eq S b (by omega), abs_mul, abs_mul,
        abs_of_nonneg (div_nonneg hΛ hsr.le), abs_of_pos (by positivity : 0 < 1 / Real.sqrt r)]
      have hrr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0.le
      have hpow : (r : ℝ) ^ (1 + ε) = r * r ^ ε := by
        rw [Real.rpow_add hr0, Real.rpow_one]
      rw [hpow, Real.div_rpow hL0.le hr0.le] at *
      have hrε : 0 < (r : ℝ) ^ ε := Real.rpow_pos_of_pos hr0 _
      calc (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r * |_ + _|) ≤
            (ArithmeticFunction.vonMangoldt r : ℝ) / Real.sqrt r * (1 / Real.sqrt r *
              (4 / Real.pi ^ 4 * (criticalWindowConstant * ((L : ℝ) ^ ε / (r : ℝ) ^ ε)) * E)) := by
            gcongr
            refine hw.trans ?_
            have := criticalWindowConstant_nonneg
            gcongr
        _ = C * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r * r ^ ε)) := by
            have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
            unfold C; field_simp; rw [hsq]; ring
    · have : 0 ≤ C * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)) := by
        have := (ArithmeticFunction.vonMangoldt_nonneg (n := r))
        positivity
      simpa using this
  have hmaj : Summable fun r : ℕ => C * (L : ℝ) ^ ε * ((ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε)) :=
    hsum.mul_left _
  have habs : Summable fun r => ‖criticalPrimeAtom S b r‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => by rw [Real.norm_eq_abs]; exact hbd r) hmaj
  unfold criticalPrimeEnergy
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm habs).trans ((habs.tsum_le_tsum (fun r => by
    rw [Real.norm_eq_abs]; exact hbd r) hmaj).trans ?_)
  rw [tsum_mul_left]
  have hsix := RHTower.tsum_vonMangoldt_div_rpow_le_six hs
  have hLε : (L : ℝ) ^ ε ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hL0]
    refine Real.exp_le_exp.mpr ?_
    unfold ε
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  have hfrac : 6 * (1 + ε) / (1 + ε - 1) = 6 * (3 + Real.log L) := by
    unfold ε; field_simp; ring
  rw [hfrac] at hsix
  have hLε0 : 0 ≤ (L : ℝ) ^ ε := (Real.rpow_pos_of_pos hL0 _).le
  calc C * (L : ℝ) ^ ε * ∑' r : ℕ, (ArithmeticFunction.vonMangoldt r : ℝ) / (r : ℝ) ^ (1 + ε) ≤
        C * Real.exp 1 * (6 * (3 + Real.log L)) := by gcongr
    _ = criticalWindowPrimeSlope * (3 + Real.log L) * E := by
        unfold C criticalWindowPrimeSlope; ring

end GaloisForLFunctions.ArithmeticPositivityTheory
