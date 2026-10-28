import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsBlindToResidueClasses
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant

/-!
# Class harmonic sums have constants

The harmonic sum of a residue class satisfies `S_a(M) = log M/q + O(q)`
(`abs_classHarmonic_sub_log_le`). The finite part on residue profiles needs its constant, with a
rate.

* **Euler's constant with a rate** (`harmonicSum_sub_log_sub_bounds`):
  `0 ≤ H_M − log M − γ ≤ 1/M`.
* **Cauchy with a rate** (`exists_abs_sub_le_of_cauchy_rate`): if `|f(M') − f(M)| ≤ K/M` for
  `M ≤ M'`, then `f` has a limit `d` with `|f(M) − d| ≤ K/M`.
* **Shifted classes** (`abs_classShift_sub_le`): `S_{a+1}(M) − S_a(M)` changes by at most `2/M`
  beyond `M`. The shift `m ↦ m + 1` matches the two classes up to the tail of the convergent series
  `Σ_{m ≡ a} (1/m − 1/(m + 1))` and one boundary term. So every difference `S_b − S_a` has Cauchy
  rate `2q/M` (`abs_classDiff_sub_le`).
* **The class constant** (`exists_classHarmonic_constant`): there is `d_a` with
  `|q S_a(M) − log M − d_a| ≤ (1 + 2q²)/M`, since `q S_a − log M = (H_M − log M) + Σ_b (S_a − S_b)`.
* **The logarithmic class sum** (`abs_classLogSum_sub_le_const`): with the same `d_a`,
  `|q L_a(M) − (log M)²/2 − d_a log M| ≤ 2(K + 1/2)` for the rate `K = 1 + 2q²`, by the telescoping
  `L_a(M + 1) = L_a(M) + log(1 + 1/M) S_a(M)` and `Σ 1/M² < 2`.

These are the second-order asymptotics of the residue-class harmonic sums: the constants `d_a`
are the class analogues of Euler's constant.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {q : ℕ}

theorem harmonicSum_eq_harmonic (M : ℕ) : harmonicSum M = (harmonic M : ℝ) := by
  simp [harmonicSum, harmonic_eq_sum_Icc, one_div]

/-- **Euler's constant with a rate**: `0 ≤ H_M − log M − γ ≤ 1/M` for `M ≥ 1`. -/
theorem harmonicSum_sub_log_sub_bounds {M : ℕ} (hM : 1 ≤ M) :
    0 ≤ harmonicSum M - Real.log M - γ ∧ harmonicSum M - Real.log M - γ ≤ 1 / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' M
  have h2 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant M
  rw [Real.eulerMascheroniSeq', if_neg (by omega)] at h1
  rw [Real.eulerMascheroniSeq] at h2
  rw [harmonicSum_eq_harmonic]
  -- `log(M + 1) − log M ≤ 1/M`
  have h3 : Real.log ((M : ℝ) + 1) - Real.log M ≤ 1 / M := by
    rw [← Real.log_div (by positivity) hM'.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((M : ℝ) + 1) / M by positivity)
    have hq : ((M : ℝ) + 1) / M - 1 = 1 / M := by field_simp; ring
    linarith
  constructor <;> linarith

/-- **Cauchy with a rate**: if `|f(M') − f(M)| ≤ K/M` for `1 ≤ M ≤ M'`, then `f` has a limit `d`
with `|f(M) − d| ≤ K/M`. -/
theorem exists_abs_sub_le_of_cauchy_rate {f : ℕ → ℝ} {K : ℝ}
    (h : ∀ M M' : ℕ, 1 ≤ M → M ≤ M' → |f M' - f M| ≤ K / M) :
    ∃ d : ℝ, ∀ M : ℕ, 1 ≤ M → |f M - d| ≤ K / M := by
  have hK : 0 ≤ K := by
    have := (abs_nonneg _).trans (h 1 1 le_rfl le_rfl)
    simpa using this
  have hcauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (K / ε)
    refine ⟨N + 1, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hN1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    refine (h (N + 1) n (by omega) hn).trans_lt ?_
    rw [div_lt_iff₀ hN1]
    rw [div_lt_iff₀ hε] at hN
    push_cast
    nlinarith
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨d, fun M hM => ?_⟩
  have hlim : Tendsto (fun M' => |f M' - f M|) atTop (𝓝 |d - f M|) :=
    ((continuous_abs.comp (continuous_sub_right (f M))).tendsto d).comp hd
  have := le_of_tendsto hlim (eventually_ge_atTop M |>.mono fun M' hM' => h M M' hM hM')
  rwa [abs_sub_comm] at this

/-! ### Shifted classes -/

/-- **The shift `m ↦ m + 1`**: `S_{a+1}(M + 1) = [1 ≡ a + 1] + Σ_{m ≤ M, m ≡ a} 1/(m + 1)`. -/
theorem classHarmonic_add_one_succ (a : ZMod q) (M : ℕ) :
    classHarmonic q (a + 1) (M + 1) =
      (if ((1 : ℕ) : ZMod q) = a + 1 then 1 / ((1 : ℕ) : ℝ) else 0) +
        ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then 1 / ((m : ℝ) + 1) else 0) := by
  rw [classHarmonic, sum_Icc_succ_shift]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  by_cases hm : (m : ZMod q) = a
  · rw [if_pos (by push_cast; rw [hm]), if_pos hm, Nat.cast_add, Nat.cast_one]
  · rw [if_neg (by push_cast; exact fun h => hm (add_right_cancel h)), if_neg hm]

/-- The increments `τ_a(M) = Σ_{m ≤ M, m ≡ a} (1/m − 1/(m + 1))`. -/
def classTail (q : ℕ) (a : ZMod q) (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then 1 / (m : ℝ) - 1 / ((m : ℝ) + 1) else 0)

theorem classTail_mono (a : ZMod q) : Monotone (classTail q a) :=
  monotone_nat_of_le_succ fun M => by
    rw [classTail, classTail, sum_Icc_succ_top (by omega)]
    have : 0 ≤ (if ((M + 1 : ℕ) : ZMod q) = a then 1 / ((M + 1 : ℕ) : ℝ) -
        1 / (((M + 1 : ℕ) : ℝ) + 1) else 0) := by
      split_ifs
      · rw [sub_nonneg]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      · exact le_rfl
    linarith

/-- The tail beyond `M` is at most `1/(M + 1)`: `τ_a(M) + 1/(M + 1)` decreases. -/
theorem classTail_add_antitone (a : ZMod q) :
    Antitone fun M : ℕ => classTail q a M + 1 / ((M : ℝ) + 1) :=
  antitone_nat_of_succ_le fun M => by
    rw [classTail, classTail, sum_Icc_succ_top (by omega)]
    push_cast
    have hd : 0 ≤ 1 / ((M : ℝ) + 1) - 1 / ((M : ℝ) + 1 + 1) := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    split_ifs <;> linarith

/-- `S_a(M) = S'_a(M) + τ_a(M)`, `S'_a(M) = Σ_{m ≤ M, m ≡ a} 1/(m + 1)`. -/
theorem classHarmonic_eq_shift_add_tail (a : ZMod q) (M : ℕ) :
    classHarmonic q a M =
      ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then 1 / ((m : ℝ) + 1) else 0) + classTail q a M := by
  rw [classHarmonic, classTail, ← sum_add_distrib]
  exact sum_congr rfl fun m _ => by split_ifs <;> ring

/-- **Shifted classes are Cauchy**: `|g(M') − g(M)| ≤ 2/M` for `g = S_{a+1} − S_a`, `1 ≤ M ≤ M'`. -/
theorem abs_classShift_sub_le (a : ZMod q) {M M' : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') :
    |(classHarmonic q (a + 1) M' - classHarmonic q a M') -
        (classHarmonic q (a + 1) M - classHarmonic q a M)| ≤ 2 / M := by
  -- `g(M) = [1 ≡ a + 1] − τ_a(M) − δ(M)`, `δ(M) = [M + 1 ≡ a + 1]/(M + 1)`
  have hg : ∀ X : ℕ, classHarmonic q (a + 1) X - classHarmonic q a X =
      (if ((1 : ℕ) : ZMod q) = a + 1 then 1 / ((1 : ℕ) : ℝ) else 0) - classTail q a X -
        (if ((X + 1 : ℕ) : ZMod q) = a + 1 then 1 / ((X + 1 : ℕ) : ℝ) else 0) := by
    intro X
    have h1 := classHarmonic_add_one_succ a X
    have h2 := classHarmonic_succ (a + 1) X
    have h3 := classHarmonic_eq_shift_add_tail a X
    linarith
  have hδ : ∀ X : ℕ, M ≤ X →
      0 ≤ (if ((X + 1 : ℕ) : ZMod q) = a + 1 then 1 / ((X + 1 : ℕ) : ℝ) else 0) ∧
        (if ((X + 1 : ℕ) : ZMod q) = a + 1 then 1 / ((X + 1 : ℕ) : ℝ) else 0) ≤ 1 / M := by
    intro X hX
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    split_ifs
    · refine ⟨by positivity, one_div_le_one_div_of_le hM' ?_⟩
      push_cast
      have : (M : ℝ) ≤ X := by exact_mod_cast hX
      linarith
    · exact ⟨le_rfl, by positivity⟩
  have hτ1 := classTail_mono a hMM'
  have hτ2 := classTail_add_antitone a hMM'
  simp only at hτ2
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hfrac : 1 / ((M : ℝ) + 1) ≤ 1 / M := one_div_le_one_div_of_le hM' (by linarith)
  have hfrac' : 0 ≤ 1 / ((M' : ℝ) + 1) := by positivity
  obtain ⟨hδ1, hδ2⟩ := hδ M le_rfl
  obtain ⟨hδ1', hδ2'⟩ := hδ M' hMM'
  rw [hg M', hg M, abs_le]
  have h2 : 2 / (M : ℝ) = 1 / M + 1 / M := by ring
  constructor <;> linarith

/-- **Class differences are Cauchy**: `|D(M') − D(M)| ≤ 2q/M` for `D = S_b − S_a`. -/
theorem abs_classDiff_sub_le [NeZero q] (a b : ZMod q) {M M' : ℕ} (hM : 1 ≤ M) (hMM' : M ≤ M') :
    |(classHarmonic q b M' - classHarmonic q a M') -
        (classHarmonic q b M - classHarmonic q a M)| ≤ 2 * q / M := by
  have hstep : ∀ j : ℕ, |(classHarmonic q (a + j) M' - classHarmonic q a M') -
      (classHarmonic q (a + j) M - classHarmonic q a M)| ≤ 2 * j / M := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := abs_classShift_sub_le (q := q) (a + (j : ZMod q)) hM hMM'
      push_cast
      rw [← add_assoc]
      calc |(classHarmonic q (a + j + 1) M' - classHarmonic q a M') -
            (classHarmonic q (a + j + 1) M - classHarmonic q a M)|
          = |((classHarmonic q (a + j + 1) M' - classHarmonic q (a + j) M') -
              (classHarmonic q (a + j + 1) M - classHarmonic q (a + j) M)) +
            ((classHarmonic q (a + j) M' - classHarmonic q a M') -
              (classHarmonic q (a + j) M - classHarmonic q a M))| := by ring_nf
        _ ≤ 2 / M + 2 * j / M := (abs_add_le _ _).trans (add_le_add h ih)
        _ = 2 * ((j : ℝ) + 1) / M := by ring
  have h := hstep (b - a).val
  rw [ZMod.natCast_zmod_val, add_sub_cancel] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  have : ((b - a).val : ℝ) ≤ q := by exact_mod_cast (ZMod.val_lt (b - a)).le
  linarith

/-- **The class constant**: there is `d_a` with `|q S_a(M) − log M − d_a| ≤ (1 + 2q²)/M`. -/
theorem exists_classHarmonic_constant [NeZero q] (a : ZMod q) :
    ∃ d : ℝ, ∀ M : ℕ, 1 ≤ M →
      |q * classHarmonic q a M - Real.log M - d| ≤ (1 + 2 * q ^ 2) / M := by
  apply exists_abs_sub_le_of_cauchy_rate
  intro M M' hM hMM'
  -- `q S_a − log M = (H_M − log M) + Σ_b (S_a − S_b)`
  have hrep : ∀ X : ℕ, (q : ℝ) * classHarmonic q a X - Real.log X =
      (harmonicSum X - Real.log X) + ∑ b : ZMod q, (classHarmonic q a X - classHarmonic q b X) := by
    intro X
    rw [sum_sub_distrib, sum_classHarmonic, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    ring
  rw [hrep M', hrep M]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hE := harmonicSum_sub_log_sub_bounds hM
  have hE' := harmonicSum_sub_log_sub_bounds (hM.trans hMM')
  have hfrac : 1 / (M' : ℝ) ≤ 1 / M :=
    one_div_le_one_div_of_le hM' (by exact_mod_cast hMM')
  have hH : |(harmonicSum M' - Real.log M') - (harmonicSum M - Real.log M)| ≤ 1 / M := by
    rw [abs_le]; constructor <;> linarith [hE.1, hE.2, hE'.1, hE'.2]
  have hD : |∑ b : ZMod q, (classHarmonic q a M' - classHarmonic q b M') -
      ∑ b : ZMod q, (classHarmonic q a M - classHarmonic q b M)| ≤ q * (2 * q / M) := by
    rw [← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b : ZMod q, |(classHarmonic q a M' - classHarmonic q b M') -
          (classHarmonic q a M - classHarmonic q b M)|
        ≤ ∑ _b : ZMod q, 2 * (q : ℝ) / M := sum_le_sum fun b _ => abs_classDiff_sub_le b a hM hMM'
      _ = q * (2 * q / M) := by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  calc |(harmonicSum M' - Real.log M' + ∑ b : ZMod q, (classHarmonic q a M' - classHarmonic q b M'))
        - (harmonicSum M - Real.log M + ∑ b : ZMod q, (classHarmonic q a M - classHarmonic q b M))|
      = |((harmonicSum M' - Real.log M') - (harmonicSum M - Real.log M)) +
          (∑ b : ZMod q, (classHarmonic q a M' - classHarmonic q b M') -
            ∑ b : ZMod q, (classHarmonic q a M - classHarmonic q b M))| := by ring_nf
    _ ≤ 1 / M + q * (2 * q / M) := (abs_add_le _ _).trans (add_le_add hH hD)
    _ = (1 + 2 * q ^ 2) / M := by ring

/-- **The logarithmic class sum to second order**: if `|q S_a(M) − log M − d| ≤ K/M` for `M ≥ 1`,
then `|q L_a(M) − (log M)²/2 − d log M| ≤ 2(K + 1/2)`. -/
theorem abs_classLogSum_sub_le_const (a : ZMod q) {d K : ℝ} (hK : 0 ≤ K)
    (hd : ∀ M : ℕ, 1 ≤ M → |q * classHarmonic q a M - Real.log M - d| ≤ K / M) {M : ℕ}
    (hM : 1 ≤ M) :
    |q * classLogSum q a M - Real.log M ^ 2 / 2 - d * Real.log M| ≤
      2 * (K + 1 / 2) * (1 - 1 / M) := by
  induction M, hM using Nat.le_induction with
  | base => simp [classLogSum]
  | succ M hM ih =>
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < M := by linarith
    set δ := Real.log (M + 1 : ℕ) - Real.log M with hδ
    have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Real.log_le_log hM0 (by push_cast; linarith))
    have hδ1 : δ ≤ 1 / M := by
      rw [hδ, ← Real.log_div (by positivity) hM0.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((M + 1 : ℕ) : ℝ) / M by positivity)
      have hq : ((M + 1 : ℕ) : ℝ) / M - 1 = 1 / M := by push_cast; field_simp; ring
      linarith
    have hlog : Real.log (M + 1 : ℕ) = Real.log M + δ := by rw [hδ]; ring
    rw [classLogSum_succ, ← hδ, hlog]
    have hS := hd M hM
    -- one step moves the error by `δ (q S_a(M) − log M − d) − δ²/2`
    have hkey : (q : ℝ) * (classLogSum q a M + δ * classHarmonic q a M) -
        (Real.log M + δ) ^ 2 / 2 - d * (Real.log M + δ) =
        ((q : ℝ) * classLogSum q a M - Real.log M ^ 2 / 2 - d * Real.log M) +
          δ * ((q : ℝ) * classHarmonic q a M - Real.log M - d) - δ ^ 2 / 2 := by ring
    rw [hkey]
    have h1 : |δ * ((q : ℝ) * classHarmonic q a M - Real.log M - d)| ≤ (1 / M) * (K / M) := by
      rw [abs_mul, abs_of_nonneg hδ0]
      exact mul_le_mul hδ1 hS (abs_nonneg _) (by positivity)
    have h2 : δ ^ 2 / 2 ≤ (1 / M) ^ 2 / 2 := by
      have := pow_le_pow_left₀ hδ0 hδ1 2
      linarith
    have h3 : 0 ≤ δ ^ 2 / 2 := by positivity
    -- `1/M² ≤ 2 (1/M − 1/(M + 1))`
    have h4 : (1 / (M : ℝ)) ^ 2 ≤ 2 * (1 / M - 1 / ((M + 1 : ℕ) : ℝ)) := by
      push_cast
      rw [div_pow, one_pow, ← sub_nonneg]
      have : 2 * (1 / (M : ℝ) - 1 / (M + 1)) - 1 / M ^ 2 = (M - 1) / (M ^ 2 * (M + 1)) := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (by linarith) (by positivity)
    have h5 : (1 / (M : ℝ)) * (K / M) = K * (1 / M) ^ 2 := by ring
    rw [abs_le] at ih h1 ⊢
    have hKM := mul_le_mul_of_nonneg_left h4 hK
    constructor <;> nlinarith [ih.1, ih.2, h1.1, h1.2]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
