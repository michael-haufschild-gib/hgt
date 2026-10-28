import GaloisForLFunctions.RHTower.DirichletCharacterPartialSumBound
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.ArithmeticElectrostatics.TheTorsionCountertermIsLogarithmic
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Mertens' theorem for characters

For a non-trivial Dirichlet character `χ` mod `q` the twisted Mertens sum
`A_χ(y) = Σ_{t ≤ y} χ(t) Λ(t)/t` is bounded (`exists_norm_charMertensSum_le`). The proof is the
elementary one, with `L(1, χ) ≠ 0` from Mathlib:

* **Abel summation with decreasing weights** (`norm_sum_antitone_mul_le`,
  `norm_sum_range_shift_le`): weights `f ≥ 0` decreasing against partial sums bounded by `C` give
  at most `f(0) C`; the partial sums of a shifted character are at most `2q`.
* **The partial sums of `L(1, χ)`** (`norm_LFunction_sub_partial_le`,
  `norm_LFunction_one_sub_partial_le`, `norm_LFunction_one_sub_charHarmonicSum_le`):
  `‖L(σ, χ) − Σ_{n < M} χ(n) n^{−σ}‖ ≤ 2q/M` for `σ > 1`, and at `σ = 1` by continuity of `L(·, χ)`.
* **The logarithmic sum is bounded** (`norm_charLogSum_le`): `‖Σ_{n ≤ M} χ(n) log n/n‖ ≤ 1 + 2q`,
  because `log x/x` decreases from `x = 3`.
* **The hyperbola identity** (`sum_divisors_eq_sum_Icc_div`, `charLogSum_eq`): with
  `log n = Σ_{t ∣ n} Λ(t)`, `Σ_{n ≤ M} χ(n) log n/n = Σ_{t ≤ M} χ(t)Λ(t)/t · S_χ(M/t)`.
* **Mertens' theorem for characters** (`exists_norm_charMertensSum_le`): replacing `S_χ(M/t)` by
  `L(1, χ)` costs `Σ_{t ≤ M} Λ(t) · 2q/M = O(q)` (Chebyshev), so `L(1, χ) A_χ(M) = O(q)`.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ} [NeZero q]

/-! ### Abel summation with decreasing weights -/

/-- **Abel bound with decreasing weights**: `‖Σ_{i<K} f(i) g(i)‖ ≤ f(0) C` for `f ≥ 0` antitone and
partial sums of `g` bounded by `C`. -/
theorem norm_sum_antitone_mul_le {f : ℕ → ℝ} {g : ℕ → ℂ} {C : ℝ}
    (hG : ∀ k, ‖∑ j ∈ range k, g j‖ ≤ C) (hf : ∀ n, 0 ≤ f n) (hanti : Antitone f) (K : ℕ) :
    ‖∑ i ∈ range K, ((f i : ℝ) : ℂ) * g i‖ ≤ f 0 * C := by
  have h := RHTower.norm_sum_ofReal_mul_le_of_bounded_partial hG hf K
  have htv : ∑ i ∈ range (K - 1), |f (i + 1) - f i| = f 0 - f (K - 1) := by
    rw [← sum_range_sub' f (K - 1)]
    exact sum_congr rfl fun i _ => by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hanti (Nat.le_succ i)))]
  rw [htv] at h
  linarith

/-- The partial sums of a shifted non-trivial character are at most `2q`. -/
theorem norm_sum_range_shift_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M k : ℕ) :
    ‖∑ j ∈ range k, χ ((M + j : ℕ) : ZMod q)‖ ≤ 2 * q := by
  have h : ∑ n ∈ range (M + k), χ (n : ZMod q) =
      ∑ n ∈ range M, χ (n : ZMod q) + ∑ j ∈ range k, χ ((M + j : ℕ) : ZMod q) :=
    sum_range_add _ M k
  have hsub : ∑ j ∈ range k, χ ((M + j : ℕ) : ZMod q) =
      ∑ n ∈ range (M + k), χ (n : ZMod q) - ∑ n ∈ range M, χ (n : ZMod q) := by
    rw [h]; ring
  rw [hsub]
  calc _ ≤ ‖∑ n ∈ range (M + k), χ (n : ZMod q)‖ + ‖∑ n ∈ range M, χ (n : ZMod q)‖ :=
        norm_sub_le _ _
    _ ≤ q + q := add_le_add (RHTower.norm_dirichletCharacter_sum_range_le χ hχ _)
        (RHTower.norm_dirichletCharacter_sum_range_le χ hχ _)
    _ = 2 * q := by ring

/-- **Tail of the Dirichlet series**: `‖Σ_{M ≤ n < M + K} χ(n) n^{−σ}‖ ≤ 2q/M` for `σ ≥ 1`. -/
theorem norm_sum_tail_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 1 ≤ σ) {M : ℕ}
    (hM : 1 ≤ M) (K : ℕ) :
    ‖∑ j ∈ range K, ((RHTower.realPowerKernel σ (M + j) : ℝ) : ℂ) * χ ((M + j : ℕ) : ZMod q)‖ ≤
      2 * q / M := by
  have hanti : Antitone fun j => RHTower.realPowerKernel σ (M + j) :=
    antitone_nat_of_succ_le fun j => by
      rw [show M + (j + 1) = M + j + 1 by ring]
      exact RHTower.realPowerKernel_succ_le (by linarith) (by omega)
  have h := norm_sum_antitone_mul_le (norm_sum_range_shift_le χ hχ M)
    (fun j => RHTower.realPowerKernel_nonneg σ _) hanti K
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h0 : RHTower.realPowerKernel σ (M + 0) ≤ 1 / M := by
    rw [add_zero, RHTower.realPowerKernel, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hM' (by linarith)
  calc _ ≤ RHTower.realPowerKernel σ (M + 0) * (2 * q) := h
    _ ≤ 1 / M * (2 * q) := mul_le_mul_of_nonneg_right h0 (by positivity)
    _ = 2 * q / M := by ring

/-! ### The partial sums of `L(1, χ)` -/

/-- For `σ > 1`: `‖L(σ, χ) − Σ_{n < M} χ(n) n^{−σ}‖ ≤ 2q/M`. -/
theorem norm_LFunction_sub_partial_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 < σ) {M : ℕ} (hM : 1 ≤ M) :
    ‖DirichletCharacter.LFunction χ (σ : ℂ) -
        ∑ n ∈ range M, ((RHTower.realPowerKernel σ n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤ 2 * q / M := by
  have hσ' : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hσ']
  have hsum : LSeriesSummable (fun m : ℕ => χ (m : ZMod q)) (σ : ℂ) :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne q) χ).mpr hσ'
  have hfin : ∀ K, ∑ n ∈ range K, LSeries.term (fun m : ℕ => χ (m : ZMod q)) (σ : ℂ) n =
      ∑ n ∈ range K, ((RHTower.realPowerKernel σ n : ℝ) : ℂ) * χ (n : ZMod q) := fun K =>
    sum_congr rfl fun n _ => RHTower.LSeries_term_dirichletCharacter_eq χ (by linarith) n
  rw [← hfin M]
  have hshift := (tendsto_add_atTop_iff_nat M).mpr hsum.hasSum.tendsto_sum_nat
  refine le_of_tendsto' ((hshift.sub_const _).norm) fun K => ?_
  rw [hfin, hfin, add_comm K M, sum_range_add, add_sub_cancel_left]
  exact norm_sum_tail_le χ hχ hσ.le hM K

/-- **The partial sums of `L(1, χ)`**: `‖L(1, χ) − Σ_{n < M} χ(n)/n‖ ≤ 2q/M`. -/
theorem norm_LFunction_one_sub_partial_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {M : ℕ}
    (hM : 1 ≤ M) :
    ‖DirichletCharacter.LFunction χ 1 -
        ∑ n ∈ range M, ((RHTower.realPowerKernel 1 n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤ 2 * q / M := by
  -- `L(σ, χ) → L(1, χ)` and the partial sum is continuous in `σ`
  have hL : Tendsto (fun σ : ℝ => DirichletCharacter.LFunction χ (σ : ℂ)) (𝓝[>] 1)
      (𝓝 (DirichletCharacter.LFunction χ 1)) := by
    have hc : Continuous fun σ : ℝ => DirichletCharacter.LFunction χ (σ : ℂ) :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
    have h1 := hc.tendsto 1
    rw [Complex.ofReal_one] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hS : Tendsto (fun σ : ℝ =>
      ∑ n ∈ range M, ((RHTower.realPowerKernel σ n : ℝ) : ℂ) * χ (n : ZMod q)) (𝓝[>] 1)
      (𝓝 (∑ n ∈ range M, ((RHTower.realPowerKernel 1 n : ℝ) : ℂ) * χ (n : ZMod q))) := by
    refine tendsto_finsetSum _ fun n _ => ?_
    have hc : ContinuousAt (fun σ : ℝ => RHTower.realPowerKernel σ n) 1 := by
      unfold RHTower.realPowerKernel
      exact (Real.continuousAt_const_rpow' (by norm_num : (-(1 : ℝ)) ≠ 0)).comp
        continuous_neg.continuousAt
    exact (((Complex.continuous_ofReal.tendsto _).comp hc.tendsto).mul_const _).mono_left
      nhdsWithin_le_nhds
  refine le_of_tendsto ((hL.sub hS).norm) ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact norm_LFunction_sub_partial_le χ hχ hσ hM

/-- The partial sum `S_χ(y) = Σ_{n ≤ y} χ(n)/n`. -/
def charHarmonicSum (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 y, χ (n : ZMod q) * ((1 / n : ℝ) : ℂ)

/-- A sum over `range (y + 1)` vanishing at `0` is a sum over `[1, y]`. -/
theorem sum_range_succ_eq_sum_Icc {f : ℕ → ℂ} (h0 : f 0 = 0) (y : ℕ) :
    ∑ n ∈ range (y + 1), f n = ∑ n ∈ Icc 1 y, f n := by
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos y), h0, zero_add]
  rfl

omit [NeZero q] in
theorem charHarmonicSum_eq (χ : DirichletCharacter ℂ q) (y : ℕ) :
    charHarmonicSum χ y =
      ∑ n ∈ range (y + 1), ((RHTower.realPowerKernel 1 n : ℝ) : ℂ) * χ (n : ZMod q) := by
  rw [sum_range_succ_eq_sum_Icc (by simp [RHTower.realPowerKernel_zero one_ne_zero]) y,
    charHarmonicSum]
  refine sum_congr rfl fun n _ => ?_
  rw [RHTower.realPowerKernel, Real.rpow_neg_one, one_div, mul_comm]

/-- **`S_χ(y)` approximates `L(1, χ)`**: `‖L(1, χ) − S_χ(y)‖ ≤ 2q/(y + 1)`. -/
theorem norm_LFunction_one_sub_charHarmonicSum_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (y : ℕ) :
    ‖DirichletCharacter.LFunction χ 1 - charHarmonicSum χ y‖ ≤ 2 * q / ((y : ℝ) + 1) := by
  rw [charHarmonicSum_eq]
  have h := norm_LFunction_one_sub_partial_le χ hχ (M := y + 1) (by omega)
  push_cast at h
  exact h

/-! ### The logarithmic sum -/

/-- The logarithmic sum `Σ_{n ≤ M} χ(n) log n/n`. -/
def charLogSum (χ : DirichletCharacter ℂ q) (M : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 M, χ (n : ZMod q) * ((Real.log n / n : ℝ) : ℂ)

/-- **The logarithmic sum is bounded**: `‖Σ_{n ≤ M} χ(n) log n/n‖ ≤ 1 + 2q`. -/
theorem norm_charLogSum_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖charLogSum χ M‖ ≤ 1 + 2 * q := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rcases lt_or_ge M 2 with hM | hM
  · interval_cases M <;> simp [charLogSum] <;> positivity
  -- split off `n = 1, 2`; from `n = 3` on, `log x/x` decreases
  set F : ℕ → ℂ := fun n => ((Real.log n / n : ℝ) : ℂ) * χ (n : ZMod q)
  have hrange : charLogSum χ M = ∑ n ∈ range (M + 1), F n := by
    rw [sum_range_succ_eq_sum_Icc (by simp [F]), charLogSum]
    exact sum_congr rfl fun n _ => mul_comm _ _
  have hsplit : ∑ n ∈ range (M + 1), F n =
      F 0 + F 1 + F 2 + ∑ j ∈ range (M - 2), F (3 + j) := by
    rw [show M + 1 = 3 + (M - 2) by omega, sum_range_add]
    simp [Finset.sum_range_succ]
  have hF0 : F 0 = 0 := by simp [F]
  have hF1 : F 1 = 0 := by simp [F]
  have hF2 : ‖F 2‖ ≤ 1 := by
    simp only [F, norm_mul, Complex.norm_real]
    have hl := Real.log_two_lt_d9
    have hl0 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have hχ2 := DirichletCharacter.norm_le_one χ ((2 : ℕ) : ZMod q)
    rw [Real.norm_of_nonneg (by positivity)]
    calc Real.log (2 : ℕ) / (2 : ℕ) * ‖χ ((2 : ℕ) : ZMod q)‖ ≤ Real.log (2 : ℕ) / (2 : ℕ) * 1 :=
          mul_le_mul_of_nonneg_left hχ2 (by positivity)
      _ ≤ 1 := by norm_num; linarith
  -- the tail
  have hanti : Antitone fun j : ℕ => Real.log ((3 + j : ℕ) : ℝ) / ((3 + j : ℕ) : ℝ) := by
    intro a b hab
    have he := Real.exp_one_lt_d9
    have ha : Real.exp 1 ≤ ((3 + a : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a)]
    have hb : Real.exp 1 ≤ ((3 + b : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)]
    exact Real.log_div_self_antitoneOn ha hb (by exact_mod_cast (by omega : 3 + a ≤ 3 + b))
  have hnonneg : ∀ j : ℕ, 0 ≤ Real.log ((3 + j : ℕ) : ℝ) / ((3 + j : ℕ) : ℝ) := fun j =>
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have htail := norm_sum_antitone_mul_le (norm_sum_range_shift_le χ hχ 3) hnonneg hanti (M - 2)
  have hf0 : Real.log ((3 + 0 : ℕ) : ℝ) / ((3 + 0 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by norm_num)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((3 + 0 : ℕ) : ℝ) by norm_num)
    linarith
  have htail' : ‖∑ j ∈ range (M - 2), F (3 + j)‖ ≤ 2 * q :=
    htail.trans (by nlinarith [hnonneg 0])
  rw [hrange, hsplit, hF0, hF1, zero_add, zero_add]
  calc ‖F 2 + ∑ j ∈ range (M - 2), F (3 + j)‖
      ≤ ‖F 2‖ + ‖∑ j ∈ range (M - 2), F (3 + j)‖ := norm_add_le _ _
    _ ≤ 1 + 2 * q := add_le_add hF2 htail'

/-! ### The hyperbola identity -/

/-- `Σ_{m ≤ M} Σ_{t ∣ m} H(t, m/t) = Σ_{t ≤ M} Σ_{k ≤ M/t} H(t, k)`. -/
theorem sum_divisors_eq_sum_Icc_div (H : ℕ → ℕ → ℂ) (M : ℕ) :
    ∑ m ∈ Icc 1 M, ∑ t ∈ m.divisors, H t (m / t) =
      ∑ t ∈ Icc 1 M, ∑ k ∈ Icc 1 (M / t), H t k := by
  have hL : ∑ m ∈ Icc 1 M, ∑ t ∈ m.divisors, H t (m / t) =
      ∑ t ∈ Icc 1 M, ∑ m ∈ (Icc 1 M).filter (t ∣ ·), H t (m / t) := by
    refine sum_comm' fun m t => ?_
    simp only [mem_Icc, mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, htm, -⟩
      exact ⟨⟨⟨h1, h2⟩, htm⟩, Nat.pos_of_dvd_of_pos htm h1, (Nat.le_of_dvd h1 htm).trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, htm⟩, -, -⟩
      exact ⟨⟨h1, h2⟩, htm, by omega⟩
  rw [hL]
  refine sum_congr rfl fun t ht => ?_
  have ht0 : 0 < t := (mem_Icc.mp ht).1
  rw [filter_dvd_Icc_eq_image ht0, sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left ht0 h]
  exact sum_congr rfl fun k _ => by rw [Nat.mul_div_cancel_left k ht0]

/-- The twisted Mertens sum `A_χ(y) = Σ_{t ≤ y} χ(t) Λ(t)/t`. -/
def charMertensSum (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ t ∈ Icc 1 y, χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ)

omit [NeZero q] in
/-- **The hyperbola identity**: `Σ_{n ≤ M} χ(n) log n/n = Σ_{t ≤ M} χ(t)Λ(t)/t · S_χ(M/t)`. -/
theorem charLogSum_eq (χ : DirichletCharacter ℂ q) (M : ℕ) :
    charLogSum χ M =
      ∑ t ∈ Icc 1 M, χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ) * charHarmonicSum χ (M / t) := by
  set H : ℕ → ℕ → ℂ := fun t k =>
    χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ) * (χ (k : ZMod q) * ((1 / k : ℝ) : ℂ))
  -- `χ(m) log m/m = Σ_{t ∣ m} χ(t)Λ(t)/t · χ(m/t)/(m/t)`
  have hm : ∀ m ∈ Icc 1 M,
      χ (m : ZMod q) * ((Real.log m / m : ℝ) : ℂ) = ∑ t ∈ m.divisors, H t (m / t) := by
    intro m _
    rw [← vonMangoldt_sum, Finset.sum_div, Complex.ofReal_sum, mul_sum]
    refine sum_congr rfl fun t ht => ?_
    obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors ht
    have hm0 : m ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors (Nat.mem_divisors_self m
      (Nat.mem_divisors.mp ht).2))
    have ht0 : t ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ht)
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hm0 hk
    subst hk
    rw [Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero ht0)]
    simp only [H]
    have ht' : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ht0
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    push_cast
    rw [map_mul]
    field_simp
  rw [charLogSum, sum_congr rfl hm, sum_divisors_eq_sum_Icc_div H M]
  refine sum_congr rfl fun t _ => ?_
  rw [charHarmonicSum, mul_sum]

/-! ### Mertens' theorem for characters -/

/-- **Mertens' theorem for characters**: for a non-trivial character `χ` the twisted Mertens sum
`A_χ(y) = Σ_{t ≤ y} χ(t)Λ(t)/t` is bounded. -/
theorem exists_norm_charMertensSum_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ y : ℕ, ‖charMertensSum χ y‖ ≤ C := by
  set L := DirichletCharacter.LFunction χ 1
  have hL : L ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
  have hLn : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  refine ⟨(1 + 2 * q + 2 * q * (Real.log 4 + 4)) / ‖L‖, fun y => ?_⟩
  rw [le_div_iff₀ hLn, mul_comm, ← norm_mul]
  -- `L A_χ(y) = charLogSum − Σ_t χ(t)Λ(t)/t (S_χ(y/t) − L)`
  have hid : L * charMertensSum χ y = charLogSum χ y -
      ∑ t ∈ Icc 1 y, χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ) * (charHarmonicSum χ (y / t) - L) := by
    rw [charLogSum_eq, charMertensSum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun t _ => by ring
  -- the error: `Σ_{t ≤ y} Λ(t)/t · 2q/(y/t + 1) ≤ (2q/y) Σ_{t ≤ y} Λ(t)`
  have herr : ‖∑ t ∈ Icc 1 y, χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ) *
      (charHarmonicSum χ (y / t) - L)‖ ≤ 2 * q * (Real.log 4 + 4) := by
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp; positivity
    have hy' : (0 : ℝ) < y := by exact_mod_cast hy
    have hterm : ∀ t ∈ Icc 1 y, ‖χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ) *
        (charHarmonicSum χ (y / t) - L)‖ ≤ 2 * q / y * Λ t := by
      intro t ht
      have ht0 : 0 < t := (mem_Icc.mp ht).1
      have ht' : (0 : ℝ) < t := by exact_mod_cast ht0
      have hΛ : 0 ≤ Λ t := vonMangoldt_nonneg
      have hS := norm_LFunction_one_sub_charHarmonicSum_le χ hχ (y / t)
      rw [norm_sub_rev] at hS
      -- `y < t (y/t + 1)`
      have hlt : (y : ℝ) < t * (((y / t : ℕ) : ℝ) + 1) := by
        exact_mod_cast Nat.lt_mul_div_succ y ht0
      have hS' : 2 * q / (((y / t : ℕ) : ℝ) + 1) ≤ 2 * q * t / y := by
        rw [div_le_div_iff₀ (by positivity) hy']
        nlinarith
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖χ (t : ZMod q)‖ * (Λ t / t) * ‖charHarmonicSum χ (y / t) - L‖
          ≤ 1 * (Λ t / t) * (2 * q * t / y) := by
            gcongr
            · exact DirichletCharacter.norm_le_one χ _
            · exact hS.trans hS'
        _ = 2 * q / y * Λ t := by field_simp
    calc _ ≤ ∑ t ∈ Icc 1 y, 2 * q / y * Λ t := (norm_sum_le _ _).trans (sum_le_sum hterm)
      _ = 2 * q / y * ∑ t ∈ Icc 1 y, Λ t := by rw [mul_sum]
      _ ≤ 2 * q / y * ((Real.log 4 + 4) * y) :=
          mul_le_mul_of_nonneg_left (RHTower.Mertens.sum_vonMangoldt_Icc_le y) (by positivity)
      _ = 2 * q * (Real.log 4 + 4) := by field_simp
  rw [hid]
  calc _ ≤ ‖charLogSum χ y‖ + ‖∑ t ∈ Icc 1 y, χ (t : ZMod q) * ((Λ t / t : ℝ) : ℂ) *
        (charHarmonicSum χ (y / t) - L)‖ := norm_sub_le _ _
    _ ≤ (1 + 2 * q) + 2 * q * (Real.log 4 + 4) := add_le_add (norm_charLogSum_le χ hχ y) herr
    _ = 1 + 2 * q + 2 * q * (Real.log 4 + 4) := by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
