import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremInResidueClasses
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsATensorProduct

/-!
# The horizon counterterm is blind to residue classes

On the `p`-adic valuation classes the horizon counterterm has unbounded rank
(`horizonCounterterm_rank_unbounded`), and the tensor law weights each class by its inverse
density. This file computes the counterterm on the **unit residue classes mod `q`** and finds rank
one: the horizon reads valuations, not residues.

* **Harmonic sums of residue classes** (`abs_classHarmonic_sub_log_le`):
  `S_a(M) = Σ_{m ≤ M, m ≡ a} 1/m` satisfies `|S_a(M) − log M/q| ≤ 2q + 1`. The shift `m ↦ m + 1`
  carries the class `a` onto `a + 1` and moves `S` by at most `2`, so every class is within `2q` of
  the mean `H_M/q`.
* **The logarithmic class sum** (`abs_classLogSum_sub_le`): `L_a(M) = Σ_{m ≤ M, m ≡ a} log(M/m)/m`
  is `(log M)²/(2q)` up to `(2q + 2) log M`, by the telescoping
  `L_a(M + 1) = L_a(M) + log(1 + 1/M) S_a(M)`.
* **The residue Gram** (`primeBilinear_residuePole_eq`): for the residue pole vectors
  `w_a^{(M)} = u^{(M)} 𝟙_{n ≡ a}`,
  `⟨w_a^{(M)}, P w_b^{(M')}⟩ = Σ_{m ≤ M, m ≡ a} R_b(m, M')/m + Σ_{n ≤ M', n ≡ b} R_a(n, M)/n`, where
  `R_b(m, X) = Σ_{t ≤ X/m, mt ≡ b} Λ(t)/t`. For a unit `a` and `m ≡ a` the row is Mertens' sum in
  the class `a⁻¹b` (`classMertensRow_eq`).
* **The residue law** (`exists_abs_residueGram_sub_le`): for units `a, b`,
  `⟨w_a^{(M)}, P w_b^{(M')}⟩ = (q/φ(q)) S_a(M) S_b(M') + O(H_{min(M, M')})`.
* **Rank one** (`exists_abs_atomicWeilForm_unitClassProfile_sub_le`): on every step profile over
  the unit classes, `|P_N(x) − (q/φ(q)) ℓ(x)²| ≤ K Σ |c_α| |c_β| H_{min(M_α, M_β)}`; on the polar
  hyperplane `ℓ(x) = 0` the form is bounded by the mass
  (`exists_abs_atomicWeilForm_unitClassProfile_le_of_polar`).

A single class has Rayleigh quotient `log M/φ(q) + O(1)`: a prime power `t` carries `m ≡ a` back
into its class only when `t ≡ 1`, and these carry `1/φ(q)` of Mertens' logarithm. Two distinct unit
classes interact with the same weight, so the class differences `w_a − w_b` are polar-neutral up to
`O(q)` and survive. The counterterm is the square of the single unit polar functional, weighted by
the inverse unit density `q/φ(q) = Π_{p ∣ q} (1 − 1/p)^{−1}`: refining the unit sieve class by
residues mod `q` adds no divergent direction. The input is Mertens' theorem in residue classes, so
at the horizon Dirichlet's theorem is the statement that residue classes are invisible. Non-unit
classes mix valuations (`n ≡ 0 mod p` is the union of the classes `v_p(n) ≥ 1`) and are excluded.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ}

/-! ### Harmonic sums of residue classes -/

/-- The **class harmonic sum** `S_a(M) = Σ_{m ≤ M, m ≡ a} 1/m`. -/
def classHarmonic (q : ℕ) (a : ZMod q) (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then 1 / (m : ℝ) else 0)

theorem classHarmonic_nonneg (a : ZMod q) (M : ℕ) : 0 ≤ classHarmonic q a M :=
  sum_nonneg fun m _ => by split_ifs <;> positivity

theorem classHarmonic_le_harmonicSum (a : ZMod q) (M : ℕ) :
    classHarmonic q a M ≤ harmonicSum M :=
  sum_le_sum fun m _ => by split_ifs <;> first | exact le_rfl | positivity

theorem classHarmonic_succ (a : ZMod q) (M : ℕ) :
    classHarmonic q a (M + 1) = classHarmonic q a M +
      (if ((M + 1 : ℕ) : ZMod q) = a then 1 / ((M + 1 : ℕ) : ℝ) else 0) := by
  rw [classHarmonic, classHarmonic, sum_Icc_succ_top (by omega)]

theorem sum_Icc_succ_shift (f : ℕ → ℝ) (M : ℕ) :
    ∑ m ∈ Icc 1 (M + 1), f m = f 1 + ∑ m ∈ Icc 1 M, f (m + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_Icc_succ_top (by omega)]
    ring

theorem sum_Icc_one_div_sub_one_div (M : ℕ) :
    ∑ m ∈ Icc 1 M, (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) = 1 - 1 / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- **Neighbouring classes**: `|S_{a+1}(M) − S_a(M)| ≤ 2`. The shift `m ↦ m + 1` carries the class
`a` onto `a + 1`; it costs the telescoping `Σ (1/m − 1/(m + 1)) ≤ 1`, the boundary term at `M + 1`
and the possible element `1`. -/
theorem abs_classHarmonic_add_one_sub_le (a : ZMod q) (M : ℕ) :
    |classHarmonic q (a + 1) M - classHarmonic q a M| ≤ 2 := by
  set S' := ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then 1 / ((m : ℝ) + 1) else 0)
  have hshift : classHarmonic q (a + 1) (M + 1) =
      (if ((1 : ℕ) : ZMod q) = a + 1 then 1 / ((1 : ℕ) : ℝ) else 0) + S' := by
    rw [classHarmonic, sum_Icc_succ_shift]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    by_cases hm : (m : ZMod q) = a
    · rw [if_pos (by push_cast; rw [hm]), if_pos hm, Nat.cast_add, Nat.cast_one]
    · rw [if_neg (by push_cast; exact fun h => hm (add_right_cancel h)), if_neg hm]
  have h2 := classHarmonic_succ (a + 1) M
  have hε : 0 ≤ (if ((1 : ℕ) : ZMod q) = a + 1 then 1 / ((1 : ℕ) : ℝ) else 0) ∧
      (if ((1 : ℕ) : ZMod q) = a + 1 then 1 / ((1 : ℕ) : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hδ : 0 ≤ (if ((M + 1 : ℕ) : ZMod q) = a + 1 then 1 / ((M + 1 : ℕ) : ℝ) else 0) ∧
      (if ((M + 1 : ℕ) : ZMod q) = a + 1 then 1 / ((M + 1 : ℕ) : ℝ) else 0) ≤ 1 := by
    split_ifs
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.le_add_left 1 M
    · norm_num
  have hS'le : S' ≤ classHarmonic q a M := sum_le_sum fun m hm => by
    have hm' : (0 : ℝ) < m := by exact_mod_cast pos_of_mem_Icc' hm
    split_ifs
    · exact one_div_le_one_div_of_le hm' (by linarith)
    · exact le_rfl
  have hS'ge : classHarmonic q a M ≤ S' + 1 := by
    have htel : classHarmonic q a M - S' ≤ ∑ m ∈ Icc 1 M, (1 / (m : ℝ) - 1 / ((m : ℝ) + 1)) := by
      rw [classHarmonic, ← sum_sub_distrib]
      refine sum_le_sum fun m hm => ?_
      have hm' : (0 : ℝ) < m := by exact_mod_cast pos_of_mem_Icc' hm
      split_ifs
      · exact le_rfl
      · rw [sub_self]
        exact sub_nonneg.mpr (one_div_le_one_div_of_le hm' (by linarith))
    have h1 : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
    rw [sum_Icc_one_div_sub_one_div] at htel
    linarith
  rw [abs_le]
  constructor <;> linarith [hε.1, hε.2, hδ.1, hδ.2]

/-- **All residue classes are comparable**: `|S_b(M) − S_a(M)| ≤ 2q`. -/
theorem abs_classHarmonic_sub_le [NeZero q] (a b : ZMod q) (M : ℕ) :
    |classHarmonic q b M - classHarmonic q a M| ≤ 2 * q := by
  have hstep : ∀ j : ℕ, |classHarmonic q (a + j) M - classHarmonic q a M| ≤ 2 * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h := abs_classHarmonic_add_one_sub_le (a + (j : ZMod q)) M
      push_cast
      rw [← add_assoc]
      calc |classHarmonic q (a + j + 1) M - classHarmonic q a M|
          = |(classHarmonic q (a + j + 1) M - classHarmonic q (a + j) M) +
              (classHarmonic q (a + j) M - classHarmonic q a M)| := by rw [sub_add_sub_cancel]
        _ ≤ 2 + 2 * j := (abs_add_le _ _).trans (add_le_add h ih)
        _ = 2 * ((j : ℝ) + 1) := by ring
  have h := hstep (b - a).val
  rw [ZMod.natCast_zmod_val, add_sub_cancel] at h
  refine h.trans ?_
  have : ((b - a).val : ℝ) ≤ q := by exact_mod_cast (ZMod.val_lt (b - a)).le
  linarith

theorem sum_classHarmonic [NeZero q] (M : ℕ) :
    ∑ a : ZMod q, classHarmonic q a M = harmonicSum M := by
  unfold classHarmonic harmonicSum
  rw [sum_comm]
  simp

/-- **Harmonic sums in residue classes**: `|S_a(M) − log M/q| ≤ 2q + 1`. -/
theorem abs_classHarmonic_sub_log_le [NeZero q] (a : ZMod q) (M : ℕ) :
    |classHarmonic q a M - Real.log M / q| ≤ 2 * q + 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  -- `q S_a(M) − H_M = Σ_b (S_a(M) − S_b(M))`
  have hsum : (q : ℝ) * classHarmonic q a M - harmonicSum M =
      ∑ b : ZMod q, (classHarmonic q a M - classHarmonic q b M) := by
    rw [sum_sub_distrib, sum_classHarmonic, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have hdev : |(q : ℝ) * classHarmonic q a M - harmonicSum M| ≤ q * (2 * q) := by
    rw [hsum]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ b : ZMod q, |classHarmonic q a M - classHarmonic q b M|
        ≤ ∑ _b : ZMod q, 2 * (q : ℝ) := sum_le_sum fun b _ => abs_classHarmonic_sub_le b a M
      _ = q * (2 * q) := by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have hH1 := harmonicSum_le M
  have hH2 := log_le_harmonicSum M
  have hmain : |(q : ℝ) * classHarmonic q a M - Real.log M| ≤ q * (2 * q) + 1 := by
    rw [abs_le] at hdev ⊢
    constructor <;> linarith [hdev.1, hdev.2]
  have heq : classHarmonic q a M - Real.log M / q =
      ((q : ℝ) * classHarmonic q a M - Real.log M) / q := by
    field_simp
  rw [heq, abs_div, abs_of_pos hq, div_le_iff₀ hq]
  nlinarith

/-! ### The logarithmic class sum -/

/-- The **logarithmic class sum** `L_a(M) = Σ_{m ≤ M, m ≡ a} log(M/m)/m`. -/
def classLogSum (q : ℕ) (a : ZMod q) (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then (Real.log M - Real.log m) / m else 0)

/-- The telescoping step `L_a(M + 1) = L_a(M) + log((M + 1)/M) S_a(M)`. -/
theorem classLogSum_succ (a : ZMod q) (M : ℕ) :
    classLogSum q a (M + 1) =
      classLogSum q a M + (Real.log (M + 1 : ℕ) - Real.log M) * classHarmonic q a M := by
  rw [classLogSum, sum_Icc_succ_top (by omega)]
  simp only [sub_self, zero_div, ite_self, add_zero]
  rw [classLogSum, classHarmonic, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

/-- **The logarithmic class sum**: `|L_a(M) − (log M)²/(2q)| ≤ (2q + 2) log M` for `M ≥ 1`. -/
theorem abs_classLogSum_sub_le [NeZero q] (a : ZMod q) {M : ℕ} (hM : 1 ≤ M) :
    |classLogSum q a M - Real.log M ^ 2 / (2 * q)| ≤ (2 * q + 2) * Real.log M := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  induction M, hM using Nat.le_induction with
  | base => simp [classLogSum]
  | succ M hM ih =>
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    set δ := Real.log (M + 1 : ℕ) - Real.log M with hδ
    have hδ0 : 0 ≤ δ := sub_nonneg.mpr (Real.log_le_log (by linarith) (by push_cast; linarith))
    have hδ1 : δ ≤ 1 := by
      have h2 : Real.log (M + 1 : ℕ) ≤ Real.log (2 * M) :=
        Real.log_le_log (by positivity) (by push_cast; linarith)
      rw [Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < M).ne'] at h2
      have := Real.log_two_lt_d9
      norm_num at this
      linarith
    have hlog : Real.log (M + 1 : ℕ) = Real.log M + δ := by rw [hδ]; ring
    rw [classLogSum_succ, ← hδ, hlog]
    have hS := abs_classHarmonic_sub_log_le a M
    -- one step moves the error by `δ (S_a(M) − log M/q) − δ²/(2q)`
    have hkey : classLogSum q a M + δ * classHarmonic q a M - (Real.log M + δ) ^ 2 / (2 * q) =
        (classLogSum q a M - Real.log M ^ 2 / (2 * q)) +
          δ * (classHarmonic q a M - Real.log M / q) - δ ^ 2 / (2 * q) := by
      field_simp
      ring
    rw [hkey]
    have h1 : |δ * (classHarmonic q a M - Real.log M / q)| ≤ δ * (2 * q + 1) := by
      rw [abs_mul, abs_of_nonneg hδ0]
      exact mul_le_mul_of_nonneg_left hS hδ0
    have h3 : δ ^ 2 / (2 * q) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hδ1 hδ0, mul_nonneg hδ0 (by linarith : (0 : ℝ) ≤ 2 * q - 1)]
    have h4 : 0 ≤ δ ^ 2 / (2 * q) := by positivity
    rw [abs_le] at ih h1 ⊢
    constructor <;> linarith [ih.1, ih.2, h1.1, h1.2]

theorem sum_classLog_div_eq (a : ZMod q) (c : ℝ) (M X : ℕ) :
    ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then (Real.log X - Real.log m) / c / m else 0) =
      (classLogSum q a M + (Real.log X - Real.log M) * classHarmonic q a M) / c := by
  rw [classLogSum, classHarmonic, mul_sum, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

/-! ### Residue pole vectors and their Gram -/

/-- The **residue pole vector** `w_a^{(M)}_n = n^{−1/2} 𝟙_{n ≤ M, n ≡ a (mod q)}`. -/
def residuePole (q : ℕ) (a : ZMod q) (M n : ℕ) : ℝ :=
  if (n : ZMod q) = a then truncPole M n else 0

/-- The **residue row** `R_b(m, X) = Σ_{t ≤ X/m, mt ≡ b} Λ(t)/t`: the prime powers carrying `m`
into the class `b`. -/
def classMertensRow (q : ℕ) (b : ZMod q) (m X : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 (X / m), (if ((m * t : ℕ) : ZMod q) = b then Λ t / t else 0)

/-- Summing over the multiples of `m` in `[1, X]` is summing over `t ≤ X/m`. -/
theorem sum_Icc_dvd_eq {m : ℕ} (hm : 0 < m) (X : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ Icc 1 X, (if m ∣ n then g n else 0) = ∑ t ∈ Icc 1 (X / m), g (m * t) := by
  rw [← sum_filter, filter_dvd_Icc_eq_image hm,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h]

/-- The residue Gram through Schur rows:
`⟨w_a^{(M)}, P w_b^{(M')}⟩ = Σ_{m ≤ M, m ≡ a} (Σ_{n ≤ M', n ≡ b} P(m, n) √(m/n))/m`. -/
theorem primeBilinear_residuePole_rows (a b : ZMod q) {M M' N : ℕ} (hMN : M ≤ N)
    (hM'N : M' ≤ N) :
    primeBilinear N (residuePole q a M) (residuePole q b M') =
      ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then
        (∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then
          weilPrimeKernel m n * Real.sqrt ((m : ℝ) / n) else 0)) / m else 0) := by
  unfold primeBilinear
  rw [← sum_truncate hMN]
  refine sum_congr rfl fun m hm => ?_
  have hm0 := pos_of_mem_Icc' hm
  by_cases hmM : m ≤ M
  · rw [if_pos hmM]
    by_cases ha : (m : ZMod q) = a
    · rw [if_pos ha, ← sum_truncate hM'N, sum_div]
      refine sum_congr rfl fun n hn => ?_
      have hn0 := pos_of_mem_Icc' hn
      simp only [residuePole, truncPole, if_pos ha, if_pos hmM]
      by_cases hb : (n : ZMod q) = b
      · by_cases hnM : n ≤ M'
        · simp only [if_pos hb, if_pos hnM]
          exact poleVector_mul_poleVector_mul hm0 hn0
        · simp only [if_pos hb, if_neg hnM]
          ring
      · simp only [if_neg hb]
        split_ifs <;> ring
    · rw [if_neg ha]
      simp [residuePole, ha]
  · rw [if_neg hmM]
    simp [residuePole, truncPole, hmM]

/-- The up part of a row: `Σ_{n ≤ X, n ≡ b, m ∣ n, n ≠ m} Λ(n/m)/(n/m) = R_b(m, X)`. -/
theorem sum_up_residue_eq (b : ZMod q) {m : ℕ} (hm : 0 < m) (X : ℕ) :
    ∑ n ∈ Icc 1 X, (if (n : ZMod q) = b then
      (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) else 0) =
      classMertensRow q b m X := by
  have hterm : ∀ n ∈ Icc 1 X, (if (n : ZMod q) = b then
      (if m ∣ n ∧ m ≠ n then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) else 0) =
      if m ∣ n then (if (n : ZMod q) = b then Λ (n / m) / ((n / m : ℕ) : ℝ) else 0) else 0 := by
    intro n _
    by_cases h : m ∣ n
    · by_cases h' : m = n
      · subst h'; simp [Nat.div_self hm]
      · rw [if_pos (show m ∣ n ∧ m ≠ n from ⟨h, h'⟩), if_pos h]
    · simp [h]
  rw [sum_congr rfl hterm, sum_Icc_dvd_eq hm, classMertensRow]
  exact sum_congr rfl fun t _ => by rw [Nat.mul_div_cancel_left t hm]

/-- The down part, summed over the class `a`: `Σ_{m ≤ M, m ≡ a} (Σ_{n ≤ M', n ≡ b, n ∣ m, n ≠ m}
Λ(m/n))/m = Σ_{n ≤ M', n ≡ b} R_a(n, M)/n`. -/
theorem sum_down_residue_eq (a b : ZMod q) (M M' : ℕ) :
    ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then
      (∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then
        (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) else 0)) / m else 0) =
      ∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then classMertensRow q a n M / n else 0) := by
  have hL : ∀ m ∈ Icc 1 M, (if (m : ZMod q) = a then
      (∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then
        (if n ∣ m ∧ n ≠ m then Λ (m / n) else 0) else 0)) / m else 0) =
      ∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then
        (if n ∣ m then (if (m : ZMod q) = a then Λ (m / n) / m else 0) else 0) else 0) := by
    intro m hm
    have hm0 := pos_of_mem_Icc' hm
    split_ifs with ha
    · rw [sum_div]
      refine sum_congr rfl fun n _ => ?_
      by_cases hb : (n : ZMod q) = b
      · simp only [if_pos hb]
        by_cases h : n ∣ m
        · by_cases h' : n = m
          · subst h'; simp [Nat.div_self hm0]
          · rw [if_pos (show n ∣ m ∧ n ≠ m from ⟨h, h'⟩), if_pos h]
        · rw [if_neg (fun h'' => h h''.1), if_neg h, zero_div]
      · simp only [if_neg hb, zero_div]
    · symm
      exact sum_eq_zero fun n _ => by simp
  rw [sum_congr rfl hL, sum_comm]
  refine sum_congr rfl fun n hn => ?_
  have hn0 := pos_of_mem_Icc' hn
  by_cases hb : (n : ZMod q) = b
  · simp only [if_pos hb]
    rw [sum_Icc_dvd_eq hn0, classMertensRow, sum_div]
    refine sum_congr rfl fun t _ => ?_
    rw [Nat.mul_div_cancel_left t hn0]
    split_ifs
    · push_cast
      ring
    · rw [zero_div]
  · simp only [if_neg hb, sum_const_zero]

/-- **The residue Gram**: for `M, M' ≤ N`,
`⟨w_a^{(M)}, P w_b^{(M')}⟩ = Σ_{m ≤ M, m ≡ a} R_b(m, M')/m + Σ_{n ≤ M', n ≡ b} R_a(n, M)/n`. -/
theorem primeBilinear_residuePole_eq (a b : ZMod q) {M M' N : ℕ} (hMN : M ≤ N)
    (hM'N : M' ≤ N) :
    primeBilinear N (residuePole q a M) (residuePole q b M') =
      ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then classMertensRow q b m M' / m else 0) +
        ∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then classMertensRow q a n M / n else 0) := by
  rw [primeBilinear_residuePole_rows a b hMN hM'N, ← sum_down_residue_eq a b M M',
    ← sum_add_distrib]
  refine sum_congr rfl fun m hm => ?_
  have hm0 := pos_of_mem_Icc' hm
  split_ifs with ha
  · rw [← sum_up_residue_eq b hm0 M', ← add_div, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun n hn => ?_
    rw [weilPrimeKernel_mul_sqrt_ratio hm0 (pos_of_mem_Icc' hn)]
    split_ifs <;> ring
  · ring

/-- For `m ≡ a` with `a` a unit, the residue row is Mertens' sum in the class `a⁻¹b`:
`R_b(m, X) = A(⌊X/m⌋; a⁻¹b)`. -/
theorem classMertensRow_eq {a : ZMod q} (ha : IsUnit a) (b : ZMod q) {m : ℕ}
    (hm : (m : ZMod q) = a) (X : ℕ) :
    classMertensRow q b m X = classMertensSum q (a⁻¹ * b) (X / m) := by
  unfold classMertensRow classMertensSum
  refine sum_congr rfl fun t _ => ?_
  have hiff : ((m * t : ℕ) : ZMod q) = b ↔ (t : ZMod q) = a⁻¹ * b := by
    rw [Nat.cast_mul, hm]
    constructor
    · intro h
      rw [← h, ← mul_assoc, ZMod.inv_mul_of_unit a ha, one_mul]
    · intro h
      rw [h, ← mul_assoc, ZMod.mul_inv_of_unit a ha, one_mul]
  by_cases h : (t : ZMod q) = a⁻¹ * b
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- A class-weighted Mertens sum: if `|A(y; r) − log y/φ(q)| ≤ C` for `y ≥ 1`, then for `M ≤ X`,
`|Σ_{m ≤ M, m ≡ a} A(⌊X/m⌋; r)/m − Σ_{m ≤ M, m ≡ a} (log X − log m)/(φ(q) m)| ≤ (C + log 2) S_a(M)`. -/
theorem abs_sum_classMertens_div_sub_le [NeZero q] {r : ZMod q} {C : ℝ}
    (hA : ∀ y : ℕ, 1 ≤ y → |classMertensSum q r y - Real.log y / q.totient| ≤ C)
    (a : ZMod q) {M X : ℕ} (hMX : M ≤ X) :
    |∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then classMertensSum q r (X / m) / m else 0) -
        ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then
          (Real.log X - Real.log m) / q.totient / m else 0)| ≤
      (C + Real.log 2) * classHarmonic q a M := by
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [← sum_sub_distrib, classHarmonic, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmX := (mem_Icc.mp hm).2.trans hMX
  split_ifs with ha
  · have hq1 : 1 ≤ X / m := (Nat.le_div_iff_mul_le hm0).mpr (by omega)
    have h1 := hA (X / m) hq1
    have h2 := log_div_add_log_le hm0 hmX
    have h3 := log_le_log_div_add_log hm0 hmX
    -- `|log ⌊X/m⌋ − (log X − log m)|/φ(q) ≤ log 2`
    have h4 : |Real.log ((X / m : ℕ) : ℝ) / q.totient -
        (Real.log X - Real.log m) / q.totient| ≤ Real.log 2 := by
      have hφ0 : (0 : ℝ) < q.totient := by linarith
      rw [← sub_div, abs_div, abs_of_pos hφ0, div_le_iff₀ hφ0]
      have : |Real.log ((X / m : ℕ) : ℝ) - (Real.log X - Real.log m)| ≤ Real.log 2 := by
        rw [abs_le]; constructor <;> linarith
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith
    rw [← sub_div, abs_div, abs_of_pos hm', mul_one_div]
    refine div_le_div_of_nonneg_right ?_ hm'.le
    calc |classMertensSum q r (X / m) - (Real.log X - Real.log m) / q.totient|
        = |(classMertensSum q r (X / m) - Real.log ((X / m : ℕ) : ℝ) / q.totient) +
            (Real.log ((X / m : ℕ) : ℝ) / q.totient - (Real.log X - Real.log m) / q.totient)| := by
          rw [sub_add_sub_cancel]
      _ ≤ C + Real.log 2 := (abs_add_le _ _).trans (add_le_add h1 h4)
  · simp

/-- **The residue law**: for units `a, b` there is `K` with
`|⟨w_a^{(M)}, P w_b^{(M')}⟩ − (q/φ(q)) S_a(M) S_b(M')| ≤ K H_M` for `1 ≤ M ≤ M' ≤ N`. -/
theorem abs_residueGram_sub_le [NeZero q] {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    ∃ K : ℝ, ∀ {M M' N : ℕ}, 1 ≤ M → M ≤ M' → M' ≤ N →
      |primeBilinear N (residuePole q a M) (residuePole q b M') -
          (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M'| ≤
        K * harmonicSum M := by
  have hainv : IsUnit a⁻¹ := IsUnit.of_mul_eq_one a (ZMod.inv_mul_of_unit a ha)
  have hbinv : IsUnit b⁻¹ := IsUnit.of_mul_eq_one b (ZMod.inv_mul_of_unit b hb)
  obtain ⟨C₁, hC₁⟩ := exists_abs_classMertensSum_sub_le (hainv.mul hb)
  obtain ⟨C₂, hC₂⟩ := exists_abs_classMertensSum_sub_le (hbinv.mul ha)
  have hC₁0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC₁ 1 le_rfl)
  have hC₂0 : 0 ≤ C₂ := (abs_nonneg _).trans (hC₂ 1 le_rfl)
  refine ⟨C₁ + C₂ + 2 * Real.log 2 + (2 * q ^ 2 + 7 * q + 5), fun {M M' N} hM hMM' hM'N => ?_⟩
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  rw [primeBilinear_residuePole_eq a b (hMM'.trans hM'N) hM'N]
  -- the rows are Mertens sums in residue classes
  have hT1 : ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then classMertensRow q b m M' / m else 0) =
      ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then classMertensSum q (a⁻¹ * b) (M' / m) / m
        else 0) :=
    sum_congr rfl fun m _ => by
      split_ifs with hm
      · rw [classMertensRow_eq ha b hm]
      · rfl
  have hT2 : ∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then classMertensRow q a n M / n else 0) =
      ∑ n ∈ Icc 1 M, (if (n : ZMod q) = b then classMertensSum q (b⁻¹ * a) (M / n) / n
        else 0) := by
    -- the rows of `n > M` are empty
    have hsub : ∑ n ∈ Icc 1 M, (if (n : ZMod q) = b then classMertensRow q a n M / n else 0) =
        ∑ n ∈ Icc 1 M', (if (n : ZMod q) = b then classMertensRow q a n M / n else 0) := by
      refine sum_subset (Icc_subset_Icc_right hMM') fun n hn hn' => ?_
      have hnM : M < n := by simp only [mem_Icc] at hn hn'; omega
      rw [classMertensRow, Nat.div_eq_of_lt hnM, Finset.Icc_eq_empty (by norm_num), sum_empty,
        zero_div, ite_self]
    rw [← hsub]
    exact sum_congr rfl fun n _ => by
      split_ifs with hn
      · rw [classMertensRow_eq hb a hn]
      · rfl
  rw [hT1, hT2]
  have hE1 := abs_sum_classMertens_div_sub_le hC₁ a hMM'
  have hE2 := abs_sum_classMertens_div_sub_le hC₂ b (le_refl M)
  rw [sum_classLog_div_eq] at hE1 hE2
  -- the main terms: `L_a + L_b + (log M' − log M) S_a − q S_a S_b'` is `O(log M + q² S_a)`
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hSa0 := classHarmonic_nonneg a M
  have hLa := abs_classLogSum_sub_le a hM
  have hLb := abs_classLogSum_sub_le b hM
  have hSa := abs_classHarmonic_sub_log_le a M
  have hSb' := abs_classHarmonic_sub_log_le b M'
  have hB : |classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M +
      (classLogSum q b M + (Real.log M - Real.log M) * classHarmonic q b M) -
      q * classHarmonic q a M * classHarmonic q b M'| ≤
      (6 * q + 5) * Real.log M + q * (2 * q + 1) * classHarmonic q a M := by
    have e : classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M +
        (classLogSum q b M + (Real.log M - Real.log M) * classHarmonic q b M) -
        q * classHarmonic q a M * classHarmonic q b M' =
        (classLogSum q a M - Real.log M ^ 2 / (2 * q)) +
          (classLogSum q b M - Real.log M ^ 2 / (2 * q)) -
          (classHarmonic q a M - Real.log M / q) * Real.log M -
          q * classHarmonic q a M * (classHarmonic q b M' - Real.log M' / q) := by
      field_simp
      ring
    have h3 : |(classHarmonic q a M - Real.log M / q) * Real.log M| ≤
        (2 * q + 1) * Real.log M := by
      rw [abs_mul, abs_of_nonneg hlogM]
      exact mul_le_mul_of_nonneg_right hSa hlogM
    have hqS : 0 ≤ (q : ℝ) * classHarmonic q a M := mul_nonneg hq.le hSa0
    have h4 : |q * classHarmonic q a M * (classHarmonic q b M' - Real.log M' / q)| ≤
        q * classHarmonic q a M * (2 * q + 1) := by
      rw [abs_mul, abs_of_nonneg hqS]
      exact mul_le_mul_of_nonneg_left hSb' hqS
    rw [e]
    obtain ⟨h1l, h1u⟩ := abs_le.mp hLa
    obtain ⟨h2l, h2u⟩ := abs_le.mp hLb
    obtain ⟨h3l, h3u⟩ := abs_le.mp h3
    obtain ⟨h4l, h4u⟩ := abs_le.mp h4
    rw [abs_le]
    constructor <;> linarith
  set B := classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M +
      (classLogSum q b M + (Real.log M - Real.log M) * classHarmonic q b M) -
      q * classHarmonic q a M * classHarmonic q b M' with hBdef
  have hBφ : |B / q.totient| ≤ |B| := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < q.totient by linarith)]
    exact div_le_self (abs_nonneg _) hφ
  have hsplit : ∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then
        classMertensSum q (a⁻¹ * b) (M' / m) / m else 0) +
      ∑ n ∈ Icc 1 M, (if (n : ZMod q) = b then classMertensSum q (b⁻¹ * a) (M / n) / n else 0) -
      (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M' =
      (∑ m ∈ Icc 1 M, (if (m : ZMod q) = a then
          classMertensSum q (a⁻¹ * b) (M' / m) / m else 0) -
        (classLogSum q a M + (Real.log M' - Real.log M) * classHarmonic q a M) / q.totient) +
      (∑ n ∈ Icc 1 M, (if (n : ZMod q) = b then
          classMertensSum q (b⁻¹ * a) (M / n) / n else 0) -
        (classLogSum q b M + (Real.log M - Real.log M) * classHarmonic q b M) / q.totient) +
      B / q.totient := by
    rw [hBdef]; ring
  rw [hsplit]
  -- every term is at most a multiple of `H_M`
  have hSaH := classHarmonic_le_harmonicSum a M
  have hSbH := classHarmonic_le_harmonicSum b M
  have hlH := log_le_harmonicSum M
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have k1 : (C₁ + Real.log 2) * classHarmonic q a M ≤ (C₁ + Real.log 2) * harmonicSum M :=
    mul_le_mul_of_nonneg_left hSaH (by linarith)
  have k2 : (C₂ + Real.log 2) * classHarmonic q b M ≤ (C₂ + Real.log 2) * harmonicSum M :=
    mul_le_mul_of_nonneg_left hSbH (by linarith)
  have k3 : (6 * q + 5) * Real.log M ≤ (6 * q + 5) * harmonicSum M :=
    mul_le_mul_of_nonneg_left hlH (by positivity)
  have k4 : q * (2 * q + 1) * classHarmonic q a M ≤ q * (2 * q + 1) * harmonicSum M :=
    mul_le_mul_of_nonneg_left hSaH (by positivity)
  calc _ ≤ (C₁ + Real.log 2) * classHarmonic q a M + (C₂ + Real.log 2) * classHarmonic q b M +
        ((6 * q + 5) * Real.log M + q * (2 * q + 1) * classHarmonic q a M) :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hE1 hE2))
          (hBφ.trans hB))
    _ ≤ _ := by nlinarith

/-- **The residue law, uniform form**: there is `K` such that for all units `a, b` and
`1 ≤ M, M' ≤ N`, `|⟨w_a^{(M)}, P w_b^{(M')}⟩ − (q/φ(q)) S_a(M) S_b(M')| ≤ K H_{min(M, M')}`. -/
theorem exists_abs_residueGram_sub_le [NeZero q] :
    ∃ K : ℝ, ∀ {a b : ZMod q}, IsUnit a → IsUnit b → ∀ {M M' N : ℕ}, 1 ≤ M → 1 ≤ M' →
      M ≤ N → M' ≤ N →
      |primeBilinear N (residuePole q a M) (residuePole q b M') -
          (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M'| ≤
        K * harmonicSum (min M M') := by
  have hex : ∀ a b : ZMod q, ∃ K : ℝ, IsUnit a → IsUnit b → ∀ {M M' N : ℕ}, 1 ≤ M → M ≤ M' →
      M' ≤ N → |primeBilinear N (residuePole q a M) (residuePole q b M') -
          (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M'| ≤
        K * harmonicSum M := by
    intro a b
    by_cases hab : IsUnit a ∧ IsUnit b
    · obtain ⟨K, hK⟩ := abs_residueGram_sub_le hab.1 hab.2
      exact ⟨K, fun _ _ => hK⟩
    · exact ⟨0, fun ha hb => absurd ⟨ha, hb⟩ hab⟩
  choose K hK using hex
  set K₀ := ∑ a : ZMod q, ∑ b : ZMod q, |K a b|
  have hKle : ∀ a b, |K a b| ≤ K₀ := fun a b =>
    (single_le_sum (f := fun b' => |K a b'|) (fun _ _ => abs_nonneg _) (mem_univ b)).trans
      (single_le_sum (f := fun a' => ∑ b', |K a' b'|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ a))
  refine ⟨K₀, fun {a b} ha hb {M M' N} hM hM' hMN hM'N => ?_⟩
  rcases le_total M M' with h | h
  · rw [min_eq_left h]
    exact (hK a b ha hb hM h hM'N).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (hKle a b)) (harmonicSum_nonneg M))
  · rw [min_eq_right h, primeBilinear_comm,
      show (q : ℝ) / q.totient * classHarmonic q a M * classHarmonic q b M' =
        (q : ℝ) / q.totient * classHarmonic q b M' * classHarmonic q a M by ring]
    exact (hK b a hb ha hM' h hMN).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (hKle b a)) (harmonicSum_nonneg M'))

/-! ### Unit-class step profiles -/

/-- A **unit-class step profile** `x = Σ_{a ∈ (ℤ/q)ˣ} Σ_i c_{a,i} w_a^{(M_i)}`. -/
def unitClassProfile (q : ℕ) [NeZero q] {k : ℕ} (c : (ZMod q)ˣ × Fin k → ℝ) (M : Fin k → ℕ)
    (n : ℕ) : ℝ :=
  ∑ α : (ZMod q)ˣ × Fin k, c α * residuePole q α.1 (M α.2) n

theorem polarFunctional_residuePole (a : ZMod q) {M N : ℕ} (hMN : M ≤ N) :
    polarFunctional N (residuePole q a M) = classHarmonic q a M := by
  unfold polarFunctional classHarmonic
  rw [← sum_truncate hMN]
  refine sum_congr rfl fun n _ => ?_
  simp only [residuePole, truncPole]
  split_ifs <;> simp [← sq, poleVector_sq]

theorem polarFunctional_fintype_sum {ι : Type*} [Fintype ι] (N : ℕ) (c : ι → ℝ)
    (x : ι → ℕ → ℝ) :
    polarFunctional N (fun n => ∑ i, c i * x i n) = ∑ i, c i * polarFunctional N (x i) := by
  unfold polarFunctional
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun n _ => by ring

/-- The polar functional of a unit-class profile: `ℓ(x) = Σ_{a,i} c_{a,i} S_a(M_i)`. -/
theorem polarFunctional_unitClassProfile [NeZero q] {k N : ℕ} (c : (ZMod q)ˣ × Fin k → ℝ)
    (M : Fin k → ℕ) (hM : ∀ i, M i ≤ N) :
    polarFunctional N (unitClassProfile q c M) = ∑ α, c α * classHarmonic q α.1 (M α.2) :=
  (polarFunctional_fintype_sum N c fun α => residuePole q α.1 (M α.2)).trans
    (sum_congr rfl fun α _ => by rw [polarFunctional_residuePole _ (hM α.2)])

/-- **The horizon counterterm on the unit classes is rank one.** There is `K` such that for every
step profile over the unit classes mod `q` with `1 ≤ M_i ≤ N`,
`|P_N(x) − (q/φ(q)) ℓ(x)²| ≤ K Σ_{α, β} |c_α| |c_β| H_{min(M_α, M_β)}`. -/
theorem exists_abs_atomicWeilForm_unitClassProfile_sub_le [NeZero q] :
    ∃ K : ℝ, ∀ {k N : ℕ} (c : (ZMod q)ˣ × Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) →
      (∀ i, 1 ≤ M i) →
      |atomicWeilForm N (unitClassProfile q c M) -
          (q : ℝ) / q.totient * polarFunctional N (unitClassProfile q c M) ^ 2| ≤
        K * ∑ α, ∑ β, |c α| * |c β| * harmonicSum (min (M α.2) (M β.2)) := by
  obtain ⟨K, hK⟩ := exists_abs_residueGram_sub_le (q := q)
  refine ⟨K, fun {k N} c M hM hM1 => ?_⟩
  set G : (ZMod q)ˣ × Fin k → (ZMod q)ˣ × Fin k → ℝ := fun α β =>
    primeBilinear N (residuePole q α.1 (M α.2)) (residuePole q β.1 (M β.2))
  set T : (ZMod q)ˣ × Fin k → (ZMod q)ˣ × Fin k → ℝ := fun α β =>
    (q : ℝ) / q.totient * classHarmonic q α.1 (M α.2) * classHarmonic q β.1 (M β.2)
  have hexp : atomicWeilForm N (unitClassProfile q c M) = ∑ α, ∑ β, c α * c β * G α β := by
    have hL : ∀ y, primeBilinear N (unitClassProfile q c M) y =
        ∑ α, c α * primeBilinear N (residuePole q α.1 (M α.2)) y := fun y =>
      primeBilinear_fintype_sum_left N c (fun α => residuePole q α.1 (M α.2)) y
    rw [atomicWeilForm_eq_primeBilinear, hL]
    refine sum_congr rfl fun α _ => ?_
    rw [primeBilinear_comm, hL, mul_sum]
    refine sum_congr rfl fun β _ => ?_
    simp only [G]
    rw [primeBilinear_comm]
    ring
  have htarget : (q : ℝ) / q.totient * polarFunctional N (unitClassProfile q c M) ^ 2 =
      ∑ α, ∑ β, c α * c β * T α β := by
    rw [polarFunctional_unitClassProfile c M hM, sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun α _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun β _ => by simp only [T]; ring
  have hterm : ∀ α β, |G α β - T α β| ≤ K * harmonicSum (min (M α.2) (M β.2)) := fun α β =>
    hK α.1.isUnit β.1.isUnit (hM1 α.2) (hM1 β.2) (hM α.2) (hM β.2)
  rw [hexp, htarget, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib]
  calc |∑ α, ∑ β, (c α * c β * G α β - c α * c β * T α β)|
      ≤ ∑ α, ∑ β, |c α * c β * G α β - c α * c β * T α β| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun α _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ α, ∑ β, |c α| * |c β| * (K * harmonicSum (min (M α.2) (M β.2))) := by
        refine sum_le_sum fun α _ => sum_le_sum fun β _ => ?_
        rw [← mul_sub, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hterm α β) (by positivity)
    _ = K * ∑ α, ∑ β, |c α| * |c β| * harmonicSum (min (M α.2) (M β.2)) := by
        rw [mul_sum]
        refine sum_congr rfl fun α _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun β _ => by ring

/-- **Survival on the unit classes is the polar hyperplane**: a unit-class step profile with
`ℓ(x) = 0` has `|P_N(x)| ≤ K Σ_{α, β} |c_α| |c_β| H_{min(M_α, M_β)}`, with no horizon divergence. -/
theorem exists_abs_atomicWeilForm_unitClassProfile_le_of_polar [NeZero q] :
    ∃ K : ℝ, ∀ {k N : ℕ} (c : (ZMod q)ˣ × Fin k → ℝ) (M : Fin k → ℕ), (∀ i, M i ≤ N) →
      (∀ i, 1 ≤ M i) → polarFunctional N (unitClassProfile q c M) = 0 →
      |atomicWeilForm N (unitClassProfile q c M)| ≤
        K * ∑ α, ∑ β, |c α| * |c β| * harmonicSum (min (M α.2) (M β.2)) := by
  obtain ⟨K, hK⟩ := exists_abs_atomicWeilForm_unitClassProfile_sub_le (q := q)
  refine ⟨K, fun c M hM hM1 h0 => ?_⟩
  have h := hK c M hM hM1
  rwa [h0, zero_pow two_ne_zero, mul_zero, sub_zero] at h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
