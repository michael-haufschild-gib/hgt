import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Controlled Leibniz laws on the natural numbers

Real normed-vector-space-valued Leibniz laws with a linearly bounded additive defect are
exactly the maps `n ↦ (n * log n) • v`. In particular, evaluation at two determines the law.
No completeness or finite-dimensionality is required.

The proof separates two mechanisms. Vanishing on powers of two gives a linear bound by
dyadic decomposition. The Leibniz law on powers of any natural number then forces vanishing.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ordinary product rule, without assuming additivity. -/
def IsArithmeticLeibniz (f : ℕ → E) : Prop :=
  ∀ m n, f (m * n) = (m : ℝ) • f n + (n : ℝ) • f m

/-- One constant controls every additive defect by the total input mass. -/
def HasLinearArithmeticAddDefect (f : ℕ → E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ m n,
    ‖f (m + n) - f m - f n‖ ≤ C * ((m + n : ℕ) : ℝ)

theorem IsArithmeticLeibniz.map_zero {f : ℕ → E} (hf : IsArithmeticLeibniz f) :
    f 0 = 0 := by
  simpa using hf 0 0

theorem IsArithmeticLeibniz.map_one {f : ℕ → E} (hf : IsArithmeticLeibniz f) :
    f 1 = 0 := by
  have h : f 1 + 0 = f 1 + f 1 := by simpa using hf 1 1
  exact (add_left_cancel h).symm

theorem IsArithmeticLeibniz.map_two_pow_eq_zero {f : ℕ → E}
    (hf : IsArithmeticLeibniz f) (h2 : f 2 = 0) (k : ℕ) : f (2 ^ k) = 0 := by
  induction k with
  | zero => simpa using hf.map_one
  | succ k ih => rw [pow_succ, hf, h2, ih, smul_zero, smul_zero, add_zero]

omit [NormedSpace ℝ E] in
/-- Dyadic vanishing and the additive defect estimate give a uniform linear bound. -/
theorem norm_le_linear_of_dyadic_zero {f : ℕ → E} {C : ℝ}
    (hC : 0 ≤ C) (h0 : f 0 = 0) (hdyadic : ∀ k, f (2 ^ k) = 0)
    (hdefect : ∀ m n, ‖f (m + n) - f m - f n‖ ≤ C * ((m + n : ℕ) : ℝ)) :
    ∀ n, ‖f n‖ ≤ 2 * C * (n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn, h0]
    let p := 2 ^ Nat.log 2 n
    have hp : p ≤ n := Nat.pow_log_le_self 2 hn
    have hp0 : 0 < p := pow_pos (by norm_num) _
    have hnupper : n < 2 * p := by
      have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
      simpa [p, pow_succ, Nat.mul_comm] using hh
    have hrlt : n - p < n := Nat.sub_lt (Nat.pos_of_ne_zero hn) hp0
    have hsmall := ih (n - p) hrlt
    have hsum : p + (n - p) = n := by omega
    have hhalf : 2 * (n - p) ≤ n := by omega
    have hhalfR : (2 : ℝ) * ((n - p : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hhalf
    have hstep := hdefect p (n - p)
    rw [hsum, hdyadic (Nat.log 2 n), sub_zero] at hstep
    have htriangle : ‖f n‖ ≤ ‖f n - f (n - p)‖ + ‖f (n - p)‖ := by
      simpa using norm_add_le (f n - f (n - p)) (f (n - p))
    have hmass := mul_nonneg hC (sub_nonneg.mpr hhalfR)
    calc
      ‖f n‖ ≤ C * (n : ℝ) + 2 * C * ((n - p : ℕ) : ℝ) :=
        htriangle.trans (add_le_add hstep hsmall)
      _ ≤ 2 * C * (n : ℝ) := by nlinarith

theorem IsArithmeticLeibniz.map_pow_succ {f : ℕ → E}
    (hf : IsArithmeticLeibniz f) (n k : ℕ) :
    f (n ^ (k + 1)) = ((k + 1 : ℕ) : ℝ) • ((n : ℝ) ^ k • f n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      f (n ^ (k + 1 + 1)) = ((n ^ (k + 1) : ℕ) : ℝ) • f n +
          (n : ℝ) • f (n ^ (k + 1)) := by rw [pow_succ, hf]
      _ = ((k + 1 + 1 : ℕ) : ℝ) • ((n : ℝ) ^ (k + 1) • f n) := by
        rw [ih]
        simp only [Nat.cast_add, Nat.cast_one, smul_smul, pow_succ,
          Nat.cast_mul, Nat.cast_pow]
        rw [← add_smul]
        congr 1
        ring

/-- A Leibniz law with a linear growth bound is zero, by testing arbitrary powers. -/
theorem IsArithmeticLeibniz.eq_zero_of_linear_bound {f : ℕ → E}
    (hf : IsArithmeticLeibniz f) {A : ℝ}
    (hbound : ∀ n, ‖f n‖ ≤ A * (n : ℝ)) : f = 0 := by
  funext n
  change f n = 0
  by_cases hn : n = 0
  · simpa [hn] using hf.map_zero
  by_contra hfn
  have hnorm : 0 < ‖f n‖ := norm_pos_iff.mpr hfn
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  obtain ⟨k, hk⟩ := exists_nat_gt (A * (n : ℝ) / ‖f n‖)
  have hkbig : A * (n : ℝ) < (k : ℝ) * ‖f n‖ := by
    have hh := mul_lt_mul_of_pos_right hk hnorm
    simpa [div_mul_cancel₀ _ (ne_of_gt hnorm)] using hh
  have hpow := hbound (n ^ (k + 1))
  rw [hf.map_pow_succ, norm_smul, norm_smul, Real.norm_natCast, norm_pow,
    Real.norm_natCast, Nat.cast_pow] at hpow
  simp only [Nat.cast_add, Nat.cast_one, pow_succ] at hpow
  have hgap : 0 < (n : ℝ) ^ k * (((k : ℝ) + 1) * ‖f n‖ - A * (n : ℝ)) :=
    mul_pos (pow_pos hnR k) (by nlinarith)
  nlinarith

/-- Zero at two forces zero everywhere under one uniform additive defect bound. -/
theorem IsArithmeticLeibniz.eq_zero_of_two_eq_zero {f : ℕ → E}
    (hf : IsArithmeticLeibniz f) (hdefect : HasLinearArithmeticAddDefect f)
    (h2 : f 2 = 0) : f = 0 := by
  obtain ⟨C, hC, hbound⟩ := hdefect
  exact hf.eq_zero_of_linear_bound
    (norm_le_linear_of_dyadic_zero hC hf.map_zero (hf.map_two_pow_eq_zero h2) hbound)

/-- Controlled arithmetic Leibniz laws with the same value at two coincide. -/
theorem arithmeticLeibniz_eq_of_eval_two {f g : ℕ → E}
    (hf : IsArithmeticLeibniz f) (hg : IsArithmeticLeibniz g)
    (hfb : HasLinearArithmeticAddDefect f) (hgb : HasLinearArithmeticAddDefect g)
    (h2 : f 2 = g 2) : f = g := by
  let d : ℕ → E := fun n => f n - g n
  have hd : IsArithmeticLeibniz d := by
    intro m n
    dsimp [d]
    rw [hf m n, hg m n, smul_sub, smul_sub]
    abel
  have hdb : HasLinearArithmeticAddDefect d := by
    obtain ⟨Cf, hCf, hfb⟩ := hfb
    obtain ⟨Cg, hCg, hgb⟩ := hgb
    refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
    intro m n
    have hsplit : d (m + n) - d m - d n =
        (f (m + n) - f m - f n) - (g (m + n) - g m - g n) := by
      dsimp [d]
      abel
    rw [hsplit]
    calc
      _ ≤ ‖f (m + n) - f m - f n‖ + ‖g (m + n) - g m - g n‖ := norm_sub_le _ _
      _ ≤ Cf * ((m + n : ℕ) : ℝ) + Cg * ((m + n : ℕ) : ℝ) :=
        add_le_add (hfb m n) (hgb m n)
      _ = (Cf + Cg) * ((m + n : ℕ) : ℝ) := by ring
  have hz : d = 0 := hd.eq_zero_of_two_eq_zero hdb (by simp [d, h2])
  funext n
  have hh := congrFun hz n
  exact sub_eq_zero.mp hh

/-- All controlled laws, including laws valued in infinite-dimensional normed spaces. -/
def ControlledArithmeticLeibnizMaps (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {f : ℕ → E // IsArithmeticLeibniz f ∧ HasLinearArithmeticAddDefect f}

/-- Evaluation at the literal integer two determines a controlled arithmetic law. -/
theorem controlledArithmeticLeibniz_eval_two_injective :
    Function.Injective (fun f : ControlledArithmeticLeibnizMaps E => f.1 2) := by
  intro f g h
  apply Subtype.ext
  exact arithmeticLeibniz_eq_of_eval_two f.2.1 g.2.1 f.2.2 g.2.2 h

/-- The logarithmic law with values in any real normed vector space. -/
noncomputable def arithmeticLogModel (v : E) (n : ℕ) : E :=
  ((n : ℝ) * Real.log (n : ℝ)) • v

theorem arithmeticLogModel_isArithmeticLeibniz (v : E) :
    IsArithmeticLeibniz (arithmeticLogModel v) := by
  intro m n
  rcases eq_or_ne m 0 with rfl | hm
  · simp [arithmeticLogModel]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [arithmeticLogModel]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [arithmeticLogModel, Nat.cast_mul, Real.log_mul hmR hnR,
    smul_smul, ← add_smul]
  congr 1
  ring

/-- The binary logarithmic defect is nonnegative and at most the total mass. -/
theorem arithmeticLogDefect_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ (x + y) * Real.log (x + y) - x * Real.log x - y * Real.log y ∧
    (x + y) * Real.log (x + y) - x * Real.log x - y * Real.log y ≤ x + y := by
  rcases eq_or_lt_of_le hx with hx0 | hx
  · simp [← hx0, hy]
  rcases eq_or_lt_of_le hy with hy0 | hy
  · simp [← hy0, le_of_lt hx]
  have hs : 0 < x + y := add_pos hx hy
  have hxl := Real.log_le_log hx (le_add_of_nonneg_right hy.le)
  have hyl := Real.log_le_log hy (le_add_of_nonneg_left hx.le)
  have hxp := mul_nonneg hx.le (sub_nonneg.mpr hxl)
  have hyp := mul_nonneg hy.le (sub_nonneg.mpr hyl)
  have hxu : x * (Real.log (x + y) - Real.log x) ≤ y := by
    calc
      _ = x * Real.log ((x + y) / x) := by rw [Real.log_div hs.ne' hx.ne']
      _ ≤ x * ((x + y) / x - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hs hx)) hx.le
      _ = y := by field_simp; ring
  have hyu : y * (Real.log (x + y) - Real.log y) ≤ x := by
    calc
      _ = y * Real.log ((x + y) / y) := by rw [Real.log_div hs.ne' hy.ne']
      _ ≤ y * ((x + y) / y - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hs hy)) hy.le
      _ = x := by field_simp; ring
  constructor <;> nlinarith

theorem arithmeticLogModel_hasLinearArithmeticAddDefect (v : E) :
    HasLinearArithmeticAddDefect (arithmeticLogModel v) := by
  refine ⟨‖v‖, norm_nonneg v, ?_⟩
  intro m n
  obtain ⟨hl, hu⟩ := arithmeticLogDefect_bounds (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  simp only [arithmeticLogModel, Nat.cast_add, ← sub_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hl]
  calc
    _ ≤ ((m : ℝ) + n) * ‖v‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg v)
    _ = ‖v‖ * ((m : ℝ) + n) := mul_comm _ _

/-- The unique calibration of a controlled law is its value at two divided by `2 log 2`. -/
theorem arithmeticLeibniz_eq_logModel {f : ℕ → E}
    (hf : IsArithmeticLeibniz f) (hb : HasLinearArithmeticAddDefect f) :
    f = arithmeticLogModel ((2 * Real.log 2)⁻¹ • f 2) := by
  apply arithmeticLeibniz_eq_of_eval_two hf (arithmeticLogModel_isArithmeticLeibniz _)
    hb (arithmeticLogModel_hasLinearArithmeticAddDefect _)
  have hlog : 2 * Real.log 2 ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  change f 2 = (2 * Real.log 2) • ((2 * Real.log 2)⁻¹ • f 2)
  rw [smul_smul, mul_inv_cancel₀ hlog, one_smul]

/-- Exact classification; the two arithmetic laws are equivalent to one vector parameter. -/
theorem controlledArithmeticLeibniz_iff_logModel (f : ℕ → E) :
    (IsArithmeticLeibniz f ∧ HasLinearArithmeticAddDefect f) ↔
      ∃ v : E, f = arithmeticLogModel v := by
  constructor
  · rintro ⟨hf, hb⟩
    exact ⟨_, arithmeticLeibniz_eq_logModel hf hb⟩
  · rintro ⟨v, rfl⟩
    exact ⟨arithmeticLogModel_isArithmeticLeibniz v,
      arithmeticLogModel_hasLinearArithmeticAddDefect v⟩

end GaloisForLFunctions.HTGeometry
