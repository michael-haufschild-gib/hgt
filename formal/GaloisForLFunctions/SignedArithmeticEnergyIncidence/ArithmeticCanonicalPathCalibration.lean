import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheOddWeilLedgerIsFrustratedOnlyByPrimes
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.FrustrationIsPaidAlongCanonicalPaths
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TriangleHolonomyDecidesLocalPayment

/-!
# Canonical-path payment and source-faithful full-form calibration for arithmetic coefficients

`FrustrationIsPaidAlongCanonicalPaths` introduces `PathCertificate`: a positive supersolution gauge
`v > 0` (`(Cv)_i ≥ 0`), canonical paths through aligned overlaps (`c_xy < 0`) for every
anti-aligned overlap (`c_ab > 0`), and packed edge shares `λ_ab(x, y) > 0` (`Σ λ ≤ 1`) satisfying
the inverse-share Cauchy–Schwarz budget. Meanwhile, `TheOddWeilLedgerIsFrustratedOnlyByPrimes`
only established frustration of the prime triangle at artificially small archimedean–polar weights
`|α| < α₀` around `α = 0`, where `primeKernel` alone makes all three overlaps positive (`c > 0`).

This module resolves the source-faithful full-form calibration `α = 1, β = 1`
(`weilLedgerKernel 1 1`) and constructs explicit canonical-path certificates and packed paths for
actual arithmetic coefficients:

1. **Pairwise completeness is false on actual arithmetic prime-kernel samplings, and pure
   prime-kernel frustration admits no canonical-path certificate.**
   * On the integer-logarithm grid `arithLogGrid = ![log 2, log 3, log 5]`, the folded prime
     overlap at `(0, 1)` vanishes (`log 2 + log 3 = log 6` has `Λ(6) = 0` and `|log 2 − log 3| =
     log(3/2)` is not an integer logarithm), refuting `IsCompleteOverlap`
     (`not_isCompleteOverlap_oddFold_arithLogGrid`).
   * On `primeTrianglePos` under `primeKernel` alone (`α = 0`), every off-diagonal overlap is
     strictly positive, so no aligned step exists and `IsEmpty (PathCertificate ...)` holds for
     every budget (`isEmpty_pathCertificate_primeTriangle_primeKernel`).

2. **Closed-form rational-logarithm law and unconditional frustration at the source-faithful
   calibration `α = 1, β = 1`.**
   * For every `x > 1`, `weilKernel (log x) = −2(x³ − x − 1) / ((x² − 1) √x)`
     (`weilKernel_log_eq`).
   * At the source-faithful calibration `weilLedgerKernel 1 1` on `primeTrianglePos`:
     - edge `(0, 1)` (sum `log 2`, difference `log(5/3)`) is aligned: `−2/5 < c 0 1 < −1/7 < 0`;
     - edge `(2, 0)` (sum `log 5`, difference `log(3/2)`) is aligned: `−15/4 < c 2 0 < −1 < 0`;
     - edge `(1, 2)` (sum `log 3`, difference `log(5/2)`) remains anti-aligned:
       `3/20 < c 1 2 < 2/5`.
   * Because two edges flip sign to aligned (`< 0`) while `(1, 2)` stays anti-aligned (`> 0`), the
     triangle holonomy is `(+1)` (`triangleHolonomy > 0`) and `oddFold primeTrianglePos
     (weilLedgerKernel 1 1) b` is **unconditionally frustrated (`¬ IsBalanced`) for every budget
     `b`** (`oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced`).

3. **Positive supersolution and canonical-path payment on the source-faithful prime triangle.**
   * The two aligned prime-sum edges `(1, 0)` and `(0, 2)` form the canonical path `1 → 0 → 2`
     paying the anti-aligned prime-sum edge `(1, 2)` in gauge `v = ![4, 1, 1]`
     (`primeTrianglePathCertificate`), certifying `0 ≤ incidenceEnergy` for every budget `b` making
     `v` a supersolution (`incidenceEnergy_oddFold_primeTriangle_weilLedgerKernel_one_nonneg`,
     `supersolution_primeTriangleGauge_of_le`).

4. **Packed canonical paths and overlapping-budget retention on `Fin 4`.**
   * Extending `primeTrianglePos` by `p_3 = (3 log 5 − log 2 − log 3)/2` (`packedPrimePos :
     Fin 4 → ℝ`) produces a second anti-aligned prime-sum edge `(1, 3)` (`p_1 + p_3 = log 5`,
     `1/4 < c 1 3 < 13/30`) alongside `(1, 2)` (`p_1 + p_2 = log 3`), while all four remaining
     edges `{0, 1}, {0, 2}, {0, 3}, {2, 3}` are aligned (`< 0`).
   * Routing `(1, 2)` along `1 → 0 → 2` and `(1, 3)` along `1 → 0 → 3` packs both canonical paths
     through the shared aligned hub edge `(1, 0)` with equal shares `λ = 1/2` (`1/2 + 1/2 = 1`) in
     gauge `v = ![8, 1, 1, 1]` (`packedPrimePathCertificate`,
     `incidenceEnergy_oddFold_packedPrime_weilLedgerKernel_one_nonneg`).
   * Whenever multiple canonical paths share a first step `(a, u)`, packing their shares forces
     `|c a u| v_u ≥ Σ_{b ∈ S} c a b v_b` (`packed_shared_step_gauge_lower_bound`): finite
     canonical-path payment retains overlapping budgets across every frustrated cycle routed through
     the shared edge.
-/

open Finset ArithmeticFunction

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Part 1: Pairwise completeness is false and pure prime-kernel frustration has no path -/

/-- The diagonal entry of `oddFold p w b` at `i` is `b i + w (2 * p i)`. -/
theorem oddFold_diag {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (w : ℝ → ℝ) (b : ι → ℝ) (i : ι) :
    oddFold p w b i i = b i + w (2 * p i) := by
  unfold oddFold mirrorCoupling
  rw [if_pos rfl, if_neg (fun h => Bool.noConfusion (Prod.ext_iff.1 h).1)]
  simp only [sideSign_true, sideSign_false]
  rw [show 1 * p i - -1 * p i = 2 * p i by ring]
  ring

@[simp] theorem walkVertex_zero {ι : Type*} (u : ι) (l : List ι) : walkVertex u l 0 = u := by
  cases l <;> rfl

/-- The integer-logarithm sample grid `![log 2, log 3, log 5]`. -/
def arithLogGrid : Fin 3 → ℝ := ![Real.log 2, Real.log 3, Real.log 5]

/-- At `log 6`, `primeKernel` vanishes because `6` is not a prime power (`Λ(6) = 0`). -/
theorem primeKernel_log_six : primeKernel (Real.log 6) = 0 := by
  have h60 : (0 : ℝ) < (6 : ℕ) := by norm_num
  have hlog : 0 ≤ Real.log (6 : ℕ) := Real.log_nonneg (by norm_num)
  have hnp : ¬ IsPrimePow 6 := by decide
  have hΛ : Λ 6 = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp
  have heq : Real.log (6 : ℝ) = Real.log (6 : ℕ) := by norm_num
  rw [heq]
  unfold primeKernel
  rw [abs_of_nonneg hlog, Real.exp_log h60,
    tsum_eq_single 6 fun n hn => if_neg fun h => hn (by exact_mod_cast h.symm),
    if_pos rfl, hΛ, zero_div]

/-- On `arithLogGrid = ![log 2, log 3, log 5]`, the folded prime overlap between `log 2` and
`log 3` vanishes identically because neither `2 · 3 = 6` nor `3 / 2` is a prime power. -/
theorem oddFold_arithLogGrid_primeKernel_zero_one (b : Fin 3 → ℝ) :
    oddFold arithLogGrid primeKernel b 0 1 = 0 := by
  rw [oddFold_offDiag (by decide : (0 : Fin 3) ≠ 1)]
  simp only [arithLogGrid, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsum : Real.log 2 + Real.log 3 = Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hdiff : primeKernel (Real.log 2 - Real.log 3) = 0 := by
    rw [show Real.log 2 - Real.log 3 = -(Real.log 3 - Real.log 2) by ring, primeKernel_neg]
    exact primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
      (by norm_num) (by norm_num)
  rw [hsum, primeKernel_log_six, hdiff, sub_zero]

/-- **Pairwise completeness is false on actual arithmetic prime-kernel samplings.** On
`arithLogGrid = ![log 2, log 3, log 5]`, `oddFold arithLogGrid primeKernel b` violates
`IsCompleteOverlap` for every budget `b`. -/
theorem not_isCompleteOverlap_oddFold_arithLogGrid (b : Fin 3 → ℝ) :
    ¬ IsCompleteOverlap (oddFold arithLogGrid primeKernel b) := fun h =>
  h 0 1 (by decide) (oddFold_arithLogGrid_primeKernel_zero_one b)

/-- Every walk between distinct endpoints contains at least one step between distinct vertices. -/
theorem exists_step_ne_of_walkEnd_ne {ι : Type*} {a b : ι} {l : List ι}
    (hab : a ≠ b) (hend : walkEnd a l = b) :
    ∃ s < l.length, walkVertex a l s ≠ walkVertex a l (s + 1) := by
  by_contra hno
  push Not at hno
  have hconst : ∀ k ≤ l.length, walkVertex a l k = a := by
    intro k hk
    induction k with
    | zero => exact walkVertex_zero a l
    | succ k ih =>
      rw [← hno k (Nat.lt_of_succ_le hk), ih (Nat.le_of_succ_le hk)]
  have hlast := hconst l.length le_rfl
  rw [walkVertex_length, hend] at hlast
  exact hab hlast.symm

/-- A coupling whose off-diagonal entries are all nonnegative and which has at least one strictly
positive off-diagonal entry admits no `PathCertificate`, because no aligned off-diagonal step
(`c x y < 0`) exists to route the anti-aligned overlap. -/
theorem isEmpty_pathCertificate_of_nonneg_offDiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ι → ι → ℝ} (hnn : ∀ x y, x ≠ y → 0 ≤ c x y)
    (hpos : ∃ a b, a ≠ b ∧ 0 < c a b) : IsEmpty (PathCertificate c) := by
  refine ⟨fun P => ?_⟩
  obtain ⟨a, b, hab, hcab⟩ := hpos
  obtain ⟨s, hs, hne⟩ := exists_step_ne_of_walkEnd_ne hab (P.path_end a b hab hcab)
  exact not_lt_of_ge (hnn _ _ hne) (P.path_aligned a b hab hcab s hs)

/-- **Pure prime-kernel frustration admits no canonical-path certificate.** On `primeTrianglePos`
with `primeKernel` alone (`α = 0`), all three off-diagonal overlaps are strictly positive, so
`PathCertificate` is empty for every budget `b`. -/
theorem isEmpty_pathCertificate_primeTriangle_primeKernel (b : Fin 3 → ℝ) :
    IsEmpty (PathCertificate (oddFold primeTrianglePos primeKernel b)) :=
  isEmpty_pathCertificate_of_nonneg_offDiag
    (fun x y hxy => (oddFold_primeTriangle_pos b x y hxy).le)
    ⟨0, 1, by decide, oddFold_primeTriangle_pos b 0 1 (by decide)⟩


/-! ### Part 2: Closed-form evaluation of `weilKernel` at rational logarithms -/

/-- **Closed-form rational-logarithm law for the archimedean–polar Weil kernel.** At `u = log x`
for any `x > 1`, `weilKernel (log x) = −2(x³ − x − 1) / ((x² − 1) √x)`. -/
theorem weilKernel_log_eq {x : ℝ} (hx : 1 < x) :
    RHTower.ArchimedeanKernel.weilKernel (Real.log x) =
      -2 * (x ^ 3 - x - 1) / ((x ^ 2 - 1) * Real.sqrt x) := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hexp_half : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]; ring_nf
  have hexp_neg_half : Real.exp (-Real.log x / 2) = (Real.sqrt x)⁻¹ := by
    rw [show -Real.log x / 2 = -(Real.log x / 2) by ring, Real.exp_neg, hexp_half]
  have hexp_neg_two : Real.exp (-2 * Real.log x) = (x ^ 2)⁻¹ := by
    rw [show -2 * Real.log x = -(Real.log x + Real.log x) by ring, Real.exp_neg,
      Real.exp_add, Real.exp_log hx0, sq]
  have hcosh : Real.cosh (Real.log x / 2) = (Real.sqrt x + (Real.sqrt x)⁻¹) / 2 := by
    rw [Real.cosh_eq, hexp_half, show -(Real.log x / 2) = -Real.log x / 2 by ring, hexp_neg_half]
  have hsum : Real.sqrt x + (Real.sqrt x)⁻¹ = (x + 1) / Real.sqrt x := by
    have hsne : Real.sqrt x ≠ 0 := hs0.ne'
    calc Real.sqrt x + (Real.sqrt x)⁻¹
        = (Real.sqrt x * Real.sqrt x + 1) / Real.sqrt x := by field_simp
      _ = (x + 1) / Real.sqrt x := by rw [hsq]
  have hden : 1 - (x ^ 2)⁻¹ = (x ^ 2 - 1) / x ^ 2 := by
    have hxne : x ≠ 0 := hx0.ne'
    field_simp
  have hx2 : x ^ 2 - 1 ≠ 0 := by nlinarith
  have hxne : x ≠ 0 := hx0.ne'
  have hsne : Real.sqrt x ≠ 0 := hs0.ne'
  unfold RHTower.ArchimedeanKernel.weilKernel
  rw [hexp_neg_half, hexp_neg_two, hcosh, hsum, hden]
  field_simp
  ring

/-- For `0 < b < a`, `|log a − log b| = log(a / b)`. -/
theorem abs_log_sub_eq_log_div {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    |Real.log a - Real.log b| = Real.log (a / b) := by
  have ha : 0 < a := lt_trans hb hab
  have hpos : 0 < Real.log a - Real.log b := sub_pos.mpr (Real.log_lt_log hb hab)
  rw [abs_of_pos hpos, Real.log_div ha.ne' hb.ne']

/-- Rational upper bound on `c / √d` from `c² < B² d`. -/
theorem div_sqrt_lt_of_sq_lt {c d B : ℝ} (hd : 0 < d) (hB : 0 ≤ B) (h : c ^ 2 < B ^ 2 * d) :
    c / Real.sqrt d < B := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  rw [div_lt_iff₀ hsd]
  by_contra hle
  push Not at hle
  have hsq : (B * Real.sqrt d) ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hB hsd.le) hle 2
  rw [mul_pow, Real.sq_sqrt hd.le] at hsq
  linarith

/-- Rational lower bound on `c / √d` from `B² d < c²`. -/
theorem lt_div_sqrt_of_sq_gt {c d B : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (h : B ^ 2 * d < c ^ 2) :
    B < c / Real.sqrt d := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  rw [lt_div_iff₀ hsd]
  by_contra hle
  push Not at hle
  have hsq : c ^ 2 ≤ (B * Real.sqrt d) ^ 2 :=
    pow_le_pow_left₀ hc hle 2
  rw [mul_pow, Real.sq_sqrt hd.le] at hsq
  linarith

/-- Concrete rational bounds on `log 2`, `log 3`, and `log 5` from `log_two_gt_d9`,
`log_two_lt_d9`, and `log_le_sub_one_of_pos`. -/
theorem log_two_bounds : (69 / 100 : ℝ) < Real.log 2 ∧ Real.log 2 < 7 / 10 :=
  ⟨by linarith [Real.log_two_gt_d9], by linarith [Real.log_two_lt_d9]⟩

theorem log_three_bounds : (21 / 20 : ℝ) < Real.log 3 ∧ Real.log 3 < 6 / 5 := by
  have h43 : Real.log (4 / 3 : ℝ) ≤ 4 / 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h32 : Real.log (3 / 2 : ℝ) ≤ 3 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have heq1 : Real.log 3 + Real.log (4 / 3 : ℝ) = 2 * Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show (3 : ℝ) * (4 / 3) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
  have heq2 : Real.log 3 = Real.log 2 + Real.log (3 / 2 : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  constructor
  · linarith [Real.log_two_gt_d9, h43, heq1]
  · linarith [Real.log_two_lt_d9, h32, heq2]

theorem log_five_bounds : (79 / 50 : ℝ) < Real.log 5 ∧ Real.log 5 < 33 / 20 := by
  have h45 : Real.log (4 / 5 : ℝ) ≤ 4 / 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h54 : Real.log (5 / 4 : ℝ) ≤ 5 / 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have heq1 : Real.log 5 + Real.log (4 / 5 : ℝ) = 2 * Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show (5 : ℝ) * (4 / 5) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
  have heq2 : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
    have : 2 * Real.log 2 = Real.log 4 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
    rw [this, ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  constructor
  · linarith [Real.log_two_gt_d9, h45, heq1]
  · linarith [Real.log_two_lt_d9, h54, heq2]

/-! ### Rational bounds on the kernel values entering the `Fin 3` and `Fin 4` calibrations -/

theorem neg_weilKernel_log_five_thirds_bounds :
    (8 / 5 : ℝ) < -RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 3)) ∧
      -RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 3)) < 12 / 7 := by
  rw [weilKernel_log_eq (by norm_num : (1 : ℝ) < 5 / 3)]
  have heq : -(-2 * ((5 / 3 : ℝ) ^ 3 - 5 / 3 - 1) / (((5 / 3 : ℝ) ^ 2 - 1) * Real.sqrt (5 / 3))) =
      (53 / 24 : ℝ) / Real.sqrt (5 / 3) := by ring
  rw [heq]
  exact ⟨lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num),
    div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)⟩

theorem neg_weilKernel_log_three_halves_lt :
    -RHTower.ArchimedeanKernel.weilKernel (Real.log (3 / 2)) < 3 / 2 := by
  rw [weilKernel_log_eq (by norm_num : (1 : ℝ) < 3 / 2)]
  have heq : -(-2 * ((3 / 2 : ℝ) ^ 3 - 3 / 2 - 1) / (((3 / 2 : ℝ) ^ 2 - 1) * Real.sqrt (3 / 2))) =
      (7 / 5 : ℝ) / Real.sqrt (3 / 2) := by ring
  rw [heq]
  exact div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)

theorem neg_weilKernel_log_five_halves_bounds :
    (29 / 10 : ℝ) < -RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 2)) ∧
      -RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 2)) < 3 := by
  rw [weilKernel_log_eq (by norm_num : (1 : ℝ) < 5 / 2)]
  have heq : -(-2 * ((5 / 2 : ℝ) ^ 3 - 5 / 2 - 1) / (((5 / 2 : ℝ) ^ 2 - 1) * Real.sqrt (5 / 2))) =
      (97 / 21 : ℝ) / Real.sqrt (5 / 2) := by ring
  rw [heq]
  exact ⟨lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num),
    div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)⟩

theorem neg_weilKernel_log_twenty_five_sixths_bounds :
    (4 : ℝ) < -RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 6)) ∧
      -RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 6)) < 41 / 10 := by
  rw [weilKernel_log_eq (by norm_num : (1 : ℝ) < 25 / 6)]
  have heq : -(-2 * ((25 / 6 : ℝ) ^ 3 - 25 / 6 - 1) /
      (((25 / 6 : ℝ) ^ 2 - 1) * Real.sqrt (25 / 6))) =
      (14509 / 1767 : ℝ) / Real.sqrt (25 / 6) := by ring
  rw [heq]
  exact ⟨lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num),
    div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)⟩

theorem neg_weilKernel_log_twenty_five_thirds_bounds :
    (5 : ℝ) < -RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 3)) ∧
      -RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 3)) < 6 := by
  rw [weilKernel_log_eq (by norm_num : (1 : ℝ) < 25 / 3)]
  have heq : -(-2 * ((25 / 3 : ℝ) ^ 3 - 25 / 3 - 1) /
      (((25 / 3 : ℝ) ^ 2 - 1) * Real.sqrt (25 / 3))) =
      (15373 / 924 : ℝ) / Real.sqrt (25 / 3) := by ring
  rw [heq]
  exact ⟨lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num),
    div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)⟩

theorem neg_weilKernel_log_twenty_five_halves_bounds :
    (6 : ℝ) < -RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 2)) ∧
      -RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 2)) < 8 := by
  rw [weilKernel_log_eq (by norm_num : (1 : ℝ) < 25 / 2)]
  have heq : -(-2 * ((25 / 2 : ℝ) ^ 3 - 25 / 2 - 1) /
      (((25 / 2 : ℝ) ^ 2 - 1) * Real.sqrt (25 / 2))) =
      (15517 / 621 : ℝ) / Real.sqrt (25 / 2) := by ring
  rw [heq]
  exact ⟨lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num),
    div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)⟩

theorem weilLedgerKernel_one_log_two_bounds :
    (-2 : ℝ) < weilLedgerKernel 1 1 (Real.log 2) ∧
      weilLedgerKernel 1 1 (Real.log 2) < -13 / 7 := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk2 := primeKernel_log_prime Nat.prime_two
  push_cast at hk2
  unfold weilLedgerKernel
  rw [abs_of_nonneg hlog0, weilKernel_log_eq (by norm_num : (1 : ℝ) < 2), hk2]
  have heq : 1 * (-2 * ((2 : ℝ) ^ 3 - 2 - 1) / ((2 ^ 2 - 1) * Real.sqrt 2)) +
      1 * (Real.log 2 / Real.sqrt 2) = -((10 / 3 - Real.log 2) / Real.sqrt 2) := by ring
  rw [heq]
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (10 / 3 - Real.log 2) / Real.sqrt 2 < 2 := by
    calc (10 / 3 - Real.log 2) / Real.sqrt 2
        < (10 / 3 - 69 / 100) / Real.sqrt 2 :=
          div_lt_div_of_pos_right (by linarith [log_two_bounds.1]) hs2
      _ = (793 / 300 : ℝ) / Real.sqrt 2 := by ring
      _ < 2 := div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)
  have h2 : (13 / 7 : ℝ) < (10 / 3 - Real.log 2) / Real.sqrt 2 := by
    calc (13 / 7 : ℝ)
        < (79 / 30 : ℝ) / Real.sqrt 2 :=
          lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num)
      _ = (10 / 3 - 7 / 10) / Real.sqrt 2 := by ring
      _ < (10 / 3 - Real.log 2) / Real.sqrt 2 :=
          div_lt_div_of_pos_right (by linarith [log_two_bounds.2]) hs2
  exact ⟨by linarith, by linarith⟩

theorem weilLedgerKernel_one_log_three_bounds :
    (-11 / 4 : ℝ) < weilLedgerKernel 1 1 (Real.log 3) ∧
      weilLedgerKernel 1 1 (Real.log 3) < -13 / 5 := by
  have hlog0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hk3 := primeKernel_log_prime Nat.prime_three
  push_cast at hk3
  unfold weilLedgerKernel
  rw [abs_of_nonneg hlog0, weilKernel_log_eq (by norm_num : (1 : ℝ) < 3), hk3]
  have heq : 1 * (-2 * ((3 : ℝ) ^ 3 - 3 - 1) / ((3 ^ 2 - 1) * Real.sqrt 3)) +
      1 * (Real.log 3 / Real.sqrt 3) = -((23 / 4 - Real.log 3) / Real.sqrt 3) := by ring
  rw [heq]
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (23 / 4 - Real.log 3) / Real.sqrt 3 < 11 / 4 := by
    calc (23 / 4 - Real.log 3) / Real.sqrt 3
        < (23 / 4 - 21 / 20) / Real.sqrt 3 :=
          div_lt_div_of_pos_right (by linarith [log_three_bounds.1]) hs3
      _ = (47 / 10 : ℝ) / Real.sqrt 3 := by ring
      _ < 11 / 4 := div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)
  have h2 : (13 / 5 : ℝ) < (23 / 4 - Real.log 3) / Real.sqrt 3 := by
    calc (13 / 5 : ℝ)
        < (91 / 20 : ℝ) / Real.sqrt 3 :=
          lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num)
      _ = (23 / 4 - 6 / 5) / Real.sqrt 3 := by ring
      _ < (23 / 4 - Real.log 3) / Real.sqrt 3 :=
          div_lt_div_of_pos_right (by linarith [log_three_bounds.2]) hs3
  exact ⟨by linarith, by linarith⟩

theorem weilLedgerKernel_one_log_five_bounds :
    (-15 / 4 : ℝ) < weilLedgerKernel 1 1 (Real.log 5) ∧
      weilLedgerKernel 1 1 (Real.log 5) < -11 / 3 := by
  have hlog0 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hk5 := primeKernel_log_prime Nat.prime_five
  push_cast at hk5
  unfold weilLedgerKernel
  rw [abs_of_nonneg hlog0, weilKernel_log_eq (by norm_num : (1 : ℝ) < 5), hk5]
  have heq : 1 * (-2 * ((5 : ℝ) ^ 3 - 5 - 1) / ((5 ^ 2 - 1) * Real.sqrt 5)) +
      1 * (Real.log 5 / Real.sqrt 5) = -((119 / 12 - Real.log 5) / Real.sqrt 5) := by ring
  rw [heq]
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (119 / 12 - Real.log 5) / Real.sqrt 5 < 15 / 4 := by
    calc (119 / 12 - Real.log 5) / Real.sqrt 5
        < (119 / 12 - 79 / 50) / Real.sqrt 5 :=
          div_lt_div_of_pos_right (by linarith [log_five_bounds.1]) hs5
      _ = (2501 / 300 : ℝ) / Real.sqrt 5 := by ring
      _ < 15 / 4 := div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)
  have h2 : (11 / 3 : ℝ) < (119 / 12 - Real.log 5) / Real.sqrt 5 := by
    calc (11 / 3 : ℝ)
        < (124 / 15 : ℝ) / Real.sqrt 5 :=
          lt_div_sqrt_of_sq_gt (by norm_num) (by norm_num) (by norm_num)
      _ = (119 / 12 - 33 / 20) / Real.sqrt 5 := by ring
      _ < (119 / 12 - Real.log 5) / Real.sqrt 5 :=
          div_lt_div_of_pos_right (by linarith [log_five_bounds.2]) hs5
  exact ⟨by linarith, by linarith⟩


/-! ### Part 3: Unconditional frustration and canonical-path payment on `primeTrianglePos` -/

/-- On `primeTrianglePos` at the source-faithful calibration `weilLedgerKernel 1 1`, the `(0, 1)`
overlap (sum `log 2`, difference `log(5/3)`) is aligned and bounded between `−2/5` and `−1/7`. -/
theorem oddFold_primeTriangle_weilLedgerKernel_one_zero_one (b : Fin 3 → ℝ) :
    (-2 / 5 : ℝ) < oddFold primeTrianglePos (weilLedgerKernel 1 1) b 0 1 ∧
      oddFold primeTrianglePos (weilLedgerKernel 1 1) b 0 1 < -1 / 7 := by
  rw [oddFold_offDiag (by decide : (0 : Fin 3) ≠ 1)]
  simp only [primeTrianglePos, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsum : (Real.log 2 + Real.log 5 - Real.log 3) / 2 +
      (Real.log 2 + Real.log 3 - Real.log 5) / 2 = Real.log 2 := by ring
  have hdiff : (Real.log 2 + Real.log 5 - Real.log 3) / 2 -
      (Real.log 2 + Real.log 3 - Real.log 5) / 2 = Real.log 5 - Real.log 3 := by ring
  have hdiv : weilLedgerKernel 1 1 (Real.log 5 - Real.log 3) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 3)) := by
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
        (by norm_num) (by norm_num)]
    ring
  rw [hsum, hdiff, hdiv]
  exact ⟨by linarith [weilLedgerKernel_one_log_two_bounds.1,
      neg_weilKernel_log_five_thirds_bounds.1],
    by linarith [weilLedgerKernel_one_log_two_bounds.2,
      neg_weilKernel_log_five_thirds_bounds.2]⟩

/-- On `primeTrianglePos` at the source-faithful calibration `weilLedgerKernel 1 1`, the `(2, 0)`
overlap (sum `log 5`, difference `log(3/2)`) is aligned and bounded between `−15/4` and `−1`. -/
theorem oddFold_primeTriangle_weilLedgerKernel_one_two_zero (b : Fin 3 → ℝ) :
    (-15 / 4 : ℝ) < oddFold primeTrianglePos (weilLedgerKernel 1 1) b 2 0 ∧
      oddFold primeTrianglePos (weilLedgerKernel 1 1) b 2 0 < -1 := by
  rw [oddFold_offDiag (by decide : (2 : Fin 3) ≠ 0)]
  simp only [primeTrianglePos, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hsum : (Real.log 3 + Real.log 5 - Real.log 2) / 2 +
      (Real.log 2 + Real.log 5 - Real.log 3) / 2 = Real.log 5 := by ring
  have hdiff : (Real.log 3 + Real.log 5 - Real.log 2) / 2 -
      (Real.log 2 + Real.log 5 - Real.log 3) / 2 = Real.log 3 - Real.log 2 := by ring
  have hdiv : weilLedgerKernel 1 1 (Real.log 3 - Real.log 2) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (3 / 2)) := by
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
        (by norm_num) (by norm_num)]
    ring
  have hpos32 : 0 < -RHTower.ArchimedeanKernel.weilKernel (Real.log (3 / 2)) := by
    rw [weilKernel_log_eq (by norm_num : (1 : ℝ) < 3 / 2)]
    have heq : -(-2 * ((3 / 2 : ℝ) ^ 3 - 3 / 2 - 1) / (((3 / 2 : ℝ) ^ 2 - 1) * Real.sqrt (3 / 2))) =
        (7 / 5 : ℝ) / Real.sqrt (3 / 2) := by ring
    rw [heq]
    positivity
  rw [hsum, hdiff, hdiv]
  exact ⟨by linarith [weilLedgerKernel_one_log_five_bounds.1, hpos32],
    by linarith [weilLedgerKernel_one_log_five_bounds.2, neg_weilKernel_log_three_halves_lt]⟩

/-- On `primeTrianglePos` at the source-faithful calibration `weilLedgerKernel 1 1`, the `(1, 2)`
overlap (sum `log 3`, difference `log(5/2)`) is anti-aligned and satisfies
`3/20 < c 1 2 < 2/5`. -/
theorem oddFold_primeTriangle_weilLedgerKernel_one_one_two (b : Fin 3 → ℝ) :
    (3 / 20 : ℝ) < oddFold primeTrianglePos (weilLedgerKernel 1 1) b 1 2 ∧
      oddFold primeTrianglePos (weilLedgerKernel 1 1) b 1 2 < 2 / 5 := by
  rw [oddFold_offDiag (by decide : (1 : Fin 3) ≠ 2)]
  simp only [primeTrianglePos, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  have hsum : (Real.log 2 + Real.log 3 - Real.log 5) / 2 +
      (Real.log 3 + Real.log 5 - Real.log 2) / 2 = Real.log 3 := by ring
  have hdiff : (Real.log 2 + Real.log 3 - Real.log 5) / 2 -
      (Real.log 3 + Real.log 5 - Real.log 2) / 2 = -(Real.log 5 - Real.log 2) := by ring
  have hdiv : weilLedgerKernel 1 1 (-(Real.log 5 - Real.log 2)) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 2)) := by
    rw [weilLedgerKernel_neg]
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 2)
        (by norm_num) (by norm_num)]
    ring
  rw [hsum, hdiff, hdiv]
  exact ⟨by linarith [weilLedgerKernel_one_log_three_bounds.1,
      neg_weilKernel_log_five_halves_bounds.1],
    by linarith [weilLedgerKernel_one_log_three_bounds.2,
      neg_weilKernel_log_five_halves_bounds.2]⟩

/-- At the source-faithful calibration `weilLedgerKernel 1 1`, every off-diagonal overlap of
`primeTrianglePos` is nonzero, and the triangle holonomy is strictly positive (`(−)(+)(−) > 0`). -/
theorem triangleHolonomy_primeTriangle_weilLedgerKernel_one_pos (b : Fin 3 → ℝ) :
    0 < triangleHolonomy (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) 0 1 2 := by
  unfold triangleHolonomy
  have h01 := (oddFold_primeTriangle_weilLedgerKernel_one_zero_one b).2
  have h12 := (oddFold_primeTriangle_weilLedgerKernel_one_one_two b).1
  have h20 := (oddFold_primeTriangle_weilLedgerKernel_one_two_zero b).2
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)

/-- **Unconditional frustration of the prime triangle at the source-faithful full-form calibration
`α = 1, β = 1`.** Unlike `exists_weight_oddWeilLedger_primeTriangle_not_isBalanced` (which required
`α → 0` so that all three edges stayed positive), at `α = 1, β = 1` the two prime-sum edges `(0, 1)`
and `(2, 0)` flip to aligned (`< 0`) while `(1, 2)` remains anti-aligned (`> 0`), so the triangle
holonomy is `(+1)` and `oddFold primeTrianglePos (weilLedgerKernel 1 1) b` is unbalanced for every
budget `b`. -/
theorem oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced (b : Fin 3 → ℝ) :
    ¬ IsBalanced (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) := by
  intro hb
  set c := oddFold primeTrianglePos (weilLedgerKernel 1 1) b
  have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 : c 0 1 < 0 := by linarith [(oddFold_primeTriangle_weilLedgerKernel_one_zero_one b).2]
  have h12 : 0 < c 1 2 := by linarith [(oddFold_primeTriangle_weilLedgerKernel_one_one_two b).1]
  have h20 : c 2 0 < 0 := by linarith [(oddFold_primeTriangle_weilLedgerKernel_one_two_zero b).2]
  have hco : IsCompleteOverlap c := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
    · exact absurd rfl hij
    · exact h01.ne
    · rw [hsym 0 2]; exact h20.ne
    · rw [hsym 1 0]; exact h01.ne
    · exact absurd rfl hij
    · exact h12.ne'
    · exact h20.ne
    · rw [hsym 2 1]; exact h12.ne'
    · exact absurd rfl hij
  have hneg := (isBalanced_iff_triangleHolonomy_neg hsym hco).mp hb 0 1 2
    (by decide) (by decide) (by decide)
  linarith [triangleHolonomy_primeTriangle_weilLedgerKernel_one_pos b]

/-- The positive gauge `v = ![4, 1, 1]` on `primeTrianglePos`. -/
def primeTriangleGauge : Fin 3 → ℝ := ![4, 1, 1]

/-- The canonical path routing on `primeTrianglePos`: the anti-aligned overlap `(1, 2)` is routed
through the interior hub `0` via `[0, 2]`, and `(2, 1)` via `[0, 1]`. -/
def primeTrianglePath (a b : Fin 3) : List (Fin 3) :=
  if a = 1 ∧ b = 2 then [0, 2]
  else if a = 2 ∧ b = 1 then [0, 1]
  else []

/-- Unit shares along the canonical path on `primeTrianglePos`. -/
def primeTriangleShare (_a _b _x _y : Fin 3) : ℝ := 1

/-- Only `(1, 2)` and `(2, 1)` are anti-aligned on `primeTrianglePos` under `weilLedgerKernel 1 1`. -/
theorem primeTriangle_pos_overlap_iff (b : Fin 3 → ℝ) {x y : Fin 3} (hxy : x ≠ y)
    (hpos : 0 < oddFold primeTrianglePos (weilLedgerKernel 1 1) b x y) :
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) := by
  have hsym : IsSymmetricCoupling (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) :=
    oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 := (oddFold_primeTriangle_weilLedgerKernel_one_zero_one b).2
  have h20 := (oddFold_primeTriangle_weilLedgerKernel_one_two_zero b).2
  fin_cases x <;> fin_cases y <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hxy hpos
  · exact absurd rfl hxy
  · linarith
  · rw [hsym 0 2] at hpos; linarith
  · rw [hsym 1 0] at hpos; linarith
  · exact absurd rfl hxy
  · decide
  · linarith
  · decide
  · exact absurd rfl hxy

/-- **Explicit `PathCertificate` for the source-faithful prime triangle `weilLedgerKernel 1 1`.**
In gauge `v = ![4, 1, 1]`, the canonical path `1 → 0 → 2` through the aligned edges `(1, 0)` and
`(0, 2)` pays the anti-aligned edge `(1, 2)` with budget `< (2/5)/4 · (7 + 1) = 4/5 ≤ 1`. -/
def primeTrianglePathCertificate (b : Fin 3 → ℝ)
    (hsuper : ∀ i, 0 ≤ couplingAction (oddFold primeTrianglePos (weilLedgerKernel 1 1) b)
      primeTriangleGauge i) :
    PathCertificate (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) where
  gauge := primeTriangleGauge
  gauge_pos i := by
    fin_cases i <;> simp [primeTriangleGauge]
  supersolution := hsuper
  path := primeTrianglePath
  share := primeTriangleShare
  path_end a d had hpos := by
    rcases primeTriangle_pos_overlap_iff b had hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  path_aligned a d had hpos s hs := by
    have hsym := oddFold_isSymmetric (p := primeTrianglePos) (b := b) (weilLedgerKernel_neg 1 1)
    have h01 : oddFold primeTrianglePos (weilLedgerKernel 1 1) b 0 1 < 0 := by
      linarith [(oddFold_primeTriangle_weilLedgerKernel_one_zero_one b).2]
    have h20 : oddFold primeTrianglePos (weilLedgerKernel 1 1) b 2 0 < 0 := by
      linarith [(oddFold_primeTriangle_weilLedgerKernel_one_two_zero b).2]
    rcases primeTriangle_pos_overlap_iff b had hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change s < 2 at hs
      interval_cases s
      · change oddFold primeTrianglePos (weilLedgerKernel 1 1) b 1 0 < 0
        rwa [hsym 1 0]
      · change oddFold primeTrianglePos (weilLedgerKernel 1 1) b 0 2 < 0
        rwa [hsym 0 2]
    · change s < 2 at hs
      interval_cases s
      · exact h20
      · exact h01
  share_pos _ _ _ _ _ _ := by simp [primeTriangleShare]
  budget a d had hpos := by
    set c := oddFold primeTrianglePos (weilLedgerKernel 1 1) b
    have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
    have h01 : c 0 1 < -1 / 7 := (oddFold_primeTriangle_weilLedgerKernel_one_zero_one b).2
    have h20 : c 2 0 < -1 := (oddFold_primeTriangle_weilLedgerKernel_one_two_zero b).2
    have h12 : c 1 2 < 2 / 5 := (oddFold_primeTriangle_weilLedgerKernel_one_one_two b).2
    have h12_pos : 0 < c 1 2 := by
      linarith [(oddFold_primeTriangle_weilLedgerKernel_one_one_two b).1]
    have habs01 : 1 / 7 < |c 0 1| := by
      rw [abs_of_neg (by linarith)]; linarith
    have habs10 : 1 / 7 < |c 1 0| := by rwa [hsym 1 0]
    have habs20 : 1 < |c 2 0| := by
      rw [abs_of_neg (by linarith)]; linarith
    have habs02 : 1 < |c 0 2| := by rwa [hsym 0 2]
    have hinv01 : 1 / (1 * (|c 0 1| * 4 * 1)) ≤ 7 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv10 : 1 / (1 * (|c 1 0| * 1 * 4)) ≤ 7 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv20 : 1 / (1 * (|c 2 0| * 1 * 4)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv02 : 1 / (1 * (|c 0 2| * 4 * 1)) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    rcases primeTriangle_pos_overlap_iff b had hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change c 1 2 * primeTriangleGauge 1 * primeTriangleGauge 2 *
        ∑ s ∈ range 2, 1 / (1 * (|c (walkVertex 1 [0, 2] s) (walkVertex 1 [0, 2] (s + 1))| *
          primeTriangleGauge (walkVertex 1 [0, 2] s) *
          primeTriangleGauge (walkVertex 1 [0, 2] (s + 1)))) ≤ 1
      rw [sum_range_succ, sum_range_one]
      change c 1 2 * 1 * 1 * (1 / (1 * (|c 1 0| * 1 * 4)) + 1 / (1 * (|c 0 2| * 4 * 1))) ≤ 1
      nlinarith
    · change c 2 1 * primeTriangleGauge 2 * primeTriangleGauge 1 *
        ∑ s ∈ range 2, 1 / (1 * (|c (walkVertex 2 [0, 1] s) (walkVertex 2 [0, 1] (s + 1))| *
          primeTriangleGauge (walkVertex 2 [0, 1] s) *
          primeTriangleGauge (walkVertex 2 [0, 1] (s + 1)))) ≤ 1
      rw [sum_range_succ, sum_range_one, hsym 2 1]
      change c 1 2 * 1 * 1 * (1 / (1 * (|c 2 0| * 1 * 4)) + 1 / (1 * (|c 0 1| * 4 * 1))) ≤ 1
      nlinarith
  packing x y := by
    set c := oddFold primeTrianglePos (weilLedgerKernel 1 1) b
    have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
    have hcond : ∀ a d : Fin 3, (a ≠ d ∧ 0 < c a d) ↔ (a = 1 ∧ d = 2) ∨ (a = 2 ∧ d = 1) := by
      intro a d
      constructor
      · rintro ⟨had, hpos⟩; exact primeTriangle_pos_overlap_iff b had hpos
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨by decide, by linarith [(oddFold_primeTriangle_weilLedgerKernel_one_one_two b).1]⟩
        · rw [hsym 2 1]
          exact ⟨by decide, by linarith [(oddFold_primeTriangle_weilLedgerKernel_one_one_two b).1]⟩
    have h00 : ¬((0 : Fin 3) ≠ 0 ∧ 0 < c 0 0) := by rw [hcond]; decide
    have h01 : ¬((0 : Fin 3) ≠ 1 ∧ 0 < c 0 1) := by rw [hcond]; decide
    have h02 : ¬((0 : Fin 3) ≠ 2 ∧ 0 < c 0 2) := by rw [hcond]; decide
    have h10 : ¬((1 : Fin 3) ≠ 0 ∧ 0 < c 1 0) := by rw [hcond]; decide
    have h11 : ¬((1 : Fin 3) ≠ 1 ∧ 0 < c 1 1) := by rw [hcond]; decide
    have h12 : (1 : Fin 3) ≠ 2 ∧ 0 < c 1 2 := by rw [hcond]; decide
    have h20 : ¬((2 : Fin 3) ≠ 0 ∧ 0 < c 2 0) := by rw [hcond]; decide
    have h21 : (2 : Fin 3) ≠ 1 ∧ 0 < c 2 1 := by rw [hcond]; decide
    have h22 : ¬((2 : Fin 3) ≠ 2 ∧ 0 < c 2 2) := by rw [hcond]; decide
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three,
      if_neg h00, if_neg h01, if_neg h02,
      if_neg h10, if_neg h11, if_pos h12,
      if_neg h20, if_pos h21, if_neg h22]
    change (0 + 0 + 0) + (0 + 0 +
        ∑ s ∈ range 2,
          (if walkVertex 1 [0, 2] s = x ∧ walkVertex 1 [0, 2] (s + 1) = y then
            primeTriangleShare 1 2 x y else 0)) +
      (0 + (∑ s ∈ range 2,
          (if walkVertex 2 [0, 1] s = x ∧ walkVertex 2 [0, 1] (s + 1) = y then
            primeTriangleShare 2 1 x y else 0)) + 0) ≤ 1
    rw [sum_range_succ, sum_range_one, sum_range_succ, sum_range_one]
    change (0 + 0 + 0) + (0 + 0 +
        ((if (1 : Fin 3) = x ∧ (0 : Fin 3) = y then (1 : ℝ) else 0) +
         (if (0 : Fin 3) = x ∧ (2 : Fin 3) = y then (1 : ℝ) else 0))) +
      (0 + (((if (2 : Fin 3) = x ∧ (0 : Fin 3) = y then (1 : ℝ) else 0) +
             (if (0 : Fin 3) = x ∧ (1 : Fin 3) = y then (1 : ℝ) else 0))) + 0) ≤ 1
    fin_cases x <;> fin_cases y <;>
      norm_num [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.ext_iff,
        Fin.val_zero, Fin.val_one, Fin.val_two]

/-- **Canonical-path positivity of the source-faithful prime triangle.** Whenever the diagonal
budgets satisfy the supersolution condition `(Cv)_i ≥ 0` in gauge `v = ![4, 1, 1]`, the frustrated
source-faithful form `oddFold primeTrianglePos (weilLedgerKernel 1 1) b` is nonnegative on all
profiles. -/
theorem incidenceEnergy_oddFold_primeTriangle_weilLedgerKernel_one_nonneg (b : Fin 3 → ℝ)
    (hsuper : ∀ i, 0 ≤ couplingAction (oddFold primeTrianglePos (weilLedgerKernel 1 1) b)
      primeTriangleGauge i) (f : Fin 3 → ℝ) :
    0 ≤ incidenceEnergy (oddFold primeTrianglePos (weilLedgerKernel 1 1) b) f :=
  incidenceEnergy_nonneg_of_pathCertificate (oddFold_isSymmetric (weilLedgerKernel_neg 1 1))
    (primeTrianglePathCertificate b hsuper) f

/-- Lower bounds on the self-interaction `weilLedgerKernel 1 1 (2 * primeTrianglePos i)` at the
three vertices of `primeTrianglePos`. Note that at `i = 1`, `2 * p_1 = log(6/5)` lies below the
archimedean sign threshold `u₀`, so `weilLedgerKernel 1 1 (2 * p_1) > 0` is positive. -/
theorem weilLedgerKernel_one_two_mul_primeTrianglePos_ge :
    (-4 : ℝ) < weilLedgerKernel 1 1 (2 * primeTrianglePos 0) ∧
      0 < weilLedgerKernel 1 1 (2 * primeTrianglePos 1) ∧
      (-6 : ℝ) < weilLedgerKernel 1 1 (2 * primeTrianglePos 2) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [primeTrianglePos, Matrix.cons_val_zero]
    have h20 : 2 * ((Real.log 2 + Real.log 5 - Real.log 3) / 2) =
        Real.log 10 - Real.log 3 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    unfold weilLedgerKernel
    rw [h20, abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 3)
        (by norm_num) (by norm_num),
      weilKernel_log_eq (by norm_num : (1 : ℝ) < 10 / 3)]
    have heq : 1 * (-2 * ((10 / 3 : ℝ) ^ 3 - 10 / 3 - 1) /
        (((10 / 3 : ℝ) ^ 2 - 1) * Real.sqrt (10 / 3))) + 1 * 0 =
        -((1766 / 273 : ℝ) / Real.sqrt (10 / 3)) := by ring
    rw [heq]
    have hlt : (1766 / 273 : ℝ) / Real.sqrt (10 / 3) < 4 :=
      div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)
    linarith
  · simp only [primeTrianglePos, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h21 : 2 * ((Real.log 2 + Real.log 3 - Real.log 5) / 2) =
        Real.log 6 - Real.log 5 := by
      rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    unfold weilLedgerKernel
    rw [h21, abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
        (by norm_num) (by norm_num),
      weilKernel_log_eq (by norm_num : (1 : ℝ) < 6 / 5)]
    have heq : 1 * (-2 * ((6 / 5 : ℝ) ^ 3 - 6 / 5 - 1) /
        (((6 / 5 : ℝ) ^ 2 - 1) * Real.sqrt (6 / 5))) + 1 * 0 =
        (118 / 55 : ℝ) / Real.sqrt (6 / 5) := by ring
    rw [heq]
    positivity
  · simp only [primeTrianglePos, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have h22 : 2 * ((Real.log 3 + Real.log 5 - Real.log 2) / 2) =
        Real.log 15 - Real.log 2 := by
      rw [show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
    unfold weilLedgerKernel
    rw [h22, abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 7)
        (by norm_num) (by norm_num),
      weilKernel_log_eq (by norm_num : (1 : ℝ) < 15 / 2)]
    have heq : 1 * (-2 * ((15 / 2 : ℝ) ^ 3 - 15 / 2 - 1) /
        (((15 / 2 : ℝ) ^ 2 - 1) * Real.sqrt (15 / 2))) + 1 * 0 =
        -((3307 / 221 : ℝ) / Real.sqrt (15 / 2)) := by ring
    rw [heq]
    have hlt : (3307 / 221 : ℝ) / Real.sqrt (15 / 2) < 6 :=
      div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)
    linarith

/-- Explicit sufficient diagonal budgets `b 0 ≥ 6`, `b 1 ≥ 2`, `b 2 ≥ 21` making
`primeTriangleGauge = ![4, 1, 1]` a positive supersolution of the source-faithful prime triangle. -/
theorem supersolution_primeTriangleGauge_of_le {b : Fin 3 → ℝ}
    (hb0 : 6 ≤ b 0) (hb1 : 2 ≤ b 1) (hb2 : 21 ≤ b 2) :
    ∀ i, 0 ≤ couplingAction (oddFold primeTrianglePos (weilLedgerKernel 1 1) b)
      primeTriangleGauge i := by
  set c := oddFold primeTrianglePos (weilLedgerKernel 1 1) b
  have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 := (oddFold_primeTriangle_weilLedgerKernel_one_zero_one b).1
  have h20 := (oddFold_primeTriangle_weilLedgerKernel_one_two_zero b).1
  have h12 := (oddFold_primeTriangle_weilLedgerKernel_one_one_two b).1
  have h02 : (-15 / 4 : ℝ) < c 0 2 := by rwa [hsym 0 2]
  have h10 : (-2 / 5 : ℝ) < c 1 0 := by rwa [hsym 1 0]
  have h21 : (3 / 20 : ℝ) < c 2 1 := by rwa [hsym 2 1]
  have ⟨hd0, hd1, hd2⟩ := weilLedgerKernel_one_two_mul_primeTrianglePos_ge
  have hc00 : b 0 - 4 < c 0 0 := by
    change b 0 - 4 < oddFold primeTrianglePos (weilLedgerKernel 1 1) b 0 0
    rw [oddFold_diag]; linarith
  have hc11 : b 1 < c 1 1 := by
    change b 1 < oddFold primeTrianglePos (weilLedgerKernel 1 1) b 1 1
    rw [oddFold_diag]; linarith
  have hc22 : b 2 - 6 < c 2 2 := by
    change b 2 - 6 < oddFold primeTrianglePos (weilLedgerKernel 1 1) b 2 2
    rw [oddFold_diag]; linarith
  intro i
  unfold couplingAction
  rw [Fin.sum_univ_three]
  fin_cases i
  · change 0 ≤ c 0 0 * 4 + c 0 1 * 1 + c 0 2 * 1
    linarith
  · change 0 ≤ c 1 0 * 4 + c 1 1 * 1 + c 1 2 * 1
    linarith
  · change 0 ≤ c 2 0 * 4 + c 2 1 * 1 + c 2 2 * 1
    linarith

/-- Canonical diagonal budget `b = ![6, 2, 21]` for the source-faithful prime triangle
`primeTrianglePos` under `weilLedgerKernel 1 1`. -/
def primeTriangleCanonicalBudget : Fin 3 → ℝ := ![6, 2, 21]

/-- **Unconditional positive supersolution for the source-faithful prime triangle.** With the
canonical diagonal budget `primeTriangleCanonicalBudget = ![6, 2, 21]`, the gauge
`primeTriangleGauge = ![4, 1, 1]` is unconditionally a positive supersolution of
`oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget`. -/
theorem supersolution_primeTriangleCanonical :
    ∀ i, 0 ≤ couplingAction
      (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget)
      primeTriangleGauge i :=
  supersolution_primeTriangleGauge_of_le le_rfl le_rfl le_rfl

/-- **Unconditional `PathCertificate` for the source-faithful prime triangle.** -/
def primeTriangleCanonicalPathCertificate :
    PathCertificate (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget) :=
  primeTrianglePathCertificate primeTriangleCanonicalBudget supersolution_primeTriangleCanonical

/-- **Unconditional canonical-path positivity of the source-faithful prime triangle.** -/
theorem incidenceEnergy_oddFold_primeTriangleCanonical_nonneg (f : Fin 3 → ℝ) :
    0 ≤ incidenceEnergy
      (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget) f :=
  incidenceEnergy_oddFold_primeTriangle_weilLedgerKernel_one_nonneg
    primeTriangleCanonicalBudget supersolution_primeTriangleCanonical f


/-! ### Part 4: Packed canonical paths and overlapping-budget retention on `Fin 4` -/

/-- Four arithmetic sample positions `packedPrimePos : Fin 4 → ℝ` extending `primeTrianglePos` by
`p_3 = (3 log 5 − log 2 − log 3) / 2`. Both `(1, 2)` (sum `log 3`) and `(1, 3)` (sum `log 5`) are
anti-aligned under `weilLedgerKernel 1 1`, while the remaining four edges `{0, 1}, {0, 2}, {0, 3},
{2, 3}` are aligned (`< 0`). -/
def packedPrimePos : Fin 4 → ℝ :=
  ![(Real.log 2 + Real.log 5 - Real.log 3) / 2,
    (Real.log 2 + Real.log 3 - Real.log 5) / 2,
    (Real.log 3 + Real.log 5 - Real.log 2) / 2,
    (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2]

/-- On `Fin 3` embedded as `{0, 1, 2} ⊂ Fin 4`, `packedPrimePos` agrees with `primeTrianglePos`. -/
theorem packedPrimePos_zero : packedPrimePos 0 = primeTrianglePos 0 := rfl
theorem packedPrimePos_one : packedPrimePos 1 = primeTrianglePos 1 := rfl
theorem packedPrimePos_two : packedPrimePos 2 = primeTrianglePos 2 := rfl

/-- The off-diagonal entries of `oddFold packedPrimePos w b` on `{0, 1, 2}` match those of
`oddFold primeTrianglePos w b`. -/
theorem oddFold_packedPrime_zero_one (b : Fin 4 → ℝ) :
    (-2 / 5 : ℝ) < oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 1 ∧
      oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 1 < -1 / 7 := by
  have heq : oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 1 =
      oddFold primeTrianglePos (weilLedgerKernel 1 1) 0 0 1 := by
    rw [oddFold_offDiag (by decide), oddFold_offDiag (by decide)]; rfl
  rw [heq]
  exact oddFold_primeTriangle_weilLedgerKernel_one_zero_one 0

theorem oddFold_packedPrime_two_zero (b : Fin 4 → ℝ) :
    (-15 / 4 : ℝ) < oddFold packedPrimePos (weilLedgerKernel 1 1) b 2 0 ∧
      oddFold packedPrimePos (weilLedgerKernel 1 1) b 2 0 < -1 := by
  have heq : oddFold packedPrimePos (weilLedgerKernel 1 1) b 2 0 =
      oddFold primeTrianglePos (weilLedgerKernel 1 1) 0 2 0 := by
    rw [oddFold_offDiag (by decide), oddFold_offDiag (by decide)]; rfl
  rw [heq]
  exact oddFold_primeTriangle_weilLedgerKernel_one_two_zero 0

theorem oddFold_packedPrime_one_two (b : Fin 4 → ℝ) :
    (3 / 20 : ℝ) < oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 2 ∧
      oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 2 < 2 / 5 := by
  have heq : oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 2 =
      oddFold primeTrianglePos (weilLedgerKernel 1 1) 0 1 2 := by
    rw [oddFold_offDiag (by decide), oddFold_offDiag (by decide)]; rfl
  rw [heq]
  exact oddFold_primeTriangle_weilLedgerKernel_one_one_two 0

/-- On `packedPrimePos` at the source-faithful calibration `weilLedgerKernel 1 1`, the `(1, 3)`
overlap (sum `log 5`, difference `log(25/6)`) is anti-aligned and satisfies
`1/4 < c 1 3 < 13/30`. -/
theorem oddFold_packedPrime_one_three (b : Fin 4 → ℝ) :
    (1 / 4 : ℝ) < oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 3 ∧
      oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 3 < 13 / 30 := by
  rw [oddFold_offDiag (by decide : (1 : Fin 4) ≠ 3)]
  simp only [packedPrimePos, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  have hsum : (Real.log 2 + Real.log 3 - Real.log 5) / 2 +
      (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2 = Real.log 5 := by ring
  have hdiff : (Real.log 2 + Real.log 3 - Real.log 5) / 2 -
      (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2 = -(Real.log 25 - Real.log 6) := by
    have h25 : 2 * Real.log 5 = Real.log 25 := by
      rw [show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
    have h6 : Real.log 2 + Real.log 3 = Real.log 6 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    linarith
  have hdiv : weilLedgerKernel 1 1 (-(Real.log 25 - Real.log 6)) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 6)) := by
    rw [weilLedgerKernel_neg]
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 4)
        (by norm_num) (by norm_num)]
    ring
  rw [hsum, hdiff, hdiv]
  exact ⟨by linarith [weilLedgerKernel_one_log_five_bounds.1,
      neg_weilKernel_log_twenty_five_sixths_bounds.1],
    by linarith [weilLedgerKernel_one_log_five_bounds.2,
      neg_weilKernel_log_twenty_five_sixths_bounds.2]⟩

/-- On `packedPrimePos` at the source-faithful calibration `weilLedgerKernel 1 1`, the `(0, 3)`
overlap (sum `log(25/3)`, difference `log(5/2)`) is aligned and satisfies
`−31/10 < c 0 3 < −2`. -/
theorem oddFold_packedPrime_zero_three (b : Fin 4 → ℝ) :
    (-31 / 10 : ℝ) < oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 3 ∧
      oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 3 < -2 := by
  rw [oddFold_offDiag (by decide : (0 : Fin 4) ≠ 3)]
  simp only [packedPrimePos, Matrix.cons_val_zero, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  have h25 : 2 * Real.log 5 = Real.log 25 := by
    rw [show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
  have hsum : (Real.log 2 + Real.log 5 - Real.log 3) / 2 +
      (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2 = Real.log 25 - Real.log 3 := by linarith
  have hdiff : (Real.log 2 + Real.log 5 - Real.log 3) / 2 -
      (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2 = -(Real.log 5 - Real.log 2) := by ring
  have hsum_k : weilLedgerKernel 1 1 (Real.log 25 - Real.log 3) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 3)) := by
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 8)
        (by norm_num) (by norm_num)]
    ring
  have hdiff_k : weilLedgerKernel 1 1 (-(Real.log 5 - Real.log 2)) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 2)) := by
    rw [weilLedgerKernel_neg]
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 2)
        (by norm_num) (by norm_num)]
    ring
  rw [hsum, hdiff, hsum_k, hdiff_k]
  exact ⟨by linarith [neg_weilKernel_log_twenty_five_thirds_bounds.2,
      neg_weilKernel_log_five_halves_bounds.1],
    by linarith [neg_weilKernel_log_twenty_five_thirds_bounds.1,
      neg_weilKernel_log_five_halves_bounds.2]⟩

/-- On `packedPrimePos` at the source-faithful calibration `weilLedgerKernel 1 1`, the `(2, 3)`
overlap (sum `log(25/2)`, difference `log(5/3)`) is aligned and satisfies
`−32/5 < c 2 3 < −4`. -/
theorem oddFold_packedPrime_two_three (b : Fin 4 → ℝ) :
    (-32 / 5 : ℝ) < oddFold packedPrimePos (weilLedgerKernel 1 1) b 2 3 ∧
      oddFold packedPrimePos (weilLedgerKernel 1 1) b 2 3 < -4 := by
  rw [oddFold_offDiag (by decide : (2 : Fin 4) ≠ 3)]
  simp only [packedPrimePos, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  have h25 : 2 * Real.log 5 = Real.log 25 := by
    rw [show (25 : ℝ) = (5 : ℝ) ^ 2 by norm_num, Real.log_pow]; ring
  have hsum : (Real.log 3 + Real.log 5 - Real.log 2) / 2 +
      (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2 = Real.log 25 - Real.log 2 := by linarith
  have hdiff : (Real.log 3 + Real.log 5 - Real.log 2) / 2 -
      (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2 = -(Real.log 5 - Real.log 3) := by ring
  have hsum_k : weilLedgerKernel 1 1 (Real.log 25 - Real.log 2) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (25 / 2)) := by
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 12)
        (by norm_num) (by norm_num)]
    ring
  have hdiff_k : weilLedgerKernel 1 1 (-(Real.log 5 - Real.log 3)) =
      RHTower.ArchimedeanKernel.weilKernel (Real.log (5 / 3)) := by
    rw [weilLedgerKernel_neg]
    unfold weilLedgerKernel
    rw [abs_log_sub_eq_log_div (by norm_num) (by norm_num),
      primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 1)
        (by norm_num) (by norm_num)]
    ring
  rw [hsum, hdiff, hsum_k, hdiff_k]
  exact ⟨by linarith [neg_weilKernel_log_twenty_five_halves_bounds.2,
      neg_weilKernel_log_five_thirds_bounds.1],
    by linarith [neg_weilKernel_log_twenty_five_halves_bounds.1,
      neg_weilKernel_log_five_thirds_bounds.2]⟩

/-- Classification of the anti-aligned overlaps on `packedPrimePos` under `weilLedgerKernel 1 1`:
the positive off-diagonal entries are exactly `(1, 2), (2, 1), (1, 3), (3, 1)`. -/
theorem packedPrime_pos_overlap_iff (b : Fin 4 → ℝ) {x y : Fin 4} (hxy : x ≠ y)
    (hpos : 0 < oddFold packedPrimePos (weilLedgerKernel 1 1) b x y) :
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 3) ∨ (x = 3 ∧ y = 1) := by
  have hsym : IsSymmetricCoupling (oddFold packedPrimePos (weilLedgerKernel 1 1) b) :=
    oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 := (oddFold_packedPrime_zero_one b).2
  have h20 := (oddFold_packedPrime_two_zero b).2
  have h03 := (oddFold_packedPrime_zero_three b).2
  have h23 := (oddFold_packedPrime_two_three b).2
  fin_cases x <;> fin_cases y <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hxy hpos
  · exact absurd rfl hxy
  · linarith
  · rw [hsym 0 2] at hpos; linarith
  · linarith
  · rw [hsym 1 0] at hpos; linarith
  · exact absurd rfl hxy
  · decide
  · decide
  · linarith
  · decide
  · exact absurd rfl hxy
  · linarith
  · rw [hsym 3 0] at hpos; linarith
  · decide
  · rw [hsym 3 2] at hpos; linarith
  · exact absurd rfl hxy

/-- The positive gauge `v = ![8, 1, 1, 1]` for the packed 4-point arithmetic configuration. -/
def packedPrimeGauge : Fin 4 → ℝ := ![8, 1, 1, 1]

/-- The packed canonical paths on `Fin 4`: `(1, 2)` and `(1, 3)` are routed through the hub `0`
via `[0, 2]` and `[0, 3]` (and their reversals via `[0, 1]`), sharing the hub edge `{0, 1}`. -/
def packedPrimePath (a d : Fin 4) : List (Fin 4) :=
  if a = 1 ∧ d = 2 then [0, 2]
  else if a = 2 ∧ d = 1 then [0, 1]
  else if a = 1 ∧ d = 3 then [0, 3]
  else if a = 3 ∧ d = 1 then [0, 1]
  else []

/-- Edge shares on `Fin 4`: the shared hub edge `(1, 0)` (and `(0, 1)`) is split with equal shares
`1/2 + 1/2 = 1` between the two frustrated triangles `(1, 0, 2)` and `(1, 0, 3)`, while the
unshared edges `(0, 2), (2, 0), (0, 3), (3, 0)` receive full share `1`. -/
def packedPrimeShare (_a _d x y : Fin 4) : ℝ :=
  if (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) then 1 / 2 else 1

/-- **Packed `PathCertificate` for actual arithmetic coefficients with source-faithful full-form
calibration on `Fin 4`.** Both anti-aligned prime-sum edges `(1, 2)` (sum `log 3`) and `(1, 3)`
(sum `log 5`) are paid simultaneously through the shared aligned hub edge `(1, 0)` with packed
shares `1/2 + 1/2 = 1` in gauge `v = ![8, 1, 1, 1]`. -/
def packedPrimePathCertificate (b : Fin 4 → ℝ)
    (hsuper : ∀ i, 0 ≤ couplingAction (oddFold packedPrimePos (weilLedgerKernel 1 1) b)
      packedPrimeGauge i) :
    PathCertificate (oddFold packedPrimePos (weilLedgerKernel 1 1) b) where
  gauge := packedPrimeGauge
  gauge_pos i := by
    fin_cases i <;> simp [packedPrimeGauge]
  supersolution := hsuper
  path := packedPrimePath
  share := packedPrimeShare
  path_end a d had hpos := by
    rcases packedPrime_pos_overlap_iff b had hpos with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  path_aligned a d had hpos s hs := by
    have hsym := oddFold_isSymmetric (p := packedPrimePos) (b := b) (weilLedgerKernel_neg 1 1)
    have h01 : oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 1 < 0 := by
      linarith [(oddFold_packedPrime_zero_one b).2]
    have h20 : oddFold packedPrimePos (weilLedgerKernel 1 1) b 2 0 < 0 := by
      linarith [(oddFold_packedPrime_two_zero b).2]
    have h03 : oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 3 < 0 := by
      linarith [(oddFold_packedPrime_zero_three b).2]
    rcases packedPrime_pos_overlap_iff b had hpos with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change s < 2 at hs
      interval_cases s
      · change oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 0 < 0
        rwa [hsym 1 0]
      · change oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 2 < 0
        rwa [hsym 0 2]
    · change s < 2 at hs
      interval_cases s
      · exact h20
      · exact h01
    · change s < 2 at hs
      interval_cases s
      · change oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 0 < 0
        rwa [hsym 1 0]
      · exact h03
    · change s < 2 at hs
      interval_cases s
      · change oddFold packedPrimePos (weilLedgerKernel 1 1) b 3 0 < 0
        rwa [hsym 3 0]
      · exact h01
  share_pos a d _ _ s _ := by
    unfold packedPrimeShare
    split_ifs <;> norm_num
  budget a d had hpos := by
    set c := oddFold packedPrimePos (weilLedgerKernel 1 1) b
    have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
    have h01 : c 0 1 < -1 / 7 := (oddFold_packedPrime_zero_one b).2
    have h20 : c 2 0 < -1 := (oddFold_packedPrime_two_zero b).2
    have h03 : c 0 3 < -2 := (oddFold_packedPrime_zero_three b).2
    have h12 : c 1 2 < 2 / 5 := (oddFold_packedPrime_one_two b).2
    have h12_pos : 0 < c 1 2 := by linarith [(oddFold_packedPrime_one_two b).1]
    have h13 : c 1 3 < 13 / 30 := (oddFold_packedPrime_one_three b).2
    have h13_pos : 0 < c 1 3 := by linarith [(oddFold_packedPrime_one_three b).1]
    have habs01 : 1 / 7 < |c 0 1| := by rw [abs_of_neg (by linarith)]; linarith
    have habs10 : 1 / 7 < |c 1 0| := by rwa [hsym 1 0]
    have habs20 : 1 < |c 2 0| := by rw [abs_of_neg (by linarith)]; linarith
    have habs02 : 1 < |c 0 2| := by rwa [hsym 0 2]
    have habs03 : 2 < |c 0 3| := by rw [abs_of_neg (by linarith)]; linarith
    have habs30 : 2 < |c 3 0| := by rwa [hsym 3 0]
    have hinv01 : 1 / ((1 / 2) * (|c 0 1| * 8 * 1)) ≤ 7 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv10 : 1 / ((1 / 2) * (|c 1 0| * 1 * 8)) ≤ 7 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv20 : 1 / (1 * (|c 2 0| * 1 * 8)) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv02 : 1 / (1 * (|c 0 2| * 8 * 1)) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv03 : 1 / (1 * (|c 0 3| * 8 * 1)) ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hinv30 : 1 / (1 * (|c 3 0| * 1 * 8)) ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    rcases packedPrime_pos_overlap_iff b had hpos with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · change c 1 2 * packedPrimeGauge 1 * packedPrimeGauge 2 *
        ∑ s ∈ range 2, 1 / (packedPrimeShare 1 2 (walkVertex 1 [0, 2] s)
          (walkVertex 1 [0, 2] (s + 1)) *
          (|c (walkVertex 1 [0, 2] s) (walkVertex 1 [0, 2] (s + 1))| *
            packedPrimeGauge (walkVertex 1 [0, 2] s) *
            packedPrimeGauge (walkVertex 1 [0, 2] (s + 1)))) ≤ 1
      rw [sum_range_succ, sum_range_one]
      change c 1 2 * 1 * 1 * (1 / ((1 / 2) * (|c 1 0| * 1 * 8)) +
        1 / (1 * (|c 0 2| * 8 * 1))) ≤ 1
      nlinarith
    · change c 2 1 * packedPrimeGauge 2 * packedPrimeGauge 1 *
        ∑ s ∈ range 2, 1 / (packedPrimeShare 2 1 (walkVertex 2 [0, 1] s)
          (walkVertex 2 [0, 1] (s + 1)) *
          (|c (walkVertex 2 [0, 1] s) (walkVertex 2 [0, 1] (s + 1))| *
            packedPrimeGauge (walkVertex 2 [0, 1] s) *
            packedPrimeGauge (walkVertex 2 [0, 1] (s + 1)))) ≤ 1
      rw [sum_range_succ, sum_range_one, hsym 2 1]
      change c 1 2 * 1 * 1 * (1 / (1 * (|c 2 0| * 1 * 8)) +
        1 / ((1 / 2) * (|c 0 1| * 8 * 1))) ≤ 1
      nlinarith
    · change c 1 3 * packedPrimeGauge 1 * packedPrimeGauge 3 *
        ∑ s ∈ range 2, 1 / (packedPrimeShare 1 3 (walkVertex 1 [0, 3] s)
          (walkVertex 1 [0, 3] (s + 1)) *
          (|c (walkVertex 1 [0, 3] s) (walkVertex 1 [0, 3] (s + 1))| *
            packedPrimeGauge (walkVertex 1 [0, 3] s) *
            packedPrimeGauge (walkVertex 1 [0, 3] (s + 1)))) ≤ 1
      rw [sum_range_succ, sum_range_one]
      change c 1 3 * 1 * 1 * (1 / ((1 / 2) * (|c 1 0| * 1 * 8)) +
        1 / (1 * (|c 0 3| * 8 * 1))) ≤ 1
      nlinarith
    · change c 3 1 * packedPrimeGauge 3 * packedPrimeGauge 1 *
        ∑ s ∈ range 2, 1 / (packedPrimeShare 3 1 (walkVertex 3 [0, 1] s)
          (walkVertex 3 [0, 1] (s + 1)) *
          (|c (walkVertex 3 [0, 1] s) (walkVertex 3 [0, 1] (s + 1))| *
            packedPrimeGauge (walkVertex 3 [0, 1] s) *
            packedPrimeGauge (walkVertex 3 [0, 1] (s + 1)))) ≤ 1
      rw [sum_range_succ, sum_range_one, hsym 3 1]
      change c 1 3 * 1 * 1 * (1 / (1 * (|c 3 0| * 1 * 8)) +
        1 / ((1 / 2) * (|c 0 1| * 8 * 1))) ≤ 1
      nlinarith
  packing x y := by
    set c := oddFold packedPrimePos (weilLedgerKernel 1 1) b
    have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
    have hcond : ∀ a d : Fin 4, (a ≠ d ∧ 0 < c a d) ↔
        (a = 1 ∧ d = 2) ∨ (a = 2 ∧ d = 1) ∨ (a = 1 ∧ d = 3) ∨ (a = 3 ∧ d = 1) := by
      intro a d
      constructor
      · rintro ⟨had, hpos⟩; exact packedPrime_pos_overlap_iff b had hpos
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨by decide, by linarith [(oddFold_packedPrime_one_two b).1]⟩
        · rw [hsym 2 1]; exact ⟨by decide, by linarith [(oddFold_packedPrime_one_two b).1]⟩
        · exact ⟨by decide, by linarith [(oddFold_packedPrime_one_three b).1]⟩
        · rw [hsym 3 1]; exact ⟨by decide, by linarith [(oddFold_packedPrime_one_three b).1]⟩
    have h00 : ¬((0 : Fin 4) ≠ 0 ∧ 0 < c 0 0) := by rw [hcond]; decide
    have h01 : ¬((0 : Fin 4) ≠ 1 ∧ 0 < c 0 1) := by rw [hcond]; decide
    have h02 : ¬((0 : Fin 4) ≠ 2 ∧ 0 < c 0 2) := by rw [hcond]; decide
    have h03 : ¬((0 : Fin 4) ≠ 3 ∧ 0 < c 0 3) := by rw [hcond]; decide
    have h10 : ¬((1 : Fin 4) ≠ 0 ∧ 0 < c 1 0) := by rw [hcond]; decide
    have h11 : ¬((1 : Fin 4) ≠ 1 ∧ 0 < c 1 1) := by rw [hcond]; decide
    have h12 : (1 : Fin 4) ≠ 2 ∧ 0 < c 1 2 := by rw [hcond]; decide
    have h13 : (1 : Fin 4) ≠ 3 ∧ 0 < c 1 3 := by rw [hcond]; decide
    have h20 : ¬((2 : Fin 4) ≠ 0 ∧ 0 < c 2 0) := by rw [hcond]; decide
    have h21 : (2 : Fin 4) ≠ 1 ∧ 0 < c 2 1 := by rw [hcond]; decide
    have h22 : ¬((2 : Fin 4) ≠ 2 ∧ 0 < c 2 2) := by rw [hcond]; decide
    have h23 : ¬((2 : Fin 4) ≠ 3 ∧ 0 < c 2 3) := by rw [hcond]; decide
    have h30 : ¬((3 : Fin 4) ≠ 0 ∧ 0 < c 3 0) := by rw [hcond]; decide
    have h31 : (3 : Fin 4) ≠ 1 ∧ 0 < c 3 1 := by rw [hcond]; decide
    have h32 : ¬((3 : Fin 4) ≠ 2 ∧ 0 < c 3 2) := by rw [hcond]; decide
    have h33 : ¬((3 : Fin 4) ≠ 3 ∧ 0 < c 3 3) := by rw [hcond]; decide
    rw [Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four, Fin.sum_univ_four,
      if_neg h00, if_neg h01, if_neg h02, if_neg h03,
      if_neg h10, if_neg h11, if_pos h12, if_pos h13,
      if_neg h20, if_pos h21, if_neg h22, if_neg h23,
      if_neg h30, if_pos h31, if_neg h32, if_neg h33]
    change (0 + 0 + 0 + 0) +
      (0 + 0 +
        (∑ s ∈ range 2,
          (if walkVertex 1 [0, 2] s = x ∧ walkVertex 1 [0, 2] (s + 1) = y then
            packedPrimeShare 1 2 x y else 0)) +
        (∑ s ∈ range 2,
          (if walkVertex 1 [0, 3] s = x ∧ walkVertex 1 [0, 3] (s + 1) = y then
            packedPrimeShare 1 3 x y else 0))) +
      (0 +
        (∑ s ∈ range 2,
          (if walkVertex 2 [0, 1] s = x ∧ walkVertex 2 [0, 1] (s + 1) = y then
            packedPrimeShare 2 1 x y else 0)) + 0 + 0) +
      (0 +
        (∑ s ∈ range 2,
          (if walkVertex 3 [0, 1] s = x ∧ walkVertex 3 [0, 1] (s + 1) = y then
            packedPrimeShare 3 1 x y else 0)) + 0 + 0) ≤ 1
    rw [sum_range_succ, sum_range_one, sum_range_succ, sum_range_one,
      sum_range_succ, sum_range_one, sum_range_succ, sum_range_one]
    change (0 + 0 + 0 + 0) +
      (0 + 0 +
        ((if (1 : Fin 4) = x ∧ (0 : Fin 4) = y then packedPrimeShare 1 2 x y else 0) +
         (if (0 : Fin 4) = x ∧ (2 : Fin 4) = y then packedPrimeShare 1 2 x y else 0)) +
        ((if (1 : Fin 4) = x ∧ (0 : Fin 4) = y then packedPrimeShare 1 3 x y else 0) +
         (if (0 : Fin 4) = x ∧ (3 : Fin 4) = y then packedPrimeShare 1 3 x y else 0))) +
      (0 +
        ((if (2 : Fin 4) = x ∧ (0 : Fin 4) = y then packedPrimeShare 2 1 x y else 0) +
         (if (0 : Fin 4) = x ∧ (1 : Fin 4) = y then packedPrimeShare 2 1 x y else 0)) + 0 + 0) +
      (0 +
        ((if (3 : Fin 4) = x ∧ (0 : Fin 4) = y then packedPrimeShare 3 1 x y else 0) +
         (if (0 : Fin 4) = x ∧ (1 : Fin 4) = y then packedPrimeShare 3 1 x y else 0)) + 0 + 0) ≤ 1
    have hval3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    fin_cases x <;> fin_cases y <;>
      norm_num [packedPrimeShare, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.ext_iff,
        Fin.val_zero, Fin.val_one, Fin.val_two, hval3]

/-- **Positivity of the packed 4-point arithmetic configuration under `weilLedgerKernel 1 1`.** -/
theorem incidenceEnergy_oddFold_packedPrime_weilLedgerKernel_one_nonneg (b : Fin 4 → ℝ)
    (hsuper : ∀ i, 0 ≤ couplingAction (oddFold packedPrimePos (weilLedgerKernel 1 1) b)
      packedPrimeGauge i) (f : Fin 4 → ℝ) :
    0 ≤ incidenceEnergy (oddFold packedPrimePos (weilLedgerKernel 1 1) b) f :=
  incidenceEnergy_nonneg_of_pathCertificate (oddFold_isSymmetric (weilLedgerKernel_neg 1 1))
    (packedPrimePathCertificate b hsuper) f

/-- Lower bound on the self-interaction `weilLedgerKernel 1 1 (2 * packedPrimePos 3)`. -/
theorem weilLedgerKernel_one_two_mul_packedPrimePos_three_gt :
    (-10 : ℝ) < weilLedgerKernel 1 1 (2 * packedPrimePos 3) := by
  have hp3 : packedPrimePos 3 = (3 * Real.log 5 - Real.log 2 - Real.log 3) / 2 := by
    simp only [packedPrimePos, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have h125 : 3 * Real.log 5 = Real.log 125 := by
    rw [show (125 : ℝ) = (5 : ℝ) ^ 3 by norm_num, Real.log_pow]; ring
  have h6 : Real.log 2 + Real.log 3 = Real.log 6 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h23 : 2 * packedPrimePos 3 = Real.log 125 - Real.log 6 := by
    rw [hp3]; linarith
  unfold weilLedgerKernel
  rw [h23, abs_log_sub_eq_log_div (by norm_num) (by norm_num),
    primeKernel_log_sub (by norm_num) (by norm_num) (by norm_num) (m := 20)
      (by norm_num) (by norm_num),
    weilKernel_log_eq (by norm_num : (1 : ℝ) < 125 / 6)]
  have heq : 1 * (-2 * ((125 / 6 : ℝ) ^ 3 - 125 / 6 - 1) /
      (((125 / 6 : ℝ) ^ 2 - 1) * Real.sqrt (125 / 6))) + 1 * 0 =
      -((1948409 / 46767 : ℝ) / Real.sqrt (125 / 6)) := by ring
  rw [heq]
  have hlt : (1948409 / 46767 : ℝ) / Real.sqrt (125 / 6) < 10 :=
    div_sqrt_lt_of_sq_lt (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- Explicit sufficient diagonal budgets `b 0 ≥ 5`, `b 1 ≥ 3`, `b 2 ≥ 43`, `b 3 ≥ 41` making
`packedPrimeGauge = ![8, 1, 1, 1]` a positive supersolution of the packed 4-point arithmetic
configuration. Packing two positive overlaps `(1, 2)` and `(1, 3)` through the shared hub step
`1 → 0` doubles the hub gauge (`v 0 = 8` vs `4`) and inflates the diagonal budget needed at vertex
`2` (`b 2 ≥ 43` vs `21`). -/
theorem supersolution_packedPrimeGauge_of_le {b : Fin 4 → ℝ}
    (hb0 : 5 ≤ b 0) (hb1 : 3 ≤ b 1) (hb2 : 43 ≤ b 2) (hb3 : 41 ≤ b 3) :
    ∀ i, 0 ≤ couplingAction (oddFold packedPrimePos (weilLedgerKernel 1 1) b)
      packedPrimeGauge i := by
  set c := oddFold packedPrimePos (weilLedgerKernel 1 1) b
  have hsym : IsSymmetricCoupling c := oddFold_isSymmetric (weilLedgerKernel_neg 1 1)
  have h01 := (oddFold_packedPrime_zero_one b).1
  have h20 := (oddFold_packedPrime_two_zero b).1
  have h12 := (oddFold_packedPrime_one_two b).1
  have h13 := (oddFold_packedPrime_one_three b).1
  have h03 := (oddFold_packedPrime_zero_three b).1
  have h23 := (oddFold_packedPrime_two_three b).1
  have h02 : (-15 / 4 : ℝ) < c 0 2 := by rwa [hsym 0 2]
  have h10 : (-2 / 5 : ℝ) < c 1 0 := by rwa [hsym 1 0]
  have h21 : (3 / 20 : ℝ) < c 2 1 := by rwa [hsym 2 1]
  have h31 : (1 / 4 : ℝ) < c 3 1 := by rwa [hsym 3 1]
  have h30 : (-31 / 10 : ℝ) < c 3 0 := by rwa [hsym 3 0]
  have h32 : (-32 / 5 : ℝ) < c 3 2 := by rwa [hsym 3 2]
  have ⟨hd0, hd1, hd2⟩ := weilLedgerKernel_one_two_mul_primeTrianglePos_ge
  have hd3 := weilLedgerKernel_one_two_mul_packedPrimePos_three_gt
  have hc00 : b 0 - 4 < c 0 0 := by
    change b 0 - 4 < oddFold packedPrimePos (weilLedgerKernel 1 1) b 0 0
    rw [oddFold_diag, packedPrimePos_zero]; linarith
  have hc11 : b 1 < c 1 1 := by
    change b 1 < oddFold packedPrimePos (weilLedgerKernel 1 1) b 1 1
    rw [oddFold_diag, packedPrimePos_one]; linarith
  have hc22 : b 2 - 6 < c 2 2 := by
    change b 2 - 6 < oddFold packedPrimePos (weilLedgerKernel 1 1) b 2 2
    rw [oddFold_diag, packedPrimePos_two]; linarith
  have hc33 : b 3 - 10 < c 3 3 := by
    change b 3 - 10 < oddFold packedPrimePos (weilLedgerKernel 1 1) b 3 3
    rw [oddFold_diag]; linarith
  intro i
  fin_cases i
  · change 0 ≤ ∑ j : Fin 4, c 0 j * packedPrimeGauge j
    rw [Fin.sum_univ_four]
    change 0 ≤ c 0 0 * 8 + c 0 1 * 1 + c 0 2 * 1 + c 0 3 * 1
    linarith
  · change 0 ≤ ∑ j : Fin 4, c 1 j * packedPrimeGauge j
    rw [Fin.sum_univ_four]
    change 0 ≤ c 1 0 * 8 + c 1 1 * 1 + c 1 2 * 1 + c 1 3 * 1
    linarith
  · change 0 ≤ ∑ j : Fin 4, c 2 j * packedPrimeGauge j
    rw [Fin.sum_univ_four]
    change 0 ≤ c 2 0 * 8 + c 2 1 * 1 + c 2 2 * 1 + c 2 3 * 1
    linarith
  · change 0 ≤ ∑ j : Fin 4, c 3 j * packedPrimeGauge j
    rw [Fin.sum_univ_four]
    change 0 ≤ c 3 0 * 8 + c 3 1 * 1 + c 3 2 * 1 + c 3 3 * 1
    linarith

/-- Canonical diagonal budget `b = ![5, 3, 43, 41]` for the packed 4-point arithmetic configuration
`packedPrimePos` under `weilLedgerKernel 1 1`. -/
def packedPrimeCanonicalBudget : Fin 4 → ℝ := ![5, 3, 43, 41]

/-- **Unconditional positive supersolution for the packed 4-point arithmetic configuration.** With
the canonical diagonal budget `packedPrimeCanonicalBudget = ![5, 3, 43, 41]`, the gauge
`packedPrimeGauge = ![8, 1, 1, 1]` is unconditionally a positive supersolution of
`oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget`. -/
theorem supersolution_packedPrimeCanonical :
    ∀ i, 0 ≤ couplingAction
      (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget)
      packedPrimeGauge i :=
  supersolution_packedPrimeGauge_of_le le_rfl le_rfl le_rfl le_rfl

/-- **Unconditional packed `PathCertificate` for the 4-point arithmetic configuration under
`weilLedgerKernel 1 1`.** -/
def packedPrimeCanonicalPathCertificate :
    PathCertificate (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget) :=
  packedPrimePathCertificate packedPrimeCanonicalBudget supersolution_packedPrimeCanonical

/-- **Unconditional canonical-path positivity of the packed 4-point arithmetic configuration under
`weilLedgerKernel 1 1`.** -/
theorem incidenceEnergy_oddFold_packedPrimeCanonical_nonneg (f : Fin 4 → ℝ) :
    0 ≤ incidenceEnergy
      (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget) f :=
  incidenceEnergy_oddFold_packedPrime_weilLedgerKernel_one_nonneg
    packedPrimeCanonicalBudget supersolution_packedPrimeCanonical f

/-- **Overlapping-budget retention along shared canonical-path steps.** In any `PathCertificate`
for `c`, every anti-aligned overlap `(a, b)` (`a ≠ b`, `c a b > 0`) whose canonical path begins
with the aligned step `a → u` (`walkVertex a (P.path a b) 1 = u`) must receive a share
`λ_ab(a, u)` satisfying `c a b * v b ≤ λ_ab(a, u) * |c a u| * v u`. Summing over any set `S` of
targets `b` routed through the shared step `(a, u)` forces
`∑_{b ∈ S} c a b * v b ≤ |c a u| * v u`, inflating the required hub gauge `v u` and retaining
overlapping diagonal budget demands at `u` and its neighbors. -/
theorem packed_shared_step_gauge_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ι → ι → ℝ} (P : PathCertificate c) (a u : ι) (S : Finset ι)
    (hS : ∀ b ∈ S, a ≠ b ∧ 0 < c a b ∧ 0 < (P.path a b).length ∧
      walkVertex a (P.path a b) 1 = u) :
    ∑ b ∈ S, c a b * P.gauge b ≤ |c a u| * P.gauge u := by
  have hterm : ∀ b ∈ S,
      c a b * P.gauge b ≤ P.share a b a u * (|c a u| * P.gauge u) := by
    intro b hb
    obtain ⟨hab, hcab, hlen, hu⟩ := hS b hb
    have h0 : 0 ∈ range (P.path a b).length := mem_range.mpr hlen
    have hWpos : ∀ s ∈ range (P.path a b).length,
        0 ≤ 1 / (P.share a b (walkVertex a (P.path a b) s) (walkVertex a (P.path a b) (s + 1)) *
          (|c (walkVertex a (P.path a b) s) (walkVertex a (P.path a b) (s + 1))| *
            P.gauge (walkVertex a (P.path a b) s) *
            P.gauge (walkVertex a (P.path a b) (s + 1)))) := fun s hs => by
      have hs' := mem_range.mp hs
      have h1 := P.share_pos a b hab hcab s hs'
      have h2 := abs_pos.mpr (P.path_aligned a b hab hcab s hs').ne
      have h3 := P.gauge_pos (walkVertex a (P.path a b) s)
      have h4 := P.gauge_pos (walkVertex a (P.path a b) (s + 1))
      positivity
    have hsingle := single_le_sum hWpos h0
    have h0v : walkVertex a (P.path a b) 0 = a := walkVertex_zero a (P.path a b)
    rw [h0v, hu] at hsingle
    have hbud := P.budget a b hab hcab
    have hcvv : 0 ≤ c a b * P.gauge a * P.gauge b := by
      have := P.gauge_pos a; have := P.gauge_pos b; positivity
    have hle1 : c a b * P.gauge a * P.gauge b *
        (1 / (P.share a b a u * (|c a u| * P.gauge a * P.gauge u))) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hsingle hcvv) hbud
    have hsh_pos : 0 < P.share a b a u := by
      have := P.share_pos a b hab hcab 0 hlen
      rwa [h0v, hu] at this
    have hcau_pos : 0 < |c a u| := by
      have := P.path_aligned a b hab hcab 0 hlen
      rw [h0v, hu] at this
      exact abs_pos.mpr this.ne
    have hga_pos := P.gauge_pos a
    have hgu_pos := P.gauge_pos u
    rw [mul_one_div, div_le_iff₀ (by positivity), one_mul] at hle1
    have hcancel : P.share a b a u * (|c a u| * P.gauge a * P.gauge u) =
        P.gauge a * (P.share a b a u * (|c a u| * P.gauge u)) := by ring
    have hcancel2 : c a b * P.gauge a * P.gauge b = P.gauge a * (c a b * P.gauge b) := by ring
    rw [hcancel, hcancel2] at hle1
    exact le_of_mul_le_mul_left hle1 hga_pos
  have hsum_le : ∑ b ∈ S, c a b * P.gauge b ≤
      (∑ b ∈ S, P.share a b a u) * (|c a u| * P.gauge u) := by
    rw [sum_mul]
    exact sum_le_sum hterm
  have hpack_b : ∀ b ∈ S, P.share a b a u ≤
      if a ≠ b ∧ 0 < c a b then
        ∑ s ∈ range (P.path a b).length,
          (if walkVertex a (P.path a b) s = a ∧ walkVertex a (P.path a b) (s + 1) = u then
            P.share a b a u else 0) else 0 := by
    intro b hb
    obtain ⟨hab, hcab, hlen, hu⟩ := hS b hb
    rw [if_pos ⟨hab, hcab⟩]
    have h0 : 0 ∈ range (P.path a b).length := mem_range.mpr hlen
    have hnonneg : ∀ s ∈ range (P.path a b).length,
        0 ≤ (if walkVertex a (P.path a b) s = a ∧ walkVertex a (P.path a b) (s + 1) = u then
          P.share a b a u else 0) := fun s hs => by
      split_ifs with h
      · have hpos := P.share_pos a b hab hcab s (mem_range.mp hs)
        rw [h.1, h.2] at hpos
        exact hpos.le
      · exact le_rfl
    have hsingle := single_le_sum hnonneg h0
    have h0v : walkVertex a (P.path a b) 0 = a := walkVertex_zero a (P.path a b)
    simpa [h0v, hu] using hsingle
  have hpack_S : ∑ b ∈ S, P.share a b a u ≤ 1 := by
    have hF_nonneg : ∀ x d : ι, 0 ≤ (if x ≠ d ∧ 0 < c x d then
        ∑ s ∈ range (P.path x d).length,
          (if walkVertex x (P.path x d) s = a ∧ walkVertex x (P.path x d) (s + 1) = u then
            P.share x d a u else 0) else 0) := fun x d => by
      split_ifs with hxd
      · refine sum_nonneg fun s hs => ?_
        split_ifs with h
        · have hpos := P.share_pos x d hxd.1 hxd.2 s (mem_range.mp hs)
          rw [h.1, h.2] at hpos
          exact hpos.le
        · exact le_rfl
      · exact le_rfl
    calc ∑ b ∈ S, P.share a b a u
        ≤ ∑ b ∈ S, (if a ≠ b ∧ 0 < c a b then
            ∑ s ∈ range (P.path a b).length,
              (if walkVertex a (P.path a b) s = a ∧ walkVertex a (P.path a b) (s + 1) = u then
                P.share a b a u else 0) else 0) := sum_le_sum hpack_b
      _ ≤ ∑ b : ι, (if a ≠ b ∧ 0 < c a b then
            ∑ s ∈ range (P.path a b).length,
              (if walkVertex a (P.path a b) s = a ∧ walkVertex a (P.path a b) (s + 1) = u then
                P.share a b a u else 0) else 0) :=
          sum_le_univ_sum_of_nonneg fun b => hF_nonneg a b
      _ ≤ ∑ x : ι, ∑ b : ι, (if x ≠ b ∧ 0 < c x b then
            ∑ s ∈ range (P.path x b).length,
              (if walkVertex x (P.path x b) s = a ∧ walkVertex x (P.path x b) (s + 1) = u then
                P.share x b a u else 0) else 0) :=
          single_le_sum (fun x _ => sum_nonneg fun b _ => hF_nonneg x b) (mem_univ a)
      _ ≤ 1 := P.packing a u
  have hgu_nn : 0 ≤ |c a u| * P.gauge u := mul_nonneg (abs_nonneg _) (P.gauge_pos u).le
  calc ∑ b ∈ S, c a b * P.gauge b
      ≤ (∑ b ∈ S, P.share a b a u) * (|c a u| * P.gauge u) := hsum_le
    _ ≤ 1 * (|c a u| * P.gauge u) := mul_le_mul_of_nonneg_right hpack_S hgu_nn
    _ = |c a u| * P.gauge u := one_mul _

/-- Unconditional shared-step gauge bound for `packedPrimeCanonicalPathCertificate` on `{2, 3}`:
the sum of the gauge-weighted anti-aligned demands `(1, 2)` and `(1, 3)` is bounded by the shared
hub step capacity `|c 1 0| * packedPrimeGauge 0`. -/
theorem packedPrimeCanonical_shared_step_gauge_bound :
    ∑ b ∈ ({2, 3} : Finset (Fin 4)),
      oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget 1 b *
        packedPrimeGauge b ≤
      |oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget 1 0| *
        packedPrimeGauge 0 := by
  refine packed_shared_step_gauge_lower_bound packedPrimeCanonicalPathCertificate 1 0 {2, 3} ?_
  intro b hb
  rcases mem_insert.mp hb with rfl | hb
  · refine ⟨by decide, ?_, by decide, rfl⟩
    linarith [(oddFold_packedPrime_one_two packedPrimeCanonicalBudget).1]
  · rw [mem_singleton.mp hb]
    refine ⟨by decide, ?_, by decide, rfl⟩
    linarith [(oddFold_packedPrime_one_three packedPrimeCanonicalBudget).1]

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
