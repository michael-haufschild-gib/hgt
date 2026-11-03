import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistenceDecidesRH
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# The archimedean place alone is not Weil positive

Mechanism D of the dimension-zero geometry reads RH as an existence statement at finite levels:
RH holds iff for every aperture `A` some real weights `λ` make Weil's functional of `ζ`'s
archimedean datum nonnegative on all autocorrelations of tests supported in `[−A, A]`
(`riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo`, RHTower). The finite-level cone
`C_A = {λ : WeilPositiveFullUpTo λ A}` is the object of the mechanism. This module records its
structure and what the archimedean place does on its own.

* **The archimedean place alone is not Weil positive** (`not_weilPositiveFull_zero`,
  `exists_not_weilPositiveFullUpTo_zero`): with all prime weights removed, the Gamma factor and the
  pole are negative on the autocorrelation of some test, at a finite aperture. (The Weil cone is
  `{Λ}`, and `Λ(2) = log 2 ≠ 0`.) Positivity is a balance between the archimedean place and the primes,
  never an archimedean property.
* **Below the first prime the weights are invisible** (`re_weilFullFunctional_eq_zero_weight`,
  `weilPositiveFullUpTo_iff_zero`): for `2A < log 2`, Weil's functional on tests supported in `[−A, A]`
  does not depend on `λ`. So `C_A` is either every weight system or empty, decided by the archimedean
  place; and it is Weil positivity of `ζ` itself.
* **Under RH the archimedean place needs the first prime to fail**
  (`log_two_le_of_not_weilPositiveFullUpTo_zero`): every aperture where the archimedean place alone
  fails has `2A ≥ log 2`. Unconditionally such apertures exist. A failure of the archimedean place
  below the first prime would refute RH.
* **The finite-level cone is local and convex** (`weilPositiveFullUpTo_congr`,
  `convex_setOf_weilPositiveFullUpTo`): positivity up to `A` depends only on the weights at
  `n ≤ e^{2A}`, and Weil's functional is affine in them. At the first-fold level
  `log 2 ≤ 2A < log 3` the cone is a convex set of values of the single weight `λ(2)`
  (`weilPositiveFullUpTo_iff_firstFold`).
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open _root_.RHTower _root_.RHTower.WeilSpectral Zeta23

/-- **The archimedean place alone is not Weil positive.** -/
theorem not_weilPositiveFull_zero : ¬ WeilPositiveFull (fun _ => 0) := by
  intro h
  have h2 := eq_vonMangoldt_of_weilPositiveFull h 2 le_rfl
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h2
  have h2' : (0 : ℝ) = Real.log 2 := by simpa using h2
  exact (Real.log_pos one_lt_two).ne' h2'.symm

/-- The archimedean place fails at a finite aperture. -/
theorem exists_not_weilPositiveFullUpTo_zero :
    ∃ A : ℝ, ¬ WeilPositiveFullUpTo (fun _ => 0) A := by
  by_contra h
  push Not at h
  apply not_weilPositiveFull_zero
  intro f hf hfc
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  exact h R f hf fun x hx => by
    have hx' := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx'
    exact abs_le.mp hx'

/-- An autocorrelation of a test supported in `[−A, A]` vanishes at `±log n` for `n ≥ 2` when
`2A < log 2`. -/
theorem weilTest_log_eq_zero_of_lt {f : ℝ → ℂ} {A : ℝ} (hfs : tsupport f ⊆ Icc (-A) A)
    (hA : 2 * A < Real.log 2) {n : ℕ} (hn : 2 ≤ n) :
    EF.weilTest f f (Real.log n) = 0 ∧ EF.weilTest f f (-Real.log n) = 0 := by
  have hsub := tsupport_weilTest_subset_add hfs hfs
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  constructor
  · exact image_eq_zero_of_notMem_tsupport fun h => by have := (hsub h).2; linarith
  · exact image_eq_zero_of_notMem_tsupport fun h => by have := (hsub h).1; linarith

/-- **Below the first prime the weights are invisible.** -/
theorem re_weilFullFunctional_eq_zero_weight {f : ℝ → ℂ} {A : ℝ} (hfs : tsupport f ⊆ Icc (-A) A)
    (hA : 2 * A < Real.log 2) (lam : ℕ → ℝ) :
    (weilFullFunctional lam (EF.weilTest f f)).re =
      (weilFullFunctional (fun _ => 0) (EF.weilTest f f)).re := by
  rw [re_weilFullFunctional_eq_affine lam (N := 2) fun n hn => weilTest_log_eq_zero_of_lt hfs hA hn]
  simp [Finset.sum_range_succ]

/-- Below the first prime the finite-level cone is everything or nothing, decided by the
archimedean place. -/
theorem weilPositiveFullUpTo_iff_zero {A : ℝ} (hA : 2 * A < Real.log 2) (lam : ℕ → ℝ) :
    WeilPositiveFullUpTo lam A ↔ WeilPositiveFullUpTo (fun _ => 0) A := by
  unfold WeilPositiveFullUpTo
  exact forall_congr' fun f => forall_congr' fun _ => forall_congr' fun hfs => by
    rw [re_weilFullFunctional_eq_zero_weight hfs hA lam]

/-- Under RH the archimedean place is positive below the first prime. -/
theorem weilPositiveFullUpTo_zero_of_riemannHypothesis (hRH : RiemannHypothesis) {A : ℝ}
    (hA : 2 * A < Real.log 2) : WeilPositiveFullUpTo (fun _ => 0) A := by
  have hW : WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) :=
    weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr ⟨hRH, fun _ _ => rfl⟩
  refine (weilPositiveFullUpTo_iff_zero hA _).mp fun f hf hfs => hW f hf ?_
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs

/-- **Under RH the archimedean place needs the first prime to fail**: every aperture where the
Gamma factor and the pole alone are not Weil positive has `2A ≥ log 2`. -/
theorem log_two_le_of_not_weilPositiveFullUpTo_zero (hRH : RiemannHypothesis) {A : ℝ}
    (hA : ¬ WeilPositiveFullUpTo (fun _ => 0) A) : Real.log 2 ≤ 2 * A := by
  by_contra h
  exact hA (weilPositiveFullUpTo_zero_of_riemannHypothesis hRH (not_le.mp h))

/-- An autocorrelation of a test supported in `[−A, A]` vanishes at `±log n` for `n > e^{2A}`. -/
theorem weilTest_log_eq_zero_of_exp_lt {f : ℝ → ℂ} {A : ℝ} (hfs : tsupport f ⊆ Icc (-A) A)
    {n : ℕ} (hn : Real.exp (2 * A) < n) :
    EF.weilTest f f (Real.log n) = 0 ∧ EF.weilTest f f (-Real.log n) = 0 := by
  have hsub := tsupport_weilTest_subset_add hfs hfs
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn
  have hlog : 2 * A < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn
  constructor
  · exact image_eq_zero_of_notMem_tsupport fun h => by have := (hsub h).2; linarith
  · exact image_eq_zero_of_notMem_tsupport fun h => by have := (hsub h).1; linarith

/-- **The finite-level cone is local**: Weil positivity up to `A` depends only on the weights at the
integers `n ≤ e^{2A}`. The cone `C_A` lives in a space of dimension `⌊e^{2A}⌋ − 1`. -/
theorem weilPositiveFullUpTo_congr {A : ℝ} {lam lam' : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (2 * A) → lam n = lam' n) :
    WeilPositiveFullUpTo lam A ↔ WeilPositiveFullUpTo lam' A := by
  unfold WeilPositiveFullUpTo
  refine forall_congr' fun f => forall_congr' fun _ => forall_congr' fun hfs => ?_
  set N := ⌊Real.exp (2 * A)⌋₊ + 1
  have hN : ∀ n : ℕ, N ≤ n → EF.weilTest f f (Real.log n) = 0 ∧ EF.weilTest f f (-Real.log n) = 0 :=
    fun n hn => weilTest_log_eq_zero_of_exp_lt hfs (by
      have := Nat.lt_floor_add_one (Real.exp (2 * A))
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast [N] at hn'
      linarith)
  rw [re_weilFullFunctional_eq_affine lam hN, re_weilFullFunctional_eq_affine lam' hN]
  have hsum : ∑ n ∈ Finset.range N, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      ∑ n ∈ Finset.range N, (if 2 ≤ n then lam' n / Real.sqrt n else 0) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
    refine Finset.sum_congr rfl fun n hn => ?_
    split_ifs with h2
    · rw [h n h2 (by
        have hlt := Finset.mem_range.mp hn
        have : n ≤ ⌊Real.exp (2 * A)⌋₊ := by omega
        exact (Nat.le_floor_iff (Real.exp_pos _).le).mp this)]
    · rfl
  rw [hsum]

/-- **The first-fold cone is a cone in one weight**: for `log 2 ≤ 2A < log 3`, Weil positivity up to
`A` depends on the weights only through `λ(2)`. -/
theorem weilPositiveFullUpTo_iff_firstFold {A : ℝ} (hA : 2 * A < Real.log 3) (lam : ℕ → ℝ) :
    WeilPositiveFullUpTo lam A ↔ WeilPositiveFullUpTo (fun n => if n = 2 then lam 2 else 0) A := by
  refine weilPositiveFullUpTo_congr fun n hn hnA => ?_
  have hn3 : n < 3 := by
    by_contra h3
    have h3' : (3 : ℝ) ≤ n := by exact_mod_cast not_lt.mp h3
    have : Real.exp (2 * A) < 3 := (Real.exp_lt_exp.mpr hA).trans_eq (Real.exp_log (by norm_num))
    linarith
  have h2 : n = 2 := by omega
  subst h2
  simp

/-- **The finite-level cone is convex.** -/
theorem convex_setOf_weilPositiveFullUpTo (A : ℝ) :
    Convex ℝ {lam : ℕ → ℝ | WeilPositiveFullUpTo lam A} := by
  intro x hx y hy a b ha hb hab f hf hfs
  have hk := EF.weilTest_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs)
    (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs)
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hk
  have e : ∀ l : ℕ → ℝ, (weilFullFunctional l (EF.weilTest f f)).re =
      (weilFullFunctional (fun _ => 0) (EF.weilTest f f)).re -
        ∑ n ∈ Finset.range N, (if 2 ≤ n then l n / Real.sqrt n else 0) *
          (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re :=
    fun l => re_weilFullFunctional_eq_affine l hN
  have hx' := hx f hf hfs
  have hy' := hy f hf hfs
  rw [e] at hx' hy' ⊢
  have hsum : ∑ n ∈ Finset.range N, (if 2 ≤ n then (a • x + b • y) n / Real.sqrt n else 0) *
      (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re =
      a * ∑ n ∈ Finset.range N, (if 2 ≤ n then x n / Real.sqrt n else 0) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re +
      b * ∑ n ∈ Finset.range N, (if 2 ≤ n then y n / Real.sqrt n else 0) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)).re := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    · ring
  rw [hsum]
  obtain rfl : b = 1 - a := by linarith
  nlinarith [mul_nonneg ha hx', mul_nonneg hb hy']

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
