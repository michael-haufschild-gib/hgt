import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityThroughApertureThreeTenths
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurLendingOddWindowThreeHundredSixtyTwoThousandths

/-!
# Window certificates and the prime weight

The Weil functional of a prime weight `w : ℕ → ℝ` on an even test kernel `k`,

`W_w(k) = k̂(i/2) + k̂(−i/2) − Σ_{n ≥ 2} w(n) n^{−1/2} (k(log n) + k(−log n)) + (1/2π) ∫ k̂ γ`,

reads `w` only at the `n` with `log n` in the support of `k` (`weilFullFunctional_eq_of_eqOn`).

* **Prime-free windows.** A kernel supported in `(−log 2, log 2)` has the same Weil functional for
  every weight (`weilFullFunctional_eq_of_tsupport_subset`). The autocorrelation of a test supported
  in `[−3/10, 3/10]` lies there, so the aperture-`3/10` certificate of `ζ` holds verbatim for every
  prime weight (`re_weilFullFunctional_ge_of_aperture_le_threeTenths`), in particular for the
  Liouville twist `λ(n)Λ(n)` and for the integer-supported part of any Beurling system. It is a
  statement about the archimedean place and the poles and carries no information on zeros.
* **Windows through the first prime.** Below `log 3` only the atom at `2` is read, and two weights
  differ by `(w'(2) − w(2)) 2^{−1/2} (k(log 2) + k(−log 2))` (`weilFullFunctional_sub_eq_atom_two`).
  The odd window certificate on `[−181/500, 181/500]` holds for every weight with `w(2) = log 2`
  (`re_weilFullFunctional_ge_of_odd_window`); the Liouville twist reverses that atom and its odd
  window form exceeds the certificate by `√2 log 2 (k(log 2) + k(−log 2))`
  (`re_weilFullFunctional_liouvilleTwist_odd_window`), so the twisted certificate holds on every
  odd test whose correlation at the first prime is nonnegative and is undecided on the rest.
-/

open MeasureTheory Set
open GaloisForLFunctions.RHTower RHTower Zeta23

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

/-- The Liouville-twisted von Mangoldt weight `λ(n) Λ(n)`, `λ(n) = (−1)^{Ω(n)}`. -/
def liouvilleTwistedVonMangoldt (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (ArithmeticFunction.cardFactors n) * (ArithmeticFunction.vonMangoldt n : ℝ)

theorem liouvilleTwistedVonMangoldt_two : liouvilleTwistedVonMangoldt 2 = -Real.log 2 := by
  rw [liouvilleTwistedVonMangoldt, ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- **Below `log 2` the Weil functional is independent of the prime weight.** -/
theorem weilFullFunctional_eq_of_tsupport_subset {k : ℝ → ℂ} {B : ℝ} (hB : B < Real.log 2)
    (hk : tsupport k ⊆ Icc (-B) B) (w w' : ℕ → ℝ) :
    weilFullFunctional w k = weilFullFunctional w' k := by
  have h0 : ∀ n : ℕ, 2 ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hlog : Real.log 2 ≤ Real.log n :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    refine ⟨image_eq_zero_of_notMem_tsupport fun h => ?_,
      image_eq_zero_of_notMem_tsupport fun h => ?_⟩
    · linarith [(hk h).2]
    · linarith [(hk h).1]
  have hs : ∀ v : ℕ → ℝ, ∑' n : ℕ, ((if 2 ≤ n then v n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)) = 0 := by
    intro v
    have hterm : ∀ n : ℕ, ((if 2 ≤ n then v n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) = 0 := by
      intro n
      by_cases hn : 2 ≤ n
      · rw [(h0 n hn).1, (h0 n hn).2, add_zero, mul_zero]
      · rw [if_neg hn, Complex.ofReal_zero, zero_mul]
    simp only [hterm, tsum_zero]
  unfold weilFullFunctional
  rw [hs w, hs w']

/-- The autocorrelation of a test supported in `[−3/10, 3/10]` lies in the prime-free window. -/
theorem weilFullFunctional_weilTest_eq_of_aperture_le_threeTenths {f : ℝ → ℂ}
    (hfs : tsupport f ⊆ Icc (-(3 / 10)) (3 / 10)) (w w' : ℕ → ℝ) :
    weilFullFunctional w (EF.weilTest f f) = weilFullFunctional w' (EF.weilTest f f) := by
  have hk := tsupport_weilTest_subset_add hfs hfs
  have hB : (3 / 10 + 3 / 10 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  exact weilFullFunctional_eq_of_tsupport_subset hB hk w w'

/-- **The aperture-`3/10` certificate holds for every prime weight.** For every `w : ℕ → ℝ` and every
`C²` test `f` supported in `[−3/10, 3/10]`, `Re W_w(f ⋆ f̃) ≥ (1/5000) ∫ |f|²`. -/
theorem re_weilFullFunctional_ge_of_aperture_le_threeTenths (w : ℕ → ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(3 / 10)) (3 / 10)) :
    1 / 5000 * ∫ x, ‖f x‖ ^ 2 ≤ (weilFullFunctional w (EF.weilTest f f)).re := by
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f).trans hfs)
  rw [weilFullFunctional_weilTest_eq_of_aperture_le_threeTenths hfs w
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)), ← zeta_W_eq_weilFullFunctional hf hfc]
  exact zetaZeroConfig_re_W_ge_of_aperture_le_threeTenths hf hfs

/-- **Liouville twist.** The aperture-`3/10` certificate holds for the twisted weight
`λ(n) Λ(n)`, `λ(n) = (−1)^{Ω(n)}`, whose prime atoms have the opposite sign. -/
theorem re_weilFullFunctional_liouvilleTwist_ge_of_aperture_le_threeTenths {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-(3 / 10)) (3 / 10)) :
    1 / 5000 * ∫ x, ‖f x‖ ^ 2 ≤
      (weilFullFunctional liouvilleTwistedVonMangoldt (EF.weilTest f f)).re :=
  re_weilFullFunctional_ge_of_aperture_le_threeTenths _ hf hfs

/-! ## Windows through the first prime -/

/-- The Weil functional reads the weight only at the `n` with `log n` in the support of the kernel. -/
theorem weilFullFunctional_eq_of_eqOn {k : ℝ → ℂ} {B : ℝ} (hk : tsupport k ⊆ Icc (-B) B)
    {w w' : ℕ → ℝ} (hww : ∀ n : ℕ, 2 ≤ n → Real.log n ≤ B → w n = w' n) :
    weilFullFunctional w k = weilFullFunctional w' k := by
  have hterm : ∀ n : ℕ, ((if 2 ≤ n then w n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)) =
        ((if 2 ≤ n then w' n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    intro n
    by_cases hn : 2 ≤ n
    · by_cases hB : Real.log n ≤ B
      · rw [hww n hn hB]
      · have h1 : k (Real.log n) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hB (hk h).2
        have h2 : k (-Real.log n) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => hB (by linarith [(hk h).1])
        rw [h1, h2, add_zero, mul_zero, mul_zero]
    · rw [if_neg hn, if_neg hn]
  unfold weilFullFunctional
  rw [tsum_congr hterm]

private theorem log_three_gt_one : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- **Below `log 3` only the atom at `2` is read.** Two weights differ on such a kernel by
`(w'(2) − w(2)) 2^{−1/2} (k(log 2) + k(−log 2))`. -/
theorem weilFullFunctional_sub_eq_atom_two {k : ℝ → ℂ} {B : ℝ} (hk : tsupport k ⊆ Icc (-B) B)
    (hB : B < Real.log 3) (w w' : ℕ → ℝ) :
    weilFullFunctional w k - weilFullFunctional w' k =
      (((w' 2 - w 2) / Real.sqrt 2 : ℝ) : ℂ) * (k (Real.log 2) + k (-Real.log 2)) := by
  have hzero : ∀ n : ℕ, 3 ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hlog : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    refine ⟨image_eq_zero_of_notMem_tsupport fun h => ?_,
      image_eq_zero_of_notMem_tsupport fun h => ?_⟩
    · linarith [(hk h).2]
    · linarith [(hk h).1]
  have hsingle : ∀ v : ℕ → ℝ, ∑' n : ℕ, ((if 2 ≤ n then v n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)) =
        ((v 2 / Real.sqrt 2 : ℝ) : ℂ) * (k (Real.log 2) + k (-Real.log 2)) := by
    intro v
    rw [tsum_eq_single 2 fun n hn => ?_]
    · simp
    · by_cases h2 : 2 ≤ n
      · have h3 : 3 ≤ n := by omega
        rw [(hzero n h3).1, (hzero n h3).2, add_zero, mul_zero]
      · rw [if_neg h2, Complex.ofReal_zero, zero_mul]
  unfold weilFullFunctional
  rw [hsingle w, hsingle w']
  push_cast
  ring

/-- The autocorrelation of a test supported in `[−181/500, 181/500]`. -/
private theorem tsupport_weilTest_window {f : ℝ → ℂ} (hfs : tsupport f ⊆ Icc (-(181 / 500)) (181 / 500)) :
    tsupport (EF.weilTest f f) ⊆ Icc (-(181 / 500 + 181 / 500)) (181 / 500 + 181 / 500) :=
  tsupport_weilTest_subset_add hfs hfs

private theorem window_lt_log_three : (181 / 500 + 181 / 500 : ℝ) < Real.log 3 := by
  have := log_three_gt_one
  linarith

private theorem tsupport_ofReal_subset {F : ℝ → ℝ} (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    tsupport (fun x => (F x : ℂ)) ⊆ Icc (-(181 / 500)) (181 / 500) := by
  refine closure_minimal (fun x hx => ?_) isClosed_Icc
  by_contra hxI
  have hx' : 181 / 500 < |x| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hxI
    rcases hxI with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  exact hx (by simp [hsupp x hx'])

/-- The odd window certificate in Weil-functional form. -/
private theorem one_div_thousand_le_re_weilFullFunctional_vonMangoldt {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤ (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  rw [← ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
  exact ArithmeticIncidencePositivity.fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hF hFc hodd hsupp

/-- **The odd window certificate holds for every weight agreeing with `Λ` at `2`.** For every
`w : ℕ → ℝ` with `w(2) = log 2` and every odd real `C²` test `F` supported in `[−181/500, 181/500]`,
`Re W_w(F ⋆ F̃) ≥ (1/1000) ∫ F²`: the window reads the weight only at `n = 2`. -/
theorem re_weilFullFunctional_ge_of_odd_window (w : ℕ → ℝ) (hw2 : w 2 = Real.log 2) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤
      (weilFullFunctional w (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  have hk := tsupport_weilTest_window (tsupport_ofReal_subset hsupp)
  have h2 : Real.log 2 = (ArithmeticFunction.vonMangoldt 2 : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num
  rw [weilFullFunctional_eq_of_eqOn hk (w' := fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    fun n hn hlog => ?_, ← ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
  · exact ArithmeticIncidencePositivity.fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hF hFc hodd hsupp
  · have hn2 : n = 2 := by
      by_contra hne
      have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      have := Real.log_le_log (by norm_num) h3
      linarith [window_lt_log_three]
    subst hn2
    rw [hw2, h2]

/-- **The Liouville twist reverses the atom at `2`.** With `λ(n) = (−1)^{Ω(n)}` and an odd real test
supported in `[−181/500, 181/500]`, the twisted Weil functional exceeds the untwisted one by
`√2 log 2 · (k(log 2) + k(−log 2))`, `k = F ⋆ F̃`; hence the odd window certificate holds for the
twisted weight on every test whose correlation at the first prime is nonnegative. -/
theorem re_weilFullFunctional_liouvilleTwist_odd_window {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    1 / 1000 * (∫ x, F x ^ 2) + Real.sqrt 2 * Real.log 2 *
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log 2) +
          EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log 2)).re ≤
      (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  have hk := tsupport_weilTest_window (tsupport_ofReal_subset hsupp)
  have hdiff := weilFullFunctional_sub_eq_atom_two hk window_lt_log_three
    liouvilleTwistedVonMangoldt (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  have hΛ2 : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num
  have hcoef : ((ArithmeticFunction.vonMangoldt 2 : ℝ) - liouvilleTwistedVonMangoldt 2) /
      Real.sqrt 2 = Real.sqrt 2 * Real.log 2 := by
    rw [hΛ2, liouvilleTwistedVonMangoldt_two]
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hcoef] at hdiff
  have hbase := one_div_thousand_le_re_weilFullFunctional_vonMangoldt hF hFc hodd hsupp
  have hre := congrArg Complex.re hdiff
  rw [Complex.sub_re, Complex.re_ofReal_mul] at hre
  linarith

end GaloisForLFunctions.SquareRootThreshold
