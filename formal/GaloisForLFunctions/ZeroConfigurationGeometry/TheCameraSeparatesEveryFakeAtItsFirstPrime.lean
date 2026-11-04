import GaloisForLFunctions.ZeroConfigurationGeometry.ThePrimesPinEveryFinitePieceOfZeta
import GaloisForLFunctions.ZeroConfigurationGeometry.TheArithmeticPinningIsStable
import GaloisForLFunctions.SquareRootThreshold.LargeDyadicPrimeWindowsDecideTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold

/-!
# The camera separates every fake at its first prime

Two arithmetic data `λ, λ'` with the archimedean place and pole of `ζ` give arithmetic images that
differ only through the primes of the camera's range (`weilFullFunctional_sub`). The camera of
aperture `r` reads the data on `n < e^{2r}` (`arithmeticImage_congr_of_eq_below`). Here the converse
is proved, sharply and without a sign.

* **Separation just above the first disagreement** (`exists_window_arithmeticImage_ne`). If `λ` and
  `λ'` agree on `2 ≤ n < n₀` and differ at `n₀`, then for every aperture `r > ½ log n₀` the
  difference test `κ_w(t + v/2) − κ_w(t − v/2)` at lag `v = log n₀` with a bump of width
  `w < ¼ log(1 + 1/n₀)` has images differing by `2(λ(n₀) − λ'(n₀)) n₀^{−1/2} ‖κ_w‖² ≠ 0`: its kernel
  `2K(x) − K(x + v) − K(x − v)` meets the logarithm of no other integer.
* **The selectivity threshold** (`arithmeticImage_eq_iff`). The images agree on every window of
  aperture `r` exactly when `2r ≤ log n₀`.
* **The images determine the data** (`eq_of_arithmeticImage_eq`).
* **Configurations** (`exists_window_W_ne_zeta`). A tempered configuration whose image at aperture
  `r` is the arithmetic image of data first differing from `Λ` at `n₀ < e^{2r}` is not the
  configuration of `ζ`: some window of that aperture tells them apart.
* **Prime flips** (`flipData_mimic_iff`). Flipping the sign of `Λ` on the primes of a set `F` with
  least prime `p₀` gives data that the camera separates exactly above aperture `½ log p₀`, however
  sparse `F` is.

At the level of data the camera family is a complete and sharp separator: every fake with the
archimedean place and pole of `ζ` — Euler twins, flips, Beurling data — is caught exactly at its
first prime. Mimicry (`eulerColumn_mimic_iff`) lives only at the level of configurations, where the
fake's zeros can rearrange into an infinite cluster with the same image below that prime.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- `λ` and `λ'` agree on `2 ≤ n < n₀` and differ at `n₀ ≥ 2`. -/
def FirstDisagreement (lam lam' : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  2 ≤ n₀ ∧ lam n₀ ≠ lam' n₀ ∧ ∀ n, 2 ≤ n → n < n₀ → lam n = lam' n

/-- Below the first disagreement the images agree. -/
theorem arithmeticImage_eq_of_le {lam lam' : ℕ → ℝ} {n₀ : ℕ}
    (h : FirstDisagreement lam lam' n₀) {r : ℝ} (hr : 2 * r ≤ Real.log n₀) {f : ℝ → ℂ}
    (hf : ApertureWindow r f) : arithmeticImage lam f = arithmeticImage lam' f := by
  refine arithmeticImage_congr_of_eq_below (fun n hn hlog => h.2.2 n hn ?_) hf
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₀0 : (0 : ℝ) < n₀ := by exact_mod_cast (show 0 < n₀ by have := h.1; omega)
  exact_mod_cast (Real.log_lt_log_iff hn0 hn₀0).mp (hlog.trans_le hr)

/-- The autocorrelation of a window at the origin is its `L²` mass. -/
theorem weilTest_self_zero_eq (b : ℝ → ℂ) :
    EF.weilTest b b 0 = ((∫ t, ‖b t‖ ^ 2 : ℝ) : ℂ) := by
  rw [_root_.RHTower.weilTest_apply, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- **Separation just above the first disagreement.** -/
theorem exists_window_arithmeticImage_ne {lam lam' : ℕ → ℝ} {n₀ : ℕ}
    (h : FirstDisagreement lam lam' n₀) {r : ℝ} (hr : Real.log n₀ < 2 * r) :
    ∃ f, ApertureWindow r f ∧ arithmeticImage lam f ≠ arithmeticImage lam' f := by
  obtain ⟨hn₀, hne, hbelow⟩ := h
  have hn₀R : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  set v := Real.log n₀ with hvdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv2 : Real.log 2 ≤ v := Real.log_le_log (by norm_num) hn₀R
  -- the logarithmic gap to the next integer
  set g := Real.log ((n₀ : ℝ) + 1) - v with hgdef
  have hg : 0 < g := by
    have := Real.log_lt_log (by linarith) (show (n₀ : ℝ) < n₀ + 1 by linarith)
    rw [hgdef]; linarith
  set w := min (r - v / 2) (min (g / 4) (Real.log 2 / 4)) with hwdef
  have hw0 : 0 < w := lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hwa : v / 2 + w ≤ r := by have := min_le_left (r - v / 2) (min (g / 4) (Real.log 2 / 4)); linarith
  have hwg : 2 * w < g := by
    have := (min_le_right (r - v / 2) _).trans (min_le_left (g / 4) (Real.log 2 / 4)); linarith
  have hw2 : 2 * w < Real.log 2 := by
    have := (min_le_right (r - v / 2) _).trans (min_le_right (g / 4) (Real.log 2 / 4)); linarith
  have hbs : ∀ u, modScaledBump w 0 u ≠ 0 → |u| ≤ w := modScaledBump_support hw0 0
  have hbc : HasCompactSupport (modScaledBump w 0) := hasCompactSupport_of_support_subset_abs hbs
  have hbcont : Continuous (modScaledBump w 0) := (contDiff_modScaledBump_two w 0).continuous
  have hbI : tsupport (modScaledBump w 0) ⊆ Icc (-w) w := closure_minimal
    (fun u hu => abs_le.mp (hbs u hu)) isClosed_Icc
  -- the difference test at lag `log n₀`
  set f := twoBump (modScaledBump w 0) v (-1) with hfdef
  have hf : ApertureWindow r f :=
    ⟨contDiff_bumpTest (contDiff_modScaledBump_two w 0) _ _,
      (tsupport_twoBump_modScaledBump_subset hw0 (by linarith)).trans
        (Icc_subset_Icc (by linarith) hwa)⟩
  refine ⟨f, hf, fun heq => ?_⟩
  set K := EF.weilTest (modScaledBump w 0) (modScaledBump w 0) with hKdef
  have hKz : ∀ s, 2 * w < |s| → K s = 0 := fun s hs => weilTest_eq_zero_of_lt hbI hbI hs
  have hvw : 2 * w < v := by linarith
  -- the kernel at `± log n₀` is `−K(0)`
  have hkv : EF.weilTest f f v = -K 0 := by
    rw [hfdef, weilTest_twoBump_neg_one hbcont hbc, ← hKdef, hKz v (by rw [abs_of_pos (by linarith)]; exact hvw),
      hKz (v + v) (by rw [abs_of_pos (by linarith)]; linarith), sub_self]
    ring
  have hkmv : EF.weilTest f f (-v) = -K 0 := by
    rw [hfdef, weilTest_twoBump_neg_one hbcont hbc, ← hKdef,
      hKz (-v) (by rw [abs_neg, abs_of_pos (by linarith)]; exact hvw), neg_add_cancel,
      hKz (-v - v) (by rw [show -v - v = -(v + v) by ring, abs_neg, abs_of_pos (by linarith)]; linarith)]
    ring
  -- every other integer of the range is invisible
  have hfar : ∀ n : ℕ, n₀ + 1 ≤ n →
      EF.weilTest f f (Real.log n) = 0 ∧ EF.weilTest f f (-Real.log n) = 0 := by
    intro n hn
    have hnR : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hlog : Real.log ((n₀ : ℝ) + 1) ≤ Real.log n := Real.log_le_log (by linarith) hnR
    have hpos : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have h0 : 2 * w < |Real.log n| := by rw [abs_of_nonneg hpos]; linarith
    have h1 : 2 * w < |Real.log n - v| := by rw [abs_of_nonneg (by linarith)]; linarith
    have h2 : 2 * w < |Real.log n + v| := by rw [abs_of_nonneg (by linarith)]; linarith
    refine ⟨weilTest_twoBump_eq_zero hbs v (-1) h0 h1 h2, weilTest_twoBump_eq_zero hbs v (-1)
      (by rwa [abs_neg]) (by rwa [show -Real.log n - v = -(Real.log n + v) by ring, abs_neg])
      (by rwa [show -Real.log n + v = -(Real.log n - v) by ring, abs_neg])⟩
  have hk : ∀ s, 2 * r < |s| → EF.weilTest f f s = 0 := fun s hs => weilTest_eq_zero_of_lt hf.2 hf.2 hs
  have hdiff := weilFullFunctional_sub lam lam' hk
  have hmem : n₀ ∈ primeRange r := by
    rw [primeRange, Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.le_floor ?_
    have hn₀0 : (0 : ℝ) < n₀ := by linarith
    rw [← Real.exp_log hn₀0]
    exact (Real.exp_lt_exp.mpr hr).le
  rw [Finset.sum_eq_single_of_mem n₀ hmem fun n _ hn => ?_] at hdiff
  · have h0 : arithmeticImage lam f - arithmeticImage lam' f = 0 := sub_eq_zero.mpr heq
    simp only [arithmeticImage] at h0
    rw [hdiff, hkv, hkmv, hKdef, weilTest_self_zero_eq] at h0
    have hmass := integral_norm_sq_modScaledBump_pos hw0
    have hw : primeWeight lam n₀ - primeWeight lam' n₀ ≠ 0 := by
      simp only [primeWeight, if_pos hn₀, ← sub_div]
      exact div_ne_zero (sub_ne_zero.mpr hne) (Real.sqrt_pos.mpr (by linarith)).ne'
    have h0' : (((2 * (primeWeight lam n₀ - primeWeight lam' n₀) *
        ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ)) : ℂ) = 0 := by
      rw [← h0]; push_cast; ring
    exact mul_ne_zero (mul_ne_zero two_ne_zero hw) hmass.ne' (Complex.ofReal_eq_zero.mp h0')
  · rcases Nat.lt_or_ge n n₀ with hlt | hge
    · by_cases h2 : 2 ≤ n
      · simp only [primeWeight, if_pos h2, hbelow n h2 hlt, sub_self, Complex.ofReal_zero, zero_mul]
      · simp only [primeWeight, if_neg h2, sub_self, Complex.ofReal_zero, zero_mul]
    · obtain ⟨e1, e2⟩ := hfar n (by omega)
      rw [e1, e2, add_zero, mul_zero]

/-- **The selectivity threshold.** The camera of aperture `r` cannot tell `λ` from `λ'` exactly when
`2r ≤ log n₀`, `n₀` the first disagreement. -/
theorem arithmeticImage_eq_iff {lam lam' : ℕ → ℝ} {n₀ : ℕ} (h : FirstDisagreement lam lam' n₀)
    (r : ℝ) :
    (∀ f, ApertureWindow r f → arithmeticImage lam f = arithmeticImage lam' f) ↔
      2 * r ≤ Real.log n₀ := by
  refine ⟨fun hall => ?_, fun hr f hf => arithmeticImage_eq_of_le h hr hf⟩
  by_contra hlt
  obtain ⟨f, hf, hne⟩ := exists_window_arithmeticImage_ne h (not_le.mp hlt)
  exact hne (hall f hf)

/-- **The images determine the data.** Equal arithmetic images on every window force equal data on
`n ≥ 2`. -/
theorem eq_of_arithmeticImage_eq {lam lam' : ℕ → ℝ}
    (h : ∀ r f, ApertureWindow r f → arithmeticImage lam f = arithmeticImage lam' f) :
    ∀ n, 2 ≤ n → lam n = lam' n := by
  by_contra hcon
  push Not at hcon
  have hex : ∃ n, 2 ≤ n ∧ lam n ≠ lam' n := hcon
  classical
  set n₀ := Nat.find hex
  have hfirst : FirstDisagreement lam lam' n₀ :=
    ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun n hn hlt => by
      by_contra hne
      exact Nat.find_min hex hlt ⟨hn, hne⟩⟩
  have hl : 0 < Real.log n₀ :=
    Real.log_pos (by exact_mod_cast (show 1 < n₀ by have := hfirst.1; omega))
  obtain ⟨f, hf, hne⟩ := exists_window_arithmeticImage_ne hfirst (r := Real.log n₀) (by linarith)
  exact hne (h _ f hf)

/-- **A fake is not the configuration of `ζ`.** A tempered configuration whose image at aperture
`r` is the arithmetic image of data first differing from `Λ` at `n₀ < e^{2r}` differs from the zeros
of `ζ` on some window of aperture `r`. -/
theorem exists_window_W_ne_zeta {Z : ZeroConfig} {lam : ℕ → ℝ} {n₀ : ℕ}
    (h : FirstDisagreement (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) lam n₀) {r : ℝ}
    (hr : Real.log n₀ < 2 * r) (hW : ∀ f, ApertureWindow r f → Z.W f f = arithmeticImage lam f) :
    ∃ f, ApertureWindow r f ∧ Z.W f f ≠ zetaZeroConfig.W f f := by
  obtain ⟨f, hf, hne⟩ := exists_window_arithmeticImage_ne h hr
  refine ⟨f, hf, fun heq => hne ?_⟩
  rw [← zeta_W_eq_arithmeticImage hf.1 hf.hasCompactSupport, ← heq, hW f hf]

/-! ### Prime flips -/

/-- The data of `ζ` with the sign of `Λ` flipped on the prime powers of the primes in `F`. -/
def flipData (F : Set ℕ) (n : ℕ) : ℝ :=
  if ∃ p ∈ F, p ∣ n then -(ArithmeticFunction.vonMangoldt n : ℝ)
  else (ArithmeticFunction.vonMangoldt n : ℝ)

/-- A flip set first differs from `Λ` at its least prime. -/
theorem flipData_firstDisagreement {F : Set ℕ} {p₀ : ℕ} (hp₀ : p₀.Prime) (hmem : p₀ ∈ F)
    (hmin : ∀ p ∈ F, p₀ ≤ p) :
    FirstDisagreement (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (flipData F) p₀ := by
  refine ⟨hp₀.two_le, ?_, fun n hn hlt => ?_⟩
  · have hpos : 0 < (ArithmeticFunction.vonMangoldt p₀ : ℝ) := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp₀]
      exact Real.log_pos (by exact_mod_cast hp₀.one_lt)
    rw [flipData, if_pos ⟨p₀, hmem, dvd_rfl⟩]
    linarith
  · have hno : ¬ ∃ p ∈ F, p ∣ n := fun ⟨p, hp, hpn⟩ =>
      absurd ((hmin p hp).trans (Nat.le_of_dvd (by omega) hpn)) (not_le.mpr hlt)
    rw [flipData, if_neg hno]

/-- **Prime flips are seen exactly above their least prime.** However sparse `F` is, the camera of
aperture `r` separates the flipped data from `Λ` exactly when `2r > log p₀`. -/
theorem flipData_mimic_iff {F : Set ℕ} {p₀ : ℕ} (hp₀ : p₀.Prime) (hmem : p₀ ∈ F)
    (hmin : ∀ p ∈ F, p₀ ≤ p) (r : ℝ) :
    (∀ f, ApertureWindow r f →
        arithmeticImage (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f =
          arithmeticImage (flipData F) f) ↔ 2 * r ≤ Real.log p₀ :=
  arithmeticImage_eq_iff (flipData_firstDisagreement hp₀ hmem hmin) r

end GaloisForLFunctions.ZeroConfigurationGeometry
