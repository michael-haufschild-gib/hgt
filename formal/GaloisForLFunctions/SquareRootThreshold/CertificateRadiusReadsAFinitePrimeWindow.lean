import GaloisForLFunctions.SquareRootThreshold.PositionAndDepthShareOneNyquistAperture
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThreeTenthsSharpGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeEvenPartOddWindowNineTwentyFifths

/-!
# A certificate of radius `R` reads the primes below `e^{2R}`

Pointwise, Schur and gauge certificates of Weil positivity hold on tests supported in a window
`[−R, R]`. On the weight side the Nyquist law says what such a window reads. The full Weil
functional of `ζ`'s archimedean datum with prime weights `lam`
(`weilFullFunctional lam (f ⋆ f̃)`) pairs the weights against the autocorrelation `f ⋆ f̃`, which
vanishes at every lag `|v| ≥ 2R`. Hence:

* **Finite prime window** (`weilFullFunctional_weilTest_congr_of_agree_below`). Two weights that
  agree on `2 ≤ n < e^{2R}` have the same functional on every test of aperture `R`.
* **Flat regime** (`weilFullFunctional_weilTest_eq_of_two_mul_le_log_two`). For `2R ≤ log 2` no
  weight is read: the functional of every weight equals the zero side of `ζ`.
* **The certificates and the first prime.** The window of the all-test certificate lies below the
  Nyquist aperture `(log 2)/2` of the first prime, the window of the odd certificate above it:
  `3/10 < (log 2)/2 < 9/25` (`three_tenths_lt_half_log_two`, `half_log_two_lt_nine_twenty_fifths`).
  So the all-test certificate certifies every weight
  (`weilFullFunctional_re_ge_of_support_le_threeTenths`), and the odd certificate certifies every
  weight with the von Mangoldt value at `2` (`weilFullFunctional_re_ge_of_odd_support_le_nineTwentyFifths`):
  the pointwise route has read exactly one prime.
* **Mimicry at every radius** (`exists_weight_not_weilPositiveFull_eq_zeta_W_on_aperture`). For
  every `R` a weight `lam ≥ Λ`, differing from `Λ` at one index above `e^{2R}`, has the functional
  of `ζ` on every test of aperture `R` and is not Weil-positive, by the rigidity of the full cone
  (`eq_vonMangoldt_of_weilPositiveFull_of_ge`).

The full Weil cone is the point `Λ` and its membership is RH
(`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`); a certificate of radius `R` is a
statement about the Toeplitz section of the weights below `e^{2R}`, shared with weights outside the
cone. This is the depth face of the Nyquist law on the weight side: the lattice of ordinate
spacing `2π/L` mimics the on-line lattice through aperture `L/2`, and a weight modified above
`e^{2R}` mimics `Λ` through aperture `R`.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticPositivityTheory

/-! ### The finite prime window of an aperture -/

/-- Two weights that agree on `2 ≤ n < e^{2R}` have the same full Weil functional on every
autocorrelation of a `C²` test supported in `[−R, R]`. -/
theorem weilFullFunctional_weilTest_congr_of_agree_below {lam lam' : ℕ → ℝ} {R : ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → Real.log n < 2 * R → lam n = lam' n) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-R) R) :
    weilFullFunctional lam (EF.weilTest f f) = weilFullFunctional lam' (EF.weilTest f f) := by
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))) =
      ∑' n : ℕ, ((if 2 ≤ n then lam' n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n)) := by
    refine tsum_congr fun n => ?_
    by_cases hn : 2 ≤ n
    · by_cases hlog : Real.log n < 2 * R
      · rw [h n hn hlog]
      · have hv : 2 * R ≤ |Real.log n| := by
          rw [abs_of_nonneg (Real.log_natCast_nonneg n)]
          exact not_lt.mp hlog
        have hv' : 2 * R ≤ |-Real.log n| := by rwa [abs_neg]
        rw [weilTest_eq_zero_of_two_mul_le hf.continuous hfs hv,
          weilTest_eq_zero_of_two_mul_le hf.continuous hfs hv']
        simp
    · simp [hn]
  unfold weilFullFunctional
  rw [hsum]

/-- **Flat regime.** Below the Nyquist aperture `(log 2)/2` of the first prime no weight is read:
on every autocorrelation of a `C²` test supported in `[−R, R]`, `2R ≤ log 2`, the full Weil
functional of every weight equals the zero side of `ζ`. -/
theorem weilFullFunctional_weilTest_eq_of_two_mul_le_log_two (lam : ℕ → ℝ) {R : ℝ}
    (hR : 2 * R ≤ Real.log 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-R) R) :
    weilFullFunctional lam (EF.weilTest f f) = zetaZeroConfig.W f f := by
  rw [zeta_W_eq_weilFullFunctional hf (hasCompactSupport_of_tsupport_subset_Icc hfs)]
  refine weilFullFunctional_weilTest_congr_of_agree_below (fun n hn hlog => ?_) hf hfs
  exfalso
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  linarith

/-! ### The certificates and the first prime -/

theorem three_tenths_lt_half_log_two : (3 / 10 : ℝ) < Real.log 2 / 2 := by
  have := Real.log_two_gt_d9
  linarith

theorem half_log_two_lt_nine_twenty_fifths : Real.log 2 / 2 < 9 / 25 := by
  have := Real.log_two_lt_d9
  linarith

theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have h := Real.exp_one_lt_d9
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) (by linarith)

/-- **The all-test certificate certifies every weight.** On tests supported in `[−3/10, 3/10]`,
below the Nyquist aperture of the first prime, the full Weil functional of every weight sequence
is coercive. -/
theorem weilFullFunctional_re_ge_of_support_le_threeTenths (lam : ℕ → ℝ) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Icc (-(3 / 10)) (3 / 10)) :
    1 / 5000 * ∫ x, ‖g x‖ ^ 2 ≤ (weilFullFunctional lam (EF.weilTest g g)).re := by
  have h := three_tenths_lt_half_log_two
  rw [weilFullFunctional_weilTest_eq_of_two_mul_le_log_two lam (by linarith) hg hgs]
  exact zetaZeroConfig_re_W_ge_of_support_le_threeTenths hg hgs

/-- **The odd certificate reads one prime.** On odd tests supported in `[−9/25, 9/25]`, past the
Nyquist aperture of the first prime and below that of the second, the full Weil functional of
every weight with the von Mangoldt value at `2` is coercive. -/
theorem weilFullFunctional_re_ge_of_odd_support_le_nineTwentyFifths {lam : ℕ → ℝ}
    (h2 : lam 2 = ArithmeticFunction.vonMangoldt 2) {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 9 / 25 < |x| → F x = 0) :
    1 / 1000 * ∫ x, F x ^ 2 ≤
      (weilFullFunctional lam (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  have h := fullZeroForm_ge_of_odd_support_le_nineTwentyFifths hF hFc hodd hsupp
  rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc] at h
  have hFd : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hfs : tsupport (fun x => (F x : ℂ)) ⊆ Icc (-(9 / 25)) (9 / 25) := by
    refine closure_minimal ?_ isClosed_Icc
    intro x hx
    rw [Function.mem_support] at hx
    have hx' : ¬ 9 / 25 < |x| := fun hlt => hx (by simp [hsupp x hlt])
    exact abs_le.mp (not_lt.mp hx')
  rwa [weilFullFunctional_weilTest_congr_of_agree_below (lam' := lam) (fun n hn hlt => ?_) hFd
    hfs] at h
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · have : n = 2 := by omega
    rw [this]
    exact h2.symm
  · exfalso
    have h3 : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
    have := one_lt_log_three
    linarith

/-! ### Mimicry at every radius -/

/-- **Every radius admits a non-positive mimic of `ζ`.** For every `R` there is a weight
`lam ≥ Λ`, differing from `Λ` at one index above `e^{2R}`, hence not Weil-positive, whose full
Weil functional agrees with the zero side of `ζ` on every autocorrelation of a `C²` test
supported in `[−R, R]`. -/
theorem exists_weight_not_weilPositiveFull_eq_zeta_W_on_aperture (R : ℝ) :
    ∃ lam : ℕ → ℝ, (∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n) ∧
      (∃ n, 2 ≤ n ∧ lam n ≠ ArithmeticFunction.vonMangoldt n) ∧ ¬ WeilPositiveFull lam ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-R) R →
        weilFullFunctional lam (EF.weilTest f f) = zetaZeroConfig.W f f := by
  set n₀ : ℕ := ⌈Real.exp (2 * R)⌉₊ + 1 with hn₀
  have hceil : 0 < ⌈Real.exp (2 * R)⌉₊ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hn₀2 : 2 ≤ n₀ := by omega
  have hlog : 2 * R ≤ Real.log n₀ := by
    have h1 : Real.exp (2 * R) ≤ n₀ := by
      have h2 := Nat.le_ceil (Real.exp (2 * R))
      have h3 : ((⌈Real.exp (2 * R)⌉₊ : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast Nat.le_succ _
      linarith
    calc 2 * R = Real.log (Real.exp (2 * R)) := (Real.log_exp _).symm
      _ ≤ Real.log n₀ := Real.log_le_log (Real.exp_pos _) h1
  set lam : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + if n = n₀ then 1 else 0
    with hlam
  have hge : ∀ n, 2 ≤ n → (ArithmeticFunction.vonMangoldt n : ℝ) ≤ lam n := by
    intro n _
    simp only [hlam]
    split_ifs <;> linarith
  have hne : lam n₀ ≠ ArithmeticFunction.vonMangoldt n₀ := by
    simp [hlam]
  refine ⟨lam, hge, ⟨n₀, hn₀2, hne⟩, fun hW => hne (eq_vonMangoldt_of_weilPositiveFull_of_ge hW hge
    n₀ hn₀2), fun f hf hfs => ?_⟩
  rw [zeta_W_eq_weilFullFunctional hf (hasCompactSupport_of_tsupport_subset_Icc hfs)]
  refine weilFullFunctional_weilTest_congr_of_agree_below (fun n hn hlt => ?_) hf hfs
  have hnn : n ≠ n₀ := by
    intro h
    rw [h] at hlt
    linarith
  simp [hlam, hnn]

/-- **The pointwise face of the Nyquist law.** The all-test window lies below the Nyquist aperture
of the first prime and the odd window above it; the all-test certificate holds for every weight
and the odd certificate for every weight with the von Mangoldt value at `2`; and at every radius
some weight outside the Weil cone has the functional of `ζ`. -/
theorem certificate_radius_reads_finite_prime_window :
    ((3 / 10 : ℝ) < Real.log 2 / 2 ∧ Real.log 2 / 2 < 9 / 25) ∧
    (∀ lam : ℕ → ℝ, ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-(3 / 10)) (3 / 10) →
      1 / 5000 * ∫ x, ‖g x‖ ^ 2 ≤ (weilFullFunctional lam (EF.weilTest g g)).re) ∧
    (∀ lam : ℕ → ℝ, lam 2 = ArithmeticFunction.vonMangoldt 2 → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F →
      HasCompactSupport F → (∀ x, F (-x) = -F x) → (∀ x, 9 / 25 < |x| → F x = 0) →
      1 / 1000 * ∫ x, F x ^ 2 ≤
        (weilFullFunctional lam (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re) ∧
    ∀ R : ℝ, ∃ lam : ℕ → ℝ, ¬ WeilPositiveFull lam ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
      tsupport f ⊆ Icc (-R) R → weilFullFunctional lam (EF.weilTest f f) = zetaZeroConfig.W f f :=
  ⟨⟨three_tenths_lt_half_log_two, half_log_two_lt_nine_twenty_fifths⟩,
    fun lam _ hg hgs => weilFullFunctional_re_ge_of_support_le_threeTenths lam hg hgs,
    fun _ h2 _ hF hFc hodd hsupp =>
      weilFullFunctional_re_ge_of_odd_support_le_nineTwentyFifths h2 hF hFc hodd hsupp,
    fun R => by
      obtain ⟨lam, -, -, hW, hmim⟩ := exists_weight_not_weilPositiveFull_eq_zeta_W_on_aperture R
      exact ⟨lam, hW, hmim⟩⟩

end GaloisForLFunctions.SquareRootThreshold
