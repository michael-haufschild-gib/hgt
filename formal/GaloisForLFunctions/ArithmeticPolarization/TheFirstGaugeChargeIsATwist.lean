import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity
import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight
import GaloisForLFunctions.ArithmeticPolarization.ThePriceOfEllipticLocalization

/-!
# The first gauge charge is a twist

Where does unconditional Weil positivity first become gauge charged? The first sign-changing
atom is the flip of `Λ(2)`, the Liouville twist on windows that read only the prime `2`.

* **The flip at `2` is the archimedean twist at `γ₂ = π / log 2`** (`exp_twist_log_two`,
  `weilFullFunctional_liouville_eq_twist`). On every kernel that vanishes at `± log n` for `n ≥ 3`,
  the Weil functional of the Liouville weight equals the Weil functional of `ζ` at the twisted
  kernel `e^{−iγ₂u} k`, plus the explicit archimedean difference `arch(k) − arch(e^{−iγ₂u}k)` and
  the polar difference. On autocorrelations of tests this reads
  `W_λ(f) = W_ζ(e^{−iγ₂u} f) + Δ_arch(f) + Δ_pole(f)` (`liouville_window_eq_zeta_twisted`): the
  first gauge charge of `ζ` is `ζ`'s own form at height `π / log 2`, corrected by the shifted Gamma
  factor and the shifted poles. Separating `ζ` from its twin on that window is a comparison of
  `ζ` with itself at two heights.
* **The second gauge charge is not a twist** (`not_twist_flips_two_and_three`): no ordinate flips
  the atoms at `2` and `3` simultaneously, since `log 3 / log 2` is irrational. From the second
  prime on, the Liouville point of the gauge torus is off the archimedean line: gauge charge
  beyond the first prime is not archimedean.
-/

open Complex MeasureTheory
open scoped ComplexConjugate ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open Zeta23 SquareRootThreshold

/-- The ordinate `γ₂ = π / log 2` at which the twist flips the atom at `2`. -/
def γ₂ : ℝ := Real.pi / Real.log 2

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- `2^{∓iγ₂} = −1`. -/
theorem exp_twist_log_two :
    Complex.exp (-(γ₂ * I * Real.log 2)) = -1 ∧ Complex.exp (γ₂ * I * Real.log 2) = -1 := by
  have h : (γ₂ : ℂ) * Real.log 2 = Real.pi := by
    have hl : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast log_two_pos'.ne'
    rw [γ₂]; push_cast; field_simp
  constructor
  · rw [show -(↑γ₂ * I * ↑(Real.log 2)) = -(↑Real.pi * I) by rw [← h]; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; norm_num
  · rw [show ↑γ₂ * I * ↑(Real.log 2) = ↑Real.pi * I by rw [← h]; ring, Complex.exp_pi_mul_I]

/-- The pole terms `k̂(i/2) + k̂(−i/2)`. -/
def poleTerms (k : ℝ → ℂ) : ℂ := paperFT k (I / 2) + paperFT k (-I / 2)

/-- The archimedean term `(1/2π) ∫ k̂(r) (Re ψ(¼ + ir/2) − log π) dr`. -/
def archTerm (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)

/-- **The flip at `2` is the twist at `γ₂`.** On kernels reading only the atom at `2`, the Weil
functional of the Liouville weight is the Weil functional of `ζ` at the twisted kernel plus the
polar and archimedean differences. -/
theorem weilFullFunctional_liouville_eq_twist {k : ℝ → ℂ}
    (hk : ∀ n : ℕ, 3 ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0) :
    RHTower.weilFullFunctional liouvilleTwistedVonMangoldt k =
      RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (twist γ₂ k)
        + (poleTerms k - poleTerms (twist γ₂ k)) + (archTerm k - archTerm (twist γ₂ k)) := by
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then liouvilleTwistedVonMangoldt n / Real.sqrt n else 0 : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n))) =
      ∑' n : ℕ, ((if 2 ≤ n then (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 : ℝ) : ℂ)
      * (twist γ₂ k (Real.log n) + twist γ₂ k (-Real.log n)) := by
    refine tsum_congr fun n => ?_
    rcases lt_trichotomy n 2 with hn | rfl | hn
    · simp [show ¬ 2 ≤ n by omega]
    · obtain ⟨h1, h2⟩ := exp_twist_log_two
      simp only [twist, show (2 : ℕ) ≤ 2 from le_rfl, if_true, Nat.cast_ofNat,
        liouvilleTwistedVonMangoldt_two, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
        Complex.ofReal_neg, mul_neg, neg_mul, neg_neg, h1, h2]
      push_cast; ring
    · obtain ⟨h1, h2⟩ := hk n hn
      simp [twist, h1, h2]
  simp only [RHTower.weilFullFunctional, poleTerms, archTerm, hsum]
  ring

/-- **The first gauge charge on autocorrelations.** For a `C²` compactly supported test whose
autocorrelation reads only the atom at `2`, the Liouville form is `ζ`'s form at height `γ₂` plus
explicit archimedean and polar corrections. -/
theorem liouville_window_eq_zeta_twisted {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f)
    (hk : ∀ n : ℕ, 3 ≤ n → EF.weilTest f f (Real.log n) = 0 ∧ EF.weilTest f f (-Real.log n) = 0) :
    RHTower.weilFullFunctional liouvilleTwistedVonMangoldt (EF.weilTest f f) =
      zetaZeroConfig.W (twist γ₂ f) (twist γ₂ f)
        + (poleTerms (EF.weilTest f f) - poleTerms (twist γ₂ (EF.weilTest f f)))
        + (archTerm (EF.weilTest f f) - archTerm (twist γ₂ (EF.weilTest f f))) := by
  rw [weilFullFunctional_liouville_eq_twist hk,
    RHTower.zeta_W_eq_weilFullFunctional (contDiff_twist hf γ₂) (hasCompactSupport_twist hfc γ₂),
    weilTest_twist]

/-- **The second gauge charge is not a twist.** No ordinate gives the phases `−1` at both `2` and
`3`: `cos(γ log 2) = cos(γ log 3) = −1` would make `log 3 / log 2` a ratio of odd integers. -/
theorem not_twist_flips_two_and_three (γ : ℝ) :
    ¬ (Real.cos (γ * Real.log 2) = -1 ∧ Real.cos (γ * Real.log 3) = -1) := by
  rintro ⟨h2, h3⟩
  rw [Real.cos_eq_neg_one_iff] at h2 h3
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := h3
  have hl2 : 0 < Real.log 2 := log_two_pos'
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- `(2a + 1) log 3 = (2b + 1) log 2`
  have hrel : ((2 * a + 1 : ℤ) : ℝ) * Real.log 3 = ((2 * b + 1 : ℤ) : ℝ) * Real.log 2 := by
    have e : Real.pi * (((2 * a + 1 : ℤ) : ℝ) * Real.log 3 - ((2 * b + 1 : ℤ) : ℝ) * Real.log 2) = 0 := by
      push_cast
      linear_combination (Real.log 3) * ha - (Real.log 2) * hb
    have := (mul_eq_zero.mp e).resolve_left Real.pi_ne_zero
    linarith
  -- both odd integers have the same sign; pass to absolute values
  have hpos : (0 < 2 * a + 1 ∧ 0 < 2 * b + 1) ∨ (2 * a + 1 < 0 ∧ 2 * b + 1 < 0) := by
    rcases lt_or_gt_of_ne (show (2 * a + 1 : ℤ) ≠ 0 by omega) with h | h
    · right; refine ⟨h, ?_⟩
      have : ((2 * a + 1 : ℤ) : ℝ) * Real.log 3 < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast h) hl3
      have : ((2 * b + 1 : ℤ) : ℝ) < 0 := by nlinarith
      exact_mod_cast this
    · left; refine ⟨h, ?_⟩
      have : 0 < ((2 * a + 1 : ℤ) : ℝ) * Real.log 3 := mul_pos (by exact_mod_cast h) hl3
      have : (0 : ℝ) < ((2 * b + 1 : ℤ) : ℝ) := by nlinarith
      exact_mod_cast this
  have habs : (((2 * b + 1).natAbs : ℕ) : ℝ) * Real.log 2 =
      (((2 * a + 1).natAbs : ℕ) : ℝ) * Real.log 3 := by
    rcases hpos with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
    · rw [Nat.cast_natAbs, Nat.cast_natAbs, abs_of_pos (by exact_mod_cast h1'),
        abs_of_pos (by exact_mod_cast h1)]
      linarith
    · rw [Nat.cast_natAbs, Nat.cast_natAbs, abs_of_neg (by exact_mod_cast h1'),
        abs_of_neg (by exact_mod_cast h1)]
      push_cast at hrel ⊢
      linarith
  have hpow : (2 : ℝ) ^ (2 * b + 1).natAbs = 3 ^ (2 * a + 1).natAbs := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ (2 * b + 1).natAbs),
      ← Real.exp_log (by positivity : (0 : ℝ) < 3 ^ (2 * a + 1).natAbs), Real.log_pow, Real.log_pow,
      habs]
  exact two_pow_ne_three_pow (by omega) hpow

end GaloisForLFunctions.ArithmeticPolarization
