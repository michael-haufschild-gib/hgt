import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactFullWeilQuantitativeSmoothing
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalCollaredFirstVariation
import GaloisForLFunctions.BiarithmeticGaugeGeometry.QuantitativeCatalanDiophantineRepulsion
import GaloisForLFunctions.ArithmeticOrientationTheory.CosetToeplitzDominanceAndShiftedPairSelectivity
import GaloisForLFunctions.ArithmeticOrientationTheory.ContinuumTowerReflectionCholesky
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Two-Prime Catalan Separation on `[-23/40, 23/40]` and the Lattice-to-Continuum Prime-Tower Obstruction

This module resolves Question 5(B) (two-prime gauge separation on `[-23/40, 23/40]` and
archimedean-free finite Catalan separation) and Question 6 (sub-exponential cell transfer from
lattice to continuum prime towers):

1. **Archimedean-free finite Catalan `{2, 3, 4}` separators (`catalanSuccessorSquareForm`,
   `catalanKroneckerTwistDefect`, `catalan_finite_gauge_separation`):**
   - Because `3 + 1 = 4 = 2²` has `Ω(4) = 2` (even) while `Ω(2) = 1` (odd), the successor-square
     bilinear form `catalanSuccessorSquareForm w := w 2 * w (3 + 1)` evaluates to `-(log 2)² < 0`
     on `liouvilleTwistedVonMangoldt`, whereas across the entire real scale-twist family
     `scaleTwistedVonMangoldt σ n = n^σ Λ(n)` (`σ ∈ ℝ`, with zero archimedean `log γ` subsidy)
     it evaluates to `+8^σ (log 2)² > 0`.
   - On `{2, 3}` (`2 + 1 = 3`), `catalanKroneckerTwistDefect w γ` vanishes at `γ = γ₀` for every
     ordinate twist `cos(γ₀ log n) Λ(n)` (`γ₀ ∈ ℝ`, including `Λ` at `γ₀ = 0`), while on
     `liouvilleTwistedVonMangoldt` it satisfies the explicit Diophantine lower bound
     `catalanKroneckerTwistDefect liouvilleTwistedVonMangoldt γ ≥ (1 / 5000) exp(-2 |γ|) > 0`
     for every `γ ∈ ℝ`, forcing any `ε`-approximating ordinate above conductor height
     `|γ| ≥ (1 / 2) log(1 / (5000 ε))`.

2. **Variational ground eigenvalue on `[-23/40, 23/40]` and simultaneous smooth separation
   (`liouvilleWindowGroundEigenvalue`, `bddBelow_liouvilleWindowRayleighSet`,
   `exists_smooth_odd_twentyThreeFortieths_zeta_pos_liouville_neg`,
   `liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths`):**
   Defines the normalized Rayleigh ground eigenvalue `liouvilleWindowGroundEigenvalue r` on
   `C²_c([-r, r])`, proves unconditional boundedness from below for every `r > 0`, and evaluates
   mollifications of the explicit odd profile `u ↦ u³ ((27/50)² - u²) 1_{[-27/50, 27/50]}(u)` to
   exhibit a single odd `F ∈ C²_c([-23/40, 23/40])` satisfying simultaneously
   `(1 / 25) ∫ F² < Re W_ζ(F ⋆ F̃)` and `Re W_{λΛ}(F ⋆ F̃) < -(3 / 10) ∫ F² < 0`, whence
   `liouvilleWindowGroundEigenvalue (23 / 40) < -(3 / 10) < 0`.

3. **Lattice-to-continuum prime-tower obstruction & pole-neutralized width equivalence
   (`towerOddPrimeSide_eq_zero_of_lt`, `not_continuumPrimeTower_subexponential_dyadicH1`,
   `continuum_poleNeutralized_width_equivalence`):**
   - On the integer lattice `[1, X]`, every prime `p > X` satisfies `towerOddPrimeSide q X p K = 0`
     identically because `p` has no proper integer divisors in `[2, X]`.
   - On the half-line continuum `[0, A]`, translated smooth bumps `edgeTowerBump A` of width
     `1 / 2 < log 2` near `A` have `A`-uniformly bounded dyadic Sobolev norm `dyadicH1NormSq F_A`,
     identically zero same-side ratio correlations across all primes, and off-lattice reflected
     crossings summing to `≤ -c₀ e^A` via Chebyshev's prime theorem, unconditionally refuting
     `-C_σ e^{2σ A} dyadicH1NormSq F` on `continuumPrimeTower` for **every** `σ < 1 / 2`.
   - Once the rank-one `s = 1` Chebyshev pole is neutralized in `scalingSubsurface (oddRealTestsAt A)`,
     the exponential Sobolev floor `-C e^{2β A} dyadicH1NormSq F` (`∀ β > σ`) is unconditionally
     equivalent to `zetaZeroWidth ≤ σ`.
-/

open MeasureTheory Set Filter Finset Asymptotics
open scoped BigOperators Topology CompactlySupported Chebyshev
open _root_.Zeta23 _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.ArchimedeanExactForm _root_.RHTower.CHMDDoobGraph
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.BiarithmeticGaugeGeometry
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws

/-! ## §1. Archimedean-Free Finite Catalan `{2, 3, 4}` Separators (Question 5B) -/

/-- Real scale twist `n^σ Λ(n)` (`σ ∈ ℝ`) of the von Mangoldt weight, carrying zero archimedean
`log γ` subsidy. -/
def scaleTwistedVonMangoldt (σ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ σ * (ArithmeticFunction.vonMangoldt n : ℝ)

/-- Real ordinate twist `cos(γ log n) Λ(n)` (`γ ∈ ℝ`) of the von Mangoldt weight (`γ = 0` is `Λ`). -/
def ordinateTwistedVonMangoldt (γ : ℝ) (n : ℕ) : ℝ :=
  Real.cos (γ * Real.log n) * (ArithmeticFunction.vonMangoldt n : ℝ)

/-- **Catalan Successor-Square Bilinear Form (`3 + 1 = 4 = 2²`):**
Reads `w` only at `2` and the successor `3 + 1 = 4`, with zero archimedean Gamma/digamma input. -/
def catalanSuccessorSquareForm (w : ℕ → ℝ) : ℝ :=
  w 2 * w (3 + 1)

/-- **Catalan–Kronecker Twist Defect on `{2, 3}` (`2 + 1 = 3`):**
Measures the squared prime-phase deviation on `{2, 3}` from the archimedean ordinate twist `γ`,
with zero archimedean `log γ` energy subsidy. -/
def catalanKroneckerTwistDefect (w : ℕ → ℝ) (γ : ℝ) : ℝ :=
  (w 2 / Real.log 2 - Real.cos (γ * Real.log 2)) ^ 2 +
    (w 3 / Real.log 3 - Real.cos (γ * Real.log 3)) ^ 2

theorem liouvilleTwistedVonMangoldt_three :
    liouvilleTwistedVonMangoldt 3 = -Real.log 3 := by
  rw [liouvilleTwistedVonMangoldt, ArithmeticFunction.cardFactors_apply_prime Nat.prime_three,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  norm_num

theorem liouvilleTwistedVonMangoldt_four :
    liouvilleTwistedVonMangoldt 4 = Real.log 2 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [liouvilleTwistedVonMangoldt, h4,
    ArithmeticFunction.cardFactors_pow, ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- **Archimedean-Free Catalan Separation Theorem (`catalan_finite_gauge_separation`):**
1. *Successor-square sign flip:* `catalanSuccessorSquareForm` is strictly positive (`8^σ (log 2)² > 0`)
   across the entire real scale-twist line `σ ∈ ℝ` (including `Λ` at `σ = 0`), and strictly negative
   (`-(log 2)² < 0`) on `liouvilleTwistedVonMangoldt`.
2. *Ordinate-twist repulsion:* `catalanKroneckerTwistDefect` vanishes at `γ = γ₀` for every real
   ordinate twist `ordinateTwistedVonMangoldt γ₀`, whereas on `liouvilleTwistedVonMangoldt` it obeys
   `(1 / 5000) exp(-2 |γ|) ≤ catalanKroneckerTwistDefect liouvilleTwistedVonMangoldt γ` for **all**
   `γ ∈ ℝ`, forcing any `ε`-approximating ordinate above `|γ| ≥ (1 / 2) log(1 / (5000 ε))`. -/
theorem catalan_finite_gauge_separation :
    (∀ σ : ℝ, catalanSuccessorSquareForm (scaleTwistedVonMangoldt σ) =
        (8 : ℝ) ^ σ * (Real.log 2) ^ 2 ∧
      0 < catalanSuccessorSquareForm (scaleTwistedVonMangoldt σ)) ∧
    (catalanSuccessorSquareForm liouvilleTwistedVonMangoldt = -(Real.log 2) ^ 2 ∧
      catalanSuccessorSquareForm liouvilleTwistedVonMangoldt < 0) ∧
    (∀ γ₀ : ℝ, catalanKroneckerTwistDefect (ordinateTwistedVonMangoldt γ₀) γ₀ = 0) ∧
    (∀ γ : ℝ, (1 / 5000 : ℝ) * Real.exp (-2 * |γ|) ≤
        catalanKroneckerTwistDefect liouvilleTwistedVonMangoldt γ) ∧
    (∀ γ ε : ℝ, 0 < ε →
      catalanKroneckerTwistDefect liouvilleTwistedVonMangoldt γ ≤ ε →
        (1 / 2 : ℝ) * Real.log (1 / (5000 * ε)) ≤ |γ|) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrep_sq : ∀ γ : ℝ, (1 / 5000 : ℝ) * Real.exp (-2 * |γ|) ≤
      catalanKroneckerTwistDefect liouvilleTwistedVonMangoldt γ := fun γ => by
    unfold catalanKroneckerTwistDefect
    rw [liouvilleTwistedVonMangoldt_two, liouvilleTwistedVonMangoldt_three,
      neg_div, div_self hl2.ne', neg_div, div_self hl3.ne']
    have hr := liouville_kronecker_repulsion_ge γ
    set s1 : ℝ := 1 + Real.cos (γ * Real.log 2)
    set s2 : ℝ := 1 + Real.cos (γ * Real.log 3)
    have hcs : (s1 + s2) ^ 2 / 2 ≤
        (-1 - Real.cos (γ * Real.log 2)) ^ 2 + (-1 - Real.cos (γ * Real.log 3)) ^ 2 := by
      dsimp [s1, s2]; nlinarith [sq_nonneg (s1 - s2)]
    have hsq : ((1 / 50 : ℝ) * Real.exp (-|γ|)) ^ 2 ≤ (s1 + s2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hr 2
    have hexp : ((1 / 50 : ℝ) * Real.exp (-|γ|)) ^ 2 / 2 =
        (1 / 5000 : ℝ) * Real.exp (-2 * |γ|) := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
    linarith
  refine ⟨fun σ => ?_, ?_, fun γ₀ => ?_, hrep_sq, fun γ ε hε hle => ?_⟩
  · have hΛ2 : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 :=
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hΛ4 : (ArithmeticFunction.vonMangoldt 4 : ℝ) = Real.log 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have heq : catalanSuccessorSquareForm (scaleTwistedVonMangoldt σ) =
        (8 : ℝ) ^ σ * (Real.log 2) ^ 2 := by
      unfold catalanSuccessorSquareForm scaleTwistedVonMangoldt
      rw [show (3 + 1 : ℕ) = 4 by norm_num, hΛ2, hΛ4]
      have hmul : (2 : ℝ) ^ σ * (4 : ℝ) ^ σ = (8 : ℝ) ^ σ := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]
        norm_num
      calc ((2 : ℕ) : ℝ) ^ σ * Real.log 2 * (((4 : ℕ) : ℝ) ^ σ * Real.log 2)
          = ((2 : ℝ) ^ σ * (4 : ℝ) ^ σ) * (Real.log 2) ^ 2 := by push_cast; ring
        _ = (8 : ℝ) ^ σ * (Real.log 2) ^ 2 := by rw [hmul]
    exact ⟨heq, heq ▸ mul_pos (Real.rpow_pos_of_pos (by norm_num) σ) (sq_pos_of_pos hl2)⟩
  · have heq : catalanSuccessorSquareForm liouvilleTwistedVonMangoldt = -(Real.log 2) ^ 2 := by
      unfold catalanSuccessorSquareForm
      rw [show (3 + 1 : ℕ) = 4 by norm_num, liouvilleTwistedVonMangoldt_two,
        liouvilleTwistedVonMangoldt_four]
      ring
    exact ⟨heq, heq ▸ neg_lt_zero.mpr (sq_pos_of_pos hl2)⟩
  · unfold catalanKroneckerTwistDefect ordinateTwistedVonMangoldt
    have hΛ2 : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 :=
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hΛ3 : (ArithmeticFunction.vonMangoldt 3 : ℝ) = Real.log 3 :=
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
    rw [hΛ2, hΛ3]
    have h2 : Real.cos (γ₀ * Real.log (2 : ℕ)) * Real.log 2 / Real.log 2 -
        Real.cos (γ₀ * Real.log 2) = 0 := by
      norm_num [mul_div_cancel_right₀ _ hl2.ne']
    have h3 : Real.cos (γ₀ * Real.log (3 : ℕ)) * Real.log 3 / Real.log 3 -
        Real.cos (γ₀ * Real.log 3) = 0 := by
      norm_num [mul_div_cancel_right₀ _ hl3.ne']
    rw [h2, h3]
    norm_num
  · have hrep : (1 / 5000 : ℝ) * Real.exp (-2 * |γ|) ≤ ε := (hrep_sq γ).trans hle
    have h2 : 1 / (5000 * ε) ≤ Real.exp (2 * |γ|) := by
      rw [show -2 * |γ| = -(2 * |γ|) by ring, Real.exp_neg] at hrep
      rw [div_le_iff₀ (by positivity)]
      have hmul := mul_le_mul_of_nonneg_right hrep
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5000) (Real.exp_pos (2 * |γ|)).le)
      calc (1 : ℝ) = (1 / 5000 : ℝ) * (Real.exp (2 * |γ|))⁻¹ * (5000 * Real.exp (2 * |γ|)) := by
            field_simp
        _ ≤ ε * (5000 * Real.exp (2 * |γ|)) := hmul
        _ = Real.exp (2 * |γ|) * (5000 * ε) := by ring
    have hlog := Real.log_le_log (by positivity) h2
    rw [Real.log_exp] at hlog
    linarith

/-! ## §2. Variational Ground Eigenvalue on `[-23/40, 23/40]` & Smooth Witness -/

/-- Set of normalized Rayleigh quotients of the Liouville-twisted Weil functional on `C²_c([-r, r])`. -/
def liouvilleWindowRayleighSet (r : ℝ) : Set ℝ :=
  { q : ℝ | ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ x, r < |x| → F x = 0) ∧ 0 < (∫ x, F x ^ 2) ∧
      q = (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re / (∫ x, F x ^ 2) }

/-- Variational ground eigenvalue `λ_Liouv(r)` of the Liouville-twisted Weil form on `[-r, r]`. -/
def liouvilleWindowGroundEigenvalue (r : ℝ) : ℝ :=
  sInf (liouvilleWindowRayleighSet r)

private theorem abs_autocorr_le_autocorr_zero (f : C_c(ℝ, ℝ)) (t : ℝ) :
    |autocorr f t| ≤ autocorr f 0 := by
  have h1 := autocorr_sub_nonneg f.hasCompactSupport f.continuous t
  have h2 := autocorr_add_nonneg f.hasCompactSupport f.continuous t
  rw [abs_le]
  constructor <;> linarith

private theorem weilFullFunctional_liouville_eq_vonMangoldt_add_sum (f : C_c(ℝ, ℝ)) {R : ℝ}
    (hR0 : 0 ≤ R) (hfR : ∀ x, R < |x| → f x = 0) :
    (weilFullFunctional liouvilleTwistedVonMangoldt
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re +
    ∑ n ∈ Finset.range (⌈Real.exp (2 * R)⌉₊ + 1),
      (if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
        Real.sqrt n else 0) * (2 * autocorr f (Real.log n)) := by
  have hwt : EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)) =
      fun x => (autocorr f x : ℂ) := by
    funext x
    simpa only [neg_neg, autocorr_neg] using (autocorr_eq_weilTest f (-x)).symm
  set N0 : ℕ := ⌈Real.exp (2 * R)⌉₊
  have hfar : ∀ n : ℕ, n ∉ Finset.range (N0 + 1) → 2 * R < |Real.log n| := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hn' : Real.exp (2 * R) < (n : ℝ) := by
      have h1 := Nat.le_ceil (Real.exp (2 * R))
      have h2 : ((N0 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      linarith
    have hpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hn'
    have hl := (Real.lt_log_iff_exp_lt hpos).mpr hn'
    rw [abs_of_pos (lt_of_le_of_lt (by linarith [hR0]) hl)]
    exact hl
  have hsum_eq : ∀ w : ℕ → ℝ,
      (∑' n : ℕ, ((if 2 ≤ n then w n / Real.sqrt n else 0 : ℝ) : ℂ) *
        ((autocorr f (Real.log n) : ℂ) + (autocorr f (-Real.log n) : ℂ))) =
      (((∑ n ∈ Finset.range (N0 + 1),
        (if 2 ≤ n then w n / Real.sqrt n else 0) * (2 * autocorr f (Real.log n))) : ℝ) : ℂ) := by
    intro w
    rw [tsum_eq_sum (s := Finset.range (N0 + 1)) fun n hn => ?_]
    · push_cast
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [autocorr_neg]
      ring
    · by_cases h2 : 2 ≤ n
      · have hz1 : autocorr f (Real.log n) = 0 := autocorr_eq_zero_of_far hfR (hfar n hn)
        have hz2 : autocorr f (-Real.log n) = 0 := by rw [autocorr_neg, hz1]
        simp [h2, hz1, hz2]
      · simp [h2]
  have hdiff : weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) -
      weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      (((∑ n ∈ Finset.range (N0 + 1),
        (if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
          Real.sqrt n else 0) * (2 * autocorr f (Real.log n))) : ℝ) : ℂ) := by
    rw [hwt]
    unfold weilFullFunctional
    rw [hsum_eq liouvilleTwistedVonMangoldt,
      hsum_eq (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))]
    have hring : ∀ z w (a b : ℂ), (z - a + w) - (z - b + w) = b - a := fun _ _ _ _ => by ring
    rw [hring, ← Complex.ofReal_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  have hre := congrArg Complex.re hdiff
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  linarith

/-- **Unconditional Lower Boundedness of `liouvilleWindowRayleighSet r`:**
For every `r > 0`, the normalized Liouville-twisted Weil functional on `C²_c([-r, r])` is bounded
below by an explicit finite constant depending only on `r`. -/
theorem bddBelow_liouvilleWindowRayleighSet {r : ℝ} (hr : 0 < r) :
    BddBelow (liouvilleWindowRayleighSet r) := by
  set N : ℕ := compactFullWeilPrimeCutoff r
  set N0 : ℕ := ⌈Real.exp (2 * r)⌉₊
  set C_prime : ℝ := ∑ n ∈ Finset.range (N0 + 1),
    |(if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
      Real.sqrt n else 0)| * 2
  refine ⟨-(|EF.gammaBracket 0| + 2 * SignedPrimePolar.mass N + C_prime), ?_⟩
  rintro q ⟨F, hF, hFc, hsupp, hnorm, rfl⟩
  let f : C_c(ℝ, ℝ) := ⟨⟨F, hF.continuous⟩, hFc⟩
  have hf_ac0 : autocorr f 0 = ∫ x, F x ^ 2 := by
    unfold autocorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change F x * F (x + 0) = F x ^ 2
    rw [add_zero, sq]
  have hcut : 2 * (r + 1) < SignedPrimePolar.cutoff N := by
    have he : Real.exp (2 * (r + 1) + 1) ≤ ((N + 2 : ℕ) : ℝ) := by
      have h1 : Real.exp (2 * (r + 1) + 1) ≤ (N : ℝ) := Nat.le_ceil _
      push_cast; linarith
    have hl := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hl
    exact lt_of_lt_of_le (by linarith) hl
  have hft : ∀ x, SignedPrimePolar.cutoff N ≤ x → autocorr f x = 0 := fun x hx =>
    autocorr_eq_zero_of_far hsupp
      ((show 2 * r < 2 * (r + 1) by linarith).trans (hcut.trans_le (hx.trans (le_abs_self _))))
  have hpair_abs : |fullPairing (autocorr f)| ≤ SignedPrimePolar.mass N * autocorr f 0 := by
    rw [fullPairing_eq_pairing_of_tail _ N hft]
    exact abs_pairing_le_mass_mul N _ _ (abs_autocorr_le_autocorr_zero f)
  have hzeta_eq := re_weilFullFunctional_eq_of_compact_finite_jump f
    (integrableOn_biScaleLevyIntegrand hF hFc)
  have hlev_nn : 0 ≤ biScaleLevyEnergy f := biScaleLevyEnergy_nonneg hFc hF.continuous
  have hliouv_eq := weilFullFunctional_liouville_eq_vonMangoldt_add_sum f hr.le hsupp
  have hsum_abs : |∑ n ∈ Finset.range (N0 + 1),
      (if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
        Real.sqrt n else 0) * (2 * autocorr f (Real.log n))| ≤ C_prime * autocorr f 0 := by
    calc _ ≤ ∑ n ∈ Finset.range (N0 + 1),
          |(if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
            Real.sqrt n else 0) * (2 * autocorr f (Real.log n))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.range (N0 + 1),
          |(if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
            Real.sqrt n else 0)| * (2 * autocorr f 0) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (abs_autocorr_le_autocorr_zero f _) (by norm_num))
            (abs_nonneg _)
      _ = C_prime * autocorr f 0 := by
          dsimp [C_prime]
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
  have hnum_ge : -(|EF.gammaBracket 0| + 2 * SignedPrimePolar.mass N + C_prime) * autocorr f 0 ≤
      (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
    change _ ≤ (weilFullFunctional liouvilleTwistedVonMangoldt
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re
    rw [hliouv_eq, hzeta_eq]
    have hg0 : -|EF.gammaBracket 0| * autocorr f 0 ≤ EF.gammaBracket 0 * autocorr f 0 :=
      mul_le_mul_of_nonneg_right (neg_abs_le _) (by rw [hf_ac0]; exact hnorm.le)
    have hp0 := (abs_le.mp hpair_abs).2
    have hs0 := (abs_le.mp hsum_abs).1
    linarith
  rw [le_div_iff₀ hnorm, ← hf_ac0]
  exact hnum_ge

/-! ### Explicit Cubic–Quintic Witness `u³ ((27/50)² - u²)` at `R = 27 / 50 < 23 / 40` -/

private def witnessR : ℝ := 27 / 50

private def cubicQuinticFun (u : ℝ) : ℝ :=
  if |u| ≤ witnessR then u ^ 3 * (witnessR ^ 2 - u ^ 2) else 0

private theorem continuous_cubicQuinticFun : Continuous cubicQuinticFun := by
  unfold cubicQuinticFun
  refine Continuous.if_le (by fun_prop) continuous_const continuous_abs continuous_const ?_
  intro u hu
  have hsq : u ^ 2 = witnessR ^ 2 := by rw [← sq_abs, hu]
  rw [hsq, sub_self, mul_zero]

private theorem cubicQuinticFun_eq_zero_of_lt {u : ℝ} (hu : witnessR < |u|) :
    cubicQuinticFun u = 0 := by
  unfold cubicQuinticFun
  rw [if_neg (not_le.mpr hu)]

private theorem hasCompactSupport_cubicQuinticFun : HasCompactSupport cubicQuinticFun :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) witnessR) fun u hu => by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hu
    exact cubicQuinticFun_eq_zero_of_lt hu

private def cubicQuinticSource : C_c(ℝ, ℝ) :=
  ⟨⟨cubicQuinticFun, continuous_cubicQuinticFun⟩, hasCompactSupport_cubicQuinticFun⟩

private theorem cubicQuinticFun_neg (u : ℝ) : cubicQuinticFun (-u) = -cubicQuinticFun u := by
  unfold cubicQuinticFun
  rw [abs_neg]
  split_ifs
  · ring
  · ring

private theorem lipschitz_cubicQuinticSource :
    ∀ x y : ℝ, |cubicQuinticSource x - cubicQuinticSource y| ≤ 2 * |x - y| := by
  have hderiv_le : ∀ u ∈ Icc (-witnessR) witnessR, |3 * witnessR ^ 2 * u ^ 2 - 5 * u ^ 4| ≤ 2 := by
    intro u hu
    have hu2 : u ^ 2 ≤ witnessR ^ 2 := by
      have habs : |u| ≤ witnessR := abs_le.mpr hu
      calc u ^ 2 = |u| ^ 2 := (sq_abs u).symm
        _ ≤ witnessR ^ 2 := pow_le_pow_left₀ (abs_nonneg u) habs 2
    have hu0 : 0 ≤ u ^ 2 := sq_nonneg u
    dsimp [witnessR] at hu2 ⊢
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u ^ 2)]
  have hseg : ∀ a b : ℝ, a ∈ Icc (-witnessR) witnessR → b ∈ Icc (-witnessR) witnessR →
      |cubicQuinticFun a - cubicQuinticFun b| ≤ 2 * |a - b| := by
    intro a b ha hb
    let g : ℝ → ℝ := fun u => u ^ 3 * (witnessR ^ 2 - u ^ 2)
    have hga : cubicQuinticFun a = g a := if_pos (abs_le.mpr ha)
    have hgb : cubicQuinticFun b = g b := if_pos (abs_le.mpr hb)
    rw [hga, hgb]
    have hg_deriv : ∀ u : ℝ, HasDerivAt g (3 * witnessR ^ 2 * u ^ 2 - 5 * u ^ 4) u := fun u => by
      have p3 := (hasDerivAt_pow 3 u).const_mul (witnessR ^ 2)
      have p5 := hasDerivAt_pow 5 u
      refine (p3.sub p5).congr_of_eventuallyEq (Eventually.of_forall fun t => by dsimp [g]; ring)
        |>.congr_deriv ?_
      ring
    have hconv : Convex ℝ (Icc (-witnessR) witnessR) := convex_Icc _ _
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := g) (f' := fun u => 3 * witnessR ^ 2 * u ^ 2 - 5 * u ^ 4) (C := 2)
      (fun u _ => (hg_deriv u).hasDerivWithinAt)
      (fun u hu => by simpa [Real.norm_eq_abs] using hderiv_le u hu) hconv hb ha
    simpa [Real.norm_eq_abs] using hmvt
  intro x y
  let clampR : ℝ → ℝ := fun t => max (-witnessR) (min witnessR t)
  have hR_pos : 0 < witnessR := by dsimp [witnessR]; norm_num
  have hclamp_mem : ∀ t : ℝ, clampR t ∈ Icc (-witnessR) witnessR := fun t => by
    dsimp [clampR]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hclamp_eq : ∀ t : ℝ, cubicQuinticFun t = cubicQuinticFun (clampR t) := fun t => by
    rcases lt_trichotomy t (-witnessR) with ht | rfl | ht
    · have hc : clampR t = -witnessR := max_eq_left ((min_le_right _ _).trans ht.le)
      have h1 : witnessR < |t| := by rw [abs_of_neg (by linarith)]; linarith
      rw [cubicQuinticFun_eq_zero_of_lt h1, hc]
      unfold cubicQuinticFun
      rw [if_pos (by rw [abs_neg, abs_of_pos hR_pos])]
      ring
    · dsimp [clampR]; rw [min_eq_right (by linarith), max_eq_right le_rfl]
    · rcases le_or_gt t witnessR with ht2 | ht2
      · have hc : clampR t = t := by
          dsimp [clampR]; rw [min_eq_right ht2, max_eq_right ht.le]
        rw [hc]
      · have hc : clampR t = witnessR := by
          dsimp [clampR]; rw [min_eq_left ht2.le, max_eq_right (by linarith)]
        have h1 : witnessR < |t| := by rw [abs_of_pos (by linarith)]; exact ht2
        rw [cubicQuinticFun_eq_zero_of_lt h1, hc]
        unfold cubicQuinticFun
        rw [if_pos (by rw [abs_of_pos hR_pos])]
        ring
  have hclamp_lip : |clampR x - clampR y| ≤ |x - y| := by
    have hval : ∀ t : ℝ, (t ≤ -witnessR ∧ clampR t = -witnessR) ∨
        (-witnessR ≤ t ∧ t ≤ witnessR ∧ clampR t = t) ∨
        (witnessR ≤ t ∧ clampR t = witnessR) := fun t => by
      rcases le_total t (-witnessR) with h1 | h1
      · left; exact ⟨h1, max_eq_left ((min_le_right _ _).trans h1)⟩
      · rcases le_total t witnessR with h2 | h2
        · right; left; exact ⟨h1, h2, by dsimp [clampR]; rw [min_eq_right h2, max_eq_right h1]⟩
        · right; right; exact ⟨h2, by dsimp [clampR]; rw [min_eq_left h2, max_eq_right (by linarith)]⟩
    rw [abs_le]
    rcases hval x with ⟨hx, hcx⟩ | ⟨hx1, hx2, hcx⟩ | ⟨hx, hcx⟩ <;>
      rcases hval y with ⟨hy, hcy⟩ | ⟨hy1, hy2, hcy⟩ | ⟨hy, hcy⟩ <;>
      rw [hcx, hcy] <;>
      exact ⟨by linarith [le_abs_self (x - y), neg_le_abs (x - y)],
        by linarith [le_abs_self (x - y), neg_le_abs (x - y)]⟩
  change |cubicQuinticFun x - cubicQuinticFun y| ≤ 2 * |x - y|
  rw [hclamp_eq x, hclamp_eq y]
  exact (hseg (clampR x) (clampR y) (hclamp_mem x) (hclamp_mem y)).trans
    (mul_le_mul_of_nonneg_left hclamp_lip (by norm_num))

/-- Normalized autocorrelation polynomial `k₁(t)` of `u³ (1 - u²)` for `t ∈ [0, 2]`. -/
private def unitCubicQuinticCorr (t : ℝ) : ℝ :=
  16 / 693 - 92 / 315 * t ^ 2 + 2 / 3 * t ^ 3 - 4 / 7 * t ^ 4 + 1 / 6 * t ^ 5 +
    1 / 140 * t ^ 7 - 1 / 252 * t ^ 9 + 1 / 2772 * t ^ 11

private theorem autocorr_cubicQuinticSource_eq {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2 * witnessR) :
    autocorr cubicQuinticSource x = witnessR ^ 11 * unitCubicQuinticCorr (x / witnessR) := by
  have hR : 0 < witnessR := by dsimp [witnessR]; norm_num
  have hlo_le : -witnessR ≤ witnessR - x := by linarith
  have hcompl : ∀ u : ℝ, u ∉ Icc (-witnessR) (witnessR - x) →
      cubicQuinticSource u * cubicQuinticSource (u + x) = 0 := by
    intro u hu
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hlt | hgt
    · have habs : witnessR < |u| := by rw [abs_of_neg (by linarith)]; linarith
      change cubicQuinticFun u * cubicQuinticFun (u + x) = 0
      rw [cubicQuinticFun_eq_zero_of_lt habs, zero_mul]
    · have habs : witnessR < |u + x| := by rw [abs_of_pos (by linarith)]; linarith
      change cubicQuinticFun u * cubicQuinticFun (u + x) = 0
      rw [cubicQuinticFun_eq_zero_of_lt habs, mul_zero]
  unfold autocorr
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlo_le]
  have hcongr : ∫ u in (-witnessR)..(witnessR - x),
      cubicQuinticSource u * cubicQuinticSource (u + x) =
      ∫ u in (-witnessR)..(witnessR - x),
        (u ^ 3 * (witnessR ^ 2 - u ^ 2)) * ((u + x) ^ 3 * (witnessR ^ 2 - (u + x) ^ 2)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hlo_le] at hu
    have hu1 : |u| ≤ witnessR := abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩
    have hu2 : |u + x| ≤ witnessR := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
    change cubicQuinticFun u * cubicQuinticFun (u + x) = _
    unfold cubicQuinticFun
    rw [if_pos hu1, if_pos hu2]
  rw [hcongr]
  set a : ℝ := x / 2
  set c : ℝ := 2 * witnessR ^ 2 + 2 * a ^ 2
  set d : ℝ := (witnessR ^ 2 - a ^ 2) ^ 2
  let anti : ℝ → ℝ := fun u =>
    let v := u + a
    (1 / 11 : ℝ) * v ^ 11 - ((3 * a ^ 2 + c) / 9) * v ^ 9 +
      ((3 * a ^ 4 + 3 * a ^ 2 * c + d) / 7) * v ^ 7 -
      ((a ^ 6 + 3 * a ^ 4 * c + 3 * a ^ 2 * d) / 5) * v ^ 5 +
      ((a ^ 6 * c + 3 * a ^ 4 * d) / 3) * v ^ 3 - a ^ 6 * d * v
  have hderiv : ∀ u : ℝ, HasDerivAt anti
      ((u ^ 3 * (witnessR ^ 2 - u ^ 2)) * ((u + x) ^ 3 * (witnessR ^ 2 - (u + x) ^ 2))) u := by
    intro u
    have hv : HasDerivAt (fun u : ℝ => u + a) 1 u := (hasDerivAt_id u).add_const a
    have hp (n : ℕ) : HasDerivAt (fun u : ℝ => (u + a) ^ n) ((n : ℝ) * (u + a) ^ (n - 1) * 1) u :=
      hv.pow n
    have hcomb := ((((((hp 11).const_mul (1 / 11 : ℝ)).sub
      ((hp 9).const_mul ((3 * a ^ 2 + c) / 9))).add
      ((hp 7).const_mul ((3 * a ^ 4 + 3 * a ^ 2 * c + d) / 7))).sub
      ((hp 5).const_mul ((a ^ 6 + 3 * a ^ 4 * c + 3 * a ^ 2 * d) / 5))).add
      ((hp 3).const_mul ((a ^ 6 * c + 3 * a ^ 4 * d) / 3))).sub
      (hv.const_mul (a ^ 6 * d))
    refine hcomb.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl) |>.congr_deriv ?_
    dsimp [c, d, a]
    norm_num
    ring
  have hint : IntervalIntegrable
      (fun u : ℝ => (u ^ 3 * (witnessR ^ 2 - u ^ 2)) * ((u + x) ^ 3 * (witnessR ^ 2 - (u + x) ^ 2)))
      volume (-witnessR) (witnessR - x) :=
    (by fun_prop : Continuous fun u : ℝ =>
      (u ^ 3 * (witnessR ^ 2 - u ^ 2)) * ((u + x) ^ 3 * (witnessR ^ 2 - (u + x) ^ 2))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u) hint]
  dsimp [anti, c, d, a, unitCubicQuinticCorr]
  field_simp [hR.ne']
  ring

/-- Universal rational upper and lower envelopes for `archLevySinhWeight x = e^{x/2} / sinh x`:
`1 / x + 1 / 2 - x / 8 ≤ archLevySinhWeight x ≤ 1 / x + 1 / 2` on `(0, 11 / 10]`. -/
private theorem archLevySinhWeight_bounds {x : ℝ} (hx : 0 < x) :
    archLevySinhWeight x ≤ 1 / x + 1 / 2 ∧
      (x ≤ 11 / 10 → 1 / x + 1 / 2 - x / 8 ≤ archLevySinhWeight x) := by
  have hy : 0 < x / 2 := half_pos hx
  have hsh_pos : 0 < Real.sinh (x / 2) := Real.sinh_pos_iff.mpr hy
  have hch_pos : 0 < Real.cosh (x / 2) := Real.cosh_pos (x / 2)
  have hsplit : archLevySinhWeight x =
      1 / (2 * Real.sinh (x / 2)) + 1 / (2 * Real.cosh (x / 2)) := by
    unfold archLevySinhWeight
    have hexp : Real.exp (x / 2) = Real.cosh (x / 2) + Real.sinh (x / 2) :=
      (Real.cosh_add_sinh (x / 2)).symm
    have hsh2 : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
      conv_lhs => rw [show x = 2 * (x / 2) by ring, Real.sinh_two_mul]
    rw [hexp, hsh2]
    field_simp
  rw [hsplit]
  have hy_le_sh : x / 2 ≤ Real.sinh (x / 2) := by
    have hmvt := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hy
      Real.continuous_sinh.continuousOn fun t _ => Real.hasDerivAt_sinh t
    obtain ⟨c, _, hc⟩ := hmvt
    rw [Real.sinh_zero, sub_zero, sub_zero] at hc
    have hch1 : 1 ≤ Real.cosh c := Real.one_le_cosh c
    rw [eq_div_iff hy.ne'] at hc
    nlinarith
  have hch_ge : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh (x / 2)
  constructor
  · have h1 : 1 / (2 * Real.sinh (x / 2)) ≤ 1 / x := by
      have : x ≤ 2 * Real.sinh (x / 2) := by linarith
      exact one_div_le_one_div_of_le hx this
    have h2 : 1 / (2 * Real.cosh (x / 2)) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · intro hx11
    set y : ℝ := x / 2
    have hy_le1 : |y| ≤ 1 := by rw [abs_of_pos hy]; dsimp [y]; linarith
    have hb_pos := Real.exp_bound hy_le1 (n := 4) (by norm_num)
    have hy_neg_le1 : |-y| ≤ 1 := by rw [abs_neg]; exact hy_le1
    have hb_neg := Real.exp_bound hy_neg_le1 (n := 4) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add] at hb_pos hb_neg
    rw [abs_of_pos hy] at hb_pos
    rw [abs_neg, abs_of_pos hy] at hb_neg
    have hy_ub : y ≤ 11 / 20 := by dsimp [y]; linarith
    have hy2_ub : y ^ 2 ≤ (11 / 20) ^ 2 := pow_le_pow_left₀ hy.le hy_ub 2
    have hsh_ub : Real.sinh y ≤ y + (1 / 5 : ℝ) * y ^ 3 := by
      rw [Real.sinh_eq]
      have hp := (abs_le.mp hb_pos).2
      have hm := (abs_le.mp hb_neg).1
      have hneg3 : (-y) ^ 3 = -y ^ 3 := by ring
      rw [hneg3] at hm
      norm_num at hp hm hy2_ub
      nlinarith [mul_nonneg (pow_nonneg hy.le 3) (sub_nonneg.mpr hy_ub)]
    have hch_ub : Real.cosh y ≤ 1 + (13 / 25 : ℝ) * y ^ 2 := by
      rw [Real.cosh_eq]
      have hp := (abs_le.mp hb_pos).2
      have hm := (abs_le.mp hb_neg).2
      norm_num at hp hm hy2_ub
      nlinarith [sq_nonneg y]
    have h1 : 1 / x - (1 / 20 : ℝ) * x ≤ 1 / (2 * Real.sinh y) := by
      have h1_aux : (1 / x - (1 / 20 : ℝ) * x) * (2 * Real.sinh y) ≤ 1 := by
        have hnn : 0 ≤ 1 / x - (1 / 20 : ℝ) * x := by
          rw [sub_nonneg, le_div_iff₀ hx]
          nlinarith
        calc (1 / x - (1 / 20 : ℝ) * x) * (2 * Real.sinh y)
            ≤ (1 / x - (1 / 20 : ℝ) * x) * (2 * (y + (1 / 5 : ℝ) * y ^ 3)) :=
              mul_le_mul_of_nonneg_left (by linarith) hnn
          _ = 1 - (1 / 400 : ℝ) * x ^ 4 := by dsimp [y]; field_simp [hx.ne']; ring
          _ ≤ 1 := by linarith [pow_nonneg hx.le 4]
      exact (le_div_iff₀ (by positivity)).mpr h1_aux
    have h2 : 1 / 2 - (13 / 200 : ℝ) * x ^ 2 ≤ 1 / (2 * Real.cosh y) := by
      have h2_aux : (1 / 2 - (13 / 200 : ℝ) * x ^ 2) * (2 * Real.cosh y) ≤ 1 := by
        have hnn : 0 ≤ 1 / 2 - (13 / 200 : ℝ) * x ^ 2 := by nlinarith
        calc (1 / 2 - (13 / 200 : ℝ) * x ^ 2) * (2 * Real.cosh y)
            ≤ (1 / 2 - (13 / 200 : ℝ) * x ^ 2) * (2 * (1 + (13 / 25 : ℝ) * y ^ 2)) :=
              mul_le_mul_of_nonneg_left (by linarith) hnn
          _ = 1 - (169 / 10000 : ℝ) * x ^ 4 := by dsimp [y]; ring
          _ ≤ 1 := by linarith [pow_nonneg hx.le 4]
      exact (le_div_iff₀ (by positivity)).mpr h2_aux
    have hx_lin : (1 / 20 : ℝ) * x + (13 / 200 : ℝ) * x ^ 2 ≤ x / 8 := by nlinarith
    dsimp [y] at h1 h2
    linarith

private theorem arctan_bounds_of_nonneg {z : ℝ} (hz0 : 0 ≤ z) :
    z - z ^ 3 / 3 ≤ Real.arctan z ∧ Real.arctan z ≤ z := by
  rcases eq_or_lt_of_le hz0 with rfl | hz
  · simp
  have hderiv_at : ∀ t : ℝ, HasDerivAt Real.arctan (1 / (1 + t ^ 2)) t := Real.hasDerivAt_arctan
  constructor
  · let g : ℝ → ℝ := fun t => Real.arctan t - (t - t ^ 3 / 3)
    have hg0 : g 0 = 0 := by simp [g]
    have hgd : ∀ t : ℝ, HasDerivAt g (t ^ 4 / (1 + t ^ 2)) t := fun t => by
      have hp : HasDerivAt (fun t : ℝ => t - t ^ 3 / 3) (1 - t ^ 2) t := by
        have p3 := ((hasDerivAt_id t).pow 3).div_const 3
        refine ((hasDerivAt_id t).sub p3).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
          |>.congr_deriv ?_
        simp only [id_eq]
        ring
      refine ((hderiv_at t).sub hp).congr_deriv ?_
      have hpos : 0 < 1 + t ^ 2 := by positivity
      field_simp [hpos.ne']
      ring
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g (fun t => t ^ 4 / (1 + t ^ 2)) hz
      (fun t _ => (hgd t).continuousAt.continuousWithinAt) (fun t _ => hgd t)
    rw [hg0, sub_zero, sub_zero, eq_div_iff hz.ne'] at hc
    have hpos : 0 ≤ c ^ 4 / (1 + c ^ 2) * z := by positivity
    dsimp [g] at hc
    linarith
  · let h : ℝ → ℝ := fun t => t - Real.arctan t
    have hh0 : h 0 = 0 := by simp [h]
    have hhd : ∀ t : ℝ, HasDerivAt h (t ^ 2 / (1 + t ^ 2)) t := fun t => by
      refine ((hasDerivAt_id t).sub (hderiv_at t)).congr_deriv ?_
      have hpos : 0 < 1 + t ^ 2 := by positivity
      field_simp [hpos.ne']
      ring
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope h (fun t => t ^ 2 / (1 + t ^ 2)) hz
      (fun t _ => (hhd t).continuousAt.continuousWithinAt) (fun t _ => hhd t)
    rw [hh0, sub_zero, sub_zero, eq_div_iff hz.ne'] at hc
    have hpos : 0 ≤ c ^ 2 / (1 + c ^ 2) * z := by positivity
    dsimp [h] at hc
    linarith

private theorem exp_neg_witnessR_bounds :
    (582 / 1000 : ℝ) < Real.exp (-witnessR) ∧ Real.exp (-witnessR) < 585 / 1000 := by
  have hR_le1 : |witnessR| ≤ 1 := by dsimp [witnessR]; rw [abs_of_pos (by norm_num)]; norm_num
  have hb := Real.exp_bound hR_le1 (n := 4) (by norm_num)
  have hlo := Real.sum_le_exp_of_nonneg (x := witnessR) (by dsimp [witnessR]; norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.cast_ofNat, pow_zero, pow_one, div_one, zero_add] at hb hlo
  dsimp [witnessR] at hb hlo
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 27 / 50)] at hb
  have hhi := (abs_le.mp hb).2
  have hexp_pos : 0 < Real.exp witnessR := Real.exp_pos witnessR
  rw [Real.exp_neg]
  dsimp [witnessR] at hexp_pos ⊢
  constructor
  · rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 582 / 1000) hexp_pos]
    norm_num at hhi ⊢
    linarith
  · rw [inv_lt_comm₀ hexp_pos (by norm_num : (0 : ℝ) < 585 / 1000)]
    norm_num at hlo ⊢
    linarith

private theorem tail_archLevySinhWeight_two_witnessR_bounds :
    (2359 / 1000 : ℝ) ≤ (∫ x in Ioi (2 * witnessR), archLevySinhWeight x) ∧
      (∫ x in Ioi (2 * witnessR), archLevySinhWeight x) ≤ 2513 / 1000 := by
  have h2R : 0 < 2 * witnessR := by dsimp [witnessR]; norm_num
  rw [integral_archLevySinhWeight_Ioi h2R, show -(2 * witnessR) / 2 = -witnessR by ring]
  obtain ⟨hea_lo, hea_hi⟩ := exp_neg_witnessR_bounds
  set ea : ℝ := Real.exp (-witnessR)
  have hea_pos : 0 < ea := by linarith
  have h1_sub : 0 < 1 - ea := by linarith
  set r : ℝ := (1 + ea) / (1 - ea)
  have hr_pos : 0 < r := div_pos (by linarith) h1_sub
  have hr_lo : (791 / 209 : ℝ) < r := by
    dsimp [r]
    rw [lt_div_iff₀ h1_sub]
    linarith
  have hr_hi : r < 317 / 83 := by
    dsimp [r]
    rw [div_lt_iff₀ h1_sub]
    linarith
  have hlog_eq : Real.log r = 2 * Real.log 2 + Real.log (r / 4) := by
    have : r = 4 * (r / 4) := by ring
    conv_lhs => rw [this, Real.log_mul (by norm_num) (by positivity),
      show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog_ub : Real.log (r / 4) ≤ r / 4 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hlog_lb : -(4 / r - 1) ≤ Real.log (r / 4) := by
    have hinv : Real.log (r / 4) = -Real.log (4 / r) := by
      rw [← Real.log_inv, inv_div]
    rw [hinv, neg_le_neg_iff]
    exact Real.log_le_sub_one_of_pos (by positivity)
  have h4r_ub : 4 / r < 836 / 791 := by
    rw [div_lt_iff₀ hr_pos]
    nlinarith
  obtain ⟨hat_lo, hat_hi⟩ := arctan_bounds_of_nonneg hea_pos.le
  have hl2_lo := Real.log_two_gt_d9
  have hl2_hi := Real.log_two_lt_d9
  have hpow3 : ea ^ 3 < (585 / 1000 : ℝ) ^ 3 := pow_lt_pow_left₀ hea_hi hea_pos.le (by norm_num)
  norm_num at hpow3 hl2_lo hl2_hi
  dsimp [r] at hlog_eq hlog_ub hlog_lb h4r_ub hr_hi
  constructor <;> linarith

private theorem gammaBracket_zero_bounds :
    -(5380 / 1000 : ℝ) ≤ EF.gammaBracket 0 ∧ EF.gammaBracket 0 ≤ -(5330 / 1000) := by
  rw [gammaBracket_zero_eq, show Real.log (8 * Real.pi) =
    3 * Real.log 2 + Real.log 3 + Real.log (Real.pi / 3) by
    have hpi : 0 < Real.pi := Real.pi_pos
    rw [show 8 * Real.pi = (2 : ℝ) ^ 3 * (3 * (Real.pi / 3)) by ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast; ring]
  have hb3 := Real.abs_log_sub_add_sum_range_le (x := (1 / 3 : ℝ)) (by norm_num) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_one, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_add] at hb3
  rw [show (1 : ℝ) - 1 / 3 = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv] at hb3
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at hb3
  have hl3_eq : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have hl32_lo := (abs_le.mp hb3).1
  have hl32_hi := (abs_le.mp hb3).2
  norm_num at hl32_lo hl32_hi
  have hpi_lo : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi_hi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hpi3_ub : Real.log (Real.pi / 3) ≤ Real.pi / 3 - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hpi3_lb : 1 - 3 / Real.pi ≤ Real.log (Real.pi / 3) := by
    simpa [inv_div] using Real.one_sub_inv_le_log_of_pos (x := Real.pi / 3) (by linarith)
  have hinv_ub : 3 / Real.pi ≤ 3 / 3.1415 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_lo.le
  have hγ_lo := RHTower.eulerMascheroniConstant_gt
  have hγ_hi := RHTower.eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have hl2_lo := Real.log_two_gt_d9
  have hl2_hi := Real.log_two_lt_d9
  norm_num at hinv_ub hγ_lo hγ_hi hl2_lo hl2_hi
  constructor <;> linarith

private theorem biScaleLevyEnergy_cubicQuinticSource_bounds :
    ((16019 / 6930 : ℝ) + witnessR - witnessR ^ 2 / 8 * (153 / 65) + 2359 / 1000) *
        autocorr cubicQuinticSource 0 ≤ biScaleLevyEnergy cubicQuinticSource ∧
      biScaleLevyEnergy cubicQuinticSource ≤
        ((16019 / 6930 : ℝ) + witnessR + 2513 / 1000) * autocorr cubicQuinticSource 0 := by
  have hR : 0 < witnessR := by dsimp [witnessR]; norm_num
  have h2R : 0 < 2 * witnessR := by positivity
  have h2R_le11 : 2 * witnessR ≤ 11 / 10 := by dsimp [witnessR]; norm_num
  let F_int : ℝ → ℝ := fun x =>
    (autocorr cubicQuinticSource 0 - autocorr cubicQuinticSource x) * archLevySinhWeight x
  have hi : IntegrableOn F_int (Ioi 0) :=
    integrableOn_levy_of_lipschitz cubicQuinticSource lipschitz_cubicQuinticSource
  have hi_in : IntegrableOn F_int (Ioc 0 (2 * witnessR)) := hi.mono_set fun _ hx => hx.1
  have hi_out : IntegrableOn F_int (Ioi (2 * witnessR)) := hi.mono_set fun _ hx => h2R.trans hx
  have hsplit : biScaleLevyEnergy cubicQuinticSource =
      (∫ x in Ioc 0 (2 * witnessR), F_int x) + ∫ x in Ioi (2 * witnessR), F_int x := by
    unfold biScaleLevyEnergy
    rw [← Ioc_union_Ioi_eq_Ioi h2R.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hi_in hi_out
  have hout_eq : (∫ x in Ioi (2 * witnessR), F_int x) =
      autocorr cubicQuinticSource 0 * ∫ x in Ioi (2 * witnessR), archLevySinhWeight x := by
    have hcongr : EqOn F_int (fun x => autocorr cubicQuinticSource 0 * archLevySinhWeight x)
        (Ioi (2 * witnessR)) := fun x hx => by
      have hx_pos : 0 < x := h2R.trans hx
      have hz : autocorr cubicQuinticSource x = 0 :=
        autocorr_eq_zero_of_far (fun _ hu => cubicQuinticFun_eq_zero_of_lt hu)
          (by rw [abs_of_pos hx_pos]; exact hx)
      dsimp [F_int]; rw [hz, sub_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
  have hac0 : autocorr cubicQuinticSource 0 = (16 / 693 : ℝ) * witnessR ^ 11 := by
    rw [autocorr_cubicQuinticSource_eq le_rfl h2R.le]
    dsimp [unitCubicQuinticCorr]; norm_num; ring
  have hac0_pos : 0 < autocorr cubicQuinticSource 0 := by rw [hac0]; positivity
  let polyDiffDivX : ℝ → ℝ := fun x =>
    witnessR ^ 10 * (92 / 315 * (x / witnessR) - 2 / 3 * (x / witnessR) ^ 2 +
      4 / 7 * (x / witnessR) ^ 3 - 1 / 6 * (x / witnessR) ^ 4 -
      1 / 140 * (x / witnessR) ^ 6 + 1 / 252 * (x / witnessR) ^ 8 -
      1 / 2772 * (x / witnessR) ^ 10)
  have hdiff_eq : ∀ x ∈ Ioc (0 : ℝ) (2 * witnessR),
      autocorr cubicQuinticSource 0 - autocorr cubicQuinticSource x = x * polyDiffDivX x := by
    intro x hx
    rw [hac0, autocorr_cubicQuinticSource_eq hx.1.le hx.2]
    dsimp [unitCubicQuinticCorr, polyDiffDivX]
    field_simp [hR.ne']
    ring
  let envHi : ℝ → ℝ := fun x => polyDiffDivX x + (x * polyDiffDivX x) / 2
  let envLo : ℝ → ℝ := fun x => polyDiffDivX x + (x * polyDiffDivX x) / 2 -
    (x ^ 2 * polyDiffDivX x) / 8
  have hcont_hi : Continuous envHi := by dsimp [envHi, polyDiffDivX]; fun_prop
  have hcont_lo : Continuous envLo := by dsimp [envLo, polyDiffDivX]; fun_prop
  have hin_le : (∫ x in Ioc 0 (2 * witnessR), F_int x) ≤ ∫ x in (0 : ℝ)..(2 * witnessR), envHi x := by
    rw [intervalIntegral.integral_of_le h2R.le]
    refine setIntegral_mono_on hi_in hcont_hi.integrableOn_Ioc measurableSet_Ioc fun x hx => ?_
    have hnn : 0 ≤ autocorr cubicQuinticSource 0 - autocorr cubicQuinticSource x :=
      autocorr_sub_nonneg hasCompactSupport_cubicQuinticFun continuous_cubicQuinticFun x
    have hw := (archLevySinhWeight_bounds hx.1).1
    have hm := mul_le_mul_of_nonneg_left hw hnn
    dsimp [F_int, envHi]
    rw [hdiff_eq x hx] at hm ⊢
    have hring : x * polyDiffDivX x * (1 / x + 1 / 2) =
        polyDiffDivX x + x * polyDiffDivX x / 2 := by
      field_simp [hx.1.ne']
    linarith
  have hin_ge : (∫ x in (0 : ℝ)..(2 * witnessR), envLo x) ≤ ∫ x in Ioc 0 (2 * witnessR), F_int x := by
    rw [intervalIntegral.integral_of_le h2R.le]
    refine setIntegral_mono_on hcont_lo.integrableOn_Ioc hi_in measurableSet_Ioc fun x hx => ?_
    have hnn : 0 ≤ autocorr cubicQuinticSource 0 - autocorr cubicQuinticSource x :=
      autocorr_sub_nonneg hasCompactSupport_cubicQuinticFun continuous_cubicQuinticFun x
    have hw := (archLevySinhWeight_bounds hx.1).2 (hx.2.trans h2R_le11)
    have hm := mul_le_mul_of_nonneg_left hw hnn
    dsimp [F_int, envLo]
    rw [hdiff_eq x hx] at hm ⊢
    have hring : x * polyDiffDivX x * (1 / x + 1 / 2 - x / 8) =
        polyDiffDivX x + x * polyDiffDivX x / 2 - x ^ 2 * polyDiffDivX x / 8 := by
      field_simp [hx.1.ne']
    linarith
  let antiHi : ℝ → ℝ := fun x =>
    let t := x / witnessR
    witnessR ^ 11 * (46 / 315 * t ^ 2 - 2 / 9 * t ^ 3 + 1 / 7 * t ^ 4 - 1 / 30 * t ^ 5 -
      1 / 980 * t ^ 7 + 1 / 2268 * t ^ 9 - 1 / 30492 * t ^ 11) +
    witnessR ^ 12 / 2 * (92 / 945 * t ^ 3 - 1 / 6 * t ^ 4 + 4 / 35 * t ^ 5 - 1 / 36 * t ^ 6 -
      1 / 1120 * t ^ 8 + 1 / 2520 * t ^ 10 - 1 / 33264 * t ^ 12)
  have hderiv_hi : ∀ x : ℝ, HasDerivAt antiHi (envHi x) x := fun x => by
    have ht : HasDerivAt (fun x : ℝ => x / witnessR) (1 / witnessR) x :=
      (hasDerivAt_id x).div_const witnessR
    have hp (n : ℕ) : HasDerivAt (fun x : ℝ => (x / witnessR) ^ n)
        ((n : ℝ) * (x / witnessR) ^ (n - 1) * (1 / witnessR)) x :=
      ht.pow n
    have pA := ((((((hp 2).const_mul (46 / 315 : ℝ)).sub ((hp 3).const_mul (2 / 9 : ℝ))).add
      ((hp 4).const_mul (1 / 7 : ℝ))).sub ((hp 5).const_mul (1 / 30 : ℝ))).sub
      ((hp 7).const_mul (1 / 980 : ℝ))).add ((hp 9).const_mul (1 / 2268 : ℝ)) |>.sub
      ((hp 11).const_mul (1 / 30492 : ℝ)) |>.const_mul (witnessR ^ 11)
    have pB := ((((((hp 3).const_mul (92 / 945 : ℝ)).sub ((hp 4).const_mul (1 / 6 : ℝ))).add
      ((hp 5).const_mul (4 / 35 : ℝ))).sub ((hp 6).const_mul (1 / 36 : ℝ))).sub
      ((hp 8).const_mul (1 / 1120 : ℝ))).add ((hp 10).const_mul (1 / 2520 : ℝ)) |>.sub
      ((hp 12).const_mul (1 / 33264 : ℝ)) |>.const_mul (witnessR ^ 12 / 2)
    refine (pA.add pB).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl) |>.congr_deriv ?_
    dsimp [envHi, polyDiffDivX]
    field_simp [hR.ne']
    norm_num
    ring
  have heval_hi : (∫ x in (0 : ℝ)..(2 * witnessR), envHi x) =
      ((16019 / 6930 : ℝ) + witnessR) * autocorr cubicQuinticSource 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv_hi x)
      (hcont_hi.intervalIntegrable _ _), hac0]
    dsimp [antiHi]
    field_simp [hR.ne']
    norm_num
    ring
  let antiX2 : ℝ → ℝ := fun x =>
    let t := x / witnessR
    witnessR ^ 13 / 8 * (23 / 315 * t ^ 4 - 2 / 15 * t ^ 5 + 2 / 21 * t ^ 6 - 1 / 42 * t ^ 7 -
      1 / 1260 * t ^ 9 + 1 / 2772 * t ^ 11 - 1 / 36036 * t ^ 13)
  have hderiv_lo : ∀ x : ℝ, HasDerivAt (fun u => antiHi u - antiX2 u) (envLo x) x := fun x => by
    have ht : HasDerivAt (fun x : ℝ => x / witnessR) (1 / witnessR) x :=
      (hasDerivAt_id x).div_const witnessR
    have hp (n : ℕ) : HasDerivAt (fun x : ℝ => (x / witnessR) ^ n)
        ((n : ℝ) * (x / witnessR) ^ (n - 1) * (1 / witnessR)) x :=
      ht.pow n
    have pC := ((((((hp 4).const_mul (23 / 315 : ℝ)).sub ((hp 5).const_mul (2 / 15 : ℝ))).add
      ((hp 6).const_mul (2 / 21 : ℝ))).sub ((hp 7).const_mul (1 / 42 : ℝ))).sub
      ((hp 9).const_mul (1 / 1260 : ℝ))).add ((hp 11).const_mul (1 / 2772 : ℝ)) |>.sub
      ((hp 13).const_mul (1 / 36036 : ℝ)) |>.const_mul (witnessR ^ 13 / 8)
    refine ((hderiv_hi x).sub pC).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl) |>.congr_deriv ?_
    dsimp [envLo, envHi, polyDiffDivX]
    field_simp [hR.ne']
    ring
  have heval_lo : (∫ x in (0 : ℝ)..(2 * witnessR), envLo x) =
      ((16019 / 6930 : ℝ) + witnessR - witnessR ^ 2 / 8 * (153 / 65)) *
        autocorr cubicQuinticSource 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv_lo x)
      (hcont_lo.intervalIntegrable _ _), hac0]
    dsimp [antiHi, antiX2]
    field_simp [hR.ne']
    norm_num
    ring
  obtain ⟨htail_lo, htail_hi⟩ := tail_archLevySinhWeight_two_witnessR_bounds
  rw [hsplit, hout_eq]
  rw [heval_hi] at hin_le
  rw [heval_lo] at hin_ge
  constructor
  · have hm := mul_le_mul_of_nonneg_left htail_lo hac0_pos.le
    linarith
  · have hm := mul_le_mul_of_nonneg_left htail_hi hac0_pos.le
    linarith

private theorem polar_cubicQuinticSource_bounds :
    -(2 / 25 : ℝ) * autocorr cubicQuinticSource 0 ≤
      2 * (∫ x in Ici (0 : ℝ), polarDensity x * autocorr cubicQuinticSource x) ∧
    2 * (∫ x in Ici (0 : ℝ), polarDensity x * autocorr cubicQuinticSource x) ≤ 0 := by
  have hf2 : MemLp (cubicQuinticSource : ℝ → ℝ) 2 volume :=
    continuous_cubicQuinticFun.memLp_of_hasCompactSupport hasCompactSupport_cubicQuinticFun
  have hmom := _root_.RHTower.integral_polar_autocorr_eq_moments_of_memLp
    hf2 hasCompactSupport_cubicQuinticFun
  have hneg_mom : (∫ u, Real.exp (-(u / 2)) * cubicQuinticSource u) =
      -(∫ u, Real.exp (u / 2) * cubicQuinticSource u) := by
    calc (∫ u, Real.exp (-(u / 2)) * cubicQuinticSource u)
        = ∫ u, Real.exp (-((-u) / 2)) * cubicQuinticFun (-u) :=
          (integral_neg_eq_self (fun u => Real.exp (-(u / 2)) * cubicQuinticFun u) volume).symm
      _ = ∫ u, -(Real.exp (u / 2) * cubicQuinticFun u) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          change Real.exp (-((-u) / 2)) * cubicQuinticFun (-u) =
            -(Real.exp (u / 2) * cubicQuinticFun u)
          rw [cubicQuinticFun_neg, neg_div, neg_neg]
          ring
      _ = -(∫ u, Real.exp (u / 2) * cubicQuinticSource u) := integral_neg _
  rw [hmom, hneg_mom]
  constructor
  · have hint_f : Integrable (cubicQuinticSource : ℝ → ℝ) :=
      continuous_cubicQuinticFun.integrable_of_hasCompactSupport hasCompactSupport_cubicQuinticFun
    have hint_ef : Integrable (fun u => Real.exp (u / 2) * cubicQuinticSource u) :=
      ((by fun_prop : Continuous fun u : ℝ => Real.exp (u / 2)).mul
        continuous_cubicQuinticFun).integrable_of_hasCompactSupport
        hasCompactSupport_cubicQuinticFun.mul_left
    have hzero_f : (∫ u, (cubicQuinticSource : ℝ → ℝ) u) = 0 := by
      have h := integral_neg_eq_self cubicQuinticFun volume
      have h2 : (∫ u, cubicQuinticFun (-u)) = -(∫ u, cubicQuinticFun u) := by
        simp_rw [cubicQuinticFun_neg]; exact integral_neg _
      change (∫ u, cubicQuinticFun u) = 0
      linarith
    have hsub : (∫ u, Real.exp (u / 2) * cubicQuinticSource u) =
        ∫ u, (Real.exp (u / 2) - 1) * cubicQuinticSource u := by
      have h1 : (∫ u, (Real.exp (u / 2) - 1) * cubicQuinticSource u) =
          (∫ u, Real.exp (u / 2) * cubicQuinticSource u) - ∫ u, cubicQuinticSource u := by
        rw [← integral_sub hint_ef hint_f]
        exact integral_congr_ae (Eventually.of_forall fun _ => by ring)
      linarith
    have hcompl : ∀ u : ℝ, u ∉ Icc (-witnessR) witnessR →
        |(Real.exp (u / 2) - 1) * cubicQuinticSource u| = 0 := fun u hu => by
      have habs : witnessR < |u| := not_le.mp fun h => hu (abs_le.mp h)
      change |(Real.exp (u / 2) - 1) * cubicQuinticFun u| = 0
      rw [cubicQuinticFun_eq_zero_of_lt habs, mul_zero, abs_zero]
    have habs_sharp : |∫ u, Real.exp (u / 2) * cubicQuinticSource u| ≤
        ∫ u in (-witnessR)..witnessR, (13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2)) := by
      rw [hsub]
      calc |∫ u, (Real.exp (u / 2) - 1) * cubicQuinticSource u|
          ≤ ∫ u, |(Real.exp (u / 2) - 1) * cubicQuinticSource u| := abs_integral_le_integral_abs
        _ = ∫ u in Icc (-witnessR) witnessR, |(Real.exp (u / 2) - 1) * cubicQuinticSource u| :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl).symm
        _ ≤ ∫ u in Icc (-witnessR) witnessR, (13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2)) := by
          refine setIntegral_mono_on (hint_ef.sub hint_f |>.congr
            (Eventually.of_forall fun _ => by dsimp; ring)).abs.integrableOn
            ((by fun_prop : Continuous fun u : ℝ =>
              (13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2))).integrableOn_Icc)
            measurableSet_Icc fun u hu => ?_
          have hu_abs : |u| ≤ witnessR := abs_le.mpr hu
          have hy_le1 : |u / 2| ≤ 1 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; dsimp [witnessR] at hu_abs; linarith
          have hb2 := Real.exp_bound hy_le1 (n := 2) (by norm_num)
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
            Nat.factorial, Nat.cast_one, Nat.cast_ofNat, div_one, zero_add] at hb2
          have hexp_diff : |Real.exp (u / 2) - 1| ≤ (13 / 20 : ℝ) * |u| := by
            have htri : |Real.exp (u / 2) - 1| ≤
                |Real.exp (u / 2) - (1 + u / 2)| + |u / 2| := by
              have : Real.exp (u / 2) - 1 = (Real.exp (u / 2) - (1 + u / 2)) + u / 2 := by ring
              rw [this]; exact abs_add_le _ _
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at htri hb2
            dsimp [witnessR] at hu_abs
            norm_num at hb2
            nlinarith [mul_nonneg (abs_nonneg u) (sub_nonneg.mpr hu_abs)]
          change |(Real.exp (u / 2) - 1) * cubicQuinticFun u| ≤ _
          unfold cubicQuinticFun
          rw [if_pos hu_abs, abs_mul, abs_mul, abs_pow]
          have hnonneg : 0 ≤ witnessR ^ 2 - u ^ 2 := by
            rw [← sq_abs u]; nlinarith [abs_nonneg u, hu_abs]
          rw [abs_of_nonneg hnonneg]
          calc |Real.exp (u / 2) - 1| * (|u| ^ 3 * (witnessR ^ 2 - u ^ 2))
              ≤ ((13 / 20 : ℝ) * |u|) * (|u| ^ 3 * (witnessR ^ 2 - u ^ 2)) :=
                mul_le_mul_of_nonneg_right hexp_diff (mul_nonneg (pow_nonneg (abs_nonneg u) 3) hnonneg)
            _ = (13 / 20 : ℝ) * (|u| ^ 4 * (witnessR ^ 2 - u ^ 2)) := by ring
            _ = (13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2)) := by
                have h4 : |u| ^ 4 = u ^ 4 := by
                  calc |u| ^ 4 = (|u| ^ 2) ^ 2 := by ring
                    _ = (u ^ 2) ^ 2 := by rw [sq_abs]
                    _ = u ^ 4 := by ring
                rw [h4]
        _ = ∫ u in (-witnessR)..witnessR, (13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2)) := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by dsimp [witnessR]; norm_num)]
    have heval_u4 : (∫ u in (-witnessR)..witnessR, (13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2))) =
        (13 / 175 : ℝ) * witnessR ^ 7 := by
      have hd : ∀ u : ℝ, HasDerivAt
          (fun t : ℝ => (13 / 20 : ℝ) * (witnessR ^ 2 * (t ^ 5 / 5) - t ^ 7 / 7))
          ((13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2))) u := fun u => by
        have p5 := ((hasDerivAt_pow 5 u).div_const 5).const_mul (witnessR ^ 2)
        have p7 := (hasDerivAt_pow 7 u).div_const 7
        refine ((p5.sub p7).const_mul (13 / 20 : ℝ)).congr_deriv ?_
        ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
        ((by fun_prop : Continuous fun u : ℝ =>
          (13 / 20 : ℝ) * (u ^ 4 * (witnessR ^ 2 - u ^ 2))).intervalIntegrable _ _)]
      ring
    rw [heval_u4] at habs_sharp
    have hsq_le : (∫ u, Real.exp (u / 2) * cubicQuinticSource u) ^ 2 ≤
        ((13 / 175 : ℝ) * witnessR ^ 7) ^ 2 := by
      rw [← sq_abs (∫ u, Real.exp (u / 2) * cubicQuinticSource u)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs_sharp 2
    have hac0 : autocorr cubicQuinticSource 0 = (16 / 693 : ℝ) * witnessR ^ 11 := by
      rw [autocorr_cubicQuinticSource_eq le_rfl (by dsimp [witnessR]; norm_num)]
      dsimp [unitCubicQuinticCorr]; norm_num; ring
    rw [hac0]
    dsimp [witnessR] at hsq_le ⊢
    norm_num at hsq_le ⊢
    have hmul : (∫ u, Real.exp (u / 2) * cubicQuinticSource u) *
        (∫ u, Real.exp (u / 2) * cubicQuinticSource u) =
        (∫ u, Real.exp (u / 2) * cubicQuinticSource u) ^ 2 := (sq _).symm
    rw [hmul]
    linarith
  · nlinarith [sq_nonneg (∫ u, Real.exp (u / 2) * cubicQuinticSource u)]

private theorem re_weilFullFunctional_liouville_eq_add_atom_two (g : C_c(ℝ, ℝ)) {R : ℝ}
    (hR : 0 ≤ R) (h2R : 2 * R < Real.log 3) (hgR : ∀ x, R < |x| → g x = 0) :
    (weilFullFunctional liouvilleTwistedVonMangoldt
      (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re =
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)))).re +
      2 * ((Real.sqrt 2 * Real.log 2) * autocorr g (Real.log 2)) := by
  have hwt : EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ)) =
      fun x => (autocorr g x : ℂ) := by
    funext x
    simpa only [neg_neg, autocorr_neg] using (autocorr_eq_weilTest g (-x)).symm
  have htsupp_k : tsupport (EF.weilTest (fun u => (g u : ℂ)) (fun u => (g u : ℂ))) ⊆
      Icc (-(2 * R)) (2 * R) := by
    rw [hwt]
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    by_contra hxI
    have hx' : 2 * R < |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
      rcases hxI with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    exact hx (by simp [autocorr_eq_zero_of_far hgR hx'])
  have hatom := weilFullFunctional_sub_eq_atom_two htsupp_k h2R
    liouvilleTwistedVonMangoldt (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  have hΛ2 : (ArithmeticFunction.vonMangoldt 2 : ℝ) = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hcoef2_eq : 2 * (Real.log 2 / Real.sqrt 2) = Real.sqrt 2 * Real.log 2 := by
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hre_diff := congrArg Complex.re hatom
  rw [Complex.sub_re, hwt] at hre_diff
  simp only [hΛ2, liouvilleTwistedVonMangoldt_two, autocorr_neg, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hre_diff
  have hring : ((Real.log 2 - -Real.log 2) / Real.sqrt 2) *
      (autocorr g (Real.log 2) + autocorr g (Real.log 2)) =
      2 * (2 * (Real.log 2 / Real.sqrt 2) * autocorr g (Real.log 2)) := by ring
  rw [hring, hcoef2_eq] at hre_diff
  rw [hwt]
  linarith

private theorem two_mul_oneHundredNineTwoHundredths_lt_log_three :
    2 * (109 / 200 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have he1 := Real.exp_one_lt_d9
  have hb := Real.exp_bound (x := (9 / 100 : ℝ)) (by norm_num) (n := 2) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.factorial,
    Nat.cast_one, Nat.cast_ofNat, div_one, zero_add] at hb
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 9 / 100)] at hb
  have he2 : Real.exp (9 / 100 : ℝ) < 1.1 := by linarith [(abs_le.mp hb).2]
  calc Real.exp (2 * (109 / 200 : ℝ)) = Real.exp (1 + 9 / 100) := by norm_num
    _ = Real.exp 1 * Real.exp (9 / 100) := Real.exp_add 1 (9 / 100)
    _ < 3 := by nlinarith [Real.exp_pos 1, Real.exp_pos (9 / 100 : ℝ)]

private theorem unsmoothed_cubicQuintic_separation :
    (1 / 25 : ℝ) * autocorr cubicQuinticSource 0 <
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (cubicQuinticSource u : ℂ))
          (fun u => (cubicQuinticSource u : ℂ)))).re ∧
    (weilFullFunctional liouvilleTwistedVonMangoldt
      (EF.weilTest (fun u => (cubicQuinticSource u : ℂ))
        (fun u => (cubicQuinticSource u : ℂ)))).re <
      -(3 / 10 : ℝ) * autocorr cubicQuinticSource 0 := by
  have h2R_lt_log3 : 2 * witnessR < Real.log 3 := by
    have := two_mul_oneHundredNineTwoHundredths_lt_log_three
    dsimp [witnessR]; linarith
  have hprime_sum : (∑' n : ℕ, primeTerm (autocorr cubicQuinticSource) n) =
      (Real.log 2 / Real.sqrt 2) * autocorr cubicQuinticSource (Real.log 2) := by
    rw [tsum_eq_single 2 fun n hn => ?_]
    · unfold primeTerm SignedPrimePolar.primeWeight
      rw [if_pos (by norm_num : 2 ≤ 2), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    · by_cases h2 : 2 ≤ n
      · have h3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
        have hlog : 2 * witnessR < |Real.log n| := by
          have hl : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) h3
          rw [abs_of_pos (by dsimp [witnessR] at h2R_lt_log3; linarith)]
          linarith
        unfold primeTerm
        change (if 2 ≤ n then SignedPrimePolar.primeWeight n *
          autocorr cubicQuinticFun (Real.log n) else 0) = 0
        rw [autocorr_eq_zero_of_far (fun _ hu => cubicQuinticFun_eq_zero_of_lt hu) hlog, mul_zero,
          ite_self]
      · unfold primeTerm
        rw [if_neg h2]
  have hac0 : autocorr cubicQuinticSource 0 = (16 / 693 : ℝ) * witnessR ^ 11 := by
    rw [autocorr_cubicQuinticSource_eq le_rfl (by dsimp [witnessR]; norm_num)]
    dsimp [unitCubicQuinticCorr]; norm_num; ring
  have hac0_pos : 0 < autocorr cubicQuinticSource 0 := by
    rw [hac0]; dsimp [witnessR]; positivity
  have hl2_lo := Real.log_two_gt_d9
  have hl2_hi := Real.log_two_lt_d9
  have hac_l2 : -(47 / 100 : ℝ) * autocorr cubicQuinticSource 0 ≤
        autocorr cubicQuinticSource (Real.log 2) ∧
      autocorr cubicQuinticSource (Real.log 2) ≤ -(41 / 100 : ℝ) * autocorr cubicQuinticSource 0 := by
    have hlog2_le : Real.log 2 ≤ 2 * witnessR := by dsimp [witnessR]; linarith
    rw [autocorr_cubicQuinticSource_eq (by linarith) hlog2_le, hac0]
    set t : ℝ := Real.log 2 / witnessR
    have ht_lo : (641802 / 500000 : ℝ) < t := by dsimp [t, witnessR]; linarith
    have ht_hi : t < 641804 / 500000 := by dsimp [t, witnessR]; linarith
    have ht0 : 0 ≤ t := by linarith
    have hp2_lo : (641802 / 500000 : ℝ) ^ 2 < t ^ 2 := pow_lt_pow_left₀ ht_lo (by norm_num) (by norm_num)
    have hp2_hi : t ^ 2 < (641804 / 500000 : ℝ) ^ 2 := pow_lt_pow_left₀ ht_hi ht0 (by norm_num)
    have hp3_lo : (641802 / 500000 : ℝ) ^ 3 < t ^ 3 := pow_lt_pow_left₀ ht_lo (by norm_num) (by norm_num)
    have hp3_hi : t ^ 3 < (641804 / 500000 : ℝ) ^ 3 := pow_lt_pow_left₀ ht_hi ht0 (by norm_num)
    have hp4_lo : (641802 / 500000 : ℝ) ^ 4 < t ^ 4 := pow_lt_pow_left₀ ht_lo (by norm_num) (by norm_num)
    have hp4_hi : t ^ 4 < (641804 / 500000 : ℝ) ^ 4 := pow_lt_pow_left₀ ht_hi ht0 (by norm_num)
    have hp5_lo : (641802 / 500000 : ℝ) ^ 5 < t ^ 5 := pow_lt_pow_left₀ ht_lo (by norm_num) (by norm_num)
    have hp5_hi : t ^ 5 < (641804 / 500000 : ℝ) ^ 5 := pow_lt_pow_left₀ ht_hi ht0 (by norm_num)
    have hp7_lo : (641802 / 500000 : ℝ) ^ 7 < t ^ 7 := pow_lt_pow_left₀ ht_lo (by norm_num) (by norm_num)
    have hp7_hi : t ^ 7 < (641804 / 500000 : ℝ) ^ 7 := pow_lt_pow_left₀ ht_hi ht0 (by norm_num)
    have hp9_lo : (641802 / 500000 : ℝ) ^ 9 < t ^ 9 := pow_lt_pow_left₀ ht_lo (by norm_num) (by norm_num)
    have hp9_hi : t ^ 9 < (641804 / 500000 : ℝ) ^ 9 := pow_lt_pow_left₀ ht_hi ht0 (by norm_num)
    have hp11_lo : (641802 / 500000 : ℝ) ^ 11 < t ^ 11 := pow_lt_pow_left₀ ht_lo (by norm_num) (by norm_num)
    have hp11_hi : t ^ 11 < (641804 / 500000 : ℝ) ^ 11 := pow_lt_pow_left₀ ht_hi ht0 (by norm_num)
    have hR11 : 0 < witnessR ^ 11 := by dsimp [witnessR]; positivity
    dsimp [unitCubicQuinticCorr]
    norm_num at hp2_lo hp2_hi hp3_lo hp3_hi hp4_lo hp4_hi hp5_lo hp5_hi hp7_lo hp7_hi hp9_lo hp9_hi hp11_lo hp11_hi
    constructor
    · have hk_lb : -(47 / 100 : ℝ) * (16 / 693) ≤
          16 / 693 - 92 / 315 * t ^ 2 + 2 / 3 * t ^ 3 - 4 / 7 * t ^ 4 + 1 / 6 * t ^ 5 +
            1 / 140 * t ^ 7 - 1 / 252 * t ^ 9 + 1 / 2772 * t ^ 11 := by linarith
      nlinarith
    · have hk_ub : 16 / 693 - 92 / 315 * t ^ 2 + 2 / 3 * t ^ 3 - 4 / 7 * t ^ 4 + 1 / 6 * t ^ 5 +
          1 / 140 * t ^ 7 - 1 / 252 * t ^ 9 + 1 / 2772 * t ^ 11 ≤
          -(41 / 100 : ℝ) * (16 / 693) := by linarith
      nlinarith
  have hs2_lo : (1414 / 1000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hcoef2_eq : 2 * (Real.log 2 / Real.sqrt 2) = Real.sqrt 2 * Real.log 2 := by
    have hs : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcoef2_lo : (980 / 1000 : ℝ) < Real.sqrt 2 * Real.log 2 := by
    norm_num at hl2_lo; nlinarith
  obtain ⟨hg0_lo, hg0_hi⟩ := gammaBracket_zero_bounds
  obtain ⟨hlev_lo, hlev_hi⟩ := biScaleLevyEnergy_cubicQuinticSource_bounds
  obtain ⟨hpol_lo, hpol_hi⟩ := polar_cubicQuinticSource_bounds
  have hzeta_eq := re_weilFullFunctional_eq_of_compact_finite_jump cubicQuinticSource
    (integrableOn_levy_of_lipschitz cubicQuinticSource lipschitz_cubicQuinticSource)
  rw [fullPairing, hprime_sum] at hzeta_eq
  have hpr_neg : autocorr cubicQuinticSource (Real.log 2) < 0 := by nlinarith [hac_l2.2]
  have h2pr_ub : (Real.sqrt 2 * Real.log 2) * autocorr cubicQuinticSource (Real.log 2) ≤
      -(980 / 1000 * (41 / 100)) * autocorr cubicQuinticSource 0 := by
    calc (Real.sqrt 2 * Real.log 2) * autocorr cubicQuinticSource (Real.log 2)
        ≤ (980 / 1000 : ℝ) * autocorr cubicQuinticSource (Real.log 2) :=
          mul_le_mul_of_nonpos_right hcoef2_lo.le hpr_neg.le
      _ ≤ (980 / 1000 : ℝ) * (-(41 / 100 : ℝ) * autocorr cubicQuinticSource 0) :=
          mul_le_mul_of_nonneg_left hac_l2.2 (by norm_num)
      _ = -(980 / 1000 * (41 / 100)) * autocorr cubicQuinticSource 0 := by ring
  have hliouv_id := re_weilFullFunctional_liouville_eq_add_atom_two cubicQuinticSource
    (by dsimp [witnessR]; norm_num) h2R_lt_log3
    (fun _ hu => cubicQuinticFun_eq_zero_of_lt hu)
  dsimp [witnessR] at hlev_lo hlev_hi
  have hrew_z : EF.gammaBracket 0 * autocorr cubicQuinticSource 0 + biScaleLevyEnergy cubicQuinticSource -
      2 * (Real.log 2 / Real.sqrt 2 * autocorr cubicQuinticSource (Real.log 2) -
        ∫ x in Ici (0 : ℝ), polarDensity x * autocorr cubicQuinticSource x) =
      EF.gammaBracket 0 * autocorr cubicQuinticSource 0 + biScaleLevyEnergy cubicQuinticSource -
        (Real.sqrt 2 * Real.log 2) * autocorr cubicQuinticSource (Real.log 2) +
        2 * (∫ x in Ici (0 : ℝ), polarDensity x * autocorr cubicQuinticSource x) := by
    linear_combination -autocorr cubicQuinticSource (Real.log 2) * hcoef2_eq
  rw [hrew_z] at hzeta_eq
  constructor
  · rw [hzeta_eq]
    have hg_term : -(5380 / 1000 : ℝ) * autocorr cubicQuinticSource 0 ≤
        EF.gammaBracket 0 * autocorr cubicQuinticSource 0 :=
      mul_le_mul_of_nonneg_right hg0_lo hac0_pos.le
    norm_num at hlev_lo h2pr_ub
    linarith
  · rw [hliouv_id, hzeta_eq]
    have hg_term : EF.gammaBracket 0 * autocorr cubicQuinticSource 0 ≤
        -(5330 / 1000 : ℝ) * autocorr cubicQuinticSource 0 :=
      mul_le_mul_of_nonneg_right hg0_hi hac0_pos.le
    norm_num at hlev_hi h2pr_ub
    linarith

private theorem mollifier_even (k : ℕ) (t : ℝ) :
    CHMDDoobGraph.mollifier k (-t) = CHMDDoobGraph.mollifier k t := by
  unfold CHMDDoobGraph.mollifier
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, ContDiffBump.neg]

private theorem smooth_odd_of_odd {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (k : ℕ) (x : ℝ) :
    CHMDDoobGraph.smooth f k (-x) = -CHMDDoobGraph.smooth f k x := by
  change (∫ t, CHMDDoobGraph.mollifier k t * f (-x - t)) =
    -(∫ t, CHMDDoobGraph.mollifier k t * f (x - t))
  calc (∫ t, CHMDDoobGraph.mollifier k t * f (-x - t))
      = ∫ t, CHMDDoobGraph.mollifier k (-t) * f (-x - -t) :=
        (integral_neg_eq_self (fun t => CHMDDoobGraph.mollifier k t * f (-x - t)) volume).symm
    _ = ∫ t, -(CHMDDoobGraph.mollifier k t * f (x - t)) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        change CHMDDoobGraph.mollifier k (-t) * f (-x - -t) =
          -(CHMDDoobGraph.mollifier k t * f (x - t))
        rw [mollifier_even, show -x - -t = -(x - t) by ring, hodd]
        ring
    _ = -(∫ t, CHMDDoobGraph.mollifier k t * f (x - t)) := integral_neg _

private theorem smooth_eq_zero_of_radius {f : ℝ → ℝ} {R : ℝ} (hf : ∀ x, R < |x| → f x = 0)
    (k : ℕ) {x : ℝ} (hx : R + 1 / (4 * ((k : ℝ) + 1)) < |x|) :
    CHMDDoobGraph.smooth f k x = 0 := by
  change (∫ t, CHMDDoobGraph.mollifier k t * f (x - t)) = 0
  have h0 : ∀ t, CHMDDoobGraph.mollifier k t * f (x - t) = 0 := fun t => by
    by_cases ht : 1 / (4 * ((k : ℝ) + 1)) < |t|
    · have hm0 : CHMDDoobGraph.mollifier k t = 0 := by
        apply Function.notMem_support.mp
        rw [CHMDDoobGraph.mollifier, ContDiffBump.support_normed_eq, Metric.mem_ball,
          dist_zero_right, Real.norm_eq_abs]
        change ¬ |t| < 1 / (4 * ((k : ℝ) + 1))
        linarith
      rw [hm0, zero_mul]
    · push Not at ht
      have hxt : R < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        linarith
      rw [hf _ hxt, mul_zero]
  simp only [h0, integral_zero]

/-- **Simultaneous Smooth Odd Two-Prime Witness on `[-23/40, 23/40]`:**
There exists an explicit odd `F ∈ C²_c(ℝ)` supported in `[-23/40, 23/40]` with `0 < ∫ F²` such
that simultaneously `(1 / 25) ∫ F² < Re W_ζ(F ⋆ F̃)` and `Re W_{λΛ}(F ⋆ F̃) < -(3 / 10) ∫ F² < 0`. -/
theorem exists_smooth_odd_twentyThreeFortieths_zeta_pos_liouville_neg :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ x, 23 / 40 < |x| → F x = 0) ∧ 0 < (∫ x, F x ^ 2) ∧
      (1 / 25 : ℝ) * (∫ x, F x ^ 2) <
        (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re ∧
      (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re <
        -(3 / 10 : ℝ) * (∫ x, F x ^ 2) := by
  let f := cubicQuinticSource
  have hfc : Continuous (f : ℝ → ℝ) := map_continuous f
  obtain ⟨M, hM_norm⟩ := hfc.bounded_above_of_compact_support f.hasCompactSupport
  have hM : ∀ x, |f x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact hM_norm x
  have hfR : ∀ x, witnessR < |x| → f x = 0 := fun _ hx => cubicQuinticFun_eq_zero_of_lt hx
  have hf2 : MemLp (f : ℝ → ℝ) 2 volume := hfc.memLp_of_hasCompactSupport f.hasCompactSupport
  have hJ := integrableOn_levy_of_lipschitz f lipschitz_cubicQuinticSource
  have hac0_pos : 0 < autocorr f 0 := by
    change 0 < autocorr cubicQuinticSource 0
    rw [autocorr_cubicQuinticSource_eq le_rfl (by dsimp [witnessR]; norm_num)]
    dsimp [unitCubicQuinticCorr, witnessR]; positivity
  obtain ⟨hzeta_pos, hliouv_neg⟩ := unsmoothed_cubicQuintic_separation
  have h2R_f : 2 * witnessR < Real.log 3 := by
    have := two_mul_oneHundredNineTwoHundredths_lt_log_three
    dsimp [witnessR]; linarith
  have hliouv_f := re_weilFullFunctional_liouville_eq_add_atom_two f
    (by dsimp [witnessR]; norm_num) h2R_f hfR
  have ht_ac0 := autocorr_smooth_tendsto hfc hM hfR 0
  have ht_ac2 := autocorr_smooth_tendsto hfc hM hfR (Real.log 2)
  have ht_zeta := re_weilFullFunctional_smooth_tendsto f hJ
  have ht_liouv : Tendsto (fun k : ℕ =>
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (smooth f k u : ℂ)) (fun u => (smooth f k u : ℂ)))).re +
        2 * ((Real.sqrt 2 * Real.log 2) * autocorr (smooth f k) (Real.log 2))) atTop
      (𝓝 ((weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re)) := by
    rw [hliouv_f]
    exact ht_zeta.add (((ht_ac2.const_mul (Real.sqrt 2 * Real.log 2)).const_mul 2))
  have hev_norm : ∀ᶠ k : ℕ in atTop, 0 < autocorr (smooth f k) 0 :=
    ht_ac0.eventually (Ioi_mem_nhds hac0_pos)
  have hev_zeta : ∀ᶠ k : ℕ in atTop,
      (1 / 25 : ℝ) * autocorr (smooth f k) 0 <
        (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun u => (smooth f k u : ℂ)) (fun u => (smooth f k u : ℂ)))).re := by
    have hdiff := ht_zeta.sub (ht_ac0.const_mul (1 / 25 : ℝ))
    have hpos : 0 < (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re - (1 / 25 : ℝ) * autocorr f 0 :=
      sub_pos.mpr hzeta_pos
    exact (hdiff.eventually (Ioi_mem_nhds hpos)).mono fun _ hk => sub_pos.mp hk
  have hev_liouv : ∀ᶠ k : ℕ in atTop,
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (smooth f k u : ℂ)) (fun u => (smooth f k u : ℂ)))).re +
        2 * ((Real.sqrt 2 * Real.log 2) * autocorr (smooth f k) (Real.log 2)) <
        -(3 / 10 : ℝ) * autocorr (smooth f k) 0 := by
    have hdiff := ht_liouv.sub (ht_ac0.const_mul (-(3 / 10 : ℝ)))
    have hneg : (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re -
        (-(3 / 10 : ℝ) * autocorr f 0) < 0 := sub_neg.mpr hliouv_neg
    exact (hdiff.eventually (Iio_mem_nhds hneg)).mono fun _ hk => sub_neg.mp hk
  obtain ⟨k, hk50, hknorm, hkzeta, hkliouv⟩ :=
    ((eventually_ge_atTop 50).and (hev_norm.and (hev_zeta.and hev_liouv))).exists
  have hk_narrow : ∀ x : ℝ, 109 / 200 < |x| → smooth f k x = 0 := by
    intro x hx
    apply smooth_eq_zero_of_radius hfR k
    have hk_cast : (50 : ℝ) ≤ k := by exact_mod_cast hk50
    have hrad : 1 / (4 * ((k : ℝ) + 1)) ≤ 1 / 204 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    dsimp [witnessR]
    linarith
  have hk_ac0 : autocorr (smooth f k) 0 = ∫ x, (smooth f k x) ^ 2 := by
    unfold autocorr
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change smooth f k x * smooth f k (x + 0) = (smooth f k x) ^ 2
    rw [add_zero, sq]
  have hk_liouv_eq := re_weilFullFunctional_liouville_eq_add_atom_two (smoothCompactSource f k)
    (by norm_num) two_mul_oneHundredNineTwoHundredths_lt_log_three hk_narrow
  change (weilFullFunctional liouvilleTwistedVonMangoldt
      (EF.weilTest (fun u => (smooth f k u : ℂ)) (fun u => (smooth f k u : ℂ)))).re = _ at hk_liouv_eq
  refine ⟨smooth f k, (smooth_contDiff hf2 k).of_le (by norm_num),
    smooth_compact f.hasCompactSupport k,
    smooth_odd_of_odd cubicQuinticFun_neg k,
    fun x hx => hk_narrow x (by linarith),
    hk_ac0 ▸ hknorm,
    hk_ac0 ▸ hkzeta,
    ?_⟩
  rw [hk_liouv_eq, ← hk_ac0]
  exact hkliouv

/-- **Strict Negativity of the Liouville Ground Eigenvalue on `[-23/40, 23/40]`:**
`liouvilleWindowGroundEigenvalue (23 / 40)` is finite (bounded below) and strictly less than
`-(3 / 10) < 0`. -/
theorem liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths :
    BddBelow (liouvilleWindowRayleighSet (23 / 40)) ∧
      liouvilleWindowGroundEigenvalue (23 / 40) < -(3 / 10 : ℝ) := by
  have hbdd := bddBelow_liouvilleWindowRayleighSet (by norm_num : (0 : ℝ) < 23 / 40)
  refine ⟨hbdd, ?_⟩
  obtain ⟨F, hF2, hFc, _, hsupp, hnorm, _, hliouv⟩ :=
    exists_smooth_odd_twentyThreeFortieths_zeta_pos_liouville_neg
  set qF : ℝ := (weilFullFunctional liouvilleTwistedVonMangoldt
    (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re / (∫ x, F x ^ 2)
  have hmem : qF ∈ liouvilleWindowRayleighSet (23 / 40) := ⟨F, hF2, hFc, hsupp, hnorm, rfl⟩
  have hlt : qF < -(3 / 10 : ℝ) := (div_lt_iff₀ hnorm).mpr hliouv
  exact (csInf_le hbdd hmem).trans_lt hlt

/-! ## §3. Lattice-to-Continuum Prime-Tower Obstruction & Pole-Neutralized Width Law (Question 6) -/

/-- Squared dyadic Sobolev `H¹` norm `(∫ F²) + (∫ (F')²)` on logarithmic coordinates `x = log u`. -/
def dyadicH1NormSq (F : ℝ → ℝ) : ℝ :=
  (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2

/-- **Integer-Lattice Prime-Divisor Vanishing (`towerOddPrimeSide_eq_zero_of_lt`):**
On the integer lattice `[1, X]`, every prime `p > X` satisfies `towerOddPrimeSide q X p K = 0`
identically for every truncation `K : ℕ` because `p^k` (`k ≥ 1`) has neither multiples `a p^k ≤ X`
(`a ≥ 2`) nor proper integer divisors `d ∣ p^k` (`1 < d < p^k`) inside `[2, X]`. -/
theorem towerOddPrimeSide_eq_zero_of_lt (q : ℕ → ℝ) {X p : ℕ}
    (hX : 1 ≤ X) (hp : p.Prime) (hXp : X < p) (hq : ∀ n, X < n → q n = 0) (K : ℕ) :
    towerOddPrimeSide q X p K = 0 := by
  unfold towerOddPrimeSide
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hpk_ge_p : p ≤ p ^ k := Nat.le_self_pow (by omega) p
  have hpk2 : 2 ≤ p ^ k := hp.two_le.trans hpk_ge_p
  rw [two_mul_ratioCorr_sub_productCorr_eq_interior q hX hpk2]
  have hrat0 : (∑ a ∈ Finset.Icc 2 X, q a * q (a * p ^ k)) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    have ha2 : 2 ≤ a := (Finset.mem_Icc.mp ha).1
    have hgt : X < a * p ^ k := by nlinarith
    rw [hq _ hgt, mul_zero]
  have hprod0 : (∑ d ∈ ((p ^ k).divisors.erase 1).erase (p ^ k), q d * q (p ^ k / d)) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    have hd1 : d ≠ 1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).1
    have hdvd : d ∣ p ^ k :=
      Nat.dvd_of_mem_divisors (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd))
    obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hj1 : 1 ≤ j := by
      by_contra hj0
      have : j = 0 := by omega
      subst this
      exact hd1 rfl
    have hgt : X < p ^ j := hXp.trans_le (Nat.le_self_pow (by omega) p)
    rw [hq _ hgt, zero_mul]
  rw [hrat0, hprod0, mul_zero, sub_self, mul_zero]

/-- Smooth unit-centered bump supported in `[3/4, 5/4]` (width `1/2 < log 2`) and equal to `1` on
`[7/8, 9/8]`, defined by translating `WeilOneSided.narrowBump 0` (`rIn = 1/8, rOut = 1/4`). -/
private def narrowUnitBump (u : ℝ) : ℝ :=
  WeilOneSided.narrowBump 0 (u - 1)

private theorem narrowUnitBump_contDiff : ContDiff ℝ 2 narrowUnitBump := by
  have h0 : ContDiff ℝ 2 (fun t : ℝ => (WeilOneSided.narrowBumpC 0 t).re) :=
    Complex.reCLM.contDiff.comp ((WeilOneSided.contDiff_narrowBumpC 0).of_le (by norm_cast))
  have heq : (fun t : ℝ => (WeilOneSided.narrowBumpC 0 t).re) =
      fun t : ℝ => (WeilOneSided.narrowBump 0 t : ℝ) := by
    funext t; simp [WeilOneSided.narrowBumpC]
  rw [heq] at h0
  exact h0.comp (contDiff_id.sub contDiff_const)

private theorem narrowUnitBump_hasCompactSupport : HasCompactSupport narrowUnitBump :=
  (WeilOneSided.narrowBump 0).hasCompactSupport.comp_homeomorph (Homeomorph.subRight (1 : ℝ))

private theorem narrowUnitBump_nonneg (u : ℝ) : 0 ≤ narrowUnitBump u :=
  (WeilOneSided.narrowBump 0).nonneg' (u - 1)

private theorem narrowUnitBump_eq_zero_of_notMem {u : ℝ} (hu : u ∉ Icc (3 / 4 : ℝ) (5 / 4)) :
    narrowUnitBump u = 0 := by
  unfold narrowUnitBump
  refine Function.notMem_support.mp fun hs => hu ?_
  have hrOut : (WeilOneSided.narrowBump 0).rOut = 1 / 4 := by
    change (1 : ℝ) / (4 * (((0 : ℕ) : ℝ) + 1)) = 1 / 4
    norm_num
  rw [(WeilOneSided.narrowBump 0).support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, hrOut] at hs
  have h := abs_lt.mp hs
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem narrowUnitBump_eq_one_of_mem {u : ℝ} (hu : u ∈ Icc (7 / 8 : ℝ) (9 / 8)) :
    narrowUnitBump u = 1 := by
  unfold narrowUnitBump
  refine (WeilOneSided.narrowBump 0).one_of_mem_closedBall ?_
  have hrIn : (WeilOneSided.narrowBump 0).rIn = 1 / 8 := by
    change (1 : ℝ) / (8 * (((0 : ℕ) : ℝ) + 1)) = 1 / 8
    norm_num
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le, hrIn]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

attribute [irreducible] narrowUnitBump

/-- Translated odd smooth bump `edgeTowerBump A` localized near `±(A - 1)` inside `[-A, A]`. -/
def edgeTowerBump (A x : ℝ) : ℝ :=
  narrowUnitBump (x - (A - 2)) - narrowUnitBump (-x - (A - 2))

private theorem sq_hasCompactSupport_real {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => g x ^ 2) := by
  have heq : (fun x => g x ^ 2) = g * g := by funext x; exact sq (g x)
  rw [heq]; exact hg.mul_left

private theorem diff_shift_reflect_L2_le {g : ℝ → ℝ} (hg_cont : Continuous g)
    (hg_comp : HasCompactSupport g) (c : ℝ) :
    (∫ x, (g (x - c) - g (-x - c)) ^ 2) ≤ 4 * ∫ u, g u ^ 2 := by
  have hg2 : Integrable (fun u => g u ^ 2) :=
    (hg_cont.pow 2).integrable_of_hasCompactSupport (sq_hasCompactSupport_real hg_comp)
  have h1 : Integrable (fun x => g (x - c) ^ 2) := hg2.comp_sub_right c
  have h2 : Integrable (fun x => g (-x - c) ^ 2) :=
    ((hg2.comp_sub_right c).comp_neg).congr (Eventually.of_forall fun _ => rfl)
  have hdiff_cont : Continuous (fun x => g (x - c) - g (-x - c)) :=
    (hg_cont.comp (continuous_id.sub continuous_const)).sub
      (hg_cont.comp (continuous_id.neg.sub continuous_const))
  have hdiff_comp : HasCompactSupport (fun x => g (x - c) - g (-x - c)) :=
    (hg_comp.comp_homeomorph (Homeomorph.subRight c)).sub
      ((hg_comp.comp_homeomorph (Homeomorph.subRight c)).comp_homeomorph (Homeomorph.neg ℝ))
  have hd2 : Integrable (fun x => (g (x - c) - g (-x - c)) ^ 2) :=
    (hdiff_cont.pow 2).integrable_of_hasCompactSupport (sq_hasCompactSupport_real hdiff_comp)
  calc (∫ x, (g (x - c) - g (-x - c)) ^ 2)
      ≤ ∫ x, (2 * g (x - c) ^ 2 + 2 * g (-x - c) ^ 2) := by
        refine integral_mono hd2 ((h1.const_mul 2).add (h2.const_mul 2)) fun x => ?_
        dsimp only
        nlinarith [sq_nonneg (g (x - c) + g (-x - c))]
    _ = 2 * (∫ x, g (x - c) ^ 2) + 2 * ∫ x, g (-x - c) ^ 2 := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul]
    _ = 4 * ∫ u, g u ^ 2 := by
        have ht1 : (∫ x, g (x - c) ^ 2) = ∫ u, g u ^ 2 :=
          integral_sub_right_eq_self (fun u => g u ^ 2) c
        have ht2 : (∫ x, g (-x - c) ^ 2) = ∫ u, g u ^ 2 := by
          calc (∫ x, g (-x - c) ^ 2)
              = ∫ x, g (- -x - c) ^ 2 :=
                (integral_neg_eq_self (fun x => g (-x - c) ^ 2) volume).symm
            _ = ∫ x, g (x - c) ^ 2 :=
                integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [neg_neg])
            _ = ∫ u, g u ^ 2 := ht1
        rw [ht1, ht2]; ring

private theorem sum_shift_reflect_L2_le {g : ℝ → ℝ} (hg_cont : Continuous g)
    (hg_comp : HasCompactSupport g) (c : ℝ) :
    (∫ x, (g (x - c) + g (-x - c)) ^ 2) ≤ 4 * ∫ u, g u ^ 2 := by
  have hg2 : Integrable (fun u => g u ^ 2) :=
    (hg_cont.pow 2).integrable_of_hasCompactSupport (sq_hasCompactSupport_real hg_comp)
  have h1 : Integrable (fun x => g (x - c) ^ 2) := hg2.comp_sub_right c
  have h2 : Integrable (fun x => g (-x - c) ^ 2) :=
    ((hg2.comp_sub_right c).comp_neg).congr (Eventually.of_forall fun _ => rfl)
  have hsum_cont : Continuous (fun x => g (x - c) + g (-x - c)) :=
    (hg_cont.comp (continuous_id.sub continuous_const)).add
      (hg_cont.comp (continuous_id.neg.sub continuous_const))
  have hsum_comp : HasCompactSupport (fun x => g (x - c) + g (-x - c)) :=
    (hg_comp.comp_homeomorph (Homeomorph.subRight c)).add
      ((hg_comp.comp_homeomorph (Homeomorph.subRight c)).comp_homeomorph (Homeomorph.neg ℝ))
  have hs2 : Integrable (fun x => (g (x - c) + g (-x - c)) ^ 2) :=
    (hsum_cont.pow 2).integrable_of_hasCompactSupport (sq_hasCompactSupport_real hsum_comp)
  calc (∫ x, (g (x - c) + g (-x - c)) ^ 2)
      ≤ ∫ x, (2 * g (x - c) ^ 2 + 2 * g (-x - c) ^ 2) := by
        refine integral_mono hs2 ((h1.const_mul 2).add (h2.const_mul 2)) fun x => ?_
        dsimp only
        nlinarith [sq_nonneg (g (x - c) - g (-x - c))]
    _ = 2 * (∫ x, g (x - c) ^ 2) + 2 * ∫ x, g (-x - c) ^ 2 := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul]
    _ = 4 * ∫ u, g u ^ 2 := by
        have ht1 : (∫ x, g (x - c) ^ 2) = ∫ u, g u ^ 2 :=
          integral_sub_right_eq_self (fun u => g u ^ 2) c
        have ht2 : (∫ x, g (-x - c) ^ 2) = ∫ u, g u ^ 2 := by
          calc (∫ x, g (-x - c) ^ 2)
              = ∫ x, g (- -x - c) ^ 2 :=
                (integral_neg_eq_self (fun x => g (-x - c) ^ 2) volume).symm
            _ = ∫ x, g (x - c) ^ 2 :=
                integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [neg_neg])
            _ = ∫ u, g u ^ 2 := ht1
        rw [ht1, ht2]; ring

private theorem edgeTowerBump_contDiff (A : ℝ) : ContDiff ℝ 2 (edgeTowerBump A) := by
  unfold edgeTowerBump
  exact (narrowUnitBump_contDiff.comp (contDiff_id.sub contDiff_const)).sub
    (narrowUnitBump_contDiff.comp (contDiff_id.neg.sub contDiff_const))

private theorem edgeTowerBump_deriv_eq (A x : ℝ) :
    deriv (edgeTowerBump A) x =
      deriv narrowUnitBump (x - (A - 2)) + deriv narrowUnitBump (-x - (A - 2)) := by
  have h1 : ContDiff ℝ (1 : ℕ) narrowUnitBump :=
    narrowUnitBump_contDiff.of_le (by norm_cast)
  have hb_diff : Differentiable ℝ narrowUnitBump := h1.differentiable (by norm_num)
  have hd1 : HasDerivAt (fun y => narrowUnitBump (y - (A - 2)))
      (deriv narrowUnitBump (x - (A - 2))) x :=
    ((hb_diff (x - (A - 2))).hasDerivAt.comp x
      ((hasDerivAt_id x).sub_const (A - 2))).congr_deriv (mul_one _)
  have hd2 : HasDerivAt (fun y => narrowUnitBump (-y - (A - 2)))
      (-(deriv narrowUnitBump (-x - (A - 2)))) x :=
    ((hb_diff (-x - (A - 2))).hasDerivAt.comp x
      ((hasDerivAt_id x).neg.sub_const (A - 2))).congr_deriv (by ring)
  have hd : HasDerivAt (edgeTowerBump A)
      (deriv narrowUnitBump (x - (A - 2)) + deriv narrowUnitBump (-x - (A - 2))) x := by
    unfold edgeTowerBump
    exact (hd1.sub hd2).congr_deriv (by ring)
  exact hd.deriv

private theorem edgeTowerBump_properties {A : ℝ} (hA : 4 ≤ A) :
    ContDiff ℝ 2 (edgeTowerBump A) ∧
    HasCompactSupport (edgeTowerBump A) ∧
    (∀ x, edgeTowerBump A (-x) = -edgeTowerBump A x) ∧
    (∀ x, A ≤ |x| → edgeTowerBump A x = 0) ∧
    (∀ x, 0 ≤ x → edgeTowerBump A x = narrowUnitBump (x - (A - 2))) ∧
    1 / 4 ≤ dyadicH1NormSq (edgeTowerBump A) ∧
    dyadicH1NormSq (edgeTowerBump A) ≤
      4 * ((∫ u, (narrowUnitBump u) ^ 2) + ∫ u, (deriv narrowUnitBump u) ^ 2) := by
  have hF_smooth : ContDiff ℝ 2 (edgeTowerBump A) := edgeTowerBump_contDiff A
  have hsupp_abs : ∀ x : ℝ, A ≤ |x| → edgeTowerBump A x = 0 := fun x hx => by
    unfold edgeTowerBump
    have h1 : x - (A - 2) ∉ Icc (3 / 4 : ℝ) (5 / 4) := fun hm => by
      rcases le_or_gt 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0] at hx; linarith [hm.2]
      · rw [abs_of_neg hx0] at hx; linarith [hm.1]
    have h2 : -x - (A - 2) ∉ Icc (3 / 4 : ℝ) (5 / 4) := fun hm => by
      rcases le_or_gt 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0] at hx; linarith [hm.1]
      · rw [abs_of_neg hx0] at hx; linarith [hm.2]
    rw [narrowUnitBump_eq_zero_of_notMem h1, narrowUnitBump_eq_zero_of_notMem h2, sub_self]
  have hpos_branch : ∀ x : ℝ, 0 ≤ x → edgeTowerBump A x = narrowUnitBump (x - (A - 2)) :=
    fun x hx => by
      unfold edgeTowerBump
      have h2 : -x - (A - 2) ∉ Icc (3 / 4 : ℝ) (5 / 4) := fun hm => by linarith [hm.1]
      rw [narrowUnitBump_eq_zero_of_notMem h2, sub_zero]
  have hF_comp : HasCompactSupport (edgeTowerBump A) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (-A) A)) fun x hx => ?_
    by_contra hnot
    have habs : A ≤ |x| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
      rcases hnot with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact hx (hsupp_abs x habs)
  have hF_sq_int : Integrable (fun x => edgeTowerBump A x ^ 2) :=
    (hF_smooth.continuous.pow 2).integrable_of_hasCompactSupport (sq_hasCompactSupport_real hF_comp)
  have hlo : 1 / 4 ≤ dyadicH1NormSq (edgeTowerBump A) := by
    set J : Set ℝ := Icc (A - 9 / 8) (A - 7 / 8)
    have hJle : A - 9 / 8 ≤ A - 7 / 8 := by linarith
    have hJ1 : ∀ x ∈ J, edgeTowerBump A x ^ 2 = 1 := fun x hx => by
      rw [hpos_branch x (by linarith [hx.1]),
        narrowUnitBump_eq_one_of_mem ⟨by linarith [hx.1], by linarith [hx.2]⟩]
      norm_num
    have hset : ∫ x in J, edgeTowerBump A x ^ 2 ≤ ∫ x, edgeTowerBump A x ^ 2 :=
      setIntegral_le_integral hF_sq_int (Eventually.of_forall fun _ => sq_nonneg _)
    have hval : ∫ x in J, edgeTowerBump A x ^ 2 = 1 / 4 := by
      rw [setIntegral_congr_fun measurableSet_Icc hJ1, setIntegral_const,
        Real.volume_real_Icc_of_le hJle, smul_eq_mul]
      ring
    have hd_nn : 0 ≤ ∫ x, deriv (edgeTowerBump A) x ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    unfold dyadicH1NormSq
    linarith
  have hL2_ub : (∫ x, edgeTowerBump A x ^ 2) ≤ 4 * ∫ u, (narrowUnitBump u) ^ 2 :=
    diff_shift_reflect_L2_le narrowUnitBump_contDiff.continuous narrowUnitBump_hasCompactSupport
      (A - 2)
  have h1_nb : ContDiff ℝ (1 : ℕ) narrowUnitBump :=
    narrowUnitBump_contDiff.of_le (by norm_cast)
  have hderiv_cont : Continuous (deriv narrowUnitBump) := h1_nb.continuous_deriv le_rfl
  have hH1_ub : (∫ x, deriv (edgeTowerBump A) x ^ 2) ≤
      4 * ∫ u, (deriv narrowUnitBump u) ^ 2 := by
    have heq : (∫ x, deriv (edgeTowerBump A) x ^ 2) =
        ∫ x, (deriv narrowUnitBump (x - (A - 2)) + deriv narrowUnitBump (-x - (A - 2))) ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [edgeTowerBump_deriv_eq])
    rw [heq]
    exact sum_shift_reflect_L2_le hderiv_cont narrowUnitBump_hasCompactSupport.deriv (A - 2)
  have hodd : ∀ x, edgeTowerBump A (-x) = -edgeTowerBump A x := fun x => by
    unfold edgeTowerBump
    rw [neg_neg]
    ring
  refine ⟨hF_smooth, hF_comp, hodd, hsupp_abs, hpos_branch, hlo, ?_⟩
  unfold dyadicH1NormSq
  linarith

private theorem continuumPrimeTower_edgeTowerBump_bounds {A : ℝ} (hA : 4 ≤ A) {p : ℕ}
    (hp : p.Prime) (N : ℕ) :
    continuumPrimeTower (edgeTowerBump A) p N ≤ 0 ∧
    (Real.log p ∈ Icc (2 * A - 33 / 16) (2 * A - 31 / 16) →
      continuumPrimeTower (edgeTowerBump A) p N ≤
        -(1 / 16 : ℝ) * Real.exp (-A) * Real.log p) := by
  obtain ⟨hF2, _, _, _, hpos_branch, _, _⟩ := edgeTowerBump_properties hA
  have hFc : Continuous (edgeTowerBump A) := hF2.continuous
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp_ge : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hlogp_pos : 0 < Real.log p := hlog2.trans_le hlogp_ge
  have hl2_gt : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  -- Every same-side ratio integral vanishes identically for all `k ≥ 1`
  have hratio_zero : ∀ k : ℕ, 1 ≤ k →
      (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
        edgeTowerBump A x * edgeTowerBump A (x + (k : ℝ) * Real.log p)) = 0 := by
    intro k hk1
    have hhi_nn : 0 ≤ ((N + 1 : ℕ) : ℝ) * Real.log p := mul_nonneg (Nat.cast_nonneg _) hlogp_pos.le
    have hk_cast : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk_shift : 1 / 2 < (k : ℝ) * Real.log p := by
      have : Real.log 2 ≤ (k : ℝ) * Real.log p :=
        calc Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
          _ ≤ (k : ℝ) * Real.log p := mul_le_mul hk_cast hlogp_ge hlog2.le (by positivity)
      linarith
    calc _ = ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p, (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le hhi_nn] at hx
          have hx0 : 0 ≤ x := hx.1
          have hxk0 : 0 ≤ x + (k : ℝ) * Real.log p := by linarith
          rw [hpos_branch x hx0, hpos_branch _ hxk0]
          by_cases hmem : x - (A - 2) ∈ Icc (3 / 4 : ℝ) (5 / 4)
          · have hnot : (x + (k : ℝ) * Real.log p) - (A - 2) ∉ Icc (3 / 4 : ℝ) (5 / 4) :=
              fun hm => by linarith [hmem.1, hm.2]
            rw [narrowUnitBump_eq_zero_of_notMem hnot, mul_zero]
          · rw [narrowUnitBump_eq_zero_of_notMem hmem, zero_mul]
      _ = 0 := by simp
  -- Every reflected crossing integral is nonnegative
  have hcross_nn : ∀ k : ℕ,
      0 ≤ ∫ x in (0 : ℝ)..(k : ℝ) * Real.log p,
        edgeTowerBump A x * edgeTowerBump A ((k : ℝ) * Real.log p - x) := fun k => by
    refine intervalIntegral.integral_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogp_pos.le)
      fun x hx => ?_
    rw [hpos_branch x hx.1, hpos_branch _ (sub_nonneg.mpr hx.2)]
    exact mul_nonneg (narrowUnitBump_nonneg _) (narrowUnitBump_nonneg _)
  -- Every summand of `continuumPrimeTower` is `≤ 0`
  let term : ℕ → ℝ := fun k =>
    ArithmeticFunction.vonMangoldt (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 * (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ) * Real.log p,
        edgeTowerBump A x * edgeTowerBump A (x + (k : ℝ) * Real.log p)) -
        ∫ x in (0 : ℝ)..(k : ℝ) * Real.log p,
          edgeTowerBump A x * edgeTowerBump A ((k : ℝ) * Real.log p - x))
  have hterm_np : ∀ k ∈ Finset.Icc 1 (2 * N + 1), term k ≤ 0 := fun k hk => by
    dsimp [term]
    rw [hratio_zero k (Finset.mem_Icc.mp hk).1, mul_zero, zero_sub]
    have hw_nn : 0 ≤ ArithmeticFunction.vonMangoldt (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact mul_nonpos_of_nonneg_of_nonpos hw_nn (neg_nonpos.mpr (hcross_nn k))
  have htower_np : continuumPrimeTower (edgeTowerBump A) p N ≤ 0 :=
    Finset.sum_nonpos hterm_np
  refine ⟨htower_np, fun hband => ?_⟩
  -- Isolate `k = 1` from `Icc 1 (2 * N + 1)`
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 (2 * N + 1) := by simp
  have hle_t1 : continuumPrimeTower (edgeTowerBump A) p N ≤ term 1 := by
    change ∑ k ∈ Finset.Icc 1 (2 * N + 1), term k ≤ term 1
    rw [← Finset.add_sum_erase _ _ h1_mem]
    have herase : ∑ k ∈ (Finset.Icc 1 (2 * N + 1)).erase 1, term k ≤ 0 :=
      Finset.sum_nonpos fun k hk => hterm_np k (Finset.mem_of_mem_erase hk)
    linarith
  -- Lower-bound the `k = 1` crossing integral on `[A - 17/16, A - 1] ⊆ [0, log p]`
  have hcross1_ge : (1 / 16 : ℝ) ≤
      ∫ x in (0 : ℝ)..Real.log p, edgeTowerBump A x * edgeTowerBump A (Real.log p - x) := by
    rw [intervalIntegral.integral_of_le hlogp_pos.le]
    set J : Set ℝ := Icc (A - 17 / 16) (A - 1)
    have hJle : A - 17 / 16 ≤ A - 1 := by linarith
    have hJsub : J ⊆ Ioc 0 (Real.log p) := fun x hx =>
      ⟨by linarith [hx.1], by linarith [hx.2, hband.1]⟩
    have hJ1 : ∀ x ∈ J, edgeTowerBump A x * edgeTowerBump A (Real.log p - x) = 1 := fun x hx => by
      rw [hpos_branch x (by linarith [hx.1]),
        hpos_branch (Real.log p - x) (by linarith [hx.2, hband.1]),
        narrowUnitBump_eq_one_of_mem ⟨by linarith [hx.1], by linarith [hx.2]⟩,
        narrowUnitBump_eq_one_of_mem ⟨by linarith [hx.2, hband.1], by linarith [hx.1, hband.2]⟩,
        mul_one]
    have hint_prod : IntegrableOn
        (fun x => edgeTowerBump A x * edgeTowerBump A (Real.log p - x)) (Ioc 0 (Real.log p)) :=
      (hFc.mul (hFc.comp (continuous_const.sub continuous_id))).integrableOn_Ioc
    have hmono : (∫ x in J, edgeTowerBump A x * edgeTowerBump A (Real.log p - x)) ≤
        ∫ x in Ioc 0 (Real.log p), edgeTowerBump A x * edgeTowerBump A (Real.log p - x) :=
      setIntegral_mono_set hint_prod
        ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => by
          change 0 ≤ edgeTowerBump A x * edgeTowerBump A (Real.log p - x)
          rw [hpos_branch x hx.1.le, hpos_branch _ (sub_nonneg.mpr hx.2)]
          exact mul_nonneg (narrowUnitBump_nonneg _) (narrowUnitBump_nonneg _))
        (Eventually.of_forall hJsub)
    have hval : ∫ x in J, edgeTowerBump A x * edgeTowerBump A (Real.log p - x) = 1 / 16 := by
      rw [setIntegral_congr_fun measurableSet_Icc hJ1, setIntegral_const,
        Real.volume_real_Icc_of_le hJle, smul_eq_mul]
      ring_nf
    linarith
  have ht1_eq : term 1 =
      -(Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
        ∫ x in (0 : ℝ)..Real.log p, edgeTowerBump A x * edgeTowerBump A (Real.log p - x)) := by
    dsimp [term]
    rw [hratio_zero 1 le_rfl, pow_one, ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    ring
  have hp0 : (0 : ℝ) < p := by positivity
  have hrpow_ge : Real.exp (-A) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hp0]
    exact Real.exp_le_exp.mpr (by linarith [hband.2])
  have hprod_ge : (1 / 16 : ℝ) * Real.exp (-A) * Real.log p ≤
      Real.log p * (p : ℝ) ^ (-(1 / 2 : ℝ)) *
        ∫ x in (0 : ℝ)..Real.log p, edgeTowerBump A x * edgeTowerBump A (Real.log p - x) := by
    have h1 : Real.exp (-A) * (1 / 16 : ℝ) ≤
        (p : ℝ) ^ (-(1 / 2 : ℝ)) *
          ∫ x in (0 : ℝ)..Real.log p, edgeTowerBump A x * edgeTowerBump A (Real.log p - x) :=
      mul_le_mul hrpow_ge hcross1_ge (by norm_num) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 hlogp_pos.le
    linarith
  linarith [hle_t1, ht1_eq, hprod_ge]

/-- **Exponential `-c₀ e^A` Continuum Prime-Tower Divergence Along `edgeTowerBump A`:**
For all sufficiently large `A` and **every** truncation schedule `N : ℕ → ℕ`, summing
`continuumPrimeTower (edgeTowerBump A) p (N p)` over primes `p ≤ ⌊e^{2A}⌋₊` falls below
`-((31 / 16384) exp(-33 / 16)) e^A`. -/
theorem eventually_sum_continuumPrimeTower_edgeTowerBump_le :
    ∀ᶠ A : ℝ in atTop, ∀ N : ℕ → ℕ,
      ∑ p ∈ (Finset.Icc 1 ⌊Real.exp (2 * A)⌋₊).filter Nat.Prime,
          continuumPrimeTower (edgeTowerBump A) p (N p) ≤
        -((31 / 16384 : ℝ) * Real.exp (-33 / 16)) * Real.exp A := by
  let X1 : ℝ → ℝ := fun A => Real.exp (2 * A - 33 / 16)
  let X2 : ℝ → ℝ := fun A => Real.exp (2 * A - 31 / 16)
  have ht1 : Tendsto X1 atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_add
      tendsto_const_nhds)
  have ht2 : Tendsto X2 atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_add
      tendsto_const_nhds)
  have hcheb : ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ (1 / 64 : ℝ) * |x| := by
    simpa [Real.norm_eq_abs] using
      (isLittleO_iff.mp _root_.chebyshev_asymptotic (by norm_num : (0 : ℝ) < 1 / 64))
  filter_upwards [eventually_ge_atTop (4 : ℝ), ht1.eventually hcheb, ht2.eventually hcheb]
    with A hA4 hc1 hc2 N
  have hX1_pos : 0 < X1 A := Real.exp_pos _
  have hX2_pos : 0 < X2 A := Real.exp_pos _
  rw [abs_of_pos hX1_pos] at hc1
  rw [abs_of_pos hX2_pos] at hc2
  have hX12_rel : X2 A = Real.exp (1 / 8) * X1 A := by
    dsimp [X1, X2]; rw [← Real.exp_add]; congr 1; ring
  have hexp16 : (17 / 16 : ℝ) ≤ Real.exp (1 / 8) := by
    have := Real.add_one_le_exp (1 / 8 : ℝ)
    linarith
  have hX2_ge : (17 / 16 : ℝ) * X1 A ≤ X2 A := by
    rw [hX12_rel]
    exact mul_le_mul_of_nonneg_right hexp16 hX1_pos.le
  have hθ1_hi : Chebyshev.theta (X1 A) ≤ (65 / 64 : ℝ) * X1 A := by
    linarith [(abs_le.mp hc1).2]
  have hθ2_lo : (63 / 64 : ℝ) * X2 A ≤ Chebyshev.theta (X2 A) := by
    linarith [(abs_le.mp hc2).1]
  have hθ_gap : (31 / 1024 : ℝ) * X1 A ≤ Chebyshev.theta (X2 A) - Chebyshev.theta (X1 A) := by
    nlinarith
  -- Identify `Chebyshev.theta x` with `(Icc 1 ⌊x⌋₊).filter Nat.Prime`
  have htheta_eq : ∀ x : ℝ,
      Chebyshev.theta x = ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, Real.log p := fun x => by
    rw [Chebyshev.theta_eq_sum_Icc]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun ⟨⟨_, h2⟩, hp⟩ => ⟨⟨hp.one_lt.le, h2⟩, hp⟩,
      fun ⟨⟨_, h2⟩, hp⟩ => ⟨⟨Nat.zero_le _, h2⟩, hp⟩⟩
  set P1 : Finset ℕ := (Finset.Icc 1 ⌊X1 A⌋₊).filter Nat.Prime
  set P2 : Finset ℕ := (Finset.Icc 1 ⌊X2 A⌋₊).filter Nat.Prime
  set SA : Finset ℕ := (Finset.Icc 1 ⌊Real.exp (2 * A)⌋₊).filter Nat.Prime
  have hX1_le_X2 : X1 A ≤ X2 A := by dsimp [X1, X2]; exact Real.exp_le_exp.mpr (by linarith)
  have hX2_le_exp : X2 A ≤ Real.exp (2 * A) := by
    dsimp [X2]; exact Real.exp_le_exp.mpr (by linarith)
  have hP12 : P1 ⊆ P2 := by
    intro p hp
    simp only [P1, P2, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hX1_le_X2)⟩, hp.2⟩
  have hP2S : P2 ⊆ SA := by
    intro p hp
    simp only [P2, SA, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_mono hX2_le_exp)⟩, hp.2⟩
  have hB_sub : P2 \ P1 ⊆ SA := sdiff_subset.trans hP2S
  have hband_sum_eq : ∑ p ∈ P2 \ P1, Real.log (p : ℝ) =
      Chebyshev.theta (X2 A) - Chebyshev.theta (X1 A) := by
    rw [htheta_eq (X2 A), htheta_eq (X1 A)]
    have hsplit := Finset.sum_sdiff (s₁ := P1) (s₂ := P2) (f := fun p : ℕ => Real.log (p : ℝ)) hP12
    linarith
  have hband_mem : ∀ p ∈ P2 \ P1,
      p.Prime ∧ Real.log (p : ℝ) ∈ Icc (2 * A - 33 / 16) (2 * A - 31 / 16) := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hp2, hp1⟩ := hp
    simp only [P2, Finset.mem_filter, Finset.mem_Icc] at hp2
    have hpp : p.Prime := hp2.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hle_X2 : (p : ℝ) ≤ X2 A := (Nat.cast_le.mpr hp2.1.2).trans (Nat.floor_le hX2_pos.le)
    have hgt_X1 : X1 A < (p : ℝ) := by
      have hnot_le : ¬ p ≤ ⌊X1 A⌋₊ := fun hle =>
        hp1 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.one_lt.le, hle⟩, hpp⟩)
      exact (Nat.floor_lt hX1_pos.le).mp (lt_of_not_ge hnot_le)
    refine ⟨hpp, ?_, ?_⟩
    · exact ((Real.lt_log_iff_exp_lt hp0).mpr hgt_X1).le
    · exact (Real.log_le_iff_le_exp hp0).mpr hle_X2
  -- Split `SA` into `P2 \ P1` and `SA \ (P2 \ P1)`
  have hsdiff := Finset.sum_sdiff (s₁ := P2 \ P1) (s₂ := SA)
    (f := fun p => continuumPrimeTower (edgeTowerBump A) p (N p)) hB_sub
  have hrest_np : ∑ p ∈ SA \ (P2 \ P1), continuumPrimeTower (edgeTowerBump A) p (N p) ≤ 0 := by
    refine Finset.sum_nonpos fun p hp => ?_
    have hpS := (Finset.mem_sdiff.mp hp).1
    have hpp : p.Prime := (Finset.mem_filter.mp hpS).2
    exact (continuumPrimeTower_edgeTowerBump_bounds hA4 hpp (N p)).1
  have hband_le : ∑ p ∈ P2 \ P1, continuumPrimeTower (edgeTowerBump A) p (N p) ≤
      ∑ p ∈ P2 \ P1, (-(1 / 16 : ℝ) * Real.exp (-A) * Real.log (p : ℝ)) := by
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hpp, hlog_mem⟩ := hband_mem p hp
    exact (continuumPrimeTower_edgeTowerBump_bounds hA4 hpp (N p)).2 hlog_mem
  rw [← Finset.mul_sum, hband_sum_eq] at hband_le
  have hmul_gap : -(1 / 16 : ℝ) * Real.exp (-A) * (Chebyshev.theta (X2 A) - Chebyshev.theta (X1 A)) ≤
      -(1 / 16 : ℝ) * Real.exp (-A) * ((31 / 1024 : ℝ) * X1 A) :=
    mul_le_mul_of_nonpos_left hθ_gap
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.exp_nonneg _))
  have hexp_id : -(1 / 16 : ℝ) * Real.exp (-A) * ((31 / 1024 : ℝ) * X1 A) =
      -((31 / 16384 : ℝ) * Real.exp (-33 / 16)) * Real.exp A := by
    dsimp [X1]
    have : Real.exp (-A) * Real.exp (2 * A - 33 / 16) = Real.exp (-33 / 16) * Real.exp A := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    linear_combination -(31 / 16384 : ℝ) * this
  change ∑ p ∈ SA, continuumPrimeTower (edgeTowerBump A) p (N p) ≤ _
  linarith

/-- **Sub-Exponential Continuum Prime-Tower No-Go Theorem (`not_continuumPrimeTower_subexponential_dyadicH1`):**
For **every** exponent `σ < 1 / 2` and **every** constant `C_σ : ℝ`, no sub-exponential dyadic
Sobolev floor `-C_σ e^{2σ A} dyadicH1NormSq F` holds across odd `F ∈ C²_c([-A, A])`, finite prime
sets `S`, and admissible truncations `A ≤ (N p + 1) log p` (`A ≥ 4`). -/
theorem not_continuumPrimeTower_subexponential_dyadicH1 {σ : ℝ} (hσ : σ < 1 / 2) (C_σ : ℝ) :
    ¬ (∀ A : ℝ, 4 ≤ A → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, A ≤ |x| → F x = 0) →
        ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        ∀ N : ℕ → ℕ, (∀ p ∈ S, A ≤ ((N p + 1 : ℕ) : ℝ) * Real.log p) →
          -C_σ * Real.exp (2 * σ * A) * dyadicH1NormSq F ≤
            ∑ p ∈ S, continuumPrimeTower F p (N p)) := by
  intro hall
  set c0 : ℝ := (31 / 16384 : ℝ) * Real.exp (-33 / 16)
  have hc0 : 0 < c0 := by dsimp [c0]; positivity
  set Cb : ℝ := 4 * ((∫ u, (narrowUnitBump u) ^ 2) + ∫ u, (deriv narrowUnitBump u) ^ 2)
  have hCb_nn : 0 ≤ Cb := by
    dsimp [Cb]
    have h1 : 0 ≤ ∫ u, (narrowUnitBump u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have h2 : 0 ≤ ∫ u, (deriv narrowUnitBump u) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith
  have hexp_decay : Tendsto (fun A : ℝ => max C_σ 0 * Cb * Real.exp ((2 * σ - 1) * A))
      atTop (𝓝 0) := by
    have hneg : 2 * σ - 1 < 0 := by linarith
    have h1 : Tendsto (fun A : ℝ => (2 * σ - 1) * A) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg hneg
    simpa [mul_zero] using (Real.tendsto_exp_atBot.comp h1).const_mul (max C_σ 0 * Cb)
  obtain ⟨A, hA4, hsum_le, hsmall⟩ :=
    ((eventually_ge_atTop (4 : ℝ)).and
      (eventually_sum_continuumPrimeTower_edgeTowerBump_le.and
        (hexp_decay.eventually (Iio_mem_nhds hc0)))).exists
  obtain ⟨hF2, hFc, hodd, hsupp, _, hH1_lo, hH1_hi⟩ := edgeTowerBump_properties hA4
  let SA : Finset ℕ := (Finset.Icc 1 ⌊Real.exp (2 * A)⌋₊).filter Nat.Prime
  let N_std : ℕ → ℕ := fun p => ⌊A / Real.log p⌋₊
  have hSA_prime : ∀ p ∈ SA, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2
  have hN_adm : ∀ p ∈ SA, A ≤ ((N_std p + 1 : ℕ) : ℝ) * Real.log p := by
    intro p hp
    have hpp : p.Prime := hSA_prime p hp
    have hlp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hpp.one_lt)
    have hlt : A / Real.log (p : ℝ) < ((N_std p + 1 : ℕ) : ℝ) := by
      dsimp [N_std]
      push_cast
      exact Nat.lt_floor_add_one _
    exact ((div_lt_iff₀ hlp).mp hlt).le
  have hinst := hall A hA4 (edgeTowerBump A) hF2 hFc hodd hsupp SA hSA_prime N_std hN_adm
  have htop : ∑ p ∈ SA, continuumPrimeTower (edgeTowerBump A) p (N_std p) ≤
      -c0 * Real.exp A := hsum_le N_std
  have hH1_nn : 0 ≤ dyadicH1NormSq (edgeTowerBump A) := by linarith
  have hfloor_gt : -c0 * Real.exp A <
      -C_σ * Real.exp (2 * σ * A) * dyadicH1NormSq (edgeTowerBump A) := by
    have h1 : C_σ * Real.exp (2 * σ * A) * dyadicH1NormSq (edgeTowerBump A) ≤
        max C_σ 0 * Cb * Real.exp (2 * σ * A) := by
      calc C_σ * Real.exp (2 * σ * A) * dyadicH1NormSq (edgeTowerBump A)
          ≤ max C_σ 0 * Real.exp (2 * σ * A) * dyadicH1NormSq (edgeTowerBump A) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)) hH1_nn
        _ ≤ max C_σ 0 * Real.exp (2 * σ * A) * Cb :=
            mul_le_mul_of_nonneg_left hH1_hi (mul_nonneg (le_max_right _ _) (Real.exp_nonneg _))
        _ = max C_σ 0 * Cb * Real.exp (2 * σ * A) := by ring
    have h2 : max C_σ 0 * Cb * Real.exp (2 * σ * A) < c0 * Real.exp A := by
      have hm := mul_lt_mul_of_pos_right hsmall (Real.exp_pos A)
      have hexp_eq : max C_σ 0 * Cb * Real.exp ((2 * σ - 1) * A) * Real.exp A =
          max C_σ 0 * Cb * Real.exp (2 * σ * A) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2; ring
      linarith
    linarith
  linarith

/-- **Pole-Neutralized Continuum Sobolev Floor ↔ Spectral Zero-Width Law:**
Once the rank-one `s = 1` Chebyshev pole is neutralized inside `scalingSubsurface (oddRealTestsAt A)`,
the sub-exponential dyadic Sobolev floor `-C e^{2β A} dyadicH1NormSq F` (`∀ β > σ`) holds if and
only if `zetaZeroWidth ≤ σ` (equivalently `oddDefectFloorRate ≤ σ`). -/
theorem continuum_poleNeutralized_width_equivalence {σ : ℝ} (hσ : 0 ≤ σ) :
    List.TFAE [
      zetaZeroWidth ≤ σ,
      oddDefectFloorRate ≤ σ,
      ∀ β : ℝ, σ < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 < A → ∀ x : ℝ × ℝ × oddRealTestsAt A,
        -(C * Real.exp (2 * β * A) * dyadicH1NormSq (x.2.2.1 : ℝ → ℝ)) ≤
          (scalingSubsurface (oddRealTestsAt A)).defect x x] := by
  tfae_have 1 ↔ 2 := by rw [oddDefectFloorRate_eq_zetaZeroWidth]
  tfae_have 1 ↔ 3 := by
    simpa only [dyadicH1NormSq] using
      zetaZeroWidth_le_iff_scalingSubsurface_odd_sobolev_defect_floor hσ
  tfae_finish

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws
