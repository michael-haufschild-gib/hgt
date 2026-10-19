import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import GaloisForLFunctions.SquareRootThreshold.PrimeTailCouplingCriterion
import GaloisForLFunctions.SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon

/-!
# Kronecker–Bohr Prime-Phase Realization and Exponential Height Escape

This module connects the prime-torus Kronecker density theorem
(`GaloisForLFunctions.primeTorus_kronecker_dense` in `HTGeometry.PrimeTorusKroneckerDensity`)
to the localized Weil explicit formula at single heights
(`SquareRootThreshold.PrimeTailCouplingCriterion` and
`SquareRootThreshold.ZetaSingleHeightPositivityAboveArchimedeanHorizon`).

## Main results

1. **Prime vs. composite prime-power decomposition (§1):**
   * `primePolynomial_eq_primeOnly_add_tail`: splits `primePolynomial f N ξ` into the prime-only
     trigonometric polynomial `primeOnlyPolynomial f N ξ` (indexed by primes `p ∈ [2, N]`) and
     the composite prime-power tail `primePowerTailPolynomial f N ξ`, with `ℓ¹` envelopes
     `primeOnlyEnvelope f N` and `primePowerTailEnvelope f N`.

2. **Kronecker–Bohr arbitrary phase realization and exact `ℓ¹` oscillation laws (§2):**
   * `exists_height_prime_phase_approx`: simultaneous Kronecker approximation of prime phases
     `e^{2πiξ log p}` to any target phase pattern `e^{iθ(p)}` across `p ∈ primeIndices N`.
   * `exists_re_primeOnlyPolynomial_approx_phase`: for every profile `f`, cutoff `N`, phase pattern
     `θ : ℕ → ℝ`, and `ε > 0`, there exists a height `ξ ∈ ℝ` where `(primeOnlyPolynomial f N ξ).re`
     is within `ε` of `∑_{p ∈ primeIndices N} 2 Re(primeCoeff f (p, true) e^{iθ(p)})`.
   * `exists_gt_and_lt_re_primeOnlyPolynomial`, `iSup_re_primeOnlyPolynomial`, and
     `iInf_re_primeOnlyPolynomial`: the prime-only polynomial attains values arbitrarily close to
     `±primeOnlyEnvelope f N`, so `⨆ ξ, Re Π_f^{prime}(N, ξ) = primeOnlyEnvelope f N` and
     `⨅ ξ, Re Π_f^{prime}(N, ξ) = -primeOnlyEnvelope f N`.
   * `exists_gt_and_lt_re_primePolynomial_of_lt_primeSubCompEnvelope`: the full von Mangoldt
     polynomial `primePolynomial f N` attains both `> B` and `< -B` for every
     `B < primeOnlyEnvelope f N - primePowerTailEnvelope f N`.
   * `exists_archPart_gt_of_riemannHypothesis`: under `RiemannHypothesis`, for every
     `B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`, there exists a
     height `ξ ∈ ℝ` at which both `(primePolynomial f ⌊e^{2a}⌋₊ ξ).re > B` and
     `(archPart f ξ).re > B`.

3. **Logarithmic height growth of `archPart` and exponential height escape (§3):**
   * `re_archPart_le`: proves the uniform logarithmic height-growth upper bound
     `Re A_f(ξ) ≤ 2 e^a (∫ ‖f‖)² + B_f² (1/2 + πC) + (∫ ‖f‖²) log(1 + 2π|ξ|)`.
   * `exists_re_W_neg_or_height_escape`: unconditional dichotomy between sub-horizon Weil
     negativity `Re W_ζ(S_ξ f, S_ξ f) < 0` and the exponential height escape lower bound
     `B - 2 e^a (∫ ‖f‖)² - B_f² (1/2 + πC) < (∫ ‖f‖²) log(1 + 2π|ξ|)`.
   * `exists_height_escape_of_riemannHypothesis`: under `RiemannHypothesis`, every coherent prime
     threshold `B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊` forces the
     corresponding Kronecker-aligned height `ξ` to satisfy the exponential height lower bound.
-/

open MeasureTheory Complex Set Filter Topology Finset
open scoped Real ComplexConjugate BigOperators

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular GaloisForLFunctions

/-! ## §1. Conjugate Pairing & Prime vs. Composite Prime-Power Decomposition -/

private theorem weilTest_self_neg_eq_conj (f : ℝ → ℂ) (v : ℝ) :
    EF.weilTest f f (-v) = conj (EF.weilTest f f v) := by
  have h := congrFun (RHTower.WeilSpectral.tilde_weilTest_self f) (-v)
  simpa [EF.tilde, neg_neg] using h.symm

private theorem primeCoeff_false_eq_conj_true (f : ℝ → ℂ) (n : ℕ) :
    primeCoeff f (n, false) = conj (primeCoeff f (n, true)) := by
  simp only [primeCoeff, primeFreq, ↓reduceIte, Bool.false_eq_true, map_mul,
    Complex.conj_ofReal, weilTest_self_neg_eq_conj]

private theorem norm_primeCoeff_false_eq_true (f : ℝ → ℂ) (n : ℕ) :
    ‖primeCoeff f (n, false)‖ = ‖primeCoeff f (n, true)‖ := by
  rw [primeCoeff_false_eq_conj_true, Complex.norm_conj]

private theorem primeCoeff_mul_cexp_false_eq_conj_true (f : ℝ → ℂ) (n : ℕ) (ξ : ℝ) :
    primeCoeff f (n, false) * cexp (2 * π * I * ξ * primeFreq (n, false)) =
      conj (primeCoeff f (n, true) * cexp (2 * π * I * ξ * primeFreq (n, true))) := by
  rw [map_mul, primeCoeff_false_eq_conj_true, ← Complex.exp_conj]
  congr 2
  simp only [primeFreq, ↓reduceIte, Bool.false_eq_true, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  ring

private theorem re_primeHarmonic_pair_eq (f : ℝ → ℂ) (n : ℕ) (ξ : ℝ) :
    (primeCoeff f (n, true) * cexp (2 * π * I * ξ * primeFreq (n, true)) +
      primeCoeff f (n, false) * cexp (2 * π * I * ξ * primeFreq (n, false))).re =
      2 * (primeCoeff f (n, true) * cexp (2 * π * I * ξ * Real.log n)).re := by
  rw [primeCoeff_mul_cexp_false_eq_conj_true, Complex.add_re, Complex.conj_re]
  simp only [primeFreq, ↓reduceIte]
  ring

/-- The prime indices in `[2, N]`. -/
def primeIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter Nat.Prime

/-- The composite indices in `[2, N]` (carrying higher prime powers `p^m` with `m ≥ 2`). -/
def compIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter (fun n => ¬ Nat.Prime n)

/-- The prime-only part `Π_f^{prime}(N, ξ)` of `primePolynomial f N ξ`. -/
def primeOnlyPolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℂ :=
  expSum (primeIndices N ×ˢ Finset.univ) (primeCoeff f) primeFreq ξ

/-- The composite-prime-power tail `Π_f^{comp}(N, ξ)` of `primePolynomial f N ξ`. -/
def primePowerTailPolynomial (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) : ℂ :=
  expSum (compIndices N ×ˢ Finset.univ) (primeCoeff f) primeFreq ξ

/-- The `ℓ¹` prime envelope `M_f^{prime}(N) = ∑_{(p, b) ∈ primeIndices N × Bool} ‖c_f(p, b)‖`. -/
def primeOnlyEnvelope (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ j ∈ primeIndices N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖

/-- The `ℓ¹` composite-prime-power envelope `M_f^{comp}(N)`. -/
def primePowerTailEnvelope (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ j ∈ compIndices N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖

theorem primeOnlyEnvelope_nonneg (f : ℝ → ℂ) (N : ℕ) : 0 ≤ primeOnlyEnvelope f N :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem primePowerTailEnvelope_nonneg (f : ℝ → ℂ) (N : ℕ) : 0 ≤ primePowerTailEnvelope f N :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Exact decomposition `primePolynomial = primeOnlyPolynomial + primePowerTailPolynomial`. -/
theorem primePolynomial_eq_primeOnly_add_tail (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    primePolynomial f N ξ = primeOnlyPolynomial f N ξ + primePowerTailPolynomial f N ξ := by
  unfold primePolynomial primeOnlyPolynomial primePowerTailPolynomial expSum
    primeIndices compIndices
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_product,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 N) Nat.Prime]

/-- `primeOnlyEnvelope` equals `∑_{p ∈ primeIndices N} 2 * ‖primeCoeff f (p, true)‖`. -/
theorem primeOnlyEnvelope_eq_sum_two_mul_norm_true (f : ℝ → ℂ) (N : ℕ) :
    primeOnlyEnvelope f N = ∑ p ∈ primeIndices N, 2 * ‖primeCoeff f (p, true)‖ := by
  unfold primeOnlyEnvelope
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_bool, norm_primeCoeff_false_eq_true]
  ring

/-- Explicit real-part expansion of `primeOnlyPolynomial`. -/
theorem re_primeOnlyPolynomial_eq_sum (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    (primeOnlyPolynomial f N ξ).re =
      ∑ p ∈ primeIndices N,
        2 * (primeCoeff f (p, true) * cexp (2 * π * I * ξ * Real.log p)).re := by
  unfold primeOnlyPolynomial expSum
  rw [Finset.sum_product, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_bool, re_primeHarmonic_pair_eq]

/-- Pointwise `ℓ¹` bound on `(primeOnlyPolynomial f N ξ).re`. -/
theorem abs_re_primeOnlyPolynomial_le (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    |(primeOnlyPolynomial f N ξ).re| ≤ primeOnlyEnvelope f N :=
  (Complex.abs_re_le_norm _).trans (norm_expSum_le _ _ _ _)

/-- Pointwise `ℓ¹` bound on `(primePowerTailPolynomial f N ξ).re`. -/
theorem abs_re_primePowerTailPolynomial_le (f : ℝ → ℂ) (N : ℕ) (ξ : ℝ) :
    |(primePowerTailPolynomial f N ξ).re| ≤ primePowerTailEnvelope f N :=
  (Complex.abs_re_le_norm _).trans (norm_expSum_le _ _ _ _)

/-! ## §2. Kronecker–Bohr Prime-Torus Phase Realization & Coherent `ℓ¹` Oscillation Laws -/

/-- Simultaneous Kronecker approximation of prime phases `e^{2πiξ log p}` to any target phase
pattern `e^{iθ(p)}` across `p ∈ primeIndices N`. -/
theorem exists_height_prime_phase_approx (N : ℕ) (θ : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ξ : ℝ, ∀ p ∈ primeIndices N,
      ‖cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I)‖ < δ := by
  obtain ⟨t, ht⟩ := GaloisForLFunctions.primeTorus_kronecker_dense N
    (fun q : primesLE N => θ ((q : Nat.Primes) : ℕ)) hδ
  refine ⟨t / (2 * π), fun p hp => ?_⟩
  have hp_mem := Finset.mem_filter.mp hp
  have hprime : Nat.Prime p := hp_mem.2
  have hpN : p ≤ N := (Finset.mem_Icc.mp hp_mem.1).2
  let q : Nat.Primes := ⟨p, hprime⟩
  have hq : q ∈ primesLE N := (mem_primesLE N q).mpr hpN
  have htq := ht ⟨q, hq⟩
  have hexp : cexp (2 * π * I * ((t / (2 * π) : ℝ) : ℂ) * Real.log p) =
      expChar (Real.log p) t := by
    unfold expChar
    congr 1
    have h2pi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    push_cast
    field_simp [h2pi]
  rw [hexp]
  exact htq

/-- For every profile `f`, cutoff `N`, phase pattern `θ : ℕ → ℝ`, and `ε > 0`, there exists a
height `ξ ∈ ℝ` at which `(primeOnlyPolynomial f N ξ).re` is within `ε` of
`∑_{p ∈ primeIndices N} 2 * Re(primeCoeff f (p, true) * e^{iθ(p)})`. -/
theorem exists_re_primeOnlyPolynomial_approx_phase (f : ℝ → ℂ) (N : ℕ) (θ : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ℝ,
      |(primeOnlyPolynomial f N ξ).re -
        ∑ p ∈ primeIndices N, 2 * (primeCoeff f (p, true) * cexp ((θ p : ℝ) * I)).re| < ε := by
  set M := primeOnlyEnvelope f N with hM_def
  have hM0 : 0 ≤ M := primeOnlyEnvelope_nonneg f N
  have hM1 : 0 < M + 1 := by linarith
  set δ := ε / (M + 1) with hδ_def
  have hδ : 0 < δ := div_pos hε hM1
  obtain ⟨ξ, hξ⟩ := exists_height_prime_phase_approx N θ hδ
  refine ⟨ξ, ?_⟩
  rw [re_primeOnlyPolynomial_eq_sum, ← Finset.sum_sub_distrib]
  have hle : |∑ p ∈ primeIndices N,
      (2 * (primeCoeff f (p, true) * cexp (2 * π * I * ξ * Real.log p)).re -
        2 * (primeCoeff f (p, true) * cexp ((θ p : ℝ) * I)).re)| ≤
      ∑ p ∈ primeIndices N, (2 * ‖primeCoeff f (p, true)‖) * δ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    have hsub : 2 * (primeCoeff f (p, true) * cexp (2 * π * I * ξ * Real.log p)).re -
        2 * (primeCoeff f (p, true) * cexp ((θ p : ℝ) * I)).re =
        2 * (primeCoeff f (p, true) *
          (cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I))).re := by
      rw [mul_sub, Complex.sub_re]
      ring
    rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hre : |(primeCoeff f (p, true) *
        (cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I))).re| ≤
        ‖primeCoeff f (p, true)‖ *
          ‖cexp (2 * π * I * ξ * Real.log p) - cexp ((θ p : ℝ) * I)‖ :=
      (Complex.abs_re_le_norm _).trans (le_of_eq (norm_mul _ _))
    have hlt := (hξ p hp).le
    nlinarith [norm_nonneg (primeCoeff f (p, true))]
  rw [← Finset.sum_mul, ← primeOnlyEnvelope_eq_sum_two_mul_norm_true] at hle
  have hstrict : M * δ < ε := by
    rw [hδ_def, mul_div_assoc', div_lt_iff₀ hM1]
    linarith
  exact lt_of_le_of_lt hle hstrict

/-- Aligning a complex number `z` by phase `-arg z` yields its nonnegative modulus `‖z‖`. -/
theorem mul_cexp_neg_arg_eq_norm (z : ℂ) :
    z * cexp (((-z.arg : ℝ) : ℂ) * I) = (‖z‖ : ℂ) := by
  have h0 : (z.arg : ℂ) * I + ((-z.arg : ℝ) : ℂ) * I = 0 := by push_cast; ring
  calc z * cexp (((-z.arg : ℝ) : ℂ) * I)
      = (↑‖z‖ * cexp ((z.arg : ℂ) * I)) * cexp (((-z.arg : ℝ) : ℂ) * I) := by
          rw [Complex.norm_mul_exp_arg_mul_I]
    _ = ↑‖z‖ * cexp ((z.arg : ℂ) * I + ((-z.arg : ℝ) : ℂ) * I) := by
          rw [mul_assoc, ← Complex.exp_add]
    _ = (‖z‖ : ℂ) := by rw [h0, Complex.exp_zero, mul_one]

theorem re_mul_cexp_neg_arg (z : ℂ) :
    (z * cexp (((-z.arg : ℝ) : ℂ) * I)).re = ‖z‖ := by
  rw [mul_cexp_neg_arg_eq_norm, Complex.ofReal_re]

theorem re_mul_cexp_pi_sub_arg (z : ℂ) :
    (z * cexp (((π - z.arg : ℝ) : ℂ) * I)).re = -‖z‖ := by
  have hexp : cexp (((π - z.arg : ℝ) : ℂ) * I) =
      cexp (π * I) * cexp (((-z.arg : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, Complex.exp_pi_mul_I]
  have h : z * (-1 * cexp (((-z.arg : ℝ) : ℂ) * I)) =
      -(z * cexp (((-z.arg : ℝ) : ℂ) * I)) := by ring
  rw [h, mul_cexp_neg_arg_eq_norm, Complex.neg_re, Complex.ofReal_re]

/-- For every `B < primeOnlyEnvelope f N`, `(primeOnlyPolynomial f N ξ).re` attains both values
`> B` and values `< -B`. -/
theorem exists_gt_and_lt_re_primeOnlyPolynomial (f : ℝ → ℂ) (N : ℕ) {B : ℝ}
    (hB : B < primeOnlyEnvelope f N) :
    (∃ ξ : ℝ, B < (primeOnlyPolynomial f N ξ).re) ∧
      (∃ ξ : ℝ, (primeOnlyPolynomial f N ξ).re < -B) := by
  have hε : 0 < primeOnlyEnvelope f N - B := sub_pos.mpr hB
  constructor
  · obtain ⟨ξ, hξ⟩ := exists_re_primeOnlyPolynomial_approx_phase f N
      (fun p => -(primeCoeff f (p, true)).arg) hε
    have hsum : ∑ p ∈ primeIndices N,
        2 * (primeCoeff f (p, true) * cexp (((-(primeCoeff f (p, true)).arg : ℝ) : ℂ) * I)).re =
        primeOnlyEnvelope f N := by
      rw [primeOnlyEnvelope_eq_sum_two_mul_norm_true]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [re_mul_cexp_neg_arg]
    rw [hsum] at hξ
    refine ⟨ξ, ?_⟩
    linarith [(abs_lt.mp hξ).1]
  · obtain ⟨ξ, hξ⟩ := exists_re_primeOnlyPolynomial_approx_phase f N
      (fun p => π - (primeCoeff f (p, true)).arg) hε
    have hsum : ∑ p ∈ primeIndices N,
        2 * (primeCoeff f (p, true) * cexp (((π - (primeCoeff f (p, true)).arg : ℝ) : ℂ) * I)).re =
        -primeOnlyEnvelope f N := by
      rw [primeOnlyEnvelope_eq_sum_two_mul_norm_true, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [re_mul_cexp_pi_sub_arg]
      ring
    rw [hsum] at hξ
    refine ⟨ξ, ?_⟩
    linarith [(abs_lt.mp hξ).2]

/-- For every `B < primeOnlyEnvelope f N - primePowerTailEnvelope f N`, the full von Mangoldt
trigonometric polynomial `(primePolynomial f N ξ).re` attains both `> B` and `< -B`. -/
theorem exists_gt_and_lt_re_primePolynomial_of_lt_primeSubCompEnvelope
    (f : ℝ → ℂ) (N : ℕ) {B : ℝ}
    (hB : B < primeOnlyEnvelope f N - primePowerTailEnvelope f N) :
    (∃ ξ : ℝ, B < (primePolynomial f N ξ).re) ∧
      (∃ ξ : ℝ, (primePolynomial f N ξ).re < -B) := by
  have hB' : B + primePowerTailEnvelope f N < primeOnlyEnvelope f N := by linarith
  obtain ⟨⟨ξ₁, hξ₁⟩, ⟨ξ₂, hξ₂⟩⟩ := exists_gt_and_lt_re_primeOnlyPolynomial f N hB'
  constructor
  · refine ⟨ξ₁, ?_⟩
    have htail := (abs_le.mp (abs_re_primePowerTailPolynomial_le f N ξ₁)).1
    rw [primePolynomial_eq_primeOnly_add_tail, Complex.add_re]
    linarith
  · refine ⟨ξ₂, ?_⟩
    have htail := (abs_le.mp (abs_re_primePowerTailPolynomial_le f N ξ₂)).2
    rw [primePolynomial_eq_primeOnly_add_tail, Complex.add_re]
    linarith

/-- The supremum of `(primeOnlyPolynomial f N ξ).re` over `ξ ∈ ℝ` equals `primeOnlyEnvelope f N`. -/
theorem iSup_re_primeOnlyPolynomial (f : ℝ → ℂ) (N : ℕ) :
    (⨆ ξ : ℝ, (primeOnlyPolynomial f N ξ).re) = primeOnlyEnvelope f N :=
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt
    (fun ξ => (le_abs_self _).trans (abs_re_primeOnlyPolynomial_le f N ξ))
    (fun _ hB => (exists_gt_and_lt_re_primeOnlyPolynomial f N hB).1)

/-- The infimum of `(primeOnlyPolynomial f N ξ).re` over `ξ ∈ ℝ` equals `-primeOnlyEnvelope f N`. -/
theorem iInf_re_primeOnlyPolynomial (f : ℝ → ℂ) (N : ℕ) :
    (⨅ ξ : ℝ, (primeOnlyPolynomial f N ξ).re) = -primeOnlyEnvelope f N :=
  ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
    (fun ξ => (abs_le.mp (abs_re_primeOnlyPolynomial_le f N ξ)).1)
    (fun B hB => by
      have hB' : -B < primeOnlyEnvelope f N := by linarith
      obtain ⟨ξ, hξ⟩ := (exists_gt_and_lt_re_primeOnlyPolynomial f N hB').2
      exact ⟨ξ, by linarith⟩)

/-- Under `RiemannHypothesis`, for every `B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`,
there exists a height `ξ ∈ ℝ` at which both `(primePolynomial f ⌊e^{2a}⌋₊ ξ).re > B` and
`(archPart f ξ).re > B`. -/
theorem exists_archPart_gt_of_riemannHypothesis
    (hRH : RiemannHypothesis) {a B : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    ∃ ξ : ℝ, B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ∧ B < (archPart f ξ).re := by
  obtain ⟨⟨ξ, hξ⟩, -⟩ :=
    exists_gt_and_lt_re_primePolynomial_of_lt_primeSubCompEnvelope f ⌊Real.exp (2 * a)⌋₊ hB
  have hle := riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs ξ
  exact ⟨ξ, hξ, lt_of_lt_of_le hξ hle⟩

/-! ## §3. Uniform Logarithmic Height-Growth Upper Bound for `archPart` & Height Escape -/

/-- Upper bound on the pole terms of `heightShift ξ f`:
`Re(h_k(i/2) + h_k(-i/2)) ≤ 2 e^a (∫ ‖f‖)²`. -/
theorem re_pole_terms_heightShift_le {a : ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (I / 2) +
      paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) (-I / 2)).re ≤
      2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 := by
  set g := heightShift ξ f with hgdef
  have hg : Continuous g := (by fun_prop : Continuous fun u : ℝ =>
    cexp (2 * π * I * ξ * u)).mul hf
  have hgs : tsupport g ⊆ Icc (-a) a := (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hgnorm : ∀ u, ‖g u‖ = ‖f u‖ := fun u => by
    simp only [hgdef, heightShift, norm_mul]
    rw [show (2 * π * I * ξ * u : ℂ) = ((2 * π * ξ * u : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  have hgint : ∫ u, ‖g u‖ = ∫ u, ‖f u‖ :=
    integral_congr_ae (Eventually.of_forall hgnorm)
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hgsupp : ∀ u, g u ≠ 0 → |u| ≤ a := fun u hu => by
    by_contra h
    exact hu (eq_zero_of_not_mem_Icc hgs fun hm => h (abs_le.mpr ⟨hm.1, hm.2⟩))
  have hb1 := norm_paperFT_le hgi hgsupp (I / 2)
  have hb2 := norm_paperFT_le hgi hgsupp (-I / 2)
  have him1 : |(I / 2 : ℂ).im| = 1 / 2 := by simp
  have him2 : |(-I / 2 : ℂ).im| = 1 / 2 := by simp; norm_num
  rw [him1, hgint] at hb1
  rw [him2, hgint] at hb2
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [EF.paperFT_weilTest hg hg hgc hgc, EF.paperFT_weilTest hg hg hgc hgc, hc1, hc2]
  have hre : (paperFT g (I / 2) * conj (paperFT g (-I / 2)) +
      paperFT g (-I / 2) * conj (paperFT g (I / 2))).re ≤
      2 * (‖paperFT g (I / 2)‖ * ‖paperFT g (-I / 2)‖) := by
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    linarith
  have hprod : ‖paperFT g (I / 2)‖ * ‖paperFT g (-I / 2)‖ ≤
      (Real.exp (1 / 2 * a) * ∫ u, ‖f u‖) * (Real.exp (1 / 2 * a) * ∫ u, ‖f u‖) :=
    mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
  have hexp : (Real.exp (1 / 2 * a) * ∫ u, ‖f u‖) * (Real.exp (1 / 2 * a) * ∫ u, ‖f u‖) =
      Real.exp a * (∫ u, ‖f u‖) ^ 2 := by
    rw [mul_mul_mul_comm, ← Real.exp_add, show 1 / 2 * a + 1 / 2 * a = a by ring, sq]
  linarith

/-- Submultiplicative logarithmic bound for shifted frequencies:
`log(1 + |τ|) ≤ log(1 + |τ + y|) + log(1 + |y|)`. -/
theorem log_one_add_abs_le_add_shift (τ y : ℝ) :
    Real.log (1 + |τ|) ≤ Real.log (1 + |τ + y|) + Real.log (1 + |y|) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by positivity) ?_
  have htri : |τ| ≤ |τ + y| + |y| := by
    have h := abs_sub (τ + y) y
    rwa [add_sub_cancel_right] at h
  nlinarith [abs_nonneg (τ + y), abs_nonneg y]

/-- Logarithmic height-growth bound for the shifted archimedean integral:
`∫ ‖h_f(τ + 2πξ)‖² μ(τ) dτ ≤ (∫ ‖f‖²) log(1 + 2π|ξ|) + B_f² (1/2 + πC)`. -/
theorem integral_norm_sq_paperFT_shift_mul_mu_le {C a : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ ≤
      (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) +
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) := by
  set B := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hB
  set y : ℝ := 2 * π * ξ with hy
  set F : ℝ → ℝ := fun σ => ‖paperFT f σ‖ ^ 2 with hFdef
  have hg : ContDiff ℝ 2 (heightShift ξ f) := heightShift_contDiff hf ξ
  have hgs : tsupport (heightShift ξ f) ⊆ Icc (-a) a :=
    (tsupport_heightShift_subset ξ f).trans hfs
  have hgc := hasCompactSupport_of_tsupport_subset_Icc hgs
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hkd := EF.weilTest_contDiff hg hg.continuous hgc
  have hkc := EF.weilTest_hasCompactSupport hgc hgc
  have hkd0 := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc0 := EF.weilTest_hasCompactSupport hfc hfc
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hint : Integrable fun τ : ℝ => F (τ + y) * mu τ := by
    refine (EF.integrable_paperFT_mul_mu hkd hkc gammaFacts).re.congr
      (Eventually.of_forall fun τ => ?_)
    simp only [hval, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re, hFdef, hy]
  have hFi : Integrable F := by
    refine (EF.integrable_paperFT_ofReal
      (EF.integrable_fourier_of_contDiff_two hkd0 hkc0)).re.congr (Eventually.of_forall fun σ => ?_)
    simp only [paperFT_weilTest_self_ofReal hf.continuous hfc σ, RCLike.re_to_complex,
      Complex.ofReal_re, hFdef]
  have hFyi : Integrable fun τ : ℝ => F (τ + y) := hFi.comp_add_right y
  set K : ℝ := B ^ 2 * (1 / (2 * π) + C) with hK
  have hKi : Integrable fun τ : ℝ => K * (1 + (τ + y) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.const_mul K).comp_add_right y
  set c_y : ℝ := Real.log (1 + |y|) / (2 * π) with hcy
  have hfa : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => by
    by_contra h
    exact hu (eq_zero_of_not_mem_Icc hfs fun hm => h (abs_le.mpr ⟨hm.1, hm.2⟩))
  have hptw0 : ∀ σ : ℝ, F σ * (Real.log (1 + |σ|) / (2 * π) + C) ≤ K * (1 + σ ^ 2)⁻¹ := by
    intro σ
    have hdec := norm_paperFT_le_decay hf hfa (σ : ℂ)
    simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
      Complex.ofReal_re] at hdec
    have hF : F σ ≤ B ^ 2 * (1 / (1 + |σ|) ^ 4) := by
      calc F σ ≤ (B / (1 + |σ|) ^ 2) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hdec 2
        _ = B ^ 2 * (1 / (1 + |σ|) ^ 4) := by rw [div_pow, ← pow_mul]; ring
    have hL : Real.log (1 + |σ|) ≤ 1 + |σ| := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + |σ| by positivity)
      linarith
    have hp1 : 1 ≤ 1 + |σ| := by linarith [abs_nonneg σ]
    have hw0 : 0 ≤ Real.log (1 + |σ|) / (2 * π) + C := by
      have : 0 ≤ Real.log (1 + |σ|) := Real.log_nonneg (by linarith [abs_nonneg σ])
      positivity
    have hstep : (1 / (1 + |σ|) ^ 4) * (Real.log (1 + |σ|) / (2 * π) + C) ≤
        (1 / (2 * π) + C) * (1 + σ ^ 2)⁻¹ := by
      have h4 := one_div_one_add_abs_pow_four_le σ
      have h3 : 1 / (1 + |σ|) ^ 4 * Real.log (1 + |σ|) ≤ (1 + σ ^ 2)⁻¹ := by
        have hq : 1 / (1 + |σ|) ^ 4 * Real.log (1 + |σ|) ≤ 1 / (1 + |σ|) ^ 4 * (1 + |σ|) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
        have hq2 : 1 / (1 + |σ|) ^ 4 * (1 + |σ|) ≤ 1 / (1 + |σ|) ^ 2 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [pow_le_pow_right₀ hp1 (show 3 ≤ 4 by norm_num)]
        have hq3 : 1 / (1 + |σ|) ^ 2 ≤ (1 + σ ^ 2)⁻¹ := by
          rw [one_div]
          exact inv_anti₀ (by positivity) (by nlinarith [sq_abs σ, abs_nonneg σ])
        linarith
      calc (1 / (1 + |σ|) ^ 4) * (Real.log (1 + |σ|) / (2 * π) + C)
          = (1 / (1 + |σ|) ^ 4 * Real.log (1 + |σ|)) / (2 * π) + 1 / (1 + |σ|) ^ 4 * C := by ring
        _ ≤ (1 + σ ^ 2)⁻¹ / (2 * π) + (1 + σ ^ 2)⁻¹ * C := by gcongr
        _ = (1 / (2 * π) + C) * (1 + σ ^ 2)⁻¹ := by ring
    calc F σ * (Real.log (1 + |σ|) / (2 * π) + C)
        ≤ B ^ 2 * (1 / (1 + |σ|) ^ 4) * (Real.log (1 + |σ|) / (2 * π) + C) :=
          mul_le_mul_of_nonneg_right hF hw0
      _ = B ^ 2 * ((1 / (1 + |σ|) ^ 4) * (Real.log (1 + |σ|) / (2 * π) + C)) := by ring
      _ ≤ B ^ 2 * ((1 / (2 * π) + C) * (1 + σ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg B)
      _ = K * (1 + σ ^ 2)⁻¹ := by rw [hK]; ring
  have hptw : ∀ τ : ℝ, F (τ + y) * mu τ ≤ c_y * F (τ + y) + K * (1 + (τ + y) ^ 2)⁻¹ := by
    intro τ
    have hF0 : 0 ≤ F (τ + y) := sq_nonneg _
    have hlog := log_one_add_abs_le_add_shift τ y
    have hmu : mu τ ≤ (Real.log (1 + |τ + y|) / (2 * π) + C) + c_y := by
      have h1 := hC τ
      have h2 : Real.log (1 + |τ|) / (2 * π) ≤
          Real.log (1 + |τ + y|) / (2 * π) + c_y := by
        rw [hcy, ← add_div]
        exact div_le_div_of_nonneg_right hlog (by positivity)
      linarith
    have hmul := mul_le_mul_of_nonneg_left hmu hF0
    linarith [hptw0 (τ + y)]
  have hmono : (∫ τ : ℝ, F (τ + y) * mu τ) ≤
      ∫ τ : ℝ, (c_y * F (τ + y) + K * (1 + (τ + y) ^ 2)⁻¹) :=
    integral_mono hint ((hFyi.const_mul c_y).add hKi) hptw
  have hFint : ∫ τ : ℝ, F (τ + y) = 2 * π * ∫ t, ‖f t‖ ^ 2 := by
    rw [integral_add_right_eq_self (fun σ => F σ) y, hFdef]
    exact integral_norm_sq_paperFT_eq hf hfs
  have hKint : ∫ τ : ℝ, K * (1 + (τ + y) ^ 2)⁻¹ = B ^ 2 * (1 / 2 + π * C) := by
    rw [integral_add_right_eq_self (fun σ => K * (1 + σ ^ 2)⁻¹) y, integral_const_mul,
      integral_univ_inv_one_add_sq, hK]
    field_simp
  rw [integral_add (hFyi.const_mul c_y) hKi, integral_const_mul, hFint, hKint] at hmono
  have hyabs : |y| = 2 * π * |ξ| := by
    rw [hy, abs_mul, abs_of_pos Real.two_pi_pos]
  have hcy_simp : c_y * (2 * π * ∫ t, ‖f t‖ ^ 2) =
      (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) := by
    rw [hcy, hyabs]
    field_simp
  linarith

/-- Uniform logarithmic height-growth upper bound for `archPart`:
`Re A_f(ξ) ≤ 2 e^a (∫ ‖f‖)² + B_f² (1/2 + πC) + (∫ ‖f‖²) log(1 + 2π|ξ|)`. -/
theorem re_archPart_le {C a : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (ξ : ℝ) :
    (archPart f ξ).re ≤
      2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 +
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) +
        (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hval := paperFT_weilTest_heightShift_ofReal hf.continuous hfc ξ
  have hμre : (∫ τ : ℝ, paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
      (mu τ : ℂ)).re = ∫ τ : ℝ, ‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ := by
    have hfun : (fun τ : ℝ => paperFT (EF.weilTest (heightShift ξ f) (heightShift ξ f)) τ *
        (mu τ : ℂ)) = fun τ : ℝ =>
        ((‖paperFT f ((τ + 2 * π * ξ : ℝ) : ℂ)‖ ^ 2 * mu τ : ℝ) : ℂ) := by
      funext τ
      rw [hval, Complex.ofReal_mul]
    rw [hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [archPart, Complex.add_re, hμre]
  have hpole := re_pole_terms_heightShift_le hf.continuous hfs ξ
  have harch := integral_norm_sq_paperFT_shift_mul_mu_le hC0 hC hf hfs ξ
  linarith

/-- Unconditional dichotomy between sub-horizon Weil negativity `Re W_ζ(S_ξ f, S_ξ f) < 0` and
exponential height escape for any threshold
`B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊`. -/
theorem exists_re_W_neg_or_height_escape {C a B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    ∃ ξ : ℝ, B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ∧
      ((zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re < 0 ∨
        B - 2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 -
          (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
          (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|)) := by
  obtain ⟨⟨ξ, hξ⟩, -⟩ :=
    exists_gt_and_lt_re_primePolynomial_of_lt_primeSubCompEnvelope f ⌊Real.exp (2 * a)⌋₊ hB
  refine ⟨ξ, hξ, ?_⟩
  by_cases hW : (zetaZeroConfig.W (heightShift ξ f) (heightShift ξ f)).re < 0
  · exact Or.inl hW
  · refine Or.inr ?_
    rw [not_lt, zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hW
    have harch := re_archPart_le hC0 hC hf hfs ξ
    linarith

/-- Under `RiemannHypothesis`, every threshold
`B < primeOnlyEnvelope f ⌊e^{2a}⌋₊ - primePowerTailEnvelope f ⌊e^{2a}⌋₊` forces the existence of
a Kronecker-aligned height `ξ ∈ ℝ` satisfying the exponential height lower bound
`B - 2 e^a (∫ ‖f‖)² - B_f² (1/2 + πC) < (∫ ‖f‖²) log(1 + 2π|ξ|)`. -/
theorem exists_height_escape_of_riemannHypothesis (hRH : RiemannHypothesis)
    {C a B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ τ : ℝ, mu τ ≤ Real.log (1 + |τ|) / (2 * π) + C) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a)
    (hB : B < primeOnlyEnvelope f ⌊Real.exp (2 * a)⌋₊ -
      primePowerTailEnvelope f ⌊Real.exp (2 * a)⌋₊) :
    ∃ ξ : ℝ, B < (primePolynomial f ⌊Real.exp (2 * a)⌋₊ ξ).re ∧
      B - 2 * Real.exp a * (∫ u, ‖f u‖) ^ 2 -
        (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) ^ 2 * (1 / 2 + π * C) <
        (∫ t, ‖f t‖ ^ 2) * Real.log (1 + 2 * π * |ξ|) := by
  obtain ⟨ξ, hξ, hW | hesc⟩ := exists_re_W_neg_or_height_escape hC0 hC hf hfs hB
  · exfalso
    have hle := riemannHypothesis_iff_primePolynomial_le_archPart.mp hRH a f hf hfs ξ
    rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, Complex.sub_re] at hW
    linarith
  · exact ⟨ξ, hξ, hesc⟩

end GaloisForLFunctions.SquareRootThreshold
