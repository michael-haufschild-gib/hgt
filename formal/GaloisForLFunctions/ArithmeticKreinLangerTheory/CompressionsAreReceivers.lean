import GaloisForLFunctions.HeckeKreinToeplitz.StepanovCompressionsAndTheAnnihilationLaw
import GaloisForLFunctions.HeckeKreinToeplitz.WeilsIndexIsCountedByTheOuterFrobeniusEigenvalues

/-!
# Compressions are receivers

HKT's annihilation law reads an auxiliary measure `P = Σ_α p_α δ_{y_α}` as a **compressor**: the
compressed kernel is positive definite iff the transform `P̂` vanishes at one character of every
hyperbolic pair. This module shows that such spectral-side certificates do not produce counts.

**Over `𝔽_q` the certificate is trivial** (`compress_traceKernel_charPoly`). The characteristic
polynomial `Π_i (X − β_i)` of Frobenius, whose coefficients are determined by finitely many point
counts through Newton's identities, annihilates the trace kernel outright: the trace sequence
satisfies the linear recurrence of order `2g`. Compression by it certifies nothing about `|β_i|`.
Stepanov's auxiliary polynomial is a different object: it vanishes at the rational points, on the
point side, and yields a count.

**Over `ℤ` local compressors kill single Nyquist progressions** (`hat_euler_zeroChar`,
`hat_euler_eq_zero_iff`). The compressor `δ₁ − c δ_p` of one Euler factor has transform
`1 − c p^{ρ−½}` at the character of `ρ`; it vanishes exactly on the vertical progression
`ρ − ½ ∈ (log c⁻¹ + 2πiℤ)/log p`, of spacing `2π/log p`.

**Euler-factor compressions are index-neutral** (`hat_euler_ne_zero`, `negIndex_compress_euler`). For
`|c| ≤ p^{−½}` (the Euler factor `1 − p^{−s}` at `s = ½` has `c = p^{−½}`, whose progression lies on
`Re s = 1`) the transform is nonzero at every character of a point in the open strip `0 < Re ρ < 1`
and at its reflection, so the compression of a Krein–Langer kernel with right-zero pairs keeps its
index exactly. Local Euler data cannot annihilate a pair: a producer must vanish at the primes, not
at the zeros.
-/

open Complex Finset Polynomial
open scoped ComplexConjugate Real
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HeckeKreinToeplitz.CurveDatumKernel

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-! ### Over `𝔽_q`: the characteristic polynomial annihilates the trace kernel -/

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The characteristic polynomial `Π_i (X − β_i)` of normalized Frobenius. -/
def frobCharPoly : ℂ[X] := ∏ i, (X - C (D.β i))

/-- Its coefficients as a compressor at the positions `0, …, |ι|` of the Frobenius tower. -/
def charPolyCoeff (k : Fin (Fintype.card ι + 1)) : ℂ := (frobCharPoly D).coeff k

/-- The positions `0, …, |ι|`. -/
def towerPositions (n : ℕ) (k : Fin (n + 1)) : Multiplicative ℤ := Multiplicative.ofAdd (k : ℤ)

theorem traceKernel_apply (m : Multiplicative ℤ) :
    traceKernel D m = ∑ i, D.β i ^ Multiplicative.toAdd m := by
  simp [traceKernel, valChar, β_ne_zero D]

theorem sum_charPolyCoeff_mul_pow (i : ι) :
    ∑ b : Fin (Fintype.card ι + 1), charPolyCoeff D b * D.β i ^ (b : ℕ) = 0 := by
  have hdeg : (frobCharPoly D).natDegree = Fintype.card ι := by
    rw [frobCharPoly, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp
  have heval : (frobCharPoly D).eval (D.β i) = 0 := by
    rw [frobCharPoly, eval_prod]
    exact prod_eq_zero (mem_univ i) (by simp)
  rw [eval_eq_sum_range, hdeg, ← Fin.sum_univ_eq_sum_range] at heval
  exact heval

/-- **The characteristic polynomial annihilates the trace kernel.** -/
theorem compress_traceKernel_charPoly :
    compress (traceKernel D) (towerPositions (Fintype.card ι)) (charPolyCoeff D) = 0 := by
  funext u
  simp only [compress, Pi.zero_apply]
  have hterm : ∀ a b : Fin (Fintype.card ι + 1),
      conj (charPolyCoeff D a) * charPolyCoeff D b *
        traceKernel D ((towerPositions _ a)⁻¹ * u * towerPositions _ b) =
      ∑ i, (conj (charPolyCoeff D a) * D.β i ^ (Multiplicative.toAdd u - (a : ℤ))) *
        (charPolyCoeff D b * D.β i ^ (b : ℕ)) := fun a b => by
    rw [traceKernel_apply, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hβ := β_ne_zero D i
    simp only [towerPositions, toAdd_mul, toAdd_inv, toAdd_ofAdd]
    rw [show -(a : ℤ) + Multiplicative.toAdd u + (b : ℤ) =
      (Multiplicative.toAdd u - (a : ℤ)) + ((b : ℕ) : ℤ) by push_cast; ring,
      zpow_add₀ hβ, zpow_natCast]
    ring
  simp only [hterm]
  refine sum_eq_zero fun a _ => ?_
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  rw [← mul_sum, sum_charPolyCoeff_mul_pow, mul_zero]

/-! ### Over `ℤ`: Euler-factor compressors -/

/-- The positions `1, p` of the Euler compressor. -/
def eulerNodes {p : ℕ} (hp : p.Prime) : Fin 2 → HeckeLattice := ![1, primeElt hp]

/-- The coefficients `1, −c` of the Euler compressor `δ₁ − c δ_p`. -/
def eulerCoeffs (c : ℂ) : Fin 2 → ℂ := ![1, -c]

/-- **The transform of a local compressor** at the character of `ρ` is `1 − c p^{ρ−½}`. -/
theorem hat_euler_zeroChar {p : ℕ} (hp : p.Prime) (c ρ : ℂ) :
    hat (eulerNodes hp) (eulerCoeffs c) (zeroChar ρ) =
      1 - c * cexp ((ρ - 1 / 2) * Real.log p) := by
  rw [hat_logChar]
  simp [eulerNodes, eulerCoeffs, Fin.sum_univ_two, primeElt, sub_eq_add_neg]

/-- At the reflected character the transform is `1 − c p^{½−ρ̄}`. -/
theorem hat_euler_reflect {p : ℕ} (hp : p.Prime) (c ρ : ℂ) :
    hat (eulerNodes hp) (eulerCoeffs c) (reflectChar (zeroChar ρ)) =
      1 - c * cexp ((1 / 2 - conj ρ) * Real.log p) := by
  rw [hat_reflect_zeroChar, hat_logChar]
  simp [eulerNodes, eulerCoeffs, Fin.sum_univ_two, primeElt, sub_eq_add_neg]

/-- **A local compressor kills one Nyquist progression.** For `c ≠ 0` the transform vanishes at the
character of `ρ` iff `(ρ − ½) log p ∈ log c⁻¹ + 2πiℤ`. -/
theorem hat_euler_eq_zero_iff {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : c ≠ 0) (ρ : ℂ) :
    hat (eulerNodes hp) (eulerCoeffs c) (zeroChar ρ) = 0 ↔
      ∃ k : ℤ, (ρ - 1 / 2) * Real.log p = Complex.log c⁻¹ + k * (2 * π * I) := by
  rw [hat_euler_zeroChar, sub_eq_zero, eq_comm, ← eq_inv_mul_iff_mul_eq₀ hc, mul_one,
    ← Complex.exp_log (inv_ne_zero hc), Complex.exp_eq_exp_iff_exists_int]

/-- **Euler compressors do not vanish on the strip.** For `|c| ≤ p^{−½}` the transform is nonzero
at the character of every `ρ` with `0 < Re ρ < 1` and at its reflection. -/
theorem hat_euler_ne_zero {p : ℕ} (hp : p.Prime) {c : ℂ} (hc : ‖c‖ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)))
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    hat (eulerNodes hp) (eulerCoeffs c) (zeroChar ρ) ≠ 0 ∧
      hat (eulerNodes hp) (eulerCoeffs c) (reflectChar (zeroChar ρ)) ≠ 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hp0 : (0 : ℝ) < p := by linarith
  -- `‖c e^{a log p}‖ = ‖c‖ p^{Re a}`, and `p^{−½} p^{Re a} < 1` for `Re a < ½`
  have key : ∀ a : ℂ, a.re < 1 / 2 → 1 - c * cexp (a * Real.log p) ≠ 0 := fun a ha h => by
    have hn : ‖c * cexp (a * Real.log p)‖ = 1 := by
      rw [← sub_eq_zero.mp h |>.symm, norm_one]
    rw [norm_mul, Complex.norm_exp, Complex.re_mul_ofReal] at hn
    have hexp : Real.exp (a.re * Real.log p) = (p : ℝ) ^ a.re := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
    rw [hexp] at hn
    have hlt : (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ a.re < 1 := by
      rw [← Real.rpow_add hp0]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hp0.le a.re)
    linarith
  refine ⟨?_, ?_⟩
  · rw [hat_euler_zeroChar]
    exact key _ (by simp; linarith)
  · rw [hat_euler_reflect]
    exact key _ (by simp; linarith)

/-- **Euler-factor compressions are index-neutral.** Compressing a positive-definite kernel plus the
pairs of `κ` distinct points with `½ < Re ρ < 1` by `δ₁ − c δ_p`, `|c| ≤ p^{−½}`, keeps the index
`κ`. -/
theorem negIndex_compress_euler {κ : ℕ} {p₀ : HeckeLattice → ℂ} (hp₀ : IsPosDefKernel p₀)
    (ρ : Fin κ → ℂ) (hρ : Function.Injective ρ) (hre : ∀ j, 1 / 2 < (ρ j).re)
    (hre1 : ∀ j, (ρ j).re < 1) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) {p : ℕ} (hp : p.Prime)
    {c : ℂ} (hc : ‖c‖ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ))) :
    negIndex (compress (fun g => p₀ g + ∑ j, pairKernel (zeroChar (ρ j)) (ω j) g)
      (eulerNodes hp) (eulerCoeffs c)) = κ := by
  obtain ⟨u, hne, hsep⟩ := exists_separating_of_small heckeLogScale heckeLogScale_small
    (fun j => ρ j - 1 / 2) (fun i j h => hρ (sub_left_injective h))
    (fun j => by simp only [sub_re, one_div, inv_re, normSq_ofNat]; norm_num; linarith [hre j])
  rw [negIndex_compress_eq hp₀ (fun j => zeroChar (ρ j)) ω hω u hne hsep]
  have hall : (univ.filter fun j => hat (eulerNodes hp) (eulerCoeffs c) (zeroChar (ρ j)) ≠ 0 ∧
      hat (eulerNodes hp) (eulerCoeffs c) (reflectChar (zeroChar (ρ j))) ≠ 0) = univ :=
    filter_true_of_mem fun j _ =>
      hat_euler_ne_zero hp hc (by linarith [hre j]) (hre1 j)
  rw [hall, card_univ, Fintype.card_fin]

end GaloisForLFunctions.ArithmeticKreinLangerTheory
