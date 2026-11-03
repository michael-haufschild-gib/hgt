import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheFrobeniusAnglesDiagonalizeTheCurveFamily
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermOfEveryPeriodicTwist

/-!
# The rescaled limit of a curve is the Hurwitz form of its angles

Over `ℤ` the complete family degenerates as the atom overlap grows, and its rescaled limit is the
Jordan-totient form of the conductors (ADT). Over a pure curve the family of lattice tests is
diagonal in the Frobenius angles at every width (`W_curveLatticeTest`); this file computes its
degeneration.

* **The density form** (`W_curveLatticeTest_eq_density`): with `u_i = {arg β_i/2π}` the fractional
  angle, `W(T_x, T_x) = w² Σ_i |Σ_k x_k β_i^k|² (D_{u_i} + D_{1−u_i})(w/log q)`.
* **The curve bulk** `E_x(a) = Σ_i |Σ_k x_k β_i^k|² (E_{u_i} + E_{1−u_i})(a)` is the antiderivative
  of the family under dilation (`hasDerivAt_curveBulk`): `W(T_x, T_x) = −w² E_x'(w/log q)`.
* **The rescaled limit** (`tendsto_rpow_mul_curveBulk`): for a profile with regular spectral tail
  `x^β T(x) → A_φ` and a curve without the eigenvalue `1`,

  `a^β E_x(a) → A_φ Σ_i |Σ_k x_k β_i^k|² (ζ(β+1, u_i) + ζ(β+1, 1 − u_i))`,

  the Hurwitz form of the Frobenius angles: the `𝔽_q` calibration of the Jordan-totient rescaled
  limit, with the angles of Frobenius in place of the conductors.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) {φ : ℝ → ℝ}

/-- The fractional Frobenius angle `u = {arg β/2π} ∈ [0, 1)`. -/
def frobeniusShift (z : ℂ) : ℝ := Int.fract (Complex.arg z / (2 * Real.pi))

/-- The lattice spectrum at an angle is the pair of shifted densities at its fractional part:
`Σ_{j∈ℤ} |φ̂(2πa(j + θ))|² = D_u(a) + D_{1−u}(a)`, `u = {θ}`. -/
theorem tsum_shellSpectrum_shift_eq_fract (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    ∑' j : ℤ, shellSpectrum φ (a * (j + θ)) =
      twistDensity φ (Int.fract θ) a + twistDensity φ (1 - Int.fract θ) a := by
  have hsplit := hasSum_shellSpectrum_shift_split hφ hφsupp ha (Int.fract θ)
  have e : ∀ j : ℤ, shellSpectrum φ (a * (j + θ)) =
      (fun k : ℤ => shellSpectrum φ (a * (k + Int.fract θ))) (Equiv.addRight ⌊θ⌋ j) := by
    intro j
    simp only [Equiv.coe_addRight]
    congr 2
    push_cast
    rw [Int.fract]
    ring
  rw [tsum_congr e]
  exact ((Equiv.addRight ⌊θ⌋).tsum_eq _).trans hsplit.tsum_eq

/-- **The density form of a curve.** -/
theorem W_curveLatticeTest_eq_density (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq) (hpure : ∀ i, ‖D.β i‖ = 1)
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {w : ℝ} (hw : 0 < w)
    (n : ℕ) (x : ℕ → ℝ) :
    (D.curveConfig hD).W (curveLatticeTest D φ w n x) (curveLatticeTest D φ w n x) =
      ((w ^ 2 * ∑ i, ‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 *
        (twistDensity φ (frobeniusShift (D.β i)) (w / Real.log D.q) +
          twistDensity φ (1 - frobeniusShift (D.β i)) (w / Real.log D.q)) : ℝ) : ℂ) := by
  have hL : 0 < Real.log D.q := D.log_q_pos
  rw [W_curveLatticeTest D hD hpure hφ hφsupp hw n x]
  simp_rw [tsum_shellSpectrum_shift_eq_fract hφ hφsupp (div_pos hw hL)]
  rw [Finset.mul_sum]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  unfold frobeniusShift
  ring

/-- The curve bulk `E_x(a) = Σ_i |Σ_k x_k β_i^k|² (E_{u_i} + E_{1−u_i})(a)`. -/
def curveBulk (φ : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (a : ℝ) : ℝ :=
  ∑ i, ‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 *
    (twistBulk φ (frobeniusShift (D.β i)) a + twistBulk φ (1 - frobeniusShift (D.β i)) a)

/-- The Hurwitz form of the Frobenius angles at exponent `s`. -/
def curveHurwitzForm (s : ℝ) (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i, ‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 *
    (hurwitzSum s (frobeniusShift (D.β i)) + hurwitzSum s (1 - frobeniusShift (D.β i)))

/-- Away from the eigenvalue `1` the fractional angle is in `(0, 1)`. -/
theorem frobeniusShift_mem {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    0 < frobeniusShift z ∧ frobeniusShift z < 1 := by
  refine ⟨?_, Int.fract_lt_one _⟩
  rcases (Int.fract_nonneg (Complex.arg z / (2 * Real.pi))).lt_or_eq with h | h
  · exact h
  · exfalso
    apply h1
    -- `arg z/2π ∈ ℤ` and `arg z ∈ (−π, π]` force `arg z = 0`, so `z = 1`
    have hz0 : z ≠ 0 := fun h0 => by rw [h0, norm_zero] at hz; exact zero_ne_one hz
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Complex.arg z / (2 * Real.pi) = m :=
      ⟨⌊Complex.arg z / (2 * Real.pi)⌋, by
        have := Int.floor_add_fract (Complex.arg z / (2 * Real.pi))
        rw [← h] at this; linarith⟩
    have hpi := Real.pi_pos
    have harg : Complex.arg z = 2 * Real.pi * m := by
      field_simp at hm; linarith
    have hm0 : m = 0 := by
      have h1' := Complex.neg_pi_lt_arg z
      have h2' := Complex.arg_le_pi z
      rw [harg] at h1' h2'
      have hlt : (m : ℝ) < 1 := by nlinarith
      have hgt : (-1 : ℝ) < m := by nlinarith
      have : m < 1 := by exact_mod_cast hlt
      have : -1 < m := by exact_mod_cast hgt
      omega
    rw [hm0, Int.cast_zero, mul_zero] at harg
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, harg, Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at h
    exact h.symm

/-- **The curve bulk is the antiderivative of the curve family under dilation.** -/
theorem hasDerivAt_curveBulk (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ p : ℝ} (hp : 1 < p) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hpure : ∀ i, ‖D.β i‖ = 1) (hne : ∀ i, D.β i ≠ 1) (n : ℕ) (x : ℕ → ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (curveBulk D φ n x)
      (-∑ i, ‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2 *
        (twistDensity φ (frobeniusShift (D.β i)) a +
          twistDensity φ (1 - frobeniusShift (D.β i)) a)) a := by
  unfold curveBulk
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun i _ => ?_
  obtain ⟨h0, h1⟩ := frobeniusShift_mem (hpure i) (hne i)
  have hd1 := hasDerivAt_twistBulk hφ hφsupp hp hCφ hdecay hβ hT h0 h1.le ha
  have hd2 := hasDerivAt_twistBulk hφ hφsupp hp hCφ hdecay hβ hT
    (by linarith : 0 < 1 - frobeniusShift (D.β i))
    (by linarith : 1 - frobeniusShift (D.β i) ≤ 1) ha
  exact ((hd1.add hd2).const_mul (‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2)).congr_deriv
    (by ring)

/-- **The rescaled limit of a curve is the Hurwitz form of its angles**:
`a^β E_x(a) → A_φ Σ_i |Σ_k x_k β_i^k|² (ζ(β+1, u_i) + ζ(β+1, 1 − u_i))`. -/
theorem tendsto_rpow_mul_curveBulk (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hpure : ∀ i, ‖D.β i‖ = 1) (hne : ∀ i, D.β i ≠ 1) (n : ℕ) (x : ℕ → ℝ) :
    Tendsto (fun a => a ^ β * curveBulk D φ n x a) atTop
      (𝓝 (Aφ * curveHurwitzForm D (β + 1) n x)) := by
  unfold curveBulk curveHurwitzForm
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine tendsto_finsetSum _ fun i _ => ?_
  obtain ⟨h0, h1⟩ := frobeniusShift_mem (hpure i) (hne i)
  have l1 := tendsto_rpow_mul_twistBulk hφ hφsupp hβ hT h0 h1.le
  have l2 := tendsto_rpow_mul_twistBulk hφ hφsupp hβ hT (by linarith : 0 < 1 - frobeniusShift (D.β i))
    (by linarith : 1 - frobeniusShift (D.β i) ≤ 1)
  have := (l1.add l2).const_mul (‖∑ k ∈ range n, (x k : ℂ) * D.β i ^ k‖ ^ 2)
  convert this using 2 <;> ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
