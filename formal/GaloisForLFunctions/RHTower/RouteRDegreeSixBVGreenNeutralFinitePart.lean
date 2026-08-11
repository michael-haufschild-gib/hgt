import GaloisForLFunctions.RHTower.RouteRDegreeSixBVGreenPhysicalCyclicDescentWall
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# Degree-six BV--Green neutral finite part

This module computes the diagonal finite part of the literal ordinary-integer
BV--Green boundary.  At dilation `n`, its `k`-th diagonal coefficient is

`n⁻¹ k⁻¹ - 1_{n ∣ k} k⁻¹`.

The cutoff through `N` is therefore exactly

`n⁻¹ (H_N - H_{⌊N/n⌋})`,

and converges to `log n / n`.  Independently, the neutral derivative of the
modular anomaly `n⁻¹(1-exp(-a log n))` is the same number.  At the Route R
degree `n=6`, this common value is strictly positive.

Consequently the grade-zero cyclic cancellation of the boundary does not
extend to a grade-flat diagonal trace law: its first Bockstein jet is a
nonzero finite part.  Any remaining physical annihilation must therefore use
the external positive-polar/compression comparison rather than analytic
continuation of the source cyclic reader.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem sum_multiples_inv_eq_harmonic
    {n N : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range N,
      if n ∣ k + 1 then (((k + 1 : ℕ) : ℝ))⁻¹ else 0) =
      ((n : ℝ))⁻¹ * (harmonic (N / n) : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  rw [harmonic]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_bij
      (fun k _hk => (k + 1) / n - 1)
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_range]
    have hklt : k < N := Finset.mem_range.mp hk.1
    have hdvd : n ∣ k + 1 := hk.2
    have hnle : n ≤ k + 1 := Nat.le_of_dvd (by omega) hdvd
    have hqpos : 0 < (k + 1) / n := Nat.div_pos hnle hn
    have hqle : (k + 1) / n ≤ N / n := Nat.div_le_div_right (by omega)
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_filter] at hk₁ hk₂
    have hnle1 : n ≤ k₁ + 1 := Nat.le_of_dvd (by omega) hk₁.2
    have hnle2 : n ≤ k₂ + 1 := Nat.le_of_dvd (by omega) hk₂.2
    have hq1 : 0 < (k₁ + 1) / n := Nat.div_pos hnle1 hn
    have hq2 : 0 < (k₂ + 1) / n := Nat.div_pos hnle2 hn
    have hdiv : (k₁ + 1) / n = (k₂ + 1) / n := by omega
    have hmul1 : n * ((k₁ + 1) / n) = k₁ + 1 :=
      Nat.mul_div_cancel' hk₁.2
    have hmul2 : n * ((k₂ + 1) / n) = k₂ + 1 :=
      Nat.mul_div_cancel' hk₂.2
    have hadd : k₁ + 1 = k₂ + 1 := by
      calc
        k₁ + 1 = n * ((k₁ + 1) / n) := hmul1.symm
        _ = n * ((k₂ + 1) / n) := by rw [hdiv]
        _ = k₂ + 1 := hmul2
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    let k := n * (j + 1) - 1
    have hprodpos : 0 < n * (j + 1) := Nat.mul_pos hn (by omega)
    have hjle : j + 1 ≤ N / n := by omega
    have hprodle : n * (j + 1) ≤ N := by
      rw [Nat.mul_comm]
      exact (Nat.le_div_iff_mul_le hn).mp hjle
    have hklt : k < N := by
      dsimp [k]
      omega
    have hkadd : k + 1 = n * (j + 1) := by
      dsimp [k]
      omega
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, ?_⟩, ?_⟩
    · rw [hkadd]
      exact dvd_mul_right n (j + 1)
    · rw [hkadd, Nat.mul_div_cancel_left _ hn]
      omega
  · intro k hk
    rw [Finset.mem_filter] at hk
    have hnle : n ≤ k + 1 := Nat.le_of_dvd (by omega) hk.2
    have hqpos : 0 < (k + 1) / n := Nat.div_pos hnle hn
    have hmul : n * ((k + 1) / n) = k + 1 := Nat.mul_div_cancel' hk.2
    have hmulR : (n : ℝ) * (((k + 1) / n : ℕ) : ℝ) = (k : ℝ) + 1 := by
      exact_mod_cast hmul
    have hqsubR : ((((k + 1) / n - 1 : ℕ) : ℝ)) + 1 =
        ((((k + 1) / n : ℕ) : ℝ)) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ (k + 1) / n))
    rw [hqsubR, ← hmulR]
    have hqR : ((((k + 1) / n : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast hqpos.ne'
    rw [mul_inv_rev]
    ring

/-- Real diagonal coefficient of the literal BV--Green boundary at dilation
`n` and basis index `k`. -/
def deningerOrdinaryIntegerBVGreenDiagonalCoefficient (n k : ℕ) : ℝ :=
  ((n : ℝ))⁻¹ * ((k : ℝ))⁻¹ -
    if n ∣ k then ((k : ℝ))⁻¹ else 0

/-- Finite diagonal cutoff of the literal BV--Green boundary. -/
def deningerOrdinaryIntegerBVGreenDiagonalCutoff (n N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    deningerOrdinaryIntegerBVGreenDiagonalCoefficient n (k + 1)

/-- The scalar coefficient is the diagonal coefficient of the actual
ordinary-integer BV--Green boundary operator. -/
theorem deningerOrdinaryIntegerBVGreenDiagonalCoefficient_eq_operator
    (n k : PNat) :
    deningerOrdinaryIntegerDiagonalCoefficient k
        (deningerOrdinaryIntegerBVGreenStokesBoundary n) =
      (deningerOrdinaryIntegerBVGreenDiagonalCoefficient
        (n : ℕ) (k : ℕ) : ℂ) := by
  have hdvd : n ∣ k ↔ (n : ℕ) ∣ (k : ℕ) := by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨(m : ℕ), congrArg (fun x : PNat => (x : ℕ)) hm⟩
    · rintro ⟨m, hm⟩
      have hmpos : 0 < m := by
        by_contra h
        have hmzero : m = 0 := Nat.eq_zero_of_not_pos h
        rw [hmzero, mul_zero] at hm
        exact k.prop.ne' hm
      exact ⟨⟨m, hmpos⟩, Subtype.ext hm⟩
  rw [deningerOrdinaryIntegerBVGreenStokesBoundary_eq]
  simp [deningerOrdinaryIntegerDiagonalCoefficient,
    deningerOrdinaryIntegerBasisVector,
    deningerOrdinaryIntegerBVGreenDiagonalCoefficient]
  rw [hdvd]
  split_ifs <;> norm_num

/-- Exact finite-cutoff identity. -/
theorem deningerOrdinaryIntegerBVGreenDiagonalCutoff_eq_harmonic
    {n N : ℕ} (hn : 0 < n) :
    deningerOrdinaryIntegerBVGreenDiagonalCutoff n N =
      ((n : ℝ))⁻¹ *
        ((harmonic N : ℝ) - (harmonic (N / n) : ℝ)) := by
  rw [deningerOrdinaryIntegerBVGreenDiagonalCutoff]
  simp only [deningerOrdinaryIntegerBVGreenDiagonalCoefficient]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  have hfirst : (∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ))⁻¹) =
      (harmonic N : ℝ) := by
    rw [harmonic]
    push_cast
    rfl
  rw [hfirst, sum_multiples_inv_eq_harmonic hn]
  ring

/-- The diagonal finite part is `log n / n`. -/
theorem tendsto_deningerOrdinaryIntegerBVGreenDiagonalCutoff
    {n : ℕ} (hn : 0 < n) :
    Tendsto (deningerOrdinaryIntegerBVGreenDiagonalCutoff n) atTop
      (nhds (Real.log n / n)) := by
  have htop := Real.tendsto_harmonic_sub_log
  have hdec :=
    GaloisForLFunctions.HTGeometry.tendsto_harmonic_natDiv_sub_log hn
  have hdiff := htop.sub hdec
  have hscaled := hdiff.const_mul ((n : ℝ)⁻¹)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  convert hscaled using 1
  · funext N
    rw [deningerOrdinaryIntegerBVGreenDiagonalCutoff_eq_harmonic hn]
    ring
  · rw [show Real.eulerMascheroniConstant -
        (Real.eulerMascheroniConstant - Real.log n) = Real.log n by ring]
    field_simp [hnR]

/-- Scalar modular anomaly whose neutral jet is compared with the diagonal
finite part. -/
def deningerOrdinaryIntegerBVGreenModularAnomaly (n : ℕ) (a : ℝ) : ℝ :=
  ((n : ℝ))⁻¹ * (1 - Real.exp (-a * Real.log n))

/-- The neutral derivative of the modular anomaly is `log n / n`. -/
theorem hasDerivAt_deningerOrdinaryIntegerBVGreenModularAnomaly_zero
    (n : ℕ) :
    HasDerivAt (deningerOrdinaryIntegerBVGreenModularAnomaly n)
      (Real.log n / n) 0 := by
  have hinner : HasDerivAt (fun a : ℝ => -a * Real.log n)
      (-Real.log n) 0 := by
    simpa [mul_comm] using
      (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul (-Real.log n)
  have hexp := hinner.exp
  have hsub :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp
  have hmul := hsub.const_mul ((n : ℝ))⁻¹
  change HasDerivAt
    (fun a : ℝ => ((n : ℝ))⁻¹ * (1 - Real.exp (-a * Real.log n)))
    (Real.log n / n) 0
  simpa only [Pi.sub_apply, neg_zero, zero_mul, Real.exp_zero, mul_neg,
    one_mul, zero_sub, neg_neg, div_eq_mul_inv, mul_comm] using hmul

/-- The diagonal finite part equals the neutral Bockstein jet. -/
theorem deningerOrdinaryIntegerBVGreenFinitePart_eq_bocksteinJet
    {n : ℕ} (hn : 0 < n) :
    Tendsto (deningerOrdinaryIntegerBVGreenDiagonalCutoff n) atTop
      (nhds (deriv (deningerOrdinaryIntegerBVGreenModularAnomaly n) 0)) := by
  rw [(hasDerivAt_deningerOrdinaryIntegerBVGreenModularAnomaly_zero n).deriv]
  exact tendsto_deningerOrdinaryIntegerBVGreenDiagonalCutoff hn

/-- Degree-six diagonal finite part is strictly positive. -/
theorem deningerDegreeSixBVGreenFinitePart_pos :
    0 < Real.log 6 / 6 := by
  positivity

/-- Degree-six neutral Bockstein jet is strictly positive. -/
theorem deningerDegreeSixBVGreenNeutralBocksteinJet_pos :
    0 < deriv (deningerOrdinaryIntegerBVGreenModularAnomaly 6) 0 := by
  rw [(hasDerivAt_deningerOrdinaryIntegerBVGreenModularAnomaly_zero 6).deriv]
  exact deningerDegreeSixBVGreenFinitePart_pos

/-- In particular, grade-zero cyclic cancellation cannot extend to a
grade-flat neutral Bockstein trace law. -/
theorem deningerDegreeSixBVGreenNeutralBocksteinJet_ne_zero :
    deriv (deningerOrdinaryIntegerBVGreenModularAnomaly 6) 0 ≠ 0 :=
  ne_of_gt deningerDegreeSixBVGreenNeutralBocksteinJet_pos

/-- The degree-six boundary cutoff cannot converge to zero. -/
theorem not_tendsto_deningerDegreeSixBVGreenDiagonalCutoff_zero :
    ¬ Tendsto (deningerOrdinaryIntegerBVGreenDiagonalCutoff 6) atTop
      (nhds 0) := by
  intro hzero
  have heq : (0 : ℝ) = Real.log 6 / 6 :=
    tendsto_nhds_unique hzero
      (tendsto_deningerOrdinaryIntegerBVGreenDiagonalCutoff
        (by norm_num : 0 < 6))
  linarith [deningerDegreeSixBVGreenFinitePart_pos]

end

end RHTower
