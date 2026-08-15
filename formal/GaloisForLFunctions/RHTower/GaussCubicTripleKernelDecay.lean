import GaloisForLFunctions.RHTower.GaussCubicTripleEnergyBound

/-!
# Marginal decay of the cubic triple-defect kernel

Two harmonic convolutions give the kernel mass at outer frequency `j` decay
`(1+|j|)^(-2/3)`.  Squaring this marginal inside the cubic energy produces exponent `4/3`, the
summable decay needed for the outer far band.
-/

namespace RHTower

open GaloisForLFunctions
open scoped ENNReal

noncomputable section

def gaussCubicTripleKernelMassConstant (p : Nat.Primes) : ℝ :=
  16 * (p : ℝ) ^ 3 *
    (2 ^ ((3 : ℝ) / 4) *
      (2 * (∑' x : ℤ, intPowWeight (5 / 4) x).toReal)) *
    (2 ^ ((2 : ℝ) / 3) *
      (2 * (∑' x : ℤ, intPowWeight (13 / 12) x).toReal))

theorem gaussCubicTripleKernelMassConstant_nonneg (p : Nat.Primes) :
    0 ≤ gaussCubicTripleKernelMassConstant p := by
  rw [gaussCubicTripleKernelMassConstant]
  positivity

/-- Sharp summable outer marginal of the true cubic coefficient chain. -/
theorem gaussCubicTripleKernelMass_le (p : Nat.Primes) (j : ℤ) :
    gaussCubicTripleKernelMass p j ≤
      ENNReal.ofReal
        (gaussCubicTripleKernelMassConstant p /
          (1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3)) := by
  set W5 : ℝ := (∑' x : ℤ, intPowWeight (5 / 4) x).toReal with hW5
  set W13 : ℝ := (∑' x : ℤ, intPowWeight (13 / 12) x).toReal with hW13
  set C0 : ℝ := 16 * (p : ℝ) ^ 3 with hC0
  set C1 : ℝ := 2 ^ ((3 : ℝ) / 4) * (2 * W5) with hC1
  set C2 : ℝ := 2 ^ ((2 : ℝ) / 3) * (2 * W13) with hC2
  have hC0nn : 0 ≤ C0 := by rw [hC0]; positivity
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  have hC2nn : 0 ≤ C2 := by rw [hC2]; positivity
  have hinner : ∀ l : ℤ,
      (∑' r : ℤ, ENNReal.ofReal (gaussCubicTripleCoeffKernel p j l r)) ≤
        ENNReal.ofReal
          (C0 / (1 + ((l - j).natAbs : ℝ)) *
            (C1 / (1 + (l.natAbs : ℝ)) ^ ((3 : ℝ) / 4))) := by
    intro l
    have hpair := tsum_ofReal_pairKernel_le l
    rw [← hW5] at hpair
    have hrewrite : ∀ r : ℤ,
        ENNReal.ofReal (gaussCubicTripleCoeffKernel p j l r) =
          ENNReal.ofReal (C0 / (1 + ((l - j).natAbs : ℝ))) *
            ENNReal.ofReal
              (1 / ((1 + ((r - l).natAbs : ℝ)) * (1 + (r.natAbs : ℝ)))) := by
      intro r
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [gaussCubicTripleCoeffKernel, gaussPrimeScaleSqCoeffKernel,
        gaussDoubleDefectCoeffKernel, hC0]
      field_simp
      ring
    rw [tsum_congr hrewrite, ENNReal.tsum_mul_left]
    calc
      ENNReal.ofReal (C0 / (1 + ((l - j).natAbs : ℝ))) *
          ∑' r : ℤ, ENNReal.ofReal
            (1 / ((1 + ((r - l).natAbs : ℝ)) * (1 + (r.natAbs : ℝ))))
          ≤ ENNReal.ofReal (C0 / (1 + ((l - j).natAbs : ℝ))) *
              ENNReal.ofReal
                (2 ^ ((3 : ℝ) / 4) *
                  (1 / (1 + (l.natAbs : ℝ)) ^ ((3 : ℝ) / 4)) * (2 * W5)) :=
            mul_le_mul' le_rfl hpair
      _ = ENNReal.ofReal
          (C0 / (1 + ((l - j).natAbs : ℝ)) *
            (C1 / (1 + (l.natAbs : ℝ)) ^ ((3 : ℝ) / 4))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hC1]
        ring
  rw [gaussCubicTripleKernelMass, ENNReal.tsum_prod']
  refine (ENNReal.tsum_le_tsum hinner).trans ?_
  have hconv := tsum_harmonicPowConv_le (j := j)
    (β := (3 : ℝ) / 4) (γ := (2 : ℝ) / 3) (by norm_num) (by norm_num) (by norm_num)
  have hkernel : ∀ l : ℤ,
      ENNReal.ofReal
          (C0 / (1 + ((l - j).natAbs : ℝ)) *
            (C1 / (1 + (l.natAbs : ℝ)) ^ ((3 : ℝ) / 4))) =
        ENNReal.ofReal (C0 * C1) * ENNReal.ofReal
          (1 / ((1 + |(l : ℝ)|) ^ ((3 : ℝ) / 4) *
            (1 + |((j - l : ℤ) : ℝ)|))) := by
    intro l
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [natAbs_cast_eq_abs l, natAbs_sub_symm l j, natAbs_cast_eq_abs (j - l)]
    field_simp
  rw [tsum_congr hkernel, ENNReal.tsum_mul_left]
  have hexp : (3 : ℝ) / 4 + 1 - (2 : ℝ) / 3 = 13 / 12 := by norm_num
  rw [hexp] at hconv
  calc
    ENNReal.ofReal (C0 * C1) *
        ∑' l : ℤ, ENNReal.ofReal
          (1 / ((1 + |(l : ℝ)|) ^ ((3 : ℝ) / 4) *
            (1 + |((j - l : ℤ) : ℝ)|)))
        ≤ ENNReal.ofReal (C0 * C1) *
            (ENNReal.ofReal
              (2 ^ ((2 : ℝ) / 3) / (1 + |(j : ℝ)|) ^ ((2 : ℝ) / 3)) *
              (2 * ∑' x : ℤ, intPowWeight (13 / 12) x)) :=
          mul_le_mul' le_rfl (by simpa using hconv)
    _ = ENNReal.ofReal
        (gaussCubicTripleKernelMassConstant p /
          (1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3)) := by
      have hW13top : (∑' x : ℤ, intPowWeight (13 / 12) x) ≠ ⊤ :=
        tsum_intPowWeight_ne_top (by norm_num)
      have hW13of : ENNReal.ofReal W13 = ∑' x : ℤ, intPowWeight (13 / 12) x := by
        rw [hW13]
        exact ENNReal.ofReal_toReal hW13top
      rw [← ENNReal.ofReal_ofNat 2, ← hW13of,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (mul_nonneg hC0nn hC1nn)]
      congr 1
      rw [gaussCubicTripleKernelMassConstant, ← hW5, ← hW13,
        ← hC0, ← hC1, ← hC2, natAbs_cast_eq_abs]
      field_simp
      ring

end

end RHTower
