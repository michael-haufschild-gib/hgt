import GaloisForLFunctions.RHTower.GaussCubicTripleKernelDecay

/-!
# Summable coordinate marginals of the cubic triple kernel

The cubic cap creates one possible far band in each of the three defect frequencies.  This module
proves the corresponding kernel marginals with exponents `4/3`, `5/4`, and `4/3`, all strictly
summable.
-/

namespace RHTower

open GaloisForLFunctions
open scoped ENNReal

noncomputable section

def gaussCubicTripleDominatingKernel (p : Nat.Primes) (j l r : ℤ) : ℝ :=
  gaussCubicTripleKernelMassConstant p /
      (1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3) *
    gaussCubicTripleCoeffKernel p j l r

theorem gaussCubicTripleDominatingKernel_nonneg (p : Nat.Primes) (j l r : ℤ) :
    0 ≤ gaussCubicTripleDominatingKernel p j l r := by
  rw [gaussCubicTripleDominatingKernel]
  exact mul_nonneg (div_nonneg (gaussCubicTripleKernelMassConstant_nonneg p) (by positivity))
    (gaussCubicTripleCoeffKernel_nonneg p j l r)

def gaussCubicTripleInnerPairConstant : ℝ :=
  2 ^ ((3 : ℝ) / 4) *
    (2 * (∑' x : ℤ, intPowWeight (5 / 4) x).toReal)

def gaussCubicTripleHalfConvConstant : ℝ :=
  2 ^ ((1 : ℝ) / 2) *
    (2 * (∑' x : ℤ, intPowWeight (7 / 6) x).toReal)

def gaussCubicTripleThirdConvConstant : ℝ :=
  2 ^ ((1 : ℝ) / 3) *
    (2 * (∑' x : ℤ, intPowWeight (7 / 6) x).toReal)

def gaussCubicTripleLMarginalConstant (p : Nat.Primes) : ℝ :=
  gaussCubicTripleKernelMassConstant p * (16 * (p : ℝ) ^ 3) *
    gaussCubicTripleHalfConvConstant * gaussCubicTripleInnerPairConstant

def gaussCubicTripleRMarginalConstant (p : Nat.Primes) : ℝ :=
  gaussCubicTripleKernelMassConstant p * (16 * (p : ℝ) ^ 3) *
    gaussCubicTripleHalfConvConstant * gaussCubicTripleThirdConvConstant

theorem gaussCubicTripleInnerPairConstant_nonneg :
    0 ≤ gaussCubicTripleInnerPairConstant := by
  rw [gaussCubicTripleInnerPairConstant]
  positivity

theorem gaussCubicTripleHalfConvConstant_nonneg :
    0 ≤ gaussCubicTripleHalfConvConstant := by
  rw [gaussCubicTripleHalfConvConstant]
  positivity

theorem gaussCubicTripleThirdConvConstant_nonneg :
    0 ≤ gaussCubicTripleThirdConvConstant := by
  rw [gaussCubicTripleThirdConvConstant]
  positivity

theorem gaussCubicTripleLMarginalConstant_nonneg (p : Nat.Primes) :
    0 ≤ gaussCubicTripleLMarginalConstant p := by
  rw [gaussCubicTripleLMarginalConstant]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (gaussCubicTripleKernelMassConstant_nonneg p) (by positivity))
      gaussCubicTripleHalfConvConstant_nonneg)
    gaussCubicTripleInnerPairConstant_nonneg

theorem gaussCubicTripleRMarginalConstant_nonneg (p : Nat.Primes) :
    0 ≤ gaussCubicTripleRMarginalConstant p := by
  rw [gaussCubicTripleRMarginalConstant]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (gaussCubicTripleKernelMassConstant_nonneg p) (by positivity))
      gaussCubicTripleHalfConvConstant_nonneg)
    gaussCubicTripleThirdConvConstant_nonneg

/-- Outer-coordinate marginal, with the kernel mass used a second time. -/
theorem tsum_gaussCubicTripleDominatingKernel_jMarginal_le
    (p : Nat.Primes) (j : ℤ) :
    (∑' lr : ℤ × ℤ, ENNReal.ofReal
      (gaussCubicTripleDominatingKernel p j lr.1 lr.2)) ≤
      ENNReal.ofReal
        (gaussCubicTripleKernelMassConstant p ^ 2 /
          (1 + (j.natAbs : ℝ)) ^ ((4 : ℝ) / 3)) := by
  set C : ℝ := gaussCubicTripleKernelMassConstant p with hC
  set u : ℝ := 1 / (1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3) with hu
  have hCnn : 0 ≤ C := by rw [hC]; exact gaussCubicTripleKernelMassConstant_nonneg p
  have hunn : 0 ≤ u := by rw [hu]; positivity
  have hterm : ∀ lr : ℤ × ℤ,
      ENNReal.ofReal (gaussCubicTripleDominatingKernel p j lr.1 lr.2) =
        ENNReal.ofReal (C * u) *
          ENNReal.ofReal (gaussCubicTripleCoeffKernel p j lr.1 lr.2) := by
    intro lr
    rw [← ENNReal.ofReal_mul (mul_nonneg hCnn hunn)]
    congr 1
    rw [gaussCubicTripleDominatingKernel, ← hC, hu]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  have hmass := gaussCubicTripleKernelMass_le p j
  rw [← hC] at hmass
  calc
    ENNReal.ofReal (C * u) *
        ∑' lr : ℤ × ℤ, ENNReal.ofReal (gaussCubicTripleCoeffKernel p j lr.1 lr.2)
        ≤ ENNReal.ofReal (C * u) * ENNReal.ofReal (C * u) := by
          exact mul_le_mul' le_rfl (by
            simpa [gaussCubicTripleKernelMass, hu, div_eq_mul_inv] using hmass)
    _ = ENNReal.ofReal
        (gaussCubicTripleKernelMassConstant p ^ 2 /
          (1 + (j.natAbs : ℝ)) ^ ((4 : ℝ) / 3)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hCnn hunn)]
      congr 1
      rw [← hC, hu]
      have hpos : 0 < 1 + (j.natAbs : ℝ) := by positivity
      have hpows : (1 + (j.natAbs : ℝ)) ^ ((4 : ℝ) / 3) =
          (1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3) *
            (1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_add hpos]
        norm_num
      field_simp
      rw [hpows]
      ring

/-- Middle-coordinate marginal. -/
theorem tsum_gaussCubicTripleDominatingKernel_lMarginal_le
    (p : Nat.Primes) (l : ℤ) :
    (∑' jr : ℤ × ℤ, ENNReal.ofReal
      (gaussCubicTripleDominatingKernel p jr.1 l jr.2)) ≤
      ENNReal.ofReal
        (gaussCubicTripleLMarginalConstant p /
          (1 + (l.natAbs : ℝ)) ^ ((5 : ℝ) / 4)) := by
  set C : ℝ := gaussCubicTripleKernelMassConstant p with hC
  set C0 : ℝ := 16 * (p : ℝ) ^ 3 with hC0
  set C1 : ℝ := gaussCubicTripleHalfConvConstant with hC1
  set C2 : ℝ := gaussCubicTripleInnerPairConstant with hC2
  have hCnn : 0 ≤ C := by rw [hC]; exact gaussCubicTripleKernelMassConstant_nonneg p
  have hC0nn : 0 ≤ C0 := by rw [hC0]; positivity
  have hC1nn : 0 ≤ C1 := by rw [hC1]; exact gaussCubicTripleHalfConvConstant_nonneg
  have hC2nn : 0 ≤ C2 := by rw [hC2]; exact gaussCubicTripleInnerPairConstant_nonneg
  let f : ℤ → ℝ := fun j => C * C0 *
    (1 / ((1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3) *
      (1 + ((l - j).natAbs : ℝ))))
  let g : ℤ → ℝ := fun r =>
    1 / ((1 + ((r - l).natAbs : ℝ)) * (1 + (r.natAbs : ℝ)))
  have hfnn : ∀ j, 0 ≤ f j := by intro j; simp only [f]; positivity
  have hgnn : ∀ r, 0 ≤ g r := by intro r; simp only [g]; positivity
  have hfactor : ∀ jr : ℤ × ℤ,
      ENNReal.ofReal (gaussCubicTripleDominatingKernel p jr.1 l jr.2) =
        ENNReal.ofReal (f jr.1) * ENNReal.ofReal (g jr.2) := by
    intro jr
    rw [← ENNReal.ofReal_mul (hfnn jr.1)]
    congr 1
    simp only [f, g]
    rw [gaussCubicTripleDominatingKernel, gaussCubicTripleCoeffKernel,
      gaussPrimeScaleSqCoeffKernel, gaussDoubleDefectCoeffKernel, ← hC, hC0]
    field_simp
    ring
  rw [ENNReal.tsum_prod']
  change (∑' j : ℤ, ∑' r : ℤ,
    ENNReal.ofReal (gaussCubicTripleDominatingKernel p j l r)) ≤ _
  have hfactor' : ∀ j r : ℤ,
      ENNReal.ofReal (gaussCubicTripleDominatingKernel p j l r) =
        ENNReal.ofReal (f j) * ENNReal.ofReal (g r) := by
    intro j r
    simpa using hfactor (j, r)
  rw [tsum_congr fun j => tsum_congr fun r => hfactor' j r]
  rw [tsum_congr (fun j => ENNReal.tsum_mul_left), ENNReal.tsum_mul_right]
  have hjconv := tsum_harmonicPowConv_le (j := l)
    (β := (2 : ℝ) / 3) (γ := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
  have hexp : (2 : ℝ) / 3 + 1 - (1 : ℝ) / 2 = 7 / 6 := by norm_num
  rw [hexp] at hjconv
  have hjform : (∑' j : ℤ, ENNReal.ofReal (f j)) ≤
      ENNReal.ofReal (C * C0 *
        (C1 / (1 + (l.natAbs : ℝ)) ^ ((1 : ℝ) / 2))) := by
    have hterm : ∀ j : ℤ, ENNReal.ofReal (f j) =
        ENNReal.ofReal (C * C0) * ENNReal.ofReal
          (1 / ((1 + |(j : ℝ)|) ^ ((2 : ℝ) / 3) *
            (1 + |((l - j : ℤ) : ℝ)|))) := by
      intro j
      rw [← ENNReal.ofReal_mul (mul_nonneg hCnn hC0nn)]
      congr 1
      simp only [f]
      rw [natAbs_cast_eq_abs j, natAbs_cast_eq_abs (l - j)]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    refine (mul_le_mul' le_rfl hjconv).trans_eq ?_
    have hWtop : (∑' x : ℤ, intPowWeight (7 / 6) x) ≠ ⊤ :=
      tsum_intPowWeight_ne_top (by norm_num)
    have hWof : ENNReal.ofReal ((∑' x : ℤ, intPowWeight (7 / 6) x).toReal) =
        ∑' x : ℤ, intPowWeight (7 / 6) x := ENNReal.ofReal_toReal hWtop
    rw [← ENNReal.ofReal_ofNat 2, ← hWof,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (mul_nonneg hCnn hC0nn)]
    congr 1
    rw [hC1, gaussCubicTripleHalfConvConstant, natAbs_cast_eq_abs]
    ring
  have hrform := tsum_ofReal_pairKernel_le l
  have hrform' : (∑' r : ℤ, ENNReal.ofReal (g r)) ≤
      ENNReal.ofReal (C2 / (1 + (l.natAbs : ℝ)) ^ ((3 : ℝ) / 4)) := by
    refine hrform.trans_eq ?_
    congr 1
    rw [hC2, gaussCubicTripleInnerPairConstant]
    ring
  calc
    (∑' j : ℤ, ENNReal.ofReal (f j)) * ∑' r : ℤ, ENNReal.ofReal (g r)
        ≤ ENNReal.ofReal (C * C0 *
            (C1 / (1 + (l.natAbs : ℝ)) ^ ((1 : ℝ) / 2))) *
          ENNReal.ofReal (C2 / (1 + (l.natAbs : ℝ)) ^ ((3 : ℝ) / 4)) :=
            mul_le_mul' hjform hrform'
    _ = ENNReal.ofReal
        (gaussCubicTripleLMarginalConstant p /
          (1 + (l.natAbs : ℝ)) ^ ((5 : ℝ) / 4)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [gaussCubicTripleLMarginalConstant, ← hC, ← hC0, ← hC1, ← hC2]
      have hpos : 0 < 1 + (l.natAbs : ℝ) := by positivity
      have hpows : (1 + (l.natAbs : ℝ)) ^ ((5 : ℝ) / 4) =
          (1 + (l.natAbs : ℝ)) ^ ((1 : ℝ) / 2) *
            (1 + (l.natAbs : ℝ)) ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add hpos]
        norm_num
      field_simp
      rw [hpows]
      ring

/-- Inner-coordinate marginal.  Pair order is `(middle, outer)` so the two harmonic
convolutions are summed in their natural order. -/
theorem tsum_gaussCubicTripleDominatingKernel_rMarginal_le
    (p : Nat.Primes) (r : ℤ) :
    (∑' lj : ℤ × ℤ, ENNReal.ofReal
      (gaussCubicTripleDominatingKernel p lj.2 lj.1 r)) ≤
      ENNReal.ofReal
        (gaussCubicTripleRMarginalConstant p /
          (1 + (r.natAbs : ℝ)) ^ ((4 : ℝ) / 3)) := by
  set C : ℝ := gaussCubicTripleKernelMassConstant p with hC
  set C0 : ℝ := 16 * (p : ℝ) ^ 3 with hC0
  set C1 : ℝ := gaussCubicTripleHalfConvConstant with hC1
  set C2 : ℝ := gaussCubicTripleThirdConvConstant with hC2
  have hCnn : 0 ≤ C := by rw [hC]; exact gaussCubicTripleKernelMassConstant_nonneg p
  have hC0nn : 0 ≤ C0 := by rw [hC0]; positivity
  have hC1nn : 0 ≤ C1 := by rw [hC1]; exact gaussCubicTripleHalfConvConstant_nonneg
  have hC2nn : 0 ≤ C2 := by rw [hC2]; exact gaussCubicTripleThirdConvConstant_nonneg
  have hRnn : 0 ≤ 1 / (1 + (r.natAbs : ℝ)) := by positivity
  have hperL : ∀ l : ℤ,
      (∑' j : ℤ, ENNReal.ofReal (gaussCubicTripleDominatingKernel p j l r)) ≤
        ENNReal.ofReal
          (C * C0 * (1 / (1 + (r.natAbs : ℝ))) *
            (C1 / (1 + (l.natAbs : ℝ)) ^ ((1 : ℝ) / 2)) *
              (1 / (1 + ((r - l).natAbs : ℝ)))) := by
    intro l
    have hconv := tsum_harmonicPowConv_le (j := l)
      (β := (2 : ℝ) / 3) (γ := (1 : ℝ) / 2) (by norm_num) (by norm_num) (by norm_num)
    have hexp : (2 : ℝ) / 3 + 1 - (1 : ℝ) / 2 = 7 / 6 := by norm_num
    rw [hexp] at hconv
    set D : ℝ := C * C0 * (1 / (1 + (r.natAbs : ℝ))) *
      (1 / (1 + ((r - l).natAbs : ℝ))) with hD
    have hDnn : 0 ≤ D := by rw [hD]; positivity
    have hterm : ∀ j : ℤ,
        ENNReal.ofReal (gaussCubicTripleDominatingKernel p j l r) =
          ENNReal.ofReal D * ENNReal.ofReal
            (1 / ((1 + |(j : ℝ)|) ^ ((2 : ℝ) / 3) *
              (1 + |((l - j : ℤ) : ℝ)|))) := by
      intro j
      rw [← ENNReal.ofReal_mul hDnn]
      congr 1
      rw [gaussCubicTripleDominatingKernel, gaussCubicTripleCoeffKernel,
        gaussPrimeScaleSqCoeffKernel, gaussDoubleDefectCoeffKernel,
        ← hC, hD, hC0, natAbs_cast_eq_abs j, natAbs_cast_eq_abs (l - j)]
      field_simp
      ring
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    refine (mul_le_mul' le_rfl hconv).trans_eq ?_
    have hWtop : (∑' x : ℤ, intPowWeight (7 / 6) x) ≠ ⊤ :=
      tsum_intPowWeight_ne_top (by norm_num)
    have hWof : ENNReal.ofReal ((∑' x : ℤ, intPowWeight (7 / 6) x).toReal) =
        ∑' x : ℤ, intPowWeight (7 / 6) x := ENNReal.ofReal_toReal hWtop
    rw [← ENNReal.ofReal_ofNat 2, ← hWof,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hDnn]
    congr 1
    rw [hD, hC1, gaussCubicTripleHalfConvConstant,
      natAbs_cast_eq_abs r, natAbs_cast_eq_abs l]
    ring
  rw [ENNReal.tsum_prod']
  refine (ENNReal.tsum_le_tsum hperL).trans ?_
  have hconv := tsum_harmonicPowConv_le (j := r)
    (β := (1 : ℝ) / 2) (γ := (1 : ℝ) / 3) (by norm_num) (by norm_num) (by norm_num)
  have hexp : (1 : ℝ) / 2 + 1 - (1 : ℝ) / 3 = 7 / 6 := by norm_num
  rw [hexp] at hconv
  set D : ℝ := C * C0 * C1 * (1 / (1 + (r.natAbs : ℝ))) with hD
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  have hterm : ∀ l : ℤ,
      ENNReal.ofReal
          (C * C0 * (1 / (1 + (r.natAbs : ℝ))) *
            (C1 / (1 + (l.natAbs : ℝ)) ^ ((1 : ℝ) / 2)) *
              (1 / (1 + ((r - l).natAbs : ℝ)))) =
        ENNReal.ofReal D * ENNReal.ofReal
          (1 / ((1 + |(l : ℝ)|) ^ ((1 : ℝ) / 2) *
            (1 + |((r - l : ℤ) : ℝ)|))) := by
    intro l
    rw [← ENNReal.ofReal_mul hDnn]
    congr 1
    rw [hD, natAbs_cast_eq_abs l, natAbs_cast_eq_abs (r - l)]
    field_simp
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  calc
    ENNReal.ofReal D *
        ∑' l : ℤ, ENNReal.ofReal
          (1 / ((1 + |(l : ℝ)|) ^ ((1 : ℝ) / 2) *
            (1 + |((r - l : ℤ) : ℝ)|)))
        ≤ ENNReal.ofReal D *
            (ENNReal.ofReal
              (2 ^ ((1 : ℝ) / 3) / (1 + |(r : ℝ)|) ^ ((1 : ℝ) / 3)) *
              (2 * ∑' x : ℤ, intPowWeight (7 / 6) x)) :=
          mul_le_mul' le_rfl hconv
    _ = ENNReal.ofReal
        (gaussCubicTripleRMarginalConstant p /
          (1 + (r.natAbs : ℝ)) ^ ((4 : ℝ) / 3)) := by
      have hWtop : (∑' x : ℤ, intPowWeight (7 / 6) x) ≠ ⊤ :=
        tsum_intPowWeight_ne_top (by norm_num)
      have hWof : ENNReal.ofReal ((∑' x : ℤ, intPowWeight (7 / 6) x).toReal) =
          ∑' x : ℤ, intPowWeight (7 / 6) x := ENNReal.ofReal_toReal hWtop
      rw [← ENNReal.ofReal_ofNat 2, ← hWof,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hDnn]
      congr 1
      rw [gaussCubicTripleRMarginalConstant, ← hC, ← hC0, ← hC1,
        hD, gaussCubicTripleThirdConvConstant, natAbs_cast_eq_abs]
      have hpos : 0 < 1 + |(r : ℝ)| := by positivity
      have hpows : (1 + |(r : ℝ)|) ^ ((4 : ℝ) / 3) =
          (1 + |(r : ℝ)|) * (1 + |(r : ℝ)|) ^ ((1 : ℝ) / 3) := by
        rw [show (4 : ℝ) / 3 = 1 + (1 : ℝ) / 3 by norm_num,
          Real.rpow_add hpos, Real.rpow_one]
      field_simp
      rw [hpows]
      ring

end

end RHTower
