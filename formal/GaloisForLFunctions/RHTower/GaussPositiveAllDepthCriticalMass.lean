import Mathlib.Analysis.PSeries
import GaloisForLFunctions.HTGeometry.PositiveOperatorPowerMoment
import GaloisForLFunctions.RHTower.GaussPositiveCubicCriticalMass
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Positive critical mass of the Gauss operator at every depth

The positive folded Gauss block has an unavoidable critical harmonic diagonal at every component
depth. This extends the previously cubic-only theorem to arbitrary `m ≥ 1`.
-/

open RCLike
open scoped InnerProductSpace ComplexConjugate ComplexOrder

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

/-- Positivity amplifies the retained source coefficient into the actual `m`-th Fourier diagonal. -/
theorem gaussArchScale_pow_mul_norm_pow_div_two_pow_le_re_inner_gaussQuasiInnerGFull_pow
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) {i : ℤ} (hi : i ≠ 0)
    (hF : gaussFoldDefect hm k p hp i *
        (gaussFoldDefect hm k p hp i +
          2 * ‖gaussPrimeScaleBlock hp
            (fourierLp 2 (0 : ℤ) :
              Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)
      ≤ 1 / (2 * (p : ℝ))) :
    gaussArchScale m ^ (2 * m) * ‖gaussSampleValue k p i‖ ^ (2 * m) / 2 ^ m ≤
      re (inner ℂ (fourierLp 2 i)
        ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 i))) := by
  let q : ℝ := re (inner ℂ (fourierLp 2 i)
    (gaussQuasiInnerGFull hm k p (fourierLp 2 i)))
  let lower : ℝ := gaussArchScale m ^ 2 * ‖gaussSampleValue k p i‖ ^ 2 / 2
  have hbase := half_norm_gaussSampleValue_sq_le_re_inner_gaussQuasiInnerG
    hm k p hp hi hF
  have hscale : 0 ≤ gaussArchScale m ^ 2 := sq_nonneg _
  have hfirst : lower ≤ q := by
    have hmul := mul_le_mul_of_nonneg_left hbase hscale
    dsimp [lower, q]
    rw [gaussQuasiInnerGFull_eq, smul_apply, inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    simpa [mul_div_assoc] using hmul
  have hlower : 0 ≤ lower := by
    dsimp [lower]
    positivity
  have hpow : lower ^ m ≤ q ^ m := pow_le_pow_left₀ hlower hfirst m
  have hmom := (gaussQuasiInnerGFull_isPositive hm k p).re_inner_pow_ge
    (fourierLp 2 i) (norm_fourierLp_eq_one i) m
  calc
    gaussArchScale m ^ (2 * m) * ‖gaussSampleValue k p i‖ ^ (2 * m) / 2 ^ m =
        lower ^ m := by
      dsimp [lower]
      rw [div_pow, mul_pow]
      simp only [pow_mul]
    _ ≤ q ^ m := hpow
    _ ≤ re (inner ℂ (fourierLp 2 i)
        ((gaussQuasiInnerGFull hm k p ^ m) (fourierLp 2 i))) := by
      simpa [q] using hmom

/-- Real two-orientation `m`-th-power diagonal of the actual `m`-component Gauss block. -/
def gaussPowerTwoSidedDiagonalReal {m : ℕ} (hm : 1 ≤ m)
    (k : Fin m) (p : Nat.Primes) (n : ℕ) : ℝ :=
  re (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
      ((gaussQuasiInnerGFull hm k p ^ m)
        (fourierLp 2 ((n : ℤ) + 1)))) +
    re (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
      ((gaussQuasiInnerGFull hm k p ^ m)
        (fourierLp 2 (-((n : ℤ) + 1)))))

/-- The positive orientation eventually retains `2⁻ᵐ` of sampled critical energy. -/
theorem eventually_energy_div_two_pow_le_gaussPowerTwoSidedDiagonalReal
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ∀ᶠ n : ℕ in atTop,
      gaussComponentPrimeMagnitudeEnergy k p n / 2 ^ m ≤
        gaussPowerTwoSidedDiagonalReal hm k p n := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  let F : ℤ → ℝ := fun i =>
    gaussFoldDefect hm k p hp i *
      (gaussFoldDefect hm k p hp i +
        2 * ‖gaussPrimeScaleBlock hp
          (fourierLp 2 (0 : ℤ) :
            Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))‖)
  have hιp : Tendsto (fun n : ℕ => (((n : ℤ) + 1)).natAbs) atTop atTop := by
    refine (tendsto_add_atTop_nat 1).congr fun n => ?_
    omega
  have hFp : Tendsto (fun n : ℕ => F ((n : ℤ) + 1)) atTop (nhds 0) :=
    tendsto_gaussRelativeDiagonalFactor hm k p hp hιp
  have hthreshold : (0 : ℝ) < 1 / (2 * (p : ℝ)) := by positivity
  have hFpe : ∀ᶠ n : ℕ in atTop, F ((n : ℤ) + 1) ≤ 1 / (2 * (p : ℝ)) :=
    hFp.eventually (eventually_le_nhds hthreshold)
  filter_upwards [hFpe] with n hpos
  have hip : ((n : ℤ) + 1) ≠ 0 := by omega
  have hpow :=
    gaussArchScale_pow_mul_norm_pow_div_two_pow_le_re_inner_gaussQuasiInnerGFull_pow
      hm k p hp hip hpos
  have henergy : gaussArchScale m ^ (2 * m) *
      ‖gaussSampleValue k p ((n : ℤ) + 1)‖ ^ (2 * m) =
        gaussComponentPrimeMagnitudeEnergy k p n := by
    have h := norm_gaussSampleValueFull_pow hm k p hip
    rw [show (((n : ℤ) + 1).natAbs - 1) = n by omega] at h
    simpa using h
  rw [henergy] at hpow
  have hnegative : 0 ≤ re (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
      ((gaussQuasiInnerGFull hm k p ^ m)
        (fourierLp 2 (-((n : ℤ) + 1))))) :=
    (gaussQuasiInnerGFull_isPositive hm k p).re_inner_pow_nonneg _ m
  rw [gaussPowerTwoSidedDiagonalReal]
  exact hpow.trans (le_add_of_nonneg_right hnegative)

/-- Every two-orientation power diagonal term is nonnegative, including finite prefix. -/
theorem gaussPowerTwoSidedDiagonalReal_nonneg {m : ℕ} (hm : 1 ≤ m)
    (k : Fin m) (p : Nat.Primes) (n : ℕ) :
    0 ≤ gaussPowerTwoSidedDiagonalReal hm k p n := by
  have hT := gaussQuasiInnerGFull_isPositive hm k p
  have hp := hT.re_inner_pow_nonneg (fourierLp 2 ((n : ℤ) + 1)) m
  have hn := hT.re_inner_pow_nonneg (fourierLp 2 (-((n : ℤ) + 1))) m
  simpa [gaussPowerTwoSidedDiagonalReal] using add_nonneg hp hn

/-- At every component depth, actual positive Gauss diagonal has divergent positive sums. -/
theorem tendsto_gaussPowerTwoSidedDiagonal_sum_atTop
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range M, gaussPowerTwoSidedDiagonalReal hm k p n)
      atTop atTop := by
  obtain ⟨c, C, hc, hC, henergy⟩ :=
    exists_gaussComponentPrimeMagnitudeEnergy_bounds hm k p
  have hevent := eventually_energy_div_two_pow_le_gaussPowerTwoSidedDiagonalReal hm k p
  have hpowpos : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  have hpoint : ∀ᶠ n : ℕ in atTop,
      c / (2 ^ m * ((n : ℝ) + 1)) ≤ gaussPowerTwoSidedDiagonalReal hm k p n := by
    filter_upwards [hevent] with n hn
    have hlow := (henergy n).1
    calc
      c / (2 ^ m * ((n : ℝ) + 1)) = (c / ((n : ℝ) + 1)) / 2 ^ m := by
        field_simp
      _ ≤ gaussComponentPrimeMagnitudeEnergy k p n / 2 ^ m := by
        exact div_le_div_of_nonneg_right hlow hpowpos.le
      _ ≤ gaussPowerTwoSidedDiagonalReal hm k p n := hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpoint
  let r : ℝ := c / (2 ^ m * ((N : ℝ) + 1))
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hshift_point : ∀ j : ℕ,
      r * (1 / ((j : ℝ) + 1)) ≤ gaussPowerTwoSidedDiagonalReal hm k p (N + j) := by
    intro j
    have hNj := hN (N + j) (Nat.le_add_right N j)
    have hbase : (N : ℝ) + (j : ℝ) + 1 ≤ ((N : ℝ) + 1) * ((j : ℝ) + 1) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)
        (show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j)]
    have hden : 2 ^ m * ((N : ℝ) + (j : ℝ) + 1) ≤
        2 ^ m * ((N : ℝ) + 1) * ((j : ℝ) + 1) := by
      calc
        2 ^ m * ((N : ℝ) + (j : ℝ) + 1) ≤
            2 ^ m * (((N : ℝ) + 1) * ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hbase hpowpos.le
        _ = 2 ^ m * ((N : ℝ) + 1) * ((j : ℝ) + 1) := by ring
    have hsmall : 0 < 2 ^ m * ((N : ℝ) + (j : ℝ) + 1) := by positivity
    have hfrac : c / (2 ^ m * ((N : ℝ) + 1) * ((j : ℝ) + 1)) ≤
        c / (2 ^ m * ((N : ℝ) + (j : ℝ) + 1)) :=
      div_le_div_of_nonneg_left hc.le hsmall hden
    calc
      r * (1 / ((j : ℝ) + 1)) =
          c / (2 ^ m * ((N : ℝ) + 1) * ((j : ℝ) + 1)) := by
        dsimp [r]
        field_simp
      _ ≤ c / (2 ^ m * ((N : ℝ) + (j : ℝ) + 1)) := hfrac
      _ = c / (2 ^ m * (((N + j : ℕ) : ℝ) + 1)) := by push_cast; ring
      _ ≤ gaussPowerTwoSidedDiagonalReal hm k p (N + j) := hNj
  have hsum_shift : ∀ M : ℕ,
      r * (∑ j ∈ Finset.range M, (1 / ((j : ℝ) + 1))) ≤
        ∑ j ∈ Finset.range M, gaussPowerTwoSidedDiagonalReal hm k p (N + j) := by
    intro M
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hshift_point j
  have hsum_total : ∀ M : ℕ,
      r * (∑ j ∈ Finset.range M, (1 / ((j : ℝ) + 1))) ≤
        ∑ j ∈ Finset.range (N + M), gaussPowerTwoSidedDiagonalReal hm k p j := by
    intro M
    rw [Finset.sum_range_add]
    exact (hsum_shift M).trans (le_add_of_nonneg_left
      (Finset.sum_nonneg fun j _ => gaussPowerTwoSidedDiagonalReal_nonneg hm k p j))
  have hharm : Tendsto
      (fun M : ℕ => r * (∑ j ∈ Finset.range M, (1 / ((j : ℝ) + 1))))
      atTop atTop :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hr
  have hshift : Tendsto
      (fun M : ℕ => ∑ j ∈ Finset.range (N + M), gaussPowerTwoSidedDiagonalReal hm k p j)
      atTop atTop :=
    tendsto_atTop_mono hsum_total hharm
  have hshift' : Tendsto
      (fun M : ℕ => ∑ j ∈ Finset.range (M + N), gaussPowerTwoSidedDiagonalReal hm k p j)
      atTop atTop := by
    simpa [Nat.add_comm] using hshift
  exact (tendsto_add_atTop_iff_nat N).mp hshift'

/-- All-depth positive Gauss diagonal is not summable. -/
theorem not_summable_gaussPowerTwoSidedDiagonalReal
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ¬ Summable (gaussPowerTwoSidedDiagonalReal hm k p) :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (gaussPowerTwoSidedDiagonalReal_nonneg hm k p)).2
      (tendsto_gaussPowerTwoSidedDiagonal_sum_atTop hm k p)

/-- Every positive critical Gauss power lies outside Schatten class one. -/
theorem gaussQuasiInnerGFull_pow_not_memSchattenClass_one
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ¬ MemSchattenClass 1 (gaussQuasiInnerGFull hm k p ^ m) := by
  intro htrace
  let T := gaussQuasiInnerGFull hm k p ^ m
  have habs : Summable (fun i : ℤ =>
      ‖inner ℂ ((fourierBasis (T := (1 : ℝ))) i)
        (T ((fourierBasis (T := (1 : ℝ))) i))‖) :=
    htrace.one_summable_norm_inner_diag_basis (fourierBasis (T := (1 : ℝ)))
  have hpos := habs.comp_injective (i := fun n : ℕ => ((n : ℤ) + 1))
    (fun a b h => by
      exact Int.ofNat_injective (add_right_cancel h))
  have hneg := habs.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1))
    (fun a b h => by
      exact Int.ofNat_injective (add_right_cancel (neg_injective h)))
  have hmajor : Summable (fun n : ℕ =>
      ‖inner ℂ (fourierLp 2 ((n : ℤ) + 1)) (T (fourierLp 2 ((n : ℤ) + 1)))‖ +
      ‖inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        (T (fourierLp 2 (-((n : ℤ) + 1))))‖) := by
    simpa only [Function.comp_apply, coe_fourierBasis] using hpos.add hneg
  apply not_summable_gaussPowerTwoSidedDiagonalReal hm k p
  apply Summable.of_nonneg_of_le
    (gaussPowerTwoSidedDiagonalReal_nonneg hm k p) (fun n => ?_) hmajor
  have hp := Complex.re_le_norm (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
      (T (fourierLp 2 ((n : ℤ) + 1))))
  have hn := Complex.re_le_norm (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
      (T (fourierLp 2 (-((n : ℤ) + 1)))))
  simpa [gaussPowerTwoSidedDiagonalReal, T] using add_le_add hp hn

/-- Real two-orientation Fourier diagonal of an arbitrary operator on the critical circle. -/
def fourierTwoSidedDiagonalReal
    (T : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (n : ℕ) : ℝ :=
  re (inner ℂ (fourierLp 2 ((n : ℤ) + 1)) (T (fourierLp 2 ((n : ℤ) + 1)))) +
    re (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
      (T (fourierLp 2 (-((n : ℤ) + 1)))))

/-- Schatten-1 membership forces summability of the real two-orientation Fourier diagonal. -/
theorem MemSchattenClass.one_summable_fourierTwoSidedDiagonalReal
    {T : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))}
    (hT : MemSchattenClass 1 T) :
    Summable (fourierTwoSidedDiagonalReal T) := by
  have habs : Summable (fun i : ℤ =>
      ‖inner ℂ ((fourierBasis (T := (1 : ℝ))) i)
        (T ((fourierBasis (T := (1 : ℝ))) i))‖) :=
    hT.one_summable_norm_inner_diag_basis (fourierBasis (T := (1 : ℝ)))
  have hposNorm := habs.comp_injective (i := fun n : ℕ => ((n : ℤ) + 1))
    (fun a b h => by exact Int.ofNat_injective (add_right_cancel h))
  have hnegNorm := habs.comp_injective (i := fun n : ℕ => -((n : ℤ) + 1))
    (fun a b h => by exact Int.ofNat_injective (add_right_cancel (neg_injective h)))
  have hposComplex : Summable (fun n : ℕ =>
      inner ℂ (fourierLp 2 ((n : ℤ) + 1)) (T (fourierLp 2 ((n : ℤ) + 1)))) := by
    apply Summable.of_norm
    simpa [Function.comp_def, coe_fourierBasis] using hposNorm
  have hnegComplex : Summable (fun n : ℕ =>
      inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        (T (fourierLp 2 (-((n : ℤ) + 1))))) := by
    apply Summable.of_norm
    simpa [Function.comp_def, coe_fourierBasis] using hnegNorm
  have hposReal : Summable (fun n : ℕ =>
      re (inner ℂ (fourierLp 2 ((n : ℤ) + 1))
        (T (fourierLp 2 ((n : ℤ) + 1))))) := by
    simpa [Function.comp_def, Complex.reCLM_apply] using
      hposComplex.map Complex.reCLM Complex.continuous_re
  have hnegReal : Summable (fun n : ℕ =>
      re (inner ℂ (fourierLp 2 (-((n : ℤ) + 1)))
        (T (fourierLp 2 (-((n : ℤ) + 1)))))) := by
    simpa [Function.comp_def, Complex.reCLM_apply] using
      hnegComplex.map Complex.reCLM Complex.continuous_re
  exact hposReal.add hnegReal

/-- If a reference differs from the critical Gauss power by Schatten-1, their real two-orientation
Fourier diagonals differ by an absolutely summable sequence. -/
theorem gaussPower_relativeReference_diagonal_summable
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (K : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (hrelative : MemSchattenClass 1 (gaussQuasiInnerGFull hm k p ^ m - K)) :
    Summable (fun n => gaussPowerTwoSidedDiagonalReal hm k p n -
      fourierTwoSidedDiagonalReal K n) := by
  have h := hrelative.one_summable_fourierTwoSidedDiagonalReal
  refine h.congr fun n => ?_
  simp [fourierTwoSidedDiagonalReal, gaussPowerTwoSidedDiagonalReal,
    sub_apply, inner_sub_right]
  ring

/-- Every Schatten-1-relative reference inherits the divergent real critical trace channel. -/
theorem tendsto_gaussPower_relativeReference_diagonal_sum_atTop
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (K : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (hrelative : MemSchattenClass 1 (gaussQuasiInnerGFull hm k p ^ m - K)) :
    Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range M, fourierTwoSidedDiagonalReal K n)
      atTop atTop := by
  let r : ℕ → ℝ := fun n => gaussPowerTwoSidedDiagonalReal hm k p n -
    fourierTwoSidedDiagonalReal K n
  have hr : Summable r := by
    simpa [r] using gaussPower_relativeReference_diagonal_summable hm k p K hrelative
  have hrLim : Tendsto
      (fun M : ℕ => ∑ n ∈ Finset.range M, r n) atTop (nhds (∑' n, r n)) :=
    hr.hasSum.tendsto_sum_nat
  have hG := tendsto_gaussPowerTwoSidedDiagonal_sum_atTop hm k p
  rw [tendsto_atTop]
  intro b
  have hrUpper : ∀ᶠ M : ℕ in atTop,
      (∑ n ∈ Finset.range M, r n) < (∑' n, r n) + 1 :=
    hrLim.eventually (Iio_mem_nhds (lt_add_one (∑' n, r n)))
  have hGLower : ∀ᶠ M : ℕ in atTop,
      b + ((∑' n, r n) + 1) ≤
        ∑ n ∈ Finset.range M, gaussPowerTwoSidedDiagonalReal hm k p n :=
    hG.eventually_ge_atTop (b + ((∑' n, r n) + 1))
  filter_upwards [hrUpper, hGLower] with M hrM hGM
  have hidentity :
      (∑ n ∈ Finset.range M, fourierTwoSidedDiagonalReal K n) =
        (∑ n ∈ Finset.range M, gaussPowerTwoSidedDiagonalReal hm k p n) -
          ∑ n ∈ Finset.range M, r n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp [r]
  rw [hidentity]
  linarith

/-- Any reference with Schatten-1 relative difference must itself carry non-Schatten critical
mass; a trace-class reference cannot renormalize the Gauss power. -/
theorem gaussQuasiInnerGFull_pow_reference_not_memSchattenClass_one_of_relative
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (K : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (hrelative : MemSchattenClass 1 (gaussQuasiInnerGFull hm k p ^ m - K)) :
    ¬ MemSchattenClass 1 K := by
  intro hK
  apply gaussQuasiInnerGFull_pow_not_memSchattenClass_one hm k p
  have hsum := memSchattenClass_one_add
    (hrelative.isCompactOperator one_pos) (hK.isCompactOperator one_pos) hrelative hK
  simpa using hsum

/-- Subtracting a Schatten-1 counterterm never regularizes a positive critical Gauss power. -/
theorem gaussQuasiInnerGFull_pow_sub_not_memSchattenClass_one
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (K : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))))
    (hK : MemSchattenClass 1 K) :
    ¬ MemSchattenClass 1 (gaussQuasiInnerGFull hm k p ^ m - K) := by
  intro hrelative
  exact (gaussQuasiInnerGFull_pow_reference_not_memSchattenClass_one_of_relative
    hm k p K hrelative) hK

end

end RHTower
