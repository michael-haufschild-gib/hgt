import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# Xi polarization does not remove its irregular type

The prime-Wold Gamma gauge is the restriction of `exp (2 t x)` to the canonical inverse boundary
scales.  This file classifies the full continuous formal type before that sparse restriction.

For a nonzero centered parameter, fixed-source unitarity at every inverse scale and persistent
failure of a finite boundary limit are equivalent to anti-Hermiticity `Re t = 0`.  The failure of a
limit is witnessed constructively by two cofinal scale sequences on which the same gauge is
identically `1` and `-1`.

Applied to a Xi divisor copy, this says critical-line placement polarizes the irregular type; it
does not make the type regular or remove its essential oscillation.  No claim is made that either
explicit cofinal sequence is a canonical prime-boundary subsequence.
-/

open scoped Topology
open Filter Complex
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Full inverse-boundary formal type whose prime-Wold samples are the arithmetic irregular
Gamma gauge. -/
def continuousIrregularGauge (t : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (2 * t * (x : ℂ))

@[simp]
theorem primeWoldIrregularGauge_eq_continuousIrregularGauge (t : ℂ) (N : ℕ) :
    primeWoldIrregularGauge t N =
      continuousIrregularGauge t (primeWoldBoundaryScale N) := rfl

/-- Cofinal scales on which a nonzero imaginary formal type completes integral turns. -/
def irregularUnitSample (gamma : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (n + 1) / |gamma|

/-- Cofinal scales on which a nonzero imaginary formal type completes half-integral turns. -/
def irregularAntipodalSample (gamma : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (2 * n + 1) / (2 * |gamma|)

theorem continuousIrregularGauge_unitSample_of_pos {gamma : ℝ} (hgamma : 0 < gamma)
    (n : ℕ) :
    continuousIrregularGauge (gamma * I) (irregularUnitSample gamma n) = 1 := by
  rw [continuousIrregularGauge]
  have harg :
      (2 : ℂ) * ((gamma : ℂ) * I) *
          (irregularUnitSample gamma n : ℂ) =
        (((n + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
    rw [irregularUnitSample, abs_of_pos hgamma]
    push_cast
    field_simp [ne_of_gt hgamma]
  rw [harg]
  exact Complex.exp_nat_mul_two_pi_mul_I (n + 1)

theorem continuousIrregularGauge_antipodalSample_of_pos {gamma : ℝ} (hgamma : 0 < gamma)
    (n : ℕ) :
    continuousIrregularGauge (gamma * I) (irregularAntipodalSample gamma n) = -1 := by
  rw [continuousIrregularGauge]
  have harg :
      (2 : ℂ) * ((gamma : ℂ) * I) *
          (irregularAntipodalSample gamma n : ℂ) =
        (Real.pi : ℂ) * I +
          (((n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
    rw [irregularAntipodalSample, abs_of_pos hgamma]
    push_cast
    field_simp [ne_of_gt hgamma]
    ring
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I,
    Complex.exp_nat_mul_two_pi_mul_I]
  ring

theorem continuousIrregularGauge_unitSample_of_neg {gamma : ℝ} (hgamma : gamma < 0)
    (n : ℕ) :
    continuousIrregularGauge (gamma * I) (irregularUnitSample gamma n) = 1 := by
  rw [continuousIrregularGauge]
  have harg :
      (2 : ℂ) * ((gamma : ℂ) * I) *
          (irregularUnitSample gamma n : ℂ) =
        -(((n + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
    rw [irregularUnitSample, abs_of_neg hgamma]
    push_cast
    field_simp [ne_of_lt hgamma]
  rw [harg, Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I]
  norm_num

theorem continuousIrregularGauge_antipodalSample_of_neg {gamma : ℝ} (hgamma : gamma < 0)
    (n : ℕ) :
    continuousIrregularGauge (gamma * I) (irregularAntipodalSample gamma n) = -1 := by
  rw [continuousIrregularGauge]
  have harg :
      (2 : ℂ) * ((gamma : ℂ) * I) *
          (irregularAntipodalSample gamma n : ℂ) =
        -((Real.pi : ℂ) * I +
          (((n : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * I))) := by
    rw [irregularAntipodalSample, abs_of_neg hgamma]
    push_cast
    field_simp [ne_of_lt hgamma]
    ring
  rw [harg, Complex.exp_neg, Complex.exp_add, Complex.exp_pi_mul_I,
    Complex.exp_nat_mul_two_pi_mul_I]
  norm_num

theorem tendsto_irregularUnitSample_atTop {gamma : ℝ} (hgamma : gamma ≠ 0) :
    Tendsto (irregularUnitSample gamma) atTop atTop := by
  have hc : 0 < Real.pi / |gamma| := div_pos Real.pi_pos (abs_pos.mpr hgamma)
  have hbase : Tendsto (fun n : ℕ => (Real.pi / |gamma|) * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
  apply Filter.tendsto_atTop_mono (fun n => ?_) hbase
  rw [irregularUnitSample]
  calc
    Real.pi / |gamma| * (n : ℝ) ≤
        Real.pi / |gamma| * ((n : ℝ) + 1) := by
      gcongr
      linarith
    _ = Real.pi * ((n : ℝ) + 1) / |gamma| := by ring

theorem tendsto_irregularAntipodalSample_atTop {gamma : ℝ} (hgamma : gamma ≠ 0) :
    Tendsto (irregularAntipodalSample gamma) atTop atTop := by
  have hc : 0 < Real.pi / |gamma| := div_pos Real.pi_pos (abs_pos.mpr hgamma)
  have hbase : Tendsto (fun n : ℕ => (Real.pi / |gamma|) * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
  apply Filter.tendsto_atTop_mono (fun n => ?_) hbase
  rw [irregularAntipodalSample]
  calc
    Real.pi / |gamma| * (n : ℝ) ≤
        Real.pi / |gamma| * ((n : ℝ) + 1 / 2) := by
      gcongr
      norm_num
    _ = Real.pi * (2 * (n : ℝ) + 1) / (2 * |gamma|) := by
      field_simp [hgamma]

/-- Every nonzero imaginary formal type has two distinct cofinal cluster values, so it admits no
finite limit at the inverse boundary. -/
theorem not_tendsto_continuousIrregularGauge_atTop_of_imaginary
    {gamma : ℝ} (hgamma : gamma ≠ 0) (z : ℂ) :
    ¬ Tendsto (continuousIrregularGauge (gamma * I)) atTop (𝓝 z) := by
  intro hlimit
  have hunit := hlimit.comp (tendsto_irregularUnitSample_atTop hgamma)
  have hantipodal := hlimit.comp (tendsto_irregularAntipodalSample_atTop hgamma)
  rcases lt_or_gt_of_ne hgamma with hneg | hpos
  · have hunit' : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 z) := by
      convert hunit using 1
      funext n
      exact (continuousIrregularGauge_unitSample_of_neg hneg n).symm
    have hantipodal' : Tendsto (fun _ : ℕ => (-1 : ℂ)) atTop (𝓝 z) := by
      convert hantipodal using 1
      funext n
      exact (continuousIrregularGauge_antipodalSample_of_neg hneg n).symm
    have hone : (1 : ℂ) = z := tendsto_nhds_unique tendsto_const_nhds hunit'
    have hnegone : (-1 : ℂ) = z := tendsto_nhds_unique tendsto_const_nhds hantipodal'
    have : (1 : ℂ) = -1 := hone.trans hnegone.symm
    norm_num at this
  · have hunit' : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 z) := by
      convert hunit using 1
      funext n
      exact (continuousIrregularGauge_unitSample_of_pos hpos n).symm
    have hantipodal' : Tendsto (fun _ : ℕ => (-1 : ℂ)) atTop (𝓝 z) := by
      convert hantipodal using 1
      funext n
      exact (continuousIrregularGauge_antipodalSample_of_pos hpos n).symm
    have hone : (1 : ℂ) = z := tendsto_nhds_unique tendsto_const_nhds hunit'
    have hnegone : (-1 : ℂ) = z := tendsto_nhds_unique tendsto_const_nhds hantipodal'
    have : (1 : ℂ) = -1 := hone.trans hnegone.symm
    norm_num at this

theorem norm_continuousIrregularGauge_eq_one_of_re_eq_zero
    {t : ℂ} (ht : t.re = 0) (x : ℝ) :
    ‖continuousIrregularGauge t x‖ = 1 := by
  rw [continuousIrregularGauge, Complex.norm_exp]
  simp [Complex.mul_re, ht]

theorem not_tendsto_continuousIrregularGauge_atTop_of_re_eq_zero
    {t : ℂ} (hre : t.re = 0) (ht : t ≠ 0) (z : ℂ) :
    ¬ Tendsto (continuousIrregularGauge t) atTop (𝓝 z) := by
  have him : t.im ≠ 0 := by
    intro him
    apply ht
    apply Complex.ext <;> simp [hre, him]
  have htImaginary : t = (t.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [htImaginary]
  exact not_tendsto_continuousIrregularGauge_atTop_of_imaginary him z

/-- A nonzero formal type is source-polarized when its irregular gauge is unitary at every
inverse boundary scale but retains no finite boundary limit. -/
def SourcePolarizedIrregularType (t : ℂ) : Prop :=
  (∀ x : ℝ, ‖continuousIrregularGauge t x‖ = 1) ∧
    ∀ z : ℂ, ¬ Tendsto (continuousIrregularGauge t) atTop (𝓝 z)

/-- Polarized irregularity is exactly an anti-Hermitian, rather than vanishing, formal type. -/
theorem sourcePolarizedIrregularType_iff {t : ℂ} (ht : t ≠ 0) :
    SourcePolarizedIrregularType t ↔ t.re = 0 := by
  constructor
  · rintro ⟨hnorm, _⟩
    have h := hnorm 1
    rw [continuousIrregularGauge, Complex.norm_exp] at h
    have hre : (2 * t * (1 : ℂ)).re = 0 := (Real.exp_eq_one_iff _).mp h
    simpa [Complex.mul_re] using hre
  · intro hre
    exact ⟨norm_continuousIrregularGauge_eq_one_of_re_eq_zero hre,
      not_tendsto_continuousIrregularGauge_atTop_of_re_eq_zero hre ht⟩

/-- Centered irregular formal type carried by one multiplicity-exact Xi divisor copy. -/
def xiCenteredIrregularType (q : XiZeroCopy) : ℂ :=
  (q.1 : ℂ) - 1 / 2

theorem xiCenteredIrregularType_ne_zero (q : XiZeroCopy) :
    xiCenteredIrregularType q ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  exact xiSupport_im_ne_zero q.1 (by
    simpa [xiCenteredIrregularType] using him)

/-- Actual Xi formal type is source-polarized precisely on the critical line. Polarization does
not regularize it: `SourcePolarizedIrregularType` includes failure of every finite boundary limit. -/
theorem xiCenteredIrregularType_sourcePolarized_iff (q : XiZeroCopy) :
    SourcePolarizedIrregularType (xiCenteredIrregularType q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourcePolarizedIrregularType_iff (xiCenteredIrregularType_ne_zero q)]
  simp only [xiCenteredIrregularType, Complex.sub_re]
  norm_num
  constructor <;> intro h <;> linarith

end

end RHTower
