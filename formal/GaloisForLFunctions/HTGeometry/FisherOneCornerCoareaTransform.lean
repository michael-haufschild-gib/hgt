import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# One-corner Fisher coarea transform

For a finite height spectrum, one oriented cutoff corner is supported exactly
while an ordered pair of heights straddles the moving cutoff.  Integrating
over the cutoff gives a symmetric pairwise holonomy law.  Laplace transforming
the same interval gives the divided difference of the height semigroup.

Thus hard spectral cuts and soft exponential damping are not separate source
constructions: before scalarization they are two presentations of one
non-diagonal operator field.
-/

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Squared Fisher amplitude attached to an ordered pair of heights. -/
def finiteFisherPairAmplitudeSq {ι : Type*}
    (p h : ι → ℝ) (m : ℝ) (i j : ι) : ℝ :=
  p i * p j * (h i + h j - 2 * m) ^ 2

/-- Energy density of one oriented Fisher cutoff corner.  The strict/weak
endpoint convention is immaterial to the integral but fixes one literal
half-open interval for every ordered pair. -/
def finiteFisherOneCornerCoareaDensity {ι : Type*} [Fintype ι]
    (p h : ι → ℝ) (m u : ℝ) : ℝ :=
  ∑ i, ∑ j,
    if h j < u ∧ u ≤ h i then
      2 * finiteFisherPairAmplitudeSq p h m i j
    else 0

/-- Symmetric signed-holonomy energy of two independent height samples. -/
def finiteFisherSignedHolonomyEnergy {ι : Type*} [Fintype ι]
    (p h : ι → ℝ) (m : ℝ) : ℝ :=
  ∑ i, ∑ j,
    p i * p j * |h i - h j| * (h i + h j - 2 * m) ^ 2

private theorem integrableOn_Ioi_indicator_Ioc_const
    {a b : ℝ} {c : ℝ} :
    IntegrableOn
      (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) (Ioi 0) := by
  rw [show (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) =
      (Ioc a b).indicator (fun _ => c) by
    funext u
    simp [indicator, mem_Ioc]]
  exact ((integrableOn_const (by simp [Real.volume_Ioc]) :
    IntegrableOn (fun _ : ℝ => c) (Ioc a b))).integrable_indicator
      measurableSet_Ioc |>.integrableOn

private theorem integral_Ioi_indicator_Ioc_const
    {a b c : ℝ} (ha : 0 ≤ a) :
    (∫ u : ℝ in Ioi 0, if a < u ∧ u ≤ b then c else 0) =
      c * max (b - a) 0 := by
  rw [show (fun u : ℝ => if a < u ∧ u ≤ b then c else 0) =
      (Ioc a b).indicator (fun _ => c) by
    funext u
    simp [indicator, mem_Ioc]]
  rw [setIntegral_indicator measurableSet_Ioc]
  have hinter : Ioi 0 ∩ Ioc a b = Ioc a b := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun hu => hu.2
    · exact fun hu => ⟨ha.trans_lt hu.1, hu⟩
  rw [hinter, setIntegral_const]
  unfold Measure.real
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal']
  ring

private theorem two_mul_sum_max_fisherPairAmplitudeSq
    {ι : Type*} [Fintype ι] (p h : ι → ℝ) (m : ℝ) :
    2 * (∑ i, ∑ j,
      finiteFisherPairAmplitudeSq p h m i j *
        max (h i - h j) 0) =
      finiteFisherSignedHolonomyEnergy p h m := by
  have hswap :
      (∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          max (h j - h i) 0) =
        ∑ i, ∑ j,
          finiteFisherPairAmplitudeSq p h m i j *
            max (h i - h j) 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [finiteFisherPairAmplitudeSq]
    ring
  calc
    2 * (∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          max (h i - h j) 0) =
      (∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          max (h i - h j) 0) +
      ∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          max (h i - h j) 0 := by ring
    _ = (∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          max (h i - h j) 0) +
      ∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          max (h j - h i) 0 := by rw [hswap]
    _ = ∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          (max (h i - h j) 0 + max (h j - h i) 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = finiteFisherSignedHolonomyEnergy p h m := by
      unfold finiteFisherSignedHolonomyEnergy
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have habs :
          max (h i - h j) 0 + max (h j - h i) 0 =
            |h i - h j| := by
        rcases le_total (h i) (h j) with hij | hji
        · rw [max_eq_right (sub_nonpos.mpr hij),
            max_eq_left (sub_nonneg.mpr hij),
            abs_of_nonpos (sub_nonpos.mpr hij)]
          ring
        · rw [max_eq_left (sub_nonneg.mpr hji),
            max_eq_right (sub_nonpos.mpr hji),
            abs_of_nonneg (sub_nonneg.mpr hji)]
          ring
      rw [finiteFisherPairAmplitudeSq, habs]
      ring

/-- **Fisher one-corner coarea law.**  The total Hilbert--Schmidt energy of
one oriented cutoff corner is exactly the signed pairwise height holonomy.
No probability normalization is required for the algebraic identity. -/
theorem integral_finiteFisherOneCornerCoareaDensity
    {ι : Type*} [Fintype ι] {p h : ι → ℝ} {m : ℝ}
    (hh : ∀ i, 0 ≤ h i) :
    (∫ u : ℝ in Ioi 0,
      finiteFisherOneCornerCoareaDensity p h m u) =
        finiteFisherSignedHolonomyEnergy p h m := by
  have hIntegral :
      (∫ u : ℝ in Ioi 0,
        finiteFisherOneCornerCoareaDensity p h m u) =
          ∑ i, ∑ j,
            2 * finiteFisherPairAmplitudeSq p h m i j *
              max (h i - h j) 0 := by
    unfold finiteFisherOneCornerCoareaDensity
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_Ioi_indicator_Ioc_const (hh j)]
      · intro j _
        exact integrableOn_Ioi_indicator_Ioc_const
    · intro i _
      exact integrable_finsetSum Finset.univ (fun _ _ =>
        integrableOn_Ioi_indicator_Ioc_const)
  rw [hIntegral]
  rw [show
      (∑ i, ∑ j,
        2 * finiteFisherPairAmplitudeSq p h m i j *
          max (h i - h j) 0) =
      2 * (∑ i, ∑ j,
        finiteFisherPairAmplitudeSq p h m i j *
          max (h i - h j) 0) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring]
  exact two_mul_sum_max_fisherPairAmplitudeSq p h m

/-- Laplace transform of one oriented height interval, with a scalar kernel
coefficient retained. -/
def orientedCutoffLaplaceCoefficient
    (a b : ℝ) (k w : ℂ) : ℂ :=
  if a ≤ b then
    ∫ u : ℝ in a..b, Complex.exp (-w * (u : ℂ)) * k
  else 0

/-- Divided-difference presentation of the same oriented interval. -/
def semigroupDividedDifferenceCoefficient
    (a b : ℝ) (k w : ℂ) : ℂ :=
  if a ≤ b then
    k * (Complex.exp (-w * (a : ℂ)) -
      Complex.exp (-w * (b : ℂ))) / w
  else 0

/-- **Hard-cut/soft-shift identity.**  Laplace transforming one oriented
cutoff interval gives exactly the divided difference of the exponential
height semigroup. -/
theorem orientedCutoffLaplaceCoefficient_eq_dividedDifference
    {a b : ℝ} {k w : ℂ} (hw : w ≠ 0) :
    orientedCutoffLaplaceCoefficient a b k w =
      semigroupDividedDifferenceCoefficient a b k w := by
  by_cases hab : a ≤ b
  · rw [orientedCutoffLaplaceCoefficient,
      semigroupDividedDifferenceCoefficient, if_pos hab, if_pos hab,
      intervalIntegral.integral_mul_const,
      integral_exp_mul_complex (neg_ne_zero.mpr hw)]
    ring
  · rw [orientedCutoffLaplaceCoefficient,
      semigroupDividedDifferenceCoefficient, if_neg hab, if_neg hab]

/-- Matrix-kernel form: the Laplace transform of every lower cutoff
coefficient is the oriented semigroup divided difference, entry by entry. -/
theorem orientedCutoffLaplaceKernel_eq_dividedDifference
    {ι : Type*} (h : ι → ℝ) (K : ι → ι → ℂ)
    {w : ℂ} (hw : w ≠ 0) (i j : ι) :
    orientedCutoffLaplaceCoefficient (h j) (h i) (K i j) w =
      semigroupDividedDifferenceCoefficient
        (h j) (h i) (K i j) w :=
  orientedCutoffLaplaceCoefficient_eq_dividedDifference hw

end GaloisForLFunctions.HTGeometry
