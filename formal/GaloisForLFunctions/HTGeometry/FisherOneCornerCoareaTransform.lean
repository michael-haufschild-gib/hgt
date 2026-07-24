import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L2Space
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
open scoped BigOperators ComplexOrder

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

/-! ## Exact four-unit Laplace completion -/

/-- Augment an arbitrary finite Hilbert Gram by one represented boundary
column and the fixed diagonal budget four. -/
def finiteFourUnitBoundaryGram
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (feature : Fin n → H) (source : H) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.fromBlocks
    (Matrix.gram ℂ feature)
    (fun i _ => inner ℂ (feature i) source)
    (fun _ j => star (inner ℂ (feature j) source))
    (Matrix.of fun _ _ : Unit => (4 : ℂ))

/-- **Four-unit represented-column law.**  Every Hilbert source of squared
norm at most four gives a positive augmented Gram.  The proof realizes the
unused budget as one orthogonal slack coordinate, so no invertibility or
finite-rank hypothesis is hidden in the statement. -/
theorem finiteFourUnitBoundaryGram_posSemidef_of_norm_sq_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {n : ℕ} (feature : Fin n → H) (source : H)
    (hsource : ‖source‖ ^ 2 ≤ 4) :
    (finiteFourUnitBoundaryGram feature source).PosSemidef := by
  let slack : ℝ := Real.sqrt (4 - ‖source‖ ^ 2)
  let augmentedFeature :
      (Fin n ⊕ Unit) → WithLp 2 (H × ℂ)
    | Sum.inl i => WithLp.toLp 2 (feature i, 0)
    | Sum.inr _ => WithLp.toLp 2 (source, (slack : ℂ))
  have hslackNonneg : 0 ≤ 4 - ‖source‖ ^ 2 :=
    sub_nonneg.mpr hsource
  have hslack : slack ^ 2 = 4 - ‖source‖ ^ 2 := by
    dsimp only [slack]
    exact Real.sq_sqrt hslackNonneg
  have hgram :
      Matrix.gram ℂ augmentedFeature =
        finiteFourUnitBoundaryGram feature source := by
    ext a b
    rcases a with i | u <;> rcases b with j | z
    · simp [augmentedFeature, finiteFourUnitBoundaryGram, Matrix.gram_apply]
    · simp [augmentedFeature, finiteFourUnitBoundaryGram, Matrix.gram_apply]
    · simp [augmentedFeature, finiteFourUnitBoundaryGram, Matrix.gram_apply,
        inner_conj_symm]
    · have huz : u = z := Subsingleton.elim _ _
      subst z
      simp only [Matrix.gram_apply, augmentedFeature,
        finiteFourUnitBoundaryGram, Matrix.fromBlocks_apply₂₂,
        Matrix.of_apply]
      rw [WithLp.prod_inner_apply, inner_self_eq_norm_sq_to_K]
      simp only [RCLike.inner_apply, conj_ofReal]
      calc
        (‖source‖ : ℂ) ^ 2 +
              (slack : ℂ) * (slack : ℂ) =
            ((‖source‖ ^ 2 + slack ^ 2 : ℝ) : ℂ) := by
              push_cast
              ring
        _ = (4 : ℂ) := by
          rw [hslack]
          push_cast
          ring
  rw [← hgram]
  exact Matrix.posSemidef_gram ℂ augmentedFeature

/-- Lebesgue measure on the positive half-line, used as the native Hardy
source carrier. -/
def halfLineLaplaceMeasure : Measure ℝ :=
  volume.restrict (Ioi 0)

/-- Raw conjugate exponential feature whose Hilbert Gram is the
right-half-plane Cauchy kernel. -/
def halfLineLaplaceFeatureRaw (w : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(star w) * (u : ℂ))

theorem halfLineLaplaceFeatureRaw_memLp
    {w : ℂ} (hw : 0 < w.re) :
    MemLp (halfLineLaplaceFeatureRaw w) 2
      halfLineLaplaceMeasure := by
  have hmeas :
      AEStronglyMeasurable (halfLineLaplaceFeatureRaw w)
        halfLineLaplaceMeasure :=
    (by
      unfold halfLineLaplaceFeatureRaw
      fun_prop : Continuous (halfLineLaplaceFeatureRaw w))
      |>.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hint :
      IntegrableOn
        (fun u : ℝ => Real.exp ((-2 * w.re) * u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [halfLineLaplaceFeatureRaw, norm_exp, neg_re, mul_re,
    RCLike.star_def, Complex.conj_re, ofReal_re, ofReal_im, mul_zero,
    sub_zero]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Normalized Hilbert feature at a right-half-plane Cauchy node. -/
def halfLineLaplaceFeature (w : ℂ) (hw : 0 < w.re) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  (halfLineLaplaceFeatureRaw_memLp hw).toLp
    (halfLineLaplaceFeatureRaw w)

/-- Exact Cauchy Gram of the half-line Laplace features. -/
theorem inner_halfLineLaplaceFeature
    {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    inner ℂ (halfLineLaplaceFeature w hw)
        (halfLineLaplaceFeature z hz) =
      1 / (w + star z) := by
  rw [L2.inner_def]
  change
    (∫ u : ℝ,
      inner ℂ (halfLineLaplaceFeature w hw u)
        (halfLineLaplaceFeature z hz u)
      ∂halfLineLaplaceMeasure) = _
  have hwmem := halfLineLaplaceFeatureRaw_memLp hw
  have hzmem := halfLineLaplaceFeatureRaw_memLp hz
  rw [MeasureTheory.integral_congr_ae
    (show
      (fun u : ℝ =>
        inner ℂ (halfLineLaplaceFeature w hw u)
          (halfLineLaplaceFeature z hz u)) =ᵐ[halfLineLaplaceMeasure]
        fun u => Complex.exp (-(w + star z) * (u : ℂ)) by
      filter_upwards [hwmem.coeFn_toLp, hzmem.coeFn_toLp] with u hwu hzu
      simp only [halfLineLaplaceFeature] at hwu hzu ⊢
      rw [hwu, hzu]
      simp only [halfLineLaplaceFeatureRaw, RCLike.inner_apply]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_neg, map_mul, RCLike.star_def,
        Complex.conj_conj, Complex.conj_ofReal]
      ring)]
  change
    (∫ u : ℝ in Ioi 0,
      Complex.exp (-(w + star z) * (u : ℂ))) = _
  rw [integral_exp_mul_complex_Ioi
    (a := -(w + star z)) (by
      simp only [neg_re, add_re, RCLike.star_def, Complex.conj_re]
      linarith) 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, neg_div]
  simp [neg_inv]

/-- Half-line Laplace transform of an actual `L²` source, defined as its
evaluation against the Cauchy feature. -/
def halfLineLaplaceTransform
    (source : Lp ℂ 2 halfLineLaplaceMeasure)
    (w : ℂ) (hw : 0 < w.re) : ℂ :=
  inner ℂ (halfLineLaplaceFeature w hw) source

/-- Integral presentation of the represented Laplace column. -/
theorem halfLineLaplaceTransform_eq_integral
    (source : Lp ℂ 2 halfLineLaplaceMeasure)
    (w : ℂ) (hw : 0 < w.re) :
    halfLineLaplaceTransform source w hw =
      ∫ u : ℝ, Complex.exp (-w * (u : ℂ)) * source u
        ∂halfLineLaplaceMeasure := by
  rw [halfLineLaplaceTransform, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  have hwmem := halfLineLaplaceFeatureRaw_memLp hw
  filter_upwards [hwmem.coeFn_toLp] with u hwu
  simp only [halfLineLaplaceFeature] at hwu ⊢
  rw [hwu]
  simp only [halfLineLaplaceFeatureRaw, RCLike.inner_apply]
  rw [← Complex.exp_conj]
  simp only [map_neg, map_mul, RCLike.star_def,
    Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- Augmented Cauchy Gram generated by one concrete half-line source. -/
def halfLineLaplaceFourUnitBoundaryGram
    {n : ℕ} (node : Fin n → ℂ)
    (hnode : ∀ i, 0 < (node i).re)
    (source : Lp ℂ 2 halfLineLaplaceMeasure) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  finiteFourUnitBoundaryGram
    (fun i => halfLineLaplaceFeature (node i) (hnode i)) source

/-- **Universal four-unit Laplace boundary law.**  Squared source energy at
most four implies positivity of every finite augmented Cauchy packet.  This
is exactly the operator inequality needed after a source incidence identifies
the represented Laplace column with the continued Xi Ward column. -/
theorem halfLineLaplaceFourUnitBoundaryGram_posSemidef
    {n : ℕ} (node : Fin n → ℂ)
    (hnode : ∀ i, 0 < (node i).re)
    (source : Lp ℂ 2 halfLineLaplaceMeasure)
    (hsource : ‖source‖ ^ 2 ≤ 4) :
    (halfLineLaplaceFourUnitBoundaryGram
      node hnode source).PosSemidef :=
  finiteFourUnitBoundaryGram_posSemidef_of_norm_sq_le
    (fun i => halfLineLaplaceFeature (node i) (hnode i))
    source hsource

theorem halfLineLaplaceFourUnitBoundaryGram_topLeft
    {n : ℕ} (node : Fin n → ℂ)
    (hnode : ∀ i, 0 < (node i).re)
    (source : Lp ℂ 2 halfLineLaplaceMeasure) (i j : Fin n) :
    halfLineLaplaceFourUnitBoundaryGram node hnode source
        (Sum.inl i) (Sum.inl j) =
      1 / (node i + star (node j)) := by
  rw [halfLineLaplaceFourUnitBoundaryGram, finiteFourUnitBoundaryGram,
    Matrix.fromBlocks_apply₁₁, Matrix.gram_apply,
    inner_halfLineLaplaceFeature]

theorem halfLineLaplaceFourUnitBoundaryGram_boundaryColumn
    {n : ℕ} (node : Fin n → ℂ)
    (hnode : ∀ i, 0 < (node i).re)
    (source : Lp ℂ 2 halfLineLaplaceMeasure) (i : Fin n) :
    halfLineLaplaceFourUnitBoundaryGram node hnode source
        (Sum.inl i) (Sum.inr ()) =
      halfLineLaplaceTransform source (node i) (hnode i) :=
  rfl

end GaloisForLFunctions.HTGeometry
