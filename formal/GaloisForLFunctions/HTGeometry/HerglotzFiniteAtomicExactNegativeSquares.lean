import GaloisForLFunctions.HTGeometry.HerglotzFiniteAtomicGaugeSlice
import GaloisForLFunctions.HTGeometry.PoleLocalizedExactNegativeSquares

/-!
# Global exact negative squares for finite-atomic Herglotz chambers

The earlier chamber modules control the pole-localized packet used for the lower bound.  This
module closes the full Krein-index statement: every finite upper-half-plane Pick packet has
negative inertia at most the number of negative atoms, and one injective packet attains that bound.
It then combines exact negative squares with rational-gauge field, matroid, independence, and
pointed-class invariance.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory Matrix Finset Set
open scoped Classical ComplexOrder Differential

noncomputable section

local instance exactSquaresDomain :
    IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance exactSquaresComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance exactSquaresCharZero :
    CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance exactSquaresDifferential :
    Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance exactSquaresCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _
    upperEndRationalCoordinateField_derivationClosed

local instance exactSquaresCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField
      upperEndMeroField :=
  ⟨fun x => derivationClosedDifferential_apply
    upperEndRationalCoordinateField
    upperEndRationalCoordinateField_derivationClosed x⟩

/-- At most `k` negative squares on every finite upper-half-plane packet. -/
def CarrierHasAtMostNegativeSquares (f : ℂ → ℂ) (k : ℕ) : Prop :=
  ∀ {N : ℕ} (z : Fin N → ℂ),
    (∀ j, 0 < (z j).im) →
    ∀ W : Submodule ℂ (Fin N → ℂ),
      (∀ x ∈ W, x ≠ 0 →
        (star x ⬝ᵥ (carrierPickMatrix f z).mulVec x).re < 0) →
      Module.finrank ℂ W ≤ k

/-- Exactly `k` negative squares: a universal upper bound and an attained finite witness. -/
def CarrierHasExactlyNegativeSquares (f : ℂ → ℂ) (k : ℕ) : Prop :=
  CarrierHasAtMostNegativeSquares f k ∧
    ∃ (N : ℕ) (z : Fin N → ℂ)
      (W : Submodule ℂ (Fin N → ℂ)),
      (∀ j, 0 < (z j).im) ∧
      Function.Injective z ∧
      Module.finrank ℂ W = k ∧
      ∀ x ∈ W, x ≠ 0 →
        (star x ⬝ᵥ (carrierPickMatrix f z).mulVec x).re < 0

theorem upper_sub_star_ne_zero {z w : ℂ}
    (hz : 0 < z.im) (hw : 0 < w.im) : z - star w ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im,
    Complex.zero_im, sub_neg_eq_add] at him
  linarith

def upperCauchyFeature {N : ℕ} (z : Fin N → ℂ)
    (j : Fin N) (t : ℝ) : ℂ :=
  ((t : ℂ) - z j)⁻¹

def upperMeasureGram {N : ℕ} (ν : Measure ℝ)
    (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  complexFeatureGram ν (upperCauchyFeature z)

theorem integrable_upperCauchyFeature_mul_star
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    {N : ℕ} (z : Fin N → ℂ) (hz : ∀ j, 0 < (z j).im)
    (j l : Fin N) :
    Integrable (fun t => upperCauchyFeature z j t *
      star (upperCauchyFeature z l t)) ν := by
  have hj := integrable_regularizedHerglotzKernel_of_nevanlinna
    ν hH0 (ne_of_gt (hz j))
  have hl := integrable_regularizedHerglotzKernel_of_nevanlinna
    ν hH0 (ne_of_gt (hz l))
  have hdiff : Integrable (fun t =>
      regularizedHerglotzKernel t (z j) -
        star (regularizedHerglotzKernel t (z l))) ν :=
    hj.sub (integrable_conj hl)
  have hden : z j - star (z l) ≠ 0 :=
    upper_sub_star_ne_zero (hz j) (hz l)
  have hden' : z j - (starRingEnd ℂ) (z l) ≠ 0 := by
    simpa only [RCLike.star_def] using hden
  refine (hdiff.div_const (z j - star (z l))).congr
    (Filter.Eventually.of_forall fun t => ?_)
  change
    (regularizedHerglotzKernel t (z j) -
        (starRingEnd ℂ) (regularizedHerglotzKernel t (z l))) /
        (z j - (starRingEnd ℂ) (z l)) =
      upperCauchyFeature z j t *
        star (upperCauchyFeature z l t)
  rw [regularizedHerglotzKernel_sub_conj
    (ne_of_gt (hz j)) (ne_of_gt (hz l)),
    mul_div_cancel_left₀ _ hden']
  simp only [upperCauchyFeature, RCLike.star_def, map_inv₀,
    map_sub, Complex.conj_ofReal]

theorem carrierPickMatrix_regularizedHerglotz_eq_upperMeasureGram
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    {N : ℕ} (z : Fin N → ℂ) (hz : ∀ j, 0 < (z j).im) :
    carrierPickMatrix
        (fun w => ∫ t, regularizedHerglotzKernel t w ∂ν) z =
      upperMeasureGram ν z := by
  ext j l
  rw [carrierPickMatrix, Matrix.of_apply, upperMeasureGram,
    complexFeatureGram]
  have hj := integrable_regularizedHerglotzKernel_of_nevanlinna
    ν hH0 (ne_of_gt (hz j))
  have hl := integrable_regularizedHerglotzKernel_of_nevanlinna
    ν hH0 (ne_of_gt (hz l))
  have hden : z j - star (z l) ≠ 0 :=
    upper_sub_star_ne_zero (hz j) (hz l)
  rw [div_eq_iff hden]
  have hmeas :
      (∫ t, regularizedHerglotzKernel t (z j) ∂ν) -
          (starRingEnd ℂ)
            (∫ t, regularizedHerglotzKernel t (z l) ∂ν) =
        (z j - star (z l)) *
          ∫ t, upperCauchyFeature z j t *
            star (upperCauchyFeature z l t) ∂ν := by
    rw [← integral_conj,
      ← integral_sub hj (integrable_conj hl),
      ← integral_const_mul]
    refine integral_congr_ae
      (Filter.Eventually.of_forall fun t => ?_)
    simpa only [upperCauchyFeature, RCLike.star_def, map_inv₀,
      map_sub, Complex.conj_ofReal] using
      regularizedHerglotzKernel_sub_conj
        (ne_of_gt (hz j)) (ne_of_gt (hz l)) t
  change
    (∫ t, regularizedHerglotzKernel t (z j) ∂ν) -
        (starRingEnd ℂ)
          (∫ t, regularizedHerglotzKernel t (z l) ∂ν) = _
  rw [hmeas]
  simp only [RCLike.star_def]
  ring

theorem upperMeasureGram_posSemidef
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    {N : ℕ} (z : Fin N → ℂ) (hz : ∀ j, 0 < (z j).im) :
    (upperMeasureGram ν z).PosSemidef :=
  complexFeatureGram_posSemidef ν (upperCauchyFeature z)
    (integrable_upperCauchyFeature_mul_star ν hH0 z hz)

def upperFiniteAtomFeature {d N : ℕ} (a : Fin d → ℝ)
    (z : Fin N → ℂ) (j : Fin d) (l : Fin N) : ℂ :=
  ((a j : ℂ) - z l)⁻¹

def upperSignedAtomGram {d N : ℕ} (a c : Fin d → ℝ)
    (z : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun l m => ∑ j, (c j : ℂ) *
    (upperFiniteAtomFeature a z j l *
      star (upperFiniteAtomFeature a z j m))

theorem carrierPickMatrix_atomPart_eq_upperSignedAtomGram
    {d N : ℕ} (a c : Fin d → ℝ)
    (z : Fin N → ℂ) (hz : ∀ j, 0 < (z j).im) :
    carrierPickMatrix (atomPart a c) z =
      upperSignedAtomGram a c z := by
  ext l m
  rw [carrierPickMatrix, Matrix.of_apply, upperSignedAtomGram,
    Matrix.of_apply]
  have hden : z l - star (z m) ≠ 0 :=
    upper_sub_star_ne_zero (hz l) (hz m)
  rw [div_eq_iff hden]
  change atomPart a c (z l) -
      (starRingEnd ℂ) (atomPart a c (z m)) = _
  rw [atomPart_sub_conj a c
    (ne_of_gt (hz l)) (ne_of_gt (hz m))]
  simp only [RCLike.star_def]
  rw [mul_comm
    (∑ j, (c j : ℂ) *
      (upperFiniteAtomFeature a z j l *
        (starRingEnd ℂ) (upperFiniteAtomFeature a z j m)))
    (z l - (starRingEnd ℂ) (z m))]
  congr 1
  simp only [upperFiniteAtomFeature, map_inv₀,
    map_sub, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro j hj
  have hal : (a j : ℂ) - z l ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub,
      Complex.zero_im] at him
    linarith [hz l]
  have ham : (a j : ℂ) - star (z m) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.star_def,
      Complex.conj_im, zero_sub, neg_neg, Complex.zero_im] at him
    linarith [hz m]
  field_simp [hal, ham]

def upperNegAtomWitness {d N : ℕ} (a c : Fin d → ℝ)
    (z : Fin N → ℂ) (i : Fin (negCount c)) (l : Fin N) : ℂ :=
  (Real.sqrt (-(c (negIndex c i))) : ℂ) *
    upperFiniteAtomFeature a z (negIndex c i) l

theorem upperNegAtomWitness_mul_star {d N : ℕ}
    (a c : Fin d → ℝ) (z : Fin N → ℂ)
    (i : Fin (negCount c)) (l m : Fin N) :
    upperNegAtomWitness a c z i l *
        star (upperNegAtomWitness a c z i m) =
      ((-(c (negIndex c i)) : ℝ) : ℂ) *
        (upperFiniteAtomFeature a z (negIndex c i) l *
          star (upperFiniteAtomFeature a z (negIndex c i) m)) := by
  have hnn : (0 : ℝ) ≤ -(c (negIndex c i)) := by
    linarith [c_negIndex_neg c i]
  have hsq := Real.mul_self_sqrt hnn
  rw [upperNegAtomWitness, upperNegAtomWitness,
    RCLike.star_def, map_mul, Complex.conj_ofReal]
  rw [show ((-(c (negIndex c i)) : ℝ) : ℂ) =
      ((Real.sqrt (-(c (negIndex c i))) : ℝ) : ℂ) *
        ((Real.sqrt (-(c (negIndex c i))) : ℝ) : ℂ) by
    rw [← Complex.ofReal_mul, hsq]]
  ring

theorem upperSignedAtomGram_add_negWitness {d N : ℕ}
    (a c : Fin d → ℝ) (z : Fin N → ℂ) :
    upperSignedAtomGram a c z +
        (∑ i, Matrix.of fun l m =>
          upperNegAtomWitness a c z i l *
            star (upperNegAtomWitness a c z i m)) =
      (Matrix.of fun l m => ∑ j, ((max (c j) 0 : ℝ) : ℂ) *
        (upperFiniteAtomFeature a z j l *
          star (upperFiniteAtomFeature a z j m))) := by
  ext l m
  simp only [Matrix.add_apply, upperSignedAtomGram, Matrix.of_apply,
    Matrix.sum_apply]
  have hcorr :
      (∑ i, upperNegAtomWitness a c z i l *
          star (upperNegAtomWitness a c z i m)) =
        ∑ j ∈ negIndices c, ((-(c j) : ℝ) : ℂ) *
          (upperFiniteAtomFeature a z j l *
            star (upperFiniteAtomFeature a z j m)) := by
    have hterm : ∀ i : Fin (negCount c),
        upperNegAtomWitness a c z i l *
            star (upperNegAtomWitness a c z i m) =
          ((-(c (negIndex c i)) : ℝ) : ℂ) *
            (upperFiniteAtomFeature a z (negIndex c i) l *
              star (upperFiniteAtomFeature a z (negIndex c i) m)) :=
      fun i => upperNegAtomWitness_mul_star a c z i l m
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [negIndex]
    rw [Equiv.sum_comp (negIndicesEquiv c).symm fun j :
      {j // j ∈ negIndices c} =>
        ((-(c (j : Fin d)) : ℝ) : ℂ) *
          (upperFiniteAtomFeature a z (j : Fin d) l *
            star (upperFiniteAtomFeature a z (j : Fin d) m))]
    exact Finset.sum_coe_sort (negIndices c) (fun j : Fin d =>
      ((-(c j) : ℝ) : ℂ) *
        (upperFiniteAtomFeature a z j l *
          star (upperFiniteAtomFeature a z j m)))
  rw [hcorr, negIndices, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hneg : c j < 0
  · rw [if_pos hneg, max_eq_right hneg.le]
    push_cast
    ring
  · rw [if_neg hneg, max_eq_left (not_lt.1 hneg)]
    ring

def upperPositiveAtomFactor {d N : ℕ} (a c : Fin d → ℝ)
    (z : Fin N → ℂ) : Matrix (Fin N) (Fin d) ℂ :=
  Matrix.of fun l j => (Real.sqrt (max (c j) 0) : ℂ) *
    upperFiniteAtomFeature a z j l

theorem upperPositiveAtomGram_posSemidef {d N : ℕ}
    (a c : Fin d → ℝ) (z : Fin N → ℂ) :
    (Matrix.of fun l m => ∑ j, ((max (c j) 0 : ℝ) : ℂ) *
      (upperFiniteAtomFeature a z j l *
        star (upperFiniteAtomFeature a z j m))).PosSemidef := by
  have hBB :
      (Matrix.of fun l m => ∑ j, ((max (c j) 0 : ℝ) : ℂ) *
        (upperFiniteAtomFeature a z j l *
          star (upperFiniteAtomFeature a z j m))) =
        upperPositiveAtomFactor a c z *
          (upperPositiveAtomFactor a c z)ᴴ := by
    ext l m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, upperPositiveAtomFactor, RCLike.star_def]
    apply Finset.sum_congr rfl
    intro j hj
    have hnn : (0 : ℝ) ≤ max (c j) 0 := le_max_right _ _
    have hsq := Real.mul_self_sqrt hnn
    rw [map_mul, Complex.conj_ofReal]
    rw [show ((max (c j) 0 : ℝ) : ℂ) =
        ((Real.sqrt (max (c j) 0) : ℝ) : ℂ) *
          ((Real.sqrt (max (c j) 0) : ℝ) : ℂ) by
      rw [← Complex.ofReal_mul, hsq]]
    ring
  rw [hBB]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem carrierPickMatrix_chamberHerglotz_eq
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    {d N : ℕ} (a c : Fin d → ℝ)
    (z : Fin N → ℂ) (hz : ∀ j, 0 < (z j).im) :
    carrierPickMatrix (chamberHerglotz ν a c) z =
      upperSignedAtomGram a c z + upperMeasureGram ν z := by
  change carrierPickMatrix
      (fun w => atomPart a c w +
        ∫ t, regularizedHerglotzKernel t w ∂ν) z = _
  rw [carrierPickMatrix_add,
    carrierPickMatrix_atomPart_eq_upperSignedAtomGram a c z hz,
    carrierPickMatrix_regularizedHerglotz_eq_upperMeasureGram
      ν hH0 z hz]

theorem carrierPickMatrix_chamberHerglotz_add_negWitness_posSemidef
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν)
    {d N : ℕ} (a c : Fin d → ℝ)
    (z : Fin N → ℂ) (hz : ∀ j, 0 < (z j).im) :
    (carrierPickMatrix (chamberHerglotz ν a c) z +
      ∑ i, Matrix.of fun l m =>
        upperNegAtomWitness a c z i l *
          star (upperNegAtomWitness a c z i m)).PosSemidef := by
  rw [carrierPickMatrix_chamberHerglotz_eq ν hH0 a c z hz]
  have hatom := upperPositiveAtomGram_posSemidef a c z
  have hmeasure := upperMeasureGram_posSemidef ν hH0 z hz
  rw [add_assoc, add_comm (upperMeasureGram ν z), ← add_assoc,
    upperSignedAtomGram_add_negWitness a c z]
  exact hatom.add hmeasure

theorem chamberHerglotz_hasExactlyNegativeSquares
    {d : ℕ} (ν : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight ν)
    (a c : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, ν {a j} = 0) :
    CarrierHasExactlyNegativeSquares
      (chamberHerglotz ν a c) (negCount c) := by
  constructor
  · intro N z hz W hW
    exact neg_inertia_le_negCount
      (carrierPickMatrix (chamberHerglotz ν a c) z) c
      (upperNegAtomWitness a c z)
      (carrierPickMatrix_chamberHerglotz_add_negWitness_posSemidef
        ν hH0 a c z hz) W hW
  · obtain ⟨δ, hδ, hc⟩ := exists_negativeCoefficientMargin c
    let R : ℝ := 1
    have hR : 0 < R := one_pos
    have hweight : Integrable (fun t : ℝ => 1 / (1 + t ^ 2)) ν := by
      refine hH0.congr (Filter.Eventually.of_forall fun t => ?_)
      simp [nevanlinnaWeight, one_div]
    have hdom : ∀ j : Fin d,
        Integrable (atomDominant (a j) R) ν := by
      intro j
      exact integrable_atomDominant ν
        (herglotzMeasure_atomBall_ne_top ν hH0 (a j) R hR)
        hweight
    have hnegTotal := eventually_negDef_totalGram_negSupported
      ν a c ha hδ hc R hR hdom hatom
    have hnegPick : ∀ᶠ y : ℝ in 𝓝[≠] 0,
        ∀ x ∈ negSupported c, x ≠ 0 →
          (star x ⬝ᵥ (chamberPickKernel ν a c y).mulVec x).re < 0 := by
      filter_upwards [hnegTotal, self_mem_nhdsWithin]
        with y hy hy0
      intro x hx hx0
      have hreg : ∀ l : Fin d,
          Integrable (fun t =>
            regularizedHerglotzKernel t (upperNode (a l) y)) ν := by
        intro l
        exact integrable_regularizedHerglotzKernel_of_nevanlinna
          ν hH0 (by simpa [upperNode_im] using hy0)
      have h := hy x hx hx0
      rw [totalGram_eq_smul_chamberPickKernel
        ν a c hy0 hreg,
        re_quadForm_smul_neg_iff _ hy0] at h
      exact h
    have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_mono 0 (by
        intro y hy
        exact ne_of_gt hy)
    have hall : ∀ᶠ y : ℝ in 𝓝[>] 0,
        0 < y ∧ ∀ x ∈ negSupported c, x ≠ 0 →
          (star x ⬝ᵥ (chamberPickKernel ν a c y).mulVec x).re < 0 := by
      filter_upwards [hmono hnegPick, self_mem_nhdsWithin]
        with y hneg hy
      exact ⟨hy, hneg⟩
    obtain ⟨y, hy, hneg⟩ := hall.exists
    let z : Fin d → ℂ := fun j => upperNode (a j) y
    have hz : ∀ j, 0 < (z j).im := by
      intro j
      simpa [z, upperNode_im] using hy
    have hzinj : Function.Injective z := by
      intro i j hij
      apply ha
      have hre := congrArg Complex.re hij
      simpa [z, upperNode] using hre
    refine ⟨d, z, negSupported c, hz, hzinj,
      finrank_negSupported c, ?_⟩
    intro x hx hx0
    change ∀ x ∈ negSupported c, x ≠ 0 →
      (star x ⬝ᵥ
        (carrierPickMatrix (chamberHerglotz ν a c) z).mulVec x).re < 0
      at hneg
    exact hneg x hx hx0

/-- Exact index in the chamber's intrinsic Hamming-distance grading. -/
theorem chamberHerglotz_hasExactlyHammingDistanceNegativeSquares
    {d : ℕ} (ν : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight ν)
    (a c : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, ν {a j} = 0) :
    CarrierHasExactlyNegativeSquares
      (chamberHerglotz ν a c)
      (hammingDist (signPattern c) (positiveChamber d)) := by
  rw [← negCount_eq_hammingDist]
  exact chamberHerglotz_hasExactlyNegativeSquares
    ν hH0 a c ha hatom

/-- Removing a finite real support and reinserting arbitrary coefficients has exact global index
equal to the negative-coefficient count.  This is the fixed-support finite-surgery form of the
chamber law; zero coefficients literally delete atoms. -/
theorem replaceFiniteAtoms_hasExactlyNegativeSquares
    {d : ℕ} (ν : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight ν)
    (a c : Fin d → ℝ) (ha : Function.Injective a) :
    let background := ν.restrict (Set.range a)ᶜ
    CarrierHasExactlyNegativeSquares
      (chamberHerglotz background a c) (negCount c) := by
  dsimp only
  let background : Measure ℝ := ν.restrict (Set.range a)ᶜ
  have hbackground : Integrable nevanlinnaWeight background :=
    hH0.mono_measure Measure.restrict_le_self
  have hatom : ∀ j, background {a j} = 0 := by
    intro j
    change (ν.restrict (Set.range a)ᶜ) {a j} = 0
    rw [Measure.restrict_apply (measurableSet_singleton (a j))]
    simp
  exact chamberHerglotz_hasExactlyNegativeSquares
    background hbackground a c ha hatom

/-- Complete measure-level chamber package with the literal global exact-negative-squares law. -/
theorem finiteAtomicHerglotzChamber_exactNegativeSquares_complete
    {d : ℕ} (ν : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight ν)
    (a c : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, ν {a j} = 0) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range (chamberHerglotzTranslateFamily ν hH0 a c)) =
        differentialAdjoin upperEndRationalCoordinateField
          (Set.range (regularizedH0TranslateFamily ν hH0)) ∧
      differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (chamberHerglotzTranslateFamily ν hH0 a c) =
        differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (regularizedH0TranslateFamily ν hH0) ∧
      (∀ h : ℂ,
        upperEndRationalGaugeClass
            (chamberHerglotzTranslateFamily ν hH0 a c h) =
          upperEndRationalGaugeClass
            (regularizedH0TranslateFamily ν hH0 h)) ∧
      CarrierHasExactlyNegativeSquares
        (chamberHerglotz ν a c)
        (hammingDist (signPattern c) (positiveChamber d)) := by
  exact ⟨chamberHerglotzTranslateFamily_differentialAdjoin_eq
      ν hH0 a c,
    chamberHerglotzTranslateFamily_differentialFamilyMatroid_eq
      ν hH0 a c,
    chamberHerglotzTranslateFamily_rationalGaugeClass_eq
      ν hH0 a c,
    chamberHerglotz_hasExactlyHammingDistanceNegativeSquares
      ν hH0 a c ha hatom⟩

/-- Complete two-point rational-gauge slice: field, represented differential matroid,
differential-independence status, and generator class are fixed, while the second representative
has its exact global Pick index. -/
theorem finiteAtomicHerglotzGaugeSlice_exactNegativeSquares_complete
    {d : ℕ} (ν : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight ν)
    (a : Fin d → ℝ) (ha : Function.Injective a)
    (hatom : ∀ j, ν {a j} = 0)
    (c₀ c₁ : Fin d → ℝ) :
    differentialAdjoin upperEndRationalCoordinateField
        (Set.range (chamberHerglotzTranslateFamily ν hH0 a c₁)) =
      differentialAdjoin upperEndRationalCoordinateField
        (Set.range (chamberHerglotzTranslateFamily ν hH0 a c₀)) ∧
      differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (chamberHerglotzTranslateFamily ν hH0 a c₁) =
        differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (chamberHerglotzTranslateFamily ν hH0 a c₀) ∧
      (DifferentialIndependent upperEndRationalCoordinateField
          (chamberHerglotzTranslateFamily ν hH0 a c₁) ↔
        DifferentialIndependent upperEndRationalCoordinateField
          (chamberHerglotzTranslateFamily ν hH0 a c₀)) ∧
      (∀ h : ℂ,
        upperEndRationalGaugeClass
            (chamberHerglotzTranslateFamily ν hH0 a c₁ h) =
          upperEndRationalGaugeClass
            (chamberHerglotzTranslateFamily ν hH0 a c₀ h)) ∧
      CarrierHasExactlyNegativeSquares
        (chamberHerglotz ν a c₁)
        (hammingDist (signPattern c₁) (positiveChamber d)) := by
  refine ⟨?_, ?_, ?_, ?_,
    chamberHerglotz_hasExactlyHammingDistanceNegativeSquares
      ν hH0 a c₁ ha hatom⟩
  · exact
      (chamberHerglotzTranslateFamily_differentialAdjoin_eq
        ν hH0 a c₁).trans
        (chamberHerglotzTranslateFamily_differentialAdjoin_eq
          ν hH0 a c₀).symm
  · exact
      (chamberHerglotzTranslateFamily_differentialFamilyMatroid_eq
        ν hH0 a c₁).trans
        (chamberHerglotzTranslateFamily_differentialFamilyMatroid_eq
          ν hH0 a c₀).symm
  · exact
      (chamberHerglotzTranslateFamily_differentialIndependent_iff
        ν hH0 a c₁).trans
        (chamberHerglotzTranslateFamily_differentialIndependent_iff
          ν hH0 a c₀).symm
  · intro h
    exact
      (chamberHerglotzTranslateFamily_rationalGaugeClass_eq
        ν hH0 a c₁ h).trans
        (chamberHerglotzTranslateFamily_rationalGaugeClass_eq
          ν hH0 a c₀ h).symm

/-- Every finite chamber over an exponentially reweighted H0 measure exists with exact global
negative-square grading, at insertion points fixed for the whole coefficient cube. -/
theorem exists_fullFiniteAtomicChamber_exactNegativeSquares
    (d : ℕ) (μ : Measure ℝ) (u : Lp ℝ ⊤ μ)
    (hH0 : Integrable nevanlinnaWeight μ) :
    ∃ a : Fin d → ℝ, Function.Injective a ∧
      (∀ j, expReweightedMeasure μ u {a j} = 0) ∧
      ∀ c : Fin d → ℝ,
        CarrierHasExactlyNegativeSquares
          (chamberHerglotz (expReweightedMeasure μ u) a c)
          (hammingDist (signPattern c) (positiveChamber d)) := by
  obtain ⟨a, ha, hatom⟩ :=
    exists_injective_expReweightedMeasure_nonAtoms d μ u hH0
  refine ⟨a, ha, hatom, ?_⟩
  intro c
  exact chamberHerglotz_hasExactlyHammingDistanceNegativeSquares
    (expReweightedMeasure μ u)
    (integrable_nevanlinnaWeight_expReweightedMeasure μ u hH0)
    a c ha hatom

def evenPairedAtomLocations {d : ℕ} (a : Fin d → ℝ) :
    Fin (d + d) → ℝ :=
  fun j => Sum.elim a (fun i => -a i) (finSumFinEquiv.symm j)

def evenPairedAtomCoefficients {d : ℕ} (c : Fin d → ℝ) :
    Fin (d + d) → ℝ :=
  fun j => Sum.elim c c (finSumFinEquiv.symm j)

@[simp] theorem evenPairedAtomLocations_inl {d : ℕ}
    (a : Fin d → ℝ) (i : Fin d) :
    evenPairedAtomLocations a (finSumFinEquiv (Sum.inl i)) = a i := by
  change Sum.elim a (fun i => -a i)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = a i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem evenPairedAtomLocations_inr {d : ℕ}
    (a : Fin d → ℝ) (i : Fin d) :
    evenPairedAtomLocations a (finSumFinEquiv (Sum.inr i)) = -a i := by
  change Sum.elim a (fun i => -a i)
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = -a i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem evenPairedAtomCoefficients_inl {d : ℕ}
    (c : Fin d → ℝ) (i : Fin d) :
    evenPairedAtomCoefficients c (finSumFinEquiv (Sum.inl i)) = c i := by
  change Sum.elim c c
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i))) = c i
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem evenPairedAtomCoefficients_inr {d : ℕ}
    (c : Fin d → ℝ) (i : Fin d) :
    evenPairedAtomCoefficients c (finSumFinEquiv (Sum.inr i)) = c i := by
  change Sum.elim c c
      (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) = c i
  rw [Equiv.symm_apply_apply]
  rfl

theorem evenPairedAtomLocations_injective {d : ℕ}
    (a : Fin d → ℝ) (ha : Function.Injective a)
    (hapos : ∀ i, 0 < a i) :
    Function.Injective (evenPairedAtomLocations a) := by
  intro x y hxy
  apply finSumFinEquiv.symm.injective
  generalize hx : finSumFinEquiv.symm x = sx
  generalize hy : finSumFinEquiv.symm y = sy
  change Sum.elim a (fun i => -a i) (finSumFinEquiv.symm x) =
      Sum.elim a (fun i => -a i) (finSumFinEquiv.symm y) at hxy
  rw [hx, hy] at hxy
  cases sx with
  | inl i =>
      cases sy with
      | inl j =>
          simp only [Sum.elim_inl] at hxy
          exact congrArg Sum.inl (ha hxy)
      | inr j =>
          simp only [Sum.elim_inl, Sum.elim_inr] at hxy
          exfalso
          linarith [hapos i, hapos j]
  | inr i =>
      cases sy with
      | inl j =>
          simp only [Sum.elim_inr, Sum.elim_inl] at hxy
          exfalso
          linarith [hapos i, hapos j]
      | inr j =>
          simp only [Sum.elim_inr] at hxy
          exact congrArg Sum.inr (ha (neg_injective hxy))

theorem negCount_evenPairedAtomCoefficients {d : ℕ}
    (c : Fin d → ℝ) :
    negCount (evenPairedAtomCoefficients c) =
      negCount c + negCount c := by
  unfold negCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [evenPairedAtomCoefficients_inl,
    evenPairedAtomCoefficients_inr]

/-- The common-coefficient `±a` rational gauge is odd, as required by the scalar functional
equation. -/
theorem atomPart_evenPaired_neg {d : ℕ}
    (a c : Fin d → ℝ) (z : ℂ) :
    atomPart (evenPairedAtomLocations a)
        (evenPairedAtomCoefficients c) (-z) =
      -atomPart (evenPairedAtomLocations a)
        (evenPairedAtomCoefficients c) z := by
  rw [atomPart, atomPart,
    ← Equiv.sum_comp finSumFinEquiv,
    Fintype.sum_sum_type,
    ← Equiv.sum_comp finSumFinEquiv,
    Fintype.sum_sum_type]
  simp only [evenPairedAtomLocations_inl,
    evenPairedAtomLocations_inr,
    evenPairedAtomCoefficients_inl,
    evenPairedAtomCoefficients_inr,
    Complex.ofReal_neg, sub_neg_eq_add]
  rw [neg_add, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib]
  rw [add_comm
    (∑ i, -((c i : ℂ) /
      ((a i : ℂ) - z)))
    (∑ i, -((c i : ℂ) /
      (-((a i : ℝ) : ℂ) - z)))]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    rw [show ((a i : ℂ) + z) =
      -(-((a i : ℝ) : ℂ) - z) by ring,
      div_neg]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [show (-((a i : ℝ) : ℂ) + z) =
      -((a i : ℂ) - z) by ring,
      div_neg]

theorem evenPaired_replaceFiniteAtoms_hasExactlyNegativeSquares
    {d : ℕ} (ν : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight ν)
    (a c : Fin d → ℝ) (ha : Function.Injective a)
    (hapos : ∀ i, 0 < a i) :
    let pairedA := evenPairedAtomLocations a
    let pairedC := evenPairedAtomCoefficients c
    let background := ν.restrict (Set.range pairedA)ᶜ
    CarrierHasExactlyNegativeSquares
      (chamberHerglotz background pairedA pairedC)
      (negCount c + negCount c) := by
  dsimp only
  have h := replaceFiniteAtoms_hasExactlyNegativeSquares
    ν hH0 (evenPairedAtomLocations a)
      (evenPairedAtomCoefficients c)
      (evenPairedAtomLocations_injective a ha hapos)
  rwa [negCount_evenPairedAtomCoefficients] at h

end

end GaloisForLFunctions.HTGeometry
