import GaloisForLFunctions.HTGeometry.ComplexEventSquareRealificationNoGo
import Mathlib.Analysis.Matrix.Spectrum

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

/-! Hermitian mixed-adjacency decomposition. -/

structure RealSymmetricMatrix (ι : Type*) where
  matrix : Matrix ι ι ℝ
  transpose_eq : matrix.transpose = matrix

structure RealSkewSymmetricMatrix (ι : Type*) where
  matrix : Matrix ι ι ℝ
  transpose_eq_neg : matrix.transpose = -matrix

def mixedHermitianMatrix {ι : Type*}
    (U : RealSymmetricMatrix ι) (D : RealSkewSymmetricMatrix ι) : Matrix ι ι ℂ :=
  fun i j => (U.matrix i j : ℂ) + Complex.I * (D.matrix i j : ℂ)

theorem mixedHermitianMatrix_isHermitian {ι : Type*}
    (U : RealSymmetricMatrix ι) (D : RealSkewSymmetricMatrix ι) :
    (mixedHermitianMatrix U D).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hU := congrFun (congrFun U.transpose_eq i) j
  have hD := congrFun (congrFun D.transpose_eq_neg i) j
  change U.matrix j i = U.matrix i j at hU
  change D.matrix j i = -D.matrix i j at hD
  simp [mixedHermitianMatrix, hU, hD]

theorem mixedHermitianMatrix_realPart {ι : Type*}
    (U : RealSymmetricMatrix ι) (D : RealSkewSymmetricMatrix ι) :
    complexMatrixRealPart (mixedHermitianMatrix U D) = U.matrix := by
  ext i j
  simp [complexMatrixRealPart, mixedHermitianMatrix]

theorem mixedHermitianMatrix_imagPart {ι : Type*}
    (U : RealSymmetricMatrix ι) (D : RealSkewSymmetricMatrix ι) :
    complexMatrixImagPart (mixedHermitianMatrix U D) = D.matrix := by
  ext i j
  simp [complexMatrixImagPart, mixedHermitianMatrix]

/-- Reversing every directed edge negates the skew-symmetric sector. -/
def reverseDirectedPart {ι : Type*} (D : RealSkewSymmetricMatrix ι) :
    RealSkewSymmetricMatrix ι where
  matrix := -D.matrix
  transpose_eq_neg := by
    rw [Matrix.transpose_neg, D.transpose_eq_neg, neg_neg]

theorem mixedHermitianMatrix_reverseDirectedPart_apply {ι : Type*}
    (U : RealSymmetricMatrix ι) (D : RealSkewSymmetricMatrix ι) (i j : ι) :
    mixedHermitianMatrix U (reverseDirectedPart D) i j =
      star (mixedHermitianMatrix U D i j) := by
  simp [mixedHermitianMatrix, reverseDirectedPart]

theorem mixedHermitianMatrix_transpose_eq_reverseDirectedPart {ι : Type*}
    (U : RealSymmetricMatrix ι) (D : RealSkewSymmetricMatrix ι) :
    (mixedHermitianMatrix U D)ᵀ = mixedHermitianMatrix U (reverseDirectedPart D) := by
  ext i j
  have hU := congrFun (congrFun U.transpose_eq i) j
  have hD := congrFun (congrFun D.transpose_eq_neg i) j
  change U.matrix j i = U.matrix i j at hU
  change D.matrix j i = -D.matrix i j at hD
  simp [mixedHermitianMatrix, reverseDirectedPart, hU, hD]

def hermitianUndirectedPart {ι : Type*} (H : {M : Matrix ι ι ℂ // M.IsHermitian}) :
    RealSymmetricMatrix ι where
  matrix := complexMatrixRealPart H
  transpose_eq := by
    have h := complexMatrixRealPart_conjTranspose (X := (H : Matrix ι ι ℂ))
    rw [H.property.eq] at h
    exact h.symm

def hermitianDirectedPart {ι : Type*} (H : {M : Matrix ι ι ℂ // M.IsHermitian}) :
    RealSkewSymmetricMatrix ι where
  matrix := complexMatrixImagPart H
  transpose_eq_neg := by
    have h := complexMatrixImagPart_conjTranspose (X := (H : Matrix ι ι ℂ))
    rw [H.property.eq] at h
    ext i j
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.neg_apply, Matrix.transpose_apply] at hij ⊢
    linarith

theorem mixedHermitianMatrix_parts_reconstruct {ι : Type*}
    (H : {M : Matrix ι ι ℂ // M.IsHermitian}) :
    mixedHermitianMatrix (hermitianUndirectedPart H) (hermitianDirectedPart H) = H := by
  ext i j
  apply Complex.ext <;>
    simp [mixedHermitianMatrix, hermitianUndirectedPart, hermitianDirectedPart,
      complexMatrixRealPart, complexMatrixImagPart]

/-- Complexification embeds every real Hermitian matrix into the mixed-graph class. -/
def realHermitianComplexification {ι : Type*}
    (H : {M : Matrix ι ι ℝ // M.IsHermitian}) :
    {M : Matrix ι ι ℂ // M.IsHermitian} :=
  ⟨H.val.map Complex.ofReal, H.property.map Complex.ofReal (by intro x; simp)⟩

theorem realHermitianComplexification_reconstruct {ι : Type*}
    (H : {M : Matrix ι ι ℝ // M.IsHermitian}) :
    mixedHermitianMatrix
        (hermitianUndirectedPart (realHermitianComplexification H))
        (hermitianDirectedPart (realHermitianComplexification H)) =
      H.val.map Complex.ofReal :=
  mixedHermitianMatrix_parts_reconstruct (realHermitianComplexification H)

@[simp] theorem realHermitianComplexification_directedPart_eq_zero {ι : Type*}
    (H : {M : Matrix ι ι ℝ // M.IsHermitian}) :
    (hermitianDirectedPart (realHermitianComplexification H)).matrix = 0 := by
  ext i j
  simp [hermitianDirectedPart, realHermitianComplexification, complexMatrixImagPart]

theorem mixedHermitianMatrix_eigenvalues_are_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : RealSymmetricMatrix ι) (D : RealSkewSymmetricMatrix ι) (i : ι) :
    star (((mixedHermitianMatrix_isHermitian U D).eigenvalues i : ℝ) : ℂ) =
      (((mixedHermitianMatrix_isHermitian U D).eigenvalues i : ℝ) : ℂ) := by
  simp

/-! Four-state edge law and radius identity. -/

structure Parameters where
  connection : ℝ
  directionality : ℝ
  connection_mem : connection ∈ Set.Icc (0 : ℝ) 1
  directionality_mem : directionality ∈ Set.Icc (0 : ℝ) 1

def edgeWeight (θ : Parameters) : Fin 4 → ℝ :=
  ![1 - θ.connection,
    θ.connection * (1 - θ.directionality),
    θ.connection * θ.directionality / 2,
    θ.connection * θ.directionality / 2]

def edgeValue : Fin 4 → ℂ := ![0, 1, Complex.I, -Complex.I]

theorem edgeWeight_nonneg (θ : Parameters) (k : Fin 4) : 0 ≤ edgeWeight θ k := by
  rcases θ.connection_mem with ⟨hc0, hc1⟩
  rcases θ.directionality_mem with ⟨hp0, hp1⟩
  fin_cases k <;> simp [edgeWeight]
  · linarith
  · exact mul_nonneg hc0 (sub_nonneg.mpr hp1)
  · positivity
  · positivity

theorem sum_edgeWeight (θ : Parameters) : ∑ k, edgeWeight θ k = 1 := by
  simp [edgeWeight, Fin.sum_univ_four]
  ring

def edgeMean (θ : Parameters) : ℂ :=
  ∑ k, (edgeWeight θ k : ℂ) * edgeValue k

theorem edgeMean_eq (θ : Parameters) :
    edgeMean θ = (θ.connection * (1 - θ.directionality) : ℝ) := by
  simp [edgeMean, edgeWeight, edgeValue, Fin.sum_univ_four]

def edgeSecondMoment (θ : Parameters) : ℝ :=
  ∑ k, edgeWeight θ k * Complex.normSq (edgeValue k)

theorem edgeSecondMoment_eq (θ : Parameters) : edgeSecondMoment θ = θ.connection := by
  simp [edgeSecondMoment, edgeWeight, edgeValue, Fin.sum_univ_four, Complex.normSq]
  ring

def edgeVariance (θ : Parameters) : ℝ :=
  edgeSecondMoment θ - Complex.normSq (edgeMean θ)

theorem edgeVariance_eq (θ : Parameters) :
    edgeVariance θ = θ.connection - (θ.connection * (1 - θ.directionality)) ^ (2 : ℕ) := by
  rw [edgeVariance, edgeSecondMoment_eq, edgeMean_eq]
  simp [Complex.normSq]
  ring

theorem edgeVariance_nonneg (θ : Parameters) : 0 ≤ edgeVariance θ := by
  rw [edgeVariance_eq]
  rcases θ.connection_mem with ⟨hc0, hc1⟩
  rcases θ.directionality_mem with ⟨hp0, hp1⟩
  have hfactor0 : 0 ≤ 1 - θ.directionality := by linarith
  have hfactor1 : 1 - θ.directionality ≤ 1 := by linarith
  have hx0 : 0 ≤ θ.connection * (1 - θ.directionality) := mul_nonneg hc0 hfactor0
  have hxc : θ.connection * (1 - θ.directionality) ≤ θ.connection :=
    mul_le_of_le_one_right hc0 hfactor1
  have hx1 : θ.connection * (1 - θ.directionality) ≤ 1 := hxc.trans hc1
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]

def radiusSquared (N : ℕ) (θ : Parameters) : ℝ :=
  4 * N * (1 - θ.directionality) * θ.connection *
      (1 - (1 - θ.directionality) * θ.connection) +
    4 * N * θ.directionality * θ.connection

theorem radiusSquared_eq_four_mul_variance (N : ℕ) (θ : Parameters) :
    radiusSquared N θ = 4 * N * edgeVariance θ := by
  rw [edgeVariance_eq]
  unfold radiusSquared
  ring

theorem radiusSquared_simplified (N : ℕ) (θ : Parameters) :
    radiusSquared N θ =
      4 * N * θ.connection *
        (1 - (1 - θ.directionality) ^ (2 : ℕ) * θ.connection) := by
  rw [radiusSquared_eq_four_mul_variance, edgeVariance_eq]
  ring

theorem radiusSquared_nonneg (N : ℕ) (θ : Parameters) : 0 ≤ radiusSquared N θ := by
  rw [radiusSquared_eq_four_mul_variance]
  exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg N)) (edgeVariance_nonneg θ)

def undirectedParameters (connection : Set.Icc (0 : ℝ) 1) : Parameters where
  connection := connection
  directionality := 0
  connection_mem := connection.property
  directionality_mem := by constructor <;> norm_num

def directedParameters (connection : Set.Icc (0 : ℝ) 1) : Parameters where
  connection := connection
  directionality := 1
  connection_mem := connection.property
  directionality_mem := by constructor <;> norm_num

@[simp] theorem edgeVariance_undirectedParameters (connection : Set.Icc (0 : ℝ) 1) :
    edgeVariance (undirectedParameters connection) = connection - connection ^ (2 : ℕ) := by
  rw [edgeVariance_eq]
  simp [undirectedParameters]

@[simp] theorem edgeVariance_directedParameters (connection : Set.Icc (0 : ℝ) 1) :
    edgeVariance (directedParameters connection) = connection := by
  rw [edgeVariance_eq]
  simp [directedParameters]

/-! Pandey--Mehta Hermitian interpolation. -/

def pandeyMehtaMatrix {ι : Type*} (alpha : Set.Icc (0 : ℝ) 1)
    (H₁ H₂ : {M : Matrix ι ι ℂ // M.IsHermitian}) : Matrix ι ι ℂ :=
  (Real.sqrt (1 - (alpha : ℝ) ^ (2 : ℕ)) : ℂ) • H₁.val + (alpha : ℂ) • H₂.val

theorem pandeyMehtaMatrix_isHermitian {ι : Type*} (alpha : Set.Icc (0 : ℝ) 1)
    (H₁ H₂ : {M : Matrix ι ι ℂ // M.IsHermitian}) :
    (pandeyMehtaMatrix alpha H₁ H₂).IsHermitian := by
  apply Matrix.IsHermitian.add
  · exact H₁.property.smul (Complex.conj_ofReal _)
  · exact H₂.property.smul (Complex.conj_ofReal _)

def orthogonalEndpoint : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩

def unitaryEndpoint : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩

@[simp] theorem pandeyMehtaMatrix_orthogonalEndpoint {ι : Type*}
    (H₁ H₂ : {M : Matrix ι ι ℂ // M.IsHermitian}) :
    pandeyMehtaMatrix orthogonalEndpoint H₁ H₂ = H₁ := by
  simp [pandeyMehtaMatrix, orthogonalEndpoint]

@[simp] theorem pandeyMehtaMatrix_unitaryEndpoint {ι : Type*}
    (H₁ H₂ : {M : Matrix ι ι ℂ // M.IsHermitian}) :
    pandeyMehtaMatrix unitaryEndpoint H₁ H₂ = H₂ := by
  simp [pandeyMehtaMatrix, unitaryEndpoint]

theorem pandeyMehtaMatrix_mixedGraph_reconstruction {ι : Type*}
    (alpha : Set.Icc (0 : ℝ) 1)
    (H₁ H₂ : {M : Matrix ι ι ℂ // M.IsHermitian}) :
    mixedHermitianMatrix
        (hermitianUndirectedPart ⟨pandeyMehtaMatrix alpha H₁ H₂,
          pandeyMehtaMatrix_isHermitian alpha H₁ H₂⟩)
        (hermitianDirectedPart ⟨pandeyMehtaMatrix alpha H₁ H₂,
          pandeyMehtaMatrix_isHermitian alpha H₁ H₂⟩) =
      pandeyMehtaMatrix alpha H₁ H₂ :=
  mixedHermitianMatrix_parts_reconstruct
    ⟨pandeyMehtaMatrix alpha H₁ H₂, pandeyMehtaMatrix_isHermitian alpha H₁ H₂⟩

/-! Ordered spacings and unfolding-free ratios. -/

structure OrderedSpectralTriple where
  lower : ℝ
  middle : ℝ
  upper : ℝ
  lower_lt_middle : lower < middle
  middle_lt_upper : middle < upper

def firstSpacing (T : OrderedSpectralTriple) : ℝ := T.middle - T.lower
def secondSpacing (T : OrderedSpectralTriple) : ℝ := T.upper - T.middle
def consecutiveSpacingRatio (T : OrderedSpectralTriple) : ℝ := secondSpacing T / firstSpacing T
def nextNearestSpacing (T : OrderedSpectralTriple) : ℝ := (T.upper - T.lower) / 2
def foldedSpacingRatio (T : OrderedSpectralTriple) : ℝ :=
  min (consecutiveSpacingRatio T) (consecutiveSpacingRatio T)⁻¹

theorem firstSpacing_pos (T : OrderedSpectralTriple) : 0 < firstSpacing T := by
  exact sub_pos.mpr T.lower_lt_middle

theorem secondSpacing_pos (T : OrderedSpectralTriple) : 0 < secondSpacing T := by
  exact sub_pos.mpr T.middle_lt_upper

theorem consecutiveSpacingRatio_pos (T : OrderedSpectralTriple) :
    0 < consecutiveSpacingRatio T := by
  exact div_pos (secondSpacing_pos T) (firstSpacing_pos T)

theorem nextNearestSpacing_eq_mean (T : OrderedSpectralTriple) :
    nextNearestSpacing T = (firstSpacing T + secondSpacing T) / 2 := by
  simp [nextNearestSpacing, firstSpacing, secondSpacing]

def affineImage (a : {x : ℝ // 0 < x}) (b : ℝ) (T : OrderedSpectralTriple) :
    OrderedSpectralTriple where
  lower := a * T.lower + b
  middle := a * T.middle + b
  upper := a * T.upper + b
  lower_lt_middle := by nlinarith [a.property, T.lower_lt_middle]
  middle_lt_upper := by nlinarith [a.property, T.middle_lt_upper]

theorem consecutiveSpacingRatio_affine_invariant
    (a : {x : ℝ // 0 < x}) (b : ℝ) (T : OrderedSpectralTriple) :
    consecutiveSpacingRatio (affineImage a b T) = consecutiveSpacingRatio T := by
  have ha : (a : ℝ) ≠ 0 := ne_of_gt a.property
  simp [consecutiveSpacingRatio, firstSpacing, secondSpacing, affineImage]
  field_simp

def reverseTriple (T : OrderedSpectralTriple) : OrderedSpectralTriple where
  lower := -T.upper
  middle := -T.middle
  upper := -T.lower
  lower_lt_middle := by linarith [T.middle_lt_upper]
  middle_lt_upper := by linarith [T.lower_lt_middle]

theorem consecutiveSpacingRatio_reverse (T : OrderedSpectralTriple) :
    consecutiveSpacingRatio (reverseTriple T) = (consecutiveSpacingRatio T)⁻¹ := by
  have h1 : firstSpacing T ≠ 0 := ne_of_gt (firstSpacing_pos T)
  have h2 : secondSpacing T ≠ 0 := ne_of_gt (secondSpacing_pos T)
  simp [consecutiveSpacingRatio, firstSpacing, secondSpacing, reverseTriple]
  field_simp
  ring

theorem foldedSpacingRatio_nonneg (T : OrderedSpectralTriple) :
    0 ≤ foldedSpacingRatio T := by
  exact le_min (consecutiveSpacingRatio_pos T).le (inv_nonneg.mpr (consecutiveSpacingRatio_pos T).le)

theorem foldedSpacingRatio_le_one (T : OrderedSpectralTriple) :
    foldedSpacingRatio T ≤ 1 := by
  have hr := consecutiveSpacingRatio_pos T
  rcases le_total (consecutiveSpacingRatio T) 1 with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans ((inv_le_one₀ hr).2 h)

theorem foldedSpacingRatio_reverse (T : OrderedSpectralTriple) :
    foldedSpacingRatio (reverseTriple T) = foldedSpacingRatio T := by
  rw [foldedSpacingRatio, consecutiveSpacingRatio_reverse, foldedSpacingRatio]
  have hr : consecutiveSpacingRatio T ≠ 0 := ne_of_gt (consecutiveSpacingRatio_pos T)
  rw [inv_inv]
  exact min_comm _ _

/-- Canonical ordered triple with constant positive spacing. -/
def equispacedTriple (origin : ℝ) (step : {x : ℝ // 0 < x}) : OrderedSpectralTriple where
  lower := origin
  middle := origin + step
  upper := origin + 2 * step
  lower_lt_middle := by linarith [step.property]
  middle_lt_upper := by linarith [step.property]

@[simp] theorem firstSpacing_equispacedTriple
    (origin : ℝ) (step : {x : ℝ // 0 < x}) :
    firstSpacing (equispacedTriple origin step) = step := by
  simp [firstSpacing, equispacedTriple]

@[simp] theorem secondSpacing_equispacedTriple
    (origin : ℝ) (step : {x : ℝ // 0 < x}) :
    secondSpacing (equispacedTriple origin step) = step := by
  simp [secondSpacing, equispacedTriple]
  ring

@[simp] theorem consecutiveSpacingRatio_equispacedTriple
    (origin : ℝ) (step : {x : ℝ // 0 < x}) :
    consecutiveSpacingRatio (equispacedTriple origin step) = 1 := by
  rw [consecutiveSpacingRatio, firstSpacing_equispacedTriple, secondSpacing_equispacedTriple,
    div_self (ne_of_gt step.property)]

@[simp] theorem foldedSpacingRatio_equispacedTriple
    (origin : ℝ) (step : {x : ℝ // 0 < x}) :
    foldedSpacingRatio (equispacedTriple origin step) = 1 := by
  simp [foldedSpacingRatio]

structure OrderedSpectralQuintuple where
  first : ℝ
  second : ℝ
  third : ℝ
  fourth : ℝ
  fifth : ℝ
  first_lt_second : first < second
  second_lt_third : second < third
  third_lt_fourth : third < fourth
  fourth_lt_fifth : fourth < fifth

/-- Paper's non-overlapping second-order ratio `(λᵢ₊₄-λᵢ₊₂)/(λᵢ₊₂-λᵢ)`. -/
def secondOrderSpacingRatio (Q : OrderedSpectralQuintuple) : ℝ :=
  (Q.fifth - Q.third) / (Q.third - Q.first)

theorem secondOrderSpacingRatio_pos (Q : OrderedSpectralQuintuple) :
    0 < secondOrderSpacingRatio Q := by
  exact div_pos
    (sub_pos.mpr (Q.third_lt_fourth.trans Q.fourth_lt_fifth))
    (sub_pos.mpr (Q.first_lt_second.trans Q.second_lt_third))

def equispacedQuintuple (origin : ℝ) (step : {x : ℝ // 0 < x}) :
    OrderedSpectralQuintuple where
  first := origin
  second := origin + step
  third := origin + 2 * step
  fourth := origin + 3 * step
  fifth := origin + 4 * step
  first_lt_second := by linarith [step.property]
  second_lt_third := by linarith [step.property]
  third_lt_fourth := by linarith [step.property]
  fourth_lt_fifth := by linarith [step.property]

@[simp] theorem secondOrderSpacingRatio_equispacedQuintuple
    (origin : ℝ) (step : {x : ℝ // 0 < x}) :
    secondOrderSpacingRatio (equispacedQuintuple origin step) = 1 := by
  unfold secondOrderSpacingRatio equispacedQuintuple
  field_simp [ne_of_gt step.property]
  ring

/-! Correlation-distance transform from the market application. -/

def CorrelationCoefficient := Set.Icc (-1 : ℝ) 1

def correlationDistance (c : CorrelationCoefficient) : ℝ :=
  Real.sqrt (2 * (1 - (c : ℝ)))

theorem correlationDistance_nonneg (c : CorrelationCoefficient) :
    0 ≤ correlationDistance c := Real.sqrt_nonneg _

theorem correlationDistance_sq (c : CorrelationCoefficient) :
    correlationDistance c ^ (2 : ℕ) = 2 * (1 - (c : ℝ)) := by
  rw [correlationDistance, Real.sq_sqrt]
  linarith [c.property.2]

theorem correlationDistance_le_two (c : CorrelationCoefficient) :
    correlationDistance c ≤ 2 := by
  rw [correlationDistance, Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [c.property.1]

theorem correlationDistance_eq_zero_iff (c : CorrelationCoefficient) :
    correlationDistance c = 0 ↔ (c : ℝ) = 1 := by
  rw [correlationDistance, Real.sqrt_eq_zero']
  constructor
  · intro h
    apply le_antisymm c.property.2
    linarith
  · intro h
    rw [h]
    norm_num

def perfectCorrelation : CorrelationCoefficient := ⟨1, by constructor <;> norm_num⟩
def zeroCorrelation : CorrelationCoefficient := ⟨0, by constructor <;> norm_num⟩
def oppositeCorrelation : CorrelationCoefficient := ⟨-1, by constructor <;> norm_num⟩

@[simp] theorem correlationDistance_perfect : correlationDistance perfectCorrelation = 0 := by
  simp [correlationDistance, perfectCorrelation]

@[simp] theorem correlationDistance_zero : correlationDistance zeroCorrelation = Real.sqrt 2 := by
  simp [correlationDistance, zeroCorrelation]

@[simp] theorem correlationDistance_opposite : correlationDistance oppositeCorrelation = 2 := by
  dsimp [correlationDistance, oppositeCorrelation]
  have hsqrt : Real.sqrt 4 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_nonneg 4]
  convert hsqrt using 1
  norm_num

end

end GaloisForLFunctions.HTGeometry.RandomMixedGraph
