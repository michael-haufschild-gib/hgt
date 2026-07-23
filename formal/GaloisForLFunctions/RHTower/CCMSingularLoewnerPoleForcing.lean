import GaloisForLFunctions.HTGeometry.HermitianLoewnerPoleForcing
import GaloisForLFunctions.RHTower.CCMRadicalQuotientHermitian
import GaloisForLFunctions.RHTower.CCMPositiveResidueCentralSlab
import GaloisForLFunctions.RHTower.CCMPublishedSourceSineCoefficient

/-!
# CCM singular Loewner pole forcing

For the actual active-even CCM completion, each quotient frame column is a resolvent column at its
clock node, and its cross Gram product is the corresponding divided difference of the source.
Consequently, a strict source descent forces a real quotient eigenvalue between the two nodes.

Centered Xi is unconditionally zero-free on `[-4,4]`.  Hence local-uniform convergence of any
normalized active-even CCM quotient determinant to Xi forces eventual source order on every pair
of moving clock nodes in that interval.  Dimensions, radical dimensions, normalization factors,
and selected node pairs may all vary with the stage.  No inverse resolvent, cyclicity, simple
ground state, residue nonvanishing, quantitative estimate, or RH hypothesis is used.
-/

open Complex Filter Metric Set Topology
open scoped Matrix

namespace RHTower

noncomputable section

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- Real metric adjointness preserves the full radical of a split Gram frame. -/
theorem realMetricAdjoint_splitRadical
    (B : Matrix m n ℝ) (A : Matrix n n ℝ) (R : Matrix n m ℝ)
    (hBR : B * R = 1)
    (hmetric : (B.transpose * B) * A = A.transpose * (B.transpose * B)) :
    B * A * (1 - R * B) = 0 := by
  have hRB : R.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, hBR, Matrix.transpose_one]
  have hBP : B * (1 - R * B) = 0 := by
    calc
      B * (1 - R * B) = B - (B * R) * B := by
        rw [Matrix.mul_sub, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBR]; simp
  have hTP : (B.transpose * B) * (1 - R * B) = 0 := by
    rw [Matrix.mul_assoc, hBP, Matrix.mul_zero]
  have hTAP : (B.transpose * B) * A * (1 - R * B) = 0 := by
    rw [hmetric, Matrix.mul_assoc, hTP, Matrix.mul_zero]
  calc
    B * A * (1 - R * B) =
        (1 : Matrix m m ℝ) * (B * A * (1 - R * B)) := by rw [Matrix.one_mul]
    _ = (R.transpose * B.transpose) * (B * A * (1 - R * B)) := by rw [hRB]
    _ = R.transpose * ((B.transpose * B) * A * (1 - R * B)) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hTAP, Matrix.mul_zero]

/-- One active-even CCM clock column is an exact resolvent column of its quotient. -/
theorem ccmActiveEven_singleColumn
    (clock : n → ℝ) (e : n → ℝ) (i : n) :
    ccmEvenBoundaryCompletion (ccmDiagonalClock clock) ccmConstantBoundary e *ᵥ
        Pi.single i 1 =
      clock i • Pi.single i 1 - ccmDiagonalClock clock *ᵥ e := by
  rw [Matrix.mulVec_single_one]
  ext q
  by_cases hqi : q = i
  · subst q
    simp [ccmEvenBoundaryCompletion, ccmDiagonalClock, ccmConstantBoundary,
      Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  · simp [ccmEvenBoundaryCompletion, ccmDiagonalClock, ccmConstantBoundary,
      Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, hqi]

omit [DecidableEq m] in
/-- Cross Gram product of two quotient frame columns is the corresponding semimetric entry. -/
theorem quotientFrameColumn_dotProduct
    (B : Matrix m n ℝ) (T : Matrix n n ℝ) (hGram : B.transpose * B = T)
    (i j : n) :
    (B *ᵥ Pi.single i 1) ⬝ᵥ (B *ᵥ Pi.single j 1) = T i j := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  have h := congr_fun (congr_fun hGram i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, dotProduct] using h

/-- **Finite CCM descent--pole law.**  Active-even source descent between two clock nodes forces a
real zero of the actual radical-quotient characteristic polynomial between those nodes. -/
theorem ccmActiveEven_sourceDescent_forces_quotientCharpoly_zero
    (clock source diagonal : n → ℝ) (e : n → ℝ)
    (hclock : Function.Injective clock)
    (he : ccmDividedDifferenceMatrix clock source diagonal *ᵥ e = 0)
    (heta : ccmConstantBoundary ⬝ᵥ e = 1)
    (hbeta : source ⬝ᵥ e = 0)
    (B : Matrix m n ℝ) (R : Matrix n m ℝ)
    (hBR : B * R = 1)
    (hGram : B.transpose * B = ccmDividedDifferenceMatrix clock source diagonal)
    (i j : n) (hij : i ≠ j) (hclockij : clock i < clock j)
    (hsourceij : source j < source i) :
    ∃ x : ℝ, x ∈ Set.Icc (clock i) (clock j) ∧
      ((realSemimetricQuotientCompression B
          (ccmEvenBoundaryCompletion (ccmDiagonalClock clock) ccmConstantBoundary e) R).map
        (algebraMap ℝ ℂ)).charpoly.eval (x : ℂ) = 0 := by
  let T := ccmDividedDifferenceMatrix clock source diagonal
  let D := ccmDiagonalClock clock
  let A := ccmEvenBoundaryCompletion D ccmConstantBoundary e
  let C := realSemimetricQuotientCompression B A R
  have hdisp : D * T - T * D =
      Matrix.vecMulVec source ccmConstantBoundary -
        Matrix.vecMulVec ccmConstantBoundary source := by
    exact ccmDividedDifference_displacement clock source diagonal hclock
  obtain ⟨hmetricT, _, _⟩ := ccmEvenBoundaryCompletion_active
    T D ccmConstantBoundary source e
      (ccmDividedDifferenceMatrix_transpose clock source diagonal)
      (ccmDiagonalClock_transpose clock) hdisp he heta hbeta
  have hmetricB : (B.transpose * B) * A = A.transpose * (B.transpose * B) := by
    simpa only [T, A, D, hGram] using hmetricT
  have hradical : B * A * (1 - R * B) = 0 :=
    realMetricAdjoint_splitRadical B A R hBR hmetricB
  have hC : C.transpose = C :=
    realSemimetricQuotientCompression_transpose B A R hBR hmetricB
  have hintertwines : C * B = B * A :=
    realSemimetricQuotientCompression_intertwines B A R hradical
  let u : m → ℝ := B *ᵥ (D *ᵥ e)
  let v : m → ℝ := B *ᵥ Pi.single i 1
  let w : m → ℝ := B *ᵥ Pi.single j 1
  have hres (q : n) : C *ᵥ (B *ᵥ Pi.single q 1) =
      clock q • (B *ᵥ Pi.single q 1) - u := by
    calc
      C *ᵥ (B *ᵥ Pi.single q 1) = (C * B) *ᵥ Pi.single q 1 :=
        Matrix.mulVec_mulVec _ _ _
      _ = (B * A) *ᵥ Pi.single q 1 := by rw [hintertwines]
      _ = B *ᵥ (A *ᵥ Pi.single q 1) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = B *ᵥ (clock q • Pi.single q 1 - D *ᵥ e) := by
        rw [ccmActiveEven_singleColumn]
      _ = clock q • (B *ᵥ Pi.single q 1) - u := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hcross : v ⬝ᵥ w < 0 := by
    calc
      v ⬝ᵥ w = T i j := quotientFrameColumn_dotProduct B T hGram i j
      _ = (source i - source j) / (clock i - clock j) := by
        simp [T, ccmDividedDifferenceMatrix, hij]
      _ < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
  have hv : C *ᵥ v = clock i • v - u := hres i
  have hw : C *ᵥ w = clock j • w - u := hres j
  obtain ⟨q, hq⟩ :=
    HTGeometry.exists_eigenvalue_mem_Icc_of_symmetric_resolvent_cross_neg
      C hC u v w hclockij hv hw hcross
  let hHerm : C.IsHermitian := by simpa [Matrix.IsHermitian] using hC
  let x := hHerm.eigenvalues q
  have hx : x ∈ Set.Icc (clock i) (clock j) := by
    simpa [hHerm, x] using hq
  have hrootReal : C.charpoly.eval x = 0 := by
    rw [hHerm.charpoly_eq, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [x]
  have hrootComplex : (C.map (algebraMap ℝ ℂ)).charpoly.eval (x : ℂ) = 0 := by
    rw [Matrix.charpoly_map]
    change Polynomial.eval ((algebraMap ℝ ℂ) x)
      (Polynomial.map (algebraMap ℝ ℂ) C.charpoly) = 0
    rw [Polynomial.eval_map_apply, hrootReal, map_zero]
  exact ⟨x, hx, by simpa [C, A, D] using hrootComplex⟩

/-- **Actual-source one-mode falsifier.**  If one positive physical CCM sine coefficient is
negative, the active-even quotient already has a real characteristic zero between the central
clock node and that frequency.  The source coefficient is the published finite
von-Mangoldt--Gamma functional, not an abstract interpolation datum. -/
theorem ccmActiveEven_negativePublishedSourceCoefficient_forces_quotientCharpoly_zero
    (clock source diagonal : n → ℝ) (e : n → ℝ)
    (hclock : Function.Injective clock)
    (he : ccmDividedDifferenceMatrix clock source diagonal *ᵥ e = 0)
    (heta : ccmConstantBoundary ⬝ᵥ e = 1)
    (hbeta : source ⬝ᵥ e = 0)
    (B : Matrix m n ℝ) (R : Matrix n m ℝ)
    (hBR : B * R = 1)
    (hGram : B.transpose * B = ccmDividedDifferenceMatrix clock source diagonal)
    (central positive : n) (hne : central ≠ positive)
    {a : ℝ} (ha : 0 < a) {mode : ℕ} (hmode : 0 < mode)
    (hclockCentral : clock central = 0)
    (hclockPositive : clock positive = ccmPublishedPhysicalFrequency a mode)
    (hsourceCentral : source central = ccmPublishedSourceSineCoefficient a 0)
    (hsourcePositive : source positive =
      ccmPublishedSourceSineCoefficient a (ccmPublishedPhysicalFrequency a mode))
    (hnegative : ccmPublishedSourceSineCoefficient a
      (ccmPublishedPhysicalFrequency a mode) < 0) :
    ∃ x : ℝ, x ∈ Set.Icc 0 (ccmPublishedPhysicalFrequency a mode) ∧
      ((realSemimetricQuotientCompression B
          (ccmEvenBoundaryCompletion (ccmDiagonalClock clock) ccmConstantBoundary e) R).map
        (algebraMap ℝ ℂ)).charpoly.eval (x : ℂ) = 0 := by
  have hfrequency : 0 < ccmPublishedPhysicalFrequency a mode := by
    rw [ccmPublishedPhysicalFrequency]
    exact div_pos (mul_pos Real.pi_pos (Nat.cast_pos.mpr hmode)) ha
  have hclockOrder : clock central < clock positive := by
    rw [hclockCentral, hclockPositive]
    exact hfrequency
  have hsourceDescent : source positive < source central := by
    rw [hsourcePositive, hsourceCentral,
      ccmPublishedSourceSineCoefficient_zero]
    exact hnegative
  obtain ⟨x, hx, hroot⟩ :=
    ccmActiveEven_sourceDescent_forces_quotientCharpoly_zero
      clock source diagonal e hclock he heta hbeta B R hBR hGram
      central positive hne hclockOrder hsourceDescent
  exact ⟨x, by simpa only [hclockCentral, hclockPositive] using hx, hroot⟩

/-- **Cofinal CCM central-slab order law.**  Any active-even CCM quotient family converging locally
uniformly to centered Xi must eventually preserve source order between every pair of moving clock
nodes in `[-4,4]`. -/
theorem eventually_ccmActiveEven_source_order_on_centralSlab_of_XiC_convergence
    {ambient quotient : ℕ → ℕ}
    (clock source diagonal e : ∀ k, Fin (ambient k) → ℝ)
    (hclock : ∀ k, Function.Injective (clock k))
    (he : ∀ k, ccmDividedDifferenceMatrix (clock k) (source k) (diagonal k) *ᵥ e k = 0)
    (heta : ∀ k, ccmConstantBoundary ⬝ᵥ e k = 1)
    (hbeta : ∀ k, source k ⬝ᵥ e k = 0)
    (B : ∀ k, Matrix (Fin (quotient k)) (Fin (ambient k)) ℝ)
    (R : ∀ k, Matrix (Fin (ambient k)) (Fin (quotient k)) ℝ)
    (hBR : ∀ k, B k * R k = 1)
    (hGram : ∀ k, (B k).transpose * B k =
      ccmDividedDifferenceMatrix (clock k) (source k) (diagonal k))
    (u : ℕ → ℂ → ℂ)
    (hconv : TendstoLocallyUniformly
      (normalizedRealSemimetricQuotientCharpoly ambient quotient B
        (fun k => ccmEvenBoundaryCompletion (ccmDiagonalClock (clock k))
          ccmConstantBoundary (e k)) R u) XiC atTop)
    (left right : ∀ k, Fin (ambient k))
    (hnodes : ∀ᶠ k in atTop,
      -4 ≤ clock k (left k) ∧ clock k (left k) < clock k (right k) ∧
        clock k (right k) ≤ 4) :
    ∀ᶠ k in atTop, source k (left k) ≤ source k (right k) := by
  have hzeroFree :=
    eventually_forall_ne_zero_closedBall_four_of_tendstoLocallyUniformly_XiC hconv
  filter_upwards [hzeroFree, hnodes] with k hfree hnode
  obtain ⟨hleftBound, hleftRight, hrightBound⟩ := hnode
  by_contra horder
  push Not at horder
  have hij : left k ≠ right k := fun hij =>
    (ne_of_lt hleftRight) (congrArg (clock k) hij)
  obtain ⟨x, hx, hroot⟩ :=
    ccmActiveEven_sourceDescent_forces_quotientCharpoly_zero
      (clock k) (source k) (diagonal k) (e k) (hclock k)
      (he k) (heta k) (hbeta k) (B k) (R k) (hBR k) (hGram k)
      (left k) (right k) hij hleftRight horder
  have hxMem : (x : ℂ) ∈ closedBall (0 : ℂ) 4 := by
    rw [mem_closedBall, dist_zero_right]
    have hxBounds : -4 ≤ x ∧ x ≤ 4 :=
      ⟨hleftBound.trans hx.1, hx.2.trans hrightBound⟩
    simpa only [norm_real, Real.norm_eq_abs] using abs_le.mpr hxBounds
  apply hfree (x : ℂ) hxMem
  simp only [normalizedRealSemimetricQuotientCharpoly, hroot, mul_zero]

/-- **Published CCM central-mode sign law.**  Specializing the moving-node order theorem to the
central clock and one positive physical frequency shows that local-uniform convergence to Xi
forces the corresponding explicit von-Mangoldt--Gamma source coefficient to be eventually
nonnegative.  Apertures and positive modes may both move. -/
theorem eventually_ccmPublishedSourceSineCoefficient_nonneg_of_XiC_convergence
    {ambient quotient : ℕ → ℕ}
    (clock source diagonal e : ∀ k, Fin (ambient k) → ℝ)
    (hclock : ∀ k, Function.Injective (clock k))
    (he : ∀ k, ccmDividedDifferenceMatrix (clock k) (source k) (diagonal k) *ᵥ e k = 0)
    (heta : ∀ k, ccmConstantBoundary ⬝ᵥ e k = 1)
    (hbeta : ∀ k, source k ⬝ᵥ e k = 0)
    (B : ∀ k, Matrix (Fin (quotient k)) (Fin (ambient k)) ℝ)
    (R : ∀ k, Matrix (Fin (ambient k)) (Fin (quotient k)) ℝ)
    (hBR : ∀ k, B k * R k = 1)
    (hGram : ∀ k, (B k).transpose * B k =
      ccmDividedDifferenceMatrix (clock k) (source k) (diagonal k))
    (u : ℕ → ℂ → ℂ)
    (hconv : TendstoLocallyUniformly
      (normalizedRealSemimetricQuotientCharpoly ambient quotient B
        (fun k => ccmEvenBoundaryCompletion (ccmDiagonalClock (clock k))
          ccmConstantBoundary (e k)) R u) XiC atTop)
    (a : ℕ → ℝ) (mode : ℕ → ℕ)
    (ha : ∀ k, 0 < a k) (hmode : ∀ k, 0 < mode k)
    (central positive : ∀ k, Fin (ambient k))
    (hclockCentral : ∀ k, clock k (central k) = 0)
    (hclockPositive : ∀ k, clock k (positive k) =
      ccmPublishedPhysicalFrequency (a k) (mode k))
    (hsourceCentral : ∀ k, source k (central k) =
      ccmPublishedSourceSineCoefficient (a k) 0)
    (hsourcePositive : ∀ k, source k (positive k) =
      ccmPublishedSourceSineCoefficient (a k)
        (ccmPublishedPhysicalFrequency (a k) (mode k)))
    (hslab : ∀ᶠ k in atTop,
      ccmPublishedPhysicalFrequency (a k) (mode k) ≤ 4) :
    ∀ᶠ k in atTop, 0 ≤ ccmPublishedSourceSineCoefficient (a k)
      (ccmPublishedPhysicalFrequency (a k) (mode k)) := by
  have hnodes : ∀ᶠ k in atTop,
      -4 ≤ clock k (central k) ∧ clock k (central k) < clock k (positive k) ∧
        clock k (positive k) ≤ 4 := by
    filter_upwards [hslab] with k hk
    have hfrequency : 0 < ccmPublishedPhysicalFrequency (a k) (mode k) := by
      rw [ccmPublishedPhysicalFrequency]
      exact div_pos (mul_pos Real.pi_pos (Nat.cast_pos.mpr (hmode k))) (ha k)
    rw [hclockCentral, hclockPositive]
    exact ⟨by norm_num, hfrequency, hk⟩
  have horder :=
    eventually_ccmActiveEven_source_order_on_centralSlab_of_XiC_convergence
      clock source diagonal e hclock he heta hbeta B R hBR hGram u hconv
      central positive hnodes
  filter_upwards [horder] with k hk
  rw [hsourceCentral, hsourcePositive,
    ccmPublishedSourceSineCoefficient_zero] at hk
  exact hk

end

end RHTower
