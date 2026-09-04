import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCuspScaledEnergy
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanRationalDeterminantProfile
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanFiniteCuspShortVectorScalar
import GaloisForLFunctions.HTGeometry.NumberFieldUnitPositiveWeightBalancing
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanBalancedMean

/-!
# Uniform height at the finite rank-two cusps

Determinant-root Minkowski reduction supplies a short integral vector.  Finite projective cusp
classification transports that vector to one fixed representative, while the product formula
prevents its projective scalar from collapsing.  Weighted AM--GM and the exact canonical
determinant formula then give a field-uniform bound for the adjacent Jacobi-weight means.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Weighted AM--GM converts scalar-cusp energy into a lower bound for the head-weight mean. -/
theorem exp_headWeightMean_add_two_scalarMean_le_cuspEnergy
    (v : Fin 2 → K) (hv : v ≠ 0)
    (B : numberFieldArchimedeanPositiveForms K 2)
    (J : NumberFieldArchimedeanJacobiData
      (numberFieldRankTwoCuspChart v hv B))
    (s : K) (hs : s ≠ 0) :
    Real.exp (
        numberFieldWeightedPlaceMean
          (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w)) +
        2 * numberFieldWeightedPlaceMean (fun w ↦ Real.log (w s))) ≤
      numberFieldArchimedeanEnergy B
        (numberFieldVectorEmbedding (fun i => s * v i)) := by
  let a : InfinitePlace K → ℝ := fun w =>
    numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w * (w s) ^ 2
  have hws (w : InfinitePlace K) : 0 < w s := by
    rw [InfinitePlace.pos_iff]
    exact hs
  have ha (w : InfinitePlace K) : 0 < a w := by
    exact mul_pos (numberFieldArchimedeanJacobiWeight_pos J _ w)
      (sq_pos_of_pos (hws w))
  have hmean :
      numberFieldWeightedPlaceMean (fun w ↦ Real.log (a w)) =
        numberFieldWeightedPlaceMean
            (fun w ↦ Real.log (numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w)) +
          2 * numberFieldWeightedPlaceMean (fun w ↦ Real.log (w s)) := by
    calc
      numberFieldWeightedPlaceMean (fun w ↦ Real.log (a w)) =
          numberFieldWeightedPlaceMean (fun w ↦
            Real.log (numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w) +
              2 * Real.log (w s)) := by
        apply congrArg numberFieldWeightedPlaceMean
        funext w
        dsimp [a]
        rw [Real.log_mul
          (numberFieldArchimedeanJacobiWeight_pos J _ w).ne'
          (sq_pos_of_pos (hws w)).ne', Real.log_pow]
        norm_num
      _ = _ := by
        rw [numberFieldWeightedPlaceMean_add,
          numberFieldWeightedPlaceMean_mul]
  rw [← hmean]
  rw [numberFieldRankTwoCuspChart_scaled_energy_eq_weight_sum v hv B J s]
  exact exp_numberFieldWeightedPlaceMean_log_le_sum a ha

/-- Every rank-two archimedean form has an integral translate whose chart at one of the finite
cusp representatives has a uniformly bounded adjacent weighted Jacobi mean. -/
theorem exists_uniform_numberFieldArchimedean_finiteCusp_headMeanRatio
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ A : numberFieldArchimedeanPositiveForms K 2,
      ∃ c : numberFieldRankTwoCuspType K,
        ∃ h : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K),
          ∃ J : NumberFieldArchimedeanJacobiData
              (numberFieldRankTwoCuspChart
                (numberFieldRankTwoCuspRepresentative K c).1
                (numberFieldRankTwoCuspRepresentative K c).2 (h • A)),
            numberFieldWeightedPlaceMean (fun w ↦ Real.log
                (numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w)) -
              numberFieldWeightedPlaceMean (fun w ↦ Real.log
                (numberFieldArchimedeanJacobiWeight J (1 : Fin 2) w)) ≤ C := by
  obtain ⟨R, hR, hshort⟩ :=
    exists_uniform_numberFieldArchimedean_finiteCuspShortVector_scalarProduct K
  let q : ℝ :=
    ((2 * Module.finrank ℚ K : ℕ) : ℝ) * R ^ 2 *
      Real.exp
        (Real.log ((numberFieldArchimedeanSquareCoordinateMatrix
          (K := K) (n := 2)).det ^ 2) *
          (((2 * Module.finrank ℚ K : ℕ) : ℝ)⁻¹))
  let cuspBound : ℝ := ∑ c : numberFieldRankTwoCuspType K,
    |numberFieldWeightedPlaceMean (fun w ↦ Real.log
      (w ((numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentativeIndex c))))|
  have hd : (0 : ℝ) < Module.finrank ℚ K := by
    rw [← numberFieldInfinitePlaceWeight_eq_finrank (K := K)]
    exact numberFieldInfinitePlaceWeight_pos (K := K)
  have htwoDegree : (0 : ℝ) < ((2 * Module.finrank ℚ K : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega)
      (by exact_mod_cast hd : 0 < Module.finrank ℚ K)
  have hq : 0 < q := by
    dsimp [q]
    exact mul_pos (mul_pos htwoDegree (sq_pos_of_pos hR)) (Real.exp_pos _)
  refine ⟨2 * Real.log q + 4 * cuspBound, ?_⟩
  intro A
  obtain ⟨a, ha, henergy, c, g, scalar, hscalar, hmap, hscalarMean⟩ := hshort A
  let beta : Matrix (Fin 2) (Fin 2) (𝓞 K) :=
    (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K))
  have hbeta : beta.det = 1 := by
    exact Matrix.SpecialLinearGroup.det_coe (g⁻¹)
  let h : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K) :=
    transposeSpecialLinearOfDetOne beta hbeta
  let b : Fin 2 → 𝓞 K :=
    (g : Matrix (Fin 2) (Fin 2) (𝓞 K)).mulVec a
  have hbeta_b : beta.mulVec b = a := by
    change ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (𝓞 K)) :
      Matrix (Fin 2) (Fin 2) (𝓞 K)).mulVec
        ((g : Matrix (Fin 2) (Fin 2) (𝓞 K)).mulVec a) = a
    rw [Matrix.mulVec_mulVec]
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    simp
  have hbcast (i : Fin 2) : (b i : K) =
      scalar * (numberFieldRankTwoCuspRepresentative K c).1 i := by
    dsimp [b]
    rw [numberFieldRankTwoMatrixBaseChange_mulVec_integer]
    exact hmap i
  have hbembed : numberFieldIntegerVectorEmbedding K b =
      numberFieldVectorEmbedding
        (fun i => scalar * (numberFieldRankTwoCuspRepresentative K c).1 i) := by
    funext i
    change mixedEmbedding K (b i : K) = mixedEmbedding K
      (scalar * (numberFieldRankTwoCuspRepresentative K c).1 i)
    rw [hbcast i]
  have henergyTransport :
      numberFieldArchimedeanEnergy (h • A)
          (numberFieldVectorEmbedding
            (fun i => scalar * (numberFieldRankTwoCuspRepresentative K c).1 i)) =
        numberFieldArchimedeanEnergy A
          (numberFieldIntegerVectorEmbedding K a) := by
    rw [← hbembed]
    simpa [h, hbeta_b] using
      numberFieldArchimedeanEnergy_transposeSpecialLinear beta hbeta A b
  let J : NumberFieldArchimedeanJacobiData
      (numberFieldRankTwoCuspChart
        (numberFieldRankTwoCuspRepresentative K c).1
        (numberFieldRankTwoCuspRepresentative K c).2 (h • A)) :=
    Classical.choice (exists_numberFieldArchimedeanJacobiData _)
  refine ⟨c, h, J, ?_⟩
  let headMean : ℝ := numberFieldWeightedPlaceMean (fun w ↦ Real.log
    (numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w))
  let tailMean : ℝ := numberFieldWeightedPlaceMean (fun w ↦ Real.log
    (numberFieldArchimedeanJacobiWeight J (1 : Fin 2) w))
  let detMean : ℝ := numberFieldWeightedPlaceMean (fun w ↦ Real.log
    (numberFieldArchimedeanDet A w))
  let scalarMean : ℝ := numberFieldWeightedPlaceMean
    (fun w ↦ Real.log (w scalar))
  let repMean : ℝ := numberFieldWeightedPlaceMean (fun w ↦ Real.log
    (w ((numberFieldRankTwoCuspRepresentative K c).1
      (numberFieldRankTwoCuspRepresentativeIndex c))))
  have hshort' :
      numberFieldArchimedeanEnergy A
          (numberFieldIntegerVectorEmbedding K a) ≤
        q * Real.exp ((1 / 2 : ℝ) * detMean) := by
    rw [rpow_numberFieldArchimedeanCanonicalMatrix_rankTwo] at henergy
    simpa [q, detMean, mul_assoc] using henergy
  have hAM : Real.exp (headMean + 2 * scalarMean) ≤
      numberFieldArchimedeanEnergy (h • A)
        (numberFieldVectorEmbedding
          (fun i => scalar * (numberFieldRankTwoCuspRepresentative K c).1 i)) := by
    exact exp_headWeightMean_add_two_scalarMean_le_cuspEnergy
      (numberFieldRankTwoCuspRepresentative K c).1
      (numberFieldRankTwoCuspRepresentative K c).2 (h • A) J scalar hscalar
  have htotal : Real.exp (headMean + 2 * scalarMean) ≤
      q * Real.exp ((1 / 2 : ℝ) * detMean) := by
    exact hAM.trans (henergyTransport.le.trans hshort')
  have hscalarMean' : -repMean ≤ scalarMean := by
    exact hscalarMean
  have hlower : Real.exp (headMean - 2 * repMean) ≤
      Real.exp (headMean + 2 * scalarMean) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hright : q * Real.exp ((1 / 2 : ℝ) * detMean) =
      Real.exp (Real.log q + (1 / 2 : ℝ) * detMean) := by
    rw [Real.exp_add, Real.exp_log hq]
  have hlogBound : headMean - 2 * repMean ≤
      Real.log q + (1 / 2 : ℝ) * detMean := by
    apply Real.exp_le_exp.mp
    rw [← hright]
    exact hlower.trans htotal
  have hdetProfile (w : InfinitePlace K) :
      numberFieldArchimedeanDet
          (numberFieldRankTwoCuspChart
            (numberFieldRankTwoCuspRepresentative K c).1
            (numberFieldRankTwoCuspRepresentative K c).2 (h • A)) w =
        numberFieldArchimedeanDet A w := by
    rw [numberFieldArchimedeanDet_cuspChart,
      numberFieldArchimedeanDet_smul]
  have hdetMean : headMean + tailMean = detMean := by
    have hlocal (w : InfinitePlace K) :
        Real.log (numberFieldArchimedeanJacobiWeight J (0 : Fin 2) w) +
            Real.log (numberFieldArchimedeanJacobiWeight J (1 : Fin 2) w) =
          Real.log (numberFieldArchimedeanDet A w) := by
      rw [← hdetProfile w]
      simpa [Fin.sum_univ_two] using
        sum_log_numberFieldArchimedeanJacobiWeight J w
    dsimp [headMean, tailMean, detMean]
    rw [← numberFieldWeightedPlaceMean_add]
    apply congrArg numberFieldWeightedPlaceMean
    funext w
    exact hlocal w
  have hrep : repMean ≤ cuspBound := by
    calc
      repMean ≤ |repMean| := le_abs_self _
      _ ≤ cuspBound := by
        exact Finset.single_le_sum
          (fun d _ ↦ abs_nonneg (numberFieldWeightedPlaceMean (fun w ↦ Real.log
            (w ((numberFieldRankTwoCuspRepresentative K d).1
              (numberFieldRankTwoCuspRepresentativeIndex d))))))
          (Finset.mem_univ c)
  dsimp [headMean, tailMean]
  dsimp [headMean, tailMean] at hdetMean hlogBound
  dsimp [repMean, cuspBound] at hrep
  linarith

end

end GaloisForLFunctions.HTGeometry
