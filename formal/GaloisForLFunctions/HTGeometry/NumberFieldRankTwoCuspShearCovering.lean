import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanFiniteCuspBalancedSiegel
import GaloisForLFunctions.HTGeometry.NumberFieldIntegerCoveringRadius

/-!
# Covering radii for rank-two cusp-relative shear lattices

For a rank-two cusp with coordinate ideal `I`, conjugating an upper shear through its pseudo-basis
frame is integral exactly when its coefficient lies in `I⁻²`.  The finite cusp family therefore
has a uniform archimedean covering radius for the required shear coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder Matrix NumberField BigOperators

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Fractional ideal of coefficients for cusp-relative upper shears. -/
def numberFieldRankTwoCuspShearIdeal
    (c : numberFieldRankTwoCuspType K) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  let I := numberFieldRankTwoCoordinateIdealUnit K v hv
  ↑(I⁻¹ * I⁻¹)

private theorem numberFieldRankTwoCuspShearIdeal_ne_bot
    (c : numberFieldRankTwoCuspType K) :
    (↑(numberFieldRankTwoCuspShearIdeal c) : Submodule (𝓞 K) K) ≠ ⊥ := by
  intro hbot
  have hzero : numberFieldRankTwoCuspShearIdeal c = 0 :=
    FractionalIdeal.coeToSubmodule_eq_bot.mp hbot
  let v := (numberFieldRankTwoCuspRepresentative K c).1
  let hv := (numberFieldRankTwoCuspRepresentative K c).2
  let I := numberFieldRankTwoCoordinateIdealUnit K v hv
  have hunit : (↑(I⁻¹ * I⁻¹) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := Units.ne_zero _
  exact hunit hzero

/-- A fixed nonzero member of each cusp-relative shear ideal. -/
def numberFieldRankTwoCuspShearMember
    (c : numberFieldRankTwoCuspType K) : K :=
  Classical.choose (Submodule.exists_mem_ne_zero_of_ne_bot
    (numberFieldRankTwoCuspShearIdeal_ne_bot c))

theorem numberFieldRankTwoCuspShearMember_mem
    (c : numberFieldRankTwoCuspType K) :
    numberFieldRankTwoCuspShearMember c ∈ numberFieldRankTwoCuspShearIdeal c :=
  (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
    (numberFieldRankTwoCuspShearIdeal_ne_bot c))).1

theorem numberFieldRankTwoCuspShearMember_ne_zero
    (c : numberFieldRankTwoCuspType K) :
    numberFieldRankTwoCuspShearMember c ≠ 0 :=
  (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot
    (numberFieldRankTwoCuspShearIdeal_ne_bot c))).2

/-- Archimedean expansion factor of the chosen shear-ideal member. -/
def numberFieldRankTwoCuspShearMemberScale
    (c : numberFieldRankTwoCuspType K) : ℝ :=
  (∑ w : {w : InfinitePlace K // w.IsReal},
      |w.1.embedding_of_isReal w.2 (numberFieldRankTwoCuspShearMember c)|) +
    ∑ w : {w : InfinitePlace K // w.IsComplex},
      ‖w.1.embedding (numberFieldRankTwoCuspShearMember c)‖

theorem numberFieldRankTwoCuspShearMemberScale_nonneg
    (c : numberFieldRankTwoCuspType K) :
    0 ≤ numberFieldRankTwoCuspShearMemberScale c := by
  unfold numberFieldRankTwoCuspShearMemberScale
  positivity

/-- One constant simultaneously approximates arbitrary mixed coordinates by elements of every
finite cusp's shear ideal. -/
theorem exists_uniform_numberFieldRankTwoCuspShearIdeal_coordinateCoveringRadius
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : numberFieldRankTwoCuspType K)
      (x : mixedEmbedding.mixedSpace K),
      ∃ a : K, a ∈ numberFieldRankTwoCuspShearIdeal c ∧
        (∀ w : {w : InfinitePlace K // w.IsReal},
          |x.1 w - w.1.embedding_of_isReal w.2 a| ≤ C) ∧
        ∀ w : {w : InfinitePlace K // w.IsComplex},
          ‖x.2 w - w.1.embedding a‖ ≤ C := by
  obtain ⟨R, hR, hcover⟩ :=
    exists_numberFieldInteger_coordinateCoveringRadius K
  let S : ℝ := ∑ c : numberFieldRankTwoCuspType K,
    numberFieldRankTwoCuspShearMemberScale c
  have hS : 0 ≤ S := Finset.sum_nonneg fun c _ =>
    numberFieldRankTwoCuspShearMemberScale_nonneg c
  refine ⟨S * R, mul_nonneg hS hR, ?_⟩
  intro c x
  let z : K := numberFieldRankTwoCuspShearMember c
  have hz : z ≠ 0 := numberFieldRankTwoCuspShearMember_ne_zero c
  let y : mixedEmbedding.mixedSpace K :=
    (fun w => x.1 w / w.1.embedding_of_isReal w.2 z,
      fun w => x.2 w / w.1.embedding z)
  obtain ⟨b, hbreal, hbcomplex⟩ := hcover y
  let a : K := z * (b : K)
  have ha : a ∈ numberFieldRankTwoCuspShearIdeal c := by
    have hzmem : z ∈ numberFieldRankTwoCuspShearIdeal c := by
      exact numberFieldRankTwoCuspShearMember_mem c
    have hsmul := Submodule.smul_mem
      (↑(numberFieldRankTwoCuspShearIdeal c) : Submodule (𝓞 K) K) b hzmem
    change z * (b : K) ∈
      (↑(numberFieldRankTwoCuspShearIdeal c) : Submodule (𝓞 K) K)
    rw [mul_comm]
    exact hsmul
  refine ⟨a, ha, ?_, ?_⟩
  · intro w
    have hzw : w.1.embedding_of_isReal w.2 z ≠ 0 := by
      exact (map_ne_zero (w.1.embedding_of_isReal w.2)).2 hz
    have hzScale :
        |w.1.embedding_of_isReal w.2 z| ≤
          numberFieldRankTwoCuspShearMemberScale c := by
      unfold numberFieldRankTwoCuspShearMemberScale
      dsimp [z]
      have hsingle :
          |w.1.embedding_of_isReal w.2
              (numberFieldRankTwoCuspShearMember c)| ≤
            ∑ q : {q : InfinitePlace K // q.IsReal},
              |q.1.embedding_of_isReal q.2
                (numberFieldRankTwoCuspShearMember c)| :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun q : {q : InfinitePlace K // q.IsReal} =>
            |q.1.embedding_of_isReal q.2
              (numberFieldRankTwoCuspShearMember c)|)
          (fun q _ => abs_nonneg _) (Finset.mem_univ w)
      exact hsingle.trans (le_add_of_nonneg_right
        (Finset.sum_nonneg fun q _ => norm_nonneg _))
    have hcScale : numberFieldRankTwoCuspShearMemberScale c ≤ S := by
      exact Finset.single_le_sum
        (fun d _ => numberFieldRankTwoCuspShearMemberScale_nonneg d)
        (Finset.mem_univ c)
    have heq :
        x.1 w - w.1.embedding_of_isReal w.2 a =
          w.1.embedding_of_isReal w.2 z *
            (y.1 w - w.1.embedding_of_isReal w.2 (b : K)) := by
      dsimp [a, y]
      rw [map_mul]
      field_simp [hzw]
    rw [heq, abs_mul]
    exact mul_le_mul (hzScale.trans hcScale) (hbreal w) (abs_nonneg _) hS
  · intro w
    have hzw : w.1.embedding z ≠ 0 := by
      exact (map_ne_zero w.1.embedding).2 hz
    have hzScale :
        ‖w.1.embedding z‖ ≤ numberFieldRankTwoCuspShearMemberScale c := by
      unfold numberFieldRankTwoCuspShearMemberScale
      dsimp [z]
      have hsingle :
          ‖w.1.embedding (numberFieldRankTwoCuspShearMember c)‖ ≤
            ∑ q : {q : InfinitePlace K // q.IsComplex},
              ‖q.1.embedding (numberFieldRankTwoCuspShearMember c)‖ :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun q : {q : InfinitePlace K // q.IsComplex} =>
            ‖q.1.embedding (numberFieldRankTwoCuspShearMember c)‖)
          (fun q _ => norm_nonneg _) (Finset.mem_univ w)
      exact hsingle.trans (le_add_of_nonneg_left
        (Finset.sum_nonneg fun q _ => abs_nonneg _))
    have hcScale : numberFieldRankTwoCuspShearMemberScale c ≤ S := by
      exact Finset.single_le_sum
        (fun d _ => numberFieldRankTwoCuspShearMemberScale_nonneg d)
        (Finset.mem_univ c)
    have heq :
        x.2 w - w.1.embedding a =
          w.1.embedding z * (y.2 w - w.1.embedding (b : K)) := by
      dsimp [a, y]
      rw [map_mul]
      field_simp [hzw]
    rw [heq, norm_mul]
    exact mul_le_mul (hzScale.trans hcScale) (hbcomplex w) (norm_nonneg _) hS

end

end GaloisForLFunctions.HTGeometry
