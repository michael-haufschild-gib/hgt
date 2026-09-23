import GaloisForLFunctions.RHTower.ChenGuptaLiAffinePoisson
import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothBumpBoundary
import GaloisForLFunctions.RHTower.ChenGuptaLiWeightedHilbertSchmidt

open Matrix
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The literal finite index block in CGL's character matrix: `N < n ≤ 2N`. -/
def cglCharacterDyadicBlock (N : CGLPositiveLength) : Finset ℕ :=
  Finset.Ioc N.value (2 * N.value)

/-- The `Fin N` matrix columns enumerate the source interval `(N, 2N]` exactly. -/
theorem cglCharacterDyadicBlock_eq_image_index (N : CGLPositiveLength) :
    cglCharacterDyadicBlock N =
      (Finset.univ : Finset (Fin N.value)).image (cglCharacterDyadicIndex N.value) := by
  classical
  ext n
  simp only [cglCharacterDyadicBlock, Finset.mem_Ioc, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlo, hhi⟩
    let j : Fin N.value := ⟨n - N.value - 1, by omega⟩
    refine ⟨j, ?_⟩
    dsimp [cglCharacterDyadicIndex, j]
    omega
  · rintro ⟨j, rfl⟩
    constructor
    · simp [cglCharacterDyadicIndex]
    · simp [cglCharacterDyadicIndex]
      omega

/-- Closed finite reindexing from CGL's matrix columns to the source dyadic interval. -/
theorem cglCharacterDyadicBlock_sum_eq_sum_fin
    {A : Type*} [AddCommMonoid A] (N : CGLPositiveLength) (F : ℕ → A) :
    ∑ n ∈ cglCharacterDyadicBlock N, F n =
      ∑ j : Fin N.value, F (cglCharacterDyadicIndex N.value j) := by
  classical
  rw [cglCharacterDyadicBlock_eq_image_index]
  apply Finset.sum_image
  intro i _ j _ hij
  apply Fin.ext
  simp only [cglCharacterDyadicIndex] at hij
  omega

/-- The CGL cutoff weight on a matrix column. -/
def cglSmoothBumpDyadicWeight (w : CGLSmoothBump) (N : CGLPositiveLength)
    (j : Fin N.value) : ℂ :=
  w.value ((cglCharacterDyadicIndex N.value j : ℝ) / N.value)

/-- Unit-supported squared CGL cutoff mass on the finite character-matrix columns. -/
def cglSmoothBumpDyadicUnitWeightMass (w : CGLSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) : ℝ :=
  ∑ j : Fin N.value, ‖cglSmoothBumpDyadicWeight w N j‖ ^ (2 : ℕ) *
    cglCharacterDyadicUnitSupport N.value Q.value j

/-- The finite CGL column mass is literally the coprime sum over `(N,2N]`. -/
theorem cglSmoothBumpDyadicUnitWeightMass_eq_dyadicCoprimeSum
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) :
    cglSmoothBumpDyadicUnitWeightMass w N Q =
      ∑ n ∈ cglCharacterDyadicBlock N,
        ‖w.value ((n : ℝ) / N.value)‖ ^ (2 : ℕ) *
          if n.Coprime Q.value then 1 else 0 := by
  unfold cglSmoothBumpDyadicUnitWeightMass
  simp only [cglSmoothBumpDyadicWeight, cglCharacterDyadicUnitSupport,
    ZMod.isUnit_iff_coprime]
  exact (cglCharacterDyadicBlock_sum_eq_sum_fin N
    (fun n => ‖w.value ((n : ℝ) / N.value)‖ ^ (2 : ℕ) *
      if n.Coprime Q.value then 1 else 0)).symm

/-- CGL's weighted Hilbert--Schmidt mass in literal source dyadic notation. -/
theorem cglSmoothBumpDyadicWeighted_hilbertSchmidtMass_eq_card_mul_dyadicCoprimeSum
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    cglCharacterDyadicWeightedHilbertSchmidtMass N.value Q.value R
      (cglSmoothBumpDyadicWeight w N) rows =
      (R : ℝ) * ∑ n ∈ cglCharacterDyadicBlock N,
        ‖w.value ((n : ℝ) / N.value)‖ ^ (2 : ℕ) *
          if n.Coprime Q.value then 1 else 0 := by
  calc
    cglCharacterDyadicWeightedHilbertSchmidtMass N.value Q.value R
        (cglSmoothBumpDyadicWeight w N) rows =
        (R : ℝ) * cglSmoothBumpDyadicUnitWeightMass w N Q := by
      rw [cglCharacterDyadicWeighted_hilbertSchmidtMass_eq_card_mul_unitWeightMass]
      rfl
    _ = _ := by rw [cglSmoothBumpDyadicUnitWeightMass_eq_dyadicCoprimeSum]

/-- The finite matrix side of CGL Lemma 4.4 in source dyadic-coprime notation. -/
theorem cglSmoothBumpDyadicWeighted_trace_self_mul_conjTranspose_re_eq_card_mul_dyadicCoprimeSum
    (w : CGLSmoothBump) (N : CGLPositiveLength) (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :
    ((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
      (cglSmoothBumpDyadicWeight w N) rows *
      (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w N) rows)ᴴ).trace).re =
      (R : ℝ) * ∑ n ∈ cglCharacterDyadicBlock N,
        ‖w.value ((n : ℝ) / N.value)‖ ^ (2 : ℕ) *
          if n.Coprime Q.value then 1 else 0 := by
  calc
    ((cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
        (cglSmoothBumpDyadicWeight w N) rows *
        (cglCharacterDyadicWeightedEvaluationMatrix N.value Q.value R
          (cglSmoothBumpDyadicWeight w N) rows)ᴴ).trace).re =
        cglCharacterDyadicWeightedHilbertSchmidtMass N.value Q.value R
          (cglSmoothBumpDyadicWeight w N) rows :=
      cglCharacterDyadicWeighted_trace_self_mul_conjTranspose_re_eq_hilbertSchmidtMass
        N.value Q.value R (cglSmoothBumpDyadicWeight w N) rows
    _ = _ := cglSmoothBumpDyadicWeighted_hilbertSchmidtMass_eq_card_mul_dyadicCoprimeSum
      w N Q R rows

end RHTower
