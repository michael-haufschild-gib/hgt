import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartDifferential

/-! On a common affine chart, normalizing the homogeneous diagonal
equations changes their generators by a unit of the tensor chart ring. -/

noncomputable section

open GlobalTheory.WH.WeightedChartSystem
open scoped TensorProduct

namespace GlobalTheory.PD

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  {d : ℕ} {x : Fin (d + 1) → F} {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)}

local notation "R" => tensorChartRing (rA k x I) (rA k x J)

/-- A left coordinate ratio embedded in the tensor of the chart rings. -/
def chartLeftCoordinate (hi : i ∈ I) (l : Fin (d + 1)) : R :=
  tensorChartRingEquiv (rA k x I) (rA k x J)
    ((⟨x l / x i, Algebra.subset_adjoin ⟨i, hi, l, rfl⟩⟩ : rA k x I) ⊗ₜ[k] (1 : rA k x J))

theorem chartLeftCoordinate_coe (hi : i ∈ I) (l : Fin (d + 1)) :
    (chartLeftCoordinate (k := k) (x := x) (J := J) hi l : F ⊗[k] F) =
      (x l / x i) ⊗ₜ[k] (1 : F) := by
  let u : rA k x I := ⟨x l / x i, Algebra.subset_adjoin ⟨i, hi, l, rfl⟩⟩
  change Algebra.TensorProduct.map (rA k x I).val (rA k x J).val (u ⊗ₜ[k] (1 : rA k x J)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- A right coordinate ratio embedded in the tensor of the chart rings. -/
def chartRightCoordinate (hj : j ∈ J) (l : Fin (d + 1)) : R :=
  tensorChartRingEquiv (rA k x I) (rA k x J)
    ((1 : rA k x I) ⊗ₜ[k] (⟨x l / x j, Algebra.subset_adjoin ⟨j, hj, l, rfl⟩⟩ : rA k x J))

theorem chartRightCoordinate_coe (hj : j ∈ J) (l : Fin (d + 1)) :
    (chartRightCoordinate (k := k) (x := x) (I := I) hj l : F ⊗[k] F) =
      (1 : F) ⊗ₜ[k] (x l / x j) := by
  let u : rA k x J := ⟨x l / x j, Algebra.subset_adjoin ⟨j, hj, l, rfl⟩⟩
  change Algebra.TensorProduct.map (rA k x I).val (rA k x J).val ((1 : rA k x I) ⊗ₜ[k] u) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

variable {E : Type} [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  (h : IsPd k x) (p q : ℕ)

/-- The normalized weights selected by the right denominator. -/
def normalizedDiagonalWeights (hi : i ∈ I) (hj : j ∈ J) (l : Fin d) : R :=
  let T := diagonalChartSystem (E := E) h p q
  ⟨T.normalizedWeight (fun _ => (1, 1)) (diagonalMinor (E := E) h p q) i j (diagonalIndexEmbedding j l),
    T.normalizedWeight_mem (diagonalChartSystem_good (E := E) h p q)
      (diagonalChartSystem_admitted (E := E) h p q) hi hj (diagonalIndexEmbedding j l)⟩

/-- On a pair sharing the right denominator chart, the normalized
weights generate precisely the multiplication kernel. -/
theorem normalizedDiagonalWeights_span (hi : i ∈ I) (hj : j ∈ J) (hjI : j ∈ I) :
    Ideal.span (Set.range (normalizedDiagonalWeights (E := E) h p q hi hj)) =
      RingHom.ker (tensorChartRingDiagonal (rA k x I) (rA k x J)).toRingHom := by
  let a : R := chartLeftCoordinate hi j
  let b : R := chartLeftCoordinate hjI i
  have hab : b * a = 1 := by
    apply Subtype.ext
    change (b : F ⊗[k] F) * (a : F ⊗[k] F) = 1
    rw [show (b : F ⊗[k] F) = (x i / x j) ⊗ₜ[k] (1 : F) from chartLeftCoordinate_coe hjI i,
      show (a : F ⊗[k] F) = (x j / x i) ⊗ₜ[k] (1 : F) from chartLeftCoordinate_coe hi j,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_mul_div_cancel₀ (h.ne j),
      div_self (h.ne i), ← Algebra.TensorProduct.one_def]
  let z := h.chartDiagonalGenerators hjI hj
  let r := normalizedDiagonalWeights (E := E) h p q hi hj
  have he (l : Fin d) : r l = a * z l := by
    apply Subtype.ext
    change (r l : F ⊗[k] F) = (a : F ⊗[k] F) * (z l : F ⊗[k] F)
    rw [show (a : F ⊗[k] F) = (x j / x i) ⊗ₜ[k] (1 : F) from chartLeftCoordinate_coe hi j]
    exact diagonalMinor_normalized_of_common (E := E) h p q i j hjI hj l
  have he' (l : Fin d) : z l = b * r l := by rw [he, ← mul_assoc, hab, one_mul]
  rw [(h.chartDiagonalGenerators_regular_kernel hjI hj).2]
  change Ideal.span (Set.range r) = Ideal.span (Set.range z)
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨l, rfl⟩
    rw [he]
    exact (Ideal.span (Set.range z)).mul_mem_left _ (Ideal.subset_span ⟨l, rfl⟩)
  · rintro _ ⟨l, rfl⟩
    rw [he']
    exact (Ideal.span (Set.range r)).mul_mem_left _ (Ideal.subset_span ⟨l, rfl⟩)

/-- On distinct charts a normalized diagonal weight exhibits a left
coordinate ratio as invertible modulo the selected ideal. -/
theorem one_sub_mul_mem_normalizedDiagonalWeights_span (hi : i ∈ I) (hj : j ∈ J) (hij : i ≠ j) :
    1 - chartLeftCoordinate hi j * chartRightCoordinate hj i ∈
      Ideal.span (Set.range (normalizedDiagonalWeights (E := E) h p q hi hj)) := by
  obtain ⟨l, hl⟩ := exists_diagonalMinor_normalized_one_sub (E := E) h p q i j hij
  apply Ideal.subset_span
  refine ⟨l, Subtype.ext ?_⟩
  change (normalizedDiagonalWeights (E := E) h p q hi hj l : F ⊗[k] F) =
    1 - (chartLeftCoordinate (k := k) (x := x) (J := J) hi j : F ⊗[k] F) *
      (chartRightCoordinate (k := k) (x := x) (I := I) hj i : F ⊗[k] F)
  rw [chartLeftCoordinate_coe, chartRightCoordinate_coe]
  exact hl

end GlobalTheory.PD
