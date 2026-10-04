import GaloisForLFunctions.RHTower.TwoGaussianDerivativeHilbertHistory

/-!
# The centered zero-Jordan history of the literal two-Gaussian source

For `k(x) = exp(-x²) + exp(-2x²)` the actual quantile derivative vectors `v_{n+1}` have zero
mean, so they lie in the mean-zero hyperplane `H₀ = (ℂ ∙ 1)ᗮ` of the original pinned Hilbert
space.  The orthogonal projection onto `H₀` is `f ↦ f − mean(f)·1`.  The centered primitive
`P ∘ B`, restricted to the span of `v_{n+1}`, kills `v_1` and lowers `v_{n+2}` to `i v_{n+1}`:
the mean-zero quotient of the two-Gaussian source carries the same infinite zero-Jordan chain as
the theta quotient.  No compactness or kernel-energy statement for the Gaussian inverse is used.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry RHTower RHTower.HedenmalmQuantile
open scoped ENNReal

namespace RHTower.TwoGaussianComparison

attribute [local instance] Real.measurableSpace NormedSpace.complexToReal

/-- The mean-zero hyperplane `(ℂ ∙ 1)ᗮ` of the original pinned Hilbert space. -/
def meanZeroHyperplane : Submodule ℂ H := (ℂ ∙ pinnedOne)ᗮ

theorem mem_meanZeroHyperplane_iff (f : H) : f ∈ meanZeroHyperplane ↔ pinnedMean f = 0 := by
  rw [meanZeroHyperplane, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hinner : inner ℂ pinnedOne f = pinnedMean f := by
    rw [MeasureTheory.L2.inner_def, pinnedMean]
    apply integral_congr_ae
    filter_upwards [pinnedOne_coeFn] with t ht
    rw [ht]
    simp
  rw [hinner]

instance meanZeroHyperplaneHasOrthogonalProjection : meanZeroHyperplane.HasOrthogonalProjection :=
  show (ℂ ∙ pinnedOne)ᗮ.HasOrthogonalProjection from inferInstance

/-- The orthogonal projection onto the mean-zero hyperplane is `f ↦ f − mean(f)·1`. -/
theorem starProjection_meanZeroHyperplane (f : H) :
    meanZeroHyperplane.starProjection f = f - pinnedMean f • pinnedOne := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · rw [mem_meanZeroHyperplane_iff, sub_eq_add_neg, ← neg_smul, pinnedMean_add, pinnedMean_smul,
      pinnedMean_pinnedOne]
    ring
  · rw [sub_sub_cancel]
    exact Submodule.le_orthogonal_orthogonal _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self pinnedOne))

/-- The orthogonal projection onto the mean-zero hyperplane. -/
def meanZeroProjection : H →L[ℂ] meanZeroHyperplane := meanZeroHyperplane.orthogonalProjectionOnto

theorem coe_meanZeroProjection (f : H) :
    (meanZeroProjection f : H) = f - pinnedMean f • pinnedOne :=
  starProjection_meanZeroHyperplane f

theorem meanZeroProjection_pinnedOne : meanZeroProjection pinnedOne = 0 := by
  apply Subtype.ext
  rw [coe_meanZeroProjection, pinnedMean_pinnedOne, one_smul, sub_self]
  rfl

theorem meanZeroProjection_of_mem {f : H} (hf : f ∈ meanZeroHyperplane) :
    (meanZeroProjection f : H) = f := by
  rw [coe_meanZeroProjection, (mem_meanZeroHyperplane_iff f).1 hf, zero_smul, sub_zero]

/-- The actual positive-order quantile derivatives, as mean-zero vectors. -/
def centeredDerivativeVector (n : ℕ) : meanZeroHyperplane :=
  ⟨quantileDerivativeVector (n + 1),
    (mem_meanZeroHyperplane_iff _).2 (pinnedMean_quantileDerivativeVector_succ n)⟩

theorem centeredDerivativeVector_coe (n : ℕ) :
    (centeredDerivativeVector n : H) = quantileDerivativeVector (n + 1) := rfl

theorem linearIndependent_centeredDerivativeVector :
    LinearIndependent ℂ centeredDerivativeVector := by
  have h : LinearIndependent ℂ (fun n => quantileDerivativeVector (n + 1)) :=
    linearIndependent_quantileDerivativeVector.comp (fun n => n + 1)
      (fun i j hij => Nat.add_right_cancel hij)
  exact LinearIndependent.of_comp meanZeroHyperplane.subtype h

theorem centeredDerivativeVector_ne_zero (n : ℕ) : centeredDerivativeVector n ≠ 0 :=
  linearIndependent_centeredDerivativeVector.ne_zero n

/-- The centered history: the span of all positive-order derivative vectors in `H₀`. -/
def centeredDerivativeHistory : Submodule ℂ meanZeroHyperplane :=
  Submodule.span ℂ (Set.range centeredDerivativeVector)

theorem quantileDerivativeVector_mem_history (n : ℕ) :
    quantileDerivativeVector n ∈ quantileDerivativeHistory := by
  rw [quantileDerivativeHistory_eq_span]
  exact Submodule.subset_span ⟨n, rfl⟩

theorem centeredDerivativeHistory_le {f : meanZeroHyperplane} (hf : f ∈ centeredDerivativeHistory) :
    (f : H) ∈ quantileDerivativeHistory := by
  refine Submodule.span_induction (p := fun (f : meanZeroHyperplane) _ => (f : H) ∈ quantileDerivativeHistory)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨n, rfl⟩
    exact quantileDerivativeVector_mem_history (n + 1)
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    exact Submodule.smul_mem _ c hx

/-- Inclusion of the centered history into the full quantile history. -/
def centeredHistoryInclusion : centeredDerivativeHistory →ₗ[ℂ] quantileDerivativeHistory :=
  LinearMap.codRestrict quantileDerivativeHistory
    (meanZeroHyperplane.subtype.comp centeredDerivativeHistory.subtype)
    fun f => centeredDerivativeHistory_le f.property

/-- The centered primitive `P ∘ B` on the centered history, with values in `H₀`. -/
def centeredPrimitive : centeredDerivativeHistory →ₗ[ℂ] meanZeroHyperplane :=
  meanZeroProjection.toLinearMap.comp
    (quantileDerivativeHistory.subtype.comp (quantileHistoryInverse.comp centeredHistoryInclusion))

theorem coe_centeredPrimitive (f : centeredDerivativeHistory) :
    (centeredPrimitive f : H) =
      (quantileHistoryInverse (centeredHistoryInclusion f) : H) -
        pinnedMean (quantileHistoryInverse (centeredHistoryInclusion f) : H) • pinnedOne :=
  coe_meanZeroProjection _

theorem centeredHistoryInclusion_vector (n : ℕ) :
    centeredHistoryInclusion ⟨centeredDerivativeVector n, Submodule.subset_span ⟨n, rfl⟩⟩ =
      quantileHistoryDerivativeVector (n + 1) := by
  apply Subtype.ext
  rw [quantileHistoryDerivativeVector_coe]
  rfl

theorem centeredPrimitive_vector_zero :
    centeredPrimitive ⟨centeredDerivativeVector 0, Submodule.subset_span ⟨0, rfl⟩⟩ = 0 := by
  change meanZeroProjection ((quantileHistoryInverse (centeredHistoryInclusion
    ⟨centeredDerivativeVector 0, Submodule.subset_span ⟨0, rfl⟩⟩) : quantileDerivativeHistory) : H) = 0
  rw [centeredHistoryInclusion_vector, quantileHistoryInverse_derivative_succ,
    Submodule.coe_smul, quantileHistoryDerivativeVector_coe, quantileDerivativeVector_zero,
    map_smul, map_smul, meanZeroProjection_pinnedOne, smul_zero, smul_zero]

theorem centeredPrimitive_vector_succ (n : ℕ) :
    centeredPrimitive ⟨centeredDerivativeVector (n + 1), Submodule.subset_span ⟨n + 1, rfl⟩⟩ =
      Complex.I • centeredDerivativeVector n := by
  apply Subtype.ext
  change (meanZeroProjection ((quantileHistoryInverse (centeredHistoryInclusion
    ⟨centeredDerivativeVector (n + 1), Submodule.subset_span ⟨n + 1, rfl⟩⟩) :
      quantileDerivativeHistory) : H) : H) = _
  rw [centeredHistoryInclusion_vector, quantileHistoryInverse_derivative_succ,
    Submodule.coe_smul, quantileHistoryDerivativeVector_coe, map_smul, Submodule.coe_smul,
    show quantileDerivativeVector (n + 1) = (centeredDerivativeVector n : H) from rfl,
    meanZeroProjection_of_mem (centeredDerivativeVector n).property, Submodule.coe_smul]

theorem centeredPrimitive_mem (f : centeredDerivativeHistory) :
    centeredPrimitive f ∈ centeredDerivativeHistory := by
  obtain ⟨f, hf⟩ := f
  refine Submodule.span_induction
    (p := fun f hf => centeredPrimitive ⟨f, hf⟩ ∈ centeredDerivativeHistory) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨n, rfl⟩
    cases n with
    | zero => rw [centeredPrimitive_vector_zero]; exact Submodule.zero_mem _
    | succ n =>
      rw [centeredPrimitive_vector_succ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  · have : (⟨0, Submodule.zero_mem _⟩ : centeredDerivativeHistory) = 0 := rfl
    rw [this, map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy hxi hyi
    have : (⟨x + y, Submodule.add_mem _ hx hy⟩ : centeredDerivativeHistory) = ⟨x, hx⟩ + ⟨y, hy⟩ :=
      rfl
    rw [this, map_add]
    exact Submodule.add_mem _ hxi hyi
  · intro c x hx hxi
    have : (⟨c • x, Submodule.smul_mem _ c hx⟩ : centeredDerivativeHistory) = c • ⟨x, hx⟩ := rfl
    rw [this, map_smul]
    exact Submodule.smul_mem _ c hxi

/-- **The centered history operator** `D = P ∘ B` on the centered history. -/
def centeredHistoryInverse : centeredDerivativeHistory →ₗ[ℂ] centeredDerivativeHistory :=
  LinearMap.codRestrict centeredDerivativeHistory centeredPrimitive centeredPrimitive_mem

/-- The centered chain, as vectors of the centered history. -/
def centeredHistoryVector (n : ℕ) : centeredDerivativeHistory :=
  ⟨centeredDerivativeVector n, Submodule.subset_span ⟨n, rfl⟩⟩

theorem centeredHistoryVector_coe (n : ℕ) :
    ((centeredHistoryVector n : meanZeroHyperplane) : H) = quantileDerivativeVector (n + 1) := rfl

/-- The literal action: `D f = B f − mean(B f)·1`. -/
theorem centeredHistoryInverse_literal (f : centeredDerivativeHistory) :
    (((centeredHistoryInverse f : centeredDerivativeHistory) : meanZeroHyperplane) : H) =
      (quantileHistoryInverse (centeredHistoryInclusion f) : H) -
        pinnedMean (quantileHistoryInverse (centeredHistoryInclusion f) : H) • pinnedOne :=
  coe_centeredPrimitive f

theorem centeredHistoryInverse_vector_zero :
    centeredHistoryInverse (centeredHistoryVector 0) = 0 :=
  Subtype.ext centeredPrimitive_vector_zero

theorem centeredHistoryInverse_vector_succ (n : ℕ) :
    centeredHistoryInverse (centeredHistoryVector (n + 1)) =
      Complex.I • centeredHistoryVector n :=
  Subtype.ext (centeredPrimitive_vector_succ n)

theorem linearIndependent_centeredHistoryVector :
    LinearIndependent ℂ centeredHistoryVector :=
  LinearIndependent.of_comp centeredDerivativeHistory.subtype
    linearIndependent_centeredDerivativeVector

theorem centeredHistoryVector_ne_zero (n : ℕ) : centeredHistoryVector n ≠ 0 :=
  linearIndependent_centeredHistoryVector.ne_zero n

theorem centeredHistoryInverse_pow_vector_self (n : ℕ) :
    (centeredHistoryInverse ^ n) (centeredHistoryVector n) =
      Complex.I ^ n • centeredHistoryVector 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, centeredHistoryInverse_vector_succ, map_smul, ih,
      smul_smul, pow_succ, mul_comm]

theorem centeredHistoryInverse_pow_vector_eq_zero (n k : ℕ) (h : n < k) :
    (centeredHistoryInverse ^ k) (centeredHistoryVector n) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show n + j + 1 = j + (n + 1) by ring, pow_add, Module.End.mul_apply, pow_succ',
    Module.End.mul_apply, centeredHistoryInverse_pow_vector_self, map_smul,
    centeredHistoryInverse_vector_zero, smul_zero, map_zero]

/-- **G3c: the centered infinite zero-Jordan chain of the two-Gaussian source.**  The mean-zero
quotient of the literal two-Gaussian source inverse has a nonzero, linearly independent chain
`w_n = v_{n+1}` with `D w_0 = 0`, `D w_{n+1} = i w_n`, `D^n w_n = iⁿ w_0` and `D^k w_n = 0` for
`k > n`. -/
theorem centeredHistory_infinite_zero_chain :
    LinearIndependent ℂ centeredHistoryVector ∧
      (∀ n, centeredHistoryVector n ≠ 0) ∧
      centeredHistoryInverse (centeredHistoryVector 0) = 0 ∧
      (∀ n, centeredHistoryInverse (centeredHistoryVector (n + 1)) =
        Complex.I • centeredHistoryVector n) ∧
      (∀ n, (centeredHistoryInverse ^ n) (centeredHistoryVector n) =
        Complex.I ^ n • centeredHistoryVector 0) ∧
      (∀ n k, n < k → (centeredHistoryInverse ^ k) (centeredHistoryVector n) = 0) :=
  ⟨linearIndependent_centeredHistoryVector, centeredHistoryVector_ne_zero,
    centeredHistoryInverse_vector_zero, centeredHistoryInverse_vector_succ,
    centeredHistoryInverse_pow_vector_self, centeredHistoryInverse_pow_vector_eq_zero⟩

end RHTower.TwoGaussianComparison
