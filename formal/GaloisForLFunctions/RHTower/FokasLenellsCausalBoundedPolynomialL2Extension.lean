import GaloisForLFunctions.RHTower.FokasLenellsCausalPolynomialResponseClassification
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedCoordinateExtension
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialPeriodicity
/-! Exact bounded L2 completions of polynomial functions of the actual derivative-chain shift.
The same classification holds at every derivative coordinate, with explicit positive-time
Cauchy operators and their sharp norms supplying the complete surviving family. -/
open Complex MeasureTheory Set Filter Topology Polynomial
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialExtensionLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialExtensionChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialExtensionChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialExtensionChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialExtensionEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedRing
local instance causalPolynomialExtensionEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialExtensionEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) := NonUnitalSeminormedRing.toIsTopologicalRing
local instance causalPolynomialExtensionEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) := ContinuousLinearMap.toNormedAlgebra


local instance causalPolynomialExtensionLowerEndNormedSpace :
    NormedSpace ℂ (hardyL2ᗮ →L[ℂ] hardyL2ᗮ) := ContinuousLinearMap.toNormedSpace
local instance causalPolynomialExtensionLowerEndNormSMul :
    NormSMulClass ℂ (hardyL2ᗮ →L[ℂ] hardyL2ᗮ) :=
  NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := hardyL2ᗮ →L[ℂ] hardyL2ᗮ)

private theorem extension_disk_response (j : ℕ)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain) (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
    (F : ℂ → ℂ)
    (hA : ∀ q : causalBoundedDiskRate,
      A (causalBoundedDiskEigenchain q) = F q.val • causalBoundedDiskEigenchain q)
    (hT : causalBoundedCoordinateExtension j A T) (q : causalBoundedDiskRate) :
    T (causalBoundedDiskEigenvector q).val = F q.val • (causalBoundedDiskEigenvector q).val := by
  have hq : q.val ≠ 0 := by
    intro h
    have hh := q.property.1
    rw [h, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh
  have hcoord : causalBoundedChainCoordinate j (causalBoundedDiskEigenchain q) =
      q.val ^ j • (causalBoundedDiskEigenvector q).val := rfl
  apply smul_right_injective (hardyL2ᗮ) (pow_ne_zero j hq)
  calc
    q.val ^ j • T (causalBoundedDiskEigenvector q).val =
        T (q.val ^ j • (causalBoundedDiskEigenvector q).val) := (map_smul T _ _).symm
    _ = T (causalBoundedChainCoordinate j (causalBoundedDiskEigenchain q)) :=
      congrArg T hcoord.symm
    _ = causalBoundedChainCoordinate j (A (causalBoundedDiskEigenchain q)) :=
      congrArg (fun Q : causalBoundedChain →L[ℂ] hardyL2ᗮ => Q (causalBoundedDiskEigenchain q)) hT
    _ = causalBoundedChainCoordinate j (F q.val • causalBoundedDiskEigenchain q) :=
      congrArg (causalBoundedChainCoordinate j) (hA q)
    _ = F q.val • causalBoundedChainCoordinate j (causalBoundedDiskEigenchain q) :=
      map_smul (causalBoundedChainCoordinate j) _ _
    _ = F q.val • (q.val ^ j • (causalBoundedDiskEigenvector q).val) :=
      congrArg (fun v : hardyL2ᗮ => F q.val • v) hcoord
    _ = q.val ^ j • (F q.val • (causalBoundedDiskEigenvector q).val) := smul_comm _ _ _

private theorem constant_operator_apply (b : ℂ) (u : causalBoundedChain) :
    causalBoundedPolynomialOperator (C b) u = b • u :=
  (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (Polynomial.aeval_C causalBoundedChainShift b)).trans (ContinuousLinearMap.algebraMap_apply b u)

private theorem scaled_flow (p : ℂ[X]) (z : ℂ) :
    causalBoundedPolynomialExponential (z • p) 1 = causalBoundedPolynomialExponential p z := by
  have hp : causalBoundedPolynomialOperator (z • p) = z • causalBoundedPolynomialOperator p :=
    (Polynomial.aeval causalBoundedChainShift).toLinearMap.map_smul z p
  have hs : (1 : ℂ) • causalBoundedPolynomialOperator (z • p) = z • causalBoundedPolynomialOperator p :=
    (one_smul ℂ _).trans hp
  exact congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) hs

private theorem linear_flow (z : ℂ) :
    causalBoundedPolynomialExponential X z = causalBoundedChainExponential z := by
  have hp : causalBoundedPolynomialOperator X = causalBoundedChainShift :=
    Polynomial.aeval_X causalBoundedChainShift
  exact congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp (z • A)) hp

private theorem affine_flow_apply (a b : ℂ) (u : causalBoundedChain) :
    causalBoundedPolynomialExponential (C a * X + C b) 1 u =
      Complex.exp b • causalBoundedChainExponential a u := by
  have hm : causalBoundedPolynomialExponential (C a * X + C b) 1 =
      causalBoundedPolynomialExponential X a * causalBoundedPolynomialExponential (C b) 1 := by
    simpa only [one_smul, Polynomial.smul_eq_C_mul] using
      causalBoundedPolynomialExponential_mix X (C b) a 1
  have hc : causalBoundedPolynomialExponential (C b) 1 u = Complex.exp b • u := by
    have h := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
      (causalBoundedPolynomialExponential_constant b 1)
    simpa only [one_mul, ContinuousLinearMap.algebraMap_apply] using h
  calc
    causalBoundedPolynomialExponential (C a * X + C b) 1 u =
        causalBoundedPolynomialExponential X a (causalBoundedPolynomialExponential (C b) 1 u) :=
      congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u) hm
    _ = causalBoundedChainExponential a (causalBoundedPolynomialExponential (C b) 1 u) :=
      congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain =>
        A (causalBoundedPolynomialExponential (C b) 1 u)) (linear_flow a)
    _ = causalBoundedChainExponential a (Complex.exp b • u) :=
      congrArg (causalBoundedChainExponential a) hc
    _ = Complex.exp b • causalBoundedChainExponential a u := map_smul _ _ _

/-- Through every genuine derivative coordinate, a polynomial in the bounded
chain shift extends to a bounded original L2 operator exactly for scalar constants. -/
theorem causalBoundedPolynomialOperator_coordinateExtension_iff (j : ℕ) (p : ℂ[X])
    (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ) :
    causalBoundedCoordinateExtension j (causalBoundedPolynomialOperator p) T ↔
      ∃ b : ℂ, p = C b ∧ T = b • ContinuousLinearMap.id ℂ (hardyL2ᗮ) := by
  constructor
  · intro hT
    apply (causalCauchyPolynomialResponse_iff p T).mp
    exact extension_disk_response j (causalBoundedPolynomialOperator p) T (fun z => p.eval z)
      (causalBoundedPolynomialOperator_diskEigenchain p) hT
  · rintro ⟨b, rfl, rfl⟩
    apply ContinuousLinearMap.ext
    intro u
    change b • causalBoundedChainCoordinate j u =
      causalBoundedChainCoordinate j (causalBoundedPolynomialOperator (C b) u)
    exact (map_smul (causalBoundedChainCoordinate j) b u).symm.trans
      (congrArg (causalBoundedChainCoordinate j) (constant_operator_apply b u)).symm

/-- Every derivative coordinate has the same exact bounded L2 extension gate for
complex-time polynomial flows. The surviving operator and its sharp norm are explicit. -/
theorem causalBoundedPolynomialExponential_coordinateExtension_iff (j : ℕ) (p : ℂ[X]) (z : ℂ)
    (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ) :
    causalBoundedCoordinateExtension j (causalBoundedPolynomialExponential p z) T ↔
      ∃ a : ℝ≥0, ∃ b : ℂ, z • p = C ((a : ℝ) : ℂ) * X + C b ∧
        T = Complex.exp b • causalLowerCauchyEvolution a ∧ ‖T‖ = Real.exp b.re := by
  constructor
  · intro hT
    have hresp : ∀ q : causalBoundedDiskRate,
        T (causalBoundedDiskEigenvector q).val =
          Complex.exp ((z • p).eval q.val) • (causalBoundedDiskEigenvector q).val := by
      intro q
      have h := extension_disk_response j (causalBoundedPolynomialExponential p z) T
        (fun w => Complex.exp (z * p.eval w)) (causalBoundedPolynomialExponential_diskEigenchain p z) hT q
      simpa only [Polynomial.eval_smul, smul_eq_mul] using h
    obtain ⟨a, b, hp, he⟩ := (causalCauchyExponentialPolynomialResponse_iff (z • p) T).mp hresp
    refine ⟨a, b, hp, he, ?_⟩
    rw [he, norm_smul, norm_causalLowerCauchyEvolution, Complex.norm_exp, mul_one]
  · rintro ⟨a, b, hp, rfl, _⟩
    apply ContinuousLinearMap.ext
    intro u
    change Complex.exp b • causalLowerCauchyEvolution a (causalBoundedChainCoordinate j u) =
      causalBoundedChainCoordinate j (causalBoundedPolynomialExponential p z u)
    have he : causalBoundedPolynomialExponential p z u =
        Complex.exp b • causalBoundedChainExponential ((a : ℝ) : ℂ) u :=
      (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u) (scaled_flow p z).symm).trans
        ((congrArg (fun q : ℂ[X] => causalBoundedPolynomialExponential q 1 u) hp).trans
          (affine_flow_apply ((a : ℝ) : ℂ) b u))
    exact ((congrArg (causalBoundedChainCoordinate j) he).trans
      ((map_smul (causalBoundedChainCoordinate j) (Complex.exp b)
        (causalBoundedChainExponential ((a : ℝ) : ℂ) u)).trans
          (congrArg (fun v : hardyL2ᗮ => Complex.exp b • v)
            (causalBoundedEntireOrbit_eq_evolution j u a)))).symm

end
end RHTower.FokasLenells
