import GaloisForLFunctions.RHTower.ArithmeticSchurRenormalizationLaw

/-!
# Universal Cauchy--Stein response law

The rank-two displacement and Cayley--Cauchy congruence used by the reciprocal-prime response
kernel are not arithmetic.  They hold for every family of disk nodes, boundary amplitudes, and
scalar responses.  This module isolates that universal algebra so arithmetic specializations
cannot be mistaken for a new source-to-RH mechanism.
-/

namespace RHTower

noncomputable section

open Matrix

/-- Cayley image of an arbitrary real disk coordinate. -/
def universalCayleyNode (q : ℝ) : ℝ :=
  (1 + q) / (1 - q)

/-- Diagonal weight converting a Schur carrier to its Cayley--Cauchy form. -/
def universalCayleyCongruenceWeight (q amplitude : ℝ) : ℝ :=
  Real.sqrt 2 * amplitude / (1 - q)

/-- Cauchy response kernel sampled at arbitrary Cayley nodes. -/
def universalCauchyResponseKernel
    {ι : Type*} (node response : ι → ℝ) (i j : ι) : ℝ :=
  (response i + response j) /
    (universalCayleyNode (node i) + universalCayleyNode (node j))

/-- A universal Schur carrier dressed by arbitrary scalar response data. -/
def universalSteinResponseKernel
    {ι : Type*} (node amplitude response : ι → ℝ) (i j : ι) : ℝ :=
  arithmeticSchurKernel (node i) (node j) (amplitude i) (amplitude j) *
    (response i + response j)

/-- Response-weighted boundary coordinate in the universal rank-two displacement. -/
def universalSteinResponseBoundary
    {ι : Type*} (amplitude response : ι → ℝ) (i : ι) : ℝ :=
  response i * amplitude i

/-- Dressing a universal Schur carrier turns its rank-one Stein residual into a symmetrized
rank-two boundary residual. -/
theorem universalSteinResponseKernel_displacement
    {ι : Type*} (node amplitude response : ι → ℝ) (i j : ι)
    (hij : 1 - node i * node j ≠ 0) :
    universalSteinResponseKernel node amplitude response i j -
        node i * node j * universalSteinResponseKernel node amplitude response i j =
      universalSteinResponseBoundary amplitude response i * amplitude j +
        amplitude i * universalSteinResponseBoundary amplitude response j := by
  simp only [universalSteinResponseKernel, universalSteinResponseBoundary,
    arithmeticSchurKernel]
  field_simp [hij]

/-- The universal dressed Schur kernel is a positive-diagonal rescaling of a sampled
Cauchy-response kernel.  No primality or arithmetic input occurs. -/
theorem universalSteinResponseKernel_eq_cayleyCongruence
    {ι : Type*} (node amplitude response : ι → ℝ) (i j : ι)
    (hi : 1 - node i ≠ 0) (hj : 1 - node j ≠ 0)
    (hij : 1 - node i * node j ≠ 0) :
    universalSteinResponseKernel node amplitude response i j =
      universalCayleyCongruenceWeight (node i) (amplitude i) *
        universalCauchyResponseKernel node response i j *
          universalCayleyCongruenceWeight (node j) (amplitude j) := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcleared :
      (1 + node i) * (1 - node j) + (1 - node i) * (1 + node j) ≠ 0 := by
    intro h
    apply hij
    nlinarith
  simp only [universalSteinResponseKernel, universalCayleyCongruenceWeight,
    universalCauchyResponseKernel, universalCayleyNode, arithmeticSchurKernel]
  field_simp [hi, hj, hij, hcleared]
  rw [pow_two, hsqrt]
  ring

/-- The universal response transform is additive in its scalar response. -/
theorem universalSteinResponseKernel_add
    {ι : Type*} (node amplitude response₁ response₂ : ι → ℝ) (i j : ι) :
    universalSteinResponseKernel node amplitude (response₁ + response₂) i j =
      universalSteinResponseKernel node amplitude response₁ i j +
        universalSteinResponseKernel node amplitude response₂ i j := by
  simp only [universalSteinResponseKernel, Pi.add_apply]
  ring

/-- Nonzero carrier diagonal makes the response transform faithful by diagonal recovery. -/
theorem universalSteinResponseKernel_injective
    {ι : Type*} (node amplitude : ι → ℝ)
    (hdiag : ∀ i,
      arithmeticSchurKernel (node i) (node i) (amplitude i) (amplitude i) ≠ 0) :
    Function.Injective (universalSteinResponseKernel node amplitude) := by
  intro response₁ response₂ h
  funext i
  have hi := congrArg (fun K => K i i) h
  simp only [universalSteinResponseKernel] at hi
  have hcarrier := hdiag i
  have hi' :
      arithmeticSchurKernel (node i) (node i) (amplitude i) (amplitude i) *
          (2 * response₁ i) =
        arithmeticSchurKernel (node i) (node i) (amplitude i) (amplitude i) *
          (2 * response₂ i) := by
    nlinarith [hi]
  have hresponse : 2 * response₁ i = 2 * response₂ i :=
    mul_left_cancel₀ hcarrier hi'
  linarith

/-- Finite universal dressed response matrix. -/
def universalFiniteSteinResponseMatrix
    {ι I : Type*} [Fintype I] (sample : I → ι)
    (node amplitude response : ι → ℝ) : Matrix I I ℝ :=
  fun i j => universalSteinResponseKernel node amplitude response (sample i) (sample j)

/-- Finite universal Cayley--Cauchy response matrix. -/
def universalFiniteCauchyResponseMatrix
    {ι I : Type*} [Fintype I] (sample : I → ι)
    (node response : ι → ℝ) : Matrix I I ℝ :=
  fun i j => universalCauchyResponseKernel node response (sample i) (sample j)

/-- Every finite dressed Schur response matrix is a diagonal congruence of the corresponding
Cauchy response matrix. -/
theorem universalFiniteSteinResponseMatrix_eq_cayleyCongruence
    {ι I : Type*} [Fintype I] [DecidableEq I] (sample : I → ι)
    (node amplitude response : ι → ℝ)
    (hnode : ∀ i, 1 - node (sample i) ≠ 0)
    (hpair : ∀ i j, 1 - node (sample i) * node (sample j) ≠ 0) :
    universalFiniteSteinResponseMatrix sample node amplitude response =
      Matrix.diagonal
          (fun i => universalCayleyCongruenceWeight
            (node (sample i)) (amplitude (sample i))) *
        universalFiniteCauchyResponseMatrix sample node response *
          Matrix.diagonal
            (fun i => universalCayleyCongruenceWeight
              (node (sample i)) (amplitude (sample i))) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact universalSteinResponseKernel_eq_cayleyCongruence node amplitude response
    (sample i) (sample j) (hnode i) (hnode j) (hpair i j)

end

end RHTower
