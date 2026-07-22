import GaloisForLFunctions.RHTower.UniversalCauchySteinResponseLaw
import GaloisForLFunctions.RHTower.XiHypertranscendenceChain
import GaloisForLFunctions.RHTower.XiSquaredEulerRayTwoPointPositivity

/-!
# Prime-space inertia: the rank-two Stein source law

The genuine Möbius Schur difference kernel is a positive reciprocal-prime Cauchy carrier.  If a
real response `lambda_p` is attached to every prime, its symmetric response kernel

`B(p,r) = G(p,r) * (lambda_p + lambda_r)`

has an exact rank-two Stein displacement under multiplication by the reciprocal-prime disk node.
The same kernel is a positive diagonal congruence of the real Cauchy--Loewner kernel sampled at
the Cayley images of the reciprocal primes.

Specializing the response to the real part of the completed Xi logarithmic derivative gives the
algebraic source operator used by the prime-space inertia paper.  This file proves the source and
finite-matrix identities.  It does not assert the analytic generalized-Nevanlinna theorem that
identifies the infinite operator's negative index with the off-critical Xi divisor.
-/

namespace RHTower

noncomputable section

open scoped BigOperators
open Matrix

/-- Cayley image of the reciprocal-prime disk node. -/
def primeSpaceCayleyNode (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  (1 + q) / (1 - q)

/-- The boundary vector in the one-step Stein displacement of the Möbius carrier. -/
def primeSpaceSteinBoundaryVector (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  q * (1 - q) / (1 + q)

/-- Positive diagonal weight relating the Möbius carrier to the Cayley Cauchy kernel. -/
def primeSpaceCayleyCongruenceWeight (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  Real.sqrt 2 * q / (1 + q)

/-- Cauchy--Loewner response kernel on reciprocal-prime Cayley nodes. -/
def primeSpaceEulerRayResponseKernel
    (response : Nat.Primes → ℝ) (p r : Nat.Primes) : ℝ :=
  (response p + response r) / (primeSpaceCayleyNode p + primeSpaceCayleyNode r)

/-- Möbius-Cauchy carrier dressed by a symmetric scalar response. -/
def primeSpaceSteinResponseKernel
    (response : Nat.Primes → ℝ) (p r : Nat.Primes) : ℝ :=
  xiMobiusPrimeSchurDifferenceKernel p r * (response p + response r)

/-- Response-weighted boundary vector. -/
def primeSpaceSteinResponseBoundaryVector
    (response : Nat.Primes → ℝ) (p : Nat.Primes) : ℝ :=
  response p * primeSpaceSteinBoundaryVector p

private theorem primeSpace_node_one_add_ne (p : Nat.Primes) :
    1 + xiTransversePrimeApertureDiskNode 1 p ≠ 0 := by
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  linarith

private theorem primeSpace_node_one_sub_ne (p : Nat.Primes) :
    1 - xiTransversePrimeApertureDiskNode 1 p ≠ 0 := by
  have hq := xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) p
  linarith

private theorem primeSpace_node_product_one_sub_ne (p r : Nat.Primes) :
    1 - xiTransversePrimeApertureDiskNode 1 p *
        xiTransversePrimeApertureDiskNode 1 r ≠ 0 := by
  have hp0 := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hp1 := xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) p
  have hr1 := xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) r
  have hprod := mul_lt_one_of_nonneg_of_lt_one_left hp0 hp1 hr1.le
  linarith

/-- The allegedly prime-specific carrier is exactly the universal Schur carrier at the chosen
reciprocal-prime nodes and boundary amplitudes. -/
theorem xiMobiusPrimeSchurDifferenceKernel_eq_universalSchurKernel
    (p r : Nat.Primes) :
    xiMobiusPrimeSchurDifferenceKernel p r =
      arithmeticSchurKernel
        (xiTransversePrimeApertureDiskNode 1 p)
        (xiTransversePrimeApertureDiskNode 1 r)
        (primeSpaceSteinBoundaryVector p)
        (primeSpaceSteinBoundaryVector r) := by
  have hpplus := primeSpace_node_one_add_ne p
  have hrplus := primeSpace_node_one_add_ne r
  have hprminus := primeSpace_node_product_one_sub_ne p r
  simp only [xiMobiusPrimeSchurDifferenceKernel, arithmeticSchurKernel,
    primeSpaceSteinBoundaryVector]
  field_simp [hpplus, hrplus, hprminus]

/-- Prime--Stein dressing is a literal specialization of the universal Cauchy--Stein response
transform; primality supplies no additional displacement identity. -/
theorem primeSpaceSteinResponseKernel_eq_universal
    (response : Nat.Primes → ℝ) (p r : Nat.Primes) :
    primeSpaceSteinResponseKernel response p r =
      universalSteinResponseKernel
        (xiTransversePrimeApertureDiskNode 1)
        primeSpaceSteinBoundaryVector response p r := by
  simp only [primeSpaceSteinResponseKernel, universalSteinResponseKernel]
  rw [xiMobiusPrimeSchurDifferenceKernel_eq_universalSchurKernel]

/-- Every prime has strictly positive mass in the Möbius Cauchy carrier. -/
theorem xiMobiusPrimeSchurDifferenceKernel_self_pos (p : Nat.Primes) :
    0 < xiMobiusPrimeSchurDifferenceKernel p p := by
  rw [xiMobiusPrimeSchurDifferenceKernel_self]
  have hq0 := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : xiTransversePrimeApertureDiskNode 1 p < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) p
  exact div_pos
    (mul_pos (pow_pos hq0 2) (sub_pos.mpr hq1))
    (pow_pos (by linarith : 0 < 1 + xiTransversePrimeApertureDiskNode 1 p) 3)

/-- The Prime--Stein construction turns addition of responses, and hence multiplication after a
logarithmic derivative, into addition of kernels. -/
theorem primeSpaceSteinResponseKernel_add
    (response₁ response₂ : Nat.Primes → ℝ) (p r : Nat.Primes) :
    primeSpaceSteinResponseKernel (response₁ + response₂) p r =
      primeSpaceSteinResponseKernel response₁ p r +
        primeSpaceSteinResponseKernel response₂ p r := by
  simp only [primeSpaceSteinResponseKernel, Pi.add_apply]
  ring

/-- The response-to-kernel map is faithful: its diagonal recovers every response coordinate. -/
theorem primeSpaceSteinResponseKernel_injective :
    Function.Injective primeSpaceSteinResponseKernel := by
  intro response₁ response₂ h
  funext p
  have hp := congrArg (fun K => K p p) h
  simp only [primeSpaceSteinResponseKernel] at hp
  nlinarith [xiMobiusPrimeSchurDifferenceKernel_self_pos p]

/-- **Rank-one carrier displacement.** The Möbius prime carrier is the unique geometric Stein
completion of one explicit boundary vector. -/
theorem xiMobiusPrimeSchurDifferenceKernel_steinDisplacement
    (p r : Nat.Primes) :
    xiMobiusPrimeSchurDifferenceKernel p r -
        xiTransversePrimeApertureDiskNode 1 p *
          xiTransversePrimeApertureDiskNode 1 r *
            xiMobiusPrimeSchurDifferenceKernel p r =
      primeSpaceSteinBoundaryVector p * primeSpaceSteinBoundaryVector r := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  have hqplus : 1 + q ≠ 0 := primeSpace_node_one_add_ne p
  have hsplus : 1 + s ≠ 0 := primeSpace_node_one_add_ne r
  have hqsminus : 1 - q * s ≠ 0 := primeSpace_node_product_one_sub_ne p r
  simp only [xiMobiusPrimeSchurDifferenceKernel, primeSpaceSteinBoundaryVector]
  rw [show xiTransversePrimeApertureDiskNode 1 p = q by rfl,
    show xiTransversePrimeApertureDiskNode 1 r = s by rfl]
  field_simp [hqplus, hsplus, hqsminus]

/-- **Rank-two response displacement.** Dressing the carrier by any diagonal response changes
the rank-one Stein boundary into the symmetrized rank-two boundary `a v* + v a*`. -/
theorem primeSpaceSteinResponseKernel_displacement
    (response : Nat.Primes → ℝ) (p r : Nat.Primes) :
    primeSpaceSteinResponseKernel response p r -
        xiTransversePrimeApertureDiskNode 1 p *
          xiTransversePrimeApertureDiskNode 1 r *
            primeSpaceSteinResponseKernel response p r =
      primeSpaceSteinResponseBoundaryVector response p *
          primeSpaceSteinBoundaryVector r +
        primeSpaceSteinBoundaryVector p *
          primeSpaceSteinResponseBoundaryVector response r := by
  rw [show primeSpaceSteinResponseKernel response p r -
      xiTransversePrimeApertureDiskNode 1 p *
        xiTransversePrimeApertureDiskNode 1 r *
          primeSpaceSteinResponseKernel response p r =
      (xiMobiusPrimeSchurDifferenceKernel p r -
        xiTransversePrimeApertureDiskNode 1 p *
          xiTransversePrimeApertureDiskNode 1 r *
            xiMobiusPrimeSchurDifferenceKernel p r) *
        (response p + response r) by
    simp only [primeSpaceSteinResponseKernel]
    ring]
  rw [xiMobiusPrimeSchurDifferenceKernel_steinDisplacement]
  simp only [primeSpaceSteinResponseBoundaryVector]
  ring

/-- The dressed Möbius carrier is exactly the positive diagonal congruence of the response kernel
on reciprocal-prime Cayley nodes. -/
theorem primeSpaceSteinResponseKernel_eq_cayleyCongruence
    (response : Nat.Primes → ℝ) (p r : Nat.Primes) :
    primeSpaceSteinResponseKernel response p r =
      primeSpaceCayleyCongruenceWeight p *
        primeSpaceEulerRayResponseKernel response p r *
          primeSpaceCayleyCongruenceWeight r := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  have hqplus : 1 + q ≠ 0 := primeSpace_node_one_add_ne p
  have hsplus : 1 + s ≠ 0 := primeSpace_node_one_add_ne r
  have hqminus : 1 - q ≠ 0 := primeSpace_node_one_sub_ne p
  have hsminus : 1 - s ≠ 0 := primeSpace_node_one_sub_ne r
  have hqsminus : 1 - q * s ≠ 0 := primeSpace_node_product_one_sub_ne p r
  have htwo : 2 - q * s * 2 ≠ 0 := by
    intro h
    apply hqsminus
    nlinarith
  have hcayleyden : (1 - s) * (1 + q) + (1 - q) * (1 + s) ≠ 0 := by
    intro h
    apply htwo
    nlinarith
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [primeSpaceSteinResponseKernel, xiMobiusPrimeSchurDifferenceKernel,
    primeSpaceCayleyCongruenceWeight, primeSpaceEulerRayResponseKernel,
    primeSpaceCayleyNode]
  rw [show xiTransversePrimeApertureDiskNode 1 p = q by rfl,
    show xiTransversePrimeApertureDiskNode 1 r = s by rfl]
  field_simp [hqplus, hsplus, hqminus, hsminus, hqsminus, htwo, hcayleyden]
  rw [pow_two, hsqrt]
  ring

/-- Finite prime-packet response matrix. -/
def primeSpaceFiniteSteinResponseMatrix
    {I : Type*} [Fintype I] (p : I → Nat.Primes)
    (response : Nat.Primes → ℝ) : Matrix I I ℝ :=
  fun i j => primeSpaceSteinResponseKernel response (p i) (p j)

/-- Finite prime-packet Cayley response matrix. -/
def primeSpaceFiniteEulerRayResponseMatrix
    {I : Type*} [Fintype I] (p : I → Nat.Primes)
    (response : Nat.Primes → ℝ) : Matrix I I ℝ :=
  fun i j => primeSpaceEulerRayResponseKernel response (p i) (p j)

/-- Every finite prime response matrix is an exact diagonal congruence of the sampled
Cauchy--Loewner matrix. -/
theorem primeSpaceFiniteSteinResponseMatrix_eq_cayleyCongruence
    {I : Type*} [Fintype I] [DecidableEq I] (p : I → Nat.Primes)
    (response : Nat.Primes → ℝ) :
    primeSpaceFiniteSteinResponseMatrix p response =
      Matrix.diagonal (fun i => primeSpaceCayleyCongruenceWeight (p i)) *
        primeSpaceFiniteEulerRayResponseMatrix p response *
          Matrix.diagonal (fun i => primeSpaceCayleyCongruenceWeight (p i)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact primeSpaceSteinResponseKernel_eq_cayleyCongruence response (p i) (p j)

/-- Scalar finite-depth form of a Stein equation. -/
theorem scalarStein_sub_prefix_eq_residual
    (N : ℕ) (B q F : ℝ) (hStein : B - q * B = F) :
    B - ∑ n ∈ Finset.range N, q ^ n * F = q ^ N * B := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ih, pow_succ, ← hStein]
      ring

/-- Every finite valuation-depth prefix leaves the exact translated response residual. -/
theorem primeSpaceSteinResponseKernel_sub_prefix_eq_residual
    (N : ℕ) (response : Nat.Primes → ℝ) (p r : Nat.Primes) :
    primeSpaceSteinResponseKernel response p r -
        (∑ n ∈ Finset.range N,
          (xiTransversePrimeApertureDiskNode 1 p *
            xiTransversePrimeApertureDiskNode 1 r) ^ n *
            (primeSpaceSteinResponseBoundaryVector response p *
                primeSpaceSteinBoundaryVector r +
              primeSpaceSteinBoundaryVector p *
                primeSpaceSteinResponseBoundaryVector response r)) =
      (xiTransversePrimeApertureDiskNode 1 p *
        xiTransversePrimeApertureDiskNode 1 r) ^ N *
          primeSpaceSteinResponseKernel response p r := by
  apply scalarStein_sub_prefix_eq_residual
  simpa [mul_assoc] using primeSpaceSteinResponseKernel_displacement response p r

/-- Completed-Xi abscissa selected by a reciprocal-prime Cayley node. -/
def xiPrimeSpaceEulerAbscissa (p : Nat.Primes) : ℝ :=
  1 / 2 + primeSpaceCayleyNode p

/-- Every prime-space abscissa lies strictly inside the absolutely convergent Euler region. -/
theorem one_lt_xiPrimeSpaceEulerAbscissa (p : Nat.Primes) :
    1 < xiPrimeSpaceEulerAbscissa p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (a := 1) (by norm_num) p
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hcayley : 1 < (1 + q) / (1 - q) := by
    rw [lt_div_iff₀ hden]
    linarith
  simp only [xiPrimeSpaceEulerAbscissa, primeSpaceCayleyNode]
  rw [show xiTransversePrimeApertureDiskNode 1 p = q by rfl]
  linarith

/-- Euler-safe completed-Xi logarithmic-derivative response at a reciprocal-prime Cayley node. -/
def xiPrimeSpaceLogDerivativeResponse (p : Nat.Primes) : ℝ :=
  (xiLogDeriv (xiPrimeSpaceEulerAbscissa p : ℂ)).re

/-- The ordinary centered real Euler-ray logarithmic derivative already used by the existing
negative-index endpoint. -/
def xiCenteredRealLogDerivativeResponse (x : ℝ) : ℝ :=
  (xiLogDeriv ((1 / 2 + x : ℝ) : ℂ)).re

/-- Prime response data are only samples of the existing centered real Euler-ray response. -/
theorem xiPrimeSpaceLogDerivativeResponse_eq_centeredEulerRaySample
    (p : Nat.Primes) :
    xiPrimeSpaceLogDerivativeResponse p =
      xiCenteredRealLogDerivativeResponse (primeSpaceCayleyNode p) := by
  rfl

/-- The prime-space Cauchy kernel is literally the existing Euler-ray response kernel restricted
to reciprocal-prime Cayley nodes. -/
theorem primeSpaceEulerRayResponseKernel_xi_eq_existingEulerRayKernel
    (p r : Nat.Primes) :
    primeSpaceEulerRayResponseKernel xiPrimeSpaceLogDerivativeResponse p r =
      eulerRayResponseKernel xiCenteredRealLogDerivativeResponse
        (primeSpaceCayleyNode p) (primeSpaceCayleyNode r) := by
  simp only [primeSpaceEulerRayResponseKernel, eulerRayResponseKernel,
    xiPrimeSpaceLogDerivativeResponse_eq_centeredEulerRaySample]

/-- The response is supplied by the existing prime--Gamma logarithmic-derivative weld entirely
inside `Re s > 1`. -/
theorem xiLogDeriv_primeSpaceEulerAbscissa_split (p : Nat.Primes) :
    xiLogDeriv (xiPrimeSpaceEulerAbscissa p : ℂ) =
      1 / (xiPrimeSpaceEulerAbscissa p : ℂ) +
        1 / ((xiPrimeSpaceEulerAbscissa p : ℂ) - 1) -
          (Real.log Real.pi) / 2 +
        (1 / 2) * Complex.digamma ((xiPrimeSpaceEulerAbscissa p : ℂ) / 2) +
          zetaLogDeriv (xiPrimeSpaceEulerAbscissa p : ℂ) := by
  apply xiLogDeriv_split
  simpa using one_lt_xiPrimeSpaceEulerAbscissa p

/-- The concrete source kernel proposed in the prime-space inertia law. -/
def xiPrimeSpaceSteinKernel (p r : Nat.Primes) : ℝ :=
  primeSpaceSteinResponseKernel xiPrimeSpaceLogDerivativeResponse p r

/-- The actual Xi-response source kernel has the same exact rank-two Stein displacement. -/
theorem xiPrimeSpaceSteinKernel_displacement (p r : Nat.Primes) :
    xiPrimeSpaceSteinKernel p r -
        xiTransversePrimeApertureDiskNode 1 p *
          xiTransversePrimeApertureDiskNode 1 r * xiPrimeSpaceSteinKernel p r =
      primeSpaceSteinResponseBoundaryVector xiPrimeSpaceLogDerivativeResponse p *
          primeSpaceSteinBoundaryVector r +
        primeSpaceSteinBoundaryVector p *
          primeSpaceSteinResponseBoundaryVector xiPrimeSpaceLogDerivativeResponse r := by
  exact primeSpaceSteinResponseKernel_displacement xiPrimeSpaceLogDerivativeResponse p r

/-- Finite Xi-response prime matrices are exact diagonal congruences of the Euler-ray
logarithmic-derivative matrices. -/
theorem xiPrimeSpaceFiniteSteinMatrix_eq_cayleyCongruence
    {I : Type*} [Fintype I] [DecidableEq I] (p : I → Nat.Primes) :
    primeSpaceFiniteSteinResponseMatrix p xiPrimeSpaceLogDerivativeResponse =
      Matrix.diagonal (fun i => primeSpaceCayleyCongruenceWeight (p i)) *
        primeSpaceFiniteEulerRayResponseMatrix p xiPrimeSpaceLogDerivativeResponse *
          Matrix.diagonal (fun i => primeSpaceCayleyCongruenceWeight (p i)) := by
  exact primeSpaceFiniteSteinResponseMatrix_eq_cayleyCongruence p
    xiPrimeSpaceLogDerivativeResponse

end

end RHTower
