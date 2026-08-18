import GaloisForLFunctions.RHTower.BakerGeneralProof.BakerGeneralStageSmallness
import GaloisForLFunctions.RHTower.BakerGeneralProof.PolynomialAuxiliaryKernelTransition

/-!
# Long extrapolation for the general Baker auxiliary matrix

One exact component-jet extrapolation is iterated on auxiliary-matrix kernels: the same nonzero
Siegel vector is retained while the consecutive sample range gains one power of the parameter and
the component cutoff is halved.  All analytic work is isolated in the stagewise scalar inequality.
-/

open scoped Classical
open BigOperators NumberField
open Filter Topology

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

namespace GeneralParameters

theorem one_le_stageRadius_cast {q k : ℕ} (hq : 1 ≤ q) :
    (1 : ℝ) ≤ ((stageRadius q k : ℕ) : ℝ) := by
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [stageRadius_cast]
  nlinarith [one_le_pow₀ (n := k + 3) hq1R]

theorem stageSampleCount_lt_stageRadius {q k : ℕ} (hq : 1 ≤ q) :
    ((stageSampleCount q k : ℕ) : ℝ) < ((stageRadius q k : ℕ) : ℝ) := by
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [stageSampleCount_cast, stageRadius_cast]
  nlinarith [one_le_pow₀ (n := k + 3) hq1R,
    pow_le_pow_right₀ hq1R (show k + 2 ≤ k + 3 by omega)]

theorem stageSample_le_stageRadius {q k s : ℕ} (hq : 1 ≤ q)
    (hs : s ≤ stageSampleCount q (k + 1)) : (s : ℝ) ≤ ((stageRadius q k : ℕ) : ℝ) := by
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hsR : (s : ℝ) ≤ (q : ℝ) ^ (k + 3) := by
    have h1 : s ≤ q ^ (k + 3) := by
      refine le_trans hs (le_of_eq ?_)
      unfold stageSampleCount
      congr 1
    exact_mod_cast h1
  rw [stageRadius_cast]
  nlinarith [one_le_pow₀ (n := k + 3) hq1R]

/-- Finite long extrapolation: one coefficient vector stays in the auxiliary kernel while the
sample interval grows and the component cutoff is halved. -/
theorem polynomialAuxiliaryMatrix_kernel_iterate
    (R : SolvedRelation) (c d : ℤ) (hc : c ≠ 0)
    (hcomp : ∀ dir, IsIntegral ℤ (R.scaledComponentCoeff c dir))
    (hbase : ∀ i, IsIntegral ℤ (R.scaledBase d i))
    (hd : d ≠ 0) (u : ℕ) (hq : 1 ≤ structuredBase R.n u)
    (eta : R.AuxiliaryColumn (additiveWidth R.n (structuredBase R.n u))
      (exponentWidth R.n (structuredBase R.n u)) → 𝓞 R.CoefficientField)
    (Heta : ℝ) (hHeta0 : 0 ≤ Heta)
    (hEta : ∀ col, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (eta col)) ≤
      Heta)
    (hker0 : Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase
      (additiveWidth R.n (structuredBase R.n u)) (exponentWidth R.n (structuredBase R.n u))
      (stageSampleCount (structuredBase R.n u) 0)
      (stageOrder R.n (structuredBase R.n u) 0)) eta = 0)
    (K : ℕ) (hK : K ≤ iterationLength R.n)
    (hsmall : ∀ k < K, ∀ (nu : R.Direction → ℕ) (s : ℕ),
      (∀ dir, nu dir ≤ stageOrder R.n (structuredBase R.n u) (k + 1)) →
      s ≤ stageSampleCount (structuredBase R.n u) (k + 1) →
      (|(d : ℝ)| ^ (s * (R.n * exponentWidth R.n (structuredBase R.n u))) *
        (((s + stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ) ^
            (stageOrder R.n (structuredBase R.n u) (k + 1) *
              stageSampleCount (structuredBase R.n u) k) *
          (R.jetScalarBound c (additiveWidth R.n (structuredBase R.n u))
              (exponentWidth R.n (structuredBase R.n u)) nu Heta
              ((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) /
            (((stageRadius (structuredBase R.n u) k : ℕ) : ℝ) -
              ((stageSampleCount (structuredBase R.n u) k : ℕ) : ℝ)) ^
              (stageOrder R.n (structuredBase R.n u) (k + 1) *
                stageSampleCount (structuredBase R.n u) k)))) *
        R.jetHouseScalarBound c d (additiveWidth R.n (structuredBase R.n u))
          (exponentWidth R.n (structuredBase R.n u)) nu Heta s ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    ∀ k ≤ K, Matrix.mulVec (R.polynomialAuxiliaryMatrix c d hcomp hbase
      (additiveWidth R.n (structuredBase R.n u)) (exponentWidth R.n (structuredBase R.n u))
      (stageSampleCount (structuredBase R.n u) k)
      (stageOrder R.n (structuredBase R.n u) k)) eta = 0 := by
  intro k hk
  induction k with
  | zero => exact hker0
  | succ k ih =>
      have hkK : k < K := by omega
      have hkJ : k ≤ iterationLength R.n := by omega
      have hprev := ih (by omega)
      apply R.polynomialAuxiliaryMatrix_kernel_extrapolate c d hc hcomp hbase
        (one_le_additiveWidth hq) eta hprev hd hHeta0 hEta
        (stageOrder R.n (structuredBase R.n u) (k + 1))
        (le_of_eq (two_mul_stageOrder_succ_structured R.n u k hkJ))
        (radius := ((stageRadius (structuredBase R.n u) k : ℕ) : ℝ))
        (one_le_stageRadius_cast hq) (stageSampleCount_lt_stageRadius hq)
        (stageSampleCount (structuredBase R.n u) (k + 1))
      · intro sample
        exact stageSample_le_stageRadius hq (le_of_lt sample.isLt)
      · intro sample nu
        exact hsmall k hkK (fun dir => (nu dir : ℕ)) (sample : ℕ)
          (fun dir => le_of_lt (nu dir).isLt) (le_of_lt sample.isLt)

end GeneralParameters

end GaloisForLFunctions.RHTower.BakerGeneralProof
