import GaloisForLFunctions.RHTower.HermiteEvenCarrier
import GaloisForLFunctions.HilbertMetric.SlaterPluckerConnector

/-!
# Hermite-even Slater--Pluecker connector

The step-four Hermite family is already an orthonormal Fourier-fixed family in the complex even
carrier.  Realifying its inner product gives a square Gram coordinate frame.  Since every orbital
of that square frame is occupied, its canonical Pluecker partition is one exponential carrying
the total degree.  Its logarithm is globally affine: the first jet is the total degree and every
higher curvature contribution, beginning with the second jet, vanishes.  For the actual step-four
Hermite degree `4j`, the first `m` modes carry the closed total charge `2m(m-1)`.

This is a finite static identity.  It assumes no ambient finite-dimensionality, aperture limit,
zero-location statement, or Riemann-hypothesis premise.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

local instance evenSubspaceRealInnerProductSpace : InnerProductSpace ℝ evenSubspace :=
  InnerProductSpace.rclikeToReal ℂ evenSubspace

/-- The complex orthonormal step-four Hermite block remains orthonormal after realification. -/
theorem orthonormal_hermiteEvenUnit_real (m : ℕ) :
    Orthonormal ℝ (fun j : Fin m => hermiteEvenUnit (j : ℕ)) := by
  have hc := orthonormal_hermiteEvenUnit m
  rw [orthonormal_iff_ite] at hc ⊢
  intro i j
  rw [real_inner_eq_re_inner, hc i j]
  split <;> simp

/-- Real Gram coordinates of the first `m` Fourier-fixed Hermite vectors. -/
def hermiteEvenRealGramCoordinates (m : ℕ) : Fin m → Fin m → ℝ :=
  orthonormalRealGramCoordinates ℝ (fun j : Fin m => hermiteEvenUnit (j : ℕ))

@[simp] theorem hermiteEvenRealGramCoordinates_apply (m : ℕ) (i j : Fin m) :
    hermiteEvenRealGramCoordinates m i j = if i = j then 1 else 0 := by
  simpa [hermiteEvenRealGramCoordinates] using
    orthonormalRealGramCoordinates_apply ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) i j

/-- The actual Hermite Gram coordinates discharge HilbertMetric's abstract orthonormal coordinate
frame interface. -/
theorem hermiteEvenRealGramCoordinates_isOrthonormalCoordinateFrame (m : ℕ) :
    IsOrthonormalCoordinateFrame (hermiteEvenRealGramCoordinates m) := by
  simpa [hermiteEvenRealGramCoordinates] using
    orthonormalRealGramCoordinates_isOrthonormalCoordinateFrame ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m)

/-- The canonical degree of the `j`-th member of the step-four Hermite family, matching its actual
Hermite index `4j`. -/
def hermiteEvenStepFourDegree {m : ℕ} (j : Fin m) : ℕ := 4 * (j : ℕ)

/-- The first `m` step-four Hermite modes carry total degree `2m(m-1)`. -/
theorem sum_hermiteEvenStepFourDegree (m : ℕ) :
    (∑ j : Fin m, (hermiteEvenStepFourDegree j : ℝ)) =
      2 * (m : ℝ) * ((m : ℝ) - 1) := by
  have hsum : (∑ j : Fin m, ((j : ℕ) : ℝ)) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih]
        push_cast
        ring
  simp only [hermiteEvenStepFourDegree, Nat.cast_mul, Nat.cast_ofNat]
  rw [← Finset.mul_sum, hsum]
  ring

/-- The exponential Gram path of the square Hermite frame is diagonal, with one exponential degree
weight on each occupied orbital. -/
theorem exponentialFeatureGram_hermiteEvenRealGramCoordinates
    (m : ℕ) (degree : Fin m → ℕ) (s : ℝ) :
    exponentialFeatureGram (hermiteEvenRealGramCoordinates m) degree s =
      Matrix.diagonal (fun k => Real.exp (s * (degree k : ℝ))) := by
  simpa [hermiteEvenRealGramCoordinates] using
    exponentialFeatureGram_orthonormalRealGramCoordinates ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) degree s

/-- **Exact Hermite Pluecker partition.**  Along exponential degree scaling, the canonical feature
volume of the fully occupied Hermite block is one exponential carrying the total orbital degree. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_exp_eq_exp_totalDegree
    (m : ℕ) (degree : Fin m → ℕ) (s : ℝ) :
    canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
        degree (Real.exp s) =
      Real.exp (s * ∑ k, (degree k : ℝ)) := by
  simpa [hermiteEvenRealGramCoordinates] using
    orthonormalRealGram_canonicalFeatureVolume_exp_eq_exp_totalDegree ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) degree s

/-- **Canonical step-four Hermite partition.**  Using the actual Hermite degree `4j`, the fully
occupied Pluecker partition is one exponential with charge `2m(m-1)`. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_exp_eq
    (m : ℕ) (s : ℝ) :
    canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
        hermiteEvenStepFourDegree (Real.exp s) =
      Real.exp (s * (2 * (m : ℝ) * ((m : ℝ) - 1))) := by
  rw [hermiteEvenRealGram_canonicalFeatureVolume_exp_eq_exp_totalDegree]
  rw [sum_hermiteEvenStepFourDegree]

/-- The logarithm of the full Hermite Pluecker partition is globally affine in the scaling
parameter, not merely flat to second order at the origin. -/
theorem hermiteEvenRealGram_log_canonicalFeatureVolume_exp_eq
    (m : ℕ) (degree : Fin m → ℕ) (s : ℝ) :
    Real.log (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
        degree (Real.exp s)) = s * ∑ k, (degree k : ℝ) := by
  simpa [hermiteEvenRealGramCoordinates] using
    orthonormalRealGram_log_canonicalFeatureVolume_exp_eq ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) degree s

/-- **Complete Hermite log-jet law.**  The full Hermite Pluecker log-partition has only its affine
zero jet and constant first jet; every derivative of order at least two vanishes at every scaling
parameter. -/
theorem hermiteEvenRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq
    (m : ℕ) (degree : Fin m → ℕ) (order : ℕ) (s : ℝ) :
    iteratedDeriv order (fun t => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp t))) s =
      if order = 0 then s * ∑ k, (degree k : ℝ)
      else if order = 1 then ∑ k, (degree k : ℝ) else 0 := by
  simpa [hermiteEvenRealGramCoordinates] using
    orthonormalRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) degree order s

/-- **Complete canonical Hermite log-jet law.**  The actual step-four degree partition has affine
logarithm with slope `2m(m-1)`; every log jet of order at least two vanishes globally. -/
theorem hermiteEvenRealGram_iteratedDeriv_log_canonicalFeatureVolume_stepFourDegree_eq
    (m order : ℕ) (s : ℝ) :
    iteratedDeriv order (fun t => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          hermiteEvenStepFourDegree (Real.exp t))) s =
      if order = 0 then s * (2 * (m : ℝ) * ((m : ℝ) - 1))
      else if order = 1 then 2 * (m : ℝ) * ((m : ℝ) - 1) else 0 := by
  rw [hermiteEvenRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq]
  rw [sum_hermiteEvenStepFourDegree]

/-- Full occupancy of the square Hermite coordinate frame makes its additive spectral mean the
sum of the assigned orbital energies. -/
theorem slaterSpectralMean_hermiteEvenRealGramCoordinates
    (m : ℕ) (energy : Fin m → ℝ) :
    slaterSpectralMean (hermiteEvenRealGramCoordinates m) energy = ∑ k, energy k := by
  simpa [hermiteEvenRealGramCoordinates] using
    slaterSpectralMean_orthonormalRealGramCoordinates ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) energy

/-- Full occupancy has no residual degree fluctuation: the Slater compression variance of the
square Hermite coordinate frame vanishes for every energy assignment. -/
theorem slaterSpectralVariance_hermiteEvenRealGramCoordinates
    (m : ℕ) (energy : Fin m → ℝ) :
    slaterSpectralVariance (hermiteEvenRealGramCoordinates m) energy = 0 := by
  simpa [hermiteEvenRealGramCoordinates] using
    slaterSpectralVariance_orthonormalRealGramCoordinates ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) energy

/-- **Exact Hermite Pluecker Fano law.**  Full occupancy makes the first log jet minus curvature
equal the total orbital degree, with no bandwidth restriction. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree
    (m : ℕ) (degree : Fin m → ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s)))) 0 = ∑ k, (degree k : ℝ) := by
  simpa [hermiteEvenRealGramCoordinates] using
    orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) degree

/-- For the canonical step-four degree, the Hermite Pluecker log-Fano margin is exactly the total
charge `2m(m-1)`. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_eq
    (m : ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          hermiteEvenStepFourDegree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          hermiteEvenStepFourDegree (Real.exp s)))) 0 =
        2 * (m : ℝ) * ((m : ℝ) - 1) := by
  rw [hermiteEvenRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree]
  rw [sum_hermiteEvenStepFourDegree]

/-- **Canonical Hermite Fano equality threshold.**  The step-four Hermite Pluecker margin
vanishes exactly for the empty block and the one-orbital block. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_eq_zero_iff
    (m : ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          hermiteEvenStepFourDegree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          hermiteEvenStepFourDegree (Real.exp s)))) 0 = 0 ↔
      m ≤ 1 := by
  rw [hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_eq]
  constructor
  · intro hzero
    by_contra hm
    have hmNat : 2 ≤ m := by omega
    have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmNat
    nlinarith
  · intro hm
    have hmCases : m = 0 ∨ m = 1 := by omega
    rcases hmCases with rfl | rfl <;> norm_num

/-- **Canonical Hermite strict Fano threshold.**  A fully occupied step-four Hermite block has
strictly positive Pluecker log-Fano margin exactly when it contains at least two orbitals. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_pos_iff
    (m : ℕ) :
    0 < deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          hermiteEvenStepFourDegree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          hermiteEvenStepFourDegree (Real.exp s)))) 0 ↔
      2 ≤ m := by
  rw [hermiteEvenRealGram_canonicalFeatureVolume_stepFourDegree_logFanoMargin_eq]
  constructor
  · intro hpos
    by_contra hm
    have hmNat : m ≤ 1 := by omega
    have hmCases : m = 0 ∨ m = 1 := by omega
    rcases hmCases with rfl | rfl <;> norm_num at hpos
  · intro hm
    have hmReal : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith

/-- Every fully occupied finite Hermite block is unconditionally Fano-underdispersed for arbitrary
natural orbital degrees; positivity and quartic upper bounds are unnecessary. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_logFanoMargin_nonnegative
    (m : ℕ) (degree : Fin m → ℕ) :
    0 ≤ deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s)))) 0 := by
  rw [hermiteEvenRealGram_canonicalFeatureVolume_logFanoMargin_eq_totalDegree]
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **Hermite spectral-floor rigidity.**  A nonempty fully occupied Hermite block attains the
universal spectral-band floor exactly when the band has width one and all orbital degrees equal its
lower endpoint. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_logFanoMargin_eq_lower_bound_iff
    (m : ℕ) (degree : Fin m → ℕ) (lower upper : ℝ) (hm : 0 < m)
    (hlower : ∀ k, lower ≤ (degree k : ℝ))
    (hupper : ∀ k, (degree k : ℝ) ≤ upper) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s))) 0 -
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s)))) 0 =
        (m : ℝ) * (lower - (upper - lower - 1) ^ 2 / 4) ↔
      upper = lower + 1 ∧ ∀ k, (degree k : ℝ) = lower := by
  simpa [hermiteEvenRealGramCoordinates] using
    orthonormalRealGram_canonicalFeatureVolume_logFanoMargin_eq_lower_bound_iff ℝ
      (fun j : Fin m => hermiteEvenUnit (j : ℕ))
      (orthonormal_hermiteEvenUnit_real m) degree lower upper hm hlower hupper

/-- **Exact Hermite--Slater--Pluecker log-jet law.**  For every finite step-four Hermite block and
every natural orbital-degree assignment, the first logarithmic jet of the canonical Pluecker
partition is the total occupied degree and the second logarithmic jet is exactly zero. -/
theorem hermiteEvenRealGram_canonicalFeatureVolume_logJets_exact
    (m : ℕ) (degree : Fin m → ℕ) :
    deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s))) 0 = ∑ k, (degree k : ℝ) ∧
      deriv (deriv (fun s => Real.log
        (canonicalFeatureVolume (hermiteEvenRealGramCoordinates m) (fun _ => 1)
          degree (Real.exp s)))) 0 = 0 := by
  constructor
  · simpa [iteratedDeriv_succ] using
      hermiteEvenRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq
        m degree 1 0
  · simpa [iteratedDeriv_succ] using
      hermiteEvenRealGram_iteratedDeriv_log_canonicalFeatureVolume_exp_eq
        m degree 2 0

end

end RHTower
