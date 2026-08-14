import GaloisForLFunctions.HTGeometry.PeriodIntegralIndependenceWitness
import GaloisForLFunctions.HTGeometry.EllipticThetaLogCoordinate
import GaloisForLFunctions.HTGeometry.PrimeLogPeriodHypertranscendence

/-!
# The period whose elliptic nome is the reciprocal prime

Scaling the imaginary prime logarithm by `2π` turns its elliptic nome into `1/p` exactly.  The
scaling does not disturb integral independence, because a relation between the scaled periods and
`1` has the same real and imaginary parts as the unscaled one up to the positive factor `2π`.  So
the occupation nome family of the prime-linear completion is realized by a genuine upper-half-plane
period family with a rank-three minor.

* `HTGeometry.primeNomePeriod`, `HTGeometry.ellipticNome_primeNomePeriod`;
* `HTGeometry.periodsIntegrallyIndependent_primeNomePeriod`;
* `HTGeometry.hypertranscendentalOver_multipleEllipticGammaMero_primeNome`.
-/

open Complex Finset
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

namespace HTGeometry

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The period whose elliptic nome is the reciprocal of the prime. -/
def primeNomePeriod (q : ι → Nat.Primes) : ι → ℂ :=
  fun i => Complex.I * ((Real.log (q i : ℕ) / (2 * Real.pi) : ℝ) : ℂ)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem primeNomePeriod_re (q : ι → Nat.Primes) (i : ι) :
    (primeNomePeriod q i).re = 0 := by
  unfold primeNomePeriod
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem primeNomePeriod_im (q : ι → Nat.Primes) (i : ι) :
    (primeNomePeriod q i).im = Real.log (q i : ℕ) / (2 * Real.pi) := by
  unfold primeNomePeriod
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem primeNomePeriod_im_pos (q : ι → Nat.Primes) (i : ι) :
    0 < (primeNomePeriod q i).im := by
  rw [primeNomePeriod_im]
  have hlog : 0 < Real.log (q i : ℕ) := Real.log_pos (by exact_mod_cast (q i).2.one_lt)
  have hpi : 0 < 2 * Real.pi := by positivity
  positivity

omit [Fintype ι] [DecidableEq ι] in
/-- **The nome of the scaled prime period is the reciprocal prime.** -/
theorem ellipticNome_primeNomePeriod (q : ι → Nat.Primes) (i : ι) :
    ellipticNome (primeNomePeriod q i) = (((q i : ℕ) : ℂ))⁻¹ := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hq : (0 : ℝ) < ((q i : ℕ) : ℝ) := by exact_mod_cast (q i).2.pos
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (primeNomePeriod q i)
      = ((-Real.log (q i : ℕ) : ℝ) : ℂ) := by
    unfold primeNomePeriod
    have hcast : ((Real.log (q i : ℕ) / (2 * Real.pi) : ℝ) : ℂ)
        = ((Real.log (q i : ℕ) : ℝ) : ℂ) / ((2 * Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast]
    have hpic : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      simp
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [ellipticNome, harg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hq]
  simp

omit [DecidableEq ι] in
theorem periodsIntegrallyIndependent_primeNomePeriod {q : ι → Nat.Primes}
    (hq : Function.Injective q) : PeriodsIntegrallyIndependent (primeNomePeriod q) := by
  classical
  intro m n hrel
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hre : (m : ℝ) = 0 := by
    have h := congrArg Complex.re hrel
    simpa only [Complex.add_re, Complex.re_sum, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_re, Complex.mul_re, primeNomePeriod_re, primeNomePeriod_im, mul_zero, zero_mul,
      sub_zero, Finset.sum_const_zero, add_zero] using h
  have him : ∑ i, (n i : ℝ) * (Real.log (q i : ℕ) / (2 * Real.pi)) = 0 := by
    have h := congrArg Complex.im hrel
    simpa only [Complex.add_im, Complex.im_sum, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_im, Complex.mul_im, primeNomePeriod_re, primeNomePeriod_im, mul_zero, zero_mul,
      add_zero, zero_add] using h
  have himscaled : ∑ i, (n i : ℝ) * Real.log (q i : ℕ) = 0 := by
    have hfac : ∑ i, (n i : ℝ) * (Real.log (q i : ℕ) / (2 * Real.pi))
        = (∑ i, (n i : ℝ) * Real.log (q i : ℕ)) / (2 * Real.pi) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfac, div_eq_zero_iff] at him
    rcases him with him | him
    · exact him
    · exact absurd him hpi.ne'
  have hind : LinearIndependent ℤ fun i : ι => Real.log (q i : ℕ) :=
    logPrime_linearIndependent_int.comp q hq
  have hzero : ∀ i ∈ (univ : Finset ι), n i = 0 := by
    refine linearIndependent_iff'.mp hind univ n ?_
    simpa [zsmul_eq_mul] using himscaled
  exact ⟨by exact_mod_cast hre, fun i => hzero i (mem_univ i)⟩

local instance primeNomeHTUnivDomain :
    IsDomain (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTUnivDomain

local instance primeNomeHTComplexAlgebraAnalytic :
    Algebra ℂ (Bottcher.analyticSubring Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraAnalytic

local instance primeNomeHTComplexAlgebraMero :
    Algebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexAlgebraMero

local instance primeNomeHTMeroDifferential :
    Differential (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroDifferential

local instance primeNomeHTComplexDifferential : Differential ℂ :=
  multipleEllipticGammaHTComplexDifferential

local instance primeNomeHTMeroCharZero :
    CharZero (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTMeroCharZero

local instance primeNomeHTComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTComplexDifferentialAlgebra

local instance primeNomeHTCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  multipleEllipticGammaHTCoordinateDifferential

local instance primeNomeHTCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (Bottcher.meroField Set.univ) :=
  multipleEllipticGammaHTCoordinateDifferentialAlgebra


/-- **Reciprocal-prime nomes already force hypertranscendence.** -/
theorem hypertranscendentalOver_multipleEllipticGammaMero_primeNome (q : ι → Nat.Primes)
    (hq : Function.Injective q) (hcard : 2 ≤ Fintype.card ι) :
    HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaMero (primeNomePeriod q) (primeNomePeriod_im_pos q)) ∧
      HypertranscendentalOver meromorphicRationalCoordinateField
        (multipleEllipticGammaLogDerivMero (primeNomePeriod q) (primeNomePeriod_im_pos q)) := by
  have hminor : MultipleEllipticGammaHasRankThreeMinor (primeNomePeriod q) :=
    multipleEllipticGammaHasRankThreeMinor_of_periodsIntegrallyIndependent (primeNomePeriod q)
      (periodsIntegrallyIndependent_primeNomePeriod hq) hcard
  have h := multipleEllipticGamma_rankThreeMinor_reflectionHypertranscendenceUniversality
    (primeNomePeriod q) (primeNomePeriod_im_pos q) hminor
  exact ⟨h.1, h.2.1⟩

end HTGeometry

end

end GaloisForLFunctions
