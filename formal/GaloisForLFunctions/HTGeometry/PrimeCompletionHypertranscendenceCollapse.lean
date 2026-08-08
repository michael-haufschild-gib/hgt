import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPeriodRankDichotomy
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaInversion
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGamma
import GaloisForLFunctions.HTGeometry.PeriodIntegralIndependenceWitness
import GaloisForLFunctions.HTGeometry.TrigLinearDA
import GaloisForLFunctions.HTGeometry.SmoothNumbers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# Prime completion can collapse hypertranscendence

For each finite prime set `S`, the backward multiple-elliptic-Gamma product with periods

`τₚ = i log(p) / π`

is hypertranscendental in its additive variable as soon as `S` contains two primes. Its nomes are
exactly `p⁻²`, so the directed all-prime completion enumerates every positive integer once by unique
factorization. The completed occupation product therefore becomes Euler's sine product:

`π t · ∏ₙ≥1 (1 - t²/n²) = sin(π t)`.

Thus a cofinal family of source-pure hypertranscendental prime-period products converges to a
differentially algebraic trigonometric carrier. Hypertranscendence is not stable under prime
completion, even though the completion retains the full integer Euler spectrum.
-/

open Complex Set Filter Topology
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher
open HTGeometry

noncomputable section

local instance primeCompletionDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance primeCompletionComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance primeCompletionMeroDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance primeCompletionRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

local instance primeCompletionRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance primeCompletionRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ

local instance primeCompletionCoordinateDifferential :
    Differential meromorphicRationalCoordinateField :=
  derivationClosedDifferential _
    meromorphicRationalCoordinateField_derivationClosed

local instance primeCompletionCoordinateDifferentialAlgebra :
    DifferentialAlgebra meromorphicRationalCoordinateField
      (meroField Set.univ) :=
  ⟨fun x ↦ derivationClosedDifferential_apply
    meromorphicRationalCoordinateField
    meromorphicRationalCoordinateField_derivationClosed x⟩

local instance primeCompletionMeroCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap ℂ (meroField Set.univ)).injective

/-! ## Finite backward products are hypertranscendental -/

/-- A rank-three minor forces the backward entire factor itself to be hypertranscendental.

If the backward factor were differentially algebraic, reflection would make the forward factor
differentially algebraic as well. Their parity-dependent product or quotient would then make the
genuine multiple elliptic Gamma differentially algebraic, contradicting the exact period-rank law.
-/
theorem hypertranscendental_multipleEllipticGammaBackwardProduct_of_rankThreeMinor
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hminor : MultipleEllipticGammaHasRankThreeMinor τ) :
    Hypertranscendental (multipleEllipticGammaBackwardProduct τ) := by
  intro hB
  have hBan : AnalyticOnNhd ℂ
      (multipleEllipticGammaBackwardProduct τ) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact differentiable_multipleEllipticGammaBackwardProduct hτ
  have hBfield :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (multipleEllipticGammaBackwardAnalytic τ hτ)) := by
    exact
      HTGeometry.differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
        hBan hB
  let T : ℂ := ∑ i, τ i
  have hF : DifferentiallyAlgebraic
      (multipleEllipticGammaForwardProduct τ) := by
    have href : multipleEllipticGammaForwardProduct τ =
        fun z => multipleEllipticGammaBackwardProduct τ (-z + T) := by
      funext z
      have h := multipleEllipticGammaForwardProduct_reflection τ (T - z)
      simpa [T, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    rw [href]
    have hs := hB.comp_add_const T
    have hsc := hs.comp_const_mul_uncond (by norm_num : (-1 : ℂ) ≠ 0)
    simpa using hsc
  have hFan : AnalyticOnNhd ℂ
      (multipleEllipticGammaForwardProduct τ) Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact differentiable_multipleEllipticGammaForwardProduct hτ
  have hFfield :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (multipleEllipticGammaForwardAnalytic τ hτ)) := by
    exact
      HTGeometry.differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
        hFan hF
  have hfull : DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaMero τ hτ) := by
    by_cases hcard : Even (Fintype.card ι)
    · simp only [multipleEllipticGammaMero, hcard, if_true]
      exact HTGeometry.differentialAlgebraicOver_div hFfield hBfield
    · simp only [multipleEllipticGammaMero, hcard, if_false]
      exact HTGeometry.differentialAlgebraicOver_mul hFfield hBfield
  letI : Nonempty ι := ⟨hminor.choose⟩
  exact
    (hypertranscendentalOver_multipleEllipticGammaMero_iff_rankThreeMinor τ hτ).2
      hminor hfull

/-! ## Prime-square periods and nomes -/

/-- Prime nome at inverse-square temperature. -/
def primeSquareNome (p : Nat.Primes) : ℂ :=
  (((p : ℕ) : ℂ)⁻¹) ^ 2

/-- Additive period whose elliptic nome is `p⁻²`. -/
def primeSquarePeriod (p : Nat.Primes) : ℂ :=
  Complex.I * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ)

@[simp] theorem primeSquarePeriod_re (p : Nat.Primes) :
    (primeSquarePeriod p).re = 0 := by
  rw [primeSquarePeriod, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
    zero_add, sub_zero, mul_zero]

@[simp] theorem primeSquarePeriod_im (p : Nat.Primes) :
    (primeSquarePeriod p).im = Real.log ((p : ℕ) : ℝ) / Real.pi := by
  rw [primeSquarePeriod, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul,
    zero_add, sub_zero, mul_zero]
  rw [div_eq_mul_inv]

theorem primeSquarePeriod_im_pos (p : Nat.Primes) :
    0 < (primeSquarePeriod p).im := by
  rw [primeSquarePeriod_im]
  exact div_pos (Real.log_pos (by exact_mod_cast p.2.one_lt)) Real.pi_pos

/-- The period `i log(p)/π` has nome exactly `p⁻²`. -/
theorem ellipticNome_primeSquarePeriod (p : Nat.Primes) :
    ellipticNome (primeSquarePeriod p) = primeSquareNome p := by
  rw [ellipticNome, primeSquarePeriod, primeSquareNome]
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hexp :
      Complex.exp (-(2 : ℂ) *
          ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) =
        (((p : ℕ) : ℂ)⁻¹) ^ 2 := by
    rw [show (-(2 : ℂ) *
        ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) =
      ((-(2 * Real.log ((p : ℕ) : ℝ)) : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_exp]
    norm_cast
    rw [Real.exp_neg, show 2 * Real.log ((p : ℕ) : ℝ) =
      Real.log ((p : ℕ) : ℝ) + Real.log ((p : ℕ) : ℝ) by ring,
      Real.exp_add, Real.exp_log hp]
    norm_num [pow_two]
  rw [show 2 * (Real.pi : ℂ) * I *
      (I * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) / ((Real.pi : ℝ) : ℂ)) =
      -(2 : ℂ) * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) by
    field_simp [Real.pi_ne_zero]
    rw [I_sq]
    ring]
  exact hexp

/-- Distinct prime-square periods have no integral relation with the unit period. -/
theorem periodsIntegrallyIndependent_primeSquarePeriod
    {ι : Type} [Fintype ι] {q : ι → Nat.Primes}
    (hq : Function.Injective q) :
    PeriodsIntegrallyIndependent (fun i => primeSquarePeriod (q i)) := by
  classical
  intro m n hrel
  have hre : (m : ℝ) = 0 := by
    have h := congrArg Complex.re hrel
    simpa only [Complex.add_re, Complex.re_sum, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_re, Complex.mul_re, primeSquarePeriod_re, primeSquarePeriod_im,
      mul_zero, zero_mul, sub_zero, Finset.sum_const_zero, add_zero] using h
  have himScaled :
      ∑ i, (n i : ℝ) *
        (Real.log (q i : ℕ) / Real.pi) = 0 := by
    have h := congrArg Complex.im hrel
    simpa only [Complex.add_im, Complex.im_sum, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_im, Complex.mul_im, primeSquarePeriod_re, primeSquarePeriod_im,
      mul_zero, zero_mul, add_zero, zero_add] using h
  have him : ∑ i, (n i : ℝ) * Real.log (q i : ℕ) = 0 := by
    calc
      ∑ i, (n i : ℝ) * Real.log (q i : ℕ) =
          Real.pi * ∑ i, (n i : ℝ) *
            (Real.log (q i : ℕ) / Real.pi) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              field_simp [Real.pi_ne_zero]
      _ = 0 := by rw [himScaled, mul_zero]
  have hind : LinearIndependent ℤ fun i : ι => Real.log (q i : ℕ) :=
    logPrime_linearIndependent_int.comp q hq
  have hzero : ∀ i ∈ (Finset.univ : Finset ι), n i = 0 := by
    refine linearIndependent_iff'.mp hind Finset.univ n ?_
    simpa [zsmul_eq_mul] using him
  exact ⟨by exact_mod_cast hre, fun i => hzero i (Finset.mem_univ i)⟩

/-- Every finite prime set with at least two elements is in the hypertranscendental phase. -/
theorem hypertranscendental_primeSquareBackwardProduct
    (S : Finset Nat.Primes) (hS : 2 ≤ S.card) :
    Hypertranscendental
      (multipleEllipticGammaBackwardProduct
        (fun p : S => primeSquarePeriod p)) := by
  classical
  let τ : S → ℂ := fun p => primeSquarePeriod p
  have hτ : ∀ p, 0 < (τ p).im := fun p => primeSquarePeriod_im_pos p
  have hQ : PeriodsIntegrallyIndependent τ :=
    periodsIntegrallyIndependent_primeSquarePeriod Subtype.val_injective
  have hminor : MultipleEllipticGammaHasRankThreeMinor τ :=
    multipleEllipticGammaHasRankThreeMinor_of_periodsIntegrallyIndependent
      τ hQ (by simpa using hS)
  exact
    hypertranscendental_multipleEllipticGammaBackwardProduct_of_rankThreeMinor
      τ hτ hminor

/-! ## Unique-factorization completion and Euler sine collapse -/

/-- Unique factorization identifies prime occupations with positive integers. -/
def primeOccupationEquivPNat : (Nat.Primes →₀ ℕ) ≃ ℕ+ where
  toFun ν := ⟨primeProduct ν, primeProduct_pos ν⟩
  invFun n := primeExponentVector n
  left_inv ν := by
    apply primeProduct_injective
    change primeProduct (primeExponentVector (primeProduct ν)) = primeProduct ν
    rw [primeProduct_primeExponentVector (primeProduct_pos ν).ne']
  right_inv n := by
    apply Subtype.ext
    exact primeProduct_primeExponentVector n.pos.ne'

/-- A prime-square occupation monomial is the inverse square of its represented integer. -/
theorem nomeMonomial_primeSquareNome (ν : Nat.Primes →₀ ℕ) :
    HTGeometry.nomeMonomial primeSquareNome ν =
      ((((primeProduct ν : ℕ) : ℂ)⁻¹) ^ 2) := by
  classical
  induction ν using Finsupp.induction with
  | zero =>
      simp [HTGeometry.nomeMonomial, primeSquareNome, primeProduct]
  | single_add a b f haf hb ih =>
      have hleft :
          HTGeometry.nomeMonomial primeSquareNome (Finsupp.single a b + f) =
            primeSquareNome a ^ b * HTGeometry.nomeMonomial primeSquareNome f := by
        unfold HTGeometry.nomeMonomial
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          simp
        · intro p
          simp
        · intro p k l
          rw [pow_add]
      have hprod :
          primeProduct (Finsupp.single a b + f) =
            (a : ℕ) ^ b * primeProduct f := by
        unfold primeProduct
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          simp
        · intro p
          simp
        · intro p k l
          rw [pow_add]
      rw [hleft, ih, hprod, Nat.cast_mul, Nat.cast_pow]
      simp only [primeSquareNome]
      field_simp
      ring

theorem primaryFactor_zero_genus (z : ℂ) :
    HTGeometry.primaryFactor 0 z = 1 - z := by
  simp [HTGeometry.primaryFactor, HTGeometry.primaryExponent]

/-- The all-prime genus-zero completion is Euler's sine product. The polynomial gauge `πt`
removes the removable singularity at the origin, so the identity is global. -/
theorem primeSquareCompletion_mul_eq_sin (t : ℂ) :
    (Real.pi : ℂ) * t *
        HTGeometry.infiniteMultipleEllipticGamma 0 primeSquareNome (t ^ 2) =
      Complex.sin ((Real.pi : ℂ) * t) := by
  have hrewrite :
      HTGeometry.infiniteMultipleEllipticGamma 0 primeSquareNome (t ^ 2) =
        ∏' n : ℕ, ((1 : ℂ) - t ^ 2 / ((n : ℂ) + 1) ^ 2) := by
    rw [HTGeometry.infiniteMultipleEllipticGamma,
      HTGeometry.canonicalWeightProduct]
    calc
      (∏' ν : Nat.Primes →₀ ℕ,
          HTGeometry.primaryFactor 0
            (t ^ 2 * HTGeometry.nomeMonomial primeSquareNome ν)) =
          ∏' n : ℕ+,
            HTGeometry.primaryFactor 0
              (t ^ 2 * HTGeometry.nomeMonomial primeSquareNome
                (primeOccupationEquivPNat.symm n)) := by
              exact (primeOccupationEquivPNat.symm.tprod_eq
                (fun ν : Nat.Primes →₀ ℕ =>
                  HTGeometry.primaryFactor 0
                    (t ^ 2 * HTGeometry.nomeMonomial primeSquareNome ν))).symm
      _ = ∏' n : ℕ+,
          ((1 : ℂ) - t ^ 2 / ((n : ℕ) : ℂ) ^ 2) := by
            apply tprod_congr
            intro n
            rw [primaryFactor_zero_genus, nomeMonomial_primeSquareNome]
            have hn :
                primeProduct (primeOccupationEquivPNat.symm n) = (n : ℕ) := by
              exact congrArg Subtype.val
                (primeOccupationEquivPNat.apply_symm_apply n)
            rw [hn]
            field_simp
      _ = ∏' n : ℕ,
          ((1 : ℂ) - t ^ 2 / ((n : ℂ) + 1) ^ 2) := by
            rw [tprod_pnat_eq_tprod_succ
              (f := fun n : ℕ =>
                (1 : ℂ) - t ^ 2 / (n : ℂ) ^ 2)]
            apply tprod_congr
            intro n
            norm_num
  rw [hrewrite]
  by_cases ht : t = 0
  · subst t
    simp
  · have hmul : Multipliable
        (fun n : ℕ => (1 : ℂ) + sineTerm t n) :=
      multipliable_sineTerm t
    have hprod :
        (∏' n : ℕ,
            ((1 : ℂ) - t ^ 2 / ((n : ℂ) + 1) ^ 2)) =
          Complex.sin ((Real.pi : ℂ) * t) /
            ((Real.pi : ℂ) * t) := by
      rw [show
        (fun n : ℕ =>
          (1 : ℂ) - t ^ 2 / ((n : ℂ) + 1) ^ 2) =
        fun n : ℕ => (1 : ℂ) + sineTerm t n by
          funext n
          simp only [sineTerm]
          ring]
      rw [← Multipliable.hasProd_iff hmul,
        Multipliable.hasProd_iff_tendsto_nat hmul]
      exact tendsto_euler_sin_prod' ht
    rw [hprod]
    field_simp [Real.pi_ne_zero, ht]

/-- The polynomial-gauged all-prime completion is differentially algebraic: it is exactly sine. -/
theorem differentiallyAlgebraic_primeSquareCompletion_gauged :
    DifferentiallyAlgebraic
      (fun t : ℂ => (Real.pi : ℂ) * t *
        HTGeometry.infiniteMultipleEllipticGamma 0 primeSquareNome (t ^ 2)) := by
  rw [show
      (fun t : ℂ => (Real.pi : ℂ) * t *
        HTGeometry.infiniteMultipleEllipticGamma 0 primeSquareNome (t ^ 2)) =
      fun t : ℂ => Complex.sin ((Real.pi : ℂ) * t) by
        funext t
        exact primeSquareCompletion_mul_eq_sin t]
  exact differentiallyAlgebraic_sin_linear (Real.pi : ℂ)

end

end GaloisForLFunctions
