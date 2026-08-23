import GaloisForLFunctions.RHTower.ZetaFisherVariance
import GaloisForLFunctions.RHTower.SuzukiCoupledErrorCriticalDerivative
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicLogTransport
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFockLocal
import GaloisForLFunctions.HTGeometry.PrimeOccupationCompletionProduct
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Poisson--Euler Sobolev natural-cone identification

The mean-zero periodic point mass has Fourier coefficients `0` at the origin and `1` at every
nonzero integer.  This file gives its literal homogeneous negative-Sobolev energy, proves the
sharp half-order wall and residue, realizes its normalized positive-frequency part as an honest
`ℓ²` vector, and transports that vector unitarily to the finite-support prime-valuation
occupation space.  The local squared amplitudes are exactly the geometric valuation laws.

The existing squarefree-times-square unitary then identifies the singular squarefree digit and
the regular doubled-temperature residual vector.  All statements are source-side and
unconditional.
-/

open Complex Filter Set Topology
open scoped BigOperators ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Literal Fourier coefficient and sharp Sobolev wall -/

/-- Fourier coefficient of `δ₀ - 1` on the circle. -/
def poissonMeanZeroFourierCoeff (n : ℤ) : ℂ := if n = 0 then 0 else 1

@[simp] theorem poissonMeanZeroFourierCoeff_zero : poissonMeanZeroFourierCoeff 0 = 0 := by
  simp [poissonMeanZeroFourierCoeff]

@[simp] theorem poissonMeanZeroFourierCoeff_ne_zero {n : ℤ} (hn : n ≠ 0) :
    poissonMeanZeroFourierCoeff n = 1 := by
  simp [poissonMeanZeroFourierCoeff, hn]

/-- A single summand of the homogeneous `H^{-r}` energy of `δ₀ - 1`. -/
def poissonMeanZeroSobolevTerm (r : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else (n.natAbs : ℝ) ^ (-2 * r)

theorem poissonMeanZeroSobolevTerm_eq_coeff (r : ℝ) (n : ℤ) :
    poissonMeanZeroSobolevTerm r n =
      ‖poissonMeanZeroFourierCoeff n‖ ^ 2 * (n.natAbs : ℝ) ^ (-2 * r) := by
  by_cases hn : n = 0
  · simp [poissonMeanZeroSobolevTerm, poissonMeanZeroFourierCoeff, hn]
  · simp [poissonMeanZeroSobolevTerm, poissonMeanZeroFourierCoeff, hn]

/-- Literal two-sided homogeneous Sobolev energy of the periodic Poisson point conormal. -/
def poissonMeanZeroSobolevNormSq (r : ℝ) : ℝ :=
  ∑' n : ℤ, poissonMeanZeroSobolevTerm r n

private theorem poissonMeanZeroSobolevTerm_natSucc (r : ℝ) (n : ℕ) :
    poissonMeanZeroSobolevTerm r ((n + 1 : ℕ) : ℤ) =
      ((n + 1 : ℕ) : ℝ) ^ (-2 * r) := by
  have hn : (((n + 1 : ℕ) : ℤ)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  rw [poissonMeanZeroSobolevTerm, if_neg hn]
  norm_num
  rw [abs_of_pos (by positivity)]

private theorem poissonMeanZeroSobolevTerm_negSucc (r : ℝ) (n : ℕ) :
    poissonMeanZeroSobolevTerm r (-(((n + 1 : ℕ) : ℤ))) =
      ((n + 1 : ℕ) : ℝ) ^ (-2 * r) := by
  have hn : (-(((n + 1 : ℕ) : ℤ))) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast (Nat.succ_ne_zero n))
  rw [poissonMeanZeroSobolevTerm, if_neg hn, Int.natAbs_neg]
  norm_num
  rw [abs_of_pos (by positivity)]

private theorem poissonMeanZeroSobolevTerm_natCast
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    poissonMeanZeroSobolevTerm r (n : ℤ) = (n : ℝ) ^ (-2 * r) := by
  rcases n with _ | n
  · simp [poissonMeanZeroSobolevTerm, hr.ne']
  · exact poissonMeanZeroSobolevTerm_natSucc r n

private theorem poissonMeanZeroSobolevTerm_neg_natCast
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    poissonMeanZeroSobolevTerm r (-(n : ℤ)) = (n : ℝ) ^ (-2 * r) := by
  rcases n with _ | n
  · simp [poissonMeanZeroSobolevTerm, hr.ne']
  · exact poissonMeanZeroSobolevTerm_negSucc r n

/-- Exact membership threshold: the periodic point conormal belongs to `H^{-r}` exactly above
the half-order wall. -/
theorem summable_poissonMeanZeroSobolevTerm_iff (r : ℝ) :
    Summable (poissonMeanZeroSobolevTerm r) ↔ 1 / 2 < r := by
  constructor
  · intro h
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 * r)) := by
      have hinj : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : ℤ)) := by
        intro m n h
        have h' : m + 1 = n + 1 := Int.ofNat_inj.mp h
        omega
      refine (h.comp_injective hinj).congr fun n => ?_
      exact poissonMeanZeroSobolevTerm_natSucc r n
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * r)) :=
      (summable_nat_add_iff 1).mp (by simpa [Nat.cast_add, Nat.cast_one] using hshift)
    have hexp : -2 * r < -1 := Real.summable_nat_rpow.mp hbase
    linarith
  · intro hr
    have hr0 : 0 < r := by linarith
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * r)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hpos : Summable (fun n : ℕ => poissonMeanZeroSobolevTerm r (n : ℤ)) :=
      hbase.congr fun n => (poissonMeanZeroSobolevTerm_natCast hr0 n).symm
    have hneg : Summable (fun n : ℕ => poissonMeanZeroSobolevTerm r (-(n : ℤ))) :=
      hbase.congr fun n => (poissonMeanZeroSobolevTerm_neg_natCast hr0 n).symm
    exact summable_int_iff_summable_nat_and_neg.mpr ⟨hpos, hneg⟩

theorem summable_poissonMeanZeroSobolevTerm {r : ℝ} (hr : 1 / 2 < r) :
    Summable (poissonMeanZeroSobolevTerm r) :=
  (summable_poissonMeanZeroSobolevTerm_iff r).2 hr

/-- Card equation `(5)`: `‖δ₀-1‖²_{H^{-r}} = 2 ζ(2r)`, first in its real Dirichlet-series form. -/
theorem poissonMeanZeroSobolevNormSq_eq_two_mul_eulerMass
    {r : ℝ} (hr : 1 / 2 < r) :
    poissonMeanZeroSobolevNormSq r = 2 * eulerMass (2 * r) := by
  have hr0 : 0 < r := by linarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * r)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hpos : Summable (fun n : ℕ => poissonMeanZeroSobolevTerm r (n : ℤ)) :=
    hbase.congr fun n => (poissonMeanZeroSobolevTerm_natCast hr0 n).symm
  have hnegSucc : Summable
      (fun n : ℕ => poissonMeanZeroSobolevTerm r (-((n : ℤ) + 1))) := by
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 * r)) :=
      (summable_nat_add_iff 1).mpr hbase
    refine hshift.congr fun n => ?_
    rw [show -((n : ℤ) + 1) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring]
    exact (poissonMeanZeroSobolevTerm_negSucc r n).symm
  rw [poissonMeanZeroSobolevNormSq,
    tsum_of_nat_of_neg_add_one hpos hnegSucc]
  have hnat : (∑' n : ℕ, poissonMeanZeroSobolevTerm r (n : ℤ)) = eulerMass (2 * r) := by
    calc
      (∑' n : ℕ, poissonMeanZeroSobolevTerm r (n : ℤ)) =
          ∑' n : ℕ, (n : ℝ) ^ (-2 * r) :=
        tsum_congr fun n => poissonMeanZeroSobolevTerm_natCast hr0 n
      _ = ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 * r) := by
        rw [hbase.tsum_eq_zero_add]
        have hzero : (((0 : ℕ) : ℝ) ^ (-2 * r)) = 0 := by
          simpa only [Nat.cast_zero] using
            (Real.zero_rpow (by linarith : -2 * r ≠ 0))
        rw [hzero, zero_add]
      _ = eulerMass (2 * r) := by
        rw [eulerMass]
        convert (tsum_pnat_eq_tsum_succ
          (f := fun n : ℕ => (n : ℝ) ^ (-2 * r))).symm using 1 <;> ring_nf
  have hnegEq :
      (∑' n : ℕ, poissonMeanZeroSobolevTerm r (-((n : ℤ) + 1))) = eulerMass (2 * r) := by
    calc
      (∑' n : ℕ, poissonMeanZeroSobolevTerm r (-((n : ℤ) + 1))) =
          ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-2 * r) := by
        refine tsum_congr fun n => ?_
        rw [show -((n : ℤ) + 1) = -(((n + 1 : ℕ) : ℤ)) by push_cast; ring]
        exact poissonMeanZeroSobolevTerm_negSucc r n
      _ = eulerMass (2 * r) := by
        rw [eulerMass]
        convert (tsum_pnat_eq_tsum_succ
          (f := fun n : ℕ => (n : ℝ) ^ (-2 * r))).symm using 1 <;> ring_nf
  rw [hnat, hnegEq]
  ring

/-- Card equation `(5)` with the actual Riemann zeta value. -/
theorem poissonMeanZeroSobolevNormSq_eq_two_mul_riemannZeta_re
    {r : ℝ} (hr : 1 / 2 < r) :
    poissonMeanZeroSobolevNormSq r =
      2 * (riemannZeta (((2 * r : ℝ) : ℂ))).re := by
  rw [poissonMeanZeroSobolevNormSq_eq_two_mul_eulerMass hr]
  have hz := congrArg Complex.re (riemannZeta_ofReal_eq_eulerMass (by linarith : 1 < 2 * r))
  simpa using congrArg (fun x : ℝ => 2 * x) hz.symm

/-- Card equation `(6)`, in the affine boundary coordinate `r = 1/2 + ω`. -/
theorem tendsto_poissonMeanZeroSobolevResidue :
    Tendsto
      (fun ω : ℝ =>
        (2 * (1 / 2 + ω) - 1) *
          poissonMeanZeroSobolevNormSq (1 / 2 + ω))
      (𝓝[>] 0) (𝓝 2) := by
  have hz := tendsto_omega_mul_riemannZeta_re_one_add_two_mul
  have hfour : Tendsto
      (fun ω : ℝ => 4 * (ω * (riemannZeta (((1 + 2 * ω : ℝ) : ℂ))).re))
      (𝓝[>] 0) (𝓝 2) := by
    convert hz.const_mul 4 using 1 <;> norm_num1
  apply hfour.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  change 0 < ω at hω
  rw [poissonMeanZeroSobolevNormSq_eq_two_mul_riemannZeta_re
    (by linarith : 1 / 2 < 1 / 2 + ω)]
  have harg : (((2 * (1 / 2 + ω) : ℝ) : ℂ)) = (((1 + 2 * ω : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [harg]
  ring

/-! ## Positive-frequency Hilbert vector -/

/-- Positive Fourier coefficient `n^{-r}`, indexed by `n+1`. -/
def poissonPositiveSobolevCoord (r : ℝ) (n : ℕ) : ℂ :=
  ((((n + 1 : ℕ) : ℝ) ^ (-r) : ℝ) : ℂ)

/-- The positive-frequency vector is square-summable exactly above the half-order wall. -/
theorem memlp_poissonPositiveSobolevCoord_iff (r : ℝ) :
    Memℓp (poissonPositiveSobolevCoord r) 2 ↔ 1 / 2 < r := by
  rw [memℓp_gen_iff (by norm_num)]
  have hterm : (fun n : ℕ => ‖poissonPositiveSobolevCoord r n‖ ^ (2 : ENNReal).toReal) =
      fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 * r) := by
    funext n
    rw [show (2 : ENNReal).toReal = 2 by norm_num]
    simp only [poissonPositiveSobolevCoord, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    ring
  rw [hterm]
  have hshift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 * r)) ↔
        Summable (fun n : ℕ => (n : ℝ) ^ (-2 * r)) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * r)) 1)
  rw [hshift, Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- Honest positive-frequency Sobolev vector. -/
def poissonPositiveSobolevVector {r : ℝ} (hr : 1 / 2 < r) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨poissonPositiveSobolevCoord r, (memlp_poissonPositiveSobolevCoord_iff r).2 hr⟩

@[simp] theorem poissonPositiveSobolevVector_apply
    {r : ℝ} (hr : 1 / 2 < r) (n : ℕ) :
    poissonPositiveSobolevVector hr n = poissonPositiveSobolevCoord r n := rfl

/-- Reindex positive Fourier modes `n+1` by positive integers. -/
def poissonPositiveToEulerUnitary :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] EulerPositiveL2 :=
  lpReindexEquiv Equiv.pnatEquivNat.symm

/-- Normalized positive-frequency representative. -/
def poissonNormalizedPositiveVector {r : ℝ} (hr : 1 / 2 < r) :
    lp (fun _ : ℕ => ℂ) 2 :=
  poissonPositiveToEulerUnitary.symm (eulerPointedState (by linarith : 1 < 2 * r))

theorem norm_poissonNormalizedPositiveVector
    {r : ℝ} (hr : 1 / 2 < r) :
    ‖poissonNormalizedPositiveVector hr‖ = 1 := by
  change ‖poissonPositiveToEulerUnitary.symm
      (eulerPointedState (by linarith : 1 < 2 * r))‖ = 1
  rw [← poissonPositiveToEulerUnitary.norm_map]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact norm_eulerPointedState (by linarith : 1 < 2 * r)

theorem poissonPositiveToEulerUnitary_normalized
    {r : ℝ} (hr : 1 / 2 < r) :
    poissonPositiveToEulerUnitary (poissonNormalizedPositiveVector hr) =
      eulerPointedState (by linarith : 1 < 2 * r) := by
  simp [poissonNormalizedPositiveVector]

/-! ## Unique factorization and local natural-cone law -/

/-- Hilbert space of finitely supported all-prime valuation configurations. -/
abbrev PrimeOccupationL2 := lp (fun _ : Nat.Primes →₀ ℕ => ℂ) 2

/-- Unique factorization, lifted to an exact unitary from positive integers to prime occupations. -/
def eulerPrimeOccupationUnitary : EulerPositiveL2 ≃ₗᵢ[ℂ] PrimeOccupationL2 :=
  lpReindexEquiv HTGeometry.occupationEquivPNat.symm

/-- Combined Fourier-to-prime unitary. -/
def poissonPrimeOccupationUnitary :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] PrimeOccupationL2 :=
  poissonPositiveToEulerUnitary.trans eulerPrimeOccupationUnitary

/-- The canonical all-prime natural-cone vector at Sobolev order `r`. -/
def poissonEulerNaturalConeVector {r : ℝ} (hr : 1 / 2 < r) : PrimeOccupationL2 :=
  poissonPrimeOccupationUnitary (poissonNormalizedPositiveVector hr)

/-- **Poisson--Euler natural-cone identification.**  Under the literal unique-factorization
unitary, the normalized positive-frequency Sobolev vector is exactly the prime-occupation
natural-cone vector. -/
theorem poissonEulerNaturalConeIdentification
    {r : ℝ} (hr : 1 / 2 < r) :
    poissonPrimeOccupationUnitary (poissonNormalizedPositiveVector hr) =
      poissonEulerNaturalConeVector hr := rfl

theorem poissonEulerNaturalConeVector_apply
    {r : ℝ} (hr : 1 / 2 < r) (ν : Nat.Primes →₀ ℕ) :
    poissonEulerNaturalConeVector hr ν =
      eulerStateCoord (2 * r) (HTGeometry.occupationEquivPNat ν) := by
  rw [poissonEulerNaturalConeVector, poissonPrimeOccupationUnitary,
    LinearIsometryEquiv.trans_apply, poissonPositiveToEulerUnitary_normalized]
  rfl

/-- Local squared amplitudes of the natural-cone vector: the geometric prime-valuation law. -/
def poissonPrimeValuationProbability (r : ℝ) (p : Nat.Primes) (k : ℕ) : ℝ :=
  dyadicEulerGeometricProbability ((p.1 : ℝ) ^ (-2 * r)) k

theorem poissonPrimeValuationProbability_eq
    (r : ℝ) (p : Nat.Primes) (k : ℕ) :
    poissonPrimeValuationProbability r p k =
      (1 - (p.1 : ℝ) ^ (-2 * r)) * (p.1 : ℝ) ^ (-2 * r * k) := by
  rw [poissonPrimeValuationProbability, dyadicEulerGeometricProbability, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]

theorem tsum_poissonPrimeValuationProbability
    {r : ℝ} (hr : 1 / 2 < r) (p : Nat.Primes) :
    ∑' k : ℕ, poissonPrimeValuationProbability r p k = 1 := by
  apply tsum_dyadicEulerGeometricProbability
  · positivity
  · exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.2.one_lt) (by linarith)

/-- The card's radial coordinate `c = 1/2-r` gives exactly its stated valuation law. -/
theorem poissonPrimeValuationProbability_eq_radial
    (r : ℝ) (p : Nat.Primes) (k : ℕ) :
    poissonPrimeValuationProbability r p k =
      (1 - (p.1 : ℝ) ^ (-(1 - 2 * (1 / 2 - r)))) *
        (p.1 : ℝ) ^ (-(1 - 2 * (1 / 2 - r)) * k) := by
  rw [poissonPrimeValuationProbability_eq]
  congr 3 <;> ring

/-! ## Exact squarefree singular layer -/

/-- At `σ=2r`, the existing dyadic arithmetic unitary gives the card's squarefree-times-square
factorization of the normalized Sobolev vector. -/
theorem poissonNormalizedPositive_dyadicSquarefreeFactorization
    {r : ℝ} (hr : 1 / 2 < r) :
    dyadicSquarefreeSignedUnitary
        (poissonPositiveToEulerUnitary (poissonNormalizedPositiveVector hr)) =
      lpTensor
        (squarefreePointedState (by linarith : 1 < 2 * r))
        (eulerPointedState (by linarith : 1 < 2 * (2 * r))) := by
  rw [poissonPositiveToEulerUnitary_normalized]
  exact dyadicSquarefreeSignedUnitary_eq_tensor
    (by linarith : 1 < 2 * r) (by linarith : 1 < 2 * (2 * r))

/-- Exact squarefree mass quotient, stated without division by using the regular doubled layer. -/
theorem poissonSquarefreeMass_mul_regularDyadicMass
    {r : ℝ} (hr : 1 / 2 < r) :
    squarefreeMass (2 * r) * eulerMass (4 * r) = eulerMass (2 * r) := by
  have h := squarefreeMass_mul_eulerMass_two_mul (by linarith : 1 < 2 * r)
  convert h using 1 <;> ring_nf

end RHTower
