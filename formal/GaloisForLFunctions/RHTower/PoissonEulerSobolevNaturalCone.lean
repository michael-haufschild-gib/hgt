import GaloisForLFunctions.RHTower.ZetaFisherVariance
import GaloisForLFunctions.RHTower.SuzukiCoupledErrorCriticalDerivative
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicLogTransport
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFockLocal
import GaloisForLFunctions.RHTower.DeningerGaussianZetaMellin
import GaloisForLFunctions.RHTower.JacobiThetaBoundaryLimits
import GaloisForLFunctions.RHTower.NymanMellinGaugeCollapse
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
          (f := fun n : ℕ => (n : ℝ) ^ (-2 * r))).symm using 1
        all_goals ring_nf
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
          (f := fun n : ℕ => (n : ℝ) ^ (-2 * r))).symm using 1
        all_goals ring_nf
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
    convert hz.const_mul 4 using 1
    norm_num
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

@[simp] theorem poissonNormalizedPositiveVector_apply
    {r : ℝ} (hr : 1 / 2 < r) (n : ℕ) :
    poissonNormalizedPositiveVector hr n =
      eulerStateCoord (2 * r) (Nat.succPNat n) := by
  change (lpReindexEquiv Equiv.pnatEquivNat.symm).symm
      (eulerPointedState (by linarith : 1 < 2 * r)) n =
    eulerStateCoord (2 * r) (Nat.succPNat n)
  rfl

theorem poissonPositiveToEulerUnitary_normalized
    {r : ℝ} (hr : 1 / 2 < r) :
    poissonPositiveToEulerUnitary (poissonNormalizedPositiveVector hr) =
      eulerPointedState (by linarith : 1 < 2 * r) := by
  simp [poissonNormalizedPositiveVector]

/-- Exact overlap of two normalized positive-frequency representatives. -/
theorem inner_eulerPointedState_eq_eulerMass
    {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    inner ℂ (eulerPointedState hσ) (eulerPointedState hτ) =
      (((eulerMass ((σ + τ) / 2) /
        (Real.sqrt (eulerMass σ) * Real.sqrt (eulerMass τ)) : ℝ) : ℂ)) := by
  have hmid : 1 < (σ + τ) / 2 := by linarith
  rw [lp.inner_eq_tsum]
  simp only [eulerPointedState_apply, RCLike.inner_apply]
  have hterm :
      (fun n : ℕ+ => eulerStateCoord τ n * (starRingEnd ℂ) (eulerStateCoord σ n)) =
        fun n : ℕ+ =>
          ((((n : ℝ) ^ (-(σ + τ) / 2) /
            (Real.sqrt (eulerMass σ) * Real.sqrt (eulerMass τ)) : ℝ) : ℂ)) := by
    funext n
    simp only [eulerStateCoord, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    rw [div_mul_div_comm]
    congr 1
    · rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    · ring
  rw [hterm, ← Complex.ofReal_tsum, tsum_div_const]
  have hmass :
      (∑' n : ℕ+, (n : ℝ) ^ (-(σ + τ) / 2)) = eulerMass ((σ + τ) / 2) := by
    rw [eulerMass]
    refine tsum_congr fun n => ?_
    congr 1
    ring
  rw [hmass]

/-- Card equation `(14)`, in the exact Sobolev parameters `r,s`. -/
theorem inner_poissonNormalizedPositiveVector_eq_zetaRatio
    {r s : ℝ} (hr : 1 / 2 < r) (hs : 1 / 2 < s) :
    inner ℂ (poissonNormalizedPositiveVector hr) (poissonNormalizedPositiveVector hs) =
      riemannZeta (((r + s : ℝ) : ℂ)) /
        (((Real.sqrt (riemannZeta (((2 * r : ℝ) : ℂ))).re *
          Real.sqrt (riemannZeta (((2 * s : ℝ) : ℂ))).re : ℝ) : ℂ)) := by
  rw [← poissonPositiveToEulerUnitary.inner_map_map,
    poissonPositiveToEulerUnitary_normalized,
    poissonPositiveToEulerUnitary_normalized,
    inner_eulerPointedState_eq_eulerMass]
  rw [riemannZeta_ofReal_eq_eulerMass (by linarith : 1 < r + s),
    riemannZeta_ofReal_eq_eulerMass (by linarith : 1 < 2 * r),
    riemannZeta_ofReal_eq_eulerMass (by linarith : 1 < 2 * s)]
  simp only [Complex.ofReal_re]
  push_cast
  congr 2
  ring

/-! ## Weak escape at the half-order wall -/

/-- The full Euler partition diverges at the critical boundary. -/
theorem tendsto_eulerMass_one_add_two_mul_atTop :
    Tendsto (fun ω : ℝ => eulerMass (1 + 2 * ω)) (𝓝[>] 0) atTop := by
  have hz := tendsto_omega_mul_riemannZeta_re_one_add_two_mul
  have hquot := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    hz (tendsto_inv_nhdsGT_zero : Tendsto (fun ω : ℝ => ω⁻¹) (𝓝[>] 0) atTop)
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  change 0 < ω at hω
  rw [riemannZeta_ofReal_eq_eulerMass (by linarith : 1 < 1 + 2 * ω)]
  simp only [Complex.ofReal_re]
  field_simp [hω.ne']

/-- Unit source family approaching the Sobolev wall, with junk value zero off the positive
boundary coordinate. -/
def poissonCriticalSourceFamily (ω : ℝ) : lp (fun _ : ℕ => ℂ) 2 :=
  if hω : 0 < ω then
    poissonNormalizedPositiveVector (by linarith : 1 / 2 < 1 / 2 + ω)
  else 0

theorem norm_poissonCriticalSourceFamily {ω : ℝ} (hω : 0 < ω) :
    ‖poissonCriticalSourceFamily ω‖ = 1 := by
  rw [poissonCriticalSourceFamily, dif_pos hω]
  exact norm_poissonNormalizedPositiveVector (by linarith : 1 / 2 < 1 / 2 + ω)

/-- Every fixed Fourier coordinate vanishes at the half-order wall. -/
theorem tendsto_poissonCriticalSourceFamily_apply_zero (n : ℕ) :
    Tendsto (fun ω : ℝ => poissonCriticalSourceFamily ω n)
      (𝓝[>] 0) (𝓝 0) := by
  have hmass := tendsto_eulerMass_one_add_two_mul_atTop
  have hsqrt : Tendsto (fun ω : ℝ => Real.sqrt (eulerMass (1 + 2 * ω)))
      (𝓝[>] 0) atTop := Real.tendsto_sqrt_atTop.comp hmass
  have hinv : Tendsto (fun ω : ℝ => (Real.sqrt (eulerMass (1 + 2 * ω)))⁻¹)
      (𝓝[>] 0) (𝓝 0) := tendsto_inv_atTop_zero.comp hsqrt
  have hnum : Tendsto
      (fun ω : ℝ => (((n + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω) / 2)))
      (𝓝[>] 0) (𝓝 (((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ) / 2))) := by
    have hc : Continuous
        (fun ω : ℝ => (((n + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω) / 2))) := by
      exact (Real.continuous_const_rpow (by positivity)).comp (by fun_prop)
    convert (hc.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    all_goals norm_num
  have hprod := hnum.mul hinv
  have hprod0 : Tendsto
      (fun ω : ℝ => (((n + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω) / 2) *
        (Real.sqrt (eulerMass (1 + 2 * ω)))⁻¹))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hprod
  have hcomplex : Tendsto
      (fun ω : ℝ =>
        ((((n + 1 : ℕ) : ℝ) ^ (-(1 + 2 * ω) / 2) *
          (Real.sqrt (eulerMass (1 + 2 * ω)))⁻¹ : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp hprod0
  apply hcomplex.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω
  change 0 < ω at hω
  rw [poissonCriticalSourceFamily, dif_pos hω,
    poissonNormalizedPositiveVector_apply]
  rw [eulerStateCoord]
  norm_cast
  rw [div_eq_mul_inv]
  congr 2
  · congr 1
    ring
  · congr 1
    ring

/-- Weak escape against every fixed Hilbert vector. -/
theorem tendsto_inner_poissonCriticalSourceFamily_zero
    (y : lp (fun _ : ℕ => ℂ) 2) :
    Tendsto (fun ω : ℝ => inner ℂ y (poissonCriticalSourceFamily ω))
      (𝓝[>] 0) (𝓝 0) := by
  have hbasis : ∀ k : ℕ,
      Tendsto (fun ω : ℝ =>
        inner ℂ ((HilbertSchmidt.lpBasis ℕ) k) (poissonCriticalSourceFamily ω))
        (𝓝[>] 0) (𝓝 0) := by
    intro k
    simpa [HilbertSchmidt.lpBasis_apply, lp.inner_single_left] using
      tendsto_poissonCriticalSourceFamily_apply_zero k
  have hspan : ∀ z ∈ Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)),
      Tendsto (fun ω : ℝ => inner ℂ z (poissonCriticalSourceFamily ω))
        (𝓝[>] 0) (𝓝 0) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact hbasis k
    | zero => simp
    | add x y hx hy hxt hyt =>
        simpa only [inner_add_left, zero_add] using hxt.add hyt
    | smul a x hx hxt =>
        simpa only [inner_smul_left, mul_zero] using
          hxt.const_mul (starRingEnd ℂ a)
  have hdense : Dense (Submodule.span ℂ (Set.range (HilbertSchmidt.lpBasis ℕ)) :
      Set (lp (fun _ : ℕ => ℂ) 2)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (HilbertSchmidt.lpBasis ℕ).dense_span
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨z, hz, hyz⟩ := hdense.exists_dist_lt y (half_pos hε)
  have hz0 := hspan z hz
  rw [NormedAddGroup.tendsto_nhds_zero] at hz0
  filter_upwards [hz0 (ε / 2) (half_pos hε), self_mem_nhdsWithin] with ω hn hω
  change 0 < ω at hω
  have hvnorm : ‖poissonCriticalSourceFamily ω‖ = 1 :=
    norm_poissonCriticalSourceFamily hω
  calc
    ‖inner ℂ y (poissonCriticalSourceFamily ω)‖ =
        ‖inner ℂ (y - z) (poissonCriticalSourceFamily ω) +
          inner ℂ z (poissonCriticalSourceFamily ω)‖ := by
      rw [← inner_add_left, sub_add_cancel]
    _ ≤ ‖inner ℂ (y - z) (poissonCriticalSourceFamily ω)‖ +
        ‖inner ℂ z (poissonCriticalSourceFamily ω)‖ := norm_add_le _ _
    _ ≤ ‖y - z‖ * ‖poissonCriticalSourceFamily ω‖ +
        ‖inner ℂ z (poissonCriticalSourceFamily ω)‖ := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = dist y z + ‖inner ℂ z (poissonCriticalSourceFamily ω)‖ := by
      rw [hvnorm, mul_one, dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add hyz hn
    _ = ε := by ring

/-- Card equation `(15)`: the normalized Poisson--Euler source is weakly null while retaining
unit norm. -/
theorem poissonCriticalSourceFamily_weakly_tendsto_zero
    (ℓ : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] ℂ) :
    Tendsto (fun ω : ℝ => ℓ (poissonCriticalSourceFamily ω))
      (𝓝[>] 0) (𝓝 0) := by
  let y : lp (fun _ : ℕ => ℂ) 2 :=
    (InnerProductSpace.toDual ℂ (lp (fun _ : ℕ => ℂ) 2)).symm ℓ
  simpa [y, InnerProductSpace.toDual_symm_apply] using
    tendsto_inner_poissonCriticalSourceFamily_zero y

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
  convert h using 1
  all_goals ring_nf

/-! ## Additive Gaussian--Mellin reporter -/

/-- Positive and negative nonzero terms of the ordinary Jacobi theta series. -/
noncomputable def poissonThetaTail (t : ℝ) : ℂ :=
  2 * deningerGaussianRayTheta 1 t

/-- On the positive real ray, the explicit Gaussian sum is literally `θ(it) - 1`. -/
theorem poissonThetaTail_eq_jacobiTheta_sub_one {t : ℝ} (ht : 0 < t) :
    poissonThetaTail t = jacobiTheta (I * (t : ℂ)) - 1 := by
  have him : 0 < (I * (t : ℂ)).im := by
    norm_num
    exact ht
  have hj := (hasSum_nat_jacobiTheta him).mul_left 2
  have hd := (deningerRayTheta_hasSum (by norm_num : (0 : ℝ) < 1) ht).mul_left 2
  have hterm : ∀ n : ℕ,
      2 * ((1 : ℂ) *
          ((Real.exp (-Real.pi * (1 * ((n : ℝ) + 1)) ^ 2 * t) : ℝ) : ℂ)) =
        2 * cexp ((Real.pi : ℂ) * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ))) := by
    intro n
    have hexp : (Real.pi : ℂ) * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ)) =
        ((-Real.pi * ((n : ℝ) + 1) ^ 2 * t : ℝ) : ℂ) := by
      have h1 : (Real.pi : ℂ) * I * ((n : ℂ) + 1) ^ 2 * (I * (t : ℂ)) =
          I ^ 2 * ((Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (t : ℂ)) := by ring
      rw [h1, Complex.I_sq]
      push_cast
      ring
    rw [hexp, ← Complex.ofReal_exp]
    push_cast
    ring
  have heq := hd.congr_fun fun n => (hterm n).symm
  have hu := heq.unique hj
  dsimp [poissonThetaTail]
  linear_combination hu

/-- The squared-variable positive theta ray has completed Gamma--zeta Mellin transform. -/
theorem deningerGaussianRayTheta_one_mellin {s : ℂ} (hs : 1 < s.re) :
    mellin (deningerGaussianRayTheta 1) (s / 2) =
      Complex.Gammaℝ s * riemannZeta s := by
  have hcomp := mellin_comp_rpow (deningerGaussianRayTheta 1) s 2
  have hfun : (fun t : ℝ => deningerGaussianRayTheta 1 (t ^ (2 : ℝ))) =
      deningerGaussianRaySum 1 := by
    funext t
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact (deningerGaussianRaySum_eq_theta 1 t).symm
  rw [hfun, deningerGaussianRaySum_mellin (by norm_num : (0 : ℝ) < 1) hs] at hcomp
  simp only [Complex.ofReal_one, one_cpow, one_mul] at hcomp
  rw [show |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ by norm_num, Complex.real_smul] at hcomp
  push_cast at hcomp
  field_simp at hcomp
  exact hcomp.symm

/-- Card equation `(23)`: the literal nonconstant theta tail reports the completed zeta factor. -/
theorem poissonThetaTail_mellin {s : ℂ} (hs : 1 < s.re) :
    mellin poissonThetaTail (s / 2) =
      2 * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
  have hlin : mellin poissonThetaTail (s / 2) =
      2 * mellin (deningerGaussianRayTheta 1) (s / 2) := by
    exact GaloisForLFunctions.NymanMellin.mellin_const_mul
      2 (deningerGaussianRayTheta 1) (s / 2)
  rw [hlin, deningerGaussianRayTheta_one_mellin hs, Complex.Gammaℝ_def]
  ring

/-- Card equation `(24)`: Jacobi--Poisson inversion on the positive real theta ray. -/
theorem jacobiTheta_I_mul_ofReal_inversion {t : ℝ} (ht : 0 < t) :
    jacobiTheta (I * (t : ℂ)) =
      (((t : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        jacobiTheta (I * ((t⁻¹ : ℝ) : ℂ)) := by
  have him : 0 < (I * (t : ℂ)).im := by
    norm_num
    exact ht
  have hS := jacobiTheta_eq_cpow_mul him
  have hfactor : I / (I * (t : ℂ)) = ((t⁻¹ : ℝ) : ℂ) := by
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp [htC, I_ne_zero]
    norm_cast
    field_simp [ht.ne']
  have hinv : -(I * (t : ℂ))⁻¹ = I * ((t⁻¹ : ℝ) : ℂ) := by
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    field_simp [htC, I_ne_zero]
    rw [Complex.I_sq]
    norm_cast
    field_simp [ht.ne']
  rw [hfactor, hinv] at hS
  rw [hS]
  congr 1
  calc
    ((t⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
        ((((t⁻¹ : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) := by
      have h := (Complex.ofReal_cpow (le_of_lt (inv_pos.mpr ht)) (1 / 2 : ℝ)).symm
      norm_num at h ⊢
      exact h
    _ = (((t : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Real.inv_rpow (le_of_lt ht), ← Real.rpow_neg (le_of_lt ht)]

/-! ## Exact zero coordinate -/

/-- Radial coordinate attached to a complex Mellin divisor point. -/
def poissonZeroRadialCoordinate (ρ : ℂ) : ℝ := 1 / 2 - ρ.re

/-- Sobolev order recovered from the radial coordinate. -/
def poissonZeroSobolevOrder (ρ : ℂ) : ℝ := 1 / 2 - poissonZeroRadialCoordinate ρ

/-- Card equation `(26)`: the source Sobolev order is exactly the real part of the divisor point. -/
theorem poissonZeroSobolevOrder_eq_re (ρ : ℂ) : poissonZeroSobolevOrder ρ = ρ.re := by
  simp [poissonZeroSobolevOrder, poissonZeroRadialCoordinate]

end RHTower
