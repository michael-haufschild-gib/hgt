import GaloisForLFunctions.RHTower.XiHedenmalmFourierEquation
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.CarrierSlope

/-!
# Exact multiplicity depth of the Hedenmalm divided chain

Iterating the removable divided slope at a centered Xi zero produces a canonical chain. At a zero
of analytic multiplicity `m`, the first `m` center values vanish and the `m`th removed quotient is
nonzero. Equivalently, the original Hedenmalm quotient sees the center value exactly at simple
zeros; a multiple zero requires the entire depth-`m` chain.

Multiplication by the spectral coordinate acts on successive chain members by a Jordan recurrence.
This identifies the precise additional state which a multiplicity-faithful completion must carry.
-/

open Complex Set Filter Function FormalMultilinearSeries
open scoped Topology

noncomputable section

namespace RHTower

/-- The canonical `k`-fold removable quotient of `XiC` at `alpha`. -/
def xiThetaDividedChain (alpha : ℂ) (k : ℕ) : ℂ → ℂ :=
  (Function.swap dslope alpha)^[k] XiC

@[simp] theorem xiThetaDividedChain_zero (alpha : ℂ) :
    xiThetaDividedChain alpha 0 = XiC := by
  rfl

/-- Every member of the canonical divided chain is entire. -/
theorem xiThetaDividedChain_analyticAt (alpha : ℂ) (k : ℕ) (z : ℂ) :
    AnalyticAt ℂ (xiThetaDividedChain alpha k) z := by
  induction k generalizing z with
  | zero =>
      exact XiC_analytic z (Set.mem_univ z)
  | succ k ih =>
      rw [xiThetaDividedChain, Function.iterate_succ_apply']
      exact analyticAt_dslope_of_analyticAt (ih alpha) (ih z)

/-- Analytic multiplicity of one centered Xi divisor support point. -/
def xiSupportMultiplicity (rho : XiDivisorSupport) : ℕ :=
  Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))

/-- Exact local-order law for the canonical divided chain. The first nonzero center value occurs
at precisely the analytic multiplicity, and that terminal quotient is the zero-free local
cofactor. -/
theorem xiThetaDividedChain_local_order
    (rho : XiDivisorSupport) :
    let alpha := xiSpectralPointSupport rho
    let m := xiSupportMultiplicity rho
    (∀ k < m, xiThetaDividedChain alpha k alpha = 0) ∧
      xiThetaDividedChain alpha m alpha ≠ 0 ∧
      ∀ z, XiC z = (z - alpha) ^ m * xiThetaDividedChain alpha m z := by
  dsimp only
  let alpha := xiSpectralPointSupport rho
  let m := xiSupportMultiplicity rho
  have hXi : AnalyticAt ℂ XiC alpha := XiC_analytic alpha (Set.mem_univ alpha)
  obtain ⟨p, hp⟩ := hXi
  have hpne : p ≠ 0 := by
    intro hpzero
    have hlocal : ∀ᶠ z in 𝓝 alpha, XiC z = 0 := hp.locally_zero_iff.mpr hpzero
    exact XiC_order_ne_top alpha (analyticOrderAt_eq_top.mpr hlocal)
  have horderXi : analyticOrderAt XiC alpha = (p.order : ℕ∞) := by
    apply (AnalyticAt.analyticOrderAt_eq_natCast hp.analyticAt).mpr
    refine ⟨xiThetaDividedChain alpha p.order,
      xiThetaDividedChain_analyticAt alpha p.order alpha,
      ?_, ?_⟩
    · exact hp.iterate_dslope_fslope_ne_zero hpne
    · exact Filter.Eventually.of_forall (fun z => by
        simpa only [xiThetaDividedChain, smul_eq_mul] using
          hp.eq_pow_order_mul_iterate_dslope z)
  have hpm : p.order = m := by
    have horders : (p.order : ℕ∞) = (m : ℕ∞) := by
      rw [← horderXi]
      simpa only [alpha, m, xiSupportMultiplicity] using
        XiC_analyticOrderAt_support rho
    exact ENat.coe_inj.mp horders
  constructor
  · intro k hk
    rw [xiThetaDividedChain]
    have hlt : k < p.order := by simpa only [hpm] using hk
    rw [← (hp.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1,
      ← coeff, coeff_iterate_fslope, zero_add, coeff,
      p.apply_eq_zero_of_lt_order hlt, ContinuousMultilinearMap.zero_apply]
  constructor
  · simpa only [hpm, xiThetaDividedChain] using
      hp.iterate_dslope_fslope_ne_zero hpne
  · intro z
    simpa only [hpm, xiThetaDividedChain, smul_eq_mul] using
      hp.eq_pow_order_mul_iterate_dslope z

theorem xiThetaDividedChain_vanish_before_multiplicity
    (rho : XiDivisorSupport) {k : ℕ} (hk : k < xiSupportMultiplicity rho) :
    xiThetaDividedChain (xiSpectralPointSupport rho) k
      (xiSpectralPointSupport rho) = 0 :=
  (xiThetaDividedChain_local_order rho).1 k hk

theorem xiThetaDividedChain_nonzero_at_multiplicity
    (rho : XiDivisorSupport) :
    xiThetaDividedChain (xiSpectralPointSupport rho) (xiSupportMultiplicity rho)
      (xiSpectralPointSupport rho) ≠ 0 :=
  (xiThetaDividedChain_local_order rho).2.1

theorem xiThetaDividedChain_factorization
    (rho : XiDivisorSupport) (z : ℂ) :
    XiC z = (z - xiSpectralPointSupport rho) ^ (xiSupportMultiplicity rho) *
      xiThetaDividedChain (xiSpectralPointSupport rho) (xiSupportMultiplicity rho) z :=
  (xiThetaDividedChain_local_order rho).2.2 z

/-- Successive canonical quotients obey an exact divided-difference chain. -/
theorem xiThetaDividedChain_jordan_step
    (rho : XiDivisorSupport) {k : ℕ} (hk : k < xiSupportMultiplicity rho) (z : ℂ) :
    xiThetaDividedChain (xiSpectralPointSupport rho) k z =
      (z - xiSpectralPointSupport rho) *
        xiThetaDividedChain (xiSpectralPointSupport rho) (k + 1) z := by
  have hzero := xiThetaDividedChain_vanish_before_multiplicity rho hk
  simp only [xiThetaDividedChain, Function.iterate_succ_apply']
  simpa only [smul_eq_mul] using
    (sub_smul_dslope_of_zero hzero z).symm

theorem xiSupportMultiplicity_pos (rho : XiDivisorSupport) :
    0 < xiSupportMultiplicity rho := by
  have hpos := xi_divisor_pos_on_support rho
  unfold xiSupportMultiplicity
  omega

/-- Every initial chain member is the exact quotient after removing its prescribed number of
copies of the zero. -/
theorem xiThetaDividedChain_partial_factorization
    (rho : XiDivisorSupport) {k : ℕ} (hk : k ≤ xiSupportMultiplicity rho) (z : ℂ) :
    XiC z = (z - xiSpectralPointSupport rho) ^ k *
      xiThetaDividedChain (xiSpectralPointSupport rho) k z := by
  have hvanish : ∀ j < k,
      xiThetaDividedChain (xiSpectralPointSupport rho) j
        (xiSpectralPointSupport rho) = 0 := by
    intro j hj
    exact xiThetaDividedChain_vanish_before_multiplicity rho (lt_of_lt_of_le hj hk)
  simpa only [xiThetaDividedChain, smul_eq_mul] using
    (pow_sub_smul_iterate_dslope_of_zero k hvanish z).symm

/-- No member through the multiplicity depth is the zero entire function. -/
theorem xiThetaDividedChain_ne_zero_of_le_multiplicity
    (rho : XiDivisorSupport) {k : ℕ} (hk : k ≤ xiSupportMultiplicity rho) :
    xiThetaDividedChain (xiSpectralPointSupport rho) k ≠ 0 := by
  intro hzero
  have hfactor := xiThetaDividedChain_partial_factorization rho hk 0
  rw [hzero] at hfactor
  simp only [Pi.zero_apply, mul_zero] at hfactor
  exact XiC_zero_ne hfactor

/-- The first divided quotient is nonzero at its base point exactly for a simple zero. -/
theorem xiThetaDividedChain_one_self_ne_zero_iff_multiplicity_one
    (rho : XiDivisorSupport) :
    xiThetaDividedChain (xiSpectralPointSupport rho) 1
      (xiSpectralPointSupport rho) ≠ 0 ↔ xiSupportMultiplicity rho = 1 := by
  constructor
  · intro hne
    have hpos := xiSupportMultiplicity_pos rho
    by_contra hm
    have hlt : 1 < xiSupportMultiplicity rho := by omega
    exact hne (xiThetaDividedChain_vanish_before_multiplicity rho hlt)
  · intro hm
    simpa only [hm] using xiThetaDividedChain_nonzero_at_multiplicity rho

theorem xiThetaEigenFourier_eq_I_mul_dividedChain_one (alpha z : ℂ) :
    xiThetaEigenFourier alpha z = I * xiThetaDividedChain alpha 1 z := by
  simp [xiThetaEigenFourier, xiThetaDividedChain]

/-- The original Hedenmalm quotient has a nonzero base value exactly at a simple zero. -/
theorem xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one
    (rho : XiDivisorSupport) :
    xiThetaEigenFourier (xiSpectralPointSupport rho)
      (xiSpectralPointSupport rho) ≠ 0 ↔ xiSupportMultiplicity rho = 1 := by
  rw [xiThetaEigenFourier_eq_I_mul_dividedChain_one]
  constructor
  · intro hne
    apply (xiThetaDividedChain_one_self_ne_zero_iff_multiplicity_one rho).mp
    intro hzero
    apply hne
    rw [hzero, mul_zero]
  · intro hm
    exact mul_ne_zero I_ne_zero
      ((xiThetaDividedChain_one_self_ne_zero_iff_multiplicity_one rho).mpr hm)

/-- Spectral-coordinate multiplication gives the Jordan recurrence pointwise. -/
theorem xiThetaDividedChain_multiplication_step
    (rho : XiDivisorSupport) {k : ℕ} (hk : k < xiSupportMultiplicity rho) (z : ℂ) :
    z * xiThetaDividedChain (xiSpectralPointSupport rho) (k + 1) z =
      xiSpectralPointSupport rho *
        xiThetaDividedChain (xiSpectralPointSupport rho) (k + 1) z +
          xiThetaDividedChain (xiSpectralPointSupport rho) k z := by
  rw [xiThetaDividedChain_jordan_step rho hk z]
  ring

/-- Multiplication by the complex coordinate on an entire function. -/
def xiCoordinateMultiplication (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => z * F z

/-- Function-level Jordan recurrence for the canonical divided chain. -/
theorem xiCoordinateMultiplication_dividedChain
    (rho : XiDivisorSupport) {k : ℕ} (hk : k < xiSupportMultiplicity rho) :
    xiCoordinateMultiplication
        (xiThetaDividedChain (xiSpectralPointSupport rho) (k + 1)) =
      xiSpectralPointSupport rho •
          xiThetaDividedChain (xiSpectralPointSupport rho) (k + 1) +
        xiThetaDividedChain (xiSpectralPointSupport rho) k := by
  funext z
  change z * xiThetaDividedChain (xiSpectralPointSupport rho) (k + 1) z =
    xiSpectralPointSupport rho *
      xiThetaDividedChain (xiSpectralPointSupport rho) (k + 1) z +
        xiThetaDividedChain (xiSpectralPointSupport rho) k z
  exact xiThetaDividedChain_multiplication_step rho hk z

end RHTower
