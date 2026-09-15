import GaloisForLFunctions.RHTower.FZZCigarParityMarkedOPEChargeIncidenceNoGo
import GaloisForLFunctions.HTGeometry.FZZCigarTorusReplicaNeutrality

/-!
# All-depth factorized neutral-screening Ward no-go

The remaining FZZ-P source edge must use the full neutral fractional-winding screening tower,
not a finite-depth truncation.  Torus neutrality supplies the nonzero coefficient
`μ^(2n)/(n!)²` at every depth, and the marked OPE calculation leaves only the opposite-winding
response with fixed prefactor `2*k*δ/(k-2)`.

This file tests the strongest conclusion available from those facts *alone*: a source-fixed,
factorized all-depth scalar Ward response should select the Abel--Jacobi wall.  It is false.
For every nonzero condensate `μ`, an explicit fixed kernel is constructed such that every weighted
depth contribution is nonzero, the full tower has an unconditional sum, and that sum is zero.
The kernel is independent of the twist and of the replica point.

This is a route-class countermodel, not a claim about the unknown physical FZZ torus kernel.
It kills

`neutrality + nonzero all-depth activation + factorized opposite-winding response
 -> scalar Ward selector -> FZZ-P passivity -> RH`.

The positive survivor is exact: literal cross-charge dynamics must provide a source-derived
cross-depth phase/coherence law (or support motion/nonfactorization) excluding this cancellation.
Neither neutrality nor depthwise nonvanishing supplies that law.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.FZZCigar

/-- A fixed, every-depth-active profile whose first term and geometric tail cancel exactly. -/
def fzzNeutralAllDepthCancellationProfile (r : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (r - 1) * r ^ n

/-- The half-geometric cancellation profile has unconditional total sum zero. -/
theorem hasSum_fzzNeutralAllDepthCancellationProfile_half :
    HasSum (fzzNeutralAllDepthCancellationProfile (1 / 2)) 0 := by
  have hr : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hgeom := hasSum_geometric_of_norm_lt_one hr
  have htail : HasSum (fun n : ℕ =>
      ((1 / 2 : ℂ) - 1) * (1 / 2 : ℂ) ^ n)
      (((1 / 2 : ℂ) - 1) * (1 - (1 / 2 : ℂ))⁻¹) := by
    exact hgeom.mul_left ((1 / 2 : ℂ) - 1)
  have hfull : HasSum (fzzNeutralAllDepthCancellationProfile (1 / 2))
      (((1 / 2 : ℂ) - 1) * (1 - (1 / 2 : ℂ))⁻¹ +
        ∑ i ∈ Finset.range 1, fzzNeutralAllDepthCancellationProfile (1 / 2) i) := by
    apply (hasSum_nat_add_iff 1).mp
    simpa [fzzNeutralAllDepthCancellationProfile] using htail
  convert hfull using 1
  norm_num [fzzNeutralAllDepthCancellationProfile]

/-- No depth of the cancellation profile is dark. -/
theorem fzzNeutralAllDepthCancellationProfile_half_ne_zero (n : ℕ) :
    fzzNeutralAllDepthCancellationProfile (1 / 2) n ≠ 0 := by
  cases n with
  | zero => norm_num [fzzNeutralAllDepthCancellationProfile]
  | succ n =>
      simp only [fzzNeutralAllDepthCancellationProfile]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))

/-- A source-fixed opposite-winding kernel cancelling the complete neutral coefficient tower. -/
def fzzNeutralAllDepthCancellingKernel (μ : ℂ) (n : ℕ) : ℂ :=
  fzzNeutralAllDepthCancellationProfile (1 / 2) n /
    neutralScreeningCoefficient μ n

/-- Each literal neutral coefficient times the fixed kernel is the nonzero cancellation profile. -/
theorem neutralScreeningCoefficient_mul_fzzNeutralAllDepthCancellingKernel_eq
    {μ : ℂ} (hμ : μ ≠ 0) (n : ℕ) :
    neutralScreeningCoefficient μ n * fzzNeutralAllDepthCancellingKernel μ n =
      fzzNeutralAllDepthCancellationProfile (1 / 2) n := by
  unfold fzzNeutralAllDepthCancellingKernel
  field_simp [neutralScreeningCoefficient_ne_zero hμ n]

/-- The all-depth weighted response is unconditionally summable and cancels exactly. -/
theorem hasSum_neutralScreeningCoefficient_mul_fzzNeutralAllDepthCancellingKernel
    {μ : ℂ} (hμ : μ ≠ 0) :
    HasSum (fun n : ℕ =>
      neutralScreeningCoefficient μ n * fzzNeutralAllDepthCancellingKernel μ n) 0 := by
  convert hasSum_fzzNeutralAllDepthCancellationProfile_half using 1
  funext n
  exact neutralScreeningCoefficient_mul_fzzNeutralAllDepthCancellingKernel_eq hμ n

/-- Cancellation does not arise by dropping any neutral screening depth. -/
theorem neutralScreeningCoefficient_mul_fzzNeutralAllDepthCancellingKernel_ne_zero
    {μ : ℂ} (hμ : μ ≠ 0) (n : ℕ) :
    neutralScreeningCoefficient μ n * fzzNeutralAllDepthCancellingKernel μ n ≠ 0 := by
  rw [neutralScreeningCoefficient_mul_fzzNeutralAllDepthCancellingKernel_eq hμ]
  exact fzzNeutralAllDepthCancellationProfile_half_ne_zero n

/-- Factorized all-depth opposite-winding Ward response.  The scalar factor is the exact marked
OPE response coefficient; a factorized kernel is otherwise unconstrained here. -/
def fzzNeutralAllDepthFactorizedWardResponse
    (μ : ℂ) (k δ : ℝ) (kernel : ℕ → ℂ) : ℂ :=
  ((2 * k / (k - 2) * δ : ℝ) : ℂ) *
    ∑' n : ℕ, neutralScreeningCoefficient μ n * kernel n

/-- The constructed fixed kernel makes the full factorized all-depth Ward response vanish. -/
theorem fzzNeutralAllDepthFactorizedWardResponse_cancels
    {μ : ℂ} (hμ : μ ≠ 0) (k δ : ℝ) :
    fzzNeutralAllDepthFactorizedWardResponse μ k δ
      (fzzNeutralAllDepthCancellingKernel μ) = 0 := by
  rw [fzzNeutralAllDepthFactorizedWardResponse,
    (hasSum_neutralScreeningCoefficient_mul_fzzNeutralAllDepthCancellingKernel hμ).tsum_eq,
    mul_zero]

/-- The fixed-support factorized model retains the torus twist only as a possible selector input;
the all-depth Ward scalar itself is independent of it. -/
def fzzNeutralAllDepthFactorizedTwistedWardResponse
    (μ : ℂ) (k δ : ℝ) (kernel : ℕ → ℂ) (_twist : ℂ) : ℂ :=
  fzzNeutralAllDepthFactorizedWardResponse μ k δ kernel

/-- The constructed response vanishes even at arbitrary off-wall torus twist. -/
theorem fzzNeutralAllDepthFactorizedTwistedWardResponse_cancels
    {μ : ℂ} (hμ : μ ≠ 0) (k δ : ℝ) (twist : ℂ) :
    fzzNeutralAllDepthFactorizedTwistedWardResponse μ k δ
      (fzzNeutralAllDepthCancellingKernel μ) twist = 0 :=
  fzzNeutralAllDepthFactorizedWardResponse_cancels hμ k δ

/-- **FZZ-P route-class no-go.**  No scalar predicate of a factorized all-depth response can
recover the Abel--Jacobi wall from neutral coefficients and depthwise activation alone. -/
theorem no_fzzNeutralAllDepthFactorizedTwistedWardResponse_wall_selector
    {μ : ℂ} (hμ : μ ≠ 0) (k δ : ℝ) :
    ¬ ∃ P : ℂ → Prop, ∀ twist : ℂ,
      P (fzzNeutralAllDepthFactorizedTwistedWardResponse μ k δ
        (fzzNeutralAllDepthCancellingKernel μ) twist) ↔ twist.im = 0 := by
  rintro ⟨P, hP⟩
  have hzero : P (fzzNeutralAllDepthFactorizedTwistedWardResponse μ k δ
      (fzzNeutralAllDepthCancellingKernel μ) 0) :=
    (hP 0).mpr (by norm_num)
  have hI : P (fzzNeutralAllDepthFactorizedTwistedWardResponse μ k δ
      (fzzNeutralAllDepthCancellingKernel μ) Complex.I) := by
    rw [fzzNeutralAllDepthFactorizedTwistedWardResponse_cancels hμ k δ 0] at hzero
    rw [fzzNeutralAllDepthFactorizedTwistedWardResponse_cancels hμ k δ Complex.I]
    exact hzero
  have := (hP Complex.I).mp hI
  norm_num at this

end

end RHTower
