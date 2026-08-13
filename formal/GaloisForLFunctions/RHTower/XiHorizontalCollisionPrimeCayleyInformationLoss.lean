import GaloisForLFunctions.RHTower.XiHorizontalCollisionTwoPrimeCesaroCarrier
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier
import GaloisForLFunctions.HTGeometry.CofinalCholeskySelection

/-!
# Horizontal collision charge as source-Cayley information loss

The fixed-prime carrier sees only the ordinate because multiplying the two line-reflected Burnol
characters cancels horizontal displacement.  This module adds the unit Cayley phase of the actual
source-horizontal centered rate before scalarization.  At Cayley depth zero it is exactly the
previous `(2,3)` prime pencil.  Averaging the new depth separates distinct points inside every
horizontal fibre and recovers the local multiplicity-square census.  The information lost by
forgetting this source-horizontal phase converges exactly to horizontal collision charge.

Thus `O(T)` is not merely a divisor statistic: it is the precise mean-square cost of quotienting
the coefficient-faithful prime/source carrier by line reflection.  All statements are
unconditional.  A closing RH producer still must prove an absolute loss bound below two from a
pre-divisor prime--Gamma law.
-/

open Complex Set Metric Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Unit Cayley phase of the source-horizontal centered rate. -/
def xiHorizontalSourceCayleyPhase (rho : ℂ) : ℂ :=
  GaloisForLFunctions.HTGeometry.realCayley (2 * rho.re - 1)

theorem xiHorizontalSourceCayleyPhase_norm (rho : ℂ) :
    ‖xiHorizontalSourceCayleyPhase rho‖ = 1 :=
  GaloisForLFunctions.HTGeometry.norm_realCayley _

/-- On an actual divisor copy this is literally the Cayley phase of the source-tail/BVW rate. -/
theorem xiHorizontalSourceCayleyPhase_eq_sourceRateCayley (q : XiZeroCopy) :
    xiHorizontalSourceCayleyPhase q.1 =
      GaloisForLFunctions.HTGeometry.realCayley
        (primeDepthBVWoldXiCenteredRate q.1) := rfl

/-- The source-Cayley phase separates points once their ordinates agree. -/
theorem eq_of_im_eq_of_horizontalSourceCayleyPhase_eq
    {rho sigma : ℂ} (him : rho.im = sigma.im)
    (hphase : xiHorizontalSourceCayleyPhase rho =
      xiHorizontalSourceCayleyPhase sigma) :
    rho = sigma := by
  have hrates : 2 * rho.re - 1 = 2 * sigma.re - 1 :=
    GaloisForLFunctions.HTGeometry.injective_realCayley hphase
  apply Complex.ext
  · linarith
  · exact him

/-- Horizontal source pencil inside one exact ordinate fibre. -/
def xiHorizontalSourceCayleyFiberPencil
    (T gamma : ℝ) (c : ℕ) : ℂ :=
  finiteExponentialPencil
    ((stripZeros_finite T).toFinset.filter (fun rho => rho.im = gamma))
    (fun rho => ((analyticOrderAt xi rho).toNat : ℂ))
    xiHorizontalSourceCayleyPhase c

/-- Energy left after the two prime clocks have separated distinct ordinates at fixed horizontal
Cayley depth. -/
def xiHorizontalSourceCayleyResolvedEnergy (T : ℝ) (c : ℕ) : ℝ :=
  ∑ gamma ∈ (stripZeros_finite T).toFinset.image Complex.im,
    ‖xiHorizontalSourceCayleyFiberPencil T gamma c‖ ^ 2

/-- Three-depth source pencil.  Prime labels, both line-reflection orientations, local
multiplicity, and the non-equivariant horizontal source phase are all retained. -/
def xiHorizontalCollisionPrimeCayleySourcePencil
    (T : ℝ) (a b c : ℕ) : ℂ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    ((analyticOrderAt xi rho).toNat : ℂ) *
      (burnolPrimeCharacter 2 rho * burnolPrimeCharacter 2 (lineReflect rho)) ^ a *
      (burnolPrimeCharacter 3 rho * burnolPrimeCharacter 3 (lineReflect rho)) ^ b *
      xiHorizontalSourceCayleyPhase rho ^ c

def xiHorizontalCollisionPrimeCayleyPhasePencil
    (T : ℝ) (a b c : ℕ) : ℂ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset,
    ((analyticOrderAt xi rho).toNat : ℂ) *
      xiHorizontalPrimePhase 2 rho.im ^ a *
      xiHorizontalPrimePhase 3 rho.im ^ b *
      xiHorizontalSourceCayleyPhase rho ^ c

def xiHorizontalCollisionPrimeCayleyGroupedPencil
    (T : ℝ) (a b c : ℕ) : ℂ :=
  finiteTwoPhasePencil
    ((stripZeros_finite T).toFinset.image Complex.im)
    (fun gamma => xiHorizontalSourceCayleyFiberPencil T gamma c)
    (xiHorizontalPrimePhase 2) (xiHorizontalPrimePhase 3) a b

theorem xiHorizontalCollisionPrimeCayleySourcePencil_eq_phasePencil
    (T : ℝ) (a b c : ℕ) :
    xiHorizontalCollisionPrimeCayleySourcePencil T a b c =
      xiHorizontalCollisionPrimeCayleyPhasePencil T a b c := by
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase (by norm_num),
    burnolPrimeCharacter_mul_lineReflect_eq_horizontalPrimePhase (by norm_num)]
  rfl

theorem xiHorizontalCollisionPrimeCayleyPhasePencil_eq_groupedPencil
    (T : ℝ) (a b c : ℕ) :
    xiHorizontalCollisionPrimeCayleyPhasePencil T a b c =
      xiHorizontalCollisionPrimeCayleyGroupedPencil T a b c := by
  classical
  let S := (stripZeros_finite T).toFinset
  let G := S.image Complex.im
  let m : ℂ → ℕ := fun rho => (analyticOrderAt xi rho).toNat
  unfold xiHorizontalCollisionPrimeCayleyPhasePencil
    xiHorizontalCollisionPrimeCayleyGroupedPencil
    xiHorizontalSourceCayleyFiberPencil finiteTwoPhasePencil finiteExponentialPencil
  change (∑ rho ∈ S,
      (m rho : ℂ) * xiHorizontalPrimePhase 2 rho.im ^ a *
        xiHorizontalPrimePhase 3 rho.im ^ b *
        xiHorizontalSourceCayleyPhase rho ^ c) =
    ∑ gamma ∈ G,
      (∑ rho ∈ S.filter (fun rho => rho.im = gamma),
        (m rho : ℂ) * xiHorizontalSourceCayleyPhase rho ^ c) *
          xiHorizontalPrimePhase 2 gamma ^ a *
          xiHorizontalPrimePhase 3 gamma ^ b
  rw [eq_comm]
  calc
    (∑ gamma ∈ G,
        (∑ rho ∈ S.filter (fun rho => rho.im = gamma),
          (m rho : ℂ) * xiHorizontalSourceCayleyPhase rho ^ c) *
            xiHorizontalPrimePhase 2 gamma ^ a *
            xiHorizontalPrimePhase 3 gamma ^ b) =
      ∑ gamma ∈ G, ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
        ((m rho : ℂ) * xiHorizontalSourceCayleyPhase rho ^ c) *
          xiHorizontalPrimePhase 2 gamma ^ a *
          xiHorizontalPrimePhase 3 gamma ^ b := by
          apply Finset.sum_congr rfl
          intro gamma hgamma
          rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ gamma ∈ G, ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
        ((m rho : ℂ) * xiHorizontalSourceCayleyPhase rho ^ c) *
          xiHorizontalPrimePhase 2 rho.im ^ a *
          xiHorizontalPrimePhase 3 rho.im ^ b := by
          apply Finset.sum_congr rfl
          intro gamma hgamma
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [(Finset.mem_filter.mp hrho).2]
    _ = ∑ rho ∈ S,
        ((m rho : ℂ) * xiHorizontalSourceCayleyPhase rho ^ c) *
          xiHorizontalPrimePhase 2 rho.im ^ a *
          xiHorizontalPrimePhase 3 rho.im ^ b := by
          exact Finset.sum_fiberwise_of_maps_to
            (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
            (fun rho => ((m rho : ℂ) * xiHorizontalSourceCayleyPhase rho ^ c) *
              xiHorizontalPrimePhase 2 rho.im ^ a *
              xiHorizontalPrimePhase 3 rho.im ^ b)
    _ = ∑ rho ∈ S,
        (m rho : ℂ) * xiHorizontalPrimePhase 2 rho.im ^ a *
          xiHorizontalPrimePhase 3 rho.im ^ b *
          xiHorizontalSourceCayleyPhase rho ^ c := by
          apply Finset.sum_congr rfl
          intro rho hrho
          ring

theorem xiHorizontalCollisionPrimeCayleySourcePencil_eq_groupedPencil
    (T : ℝ) (a b c : ℕ) :
    xiHorizontalCollisionPrimeCayleySourcePencil T a b c =
      xiHorizontalCollisionPrimeCayleyGroupedPencil T a b c := by
  rw [xiHorizontalCollisionPrimeCayleySourcePencil_eq_phasePencil,
    xiHorizontalCollisionPrimeCayleyPhasePencil_eq_groupedPencil]

/-- At horizontal depth zero the new carrier is exactly the earlier two-prime carrier. -/
theorem xiHorizontalCollisionPrimeCayleySourcePencil_zero
    (T : ℝ) (a b : ℕ) :
    xiHorizontalCollisionPrimeCayleySourcePencil T a b 0 =
      xiHorizontalCollisionTwoPrimeSourcePencil T a b := by
  simp [xiHorizontalCollisionPrimeCayleySourcePencil,
    xiHorizontalCollisionTwoPrimeSourcePencil]

/-- The two prime clocks first reduce the three-depth pencil to its exact horizontal-fibre
energy, without yet averaging away horizontal source orientation. -/
theorem tendsto_xiHorizontalCollisionPrimeCayleySourcePencil_verticalEnergy
    (T : ℝ) (c : ℕ) :
    Tendsto
      (fun N : ℕ => ((N : ℝ)⁻¹ ^ 2) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          ‖xiHorizontalCollisionPrimeCayleySourcePencil T a b c‖ ^ 2)
      atTop (nhds (xiHorizontalSourceCayleyResolvedEnergy T c)) := by
  let G := (stripZeros_finite T).toFinset.image Complex.im
  have hlim := tendsto_finiteTwoPhasePencil_cesaro_norm_sq G
    (fun gamma => xiHorizontalSourceCayleyFiberPencil T gamma c)
    (xiHorizontalPrimePhase 2) (xiHorizontalPrimePhase 3)
    (fun gamma _ => xiHorizontalPrimePhase_norm 2 gamma)
    (fun gamma _ => xiHorizontalPrimePhase_norm 3 gamma)
    xiHorizontalPrimePhase_pair_injective.injOn
  convert hlim using 1
  · funext N
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [xiHorizontalCollisionPrimeCayleySourcePencil_eq_groupedPencil]
    rfl
  · rfl

theorem tendsto_xiHorizontalSourceCayleyFiberPencil_cesaro_norm_sq
    {T gamma : ℝ}
    (_hgamma : gamma ∈ (stripZeros_finite T).toFinset.image Complex.im) :
    Tendsto
      (fun M : ℕ => (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M,
        ‖xiHorizontalSourceCayleyFiberPencil T gamma c‖ ^ 2)
      atTop
      (nhds (∑ rho ∈ (stripZeros_finite T).toFinset.filter
        (fun rho => rho.im = gamma),
          (((analyticOrderAt xi rho).toNat : ℝ) ^ 2))) := by
  let F := (stripZeros_finite T).toFinset.filter (fun rho => rho.im = gamma)
  have hinj : Set.InjOn xiHorizontalSourceCayleyPhase (F : Set ℂ) := by
    intro rho hrho sigma hsigma hphase
    apply eq_of_im_eq_of_horizontalSourceCayleyPhase_eq
    · exact (Finset.mem_filter.mp hrho).2.trans (Finset.mem_filter.mp hsigma).2.symm
    · exact hphase
  have hlim := tendsto_finiteExponentialPencil_cesaro_norm_sq F
    (fun rho => ((analyticOrderAt xi rho).toNat : ℂ))
    xiHorizontalSourceCayleyPhase
    (fun rho _ => xiHorizontalSourceCayleyPhase_norm rho) hinj
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    apply Finset.sum_congr rfl
    intro rho hrho
    norm_num

/-- Averaging the non-equivariant source-Cayley depth resolves every point inside each horizontal
fibre and returns the local multiplicity-square census. -/
theorem tendsto_xiHorizontalSourceCayleyResolvedEnergy_cesaro
    (T : ℝ) :
    Tendsto
      (fun M : ℕ => (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M,
        xiHorizontalSourceCayleyResolvedEnergy T c)
      atTop (nhds (xiStripWindowLocalSquareSum T : ℝ)) := by
  let S := (stripZeros_finite T).toFinset
  let G := S.image Complex.im
  have hsum := tendsto_finsetSum G
    (fun gamma hgamma =>
      tendsto_xiHorizontalSourceCayleyFiberPencil_cesaro_norm_sq hgamma)
  convert hsum using 1
  · funext M
    simp only [xiHorizontalSourceCayleyResolvedEnergy]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  · apply congrArg nhds
    rw [xiStripWindowLocalSquareSum]
    push_cast
    symm
    change (∑ gamma ∈ G, ∑ rho ∈ S.filter (fun rho => rho.im = gamma),
      ((analyticOrderAt xi rho).toNat : ℝ) ^ 2) =
      ∑ rho ∈ S, ((analyticOrderAt xi rho).toNat : ℝ) ^ 2
    exact Finset.sum_fiberwise_of_maps_to
      (fun rho hrho => Finset.mem_image.mpr ⟨rho, hrho, rfl⟩)
      (fun rho => ((analyticOrderAt xi rho).toNat : ℝ) ^ 2)

/-- At depth zero, all horizontal rates are forgotten and the resolved energy is exactly the
horizontal square census. -/
theorem xiHorizontalSourceCayleyResolvedEnergy_zero (T : ℝ) :
    xiHorizontalSourceCayleyResolvedEnergy T 0 =
      (xiStripWindowHorizontalSquareSum T : ℝ) := by
  rw [xiHorizontalSourceCayleyResolvedEnergy, xiStripWindowHorizontalSquareSum]
  push_cast
  apply Finset.sum_congr rfl
  intro gamma hgamma
  rw [show xiHorizontalSourceCayleyFiberPencil T gamma 0 =
      (xiHorizontalMultiplicity gamma : ℂ) by
    rw [xiHorizontalSourceCayleyFiberPencil, finiteExponentialPencil]
    simp only [pow_zero, mul_one]
    rw [horizontalMultiplicity_eq_sum_stripZeros_filter_im hgamma]
    push_cast
    rfl]
  simp

/-- Finite-depth horizontal information loss: depth zero retains horizontal collisions, while the
averaged source-Cayley frame progressively resolves the individual points. -/
def xiHorizontalPrimeCayleyInformationLoss (T : ℝ) (M : ℕ) : ℝ :=
  (xiStripWindowHorizontalSquareSum T : ℝ) -
    (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M,
      xiHorizontalSourceCayleyResolvedEnergy T c

/-- The loss compares two depths of one carrier: reflection-quotiented depth zero against its
finite source-horizontal Cayley resolution. -/
theorem xiHorizontalPrimeCayleyInformationLoss_eq_zeroDepth_sub_average
    (T : ℝ) (M : ℕ) :
    xiHorizontalPrimeCayleyInformationLoss T M =
      xiHorizontalSourceCayleyResolvedEnergy T 0 -
        (M : ℝ)⁻¹ * ∑ c ∈ Finset.range M,
          xiHorizontalSourceCayleyResolvedEnergy T c := by
  rw [xiHorizontalPrimeCayleyInformationLoss,
    xiHorizontalSourceCayleyResolvedEnergy_zero]

/-- Exact Frankenstein identity: source-horizontal information loss converges to `O(T)`. -/
theorem tendsto_xiHorizontalPrimeCayleyInformationLoss
    (T : ℝ) :
    Tendsto (xiHorizontalPrimeCayleyInformationLoss T) atTop
      (nhds (xiHorizontalCollisionCharge T : ℝ)) := by
  have hconst : Tendsto (fun _ : ℕ => (xiStripWindowHorizontalSquareSum T : ℝ))
      atTop (nhds (xiStripWindowHorizontalSquareSum T : ℝ)) := tendsto_const_nhds
  have hlim := hconst.sub (tendsto_xiHorizontalSourceCayleyResolvedEnergy_cesaro T)
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    rw [xiStripWindowHorizontalSquareSum_eq_localSquare_add_collisionCharge]
    push_cast
    ring

/-- RH is equivalent to zero information loss between the reflection-quotiented prime carrier and
its full source-horizontal Cayley resolution. -/
theorem riemannHypothesis_iff_horizontalPrimeCayleyInformationLoss_tendsto_zero :
    RiemannHypothesis ↔
      ∀ T : ℝ, Tendsto (xiHorizontalPrimeCayleyInformationLoss T) atTop (nhds 0) := by
  constructor
  · intro hRH T
    simpa [xiHorizontalCollisionCharge_eq_zero_of_riemannHypothesis hRH T] using
      tendsto_xiHorizontalPrimeCayleyInformationLoss T
  · intro hloss
    apply riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero.mpr
    intro T
    have hzero : (xiHorizontalCollisionCharge T : ℝ) = 0 :=
      tendsto_nhds_unique (tendsto_xiHorizontalPrimeCayleyInformationLoss T) (hloss T)
    exact_mod_cast hzero

/-- Quantized source endpoint: an eventual absolute information-loss ceiling below two excludes
every reflected off-line pair. -/
theorem riemannHypothesis_of_horizontalPrimeCayleyInformationLoss_eventually_lt_two
    (hloss : ∀ T : ℝ, ∃ C : ℝ, C < 2 ∧
      ∀ᶠ M : ℕ in atTop, xiHorizontalPrimeCayleyInformationLoss T M ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_forall_horizontalCollisionCharge_lt_two.mpr
  intro T
  obtain ⟨C, hC, hbound⟩ := hloss T
  have hle : (xiHorizontalCollisionCharge T : ℝ) ≤ C :=
    le_of_tendsto (tendsto_xiHorizontalPrimeCayleyInformationLoss T) hbound
  exact_mod_cast hle.trans_lt hC

theorem riemannHypothesis_iff_horizontalPrimeCayleyInformationLoss_eventually_lt_two :
    RiemannHypothesis ↔
      ∀ T : ℝ, ∃ C : ℝ, C < 2 ∧
        ∀ᶠ M : ℕ in atTop, xiHorizontalPrimeCayleyInformationLoss T M ≤ C := by
  constructor
  · intro hRH T
    refine ⟨1, by norm_num, ?_⟩
    have hzero :=
      riemannHypothesis_iff_horizontalPrimeCayleyInformationLoss_tendsto_zero.mp hRH T
    filter_upwards [hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with M hM
    exact hM.le
  · exact riemannHypothesis_of_horizontalPrimeCayleyInformationLoss_eventually_lt_two

end
end RHTower
