import GaloisForLFunctions.RHTower.CCM.CCMFirstClockJuliaEquilibriumGram

/-!
# Two-packet Julia capacity on the CCM first clock

The Julia equilibrium kernel controls the complete signed prime-power packet, without first
splitting its coefficients into good and bad parts.  Its coherent prime energy and the energy of
the packet augmented by the continuous archimedean budget are therefore nonnegative directly.

For the admitted prime window, the source decomposition identifies that signed energy with good
energy plus bad energy minus twice their mixed correlation.  The universal two-packet Cauchy law
also makes the corresponding two-channel determinant nonnegative.
-/

open scoped BigOperators
open Filter Set

namespace RHTower

noncomputable section

/-- Origin correlation of the literal first-clock prime-power coefficients. -/
def ccmFirstClockJuliaPrimePowerOriginCorrelation
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ∑ i, HTGeometry.juliaDefectAttenuationKernel
      (x * Real.log (p i : ℝ)) *
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)

/-- Coherent Julia energy of the literal signed prime-power packet. -/
def ccmFirstClockJuliaPrimePowerCoherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  GaloisForLFunctions.HTGeometry.realKernelPacketEnergy
    HTGeometry.juliaDefectAttenuationKernel
    (fun i => x * Real.log (p i : ℝ))
    (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i))

/-- Coherent Julia energy of the archimedean budget and all literal prime-power coefficients. -/
def ccmFirstClockJuliaCompletedCoherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  GaloisForLFunctions.HTGeometry.realKernelPacketEnergy
    HTGeometry.juliaDefectAttenuationKernel
    (Fin.cases 0 (fun i => x * Real.log (p i : ℝ)))
    (Fin.cases (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L))
      (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)))

/-- Coherent Julia energy of the reduced good prime channel. -/
def ccmFirstClockJuliaGoodCoherentEnergy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) : ℝ :=
  ∑ i, ∑ j,
    ccmFirstClockReducedGoodPrimeTerm L (p i) *
      HTGeometry.juliaDefectAttenuationKernel
        (x * Real.log (p j : ℝ) - x * Real.log (p i : ℝ)) *
      ccmFirstClockReducedGoodPrimeTerm L (p j)

/-- Mixed Julia correlation of a reduced good packet with a reduced bad packet. -/
def ccmFirstClockJuliaGoodBadCoherentCorrelation
    {N M : ℕ} (x L : ℝ)
    (p : Fin N → Nat.Primes) (q : Fin M → Nat.Primes) : ℝ :=
  ∑ i, ∑ j,
    ccmFirstClockReducedGoodPrimeTerm L (p i) *
      HTGeometry.juliaDefectAttenuationKernel
        (x * Real.log (q j : ℝ) - x * Real.log (p i : ℝ)) *
      ccmFirstClockReducedBadPrimeTerm L (q j)

/-- Literal, reduced-good, and reduced-bad prime coefficients as three coherent channels over the
same prime-logarithm nodes. -/
def ccmFirstClockJuliaPrimeDecompositionChannelMass
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes) : Fin 3 → Fin N → ℝ :=
  fun r i => Fin.cases
    (ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i))
    (Fin.cases
      (ccmFirstClockReducedGoodPrimeTerm L (p i))
      (fun _ => ccmFirstClockReducedBadPrimeTerm L (p i))) r

/-- Independent good/bad arithmetic source channels before the literal channel is reconstructed. -/
def ccmFirstClockJuliaGoodBadChannelMass
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes) : Fin 2 → Fin N → ℝ :=
  fun r i => ![
    ccmFirstClockReducedGoodPrimeTerm L (p i),
    ccmFirstClockReducedBadPrimeTerm L (p i)] r

/-- Fixed reconstruction map `(good, bad) ↦ (literal, good, bad)`, with
`literal = good - bad`. -/
def ccmFirstClockJuliaPrimeDecompositionMatrix : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, -1; 1, 0; 0, 1]

@[simp] theorem ccmFirstClockJuliaPrimeDecompositionChannelMass_zero
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes) (i : Fin N) :
    ccmFirstClockJuliaPrimeDecompositionChannelMass L p 0 i =
      ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i) := rfl

@[simp] theorem ccmFirstClockJuliaPrimeDecompositionChannelMass_one
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes) (i : Fin N) :
    ccmFirstClockJuliaPrimeDecompositionChannelMass L p 1 i =
      ccmFirstClockReducedGoodPrimeTerm L (p i) := rfl

@[simp] theorem ccmFirstClockJuliaPrimeDecompositionChannelMass_two
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes) (i : Fin N) :
    ccmFirstClockJuliaPrimeDecompositionChannelMass L p 2 i =
      ccmFirstClockReducedBadPrimeTerm L (p i) := rfl

/-- **Exact arithmetic two-channel factorization.**  On the admitted source window, the full
literal/good/bad coefficient matrix factors through the two independent good/bad channels. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelMass_eq_decomposition_mul_goodBad
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    Matrix.of (ccmFirstClockJuliaPrimeDecompositionChannelMass L p) =
      ccmFirstClockJuliaPrimeDecompositionMatrix *
        Matrix.of (ccmFirstClockJuliaGoodBadChannelMass L p) := by
  ext r i
  fin_cases r
  · change ccmFirstClockJuliaPrimeDecompositionChannelMass L p 0 i = _
    rw [ccmFirstClockJuliaPrimeDecompositionChannelMass_zero]
    simp [ccmFirstClockJuliaPrimeDecompositionMatrix,
      ccmFirstClockJuliaGoodBadChannelMass, Matrix.mul_apply, Fin.sum_univ_two]
    rw [ccmFirstClockPrimePowerTowerMass_eq_reducedGoodPrimeTerm_sub_bad
      (hpCut := hpCut i)]
    ring
  · change ccmFirstClockJuliaPrimeDecompositionChannelMass L p 1 i = _
    rw [ccmFirstClockJuliaPrimeDecompositionChannelMass_one]
    simp [ccmFirstClockJuliaPrimeDecompositionMatrix,
      ccmFirstClockJuliaGoodBadChannelMass, Matrix.mul_apply, Fin.sum_univ_two]
  · change ccmFirstClockJuliaPrimeDecompositionChannelMass L p 2 i = _
    rw [ccmFirstClockJuliaPrimeDecompositionChannelMass_two]
    simp [ccmFirstClockJuliaPrimeDecompositionMatrix,
      ccmFirstClockJuliaGoodBadChannelMass, Matrix.mul_apply, Fin.sum_univ_two]

/-- The admitted literal/good/bad arithmetic source has channel rank at most two. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelMass_rank_le_two
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    (Matrix.of (ccmFirstClockJuliaPrimeDecompositionChannelMass L p)).rank ≤ 2 := by
  rw [ccmFirstClockJuliaPrimeDecompositionChannelMass_eq_decomposition_mul_goodBad
    L p hpCut]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width
      ccmFirstClockJuliaPrimeDecompositionMatrix)

/-- Coherent three-channel Gram matrix of the literal/good/bad CCM prime decomposition. -/
def ccmFirstClockJuliaPrimeDecompositionChannelGram
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  GaloisForLFunctions.HTGeometry.realKernelSharedNodePacketChannelGram
    HTGeometry.juliaDefectAttenuationKernel
    (fun i => x * Real.log (p i : ℝ))
    (ccmFirstClockJuliaPrimeDecompositionChannelMass L p)

@[simp] theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_zero_zero
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 0 0 =
      ccmFirstClockJuliaPrimePowerCoherentEnergy x L p := rfl

@[simp] theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_one_one
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 1 1 =
      ccmFirstClockJuliaGoodCoherentEnergy x L p := rfl

@[simp] theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_two_two
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 2 2 =
      ccmFirstClockJuliaBadCoherentEnergy x L p := rfl

@[simp] theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_one_two
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 1 2 =
      ccmFirstClockJuliaGoodBadCoherentCorrelation x L p p := rfl

/-- **CCM coherent-channel positivity.**  The literal prime-power packet and its reduced good and
bad channels form a positive-semidefinite Gram matrix for every finite prime family.  No aperture,
prime-window, sign, or RH hypothesis is required. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).PosSemidef := by
  exact
    GaloisForLFunctions.HTGeometry.realKernelPacketChannelGram_posSemidef_of_positiveDefinite
      HTGeometry.juliaDefectAttenuationKernel
      HTGeometry.positiveDefiniteOnReal_juliaDefectAttenuationKernel
      HTGeometry.juliaDefectAttenuationKernel_neg _ _

/-- The full three-channel coherent determinant is nonnegative without a prime-window cutoff. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_det_nonneg
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    0 ≤ (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).det :=
  (ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef x L p).det_nonneg

/-- **CCM arithmetic channel-dimension law.**  On the admitted source window, Julia equilibrium
transport preserves positivity and cannot lift the two-dimensional good/bad arithmetic source to
a third coherent direction. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef_and_rank_le_two
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).PosSemidef ∧
      (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).rank ≤ 2 := by
  refine ⟨ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef x L p, ?_⟩
  exact
    (GaloisForLFunctions.HTGeometry.realKernelSharedNodePacketChannelGram_rank_le_massRank
        HTGeometry.juliaDefectAttenuationKernel
        (fun i => x * Real.log (p i : ℝ))
        (ccmFirstClockJuliaPrimeDecompositionChannelMass L p)).trans
      (ccmFirstClockJuliaPrimeDecompositionChannelMass_rank_le_two L p hpCut)

/-- On the admitted prime window, the literal row is exactly the good row minus the bad row. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_row_literal_eq_good_sub_bad
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) (s : Fin 3) :
    ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 0 s =
      ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 1 s -
        ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 2 s := by
  simp only [ccmFirstClockJuliaPrimeDecompositionChannelGram,
    GaloisForLFunctions.HTGeometry.realKernelSharedNodePacketChannelGram,
    GaloisForLFunctions.HTGeometry.realKernelPacketChannelGram,
    GaloisForLFunctions.HTGeometry.realKernelPacketCross,
    ccmFirstClockJuliaPrimeDecompositionChannelMass_zero,
    ccmFirstClockJuliaPrimeDecompositionChannelMass_one,
    ccmFirstClockJuliaPrimeDecompositionChannelMass_two]
  simp_rw [ccmFirstClockPrimePowerTowerMass_eq_reducedGoodPrimeTerm_sub_bad
    (hpCut := hpCut _), sub_mul]
  simp_rw [Finset.sum_sub_distrib]

/-- On the admitted prime window, the literal column is exactly the good column minus the bad
column. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_col_literal_eq_good_sub_bad
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) (r : Fin 3) :
    ccmFirstClockJuliaPrimeDecompositionChannelGram x L p r 0 =
      ccmFirstClockJuliaPrimeDecompositionChannelGram x L p r 1 -
        ccmFirstClockJuliaPrimeDecompositionChannelGram x L p r 2 := by
  simp only [ccmFirstClockJuliaPrimeDecompositionChannelGram,
    GaloisForLFunctions.HTGeometry.realKernelSharedNodePacketChannelGram,
    GaloisForLFunctions.HTGeometry.realKernelPacketChannelGram,
    GaloisForLFunctions.HTGeometry.realKernelPacketCross,
    ccmFirstClockJuliaPrimeDecompositionChannelMass_zero,
    ccmFirstClockJuliaPrimeDecompositionChannelMass_one,
    ccmFirstClockJuliaPrimeDecompositionChannelMass_two]
  simp_rw [ccmFirstClockPrimePowerTowerMass_eq_reducedGoodPrimeTerm_sub_bad
    (hpCut := hpCut _), mul_sub]
  simp_rw [Finset.sum_sub_distrib]

/-- Pointwise source relation among literal, good, and bad channel masses. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelMass_sourceRelation
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) (i : Fin N) :
    ∑ s, ccmFirstClockJuliaPrimeDecompositionChannelMass L p s i *
      (![1, -1, 1] : Fin 3 → ℝ) s = 0 := by
  rw [Fin.sum_univ_three]
  simp
  rw [ccmFirstClockPrimePowerTowerMass_eq_reducedGoodPrimeTerm_sub_bad
    (hpCut := hpCut i)]
  ring

/-- **Exact arithmetic null channel.**  The coefficient vector `(1, -1, 1)` is in the kernel of
the coherent literal/good/bad Gram precisely because the source identity is
`literal = good - bad`. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_mulVec_sourceRelation_eq_zero
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).mulVec
        (![1, -1, 1] : Fin 3 → ℝ) = 0 := by
  exact
    GaloisForLFunctions.HTGeometry.realKernelSharedNodePacketChannelGram_mulVec_eq_zero_of_mass_relation
        HTGeometry.juliaDefectAttenuationKernel
        (fun i => x * Real.log (p i : ℝ))
        (ccmFirstClockJuliaPrimeDecompositionChannelMass L p)
        (![1, -1, 1] : Fin 3 → ℝ)
        (ccmFirstClockJuliaPrimeDecompositionChannelMass_sourceRelation L p hpCut)

/-- **CCM coherent boundary law.**  On the admitted source window, the literal/good/bad Gram is
positive semidefinite and lies exactly on its singular boundary, with the arithmetic source
relation as a nonzero null direction. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef_and_det_eq_zero
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).PosSemidef ∧
      (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).det = 0 := by
  refine ⟨(ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef_and_rank_le_two
    x L p hpCut).1, ?_⟩
  by_contra hdet
  have hunitDet : IsUnit
      (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hunit : IsUnit (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunitDet
  have hrank :
      (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).rank = 3 := by
    simpa using Matrix.rank_of_isUnit _ hunit
  have hle :=
    (ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef_and_rank_le_two
      x L p hpCut).2
  omega

/-- The admitted literal/good/bad coherent Gram has rank defect. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_det_eq_zero
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L p).det = 0 :=
  (ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef_and_det_eq_zero
    x L p hpCut).2

/-- Diagonal polarization of the exact arithmetic null channel.  Literal coherent energy is the
good energy plus bad energy minus twice their coherent correlation. -/
theorem ccmFirstClockJuliaPrimeDecompositionChannelGram_literalDiagonal
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 0 0 =
      ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 1 1 +
        ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 2 2 -
          2 * ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 1 2 := by
  rw [ccmFirstClockJuliaPrimeDecompositionChannelGram_row_literal_eq_good_sub_bad
      x L p hpCut 0,
    ccmFirstClockJuliaPrimeDecompositionChannelGram_col_literal_eq_good_sub_bad
      x L p hpCut 1,
    ccmFirstClockJuliaPrimeDecompositionChannelGram_col_literal_eq_good_sub_bad
      x L p hpCut 2]
  have hHermitian :=
    (ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef x L p).isHermitian.eq
  have hsym :
      ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 2 1 =
        ccmFirstClockJuliaPrimeDecompositionChannelGram x L p 1 2 := by
    simpa using congrFun (congrFun hHermitian 1) 2
  rw [hsym]
  ring

/-- Arithmetic Julia attenuation is the origin correlation of the literal prime-power packet;
no good/bad decomposition or prime-window cutoff is needed. -/
theorem ccmFirstClockJuliaAttenuatedCompletedPacket_eq_continuousBudget_add_primePowerOrigin
    {N : ℕ} {x : ℝ} (hx : 0 < x) (L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L p =
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ccmFirstClockJuliaPrimePowerOriginCorrelation x L p := by
  rw [ccmFirstClockJuliaAttenuatedCompletedPacket,
    ccmFirstClockJuliaPrimePowerOriginCorrelation]
  apply congrArg (fun z => ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) + z)
  apply Finset.sum_congr rfl
  intro i _
  rw [gammaSewnMobiusJuliaPrimeAttenuation_eq_equilibriumKernel hx]

/-- The literal prime-packet Julia origin correlation varies continuously with attenuation
scale. -/
theorem continuous_ccmFirstClockJuliaPrimePowerOriginCorrelation
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes) :
    Continuous (fun x => ccmFirstClockJuliaPrimePowerOriginCorrelation x L p) := by
  unfold ccmFirstClockJuliaPrimePowerOriginCorrelation
  exact continuous_finsetSum _ fun i _ =>
    (HTGeometry.continuous_juliaDefectAttenuationKernel.comp
      (continuous_id.mul continuous_const)).mul continuous_const

/-- **Finite-packet de-attenuation law.**  As positive Julia scale tends to zero, the attenuated
completed packet converges to its literal continuous-budget-plus-prime value.  This is the exact
source connector supplied by the characteristic-function realization. -/
theorem ccmFirstClockJuliaAttenuatedCompletedPacket_tendsto_literal
    {N : ℕ} (L : ℝ) (p : Fin N → Nat.Primes) :
    Tendsto (fun x => ccmFirstClockJuliaAttenuatedCompletedPacket x L p)
      (nhdsWithin 0 (Ioi 0))
      (nhds (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ∑ i, ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i))) := by
  have hcont : Continuous (fun x =>
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ccmFirstClockJuliaPrimePowerOriginCorrelation x L p) :=
    continuous_const.add
      (continuous_ccmFirstClockJuliaPrimePowerOriginCorrelation L p)
  have hlim : Tendsto (fun x =>
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ccmFirstClockJuliaPrimePowerOriginCorrelation x L p)
      (nhdsWithin 0 (Ioi 0))
      (nhds (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
        ∑ i, ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i))) := by
    have h0 : Tendsto (fun x =>
        ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
          ccmFirstClockJuliaPrimePowerOriginCorrelation x L p)
        (nhds 0)
        (nhds (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) +
          ccmFirstClockJuliaPrimePowerOriginCorrelation 0 L p)) :=
      hcont.continuousAt
    simp only [ccmFirstClockJuliaPrimePowerOriginCorrelation,
      zero_mul, HTGeometry.juliaDefectAttenuationKernel_zero, one_mul] at h0
    exact h0.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact
    (ccmFirstClockJuliaAttenuatedCompletedPacket_eq_continuousBudget_add_primePowerOrigin
      hx L p).symm

/-- The literal signed prime-power packet has nonnegative coherent Julia energy. -/
theorem ccmFirstClockJuliaPrimePowerCoherentEnergy_nonneg
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    0 ≤ ccmFirstClockJuliaPrimePowerCoherentEnergy x L p := by
  exact GaloisForLFunctions.HTGeometry.realKernelPacketEnergy_nonneg_of_positiveDefinite
    HTGeometry.juliaDefectAttenuationKernel
    HTGeometry.positiveDefiniteOnReal_juliaDefectAttenuationKernel _ _

/-- The archimedean-plus-prime packet has nonnegative coherent Julia energy. -/
theorem ccmFirstClockJuliaCompletedCoherentEnergy_nonneg
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    0 ≤ ccmFirstClockJuliaCompletedCoherentEnergy x L p := by
  exact GaloisForLFunctions.HTGeometry.realKernelPacketEnergy_nonneg_of_positiveDefinite
    HTGeometry.juliaDefectAttenuationKernel
    HTGeometry.positiveDefiniteOnReal_juliaDefectAttenuationKernel _ _

/-- Exact archimedean/prime decomposition of complete coherent energy. -/
theorem ccmFirstClockJuliaCompletedCoherentEnergy_eq_arch_prime
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaCompletedCoherentEnergy x L p =
      ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) ^ 2 +
        2 * ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) *
          ccmFirstClockJuliaPrimePowerOriginCorrelation x L p +
        ccmFirstClockJuliaPrimePowerCoherentEnergy x L p := by
  simp only [ccmFirstClockJuliaCompletedCoherentEnergy,
    ccmFirstClockJuliaPrimePowerCoherentEnergy,
    ccmFirstClockJuliaPrimePowerOriginCorrelation,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy, Fin.sum_univ_succ,
    Fin.cases_zero, Fin.cases_succ, HTGeometry.juliaDefectAttenuationKernel_zero,
    sub_zero, zero_sub, HTGeometry.juliaDefectAttenuationKernel_neg]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum]
  ring_nf
  rw [← Finset.sum_mul]
  have hcross :
      (∑ i,
          ccmFirstClockContinuousHalfWaveBudget L (Real.pi * L⁻¹ * 2) *
              ccmFirstClockPrimePowerTowerMass L (Real.pi * L⁻¹ * 2) (p i) *
            HTGeometry.juliaDefectAttenuationKernel (x * Real.log (p i : ℝ))) =
        ∑ i,
          ccmFirstClockContinuousHalfWaveBudget L (Real.pi * L⁻¹ * 2) *
              HTGeometry.juliaDefectAttenuationKernel (x * Real.log (p i : ℝ)) *
            ccmFirstClockPrimePowerTowerMass L (Real.pi * L⁻¹ * 2) (p i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcross]
  ring

/-- **Completed-packet capacity.**  The literal Julia-attenuated completed first-clock value is
bounded in square by the coherent energy of the complete archimedean-plus-prime packet. -/
theorem ccmFirstClockJuliaAttenuatedCompletedPacket_sq_le_completedCoherentEnergy
    {N : ℕ} {x : ℝ} (hx : 0 < x) (L : ℝ) (p : Fin N → Nat.Primes) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L p ^ 2 ≤
      ccmFirstClockJuliaCompletedCoherentEnergy x L p := by
  let T : Fin (N + 1) → ℝ :=
    Fin.cases 0 (fun i => x * Real.log (p i : ℝ))
  let B : Fin (N + 1) → ℝ :=
    Fin.cases (ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L))
      (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i))
  have h := HTGeometry.juliaDefectAttenuationKernel_anchorCorrelation_sq_le_gramEnergy T B
  have horigin :
      (∑ i, B i * HTGeometry.juliaDefectAttenuationKernel (T i)) =
        ccmFirstClockJuliaAttenuatedCompletedPacket x L p := by
    simp only [Fin.sum_univ_succ, T, B, Fin.cases_zero, Fin.cases_succ,
      HTGeometry.juliaDefectAttenuationKernel_zero, mul_one]
    rw [ccmFirstClockJuliaAttenuatedCompletedPacket]
    apply congrArg (fun z => ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L) + z)
    apply Finset.sum_congr rfl
    intro i _
    rw [gammaSewnMobiusJuliaPrimeAttenuation_eq_equilibriumKernel hx]
    ring
  rw [horigin] at h
  simpa only [ccmFirstClockJuliaCompletedCoherentEnergy,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy] using h

/-- The deviation from the continuous budget is controlled by the literal signed prime energy.
This removes the cutoff, bad-channel, and negative-excursion interfaces from the capacity law. -/
theorem ccmFirstClockJulia_attenuatedCompletedPacket_sub_continuousBudget_sq_le_primeEnergy
    {N : ℕ} {x : ℝ} (hx : 0 < x) (L : ℝ) (p : Fin N → Nat.Primes) :
    (ccmFirstClockJuliaAttenuatedCompletedPacket x L p -
        ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L)) ^ 2 ≤
      ccmFirstClockJuliaPrimePowerCoherentEnergy x L p := by
  rw [ccmFirstClockJuliaAttenuatedCompletedPacket_eq_continuousBudget_add_primePowerOrigin
    hx L p]
  ring_nf
  simpa only [ccmFirstClockJuliaPrimePowerOriginCorrelation,
    ccmFirstClockJuliaPrimePowerCoherentEnergy,
    GaloisForLFunctions.HTGeometry.realKernelPacketEnergy, mul_comm] using
      (HTGeometry.juliaDefectAttenuationKernel_anchorCorrelation_sq_le_gramEnergy
        (fun i => x * Real.log (p i : ℝ))
        (fun i => ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) (p i)))

/-- Good/bad mixed correlation obeys the two-packet Julia capacity law. -/
theorem ccmFirstClockJuliaGoodBadCoherentCorrelation_sq_le_energy_mul_energy
    {N M : ℕ} (x L : ℝ)
    (p : Fin N → Nat.Primes) (q : Fin M → Nat.Primes) :
    ccmFirstClockJuliaGoodBadCoherentCorrelation x L p q ^ 2 ≤
      ccmFirstClockJuliaGoodCoherentEnergy x L p *
        ccmFirstClockJuliaBadCoherentEnergy x L q := by
  simpa only [ccmFirstClockJuliaGoodBadCoherentCorrelation,
    ccmFirstClockJuliaGoodCoherentEnergy,
    ccmFirstClockJuliaBadCoherentEnergy] using
      (HTGeometry.juliaDefectAttenuationKernel_packetCross_sq_le_energy_mul_energy
        (fun i => x * Real.log (p i : ℝ))
        (fun i => ccmFirstClockReducedGoodPrimeTerm L (p i))
        (fun j => x * Real.log (q j : ℝ))
        (fun j => ccmFirstClockReducedBadPrimeTerm L (q j)))

/-- The Julia good/bad two-channel determinant is nonnegative. -/
theorem ccmFirstClockJuliaGoodBadCoherentDeterminant_nonneg
    {N M : ℕ} (x L : ℝ)
    (p : Fin N → Nat.Primes) (q : Fin M → Nat.Primes) :
    0 ≤ ccmFirstClockJuliaGoodCoherentEnergy x L p *
        ccmFirstClockJuliaBadCoherentEnergy x L q -
      ccmFirstClockJuliaGoodBadCoherentCorrelation x L p q ^ 2 :=
  sub_nonneg.mpr
    (ccmFirstClockJuliaGoodBadCoherentCorrelation_sq_le_energy_mul_energy x L p q)

/-- On the admitted prime window, literal signed prime energy is good energy plus bad energy minus
twice their mixed coherent correlation. -/
theorem ccmFirstClockJuliaPrimePowerCoherentEnergy_eq_good_add_bad_sub_two_cross
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    ccmFirstClockJuliaPrimePowerCoherentEnergy x L p =
      ccmFirstClockJuliaGoodCoherentEnergy x L p +
        ccmFirstClockJuliaBadCoherentEnergy x L p -
          2 * ccmFirstClockJuliaGoodBadCoherentCorrelation x L p p := by
  simpa using
      (ccmFirstClockJuliaPrimeDecompositionChannelGram_literalDiagonal
        x L p hpCut)

/-- Good/bad interference cannot exceed half of their total coherent energy on the admitted
prime window. -/
theorem two_mul_ccmFirstClockJuliaGoodBadCoherentCorrelation_le_energy_add_energy
    {N : ℕ} (x L : ℝ) (p : Fin N → Nat.Primes)
    (hpCut : ∀ i, (p i : ℕ) ≤ ⌊Real.exp L⌋₊) :
    2 * ccmFirstClockJuliaGoodBadCoherentCorrelation x L p p ≤
      ccmFirstClockJuliaGoodCoherentEnergy x L p +
        ccmFirstClockJuliaBadCoherentEnergy x L p := by
  have hnonneg := ccmFirstClockJuliaPrimePowerCoherentEnergy_nonneg x L p
  rw [ccmFirstClockJuliaPrimePowerCoherentEnergy_eq_good_add_bad_sub_two_cross
    x L p hpCut] at hnonneg
  linarith

/-! ### Canonical full admitted prime window -/

/-- Canonical enumeration of every prime admitted at first-clock aperture `L`. -/
def ccmFirstClockAdmittedPrimePacket (L : ℝ) :
    Fin (Nat.primesLE ⌊Real.exp L⌋₊).card → Nat.Primes :=
  fun i => ⟨((Nat.primesLE ⌊Real.exp L⌋₊).equivFin.symm i : ℕ),
    ((Nat.mem_primesLE).mp
      ((Nat.primesLE ⌊Real.exp L⌋₊).equivFin.symm i).2).2⟩

/-- Every member of the canonical packet satisfies the source cutoff by construction. -/
theorem ccmFirstClockAdmittedPrimePacket_le_cutoff (L : ℝ)
    (i : Fin (Nat.primesLE ⌊Real.exp L⌋₊).card) :
    (ccmFirstClockAdmittedPrimePacket L i : ℕ) ≤ ⌊Real.exp L⌋₊ := by
  exact ((Nat.mem_primesLE).mp
    ((Nat.primesLE ⌊Real.exp L⌋₊).equivFin.symm i).2).1

/-- Canonical packet summation is exactly summation over the full admitted prime set. -/
theorem sum_ccmFirstClockAdmittedPrimePacket
    {M : Type*} [AddCommMonoid M] (L : ℝ) (f : ℕ → M) :
    ∑ i, f (ccmFirstClockAdmittedPrimePacket L i) =
      ∑ p ∈ Nat.primesLE ⌊Real.exp L⌋₊, f p := by
  rw [← Finset.sum_coe_sort (Nat.primesLE ⌊Real.exp L⌋₊) f]
  exact Equiv.sum_comp (Nat.primesLE ⌊Real.exp L⌋₊).equivFin.symm
    fun x => f (x : ℕ)

/-- The published finite first-clock prime source is exactly the literal mass of the canonical
full admitted packet.  No enumeration or cutoff hypothesis remains. -/
theorem ccmFirstClockPrimeSineMass_eq_sum_admittedPrimePacket
    (L : ℝ) :
    ccmFirstClockPrimeSineMass L (2 * Real.pi / L) =
      ∑ i, ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L)
        (ccmFirstClockAdmittedPrimePacket L i) := by
  rw [ccmFirstClockPrimeSineMass_eq_sum_primePowerTowerMass]
  exact (sum_ccmFirstClockAdmittedPrimePacket L fun p =>
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p).symm

/-- **Literal-source de-attenuation law.**  For the canonical full admitted prime window, the
zero-scale Julia limit is exactly the published first-clock source, including its archimedean
half-wave budget. -/
theorem ccmFirstClockJuliaFullPrimeWindow_tendsto_publishedSource
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun x => ccmFirstClockJuliaAttenuatedCompletedPacket x L
        (ccmFirstClockAdmittedPrimePacket L))
      (nhdsWithin 0 (Ioi 0))
      (nhds (Real.pi *
        ccmPublishedSourceSineCoefficient (L / 2) (2 * Real.pi / L))) := by
  have hperiod : (2 * Real.pi / L) * L = 2 * Real.pi := by
    field_simp
  have hsource :=
    pi_mul_ccmPublishedSourceSineCoefficient_eq_halfWaveBudget_add_prime
      hL hperiod
  have hlim :=
    ccmFirstClockJuliaAttenuatedCompletedPacket_tendsto_literal
      L (ccmFirstClockAdmittedPrimePacket L)
  convert hlim using 1
  rw [← ccmFirstClockPrimeSineMass_eq_sum_admittedPrimePacket]
  exact congrArg nhds hsource

/-- **Full-window arithmetic channel law.**  The actual complete finite prime source at aperture
`L` has a positive-semidefinite Julia Gram of rank at most two.  The arbitrary-packet cutoff
interface has disappeared. -/
theorem ccmFirstClockJuliaFullPrimeDecompositionChannelGram_posSemidef_and_rank_le_two
    (x L : ℝ) :
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L
      (ccmFirstClockAdmittedPrimePacket L)).PosSemidef ∧
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L
      (ccmFirstClockAdmittedPrimePacket L)).rank ≤ 2 :=
  ccmFirstClockJuliaPrimeDecompositionChannelGram_posSemidef_and_rank_le_two
    x L (ccmFirstClockAdmittedPrimePacket L)
      (ccmFirstClockAdmittedPrimePacket_le_cutoff L)

/-- The full admitted literal/good/bad Julia Gram is singular at every aperture. -/
theorem ccmFirstClockJuliaFullPrimeDecompositionChannelGram_det_eq_zero
    (x L : ℝ) :
    (ccmFirstClockJuliaPrimeDecompositionChannelGram x L
      (ccmFirstClockAdmittedPrimePacket L)).det = 0 :=
  ccmFirstClockJuliaPrimeDecompositionChannelGram_det_eq_zero
    x L (ccmFirstClockAdmittedPrimePacket L)
      (ccmFirstClockAdmittedPrimePacket_le_cutoff L)

/-- **Full-window Julia capacity law.**  On the literal complete admitted prime source, coherent
positivity simultaneously controls the attenuated completed source and its deviation from the
continuous budget; if the source is negative, the bad-channel coherent energy carries its entire
squared excursion. -/
theorem ccmFirstClockJuliaFullPrimeWindowCapacityLaw
    {x L : ℝ} (hx : 0 < x) (hL : 0 < L) :
    ccmFirstClockJuliaAttenuatedCompletedPacket x L
        (ccmFirstClockAdmittedPrimePacket L) ^ 2 ≤
        ccmFirstClockJuliaCompletedCoherentEnergy x L
          (ccmFirstClockAdmittedPrimePacket L) ∧
    (ccmFirstClockJuliaAttenuatedCompletedPacket x L
          (ccmFirstClockAdmittedPrimePacket L) -
        ccmFirstClockContinuousHalfWaveBudget L (2 * Real.pi / L)) ^ 2 ≤
        ccmFirstClockJuliaPrimePowerCoherentEnergy x L
          (ccmFirstClockAdmittedPrimePacket L) ∧
    (ccmFirstClockJuliaAttenuatedCompletedPacket x L
          (ccmFirstClockAdmittedPrimePacket L) < 0 →
        ccmFirstClockJuliaAttenuatedCompletedPacket x L
            (ccmFirstClockAdmittedPrimePacket L) ^ 2 ≤
          ccmFirstClockJuliaBadCoherentEnergy x L
            (ccmFirstClockAdmittedPrimePacket L)) := by
  exact ⟨ccmFirstClockJuliaAttenuatedCompletedPacket_sq_le_completedCoherentEnergy
      hx L (ccmFirstClockAdmittedPrimePacket L),
    ccmFirstClockJulia_attenuatedCompletedPacket_sub_continuousBudget_sq_le_primeEnergy
      hx L (ccmFirstClockAdmittedPrimePacket L),
    fun hneg =>
      ccmFirstClockJulia_negative_attenuatedCompletedPacket_forces_badCoherentEnergy
        hx hL (ccmFirstClockAdmittedPrimePacket L)
          (ccmFirstClockAdmittedPrimePacket_le_cutoff L) hneg⟩

end

end RHTower
