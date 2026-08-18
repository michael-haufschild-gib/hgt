import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierHermitianIncidencePolarization

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-!
# Source-horizontal second-Cartier orbit coercivity

The incidence and Krein forms of the second-Cartier shell are invariant under reciprocal
hyperbolic transfer.  This file supplies the missing positive two-sided observable: it measures
the unit coordinate and the symmetric ghost coordinate independently.  Its exact orbit formula
shows that a nonzero polarized ghost has a bounded bilateral transfer orbit precisely when the
transfer character is unitary.

For the actual strict-right Xi character the norm is strictly smaller than one.  Consequently the
literal coefficient-faithful orbit energy diverges, and this conclusion survives the exact
support-fibre multiplicity sum.  Thus compact endpoint admission cannot be hidden in the existing
indefinite conservation law; it must be supplied by a genuinely new completed-source theorem.
-/

/-- Positive energy transverse to the conserved indefinite incidence form. -/
def sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
    (w : SourceHorizontalSecondCartierKreinJet) : ℝ :=
  ‖w.1‖ ^ 2 + ‖w.2.1 + w.2.2‖ ^ 2

/-- Forward orbit of the polarized unit-plus-ghost vector under a nonzero transfer character. -/
def sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
    (lam c : ℂ) (n : ℕ) : SourceHorizontalSecondCartierKreinJet :=
  sourceHorizontalSecondCartierKreinJetTransfer (lam ^ n)
    (sourceHorizontalSecondCartierKreinPolarizedGhost c)

/-- Exact reciprocal-hyperbolic energy decomposition. -/
theorem sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy
    (lam c : ℂ) (n : ℕ) :
    sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lam c n) =
      ‖lam‖ ^ (2 * n) + 4 * ‖c‖ ^ 2 * (‖lam‖⁻¹) ^ (2 * n) := by
  rw [sourceHorizontalSecondCartierKreinPositiveOrbitEnergy,
    sourceHorizontalSecondCartierKreinPolarizedGhostOrbit,
    sourceHorizontalSecondCartierKreinJetTransfer]
  rw [sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sum]
  simp only [sourceHorizontalSecondCartierKreinPolarizedGhost,
    sourceHorizontalSecondCartierKreinUnit,
    sourceHorizontalSecondCartierKreinGhost, Prod.fst_add, Prod.snd_add]
  simp only [norm_mul, norm_pow, norm_inv, norm_star]
  norm_num [pow_mul, mul_pow]
  rw [show c + c = c * 2 by ring, norm_mul]
  norm_num
  ring

/-- Literal two-sided endpoint radial energy: the source anchor is read in the negative Hardy
direction, while the coefficient-faithful physical ghost is read in the positive direction. -/
def sourceHorizontalSecondCartierLiteralEndpointRadialEnergy
    (lam c : ℂ) (n : ℕ) : ℝ :=
  ‖bilateralEigenFamily lam (-(n : ℤ))‖ ^ 2 +
    4 * ‖c * bilateralEigenFamily lam (n : ℤ)‖ ^ 2

/-- The positive Krein-orbit observable is exactly the literal two-sided Hardy endpoint energy;
no fitted comparison constant or asymptotic passage occurs. -/
theorem sourceHorizontalSecondCartierLiteralEndpointRadialEnergy_eq_positiveOrbitEnergy
    (lam c : ℂ) (n : ℕ) :
    sourceHorizontalSecondCartierLiteralEndpointRadialEnergy lam c n =
      sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lam c n) := by
  rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy]
  simp [sourceHorizontalSecondCartierLiteralEndpointRadialEnergy,
    bilateralEigenFamily, pow_mul]
  ring

/-- Uniform boundedness of the positive energy along the forward transfer orbit. -/
def SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded
    (lam c : ℂ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ,
    sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
      (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lam c n) ≤ C

/-- A nondegenerate reciprocal orbit is bounded exactly on the unitary locus. -/
theorem sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff
    {lam c : ℂ} (hlam : lam ≠ 0) (hc : c ≠ 0) :
    SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded lam c ↔ ‖lam‖ = 1 := by
  constructor
  · rintro ⟨C, hC⟩
    have hlamPos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
    rcases lt_trichotomy ‖lam‖ 1 with hlt | heq | hgt
    · have hinv : 1 < ‖lam‖⁻¹ := (one_lt_inv₀ hlamPos).2 hlt
      have hbase : 1 < (‖lam‖⁻¹) ^ 2 := by nlinarith
      have hpow : Tendsto (fun n : ℕ => (‖lam‖⁻¹) ^ (2 * n)) atTop atTop := by
        simpa [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt hbase
      have hcoef : 0 < 4 * ‖c‖ ^ 2 := by positivity
      have hlarge := (hpow.const_mul_atTop hcoef).eventually_gt_atTop C
      obtain ⟨n, hn⟩ := hlarge.exists
      have hnonneg : 0 ≤ ‖lam‖ ^ (2 * n) := by positivity
      have hbound := hC n
      rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy] at hbound
      linarith
    · exact heq
    · have hbase : 1 < ‖lam‖ ^ 2 := by nlinarith
      have hpow : Tendsto (fun n : ℕ => ‖lam‖ ^ (2 * n)) atTop atTop := by
        simpa [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt hbase
      obtain ⟨n, hn⟩ := (hpow.eventually_gt_atTop C).exists
      have hnonneg : 0 ≤ 4 * ‖c‖ ^ 2 * (‖lam‖⁻¹) ^ (2 * n) := by positivity
      have hbound := hC n
      rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy] at hbound
      linarith
  · intro hnorm
    refine ⟨1 + 4 * ‖c‖ ^ 2, fun n => ?_⟩
    rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy, hnorm]
    norm_num

/-- Exact topology bridge: positive radial orbit boundedness is the same unit-character condition
as physical moderation of the literal endpoint-scaled quadratic source ghost. -/
theorem sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff_endpointModerate
    {c₀ lam : ℂ} {N : ℕ}
    (hscale : sourceHorizontalWoldBVKreinGhostEnergy c₀ N ≠ 0)
    (hlam : lam ≠ 0) :
    SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded lam
        (sourceHorizontalWoldBVKreinGhostEnergy c₀ N : ℂ) ↔
      bilateralModerate
        (sourceHorizontalEndpointSecondJetHardyDescent c₀ N lam
          sourceHorizontalBilateralSecondJetGhost) := by
  rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff
      hlam (by exact_mod_cast hscale),
    sourceHorizontalEndpointSecondJetHardyDescent_ghost_moderate_iff hscale hlam]

/-- In the contracting chamber the reciprocal ghost leg forces energy to infinity. -/
theorem tendsto_sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy_atTop_of_norm_lt_one
    {lam c : ℂ} (hlam : lam ≠ 0) (hc : c ≠ 0) (hlt : ‖lam‖ < 1) :
    Tendsto (fun n : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
      (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit lam c n)) atTop atTop := by
  have hlamPos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hinv : 1 < ‖lam‖⁻¹ := (one_lt_inv₀ hlamPos).2 hlt
  have hbase : 1 < (‖lam‖⁻¹) ^ 2 := by nlinarith
  have hpow : Tendsto (fun n : ℕ => (‖lam‖⁻¹) ^ (2 * n)) atTop atTop := by
    simpa [pow_mul] using tendsto_pow_atTop_atTop_of_one_lt hbase
  have hcoef : 0 < 4 * ‖c‖ ^ 2 := by positivity
  have hsecond : Tendsto
      (fun n : ℕ => 4 * ‖c‖ ^ 2 * (‖lam‖⁻¹) ^ (2 * n)) atTop atTop :=
    hpow.const_mul_atTop hcoef
  rw [tendsto_atTop]
  intro C
  filter_upwards [hsecond.eventually_ge_atTop C] with n hn
  rw [sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy]
  exact hn.trans (le_add_of_nonneg_left (by positivity))

/-- Actual coefficient-faithful bounded-orbit assertion on one Xi divisor copy and one prime. -/
def SourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) : Prop :=
  SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded
    (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

/-- On the actual Xi fibre, the second positive radial square is literally the endpoint-scaled
Hardy ghost value with the same conormal coefficient, clock, divisor copy, and prime label. -/
theorem sourceHorizontalActualXiSecondCartierKreinOrbitEnergy_eq_literalEndpointEnergy
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) (n : ℕ) :
    sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
          (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n) =
      ‖bilateralEigenFamily
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) (-(n : ℤ))‖ ^ 2 +
        4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) (n : ℤ)‖ ^ 2 := by
  rw [← sourceHorizontalSecondCartierLiteralEndpointRadialEnergy_eq_positiveOrbitEnergy
    (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n]
  simp only [sourceHorizontalSecondCartierLiteralEndpointRadialEnergy]
  congr 2
  rw [sourceHorizontalActualXiEndpointSecondJetHardyDescent]
  change _ = ‖(sourceHorizontalWoldBVKreinGhostEnergy
      (sourceHorizontalActualXiConormalCoefficient x u q r) N : ℂ) *
        sourceHorizontalBilateralSecondJetHardyDescent
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
          sourceHorizontalBilateralSecondJetGhost (n : ℤ)‖ ^ 2
  rw [sourceHorizontalBilateralSecondJetHardyDescent_ghost]
  simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
    sourceHorizontalActualXiSecondCartierKreinScale, bilateralEigenFamily]

/-- Actual coefficient-faithful bridge: radial boundedness is neither weaker nor stronger than
physical moderation of the already-constructed literal endpoint descent. -/
theorem sourceHorizontalActualXiSecondCartierKreinOrbitBounded_iff_endpointModerate
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    SourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded x u q r N p ↔
      bilateralModerate
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) := by
  have hscaleC := sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
    q hkappa hr N hjet
  have hscale : sourceHorizontalWoldBVKreinGhostEnergy
      (sourceHorizontalActualXiConormalCoefficient x u q r) N ≠ 0 := by
    rw [sourceHorizontalActualXiSecondCartierKreinScale] at hscaleC
    exact_mod_cast hscaleC
  exact sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff_endpointModerate
    hscale (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p)

/-- Every occupied strict-right Xi fibre has an unbounded actual prime-character orbit. -/
theorem not_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    ¬ SourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded
      x u q r N p := by
  intro hbounded
  have hlam := sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p
  have hc := sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
    q hkappa hr N hjet
  have hnorm :=
    (sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff hlam hc).1 hbounded
  have hline := (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le
    (q.1.1 : XiDivisorSupport)).1 hnorm
  have hright : 1 / 2 < ((q.1.1 : XiDivisorSupport) : ℂ).re := by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith
  exact (ne_of_gt hright) hline

/-- The same reciprocal escape is visible directly in the literal coefficient-faithful endpoint:
its Stokes-flat Hardy ghost is not a compact-circle distribution on any strict-right Xi fibre. -/
theorem not_bilateralModerate_sourceHorizontalActualXiEndpointSecondJetHardyDescent_ghost
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    ¬ bilateralModerate
      (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
        sourceHorizontalBilateralSecondJetGhost) := by
  intro hmoderate
  exact not_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded
    q hkappa hr N hjet p
    ((sourceHorizontalActualXiSecondCartierKreinOrbitBounded_iff_endpointModerate
      q hkappa hr N hjet p).2 hmoderate)

/-- Quantitative actual-fibre coercivity: the positive orbit energy diverges to infinity. -/
theorem tendsto_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbit_energy_atTop
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    Tendsto (fun n : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
      (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
        (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
        (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n))
      atTop atTop := by
  have hlam := sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p
  have hc := sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
    q hkappa hr N hjet
  apply
    tendsto_sourceHorizontalSecondCartierKreinPolarizedGhostOrbit_energy_atTop_of_norm_lt_one
      hlam hc
  rw [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
    norm_bilateralHalfDensityCharacter (by exact_mod_cast p.2.pos)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith)

/-- Simultaneous actual boundedness over every strict-right Xi divisor copy. -/
def EverySourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded
    (x u r : ℝ) (N : ℕ) (p : Nat.Primes) : Prop :=
  ∀ q : XiRightZeroCopy,
    SourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded x u q r N p

/-- Exact firewall: universal actual orbit boundedness is equivalent to RH, not an available
consequence of the existing indefinite conservation laws. -/
theorem everySourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded_iff_rh
    {x u r : ℝ}
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    EverySourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded x u r N p ↔
      RiemannHypothesis := by
  constructor
  · intro hbounded
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    exact not_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded
      q hkappa hr N hjet p (hbounded q)
  · intro hRH q
    haveI : IsEmpty XiRightZeroCopy := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
    exact isEmptyElim q

/-- Coercivity and divisor multiplicity survive together on the literal actual Xi fibre. -/
theorem sourceHorizontalActualXiSecondCartierKreinOrbitCoercivity_capstone
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    Tendsto (fun n : ℕ => sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
      (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
        (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
        (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n)) atTop atTop ∧
      ¬ bilateralModerate
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N p
          sourceHorizontalBilateralSecondJetGhost) ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u s.1 r N) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
  exact ⟨
    tendsto_sourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbit_energy_atTop
      q hkappa hr N hjet p,
    not_bilateralModerate_sourceHorizontalActualXiEndpointSecondJetHardyDescent_ghost
      q hkappa hr N hjet p,
    sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_fiber_sum x u q r N⟩

end

end RHTower
