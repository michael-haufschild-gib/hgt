import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability
import GaloisForLFunctions.RHTower.GibbsAntiscaleDeterminantOddCube
import GaloisForLFunctions.RHTower.GibbsParityVortex

/-!
# Route E source-faithful Euler tilt and unit-shell algebra

This module certifies the finite identities behind Route E's source-faithful change of measure.
The literal squarefree Gibbs current is rewritten as a Bernoulli Euler expectation without changing
its physical multiplier.  The multiplier has an exact aperture-independent unit-log-shell profile,
weighted parity--energy regression has a strict Schur-complement law on transverse packets, and the
complete parity--energy characteristic function factors as a finite Euler product.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Logarithmic energy of one occupied prime subset. -/
def routeEPrimeLogEnergy (T : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ T, Real.log (p : ℕ)

/-- Euler normalizer for the `p^{-σ}` Bernoulli tilt. -/
def routeEEulerTiltNormalizer (sigma : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P, (1 + (p : ℝ) ^ (-sigma))

/-- Product Bernoulli weight of one occupied subset. -/
def routeEEulerTiltOccupancyWeight
    (sigma : ℝ) (P T : Finset Nat.Primes) : ℝ :=
  finiteActivationOccupancyWeight
    (fun p : Nat.Primes => (p : ℝ) ^ (-sigma)) P T

/-- Source-faithful physical multiplier after Euler tilting. -/
def routeEPhysicalTiltWeight (sigma x E : ℝ) : ℝ :=
  Real.exp (sigma * E - x * Real.exp E)

/-- Literal finite squarefree exponential Gibbs partition. -/
def routeESquarefreeGibbsPartition (P : Finset Nat.Primes) (x : ℝ) : ℝ :=
  ∑ T ∈ P.powerset,
    Real.exp (-x * (finitePrimeActivationRadical T : ℝ))

/-- Literal finite alternating squarefree exponential Gibbs current. -/
def routeESquarefreeGibbsCurrent (P : Finset Nat.Primes) (x : ℝ) : ℝ :=
  ∑ T ∈ P.powerset,
    (-1 : ℝ) ^ T.card *
      Real.exp (-x * (finitePrimeActivationRadical T : ℝ))

/-- Normalized literal finite Gibbs current. -/
def routeESquarefreeNormalizedGibbsCurrent
    (P : Finset Nat.Primes) (x : ℝ) : ℝ :=
  routeESquarefreeGibbsCurrent P x / routeESquarefreeGibbsPartition P x

theorem routeEFinitePrimeActivationRadical_pos (T : Finset Nat.Primes) :
    0 < finitePrimeActivationRadical T := by
  unfold finitePrimeActivationRadical
  exact Finset.prod_pos fun p hp => p.2.pos

/-- Energy exponent is exactly represented prime radical. -/
theorem routeE_exp_logEnergy_eq_radical (T : Finset Nat.Primes) :
    Real.exp (routeEPrimeLogEnergy T) = finitePrimeActivationRadical T := by
  rw [routeEPrimeLogEnergy, Real.exp_sum, finitePrimeActivationRadical, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  exact Real.exp_log (by exact_mod_cast p.2.pos)

theorem routeEEulerTiltNormalizer_pos (sigma : ℝ) (P : Finset Nat.Primes) :
    0 < routeEEulerTiltNormalizer sigma P := by
  unfold routeEEulerTiltNormalizer
  exact Finset.prod_pos fun p hp => by
    have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    have hpow := Real.rpow_pos_of_pos hpR (-sigma)
    linarith

/-- Exact source equality for one occupied subset, with validity encoded by subtype. -/
theorem routeEEulerTiltTerm_eq_gibbsTerm
    (sigma x : ℝ) (P : Finset Nat.Primes)
    (T : {T : Finset Nat.Primes // T ⊆ P}) :
    routeEEulerTiltNormalizer sigma P *
        routeEEulerTiltOccupancyWeight sigma P T *
          routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T) =
      Real.exp (-x * (finitePrimeActivationRadical T : ℝ)) := by
  let m : ℝ := finitePrimeActivationRadical T
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast routeEFinitePrimeActivationRadical_pos T
  have hdenpos := routeEEulerTiltNormalizer_pos sigma P
  have hweight :
      routeEEulerTiltOccupancyWeight sigma P T =
        m ^ (-sigma) / routeEEulerTiltNormalizer sigma P := by
    simpa [routeEEulerTiltOccupancyWeight, routeEEulerTiltNormalizer, m] using
      finitePrimeActivationOccupancyWeight_eq_gibbs sigma P T T.property
  have henergy : Real.exp (routeEPrimeLogEnergy T) = m := by
    simpa [m] using routeE_exp_logEnergy_eq_radical T
  have hsigma :
      Real.exp (sigma * routeEPrimeLogEnergy T) = m ^ sigma := by
    rw [Real.rpow_def_of_pos hmpos]
    congr 1
    have hlog : Real.log m = routeEPrimeLogEnergy T := by
      apply Real.exp_injective
      rw [Real.exp_log hmpos, henergy]
    rw [hlog]
    ring
  rw [hweight, routeEPhysicalTiltWeight, sub_eq_add_neg, Real.exp_add, hsigma, henergy,
    Real.rpow_neg hmpos.le]
  field_simp [hdenpos.ne', (Real.rpow_pos_of_pos hmpos sigma).ne']
  simp [m]

/-- Literal finite Gibbs partition is exactly the Euler-Bernoulli expectation of physical tilt. -/
theorem routeESquarefreeGibbsPartition_eq_eulerTilt
    (sigma x : ℝ) (P : Finset Nat.Primes) :
    routeESquarefreeGibbsPartition P x =
      routeEEulerTiltNormalizer sigma P *
        ∑ T ∈ P.powerset,
          routeEEulerTiltOccupancyWeight sigma P T *
            routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T) := by
  rw [routeESquarefreeGibbsPartition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simpa [mul_assoc] using (routeEEulerTiltTerm_eq_gibbsTerm sigma x P
    ⟨T, Finset.mem_powerset.mp hT⟩).symm

/-- Literal finite Gibbs current is exactly the signed Euler-Bernoulli expectation. -/
theorem routeESquarefreeGibbsCurrent_eq_eulerTilt
    (sigma x : ℝ) (P : Finset Nat.Primes) :
    routeESquarefreeGibbsCurrent P x =
      routeEEulerTiltNormalizer sigma P *
        ∑ T ∈ P.powerset,
          (-1 : ℝ) ^ T.card *
            routeEEulerTiltOccupancyWeight sigma P T *
              routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T) := by
  rw [routeESquarefreeGibbsCurrent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show routeEEulerTiltNormalizer sigma P *
        ((-1 : ℝ) ^ T.card * routeEEulerTiltOccupancyWeight sigma P T *
          routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T)) =
      (-1 : ℝ) ^ T.card *
        (routeEEulerTiltNormalizer sigma P *
          routeEEulerTiltOccupancyWeight sigma P T *
            routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T)) by ring]
  rw [routeEEulerTiltTerm_eq_gibbsTerm sigma x P
    ⟨T, Finset.mem_powerset.mp hT⟩]

theorem routeESquarefreeGibbsPartition_pos
    (P : Finset Nat.Primes) (x : ℝ) :
    0 < routeESquarefreeGibbsPartition P x := by
  unfold routeESquarefreeGibbsPartition
  apply Finset.sum_pos'
  · intro T hT
    exact (Real.exp_pos _).le
  · exact ⟨∅, Finset.empty_mem_powerset P, Real.exp_pos _⟩

/-- Exact normalized source-faithful tilt identity. -/
theorem routeESquarefreeNormalizedGibbsCurrent_eq_eulerTilt
    (sigma x : ℝ) (P : Finset Nat.Primes) :
    routeESquarefreeNormalizedGibbsCurrent P x =
      (∑ T ∈ P.powerset,
          (-1 : ℝ) ^ T.card *
            routeEEulerTiltOccupancyWeight sigma P T *
              routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T)) /
        (∑ T ∈ P.powerset,
          routeEEulerTiltOccupancyWeight sigma P T *
            routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T)) := by
  rw [routeESquarefreeNormalizedGibbsCurrent,
    routeESquarefreeGibbsCurrent_eq_eulerTilt,
    routeESquarefreeGibbsPartition_eq_eulerTilt]
  field_simp [routeEEulerTiltNormalizer_pos sigma P |>.ne']

/-- Positive physical coupling, encoding validity without theorem premises. -/
structure RouteEPositiveTiltCoupling where
  sigma : ℝ
  x : ℝ
  sigma_pos : 0 < sigma
  x_pos : 0 < x

/-- Unique logarithmic center of source-faithful physical multiplier. -/
def RouteEPositiveTiltCoupling.center (c : RouteEPositiveTiltCoupling) : ℝ :=
  Real.log (c.sigma / c.x)

/-- Exact aperture-independent unit-log-shell profile. -/
theorem routeEPhysicalTiltWeight_centeredProfile
    (c : RouteEPositiveTiltCoupling) (u : ℝ) :
    routeEPhysicalTiltWeight c.sigma c.x (c.center + u) /
        routeEPhysicalTiltWeight c.sigma c.x c.center =
      Real.exp (c.sigma * (u + 1 - Real.exp u)) := by
  have hratio : 0 < c.sigma / c.x := div_pos c.sigma_pos c.x_pos
  have hcenter : Real.exp c.center = c.sigma / c.x := by
    exact Real.exp_log hratio
  have hx : c.x ≠ 0 := c.x_pos.ne'
  unfold routeEPhysicalTiltWeight
  apply (div_eq_iff (Real.exp_ne_zero _)).2
  rw [← Real.exp_add]
  apply congrArg Real.exp
  rw [Real.exp_add, hcenter]
  field_simp [hx]
  ring

/-- Physical multiplier has global maximum at its exact log-energy center. -/
theorem routeEPhysicalTiltWeight_le_center
    (c : RouteEPositiveTiltCoupling) (E : ℝ) :
    routeEPhysicalTiltWeight c.sigma c.x E ≤
      routeEPhysicalTiltWeight c.sigma c.x c.center := by
  let u := E - c.center
  have hprofile := routeEPhysicalTiltWeight_centeredProfile c u
  have hE : c.center + u = E := by simp [u]
  rw [hE] at hprofile
  have hphase : c.sigma * (u + 1 - Real.exp u) ≤ 0 := by
    have hexp := Real.add_one_le_exp u
    nlinarith [c.sigma_pos]
  have hratio : Real.exp (c.sigma * (u + 1 - Real.exp u)) ≤ 1 :=
    Real.exp_le_one_iff.mpr hphase
  have hcenterpos : 0 < routeEPhysicalTiltWeight c.sigma c.x c.center :=
    Real.exp_pos _
  rw [div_eq_iff hcenterpos.ne'] at hprofile
  rw [hprofile]
  exact mul_le_of_le_one_left hcenterpos.le hratio

/-- Physical multiplier has no second maximizer. -/
theorem routeEPhysicalTiltWeight_lt_center_of_ne
    (c : RouteEPositiveTiltCoupling) {E : ℝ} (hE : E ≠ c.center) :
    routeEPhysicalTiltWeight c.sigma c.x E <
      routeEPhysicalTiltWeight c.sigma c.x c.center := by
  let u := E - c.center
  have hu : u ≠ 0 := sub_ne_zero.mpr hE
  have hprofile := routeEPhysicalTiltWeight_centeredProfile c u
  have hEc : c.center + u = E := by simp [u]
  rw [hEc] at hprofile
  have hphase : c.sigma * (u + 1 - Real.exp u) < 0 := by
    have hexp := Real.add_one_lt_exp hu
    nlinarith [c.sigma_pos]
  have hratio : Real.exp (c.sigma * (u + 1 - Real.exp u)) < 1 :=
    Real.exp_lt_one_iff.mpr hphase
  have hcenterpos : 0 < routeEPhysicalTiltWeight c.sigma c.x c.center :=
    Real.exp_pos _
  rw [div_eq_iff hcenterpos.ne'] at hprofile
  rw [hprofile]
  exact mul_lt_of_lt_one_left hcenterpos hratio

/-! ## Exact parity--energy regression algebra -/

/-- Weighted occupancy mass. -/
def routeEParityEnergyMass
    {ι : Type*} (P : Finset ι) (weight : ι → ℝ) : ℝ :=
  ∑ i ∈ P, weight i

/-- Weighted parity--energy covariance coordinate. -/
def routeEParityEnergyFirstMoment
    {ι : Type*} (P : Finset ι) (weight energy : ι → ℝ) : ℝ :=
  ∑ i ∈ P, weight i * energy i

/-- Weighted energy variance coordinate. -/
def routeEParityEnergySecondMoment
    {ι : Type*} (P : Finset ι) (weight energy : ι → ℝ) : ℝ :=
  ∑ i ∈ P, weight i * energy i ^ 2

/-- Exact quadratic parity phase after energy correction. -/
def routeEParityEnergyQuadratic
    {ι : Type*} (P : Finset ι) (weight energy : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ P, weight i * (Real.pi - t * energy i) ^ 2

/-- Schur-complement numerator, avoiding division and any nondegeneracy premise. -/
def routeEParityEnergyResidualNumerator
    {ι : Type*} (P : Finset ι) (weight energy : ι → ℝ) : ℝ :=
  Real.pi ^ 2 *
    (routeEParityEnergyMass P weight *
        routeEParityEnergySecondMoment P weight energy -
      routeEParityEnergyFirstMoment P weight energy ^ 2)

private theorem routeEParityEnergyQuadratic_expansion
    {ι : Type*} (P : Finset ι) (weight energy : ι → ℝ) (t : ℝ) :
    routeEParityEnergyQuadratic P weight energy t =
      Real.pi ^ 2 * routeEParityEnergyMass P weight -
        2 * Real.pi * t * routeEParityEnergyFirstMoment P weight energy +
          t ^ 2 * routeEParityEnergySecondMoment P weight energy := by
  unfold routeEParityEnergyQuadratic routeEParityEnergyMass
    routeEParityEnergyFirstMoment routeEParityEnergySecondMoment
  calc
    (∑ i ∈ P, weight i * (Real.pi - t * energy i) ^ 2) =
        ∑ i ∈ P,
          (Real.pi ^ 2 * weight i -
            2 * Real.pi * t * (weight i * energy i) +
              t ^ 2 * (weight i * energy i ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = Real.pi ^ 2 * (∑ i ∈ P, weight i) -
          2 * Real.pi * t * (∑ i ∈ P, weight i * energy i) +
            t ^ 2 * (∑ i ∈ P, weight i * energy i ^ 2) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]

/-- Denominator-free regression identity, valid for every finite weighted packet. -/
theorem routeEParityEnergyRegression_denominatorFree
    {ι : Type*} (P : Finset ι) (weight energy : ι → ℝ) (t : ℝ) :
    routeEParityEnergySecondMoment P weight energy *
        routeEParityEnergyQuadratic P weight energy t =
      routeEParityEnergyResidualNumerator P weight energy +
        (routeEParityEnergySecondMoment P weight energy * t -
          Real.pi * routeEParityEnergyFirstMoment P weight energy) ^ 2 := by
  rw [routeEParityEnergyQuadratic_expansion]
  unfold routeEParityEnergyResidualNumerator
  ring

/-- Pairwise representation of weighted Schur-complement numerator. -/
theorem routeEParityEnergy_pairwiseGap
    {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (weight energy : ι → ℝ) :
    (∑ i ∈ P, ∑ j ∈ P,
        weight i * weight j * (energy i - energy j) ^ 2) =
      2 * (routeEParityEnergyMass P weight *
          routeEParityEnergySecondMoment P weight energy -
        routeEParityEnergyFirstMoment P weight energy ^ 2) := by
  unfold routeEParityEnergyMass routeEParityEnergyFirstMoment
    routeEParityEnergySecondMoment
  rw [show (∑ i ∈ P, ∑ j ∈ P,
      weight i * weight j * (energy i - energy j) ^ 2) =
      ∑ i ∈ P, ∑ j ∈ P,
        (weight i * weight j * energy i ^ 2 -
          2 * (weight i * weight j * energy i * energy j) +
            weight i * weight j * energy j ^ 2) by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hdiag1 :
      (∑ i ∈ P, ∑ j ∈ P, weight i * weight j * energy i ^ 2) =
        (∑ i ∈ P, weight i) *
          (∑ i ∈ P, weight i * energy i ^ 2) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdiag2 :
      (∑ i ∈ P, ∑ j ∈ P, weight i * weight j * energy j ^ 2) =
        (∑ i ∈ P, weight i) *
          (∑ i ∈ P, weight i * energy i ^ 2) := by
    calc
      (∑ i ∈ P, ∑ j ∈ P, weight i * weight j * energy j ^ 2) =
          ∑ j ∈ P, ∑ i ∈ P, weight j * weight i * energy j ^ 2 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ P, weight i) *
          (∑ i ∈ P, weight i * energy i ^ 2) := hdiag1
  have hcross :
      (∑ i ∈ P, ∑ j ∈ P,
        weight i * weight j * energy i * energy j) =
        (∑ i ∈ P, weight i * energy i) ^ 2 := by
    rw [sq]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcross2 :
      (∑ i ∈ P, ∑ j ∈ P,
        2 * (weight i * weight j * energy i * energy j)) =
        2 * (∑ i ∈ P, weight i * energy i) ^ 2 := by
    calc
      (∑ i ∈ P, ∑ j ∈ P,
          2 * (weight i * weight j * energy i * energy j)) =
          2 * (∑ i ∈ P, ∑ j ∈ P,
            weight i * weight j * energy i * energy j) := by
              simp only [Finset.mul_sum]
      _ = 2 * (∑ i ∈ P, weight i * energy i) ^ 2 := by rw [hcross]
  rw [hdiag1, hdiag2, hcross2]
  ring

/-- A finite packet whose type carries every validity condition for strict transversality. -/
structure RouteETransverseParityEnergyPacket (ι : Type*) [DecidableEq ι] where
  support : Finset ι
  weight : ι → ℝ
  energy : ι → ℝ
  weight_pos : ∀ i ∈ support, 0 < weight i
  transverse : ∃ i ∈ support, ∃ j ∈ support, energy i ≠ energy j

namespace RouteETransverseParityEnergyPacket

variable {ι : Type*} [DecidableEq ι]

/-- Every valid transverse packet has positive energy second moment. -/
theorem secondMoment_pos (packet : RouteETransverseParityEnergyPacket ι) :
    0 < routeEParityEnergySecondMoment
      packet.support packet.weight packet.energy := by
  obtain ⟨i, hi, j, hj, hij⟩ := packet.transverse
  have hnonzero : packet.energy i ≠ 0 ∨ packet.energy j ≠ 0 := by
    by_contra h
    push Not at h
    exact hij (h.1.trans h.2.symm)
  rcases hnonzero with hi0 | hj0
  · apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (packet.weight_pos k hk).le (sq_nonneg _)
    · exact ⟨i, hi, mul_pos (packet.weight_pos i hi) (sq_pos_of_ne_zero hi0)⟩
  · apply Finset.sum_pos'
    · intro k hk
      exact mul_nonneg (packet.weight_pos k hk).le (sq_nonneg _)
    · exact ⟨j, hj, mul_pos (packet.weight_pos j hj) (sq_pos_of_ne_zero hj0)⟩

/-- Strict parity--energy Schur complement from an actual transverse pair. -/
theorem schurComplement_pos (packet : RouteETransverseParityEnergyPacket ι) :
    0 < routeEParityEnergyMass packet.support packet.weight *
          routeEParityEnergySecondMoment packet.support packet.weight packet.energy -
        routeEParityEnergyFirstMoment packet.support packet.weight packet.energy ^ 2 := by
  obtain ⟨i, hi, j, hj, hij⟩ := packet.transverse
  have hpair :
      0 < packet.weight i * packet.weight j *
        (packet.energy i - packet.energy j) ^ 2 := by
    exact mul_pos (mul_pos (packet.weight_pos i hi) (packet.weight_pos j hj))
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hij))
  have hsumpos :
      0 < ∑ a ∈ packet.support, ∑ b ∈ packet.support,
        packet.weight a * packet.weight b *
          (packet.energy a - packet.energy b) ^ 2 := by
    apply Finset.sum_pos'
    · intro a ha
      exact Finset.sum_nonneg fun b hb =>
        mul_nonneg (mul_nonneg (packet.weight_pos a ha).le
          (packet.weight_pos b hb).le) (sq_nonneg _)
    · refine ⟨i, hi, ?_⟩
      apply Finset.sum_pos'
      · intro b hb
        exact mul_nonneg (mul_nonneg (packet.weight_pos i hi).le
          (packet.weight_pos b hb).le) (sq_nonneg _)
      · exact ⟨j, hj, hpair⟩
  rw [routeEParityEnergy_pairwiseGap] at hsumpos
  linarith

/-- Exact regression minimizer, now denominator is internally certified positive. -/
def regressionFrequency (packet : RouteETransverseParityEnergyPacket ι) : ℝ :=
  Real.pi * routeEParityEnergyFirstMoment packet.support packet.weight packet.energy /
    routeEParityEnergySecondMoment packet.support packet.weight packet.energy

/-- Exact Schur-complement residual at regression frequency. -/
theorem quadratic_regressionFrequency
    (packet : RouteETransverseParityEnergyPacket ι) :
    routeEParityEnergyQuadratic packet.support packet.weight packet.energy
        packet.regressionFrequency =
      Real.pi ^ 2 *
        (routeEParityEnergyMass packet.support packet.weight -
          routeEParityEnergyFirstMoment packet.support packet.weight packet.energy ^ 2 /
            routeEParityEnergySecondMoment packet.support packet.weight packet.energy) := by
  have hC := packet.secondMoment_pos
  rw [routeEParityEnergyQuadratic_expansion]
  unfold regressionFrequency
  field_simp [hC.ne']
  ring

/-- Exact Pythagorean regression law with unique correction coordinate. -/
theorem quadratic_eq_residual_add_centering
    (packet : RouteETransverseParityEnergyPacket ι) (t : ℝ) :
    routeEParityEnergyQuadratic packet.support packet.weight packet.energy t =
      routeEParityEnergyQuadratic packet.support packet.weight packet.energy
          packet.regressionFrequency +
        routeEParityEnergySecondMoment packet.support packet.weight packet.energy *
          (t - packet.regressionFrequency) ^ 2 := by
  rw [packet.quadratic_regressionFrequency,
    routeEParityEnergyQuadratic_expansion]
  have hC := packet.secondMoment_pos
  unfold regressionFrequency
  field_simp [hC.ne']
  ring

end RouteETransverseParityEnergyPacket

/-! ## Exact all-cumulant Boolean Euler product -/

/-- Local parity--energy Fourier coordinate. -/
def routeEParityEnergyLocalCoordinate
    (sigma t : ℝ) (p : Nat.Primes) : ℂ :=
  Complex.ofReal ((p : ℝ) ^ (-sigma)) *
    Complex.exp (-(t * Real.log (p : ℕ) : ℝ) * Complex.I)

/-- Exact complete finite Euler product of parity--energy phases. -/
def routeEParityEnergyEulerProduct
    (sigma t : ℝ) (P : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ P,
    (1 - routeEParityEnergyLocalCoordinate sigma t p) /
      (1 + Complex.ofReal ((p : ℝ) ^ (-sigma)))

/-- Exact normalized Bernoulli parity--energy Fourier sum. -/
def routeEParityEnergyFourierSum
    (sigma t : ℝ) (P : Finset Nat.Primes) : ℂ :=
  ∑ T ∈ P.powerset,
    (routeEEulerTiltOccupancyWeight sigma P T : ℂ) *
      (-1 : ℂ) ^ T.card *
        Complex.exp (-(t * routeEPrimeLogEnergy T : ℝ) * Complex.I)

private theorem routeEParityEnergySubsetProduct
    (sigma t : ℝ) (T : Finset Nat.Primes) :
    (∏ p ∈ T, -routeEParityEnergyLocalCoordinate sigma t p) =
      Complex.ofReal ((finitePrimeActivationRadical T : ℝ) ^ (-sigma)) *
        (-1 : ℂ) ^ T.card *
          Complex.exp (-(t * routeEPrimeLogEnergy T : ℝ) * Complex.I) := by
  rw [Finset.prod_neg]
  simp only [routeEParityEnergyLocalCoordinate, Finset.prod_mul_distrib]
  have hrpow :
      ∏ p ∈ T, (p : ℝ) ^ (-sigma) =
        (finitePrimeActivationRadical T : ℝ) ^ (-sigma) := by
    rw [finitePrimeActivationRadical, Nat.cast_prod]
    exact Real.finsetProd_rpow T (fun p : Nat.Primes => (p : ℝ))
      (fun p hp => by exact_mod_cast p.2.pos.le) (-sigma)
  have hcrpow :
      (∏ p ∈ T, Complex.ofReal ((p : ℝ) ^ (-sigma))) =
        Complex.ofReal ((finitePrimeActivationRadical T : ℝ) ^ (-sigma)) := by
    rw [← Complex.ofReal_prod, hrpow]
  have hexp :
      (∏ p ∈ T,
        Complex.exp (-(t * Real.log (p : ℕ) : ℝ) * Complex.I)) =
          Complex.exp (-(t * routeEPrimeLogEnergy T : ℝ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    unfold routeEPrimeLogEnergy
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
  rw [hcrpow, hexp]
  ring

/-- Complete finite Bernoulli characteristic is exactly its normalized Euler product. -/
theorem routeEParityEnergyFourierSum_eq_eulerProduct
    (sigma t : ℝ) (P : Finset Nat.Primes) :
    routeEParityEnergyFourierSum sigma t P =
      routeEParityEnergyEulerProduct sigma t P := by
  let D : ℝ := routeEEulerTiltNormalizer sigma P
  have hDpos : 0 < D := routeEEulerTiltNormalizer_pos sigma P
  have hsum :
      (D : ℂ) * routeEParityEnergyFourierSum sigma t P =
        ∏ p ∈ P, (1 - routeEParityEnergyLocalCoordinate sigma t p) := by
    rw [routeEParityEnergyFourierSum, Finset.mul_sum]
    calc
      ∑ T ∈ P.powerset,
          (D : ℂ) *
            ((routeEEulerTiltOccupancyWeight sigma P T : ℂ) *
              (-1 : ℂ) ^ T.card *
                Complex.exp (-(t * routeEPrimeLogEnergy T : ℝ) * Complex.I)) =
        ∑ T ∈ P.powerset,
          ∏ p ∈ T, -routeEParityEnergyLocalCoordinate sigma t p := by
            apply Finset.sum_congr rfl
            intro T hT
            rw [routeEParityEnergySubsetProduct]
            have hw := finitePrimeActivationOccupancyWeight_eq_gibbs
              sigma P T (Finset.mem_powerset.mp hT)
            change routeEEulerTiltOccupancyWeight sigma P T =
              (finitePrimeActivationRadical T : ℝ) ^ (-sigma) / D at hw
            rw [hw]
            let R : ℝ := (finitePrimeActivationRadical T : ℝ) ^ (-sigma)
            have hcancel : D * (R / D) = R := by
              field_simp [hDpos.ne']
            have hcancelC :
                (D : ℂ) * Complex.ofReal (R / D) = Complex.ofReal R := by
              rw [← Complex.ofReal_mul, hcancel]
            change (D : ℂ) *
                (Complex.ofReal (R / D) * (-1 : ℂ) ^ T.card *
                  Complex.exp (-(t * routeEPrimeLogEnergy T : ℝ) * Complex.I)) =
              Complex.ofReal R * (-1 : ℂ) ^ T.card *
                Complex.exp (-(t * routeEPrimeLogEnergy T : ℝ) * Complex.I)
            calc
              _ = ((D : ℂ) * Complex.ofReal (R / D)) *
                    (-1 : ℂ) ^ T.card *
                      Complex.exp (-(t * routeEPrimeLogEnergy T : ℝ) *
                        Complex.I) := by ring
              _ = _ := by rw [hcancelC]
      _ = ∏ p ∈ P, (1 - routeEParityEnergyLocalCoordinate sigma t p) := by
        simpa [sub_eq_add_neg] using
          (Finset.prod_one_add
            (R := ℂ) (f := fun p : Nat.Primes =>
              -routeEParityEnergyLocalCoordinate sigma t p) P).symm
  rw [routeEParityEnergyEulerProduct]
  rw [Finset.prod_div_distrib]
  have hden :
      ∏ p ∈ P, (1 + Complex.ofReal ((p : ℝ) ^ (-sigma))) = (D : ℂ) := by
    push_cast [D, routeEEulerTiltNormalizer]
    rfl
  rw [hden]
  apply (eq_div_iff (by exact_mod_cast hDpos.ne')).2
  simpa [mul_comm] using hsum

/-! ## Exact Euler-gauge cancellation for arbitrary observables -/

/-- Normalized Euler-tilted expectation of an arbitrary predeclared finite observable. -/
def routeEEulerTiltObservableMean
    (sigma x : ℝ) (P : Finset Nat.Primes) (F : Finset Nat.Primes → ℝ) : ℝ :=
  (∑ T ∈ P.powerset,
      routeEEulerTiltOccupancyWeight sigma P T *
        routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T) * F T) /
    (∑ T ∈ P.powerset,
      routeEEulerTiltOccupancyWeight sigma P T *
        routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T))

/-- Normalized literal Gibbs expectation of the same observable. -/
def routeESquarefreeGibbsObservableMean
    (x : ℝ) (P : Finset Nat.Primes) (F : Finset Nat.Primes → ℝ) : ℝ :=
  (∑ T ∈ P.powerset,
      Real.exp (-x * (finitePrimeActivationRadical T : ℝ)) * F T) /
    routeESquarefreeGibbsPartition P x

/-- Atomwise Euler-gauge cancellation survives multiplication by every predeclared observable. -/
theorem routeEEulerTiltObservableSum_eq_gibbsSum
    (sigma x : ℝ) (P : Finset Nat.Primes) (F : Finset Nat.Primes → ℝ) :
    routeEEulerTiltNormalizer sigma P *
        (∑ T ∈ P.powerset,
          routeEEulerTiltOccupancyWeight sigma P T *
            routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T) * F T) =
      ∑ T ∈ P.powerset,
        Real.exp (-x * (finitePrimeActivationRadical T : ℝ)) * F T := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  calc
    routeEEulerTiltNormalizer sigma P *
          (routeEEulerTiltOccupancyWeight sigma P T *
            routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T) * F T) =
        (routeEEulerTiltNormalizer sigma P *
          routeEEulerTiltOccupancyWeight sigma P T *
            routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T)) * F T := by ring
    _ = Real.exp (-x * (finitePrimeActivationRadical T : ℝ)) * F T := by
      rw [routeEEulerTiltTerm_eq_gibbsTerm sigma x P
        ⟨T, Finset.mem_powerset.mp hT⟩]

/-- **Exact arbitrary-observable gauge law.** The moving Euler parameter locates mass but cannot
change any normalized observable formed from the literal physical Gibbs atoms. -/
theorem routeEEulerTiltObservableMean_eq_gibbsObservableMean
    (sigma x : ℝ) (P : Finset Nat.Primes) (F : Finset Nat.Primes → ℝ) :
    routeEEulerTiltObservableMean sigma x P F =
      routeESquarefreeGibbsObservableMean x P F := by
  let A := ∑ T ∈ P.powerset,
    routeEEulerTiltOccupancyWeight sigma P T *
      routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T) * F T
  let B := ∑ T ∈ P.powerset,
    routeEEulerTiltOccupancyWeight sigma P T *
      routeEPhysicalTiltWeight sigma x (routeEPrimeLogEnergy T)
  let C := ∑ T ∈ P.powerset,
    Real.exp (-x * (finitePrimeActivationRadical T : ℝ)) * F T
  let D := routeESquarefreeGibbsPartition P x
  have hnum : routeEEulerTiltNormalizer sigma P * A = C := by
    simpa [A, C] using routeEEulerTiltObservableSum_eq_gibbsSum sigma x P F
  have hden : D = routeEEulerTiltNormalizer sigma P * B := by
    simpa [D, B] using routeESquarefreeGibbsPartition_eq_eulerTilt sigma x P
  have hD : D ≠ 0 := (routeESquarefreeGibbsPartition_pos P x).ne'
  have hB : B ≠ 0 := by
    intro h
    rw [h, mul_zero] at hden
    exact hD hden
  change A / B = C / D
  apply (div_eq_div_iff hB hD).2
  rw [hden]
  calc
    A * (routeEEulerTiltNormalizer sigma P * B) =
        (routeEEulerTiltNormalizer sigma P * A) * B := by ring
    _ = C * B := by rw [hnum]

/-! ## Sharp local physical matching receiver -/

/-- Exponential form of the real hyperbolic tangent. -/
private lemma routeETanh_eq_expTwoRatio (y : ℝ) :
    Real.tanh y = (Real.exp (2 * y) - 1) / (Real.exp (2 * y) + 1) := by
  rw [Real.tanh_eq, show Real.exp (2 * y) = Real.exp y * Real.exp y by
    rw [show 2 * y = y + y by ring, Real.exp_add], Real.exp_neg]
  have hden : Real.exp y ^ 2 + 1 ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero y, hden]

/-- Monotonicity of `tanh`, supplied here in the exact algebraic form used by the receiver. -/
private lemma routeETanh_mono {a b : ℝ} (hab : a ≤ b) : Real.tanh a ≤ Real.tanh b := by
  rw [routeETanh_eq_expTwoRatio a, routeETanh_eq_expTwoRatio b]
  apply (div_le_div_iff₀ (by positivity : 0 < Real.exp (2 * a) + 1)
    (by positivity : 0 < Real.exp (2 * b) + 1)).2
  have hexp : Real.exp (2 * a) ≤ Real.exp (2 * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab (by norm_num))
  nlinarith

/-- The sharp elementary estimate `tanh y ≤ y` on the physical half-line. -/
private lemma routeETanh_le_self_of_nonneg (y : ℝ) (hy : 0 ≤ y) :
    Real.tanh y ≤ y := by
  have hx : 0 ≤ Real.exp (2 * y) - 1 := by
    rw [sub_nonneg]
    exact Real.one_le_exp (by positivity : 0 ≤ 2 * y)
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hone : 1 + (Real.exp (2 * y) - 1) = Real.exp (2 * y) := by ring
  rw [hone, Real.log_exp] at hlog
  have htanh :
      2 * (Real.exp (2 * y) - 1) / (Real.exp (2 * y) - 1 + 2) =
        2 * Real.tanh y := by
    rw [routeETanh_eq_expTwoRatio]
    ring
  rw [htanh] at hlog
  linarith

/-- **Exact pair polarization.** Relative imbalance of two physical Gibbs atoms is the hyperbolic
tangent of half their normalized displacement. -/
theorem routeEGibbsPair_abs_sub_eq_tanh
    (X m n : ℝ) (hX : 0 < X) :
    |Real.exp (-m / X) - Real.exp (-n / X)| =
      Real.tanh (|m - n| / (2 * X)) *
        (Real.exp (-m / X) + Real.exp (-n / X)) := by
  wlog hmn : m ≤ n generalizing m n
  · have hswap := this n m (le_of_not_ge hmn)
    simpa [abs_sub_comm, add_comm] using hswap
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by
      exact div_le_div_of_nonneg_right (neg_le_neg hmn) hX.le)))]
    rw [abs_of_nonpos (sub_nonpos.mpr hmn)]
    have hplus :
        Real.exp (-m / X) =
          Real.exp (-(m + n) / (2 * X)) * Real.exp ((n - m) / (2 * X)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hX.ne']
      ring
    have hminus :
        Real.exp (-n / X) =
          Real.exp (-(m + n) / (2 * X)) * Real.exp (-((n - m) / (2 * X))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hX.ne']
      ring
    rw [hplus, hminus, Real.tanh_eq]
    have hden :
        Real.exp ((n - m) / (2 * X)) + Real.exp (-((n - m) / (2 * X))) ≠ 0 := by
      positivity
    field_simp [hden]
    ring

/-- Ratio form of exact pair polarization. -/
theorem routeEGibbsPair_abs_sub_div_add_eq_tanh
    (X m n : ℝ) (hX : 0 < X) :
    |Real.exp (-m / X) - Real.exp (-n / X)| /
        (Real.exp (-m / X) + Real.exp (-n / X)) =
      Real.tanh (|m - n| / (2 * X)) := by
  rw [routeEGibbsPair_abs_sub_eq_tanh X m n hX]
  field_simp [ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))]

/-- Finite source-predeclared opposite-sign matching, including unmatched positive and negative
physical mass. All validity conditions are fields of the datum, so consumers need no route
hypothesis. -/
structure RouteELocalPhysicalMatchingReceiver (ι : Type*) [Fintype ι] where
  X : ℝ
  H : ℝ
  left : ι → ℝ
  right : ι → ℝ
  unmatchedPositive : ℝ
  unmatchedNegative : ℝ
  X_pos : 0 < X
  H_nonneg : 0 ≤ H
  gap : ∀ i, |left i - right i| ≤ H
  unmatchedPositive_nonneg : 0 ≤ unmatchedPositive
  unmatchedNegative_nonneg : 0 ≤ unmatchedNegative
  total_pos : 0 <
    (∑ i, (Real.exp (-left i / X) + Real.exp (-right i / X))) +
      unmatchedPositive + unmatchedNegative

namespace RouteELocalPhysicalMatchingReceiver

variable {ι : Type*} [Fintype ι]

def leftWeight (d : RouteELocalPhysicalMatchingReceiver ι) (i : ι) : ℝ :=
  Real.exp (-d.left i / d.X)

def rightWeight (d : RouteELocalPhysicalMatchingReceiver ι) (i : ι) : ℝ :=
  Real.exp (-d.right i / d.X)

def matchedMass (d : RouteELocalPhysicalMatchingReceiver ι) : ℝ :=
  ∑ i, (d.leftWeight i + d.rightWeight i)

def unmatchedMass (d : RouteELocalPhysicalMatchingReceiver ι) : ℝ :=
  d.unmatchedPositive + d.unmatchedNegative

def totalMass (d : RouteELocalPhysicalMatchingReceiver ι) : ℝ :=
  d.matchedMass + d.unmatchedMass

def signedCurrent (d : RouteELocalPhysicalMatchingReceiver ι) : ℝ :=
  (∑ i, (d.leftWeight i - d.rightWeight i)) +
    d.unmatchedPositive - d.unmatchedNegative

def normalizedCurrent (d : RouteELocalPhysicalMatchingReceiver ι) : ℝ :=
  d.signedCurrent / d.totalMass

def unmatchedFraction (d : RouteELocalPhysicalMatchingReceiver ι) : ℝ :=
  d.unmatchedMass / d.totalMass

theorem totalMass_pos (d : RouteELocalPhysicalMatchingReceiver ι) : 0 < d.totalMass := by
  simpa [totalMass, matchedMass, unmatchedMass, leftWeight, rightWeight,
    add_assoc] using d.total_pos

theorem matchedMass_nonneg (d : RouteELocalPhysicalMatchingReceiver ι) : 0 ≤ d.matchedMass := by
  rw [matchedMass]
  apply Finset.sum_nonneg
  intro i _hi
  exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem unmatchedMass_nonneg
    (d : RouteELocalPhysicalMatchingReceiver ι) : 0 ≤ d.unmatchedMass :=
  add_nonneg d.unmatchedPositive_nonneg d.unmatchedNegative_nonneg

private theorem abs_pair_sub_le
    (d : RouteELocalPhysicalMatchingReceiver ι) (i : ι) :
    |d.leftWeight i - d.rightWeight i| ≤
      Real.tanh (d.H / (2 * d.X)) * (d.leftWeight i + d.rightWeight i) := by
  rw [leftWeight, rightWeight,
    routeEGibbsPair_abs_sub_eq_tanh d.X (d.left i) (d.right i) d.X_pos]
  apply mul_le_mul_of_nonneg_right
  · apply routeETanh_mono
    exact div_le_div_of_nonneg_right (d.gap i)
      (mul_nonneg (by norm_num) d.X_pos.le)
  · positivity

/-- **Sharp local receiver.** Normalized physical current is bounded by normalized unmatched mass
plus the exact worst-pair polarization. -/
theorem abs_normalizedCurrent_le_unmatchedFraction_add_tanh
    (d : RouteELocalPhysicalMatchingReceiver ι) :
    |d.normalizedCurrent| ≤
      d.unmatchedFraction + Real.tanh (d.H / (2 * d.X)) := by
  let tau := Real.tanh (d.H / (2 * d.X))
  have htau : 0 ≤ tau := by
    dsimp [tau]
    have harg : 0 ≤ d.H / (2 * d.X) :=
      div_nonneg d.H_nonneg (mul_nonneg (by norm_num) d.X_pos.le)
    simpa using routeETanh_mono harg
  have hunmatched :
      |d.unmatchedPositive - d.unmatchedNegative| ≤ d.unmatchedMass := by
    rw [unmatchedMass, abs_sub_le_iff]
    constructor <;> linarith [d.unmatchedPositive_nonneg, d.unmatchedNegative_nonneg]
  have hpair :
      ∑ i, |d.leftWeight i - d.rightWeight i| ≤ tau * d.matchedMass := by
    calc
      ∑ i, |d.leftWeight i - d.rightWeight i| ≤
          ∑ i, tau * (d.leftWeight i + d.rightWeight i) := by
            apply Finset.sum_le_sum
            intro i _hi
            exact d.abs_pair_sub_le i
      _ = tau * d.matchedMass := by rw [matchedMass, Finset.mul_sum]
  have hcurrent : |d.signedCurrent| ≤ d.unmatchedMass + tau * d.matchedMass := by
    calc
      |d.signedCurrent| =
          |(∑ i, (d.leftWeight i - d.rightWeight i)) +
            (d.unmatchedPositive - d.unmatchedNegative)| := by
              simp [signedCurrent]
              ring
      _ ≤ |∑ i, (d.leftWeight i - d.rightWeight i)| +
          |d.unmatchedPositive - d.unmatchedNegative| := abs_add_le _ _
      _ ≤ (∑ i, |d.leftWeight i - d.rightWeight i|) + d.unmatchedMass :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) hunmatched
      _ ≤ d.unmatchedMass + tau * d.matchedMass := by linarith
  have hmatched_le : d.matchedMass ≤ d.totalMass := by
    rw [totalMass]
    linarith [d.unmatchedMass_nonneg]
  have hratio : d.matchedMass / d.totalMass ≤ 1 :=
    (div_le_one d.totalMass_pos).2 hmatched_le
  rw [normalizedCurrent, abs_div, abs_of_pos d.totalMass_pos]
  calc
    |d.signedCurrent| / d.totalMass ≤
        (d.unmatchedMass + tau * d.matchedMass) / d.totalMass :=
      div_le_div_of_nonneg_right hcurrent d.totalMass_pos.le
    _ = d.unmatchedFraction + tau * (d.matchedMass / d.totalMass) := by
      simp [unmatchedFraction]
      ring
    _ ≤ d.unmatchedFraction + tau * 1 :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hratio htau)
    _ = d.unmatchedFraction + Real.tanh (d.H / (2 * d.X)) := by simp [tau]

/-- Linear physical-scale corollary `u + H/(2X)`. -/
theorem abs_normalizedCurrent_le_unmatchedFraction_add_gap
    (d : RouteELocalPhysicalMatchingReceiver ι) :
    |d.normalizedCurrent| ≤ d.unmatchedFraction + d.H / (2 * d.X) := by
  exact d.abs_normalizedCurrent_le_unmatchedFraction_add_tanh.trans
    (add_le_add (le_refl d.unmatchedFraction)
      (routeETanh_le_self_of_nonneg _
        (div_nonneg d.H_nonneg (mul_nonneg (by norm_num) d.X_pos.le))))

/-- Paper notation for the sharp receiver, with `|J|/Z` displayed literally. -/
theorem abs_signedCurrent_div_totalMass_le_unmatchedFraction_add_tanh
    (d : RouteELocalPhysicalMatchingReceiver ι) :
    |d.signedCurrent| / d.totalMass ≤
      d.unmatchedFraction + Real.tanh (d.H / (2 * d.X)) := by
  simpa [normalizedCurrent, abs_div, abs_of_pos d.totalMass_pos] using
    d.abs_normalizedCurrent_le_unmatchedFraction_add_tanh

/-- Paper notation for the linear receiver `|J|/Z ≤ u + H/(2X)`. -/
theorem abs_signedCurrent_div_totalMass_le_unmatchedFraction_add_gap
    (d : RouteELocalPhysicalMatchingReceiver ι) :
    |d.signedCurrent| / d.totalMass ≤ d.unmatchedFraction + d.H / (2 * d.X) := by
  simpa [normalizedCurrent, abs_div, abs_of_pos d.totalMass_pos] using
    d.abs_normalizedCurrent_le_unmatchedFraction_add_gap

end RouteELocalPhysicalMatchingReceiver

end

end RHTower
