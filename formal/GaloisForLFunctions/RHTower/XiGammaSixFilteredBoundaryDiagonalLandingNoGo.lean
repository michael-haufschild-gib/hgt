import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryCollisionCurrent
import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent

/-!
# No bounded diagonal landing from filtered Gamma-six flux to Gauss--Hodge collision current

The literal filtered Gamma-six boundary flux is a strictly positive, absolutely summable sequence
over prime labels at every positive depth. The multiplicity-faithful Gauss--Hodge current has a
different trace-ideal phase: it is summable exactly on a critical Xi copy, where it vanishes.

This mismatch closes the positive prime-diagonal version of HC's proposed source identification.
Existence of one fixed summable filtered envelope for every strip window is equivalent to RH, as
is copywise bounded diagonal landing. More sharply, literal coefficientwise equality is impossible
both globally and at every individual Xi copy. Thus any surviving HC transform must be unbounded,
signed, off-diagonal, singular, or otherwise retain information not present in a positive diagonal
prime multiplier.
-/

open Complex Set Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- One fixed positive diagonal envelope from filtered Gamma-six flux dominates every finite
horizontal-collision Gauss--Hodge window. -/
def HCFilteredGammaSixDiagonalLanding : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧
    ∃ t : ℝ, 0 < t ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ T : ℝ, ∀ p : Nat.Primes,
          xiHorizontalCollisionGaussHodgePrimeCurrent m T p ≤
            C * gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p

/-- Proposed literal coefficientwise identification of one fixed filtered Gamma-six source with
every horizontal-collision Gauss--Hodge window. -/
def HCFilteredGammaSixExactDiagonalLanding : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧
    ∃ t : ℝ, 0 < t ∧
      ∀ T : ℝ, ∀ p : Nat.Primes,
        xiHorizontalCollisionGaussHodgePrimeCurrent m T p =
          gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p

/-- Every Xi multiplicity copy admits some bounded positive diagonal landing into a filtered
Gamma-six source sequence. -/
def HCFilteredGammaSixCopyDiagonalLanding : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧
    ∀ q : XiZeroCopy,
      ∃ t : ℝ, 0 < t ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ p : Nat.Primes,
            gaussHodgeMassCurrent m q p ≤
              C * gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p

/-- Filtered Gamma-six collision flux is nonnegative at every prime label. -/
theorem gammaSixFilteredBoundaryCollisionCurrentPrimeTerm_nonneg
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p := by
  rw [gammaSixFilteredBoundaryCollisionCurrentPrimeTerm]
  exact mul_nonneg
    (gammaSixFilteredBoundaryConfluentFluxPrimeTerm_nonneg hm ht p)
    (gammaSixFilteredBoundaryRadialFactor_bounds hm p).1

/-- The unfiltered confluent flux is strictly positive at positive depth. -/
theorem gammaSixFilteredBoundaryConfluentFluxPrimeTerm_pos
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    0 < gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hexp : -(1 + 2 * t) < -(1 + 2 * (t / 2)) := by linarith
  have hrpow := Real.rpow_lt_rpow_of_exponent_lt hp1 hexp
  have hweight : xiMassPrimeSquareEulerWeight t p <
      xiMassPrimeSquareEulerWeight (t / 2) p := by
    rw [xiMassPrimeSquareEulerWeight_eq, xiMassPrimeSquareEulerWeight_eq]
    exact mul_lt_mul_of_pos_left hrpow hlog
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  rw [gammaSixFilteredBoundaryConfluentFluxPrimeTerm]
  exact mul_pos (by positivity) (sub_pos.mpr hweight)

/-- All three literal radial factors are strictly positive. -/
theorem gammaSixFilteredBoundaryRadialFactor_pos
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    0 < gammaSixFilteredBoundaryRadialFactor m p := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp1
  have hinv : (p : ℝ)⁻¹ < 1 := by
    simpa only [one_div] using (inv_lt_one₀ hp0).2 hp1
  have hbase : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr hinv
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hrpow : (p : ℝ) ^ (-(m : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hgap : 0 < 1 - (p : ℝ) ^ (-(m : ℝ)) := sub_pos.mpr hrpow
  rw [gammaSixFilteredBoundaryRadialFactor]
  positivity

/-- The literal filtered Gamma-six flux is strictly positive at every prime label. -/
theorem gammaSixFilteredBoundaryCollisionCurrentPrimeTerm_pos
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    0 < gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p := by
  rw [gammaSixFilteredBoundaryCollisionCurrentPrimeTerm]
  exact mul_pos
    (gammaSixFilteredBoundaryConfluentFluxPrimeTerm_pos hm ht p)
    (gammaSixFilteredBoundaryRadialFactor_pos hm p)

/-- Every finite-window Gauss--Hodge prime current is pointwise nonnegative. -/
theorem xiHorizontalCollisionGaussHodgePrimeCurrent_nonneg
    {m : ℕ} (hm : 1 ≤ m) (T : ℝ) (p : Nat.Primes) :
    0 ≤ xiHorizontalCollisionGaussHodgePrimeCurrent m T p := by
  exact xiFiniteGaussHodgePrimeCurrent_nonneg hm _ p

/-- Under RH every finite-window Gauss--Hodge prime coefficient vanishes, not merely its sum. -/
theorem xiHorizontalCollisionGaussHodgePrimeCurrent_eq_zero_of_rh
    (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m)
    (T : ℝ) (p : Nat.Primes) :
    xiHorizontalCollisionGaussHodgePrimeCurrent m T p = 0 := by
  rw [xiHorizontalCollisionGaussHodgePrimeCurrent,
    xiFiniteGaussHodgePrimeCurrent]
  apply Finset.sum_eq_zero
  intro q hq
  apply (gaussHodgeMassCurrent_eq_zero_iff hm q p).2
  exact riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH (q.1 : ℂ)
    (xi_eq_zero_of_mem_divisor_support q.1)

/-- Under RH every copywise Gauss--Hodge prime coefficient vanishes. -/
theorem gaussHodgeMassCurrent_eq_zero_of_rh
    (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m)
    (q : XiZeroCopy) (p : Nat.Primes) :
    gaussHodgeMassCurrent m q p = 0 := by
  apply (gaussHodgeMassCurrent_eq_zero_iff hm q p).2
  exact riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH (q.1 : ℂ)
    (xi_eq_zero_of_mem_divisor_support q.1)

/-- **Global diagonal landing classification.** Existence of one summable positive filtered
Gamma-six envelope dominating every horizontal-collision window is exactly RH. -/
theorem riemannHypothesis_iff_hcFilteredGammaSixDiagonalLanding :
    RiemannHypothesis ↔ HCFilteredGammaSixDiagonalLanding := by
  constructor
  · intro hRH
    refine ⟨1, by omega, 1, by norm_num, 1, by norm_num, ?_⟩
    intro T p
    rw [xiHorizontalCollisionGaussHodgePrimeCurrent_eq_zero_of_rh hRH (by omega)]
    simpa using gammaSixFilteredBoundaryCollisionCurrentPrimeTerm_nonneg
      (m := 1) (by omega) (t := 1) (by norm_num) p
  · rintro ⟨m, hm, t, ht, C, hC, hbound⟩
    apply
      (riemannHypothesis_iff_forall_summable_horizontalCollisionGaussHodgePrimeCurrent hm).2
    intro T
    apply Summable.of_nonneg_of_le
    · exact xiHorizontalCollisionGaussHodgePrimeCurrent_nonneg hm T
    · exact hbound T
    · exact
        (summable_gammaSixFilteredBoundaryCollisionCurrentPrimeTerm hm ht).mul_left C

/-- **Window-level exact-landing no-go.** No one positive-depth filtered Gamma-six sequence can
equal every horizontal-collision window prime by prime. -/
theorem not_hcFilteredGammaSixExactDiagonalLanding :
    ¬ HCFilteredGammaSixExactDiagonalLanding := by
  rintro ⟨m, hm, t, ht, heq⟩
  have hlanding : HCFilteredGammaSixDiagonalLanding := by
    refine ⟨m, hm, t, ht, 1, by norm_num, ?_⟩
    intro T p
    rw [heq T p]
    simp
  have hRH := riemannHypothesis_iff_hcFilteredGammaSixDiagonalLanding.mpr hlanding
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hzero := xiHorizontalCollisionGaussHodgePrimeCurrent_eq_zero_of_rh
    hRH hm 0 p2
  have heq2 := heq 0 p2
  have hpos := gammaSixFilteredBoundaryCollisionCurrentPrimeTerm_pos hm ht p2
  rw [hzero] at heq2
  exact hpos.ne' heq2.symm

/-- **Copywise diagonal landing classification.** Even allowing depth and bound to depend on the
Xi multiplicity copy, bounded positive diagonal landing into filtered Gamma-six flux is exactly
RH. -/
theorem riemannHypothesis_iff_hcFilteredGammaSixCopyDiagonalLanding :
    RiemannHypothesis ↔ HCFilteredGammaSixCopyDiagonalLanding := by
  constructor
  · intro hRH
    refine ⟨1, by omega, ?_⟩
    intro q
    refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
    intro p
    rw [gaussHodgeMassCurrent_eq_zero_of_rh hRH (by omega)]
    simpa using gammaSixFilteredBoundaryCollisionCurrentPrimeTerm_nonneg
      (m := 1) (by omega) (t := 1) (by norm_num) p
  · rintro ⟨m, hm, hlanding⟩
    apply (forall_summable_gaussHodgeMassCurrent_iff_riemannHypothesis hm).mp
    intro q
    obtain ⟨t, ht, C, hC, hbound⟩ := hlanding q
    apply Summable.of_nonneg_of_le
    · exact gaussHodgeMassCurrent_nonneg hm q
    · exact hbound
    · exact
        (summable_gammaSixFilteredBoundaryCollisionCurrentPrimeTerm hm ht).mul_left C

/-- **Strong copywise exact-landing obstruction.** At every Xi copy and every positive source
depth, Gauss--Hodge mass and filtered Gamma-six flux cannot agree prime by prime. Summability first
forces the copy onto the critical line, where the former vanishes and the latter remains strictly
positive. -/
theorem no_exact_copywise_gammaSixFilteredBoundaryCollisionLanding :
    ∀ m : ℕ, 1 ≤ m → ∀ q : XiZeroCopy, ∀ t : ℝ, 0 < t →
      ¬ (∀ p : Nat.Primes,
        gaussHodgeMassCurrent m q p =
          gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p) := by
  intro m hm q t ht heq
  have hsum : Summable (gaussHodgeMassCurrent m q) :=
    (summable_gammaSixFilteredBoundaryCollisionCurrentPrimeTerm hm ht).congr
      (fun p => (heq p).symm)
  have hrate :=
    (summable_gaussHodgeMassCurrent_iff_centeredRate_eq_zero hm q).mp hsum
  have hre : (q.1 : ℂ).re = 1 / 2 := by
    rw [primeDepthBVWoldXiCenteredRate] at hrate
    linarith
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hzero : gaussHodgeMassCurrent m q p2 = 0 :=
    (gaussHodgeMassCurrent_eq_zero_iff hm q p2).2 hre
  have heq2 := heq p2
  have hpos := gammaSixFilteredBoundaryCollisionCurrentPrimeTerm_pos hm ht p2
  rw [hzero] at heq2
  exact hpos.ne' heq2.symm

end

end RHTower
