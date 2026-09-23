import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalMassNoGo
import GaloisForLFunctions.RHTower.SourceHorizontalStokesConditionedInformationCoenergy

/-!
# Critical information Schur depletion no-go

The first coefficient-faithful negative channel suggested by the source-horizontal information
virial is mathematically well-posed.  At critical aperture, its coefficient `κ(p,e)` is strictly
between zero and two on every prime-power label.  Subtracting `κ w` from P-G71's raw mass `2w`
therefore leaves a strictly positive summable carrier.

This valid Schur channel is nevertheless far too weak.  A cubic virial bound proves `κ < 3/10`
on the same four hostile atoms used by P-G72, while sharper source-only contraction estimates show
their raw mass exceeds `63/1000`.  Consequently the four depleted atoms alone still exceed the
entire completed seam mass `29/625`.  First-information depletion is retired; any successful
Gamma/polar Feshbach completion requires an additional genuinely coupled negative channel.

No Xi zero, RH premise, fitted scalar, numerical computation, or added axiom enters.
-/

open Real Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

theorem sourceHorizontalHolonomyVirial_le_cubic_exp
    {u : ℝ} (hu : 0 ≤ u) :
    sourceHorizontalHolonomyVirial u ≤ u ^ (3 : ℕ) * Real.exp u / 3 := by
  let F : ℝ → ℝ := fun x => x ^ (3 : ℕ) * Real.exp x / 3 -
    sourceHorizontalHolonomyVirial x
  have hderiv : ∀ x : ℝ, HasDerivAt F
      ((3 * x ^ (2 : ℕ) * Real.exp x + x ^ (3 : ℕ) * Real.exp x) / 3 -
        x * Real.sinh x) x := by
    intro x
    have hpow : HasDerivAt (fun y : ℝ => y ^ (3 : ℕ)) (3 * x ^ (2 : ℕ)) x :=
      hasDerivAt_pow 3 x
    have hmain := (hpow.mul (Real.hasDerivAt_exp x)).div_const 3
    have hvirial := hasDerivAt_sourceHorizontalHolonomyVirial x
    have h := hmain.sub hvirial
    change HasDerivAt
      (fun y : ℝ => y ^ (3 : ℕ) * Real.exp y / 3 - sourceHorizontalHolonomyVirial y)
      _ x at h
    exact h.congr_deriv (by ring)
  have hmono : MonotoneOn F (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hderiv x).deriv]
    have hx0 : 0 ≤ x := hx.le
    have hsinh := HTGeometry.sinh_le_self_mul_cosh hx0
    have hcosh := HTGeometry.cosh_le_exp_of_nonneg hx0
    have hxsinh : x * Real.sinh x ≤ x ^ (2 : ℕ) * Real.exp x := by
      calc
        x * Real.sinh x ≤ x * (x * Real.cosh x) :=
          mul_le_mul_of_nonneg_left hsinh hx0
        _ = x ^ (2 : ℕ) * Real.cosh x := by ring
        _ ≤ x ^ (2 : ℕ) * Real.exp x :=
          mul_le_mul_of_nonneg_left hcosh (sq_nonneg x)
    nlinarith [mul_nonneg (pow_nonneg hx0 3) (Real.exp_pos x).le]
  have h := hmono Set.self_mem_Ici hu hu
  change F 0 ≤ F u at h
  simpa [F, sourceHorizontalHolonomyVirial] using h

def gammaSewnMobiusApertureStokesCriticalInformationFactor
    (pk : Nat.Primes × ℕ) : ℝ :=
  sourceHorizontalPrimeGeometricKLScaleTerm pk.1 pk.2 (1 / 4)

theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_eq
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusApertureStokesCriticalInformationFactor (p, e) =
      4 * Real.exp (-Real.log (p : ℝ) * (e + 1)) / (e + 1) *
        sourceHorizontalHolonomyVirial
          ((e + 1) * Real.log (p : ℝ) / 2) := by
  rw [gammaSewnMobiusApertureStokesCriticalInformationFactor,
    sourceHorizontalPrimeGeometricKLScaleTerm,
    sourceHorizontalPrimePowerHolonomy_scaleVirial]
  ring

private theorem two_mul_lt_exp_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    2 * u < Real.exp u := by
  have hTaylor0 := Real.sum_le_exp_of_nonneg hu 3
  have hTaylor : 1 + u + u ^ (2 : ℕ) / 2 ≤ Real.exp u := by
    norm_num [Finset.sum_range_succ] at hTaylor0 ⊢
    exact hTaylor0
  have hstrict : 2 * u < 1 + u + u ^ (2 : ℕ) / 2 := by
    nlinarith [sq_nonneg (u - 1)]
  exact hstrict.trans_le hTaylor

theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_pos
    (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesCriticalInformationFactor pk := by
  have h := sourceHorizontalPrimeGeometricKLScaleTerm_complementary_pos
    (s := (1 / 2 : ℝ)) (by norm_num) pk.1 pk.2
  norm_num at h
  exact h

theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_lt_two
    (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesCriticalInformationFactor pk < 2 := by
  let k : ℝ := pk.2 + 1
  let u : ℝ := k * Real.log (pk.1 : ℝ) / 2
  have hk : 1 ≤ k := by dsimp [k]; norm_num
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hL : 0 < Real.log (pk.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pk.1.2.one_lt)
  have hu : 0 < u := by dsimp [u]; positivity
  have htwo := two_mul_lt_exp_of_nonneg hu.le
  have hvirial := sourceHorizontalHolonomyVirial_le_mul_exp hu.le
  have hvirialStrict :
      sourceHorizontalHolonomyVirial u < Real.exp u ^ (2 : ℕ) / 2 := by
    have hmul : u * Real.exp u < Real.exp u ^ (2 : ℕ) / 2 := by
      nlinarith [Real.exp_pos u]
    exact hvirial.trans_lt hmul
  rw [gammaSewnMobiusApertureStokesCriticalInformationFactor_eq]
  change 4 * Real.exp (-Real.log (pk.1 : ℝ) * k) / k *
      sourceHorizontalHolonomyVirial u < 2
  have hexpcoord : -Real.log (pk.1 : ℝ) * k = -2 * u := by
    dsimp [u]
    ring
  rw [hexpcoord]
  have hcoeff : 0 < 4 * Real.exp (-2 * u) / k := by positivity
  calc
    4 * Real.exp (-2 * u) / k * sourceHorizontalHolonomyVirial u <
        4 * Real.exp (-2 * u) / k * (Real.exp u ^ (2 : ℕ) / 2) :=
      mul_lt_mul_of_pos_left hvirialStrict hcoeff
    _ = 2 / k := by
      have hexpone : Real.exp (-2 * u) * Real.exp u ^ (2 : ℕ) = 1 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]
        convert Real.exp_zero using 1
        · congr 1
          ring
      rw [show 4 * Real.exp (-2 * u) / k * (Real.exp u ^ (2 : ℕ) / 2) =
        (2 / k) * (Real.exp (-2 * u) * Real.exp u ^ (2 : ℕ)) by ring,
        hexpone, mul_one]
    _ ≤ 2 := by
      exact div_le_self (by norm_num) hk

theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusApertureStokesCriticalInformationFactor (p, e) ≤
      4 / (3 * (e + 1 : ℝ)) *
        (((e + 1 : ℝ) * Real.log (p : ℝ) / 2) ^ (3 : ℕ) *
          Real.exp (-((e + 1 : ℝ) * Real.log (p : ℝ) / 2))) := by
  let k : ℝ := e + 1
  let u : ℝ := k * Real.log (p : ℝ) / 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hvirial := sourceHorizontalHolonomyVirial_le_cubic_exp hu
  rw [gammaSewnMobiusApertureStokesCriticalInformationFactor_eq]
  change 4 * Real.exp (-Real.log (p : ℝ) * k) / k *
      sourceHorizontalHolonomyVirial u ≤
    4 / (3 * k) * (u ^ (3 : ℕ) * Real.exp (-u))
  have hcoeff : 0 ≤ 4 * Real.exp (-Real.log (p : ℝ) * k) / k := by positivity
  calc
    4 * Real.exp (-Real.log (p : ℝ) * k) / k *
        sourceHorizontalHolonomyVirial u ≤
      4 * Real.exp (-Real.log (p : ℝ) * k) / k *
        (u ^ (3 : ℕ) * Real.exp u / 3) :=
      mul_le_mul_of_nonneg_left hvirial hcoeff
    _ = 4 / (3 * k) * (u ^ (3 : ℕ) * Real.exp (-u)) := by
      have hcoord : -Real.log (p : ℝ) * k = -2 * u := by
        dsimp [u]
        ring
      rw [hcoord]
      have hexp : Real.exp (-2 * u) * Real.exp u = Real.exp (-u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [show 4 * Real.exp (-2 * u) / k * (u ^ (3 : ℕ) * Real.exp u / 3) =
        4 / (3 * k) * u ^ (3 : ℕ) *
          (Real.exp (-2 * u) * Real.exp u) by ring, hexp]
      ring

private theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_two_zero_lt :
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) < 3 / 10 := by
  have h := gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic
    RHTower.gammaSewnMobiusApertureStokesPrimeTwo 0
  have hlog : Real.log 2 < 7 / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have hu0 : 0 ≤ Real.log 2 / 2 := by positivity
  have hu : Real.log 2 / 2 < 7 / 20 := by linarith
  have hexp : Real.exp (-(Real.log 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  norm_num only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul, mul_one] at h
  calc
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) ≤
      4 / 3 * ((Real.log 2 / 2) ^ (3 : ℕ) * Real.exp (-(Real.log 2 / 2))) := h
    _ < 4 / 3 * ((7 / 20 : ℝ) ^ (3 : ℕ) * Real.exp (-(Real.log 2 / 2))) := by gcongr
    _ ≤ 4 / 3 * ((7 / 20 : ℝ) ^ (3 : ℕ) * 1) := by gcongr
    _ < 3 / 10 := by norm_num

private theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_two_one_lt :
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1) < 3 / 10 := by
  have h := gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic
    RHTower.gammaSewnMobiusApertureStokesPrimeTwo 1
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlog : Real.log 2 < 7 / 10 := Real.log_two_lt_d9.trans (by norm_num)
  have hexp : Real.exp (-Real.log 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  norm_num only [Nat.cast_one, one_add_one_eq_two] at h
  norm_num at h
  calc
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1) ≤
      2 / 3 * (Real.log 2 ^ (3 : ℕ) * Real.exp (-Real.log 2)) := by simpa using h
    _ < 2 / 3 * ((7 / 10 : ℝ) ^ (3 : ℕ) * Real.exp (-Real.log 2)) := by gcongr
    _ ≤ 2 / 3 * ((7 / 10 : ℝ) ^ (3 : ℕ) * 1) := by gcongr
    _ < 3 / 10 := by norm_num

private theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_three_zero_lt :
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0) < 3 / 10 := by
  have h := gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic
    RHTower.gammaSewnMobiusApertureStokesPrimeThree 0
  have hlog : Real.log 3 < 11 / 10 := Real.log_three_lt_d9.trans (by norm_num)
  have hu0 : 0 ≤ Real.log 3 / 2 := by positivity
  have hu : Real.log 3 / 2 < 11 / 20 := by linarith
  have hexp : Real.exp (-(Real.log 3 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
  norm_num only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul, mul_one] at h
  calc
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0) ≤
      4 / 3 * ((Real.log 3 / 2) ^ (3 : ℕ) * Real.exp (-(Real.log 3 / 2))) := h
    _ < 4 / 3 * ((11 / 20 : ℝ) ^ (3 : ℕ) * Real.exp (-(Real.log 3 / 2))) := by gcongr
    _ ≤ 4 / 3 * ((11 / 20 : ℝ) ^ (3 : ℕ) * 1) := by gcongr
    _ < 3 / 10 := by norm_num

private theorem gammaSewnMobiusApertureStokesCriticalInformationFactor_three_one_lt :
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1) < 3 / 10 := by
  have h := gammaSewnMobiusApertureStokesCriticalInformationFactor_le_cubic
    RHTower.gammaSewnMobiusApertureStokesPrimeThree 1
  have hlog0 : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hlog : Real.log 3 < 11 / 10 := Real.log_three_lt_d9.trans (by norm_num)
  have hexp : Real.exp (-Real.log 3) = 1 / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  norm_num only [Nat.cast_one, one_add_one_eq_two] at h
  norm_num at h
  calc
    gammaSewnMobiusApertureStokesCriticalInformationFactor
        (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1) ≤
      2 / 3 * (Real.log 3 ^ (3 : ℕ) * Real.exp (-Real.log 3)) := by simpa using h
    _ = 2 / 3 * (Real.log 3 ^ (3 : ℕ) * (1 / 3)) := by rw [hexp]
    _ < 2 / 3 * ((11 / 10 : ℝ) ^ (3 : ℕ) * (1 / 3)) := by gcongr
    _ < 3 / 10 := by norm_num

private theorem criticalPrimeTwoHalfNode_strongBounds :
    let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
      RHTower.gammaSewnMobiusApertureStokesPrimeTwo
    (7 / 10 : ℝ) < r ∧ r < 5 / 7 := by
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
    RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hr2 : r ^ (2 : ℕ) = 1 / 2 := by
    simpa [r, RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv] using
      RHTower.xiMobiusContinuousApertureDiskNode_half_sq
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  constructor <;> by_contra h
  · have hr : r ≤ 7 / 10 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 7 / 10))]
  · have hr : 5 / 7 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 5 / 7))]

private theorem criticalPrimeThreeHalfNode_strongBounds :
    let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
      RHTower.gammaSewnMobiusApertureStokesPrimeThree
    (4 / 7 : ℝ) < r ∧ r < 3 / 5 := by
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
    RHTower.gammaSewnMobiusApertureStokesPrimeThree
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hr2 : r ^ (2 : ℕ) = 1 / 3 := by
    simpa [r, RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv] using
      RHTower.xiMobiusContinuousApertureDiskNode_half_sq
        RHTower.gammaSewnMobiusApertureStokesPrimeThree
  constructor <;> by_contra h
  · have hr : r ≤ 4 / 7 := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 4 / 7))]
  · have hr : 3 / 5 ≤ r := le_of_not_gt h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr)
      (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 3 / 5))]

private theorem nineteen_twentieths_lt_criticalPrimeTwoContraction :
    (19 / 20 : ℝ) <
      RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2)
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo := by
  let p := RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (7 / 10 : ℝ) < r ∧ r < 5 / 7 := by
    simpa only [r, p] using criticalPrimeTwoHalfNode_strongBounds
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hc0 : 0 < c := RHTower.gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hden : 0 < 8 * (1 + r ^ (4 : ℕ)) := by positivity
  have hnum : (17 / 10 : ℝ) ^ (4 : ℕ) < (1 + r) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ (by linarith [hr.1]) (by norm_num) (by norm_num)
  have hr4 : r ^ (4 : ℕ) < (5 / 7 : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hr.2 hr0.le (by norm_num)
  have hc4 : (19 / 20 : ℝ) ^ (4 : ℕ) < c ^ (4 : ℕ) := by
    rw [RHTower.gammaSewnMobiusValuationContractionMultiplier_pow_four]
    change (19 / 20 : ℝ) ^ (4 : ℕ) < (1 + r) ^ (4 : ℕ) / (8 * (1 + r ^ (4 : ℕ)))
    rw [lt_div_iff₀ hden]
    norm_num at hnum hr4 ⊢
    nlinarith
  by_contra h
  have hc : c ≤ 19 / 20 := le_of_not_gt h
  have hc2 : c ^ (2 : ℕ) ≤ (19 / 20 : ℝ) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (add_nonneg hc0.le (by norm_num : (0 : ℝ) ≤ 19 / 20))]
  have hc4le : c ^ (4 : ℕ) ≤ (19 / 20 : ℝ) ^ (4 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2)
      (add_nonneg (sq_nonneg c) (sq_nonneg (19 / 20 : ℝ)))]
  linarith

private theorem nine_tenths_lt_criticalPrimeThreeContraction :
    (9 / 10 : ℝ) <
      RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2)
        RHTower.gammaSewnMobiusApertureStokesPrimeThree := by
  let p := RHTower.gammaSewnMobiusApertureStokesPrimeThree
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (4 / 7 : ℝ) < r ∧ r < 3 / 5 := by
    simpa only [r, p] using criticalPrimeThreeHalfNode_strongBounds
  have hr0 : 0 < r := RHTower.xiMobiusContinuousApertureDiskNode_pos _ _
  have hc0 : 0 < c := RHTower.gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hden : 0 < 8 * (1 + r ^ (4 : ℕ)) := by positivity
  have hnum : (11 / 7 : ℝ) ^ (4 : ℕ) < (1 + r) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ (by linarith [hr.1]) (by norm_num) (by norm_num)
  have hr4 : r ^ (4 : ℕ) < (3 / 5 : ℝ) ^ (4 : ℕ) :=
    pow_lt_pow_left₀ hr.2 hr0.le (by norm_num)
  have hc4 : (9 / 10 : ℝ) ^ (4 : ℕ) < c ^ (4 : ℕ) := by
    rw [RHTower.gammaSewnMobiusValuationContractionMultiplier_pow_four]
    change (9 / 10 : ℝ) ^ (4 : ℕ) < (1 + r) ^ (4 : ℕ) / (8 * (1 + r ^ (4 : ℕ)))
    rw [lt_div_iff₀ hden]
    norm_num at hnum hr4 ⊢
    nlinarith
  by_contra h
  have hc : c ≤ 9 / 10 := le_of_not_gt h
  have hc2 : c ^ (2 : ℕ) ≤ (9 / 10 : ℝ) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc)
      (add_nonneg hc0.le (by norm_num : (0 : ℝ) ≤ 9 / 10))]
  have hc4le : c ^ (4 : ℕ) ≤ (9 / 10 : ℝ) ^ (4 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2)
      (add_nonneg (sq_nonneg c) (sq_nonneg (9 / 10 : ℝ)))]
  linarith

private theorem criticalPrimeTwoDepthZero_strongWeightLower :
    (4 / 125 : ℝ) <
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
        (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) := by
  let p := RHTower.gammaSewnMobiusApertureStokesPrimeTwo
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (7 / 10 : ℝ) < r ∧ r < 5 / 7 := by
    simpa only [r, p] using criticalPrimeTwoHalfNode_strongBounds
  have hc : (19 / 20 : ℝ) < c := nineteen_twentieths_lt_criticalPrimeTwoContraction
  have hc2 : (361 / 400 : ℝ) < c ^ (2 : ℕ) := by nlinarith [sq_nonneg (c - 19 / 20)]
  have hgap : (4 / 49 : ℝ) < (1 - r) ^ (2 : ℕ) := by nlinarith [sq_nonneg (r - 5 / 7)]
  have hprod : (361 / 4900 : ℝ) < c ^ (2 : ℕ) * (1 - r) ^ (2 : ℕ) := by
    nlinarith [mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hgap)]
  have hdenpos : 0 < Real.log 2 * r :=
    mul_pos (Real.log_pos (by norm_num)) (lt_trans (by norm_num) hr.1)
  have hden : Real.log 2 * r < 1 / 2 := by
    calc
      Real.log 2 * r < (7 / 10 : ℝ) * r := by
        exact mul_lt_mul_of_pos_right
          (Real.log_two_lt_d9.trans (by norm_num)) (lt_trans (by norm_num) hr.1)
      _ < (7 / 10 : ℝ) * (5 / 7) :=
        mul_lt_mul_of_pos_left hr.2 (by norm_num)
      _ = 1 / 2 := by norm_num
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesReflectedWeight_eq_source (by norm_num)]
  simp only [RHTower.gammaSewnMobiusApertureStokesPrimeTwo,
    RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, pow_zero, mul_one, Nat.reduceAdd,
    Nat.cast_one, one_pow]
  change (4 / 125 : ℝ) <
    2 * (c ^ (2 : ℕ) * (1 / 9) * (1 - r) ^ (2 : ℕ) /
      (1 * Real.log 2 * r))
  norm_num only [one_mul]
  rw [show 2 * (c ^ (2 : ℕ) * (1 / 9) * (1 - r) ^ (2 : ℕ) / (Real.log 2 * r)) =
    (2 * c ^ (2 : ℕ) * (1 / 9) * (1 - r) ^ (2 : ℕ)) / (Real.log 2 * r) by ring]
  rw [lt_div_iff₀ hdenpos]
  nlinarith

private theorem criticalPrimeThreeDepthZero_strongWeightLower :
    (3 / 125 : ℝ) <
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
        (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0) := by
  let p := RHTower.gammaSewnMobiusApertureStokesPrimeThree
  let r := RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p
  let c := RHTower.gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr : (4 / 7 : ℝ) < r ∧ r < 3 / 5 := by
    simpa only [r, p] using criticalPrimeThreeHalfNode_strongBounds
  have hc : (9 / 10 : ℝ) < c := nine_tenths_lt_criticalPrimeThreeContraction
  have hc2 : (81 / 100 : ℝ) < c ^ (2 : ℕ) := by nlinarith [sq_nonneg (c - 9 / 10)]
  have hgap : (4 / 25 : ℝ) < (1 - r) ^ (2 : ℕ) := by nlinarith [sq_nonneg (r - 3 / 5)]
  have hprod : (81 / 625 : ℝ) < c ^ (2 : ℕ) * (1 - r) ^ (2 : ℕ) := by
    nlinarith [mul_pos (sub_pos.mpr hc2) (sub_pos.mpr hgap)]
  have hdenpos : 0 < Real.log 3 * r :=
    mul_pos (Real.log_pos (by norm_num)) (lt_trans (by norm_num) hr.1)
  have hden : Real.log 3 * r < 33 / 50 := by
    calc
      Real.log 3 * r < (11 / 10 : ℝ) * r := by
        exact mul_lt_mul_of_pos_right
          (Real.log_three_lt_d9.trans (by norm_num)) (lt_trans (by norm_num) hr.1)
      _ < (11 / 10 : ℝ) * (3 / 5) :=
        mul_lt_mul_of_pos_left hr.2 (by norm_num)
      _ = 33 / 50 := by norm_num
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesReflectedWeight_eq_source (by norm_num)]
  simp only [RHTower.gammaSewnMobiusApertureStokesPrimeThree,
    RHTower.xiTransversePrimeApertureDiskNode_one_eq_inv]
  norm_num only [Nat.cast_ofNat, invOf_eq_inv, pow_zero, mul_one, Nat.reduceAdd,
    Nat.cast_one, one_pow]
  change (3 / 125 : ℝ) <
    2 * (c ^ (2 : ℕ) * (1 / 16) * (1 - r) ^ (2 : ℕ) /
      (1 * Real.log 3 * r))
  norm_num only [one_mul]
  rw [show 2 * (c ^ (2 : ℕ) * (1 / 16) * (1 - r) ^ (2 : ℕ) / (Real.log 3 * r)) =
    (2 * c ^ (2 : ℕ) * (1 / 16) * (1 - r) ^ (2 : ℕ)) / (Real.log 3 * r) by ring]
  rw [lt_div_iff₀ hdenpos]
  nlinarith

private theorem criticalSquaredWeight_depthOne_eq
    (p : Nat.Primes) :
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, 1) =
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2) p / 4 *
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) (p, 0) := by
  rw [RHTower.gammaSewnMobiusApertureStokesSquaredWeight,
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight,
    gammaSewnMobiusApertureStokesReflectedWeight_eq_source (by norm_num),
    gammaSewnMobiusApertureStokesReflectedWeight_eq_source (by norm_num)]
  have hr :=
    (RHTower.xiMobiusContinuousApertureDiskNode_pos (1 / 2) p).ne'
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog := (Real.log_pos hp).ne'
  norm_num
  field_simp [hr, hlog]

theorem gammaSewnMobiusApertureStokesCriticalRawFourAtomMass_strongLower :
    (63 / 1000 : ℝ) <
      RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) +
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1) +
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0) +
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
          (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1) := by
  let w20 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)
  let w21 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1)
  let w30 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0)
  let w31 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2)
    (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1)
  have h20 : (4 / 125 : ℝ) < w20 := criticalPrimeTwoDepthZero_strongWeightLower
  have h30 : (3 / 125 : ℝ) < w30 := criticalPrimeThreeDepthZero_strongWeightLower
  have hw20 : 0 < w20 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) _
  have hw30 : 0 < w30 := RHTower.gammaSewnMobiusApertureStokesSquaredWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) _
  have hr2 : (1 / 2 : ℝ) <
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo :=
    (lt_trans (by norm_num : (1 / 2 : ℝ) < 7 / 10)
      criticalPrimeTwoHalfNode_strongBounds.1)
  have hr3 : (1 / 2 : ℝ) <
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
        RHTower.gammaSewnMobiusApertureStokesPrimeThree :=
    (lt_trans (by norm_num : (1 / 2 : ℝ) < 4 / 7)
      criticalPrimeThreeHalfNode_strongBounds.1)
  have h21eq : w21 =
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
        RHTower.gammaSewnMobiusApertureStokesPrimeTwo / 4 * w20 :=
    criticalSquaredWeight_depthOne_eq _
  have h31eq : w31 =
      RHTower.xiMobiusContinuousApertureDiskNode (1 / 2)
        RHTower.gammaSewnMobiusApertureStokesPrimeThree / 4 * w30 :=
    criticalSquaredWeight_depthOne_eq _
  have h21 : (1 / 8 : ℝ) * w20 < w21 := by
    rw [h21eq]
    nlinarith [mul_pos (sub_pos.mpr hr2) hw20]
  have h31 : (1 / 8 : ℝ) * w30 < w31 := by
    rw [h31eq]
    nlinarith [mul_pos (sub_pos.mpr hr3) hw30]
  change (63 / 1000 : ℝ) < w20 + w21 + w30 + w31
  nlinarith

def gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
    (pk : Nat.Primes × ℕ) : ℝ :=
  (2 - gammaSewnMobiusApertureStokesCriticalInformationFactor pk) *
    RHTower.gammaSewnMobiusApertureStokesReflectedWeight (1 / 2) pk

theorem gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos
    (pk : Nat.Primes × ℕ) :
    0 < gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk := by
  exact mul_pos
    (sub_pos.mpr (gammaSewnMobiusApertureStokesCriticalInformationFactor_lt_two pk))
    (RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos
      (s := (1 / 2 : ℝ)) (by norm_num) pk)

theorem summable_gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight :
    Summable gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight := by
  apply Summable.of_nonneg_of_le
    (fun pk =>
      (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le)
    (fun pk => ?_)
    (RHTower.summable_gammaSewnMobiusApertureStokesSquaredWeight
      (s := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  rw [gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight,
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight]
  have hk0 := gammaSewnMobiusApertureStokesCriticalInformationFactor_pos pk
  have hw0 :=
    (RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos
      (s := (1 / 2 : ℝ)) (by norm_num) pk).le
  exact mul_le_mul_of_nonneg_right (by linarith) hw0

private theorem criticalInformationDepletedWeight_gt_seventeenTwentieths_raw
    (pk : Nat.Primes × ℕ)
    (hk : gammaSewnMobiusApertureStokesCriticalInformationFactor pk < 3 / 10) :
    (17 / 20 : ℝ) *
        RHTower.gammaSewnMobiusApertureStokesSquaredWeight (1 / 2) pk <
      gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk := by
  rw [gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight,
    RHTower.gammaSewnMobiusApertureStokesSquaredWeight]
  have hw := RHTower.gammaSewnMobiusApertureStokesReflectedWeight_pos
    (s := (1 / 2 : ℝ)) (by norm_num) pk
  nlinarith [mul_pos (sub_pos.mpr hk) hw]

theorem gammaSewnMobiusApertureStokesCriticalInformationDepletedFourAtomMass_lower :
    (29 / 625 : ℝ) <
      gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) +
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1) +
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0) +
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1) := by
  have h20 := criticalInformationDepletedWeight_gt_seventeenTwentieths_raw
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0)
    gammaSewnMobiusApertureStokesCriticalInformationFactor_two_zero_lt
  have h21 := criticalInformationDepletedWeight_gt_seventeenTwentieths_raw
    (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1)
    gammaSewnMobiusApertureStokesCriticalInformationFactor_two_one_lt
  have h30 := criticalInformationDepletedWeight_gt_seventeenTwentieths_raw
    (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0)
    gammaSewnMobiusApertureStokesCriticalInformationFactor_three_zero_lt
  have h31 := criticalInformationDepletedWeight_gt_seventeenTwentieths_raw
    (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1)
    gammaSewnMobiusApertureStokesCriticalInformationFactor_three_one_lt
  have hraw := gammaSewnMobiusApertureStokesCriticalRawFourAtomMass_strongLower
  nlinarith

theorem normalizedPrimeArchMoment_zero_lt_tsum_criticalInformationDepletedWeight :
    RHTower.normalizedPrimeArchMoment 0 <
      ∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk := by
  let S : Finset (Nat.Primes × ℕ) :=
    {(RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0),
      (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1),
      (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0),
      (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1)}
  have hle := summable_gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight.sum_le_tsum
    S (fun pk _ =>
      (gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight_pos pk).le)
  have hpne : RHTower.gammaSewnMobiusApertureStokesPrimeTwo ≠
      RHTower.gammaSewnMobiusApertureStokesPrimeThree := by
    intro h
    have := congrArg Subtype.val h
    norm_num at this
  have hfinite :
      gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 0) +
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeTwo, 1) +
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 0) +
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight
          (RHTower.gammaSewnMobiusApertureStokesPrimeThree, 1) ≤
      ∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk := by
    simpa [S, hpne, add_assoc, add_comm, add_left_comm] using hle
  exact RHTower.normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive.trans
    (gammaSewnMobiusApertureStokesCriticalInformationDepletedFourAtomMass_lower.trans_le
      hfinite)

theorem gammaSewnMobiusApertureStokesCriticalInformationAdditionalDepletion_neg
    {C : ℝ}
    (hC : (∑' pk : Nat.Primes × ℕ,
        gammaSewnMobiusApertureStokesCriticalInformationDepletedWeight pk) + C =
      RHTower.normalizedPrimeArchMoment 0) :
    C < 0 := by
  linarith [normalizedPrimeArchMoment_zero_lt_tsum_criticalInformationDepletedWeight]

end RHTower.HedenmalmThetaSource
