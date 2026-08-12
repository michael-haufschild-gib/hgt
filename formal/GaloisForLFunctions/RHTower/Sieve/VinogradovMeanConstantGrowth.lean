import GaloisForLFunctions.RHTower.Sieve.MontgomeryVaughanLogPhaseReceiver
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Polynomial-log growth of the Route-T VMVT constants

The finite mean-value proof uses a recursive natural constant.  Existence of a strict phase saving
is not enough for a zeta estimate: its base threshold must grow at most exponentially in a
polynomial of the height-shell index.  This file gives a deliberately coarse, closed envelope.
-/

namespace RHTower.Sieve

noncomputable section

def vinogradovReservoirPrimeGrowthExponent (k : ℕ) : ℕ :=
  vinogradovReservoirSize k * k + k + (k + 3) * k

def vinogradovMeanInnerGrowthExponent (k R : ℕ) : ℕ :=
  2 * vinogradovReservoirSize k + k * k + (k + 2 * k * R) +
    vinogradovReservoirPrimeGrowthExponent k * k + 4 * k + 1

def vinogradovMeanGrowthStep (k R : ℕ) : ℕ :=
  (vinogradovReservoirSize k + k + 4) * k * (2 * k * (R + 1)) +
    vinogradovMeanInnerGrowthExponent k R + 10

theorem nat_le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by omega)
      omega

theorem factorial_le_two_pow_sq (k : ℕ) :
    k.factorial ≤ 2 ^ (k * k) := by
  calc
    k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left (nat_le_two_pow_self k) k
    _ = 2 ^ (k * k) := by rw [pow_mul]

theorem vinogradovReservoirLinearConstant_le_two_pow (k : ℕ) :
    vinogradovReservoirLinearConstant k ≤
      2 ^ (vinogradovReservoirSize k + k + 3) := by
  unfold vinogradovReservoirLinearConstant
  calc
    2 ^ vinogradovReservoirSize k * (k + 3) ≤
        2 ^ vinogradovReservoirSize k * 2 ^ (k + 3) :=
      Nat.mul_le_mul_left _ (nat_le_two_pow_self (k + 3))
    _ = 2 ^ (vinogradovReservoirSize k + k + 3) := by
      rw [← pow_add]
      congr 1

theorem vinogradovReservoirPrimePowerConstant_le_two_pow (k : ℕ) :
    vinogradovReservoirPrimePowerConstant k ≤
      2 ^ vinogradovReservoirPrimeGrowthExponent k := by
  have hbase : (k + 3) ^ k ≤ (2 ^ (k + 3)) ^ k :=
    Nat.pow_le_pow_left (nat_le_two_pow_self (k + 3)) k
  unfold vinogradovReservoirPrimePowerConstant
    vinogradovReservoirPrimeGrowthExponent
  calc
    2 ^ (vinogradovReservoirSize k * k + k) * (k + 3) ^ k ≤
        2 ^ (vinogradovReservoirSize k * k + k) * (2 ^ (k + 3)) ^ k :=
      Nat.mul_le_mul_left _ hbase
    _ = 2 ^ (vinogradovReservoirSize k * k + k + (k + 3) * k) := by
      rw [← pow_mul, ← pow_add]

theorem vinogradovReservoirSmallThreshold_le_two_pow (k : ℕ) :
    vinogradovReservoirSmallThreshold k ≤
      2 ^ ((vinogradovReservoirSize k + k + 4) * k) := by
  have hlinear := vinogradovReservoirLinearConstant_le_two_pow k
  have htwice : 2 * vinogradovReservoirLinearConstant k ≤
      2 ^ (vinogradovReservoirSize k + k + 4) := by
    calc
      2 * vinogradovReservoirLinearConstant k ≤
          2 * 2 ^ (vinogradovReservoirSize k + k + 3) :=
        Nat.mul_le_mul_left 2 hlinear
      _ = 2 ^ (vinogradovReservoirSize k + k + 4) := by
        calc
          2 * 2 ^ (vinogradovReservoirSize k + k + 3) =
              2 ^ 1 * 2 ^ (vinogradovReservoirSize k + k + 3) := by norm_num
          _ = 2 ^ (1 + (vinogradovReservoirSize k + k + 3)) := by rw [← pow_add]
          _ = 2 ^ (vinogradovReservoirSize k + k + 4) := by
            congr 1
            omega
  unfold vinogradovReservoirSmallThreshold
  calc
    (2 * vinogradovReservoirLinearConstant k) ^ k ≤
        (2 ^ (vinogradovReservoirSize k + k + 4)) ^ k :=
      Nat.pow_le_pow_left htwice k
    _ = 2 ^ ((vinogradovReservoirSize k + k + 4) * k) := by rw [pow_mul]

theorem vinogradovMeanExponent_le_linear (k r : ℕ) :
    vinogradovMeanExponent k r ≤ k + 2 * k * r := by
  unfold vinogradovMeanExponent
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

theorem vinogradovMeanInnerFactor_le_two_pow
    (k R r : ℕ) (hr : r ≤ R) :
    vinogradovReservoirSize k ^ 2 * k.factorial *
          2 ^ vinogradovMeanExponent k r *
          vinogradovReservoirPrimePowerConstant k ^ (k - 2) +
        (k * k - k) ^ 2 ≤
      2 ^ vinogradovMeanInnerGrowthExponent k R := by
  let V := vinogradovReservoirSize k
  let C := vinogradovReservoirPrimeGrowthExponent k
  let E := 2 * V + k * k + (k + 2 * k * R) + C * k + 4 * k
  have hV : V ^ 2 ≤ 2 ^ (2 * V) := by
    calc
      V ^ 2 ≤ (2 ^ V) ^ 2 := Nat.pow_le_pow_left (nat_le_two_pow_self V) 2
      _ = 2 ^ (2 * V) := by
        rw [← pow_mul]
        congr 1
        omega
  have hfac := factorial_le_two_pow_sq k
  have hmean : 2 ^ vinogradovMeanExponent k r ≤ 2 ^ (k + 2 * k * R) := by
    apply Nat.pow_le_pow_right (by omega)
    exact (vinogradovMeanExponent_le_linear k r).trans (by gcongr)
  have hprime : vinogradovReservoirPrimePowerConstant k ^ (k - 2) ≤
      2 ^ (C * k) := by
    calc
      vinogradovReservoirPrimePowerConstant k ^ (k - 2) ≤
          (2 ^ C) ^ (k - 2) :=
        Nat.pow_le_pow_left (vinogradovReservoirPrimePowerConstant_le_two_pow k) _
      _ = 2 ^ (C * (k - 2)) := by rw [pow_mul]
      _ ≤ 2 ^ (C * k) := by
        apply Nat.pow_le_pow_right (by omega)
        exact Nat.mul_le_mul_left C (Nat.sub_le k 2)
  have hfirst : V ^ 2 * k.factorial * 2 ^ vinogradovMeanExponent k r *
      vinogradovReservoirPrimePowerConstant k ^ (k - 2) ≤ 2 ^ E := by
    calc
      V ^ 2 * k.factorial * 2 ^ vinogradovMeanExponent k r *
          vinogradovReservoirPrimePowerConstant k ^ (k - 2) ≤
        2 ^ (2 * V) * 2 ^ (k * k) * 2 ^ (k + 2 * k * R) * 2 ^ (C * k) := by
          gcongr
      _ = 2 ^ (2 * V + k * k + (k + 2 * k * R) + C * k) := by
        simp only [← pow_add]
      _ ≤ 2 ^ E := by
        apply Nat.pow_le_pow_right (by omega)
        unfold E
        omega
  have hsecond : (k * k - k) ^ 2 ≤ 2 ^ E := by
    calc
      (k * k - k) ^ 2 ≤ (k * k) ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
      _ = k ^ 4 := by ring
      _ ≤ (2 ^ k) ^ 4 := Nat.pow_le_pow_left (nat_le_two_pow_self k) 4
      _ = 2 ^ (4 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ 2 ^ E := by
        apply Nat.pow_le_pow_right (by omega)
        unfold E
        omega
  calc
    _ ≤ 2 ^ E + 2 ^ E := Nat.add_le_add hfirst hsecond
    _ = 2 ^ (E + 1) := by rw [pow_succ]; ring
    _ = 2 ^ vinogradovMeanInnerGrowthExponent k R := by
      rfl

theorem vinogradovMeanConstant_le_two_pow_growth_aux
    {k : ℕ} (hk : 2 ≤ k) : ∀ r R : ℕ, r ≤ R →
      vinogradovMeanConstant k r ≤
        2 ^ (r * (vinogradovMeanGrowthStep k R + 4)) := by
  intro r
  induction r with
  | zero =>
      intro R _
      simp [vinogradovMeanConstant]
  | succ r ih =>
      intro R hrR
      have hrR' : r ≤ R := by omega
      let G := vinogradovMeanGrowthStep k R
      let D := r * (G + 4)
      let E := D + G
      have hprevious : vinogradovMeanConstant k r ≤ 2 ^ D := by
        simpa only [D, G] using ih R hrR'
      have hsmallBase := vinogradovReservoirSmallThreshold_le_two_pow k
      have hsmall : vinogradovReservoirSmallThreshold k ^ (2 * k * (r + 1)) ≤
          2 ^ G := by
        calc
          vinogradovReservoirSmallThreshold k ^ (2 * k * (r + 1)) ≤
              (2 ^ ((vinogradovReservoirSize k + k + 4) * k)) ^
                (2 * k * (r + 1)) := Nat.pow_le_pow_left hsmallBase _
          _ = 2 ^ (((vinogradovReservoirSize k + k + 4) * k) *
                (2 * k * (r + 1))) := by rw [← pow_mul]
          _ ≤ 2 ^ G := by
            apply Nat.pow_le_pow_right (by omega)
            unfold G vinogradovMeanGrowthStep
            have : r + 1 ≤ R + 1 := by omega
            have hmul :
                ((vinogradovReservoirSize k + k + 4) * k) *
                    (2 * k * (r + 1)) ≤
                  ((vinogradovReservoirSize k + k + 4) * k) *
                    (2 * k * (R + 1)) := by gcongr
            calc
              _ ≤ ((vinogradovReservoirSize k + k + 4) * k) *
                    (2 * k * (R + 1)) := hmul
              _ ≤ ((vinogradovReservoirSize k + k + 4) * k) *
                    (2 * k * (R + 1)) + vinogradovMeanInnerGrowthExponent k R + 10 := by
                omega
      have hfac : k.factorial ≤ 2 ^ G := by
        calc
          k.factorial ≤ 2 ^ (k * k) := factorial_le_two_pow_sq k
          _ ≤ 2 ^ G := by
            apply Nat.pow_le_pow_right (by omega)
            unfold G vinogradovMeanGrowthStep vinogradovMeanInnerGrowthExponent
            omega
      have hinner := vinogradovMeanInnerFactor_le_two_pow k R r hrR'
      have hinnerG :
          vinogradovReservoirSize k ^ 2 * k.factorial *
                2 ^ vinogradovMeanExponent k r *
                vinogradovReservoirPrimePowerConstant k ^ (k - 2) +
              (k * k - k) ^ 2 ≤ 2 ^ (G - 2) := by
        calc
          _ ≤ 2 ^ vinogradovMeanInnerGrowthExponent k R := hinner
          _ ≤ 2 ^ (G - 2) := by
            apply Nat.pow_le_pow_right (by omega)
            unfold G vinogradovMeanGrowthStep
            omega
      have hproduct :
          2 * vinogradovMeanConstant k r *
              (vinogradovReservoirSize k ^ 2 * k.factorial *
                  2 ^ vinogradovMeanExponent k r *
                  vinogradovReservoirPrimePowerConstant k ^ (k - 2) +
                (k * k - k) ^ 2) ≤ 2 ^ E := by
        calc
          _ ≤ 2 * 2 ^ D * 2 ^ (G - 2) := by gcongr
          _ = 2 ^ (D + 1 + (G - 2)) := by
            calc
              2 * 2 ^ D * 2 ^ (G - 2) = 2 ^ 1 * 2 ^ D * 2 ^ (G - 2) := by
                norm_num
              _ = 2 ^ (1 + D + (G - 2)) := by rw [← pow_add, ← pow_add]
              _ = 2 ^ (D + 1 + (G - 2)) := by
                congr 1
                omega
          _ ≤ 2 ^ E := by
            apply Nat.pow_le_pow_right (by omega)
            unfold E
            have hG : 2 ≤ G := by
              unfold G vinogradovMeanGrowthStep
              omega
            omega
      have hsmallE : vinogradovReservoirSmallThreshold k ^ (2 * k * (r + 1)) ≤
          2 ^ E := hsmall.trans (Nat.pow_le_pow_right (by omega) (by unfold E D; omega))
      have hfacE : k.factorial ≤ 2 ^ E :=
        hfac.trans (Nat.pow_le_pow_right (by omega) (by unfold E D; omega))
      have honeE : 1 ≤ 2 ^ E := Nat.one_le_pow _ _ (by omega)
      have hfinal : vinogradovMeanConstant k (r + 1) ≤
          2 ^ ((r + 1) * (G + 4)) := by
        rw [vinogradovMeanConstant]
        calc
          vinogradovReservoirSmallThreshold k ^ (2 * k * (r + 1)) + k.factorial +
                2 * vinogradovMeanConstant k r *
                  (vinogradovReservoirSize k ^ 2 * k.factorial *
                      2 ^ vinogradovMeanExponent k r *
                      vinogradovReservoirPrimePowerConstant k ^ (k - 2) +
                    (k * k - k) ^ 2) + 1 ≤
              2 ^ E + 2 ^ E + 2 ^ E + 2 ^ E := by omega
          _ = 2 ^ (E + 2) := by
            rw [show E + 2 = E + 1 + 1 by omega, pow_succ, pow_succ]
            ring
          _ ≤ 2 ^ ((r + 1) * (G + 4)) := by
            apply Nat.pow_le_pow_right (by omega)
            rw [show (r + 1) * (G + 4) = r * (G + 4) + G + 4 by ring]
            unfold E D
            omega
      simpa only [G] using hfinal

theorem vinogradovMeanConstant_le_two_pow_growth
    {k r : ℕ} (hk : 2 ≤ k) :
    vinogradovMeanConstant k r ≤
      2 ^ (r * (vinogradovMeanGrowthStep k r + 4)) :=
  vinogradovMeanConstant_le_two_pow_growth_aux hk r r le_rfl

def routeTLogGrowthOrder (u : ℕ) : ℕ := 400 * u

def routeTLogGrowthSteps (u : ℕ) : ℕ := 40000 * u ^ 2

def routeTLogGrowthMoment (u : ℕ) : ℕ :=
  routeTLogGrowthOrder u * routeTLogGrowthSteps u

def routeTLogMeanConstantGrowthExponent (u : ℕ) : ℕ :=
  routeTLogGrowthSteps u *
    (vinogradovMeanGrowthStep (routeTLogGrowthOrder u) (routeTLogGrowthSteps u) + 4)

/-- Explicit nonrecursive polynomial exponent dominating every natural threshold in the Route-T
receiver.  Its deliberately redundant summands keep each provenance visible. -/
def routeTLogReceiverPolynomialExponent (u : ℕ) : ℕ :=
  2 * routeTLogMeanConstantGrowthExponent u +
    24 * routeTLogGrowthMoment u ^ 2 * routeTLogGrowthOrder u +
    160 * routeTLogGrowthMoment u ^ 2 * routeTLogGrowthOrder u +
    (5 + (240 * u + 1) + 202 * (240 * u)) +
    12 * routeTLogGrowthMoment u ^ 2 + 10

theorem vinogradovRouteTOrder_eq_growthOrder (u : ℕ) :
    vinogradovRouteTOrder (4 * u) = routeTLogGrowthOrder u := by
  simp [vinogradovRouteTOrder, routeTLogGrowthOrder]
  ring

theorem vinogradovRouteTMomentSteps_le_growthSteps (u : ℕ) :
    vinogradovRouteTMomentSteps (4 * u) ≤ routeTLogGrowthSteps u := by
  unfold vinogradovRouteTMomentSteps routeTLogGrowthSteps
  rw [show 2500 * (4 * u) ^ 2 = 40000 * u ^ 2 by ring]
  exact Nat.sub_le _ _

theorem vinogradovRouteTMoment_le_growthMoment (u : ℕ) :
    vinogradovRouteTMoment (4 * u) ≤ routeTLogGrowthMoment u := by
  unfold vinogradovRouteTMoment routeTLogGrowthMoment
  rw [vinogradovRouteTOrder_eq_growthOrder]
  exact Nat.mul_le_mul_left _ (vinogradovRouteTMomentSteps_le_growthSteps u)

theorem routeT_vinogradovMeanConstant_le_two_pow
    {u : ℕ} (hu : 1 ≤ u) :
    vinogradovMeanConstant
        (vinogradovRouteTOrder (4 * u)) (vinogradovRouteTMomentSteps (4 * u)) ≤
      2 ^ routeTLogMeanConstantGrowthExponent u := by
  let k := routeTLogGrowthOrder u
  let r := vinogradovRouteTMomentSteps (4 * u)
  let R := routeTLogGrowthSteps u
  have hk : 2 ≤ k := by unfold k routeTLogGrowthOrder; omega
  have hrR : r ≤ R := by
    simpa only [r, R] using vinogradovRouteTMomentSteps_le_growthSteps u
  have hmean := vinogradovMeanConstant_le_two_pow_growth_aux hk r R hrR
  have hexponent : r * (vinogradovMeanGrowthStep k R + 4) ≤
      routeTLogMeanConstantGrowthExponent u := by
    unfold routeTLogMeanConstantGrowthExponent
    simpa only [k, R] using
      Nat.mul_le_mul_right (vinogradovMeanGrowthStep k R + 4) hrR
  rw [vinogradovRouteTOrder_eq_growthOrder]
  exact hmean.trans (Nat.pow_le_pow_right (by omega) hexponent)

theorem routeT_vinogradovMomentConstant_le_two_pow
    {u : ℕ} (hu : 1 ≤ u) :
    vinogradovRouteTMomentConstant u ≤
      2 ^ (2 * routeTLogMeanConstantGrowthExponent u +
        24 * routeTLogGrowthMoment u ^ 2 * routeTLogGrowthOrder u) := by
  let k := vinogradovRouteTOrder (4 * u)
  let b := vinogradovRouteTMoment (4 * u)
  let K := routeTLogGrowthOrder u
  let B := routeTLogGrowthMoment u
  let D := routeTLogMeanConstantGrowthExponent u
  have hkK : k = K := vinogradovRouteTOrder_eq_growthOrder u
  have hbB : b ≤ B := vinogradovRouteTMoment_le_growthMoment u
  have hmean := routeT_vinogradovMeanConstant_le_two_pow hu
  have hmeanSq : vinogradovMeanConstant k (vinogradovRouteTMomentSteps (4 * u)) ^ 2 ≤
      2 ^ (2 * D) := by
    calc
      _ ≤ (2 ^ D) ^ 2 := Nat.pow_le_pow_left (by simpa only [k, D] using hmean) 2
      _ = 2 ^ (2 * D) := by
        rw [← pow_mul]
        congr 1
        omega
  have hfactorBase : 24 * b ^ 2 ≤ 2 ^ (24 * b ^ 2) :=
    nat_le_two_pow_self (24 * b ^ 2)
  have hfactor : (24 * b ^ 2) ^ k ≤ 2 ^ (24 * B ^ 2 * K) := by
    calc
      (24 * b ^ 2) ^ k ≤ (2 ^ (24 * b ^ 2)) ^ k :=
        Nat.pow_le_pow_left hfactorBase k
      _ = 2 ^ ((24 * b ^ 2) * k) := by rw [← pow_mul]
      _ ≤ 2 ^ (24 * B ^ 2 * K) := by
        apply Nat.pow_le_pow_right (by omega)
        rw [hkK]
        gcongr
  unfold vinogradovRouteTMomentConstant
  change vinogradovMeanConstant k (vinogradovRouteTMomentSteps (4 * u)) ^ 2 *
      (24 * b ^ 2) ^ k ≤ _
  calc
    _ ≤ 2 ^ (2 * D) * 2 ^ (24 * B ^ 2 * K) :=
      Nat.mul_le_mul hmeanSq hfactor
    _ = 2 ^ (2 * D + 24 * B ^ 2 * K) := by rw [← pow_add]

theorem routeTLogWindowThreshold_le_two_pow_polynomial (u : ℕ) :
    routeTLogWindowThreshold u ≤
      2 ^ (5 + (240 * u + 1) + 202 * (240 * u)) := by
  have hlinear : 240 * u + 1 ≤ 2 ^ (240 * u + 1) :=
    nat_le_two_pow_self (240 * u + 1)
  unfold routeTLogWindowThreshold routeTLogCentreMultiplier
  calc
    32 * (240 * u + 1) * (2 ^ 202) ^ (240 * u) ≤
        2 ^ 5 * 2 ^ (240 * u + 1) * (2 ^ 202) ^ (240 * u) := by
      simpa only [show 2 ^ 5 = 32 by norm_num] using
        Nat.mul_le_mul_right ((2 ^ 202) ^ (240 * u))
          (Nat.mul_le_mul_left 32 hlinear)
    _ = 2 ^ (5 + (240 * u + 1) + 202 * (240 * u)) := by
      rw [← pow_mul, ← pow_add, ← pow_add]

theorem routeTLogBaseThreshold_le_two_pow_polynomial
    {u : ℕ} (hu : 1 ≤ u) :
    routeTLogBaseThreshold u ≤ 2 ^ routeTLogReceiverPolynomialExponent u := by
  let k := vinogradovRouteTOrder (4 * u)
  let b := vinogradovRouteTMoment (4 * u)
  let K := routeTLogGrowthOrder u
  let B := routeTLogGrowthMoment u
  let E := routeTLogReceiverPolynomialExponent u
  have hkK : k = K := vinogradovRouteTOrder_eq_growthOrder u
  have hbB : b ≤ B := vinogradovRouteTMoment_le_growthMoment u
  have hwindow := routeTLogWindowThreshold_le_two_pow_polynomial u
  have hwindowE : routeTLogWindowThreshold u ≤ 2 ^ E :=
    hwindow.trans (Nat.pow_le_pow_right (by omega) (by
      unfold E routeTLogReceiverPolynomialExponent
      omega))
  have hscale : 160 * b ^ 2 * k ≤ 2 ^ E := by
    calc
      160 * b ^ 2 * k ≤ 2 ^ (160 * b ^ 2 * k) :=
        nat_le_two_pow_self (160 * b ^ 2 * k)
      _ ≤ 2 ^ E := by
        apply Nat.pow_le_pow_right (by omega)
        rw [hkK]
        unfold E routeTLogReceiverPolynomialExponent
        have : b ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hbB 2
        nlinarith
  have hmoment := routeT_vinogradovMomentConstant_le_two_pow hu
  have hmomentE : vinogradovRouteTMomentConstant u ≤ 2 ^ E :=
    hmoment.trans (Nat.pow_le_pow_right (by omega) (by
      unfold E routeTLogReceiverPolynomialExponent
      omega))
  unfold routeTLogBaseThreshold
  exact max_le hwindowE (max_le hscale hmomentE)

theorem routeTLogReceiverBaseThreshold_le_two_pow_polynomial
    {u : ℕ} (hu : 1 ≤ u) :
    routeTLogReceiverBaseThreshold u ≤ 2 ^ routeTLogReceiverPolynomialExponent u := by
  let b := vinogradovRouteTMoment (4 * u)
  let B := routeTLogGrowthMoment u
  let E := routeTLogReceiverPolynomialExponent u
  have hbB : b ≤ B := vinogradovRouteTMoment_le_growthMoment u
  have hbase := routeTLogBaseThreshold_le_two_pow_polynomial hu
  have hreceiver : 8 ^ (4 * b ^ 2) ≤ 2 ^ E := by
    calc
      8 ^ (4 * b ^ 2) = 2 ^ (12 * b ^ 2) := by
        rw [show 8 = 2 ^ 3 by norm_num, ← pow_mul]
        congr 1
        ring
      _ ≤ 2 ^ E := by
        apply Nat.pow_le_pow_right (by omega)
        unfold E routeTLogReceiverPolynomialExponent
        have : b ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hbB 2
        nlinarith
  unfold routeTLogReceiverBaseThreshold
  exact max_le (by simpa only [E] using hbase) hreceiver

theorem routeTLogReceiverBaseThreshold_add_one_le_two_pow_polynomial
    {u : ℕ} (hu : 1 ≤ u) :
    routeTLogReceiverBaseThreshold u + 1 ≤
      2 ^ (routeTLogReceiverPolynomialExponent u + 1) := by
  have hthreshold := routeTLogReceiverBaseThreshold_le_two_pow_polynomial hu
  have hone : 1 ≤ 2 ^ routeTLogReceiverPolynomialExponent u :=
    Nat.one_le_pow _ _ (by omega)
  calc
    routeTLogReceiverBaseThreshold u + 1 ≤
        2 ^ routeTLogReceiverPolynomialExponent u +
          2 ^ routeTLogReceiverPolynomialExponent u := Nat.add_le_add hthreshold hone
    _ = 2 ^ (routeTLogReceiverPolynomialExponent u + 1) := by
      rw [pow_succ]
      ring

/-- Polynomial size alone now certifies floor-root eligibility; the recursive VMVT constant no
longer appears in hypotheses consumed by later zeta estimates. -/
theorem routeTLogReceiverBaseThreshold_le_nthRoot_of_polynomial_size
    {u X : ℕ} (hu : 1 ≤ u)
    (hX : 2 ^ (routeTLogCentreExponent *
        (routeTLogReceiverPolynomialExponent u + 1)) ≤ X) :
    routeTLogReceiverBaseThreshold u + 1 ≤
      Nat.nthRoot routeTLogCentreExponent X := by
  have hdegree : routeTLogCentreExponent ≠ 0 := by
    norm_num [routeTLogCentreExponent]
  have hpower : (2 ^ (routeTLogReceiverPolynomialExponent u + 1)) ^
      routeTLogCentreExponent ≤ X := by
    calc
      (2 ^ (routeTLogReceiverPolynomialExponent u + 1)) ^
          routeTLogCentreExponent =
        2 ^ ((routeTLogReceiverPolynomialExponent u + 1) *
          routeTLogCentreExponent) :=
            (pow_mul 2 (routeTLogReceiverPolynomialExponent u + 1)
              routeTLogCentreExponent).symm
      _ =
        2 ^ (routeTLogCentreExponent *
          (routeTLogReceiverPolynomialExponent u + 1)) := by
            rw [mul_comm]
      _ ≤ X := hX
  exact (routeTLogReceiverBaseThreshold_add_one_le_two_pow_polynomial hu).trans
    ((Nat.le_nthRoot_iff hdegree).2 hpower)

end

end RHTower.Sieve
