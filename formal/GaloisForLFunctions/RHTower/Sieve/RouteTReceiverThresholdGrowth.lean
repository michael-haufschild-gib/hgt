import GaloisForLFunctions.RHTower.Sieve.VinogradovMeanConstantGrowth

/-!
# Degree-nine envelope for the Route-T receiver threshold

This turns the nonrecursive polynomial exponent into one monomial bound.  Degree nine is the
quantitative datum needed by the near-one zeta optimization.
-/

namespace RHTower.Sieve

noncomputable section

def routeTLogGrowthOrderConstant : ℕ := 400
def routeTLogGrowthStepsConstant : ℕ := 40000
def routeTLogGrowthReservoirConstant : ℕ := routeTLogGrowthOrderConstant ^ (3 : ℕ) + 1
def routeTLogGrowthPrimeConstant : ℕ :=
  routeTLogGrowthReservoirConstant * routeTLogGrowthOrderConstant +
    routeTLogGrowthOrderConstant +
    (routeTLogGrowthOrderConstant + 3) * routeTLogGrowthOrderConstant
def routeTLogGrowthInnerConstant : ℕ :=
  2 * routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant ^ (2 : ℕ) +
    (routeTLogGrowthOrderConstant +
      2 * routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) +
    routeTLogGrowthPrimeConstant * routeTLogGrowthOrderConstant +
    4 * routeTLogGrowthOrderConstant + 1
def routeTLogGrowthStepConstant : ℕ :=
  (routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) *
      routeTLogGrowthOrderConstant *
      (2 * routeTLogGrowthOrderConstant * (routeTLogGrowthStepsConstant + 1)) +
    routeTLogGrowthInnerConstant + 10
def routeTLogGrowthMeanConstant : ℕ :=
  routeTLogGrowthStepsConstant * (routeTLogGrowthStepConstant + 4)
def routeTLogReceiverDegreeNineConstant : ℕ :=
  2 * routeTLogGrowthMeanConstant +
    24 * (routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) ^ (2 : ℕ) *
      routeTLogGrowthOrderConstant +
    160 * (routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) ^ (2 : ℕ) *
      routeTLogGrowthOrderConstant +
    (5 + (240 + 1) + 202 * 240) +
    12 * (routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) ^ (2 : ℕ) + 10

private theorem succ_pow_mono {u a b : ℕ} (hab : a ≤ b) :
    (u + 1) ^ a ≤ (u + 1) ^ b :=
  Nat.pow_le_pow_right (by omega) hab

private theorem routeTLogGrowthOrder_le (u : ℕ) :
    routeTLogGrowthOrder u ≤ routeTLogGrowthOrderConstant * (u + 1) := by
  unfold routeTLogGrowthOrder routeTLogGrowthOrderConstant
  omega

private theorem routeTLogGrowthSteps_le (u : ℕ) :
    routeTLogGrowthSteps u ≤ routeTLogGrowthStepsConstant * (u + 1) ^ (2 : ℕ) := by
  unfold routeTLogGrowthSteps routeTLogGrowthStepsConstant
  gcongr
  omega

private theorem routeTLogGrowthReservoir_le (u : ℕ) :
    vinogradovReservoirSize (routeTLogGrowthOrder u) ≤
      routeTLogGrowthReservoirConstant * (u + 1) ^ (3 : ℕ) := by
  let k := routeTLogGrowthOrder u
  let U := u + 1
  have hk := routeTLogGrowthOrder_le u
  have hone : 1 ≤ U ^ (3 : ℕ) := Nat.one_le_pow _ _ (by omega)
  calc
    vinogradovReservoirSize k = k * (k * k - k) + 1 := rfl
    _ ≤ k * (k * k) + 1 := by gcongr; exact Nat.sub_le _ _
    _ = k ^ (3 : ℕ) + 1 := by ring
    _ ≤ (routeTLogGrowthOrderConstant * U) ^ (3 : ℕ) + 1 := by gcongr
    _ ≤ routeTLogGrowthReservoirConstant * U ^ (3 : ℕ) := by
      unfold routeTLogGrowthReservoirConstant
      rw [mul_pow]
      nlinarith

private theorem routeTLogGrowthPrimeExponent_le (u : ℕ) :
    vinogradovReservoirPrimeGrowthExponent (routeTLogGrowthOrder u) ≤
      routeTLogGrowthPrimeConstant * (u + 1) ^ (4 : ℕ) := by
  let k := routeTLogGrowthOrder u
  let U := u + 1
  have hk := routeTLogGrowthOrder_le u
  have hV := routeTLogGrowthReservoir_le u
  have hk' : k ≤ routeTLogGrowthOrderConstant * U := by simpa only [k, U] using hk
  have hV' : vinogradovReservoirSize k ≤
      routeTLogGrowthReservoirConstant * U ^ (3 : ℕ) := by simpa only [k, U] using hV
  have hk3 : k + 3 ≤ (routeTLogGrowthOrderConstant + 3) * U := by
    have hthree : 3 ≤ 3 * U := by omega
    calc
      k + 3 ≤ routeTLogGrowthOrderConstant * U + 3 := Nat.add_le_add_right hk' 3
      _ ≤ routeTLogGrowthOrderConstant * U + 3 * U := Nat.add_le_add_left hthree _
      _ = (routeTLogGrowthOrderConstant + 3) * U := by ring
  have hU14 := succ_pow_mono (u := u) (a := 1) (b := 4) (by omega)
  have hU24 := succ_pow_mono (u := u) (a := 2) (b := 4) (by omega)
  have hU14' : U ≤ U ^ (4 : ℕ) := by simpa only [U, pow_one] using hU14
  have hU24' : U ^ (2 : ℕ) ≤ U ^ (4 : ℕ) := by simpa only [U] using hU24
  calc
    vinogradovReservoirPrimeGrowthExponent k =
        vinogradovReservoirSize k * k + k + (k + 3) * k := rfl
    _ ≤ (routeTLogGrowthReservoirConstant * U ^ (3 : ℕ)) *
          (routeTLogGrowthOrderConstant * U) +
        routeTLogGrowthOrderConstant * U +
        ((routeTLogGrowthOrderConstant + 3) * U) *
          (routeTLogGrowthOrderConstant * U) := by
      gcongr
    _ ≤ (routeTLogGrowthReservoirConstant * routeTLogGrowthOrderConstant) * U ^ (4 : ℕ) +
        routeTLogGrowthOrderConstant * U ^ (4 : ℕ) +
        ((routeTLogGrowthOrderConstant + 3) * routeTLogGrowthOrderConstant) * U ^ (4 : ℕ) := by
      have hfirst : (routeTLogGrowthReservoirConstant * U ^ (3 : ℕ)) *
          (routeTLogGrowthOrderConstant * U) =
          (routeTLogGrowthReservoirConstant * routeTLogGrowthOrderConstant) * U ^ (4 : ℕ) := by
        ring
      have hthird : ((routeTLogGrowthOrderConstant + 3) * U) *
          (routeTLogGrowthOrderConstant * U) =
          ((routeTLogGrowthOrderConstant + 3) * routeTLogGrowthOrderConstant) * U ^ (2 : ℕ) := by
        ring
      rw [hfirst, hthird]
      exact Nat.add_le_add
        (Nat.add_le_add le_rfl (Nat.mul_le_mul_left routeTLogGrowthOrderConstant hU14'))
        (Nat.mul_le_mul_left
          ((routeTLogGrowthOrderConstant + 3) * routeTLogGrowthOrderConstant) hU24')
    _ = routeTLogGrowthPrimeConstant * U ^ (4 : ℕ) := by
      unfold routeTLogGrowthPrimeConstant
      ring

private theorem routeTLogGrowthInnerExponent_le (u : ℕ) :
    vinogradovMeanInnerGrowthExponent
        (routeTLogGrowthOrder u) (routeTLogGrowthSteps u) ≤
      routeTLogGrowthInnerConstant * (u + 1) ^ (5 : ℕ) := by
  let k := routeTLogGrowthOrder u
  let R := routeTLogGrowthSteps u
  let U := u + 1
  have hk := routeTLogGrowthOrder_le u
  have hR := routeTLogGrowthSteps_le u
  have hV := routeTLogGrowthReservoir_le u
  have hC := routeTLogGrowthPrimeExponent_le u
  have hk' : k ≤ routeTLogGrowthOrderConstant * U := by simpa only [k, U] using hk
  have hR' : R ≤ routeTLogGrowthStepsConstant * U ^ (2 : ℕ) := by simpa only [R, U] using hR
  have hV' : vinogradovReservoirSize k ≤
      routeTLogGrowthReservoirConstant * U ^ (3 : ℕ) := by simpa only [k, U] using hV
  have hC' : vinogradovReservoirPrimeGrowthExponent k ≤
      routeTLogGrowthPrimeConstant * U ^ (4 : ℕ) := by simpa only [k, U] using hC
  have hU15 := succ_pow_mono (u := u) (a := 1) (b := 5) (by omega)
  have hU25 := succ_pow_mono (u := u) (a := 2) (b := 5) (by omega)
  have hU35 := succ_pow_mono (u := u) (a := 3) (b := 5) (by omega)
  have hone : 1 ≤ U ^ (5 : ℕ) := Nat.one_le_pow _ _ (by omega)
  have hU15' : U ≤ U ^ (5 : ℕ) := by simpa only [U, pow_one] using hU15
  have hU25' : U ^ (2 : ℕ) ≤ U ^ (5 : ℕ) := by simpa only [U] using hU25
  have hU35' : U ^ (3 : ℕ) ≤ U ^ (5 : ℕ) := by simpa only [U] using hU35
  calc
    vinogradovMeanInnerGrowthExponent k R =
        2 * vinogradovReservoirSize k + k * k + (k + 2 * k * R) +
          vinogradovReservoirPrimeGrowthExponent k * k + 4 * k + 1 := rfl
    _ ≤ 2 * (routeTLogGrowthReservoirConstant * U ^ (3 : ℕ)) +
          (routeTLogGrowthOrderConstant * U) ^ (2 : ℕ) +
          (routeTLogGrowthOrderConstant * U +
            2 * (routeTLogGrowthOrderConstant * U) *
              (routeTLogGrowthStepsConstant * U ^ (2 : ℕ))) +
          (routeTLogGrowthPrimeConstant * U ^ (4 : ℕ)) *
            (routeTLogGrowthOrderConstant * U) +
          4 * (routeTLogGrowthOrderConstant * U) + 1 := by
      have hsq : k * k ≤
          (routeTLogGrowthOrderConstant * U) ^ (2 : ℕ) := by
        rw [pow_two]
        exact Nat.mul_le_mul hk' hk'
      have hkr : 2 * k * R ≤
          2 * (routeTLogGrowthOrderConstant * U) *
            (routeTLogGrowthStepsConstant * U ^ (2 : ℕ)) := by gcongr
      have hCk : vinogradovReservoirPrimeGrowthExponent k * k ≤
          (routeTLogGrowthPrimeConstant * U ^ (4 : ℕ)) *
            (routeTLogGrowthOrderConstant * U) := Nat.mul_le_mul hC' hk'
      omega
    _ ≤ 2 * routeTLogGrowthReservoirConstant * U ^ (5 : ℕ) +
          routeTLogGrowthOrderConstant ^ (2 : ℕ) * U ^ (5 : ℕ) +
          (routeTLogGrowthOrderConstant * U ^ (5 : ℕ) +
            (2 * routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) * U ^ (5 : ℕ)) +
          (routeTLogGrowthPrimeConstant * routeTLogGrowthOrderConstant) * U ^ (5 : ℕ) +
          (4 * routeTLogGrowthOrderConstant) * U ^ (5 : ℕ) + U ^ (5 : ℕ) := by
      have heq :
          2 * (routeTLogGrowthReservoirConstant * U ^ (3 : ℕ)) +
              (routeTLogGrowthOrderConstant * U) ^ (2 : ℕ) +
              (routeTLogGrowthOrderConstant * U +
                2 * (routeTLogGrowthOrderConstant * U) *
                  (routeTLogGrowthStepsConstant * U ^ (2 : ℕ))) +
              (routeTLogGrowthPrimeConstant * U ^ (4 : ℕ)) *
                (routeTLogGrowthOrderConstant * U) +
              4 * (routeTLogGrowthOrderConstant * U) + 1 =
            2 * routeTLogGrowthReservoirConstant * U ^ (3 : ℕ) +
              routeTLogGrowthOrderConstant ^ (2 : ℕ) * U ^ (2 : ℕ) +
              (routeTLogGrowthOrderConstant * U +
                (2 * routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) * U ^ (3 : ℕ)) +
              (routeTLogGrowthPrimeConstant * routeTLogGrowthOrderConstant) * U ^ (5 : ℕ) +
              (4 * routeTLogGrowthOrderConstant) * U + 1 := by ring
      rw [heq]
      have h1 := Nat.mul_le_mul_left (2 * routeTLogGrowthReservoirConstant) hU35'
      have h2 := Nat.mul_le_mul_left (routeTLogGrowthOrderConstant ^ (2 : ℕ)) hU25'
      have h3 := Nat.mul_le_mul_left routeTLogGrowthOrderConstant hU15'
      have h4 := Nat.mul_le_mul_left
        (2 * routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) hU35'
      have h5 := Nat.mul_le_mul_left (4 * routeTLogGrowthOrderConstant) hU15'
      omega
    _ = routeTLogGrowthInnerConstant * U ^ (5 : ℕ) := by
      unfold routeTLogGrowthInnerConstant
      ring

private theorem routeTLogGrowthStep_le (u : ℕ) :
    vinogradovMeanGrowthStep (routeTLogGrowthOrder u) (routeTLogGrowthSteps u) ≤
      routeTLogGrowthStepConstant * (u + 1) ^ (7 : ℕ) := by
  let k := routeTLogGrowthOrder u
  let R := routeTLogGrowthSteps u
  let U := u + 1
  have hk := routeTLogGrowthOrder_le u
  have hR := routeTLogGrowthSteps_le u
  have hV := routeTLogGrowthReservoir_le u
  have hinner := routeTLogGrowthInnerExponent_le u
  have hk' : k ≤ routeTLogGrowthOrderConstant * U := by simpa only [k, U] using hk
  have hR' : R ≤ routeTLogGrowthStepsConstant * U ^ (2 : ℕ) := by simpa only [R, U] using hR
  have hV' : vinogradovReservoirSize k ≤
      routeTLogGrowthReservoirConstant * U ^ (3 : ℕ) := by simpa only [k, U] using hV
  have hinner' : vinogradovMeanInnerGrowthExponent k R ≤
      routeTLogGrowthInnerConstant * U ^ (5 : ℕ) := by simpa only [k, R, U] using hinner
  have hfirst : vinogradovReservoirSize k + k + 4 ≤
      (routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) * U ^ (3 : ℕ) := by
    have hU13 := succ_pow_mono (u := u) (a := 1) (b := 3) (by omega)
    have hU13' : U ≤ U ^ (3 : ℕ) := by simpa only [U, pow_one] using hU13
    have hone : 1 ≤ U ^ (3 : ℕ) := Nat.one_le_pow _ _ (by omega)
    have hk3 := Nat.mul_le_mul_left routeTLogGrowthOrderConstant hU13'
    have hfour : 4 ≤ 4 * U ^ (3 : ℕ) := by omega
    calc
      vinogradovReservoirSize k + k + 4 ≤
          routeTLogGrowthReservoirConstant * U ^ (3 : ℕ) +
            routeTLogGrowthOrderConstant * U + 4 := by omega
      _ ≤ routeTLogGrowthReservoirConstant * U ^ (3 : ℕ) +
            routeTLogGrowthOrderConstant * U ^ (3 : ℕ) + 4 * U ^ (3 : ℕ) := by omega
      _ = (routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) *
            U ^ (3 : ℕ) := by ring
  have hRone : R + 1 ≤ (routeTLogGrowthStepsConstant + 1) * U ^ (2 : ℕ) := by
    have hone : 1 ≤ U ^ (2 : ℕ) := Nat.one_le_pow _ _ (by omega)
    calc
      R + 1 ≤ routeTLogGrowthStepsConstant * U ^ (2 : ℕ) + 1 := Nat.add_le_add_right hR' 1
      _ ≤ routeTLogGrowthStepsConstant * U ^ (2 : ℕ) + U ^ (2 : ℕ) := Nat.add_le_add_left hone _
      _ = (routeTLogGrowthStepsConstant + 1) * U ^ (2 : ℕ) := by ring
  have hU57 := succ_pow_mono (u := u) (a := 5) (b := 7) (by omega)
  have hU57' : U ^ (5 : ℕ) ≤ U ^ (7 : ℕ) := by simpa only [U] using hU57
  have hone : 1 ≤ U ^ (7 : ℕ) := Nat.one_le_pow _ _ (by omega)
  have hthird : 2 * k * (R + 1) ≤
      2 * (routeTLogGrowthOrderConstant * U) *
        ((routeTLogGrowthStepsConstant + 1) * U ^ (2 : ℕ)) := by gcongr
  have hmain : (vinogradovReservoirSize k + k + 4) * k * (2 * k * (R + 1)) ≤
      ((routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) * U ^ (3 : ℕ)) *
        (routeTLogGrowthOrderConstant * U) *
        (2 * (routeTLogGrowthOrderConstant * U) *
          ((routeTLogGrowthStepsConstant + 1) * U ^ (2 : ℕ))) :=
    Nat.mul_le_mul (Nat.mul_le_mul hfirst hk') hthird
  calc
    vinogradovMeanGrowthStep k R =
        (vinogradovReservoirSize k + k + 4) * k * (2 * k * (R + 1)) +
          vinogradovMeanInnerGrowthExponent k R + 10 := rfl
    _ ≤ ((routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) * U ^ (3 : ℕ)) *
          (routeTLogGrowthOrderConstant * U) *
          (2 * (routeTLogGrowthOrderConstant * U) *
            ((routeTLogGrowthStepsConstant + 1) * U ^ (2 : ℕ))) +
        routeTLogGrowthInnerConstant * U ^ (5 : ℕ) + 10 := by omega
    _ ≤ ((routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) *
            routeTLogGrowthOrderConstant *
            (2 * routeTLogGrowthOrderConstant * (routeTLogGrowthStepsConstant + 1))) * U ^ (7 : ℕ) +
        routeTLogGrowthInnerConstant * U ^ (7 : ℕ) + 10 * U ^ (7 : ℕ) := by
      have hmainequality :
          ((routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) * U ^ (3 : ℕ)) *
              (routeTLogGrowthOrderConstant * U) *
              (2 * (routeTLogGrowthOrderConstant * U) *
                ((routeTLogGrowthStepsConstant + 1) * U ^ (2 : ℕ))) =
            ((routeTLogGrowthReservoirConstant + routeTLogGrowthOrderConstant + 4) *
              routeTLogGrowthOrderConstant *
              (2 * routeTLogGrowthOrderConstant * (routeTLogGrowthStepsConstant + 1))) *
                U ^ (7 : ℕ) := by ring
      rw [hmainequality]
      have hinnerLift := Nat.mul_le_mul_left routeTLogGrowthInnerConstant hU57'
      have hten : 10 ≤ 10 * U ^ (7 : ℕ) := by omega
      omega
    _ = routeTLogGrowthStepConstant * U ^ (7 : ℕ) := by
      unfold routeTLogGrowthStepConstant
      ring

private theorem routeTLogMeanConstantGrowthExponent_le (u : ℕ) :
    routeTLogMeanConstantGrowthExponent u ≤
      routeTLogGrowthMeanConstant * (u + 1) ^ (9 : ℕ) := by
  let U := u + 1
  have hR := routeTLogGrowthSteps_le u
  have hG := routeTLogGrowthStep_le u
  have hfour : 4 ≤ 4 * U ^ (7 : ℕ) := by
    have : 1 ≤ U ^ (7 : ℕ) := Nat.one_le_pow _ _ (by omega)
    omega
  have hGplus : vinogradovMeanGrowthStep
      (routeTLogGrowthOrder u) (routeTLogGrowthSteps u) + 4 ≤
      (routeTLogGrowthStepConstant + 4) * U ^ (7 : ℕ) := by
    calc
      _ ≤ routeTLogGrowthStepConstant * U ^ (7 : ℕ) + 4 * U ^ (7 : ℕ) :=
        Nat.add_le_add hG hfour
      _ = (routeTLogGrowthStepConstant + 4) * U ^ (7 : ℕ) := by ring
  unfold routeTLogMeanConstantGrowthExponent
  calc
    routeTLogGrowthSteps u *
        (vinogradovMeanGrowthStep (routeTLogGrowthOrder u) (routeTLogGrowthSteps u) + 4) ≤
      (routeTLogGrowthStepsConstant * U ^ (2 : ℕ)) *
        ((routeTLogGrowthStepConstant + 4) * U ^ (7 : ℕ)) := by
          exact Nat.mul_le_mul hR hGplus
    _ = routeTLogGrowthMeanConstant * U ^ (9 : ℕ) := by
      unfold routeTLogGrowthMeanConstant
      ring

/-- Degree-nine logarithmic threshold law. -/
theorem routeTLogReceiverPolynomialExponent_le_degreeNine (u : ℕ) :
    routeTLogReceiverPolynomialExponent u ≤
      routeTLogReceiverDegreeNineConstant * (u + 1) ^ (9 : ℕ) := by
  let U := u + 1
  let B0 := routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant
  have hD := routeTLogMeanConstantGrowthExponent_le u
  have hK := routeTLogGrowthOrder_le u
  have hR := routeTLogGrowthSteps_le u
  have hB : routeTLogGrowthMoment u ≤ B0 * U ^ (3 : ℕ) := by
    unfold routeTLogGrowthMoment B0
    calc
      routeTLogGrowthOrder u * routeTLogGrowthSteps u ≤
          (routeTLogGrowthOrderConstant * U) *
            (routeTLogGrowthStepsConstant * U ^ (2 : ℕ)) := Nat.mul_le_mul hK hR
      _ = (routeTLogGrowthOrderConstant * routeTLogGrowthStepsConstant) * U ^ (3 : ℕ) := by ring
  have hU19 := succ_pow_mono (u := u) (a := 1) (b := 9) (by omega)
  have hU69 := succ_pow_mono (u := u) (a := 6) (b := 9) (by omega)
  have hU79 := succ_pow_mono (u := u) (a := 7) (b := 9) (by omega)
  have hU19' : U ≤ U ^ (9 : ℕ) := by simpa only [U, pow_one] using hU19
  have hU69' : U ^ (6 : ℕ) ≤ U ^ (9 : ℕ) := by simpa only [U] using hU69
  have hU79' : U ^ (7 : ℕ) ≤ U ^ (9 : ℕ) := by simpa only [U] using hU79
  have hone : 1 ≤ U ^ (9 : ℕ) := Nat.one_le_pow _ _ (by omega)
  have hwindow : 5 + (240 * u + 1) + 202 * (240 * u) ≤
      (5 + (240 + 1) + 202 * 240) * U := by
    unfold U
    nlinarith
  have hD' : routeTLogMeanConstantGrowthExponent u ≤
      routeTLogGrowthMeanConstant * U ^ (9 : ℕ) := by simpa only [U] using hD
  have hD2 : 2 * routeTLogMeanConstantGrowthExponent u ≤
      2 * routeTLogGrowthMeanConstant * U ^ (9 : ℕ) := by
    calc
      2 * routeTLogMeanConstantGrowthExponent u ≤
          2 * (routeTLogGrowthMeanConstant * U ^ (9 : ℕ)) := Nat.mul_le_mul_left 2 hD'
      _ = 2 * routeTLogGrowthMeanConstant * U ^ (9 : ℕ) := by ring
  have hmomentSq : routeTLogGrowthMoment u ^ (2 : ℕ) ≤ (B0 * U ^ (3 : ℕ)) ^ (2 : ℕ) :=
    Nat.pow_le_pow_left hB 2
  have hcore : routeTLogGrowthMoment u ^ (2 : ℕ) * routeTLogGrowthOrder u ≤
      B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant * U ^ (7 : ℕ) := by
    calc
      routeTLogGrowthMoment u ^ (2 : ℕ) * routeTLogGrowthOrder u ≤
          (B0 * U ^ (3 : ℕ)) ^ (2 : ℕ) * (routeTLogGrowthOrderConstant * U) :=
        Nat.mul_le_mul hmomentSq hK
      _ = B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant * U ^ (7 : ℕ) := by ring
  have h24 : 24 * routeTLogGrowthMoment u ^ (2 : ℕ) * routeTLogGrowthOrder u ≤
      (24 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) * U ^ (7 : ℕ) := by
    simpa only [mul_assoc] using Nat.mul_le_mul_left 24 hcore
  have h160 : 160 * routeTLogGrowthMoment u ^ (2 : ℕ) * routeTLogGrowthOrder u ≤
      (160 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) * U ^ (7 : ℕ) := by
    simpa only [mul_assoc] using Nat.mul_le_mul_left 160 hcore
  have h12 : 12 * routeTLogGrowthMoment u ^ (2 : ℕ) ≤ (12 * B0 ^ (2 : ℕ)) * U ^ (6 : ℕ) := by
    calc
      12 * routeTLogGrowthMoment u ^ (2 : ℕ) ≤ 12 * (B0 * U ^ (3 : ℕ)) ^ (2 : ℕ) :=
        Nat.mul_le_mul_left 12 hmomentSq
      _ = (12 * B0 ^ (2 : ℕ)) * U ^ (6 : ℕ) := by ring
  unfold routeTLogReceiverPolynomialExponent
  calc
    2 * routeTLogMeanConstantGrowthExponent u +
          24 * routeTLogGrowthMoment u ^ (2 : ℕ) * routeTLogGrowthOrder u +
          160 * routeTLogGrowthMoment u ^ (2 : ℕ) * routeTLogGrowthOrder u +
          (5 + (240 * u + 1) + 202 * (240 * u)) +
          12 * routeTLogGrowthMoment u ^ (2 : ℕ) + 10 ≤
      2 * routeTLogGrowthMeanConstant * U ^ (9 : ℕ) +
          (24 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) * U ^ (7 : ℕ) +
          (160 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) * U ^ (7 : ℕ) +
          (5 + (240 + 1) + 202 * 240) * U +
          (12 * B0 ^ (2 : ℕ)) * U ^ (6 : ℕ) + 10 := by
      omega
    _ ≤ 2 * routeTLogGrowthMeanConstant * U ^ (9 : ℕ) +
          (24 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) * U ^ (9 : ℕ) +
          (160 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) * U ^ (9 : ℕ) +
          (5 + (240 + 1) + 202 * 240) * U ^ (9 : ℕ) +
          (12 * B0 ^ (2 : ℕ)) * U ^ (9 : ℕ) + 10 * U ^ (9 : ℕ) := by
      have h24lift := Nat.mul_le_mul_left
        (24 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) hU79'
      have h160lift := Nat.mul_le_mul_left
        (160 * B0 ^ (2 : ℕ) * routeTLogGrowthOrderConstant) hU79'
      have hwindowLift := Nat.mul_le_mul_left (5 + (240 + 1) + 202 * 240) hU19'
      have h12lift := Nat.mul_le_mul_left (12 * B0 ^ (2 : ℕ)) hU69'
      have hten : 10 ≤ 10 * U ^ (9 : ℕ) := by omega
      omega
    _ = routeTLogReceiverDegreeNineConstant * U ^ (9 : ℕ) := by
      unfold routeTLogReceiverDegreeNineConstant B0
      ring

theorem routeTLogReceiverBaseThreshold_le_degreeNine
    {u : ℕ} (hu : 1 ≤ u) :
    routeTLogReceiverBaseThreshold u ≤
      2 ^ (routeTLogReceiverDegreeNineConstant * (u + 1) ^ (9 : ℕ)) :=
  (routeTLogReceiverBaseThreshold_le_two_pow_polynomial hu).trans
    (Nat.pow_le_pow_right (by omega) (routeTLogReceiverPolynomialExponent_le_degreeNine u))

theorem routeTLogReceiverBaseThreshold_le_nthRoot_of_degreeNine_size
    {u X : ℕ} (hu : 1 ≤ u)
    (hX : 2 ^ (routeTLogCentreExponent *
        (routeTLogReceiverDegreeNineConstant * (u + 1) ^ (9 : ℕ) + 1)) ≤ X) :
    routeTLogReceiverBaseThreshold u + 1 ≤
      Nat.nthRoot routeTLogCentreExponent X := by
  apply routeTLogReceiverBaseThreshold_le_nthRoot_of_polynomial_size hu
  apply (Nat.pow_le_pow_right (by omega) ?_).trans hX
  exact Nat.mul_le_mul_left routeTLogCentreExponent
    (Nat.add_le_add_right (routeTLogReceiverPolynomialExponent_le_degreeNine u) 1)

end

end RHTower.Sieve
