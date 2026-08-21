import GaloisForLFunctions.RHTower.Sieve.MaynardWindowRelevantPacketBound
import GaloisForLFunctions.RHTower.Sieve.MaynardLabelAbsorption
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination
import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketNatOrder

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

open Filter Topology

namespace RHTower.Sieve

noncomputable section

def routeTPrimeGapPacketPolylogConstant : ℝ :=
  (4 * ((2 : ℝ) ^ 120) ^ 2) * 60 * (2 : ℝ) ^ 60

theorem heathBrownWindowRelevantFixedPolylogBound_sixty_comparable
    {x : ℝ} {X : ℕ} (hx : 1 ≤ x) (hX : 1 ≤ X)
    (hXx : (X : ℝ) ≤ 4 * x) :
    heathBrownWindowRelevantFixedPolylogBound X X 60 x 1 ≤
      routeTPrimeGapPacketPolylogConstant *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ 60 *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ 60 *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) *
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ (2 ^ 121 - 1) := by
  let C : ℝ := (2 : ℝ) ^ 120
  let M : ℝ := (((2 ^ 120 * X : ℕ) : ℝ))
  let B : ℝ := 1 + 2 * Real.log M
  let E : ℕ := 2 ^ 121 - 1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hC0 : 0 < C := by dsimp only [C]; positivity
  have hM_eq : M = C * (X : ℝ) := by
    simp only [M, C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hM1 : 1 ≤ M := by
    rw [hM_eq]
    have hC1 : 1 ≤ C := by norm_num [C]
    exact one_le_mul_of_one_le_of_one_le hC1 (by exact_mod_cast hX)
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hB1 : 1 ≤ B := by dsimp only [B]; linarith
  have hnatlog : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ B := by
    calc
      ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 1 + 2 * Real.log X :=
        natLogTwo_add_one_cast_le hX
      _ ≤ 1 + 2 * Real.log M := by
        have hXM : (X : ℝ) ≤ M := by
          rw [hM_eq]
          have hC1 : 1 ≤ C := by norm_num [C]
          nlinarith [show (0 : ℝ) ≤ X by positivity]
        have hlog := Real.log_le_log (by positivity : (0 : ℝ) < X) hXM
        linarith
      _ = B := rfl
  have hcardNat := card_heathBrownBoxChoice_le X X 60
  have hcard :
      (Fintype.card (HeathBrownBoxChoice X X 60) : ℝ) ≤
        60 * B ^ 60 * B ^ 60 := by
    have hcardCast :
        (Fintype.card (HeathBrownBoxChoice X X 60) : ℝ) ≤
          ((60 * (Nat.log 2 X + 1) ^ 60 * (Nat.log 2 X + 1) ^ 60 : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    calc
      (Fintype.card (HeathBrownBoxChoice X X 60) : ℝ) ≤
          ((60 * (Nat.log 2 X + 1) ^ 60 * (Nat.log 2 X + 1) ^ 60 : ℕ) : ℝ) := hcardCast
      _ = 60 * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60) *
          (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60) := by
            simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
              Nat.cast_ofNat]
      _ ≤ 60 * B ^ 60 * B ^ 60 := by
        have hbase0 : 0 ≤ ((Nat.log 2 X + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have hpow : (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60) ≤ B ^ 60 :=
          pow_le_pow_left₀ hbase0 hnatlog 60
        have hA0 : 0 ≤ (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60) := pow_nonneg hbase0 _
        have hB0 : 0 ≤ B ^ 60 := pow_nonneg (zero_le_one.trans hB1) _
        calc
          60 * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60) *
              (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60) ≤
              60 * B ^ 60 * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ 60) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hpow (by norm_num)) hA0
          _ ≤ 60 * B ^ 60 * B ^ 60 := by
                exact mul_le_mul_of_nonneg_left hpow
                  (mul_nonneg (by norm_num) hB0)
  have hlogM : Real.log M ≤ B := by dsimp only [B]; linarith
  have honeLogM : 1 + Real.log M ≤ B := by dsimp only [B]; linarith
  have hratioM : (x / C) ^ (-1 : ℝ) * M ≤ 4 * C ^ 2 := by
    rw [Real.rpow_neg_one]
    have hMupper : M ≤ C * (4 * x) := by
      rw [hM_eq]
      exact mul_le_mul_of_nonneg_left hXx hC0.le
    calc
      (x / C)⁻¹ * M = (C / x) * M := by
        congr 1
        field_simp
      _ ≤ (C / x) * (C * (4 * x)) :=
        mul_le_mul_of_nonneg_left hMupper (by positivity)
      _ = 4 * C ^ 2 := by field_simp
  have hnonnegCard : 0 ≤ (Fintype.card (HeathBrownBoxChoice X X 60) : ℝ) :=
    Nat.cast_nonneg _
  have hnonnegPow60 : 0 ≤ B ^ 60 := pow_nonneg (zero_le_one.trans hB1) _
  have hnonnegE : 0 ≤ B ^ E := pow_nonneg (zero_le_one.trans hB1) _
  have hnonnegOneLog : 0 ≤ 1 + Real.log M := by linarith
  have hpowE : (1 + Real.log M) ^ E ≤ B ^ E :=
    pow_le_pow_left₀ hnonnegOneLog honeLogM E
  have hratio0 : 0 ≤ (x / C) ^ (-1 : ℝ) * M :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg hx0.le hC0.le) _)
      (zero_le_one.trans hM1)
  have hratioUpper0 : 0 ≤ 4 * C ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg C)
  have hcardUpper0 : 0 ≤ 60 * B ^ 60 * B ^ 60 := by positivity
  have htwoPow0 : 0 ≤ (2 : ℝ) ^ 60 := by positivity
  have hac :
      ((x / C) ^ (-1 : ℝ) * M) *
          (Fintype.card (HeathBrownBoxChoice X X 60) : ℝ) ≤
        (4 * C ^ 2) * (60 * B ^ 60 * B ^ 60) :=
    mul_le_mul hratioM hcard hnonnegCard hratioUpper0
  have hacd :
      (((x / C) ^ (-1 : ℝ) * M) *
          (Fintype.card (HeathBrownBoxChoice X X 60) : ℝ)) * (2 : ℝ) ^ 60 ≤
        ((4 * C ^ 2) * (60 * B ^ 60 * B ^ 60)) * (2 : ℝ) ^ 60 :=
    mul_le_mul_of_nonneg_right hac htwoPow0
  have hlp : Real.log M * (1 + Real.log M) ^ E ≤ B * B ^ E :=
    mul_le_mul hlogM hpowE (pow_nonneg hnonnegOneLog _) (zero_le_one.trans hB1)
  have hlp0 : 0 ≤ Real.log M * (1 + Real.log M) ^ E :=
    mul_nonneg hlogM0 (pow_nonneg hnonnegOneLog _)
  have hacdUpper0 :
      0 ≤ ((4 * C ^ 2) * (60 * B ^ 60 * B ^ 60)) * (2 : ℝ) ^ 60 := by
    exact mul_nonneg
      (mul_nonneg hratioUpper0
        (mul_nonneg (mul_nonneg (by norm_num) hnonnegPow60) hnonnegPow60))
      htwoPow0
  simp only [heathBrownWindowRelevantFixedPolylogBound, Nat.reduceMul,
    Nat.reduceAdd, Nat.cast_pow, Nat.cast_ofNat]
  change (x / C) ^ (-1 : ℝ) *
      ((Fintype.card (HeathBrownBoxChoice X X 60) : ℝ) *
        (2 : ℝ) ^ 60 * Real.log M * (M * (1 + Real.log M) ^ E)) ≤
      routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B * B ^ E
  calc
    (x / C) ^ (-1 : ℝ) *
        ((Fintype.card (HeathBrownBoxChoice X X 60) : ℝ) *
          (2 : ℝ) ^ 60 * Real.log M * (M * (1 + Real.log M) ^ E)) =
        ((((x / C) ^ (-1 : ℝ) * M) *
          (Fintype.card (HeathBrownBoxChoice X X 60) : ℝ)) *
          (2 : ℝ) ^ 60) * (Real.log M * (1 + Real.log M) ^ E) := by ac_rfl
    _ ≤ (((4 * C ^ 2) * (60 * B ^ 60 * B ^ 60)) *
          (2 : ℝ) ^ 60) * (B * B ^ E) :=
      mul_le_mul hacd hlp hlp0 hacdUpper0
    _ = routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B * B ^ E := by
      simp only [routeTPrimeGapPacketPolylogConstant, C]
      ac_rfl

/-- Every fixed power of the exact frozen-source logarithmic base is absorbed uniformly over the
canonical Route-T support range `X ≤ T^(8/5)`. -/
theorem eventually_routeTPrimeGapPacketLogBase_pow_absorbed
    (q : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → (X : ℝ) ≤ T ^ (8 / 5 : ℝ) →
        (1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))) ^ q ≤ T ^ eta := by
  let D : ℝ := 4 + 240 * Real.log 2
  have hlogTwo0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hD0 : 0 < D := by dsimp only [D]; nlinarith
  have hdom := eventually_const_mul_rpow_polylog_le_rpow
    (C := D ^ q) (α := (0 : ℝ)) (β := eta) q heta
  filter_upwards [hdom, Filter.eventually_ge_atTop (1 : ℝ)] with T hdomT hT
  intro X hX hXscale
  let C : ℝ := (2 : ℝ) ^ 120
  let M : ℝ := (((2 ^ 120 * X : ℕ) : ℝ))
  let B : ℝ := 1 + 2 * Real.log M
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have habsLogT : |Real.log T| = Real.log T := abs_of_nonneg hlogT0
  have hC0 : 0 < C := by dsimp only [C]; positivity
  have hXR0 : 0 < (X : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hM_eq : M = C * (X : ℝ) := by
    simp only [M, C, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hlogX : Real.log (X : ℝ) ≤ (8 / 5 : ℝ) * Real.log T := by
    have hlog := Real.log_le_log hXR0 hXscale
    rwa [Real.log_rpow hT0] at hlog
  have hlogC : Real.log C = 120 * Real.log 2 := by
    dsimp only [C]
    rw [Real.log_pow]
    norm_num
  have hlogM : Real.log M ≤ 120 * Real.log 2 + (8 / 5 : ℝ) * Real.log T := by
    rw [hM_eq, Real.log_mul hC0.ne' hXR0.ne', hlogC]
    linarith
  have hB : B ≤ D * (1 + |Real.log T|) := by
    rw [habsLogT]
    dsimp only [B, D]
    have hDlog : 0 ≤ (4 + 240 * Real.log 2) * Real.log T :=
      mul_nonneg (by nlinarith) hlogT0
    nlinarith
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    have hM1 : 1 ≤ M := by
      rw [hM_eq]
      exact one_le_mul_of_one_le_of_one_le (by norm_num [C]) (by exact_mod_cast hX)
    linarith [Real.log_nonneg hM1]
  have hpow : B ^ q ≤ (D * (1 + |Real.log T|)) ^ q :=
    pow_le_pow_left₀ hB0 hB q
  have hdomT' : D ^ q * (1 + |Real.log T|) ^ q ≤ T ^ eta := by
    simpa only [Real.rpow_zero, mul_one] using hdomT
  change B ^ q ≤ T ^ eta
  calc
    B ^ q ≤ (D * (1 + |Real.log T|)) ^ q := hpow
    _ = D ^ q * (1 + |Real.log T|) ^ q := mul_pow _ _ _
    _ ≤ T ^ eta := hdomT'

/-- The complete order-60 frozen-source envelope is absorbed by every positive Route-T power,
uniformly over comparable source/support scales. -/
theorem eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_routeT_absorbed
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (x : ℝ) (X : ℕ), 1 ≤ x → 1 ≤ X → (X : ℝ) ≤ 4 * x →
        (X : ℝ) ≤ T ^ (8 / 5 : ℝ) →
        heathBrownWindowRelevantFixedPolylogBound X X 60 x 1 ≤ T ^ eta := by
  let eps : ℝ := eta / 5
  have heps : 0 < eps := by dsimp only [eps]; linarith
  have h60 := eventually_routeTPrimeGapPacketLogBase_pow_absorbed 60 heps
  have h1 := eventually_routeTPrimeGapPacketLogBase_pow_absorbed 1 heps
  have hE := eventually_routeTPrimeGapPacketLogBase_pow_absorbed (2 ^ 121 - 1) heps
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      routeTPrimeGapPacketPolylogConstant ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop routeTPrimeGapPacketPolylogConstant
  filter_upwards [h60, h1, hE, hconst, Filter.eventually_ge_atTop (1 : ℝ)] with
    T h60T h1T hET hconstT hT
  intro x X hx hX hXx hXscale
  let B : ℝ := 1 + 2 * Real.log (((2 ^ 120 * X : ℕ) : ℝ))
  let P : ℝ := T ^ eps
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hB60 : B ^ 60 ≤ P := by simpa only [B, P] using h60T X hX hXscale
  have hB1 : B ≤ P := by simpa only [B, P, pow_one] using h1T X hX hXscale
  have hBE : B ^ (2 ^ 121 - 1) ≤ P := by
    simpa only [B, P] using hET X hX hXscale
  have hM1 : (1 : ℝ) ≤ (((2 ^ 120 * X : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_le_mul (Nat.one_le_two_pow) hX
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    linarith [Real.log_nonneg hM1]
  have hB600 : 0 ≤ B ^ 60 := pow_nonneg hB0 _
  have hBE0 : 0 ≤ B ^ (2 ^ 121 - 1) := pow_nonneg hB0 _
  have hP0 : 0 ≤ P := by dsimp only [P]; exact Real.rpow_nonneg hT0.le _
  have hC0 : 0 ≤ routeTPrimeGapPacketPolylogConstant := by
    unfold routeTPrimeGapPacketPolylogConstant
    positivity
  have h01 : routeTPrimeGapPacketPolylogConstant * B ^ 60 ≤ P * P :=
    mul_le_mul hconstT hB60 hB600 hP0
  have h012 : routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 ≤
      P * P * P :=
    mul_le_mul h01 hB60 hB600 (mul_nonneg hP0 hP0)
  have h0123 : routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B ≤
      P * P * P * P :=
    mul_le_mul h012 hB1 hB0 (mul_nonneg (mul_nonneg hP0 hP0) hP0)
  have hprod :
      routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B *
          B ^ (2 ^ 121 - 1) ≤ P * P * P * P * P :=
    mul_le_mul h0123 hBE hBE0
      (mul_nonneg (mul_nonneg (mul_nonneg hP0 hP0) hP0) hP0)
  calc
    heathBrownWindowRelevantFixedPolylogBound X X 60 x 1 ≤
        routeTPrimeGapPacketPolylogConstant * B ^ 60 * B ^ 60 * B *
          B ^ (2 ^ 121 - 1) := by
      simpa only [B] using
        heathBrownWindowRelevantFixedPolylogBound_sixty_comparable hx hX hXx
    _ ≤ P * P * P * P * P := hprod
    _ = P ^ 5 := by ring
    _ = T ^ (eps * 5) := by
      dsimp only [P]
      rw [← Real.rpow_natCast (T ^ eps) 5, ← Real.rpow_mul hT0.le]
      norm_num
    _ = T ^ eta := by
      congr 1
      dsimp only [eps]
      ring

/-- At the strict split `theta = 31/80`, Mellin order `50` beats the natural equation-(111)
cutoff `floor T` by the exact power `T^(-1/50)`, up to the fixed floor constant. -/
theorem routeTPrimeGapPacket_orderFifty_power_bound
    {T lambda : ℝ} (hT : 2 ≤ T) (hlambda0 : 0 < lambda)
    (hlambda : lambda ≤ T ^ (8 / 5 : ℝ)) :
    (1 / lambda ^ (-(49 / 80 : ℝ))) ^ (51 : ℕ) *
        ((⌊T⌋₊ : ℕ) : ℝ) ^ (-(50 : ℝ)) ≤
      (2 : ℝ) ^ (50 : ℝ) * T ^ (-(1 / 50 : ℝ)) := by
  have hT0 : 0 < T := by linarith
  have hfloorLower : T / 2 ≤ ((⌊T⌋₊ : ℕ) : ℝ) := by
    have hlt := Nat.lt_floor_add_one T
    linarith
  have hhalf0 : 0 < T / 2 := by positivity
  have hfloor0 : 0 < ((⌊T⌋₊ : ℕ) : ℝ) := hhalf0.trans_le hfloorLower
  have hfloorPow : ((⌊T⌋₊ : ℕ) : ℝ) ^ (-(50 : ℝ)) ≤
      (T / 2) ^ (-(50 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hhalf0 hfloorLower (by norm_num)
  have hwidthInv : 1 / lambda ^ (-(49 / 80 : ℝ)) =
      lambda ^ (49 / 80 : ℝ) := by
    rw [Real.rpow_neg hlambda0.le]
    field_simp
  have hlambdaPow :
      (lambda ^ (49 / 80 : ℝ)) ^ (51 : ℕ) ≤ T ^ (2499 / 50 : ℝ) := by
    rw [← Real.rpow_mul_natCast hlambda0.le]
    have hmono := Real.rpow_le_rpow hlambda0.le hlambda
      (by norm_num : (0 : ℝ) ≤ (49 / 80 : ℝ) * (51 : ℕ))
    calc
      lambda ^ ((49 / 80 : ℝ) * (51 : ℕ)) ≤
          (T ^ (8 / 5 : ℝ)) ^ ((49 / 80 : ℝ) * (51 : ℕ)) := hmono
      _ = T ^ (2499 / 50 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        congr 1
        norm_num
  have hhalfPow : (T / 2) ^ (-(50 : ℝ)) =
      (2 : ℝ) ^ (50 : ℝ) * T ^ (-(50 : ℝ)) := by
    rw [Real.div_rpow hT0.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg hT0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  rw [hwidthInv]
  calc
    (lambda ^ (49 / 80 : ℝ)) ^ (51 : ℕ) *
        ((⌊T⌋₊ : ℕ) : ℝ) ^ (-(50 : ℝ)) ≤
      T ^ (2499 / 50 : ℝ) * (T / 2) ^ (-(50 : ℝ)) :=
        mul_le_mul hlambdaPow hfloorPow
          (Real.rpow_nonneg hfloor0.le _) (Real.rpow_nonneg hT0.le _)
    _ = (2 : ℝ) ^ (50 : ℝ) *
        (T ^ (2499 / 50 : ℝ) * T ^ (-(50 : ℝ))) := by
      rw [hhalfPow]
      ac_rfl
    _ = (2 : ℝ) ^ (50 : ℝ) * T ^ (-(1 / 50 : ℝ)) := by
      congr 1
      rw [← Real.rpow_add hT0]
      congr 1
      norm_num

def routeTPrimeGapPacketBase (T : ℝ) : ℝ := T ^ (8 / 5 : ℝ) / 4

def routeTPrimeGapPacketSupport (T : ℝ) : ℕ :=
  ⌈3 * routeTPrimeGapPacketBase T⌉₊

def routeTPrimeGapPacketWidth (lambda : ℝ) : ℝ :=
  lambda ^ (-(49 / 80 : ℝ))

def routeTPrimeGapPacketCutoff (T : ℝ) : ℕ := ⌊T⌋₊

/-- The exact order-50 tail inequality required by O9 is automatic on the strict-gap schedule.
This keeps the literal equation-(111) cutoff `floor T`; no outer-frequency enlargement is used. -/
theorem eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T),
        heathBrownWindowRelevantFixedPolylogBound
              (routeTPrimeGapPacketSupport T) (routeTPrimeGapPacketSupport T) 60
              (routeTPrimeGapPacketBase T) 1 *
            (C * (1 / routeTPrimeGapPacketWidth lambda) ^ (51 : ℕ) *
              (routeTPrimeGapPacketCutoff T : ℝ) ^ (-(50 : ℝ))) ≤
          ((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
            (2 * (1 +
              Real.log ((1 / 4) / routeTPrimeGapPacketWidth lambda) / Real.log 2)) := by
  let A : ℝ := (2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)
  let Dq : ℝ := 2 + 1 / Real.log 2
  have hA : 0 < A := by
    dsimp only [A]
    positivity [routeTSmoothWindowCentralMargin_pos]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDq : 0 < Dq := by dsimp only [Dq]; positivity
  have hPevent :=
    eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_routeT_absorbed
      (by norm_num : (0 : ℝ) < 1 / 400)
  have hbaseTop : Filter.Tendsto routeTPrimeGapPacketBase Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in Filter.atTop, 16 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 16
  have hwidthSmall : ∀ᶠ T : ℝ in Filter.atTop,
      (routeTPrimeGapPacketBase T) ^ (-(49 / 80 : ℝ)) ≤ 1 / 4 := by
    have hlim := (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 49 / 80)).comp hbaseTop
    exact Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4) hlim
  let Nconst : ℝ :=
    (C * (2 : ℝ) ^ (50 : ℝ)) * (2 * Dq) / A
  have hdom := eventually_const_mul_rpow_polylog_le_rpow
    (C := Nconst) (α := (-(7 / 400 : ℝ))) (β := (0 : ℝ)) 1 (by norm_num)
  filter_upwards [hPevent, hbaseLarge, hwidthSmall, hdom,
    Filter.eventually_ge_atTop (2 : ℝ)] with T hPT hbase16 hwidthBase hdomT hT
  intro lambda hlambda
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let H0 : ℝ := routeTPrimeGapPacketWidth lambda
  let K : ℕ := routeTPrimeGapPacketCutoff T
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound X X 60 x 1
  let Q : ℝ := 1 + Real.log ((1 / 4) / H0) / Real.log 2
  have hT0 : 0 < T := by linarith
  have hTpow0 : 0 < T ^ (8 / 5 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hx0 : 0 < x := by dsimp only [x, routeTPrimeGapPacketBase]; positivity
  have hx1 : 1 ≤ x := by
    dsimp only [x] at hbase16 ⊢
    linarith
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 3 * x + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hXx : (X : ℝ) ≤ 4 * x := by linarith
  have hxscale : 4 * x = T ^ (8 / 5 : ℝ) := by
    dsimp only [x, routeTPrimeGapPacketBase]
    field_simp
  have hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ) := by
    rw [← hxscale]
    exact hXx
  have hP : P ≤ T ^ (1 / 400 : ℝ) := by
    exact hPT x X hx1 hX hXx hXscale
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact (norm_nonneg
      (heathBrownWindowRelevantEligibleDyadicAggregate X X 60 2 0 x
        ((1 : ℂ) + (0 : ℝ) * Complex.I))).trans
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        X X 60 hX 2 0 x 1 0 hx0 (by norm_num))
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hH0 : 0 < H0 := by
    dsimp only [H0, routeTPrimeGapPacketWidth]
    positivity
  have hlambdaScale : lambda ≤ T ^ (8 / 5 : ℝ) := by
    calc
      lambda ≤ 2 * x := hlambda.2
      _ ≤ 4 * x := by linarith [hx0]
      _ = T ^ (8 / 5 : ℝ) := hxscale
  have hpower := routeTPrimeGapPacket_orderFifty_power_bound hT hlambda0 hlambdaScale
  have hpower' :
      (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ)) ≤
        (2 : ℝ) ^ (50 : ℝ) * T ^ (-(1 / 50 : ℝ)) := by
    simpa only [H0, K, routeTPrimeGapPacketWidth, routeTPrimeGapPacketCutoff] using hpower
  have hpower0 : 0 ≤ (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ)) := by
    exact mul_nonneg (pow_nonneg (one_div_nonneg.mpr hH0.le) _)
      (Real.rpow_nonneg (Nat.cast_nonneg K) _)
  have hpowerUpper0 : 0 ≤
      (2 : ℝ) ^ (50 : ℝ) * T ^ (-(1 / 50 : ℝ)) := by positivity
  have hCP : C * P ≤ C * T ^ (1 / 400 : ℝ) :=
    mul_le_mul_of_nonneg_left hP hC
  have htailRaw :
      P * (C * (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ))) ≤
        C * (2 : ℝ) ^ (50 : ℝ) * T ^ (-(7 / 400 : ℝ)) := by
    calc
      P * (C * (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ))) =
          (C * P) * ((1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ))) := by ac_rfl
      _ ≤ (C * T ^ (1 / 400 : ℝ)) *
          ((2 : ℝ) ^ (50 : ℝ) * T ^ (-(1 / 50 : ℝ))) :=
        mul_le_mul hCP hpower' hpower0
          (mul_nonneg hC (Real.rpow_nonneg hT0.le _))
      _ = C * (2 : ℝ) ^ (50 : ℝ) * T ^ (-(7 / 400 : ℝ)) := by
        rw [show (-(7 / 400 : ℝ)) = (1 / 400 : ℝ) + (-(1 / 50 : ℝ)) by norm_num,
          Real.rpow_add hT0]
        ac_rfl
  have hH0quarter : H0 ≤ 1 / 4 := by
    have hanti := Real.rpow_le_rpow_of_nonpos hx0 hlambda.1
      (by norm_num : (-(49 / 80 : ℝ)) ≤ 0)
    dsimp only [H0, routeTPrimeGapPacketWidth]
    exact hanti.trans (by simpa only [x] using hwidthBase)
  have hratioOne : 1 ≤ (1 / 4) / H0 :=
    (le_div_iff₀ hH0).2 (by simpa using hH0quarter)
  have hlogRatio0 : 0 ≤ Real.log ((1 / 4) / H0) := Real.log_nonneg hratioOne
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hlogLambda : Real.log lambda ≤ (8 / 5 : ℝ) * Real.log T := by
    have hlog := Real.log_le_log hlambda0 hlambdaScale
    rwa [Real.log_rpow hT0] at hlog
  have hlogQuarter : Real.log (1 / 4 : ℝ) ≤ 0 :=
    Real.log_nonpos (by norm_num) (by norm_num)
  have hlogH0 : Real.log H0 = (-(49 / 80 : ℝ)) * Real.log lambda := by
    dsimp only [H0, routeTPrimeGapPacketWidth]
    rw [Real.log_rpow hlambda0]
  have hlogRatio :
      Real.log ((1 / 4) / H0) ≤ (49 / 50 : ℝ) * Real.log T := by
    rw [Real.log_div (by norm_num : (1 / 4 : ℝ) ≠ 0) hH0.ne', hlogH0]
    nlinarith
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogRatio' : Real.log ((1 / 4) / H0) ≤ Real.log T := by
    nlinarith
  have hQsimple : Q ≤ 1 + (1 / Real.log 2) * Real.log T := by
    dsimp only [Q]
    have hdiv := (div_le_div_iff_of_pos_right hlogTwo).2 hlogRatio'
    calc
      1 + Real.log ((1 / 4) / H0) / Real.log 2 ≤
          1 + Real.log T / Real.log 2 := by
        simpa only [add_comm] using add_le_add_left hdiv 1
      _ = 1 + (1 / Real.log 2) * Real.log T := by ring
  have habsLogT : |Real.log T| = Real.log T := abs_of_nonneg hlogT0
  have hQbound : Q ≤ Dq * (1 + |Real.log T|) := by
    calc
      Q ≤ 1 + (1 / Real.log 2) * Real.log T := hQsimple
      _ ≤ Dq * (1 + |Real.log T|) := by
        rw [habsLogT]
        have hinv0 : 0 ≤ 1 / Real.log 2 := one_div_nonneg.mpr hlogTwo.le
        dsimp only [Dq]
        nlinarith
  have htailQ :
      (P * (C * (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ)))) *
          (2 * Q) ≤
        (C * (2 : ℝ) ^ (50 : ℝ) * T ^ (-(7 / 400 : ℝ))) *
          (2 * (Dq * (1 + |Real.log T|))) := by
    exact mul_le_mul htailRaw (mul_le_mul_of_nonneg_left hQbound (by norm_num))
      (mul_nonneg (by norm_num) hQ.le)
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
        (Real.rpow_nonneg hT0.le _))
  have hdomT' :
      Nconst * T ^ (-(7 / 400 : ℝ)) * (1 + |Real.log T|) ≤ 1 := by
    simpa only [Real.rpow_zero, pow_one] using hdomT
  have hscaled :
      (C * (2 : ℝ) ^ (50 : ℝ) * T ^ (-(7 / 400 : ℝ))) *
          (2 * (Dq * (1 + |Real.log T|))) ≤ A := by
    calc
      (C * (2 : ℝ) ^ (50 : ℝ) * T ^ (-(7 / 400 : ℝ))) *
          (2 * (Dq * (1 + |Real.log T|))) =
        A * (Nconst * T ^ (-(7 / 400 : ℝ)) * (1 + |Real.log T|)) := by
          dsimp only [Nconst]
          field_simp
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hdomT' hA.le
      _ = A := mul_one A
  have hcross :
      (P * (C * (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ)))) *
          (2 * Q) ≤ A := htailQ.trans hscaled
  have hcut :
      P * (C * (1 / H0) ^ (51 : ℕ) * (K : ℝ) ^ (-(50 : ℝ))) ≤
        A / (2 * Q) := (le_div_iff₀ (mul_pos (by norm_num) hQ)).2 hcross
  simpa only [P, X, x, H0, K, Q, A] using hcut

/-- On the strict-gap schedule, the order-50 proportional prime-free packet theorem has no
remaining analytic cutoff hypothesis.  The only input left is the literal prime-free interval. -/
theorem exists_eventually_routeT_strictGapSplit_primeFree_large_range_packet :
    ∃ C50 : ℝ, 1 ≤ C50 ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
            (2 * routeTPrimeGapPacketBase T),
          Chebyshev.theta
                (lambda + 2 * (lambda * routeTPrimeGapPacketWidth lambda)) -
              Chebyshev.theta lambda = 0 →
          ∃ J : ℕ, 0 < J ∧
            (((2 ^ (J - 1) : ℕ) : ℝ)) ≤
                (1 / 4) / routeTPrimeGapPacketWidth lambda ∧
            ∃ j ∈ Finset.range J,
              (((2 * Real.pi) * (routeTSmoothWindowCentralMargin / 4)) /
                  (J : ℝ)) / 8 ≤
                ‖maynardFixedAmbientPhysicalDefectPacket
                    (Finset.range (routeTPrimeGapPacketCutoff T))
                    (fun y : ℝ ↦
                      heathBrownWindowRelevantEligibleDyadicAggregate
                        (routeTPrimeGapPacketSupport T)
                        (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                        (routeTPrimeGapPacketBase T)
                        ((1 : ℂ) + (y : ℝ) * Complex.I))
                    lambda 1
                    (routeTComparableWidthLadder
                      (routeTPrimeGapPacketWidth lambda) (1 / 4) j)
                    (routeTComparableWidthLadder
                      (routeTPrimeGapPacketWidth lambda) (1 / 4) (j + 1)) 1‖ := by
  obtain ⟨C50, hC50, hpacket⟩ :=
    exists_eventually_routeT_proportional_primeFree_large_range_packet_natOrder
      50 (by norm_num) (theta := (31 / 80 : ℝ)) (by norm_num)
  refine ⟨C50, hC50, ?_⟩
  obtain ⟨lambda0, hlambda0⟩ := Filter.eventually_atTop.1 hpacket
  have hbaseTop :
      Filter.Tendsto routeTPrimeGapPacketBase Filter.atTop Filter.atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseThreshold : ∀ᶠ T : ℝ in Filter.atTop,
      lambda0 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop lambda0
  have hbaseLarge : ∀ᶠ T : ℝ in Filter.atTop,
      16 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 16
  have hwidthSmall : ∀ᶠ T : ℝ in Filter.atTop,
      (routeTPrimeGapPacketBase T) ^ (-(49 / 80 : ℝ)) ≤ 1 / 4 := by
    have hlim := (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 49 / 80)).comp hbaseTop
    exact Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4) hlim
  have hscale : ∀ᶠ T : ℝ in Filter.atTop,
      4 * (((2 ^ 120 : ℕ) : ℝ)) ≤ T ^ (119 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 119 / 75)).eventually_ge_atTop
      (4 * (((2 ^ 120 : ℕ) : ℝ)))
  have hcut := eventually_routeTPrimeGapPacket_orderFifty_scalar_cutoff C50
    (zero_le_one.trans hC50)
  filter_upwards [hbaseThreshold, hbaseLarge, hwidthSmall, hscale, hcut,
    Filter.eventually_ge_atTop (2 : ℝ)] with T hthreshold hbase16 hwidthBase
      hscaleT hcutT hT
  intro lambda hlambda hprimeFree
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let H0 : ℝ := routeTPrimeGapPacketWidth lambda
  let K : ℕ := routeTPrimeGapPacketCutoff T
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hx1 : 1 ≤ x := by
    dsimp only [x] at hbase16 ⊢
    linarith
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hlambdaPos : 0 < lambda := hx0.trans_le hlambda.1
  have hH0 : 0 < H0 := by
    dsimp only [H0, routeTPrimeGapPacketWidth]
    positivity
  have hH0quarter : H0 ≤ 1 / 4 := by
    have hanti := Real.rpow_le_rpow_of_nonpos hx0 hlambda.1
      (by norm_num : (-(49 / 80 : ℝ)) ≤ 0)
    dsimp only [H0, routeTPrimeGapPacketWidth]
    exact hanti.trans (by simpa only [x] using hwidthBase)
  have hfloorLower : T / 2 ≤ (K : ℝ) := by
    have hlt := Nat.lt_floor_add_one T
    dsimp only [K, routeTPrimeGapPacketCutoff]
    linarith
  have hKreal : (0 : ℝ) < (K : ℝ) := by
    exact (by positivity : (0 : ℝ) < T / 2).trans_le hfloorLower
  have hK : 0 < K := by exact_mod_cast hKreal
  have hXL : X < (X + 1) ^ (60 : ℕ) := by
    exact (Nat.lt_succ_self X).trans_le (Nat.le_pow (by omega))
  have hscaleLambda :
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) ≤ lambda := by
    have hmul :
        (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) ≤
          T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hscaleT
        (div_nonneg (Real.rpow_nonneg hT0.le (1 / 75 : ℝ))
          (by norm_num : (0 : ℝ) ≤ 4))
    calc
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) =
          (4 * (((2 ^ 120 : ℕ) : ℝ))) *
            (T ^ (1 / 75 : ℝ) / 4) := by norm_num; ring
      _ ≤ T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) := hmul
      _ = T ^ (8 / 5 : ℝ) / 4 := by
        rw [show T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) =
          (T ^ (119 / 75 : ℝ) * T ^ (1 / 75 : ℝ)) / 4 by ring,
          ← Real.rpow_add hT0]
        congr 2
        norm_num
      _ = x := by rfl
      _ ≤ lambda := hlambda.1
  have hpower : lambda ^ (31 / 80 : ℝ) ≤ lambda * H0 := by
    have heq : lambda ^ (31 / 80 : ℝ) = lambda * H0 := by
      dsimp only [H0, routeTPrimeGapPacketWidth]
      calc
        lambda ^ (31 / 80 : ℝ) = lambda ^ (1 + (-(49 / 80 : ℝ))) := by
          congr 1
          norm_num
        _ = lambda ^ (1 : ℝ) * lambda ^ (-(49 / 80 : ℝ)) :=
          Real.rpow_add hlambdaPos 1 (-(49 / 80 : ℝ))
        _ = lambda * lambda ^ (-(49 / 80 : ℝ)) := by rw [Real.rpow_one]
    exact heq.le
  have hsupport : lambda + 2 * (lambda / 4) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda / 4) = (3 / 2 : ℝ) * lambda := by ring
      _ ≤ (3 / 2 : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left hlambda.2 (by norm_num)
      _ = 3 * x := by ring
      _ ≤ (X : ℝ) := hceilLower
  have hpacketLambda := hlambda0 lambda (hthreshold.trans hlambda.1)
  have hresult := hpacketLambda X X 60 K hX hx0 hlambda hH0 hH0quarter hK hXL
    (by linarith : (1 : ℝ) < T) hscaleLambda hpower hsupport
    (hcutT lambda hlambda) hprimeFree
  simpa only [x, X, H0, K] using hresult

end

end RHTower.Sieve
