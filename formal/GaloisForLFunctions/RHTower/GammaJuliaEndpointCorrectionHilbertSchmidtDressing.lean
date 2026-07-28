import GaloisForLFunctions.RHTower.GammaSewnJuliaRectangularDivisorTransgression
import GaloisForLFunctions.RHTower.XiPhysicalEndpointValuationCorrectionOddShuttle
import GaloisForLFunctions.HTGeometry.HilbertSchmidt
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization

/-!
# Gamma--Julia endpoint-correction Hilbert--Schmidt dressing

The critical arithmetic Julia normal coordinate has the observer-free Suzuki wall amplitude as
its boundary face.  Relative to the square of that singular wall coordinate, the complete
physical-endpoint valuation correction is one explicit diagonal multiplier.

The multiplier is nonzero on every prime-power clock, positive only at valuation depth zero,
negative at every higher depth, and has sharp squared norm `1 / 2`.  Its squares are summable on
the full prime-power diagram, while its absolute values are not.  Thus it is the diagonal of an
injective Hilbert--Schmidt, non-trace-class strict contraction.

Half-dressing the raw critical wall by the absolute multiplier produces an honest square-summable
source amplitude.  Pointwise in height, the signed dressed wall square is exactly the previously
constructed physical endpoint correction atom, including its full prime-power phase.

No Xi zero, RH premise, target-selected factorization, estimate, or numerical computation enters.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Critical Julia wall half-weight at one prime-power clock. -/
def gammaJuliaEndpointHalfWeight (p : Nat.Primes) (e : ℕ) : ℝ :=
  (Real.sqrt (p : ℝ))⁻¹ ^ (e + 1)

/-- Exact diagonal multiplier from the critical Julia wall mass to the physical endpoint
correction.  The ordinary-prime layer is positive; every higher valuation layer is negative. -/
def gammaJuliaEndpointCorrectionMultiplier
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  if e = 0 then
    2 * gammaJuliaEndpointHalfWeight p e * (p : ℝ)⁻¹
  else
    gammaJuliaEndpointHalfWeight p e *
      (2 * ((p : ℝ)⁻¹) ^ (e + 1) - 1)

/-- Squaring the critical half-weight returns the full inverse prime-power weight. -/
theorem gammaJuliaEndpointHalfWeight_sq
    (p : Nat.Primes) (e : ℕ) :
    gammaJuliaEndpointHalfWeight p e ^ 2 =
      ((p : ℝ)⁻¹) ^ (e + 1) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hr2 : (Real.sqrt (p : ℝ))⁻¹ ^ 2 = (p : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hp.le]
  unfold gammaJuliaEndpointHalfWeight
  rw [← pow_mul, show (e + 1) * 2 = 2 * (e + 1) by omega, pow_mul, hr2]

/-- The square of the observer-free wall amplitude is `log p` times the Julia half-weight. -/
theorem sq_suzukiCriticalEntryWallBareAmplitude_eq_log_mul_halfWeight
    (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEntryWallBareAmplitude p e ^ 2 =
      Real.log (p : ℝ) * gammaJuliaEndpointHalfWeight p e := by
  rw [sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  have hvm :
      ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) =
        Real.log (p : ℝ) := by
    simpa only [xiGammaEulerValuationNat] using
      vonMangoldt_prime_pow_succ_eq_log (p, e)
  rw [hvm]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hsqrtpow :
      Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) =
        Real.sqrt (p : ℝ) ^ (e + 1) := by
    rw [xiGammaEulerValuationNat]
    push_cast
    rw [HilbertSchmidt.sqrt_pow_nonneg _ hp.le]
  rw [hsqrtpow]
  unfold gammaJuliaEndpointHalfWeight
  rw [inv_pow]
  field_simp

/-- **Arithmetic Julia endpoint-correction factorization.**  Every clocked physical endpoint
correction coefficient is the critical Julia wall mass times the explicit diagonal multiplier. -/
theorem gammaJuliaEndpointCorrection_factorization
    (p : Nat.Primes) (e : ℕ) :
    Real.log (p : ℝ) * xiPhysicalEndpointValuationCorrection p e =
      suzukiCriticalEntryWallBareAmplitude p e ^ 2 *
        gammaJuliaEndpointCorrectionMultiplier p e := by
  rw [sq_suzukiCriticalEntryWallBareAmplitude_eq_log_mul_halfWeight]
  by_cases he : e = 0
  · subst e
    rw [xiPhysicalEndpointValuationCorrection_zero]
    simp [gammaJuliaEndpointCorrectionMultiplier]
    rw [show
      Real.log (p : ℝ) * gammaJuliaEndpointHalfWeight p 0 *
          (2 * gammaJuliaEndpointHalfWeight p 0 * (p : ℝ)⁻¹) =
        Real.log (p : ℝ) * 2 *
          gammaJuliaEndpointHalfWeight p 0 ^ 2 * (p : ℝ)⁻¹ by ring,
      gammaJuliaEndpointHalfWeight_sq]
    rw [inv_pow]
    ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    rw [xiPhysicalEndpointValuationCorrection_succ]
    simp only [gammaJuliaEndpointCorrectionMultiplier, Nat.succ_ne_zero,
      if_false]
    rw [show
      Real.log (p : ℝ) * gammaJuliaEndpointHalfWeight p k.succ *
          (gammaJuliaEndpointHalfWeight p k.succ *
            (2 * (p : ℝ)⁻¹ ^ (k.succ + 1) - 1)) =
        Real.log (p : ℝ) * gammaJuliaEndpointHalfWeight p k.succ ^ 2 *
          (2 * (p : ℝ)⁻¹ ^ (k.succ + 1) - 1) by ring,
      gammaJuliaEndpointHalfWeight_sq]
    simp only [Nat.succ_eq_add_one]
    rw [show 2 * (k + 1 + 1) = (k + 2) + (k + 2) by omega, pow_add]
    ring

private theorem gammaJulia_inversePrime_pos (p : Nat.Primes) :
    0 < ((p : ℝ)⁻¹) := by
  exact inv_pos.mpr (by exact_mod_cast p.2.pos)

private theorem gammaJulia_inversePrime_le_half (p : Nat.Primes) :
    ((p : ℝ)⁻¹) ≤ 1 / 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  rw [inv_eq_one_div, div_le_iff₀ hp0]
  nlinarith

theorem gammaJuliaEndpointHalfWeight_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < gammaJuliaEndpointHalfWeight p e := by
  unfold gammaJuliaEndpointHalfWeight
  exact pow_pos (inv_pos.mpr
    (Real.sqrt_pos.mpr (by exact_mod_cast p.2.pos))) _

/-- The ordinary-prime multiplier is strictly positive. -/
theorem gammaJuliaEndpointCorrectionMultiplier_zero_pos
    (p : Nat.Primes) :
    0 < gammaJuliaEndpointCorrectionMultiplier p 0 := by
  rw [gammaJuliaEndpointCorrectionMultiplier, if_pos rfl]
  exact mul_pos (mul_pos (by norm_num) (gammaJuliaEndpointHalfWeight_pos p 0))
    (gammaJulia_inversePrime_pos p)

/-- Every higher-valuation multiplier is strictly negative. -/
theorem gammaJuliaEndpointCorrectionMultiplier_succ_neg
    (p : Nat.Primes) (e : ℕ) :
    gammaJuliaEndpointCorrectionMultiplier p (e + 1) < 0 := by
  rw [gammaJuliaEndpointCorrectionMultiplier, if_neg (by omega)]
  have hq0 := (gammaJulia_inversePrime_pos p).le
  have hq1 : ((p : ℝ)⁻¹) ≤ 1 :=
    (gammaJulia_inversePrime_le_half p).trans (by norm_num)
  have hpow :
      ((p : ℝ)⁻¹) ^ ((e + 1) + 1) ≤ ((p : ℝ)⁻¹) ^ 2 :=
    pow_le_pow_of_le_one hq0 hq1 (by omega)
  have hq2 : ((p : ℝ)⁻¹) ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_nonneg ((p : ℝ)⁻¹ - 1 / 2),
      gammaJulia_inversePrime_le_half p]
  exact mul_neg_of_pos_of_neg (gammaJuliaEndpointHalfWeight_pos p (e + 1))
    (by nlinarith)

/-- The compact dressing loses no prime-power clock coordinate algebraically. -/
theorem gammaJuliaEndpointCorrectionMultiplier_ne_zero
    (p : Nat.Primes) (e : ℕ) :
    gammaJuliaEndpointCorrectionMultiplier p e ≠ 0 := by
  rcases e with _ | e
  · exact (gammaJuliaEndpointCorrectionMultiplier_zero_pos p).ne'
  · exact (gammaJuliaEndpointCorrectionMultiplier_succ_neg p e).ne

/-- Every multiplier has squared modulus at most `1 / 2`. -/
theorem gammaJuliaEndpointCorrectionMultiplier_sq_le_half
    (p : Nat.Primes) (e : ℕ) :
    gammaJuliaEndpointCorrectionMultiplier p e ^ 2 ≤ 1 / 2 := by
  let q : ℝ := (p : ℝ)⁻¹
  have hq0 : 0 ≤ q := (gammaJulia_inversePrime_pos p).le
  have hqhalf : q ≤ 1 / 2 := gammaJulia_inversePrime_le_half p
  rcases e with _ | e
  · rw [gammaJuliaEndpointCorrectionMultiplier, if_pos rfl]
    have hhalfSq := gammaJuliaEndpointHalfWeight_sq p 0
    change (2 * gammaJuliaEndpointHalfWeight p 0 * q) ^ 2 ≤ 1 / 2
    have hq3 : q ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hq0 hqhalf 3
    rw [show
      (2 * gammaJuliaEndpointHalfWeight p 0 * q) ^ 2 =
        4 * gammaJuliaEndpointHalfWeight p 0 ^ 2 * q ^ 2 by ring,
      hhalfSq]
    simp only [Nat.zero_add, pow_one]
    change 4 * q * q ^ 2 ≤ 1 / 2
    nlinarith
  · rw [gammaJuliaEndpointCorrectionMultiplier, if_neg (by omega)]
    let z : ℝ := q ^ (e + 2)
    have hz0 : 0 ≤ z := pow_nonneg hq0 _
    have hzquarter : z ≤ 1 / 4 := by
      have hq1 : q ≤ 1 := hqhalf.trans (by norm_num)
      have hpow : q ^ (e + 2) ≤ q ^ 2 :=
        pow_le_pow_of_le_one hq0 hq1 (by omega)
      have hq2raw := pow_le_pow_left₀ hq0 hqhalf 2
      have hq2 : q ^ 2 ≤ 1 / 4 := by
        norm_num at hq2raw ⊢
        exact hq2raw
      exact hpow.trans hq2
    have hz1 : z ≤ 1 := hzquarter.trans (by norm_num)
    have hfactor : (2 * z - 1) ^ 2 ≤ 1 := by
      have hzmul : 0 ≤ z * (1 - z) :=
        mul_nonneg hz0 (sub_nonneg.mpr hz1)
      nlinarith
    have hhalfSq := gammaJuliaEndpointHalfWeight_sq p (e + 1)
    change
      (gammaJuliaEndpointHalfWeight p (e + 1) *
          (2 * q ^ (e + 2) - 1)) ^ 2 ≤ 1 / 2
    rw [show
      (gammaJuliaEndpointHalfWeight p (e + 1) *
          (2 * q ^ (e + 2) - 1)) ^ 2 =
        gammaJuliaEndpointHalfWeight p (e + 1) ^ 2 *
          (2 * q ^ (e + 2) - 1) ^ 2 by ring,
      hhalfSq]
    change z * (2 * z - 1) ^ 2 ≤ 1 / 2
    calc
      z * (2 * z - 1) ^ 2 ≤ z * 1 :=
        mul_le_mul_of_nonneg_left hfactor hz0
      _ ≤ 1 / 2 := by linarith

/-- Prime two at depth zero attains the sharp squared multiplier norm `1 / 2`. -/
theorem gammaJuliaEndpointCorrectionMultiplier_two_zero_sq :
    gammaJuliaEndpointCorrectionMultiplier ⟨2, Nat.prime_two⟩ 0 ^ 2 =
      1 / 2 := by
  rw [gammaJuliaEndpointCorrectionMultiplier, if_pos rfl]
  change
    (2 * gammaJuliaEndpointHalfWeight ⟨2, Nat.prime_two⟩ 0 *
      (2 : ℝ)⁻¹) ^ 2 = 1 / 2
  rw [show
    (2 * gammaJuliaEndpointHalfWeight ⟨2, Nat.prime_two⟩ 0 * (2 : ℝ)⁻¹) ^ 2 =
      gammaJuliaEndpointHalfWeight ⟨2, Nat.prime_two⟩ 0 ^ 2 by ring]
  rw [gammaJuliaEndpointHalfWeight_sq]
  norm_num

/-- A summable pointwise majorant for the squared multiplier. -/
def gammaJuliaEndpointCorrectionMultiplierSqMajorant
    (pe : Nat.Primes × ℕ) : ℝ :=
  if pe.2 = 0 then
    4 * ((pe.1 : ℝ)⁻¹) ^ 3
  else
    ((pe.1 : ℝ)⁻¹) ^ (pe.2 + 1)

theorem gammaJuliaEndpointCorrectionMultiplier_sq_le_majorant
    (pe : Nat.Primes × ℕ) :
    gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2 ^ 2 ≤
      gammaJuliaEndpointCorrectionMultiplierSqMajorant pe := by
  rcases pe with ⟨p, _ | e⟩
  · rw [gammaJuliaEndpointCorrectionMultiplierSqMajorant, if_pos rfl,
      gammaJuliaEndpointCorrectionMultiplier, if_pos rfl]
    rw [show
      (2 * gammaJuliaEndpointHalfWeight p 0 * (p : ℝ)⁻¹) ^ 2 =
        4 * gammaJuliaEndpointHalfWeight p 0 ^ 2 *
          ((p : ℝ)⁻¹) ^ 2 by ring,
      gammaJuliaEndpointHalfWeight_sq]
    norm_num
    ring_nf
    exact le_rfl
  · rw [gammaJuliaEndpointCorrectionMultiplierSqMajorant, if_neg (by omega),
      gammaJuliaEndpointCorrectionMultiplier, if_neg (by omega)]
    let q : ℝ := (p : ℝ)⁻¹
    let z : ℝ := q ^ (e + 2)
    have hq0 : 0 ≤ q := (gammaJulia_inversePrime_pos p).le
    have hq1 : q ≤ 1 :=
      (gammaJulia_inversePrime_le_half p).trans (by norm_num)
    have hz0 : 0 ≤ z := pow_nonneg hq0 _
    have hz1 : z ≤ 1 := by
      exact
        (pow_le_pow_of_le_one hq0 hq1 (by omega : 1 ≤ e + 2)).trans
          (by simpa using hq1)
    have hfactor : (2 * z - 1) ^ 2 ≤ 1 := by
      have hzmul : 0 ≤ z * (1 - z) :=
        mul_nonneg hz0 (sub_nonneg.mpr hz1)
      nlinarith
    rw [show
      (gammaJuliaEndpointHalfWeight p (e + 1) *
          (2 * (p : ℝ)⁻¹ ^ (e + 2) - 1)) ^ 2 =
        gammaJuliaEndpointHalfWeight p (e + 1) ^ 2 *
          (2 * (p : ℝ)⁻¹ ^ (e + 2) - 1) ^ 2 by ring,
      gammaJuliaEndpointHalfWeight_sq]
    change z * (2 * z - 1) ^ 2 ≤ z
    simpa using mul_le_mul_of_nonneg_left hfactor hz0

/-- The majorant has finite total mass on the full prime-power diagram. -/
theorem summable_gammaJuliaEndpointCorrectionMultiplierSqMajorant :
    Summable gammaJuliaEndpointCorrectionMultiplierSqMajorant := by
  have hp0 (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ :=
    gammaJulia_inversePrime_pos p
  have hp1 (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast p.prop.one_lt)
  have hsquare : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    apply h.congr
    intro p
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [inv_pow]
  rw [summable_prod_of_nonneg]
  · refine ⟨fun p => ?_, ?_⟩
    · have hgeo :
          Summable (fun e : ℕ => ((p : ℝ)⁻¹) ^ (e + 1)) := by
        have h :=
          (summable_geometric_of_lt_one (hp0 p).le (hp1 p)).mul_left
            ((p : ℝ)⁻¹)
        apply h.congr
        intro e
        rw [pow_succ']
      have hdelta :
          Summable (fun e : ℕ =>
            if e = 0 then
              4 * ((p : ℝ)⁻¹) ^ 3 - (p : ℝ)⁻¹
            else 0) :=
        (hasSum_ite_eq 0
          (4 * ((p : ℝ)⁻¹) ^ 3 - (p : ℝ)⁻¹)).summable
      apply (hdelta.add hgeo).congr
      intro e
      by_cases he : e = 0
      · subst e
        simp [gammaJuliaEndpointCorrectionMultiplierSqMajorant]
      · simp [gammaJuliaEndpointCorrectionMultiplierSqMajorant, he]
    · apply (hsquare.mul_left 4).of_nonneg_of_le
        (fun p => tsum_nonneg fun e => by
          unfold gammaJuliaEndpointCorrectionMultiplierSqMajorant
          split_ifs <;> positivity)
      intro p
      let q : ℝ := (p : ℝ)⁻¹
      have hq0 : 0 ≤ q := (hp0 p).le
      have hden : 0 < 1 - q := sub_pos.mpr (hp1 p)
      have hinv : (1 - q)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hden zero_lt_two]
        have hhalf : q ≤ 1 / 2 := gammaJulia_inversePrime_le_half p
        linarith
      have hinner :
          Summable
            (fun e : ℕ =>
              gammaJuliaEndpointCorrectionMultiplierSqMajorant (p, e)) := by
        have hgeo :
            Summable (fun e : ℕ => q ^ (e + 1)) := by
          have h :=
            (summable_geometric_of_lt_one (hp0 p).le (hp1 p)).mul_left q
          apply h.congr
          intro e
          rw [pow_succ']
        have hdelta :
            Summable (fun e : ℕ =>
              if e = 0 then 4 * q ^ 3 - q else 0) :=
          (hasSum_ite_eq 0 (4 * q ^ 3 - q)).summable
        apply (hdelta.add hgeo).congr
        intro e
        by_cases he : e = 0
        · subst e
          simp [gammaJuliaEndpointCorrectionMultiplierSqMajorant, q]
        · simp [gammaJuliaEndpointCorrectionMultiplierSqMajorant, q, he]
      have hsplit := hinner.sum_add_tsum_nat_add 1
      have htail :
          (∑' e : ℕ,
            gammaJuliaEndpointCorrectionMultiplierSqMajorant (p, e + 1)) =
            q ^ 2 * (1 - q)⁻¹ := by
        rw [show
          (fun e : ℕ =>
            gammaJuliaEndpointCorrectionMultiplierSqMajorant (p, e + 1)) =
              fun e => q ^ 2 * q ^ e by
          funext e
          rw [gammaJuliaEndpointCorrectionMultiplierSqMajorant, if_neg (by omega)]
          change q ^ (e + 1 + 1) = q ^ 2 * q ^ e
          rw [show e + 1 + 1 = 2 + e by omega, pow_add]]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (hp0 p).le (hp1 p)]
      change
        (∑' e : ℕ,
          gammaJuliaEndpointCorrectionMultiplierSqMajorant (p, e)) ≤
            4 * q ^ 2
      rw [← hsplit, htail]
      simp only [Finset.sum_range_one,
        gammaJuliaEndpointCorrectionMultiplierSqMajorant]
      change 4 * q ^ 3 + q ^ 2 * (1 - q)⁻¹ ≤ 4 * q ^ 2
      have hqhalf : q ≤ 1 / 2 := gammaJulia_inversePrime_le_half p
      calc
        4 * q ^ 3 + q ^ 2 * (1 - q)⁻¹
            ≤ 4 * q ^ 3 + q ^ 2 * 2 := by
              gcongr
        _ ≤ 4 * q ^ 2 := by
              have hmul : q ^ 2 * q ≤ q ^ 2 * (1 / 2) :=
                mul_le_mul_of_nonneg_left hqhalf (sq_nonneg q)
              nlinarith
  · intro pe
    unfold gammaJuliaEndpointCorrectionMultiplierSqMajorant
    split_ifs <;> positivity

/-- The endpoint-correction diagonal is Hilbert--Schmidt. -/
theorem summable_sq_gammaJuliaEndpointCorrectionMultiplier :
    Summable (fun pe : Nat.Primes × ℕ =>
      gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2 ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    gammaJuliaEndpointCorrectionMultiplier_sq_le_majorant
    summable_gammaJuliaEndpointCorrectionMultiplierSqMajorant

theorem gammaJuliaEndpointHalfWeight_one
    (p : Nat.Primes) :
    gammaJuliaEndpointHalfWeight p 1 = (p : ℝ)⁻¹ := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  unfold gammaJuliaEndpointHalfWeight
  norm_num

/-- The depth-one slice dominates half of the divergent prime-harmonic series. -/
theorem half_invPrime_le_abs_gammaJuliaEndpointCorrectionMultiplier_one
    (p : Nat.Primes) :
    1 / (2 * (p : ℝ)) ≤
      |gammaJuliaEndpointCorrectionMultiplier p 1| := by
  have hq0 := gammaJulia_inversePrime_pos p
  have hqhalf := gammaJulia_inversePrime_le_half p
  have hq2 : ((p : ℝ)⁻¹) ^ 2 ≤ 1 / 4 := by
    have hraw := pow_le_pow_left₀ hq0.le hqhalf 2
    norm_num at hraw ⊢
    exact hraw
  rw [abs_of_neg
    (by simpa only [Nat.zero_add] using
      gammaJuliaEndpointCorrectionMultiplier_succ_neg p 0)]
  rw [gammaJuliaEndpointCorrectionMultiplier, if_neg (by norm_num),
    gammaJuliaEndpointHalfWeight_one]
  let q : ℝ := (p : ℝ)⁻¹
  have hleft : 1 / (2 * (p : ℝ)) = q / 2 := by
    dsimp [q]
    field_simp [show (p : ℝ) ≠ 0 by exact_mod_cast p.2.ne_zero]
  rw [hleft]
  change q / 2 ≤ -(q * (2 * q ^ 2 - 1))
  have hgap : 0 ≤ 1 / 2 - 2 * q ^ 2 := by
    dsimp [q]
    nlinarith
  have hprod : 0 ≤ q * (1 / 2 - 2 * q ^ 2) :=
    mul_nonneg hq0.le hgap
  nlinarith

/-- The Hilbert--Schmidt diagonal is not trace class. -/
theorem not_summable_abs_gammaJuliaEndpointCorrectionMultiplier :
    ¬ Summable (fun pe : Nat.Primes × ℕ =>
      |gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2|) := by
  intro h
  have hinj : Function.Injective (fun p : Nat.Primes => (p, 1)) := by
    intro p q hpq
    exact (Prod.mk.inj hpq).1
  have hslice : Summable (fun p : Nat.Primes =>
      |gammaJuliaEndpointCorrectionMultiplier p 1|) := by
    simpa only [Prod.fst, Prod.snd] using h.comp_injective hinj
  have hhalf : Summable (fun p : Nat.Primes => (1 / (2 * (p : ℝ)))) :=
    Summable.of_nonneg_of_le
      (fun p => by positivity)
      half_invPrime_le_abs_gammaJuliaEndpointCorrectionMultiplier_one
      hslice
  have hone : Summable (fun p : Nat.Primes => (1 / (p : ℝ))) := by
    apply (hhalf.mul_left 2).congr
    intro p
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    field_simp
  exact Nat.Primes.not_summable_one_div hone

/-- Half-dressed critical Julia wall amplitude. -/
def gammaJuliaEndpointCorrectionDressedAmplitude
    (pe : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt
    |gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2| *
      suzukiCriticalEntryWallBareAmplitude pe.1 pe.2

/-- The dressed amplitude's square is exactly the absolute endpoint correction coefficient. -/
theorem gammaJuliaEndpointCorrectionDressedAmplitude_sq
    (pe : Nat.Primes × ℕ) :
    gammaJuliaEndpointCorrectionDressedAmplitude pe ^ 2 =
      |Real.log (pe.1 : ℝ) *
        xiPhysicalEndpointValuationCorrection pe.1 pe.2| := by
  have hwall :
      0 ≤ suzukiCriticalEntryWallBareAmplitude pe.1 pe.2 ^ 2 :=
    sq_nonneg _
  have hfactor :=
    gammaJuliaEndpointCorrection_factorization pe.1 pe.2
  unfold gammaJuliaEndpointCorrectionDressedAmplitude
  rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  calc
    |gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2| *
          suzukiCriticalEntryWallBareAmplitude pe.1 pe.2 ^ 2 =
        |suzukiCriticalEntryWallBareAmplitude pe.1 pe.2 ^ 2 *
          gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2| := by
            rw [abs_mul, abs_of_nonneg hwall]
            ring
    _ = _ := by rw [← hfactor]

/-- The half-dressed critical wall is an honest square-summable Hilbert channel. -/
theorem summable_sq_gammaJuliaEndpointCorrectionDressedAmplitude :
    Summable (fun pe : Nat.Primes × ℕ =>
      gammaJuliaEndpointCorrectionDressedAmplitude pe ^ 2) := by
  apply summable_abs_clocked_xiPhysicalEndpointValuationCorrection.congr
  intro pe
  exact (gammaJuliaEndpointCorrectionDressedAmplitude_sq pe).symm

/-- **Phase-faithful Julia dressing law.**  At every prime-power clock and height, the signed
square of the critical Julia wall at reflected height is exactly the physical endpoint correction
atom, including its full delay phase. -/
theorem xiPhysicalEndpointValuationCorrectionKernelTerm_eq_juliaWallDressing
    (t : ℝ) (pe : Nat.Primes × ℕ) :
    xiPhysicalEndpointValuationCorrectionKernelTerm t pe =
      (gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2 : ℂ) *
        suzukiCriticalWallField (-t) pe.1 pe.2 ^ 2 := by
  have hlog :
      Real.log (xiGammaEulerValuationNat pe : ℝ) =
        ((pe.2 + 1 : ℕ) : ℝ) * Real.log (pe.1 : ℝ) := by
    rw [xiGammaEulerValuationNat]
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [sq_suzukiCriticalWallField_eq_farHingeNumerator]
  rw [← Complex.ofReal_div]
  rw [← sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul]
  rw [mul_comm
    (gammaJuliaEndpointCorrectionMultiplier pe.1 pe.2)
    (suzukiCriticalEntryWallBareAmplitude pe.1 pe.2 ^ 2)]
  rw [← gammaJuliaEndpointCorrection_factorization]
  unfold xiPhysicalEndpointValuationCorrectionKernelTerm
    suzukiOscillatoryKernel
  rw [hlog]
  push_cast
  congr 1
  ring_nf

end

end RHTower
