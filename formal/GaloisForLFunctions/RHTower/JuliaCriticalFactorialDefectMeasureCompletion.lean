import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport
import GaloisForLFunctions.RHTower.PrimeLaplaceEvenFactorialFockIncidence
import GaloisForLFunctions.RHTower.GammaConductorSchurCapacity

namespace RHTower

noncomputable section

open Filter Topology
open GaloisForLFunctions.HTGeometry

def juliaCriticalEvenFactorialJetEnergy
    (x : ℝ) (p : Nat.Primes) (j : ℕ) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    (p : ℝ)⁻¹ *
      gammaSewnMobiusJuliaNormalizedPrimeLog x p ^ (2 * j) /
        ((2 * j).factorial : ℝ)

lemma gammaSewnMobiusJuliaDefect_le_one
    (x : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusJuliaDefect x p ≤ 1 := by
  rw [gammaSewnMobiusJuliaDefect, Real.sqrt_le_one]
  nlinarith [sq_nonneg (gammaSewnMobiusValuationContractionMultiplier x p)]

lemma gammaSewnMobiusJuliaNormalizedPrimeLog_nonneg
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 ≤ gammaSewnMobiusJuliaNormalizedPrimeLog x p := by
  rw [gammaSewnMobiusJuliaNormalizedPrimeLog,
    gammaSewnMobiusJuliaSourceTransportV_sourceAxis]
  simp only [mul_one]
  change 0 ≤ (Real.sqrt (3 / 4 : ℝ))⁻¹ *
    (gammaSewnMobiusJuliaDefect x p / x)
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (div_nonneg (Real.sqrt_nonneg _) hx.le)

lemma gammaSewnMobiusJuliaNormalizedPrimeLog_le
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusJuliaNormalizedPrimeLog x p ≤
      (Real.sqrt (3 / 4 : ℝ))⁻¹ / x := by
  rw [gammaSewnMobiusJuliaNormalizedPrimeLog,
    gammaSewnMobiusJuliaSourceTransportV_sourceAxis]
  simp only [mul_one]
  have hd := gammaSewnMobiusJuliaDefect_le_one x p
  have hn : 0 ≤ (Real.sqrt (3 / 4 : ℝ))⁻¹ := by positivity
  have hx0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
  calc
    (Real.sqrt (3 / 4 : ℝ))⁻¹ *
        (gammaSewnMobiusJuliaDefect x p / x) ≤
      (Real.sqrt (3 / 4 : ℝ))⁻¹ * (1 / x) := by
        gcongr
    _ = (Real.sqrt (3 / 4 : ℝ))⁻¹ / x := by ring_nf

lemma juliaCriticalEvenFactorialJetEnergy_nonneg
    (x : ℝ) (p : Nat.Primes) (j : ℕ) :
    0 ≤ juliaCriticalEvenFactorialJetEnergy x p j := by
  have hpow :
      0 ≤ gammaSewnMobiusJuliaNormalizedPrimeLog x p ^ (2 * j) := by
    rw [pow_mul]
    positivity
  unfold juliaCriticalEvenFactorialJetEnergy
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (Real.cosh_pos _).le _)
        (inv_nonneg.mpr (Nat.cast_nonneg _)))
      hpow)
    (Nat.cast_nonneg _)

theorem hasSum_juliaCriticalEvenFactorialJetEnergy
    (x : ℝ) (p : Nat.Primes) :
    HasSum (juliaCriticalEvenFactorialJetEnergy x p)
      (semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ)⁻¹ *
          Real.cosh (gammaSewnMobiusJuliaNormalizedPrimeLog x p)) := by
  have h := (Real.hasSum_cosh
    (gammaSewnMobiusJuliaNormalizedPrimeLog x p)).mul_left
      (semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ)⁻¹)
  exact h.congr fun j => by
    unfold juliaCriticalEvenFactorialJetEnergy
    ring_nf

theorem summable_juliaCriticalEvenFactorialJetTotalEnergy
    {x : ℝ} (hx : 0 < x) :
    Summable (fun p : Nat.Primes =>
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ)⁻¹ *
          Real.cosh (gammaSewnMobiusJuliaNormalizedPrimeLog x p)) := by
  let M : ℝ := (Real.sqrt (3 / 4 : ℝ))⁻¹ / x
  have hsquare : Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹) ^ 2) := by
    have h := Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
    apply h.congr
    intro p
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    simp only [inv_pow]
  have hmajor : Summable (fun p : Nat.Primes =>
      (Real.sqrt 2 * Real.cosh M) * ((p : ℝ)⁻¹) ^ 2) :=
    hsquare.mul_left _
  apply hmajor.of_nonneg_of_le
  · intro p
    exact mul_nonneg
      (mul_nonneg
        (Real.rpow_nonneg (Real.cosh_pos _).le _)
        (inv_nonneg.mpr (Nat.cast_nonneg _)))
      (Real.cosh_pos _).le
  · intro p
    have hchar :=
      semilocalArchimedeanCharacteristic_two_mul_le_sqrtTwo_mul_exp_neg
        (primeLogSupport p)
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    have hexp : Real.exp (-primeLogSupport p) = ((p : ℝ))⁻¹ := by
      rw [primeLogSupport, Real.exp_neg, Real.exp_log hp0]
    rw [hexp] at hchar
    have hlog0 :=
      gammaSewnMobiusJuliaNormalizedPrimeLog_nonneg hx p
    have hlogM :
        gammaSewnMobiusJuliaNormalizedPrimeLog x p ≤ M := by
      exact gammaSewnMobiusJuliaNormalizedPrimeLog_le hx p
    have hcosh :
        Real.cosh (gammaSewnMobiusJuliaNormalizedPrimeLog x p) ≤
          Real.cosh M := by
      rw [Real.cosh_le_cosh]
      rw [abs_of_nonneg hlog0, abs_of_nonneg (by dsimp [M]; positivity)]
      exact hlogM
    calc
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
          (p : ℝ)⁻¹ *
            Real.cosh (gammaSewnMobiusJuliaNormalizedPrimeLog x p) ≤
        (Real.sqrt 2 * (p : ℝ)⁻¹) * (p : ℝ)⁻¹ *
          Real.cosh M := by gcongr
      _ = (Real.sqrt 2 * Real.cosh M) * ((p : ℝ)⁻¹) ^ 2 := by ring_nf

theorem summable_juliaCriticalEvenFactorialJetEnergy
    {x : ℝ} (hx : 0 < x) :
    Summable (fun pj : Nat.Primes × ℕ =>
      juliaCriticalEvenFactorialJetEnergy x pj.1 pj.2) := by
  rw [summable_prod_of_nonneg (fun pj =>
    juliaCriticalEvenFactorialJetEnergy_nonneg x pj.1 pj.2)]
  refine ⟨fun p => (hasSum_juliaCriticalEvenFactorialJetEnergy x p).summable, ?_⟩
  simpa only [(hasSum_juliaCriticalEvenFactorialJetEnergy x _).tsum_eq] using
    summable_juliaCriticalEvenFactorialJetTotalEnergy hx

/-- Boundary coefficient of the Julia-regularized critical incidence. -/
def juliaCriticalEvenFactorialBoundaryEnergy
    (p : Nat.Primes) (j : ℕ) : ℝ :=
  semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
    (p : ℝ)⁻¹ *
      primeLogSupport p ^ (2 * j) / ((2 * j).factorial : ℝ)

/-- Every fixed prime/jet coordinate converges to the true critical factorial incidence. -/
theorem tendsto_juliaCriticalEvenFactorialJetEnergy_nhdsGT_zero
    (p : Nat.Primes) (j : ℕ) :
    Tendsto
      (fun x : ℝ => juliaCriticalEvenFactorialJetEnergy x p j)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (juliaCriticalEvenFactorialBoundaryEnergy p j)) := by
  have hpow :=
    (tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero p).pow (2 * j)
  let A : ℝ :=
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) * (p : ℝ)⁻¹
  have hconst : Tendsto (fun _ : ℝ => A)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds A) :=
    tendsto_const_nhds
  have hmul := (hconst.mul hpow).div_const
    (((2 * j).factorial : ℝ))
  simpa only [juliaCriticalEvenFactorialJetEnergy,
    juliaCriticalEvenFactorialBoundaryEnergy, primeLogSupport, A] using hmul

lemma semilocalArchimedeanCharacteristic_two_primeLogSupport_sq
    (p : Nat.Primes) :
    semilocalArchimedeanCharacteristic (2 * primeLogSupport p) ^ 2 =
      2 * (p : ℝ) ^ 2 / ((p : ℝ) ^ 4 + 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hlog :
      2 * primeLogSupport p = Real.log ((p : ℝ) ^ 2) := by
    rw [primeLogSupport, Real.log_pow]
    norm_num
  rw [semilocalArchimedeanCharacteristic_sq, hlog,
    Real.cosh_log (sq_pos_of_pos hp0)]
  field_simp

lemma invPrime_le_semilocalArchimedeanCharacteristic_two_primeLogSupport
    (p : Nat.Primes) :
    (p : ℝ)⁻¹ ≤
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.one_le
  have hchar0 :
      0 ≤ semilocalArchimedeanCharacteristic (2 * primeLogSupport p) :=
    (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le
  apply (sq_le_sq₀ (inv_nonneg.mpr hp0.le) hchar0).mp
  rw [semilocalArchimedeanCharacteristic_two_primeLogSupport_sq]
  have hp4 : (1 : ℝ) ≤ (p : ℝ) ^ 4 := one_le_pow₀ hp1
  field_simp
  nlinarith

lemma half_prime_le_cosh_primeLogSupport (p : Nat.Primes) :
    (p : ℝ) / 2 ≤ Real.cosh (primeLogSupport p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  rw [primeLogSupport, Real.cosh_log hp0]
  linarith [inv_nonneg.mpr hp0.le]

theorem hasSum_juliaCriticalEvenFactorialBoundaryEnergy
    (p : Nat.Primes) :
    HasSum (juliaCriticalEvenFactorialBoundaryEnergy p)
      (semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ)⁻¹ * Real.cosh (primeLogSupport p)) := by
  have h := (Real.hasSum_cosh (primeLogSupport p)).mul_left
    (semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
      (p : ℝ)⁻¹)
  exact h.congr fun j => by
    unfold juliaCriticalEvenFactorialBoundaryEnergy
    ring_nf

theorem tsum_juliaCriticalEvenFactorialBoundaryEnergy
    (p : Nat.Primes) :
    ∑' j, juliaCriticalEvenFactorialBoundaryEnergy p j =
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ)⁻¹ * Real.cosh (primeLogSupport p) :=
  (hasSum_juliaCriticalEvenFactorialBoundaryEnergy p).tsum_eq

lemma half_invPrime_le_juliaCriticalEvenFactorialBoundaryColumn
    (p : Nat.Primes) :
    (1 / 2 : ℝ) * (p : ℝ)⁻¹ ≤
      semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ)⁻¹ * Real.cosh (primeLogSupport p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hchar :=
    invPrime_le_semilocalArchimedeanCharacteristic_two_primeLogSupport p
  have hcosh := half_prime_le_cosh_primeLogSupport p
  calc
    (1 / 2 : ℝ) * (p : ℝ)⁻¹ =
        (p : ℝ)⁻¹ * (p : ℝ)⁻¹ * ((p : ℝ) / 2) := by
      field_simp
    _ ≤ semilocalArchimedeanCharacteristic (2 * primeLogSupport p) *
        (p : ℝ)⁻¹ * Real.cosh (primeLogSupport p) := by
      gcongr
      exact mul_nonneg
        (Real.rpow_nonneg (Real.cosh_pos _).le _)
        (inv_nonneg.mpr hp0.le)

/-- The unsaturated critical boundary has divergent total squared coefficient mass. -/
theorem not_summable_juliaCriticalEvenFactorialBoundaryEnergy :
    ¬ Summable (fun pj : Nat.Primes × ℕ =>
      juliaCriticalEvenFactorialBoundaryEnergy pj.1 pj.2) := by
  intro h
  have hnonneg (pj : Nat.Primes × ℕ) :
      0 ≤ juliaCriticalEvenFactorialBoundaryEnergy pj.1 pj.2 := by
    unfold juliaCriticalEvenFactorialBoundaryEnergy
    have hpow : 0 ≤ primeLogSupport pj.1 ^ (2 * pj.2) := by
      rw [pow_mul]
      positivity
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (Real.rpow_nonneg (Real.cosh_pos _).le _)
          (inv_nonneg.mpr (Nat.cast_nonneg _)))
        hpow)
      (Nat.cast_nonneg _)
  have hcolumns :=
    (summable_prod_of_nonneg hnonneg).mp h |>.2
  have hhalf : Summable (fun p : Nat.Primes =>
      (1 / 2 : ℝ) * (p : ℝ)⁻¹) := by
    apply hcolumns.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      rw [tsum_juliaCriticalEvenFactorialBoundaryEnergy]
      exact half_invPrime_le_juliaCriticalEvenFactorialBoundaryColumn p
  have hreciprocal := hhalf.mul_left 2
  have hone : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) := by
    apply hreciprocal.congr
    intro p
    ring_nf
  exact Nat.Primes.not_summable_one_div hone

end

end RHTower
