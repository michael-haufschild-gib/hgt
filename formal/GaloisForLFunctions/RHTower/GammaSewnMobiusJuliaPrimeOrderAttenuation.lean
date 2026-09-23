import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport
import GaloisForLFunctions.RHTower.CCMFirstClockPrimePowerTowerCollapse
import GaloisForLFunctions.HTGeometry.JuliaDefectAttenuation

/-!
# Prime-order attenuation of the Gamma-sewn Julia source

The canonical Julia environment does more than recover the von Mangoldt prime logarithm at the
lossless boundary.  At every positive aperture its squared hard half-weight mass is the literal
critical Euler mass multiplied by a factor depending only on `x * log p`.  This factor is strictly
decreasing in the prime base.

At the first CCM clock, every admitted multi-mode tower has smaller prime base than every
one-mode outer tower.  Hence the Julia transport strictly favors every multi-mode tower over every
outer bad tower.  It preserves the sign of each complete tower, so this is an exact relative-budget
gain rather than a positivity theorem by itself.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Finite-aperture mass ratio between the Julia hard half-weight and its critical boundary
amplitude at prime `p`. -/
def gammaSewnMobiusJuliaPrimeAttenuation
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  (gammaSewnMobiusJuliaNormalizedPrimeLog x p /
    Real.log (p : ℝ)) ^ (2 : ℕ)

/-- Fourth-power identity matching the aperture-disk and hyperbolic descriptions of the sewn
Julia compression. -/
lemma hyperbolicJuliaCompression_sq_sq (y : ℝ) :
    (Real.cosh (y / 2) ^ (2 : ℕ) / Real.sqrt (Real.cosh (2 * y))) ^ (2 : ℕ) =
      let q := Real.exp (-y)
      (1 + q) ^ (4 : ℕ) / (8 * (1 + q ^ (4 : ℕ))) := by
  let q := Real.exp (-y)
  let e := Real.exp y
  have hq0 : q ≠ 0 := (Real.exp_pos _).ne'
  have hqe : q * e = 1 := by
    dsimp only [q, e]
    rw [← Real.exp_add]
    simp
  have hsqrt : Real.sqrt (Real.cosh (2 * y)) ^ (2 : ℕ) = Real.cosh (2 * y) :=
    Real.sq_sqrt (Real.cosh_pos _).le
  have heq : e = 1 / q := by
    apply (eq_div_iff hq0).2
    nlinarith
  have hhalf : Real.cosh (y / 2) ^ (2 : ℕ) = (Real.cosh y + 1) / 2 := by
    have h := Real.cosh_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (y / 2)]
  have hcosh : Real.cosh y = (e + q) / 2 := by
    rw [Real.cosh_eq]
  have hcosh2 : Real.cosh (2 * y) = (e ^ (2 : ℕ) + q ^ (2 : ℕ)) / 2 := by
    rw [Real.cosh_eq]
    rw [show Real.exp (2 * y) = e ^ (2 : ℕ) by
      dsimp only [e]
      rw [show 2 * y = y + y by ring, Real.exp_add]
      ring,
    show Real.exp (-(2 * y)) = q ^ (2 : ℕ) by
      dsimp only [q]
      rw [show -(2 * y) = (-y) + (-y) by ring, Real.exp_add]
      ring]
  dsimp only
  rw [div_pow, hsqrt, hhalf, hcosh, hcosh2, heq]
  field_simp [hq0]
  ring

/-- Exact hyperbolic normal form of the squared arithmetic compression. -/
theorem gammaSewnMobiusValuationContractionMultiplier_sq_eq_hyperbolic
    (x : ℝ) (p : Nat.Primes) :
    gammaSewnMobiusValuationContractionMultiplier x p ^ (2 : ℕ) =
      Real.cosh (x * Real.log (p : ℝ) / 2) ^ (2 : ℕ) /
        Real.sqrt (Real.cosh (2 * (x * Real.log (p : ℝ)))) := by
  let y := x * Real.log (p : ℝ)
  let c := gammaSewnMobiusValuationContractionMultiplier x p
  let H := Real.cosh (y / 2) ^ (2 : ℕ) / Real.sqrt (Real.cosh (2 * y))
  have hc4 := gammaSewnMobiusValuationContractionMultiplier_pow_four x p
  have hq : xiMobiusContinuousApertureDiskNode x p = Real.exp (-y) := by
    simp only [xiMobiusContinuousApertureDiskNode, y]
    congr 1
    ring
  rw [hq] at hc4
  have hH2 := hyperbolicJuliaCompression_sq_sq y
  have hsq : (c ^ (2 : ℕ)) ^ (2 : ℕ) = H ^ (2 : ℕ) := by
    calc
      (c ^ (2 : ℕ)) ^ (2 : ℕ) = c ^ (4 : ℕ) := by ring
      _ = (1 + Real.exp (-y)) ^ (4 : ℕ) /
          (8 * (1 + Real.exp (-y) ^ (4 : ℕ))) := by
        simpa only [c] using hc4
      _ = H ^ (2 : ℕ) := by
        simpa only [H] using hH2.symm
  have hc0 : 0 ≤ c ^ (2 : ℕ) := sq_nonneg _
  have hH0 : 0 < H := by
    dsimp only [H]
    positivity
  dsimp only [c, H, y] at hsq hc0 hH0 ⊢
  nlinarith

/-- The literal arithmetic Julia defect is the universal HT defect profile at `x * log p`. -/
theorem gammaSewnMobiusJuliaDefect_sq_eq_juliaDefectSquareProfile
    {x : ℝ} (hx : 0 ≤ x) (p : Nat.Primes) :
    gammaSewnMobiusJuliaDefect x p ^ (2 : ℕ) =
      HTGeometry.juliaDefectSquareProfile (x * Real.log (p : ℝ)) := by
  let y := x * Real.log (p : ℝ)
  rw [gammaSewnMobiusJuliaDefect_sq hx,
    gammaSewnMobiusValuationContractionMultiplier_sq_eq_hyperbolic]
  have h := HTGeometry.inv_sqrt_juliaDefectQuartic_tanh_eq_cosh_ratio (y / 2)
  rw [show 4 * (y / 2) = 2 * y by ring] at h
  dsimp only [HTGeometry.juliaDefectSquareProfile]
  rw [h]

/-- Exact identification of arithmetic mass attenuation with the universal HT profile. -/
theorem gammaSewnMobiusJuliaPrimeAttenuation_eq_profile
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnMobiusJuliaPrimeAttenuation x p =
      HTGeometry.juliaDefectAttenuationProfile
        (x * Real.log (p : ℝ)) := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hsqrtSq : Real.sqrt (3 / 4 : ℝ) ^ (2 : ℕ) = 3 / 4 := by
    rw [Real.sq_sqrt]
    norm_num
  have hdef := gammaSewnMobiusJuliaDefect_sq_eq_juliaDefectSquareProfile hx.le p
  rw [gammaSewnMobiusJuliaPrimeAttenuation,
    gammaSewnMobiusJuliaNormalizedPrimeLog,
    gammaSewnMobiusJuliaSourceTransportV_sourceAxis]
  dsimp only [HTGeometry.juliaDefectAttenuationProfile]
  field_simp [gammaSewnMobiusJuliaNormalization_ne_zero, hx.ne', hpLog.ne']
  nlinarith

theorem gammaSewnMobiusJuliaPrimeAttenuation_pos
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    0 < gammaSewnMobiusJuliaPrimeAttenuation x p := by
  rw [gammaSewnMobiusJuliaPrimeAttenuation]
  apply sq_pos_of_ne_zero
  apply div_ne_zero
  · rw [gammaSewnMobiusJuliaNormalizedPrimeLog,
      gammaSewnMobiusJuliaSourceTransportV_sourceAxis]
    simp only [mul_one]
    exact mul_ne_zero (inv_ne_zero gammaSewnMobiusJuliaNormalization_ne_zero)
      (div_ne_zero (gammaSewnMobiusJuliaDefect_pos hx p).ne' hx.ne')
  · exact (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'

/-- Boundary source fidelity: attenuation tends to one at every fixed prime. -/
theorem tendsto_gammaSewnMobiusJuliaPrimeAttenuation_nhdsGT_zero
    (p : Nat.Primes) :
    Tendsto (fun x : ℝ => gammaSewnMobiusJuliaPrimeAttenuation x p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
  have hpLog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
  have h :=
    (tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero p).div_const
      (Real.log (p : ℝ)) |>.pow 2
  have hlim : (Real.log (p : ℝ) / Real.log (p : ℝ)) ^ (2 : ℕ) = 1 := by
    field_simp
  rw [hlim] at h
  simpa only [gammaSewnMobiusJuliaPrimeAttenuation] using h

/-- Strict prime-order law: larger primes receive strictly smaller Julia mass weight. -/
theorem gammaSewnMobiusJuliaPrimeAttenuation_strictAnti
    {x : ℝ} (hx : 0 < x) {p q : Nat.Primes}
    (hpq : (p : ℕ) < q) :
    gammaSewnMobiusJuliaPrimeAttenuation x q <
      gammaSewnMobiusJuliaPrimeAttenuation x p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hlog : Real.log (p : ℝ) < Real.log (q : ℝ) :=
    Real.strictMonoOn_log hp0 hq0 hpqR
  have hyP : x * Real.log (p : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    exact mul_pos hx (Real.log_pos (by exact_mod_cast p.property.one_lt))
  have hyQ : x * Real.log (q : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    exact mul_pos hx (Real.log_pos (by exact_mod_cast q.property.one_lt))
  have hylt : x * Real.log (p : ℝ) < x * Real.log (q : ℝ) :=
    mul_lt_mul_of_pos_left hlog hx
  rw [gammaSewnMobiusJuliaPrimeAttenuation_eq_profile hx,
    gammaSewnMobiusJuliaPrimeAttenuation_eq_profile hx]
  exact HTGeometry.strictAntiOn_juliaDefectAttenuationProfile hyP hyQ hylt

/-- Any admitted multi-mode first-clock tower has smaller prime base than an admitted one-mode
outer tower. -/
theorem ccmFirstClockPrime_lt_of_two_le_length_of_length_one
    {L : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpCut : p ≤ ⌊Real.exp L⌋₊)
    (hpLength : 2 ≤ ccmFirstClockPrimePowerLength L p)
    (hqLength : ccmFirstClockPrimePowerLength L q = 1) :
    p < q := by
  let n : ℕ := ⌊Real.exp L⌋₊
  have hn0 : n ≠ 0 := by
    exact (lt_of_lt_of_le hp.pos hpCut).ne'
  have hpPowN : p ^ ccmFirstClockPrimePowerLength L p ≤ n := by
    simpa only [ccmFirstClockPrimePowerLength, n] using
      Nat.pow_log_le_self p hn0
  have hpSqN : p ^ (2 : ℕ) ≤ n :=
    (Nat.pow_le_pow_right hp.pos hpLength).trans hpPowN
  have hnqPow : n < q ^ (ccmFirstClockPrimePowerLength L q + 1) := by
    simpa only [ccmFirstClockPrimePowerLength, n] using
      Nat.lt_pow_succ_log_self hq.one_lt n
  rw [hqLength] at hnqPow
  have hpqPow : p ^ (2 : ℕ) < q ^ (2 : ℕ) := by
    norm_num at hnqPow ⊢
    exact hpSqN.trans_lt hnqPow
  exact (Nat.pow_lt_pow_iff_left (by norm_num : 2 ≠ 0)).mp hpqPow

/-- Every one-mode outer first-clock prime is attenuated more strongly than every admitted
multi-mode prime tower. -/
theorem ccmFirstClockJuliaAttenuation_outer_lt_multimode
    {x L : ℝ} (hx : 0 < x) {p q : Nat.Primes}
    (hpCut : (p : ℕ) ≤ ⌊Real.exp L⌋₊)
    (hpLength : 2 ≤ ccmFirstClockPrimePowerLength L p)
    (hqLength : ccmFirstClockPrimePowerLength L q = 1) :
    gammaSewnMobiusJuliaPrimeAttenuation x q <
      gammaSewnMobiusJuliaPrimeAttenuation x p := by
  apply gammaSewnMobiusJuliaPrimeAttenuation_strictAnti hx
  exact ccmFirstClockPrime_lt_of_two_le_length_of_length_one
    p.property q.property hpCut hpLength hqLength

/-- Exact gain in good-minus-bad budget relative to applying the outer-prime attenuation
uniformly to both terms. -/
theorem ccmFirstClockJuliaAttenuation_relative_budget_gain
    {x L G B : ℝ} (hx : 0 < x) (hG : 0 < G) {p q : Nat.Primes}
    (hpCut : (p : ℕ) ≤ ⌊Real.exp L⌋₊)
    (hpLength : 2 ≤ ccmFirstClockPrimePowerLength L p)
    (hqLength : ccmFirstClockPrimePowerLength L q = 1) :
    gammaSewnMobiusJuliaPrimeAttenuation x q * (G - B) <
      gammaSewnMobiusJuliaPrimeAttenuation x p * G -
        gammaSewnMobiusJuliaPrimeAttenuation x q * B := by
  have horder := ccmFirstClockJuliaAttenuation_outer_lt_multimode
    hx hpCut hpLength hqLength
  nlinarith [mul_pos (sub_pos.mpr horder) hG]

/-- Julia-attenuated literal first-clock mass of one complete prime-power tower. -/
def ccmFirstClockJuliaAttenuatedPrimePowerTowerMass
    (x L : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSewnMobiusJuliaPrimeAttenuation x p *
    ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p

/-- Canonical Julia attenuation is sign-preserving on every complete prime tower. -/
theorem ccmFirstClockJuliaAttenuatedPrimePowerTowerMass_nonpos_iff
    {x L : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    ccmFirstClockJuliaAttenuatedPrimePowerTowerMass x L p ≤ 0 ↔
      ccmFirstClockPrimePowerTowerMass L (2 * Real.pi / L) p ≤ 0 := by
  rw [← not_lt, ← not_lt,
    ccmFirstClockJuliaAttenuatedPrimePowerTowerMass,
    mul_pos_iff_of_pos_left
      (gammaSewnMobiusJuliaPrimeAttenuation_pos hx p)]

/-- Exact finite-aperture mass factorization on every prime-power cell.  All exponents over one
prime receive the same strictly positive scalar. -/
theorem gammaSewnMobiusJuliaHardHalfWeightTransport_sq_eq_attenuated
    (x u : ℝ) (pe : Nat.Primes × ℕ) :
    gammaSewnMobiusJuliaHardHalfWeightTransport x u pe ^ (2 : ℕ) =
      gammaSewnMobiusJuliaPrimeAttenuation x pe.1 *
        xiGammaEulerBoundaryRealAmplitude u pe ^ (2 : ℕ) := by
  have hpLog : Real.log (pe.1 : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast pe.1.property.one_lt)).ne'
  rw [← primeLog_mul_gammaSewnMobiusJuliaSoftHalfWeightSource u pe]
  unfold gammaSewnMobiusJuliaHardHalfWeightTransport
    gammaSewnMobiusJuliaPrimeAttenuation
  field_simp [hpLog]

end

end RHTower
