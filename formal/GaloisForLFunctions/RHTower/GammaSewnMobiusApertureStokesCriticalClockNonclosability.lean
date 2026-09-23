import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalInformationSchurDepletion
import GaloisForLFunctions.RHTower.ArithmeticSchurFirstTraceNonclosability

/-!
# Critical Stokes clock nonclosability through the Gamma--Schur Hardy carrier

P-G72 and P-G73 show that diagonal scalar compression has the wrong critical mass.  This module
identifies the deeper topology obstruction.  At critical aperture the exact inverse Stokes tilt
grows like `sqrt(p) log p`.  Rescaled two-prime Schur-null witnesses, pairing `p` with a prime
strictly beyond `p^(2 : ℕ)`, therefore vanish after the coherent Hardy kernel map while their Stokes
clock images converge to the nonzero first Hardy basis vector.

Hence the critical Stokes clock is not sequentially closable through the Gamma--Schur Hardy
carrier.  The obstruction uses actual primes and exact source inequalities.  Its positive survivor
is a precise architectural requirement: Gamma/polar completion must retain a stronger graph or
Köthe topology before scalar Hardy compression.

No Xi zero, RH premise, numerical computation, fitted parameter, or added axiom enters.
-/

open Filter Topology

namespace RHTower

noncomputable section

def criticalStokesNode (p : Nat.Primes) : ℝ :=
  xiMobiusContinuousApertureDiskNode (1 / 2) p

theorem criticalStokesNode_pos (p : Nat.Primes) : 0 < criticalStokesNode p :=
  xiMobiusContinuousApertureDiskNode_pos _ _

theorem criticalStokesNode_sq (p : Nat.Primes) :
    criticalStokesNode p ^ (2 : ℕ) = ((p : ℝ))⁻¹ := by
  simpa [criticalStokesNode, xiTransversePrimeApertureDiskNode_one_eq_inv] using
    xiMobiusContinuousApertureDiskNode_half_sq p

theorem criticalStokesNode_lt_five_sevenths (p : Nat.Primes) :
    criticalStokesNode p < 5 / 7 := by
  let r := criticalStokesNode p
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr2 : r ^ (2 : ℕ) = ((p : ℝ))⁻¹ := criticalStokesNode_sq p
  have hinv : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    have hi0 : (0 : ℝ) ≤ ((p : ℝ))⁻¹ := (inv_pos.mpr hp0).le
    have hmul : (p : ℝ) * ((p : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
    nlinarith
  by_contra h
  have hr : 5 / 7 ≤ r := le_of_not_gt h
  nlinarith [mul_nonneg (sub_nonneg.mpr hr)
    (add_nonneg hr0.le (by norm_num : (0 : ℝ) ≤ 5 / 7))]

theorem gammaSewnMobiusApertureStokesCriticalInverseTilt_eq
    (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p =
      Real.log (p : ℝ) / criticalStokesNode p *
        ((1 + criticalStokesNode p ^ (2 : ℕ)) /
          (gammaSewnMobiusValuationContractionMultiplier (1 / 2) p *
            (1 - criticalStokesNode p))) := by
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr := (criticalStokesNode_pos p).ne'
  have hc := (gammaSewnMobiusValuationContractionMultiplier_pos (1 / 2) p).ne'
  have hr1 := sub_ne_zero.mpr (xiMobiusContinuousApertureDiskNode_lt_one
    (a := (1 / 2 : ℝ)) (by norm_num) p).ne'
  have hq : xiTransversePrimeApertureDiskNode 1 p = r ^ (2 : ℕ) := by
    rw [xiTransversePrimeApertureDiskNode_one_eq_inv, criticalStokesNode_sq]
  rw [gammaSewnMobiusApertureStokesInverseTilt, hq]
  change Real.log (p : ℝ) * r /
      (c * (r ^ (2 : ℕ) / (1 + r ^ (2 : ℕ))) * (1 - r)) =
    Real.log (p : ℝ) / r * ((1 + r ^ (2 : ℕ)) / (c * (1 - r)))
  have hr1' : 1 - r ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt ((criticalStokesNode_lt_five_sevenths p).trans
      (by norm_num : (5 / 7 : ℝ) < 1)))
  field_simp [hr, hc, hr1']

theorem criticalStokesInverseTilt_lower (p : Nat.Primes) :
    Real.log (p : ℝ) / criticalStokesNode p <
      gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p := by
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one (by norm_num) p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos _ _
  have hc1 : c < 1 := gammaSewnMobiusValuationContractionMultiplier_lt_one
    (x := (1 / 2 : ℝ)) (by norm_num) p
  have hL : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  rw [gammaSewnMobiusApertureStokesCriticalInverseTilt_eq]
  change Real.log (p : ℝ) / r <
    Real.log (p : ℝ) / r * ((1 + r ^ (2 : ℕ)) / (c * (1 - r)))
  have hbase : 1 < (1 + r ^ (2 : ℕ)) / (c * (1 - r)) := by
    rw [lt_div_iff₀ (mul_pos hc0 (sub_pos.mpr hr1))]
    nlinarith [mul_pos (sub_pos.mpr hc1) (sub_pos.mpr hr1)]
  exact (lt_mul_iff_one_lt_right (div_pos hL hr0)).2 hbase

theorem criticalStokesInverseTilt_upper (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p ≤
      14 * Real.log (p : ℝ) / criticalStokesNode p := by
  let r := criticalStokesNode p
  let c := gammaSewnMobiusValuationContractionMultiplier (1 / 2) p
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr57 : r < 5 / 7 := criticalStokesNode_lt_five_sevenths p
  have hr1 : r < 1 := hr57.trans (by norm_num)
  have hc : 1 / 2 < c := one_half_lt_gammaSewnMobiusValuationContractionMultiplier _ _
  have hden : 0 < c * (1 - r) := by positivity
  have hfactor : (1 + r ^ (2 : ℕ)) / (c * (1 - r)) ≤ 14 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg r,
      mul_pos (sub_pos.mpr hc) (sub_pos.mpr (show r < 5 / 7 from hr57))]
  have hL : 0 ≤ Real.log (p : ℝ) / r := by positivity
  rw [gammaSewnMobiusApertureStokesCriticalInverseTilt_eq]
  calc
    Real.log (p : ℝ) / r * ((1 + r ^ (2 : ℕ)) / (c * (1 - r))) ≤
        Real.log (p : ℝ) / r * 14 := mul_le_mul_of_nonneg_left hfactor hL
    _ = 14 * Real.log (p : ℝ) / r := by ring

def primeCriticalStokesClock : (Nat.Primes →₀ ℝ) →ₗ[ℝ] PrimeHardy :=
  Finsupp.lsum ℝ (fun p => LinearMap.toSpanSingleton ℝ _
    (gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p • primeHardyTail p))

@[simp] theorem primeCriticalStokesClock_single (p : Nat.Primes) (a : ℝ) :
    primeCriticalStokesClock (Finsupp.single p a) =
      a • (gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p • primeHardyTail p) := by
  simp [primeCriticalStokesClock]

def primeCriticalStokesWitness (p r : Nat.Primes) : Nat.Primes →₀ ℝ :=
  ((p.1 : ℝ) / gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p) •
    (Finsupp.single p 1 - Finsupp.single r 1)

theorem primeHardyKernelMap_criticalStokesWitness (p r : Nat.Primes) :
    primeHardyKernelMap (primeCriticalStokesWitness p r) =
      ((p.1 : ℝ) / gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p) •
        (primeHardyTail p - primeHardyTail r) := by
  simp [primeCriticalStokesWitness, primeHardyKernel, primeHardyTail, hardyFirstTail]

theorem primeCriticalStokesClock_witness (p r : Nat.Primes) :
    primeCriticalStokesClock (primeCriticalStokesWitness p r) =
      (p.1 : ℝ) • primeHardyTail p -
        ((p.1 : ℝ) * gammaSewnMobiusApertureStokesInverseTilt (1 / 2) r /
          gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p) • primeHardyTail r := by
  have hWp : gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p ≠ 0 :=
    (gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) p).ne'
  simp only [primeCriticalStokesWitness, map_smul, map_sub,
    primeCriticalStokesClock_single, smul_sub, smul_smul, one_mul]
  congr 1
  · field_simp [hWp]
  · ring

theorem norm_primeHardyKernelMap_criticalFarWitness_le (p : Nat.Primes) :
    ‖primeHardyKernelMap (primeCriticalStokesWitness p (farPrime p))‖ ≤
      4 / gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let W : ℝ := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hW0 : 0 < W := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) p
  have hPR : P ≤ R := by
    dsimp [P, R]
    have hp2 : p.1 ≤ p.1 ^ (2 : ℕ) := by nlinarith [p.2.two_le]
    exact_mod_cast hp2.trans (farPrime_sq_lt p).le
  rw [primeHardyKernelMap_criticalStokesWitness, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hP0 hW0)]
  calc
    P / W * ‖primeHardyTail p - primeHardyTail (farPrime p)‖ ≤
        P / W * (‖primeHardyTail p‖ + ‖primeHardyTail (farPrime p)‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (div_nonneg hP0.le hW0.le)
    _ ≤ P / W * (2 / P + 2 / R) := by
      gcongr
      · simpa [P] using norm_primeHardyTail_le p
      · simpa [R] using norm_primeHardyTail_le (farPrime p)
    _ ≤ P / W * (4 / P) := by
      gcongr
      have htwo : 2 / R ≤ 2 / P := by
        exact (div_le_div_iff₀ hR0 hP0).2 (by nlinarith)
      calc
        2 / P + 2 / R ≤ 2 / P + 2 / P := add_le_add_right htwo _
        _ = 4 / P := by ring
    _ = 4 / W := by field_simp
    _ = _ := rfl

theorem criticalFarStokesSusceptibilityRatio_le (p : Nat.Primes) :
    (p.1 : ℝ) * gammaSewnMobiusApertureStokesInverseTilt (1 / 2) (farPrime p) /
        (gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p * (farPrime p).1) ≤
      42 * criticalStokesNode p := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let L : ℝ := Real.log P
  let M : ℝ := Real.log R
  let rp := criticalStokesNode p
  let rr := criticalStokesNode (farPrime p)
  let Wp := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p
  let Wr := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) (farPrime p)
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hL0 : 0 < L := by dsimp [L, P]; exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hM0 : 0 < M := by dsimp [M, R]; exact Real.log_pos (by exact_mod_cast (farPrime p).2.one_lt)
  have hrp0 : 0 < rp := criticalStokesNode_pos p
  have hrr0 : 0 < rr := criticalStokesNode_pos (farPrime p)
  have hWp0 : 0 < Wp := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) p
  have hWr0 : 0 < Wr := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) (farPrime p)
  have hrp2 : rp ^ (2 : ℕ) = P⁻¹ := by simpa [rp, P] using criticalStokesNode_sq p
  have hrr2 : rr ^ (2 : ℕ) = R⁻¹ := by simpa [rr, R] using criticalStokesNode_sq (farPrime p)
  have hPrr : P * rr < 1 := by
    have hsqNat := farPrime_sq_lt p
    have hsq : P ^ (2 : ℕ) < R := by
      dsimp [P, R]
      exact_mod_cast hsqNat
    have hprod : P ^ (2 : ℕ) * rr ^ (2 : ℕ) < R * rr ^ (2 : ℕ) :=
      mul_lt_mul_of_pos_right hsq (sq_pos_of_pos hrr0)
    have hRrr2 : R * rr ^ (2 : ℕ) = 1 := by
      rw [hrr2]
      exact mul_inv_cancel₀ hR0.ne'
    rw [hRrr2] at hprod
    nlinarith [sq_nonneg (P * rr - 1)]
  have hPRr : P / rr < R := by
    rw [div_lt_iff₀ hrr0]
    have hRrr2 : R * rr ^ (2 : ℕ) = 1 := by
      rw [hrr2]
      exact mul_inv_cancel₀ hR0.ne'
    nlinarith [sq_pos_of_pos hrr0]
  have hlog : M ≤ 3 * L := by simpa [M, L, R, P] using farPrime_log_le_three_log p
  have hPM : P * M / rr ≤ 3 * L * R := by
    calc
      P * M / rr = (P / rr) * M := by ring
      _ ≤ R * M := mul_le_mul_of_nonneg_right hPRr.le hM0.le
      _ ≤ R * (3 * L) := mul_le_mul_of_nonneg_left hlog hR0.le
      _ = 3 * L * R := by ring
  have hWr : Wr ≤ 14 * M / rr := by simpa [Wr, M, rr] using criticalStokesInverseTilt_upper (farPrime p)
  have hWp : L / rp < Wp := by simpa [Wp, L, rp] using criticalStokesInverseTilt_lower p
  have hleft : P * Wr ≤ 42 * L * R := by
    calc
      P * Wr ≤ P * (14 * M / rr) := mul_le_mul_of_nonneg_left hWr hP0.le
      _ = 14 * (P * M / rr) := by ring
      _ ≤ 14 * (3 * L * R) := mul_le_mul_of_nonneg_left hPM (by norm_num)
      _ = 42 * L * R := by ring
  have hright : 42 * L * R < 42 * rp * Wp * R := by
    have hmul : L < rp * Wp := by
      have := (div_lt_iff₀ hrp0).mp hWp
      nlinarith
    have h42 := mul_lt_mul_of_pos_left hmul (by norm_num : (0 : ℝ) < 42)
    have h42R := mul_lt_mul_of_pos_right h42 hR0
    simpa only [mul_assoc] using h42R
  apply (div_le_iff₀ (mul_pos hWp0 hR0)).2
  calc
    P * Wr ≤ 42 * L * R := hleft
    _ ≤ 42 * rp * (Wp * R) := by
      rw [← mul_assoc]
      exact hright.le

theorem norm_primeCriticalStokesClock_farWitness_sub_basisOne_le (p : Nat.Primes) :
    ‖primeCriticalStokesClock (primeCriticalStokesWitness p (farPrime p)) -
        lp.single 2 1 1‖ ≤
      2 / (p.1 : ℝ) + 84 * criticalStokesNode p := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  let Wp : ℝ := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p
  let Wr : ℝ := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) (farPrime p)
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hWp0 : 0 < Wp := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) p
  have hWr0 : 0 < Wr := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) (farPrime p)
  rw [primeCriticalStokesClock_witness, prime_smul_tail_eq_remainder_add_basisOne]
  have heq :
      (hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p) +
          lp.single 2 1 1 - (P * Wr / Wp) • primeHardyTail (farPrime p)) -
          lp.single 2 1 1 =
        hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p) -
          (P * Wr / Wp) • primeHardyTail (farPrime p) := by abel
  rw [heq]
  calc
    ‖hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p) -
        (P * Wr / Wp) • primeHardyTail (farPrime p)‖ ≤
      ‖hardyFirstTailRemainder (primeReciprocal p) (primeReciprocal_abs_lt_one p)‖ +
        ‖(P * Wr / Wp) • primeHardyTail (farPrime p)‖ := norm_sub_le _ _
    _ ≤ 2 / P + (P * Wr / Wp) * (2 / R) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (mul_pos hP0 hWr0) hWp0)]
      exact add_le_add (by simpa [P] using norm_primeHardyRemainder_le p)
        (mul_le_mul_of_nonneg_left
          (by simpa [R] using norm_primeHardyTail_le (farPrime p))
          (div_nonneg (mul_nonneg hP0.le hWr0.le) hWp0.le))
    _ = 2 / P + 2 * (P * Wr / (Wp * R)) := by field_simp
    _ ≤ 2 / P + 2 * (42 * criticalStokesNode p) := by
      gcongr
      simpa [P, R, Wp, Wr] using criticalFarStokesSusceptibilityRatio_le p
    _ = 2 / P + 84 * criticalStokesNode p := by ring
    _ = _ := rfl

def primeCriticalStokesNullSequence (n : ℕ) : Nat.Primes →₀ ℝ :=
  let p := nthPrimePoint n
  primeCriticalStokesWitness p (farPrime p)

theorem tendsto_criticalStokesNode_nthPrime_zero :
    Tendsto (fun n => criticalStokesNode (nthPrimePoint n)) atTop (𝓝 0) := by
  have hP := tendsto_nthPrimePoint_cast_atTop
  have hinv : Tendsto (fun n : ℕ => (((nthPrimePoint n).1 : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hP
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hinv
  have heq : (fun n => criticalStokesNode (nthPrimePoint n)) =
      (fun n => Real.sqrt (((nthPrimePoint n).1 : ℝ)⁻¹)) := by
    funext n
    have hr0 := (criticalStokesNode_pos (nthPrimePoint n)).le
    rw [← Real.sqrt_sq hr0, criticalStokesNode_sq]
  rw [heq]
  change Tendsto ((fun x : ℝ => Real.sqrt x) ∘
    fun n => (((nthPrimePoint n).1 : ℝ))⁻¹) atTop (𝓝 0)
  simpa only [Real.sqrt_zero] using hsqrt

theorem tendsto_primeHardyKernelMap_criticalStokesNullSequence :
    Tendsto (fun n => primeHardyKernelMap (primeCriticalStokesNullSequence n))
      atTop (𝓝 0) := by
  have hr := tendsto_criticalStokesNode_nthPrime_zero
  have hconst : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : Tendsto (fun n =>
      4 / Real.log 2 * criticalStokesNode (nthPrimePoint n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hr)
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop,
      4 / Real.log 2 * criticalStokesNode (nthPrimePoint n) < ε :=
    (tendsto_order.1 hbound).2 ε hε
  filter_upwards [hevent] with n hn
  let p := nthPrimePoint n
  let W := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p
  have hW0 : 0 < W := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) p
  have hL : Real.log 2 ≤ Real.log (p.1 : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast p.2.two_le
  have hlower : Real.log 2 / criticalStokesNode p < W :=
    (div_le_div_of_nonneg_right hL (criticalStokesNode_pos p).le).trans_lt
      (criticalStokesInverseTilt_lower p)
  have hinv : 4 / W < 4 / Real.log 2 * criticalStokesNode p := by
    have hr0 := criticalStokesNode_pos p
    apply (div_lt_iff₀ hW0).2
    have hcross : Real.log 2 < W * criticalStokesNode p := by
      have := (div_lt_iff₀ hr0).mp hlower
      nlinarith
    have hratio : 1 < W * criticalStokesNode p / Real.log 2 := by
      exact (lt_div_iff₀ hconst).2 (by simpa using hcross)
    calc
      4 < 4 * (W * criticalStokesNode p / Real.log 2) := by nlinarith
      _ = 4 / Real.log 2 * criticalStokesNode p * W := by ring
  exact lt_of_le_of_lt
    (by simpa [primeCriticalStokesNullSequence, p, W] using
      norm_primeHardyKernelMap_criticalFarWitness_le p)
    (hinv.trans (by simpa [p] using hn))

theorem tendsto_primeCriticalStokesClock_nullSequence :
    Tendsto (fun n => primeCriticalStokesClock (primeCriticalStokesNullSequence n))
      atTop (𝓝 (lp.single 2 1 1)) := by
  have hP := tendsto_nthPrimePoint_cast_atTop
  have hinv : Tendsto (fun n : ℕ => (((nthPrimePoint n).1 : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hP
  have hr := tendsto_criticalStokesNode_nthPrime_zero
  have hbound : Tendsto (fun n =>
      2 / ((nthPrimePoint n).1 : ℝ) +
        84 * criticalStokesNode (nthPrimePoint n)) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun n => 2 / ((nthPrimePoint n).1 : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
    simpa using hfirst.add (tendsto_const_nhds.mul hr)
  have hzero : Tendsto (fun n =>
      primeCriticalStokesClock (primeCriticalStokesNullSequence n) - lp.single 2 1 1)
      atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    have hevent : ∀ᶠ n : ℕ in atTop,
        2 / ((nthPrimePoint n).1 : ℝ) +
          84 * criticalStokesNode (nthPrimePoint n) < ε :=
      (tendsto_order.1 hbound).2 ε hε
    filter_upwards [hevent] with n hn
    exact lt_of_le_of_lt
      (by simpa [primeCriticalStokesNullSequence] using
        norm_primeCriticalStokesClock_farWitness_sub_basisOne_le (nthPrimePoint n)) hn
  have hadd := hzero.add (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (lp.single 2 1 1 : PrimeHardy)) atTop (𝓝 (lp.single 2 1 1)))
  simpa only [sub_add_cancel, zero_add] using hadd

theorem not_closable_primeCriticalStokesClock :
    ¬ IsSequentiallyClosableThrough primeCriticalStokesClock primeHardyKernelMap := by
  exact not_isSequentiallyClosableThrough_of_graphNull
    primeCriticalStokesClock primeHardyKernelMap primeCriticalStokesNullSequence
    (lp.single 2 1 1) tendsto_primeHardyKernelMap_criticalStokesNullSequence
    tendsto_primeCriticalStokesClock_nullSequence primeHardy_basisOne_ne_zero

end

end RHTower
