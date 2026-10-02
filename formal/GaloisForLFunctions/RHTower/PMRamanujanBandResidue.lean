import GaloisForLFunctions.RHTower.PMRamanujanBandProfile

/-!
# Exact coprime residue in natural Ramanujan bands

The actual Ramanujan cofactor has a positive squarefree inner weight with
its cofactor primes deleted. Its exact Möbius residue has only prime and
prime-square local terms. We prove absolute reciprocal residue summability,
fixed-mask mean existence, and the exact moving-cutoff residue expansion.
The candidate profile prime multiplier is the local source-density correction.

The full actual-band profile limit and the anchored energy of the moving
signed remainder are not established here.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Positive squarefree weight with the primes dividing `d` deleted. -/
def pmRamanujanBandSquarefree (ε : ℝ) (d : ℕ) : ArithmeticFunction ℝ :=
  DampedMobius.dampedMobius (fun p => -pmPowerDampedRamanujanPrimeCorrection ε d p)

private theorem prime_correction_reciprocal (ε : ℝ) {p d : ℕ}
    (hp : p.Prime) (hpd : ¬p ∣ d) :
    (p : ℝ)^(-1-ε)*pmPowerDampedRamanujanPrimeCorrection ε d p =
      1/((p : ℝ)^(1+ε)-1) := by
  rw [pmPowerDampedRamanujanPrimeCorrection, if_neg hpd, ← mul_div_assoc,
    ← Real.rpow_add (by exact_mod_cast hp.pos)]
  simp

/-- Exact source identity, before any cutoff or asymptotic replacement. -/
theorem pmRamanujanBandSquarefree_actual {ε : ℝ} (hε : 0 < ε) (d m : ℕ) :
    (moebius m : ℂ)*pmPowerDampedRamanujanWeight ε (d*m) =
      pmPowerDampedRamanujanWeight ε d *
        (((m : ℝ)^(-1-ε)*pmRamanujanBandSquarefree ε d m : ℝ) : ℂ) := by
  induction m using induction_on_primes with
  | zero => simp [pmPowerDampedRamanujanWeight_zero]
  | one => simp [pmRamanujanBandSquarefree,
      (DampedMobius.isMultiplicative_dampedMobius _).map_one]
  | prime_mul p q hp ih =>
    have hmu := Sieve.moebius_prime_mul (e := q) hp
    rw [pmRamanujanBandSquarefree, pm_dampedMobius_prime_mul _ hp]
    by_cases hpq : p ∣ q
    · rw [if_pos hpq] at hmu ⊢
      have hz : moebius (p*q) = 0 := by exact_mod_cast hmu
      simp [hz]
    by_cases hpd : p ∣ d
    · have hdiv : p ∣ d*q := dvd_mul_of_dvd_left hpd q
      have hns : ¬Squarefree (d*(p*q)) := by
        rw [show d*(p*q)=p*(d*q) by ring]
        exact fun hs =>
          (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)) hdiv
      rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hns, if_neg hpq]
      simp [pmPowerDampedRamanujanPrimeCorrection, hpd]
    have hnot : ¬p ∣ d*q := fun h => (hp.dvd_mul.mp h).elim hpd hpq
    have ha : pmPowerDampedRamanujanWeight ε (d*(p*q)) =
        -pmPowerDampedRamanujanWeight ε (d*q)/
          (((p : ℝ)^(1+ε)-1 : ℝ) : ℂ) := by
      rw [show d*(p*q)=p*(d*q) by ring]
      exact pmPowerDampedRamanujanWeight_prime_mul hε hp hnot
    rw [if_neg hpq] at hmu
    have hmuC : (moebius (p*q) : ℂ) = -(moebius q : ℂ) := by exact_mod_cast hmu
    rw [ha, hmuC, if_neg hpq, neg_neg]
    change _ = pmPowerDampedRamanujanWeight ε d *
      (((((p*q : ℕ) : ℝ)^(-1-ε))*(pmPowerDampedRamanujanPrimeCorrection ε d p *
        pmRamanujanBandSquarefree ε d q) : ℝ) : ℂ)
    have hb := congrArg (fun x : ℝ => (x : ℂ)) (prime_correction_reciprocal ε hp hpd)
    push_cast at hb ⊢
    rw [Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
    push_cast
    have he : -(moebius q : ℂ) *
        (-pmPowerDampedRamanujanWeight ε (d*q) /
          (((p : ℝ)^(1+ε)-1 : ℝ) : ℂ)) =
        ((moebius q : ℂ)*pmPowerDampedRamanujanWeight ε (d*q)) /
          (((p : ℝ)^(1+ε)-1 : ℝ) : ℂ) := by ring
    push_cast at he
    rw [he, ih]
    push_cast
    linear_combination -(pmPowerDampedRamanujanWeight ε d *
      (((q : ℝ)^(-1-ε) : ℝ) : ℂ) * (pmRamanujanBandSquarefree ε d q : ℂ))*hb

theorem pmPowerDampedRamanujanCofactor_eq_squarefree {ε : ℝ} (hε : 0 < ε)
    (Q d : ℕ) :
    pmPowerDampedRamanujanCofactor ε Q d =
      (d : ℂ)*pmPowerDampedRamanujanWeight ε d *
        ((∑ m ∈ Icc 1 (Q/d), (m : ℝ)^(-1-ε)*pmRamanujanBandSquarefree ε d m : ℝ) : ℂ) := by
  unfold pmPowerDampedRamanujanCofactor
  simp_rw [pmRamanujanBandSquarefree_actual hε]
  rw [← Finset.mul_sum]
  push_cast
  ring

/-- The exact coprime squarefree residue, retaining all signs. -/
def pmRamanujanBandResidue (ε : ℝ) (d : ℕ) : ArithmeticFunction ℝ :=
  (moebius : ArithmeticFunction ℝ) * pmRamanujanBandSquarefree ε d

theorem pmRamanujanBandResidue_multiplicative (ε : ℝ) (d : ℕ) :
    (pmRamanujanBandResidue ε d).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (DampedMobius.isMultiplicative_dampedMobius _)

theorem pmRamanujanBandResidue_divisor_sum (ε : ℝ) (d n : ℕ) :
    ∑ r ∈ n.divisors, pmRamanujanBandResidue ε d r = pmRamanujanBandSquarefree ε d n := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply, pmRamanujanBandResidue, ← mul_assoc,
    mul_comm (zeta : ArithmeticFunction ℝ) (moebius : ArithmeticFunction ℝ),
    ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]


theorem pmRamanujanBandSquarefree_prime_pow (ε : ℝ) (d : ℕ)
    {p k : ℕ} (hp : p.Prime) :
    pmRamanujanBandSquarefree ε d (p^k) =
      if k=0 then 1 else if k=1 then pmPowerDampedRamanujanPrimeCorrection ε d p else 0 := by
  rw [pmRamanujanBandSquarefree, DampedMobius.dampedMobius_apply_prime_pow _ hp]
  split_ifs <;> simp

theorem pmRamanujanBandSquarefree_nonneg {ε : ℝ} (hε : 0 < ε) (d n : ℕ) :
    0 ≤ pmRamanujanBandSquarefree ε d n := by
  induction n using induction_on_primes with
  | zero => simp
  | one => simp [pmRamanujanBandSquarefree,
      (DampedMobius.isMultiplicative_dampedMobius _).map_one]
  | prime_mul p q hp ih =>
    rw [pmRamanujanBandSquarefree, pm_dampedMobius_prime_mul _ hp]
    split_ifs
    · exact le_rfl
    rw [neg_neg]
    apply mul_nonneg _ ih
    unfold pmPowerDampedRamanujanPrimeCorrection
    split_ifs
    · exact le_rfl
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact div_nonneg (by positivity) (sub_nonneg.mpr
      (Real.one_lt_rpow hp1 (by linarith : 0 < 1+ε)).le)

theorem pmRamanujanBandResidue_one (ε : ℝ) (d : ℕ) :
    pmRamanujanBandResidue ε d 1 = 1 :=
  (pmRamanujanBandResidue_multiplicative ε d).map_one

theorem pmRamanujanBandResidue_prime (ε : ℝ) (d : ℕ) {p : ℕ} (hp : p.Prime) :
    pmRamanujanBandResidue ε d p = pmPowerDampedRamanujanPrimeCorrection ε d p-1 := by
  have h := pmRamanujanBandResidue_divisor_sum ε d (p^1)
  rw [Nat.sum_divisors_prime_pow hp, pmRamanujanBandSquarefree_prime_pow ε d hp] at h
  simp [Finset.sum_range_succ, pmRamanujanBandResidue_one] at h
  linarith

theorem pmRamanujanBandResidue_prime_sq (ε : ℝ) (d : ℕ) {p : ℕ} (hp : p.Prime) :
    pmRamanujanBandResidue ε d (p^2) = -pmPowerDampedRamanujanPrimeCorrection ε d p := by
  have h := pmRamanujanBandResidue_divisor_sum ε d (p^2)
  rw [Nat.sum_divisors_prime_pow hp, pmRamanujanBandSquarefree_prime_pow ε d hp] at h
  simp [Finset.sum_range_succ, pmRamanujanBandResidue_one,
    pmRamanujanBandResidue_prime ε d hp] at h
  linarith

/-- The signed residue stops at prime squares, including deleted primes. -/
theorem pmRamanujanBandResidue_prime_pow_eq_zero (ε : ℝ) (d : ℕ)
    {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    pmRamanujanBandResidue ε d (p^k) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have h := pmRamanujanBandResidue_divisor_sum ε d (p^k)
    rw [Nat.sum_divisors_prime_pow hp, pmRamanujanBandSquarefree_prime_pow ε d hp,
      if_neg (by omega : k ≠ 0), if_neg (by omega : k ≠ 1), Finset.sum_range_succ] at h
    have hhead : ∑ j ∈ range k, pmRamanujanBandResidue ε d (p^j) = 0 := by
      rw [show k=3+(k-3) by omega, Finset.sum_range_add]
      have hfirst : ∑ j ∈ range 3, pmRamanujanBandResidue ε d (p^j) = 0 := by
        simp [Finset.sum_range_succ, pmRamanujanBandResidue_one,
          pmRamanujanBandResidue_prime ε d hp, pmRamanujanBandResidue_prime_sq ε d hp]
      rw [hfirst, zero_add]
      apply sum_eq_zero
      intro j hj
      exact ih (3+j) (by have := mem_range.mp hj; omega) (by omega)
    rw [hhead, zero_add] at h
    exact h

private theorem correction_bounds {ε : ℝ} (hε : 0 < ε) (d : ℕ)
    {p : ℕ} (hp : p.Prime) :
    0 ≤ pmPowerDampedRamanujanPrimeCorrection ε d p ∧
    pmPowerDampedRamanujanPrimeCorrection ε d p ≤ 2 ∧
    (¬p ∣ d → 0 ≤ pmPowerDampedRamanujanPrimeCorrection ε d p-1 ∧
      pmPowerDampedRamanujanPrimeCorrection ε d p-1 ≤ 2/(p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have ht : (p : ℝ) ≤ (p : ℝ)^(1+ε) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : (1 : ℝ) ≤ p) (by linarith : (1 : ℝ) ≤ 1+ε)
  unfold pmPowerDampedRamanujanPrimeCorrection
  split_ifs with hpd
  · simp [hpd]
  have hden : 0 < (p : ℝ)^(1+ε)-1 := by linarith
  have he : (p : ℝ)^(1+ε)/((p : ℝ)^(1+ε)-1)-1 =
      1/((p : ℝ)^(1+ε)-1) := by field_simp; ring
  refine ⟨div_nonneg (by positivity) hden.le, ?_, fun _ => ?_⟩
  · rw [div_le_iff₀ hden]
    linarith
  · rw [he]
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ hden (by linarith : (0 : ℝ) < p)]
    linarith

private def residueAbsHarmonic (ε : ℝ) (d : ℕ) : ArithmeticFunction ℝ where
  toFun n := |pmRamanujanBandResidue ε d n|/(n : ℝ)
  map_zero' := by simp

private theorem residueAbsHarmonic_multiplicative (ε : ℝ) (d : ℕ) :
    (residueAbsHarmonic ε d).IsMultiplicative := by
  constructor
  · simp [residueAbsHarmonic, pmRamanujanBandResidue_one]
  · intro m n hmn
    change |pmRamanujanBandResidue ε d (m*n)|/((m*n : ℕ) : ℝ) = _
    rw [(pmRamanujanBandResidue_multiplicative ε d).map_mul_of_coprime hmn]
    simp only [residueAbsHarmonic, ArithmeticFunction.coe_mk, abs_mul, Nat.cast_mul]
    ring

private theorem residueAbsHarmonic_local (ε : ℝ) (d : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => residueAbsHarmonic ε d (p^k)) := by
  apply summable_of_ne_finset_zero (s := {0,1,2})
  intro k hk
  simp only [mem_insert, mem_singleton, not_or] at hk
  change |pmRamanujanBandResidue ε d (p^k)|/((p^k : ℕ) : ℝ) = 0
  rw [pmRamanujanBandResidue_prime_pow_eq_zero ε d hp (by omega)]
  simp

private theorem residueAbsHarmonic_local_sum {ε : ℝ} (hε : 0 < ε) (d : ℕ)
    {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, residueAbsHarmonic ε d (p^k)) =
      1 + |pmPowerDampedRamanujanPrimeCorrection ε d p-1|/(p : ℝ) +
        pmPowerDampedRamanujanPrimeCorrection ε d p/(p : ℝ)^2 := by
  rw [tsum_eq_sum (s := {0,1,2})]
  · simp [residueAbsHarmonic, pmRamanujanBandResidue_one,
      pmRamanujanBandResidue_prime ε d hp, pmRamanujanBandResidue_prime_sq ε d hp,
      abs_of_nonneg (correction_bounds hε d hp).1, add_assoc]
  · intro k hk
    simp only [mem_insert, mem_singleton, not_or] at hk
    change |pmRamanujanBandResidue ε d (p^k)|/((p^k : ℕ) : ℝ) = 0
    rw [pmRamanujanBandResidue_prime_pow_eq_zero ε d hp (by omega)]
    simp

/-- Absolute reciprocal residue mass is finite for every fixed nonzero coprime
mask. No assertion about the moving signed band norm follows from this. -/
theorem summable_pmRamanujanBandResidue_reciprocal {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : d ≠ 0) :
    Summable (fun n : ℕ => |pmRamanujanBandResidue ε d n|/(n : ℝ)) := by
  let b : ℕ → ℝ := fun n => 4/(n : ℝ)^2 + if n ∈ d.primeFactors then 1/(n : ℝ) else 0
  have hb : Summable b := by
    have htwo : Summable (fun n : ℕ => 4/(n : ℝ)^2) := by
      simpa only [Real.rpow_two, mul_one_div] using
        ((Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 2)).mul_left 4)
    apply htwo.add
    apply summable_of_ne_finset_zero (s := d.primeFactors)
    intro n hn
    simp [hn]
  apply pm_summable_of_multiplicative_local_bound (residueAbsHarmonic ε d)
    (residueAbsHarmonic_multiplicative ε d) (fun n => div_nonneg (abs_nonneg _) (Nat.cast_nonneg n))
    (residueAbsHarmonic_local ε d) b (fun n => by dsimp [b]; positivity) hb
  intro p hp
  rw [residueAbsHarmonic_local_sum hε d hp]
  have hc := correction_bounds hε d hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht : |pmPowerDampedRamanujanPrimeCorrection ε d p-1|/(p : ℝ) +
      pmPowerDampedRamanujanPrimeCorrection ε d p/(p : ℝ)^2 ≤ b p := by
    by_cases hpd : p ∣ d
    · have hmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpd,hd⟩
      simp only [pmPowerDampedRamanujanPrimeCorrection, if_pos hpd, zero_sub, abs_neg,
        abs_one, zero_div, add_zero, b, if_pos hmem]
      exact le_add_of_nonneg_left (by positivity)
    · have hmem : p ∉ d.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
      rw [abs_of_nonneg (hc.2.2 hpd).1]
      calc
        _ ≤ (2/(p : ℝ))/(p : ℝ) + 2/(p : ℝ)^2 :=
          add_le_add (div_le_div_of_nonneg_right (hc.2.2 hpd).2 hp0.le)
            (div_le_div_of_nonneg_right hc.2.1 (sq_nonneg _))
        _ = 4/(p : ℝ)^2 := by ring
        _ = b p := by simp only [b,if_neg hmem,add_zero]
  calc
    _ ≤ 1+b p := by linarith
    _ ≤ Real.exp (b p) := by simpa only [add_comm] using Real.add_one_le_exp (b p)

private theorem squarefree_sum_eq_floor (ε : ℝ) (d N : ℕ) :
    (∑ n ∈ Icc 1 N, pmRamanujanBandSquarefree ε d n) =
      ∑ r ∈ Icc 1 N, pmRamanujanBandResidue ε d r*((N/r : ℕ) : ℝ) := by
  have he (n : ℕ) : pmRamanujanBandSquarefree ε d n =
      (pmRamanujanBandResidue ε d*(zeta : ArithmeticFunction ℝ)) n := by
    rw [ArithmeticFunction.coe_mul_zeta_apply, pmRamanujanBandResidue_divisor_sum]
  simp_rw [he, ArithmeticFunction.mul_apply]
  rw [Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun r m => pmRamanujanBandResidue ε d r*(zeta : ArithmeticFunction ℝ) m) N]
  apply sum_congr rfl
  intro r hr
  trans ∑ m ∈ Icc 1 (N/r), pmRamanujanBandResidue ε d r
  · apply sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hm0]
  · simp [mul_comm]

/-- The density of the literal positive coprime cofactor weight. -/
def pmRamanujanBandSquarefreeDensity (ε : ℝ) (d : ℕ) : ℝ :=
  ∑' r : ℕ, pmRamanujanBandResidue ε d r/(r : ℝ)

/-- Mean existence for the actual coprime squarefree weight, proved by its
absolutely admitted residue. The spatial variable here is unbounded; the mask
`d` is fixed. -/
theorem tendsto_pmRamanujanBandSquarefree_mean {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : d ≠ 0) :
    Tendsto (fun x : ℝ => (∑ n ∈ Icc 1 ⌊x⌋₊, pmRamanujanBandSquarefree ε d n)/x)
      atTop (𝓝 (pmRamanujanBandSquarefreeDensity ε d)) := by
  let F : ℝ → ℕ → ℝ := fun x r => pmRamanujanBandResidue ε d r *
    (((⌊x/(r : ℝ)⌋₊ : ℕ) : ℝ)/x)
  let b : ℕ → ℝ := fun r => pmRamanujanBandResidue ε d r/(r : ℝ)
  have hlim (r : ℕ) : Tendsto (fun x => F x r) atTop (𝓝 (b r)) := by
    have he (x : ℝ) : (1/(r : ℝ))*x=x/(r : ℝ) := by ring
    have hfloor : Tendsto (fun x : ℝ => ((⌊x/(r : ℝ)⌋₊ : ℕ) : ℝ)/x) atTop
        (𝓝 (1/(r : ℝ))) := by
      simpa only [he] using tendsto_nat_floor_mul_div_atTop
        (a := 1/(r : ℝ)) (by positivity)
    simpa only [F,b,mul_one_div] using hfloor.const_mul (pmRamanujanBandResidue ε d r)
  have hbound : ∀ᶠ x : ℝ in atTop, ∀ r : ℕ, ‖F x r‖ ≤
      |pmRamanujanBandResidue ε d r|/(r : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    intro r
    have hn0 : 0 ≤ (((⌊x/(r : ℝ)⌋₊ : ℕ) : ℝ)/x) := by positivity
    have hn1 : (((⌊x/(r : ℝ)⌋₊ : ℕ) : ℝ)/x) ≤ 1/(r : ℝ) := by
      rw [div_le_iff₀ hx, show 1/(r : ℝ)*x=x/(r : ℝ) by ring]
      exact Nat.floor_le (div_nonneg hx.le (Nat.cast_nonneg r))
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn0]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hn1 (abs_nonneg _)
  have h := tendsto_tsum_of_dominated_convergence
    (summable_pmRamanujanBandResidue_reciprocal hε hd) hlim hbound
  change Tendsto (fun x => ∑' r, F x r) atTop (𝓝 (pmRamanujanBandSquarefreeDensity ε d)) at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [tsum_eq_sum (s := Icc 1 ⌊x⌋₊), squarefree_sum_eq_floor, Finset.sum_div]
  · apply sum_congr rfl
    intro r hr
    simp only [F,Nat.floor_div_natCast]
    ring
  · intro r hr
    by_cases hr0 : r=0
    · subst r; simp [F]
    have hrpos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr0
    have hgt : ⌊x⌋₊ < r := by have := mt mem_Icc.mpr hr; omega
    have hxr : x/(r : ℝ) < 1 := (div_lt_one hrpos).mpr ((Nat.floor_lt hx.le).mp hgt)
    simp [F,Nat.floor_eq_zero.mpr hxr]

/-- The profile multiplier is exactly the local coprime-density correction of
the literal squarefree cofactor weight. -/
theorem pmRamanujanBandProfilePrime_eq_source_factor {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) :
    pmRamanujanBandProfilePrime ε p =
      pmPowerDampedRamanujanPrimeCorrection ε 1 p /
        (1+pmPowerDampedRamanujanPrimeCorrection ε 1 p/(p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnot : ¬p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have ht : 0 < (p : ℝ)^(1+ε)-1 :=
    sub_pos.mpr (Real.one_lt_rpow hp1 (by linarith))
  have hu : (p : ℝ)^(-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hg : 0 < (p : ℝ)+1-(p : ℝ)^(-ε) := by linarith
  have hr : (p : ℝ)^(-ε)*(p : ℝ)^(1+ε) = p := by
    rw [← Real.rpow_add hp0]
    norm_num
  have hrp := congrArg (fun x : ℝ => (p : ℝ)*x) hr
  rw [pmPowerDampedRamanujanPrimeCorrection, if_neg hnot]
  apply (eq_div_iff (by positivity : (1+(p : ℝ)^(1+ε)/((p : ℝ)^(1+ε)-1)/(p : ℝ)) ≠ 0)).mpr
  unfold pmRamanujanBandProfilePrime
  field_simp [ne_of_gt hp0, ne_of_gt ht, ne_of_gt hg]
  nlinarith [hrp]

/-- Exact two-factor expansion of the literal weighted cofactor. The product
cutoff is retained, including the multiplier-one boundary. -/
theorem pmRamanujanBandSquarefree_weighted_sum (ε : ℝ) (d Q : ℕ) :
    (∑ m ∈ Icc 1 Q, (m : ℝ)^(-1-ε)*pmRamanujanBandSquarefree ε d m) =
      ∑ r ∈ Icc 1 Q, (r : ℝ)^(-1-ε)*pmRamanujanBandResidue ε d r *
        ∑ k ∈ Icc 1 (Q/r), (k : ℝ)^(-1-ε) := by
  calc
    _ = ∑ m ∈ Icc 1 Q, ∑ x ∈ m.divisorsAntidiagonal,
        (((x.1*x.2 : ℕ) : ℝ)^(-1-ε))*pmRamanujanBandResidue ε d x.1 := by
      apply sum_congr rfl
      intro m hm
      have he : pmRamanujanBandSquarefree ε d m =
          ∑ x ∈ m.divisorsAntidiagonal, pmRamanujanBandResidue ε d x.1 := by
        rw [Nat.sum_divisorsAntidiagonal (fun r _ => pmRamanujanBandResidue ε d r),
          pmRamanujanBandResidue_divisor_sum]
      rw [he, Finset.mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    _ = ∑ r ∈ Icc 1 Q, ∑ k ∈ Icc 1 (Q/r),
        (((r*k : ℕ) : ℝ)^(-1-ε))*pmRamanujanBandResidue ε d r :=
      Sieve.sum_Icc_divisorsAntidiagonal_swap
        (fun r k => (((r*k : ℕ) : ℝ)^(-1-ε))*pmRamanujanBandResidue ε d r) Q
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg r) (Nat.cast_nonneg k)]
      ring

/-- The actual cofactor with the exact signed residue and moving cutoff. -/
theorem pmPowerDampedRamanujanCofactor_eq_residue {ε : ℝ} (hε : 0 < ε)
    (Q d : ℕ) :
    pmPowerDampedRamanujanCofactor ε Q d =
      (d : ℂ)*pmPowerDampedRamanujanWeight ε d *
        ((∑ r ∈ Icc 1 (Q/d), (r : ℝ)^(-1-ε)*pmRamanujanBandResidue ε d r *
          ∑ k ∈ Icc 1 (Q/d/r), (k : ℝ)^(-1-ε) : ℝ) : ℂ) := by
  rw [pmPowerDampedRamanujanCofactor_eq_squarefree hε,
    pmRamanujanBandSquarefree_weighted_sum]

end RHTower
