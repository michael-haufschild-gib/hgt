import GaloisForLFunctions.RHTower.PMPairedRamanujanGram
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanAbsolute
import GaloisForLFunctions.RHTower.EulerDeletionWeightedPrimeCancellation

/-!
# Growing cofactor packets retain a coherent prime head

The actual prime-weight and primitive recursions identify every cofactor packet
before its first prime multiple. A cutoff-uniform sublinear prefix estimate
makes this head positive, including when all allowed cofactors grow.

At denominator cutoff `P^2`, take every prime in `(P,2*P]` and every cofactor
through `P^2/p`. These are distinct actual denominators. Their anchored energy
on `1 <= N < P` tends to infinity for `0 < epsilon < 1/2`.

This obstructs a separate budget for these growing prime packets. The complete
natural prefix also contains the complementary sector and signed cross terms;
its small-damping energy bound and RH remain open.
-/

open Finset Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- All actual cofactors of a chosen prime up to `R`, including the prime itself. -/
def pmRamanujanPrimeCofactorPacket (ε : ℝ) (p R N : ℕ) : ℂ :=
  ∑ r ∈ Icc 1 R, pmPowerDampedRamanujanWeight ε (p*r) * pmRamanujanPrimitive (p*r) N

private theorem head_uncentered_prefix {ε : ℝ} (hε : 0 < ε) {R : ℕ}
    (hR : 1 ≤ R) (N : ℕ) :
    (∑ r ∈ Icc 1 R, pmPowerDampedRamanujanWeight ε r * pmRamanujanPrimitive r N) =
      pmPowerDampedDivisorDensity ε * N +
        pmPowerDampedRamanujanCumulativePrefix ε (R-1) N := by
  have h : pmPowerDampedRamanujanCumulativePrefix ε (R-1) N =
      (∑ r ∈ Icc 1 R, pmPowerDampedRamanujanWeight ε r * pmRamanujanPrimitive r N) -
        pmPowerDampedDivisorDensity ε * N := by
    rw [pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_floor hε,
      Nat.sub_add_cancel hR, ← pmPowerDampedRamanujanCofactor_cumulative, Finset.sum_comm]
    simp only [pmRamanujanPrimitive, Finset.mul_sum]
  linear_combination -h

/-- Exact growing-cofactor head before the first prime multiple. -/
theorem pmRamanujanPrimeCofactorPacket_head {ε : ℝ} (hε : 0 < ε)
    {p R N : ℕ} (hp : p.Prime) (hR : 1 ≤ R) (hRp : R < p) (hNp : N < p) :
    pmRamanujanPrimeCofactorPacket ε p R N =
      (pmPowerDampedDivisorDensity ε * N +
        pmPowerDampedRamanujanCumulativePrefix ε (R-1) N) /
          (((p : ℝ)^(1+ε)-1 : ℝ) : ℂ) := by
  rw [← head_uncentered_prefix hε hR, pmRamanujanPrimeCofactorPacket, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  have hpr : ¬ p ∣ r := Nat.not_dvd_of_pos_of_lt
    (by have := (mem_Icc.mp hr).1; omega) ((mem_Icc.mp hr).2.trans_lt hRp)
  rw [pmPowerDampedRamanujanWeight_prime_mul hε hp hpr,
    pmRamanujanPrimitive_prime_mul hp hpr, Nat.div_eq_of_lt hNp]
  simp only [pmRamanujanPrimitive, Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty,
    mul_zero, zero_sub]
  ring

private theorem head_prefix_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ,
      ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖ ≤
        (pmPowerDampedDivisorDensity ε).re * N / 2 := by
  have hgap : max 0 (1-ε) < (1 : ℝ) := by rw [max_lt_iff]; constructor <;> linarith
  obtain ⟨a, ha0, ha1⟩ := exists_between hgap
  have ha : 0 ≤ a := (le_max_left 0 (1-ε)).trans ha0.le
  have hεa : 1 < ε+a := by have := (le_max_right 0 (1-ε)).trans_lt ha0; linarith
  let C : ℝ := ∑' d : ℕ, (d : ℝ)^(-(ε+a))
  have ht : Tendsto (fun N : ℕ => C*(N : ℝ)^(a-1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < 1-a)).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, neg_sub, mul_zero] using h.const_mul C
  have hev := ht.eventually (gt_mem_nhds (half_pos (pmPowerDampedDivisorDensity_re_pos hε)))
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 Q
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hb := norm_pmPowerDampedRamanujanCumulativePrefix_le_rpow hε ha ha1.le hεa Q N
  have hp : (N : ℝ)^a*C = (C*(N : ℝ)^(a-1)) * N := by
    rw [Real.rpow_sub hNR, Real.rpow_one]
    field_simp
  calc
    _ ≤ (N : ℝ)^a*C := hb
    _ = (C*(N : ℝ)^(a-1)) * N := hp
    _ ≤ ((pmPowerDampedDivisorDensity ε).re/2)*N :=
      mul_le_mul_of_nonneg_right hN.le hNR.le
    _ = _ := by ring

/-- The coherent head is uniform over every permitted, possibly growing cofactor cutoff. -/
theorem pmRamanujanPrimeCofactorPacket_eventually_head_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p R : ℕ, p.Prime → 1 ≤ R → R < p → N < p →
      (pmPowerDampedDivisorDensity ε).re * N / (2*((p : ℝ)^(1+ε)-1)) ≤
        (pmRamanujanPrimeCofactorPacket ε p R N).re := by
  filter_upwards [head_prefix_eventually_small hε] with N hN p R hp hR hRp hNp
  rw [pmRamanujanPrimeCofactorPacket_head hε hp hR hRp hNp,
    Complex.div_ofReal_re]
  have hd : 0 < (p : ℝ)^(1+ε)-1 := sub_pos.mpr
    (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith))
  have he := (abs_le.mp (Complex.abs_re_le_norm (pmPowerDampedRamanujanCumulativePrefix ε (R-1) N))).1
  have hb := hN (R-1)
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero]
  rw [div_mul_eq_div_div]
  apply div_le_div_of_nonneg_right _ hd.le
  linarith

/-- Literal large-prime sector of the natural denominator cutoff `P^2`. -/
def pmRamanujanLargePrimeSector (ε : ℝ) (P N : ℕ) : ℂ :=
  ∑ p ∈ DeletionPeriodGrowth.upperPrimes (2*P),
    pmRamanujanPrimeCofactorPacket ε p (P^2/p) N

/-- Reciprocal local denominator mass of the selected prime band. -/
def pmRamanujanLargePrimeMass (ε : ℝ) (P : ℕ) : ℝ :=
  ∑ p ∈ DeletionPeriodGrowth.upperPrimes (2*P), 1/((p : ℝ)^(1+ε)-1)

/-- Anchored energy, with the original reciprocal weight and the whole selected sector. -/
def pmRamanujanLargePrimeSectorEnergy (ε : ℝ) (P : ℕ) : ℝ :=
  ∑ N ∈ Icc 1 (P-1), ‖pmRamanujanLargePrimeSector ε P N‖^2 /
    ((N : ℝ)*((N : ℝ)+1))

private theorem head_band_mem {P p : ℕ}
    (hp : p ∈ DeletionPeriodGrowth.upperPrimes (2*P)) :
    p.Prime ∧ P < p ∧ p ≤ 2*P := by
  obtain ⟨hi, hprime, hhalf⟩ := mem_filter.mp hp
  exact ⟨hprime, by omega, (mem_Icc.mp hi).2⟩

private theorem head_cofactor_cutoff {P p : ℕ} (hP : 2 ≤ P)
    (hp : p ∈ DeletionPeriodGrowth.upperPrimes (2*P)) :
    1 ≤ P^2/p ∧ P^2/p < p := by
  obtain ⟨hprime, hlt, hle⟩ := head_band_mem hp
  constructor
  · exact (Nat.le_div_iff_mul_le hprime.pos).mpr (by nlinarith)
  · apply (Nat.div_lt_iff_lt_mul hprime.pos).mpr
    nlinarith

/-- Every sector term is an actual nonconstant channel inside the natural cutoff. -/
theorem pmRamanujanLargePrimeSector_denominator_mem {P p r : ℕ}
    (hp : p ∈ DeletionPeriodGrowth.upperPrimes (2*P)) (hr : r ∈ Icc 1 (P^2/p)) :
    p*r ∈ Icc 2 (P^2) := by
  obtain ⟨hprime, _, _⟩ := head_band_mem hp
  obtain ⟨hr1, hrle⟩ := mem_Icc.mp hr
  exact mem_Icc.mpr ⟨by nlinarith [hprime.two_le],
    by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hprime.pos).mp hrle⟩

/-- Distinct selected primes cannot duplicate any denominator at this cutoff. -/
theorem pmRamanujanLargePrimeSector_denominator_unique {P p q r s : ℕ}
    (hP : 2 ≤ P) (hp : p ∈ DeletionPeriodGrowth.upperPrimes (2*P))
    (hq : q ∈ DeletionPeriodGrowth.upperPrimes (2*P))
    (_hr : r ∈ Icc 1 (P^2/p)) (hs : s ∈ Icc 1 (P^2/q)) (he : p*r=q*s) :
    p=q ∧ r=s := by
  obtain ⟨hprime, hPp, _⟩ := head_band_mem hp
  obtain ⟨hqprime, hPq, _⟩ := head_band_mem hq
  have hsP : s < p := by
    have hdiv : P^2/q < P := (Nat.div_lt_iff_lt_mul hqprime.pos).mpr (by nlinarith)
    exact ((mem_Icc.mp hs).2.trans_lt hdiv).trans hPp
  have hps : ¬ p ∣ s := Nat.not_dvd_of_pos_of_lt (by have := (mem_Icc.mp hs).1; omega) hsP
  have hd : p ∣ q*s := he ▸ dvd_mul_right p r
  have hpq : p=q := (Nat.prime_dvd_prime_iff_eq hprime hqprime).mp
    ((hprime.dvd_mul.mp hd).resolve_right hps)
  subst q
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hprime.pos he⟩

private theorem head_sector_lower {ε : ℝ} (hε : 0 < ε) {M : ℕ}
    (hM : ∀ N ≥ M, ∀ Q : ℕ, ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖ ≤
      (pmPowerDampedDivisorDensity ε).re*N/2) {P N : ℕ}
    (hP : 2 ≤ P) (hMN : M ≤ N) (hNP : N < P) :
    (pmPowerDampedDivisorDensity ε).re*N/2 * pmRamanujanLargePrimeMass ε P ≤
      (pmRamanujanLargePrimeSector ε P N).re := by
  rw [pmRamanujanLargePrimeSector, Complex.re_sum, pmRamanujanLargePrimeMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hprime,hPp,_⟩ := head_band_mem hp
  obtain ⟨hR,hRp⟩ := head_cofactor_cutoff hP hp
  rw [pmRamanujanPrimeCofactorPacket_head hε hprime hR hRp (hNP.trans hPp),
    Complex.div_ofReal_re]
  have hd : 0 < (p : ℝ)^(1+ε)-1 := sub_pos.mpr
    (Real.one_lt_rpow (by exact_mod_cast hprime.one_lt) (by linarith))
  have he := (abs_le.mp (Complex.abs_re_le_norm
    (pmPowerDampedRamanujanCumulativePrefix ε (P^2/p-1) N))).1
  have hb := hM N hMN (P^2/p-1)
  simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    mul_zero, sub_zero, mul_one_div]
  apply div_le_div_of_nonneg_right _ hd.le
  linarith

/-- The full growing-cofactor sector retains a common positive head of length comparable to `P`. -/
theorem pmRamanujanLargePrimeSectorEnergy_eventually_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop,
      (pmPowerDampedDivisorDensity ε).re^2 * P *
        (pmRamanujanLargePrimeMass ε P)^2 / 16 ≤ pmRamanujanLargePrimeSectorEnergy ε P := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (head_prefix_eventually_small hε)
  let K := max M 1
  have hKM : M ≤ K := le_max_left _ _
  have hK1 : 1 ≤ K := le_max_right _ _
  filter_upwards [eventually_ge_atTop (2*K)] with P hP
  have hP2 : 2 ≤ P := by omega
  let A := (pmPowerDampedDivisorDensity ε).re
  let H := pmRamanujanLargePrimeMass ε P
  have hA : 0 < A := pmPowerDampedDivisorDensity_re_pos hε
  have hH : 0 ≤ H := by
    apply Finset.sum_nonneg
    intro p hp
    have hprime := (head_band_mem hp).1
    exact (one_div_pos.mpr (sub_pos.mpr
      (Real.one_lt_rpow (by exact_mod_cast hprime.one_lt) (by linarith)))).le
  have hterm (N : ℕ) (hN : N ∈ Icc K (P-1)) :
      A^2*H^2/8 ≤ ‖pmRamanujanLargePrimeSector ε P N‖^2/((N : ℝ)*((N : ℝ)+1)) := by
    obtain ⟨hKN,hNP⟩ := mem_Icc.mp hN
    have hN1 : 1 ≤ N := hK1.trans hKN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hh := head_sector_lower hε hM hP2 (hKM.trans hKN) (by omega : N < P)
    have hn : A*N/2*H ≤ ‖pmRamanujanLargePrimeSector ε P N‖ := hh.trans (Complex.re_le_norm _)
    have hsq := pow_le_pow_left₀ (show 0 ≤ A*N/2*H by positivity) hn 2
    apply (le_div_iff₀ (by positivity)).mpr
    have he : A^2*H^2/8 * ((N : ℝ)*((N : ℝ)+1)) ≤ (A*N/2*H)^2 := by
      have hm := mul_nonneg (show 0 ≤ A^2*H^2 by positivity)
        (show 0 ≤ (N : ℝ)*(N-1) by positivity)
      nlinarith
    exact he.trans hsq
  have hcard : ((Icc K (P-1)).card : ℝ) ≥ (P : ℝ)/2 := by
    rw [Nat.card_Icc]
    have hkP : K ≤ P := by omega
    have hle : P ≤ 2*(P-K) := by omega
    have he : P-1+1-K=P-K := by omega
    rw [he]
    have hreal : (P : ℝ) ≤ 2*((P-K : ℕ) : ℝ) := by exact_mod_cast hle
    linarith
  calc
    A^2*P*H^2/16 = (P : ℝ)/2*(A^2*H^2/8) := by ring
    _ ≤ ((Icc K (P-1)).card : ℝ)*(A^2*H^2/8) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ N ∈ Icc K (P-1), A^2*H^2/8 := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ ∑ N ∈ Icc K (P-1), ‖pmRamanujanLargePrimeSector ε P N‖^2/
        ((N : ℝ)*((N : ℝ)+1)) := Finset.sum_le_sum hterm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun N hN => mem_Icc.mpr ⟨hK1.trans (mem_Icc.mp hN).1, (mem_Icc.mp hN).2⟩)
      (fun N _ _ => by positivity)

/-- Quantitative lower mass for comparison with the complete signed head energy. -/
theorem pmRamanujanLargePrimeMass_eventually_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop,
      (2*(P : ℝ))^(-ε)/(32768*Real.log (2*(P : ℝ))) ≤ pmRamanujanLargePrimeMass ε P := by
  have htop : Tendsto (fun P : ℕ => 2*P) atTop atTop :=
    tendsto_atTop_mono (fun P => by dsimp only [id]; omega) tendsto_id
  filter_upwards [htop.eventually DeletionPrimePacket.upperPrime_card_eventually_lower,
    eventually_ge_atTop 1] with P hc hP
  have hX : 0 < 2*(P : ℝ) := by positivity
  have hlog : 0 < Real.log (2*(P : ℝ)) := Real.log_pos (by exact_mod_cast (show 1 < 2*P by omega))
  have hs : 0 < (2*(P : ℝ))^(1+ε) := Real.rpow_pos_of_pos hX _
  have hterm : ((DeletionPeriodGrowth.upperPrimes (2*P)).card : ℝ)/(2*(P : ℝ))^(1+ε) ≤
      pmRamanujanLargePrimeMass ε P := by
    rw [pmRamanujanLargePrimeMass]
    calc
      _ = ∑ p ∈ DeletionPeriodGrowth.upperPrimes (2*P), 1/(2*(P : ℝ))^(1+ε) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hprime,_,hle⟩ := head_band_mem hp
        have hd : 0 < (p : ℝ)^(1+ε)-1 := sub_pos.mpr
          (Real.one_lt_rpow (by exact_mod_cast hprime.one_lt) (by linarith))
        apply div_le_div_of_nonneg_left (by norm_num) hd
        have hh : (p : ℝ)^(1+ε) ≤ (2*(P : ℝ))^(1+ε) :=
          Real.rpow_le_rpow (Nat.cast_nonneg p) (by exact_mod_cast hle) (by linarith)
        linarith
  have he : (2*(P : ℝ))^(-ε)/(32768*Real.log (2*(P : ℝ))) =
      ((2*(P : ℝ))/(32768*Real.log (2*(P : ℝ))))/(2*(P : ℝ))^(1+ε) := by
    rw [Real.rpow_add hX, Real.rpow_one, Real.rpow_neg hX.le]
    field_simp
  rw [he]
  apply le_trans _ hterm
  apply div_le_div_of_nonneg_right _ hs.le
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc

/-- A literal sector with all its cofactors has unbounded anchored energy at small damping.
The complementary sector and its mixed terms are not removed from the RH target. -/
theorem tendsto_pmRamanujanLargePrimeSectorEnergy_atTop {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (pmRamanujanLargePrimeSectorEnergy ε) atTop atTop := by
  let A := (pmPowerDampedDivisorDensity ε).re
  let C := A^2/(32*(32768 : ℝ)^2)
  have hA : 0 < A := pmPowerDampedDivisorDensity_re_pos hε
  have hC : 0 < C := by dsimp [C]; positivity
  have hd : 0 < 1-2*ε := by linarith
  have ht : Tendsto (fun X : ℝ => X^(1-2*ε)/Real.log X^2) atTop atTop := by
    have hz : Tendsto (fun X : ℝ => Real.log X^2/X^(1-2*ε)) atTop (𝓝 0) := by
      simpa only [Real.rpow_two] using
        (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hd).tendsto_div_nhds_zero
    have hp : ∀ᶠ X : ℝ in atTop, Real.log X^2/X^(1-2*ε) ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [eventually_gt_atTop 1] with X hX
      exact div_pos (sq_pos_of_pos (Real.log_pos hX)) (Real.rpow_pos_of_pos (by linarith) _)
    have hi := (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz hp).inv_tendsto_nhdsGT_zero
    apply hi.congr
    intro X
    change (Real.log X^2/X^(1-2*ε))⁻¹ = _
    rw [inv_div]
  have hXtop : Tendsto (fun P : ℕ => 2*(P : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  have hl : Tendsto (fun P : ℕ => C*((2*(P : ℝ))^(1-2*ε)/Real.log (2*(P : ℝ))^2))
      atTop atTop := (ht.comp hXtop).const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hl
  filter_upwards [pmRamanujanLargePrimeSectorEnergy_eventually_lower hε,
    pmRamanujanLargePrimeMass_eventually_lower hε, eventually_ge_atTop 1] with P hE hH hP
  have hX : 0 < 2*(P : ℝ) := by positivity
  have hpow : (2*(P : ℝ))^(1-2*ε) =
      (2*(P : ℝ))*((2*(P : ℝ))^(-ε))^2 := by
    rw [show 1-2*ε=1+(-ε)*2 by ring, Real.rpow_add hX,
      Real.rpow_mul hX.le, Real.rpow_one, Real.rpow_two]
  have hsq := pow_le_pow_left₀ (show 0 ≤
    (2*(P : ℝ))^(-ε)/(32768*Real.log (2*(P : ℝ))) from
      div_nonneg (Real.rpow_nonneg hX.le _) (mul_nonneg (by norm_num)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*P by omega))))) hH 2
  calc
    _ = A^2*P*((2*(P : ℝ))^(-ε)/(32768*Real.log (2*(P : ℝ))))^2/16 := by
      dsimp only [C]
      rw [hpow]
      ring
    _ ≤ A^2*P*(pmRamanujanLargePrimeMass ε P)^2/16 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (by norm_num)
    _ ≤ _ := hE

end RHTower
