import GaloisForLFunctions.RHTower.PMPairedRamanujanGram
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeThreshold
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernel

/-!
# Completed Ramanujan prime apertures and the necessity of denominator order

The actual Ramanujan aperture over all subsets of a finite prime set is a
normalized finite Mobius source. Its normalization is the retained probability
mass, lying between the positive source density and one. Known small-damping
prime-aperture divergence therefore persists for these actual Ramanujan weights,
while their logarithmic coefficient-square mass stays uniformly finite.
Consequently an energy ceiling valid for all completed prime supports is false.
The natural-denominator cutoff conjecture and small-damping admission remain open.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

def pmCompleteRamanujanPrimitive (ε : ℝ) (S : Finset ℕ) (N : ℕ) : ℂ :=
  ∑ T ∈ S.powerset, pmPowerDampedRamanujanWeight ε (∏ p ∈ T, p) *
    pmRamanujanPrimitive (∏ p ∈ T, p) N

def pmCompleteMobiusFloor (ε : ℝ) (S : Finset ℕ) (N : ℕ) : ℂ :=
  ∑ T ∈ S.powerset, pmPowerDampedMobiusCoeff ε (∏ p ∈ T, p) *
    ((N / (∏ p ∈ T, p) : ℕ) : ℂ)

def pmRamanujanApertureScale (ε : ℝ) (S : Finset ℕ) : ℝ :=
  (pmPowerDampedDivisorDensity ε).re *
    ∏ p ∈ S, (1 + 1 / ((p : ℝ) ^ (1 + ε) - 1))

private theorem prime_not_dvd_subset_prod (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) {T : Finset ℕ} (hT : T ∈ S.powerset) :
    ¬p ∣ ∏ q ∈ T, q := by
  have hT' : ∀ q ∈ T, q.Prime := fun q hq => hS q (Finset.mem_powerset.mp hT hq)
  intro hd
  have hmem : p ∈ (∏ q ∈ T, q).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, hd, (Finset.prod_pos (fun q hq => (hT' q hq).pos)).ne'⟩
  rw [Nat.primeFactors_prod hT'] at hmem
  exact hpS (Finset.mem_powerset.mp hT hmem)

private theorem damped_coeff_prime_mul (ε : ℝ) {p q : ℕ} (hp : p.Prime)
    (hpq : ¬p ∣ q) :
    pmPowerDampedMobiusCoeff ε (p*q) =
      -(((p : ℝ)^(-ε) : ℝ) : ℂ) * pmPowerDampedMobiusCoeff ε q := by
  have hm : (moebius (p*q) : ℝ) = -(moebius q : ℝ) := by
    simpa [hpq] using (Sieve.moebius_prime_mul (e := q) hp)
  simp only [pmPowerDampedMobiusCoeff, hm, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg q)]
  push_cast
  ring

theorem pmCompleteRamanujanPrimitive_insert {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (N : ℕ) :
    let b : ℂ := (((p : ℝ)^(1+ε)-1 : ℝ) : ℂ)
    pmCompleteRamanujanPrimitive ε (insert p S) N =
      (1 + 1/b) * pmCompleteRamanujanPrimitive ε S N -
        (p : ℂ)/b * pmCompleteRamanujanPrimitive ε S (N/p) := by
  dsimp only
  rw [pmCompleteRamanujanPrimitive, Finset.sum_powerset_insert hpS]
  have ht (T : Finset ℕ) (hT : T ∈ S.powerset) :
      pmPowerDampedRamanujanWeight ε (∏ q ∈ insert p T, q) *
        pmRamanujanPrimitive (∏ q ∈ insert p T, q) N =
      (pmPowerDampedRamanujanWeight ε (∏ q ∈ T, q) * pmRamanujanPrimitive (∏ q ∈ T, q) N) /
          (((p : ℝ)^(1+ε)-1 : ℝ) : ℂ) -
      (p : ℂ)/(((p : ℝ)^(1+ε)-1 : ℝ) : ℂ) *
        (pmPowerDampedRamanujanWeight ε (∏ q ∈ T, q) * pmRamanujanPrimitive (∏ q ∈ T, q) (N/p)) := by
    have hpT : p ∉ T := fun ht => hpS (Finset.mem_powerset.mp hT ht)
    rw [Finset.prod_insert hpT, pmPowerDampedRamanujanWeight_prime_mul hε hp
      (prime_not_dvd_subset_prod S hS hp hpS hT), pmRamanujanPrimitive_prime_mul hp
      (prime_not_dvd_subset_prod S hS hp hpS hT)]
    ring
  rw [Finset.sum_congr rfl ht, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  unfold pmCompleteRamanujanPrimitive
  ring

theorem pmCompleteMobiusFloor_insert (ε : ℝ)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (N : ℕ) :
    pmCompleteMobiusFloor ε (insert p S) N =
      pmCompleteMobiusFloor ε S N - (((p : ℝ)^(-ε) : ℝ) : ℂ) *
        pmCompleteMobiusFloor ε S (N/p) := by
  rw [pmCompleteMobiusFloor, Finset.sum_powerset_insert hpS]
  have ht (T : Finset ℕ) (hT : T ∈ S.powerset) :
      pmPowerDampedMobiusCoeff ε (∏ q ∈ insert p T, q) * ((N / (∏ q ∈ insert p T, q) : ℕ) : ℂ) =
      -(((p : ℝ)^(-ε) : ℝ) : ℂ) *
        (pmPowerDampedMobiusCoeff ε (∏ q ∈ T, q) * (((N/p) / (∏ q ∈ T, q) : ℕ) : ℂ)) := by
    have hpT : p ∉ T := fun ht => hpS (Finset.mem_powerset.mp hT ht)
    rw [Finset.prod_insert hpT, damped_coeff_prime_mul ε hp
      (prime_not_dvd_subset_prod S hS hp hpS hT), Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm p]
    ring
  rw [Finset.sum_congr rfl ht, ← Finset.mul_sum]
  unfold pmCompleteMobiusFloor
  ring

private theorem aperture_prime_balance {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) :
    (1 + 1 / ((p : ℝ)^(1+ε)-1)) * (p : ℝ)^(-ε) =
      (p : ℝ) / ((p : ℝ)^(1+ε)-1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hb : (p : ℝ)^(1+ε)-1 ≠ 0 := ne_of_gt
    (lt_trans (by norm_num) (pmPowerDampedRamanujan_prime_denominator_one_lt hε hp))
  have hpow : (p : ℝ)^(1+ε) * (p : ℝ)^(-ε) = p := by
    rw [← Real.rpow_add hp0, show 1+ε+-ε = (1 : ℝ) by ring, Real.rpow_one]
  calc
    _ = ((p : ℝ)^(1+ε) * (p : ℝ)^(-ε)) / ((p : ℝ)^(1+ε)-1) := by
      field_simp
      ring
    _ = _ := by rw [hpow]

theorem pmRamanujanApertureScale_insert (ε : ℝ) (S : Finset ℕ) {p : ℕ} (hpS : p ∉ S) :
    pmRamanujanApertureScale ε (insert p S) =
      (1 + 1/((p : ℝ)^(1+ε)-1)) * pmRamanujanApertureScale ε S := by
  rw [pmRamanujanApertureScale, Finset.prod_insert hpS, pmRamanujanApertureScale]
  ring

/-- Completed Ramanujan apertures are exactly normalized finite Mobius floor sums. -/
theorem pmCompleteRamanujanPrimitive_eq_normalized {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    pmCompleteRamanujanPrimitive ε S N =
      (pmRamanujanApertureScale ε S : ℂ) * pmCompleteMobiusFloor ε S N := by
  induction S using Finset.induction_on generalizing N with
  | empty =>
    simpa [pmCompleteRamanujanPrimitive, pmCompleteMobiusFloor, pmRamanujanApertureScale,
      pmPowerDampedMobiusCoeff, pmPowerDampedRamanujanWeight_one hε,
      pmRamanujanPrimitive, pm_ramanujan_one] using
        congrArg (fun z : ℂ => z * (N : ℂ)) (pmPowerDampedDivisorDensity_eq_ofReal_re hε)
  | @insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    rw [pmCompleteRamanujanPrimitive_insert hε S hS' hp hpS,
      ih hS' N, ih hS' (N/p), pmRamanujanApertureScale_insert ε S hpS,
      pmCompleteMobiusFloor_insert ε S hS' hp hpS]
    have hbal : (1 + 1/((((p : ℝ)^(1+ε)-1 : ℝ) : ℂ))) * (((p : ℝ)^(-ε) : ℝ) : ℂ) =
        (p : ℂ)/((((p : ℝ)^(1+ε)-1 : ℝ) : ℂ)) := by
      exact_mod_cast aperture_prime_balance hε hp
    push_cast
    push_cast at hbal
    linear_combination (pmRamanujanApertureScale ε S : ℂ) * pmCompleteMobiusFloor ε S (N/p) * hbal

theorem pmCompleteMobiusFloor_eq_coefficient_sum (ε : ℝ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    pmCompleteMobiusFloor ε S N =
      ∑ d ∈ Finset.Icc 1 (∏ p ∈ S, p), finitePrimeApertureMobiusCoefficient S d *
        (((d : ℝ)^(-ε) : ℝ) : ℂ) * ((N/d : ℕ) : ℂ) := by
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ)^T.card *
        (((((∏ p ∈ T, p : ℕ) : ℝ)^(-ε) : ℝ) : ℂ) * ((N/(∏ p ∈ T, p) : ℕ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hT' : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hT hp)
      simp only [pmPowerDampedMobiusCoeff, moebius_prod_distinct_primes hT']
      push_cast
      ring
    _ = _ := by
      simpa only [mul_assoc] using
        (pm_finitePrime_coefficient_sum_eq_powerset S hS
          (fun d => (((d : ℝ)^(-ε) : ℝ) : ℂ) * ((N/d : ℕ) : ℂ))).symm

theorem pmFinitePrimePowerDampedFermiSource_eq_floor_difference (ε : ℝ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {t : ℝ} (ht : 0 < t) :
    pmFinitePrimePowerDampedFermiSource S ε t =
      pmCompleteMobiusFloor ε S ⌊1/t⌋₊ - 2 * pmCompleteMobiusFloor ε S ⌊1/(2*t)⌋₊ := by
  rw [pmCompleteMobiusFloor_eq_coefficient_sum ε S hS,
    pmCompleteMobiusFloor_eq_coefficient_sum ε S hS, pmFinitePrimePowerDampedFermiSource]
  simp_rw [fermiNymanGen_eq_floor_difference,
    real_floor_div_eq_nat_div _ (by positivity : 0 ≤ 1/(2*t)),
    real_floor_div_eq_nat_div _ (by positivity : 0 ≤ 1/t)]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Literal completed Ramanujan aperture, including its fixed denominator-one packet. -/
def pmCompleteRamanujanFermiSource (ε : ℝ) (S : Finset ℕ) (t : ℝ) : ℂ :=
  pmCompleteRamanujanPrimitive ε S ⌊1/t⌋₊ -
    2 * pmCompleteRamanujanPrimitive ε S ⌊1/(2*t)⌋₊

theorem pmCompleteRamanujanFermiSource_eq_normalized {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {t : ℝ} (ht : 0 < t) :
    pmCompleteRamanujanFermiSource ε S t =
      (pmRamanujanApertureScale ε S : ℂ) * pmFinitePrimePowerDampedFermiSource S ε t := by
  rw [pmCompleteRamanujanFermiSource,
    pmCompleteRamanujanPrimitive_eq_normalized hε S hS,
    pmCompleteRamanujanPrimitive_eq_normalized hε S hS,
    pmFinitePrimePowerDampedFermiSource_eq_floor_difference ε S hS ht]
  ring

theorem pmRamanujanApertureScale_ge_density {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (pmPowerDampedDivisorDensity ε).re ≤ pmRamanujanApertureScale ε S := by
  have hprod : 1 ≤ ∏ p ∈ S, (1 + 1 / ((p : ℝ)^(1+ε)-1)) := by
    apply Finset.one_le_prod
    intro p hp
    have hb := pmPowerDampedRamanujan_prime_denominator_one_lt hε (hS p hp)
    have : 0 ≤ 1 / ((p : ℝ)^(1+ε)-1) := by positivity
    linarith
  exact le_mul_of_one_le_right (pmPowerDampedDivisorDensity_re_pos hε).le hprod

theorem pmRamanujanApertureScale_pos {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 < pmRamanujanApertureScale ε S :=
  (pmPowerDampedDivisorDensity_re_pos hε).trans_le (pmRamanujanApertureScale_ge_density hε S hS)

private theorem completeFermi_ae {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    pmCompleteRamanujanFermiSource ε S =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (pmRamanujanApertureScale ε S : ℂ) • pmFinitePrimePowerDampedFermiSource S ε := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact pmCompleteRamanujanFermiSource_eq_normalized hε S hS ht

theorem memLp_pmCompleteRamanujanFermiSource {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    MemLp (pmCompleteRamanujanFermiSource ε S) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_congr_ae (completeFermi_ae hε S hS)).mpr
    ((memLp_pmFinitePrimePowerDampedFermiSource S ε).const_smul
      (pmRamanujanApertureScale ε S : ℂ))

theorem pmCompleteRamanujanFermiSource_norm_eq {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (eLpNorm (pmCompleteRamanujanFermiSource ε S) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal =
      pmRamanujanApertureScale ε S *
        (eLpNorm (pmFinitePrimePowerDampedFermiSource S ε) 2 (volume.restrict (Ioi (0 : ℝ)))).toReal := by
  rw [eLpNorm_congr_ae (completeFermi_ae hε S hS), eLpNorm_const_smul,
    ENNReal.toReal_mul, toReal_enorm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pmRamanujanApertureScale_pos hε S hS)]

/-- Even the actual Mobius-aligned Ramanujan coefficients diverge when prime supports are completed. -/
theorem tendsto_pmCompleteRamanujanFermiSource_norm_atTop {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1/2) :
    Tendsto (fun N : ℕ =>
      (eLpNorm (pmCompleteRamanujanFermiSource ε (mobiusFinitePrimeAperture N))
        2 (volume.restrict (Ioi (0 : ℝ)))).toReal) atTop atTop := by
  have hbase := (tendsto_pmCanonicalPrime_norm_atTop hε0 hε1).const_mul_atTop
    (pmPowerDampedDivisorDensity_re_pos hε0)
  apply tendsto_atTop_mono (fun N => ?_) hbase
  have hS : ∀ p ∈ mobiusFinitePrimeAperture N, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  rw [pmCompleteRamanujanFermiSource_norm_eq hε0 _ hS]
  exact mul_le_mul_of_nonneg_right (pmRamanujanApertureScale_ge_density hε0 _ hS)
    ENNReal.toReal_nonneg

/-- Completing prime supports retains a uniformly summable coefficient-square mass. -/
theorem pmCompleteRamanujan_logSquareMass_le {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ T ∈ S.powerset, pmPowerDampedRamanujanLogSquareTerm ε (∏ p ∈ T, p)) ≤
      ∑' q : ℕ, pmPowerDampedRamanujanLogSquareTerm ε q := by
  rw [← Finset.sum_image (prod_primes_injOn hS)]
  exact (summable_pmPowerDampedRamanujanLogSquareTerm hε).sum_le_tsum _
    (fun q _ => pmPowerDampedRamanujanLogSquareTerm_nonneg ε q)


/-- No coefficient-square ceiling can hold uniformly over completed prime supports. -/
theorem pmCompleteRamanujan_eventually_exceeds_logSquare_budget {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1/2) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      C * (∑ T ∈ (mobiusFinitePrimeAperture N).powerset,
        pmPowerDampedRamanujanLogSquareTerm ε (∏ p ∈ T, p)) <
      (eLpNorm (pmCompleteRamanujanFermiSource ε (mobiusFinitePrimeAperture N))
        2 (volume.restrict (Ioi (0 : ℝ)))).toReal^2 := by
  let L := ∑' q : ℕ, pmPowerDampedRamanujanLogSquareTerm ε q
  let B := max C 0 * L
  have hL : 0 ≤ L := tsum_nonneg (pmPowerDampedRamanujanLogSquareTerm_nonneg ε)
  have hB : 0 ≤ B := mul_nonneg (le_max_right _ _) hL
  have ht := (tendsto_pmCompleteRamanujanFermiSource_norm_atTop hε0 hε1).eventually
    (eventually_gt_atTop (B+1))
  filter_upwards [ht] with N hN
  have hS : ∀ p ∈ mobiusFinitePrimeAperture N, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hm := pmCompleteRamanujan_logSquareMass_le hε0 _ hS
  have hm0 : 0 ≤ ∑ T ∈ (mobiusFinitePrimeAperture N).powerset,
      pmPowerDampedRamanujanLogSquareTerm ε (∏ p ∈ T, p) :=
    Finset.sum_nonneg (fun T _ => pmPowerDampedRamanujanLogSquareTerm_nonneg ε _)
  have hcap : C * (∑ T ∈ (mobiusFinitePrimeAperture N).powerset,
      pmPowerDampedRamanujanLogSquareTerm ε (∏ p ∈ T, p)) ≤ B :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hm0).trans
      (mul_le_mul_of_nonneg_left hm (le_max_right C 0))
  have hsq := sq_nonneg ((eLpNorm (pmCompleteRamanujanFermiSource ε (mobiusFinitePrimeAperture N))
    2 (volume.restrict (Ioi (0 : ℝ)))).toReal - 1)
  nlinarith

theorem pmCompleteMobiusFloor_one (ε : ℝ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : pmCompleteMobiusFloor ε S 1 = 1 := by
  rw [pmCompleteMobiusFloor_eq_coefficient_sum ε S hS, Finset.sum_eq_single 1]
  · simp [finitePrimeApertureMobiusCoefficient, mobiusComplexCoefficient]
  · intro d hd hne
    have hlt : 1 < d := by have := (Finset.mem_Icc.mp hd).1; omega
    simp [Nat.div_eq_of_lt hlt]
  · intro hnot
    have hprod : 1 ≤ ∏ p ∈ S, p := Finset.prod_pos (fun p hp => (hS p hp).pos)
    exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, hprod⟩)).elim

/-- The normalizer is exactly the actual probability mass of the completed aperture. -/
theorem pmRamanujanApertureScale_eq_weight_mass {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    pmRamanujanApertureScale ε S =
      ∑ T ∈ S.powerset, ‖pmPowerDampedRamanujanWeight ε (∏ p ∈ T, p)‖ := by
  apply Complex.ofReal_injective
  have h := pmCompleteRamanujanPrimitive_eq_normalized hε S hS 1
  rw [pmCompleteMobiusFloor_one ε S hS, mul_one] at h
  rw [← h, Complex.ofReal_sum, pmCompleteRamanujanPrimitive]
  apply Finset.sum_congr rfl
  intro T hT
  simpa [pmRamanujanPrimitive, pm_ramanujan_at_one, mul_comm] using
    pmPowerDampedRamanujanWeight_mobius_pair hε 1 (∏ p ∈ T, p)

theorem pmRamanujanApertureScale_le_one {ε : ℝ} (hε : 0 < ε)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) : pmRamanujanApertureScale ε S ≤ 1 := by
  rw [pmRamanujanApertureScale_eq_weight_mass hε S hS,
    ← Finset.sum_image (f := fun q => ‖pmPowerDampedRamanujanWeight ε q‖)
      (prod_primes_injOn hS), ← (hasSum_norm_pmPowerDampedRamanujanWeight hε).tsum_eq]
  exact (hasSum_norm_pmPowerDampedRamanujanWeight hε).summable.sum_le_tsum _ (fun q _ => norm_nonneg _)

end RHTower
