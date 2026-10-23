import GaloisForLFunctions.ArithmeticCompensationTheory.CompensationCoordinates

/-!
# The compensation defect of the large-prime sector decays logarithmically

`CompensationCoordinates` writes the complete head energy of the damped Möbius–Ramanujan
expansion at cutoff `P²` as `(1 − α_P)²‖L_P‖² + ‖R_P‖²`, so the **compensation defect**
`(1 − α_P)² + ‖R_P‖²/‖L_P‖²` is the relative complete energy
(`eventually_compensationDefect_eq_relative`), and `RHTower.PMRamanujanComplementaryCancellation` shows it
tends to `0`. This file gives the rate.

* The large-prime sector energy is at least `c P^{1−2ε}/log² P`, through the mass of the prime
  band `(P, 2P]` (`sectorEnergy_eventually_lower`).
* The complete head energy is at most `2 Σ_{N ≤ P} |R_ε(N)|²/(N(N+1)) + 2T⁴P^{1−3ε}`, the
  Ramanujan truncation costing `T⁴P^{1−3ε}` (`prefixEnergy_le`), and the remainder energy is at
  most `O(P^{(1−2ε)/2}) + O(1) + O(P^{1−2ε}/log⁸ P)` by the `log⁴`-saving bound on the damped
  divisor remainder (`remainderEnergy_le`).

Hence (`exists_compensationDefect_le_inv_log_pow_six`)

`(1 − α_P)² + ‖R_P‖²/‖L_P‖² ≤ K/log⁶ P`  for all large `P`,

an explicit rate of compensation on the actual source, stronger than the relative cancellation,
and summable over the dyadic scales `P = 2^k` (`summable_compensationDefect_dyadic`).
It is a logarithmic saving against a sector of size `P^{1−2ε}/log² P`: the absolute complete
energy it leaves, `O(P^{1−2ε}/log⁸ P)`, still grows with the cutoff. A power saving in the defect
would be a power saving in the receiver, which is the zero-width problem.
-/

open Finset Filter Topology Complex ArithmeticFunction RHTower
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## The size of the receiver and of the sector -/

/-- `(N^{1−ε})²/(N(N+1)) ≤ N^{−2ε}`. -/
theorem rpow_sq_div_pronic_le {ε : ℝ} {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ)^(1-ε))^2/((N : ℝ)*((N : ℝ)+1)) ≤ (N : ℝ)^(-2*ε) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have he : ((N : ℝ)^(1-ε))^2 = (N : ℝ)^(-2*ε)*(N : ℝ)^2 := by
    rw [← Real.rpow_natCast ((N : ℝ)^(1-ε)) 2, ← Real.rpow_mul hN0.le,
      ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hN0]
    congr 1
    ring
  rw [he, div_le_iff₀ (by positivity)]
  have hp := mul_nonneg (Real.rpow_nonneg hN0.le (-2*ε)) hN0.le
  nlinarith

private theorem weighted_sq_norm_le {z : ℂ} {ε A B : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) (hz : ‖z‖ ≤ A+B*(N : ℝ)^(1-ε)) :
    ‖z‖^2/((N : ℝ)*((N : ℝ)+1)) ≤
      2*A^2*(N : ℝ)^(-2 : ℝ)+2*B^2*(N : ℝ)^(-2*ε) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hb : ‖z‖^2 ≤ 2*A^2+2*B^2*((N : ℝ)^(1-ε))^2 := by
    nlinarith [sq_nonneg (A-B*(N : ℝ)^(1-ε))]
  have hone : 1/((N : ℝ)*((N : ℝ)+1)) ≤ (N : ℝ)^(-2 : ℝ) := by
    rw [Real.rpow_neg hN0.le, Real.rpow_two]
    simpa only [one_div] using (one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (N : ℝ)^2)
      (by nlinarith : (N : ℝ)^2 ≤ (N : ℝ)*((N : ℝ)+1)))
  have hp := rpow_sq_div_pronic_le (ε := ε) hN
  calc
    _ ≤ (2*A^2+2*B^2*((N : ℝ)^(1-ε))^2)/((N : ℝ)*((N : ℝ)+1)) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = 2*A^2*(1/((N : ℝ)*((N : ℝ)+1)))+
        2*B^2*(((N : ℝ)^(1-ε))^2/((N : ℝ)*((N : ℝ)+1))) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hone (by positivity))
      (mul_le_mul_of_nonneg_left hp (by positivity))

/-- The damped divisor remainder is `O(N^{1−ε})` at every integer `N ≥ 1`, for `0 < ε < ½`. -/
theorem divisorRemainder_le_global {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
      ‖pmPowerDampedDivisorRemainder ε N‖ ≤ A*(N : ℝ)^(1-ε) := by
  obtain ⟨C, hC, hc⟩ := pmPowerDampedDivisorRemainder_eventually_log_four hε hεhalf
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hc.and hl)
  let A : ℝ := 1+C+∑ n ∈ range K, ‖pmPowerDampedDivisorRemainder ε n‖
  have hsum0 : 0 ≤ ∑ n ∈ range K, ‖pmPowerDampedDivisorRemainder ε n‖ :=
    sum_nonneg (fun _ _ => norm_nonneg _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 1 ≤ (N : ℝ)^(1-ε) := Real.one_le_rpow hNR (by linarith)
  by_cases hNK : N < K
  · have hs := Finset.single_le_sum (fun (n : ℕ) _ => norm_nonneg (pmPowerDampedDivisorRemainder ε n))
      (mem_range.mpr hNK)
    have hh : ‖pmPowerDampedDivisorRemainder ε N‖ ≤ A := by dsimp only [A]; linarith
    exact hh.trans (le_mul_of_one_le_right hA hp)
  · obtain ⟨hbound, hlog⟩ := hK N (by omega)
    have hpow : 1 ≤ Real.log (N : ℝ)^4 := one_le_pow₀ hlog
    have hdiv : C*(N : ℝ)^(1-ε)/Real.log (N : ℝ)^4 ≤ C*(N : ℝ)^(1-ε) :=
      div_le_self (by positivity) hpow
    have hAC : 1+C ≤ A := by dsimp only [A]; linarith
    have hh := mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg (Nat.cast_nonneg N) (1-ε))
    nlinarith

/-- The pronic energy of the damped divisor remainder up to `P`: a `√P`-head, a constant, and a
tail saving `log⁸ P` against `P^{1−2ε}`. -/
theorem remainderEnergy_le {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ᶠ P : ℕ in atTop,
      (∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1))) ≤
        2*A^2*(1+(P : ℝ)^((1-2*ε)/2)/(1-2*ε)) +
        2*(∑' n : ℕ, (n : ℝ)^(-2 : ℝ)) +
        (512*C^2/Real.log (P : ℝ)^8)*(1+(P : ℝ)^(1-2*ε)/(1-2*ε)) := by
  obtain ⟨A, hA, hglobal⟩ := divisorRemainder_le_global hε hεhalf
  obtain ⟨C, hC, hc⟩ := pmPowerDampedDivisorRemainder_eventually_log_four hε hεhalf
  obtain ⟨K, hK⟩ := eventually_atTop.mp hc
  refine ⟨A, C, hA, hC, ?_⟩
  have hroot := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (K : ℝ)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hroot, hlog, eventually_ge_atTop 1] with P hrootP hlogP hP
  dsimp only [Function.comp_def] at hrootP hlogP
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := zero_lt_one.trans_le hPR
  have hl0 : 0 < Real.log (P : ℝ) := by linarith
  have hδ : 0 < 1-2*ε := by linarith
  let T := ⌊Real.sqrt (P : ℝ)⌋₊
  let w : ℕ → ℝ := fun N => ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1))
  have hT : (T : ℝ) ≤ Real.sqrt (P : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hTP : T ≤ P := by
    apply Nat.floor_le_of_le
    nlinarith [Real.sq_sqrt hP0.le, Real.sqrt_nonneg (P : ℝ)]
  have hsmall : (∑ N ∈ Icc 1 T, w N) ≤ 2*A^2*(1+(P : ℝ)^((1-2*ε)/2)/(1-2*ε)) := by
    calc
      _ ≤ ∑ N ∈ Icc 1 T, 2*A^2*(N : ℝ)^(-2*ε) := by
        apply Finset.sum_le_sum
        intro N hN
        simpa only [zero_add, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, zero_mul] using
          weighted_sq_norm_le (ε := ε) (A := 0) (B := A) (mem_Icc.mp hN).1 le_rfl hA
            (by simpa using hglobal N (mem_Icc.mp hN).1)
      _ = 2*A^2*(∑ N ∈ Icc 1 T, (N : ℝ)^(-(2*ε))) := by simp only [Finset.mul_sum, neg_mul]
      _ ≤ 2*A^2*(1+(T : ℝ)^(1-2*ε)/(1-2*ε)) :=
        mul_le_mul_of_nonneg_left (sum_rpow_neg_head_le (by positivity : 0 < 2*ε) (by linarith) T) (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add le_rfl
        apply div_le_div_of_nonneg_right _ hδ.le
        calc
          (T : ℝ)^(1-2*ε) ≤ (Real.sqrt (P : ℝ))^(1-2*ε) := Real.rpow_le_rpow (Nat.cast_nonneg _) hT hδ.le
          _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP0.le]; congr 1; ring
  have hlargeTerm (N : ℕ) (hN : N ∈ Ioc T P) :
      w N ≤ 2*(N : ℝ)^(-2 : ℝ)+(512*C^2/Real.log (P : ℝ)^8)*(N : ℝ)^(-2*ε) := by
    have hN1 : 1 ≤ N := by have := (mem_Ioc.mp hN).1; omega
    have hNr : Real.sqrt (P : ℝ) < N :=
      (Nat.floor_lt (Real.sqrt_nonneg _)).mp (mem_Ioc.mp hN).1
    have hNK : K ≤ N := by exact_mod_cast (hrootP.trans hNr.le)
    have hln : Real.log (P : ℝ)/2 ≤ Real.log (N : ℝ) := by
      rw [← Real.log_sqrt hP0.le]
      exact Real.log_le_log (Real.sqrt_pos.2 hP0) hNr.le
    have hcoef : C/Real.log (N : ℝ)^4 ≤ 16*C/Real.log (P : ℝ)^4 := by
      calc
        _ ≤ C/(Real.log (P : ℝ)/2)^4 := div_le_div_of_nonneg_left hC (by positivity)
          (pow_le_pow_left₀ (by positivity) hln 4)
        _ = _ := by rw [div_pow]; norm_num; ring
    have hz : ‖pmPowerDampedDivisorRemainder ε N‖ ≤
        1+(16*C/Real.log (P : ℝ)^4)*(N : ℝ)^(1-ε) := by
      have hb := hK N hNK
      have hm := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (Nat.cast_nonneg N) (1-ε))
      apply hb.trans
      calc
        _ = 1+(C/Real.log (N : ℝ)^4)*(N : ℝ)^(1-ε) := by ring
        _ ≤ _ := add_le_add le_rfl hm
    have hw := weighted_sq_norm_le (ε := ε) hN1 (by positivity : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ 16*C/Real.log (P : ℝ)^4) hz
    dsimp only [w]
    convert hw using 1; ring
  have hlarge : (∑ N ∈ Ioc T P, w N) ≤ 2*(∑' n : ℕ, (n : ℝ)^(-2 : ℝ))+
      (512*C^2/Real.log (P : ℝ)^8)*(1+(P : ℝ)^(1-2*ε)/(1-2*ε)) := by
    have hg : Summable (fun n : ℕ => (n : ℝ)^(-2 : ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
    calc
      _ ≤ ∑ N ∈ Ioc T P, (2*(N : ℝ)^(-2 : ℝ)+(512*C^2/Real.log (P : ℝ)^8)*(N : ℝ)^(-2*ε)) :=
        Finset.sum_le_sum hlargeTerm
      _ ≤ ∑ N ∈ Icc 1 P, (2*(N : ℝ)^(-2 : ℝ)+(512*C^2/Real.log (P : ℝ)^8)*(N : ℝ)^(-2*ε)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro N hN
          obtain ⟨hTN,hNP⟩ := mem_Ioc.mp hN
          exact mem_Icc.mpr ⟨by omega,hNP⟩
        · intro N _ _
          positivity
      _ = 2*(∑ N ∈ Icc 1 P, (N : ℝ)^(-2 : ℝ))+
          (512*C^2/Real.log (P : ℝ)^8)*(∑ N ∈ Icc 1 P, (N : ℝ)^(-(2*ε))) := by
        simp only [sum_add_distrib, mul_sum, neg_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (hg.sum_le_tsum _ (fun N _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity))
        (mul_le_mul_of_nonneg_left (sum_rpow_neg_head_le (by positivity : 0 < 2*ε) (by linarith) P) (by positivity))
  have hu : Icc 1 P = Icc 1 T ∪ Ioc T P := by
    ext N
    simp only [mem_Icc,mem_union,mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 T) (Ioc T P) := by
    apply Finset.disjoint_left.mpr
    intro N hn hm
    have := (mem_Icc.mp hn).2
    have := (mem_Ioc.mp hm).1
    omega
  change (∑ N ∈ Icc 1 P, w N) ≤ _
  rw [hu, Finset.sum_union hd]
  linarith

/-- The complete head energy is controlled by the divisor-remainder energy plus the Ramanujan
truncation cost `2T⁴P^{1−3ε}`. -/
theorem prefixEnergy_le {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ P : ℕ, 1 ≤ P →
      pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) P ≤
        2*(∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1))) +
        2*T^4*(P : ℝ)^(1-3*ε) := by
  let β : ℝ := 3*ε/4
  let T : ℝ := ∑' m : ℕ, (m : ℝ)^(-(1+ε-β))
  have hT : 0 ≤ T := tsum_nonneg (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨T,hT,?_⟩
  intro P hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  let D : ℝ := ((P^2 : ℕ) : ℝ)^(-β)*T^2
  have hD : 0 ≤ D := by positivity
  have hterm (N : ℕ) (hN : N ∈ Icc 1 P) :
      ‖pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N‖^2/((N : ℝ)*((N : ℝ)+1)) ≤
        2*(‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1)))+2*D^2 := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (mem_Icc.mp hN).1
    have hb := norm_pmPowerDampedRamanujanCumulativePrefix_sub_remainder_le hε
      (show 0 ≤ β by dsimp only [β]; positivity) (show β < ε by dsimp only [β]; linarith)
      (show 0 < P^2 by positivity) (show N ≤ P^2 by have := (mem_Icc.mp hN).2; nlinarith)
    have hn : ‖pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N‖ ≤
        ‖pmPowerDampedDivisorRemainder ε N‖+D*N := by
      have hh := norm_add_le (pmPowerDampedDivisorRemainder ε N)
        (pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N-pmPowerDampedDivisorRemainder ε N)
      have he : pmPowerDampedDivisorRemainder ε N +
          (pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N-pmPowerDampedDivisorRemainder ε N) =
          pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N := by ring
      rw [he] at hh
      dsimp only [D,T] at *
      nlinarith
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hh : ‖pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N‖^2 ≤
        2*‖pmPowerDampedDivisorRemainder ε N‖^2+2*D^2*(N : ℝ)^2 := by
      nlinarith [sq_nonneg (‖pmPowerDampedDivisorRemainder ε N‖-D*N)]
    rw [div_le_iff₀ (by positivity)]
    have he : (2*(‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1)))+2*D^2)*
        ((N : ℝ)*((N : ℝ)+1)) =
        2*‖pmPowerDampedDivisorRemainder ε N‖^2+2*D^2*((N : ℝ)*((N : ℝ)+1)) := by field_simp
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg D) hN0.le]
  have hpow : ((P^2 : ℕ) : ℝ)^(-β) = (P : ℝ)^(-2*β) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (P : ℝ) 2, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  have hpow2 : ((P : ℝ)^(-2*β))^2 = (P : ℝ)^(-4*β) := by
    rw [← Real.rpow_natCast ((P : ℝ)^(-2*β)) 2, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  have hlast : (P : ℝ)^(-4*β)*(P : ℝ) = (P : ℝ)^(1-3*ε) := by
    calc
      _ = (P : ℝ)^(-4*β)*(P : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hP0]; congr 1; dsimp only [β]; ring
  have heD : 2*D^2*(P : ℝ) = 2*T^4*(P : ℝ)^(1-3*ε) := by
    dsimp only [D]
    rw [hpow,mul_pow,hpow2]
    calc
      _ = 2*T^4*((P : ℝ)^(-4*β)*(P : ℝ)) := by ring
      _ = _ := by rw [hlast]
  calc
    _ ≤ ∑ N ∈ Icc 1 P, (2*(‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1)))+2*D^2) :=
      Finset.sum_le_sum hterm
    _ = 2*(∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1)))+2*D^2*P := by
      simp only [sum_add_distrib,← mul_sum,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
      ring
    _ = _ := by rw [heD]

/-- The large-prime sector energy is at least `c P^{1−2ε}/log² P`. -/
theorem sectorEnergy_eventually_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ P : ℕ in atTop,
      c*(P : ℝ)^(1-2*ε)/Real.log (P : ℝ)^2 ≤ pmRamanujanLargePrimeSectorEnergy ε P := by
  let A := (pmPowerDampedDivisorDensity ε).re
  let k : ℝ := (2 : ℝ)^(-ε)/65536
  let c : ℝ := A^2*k^2/16
  have hA : 0 < A := pmPowerDampedDivisorDensity_re_pos hε
  have hk : 0 < k := by dsimp only [k]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨c,hc,?_⟩
  filter_upwards [pmRamanujanLargePrimeMass_eventually_lower hε,
    pmRamanujanLargePrimeSectorEnergy_eventually_lower hε,eventually_ge_atTop 2] with P hM hE hP
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hl : 0 < Real.log (P : ℝ) := Real.log_pos hP1
  have hl2 : 0 < Real.log (2*(P : ℝ)) := Real.log_pos (by linarith)
  have hlog : Real.log (2*(P : ℝ)) ≤ 2*Real.log (P : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ P by exact_mod_cast hP)
    linarith
  have hmass : k*(P : ℝ)^(-ε)/Real.log (P : ℝ) ≤ pmRamanujanLargePrimeMass ε P := by
    apply le_trans _ hM
    calc
      _ = (2*(P : ℝ))^(-ε)/(32768*(2*Real.log (P : ℝ))) := by
        dsimp only [k]
        rw [Real.mul_rpow (by norm_num) hP0.le]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _) (by positivity)
        (mul_le_mul_of_nonneg_left hlog (by norm_num))
  have hs := pow_le_pow_left₀ (show 0 ≤ k*(P : ℝ)^(-ε)/Real.log (P : ℝ) by positivity) hmass 2
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ A^2*(P : ℝ)/16 by positivity)
  have hp : (P : ℝ)*((P : ℝ)^(-ε))^2 = (P : ℝ)^(1-2*ε) := by
    calc
      _ = (P : ℝ)^(1 : ℝ)*((P : ℝ)^(-ε))^2 := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_natCast ((P : ℝ)^(-ε)) 2, ← Real.rpow_mul hP0.le, ← Real.rpow_add hP0]
        congr 1
        ring
  have he : A^2*(P : ℝ)/16*(k*(P : ℝ)^(-ε)/Real.log (P : ℝ))^2 =
      c*(P : ℝ)^(1-2*ε)/Real.log (P : ℝ)^2 := by
    dsimp only [c]
    calc
      _ = (A^2*k^2/16)*((P : ℝ)*((P : ℝ)^(-ε))^2)/Real.log (P : ℝ)^2 := by ring
      _ = _ := by rw [hp]
  rw [he] at hh
  dsimp only [A] at hh
  nlinarith

/-! ## The rate -/

/-- The compensation defect `(1 − α_P)² + ‖R_P‖²/‖L_P‖²` of the large-prime sector at cutoff `P²`. -/
def compensationDefect (ε : ℝ) (P : ℕ) : ℝ :=
  (1 - pmCompensationAmplitude ε P) ^ 2 +
    pmTransverseEnergy ε P / pmRamanujanLargePrimeSectorEnergy ε P

theorem compensationDefect_nonneg (ε : ℝ) {P : ℕ} (hP : 2 ≤ P) : 0 ≤ compensationDefect ε P :=
  add_nonneg (sq_nonneg _) (div_nonneg (pmCompleteHeadEnergy_eq_compensation hP ε).2
    (by unfold pmRamanujanLargePrimeSectorEnergy; positivity))

/-- **The compensation defect is the relative complete head energy**, at every cutoff where the
sector energy is positive, in particular at all large `P` when `0 < ε < ½`. -/
theorem eventually_compensationDefect_eq_relative {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ P : ℕ in atTop, compensationDefect ε P =
      pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) /
        pmRamanujanLargePrimeSectorEnergy ε P := by
  filter_upwards [(tendsto_pmRamanujanLargePrimeSectorEnergy_atTop hε hεhalf).eventually_gt_atTop 0,
    eventually_ge_atTop 2] with P hL hP
  rw [compensationDefect, (pmCompleteHeadEnergy_eq_compensation hP ε).1]
  field_simp

theorem prefixEnergy_mono (ε : ℝ) (Q : ℕ) {T T' : ℕ} (h : T ≤ T') :
    pmPowerDampedRamanujanPrefixEnergy ε Q T ≤ pmPowerDampedRamanujanPrefixEnergy ε Q T' :=
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun _ _ _ => by positivity

/-- `log⁸ P / P^s → 0` along the integers. -/
theorem tendsto_log_pow_eight_div_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun P : ℕ => Real.log P ^ 8 / (P : ℝ) ^ s) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (8 : ℝ) hs).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun P => ?_
  simp only [Function.comp_apply]
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- **The compensation defect decays like `log⁻⁶ P`.** For `0 < ε < ½` there is `K` with
`(1 − α_P)² + ‖R_P‖²/‖L_P‖² ≤ K/log⁶ P` for all large `P`. -/
theorem exists_compensationDefect_le_inv_log_pow_six {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ K : ℝ, ∀ᶠ P : ℕ in atTop, compensationDefect ε P ≤ K / Real.log P ^ 6 := by
  obtain ⟨A, C, hA, hC, hrem⟩ := remainderEnergy_le hε hεhalf
  obtain ⟨T, hT, hpre⟩ := prefixEnergy_le hε
  obtain ⟨c, hc, hsec⟩ := sectorEnergy_eventually_lower hε
  set d : ℝ := 1 - 2 * ε with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ)
  have hZ : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  set K₀ : ℝ := 1024 * C ^ 2 * (1 + 1 / d) / c
  refine ⟨3 + K₀, ?_⟩
  have l1 := ((tendsto_log_pow_eight_div_rpow hd).const_mul ((4 * A ^ 2 + 4 * Z) / c)).eventually
    (eventually_le_nhds (show ((4 * A ^ 2 + 4 * Z) / c) * 0 < 1 by rw [mul_zero]; norm_num))
  have l2 := ((tendsto_log_pow_eight_div_rpow (half_pos hd)).const_mul (4 * A ^ 2 / (c * d))).eventually
    (eventually_le_nhds (show (4 * A ^ 2 / (c * d)) * 0 < 1 by rw [mul_zero]; norm_num))
  have l3 := ((tendsto_log_pow_eight_div_rpow hε).const_mul (2 * T ^ 4 / c)).eventually
    (eventually_le_nhds (show (2 * T ^ 4 / c) * 0 < 1 by rw [mul_zero]; norm_num))
  filter_upwards [hrem, hsec, l1, l2, l3, eventually_ge_atTop 2,
    eventually_compensationDefect_eq_relative hε hεhalf] with P hR hS h1 h2 h3 hP hrel
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos hP1
  set L : ℝ := Real.log P ^ 8 with hLdef
  have hL : 0 < L := by positivity
  have hPd : 0 < (P : ℝ) ^ d := Real.rpow_pos_of_pos hP0 d
  have hPd2 : 0 < (P : ℝ) ^ (d / 2) := Real.rpow_pos_of_pos hP0 _
  have hPe : 0 < (P : ℝ) ^ ε := Real.rpow_pos_of_pos hP0 _
  have hPd1 : 1 ≤ (P : ℝ) ^ d := Real.one_le_rpow hP1.le hd.le
  have hsplit2 : (P : ℝ) ^ (d / 2) * (P : ℝ) ^ (d / 2) = (P : ℝ) ^ d := by
    rw [← Real.rpow_add hP0]; ring_nf
  have hsplit3 : (P : ℝ) ^ ε * (P : ℝ) ^ (1 - 3 * ε) = (P : ℝ) ^ d := by
    rw [← Real.rpow_add hP0, hddef]; ring_nf
  -- the three vanishing terms, multiplied out
  have m1 : (4 * A ^ 2 + 4 * Z) * L ≤ c * (P : ℝ) ^ d := by
    rw [div_mul_div_comm, div_le_one (by positivity)] at h1; linarith
  have m2 : 4 * A ^ 2 / d * L * (P : ℝ) ^ (d / 2) ≤ c * (P : ℝ) ^ d := by
    rw [div_mul_div_comm, div_le_one (by positivity)] at h2
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (P : ℝ) ^ (d / 2) / d)
    calc 4 * A ^ 2 / d * L * (P : ℝ) ^ (d / 2) = 4 * A ^ 2 * L * ((P : ℝ) ^ (d / 2) / d) := by
          ring
      _ ≤ c * d * (P : ℝ) ^ (d / 2) * ((P : ℝ) ^ (d / 2) / d) := this
      _ = c * (P : ℝ) ^ d := by rw [← hsplit2]; field_simp
  have m3 : 2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε) * L ≤ c * (P : ℝ) ^ d := by
    rw [div_mul_div_comm, div_le_one (by positivity)] at h3
    have := mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hP0.le (1 - 3 * ε))
    calc 2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε) * L = 2 * T ^ 4 * L * (P : ℝ) ^ (1 - 3 * ε) := by
          ring
      _ ≤ c * (P : ℝ) ^ ε * (P : ℝ) ^ (1 - 3 * ε) := this
      _ = c * (P : ℝ) ^ d := by rw [mul_assoc, hsplit3]
  have m4 : 512 * C ^ 2 / L * (1 + (P : ℝ) ^ d / d) * L ≤ K₀ / 2 * c * (P : ℝ) ^ d := by
    have h1' : 512 * C ^ 2 / L * (1 + (P : ℝ) ^ d / d) * L = 512 * C ^ 2 * (1 + (P : ℝ) ^ d / d) :=
      by field_simp
    rw [h1']
    have h2' : 1 + (P : ℝ) ^ d / d ≤ (1 + 1 / d) * (P : ℝ) ^ d := by
      have : (P : ℝ) ^ d / d = 1 / d * (P : ℝ) ^ d := by ring
      rw [this]; nlinarith
    calc 512 * C ^ 2 * (1 + (P : ℝ) ^ d / d) ≤ 512 * C ^ 2 * ((1 + 1 / d) * (P : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left h2' (by positivity)
      _ = K₀ / 2 * c * (P : ℝ) ^ d := by simp only [K₀]; field_simp; ring
  -- the bound on the complete energy
  set B : ℝ := 2 * (2 * A ^ 2 * (1 + (P : ℝ) ^ (d / 2) / d) + 2 * Z +
      512 * C ^ 2 / L * (1 + (P : ℝ) ^ d / d)) + 2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε)
  have hcomp : pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) ≤ B := by
    refine (prefixEnergy_mono ε _ (Nat.sub_le P 1)).trans ((hpre P (by omega)).trans ?_)
    have hR' := hR
    rw [show (1 - 2 * ε) / 2 = d / 2 by rw [hddef]] at hR'
    simp only [B, hLdef]
    linarith
  have hBL : B * L ≤ (3 + K₀) * c * (P : ℝ) ^ d := by
    have e : B * L = (4 * A ^ 2 + 4 * Z) * L + 4 * A ^ 2 / d * L * (P : ℝ) ^ (d / 2) +
        2 * (512 * C ^ 2 / L * (1 + (P : ℝ) ^ d / d) * L) +
        2 * T ^ 4 * (P : ℝ) ^ (1 - 3 * ε) * L := by
      simp only [B]; field_simp; ring
    rw [e]
    nlinarith
  have hsecpos : 0 < pmRamanujanLargePrimeSectorEnergy ε P :=
    lt_of_lt_of_le (by positivity) hS
  rw [hrel, div_le_div_iff₀ hsecpos (by positivity)]
  have hl6 : Real.log P ^ 6 * Real.log P ^ 2 = L := by rw [hLdef]; ring
  have hlow : c * (P : ℝ) ^ d ≤ pmRamanujanLargePrimeSectorEnergy ε P * Real.log P ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hS
    simpa [hddef] using hS
  have hK : 0 ≤ 3 + K₀ := by positivity
  calc pmPowerDampedRamanujanPrefixEnergy ε (P ^ 2 - 1) (P - 1) * Real.log P ^ 6
      ≤ B * Real.log P ^ 6 := mul_le_mul_of_nonneg_right hcomp (by positivity)
    _ = B * L / Real.log P ^ 2 := by rw [← hl6]; field_simp
    _ ≤ (3 + K₀) * c * (P : ℝ) ^ d / Real.log P ^ 2 :=
        div_le_div_of_nonneg_right hBL (by positivity)
    _ ≤ (3 + K₀) * (pmRamanujanLargePrimeSectorEnergy ε P * Real.log P ^ 2) / Real.log P ^ 2 := by
        rw [mul_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hK) (by positivity)
    _ = (3 + K₀) * pmRamanujanLargePrimeSectorEnergy ε P := by field_simp

/-- **The compensation defects are summable along dyadic scales.** The logarithmic rate is enough
to iterate over the scales `P = 2^k`: `Σ_k (1 − α_{2^k})² + ‖R_{2^k}‖²/‖L_{2^k}‖² < ∞`, while the
absolute complete energies `O(4^{k(1−2ε)}/k⁸)` are not summable. -/
theorem summable_compensationDefect_dyadic {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    Summable fun k : ℕ => compensationDefect ε (2 ^ k) := by
  obtain ⟨K, hK⟩ := exists_compensationDefect_le_inv_log_pow_six hε hεhalf
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun k : ℕ => |K| / Real.log 2 ^ 6 * (1 / (k : ℝ) ^ 6))
    ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _) ?_
  filter_upwards [h2.eventually hK, eventually_ge_atTop 1] with k hk hk1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  rw [Real.norm_eq_abs, abs_of_nonneg (compensationDefect_nonneg ε hk2)]
  have hlog : Real.log ((2 ^ k : ℕ) : ℝ) = k * Real.log 2 := by simp [Real.log_pow]
  calc compensationDefect ε (2 ^ k) ≤ K / Real.log ((2 ^ k : ℕ) : ℝ) ^ 6 := hk
    _ = K / ((k : ℝ) * Real.log 2) ^ 6 := by rw [hlog]
    _ ≤ |K| / ((k : ℝ) * Real.log 2) ^ 6 :=
        div_le_div_of_nonneg_right (le_abs_self K) (by positivity)
    _ = |K| / Real.log 2 ^ 6 * (1 / (k : ℝ) ^ 6) := by field_simp

end GaloisForLFunctions.ArithmeticCompensationTheory
