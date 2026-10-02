import GaloisForLFunctions.RHTower.PMRamanujanComplementarySourceBounds
import GaloisForLFunctions.RHTower.PMRamanujanGrowingCofactorHead

/-!
# Actual complementary cancellation of a divergent large-prime sector

At denominator cutoff `P^2`, let `L_P` contain every allowed cofactor of every
prime in `(P,2*P]`. The complement is the literal remaining denominator sum.
On `1 <= N < P`, all energies use the original weight `1/(N*(N+1))`.

For every fixed `0 < epsilon < 1/2`, the complete-prefix energy divided by
`E(L_P)` tends to zero, the complement-energy ratio tends to one, and the
signed mixed-energy ratio tends to minus one. Signed Möbius cancellation,
the actual coefficient-moment truncation estimate, and the quantitative
prime-sector lower bound discharge the source comparison.

The complete-energy estimate still retains a positive power of `P`. These
relative laws do not prove global PM admission or RH.
-/

open Finset Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem pmce_rpow_energy {ε : ℝ} {N : ℕ} (hN : 1 ≤ N) :
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

private theorem pmce_weighted_norm {z : ℂ} {ε A B : ℝ} {N : ℕ} (hN : 1 ≤ N)
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
  have hp := pmce_rpow_energy (ε := ε) hN
  calc
    _ ≤ (2*A^2+2*B^2*((N : ℝ)^(1-ε))^2)/((N : ℝ)*((N : ℝ)+1)) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = 2*A^2*(1/((N : ℝ)*((N : ℝ)+1)))+
        2*B^2*(((N : ℝ)^(1-ε))^2/((N : ℝ)*((N : ℝ)+1))) := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hone (by positivity))
      (mul_le_mul_of_nonneg_left hp (by positivity))

private theorem pmce_global_remainder {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
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

private theorem pmce_remainder_energy_bound {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 ≤ C ∧ ∀ᶠ P : ℕ in atTop,
      (∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1))) ≤
        2*A^2*(1+(P : ℝ)^((1-2*ε)/2)/(1-2*ε)) +
        2*(∑' n : ℕ, (n : ℝ)^(-2 : ℝ)) +
        (512*C^2/Real.log (P : ℝ)^8)*(1+(P : ℝ)^(1-2*ε)/(1-2*ε)) := by
  obtain ⟨A, hA, hglobal⟩ := pmce_global_remainder hε hεhalf
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
          pmce_weighted_norm (ε := ε) (A := 0) (B := A) (mem_Icc.mp hN).1 le_rfl hA
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
    have hw := pmce_weighted_norm (ε := ε) hN1 (by positivity : (0 : ℝ) ≤ 1)
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

private theorem pmce_remainder_energy_normalized {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun P : ℕ =>
      (∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1))) *
        Real.log (P : ℝ)^2/(P : ℝ)^(1-2*ε)) atTop (𝓝 0) := by
  obtain ⟨A,C,hA,hC,henergy⟩ := pmce_remainder_energy_bound hε hεhalf
  let d : ℝ := 1-2*ε
  let H : ℝ := ∑' n : ℕ, (n : ℝ)^(-2 : ℝ)
  have hd : 0 < d := by dsimp only [d]; linarith
  have h1 : Tendsto (fun P : ℕ => Real.log (P : ℝ)^2/(P : ℝ)^d) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hd).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun P : ℕ => Real.log (P : ℝ)^2/(P : ℝ)^(d/2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (half_pos hd)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlogtop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun P : ℕ => 1/Real.log (P : ℝ)^6) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div,inv_pow,zero_pow (by omega : (6 : ℕ) ≠ 0)] using
      (tendsto_inv_atTop_zero.comp hlogtop).pow 6
  have hmajor : Tendsto (fun P : ℕ =>
      2*A^2*(Real.log (P : ℝ)^2/(P : ℝ)^d+(1/d)*(Real.log (P : ℝ)^2/(P : ℝ)^(d/2))) +
      2*H*(Real.log (P : ℝ)^2/(P : ℝ)^d) +
      512*C^2*(1+1/d)*(1/Real.log (P : ℝ)^6)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (((h1.add (h2.const_mul (1/d))).const_mul (2*A^2)).add (h1.const_mul (2*H))).add
        (h3.const_mul (512*C^2*(1+1/d)))
  apply squeeze_zero' (Eventually.of_forall (fun P => by positivity)) ?_ hmajor
  filter_upwards [henergy,hlogtop.eventually_ge_atTop 2,eventually_ge_atTop 1] with P hE hlogP hP
  dsimp only [Function.comp_def] at hlogP
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := zero_lt_one.trans_le hP1
  have hl0 : 0 < Real.log (P : ℝ) := by linarith
  have hpd := Real.rpow_pos_of_pos hP0 d
  have hph := Real.rpow_pos_of_pos hP0 (d/2)
  have hp : 1 ≤ (P : ℝ)^d := Real.one_le_rpow hP1 hd.le
  have hone : 1+(P : ℝ)^d/d ≤ (1+1/d)*(P : ℝ)^d := by
    calc
      _ ≤ (P : ℝ)^d+(P : ℝ)^d/d := add_le_add hp le_rfl
      _ = _ := by ring
  have hlast := mul_le_mul_of_nonneg_left hone (show 0 ≤ 512*C^2/Real.log (P : ℝ)^8 by positivity)
  have hE' : (∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1))) ≤
      2*A^2*(1+(P : ℝ)^(d/2)/d)+2*H+
      (512*C^2/Real.log (P : ℝ)^8)*((1+1/d)*(P : ℝ)^d) := by
    dsimp only [d,H] at *
    linarith
  have hepow : (P : ℝ)^d = ((P : ℝ)^(d/2))^2 := by
    rw [← Real.rpow_natCast ((P : ℝ)^(d/2)) 2, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  calc
    _ ≤ (2*A^2*(1+(P : ℝ)^(d/2)/d)+2*H+
        (512*C^2/Real.log (P : ℝ)^8)*((1+1/d)*(P : ℝ)^d))*Real.log (P : ℝ)^2/(P : ℝ)^d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hE' (sq_nonneg _)) hpd.le
    _ = _ := by rw [hepow]; field_simp

private theorem pmce_prefix_energy_bound {ε : ℝ} (hε : 0 < ε) :
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

private theorem pmce_prefix_energy_normalized {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun P : ℕ => pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) P *
      Real.log (P : ℝ)^2/(P : ℝ)^(1-2*ε)) atTop (𝓝 0) := by
  obtain ⟨T,hT,hbound⟩ := pmce_prefix_energy_bound hε
  have hR := pmce_remainder_energy_normalized hε hεhalf
  have ht : Tendsto (fun P : ℕ => Real.log (P : ℝ)^2/(P : ℝ)^ε) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hmajor := (hR.const_mul 2).add (ht.const_mul (2*T^4))
  simp only [mul_zero,add_zero] at hmajor
  apply squeeze_zero' (Eventually.of_forall (fun P => by unfold pmPowerDampedRamanujanPrefixEnergy; positivity)) ?_ hmajor
  filter_upwards [eventually_ge_atTop 1] with P hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hb := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hbound P hP) (sq_nonneg (Real.log (P : ℝ))))
      (Real.rpow_nonneg hP0.le (1-2*ε))
  have he : (P : ℝ)^(1-3*ε)/(P : ℝ)^(1-2*ε) = (P : ℝ)^(-ε) := by
    rw [← Real.rpow_sub hP0]
    congr 1
    ring
  have hc : (P : ℝ)^(1-3*ε)*Real.log (P : ℝ)^2/(P : ℝ)^(1-2*ε) =
      Real.log (P : ℝ)^2/(P : ℝ)^ε := by
    calc
      _ = Real.log (P : ℝ)^2*((P : ℝ)^(1-3*ε)/(P : ℝ)^(1-2*ε)) := by ring
      _ = _ := by rw [he,Real.rpow_neg hP0.le]; ring
  apply hb.trans_eq
  calc
    _ = 2*((∑ N ∈ Icc 1 P, ‖pmPowerDampedDivisorRemainder ε N‖^2/((N : ℝ)*((N : ℝ)+1)))*
        Real.log (P : ℝ)^2/(P : ℝ)^(1-2*ε)) +
        2*T^4*((P : ℝ)^(1-3*ε)*Real.log (P : ℝ)^2/(P : ℝ)^(1-2*ε)) := by ring
    _ = _ := by rw [hc]

private theorem pmce_sector_eventually_lower {ε : ℝ} (hε : 0 < ε) :
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

/-- On the moving head, the complete signed prefix has negligible energy relative to its
literal divergent large-prime sector. This compares the original anchored weights. -/
theorem tendsto_pmRamanujanCompleteHeadEnergy_div_largePrimeSectorEnergy_zero
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun P : ℕ => pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) (P-1) /
      pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 0) := by
  obtain ⟨c,hc,hlower⟩ := pmce_sector_eventually_lower hε
  have ht := (pmce_prefix_energy_normalized hε hεhalf).div_const c
  simp only [zero_div] at ht
  apply squeeze_zero' (Eventually.of_forall (fun P => by
    unfold pmPowerDampedRamanujanPrefixEnergy pmRamanujanLargePrimeSectorEnergy
    positivity)) ?_ ht
  filter_upwards [hlower,eventually_ge_atTop 2] with P hlow hP
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hl : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hd : 0 < c*(P : ℝ)^(1-2*ε)/Real.log (P : ℝ)^2 := by positivity
  have hE0 : 0 < pmRamanujanLargePrimeSectorEnergy ε P := hd.trans_le hlow
  have hEP0 : 0 ≤ pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) P := by
    unfold pmPowerDampedRamanujanPrefixEnergy
    positivity
  have hmono : pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) (P-1) ≤
      pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) P := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.sub_le _ _))
    intro N _ _
    positivity
  calc
    _ ≤ pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) P / pmRamanujanLargePrimeSectorEnergy ε P :=
      div_le_div_of_nonneg_right hmono hE0.le
    _ ≤ pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) P /
        (c*(P : ℝ)^(1-2*ε)/Real.log (P : ℝ)^2) := div_le_div_of_nonneg_left hEP0 hd hlow
    _ = _ := by field_simp

/-- Actual denominator set of the growing large-prime sector at cutoff `P^2`. -/
def pmRamanujanLargePrimeDenominators (P : ℕ) : Finset ℕ :=
  (DeletionPeriodGrowth.upperPrimes (2*P)).biUnion
    (fun p => (Icc 1 (P^2/p)).image (fun r => p*r))

/-- Literal remaining denominator sum, retaining every original coefficient. -/
def pmRamanujanLargePrimeComplement (ε : ℝ) (P N : ℕ) : ℂ :=
  ∑ q ∈ Icc 2 (P^2) \ pmRamanujanLargePrimeDenominators P,
    pmPowerDampedRamanujanWeight ε q*pmRamanujanPrimitive q N

/-- Complement energy on the same moving head and original reciprocal weight. -/
def pmRamanujanLargePrimeComplementEnergy (ε : ℝ) (P : ℕ) : ℝ :=
  ∑ N ∈ Icc 1 (P-1), ‖pmRamanujanLargePrimeComplement ε P N‖^2/((N : ℝ)*((N : ℝ)+1))

/-- Signed mixed energy of the actual sector and its literal complement. -/
def pmRamanujanLargePrimeComplementMixedEnergy (ε : ℝ) (P : ℕ) : ℝ :=
  ∑ N ∈ Icc 1 (P-1), (pmRamanujanLargePrimeSector ε P N*
    star (pmRamanujanLargePrimeComplement ε P N)).re/((N : ℝ)*((N : ℝ)+1))

private theorem pmce_denominators_subset (P : ℕ) :
    pmRamanujanLargePrimeDenominators P ⊆ Icc 2 (P^2) := by
  intro q hq
  obtain ⟨p,hp,hq⟩ := mem_biUnion.mp hq
  obtain ⟨r,hr,rfl⟩ := mem_image.mp hq
  exact pmRamanujanLargePrimeSector_denominator_mem hp hr

private theorem pmce_sector_sum {P : ℕ} (hP : 2 ≤ P) (ε : ℝ) (N : ℕ) :
    (∑ q ∈ pmRamanujanLargePrimeDenominators P,
      pmPowerDampedRamanujanWeight ε q*pmRamanujanPrimitive q N) =
        pmRamanujanLargePrimeSector ε P N := by
  have hd : Set.PairwiseDisjoint (↑(DeletionPeriodGrowth.upperPrimes (2*P)) : Set ℕ)
      (fun p => (Icc 1 (P^2/p)).image (fun r => p*r)) := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨r,hr,he⟩ := mem_image.mp hn
    obtain ⟨s,hs,he'⟩ := mem_image.mp hm
    exact hpq (pmRamanujanLargePrimeSector_denominator_unique hP hp hq hr hs (he.trans he'.symm)).1
  rw [pmRamanujanLargePrimeDenominators,Finset.sum_biUnion hd,pmRamanujanLargePrimeSector]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_image]
  · rfl
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left (mem_filter.mp hp).2.1.pos hab

private theorem pmce_complete_sum (ε : ℝ) (Q N : ℕ) :
    pmPowerDampedRamanujanCumulativePrefix ε (Q-1) N =
      ∑ q ∈ Icc 2 Q, pmPowerDampedRamanujanWeight ε q*pmRamanujanPrimitive q N := by
  rw [pmPowerDampedRamanujanCumulativePrefix]
  simp only [pmPowerDampedRamanujanCenteredPrefix]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  change (∑ q ∈ range (Q-1), pmPowerDampedRamanujanWeight ε (q+2)*pmRamanujanPrimitive (q+2) N) = _
  rw [show Icc 2 Q = Ico 2 (Q+1) by ext q; simp, Finset.sum_Ico_eq_sum_range]
  simp only [show Q+1-2 = Q-1 by omega,Nat.add_comm]

/-- The complement is exactly the difference of the complete prefix and the selected sector. -/
theorem pmRamanujanLargePrimeComplement_eq_sub {P : ℕ} (hP : 2 ≤ P) (ε : ℝ) (N : ℕ) :
    pmRamanujanLargePrimeComplement ε P N =
      pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N-pmRamanujanLargePrimeSector ε P N := by
  rw [pmRamanujanLargePrimeComplement,Finset.sum_sdiff_eq_sub (pmce_denominators_subset P),
    pmce_sector_sum hP,← pmce_complete_sum]

private def pmce_cross (ε : ℝ) (P : ℕ) : ℝ :=
  ∑ N ∈ Icc 1 (P-1), (pmRamanujanLargePrimeSector ε P N*
    star (pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N)).re/((N : ℝ)*((N : ℝ)+1))

private theorem pmce_cross_sq_le (ε : ℝ) (P : ℕ) :
    (pmce_cross ε P)^2 ≤ pmRamanujanLargePrimeSectorEnergy ε P *
      pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) (P-1) := by
  unfold pmce_cross pmRamanujanLargePrimeSectorEnergy pmPowerDampedRamanujanPrefixEnergy
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun N _ => by positivity) (fun N _ => by positivity)
  intro N hN
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (Complex.abs_re_le_norm (pmRamanujanLargePrimeSector ε P N*
      star (pmPowerDampedRamanujanCumulativePrefix ε (P^2-1) N))) 2
  simp only [sq_abs,norm_mul,norm_star,mul_pow] at h
  have hh := div_le_div_of_nonneg_right h (sq_nonneg ((N : ℝ)*((N : ℝ)+1)))
  simpa only [div_pow,div_mul_div_comm,← pow_two] using hh

private theorem pmce_cross_normalized {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun P => pmce_cross ε P/pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 0) := by
  have hS := tendsto_pmRamanujanCompleteHeadEnergy_div_largePrimeSectorEnergy_zero hε hεhalf
  have hL := (tendsto_pmRamanujanLargePrimeSectorEnergy_atTop hε hεhalf).eventually_gt_atTop 0
  have hs : Tendsto (fun P => (pmce_cross ε P/pmRamanujanLargePrimeSectorEnergy ε P)^2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun P => sq_nonneg _)) ?_ hS
    filter_upwards [hL] with P hP
    rw [div_pow]
    apply (div_le_div_of_nonneg_right (pmce_cross_sq_le ε P) (sq_nonneg _)).trans_eq
    field_simp
  have hh := (Real.continuous_sqrt.tendsto 0).comp hs
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,Real.norm_eq_abs] using hh

private theorem pmce_complement_mixed_eq {P : ℕ} (hP : 2 ≤ P) (ε : ℝ) :
    pmRamanujanLargePrimeComplementMixedEnergy ε P = pmce_cross ε P-pmRamanujanLargePrimeSectorEnergy ε P := by
  unfold pmRamanujanLargePrimeComplementMixedEnergy pmce_cross pmRamanujanLargePrimeSectorEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro N hN
  rw [pmRamanujanLargePrimeComplement_eq_sub hP]
  simp only [star_sub,mul_sub,Complex.sub_re,Complex.star_def,
    Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  ring

private theorem pmce_complement_energy_eq {P : ℕ} (hP : 2 ≤ P) (ε : ℝ) :
    pmRamanujanLargePrimeComplementEnergy ε P =
      pmPowerDampedRamanujanPrefixEnergy ε (P^2-1) (P-1)+pmRamanujanLargePrimeSectorEnergy ε P-2*pmce_cross ε P := by
  have hn (z w : ℂ) : ‖z-w‖^2 = ‖z‖^2+‖w‖^2-2*(w*star z).re := by
    simp only [Complex.sq_norm,Complex.normSq_sub,Complex.star_def,
      Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  unfold pmRamanujanLargePrimeComplementEnergy pmPowerDampedRamanujanPrefixEnergy
    pmRamanujanLargePrimeSectorEnergy pmce_cross
  rw [← Finset.sum_add_distrib,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro N hN
  rw [pmRamanujanLargePrimeComplement_eq_sub hP,hn]
  ring

/-- The actual complement asymptotically cancels one full sector energy in the signed cross term. -/
theorem tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun P => pmRamanujanLargePrimeComplementMixedEnergy ε P/
      pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 (-1)) := by
  have hh := (pmce_cross_normalized hε hεhalf).sub_const 1
  simp only [zero_sub] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_pmRamanujanLargePrimeSectorEnergy_atTop hε hεhalf).eventually_gt_atTop 0] with P hP hL
  rw [pmce_complement_mixed_eq hP]
  field_simp

/-- The literal complementary denominator sector has the same asymptotic head energy as the selected sector. -/
theorem tendsto_pmRamanujanLargePrimeComplementEnergy_ratio_one
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    Tendsto (fun P => pmRamanujanLargePrimeComplementEnergy ε P/
      pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 1) := by
  have hh := ((tendsto_pmRamanujanCompleteHeadEnergy_div_largePrimeSectorEnergy_zero hε hεhalf).add_const 1).sub
    ((pmce_cross_normalized hε hεhalf).const_mul 2)
  simp only [zero_add,mul_zero,sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2,
    (tendsto_pmRamanujanLargePrimeSectorEnergy_atTop hε hεhalf).eventually_gt_atTop 0] with P hP hL
  rw [pmce_complement_energy_eq hP]
  field_simp

end RHTower

