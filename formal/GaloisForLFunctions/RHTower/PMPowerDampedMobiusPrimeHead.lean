import GaloisForLFunctions.RHTower.PMPowerDampedMobiusBoundaryMoments
import GaloisForLFunctions.RHTower.PrimeRpowStrongPNTBandTransfer
/-!
# Signed PM prime heads and their boundary-moment kernel

Finite divisor-count interchange transfers the literal signed source from
weighted prime sums to integrals, uniformly for growing cofactor cutoffs.
The error follows from the unconditional Chebyshev PNT estimate. Reciprocal
substitution identifies the integral with the actual boundary-moment kernel.
No small-damping square-integrability assumption is used.
-/

noncomputable section
open MeasureTheory Set Filter Topology Asymptotics
namespace RHTower

private theorem pmt_theta_sqrt_band :
    ∃ c > 0, ∃ K > 0, ∀ᶠ X : ℝ in atTop, ∀ y ∈ Icc (Real.sqrt X) X,
      |Chebyshev.theta y-y| ≤ K*X*Real.exp (-c*Real.sqrt (Real.log X)) := by
  obtain ⟨c,hc,hO⟩ := Sieve.chebyshevTheta_sub_id_isBigO
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp hO
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hC
  refine ⟨c/2,by positivity,|C|+1,by positivity,?_⟩
  filter_upwards [Real.tendsto_sqrt_atTop.eventually_ge_atTop (max Y 2),
    eventually_ge_atTop 4] with X hroot hX y hy
  have hx0 : 0 < X := by linarith
  have hy2 : 2 ≤ y := (le_max_right _ _).trans (hroot.trans hy.1)
  have hy0 : 0 < y := by linarith
  have hb := hY y ((le_max_left _ _).trans (hroot.trans hy.1))
  rw [Pi.sub_apply,id_eq,Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity : 0 ≤ y*Real.exp (-c*Real.sqrt (Real.log y)))] at hb
  have hl : Real.log X/2 ≤ Real.log y := by
    rw [← Real.log_sqrt hx0.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hx0) hy.1
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hr : Real.sqrt (Real.log X)/2 ≤ Real.sqrt (Real.log y) := by
    nlinarith [Real.sq_sqrt hlX,Real.sq_sqrt hly,
      Real.sqrt_nonneg (Real.log X),Real.sqrt_nonneg (Real.log y)]
  have he : Real.exp (-c*Real.sqrt (Real.log y)) ≤
      Real.exp (-(c/2)*Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ |C| *(y*Real.exp (-c*Real.sqrt (Real.log y))) :=
      hb.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    _ ≤ (|C|+1) *(X*Real.exp (-(c/2)*Real.sqrt (Real.log X))) := by
      exact mul_le_mul (by linarith [abs_nonneg C])
        (mul_le_mul hy.2 he (by positivity) hx0.le) (by positivity) (by positivity)
    _ = _ := by ring

private theorem pmt_band_error {ε u v E : ℝ} (hε : 0 ≤ ε) (hu : 2 ≤ u) (huv : u ≤ v)
    (hE : ∀ t ∈ Icc u v, |Chebyshev.theta t-t| ≤ E) :
    |(primeRpowSumIoc (1-ε) v-primeRpowSumIoc (1-ε) u)-
      (HTGeometry.logRpowIntegral (1-ε) v-HTGeometry.logRpowIntegral (1-ε) u)| ≤
      (2+(v-u)*abelKernelConst (1-ε)/u)*(u^(-ε)/Real.log u)*E := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  let W := u^(-ε)/Real.log u
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hW (t : ℝ) (ht : t ∈ Icc u v) : |rpowDivLog (1-ε) t| ≤ W := by
    have ht0 : 0 < t := hu0.trans_le ht.1
    have hlt : 0 < Real.log t := hlu.trans_le (Real.log_le_log hu0 ht.1)
    rw [rpowDivLog,show 1-ε-1 = -ε by ring,abs_of_nonneg (by positivity)]
    exact div_le_div₀ (by positivity)
      (Real.rpow_le_rpow_of_nonpos hu0 ht.1 (by linarith)) hlu
      (Real.log_le_log hu0 ht.1)
  have hD (t : ℝ) (ht : t ∈ Icc u v) :
      |deriv (rpowDivLog (1-ε)) t| ≤ abelKernelConst (1-ε)*W/u := by
    have ht2 := hu.trans ht.1
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have hs := abs_abelKernel_le (a := 1-ε) ht2
    have hw := hW t ht
    rw [rpowDivLog,abs_of_nonneg (by positivity : 0 ≤ t^((1-ε)-1)/Real.log t)] at hw
    have hb : |abelKernel (1-ε) t| ≤ abelKernelConst (1-ε)*W :=
      hs.trans (mul_le_mul_of_nonneg_left hw (abelKernelConst_nonneg _))
    rw [abelKernel,abs_mul,abs_of_pos ht0,← deriv_rpowDivLog ht2] at hb
    calc
      _ ≤ (abelKernelConst (1-ε)*W)/t := (le_div_iff₀ ht0).mpr (by simpa [mul_comm] using hb)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (abelKernelConst_nonneg _) hW0) hu0 ht.1
  have h := abs_primeRpowSumIoc_diff_sub_logRpowIntegral_diff_le hu huv hW hD hE
  exact h.trans_eq (by dsimp [W]; ring)

private theorem pmt_prime_band_exp {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ c > 0, ∃ K > 0, ∀ᶠ X : ℝ in atTop, ∀ u v : ℝ,
      Real.sqrt X ≤ u → u ≤ v → v ≤ X →
      |(primeRpowSumIoc (1-ε) v-primeRpowSumIoc (1-ε) u)-
        (HTGeometry.logRpowIntegral (1-ε) v-HTGeometry.logRpowIntegral (1-ε) u)| ≤
        K*X^2*u^(-ε-1)*Real.exp (-c*Real.sqrt (Real.log X)) := by
  obtain ⟨c,hc,C,hC,he⟩ := pmt_theta_sqrt_band
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B := abelKernelConst (1-ε)
  have hB : 0 ≤ B := abelKernelConst_nonneg _
  refine ⟨c,hc,(2+B)*C/Real.log 2,by positivity,?_⟩
  filter_upwards [he,Real.tendsto_sqrt_atTop.eventually_ge_atTop 2,
    eventually_ge_atTop 4] with X heX hr hX u v hru huv hvX
  have hu2 : 2 ≤ u := hr.trans hru
  have hu0 : 0 < u := by linarith
  have hX0 : 0 < X := by linarith
  have hlu : 0 < Real.log u := Real.log_pos (by linarith)
  have huX : u ≤ X := huv.trans hvX
  let E := C*X*Real.exp (-c*Real.sqrt (Real.log X))
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hb := pmt_band_error hε hu2 huv (E := E)
    (fun t ht => heX t ⟨hru.trans ht.1,ht.2.trans hvX⟩)
  have hratio : 1 ≤ X/u := (le_div_iff₀ hu0).mpr (by simpa using huX)
  have hlen : (v-u)/u ≤ X/u := div_le_div_of_nonneg_right (by linarith) hu0.le
  have hfactor : 2+(v-u)*B/u ≤ (2+B)*(X/u) := by
    have hm := mul_le_mul_of_nonneg_left hlen hB
    nlinarith [show (v-u)*B/u = B*((v-u)/u) by ring]
  have hweight : u^(-ε)/Real.log u ≤ u^(-ε)/Real.log 2 :=
    div_le_div_of_nonneg_left (by positivity) hl2
      (Real.log_le_log (by norm_num) hu2)
  have hp : u^(-ε-1) = u^(-ε)/u := by
    rw [Real.rpow_sub hu0,Real.rpow_one]
  calc
    _ ≤ (2+(v-u)*B/u)*(u^(-ε)/Real.log u)*E := hb
    _ ≤ ((2+B)*(X/u))*(u^(-ε)/Real.log 2)*E := by
      apply mul_le_mul_of_nonneg_right _ hE0
      exact mul_le_mul hfactor hweight (by positivity) (by positivity)
    _ = _ := by dsimp [E]; rw [hp]; ring

private theorem pmt_prime_interval {ε u v : ℝ} (hu : 2 ≤ u) (huv : u ≤ v) :
    (∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
      if q.Prime then (q : ℝ)^(-ε) else 0) =
      primeRpowSumIoc (1-ε) v-primeRpowSumIoc (1-ε) u := by
  have hu2 : 2 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu)
  have hfl := Nat.floor_mono huv
  have hsplit : Finset.Ioc 2 ⌊v⌋₊ = Finset.Ioc 2 ⌊u⌋₊ ∪ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊ := by
    ext q
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Ioc 2 ⌊u⌋₊) (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊) := by
    rw [Finset.disjoint_left]
    intro q hq hk
    simp only [Finset.mem_Ioc] at hq hk
    omega
  simp only [primeRpowSumIoc,show 1-ε-1 = -ε by ring]
  rw [hsplit,Finset.sum_union hd]
  ring

private theorem pmt_divisor_count_extend (ε : ℝ) {b u q : ℝ}
    (hb : 0 ≤ b) (hu : 0 < u) (hq : u ≤ q) :
    pmPowerDampedDivisorSum ε (b/q) =
      ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊,
        if (n : ℝ)*q ≤ b then pmPowerDampedDivisorCoeff ε n else 0 := by
  have hq0 : 0 < q := hu.trans_le hq
  have hf : ⌊b/q⌋₊ ≤ ⌊b/u⌋₊ := Nat.floor_mono
    (div_le_div_of_nonneg_left hb hu hq)
  rw [pmPowerDampedDivisorSum]
  apply Finset.sum_subset_zero_on_sdiff (Finset.Icc_subset_Icc_right hf)
  · intro n hn
    rcases Finset.mem_sdiff.mp hn with ⟨hn,hnsmall⟩
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hnr : ¬(n : ℝ)*q ≤ b := by
      intro h
      apply hnsmall
      exact Finset.mem_Icc.mpr ⟨hn1,Nat.le_floor ((le_div_iff₀ hq0).mpr h)⟩
    exact if_neg hnr
  · intro n hn
    have hnr : (n : ℝ) ≤ b/q := (Nat.le_floor_iff (by positivity)).mp
      (Finset.mem_Icc.mp hn).2
    rw [if_pos ((le_div_iff₀ hq0).mp hnr)]

private theorem pmt_prime_count_pair (ε : ℝ) {b u X : ℝ}
    (hu : 2 ≤ u) (hub : u ≤ b) (hbX : b ≤ X) :
    (∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
      (if q.Prime then (q : ℝ)^(-ε) else 0)*
        pmPowerDampedDivisorSum ε (b/q)) =
    ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊, pmPowerDampedDivisorCoeff ε n *
      (primeRpowSumIoc (1-ε) (b/n)-primeRpowSumIoc (1-ε) u) := by
  have hu0 : 0 < u := by linarith
  have hb0 : 0 < b := hu0.trans_le hub
  have hX0 : 0 < X := hb0.trans_le hbX
  calc
    _ = ∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊, ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊,
        (if q.Prime then (q : ℝ)^(-ε) else 0)*
          (if (n : ℝ)*(q : ℝ) ≤ b then pmPowerDampedDivisorCoeff ε n else 0) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqu : u < (q : ℝ) := (Nat.floor_lt hu0.le).mp (Finset.mem_Ioc.mp hq).1
      rw [pmt_divisor_count_extend ε hb0.le hu0 hqu.le,Finset.mul_sum]
    _ = ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊, ∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
        (if q.Prime then (q : ℝ)^(-ε) else 0)*
          (if (n : ℝ)*(q : ℝ) ≤ b then pmPowerDampedDivisorCoeff ε n else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by linarith
      have hnu : (n : ℝ) ≤ b/u :=
        (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
      have hubn : u ≤ b/n := (le_div_iff₀ hn0).mpr (by
        nlinarith [(le_div_iff₀ hu0).mp hnu])
      have hbnX : b/n ≤ X := (div_le_iff₀ hn0).mpr (by nlinarith)
      rw [← pmt_prime_interval hu hubn,Finset.mul_sum]
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hbnX))
      · intro q hq
        rcases Finset.mem_sdiff.mp hq with ⟨hq,hqsmall⟩
        have hqlo := (Finset.mem_Ioc.mp hq).1
        have hcut : ¬(n : ℝ)*(q : ℝ) ≤ b := by
          intro h
          apply hqsmall
          exact Finset.mem_Ioc.mpr ⟨hqlo,Nat.le_floor ((le_div_iff₀ hn0).mpr (by nlinarith))⟩
        rw [if_neg hcut,mul_zero]
      · intro q hq
        have hqbn : (q : ℝ) ≤ b/n := (Nat.le_floor_iff (by positivity)).mp
          (Finset.mem_Ioc.mp hq).2
        have hmul : (n : ℝ)*(q : ℝ) ≤ b := by nlinarith [(le_div_iff₀ hn0).mp hqbn]
        rw [if_pos hmul]
        ring


private theorem pmt_integral_count_pair (ε : ℝ) {b u X : ℝ}
    (hu : 2 ≤ u) (hub : u ≤ b) (hbX : b ≤ X) :
    IntegrableOn (fun t : ℝ => rpowDivLog (1-ε) t *
        pmPowerDampedDivisorSum ε (b/t)) (Ioc u X) ∧
    (∫ t in Ioc u X, rpowDivLog (1-ε) t * pmPowerDampedDivisorSum ε (b/t)) =
      ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊, pmPowerDampedDivisorCoeff ε n *
        (HTGeometry.logRpowIntegral (1-ε) (b/n)-HTGeometry.logRpowIntegral (1-ε) u) := by
  have hu0 : 0 < u := by linarith
  have hb0 : 0 < b := hu0.trans_le hub
  have huX : u ≤ X := hub.trans hbX
  have hi : IntegrableOn (rpowDivLog (1-ε)) (Ioc u X) := by
    exact ((HTGeometry.intervalIntegrable_rpowDivLog (1-ε) hu (hu.trans huX)).1)
  let g : ℕ → ℝ → ℝ := fun n => (Iic (b/n)).indicator
    (fun t => pmPowerDampedDivisorCoeff ε n * rpowDivLog (1-ε) t)
  have hig (n : ℕ) : IntegrableOn (g n) (Ioc u X) :=
    (hi.const_mul _).indicator measurableSet_Iic
  have heq : Set.EqOn (fun t : ℝ => rpowDivLog (1-ε) t * pmPowerDampedDivisorSum ε (b/t))
      (fun t => ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊, g n t) (Ioc u X) := by
    intro t ht
    dsimp only
    rw [pmt_divisor_count_extend ε hb0.le hu0 ht.1.le,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    have he : (n : ℝ)*t ≤ b ↔ t ∈ Iic (b/n) := by
      simp only [mem_Iic,le_div_iff₀ hn0]
      constructor <;> intro h <;> nlinarith
    by_cases h : (n : ℝ)*t ≤ b
    · rw [if_pos h]
      dsimp only [g]
      rw [Set.indicator_of_mem (he.mp h)]
      ring
    · dsimp only [g]
      rw [if_neg h,mul_zero,Set.indicator_of_notMem (fun ht => h (he.mpr ht))]
  have hsum : IntegrableOn (fun t => ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊,g n t) (Ioc u X) :=
    integrable_finsetSum _ (fun n _ => hig n)
  refine ⟨hsum.congr_fun (fun t ht => (heq ht).symm) measurableSet_Ioc,?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc heq,
    integral_finsetSum _ (fun n _ => hig n)]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by linarith
  have hnu : (n : ℝ) ≤ b/u :=
    (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
  have hubn : u ≤ b/n := (le_div_iff₀ hn0).mpr (by
    nlinarith [(le_div_iff₀ hu0).mp hnu])
  have hbnX : b/n ≤ X := (div_le_iff₀ hn0).mpr (by nlinarith)
  have hset : Ioc u X ∩ Iic (b/n) = Ioc u (b/n) := by
    ext t
    simp only [mem_inter_iff,mem_Ioc,mem_Iic]
    constructor
    · rintro ⟨⟨ht,hX⟩,hb⟩; exact ⟨ht,hb⟩
    · rintro ⟨ht,hb⟩; exact ⟨⟨ht,hb.trans hbnX⟩,hb⟩
  dsimp only [g]
  rw [setIntegral_indicator measurableSet_Iic,hset,integral_const_mul]
  congr 1
  rw [← intervalIntegral.integral_of_le hubn]
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (HTGeometry.intervalIntegrable_rpowDivLog (1-ε) (u := 2) (by norm_num) hu)
    (HTGeometry.intervalIntegrable_rpowDivLog (1-ε) hu (hu.trans hubn))
  change (∫ t in u..b/n, t^((1-ε)-1)/Real.log t) = _
  dsimp [HTGeometry.logRpowIntegral]
  linarith

private theorem pmt_count_transfer {ε u X b E : ℝ} (hε : 0 ≤ ε)
    (hu : 2 ≤ u) (hub : u ≤ b) (hbX : b ≤ X)
    (hE : 0 ≤ E)
    (he : ∀ v ∈ Icc u X,
      |(primeRpowSumIoc (1-ε) v-primeRpowSumIoc (1-ε) u)-
        (HTGeometry.logRpowIntegral (1-ε) v-HTGeometry.logRpowIntegral (1-ε) u)| ≤ E) :
    |(∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
      (if q.Prime then (q : ℝ)^(-ε) else 0)*pmPowerDampedDivisorSum ε (b/q))-
      ∫ t in Ioc u X, rpowDivLog (1-ε) t*pmPowerDampedDivisorSum ε (b/t)| ≤
      (b/u)*E := by
  have hu0 : 0 < u := by linarith
  have hb0 : 0 < b := hu0.trans_le hub
  rw [pmt_prime_count_pair ε hu hub hbX,(pmt_integral_count_pair ε hu hub hbX).2,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊b/u⌋₊, E := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by linarith
      have hnu : (n : ℝ) ≤ b/u :=
        (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Icc.mp hn).2
      have hbn : b/n ∈ Icc u X := ⟨(le_div_iff₀ hn0).mpr (by
        nlinarith [(le_div_iff₀ hu0).mp hnu]),(div_le_iff₀ hn0).mpr (by nlinarith)⟩
      rw [← mul_sub,abs_mul,abs_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε n)]
      exact (mul_le_mul_of_nonneg_left (he _ hbn)
        (pmPowerDampedDivisorCoeff_nonneg hε n)).trans
          (by simpa using mul_le_mul_of_nonneg_right (pmPowerDampedDivisorCoeff_le_one hε n) hE)
    _ ≤ (b/u)*E := by
      simp only [Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hE

/-- The actual signed PM source transfers from prime heads to its weighted integral.
The cofactor cutoff may grow subexponentially; all constants are unconditional. -/
theorem pmPowerDampedFermiSource_prime_head_transfer {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ c > 0, ∃ K > 0, ∀ᶠ X : ℝ in atTop, ∀ u : ℝ,
      Real.sqrt X ≤ u → u ≤ X/2 →
      |(∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
        (if q.Prime then (q : ℝ)^(-ε) else 0)*
          (pmPowerDampedFermiSource ε ((q : ℝ)/X)).re)-
        ∫ t in Ioc u X, (t^(-ε)/Real.log t)*
          (pmPowerDampedFermiSource ε (t/X)).re| ≤
        K*X^3*u^(-ε-2)*Real.exp (-c*Real.sqrt (Real.log X)) := by
  obtain ⟨c,hc,K,hK,he⟩ := pmt_prime_band_exp hε
  refine ⟨c,hc,3*K,by positivity,?_⟩
  filter_upwards [he,Real.tendsto_sqrt_atTop.eventually_ge_atTop 2,
    eventually_ge_atTop 4] with X heX hr hX u hru huXhalf
  have hu2 : 2 ≤ u := hr.trans hru
  have hu0 : 0 < u := by linarith
  have hX0 : 0 < X := by linarith
  have huX : u ≤ X := by linarith
  let E := K*X^2*u^(-ε-1)*Real.exp (-c*Real.sqrt (Real.log X))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he' (v : ℝ) (hv : v ∈ Icc u X) :
      |(primeRpowSumIoc (1-ε) v-primeRpowSumIoc (1-ε) u)-
        (HTGeometry.logRpowIntegral (1-ε) v-HTGeometry.logRpowIntegral (1-ε) u)| ≤ E :=
    heX u v hru hv.1 hv.2
  have hA := pmt_count_transfer hε hu2 huX le_rfl hE he'
  have hB := pmt_count_transfer hε hu2 huXhalf (by linarith : X/2 ≤ X) hE he'
  have hBr : (X/2/u)*E ≤ (X/u)*E :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hu0.le) hE
  have hf (t : ℝ) (ht : 0 < t) :
      (pmPowerDampedFermiSource ε (t/X)).re =
        pmPowerDampedDivisorSum ε (X/t)-2*pmPowerDampedDivisorSum ε ((X/2)/t) := by
    have h1 : 1/(t/X) = X/t := by field_simp
    have h2 : 1/(2*(t/X)) = (X/2)/t := by field_simp
    rw [pmPowerDampedFermiSource_eq_divisor_counts ε (div_pos ht hX0),h1,h2]
    simp
  have hsum : (∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
        (if q.Prime then (q : ℝ)^(-ε) else 0)*
          (pmPowerDampedFermiSource ε ((q : ℝ)/X)).re) =
      (∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
        (if q.Prime then (q : ℝ)^(-ε) else 0)*pmPowerDampedDivisorSum ε (X/q))-
      2*(∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
        (if q.Prime then (q : ℝ)^(-ε) else 0)*pmPowerDampedDivisorSum ε ((X/2)/q)) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (0 : ℝ) < q := hu0.trans ((Nat.floor_lt hu0.le).mp (Finset.mem_Ioc.mp hq).1)
    rw [hf q hq0]
    ring
  have hiA := (pmt_integral_count_pair ε hu2 huX le_rfl).1
  have hiB := (pmt_integral_count_pair ε hu2 huXhalf (by linarith : X/2 ≤ X)).1
  have hint : (∫ t in Ioc u X, (t^(-ε)/Real.log t)*
      (pmPowerDampedFermiSource ε (t/X)).re) =
      (∫ t in Ioc u X, rpowDivLog (1-ε) t*pmPowerDampedDivisorSum ε (X/t))-
      2*(∫ t in Ioc u X, rpowDivLog (1-ε) t*pmPowerDampedDivisorSum ε ((X/2)/t)) := by
    rw [← integral_const_mul,← integral_sub hiA (hiB.const_mul 2)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hf t (hu0.trans ht.1),rpowDivLog,show 1-ε-1 = -ε by ring]
    ring
  rw [hsum,hint]
  calc
    _ ≤ |(∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
          (if q.Prime then (q : ℝ)^(-ε) else 0)*pmPowerDampedDivisorSum ε (X/q))-
          ∫ t in Ioc u X, rpowDivLog (1-ε) t*pmPowerDampedDivisorSum ε (X/t)|+
        2*|(∑ q ∈ Finset.Ioc ⌊u⌋₊ ⌊X⌋₊,
          (if q.Prime then (q : ℝ)^(-ε) else 0)*pmPowerDampedDivisorSum ε ((X/2)/q))-
          ∫ t in Ioc u X, rpowDivLog (1-ε) t*pmPowerDampedDivisorSum ε ((X/2)/t)| := by
      have htri (a b c d : ℝ) : |(a-2*b)-(c-2*d)| ≤ |a-c|+2*|b-d| := by
        calc
          _ = |(a-c)-2*(b-d)| := by congr 1; ring
          _ ≤ |a-c|+|2*(b-d)| := abs_sub _ _
          _ = _ := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact htri _ _ _ _
    _ ≤ (X/u)*E+2*((X/u)*E) := add_le_add hA (by linarith [hB.trans hBr])
    _ = _ := by
      have hp : u^(-ε-2) = u^(-ε-1)/u := by
        rw [show -ε-2 = (-ε-1)-1 by ring,Real.rpow_sub hu0,Real.rpow_one]
      dsimp [E]
      rw [hp]
      ring

/-- The prime-head integral is exactly the truncated boundary-moment kernel. -/
theorem pmPowerDampedFermiSource_prime_head_integral (ε : ℝ) {X H : ℝ}
    (hX : 0 < X) (hH : 1 ≤ H) :
    (∫ t in Ioc (X/H) X, (t^(-ε)/Real.log t)*
      (pmPowerDampedFermiSource ε (t/X)).re) =
    X^(1-ε)*∫ v in Ioc (1 : ℝ) H,
      (pmPowerDampedBoundaryWeight ε v).re/(Real.log X-Real.log v) := by
  have hH0 : 0 < H := by linarith
  have himage : (fun v : ℝ => X/v) '' Icc 1 H = Icc (X/H) X := by
    ext t
    constructor
    · rintro ⟨v,hv,rfl⟩
      have hv0 : 0 < v := by linarith [hv.1]
      refine ⟨div_le_div_of_nonneg_left hX.le hv0 hv.2,?_⟩
      exact (div_le_iff₀ hv0).mpr (by nlinarith [hv.1])
    · intro ht
      have ht0 : 0 < t := (div_pos hX hH0).trans_le ht.1
      refine ⟨X/t,⟨(le_div_iff₀ ht0).mpr (by simpa using ht.2),?_⟩,?_⟩
      · exact (div_le_iff₀ ht0).mpr (by nlinarith [(div_le_iff₀ hH0).mp ht.1])
      · field_simp
  have hd : ∀ v ∈ Icc (1 : ℝ) H,
      HasDerivWithinAt (fun v : ℝ => X/v) (-X/v^2) (Icc 1 H) v := by
    intro v hv
    have hv0 : v ≠ 0 := by linarith [hv.1]
    have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-(v^2)⁻¹) v := hasDerivAt_inv hv0
    have hdiv : HasDerivAt (fun v : ℝ => X/v) (-(X/v^2)) v := by
      refine (hinv.const_mul X).congr_deriv ?_ |>.congr_of_eventuallyEq ?_
      · rw [div_eq_mul_inv]
        ring
      · filter_upwards with t
        rw [div_eq_mul_inv]
    simpa only [neg_div] using hdiv.hasDerivWithinAt (s := Icc 1 H)
  have hinj : InjOn (fun v : ℝ => X/v) (Icc 1 H) := by
    intro v hv w hw he
    have hv0 : v ≠ 0 := by linarith [hv.1]
    have hw0 : w ≠ 0 := by linarith [hw.1]
    field_simp at he
    nlinarith
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj
    (fun t : ℝ => (t^(-ε)/Real.log t)*(pmPowerDampedFermiSource ε (t/X)).re)
  rw [himage] at hi
  rw [← integral_Icc_eq_integral_Ioc,hi,← integral_const_mul,
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  have hv0 : 0 < v := by linarith [hv.1]
  have ha : |(-X)/v^2| = X/v^2 := by
    rw [neg_div,abs_neg,abs_of_pos (by positivity)]
  have hf : X/v/X = 1/v := by field_simp
  have hpX : X^(1-ε) = X*X^(-ε) := by
    rw [sub_eq_add_neg,Real.rpow_add hX,Real.rpow_one]
  have hpv : v^(ε-2) = v^ε/v^2 := by
    rw [Real.rpow_sub hv0,Real.rpow_two]
  rw [smul_eq_mul,ha,Real.log_div hX.ne' hv0.ne',hf,
    Real.div_rpow hX.le hv0.le,Real.rpow_neg hv0.le,hpX]
  simp only [pmPowerDampedBoundaryWeight,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  rw [hpv]
  field_simp

/-- Cofactor-cutoff form of the signed transfer, using the actual boundary weight. -/
theorem pmPowerDampedFermiSource_prime_cofactor_transfer {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ c > 0, ∃ K > 0, ∀ᶠ X : ℝ in atTop, ∀ H : ℝ,
      2 ≤ H → H ≤ Real.sqrt X →
      |(∑ q ∈ Finset.Ioc ⌊X/H⌋₊ ⌊X⌋₊,
        (if q.Prime then (q : ℝ)^(-ε) else 0)*
          (pmPowerDampedFermiSource ε ((q : ℝ)/X)).re)-
        X^(1-ε)*∫ v in Ioc (1 : ℝ) H,
          (pmPowerDampedBoundaryWeight ε v).re/(Real.log X-Real.log v)| ≤
        K*X^(1-ε)*H^(ε+2)*Real.exp (-c*Real.sqrt (Real.log X)) := by
  obtain ⟨c,hc,K,hK,he⟩ := pmPowerDampedFermiSource_prime_head_transfer hε
  refine ⟨c,hc,K,hK,?_⟩
  filter_upwards [he,eventually_ge_atTop 4] with X heX hX H hH hHX
  have hX0 : 0 < X := by linarith
  have hH0 : 0 < H := by linarith
  have hr : Real.sqrt X ≤ X/H := (le_div_iff₀ hH0).mpr (by
    have hm := mul_le_mul_of_nonneg_left hHX (Real.sqrt_nonneg X)
    nlinarith [Real.sq_sqrt hX0.le])
  have hh : X/H ≤ X/2 := div_le_div_of_nonneg_left hX0.le (by norm_num) hH
  have hb := heX (X/H) hr hh
  rw [pmPowerDampedFermiSource_prime_head_integral ε hX0 (by linarith)] at hb
  have hp : X^3*(X/H)^(-ε-2) = X^(1-ε)*H^(ε+2) := by
    rw [Real.div_rpow hX0.le hH0.le,
      show -ε-2 = -(ε+2) by ring,Real.rpow_neg hH0.le,div_inv_eq_mul]
    have hpow : X^3*X^(-(ε+2)) = X^(1-ε) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hX0]
      congr 1
      ring
    calc
      _ = (X^3*X^(-(ε+2)))*H^(ε+2) := by ring
      _ = _ := by rw [hpow]
  convert hb using 1
  calc
    _ = K*(X^(1-ε)*H^(ε+2))*Real.exp (-c*Real.sqrt (Real.log X)) := by ring
    _ = K*(X^3*(X/H)^(-ε-2))*Real.exp (-c*Real.sqrt (Real.log X)) := by rw [hp]
    _ = _ := by ring


end RHTower
