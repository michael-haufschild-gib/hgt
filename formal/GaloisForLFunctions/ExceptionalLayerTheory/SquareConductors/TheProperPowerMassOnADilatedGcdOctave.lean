import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ReciprocalOctavesAtSquareRootDensity
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CountingLargeEighthPowerGcdDeficits
import GaloisForLFunctions.RHTower.CCM.CCMPrimePowerSquareRootControl

/-!
# Leading correction from proper powers on a gcd octave

The proper-power counting measure has square-root density one. Its
reciprocal octave therefore has coefficient 1−1/√2. Replacing the real
cofactor length by its floor costs at most the number of weighted proper
powers, so every horizon X/M tending to infinity keeps that coefficient.
-/

noncomputable section
open ArithmeticFunction Filter Finset
open scoped Topology
open GaloisForLFunctions.ReciprocalOctaves
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def pp (d : ℕ) : ℝ := if d.Prime then 0 else vonMangoldt d
private theorem pp_nonneg (d : ℕ) : 0 ≤ pp d := by
  unfold pp; split <;> first | exact le_rfl | exact vonMangoldt_nonneg

private abbrev prefix (n : ℕ) := ∑ d ∈ Icc 1 n, pp d

private theorem prefix_eq (n : ℕ) : prefix n = Chebyshev.psi n-Chebyshev.theta n := by
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,sum_filter]
  have hset : Icc 1 n=Ioc 0 n := by ext d; simp only [mem_Icc,mem_Ioc]; omega
  simp only [prefix,hset,pp,ite_not]

private theorem pp_prefix_density :
    Tendsto (fun n : ℕ => prefix n/Real.sqrt n) atTop (𝓝 1) := by
  have h := _root_.RHTower.tendsto_ccmProperPrimePowerSource_scaled_one.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hr := (Nat.cast_pos (α:=ℝ)).mpr hn
  change Real.exp (-Real.log n/2)*(Chebyshev.psi (Real.exp (Real.log n))-Chebyshev.theta
    (Real.exp (Real.log n)))=_
  rw [Real.exp_log hr,prefix_eq,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hr,
    show -Real.log n/2 = -(Real.log n*(1/2)) by ring,Real.exp_neg,div_eq_mul_inv,mul_comm]

/-- Extra logarithmic price of the gcd product beyond its ordinary primes. -/
def properGcdOctavePrice (M X : ℕ) : ℝ := Real.log (octaveGcdProduct M X)-
  ∑ p ∈ (Ioc M (2*M)).filter Nat.Prime, ((X/p:ℕ):ℝ)*Real.log p

private theorem floors (M X : ℕ) (mp : 0<M) :
    properGcdOctavePrice M X = ∑ d ∈ Ioc M (2*M), ((X/d:ℕ):ℝ)*pp d := by
  rw [properGcdOctavePrice,log_octave_gcd_product mp,sum_filter,←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases hp : d.Prime <;> simp [pp,hp,vonMangoldt_apply_prime]

/-- The signed floor error lies between zero and the weighted proper-power
count in the octave, independent of the cofactor horizon. -/
theorem proper_gcd_rounding {M : ℕ} (mp : 0<M) (X : ℕ) :
    0 ≤ (X:ℝ)*price pp M-properGcdOctavePrice M X ∧
      (X:ℝ)*price pp M-properGcdOctavePrice M X ≤ prefix (2*M)-prefix M := by
  have sets : Icc 1 (2*M) \ Icc 1 M = Ioc M (2*M) := by
    ext d; simp only [mem_sdiff,mem_Icc,mem_Ioc]; omega
  have diff : prefix (2*M)-prefix M = ∑ d ∈ Ioc M (2*M),pp d := by
    rw [←sets,sum_sdiff_eq_sub (Icc_subset_Icc_right (show M ≤ 2*M by omega))]
  rw [price,floors _ _ mp,mul_sum,←sum_sub_distrib,diff]
  have term (d : ℕ) : (X:ℝ)*(pp d/d)-((X/d:ℕ):ℝ)*pp d =
      ((X:ℝ)/d-((X/d:ℕ):ℝ))*pp d := by ring
  simp_rw [term]
  refine ⟨sum_nonneg fun d _ => mul_nonneg (sub_nonneg.mpr Nat.cast_div_le) (pp_nonneg d),?_⟩
  apply sum_le_sum
  intro d hd
  have dp := mp.trans (mem_Ioc.mp hd).1
  have lt : (X:ℝ)/d < ((X/d:ℕ):ℝ)+1 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr dp)).mpr
    exact_mod_cast (show X < (X/d+1)*d by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ X dp)
  exact mul_le_of_le_one_left (pp_nonneg d) (by linarith only [lt])

/-- Every diverging octave with X/M tending to infinity has the same
leading proper-power coefficient, even for independently moving heights. -/
theorem dilated_gcd_proper_power_mass {ι : Type*} {l : Filter ι} {M X : ι → ℕ}
    (hm : Tendsto M l atTop) (hr : Tendsto (fun i => (X i:ℝ)/(M i:ℝ)) l atTop) :
    Tendsto (fun i => Real.sqrt (M i)*properGcdOctavePrice (M i) (X i)/(X i:ℝ))
      l (𝓝 (1-1/Real.sqrt 2)) := by
  have main := (square_root_octave_transfer pp_prefix_density).comp hm
  rw [one_mul] at main
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have tiny := (tendsto_const_nhds (x:=|C|*Real.sqrt 2)).div_atTop hr
  have delta : Tendsto (fun i => Real.sqrt (M i)*price pp (M i)-
      Real.sqrt (M i)*properGcdOctavePrice (M i) (X i)/(X i:ℝ)) l (𝓝 0) := by
    apply squeeze_zero' _ _ tiny
    all_goals
      filter_upwards [hm.eventually_ge_atTop 1,hr.eventually_gt_atTop 0] with i mpos xpos
      have mr := (Nat.cast_pos (α:=ℝ)).mpr mpos
      have xr : 0 < (X i:ℝ) := (div_pos_iff_of_pos_right mr).mp xpos
      have h := proper_gcd_rounding mpos (X i)
      have factor : Real.sqrt (M i)*price pp (M i)-
          Real.sqrt (M i)*properGcdOctavePrice (M i) (X i)/(X i:ℝ) =
          Real.sqrt (M i)/(X i:ℝ)*((X i:ℝ)*price pp (M i)-properGcdOctavePrice (M i) (X i)) := by
        field_simp; ring
      rw [factor]
    · exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) xr.le) h.1
    · have hc := (hC ((2*M i:ℕ):ℝ)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))
      rw [←prefix_eq,Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at hc
      have plen := (sub_le_self _ (sum_nonneg (fun n _ => pp_nonneg n) : 0 ≤ prefix (M i))).trans hc
      apply (mul_le_mul_of_nonneg_left (h.2.trans plen) (div_nonneg (Real.sqrt_nonneg _) xr.le)).trans_eq
      calc _ = |C|*Real.sqrt 2*(Real.sqrt (M i)*Real.sqrt (M i))/(X i:ℝ) := by ring
           _ = _ := by rw [Real.mul_self_sqrt mr.le]; field_simp
  have hd := main.sub delta
  rw [sub_zero] at hd
  exact hd.congr fun i => by dsimp only [Function.comp_apply]; ring

/-- On the eighth/ninth-power grid, the two signed readings first separate
at order m⁻⁴, with exact positive coefficient 1−1/√2. -/
theorem eighth_proper_power_fourth_coefficient :
    Tendsto (fun m : ℕ => (m:ℝ)^4*(eighthReading true m-eighthReading false m))
      atTop (𝓝 (1-1/Real.sqrt 2)) := by
  have rat : Tendsto (fun m : ℕ => ((m^9:ℕ):ℝ)/((m^8:ℕ):ℝ)) atTop atTop := by
    apply (tendsto_natCast_atTop_atTop (R:=ℝ)).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m mp
    push_cast
    field_simp
  have main := dilated_gcd_proper_power_mass (M:=fun m : ℕ => m^8) (X:=fun m => m^9)
    (tendsto_pow_atTop (by decide : (8:ℕ)≠0)) rat
  apply main.congr
  intro m
  simp only [eighthReading,properGcdOctavePrice,eighthOrdinaryPrimePrice,Bool.false_eq_true,
    if_false,if_true,Nat.cast_pow]
  rw [show (m:ℝ)^8=((m:ℝ)^4)^2 by ring,Real.sqrt_sq (by positivity)]
  ring

#print axioms dilated_gcd_proper_power_mass
#print axioms eighth_proper_power_fourth_coefficient
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
