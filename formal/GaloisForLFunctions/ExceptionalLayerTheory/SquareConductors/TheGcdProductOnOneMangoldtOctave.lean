import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors

/-!
# The gcd product across a Mangoldt octave

Replacing the lcm of the first M integers by the lcm through 2M increases
each integer's gcd by an integer factor. The logarithm of the resulting
product counts multiples of precisely the prime powers in that octave.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem pow_dvd_lcm_iff {d M : ℕ} (hM : 0 < M) (hd : vonMangoldt d ≠ 0) :
    d ∣ M.lcmUpto ↔ d ≤ M := by
  obtain ⟨p,k,hp,_,rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hd)
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero M),
    Nat.factorization_lcmUpto _ hp, Nat.le_log_iff_pow_le hp.one_lt hM.ne']

/-- The gcd with the lcm retains each prime-power logarithm through M. -/
theorem log_gcd_lcm_ordinary_divisors {u M : ℕ} (hu : 0 < u) (hM : 0 < M) :
    Real.log (u.gcd M.lcmUpto) =
      ∑ d ∈ Ioc 0 M, if d ∣ u then vonMangoldt d else 0 := by
  classical
  let g := u.gcd M.lcmUpto
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hu
  have hs : g.divisors = u.divisors.filter (· ∣ M.lcmUpto) := by
    ext d
    simp only [Nat.mem_divisors,mem_filter,g,Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨⟨h.1.1,hu.ne'⟩,h.1.2⟩,fun h => ⟨⟨h.1.1,h.2⟩,hg.ne'⟩⟩
  have ht : (Ioc 0 M).filter (· ∣ u) = u.divisors.filter (· ≤ M) := by
    ext d
    simp only [mem_filter,mem_Ioc,Nat.mem_divisors]
    exact ⟨fun h => ⟨⟨h.2,hu.ne'⟩,h.1.2⟩,fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1.1 hu,h.2⟩,h.1.1⟩⟩
  change Real.log g = _
  rw [← vonMangoldt_sum,hs,←sum_filter,ht,sum_filter,sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : vonMangoldt d = 0
  · simp [hd]
  · simp only [pow_dvd_lcm_iff hM hd]

/-- Integer product of the gcd quotients through the specified endpoint. -/
def octaveGcdProduct (M X : ℕ) : ℕ :=
  ∏ u ∈ Ioc 0 X, (u.gcd (2*M).lcmUpto)/(u.gcd M.lcmUpto)

private theorem gcd_dvd_doubled (u M : ℕ) :
    u.gcd M.lcmUpto ∣ u.gcd (2*M).lcmUpto := by
  apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
  apply (Nat.gcd_dvd_right u M.lcmUpto).trans
  unfold Nat.lcmUpto
  apply Finset.lcm_dvd
  intro d hd
  exact Finset.dvd_lcm (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (by omega)⟩)

private theorem gcd_log_step {M u : ℕ} (hM : 0 < M) (hu : 0 < u) :
    Real.log (((u.gcd (2*M).lcmUpto)/(u.gcd M.lcmUpto) : ℕ) : ℝ) =
      ∑ d ∈ Ioc M (2*M), if d ∣ u then vonMangoldt d else 0 := by
  have hg (k : ℕ) : ((u.gcd k.lcmUpto : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.gcd_pos_of_pos_left _ hu).ne'
  rw [Nat.cast_div (gcd_dvd_doubled u M) (hg M),Real.log_div (hg _) (hg _),
    log_gcd_lcm_ordinary_divisors hu (by omega),log_gcd_lcm_ordinary_divisors hu hM]
  have hs := sum_Ioc_consecutive (fun d => if d ∣ u then vonMangoldt d else 0)
    (Nat.zero_le M) (by omega : M ≤ 2*M)
  linarith only [hs]

/-- A finite factorization, valid at every upper endpoint, including X below the octave. -/
theorem log_octave_gcd_product {M : ℕ} (hM : 0 < M) (X : ℕ) :
    Real.log (octaveGcdProduct M X) =
      ∑ d ∈ Ioc M (2*M), ((X/d : ℕ) : ℝ) * vonMangoldt d := by
  classical
  rw [octaveGcdProduct,Nat.cast_prod,Real.log_prod]
  · calc _ = ∑ u ∈ Ioc 0 X, ∑ d ∈ Ioc M (2*M), if d ∣ u then vonMangoldt d else 0 :=
           sum_congr rfl fun u hu => gcd_log_step hM (mem_Ioc.mp hu).1
         _ = _ := by
           rw [sum_comm]
           apply sum_congr rfl
           intro d hd
           have hd0 := hM.trans (mem_Ioc.mp hd).1
           rw [←sum_filter,sum_divisible_Ioc hd0,Nat.zero_div,sum_const,Nat.card_Ioc,
             Nat.sub_zero,nsmul_eq_mul]
  · intro u hu
    apply Nat.cast_ne_zero.mpr
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (mem_Ioc.mp hu).1)
      (gcd_dvd_doubled u M)) (Nat.gcd_pos_of_pos_left _ (mem_Ioc.mp hu).1)).ne'

/-- The product undercounts the reciprocal Mangoldt mass times X by at most
the total Mangoldt mass of the octave, uniformly in X. -/
theorem octave_gcd_product_rounding {M : ℕ} (hM : 0 < M) (X : ℕ) :
    let E := X * (∑ d ∈ Ioc M (2*M), vonMangoldt d/(d:ℝ)) - Real.log (octaveGcdProduct M X)
    0 ≤ E ∧ E ≤ ∑ d ∈ Ioc M (2*M), vonMangoldt d := by
  dsimp only
  rw [log_octave_gcd_product hM,mul_sum,←sum_sub_distrib]
  have term (d : ℕ) : (X:ℝ)*(vonMangoldt d/d)-((X/d : ℕ):ℝ)*vonMangoldt d =
      ((X:ℝ)/d-((X/d : ℕ):ℝ))*vonMangoldt d := by ring
  simp_rw [term]
  constructor
  · exact sum_nonneg fun d _ => mul_nonneg (sub_nonneg.mpr Nat.cast_div_le) vonMangoldt_nonneg
  · apply sum_le_sum
    intro d hd
    have hd0 := hM.trans (mem_Ioc.mp hd).1
    have hlt : (X:ℝ)/d < ((X/d : ℕ):ℝ)+1 := by
      apply (div_lt_iff₀ (Nat.cast_pos.mpr hd0)).mpr
      exact_mod_cast (show X < (X/d+1)*d by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ X hd0)
    exact mul_le_of_le_one_left vonMangoldt_nonneg (by linarith only [hlt])

/-- Removing the proper powers from the gcd product costs at most the
square-root prime-power mass times the maximum cofactor length. -/
theorem octave_gcd_product_ordinary_primes {M : ℕ} (hM : 0 < M) (X : ℕ) :
    let P := ∑ p ∈ (Ioc M (2*M)).filter Nat.Prime, ((X/p : ℕ) : ℝ)*Real.log p
    0 ≤ Real.log (octaveGcdProduct M X)-P ∧
      Real.log (octaveGcdProduct M X)-P ≤ (X:ℝ)/M*(Chebyshev.psi (2*M : ℕ)-Chebyshev.theta (2*M : ℕ)) := by
  classical
  let S := Ioc M (2*M)
  let f (d : ℕ) := ((X/d : ℕ):ℝ)*vonMangoldt d
  let T := S.filter (fun d => ¬d.Prime)
  have hsplit := sum_filter_add_sum_filter_not S Nat.Prime f
  have hp : (∑ p ∈ S.filter Nat.Prime, f p) =
      ∑ p ∈ S.filter Nat.Prime, ((X/p : ℕ):ℝ)*Real.log p :=
    sum_congr rfl (fun p hp => by dsimp only [f]; rw [vonMangoldt_apply_prime (mem_filter.mp hp).2])
  have hd : Real.log (octaveGcdProduct M X)-
      (∑ p ∈ S.filter Nat.Prime, ((X/p : ℕ):ℝ)*Real.log p) = ∑ d ∈ T, f d := by
    rw [log_octave_gcd_product hM,←hp]
    exact sub_eq_of_eq_add (by simpa only [add_comm] using hsplit.symm)
  dsimp only
  rw [hd]
  refine ⟨sum_nonneg fun d _ => mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg, ?_⟩
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
  have hsub : T ⊆ (Ioc 0 (2*M)).filter (fun d => ¬d.Prime) := by
    intro d hd
    obtain ⟨hd,hn⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hM.trans (mem_Ioc.mp hd).1,(mem_Ioc.mp hd).2⟩,hn⟩
  calc _ ≤ ∑ d ∈ T, ((X:ℝ)/M)*vonMangoldt d := by
           apply sum_le_sum
           intro d hd
           have hMd := (mem_Ioc.mp (mem_filter.mp hd).1).1
           exact mul_le_mul_of_nonneg_right (Nat.cast_div_le.trans
             (div_le_div_of_nonneg_left (Nat.cast_nonneg X) (Nat.cast_pos.mpr hM) (Nat.cast_le.mpr hMd.le))) vonMangoldt_nonneg
       _ ≤ _ := by
           rw [←mul_sum]
           exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
             (fun _ _ _ => vonMangoldt_nonneg)) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

#print axioms octave_gcd_product_ordinary_primes
#print axioms log_gcd_lcm_ordinary_divisors
#print axioms log_octave_gcd_product
#print axioms octave_gcd_product_rounding
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
