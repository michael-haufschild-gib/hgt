import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.GibbsThermometry

/-! # Removing a prime block from the thermal partition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open _root_.RHTower.PrimeCoShift
local instance (P : Prop) : Decidable P := Classical.propDecidable P

private theorem gasPartition_sum (β : TraceTemperature) :
    (riemannZeta β.val).re = ∑' n, thermalWeight β n := (congrArg Complex.re (thermalWeight_partition β)).symm

theorem gasPartition_pos (β : TraceTemperature) : 0 < (riemannZeta β.val).re := by
  rw [gasPartition_sum]
  exact (thermalWeight_pos β 1).trans_le ((thermalWeight_summable β).le_tsum 1 (fun n _ => (thermalWeight_pos β n).le))

private theorem weight_le {β γ : TraceTemperature} (h : β ≤ γ) (n : ℕ+) : thermalWeight γ n ≤ thermalWeight β n := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg h) (Real.log_nonneg (by exact_mod_cast n.pos))

private theorem weight_lt {β γ : TraceTemperature} (h : β < γ) (n : ℕ+) (hn : 1 < n.val) :
    thermalWeight γ n < thermalWeight β n := by
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_right (neg_lt_neg h) (Real.log_pos (by exact_mod_cast hn))

/-- The partition restricted to a fixed set decreases strictly if the set contains an excitation. -/
theorem thermalEvent_strictAnti (P : ℕ+ → Prop) (a : ℕ+) (ha : 1 < a.val) (hP : P a) :
    StrictAnti (fun β => selectedMass (thermalWeight β) P) := by
  intro β γ h
  apply (selected_summable (thermalWeight_summable γ) P).tsum_lt_tsum _ (i := a) _
    (selected_summable (thermalWeight_summable β) P)
  · intro n
    by_cases hn : P n
    · simpa only [if_pos hn] using weight_le h.le n
    · simp [hn]
  · simpa only [if_pos hP] using weight_lt h a ha

theorem gasPartition_strictAnti : StrictAnti (fun β : TraceTemperature => (riemannZeta β.val).re) := by
  intro β γ h
  change (riemannZeta γ.val).re < (riemannZeta β.val).re
  rw [gasPartition_sum γ,gasPartition_sum β]
  exact (thermalWeight_summable γ).tsum_lt_tsum (weight_le h.le)
    (weight_lt h 2 (by norm_num)) (thermalWeight_summable β)

private theorem weight_product (β : TraceTemperature) (a n : ℕ+) :
    thermalWeight β (a*n) = thermalWeight β a * thermalWeight β n := by
  rw [thermalWeight,energy_mul,mul_add,Real.exp_add]
  rfl

/-- Multiplication maps the whole thermal ensemble onto the divisible shells with one Boltzmann factor. -/
theorem divisibleThermalMass (β : TraceTemperature) (a : ℕ+) :
    selectedMass (thermalWeight β) (fun n => a ∣ n) = thermalWeight β a * (riemannZeta β.val).re := by
  let f (n : ℕ+) := if a ∣ n then thermalWeight β n else 0
  have hi : Function.Injective (fun k : ℕ+ => a*k) := fun _ _ h => mul_left_cancel h
  have hs : Function.support f ⊆ Set.range (fun k : ℕ+ => a*k) := by
    intro n hn
    by_cases hd : a ∣ n
    · obtain ⟨k,rfl⟩ := hd
      exact ⟨k,rfl⟩
    · exact False.elim (hn (if_neg hd))
  change ∑' n, f n = _
  rw [← hi.tsum_eq hs,gasPartition_sum]
  have h (k : ℕ+) : f (a*k) = thermalWeight β a * thermalWeight β k :=
    (if_pos (dvd_mul_right a k)).trans (weight_product β a k)
  simp_rw [h]
  exact tsum_mul_left

theorem clockBlock_gt_one (p : Nat.Primes) (D : ℕ+) : 1 < (primeRayLabel p D.val).val :=
  p.property.one_lt.trans_le (Nat.le_self_pow D.ne_zero _)

theorem clockRatio_lt_one (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) : gibbsBlockRatio β p D < 1 :=
  Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos (zero_lt_one.trans β.property))
    (mul_pos (Nat.cast_pos.mpr D.pos) (prime_energy_pos p)))

theorem clockReturn_positive (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    0 < gibbsClockReturn χ β p D := by
  rw [gibbsClockReturn_eq]
  exact div_pos (inv_pos.mpr (sub_pos.mpr (clockRatio_lt_one β p D))) (gasPartition_pos β)

/-- The reciprocal return probability is the partition sum of the shells with the whole block deleted. -/
theorem clockReturn_inv_eq (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    (gibbsClockReturn χ β p D)⁻¹ = selectedMass (thermalWeight β) (fun n => ¬ primeRayLabel p D.val ∣ n) := by
  let a := primeRayLabel p D.val
  have hsum : selectedMass (thermalWeight β) (fun n => ¬ a ∣ n) + selectedMass (thermalWeight β) (fun n => a ∣ n)
      = (riemannZeta β.val).re := by
    rw [gasPartition_sum]
    unfold selectedMass
    rw [← (selected_summable (thermalWeight_summable β) _).tsum_add (selected_summable (thermalWeight_summable β) _)]
    apply tsum_congr
    intro n
    by_cases hd : a ∣ n <;> simp [hd]
  have hw : thermalWeight β a = gibbsBlockRatio β p D := by
    simp only [thermalWeight,a,energy_primeRayLabel,gibbsBlockRatio]
  rw [divisibleThermalMass,hw] at hsum
  rw [gibbsClockReturn_eq,inv_div,div_inv_eq_mul]
  change _ = selectedMass (thermalWeight β) (fun n => ¬ a ∣ n)
  linear_combination hsum.symm

theorem clockReturn_strictMono (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) :
    StrictMono (fun β => gibbsClockReturn χ β p D) := by
  let a := primeRayLabel p D.val
  have h1 : ¬ a.val ∣ 1 := Nat.not_dvd_of_pos_of_lt Nat.zero_lt_one (clockBlock_gt_one p D)
  have hn : ¬ a ∣ a+1 := fun hd => h1 (Nat.dvd_add_self_left.mp (PNat.dvd_iff.mp hd))
  have he : 1 < (a+1).val := by change 1 < a.val+1; have := a.pos; omega
  intro β γ h
  apply (inv_lt_inv₀ (clockReturn_positive χ γ p D) (clockReturn_positive χ β p D)).mp
  rw [clockReturn_inv_eq,clockReturn_inv_eq]
  exact thermalEvent_strictAnti (fun n => ¬ a ∣ n) (a+1) he hn h

/-- For any fixed test containing the vacuum, only its vacuum term survives the cold limit. -/
theorem thermalEvent_cold (P : ℕ+ → Prop) (hv : P 1) :
    Tendsto (fun β => selectedMass (thermalWeight β) P) atTop (𝓝 1) := by
  let b : TraceTemperature := ⟨2,by norm_num⟩
  let f (β : TraceTemperature) (n : ℕ+) := if P n then thermalWeight β n else 0
  have ht : Tendsto (fun β : TraceTemperature => β.val) atTop atTop :=
    (tendsto_Ioi_atTop (a := (1:ℝ)) (f := fun β : TraceTemperature => β)).mp tendsto_id
  have hl (n : ℕ+) : Tendsto (fun β => f β n) atTop (𝓝 (if n = 1 then (1:ℝ) else 0)) := by
    by_cases hn : n = 1
    · subst n
      simp [f,hv,thermalWeight,energy]
    by_cases hP : P n
    · have hn₁ : 1 < n.val := by
        by_contra h
        apply hn
        apply PNat.coe_injective
        change n.val = 1
        have := n.pos
        omega
      have he : 0 < energy n := Real.log_pos (by exact_mod_cast hn₁)
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (ht.atTop_mul_const he)
      simpa only [f,if_pos hP,if_neg hn,thermalWeight,Function.comp_def,neg_mul] using h
    · simp [f,hP,hn]
  have hb : ∀ᶠ β in atTop, ∀ n, ‖f β n‖ ≤ thermalWeight b n := by
    filter_upwards [eventually_ge_atTop b] with β hβ n
    by_cases hn : P n
    · simpa only [f,if_pos hn,Real.norm_of_nonneg (thermalWeight_pos β n).le] using weight_le hβ n
    · simp [f,hn,(thermalWeight_pos b n).le]
  have h := tendsto_tsum_of_dominated_convergence (thermalWeight_summable b) hl hb
  simpa only [selectedMass,f,tsum_ite_eq] using h

#print axioms gasPartition_pos
#print axioms thermalEvent_strictAnti
#print axioms gasPartition_strictAnti
#print axioms divisibleThermalMass
#print axioms clockBlock_gt_one
#print axioms clockRatio_lt_one
#print axioms clockReturn_positive
#print axioms clockReturn_inv_eq
#print axioms clockReturn_strictMono
#print axioms thermalEvent_cold

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
