import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Marginal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Radix
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalResidueState
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # The critical line from the vacuum of any nontrivial finite tensor factor -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology InverseSpectrum.ShellMixing
open _root_.HTGeometry (finiteGibbsStateWeight finiteGibbsPartition finiteGibbsPartition_pos)

variable {ι κ : Type*} [Fintype ι]

theorem vacuum_marginal (χ : ℕ+ → Circle) (β : TraceTemperature) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) :
    marginal χ β a b (factorVacuum h) = (finiteGibbsPartition β.val (fun i => energy (a i)))⁻¹ := by
  rw [marginal_eq_gibbs χ β h,finiteGibbsStateWeight,factorVacuum_label h]
  simp [energy]

/-- A nontrivial exact subsystem has an excited label. Its finite partition is strictly decreasing. -/
theorem subsystem_partition_strict [Nontrivial ι] {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    StrictAnti (fun t => finiteGibbsPartition t (fun i => energy (a i))) := by
  let v := factorVacuum h
  obtain ⟨j,hj⟩ := exists_ne v
  obtain ⟨u,_⟩ := h.2 1
  have hne : a j ≠ 1 := by
    intro he
    have hav : a j = a v := he.trans (factorVacuum_label h).symm
    exact hj (congrArg Prod.fst (h.1 (a₁ := (j,u.2)) (a₂ := (v,u.2)) (congrArg (· * b u.2) hav)))
  have hjE : 0 < energy (a j) := by
    apply Real.log_pos
    have hn : (a j).val ≠ 1 := fun he => hne (PNat.coe_injective he)
    have hp := (a j).pos
    exact_mod_cast (show 1 < (a j).val by omega)
  intro t w htw
  apply Finset.sum_lt_sum
  · intro i _
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg htw.le)
      (Real.log_nonneg (by exact_mod_cast (a i).pos)))
  · exact ⟨j,Finset.mem_univ _,Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right (neg_lt_neg htw) hjE)⟩

/-- The singular global ensemble has a regular finite-subsystem vacuum limit. -/
theorem vacuum_pole_limit (χ : ℕ+ → Circle) {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    Tendsto (fun β => marginal χ β a b (factorVacuum h)) atPartitionPole
      (𝓝 ((finiteGibbsPartition 1 (fun i => energy (a i)))⁻¹)) := by
  letI : Nonempty ι := ⟨factorVacuum h⟩
  have ht : Tendsto (fun β : TraceTemperature => β.val) atPartitionPole (𝓝 (1:ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hc : Continuous (fun t : ℝ => finiteGibbsPartition t (fun i => energy (a i))) :=
    continuous_finsetSum _ (fun i _ => (continuous_id.neg.mul_const (energy (a i))).rexp)
  simpa only [vacuum_marginal χ _ h,Function.comp_apply] using
    (((hc.tendsto 1).comp ht).inv₀ (finiteGibbsPartition_pos 1 _).ne')

/-- Normalizing squared heat amplitudes doubles the real inverse temperature. -/
theorem bornPartition_eq (a : ι → ℕ+) (s : ℂ) :
    (∑ i, ‖heat s (a i)‖^2) = finiteGibbsPartition (2*s.re) (fun i => energy (a i)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_heat,sq,← Real.exp_add]
  congr 1
  ring

/-- A single absolute reading on any nontrivial finite factor detects the critical line. -/
theorem finiteVacuum_born_iff [Nontrivial ι] (χ : ℕ+ → Circle) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (s : ℂ) :
    Tendsto (fun β => marginal χ β a b (factorVacuum h)) atPartitionPole
      (𝓝 ((∑ i, ‖heat s (a i)‖^2)⁻¹)) ↔ s.re = 1/2 := by
  rw [bornPartition_eq]
  have hl := vacuum_pole_limit χ h
  constructor
  · intro hb
    have he := (subsystem_partition_strict h).injective (inv_injective (tendsto_nhds_unique hl hb))
    linarith only [he]
  · intro he
    rwa [show 2*s.re = 1 by linarith only [he]]

theorem finiteVacuum_iff_split_isometry [Nontrivial ι] (χ : ℕ+ → Circle) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (s : ℂ) :
    Tendsto (fun β => marginal χ β a b (factorVacuum h)) atPartitionPole
      (𝓝 ((∑ i, ‖heat s (a i)‖^2)⁻¹)) ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  (finiteVacuum_born_iff χ h s).trans (split_isometric_iff s).symm

/-- Counting occupations divisible by any radix at any prime suffices to test the full isometry. -/
theorem primeDigit_vacuum_iff_split_isometry (χ : ℕ+ → Circle) (q : Nat.Primes) (d : ℕ) (s : ℂ) :
    Tendsto (fun β => selectedMass (fun n => ‖coherentVector χ β n‖^2)
      (fun n => d+2 ∣ (primeCoordinates q n).1)) atPartitionPole
      (𝓝 ((∑ i : Fin (d+2), ‖heat s (primeRayLabel q i.val)‖^2)⁻¹)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  let D : ℕ+ := ⟨d+2,by omega⟩
  letI : Nontrivial (Fin D.val) := inferInstanceAs (Nontrivial (Fin (d+2)))
  let h := radix_exact q D
  have hv : primeRayLabel q (factorVacuum h).val = 1 := factorVacuum_label h
  have hm (β : TraceTemperature) :
      selectedMass (fun n => ‖coherentVector χ β n‖^2) (fun n => d+2 ∣ (primeCoordinates q n).1) =
        marginal χ β (fun i : Fin D.val => primeRayLabel q i.val) (fun c : radixComplement q D => c.val)
          (factorVacuum h) := by
    apply selectedMass_congr
    intro n
    change n ∈ radixComplement q D ↔ ∃ c : radixComplement q D, primeRayLabel q (factorVacuum h).val*c.val = n
    rw [hv]
    simp only [one_mul]
    exact ⟨fun hn => ⟨⟨n,hn⟩,rfl⟩,fun ⟨c,hc⟩ => hc ▸ c.property⟩
  simp only [hm]
  exact finiteVacuum_iff_split_isometry χ h s

#print axioms vacuum_marginal
#print axioms subsystem_partition_strict
#print axioms vacuum_pole_limit
#print axioms bornPartition_eq
#print axioms finiteVacuum_born_iff
#print axioms finiteVacuum_iff_split_isometry
#print axioms primeDigit_vacuum_iff_split_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
