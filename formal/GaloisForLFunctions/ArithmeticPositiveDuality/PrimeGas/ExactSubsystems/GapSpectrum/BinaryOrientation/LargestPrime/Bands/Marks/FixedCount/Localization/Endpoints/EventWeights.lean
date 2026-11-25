import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Separation

/-! # Gibbs weights of ordered occupation events under inclusion of prime packets -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

open Set Filter Topology MeasureTheory _root_.RHTower
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- Hamiltonian of the subset of occupied modes. -/
def energyOf {S : Finset Nat.Primes} {k : ℕ} (R : BreadthSubset k ↥S) :=
  ∑ p ∈ R.val, squarefreePrimeEnergy p.val

theorem energyOf_eq {S : Finset Nat.Primes} {k : ℕ} (R : BreadthSubset k ↥S) :
    finiteSquarefreeHamiltonian S ((squarefreeOccupationEquiv S).symm R.val) = energyOf R := by
  rw [finiteSquarefreeHamiltonian_eq_sum_occupation,
    show squarefreeOccupationFinset ((squarefreeOccupationEquiv S).symm R.val) = R.val from
      (squarefreeOccupationEquiv S).apply_symm_apply R.val]
  rfl

/-- Unnormalized Gibbs weight of a measurable selection of ordered spectra. -/
def eventWeight (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) (F : Set (Fin k → ℝ)) :=
  ∑ R : BreadthSubset k ↥S, if spectrum h R ∈ F then Real.exp (-s*energyOf R) else 0

theorem eventWeight_eq (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (k : ℕ)
    {F : Set (Fin k → ℝ)} (hF : MeasurableSet F) :
    eventWeight S s h k F = finiteSquarefreePartition S s * (slice S s h k F : ℝ) := by
  have hi : (∫ v, F.indicator (fun _ => (1:ℝ)) v ∂(slice S s h k : Measure _)) = (slice S s h k F : ℝ) := by
    rw [integral_indicator hF,setIntegral_const,smul_eq_mul,mul_one,FiniteMeasure.measureReal_eq_coe_coeFn]
  rw [← hi,slice,atomic_integral,Finset.mul_sum,eventWeight]
  apply Finset.sum_congr rfl
  intro R _
  by_cases hr : spectrum h R ∈ F
  · rw [if_pos hr,indicator_of_mem hr,mul_one]
    change Real.exp (-s*energyOf R) = finiteSquarefreePartition S s * finiteSquarefreeBornWeight S s _
    rw [finiteSquarefreeBornWeight_eq,energyOf_eq,mul_div_cancel₀ _ (finiteSquarefreePartition_pos S s).ne']
  · rw [if_neg hr,indicator_of_notMem hr,mul_zero,mul_zero]

theorem coefficient_exp_sum (S : Finset Nat.Primes) (s : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) :
    coefficient S s k = ∑ R : BreadthSubset k ↥S, Real.exp (-s*energyOf R) := by
  have H := eventWeight_eq S s h k (F := univ) MeasurableSet.univ
  change _ = finiteSquarefreePartition S s*((slice S s h k).mass:ℝ) at H
  rw [slice_mass] at H
  simpa only [coefficient,eventWeight,mem_univ,if_true] using H.symm

/-- Extending an occupied subset by empty modes preserves its size and energy. -/
theorem coefficient_mono {A S : Finset Nat.Primes} (hAS : A ⊆ S) (s : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) :
    coefficient A s k ≤ coefficient S s k := by
  let e : ↥A ↪ ↥S := ⟨fun p => ⟨p.val,hAS p.property⟩,fun _ _ hp => Subtype.ext (congrArg (fun x : ↥S => x.val) hp)⟩
  let j : BreadthSubset k ↥A ↪ BreadthSubset k ↥S :=
    ⟨fun R => ⟨R.val.map e,(Finset.card_map e).trans R.property⟩,
     fun _ _ hr => Subtype.ext (Finset.map_injective e (congrArg (fun T : BreadthSubset k ↥S => T.val) hr))⟩
  have he (R : BreadthSubset k ↥A) : energyOf (j R) = energyOf R := by
    change (∑ p ∈ R.val.map e, squarefreePrimeEnergy p.val) = _
    rw [Finset.sum_map]
    rfl
  let w (R : BreadthSubset k ↥S) := Real.exp (-s*energyOf R)
  rw [coefficient_exp_sum A s h,coefficient_exp_sum S s h]
  calc _ = ∑ R ∈ Finset.univ.map j, w R := by simp only [Finset.sum_map,w,he]
       _ ≤ ∑ R, w R := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le

/-- Conditional law at an arbitrary inverse temperature on the moving band. -/
def thermalLaw (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) (k : ℕ) := (slice (added c d h) s h k).normalize

theorem thermalLaw_event {c d s : ℝ} (h : Ioi (0:ℝ)) (k : ℕ) {F : Set (Fin k → ℝ)} (hF : MeasurableSet F)
    (hp : 0 < coefficient (added c d h) s k) :
    (thermalLaw c d h s k F : ℝ) = eventWeight (added c d h) s h k F / coefficient (added c d h) s k := by
  let S := added c d h
  let μ := slice S s h k
  have hZ := finiteSquarefreePartition_pos S s
  have hm : μ.mass ≠ 0 := by
    intro hz
    have he := slice_mass S s h k
    change (μ.mass:ℝ) = _ at he
    rw [hz,NNReal.coe_zero] at he
    exact (pos_of_mul_pos_right hp hZ.le).ne he
  change (μ.normalize F : ℝ) = eventWeight S s h k F / coefficient S s k
  rw [FiniteMeasure.normalize_eq_of_nonzero _ ((FiniteMeasure.mass_nonzero_iff μ).mp hm),
    NNReal.coe_mul,NNReal.coe_inv,← div_eq_inv_mul,eventWeight_eq S s h k hF,coefficient,
    ← slice_mass S s h k,mul_div_mul_left _ _ hZ.ne']

/-- A uniform upper bound on the tilt multiplier controls the entire selected event. -/
theorem eventWeight_le (S : Finset Nat.Primes) (s M : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) (F : Set (Fin k → ℝ))
    (hM : ∀ R : BreadthSubset k ↥S, spectrum h R ∈ F → (1-s)*energyOf R ≤ M) :
    eventWeight S s h k F ≤ Real.exp M * coefficient S 1 k := by
  rw [eventWeight,coefficient_exp_sum S 1 h,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro R _
  by_cases hr : spectrum h R ∈ F
  · rw [if_pos hr,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hM R hr]
  · rw [if_neg hr]
    exact (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le

#print axioms eventWeight_eq
#print axioms coefficient_mono
#print axioms thermalLaw_event
#print axioms eventWeight_le

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
