import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock.Existence
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Partition

/-! # The quantum instrument determined by bounded memoryless prime clocks -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock

open scoped NNReal
open ModeCapacities CoassociativeSplitting

private theorem same_profile {u v : ℕ → ℝ} (h : ∀ p : Nat.Primes, u p.val=v p.val) :
    profile u=profile v := by
  have mult (g : ℕ → ℝ) : (profile g).IsMultiplicative := RHTower.Sieve.localEuler_isMultiplicative _
  apply (mult u).eq_iff_eq_on_prime_powers _ _ (mult v) |>.mpr
  intro p k hp
  rw [prime_power _ hp,prime_power _ hp,h ⟨p,hp⟩]

def reading (q : ℕ → Curve) (t : ℝ≥0) (m : ℕ) := (q m t).val

/-- Every family of calibrated prime probabilities specifies the same splitter,
even with arbitrary readings assigned at nonprime indices. -/
theorem instrument_kernel (q : ℕ → Curve) (law : ∀ p : Nat.Primes, calibrated p (q p.val))
    (s : ℂ) (t : ℝ≥0) :
    kernel s (1-reading q t) (reading q t)=kernel s (emit t) (survive t) := by
  have agree (p : Nat.Primes) : reading q t p.val=survive t p.val := (calibrated_iff p _).mp (law p) t
  have emission : profile (1-reading q t)=profile (emit t) :=
    same_profile fun p => congrArg (fun x : ℝ => 1-x) (agree p)
  funext a b
  simp only [kernel,branch,sub_add_cancel,capacities_sum,emission,same_profile agree]

/-- Counting and temporal composition determine the full no-emission
operator and its trace on the physical occupation space. -/
theorem calibrated_partition (q : ℕ → Curve) (law : ∀ p : Nat.Primes, calibrated p (q p.val))
    (z : TracePoint) :
    let t := observationTime z
    let r : ℝ≥0 := ⟨t.val,t.property.le⟩
    let s := conservingExponent z
    ∃ T : Gas →ₗᵢ[ℂ] PairGas,
      (∀ f x, T f x=wave (kernel s.val (1-reading q r) (reading q r)) f x) ∧
      vacuumSlice ∘L T.toContinuousLinearMap=gibbsOperator z ∧
      ContinuousLinearMap.opTrace (vacuumSlice ∘L T.toContinuousLinearMap)=riemannZeta z.val := by
  dsimp only
  refine ⟨instrument (conservingExponent z) (observationTime z),?_,noEmission_eq_gibbs z,noEmission_trace z⟩
  intro f x
  rw [instrument_kernel q law]
  exact instrument_apply _ _ _ _

/-- Extend a prime-indexed family to the arithmetic index of a profile.
Only its values at primes enter the splitting amplitudes. -/
def onNaturals (q : Nat.Primes → Curve) (n : ℕ) : Curve :=
  if hp : n.Prime then q ⟨n,hp⟩ else fun _ => ⟨1,zero_le_one,le_rfl⟩

/-- The unique calibrated family realizes the partition operator at every
trace parameter with the same elementary probability curves. -/
theorem unique_partition_family :
    ∃! q : Nat.Primes → Curve, (∀ p, calibrated p (q p)) ∧
      ∀ z : TracePoint,
        let t := observationTime z
        let r : ℝ≥0 := ⟨t.val,t.property.le⟩
        let u := reading (onNaturals q) r
        ∃ T : Gas →ₗᵢ[ℂ] PairGas,
          (∀ f x, T f x=wave (kernel (conservingExponent z).val (1-u) u) f x) ∧
          vacuumSlice ∘L T.toContinuousLinearMap=gibbsOperator z ∧
          ContinuousLinearMap.opTrace (vacuumSlice ∘L T.toContinuousLinearMap)=riemannZeta z.val := by
  obtain ⟨q,hq,unique⟩ := unique_family
  refine ⟨q,⟨hq,?_⟩,fun r hr => unique r hr.1⟩
  intro z
  refine calibrated_partition (onNaturals q) (fun p => ?_) z
  rcases p with ⟨p,hp⟩
  change calibrated ⟨p,hp⟩ (onNaturals q p)
  rw [onNaturals,dif_pos hp]
  exact hq ⟨p,hp⟩

#print axioms instrument_kernel
#print axioms calibrated_partition
#print axioms unique_partition_family

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.SurvivalClock
