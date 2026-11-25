import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.FiniteEnergy

/-! # The isolated zero energy in a finite prime band -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace
open scoped ENNReal

theorem packetEnergy_zero_iff (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) (x : SquarefreeBitConfig S) :
    packetEnergy S h x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hs := (mul_eq_zero.mp hx).resolve_left (show h.val ≠ 0 from h.property.ne')
    have hp (p : ↥S) : 0 < squarefreePrimeEnergy p.val :=
      Real.log_pos (by exact_mod_cast p.val.property.one_lt)
    change (∑ p : ↥S, ((x p).val:ℝ)*squarefreePrimeEnergy p.val) = 0 at hs
    have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun (p : ↥S) _ =>
      mul_nonneg (Nat.cast_nonneg (x p).val) (hp p).le)).mp hs
    funext p
    apply Fin.ext
    have hz := (mul_eq_zero.mp (ha p (Finset.mem_univ p))).resolve_right (hp p).ne'
    change (x p).val = 0
    exact Nat.cast_eq_zero.mp hz
  · rintro rfl
    simp [packetEnergy,finiteSquarefreeHamiltonian,squarefreeBitEnergy]

/-- Only the empty configuration contributes to the finite zero-energy line. -/
theorem packet_zero_mass (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) :
    (packetLaw S h : Measure ℝ) {0} = ENNReal.ofReal ((finiteSquarefreePartition S (1+h.val))⁻¹) := by
  rw [packetLaw,observed_apply _ _ _ (measurableSet_singleton _),Finset.sum_eq_single (0 : SquarefreeBitConfig S)]
  · rw [indicator_of_mem (show packetEnergy S h 0 ∈ ({0}:Set ℝ) from (packetEnergy_zero_iff S h 0).mpr rfl)]
    simp [finiteSquarefreeBornWeight_eq,finiteSquarefreeHamiltonian,squarefreeBitEnergy,one_div]
  · intro x _ hx
    have he : packetEnergy S h x ∉ ({0}:Set ℝ) := fun hx0 => hx ((packetEnergy_zero_iff S h x).mp hx0)
    rw [indicator_of_notMem he]
  · simp

private theorem partition_product (N : ℕ) (s : ℝ) :
    finiteSquarefreePartition (Window.packet N) s = ∏ p ∈ N.primesLE, (1+(p:ℝ)^(-s)) := by
  calc _ = ∏ p : ↥(Window.packet N), (1+(p.val.val:ℝ)^(-s)) := by
         apply Finset.prod_congr rfl
         intro p _
         rw [Real.rpow_def_of_pos (by exact_mod_cast p.val.property.pos)]
         simp only [squarefreePrimeNome,primeSchurWeight,mul_comm]
       _ = ∏ p ∈ Window.packet N, (1+(p.val:ℝ)^(-s)) :=
         Finset.prod_coe_sort (Window.packet N) (fun p : Nat.Primes => 1+(p.val:ℝ)^(-s))
       _ = _ := Finset.prod_subtype_of_mem (fun n : ℕ => 1+(n:ℝ)^(-s)) (fun _ hn => Nat.prime_of_mem_primesLE hn)

private theorem event_partition (c : ℝ) (h : Ioi (0:ℝ)) :
    jointReading c 0 h = finiteSquarefreePartition (initial c h) (1+h.val)/binaryPartition h := by
  rw [joint_product c 0 (by simp),partition_product]
  simp only [add_zero,one_mul]
  rfl

theorem vacuum_ratio {c d : ℝ} (hcd : c ≤ d) (h : Ioi (0:ℝ)) :
    (finiteSquarefreePartition (added c d h) (1+h.val))⁻¹ = jointReading c 0 h/jointReading d 0 h := by
  rw [event_partition,event_partition,div_div_div_cancel_right₀ (binaryPartition_pos h).ne',
    partition_split (initial_subset hcd h)]
  change _ = _ / (_ * finiteSquarefreePartition (added c d h) (1+h.val))
  field_simp [(finiteSquarefreePartition_pos (initial c h) (1+h.val)).ne',
    (finiteSquarefreePartition_pos (added c d h) (1+h.val)).ne']

/-- The discrete vacuum atom survives weak convergence with its exact mass. -/
theorem vacuum_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    Tendsto (fun h => ((packetLaw (added c d h) h : Measure ℝ) {0}).toReal) criticalApproach
      (𝓝 (Real.exp (expIntegralOne d-expIntegralOne c))) := by
  have h1 := joint_limit (t := 0) hc (by simp)
  have h2 := joint_limit (t := 0) (hc.trans hcd) (by simp)
  simp only [add_zero,one_mul,div_one] at h1 h2
  have H := h1.div h2 (Real.exp_pos _).ne'
  rw [← Real.exp_sub,neg_sub_neg] at H
  apply H.congr
  intro h
  rw [packet_zero_mass,ENNReal.toReal_ofReal (inv_pos.mpr (finiteSquarefreePartition_pos _ _)).le,
    vacuum_ratio hcd.le]
  rfl

#print axioms packetEnergy_zero_iff
#print axioms packet_zero_mass
#print axioms vacuum_ratio
#print axioms vacuum_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands
