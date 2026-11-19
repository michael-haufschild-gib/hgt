import GaloisForLFunctions.SignedArithmeticCorrespondences.SeparateConductorEnergiesOnInterleavingSupports
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusEndpoint
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount

/-!
# The three-halves conductor weight in the full mixed intersection

At conductor n the individual energy charges n³ times the squared
multiplicity. The de la Vallée Poussin factor makes the quotient price
square summable against this weight, including its critical exponent.
The resulting finite-part bound is uniform on all interleaved supports.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory

/-- The value at zero is one. Only positive conductors occur in the energies. -/
def criticalConductorWeight (k : ℕ) : ℝ :=
  ((max k 1:ℕ):ℝ)*Real.sqrt ((max k 1:ℕ):ℝ)

private theorem weight_pos (k : ℕ) : 0<criticalConductorWeight k := by
  have h : 0<(max k 1:ℕ) := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  exact mul_pos (Nat.cast_pos.mpr h) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr h))

private theorem weight_mono : Monotone criticalConductorWeight := by
  intro k l hkl
  have h : ((max k 1:ℕ):ℝ) ≤ ((max l 1:ℕ):ℝ) := Nat.cast_le.mpr (max_le_max_right 1 hkl)
  exact mul_le_mul h (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg _) (Nat.cast_nonneg _)

private theorem inv_weight_summable : Summable (fun k => (1/criticalConductorWeight k)^2) := by
  apply (summable_nat_add_iff 1).mp
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1<3))
  refine hs.congr fun n => ?_
  have hk : 1≤n+1 := Nat.succ_pos _
  simp only [criticalConductorWeight,max_eq_left hk,div_pow,one_pow,mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [pow_succ _ 2]

/-- The weighted quotient price has finite square mass at n^(3/2). -/
theorem critical_quotient_price_summable {c : ℝ} (hc : 0<c) :
    Summable (fun k : ℕ => (((k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)))/
      criticalConductorWeight k)^2) := by
  let K := ⌈Real.exp 1⌉₊+1
  let C := ((2*2).factorial:ℝ)/c^(2*2)
  have hC : 0≤C := by dsimp only [C]; positivity
  apply (summable_nat_add_iff K).mp
  have hs := (summable_nat_add_iff K).mpr (_root_.RHTower.pm_summable_reciprocal_log_sq.mul_left C)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
  intro n
  let k := n+K
  have hk : 1≤k := by dsimp [k,K]; omega
  have hkR : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hex : Real.exp 1≤(k:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (by dsimp [k,K]; omega))
  have hl : 1≤Real.log (k:ℝ) := (Real.le_log_iff_exp_le hkR).mpr hex
  let e := Real.exp (-c*Real.sqrt (Real.log k))
  have he : e≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc.le.neg (Real.sqrt_nonneg _))
  have he₂ : e^2≤C/(Real.log k)^2 :=
    (show e^2≤e by rw [sq]; exact mul_le_of_le_one_right (Real.exp_pos _).le he).trans
      (_root_.RHTower.PrimeCells.exp_neg_mul_sqrt_le hc hl 2)
  change (((k:ℝ)*e)/criticalConductorWeight k)^2 ≤ C*(1/((k:ℝ)*Real.log k^2))
  have hz : ((k:ℝ)*e)/criticalConductorWeight k=e/Real.sqrt (k:ℝ) := by
    rw [criticalConductorWeight,max_eq_left hk,mul_div_mul_left _ _ hkR.ne']
  rw [hz,div_pow,Real.sq_sqrt hkR.le]
  exact (div_le_div_of_nonneg_right he₂ hkR.le).trans_eq (by simp only [div_eq_mul_inv,mul_inv_rev,one_mul]; ring)

/-- Uniform independent conductor energies pay the two-sided Chebyshev
variation and the actual integrated half-jet at every cutoff. -/
theorem critical_joint_price {c : ℝ} (hc : 0<c) :
    ∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ) (a b : ℕ → ℤ),
      (∑ k ∈ Icc 1 N, ((k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)))* |twoSidedCoefficient N a b k|) +
        (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|)/2 ≤
      C*conductorNorm N (fun i => criticalConductorWeight i*upperDivisor N a i)*
        conductorNorm N (fun i => criticalConductorWeight i*upperDivisor N b i) := by
  let w := fun k : ℕ => (k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k))
  let A := Real.sqrt (∑' k, (1/criticalConductorWeight k)^2)
  let B := Real.sqrt (∑' k, (w k/criticalConductorWeight k)^2)
  refine ⟨4*A*B+A^2,add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)) (sq_nonneg _),?_⟩
  exact interleaved_joint_uniform criticalConductorWeight w weight_pos weight_mono
    (fun k => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) inv_weight_summable
    (critical_quotient_price_summable hc)

/-- The full mixed Weil form, after its two fractional boundaries and
common diagonal, is bounded on all supports by the separate cubic masses. -/
theorem interleaved_finite_part_cubic_energy :
    ∃ K : ℝ, 0≤K ∧ ∀ (N : ℕ) (a b : ℕ → ℤ), |interleavedFinitePart N a b| ≤
      K*conductorNorm N (fun i => criticalConductorWeight i*upperDivisor N a i)*
        conductorNorm N (fun i => criticalConductorWeight i*upperDivisor N b i) := by
  obtain ⟨c,C,hc,hC,hP⟩ := interleaved_de_la_vallee_poussin
  obtain ⟨B,hB,hJ⟩ := critical_joint_price hc
  let K := max C 1
  have hK : 0≤K := hC.trans (le_max_left _ _)
  refine ⟨K*B,mul_nonneg hK hB,fun N a b => ?_⟩
  let w := fun k : ℕ => (k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k))
  let V := ∑ k ∈ Icc 1 N, w k* |twoSidedCoefficient N a b k|
  let J := (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|)/2
  have h₀ : 0 ∈ range (N+1) := mem_range.mpr (Nat.succ_pos _)
  have hs : (range (N+1)).erase 0=Icc 1 N := by
    ext k
    simp only [mem_erase,mem_range,mem_Icc]
    omega
  have hsum : (∑ k ∈ range (N+1), |twoSidedCoefficient N a b k| * w k) = V := by
    rw [← sum_erase_add _ _ h₀,hs]
    simp only [w,Nat.cast_zero,zero_mul,mul_zero,add_zero]
    exact sum_congr rfl fun k _ => mul_comm _ _
  have hV : 0≤V := sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (abs_nonneg _)
  have hJ₀ : 0≤J := div_nonneg (intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun x => abs_nonneg (mixedJetSection N a b x))) (by norm_num)
  have hp := hP N a b
  change _ ≤ C*(∑ k ∈ range (N+1), |twoSidedCoefficient N a b k| * w k)+J at hp
  rw [hsum] at hp
  calc _ ≤ C*V+J := hp
       _ ≤ K*(V+J) := by
         rw [mul_add]
         exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hV)
           (le_mul_of_one_le_left hJ₀ (le_max_right _ _))
       _ ≤ _ := (mul_le_mul_of_nonneg_left (hJ N a b) hK).trans_eq (by ring)

#print axioms critical_quotient_price_summable
#print axioms critical_joint_price
#print axioms interleaved_finite_part_cubic_energy
end GaloisForLFunctions.SignedArithmeticCorrespondences
