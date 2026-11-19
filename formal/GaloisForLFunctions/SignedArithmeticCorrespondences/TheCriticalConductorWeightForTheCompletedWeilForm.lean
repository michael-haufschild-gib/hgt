import GaloisForLFunctions.SignedArithmeticCorrespondences.TheSharpWeightTestOnOneConductor
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
  have he : e≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
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
  have hJ₀ : 0≤J := div_nonneg (intervalIntegral.integral_nonneg_of_forall (μ := volume) zero_le_one
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

/-- Below exponent three halves the square of the dual Chebyshev price
eventually dominates the harmonic sequence, even with its exponential
saving. -/
private theorem divergent_subcritical_price {c s : ℝ} (hc : 0<c) (hs : s<3/2) :
    ¬Summable (fun k : ℕ => (((k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)))/
      powerConductorWeight s k)^2) := by
  intro h
  let g := 3/2-s
  have hg : 0<g := sub_pos.mpr hs
  let K := ⌈Real.exp ((c/g)^2)⌉₊+1
  have hlarge (k : ℕ) (hk : K≤k) :
      1/(k:ℝ) ≤ (((k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)))/powerConductorWeight s k)^2 := by
    have h₁ : 1≤k := by dsimp [K] at hk; omega
    have hkR : (0:ℝ)<k := Nat.cast_pos.mpr h₁
    have hex : Real.exp ((c/g)^2) ≤ (k:ℝ) := (Nat.le_ceil _).trans
      (Nat.cast_le.mpr (show ⌈Real.exp ((c/g)^2)⌉₊≤k by dsimp [K] at hk; omega))
    have hl : (c/g)^2≤Real.log (k:ℝ) := (Real.le_log_iff_exp_le hkR).mpr hex
    have hlog := (sq_nonneg (c/g)).trans hl
    have hroot := Real.sqrt_le_sqrt hl
    rw [Real.sqrt_sq (div_nonneg hc.le hg.le)] at hroot
    have hcg := (div_le_iff₀ hg).mp hroot
    have he : (k:ℝ)^(-g) ≤ Real.exp (-c*Real.sqrt (Real.log k)) := by
      rw [Real.rpow_def_of_pos hkR]
      apply Real.exp_le_exp.mpr
      have h₀ := mul_le_mul_of_nonneg_right hcg (Real.sqrt_nonneg (Real.log k))
      nlinarith only [h₀,congrArg (fun x : ℝ => g*x) (Real.sq_sqrt hlog)]
    have hbase : (k:ℝ)^(-(1/2:ℝ)) ≤ (k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k))/(k:ℝ)^s := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hkR s)).mpr
      calc (k:ℝ)^(-(1/2:ℝ))*(k:ℝ)^s = (k:ℝ)^(1+ -g) := by
             rw [← Real.rpow_add hkR]
             congr 1
             dsimp [g]
             ring
           _ = (k:ℝ)*(k:ℝ)^(-g) := by rw [Real.rpow_add hkR,Real.rpow_one]
           _ ≤ _ := mul_le_mul_of_nonneg_left he hkR.le
    rw [powerConductorWeight,max_eq_left h₁]
    calc 1/(k:ℝ) = ((k:ℝ)^(-(1/2:ℝ)))^2 := by
           rw [← Real.rpow_two,← Real.rpow_mul hkR.le,show (-(1/2:ℝ))*2 = -1 by norm_num,
             Real.rpow_neg_one,one_div]
         _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hkR.le _) hbase 2
  have htail := (summable_nat_add_iff K).mpr h
  have hH : Summable (fun n : ℕ => 1/(n:ℝ)) := (summable_nat_add_iff K).mp
    (Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => hlarge (n+K) (Nat.le_add_left _ _)) htail)
  exact (lt_irrefl (1:ℝ)) ((Real.summable_one_div_nat_rpow (p := 1)).mp (by simpa using hH))

/-- The de la Vallée Poussin variation together with the real half-jet
is uniformly bounded by separate power energies exactly from exponent
three halves onward. All tests in the converse are integral. -/
theorem critical_joint_power_iff {c : ℝ} (hc : 0<c) (s : ℝ) :
    (∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ) (a b : ℕ → ℤ),
      (∑ k ∈ Icc 1 N, ((k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)))* |twoSidedCoefficient N a b k|) +
        (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|)/2 ≤
      C*conductorNorm N (fun i => powerConductorWeight s i*upperDivisor N a i)*
        conductorNorm N (fun i => powerConductorWeight s i*upperDivisor N b i)) ↔ 3/2 ≤ s := by
  constructor
  · rintro ⟨C,hC,h⟩
    by_contra! hs
    apply divergent_subcritical_price hc hs
    refine dual_price_summable_of_uniform_variation (powerConductorWeight s) _ ?_ ?_ hC ?_
    · intro k
      exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le (le_max_right k 1))) s
    · intro k
      positivity
    · intro N a b
      have hj := intervalIntegral.integral_nonneg_of_forall (μ := volume) zero_le_one (fun x => abs_nonneg (mixedJetSection N a b x))
      exact (le_add_of_nonneg_right (div_nonneg hj (by norm_num))).trans (h N a b)
  · intro hs
    obtain ⟨C,hC,h⟩ := critical_joint_price hc
    have hw (n : ℕ) (hn : 1≤n) : criticalConductorWeight n ≤ powerConductorWeight s n := by
      simp only [criticalConductorWeight,powerConductorWeight,max_eq_left hn,Real.sqrt_eq_rpow]
      calc (n:ℝ)*(n:ℝ)^(1/2:ℝ) = (n:ℝ)^(1+1/2:ℝ) := by
             rw [Real.rpow_add (Nat.cast_pos.mpr hn),Real.rpow_one]
           _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith only [hs])
    refine ⟨C,hC,fun N a b => (h N a b).trans ?_⟩
    have hn (v : ℕ → ℤ) : conductorNorm N (fun i => criticalConductorWeight i*upperDivisor N v i) ≤
        conductorNorm N (fun i => powerConductorWeight s i*upperDivisor N v i) := by
      apply Real.sqrt_le_sqrt
      apply sum_le_sum
      intro i hi
      simp only [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (weight_pos i).le (hw i (mem_Icc.mp hi).1) 2) (sq_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hn a) hC) (hn b) (Real.sqrt_nonneg _)
      (mul_nonneg hC (Real.sqrt_nonneg _))

#print axioms critical_joint_power_iff
#print axioms critical_quotient_price_summable
#print axioms critical_joint_price
#print axioms interleaved_finite_part_cubic_energy
end GaloisForLFunctions.SignedArithmeticCorrespondences
