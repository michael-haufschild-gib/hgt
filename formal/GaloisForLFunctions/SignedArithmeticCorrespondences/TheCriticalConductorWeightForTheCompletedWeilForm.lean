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

/-- At every large dyadic cutoff the alternating integral block on (K,2K]
violates any proposed subcritical separate power bound. Its interior
quotient cells have absolute value two. -/
theorem alternating_dyadic_price_obstruction {c s : ℝ} (hc : 0 < c) (hs : s < 3/2) (B : ℝ) :
    ∀ᶠ K : ℕ in Filter.atTop, ∃ a b : ℕ → ℤ,
      (∀ i ∈ Icc 1 (2*K), upperDivisor (2*K) a i=if i=1 then 1 else 0) ∧
      (∀ i ∈ Icc 1 (2*K), upperDivisor (2*K) b i=if K < i then (-1:ℤ)^i else 0) ∧
      (∀ i ∈ Ioo K (2*K), |twoSidedCoefficient (2*K) a b i|=2) ∧
      B*conductorNorm (2*K) (fun i => powerConductorWeight s i*upperDivisor (2*K) a i)*
        conductorNorm (2*K) (fun i => powerConductorWeight s i*upperDivisor (2*K) b i) <
        ∑ i ∈ Icc 1 (2*K), ((i:ℝ)*Real.exp (-c*Real.sqrt (Real.log i)))*|twoSidedCoefficient (2*K) a b i| := by
  let t := max s 0
  let g := (3/2-t)/2
  have ht : 0 ≤ t := le_max_right _ _
  have hg : 0 < g := by
    have he : t < 3/2 := max_lt hs (by norm_num)
    dsimp only [g]; linarith only [he]
  let b₀ := max B 1
  have hb₀ : 0 < b₀ := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨L,hL⟩ := exists_nat_gt (max (Real.exp ((c/g)^2)) ((4*b₀)^(1/g)))
  filter_upwards [Filter.eventually_ge_atTop (L+1)] with K hK
  let N := 2*K
  let S := Icc 1 N
  let T := Ioc K N
  let v := fun i : ℕ => if K < i then (-1:ℤ)^i else 0
  let r := powerConductorWeight s
  let w := fun i : ℕ => (i:ℝ)*Real.exp (-c*Real.sqrt (Real.log i))
  have hK₀ : 0 < K := by omega
  have hN : 0 < N := by dsimp [N]; omega
  have hKN : K ≤ N := by dsimp [N]; omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hLN : (L:ℝ) ≤ N := Nat.cast_le.mpr (by omega)
  have hT : T⊆S := fun i hi => mem_Icc.mpr ⟨(hK₀.trans (mem_Ioc.mp hi).1),(mem_Ioc.mp hi).2⟩
  have hcard : T.card=K := by simp only [T,N,Nat.card_Ioc]; omega
  obtain ⟨a,b,ha,hb,_,hC⟩ := conductor_one_profile hN v
  let C := twoSidedCoefficient N a b
  have cell (i : ℕ) (hi : i∈T) : |C i|=if i < N then 2 else 1 := by
    have hik := (mem_Ioc.mp hi).1
    have hne : i≠1 := by omega
    change |twoSidedCoefficient N a b i|=_
    rw [hC i (hT hi),if_neg hne,add_zero]
    by_cases hin : i < N
    · simp only [v,if_pos hik,if_pos (show K < i+1 by omega),if_pos (show i+1 ≤ N by omega),
        if_pos hin,Int.cast_pow,Int.cast_neg,Int.cast_one,pow_succ,mul_neg_one,sub_neg_eq_add]
      rw [← two_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    · simp [v,hik,hin,show ¬i+1 ≤ N by omega,abs_pow]
  have h₁ : 1∈S := mem_Icc.mpr ⟨le_rfl,hN⟩
  have hu : conductorNorm N (fun i => r i*upperDivisor N a i)=1 := by
    rw [conductorNorm,sum_eq_single_of_mem 1 h₁]
    · simp [ha 1 h₁,r,powerConductorWeight]
    · intro i hi he; simp [ha i hi,he]
  have hv : conductorNorm N (fun i => r i*upperDivisor N b i) ≤ (N:ℝ)^t*Real.sqrt K := by
    have entry (i : ℕ) (hi : i∈S) :
        (r i*(upperDivisor N b i:ℝ))^2 ≤ if i∈T then ((N:ℝ)^t)^2 else 0 := by
      have h₁ := (mem_Icc.mp hi).1
      have h₂ := (mem_Icc.mp hi).2
      rw [hb i hi]
      by_cases hk : K < i
      · have hri : r i ≤ (N:ℝ)^t := by
          change ((max i 1:ℕ):ℝ)^s ≤ _
          rw [max_eq_left h₁]
          exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h₁) (le_max_left s 0)).trans
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr h₂) ht)
        have hrp : 0 ≤ r i := Real.rpow_nonneg (Nat.cast_nonneg _) _
        simpa only [if_pos (show i∈T from mem_Ioc.mpr ⟨hk,h₂⟩),v,if_pos hk,Int.cast_pow,
          Int.cast_neg,Int.cast_one,mul_pow,pow_right_comm (-1:ℝ) i 2,neg_one_sq,one_pow,mul_one]
          using pow_le_pow_left₀ hrp hri 2
      · simp [v,T,hk]
    have e := sum_le_sum (s := S) entry
    have hfilter : S.filter (fun i => i∈T)=T := by ext i; simp only [mem_filter]; exact and_iff_right_of_imp (fun h => hT h)
    rw [← sum_filter,hfilter,sum_const,nsmul_eq_mul,hcard] at e
    apply (Real.sqrt_le_sqrt e).trans_eq
    rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq (Real.rpow_nonneg (Nat.cast_nonneg _) _),mul_comm]
  let e := Real.exp (-c*Real.sqrt (Real.log N))
  have low : (K:ℝ)^2*e ≤ ∑ i ∈ S, w i*|C i| := by
    have row (i : ℕ) (hi : i∈T) : (K:ℝ)*e ≤ w i*|C i| := by
      have h₁ := (mem_Ioc.mp hi).1
      have h₂ := (mem_Ioc.mp hi).2
      have hl := Real.sqrt_le_sqrt (Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < i)) (Nat.cast_le.mpr h₂))
      have hw : (K:ℝ)*e ≤ w i := mul_le_mul (Nat.cast_le.mpr h₁.le)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hl (neg_nonpos.mpr hc.le)))
        (Real.exp_pos _).le (Nat.cast_nonneg _)
      apply hw.trans (le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) ?_)
      rw [cell i hi]; split <;> norm_num
    have hsum := sum_le_sum row
    rw [sum_const,nsmul_eq_mul,hcard] at hsum
    exact (show (K:ℝ)^2*e=(K:ℝ)*((K:ℝ)*e) by ring).le.trans
      (hsum.trans (sum_le_sum_of_subset_of_nonneg hT (fun i _ _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (abs_nonneg _))))
  have hlog := (Real.le_log_iff_exp_le hNR).mpr (((le_max_left _ _).trans hL.le).trans hLN)
  have hroot := Real.sqrt_le_sqrt hlog
  rw [Real.sqrt_sq (div_nonneg hc.le hg.le)] at hroot
  have he : (N:ℝ)^(-g) ≤ e := by
    rw [Real.rpow_def_of_pos hNR]
    apply Real.exp_le_exp.mpr
    have hcp := mul_le_mul_of_nonneg_right ((div_le_iff₀ hg).mp hroot) (Real.sqrt_nonneg (Real.log N))
    nlinarith only [hcp,congrArg (fun z : ℝ => g*z) (Real.sq_sqrt ((sq_nonneg _).trans hlog))]
  have hbN : 4*b₀ < (N:ℝ)^g := by
    have h := Real.rpow_lt_rpow (Real.rpow_nonneg (mul_nonneg (by norm_num) hb₀.le) _)
      (((le_max_right _ _).trans_lt hL).trans_le hLN) hg
    rwa [← Real.rpow_mul (mul_nonneg (by norm_num) hb₀.le),one_div_mul_cancel hg.ne',Real.rpow_one] at h
  have hsqrt : Real.sqrt K ≤ (N:ℝ)^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (Nat.cast_le.mpr hKN)
  have hmul : 0 < (N:ℝ)^t*(N:ℝ)^(1/2:ℝ) := mul_pos (Real.rpow_pos_of_pos hNR _) (Real.rpow_pos_of_pos hNR _)
  have heq : ((N:ℝ)^g/4)*((N:ℝ)^t*(N:ℝ)^(1/2:ℝ))=(K:ℝ)^2*(N:ℝ)^(-g) := by
    have hg' : g+(t+1/2)=2+ -g := by dsimp [g]; ring
    calc _ = (N:ℝ)^(g+(t+1/2))/4 := by rw [Real.rpow_add hNR,Real.rpow_add hNR]; ring
         _ = (N:ℝ)^2*(N:ℝ)^(-g)/4 := by rw [hg',Real.rpow_add hNR,Real.rpow_two]
         _ = _ := by dsimp only [N]; push_cast; ring
  refine ⟨a,b,ha,hb,fun i hi => (cell i (mem_Ioc.mpr ⟨(mem_Ioo.mp hi).1,(mem_Ioo.mp hi).2.le⟩)).trans
    (if_pos (mem_Ioo.mp hi).2),?_⟩
  change B*conductorNorm N (fun i => r i*upperDivisor N a i)*conductorNorm N (fun i => r i*upperDivisor N b i) < _
  rw [hu,mul_one]
  calc _ ≤ b₀*((N:ℝ)^t*(N:ℝ)^(1/2:ℝ)) := mul_le_mul (le_max_left _ _) (hv.trans
           (mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hNR.le _))) (Real.sqrt_nonneg _) hb₀.le
       _ < _ := mul_lt_mul_of_pos_right (show b₀ < (N:ℝ)^g/4 by linarith only [hbN]) hmul
       _ = _ := heq
       _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg _)
       _ ≤ _ := low

#print axioms alternating_dyadic_price_obstruction

#print axioms critical_joint_power_iff
#print axioms critical_quotient_price_summable
#print axioms critical_joint_price
#print axioms interleaved_finite_part_cubic_energy
end GaloisForLFunctions.SignedArithmeticCorrespondences
