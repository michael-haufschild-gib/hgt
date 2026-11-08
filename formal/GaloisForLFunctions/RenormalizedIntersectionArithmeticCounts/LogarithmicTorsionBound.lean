import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.LogarithmicMangoldtTail
import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector
import GaloisForLFunctions.HTGeometry.WeightedSchurTest
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeStarCompensation

/-!
# The sharp logarithmic boundary for full torsion compensation

A Schur reference vector controls the two orientations of the divisor kernel.
The multiple row uses the convergent Mangoldt logarithmic tail; the divisor row
uses the exact logarithmic divisor identity. Every conductor interaction is
bounded and admits an explicit positive diagonal correction above exponent two.
An exact restriction to the original prime star proves necessity.
-/

noncomputable section
open Finset
open scoped ArithmeticFunction.vonMangoldt
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticCouplingTheory

/-- The logarithmic reference vector used to bound both divisor directions. -/
def logarithmicSchurReference (a : ℝ) (n : ℕ) : ℝ :=
  1/(Real.sqrt n*(logConductor n)^a)

theorem logarithmicSchurReference_pos (a : ℝ) (n : ℕ) (hn : 0 < n) :
    0 < logarithmicSchurReference a n := by
  have hl : 0 < logConductor n := lt_of_lt_of_le zero_lt_one (one_le_logConductor n)
  exact one_div_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hn))
    (Real.rpow_pos_of_pos hl _))

/-- The forward divisor row turns into reciprocal Mangoldt mass after normalization. -/
theorem divisorKernel_logReference_multiple (a : ℝ) (m t : ℕ) (hm : 0 < m) :
    divisorKernel m (m*t)*logarithmicSchurReference a (m*t)=
      (Λ t:ℝ)/(Real.sqrt m*(t:ℝ)*(logConductor (m*t))^a) := by
  rw [divisorKernel,if_pos (dvd_mul_right m t),Nat.mul_div_cancel_left _ hm,
    logarithmicSchurReference,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg m),
    div_mul_div_comm,mul_one]
  congr 1
  calc Real.sqrt (t:ℝ)*(Real.sqrt (m:ℝ)*Real.sqrt (t:ℝ)*(logConductor (m*t))^a)=
        Real.sqrt (m:ℝ)*(Real.sqrt (t:ℝ))^2*(logConductor (m*t))^a := by ring
       _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg t)]

/-- The reverse divisor row has the exact common conductor denominator. -/
theorem divisorKernel_logReference_divisor (a : ℝ) (m t : ℕ) (hm : 0 < m) :
    divisorKernel m (m*t)*logarithmicSchurReference a m=
      (Λ t:ℝ)/(Real.sqrt ((m*t:ℕ):ℝ)*(logConductor m)^a) := by
  rw [divisorKernel,if_pos (dvd_mul_right m t),Nat.mul_div_cancel_left _ hm,
    logarithmicSchurReference,div_mul_div_comm,mul_one,Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m)]
  congr 1
  ring

/-- Every reverse divisor row is controlled by the exact logarithmic divisor identity. -/
theorem divisorKernel_logReference_lower_bound (a : ℝ) (ha : 0 ≤ a)
    (n : ℕ) (hn : 0 < n) (S : Finset ℕ) (hS : ∀ m∈S, 0 < m) :
    (∑ m∈S,divisorKernel m n*logarithmicSchurReference a m) ≤ Real.log n/Real.sqrt n := by
  have hterm (m : ℕ) (hm : m∈S) :
      divisorKernel m n*logarithmicSchurReference a m ≤
        if m∣n then (Λ (n/m):ℝ)/Real.sqrt n else 0 := by
    by_cases hd : m∣n
    · have he := divisorKernel_logReference_divisor a m (n/m) (hS m hm)
      rw [Nat.mul_div_cancel' hd] at he
      rw [he,if_pos hd,div_mul_eq_div_div]
      exact div_le_self (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
        (Real.one_le_rpow (one_le_logConductor m) ha)
    · simp only [divisorKernel,if_neg hd,zero_mul,le_refl]
  have hsub : S.filter (fun m => m∣n) ⊆ n.divisors := by
    intro m hm
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hm).2,hn.ne'⟩
  calc (∑ m∈S,divisorKernel m n*logarithmicSchurReference a m) ≤
        ∑ m∈S,if m∣n then (Λ (n/m):ℝ)/Real.sqrt n else 0 := sum_le_sum hterm
       _ = ∑ m∈S.filter (fun m => m∣n),(Λ (n/m):ℝ)/Real.sqrt n := by rw [sum_filter]
       _ ≤ ∑ m∈n.divisors,(Λ (n/m):ℝ)/Real.sqrt n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ =>
          div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
       _ = Real.log n/Real.sqrt n := by
        rw [←sum_div,Nat.sum_div_divisors n (fun d => (Λ d:ℝ)),ArithmeticFunction.vonMangoldt_sum]

/-- The forward divisor row is uniformly controlled by the convergent Mangoldt tail. -/
theorem divisorKernel_logReference_upper_bound (a : ℝ) (ha : 1 < a)
    (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : ∀ n∈S, 0 < n) :
    (∑ n∈S,divisorKernel m n*logarithmicSchurReference a n) ≤
      (∑' t : ℕ,(Λ t:ℝ)/((t:ℝ)*(logConductor t)^a))/Real.sqrt m := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hsqrt := Real.sqrt_pos.mpr hmR
  have htail := summable_mangoldt_logConductor a ha
  have hnn (t : ℕ) : 0 ≤ (Λ t:ℝ)/((t:ℝ)*(logConductor t)^a) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
        (lt_of_lt_of_le zero_lt_one (one_le_logConductor t)).le _))
  have hinj : Set.InjOn (fun n : ℕ => n/m) (S.filter (fun n => m∣n)) := by
    intro n hn k hk he
    have hn' := (mem_filter.mp hn).2
    have hk' := (mem_filter.mp hk).2
    calc n=m*(n/m) := (Nat.mul_div_cancel' hn').symm
         _ = m*(k/m) := congrArg (fun t : ℕ => m*t) he
         _ = k := Nat.mul_div_cancel' hk'
  have hterm (n : ℕ) (hn : n∈S.filter (fun n => m∣n)) :
      divisorKernel m n*logarithmicSchurReference a n ≤
        (1/Real.sqrt m)*((Λ (n/m):ℝ)/(((n/m:ℕ):ℝ)*(logConductor (n/m))^a)) := by
    have hdiv := (mem_filter.mp hn).2
    have hn0 := hS n (mem_filter.mp hn).1
    have ht : (0:ℕ) < n/m := by
      by_contra h
      have hz : (n/m:ℕ)=0 := le_antisymm (le_of_not_gt h) (Nat.zero_le _)
      have he := Nat.mul_div_cancel' hdiv
      rw [hz,mul_zero] at he
      omega
    have htR : (0:ℝ) < ((n/m:ℕ):ℝ) := by exact_mod_cast ht
    have hL : logConductor (n/m) ≤ logConductor n := by
      dsimp only [logConductor]
      have hdivR : ((n/m:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.div_le_self n m
      exact add_le_add (le_refl 1) (Real.log_le_log htR hdivR)
    have hp : (logConductor (n/m))^a ≤ (logConductor n)^a :=
      Real.rpow_le_rpow (by linarith [one_le_logConductor (n/m)]) hL (by linarith only [ha])
    have hpow := Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (one_le_logConductor (n/m))) a
    have he := divisorKernel_logReference_multiple a m (n/m) hm
    rw [Nat.mul_div_cancel' hdiv] at he
    rw [he]
    calc (Λ (n/m):ℝ)/(Real.sqrt m*((n/m:ℕ):ℝ)*(logConductor n)^a) ≤
          (Λ (n/m):ℝ)/(Real.sqrt m*((n/m:ℕ):ℝ)*(logConductor (n/m))^a) :=
        div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
          (mul_pos (mul_pos hsqrt htR) hpow)
          (mul_le_mul_of_nonneg_left hp (mul_pos hsqrt htR).le)
         _ = _ := by field_simp
  calc (∑ n∈S,divisorKernel m n*logarithmicSchurReference a n)=
        ∑ n∈S.filter (fun n => m∣n),divisorKernel m n*logarithmicSchurReference a n := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n _
        by_cases hd : m∣n
        · rw [if_pos hd]
        · simp only [divisorKernel,if_neg hd,zero_mul]
       _ ≤ ∑ n∈S.filter (fun n => m∣n),
          (1/Real.sqrt m)*((Λ (n/m):ℝ)/(((n/m:ℕ):ℝ)*(logConductor (n/m))^a)) :=
        sum_le_sum hterm
       _ = (1/Real.sqrt m)*∑ t∈(S.filter (fun n => m∣n)).image (fun n => n/m),
          (Λ t:ℝ)/((t:ℝ)*(logConductor t)^a) := by
        rw [sum_image hinj, mul_sum]
       _ ≤ (1/Real.sqrt m)*(∑' t : ℕ,(Λ t:ℝ)/((t:ℝ)*(logConductor t)^a)) :=
        mul_le_mul_of_nonneg_left (htail.sum_le_tsum _ (fun t _ => hnn t)) (one_div_pos.mpr hsqrt).le
       _ = _ := by ring

/-- A finite explicit cost for the logarithmically normalized prime kernel. -/
def logarithmicSchurCost (a : ℝ) : ℝ :=
  (∑' t : ℕ,(Λ t:ℝ)/((t:ℝ)*(logConductor t)^a))+1

theorem logarithmicSchurCost_pos (a : ℝ) : 0 < logarithmicSchurCost a := by
  have ht : 0 ≤ ∑' t : ℕ,(Λ t:ℝ)/((t:ℝ)*(logConductor t)^a) :=
    tsum_nonneg (fun t => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
        (lt_of_lt_of_le zero_lt_one (one_le_logConductor t)).le _)))
  dsimp only [logarithmicSchurCost]
  linarith only [ht]

/-- The full prime kernel obeys the sharp logarithmic weighted row estimate. -/
theorem weilPrimeKernel_logReference_row (α : ℝ) (hα : 2 < α)
    (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : ∀ n∈S, 0 < n) :
    (∑ n∈S,ArithmeticEffectivityTheory.weilPrimeKernel m n*
      logarithmicSchurReference (α-1) n) ≤
        logarithmicSchurCost (α-1)*(logConductor m)^α*logarithmicSchurReference (α-1) m := by
  have ha : 1 < α-1 := by linarith only [hα]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hsqrt := Real.sqrt_pos.mpr hmR
  have hL := lt_of_lt_of_le zero_lt_one (one_le_logConductor m)
  have hp := Real.rpow_pos_of_pos hL (α-1)
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hcost : 0 ≤ logarithmicSchurCost (α-1)-1 := by
    change 0 ≤ ((∑' t : ℕ,(Λ t:ℝ)/((t:ℝ)*(logConductor t)^(α-1)))+1)-1
    have ht : 0 ≤ ∑' t : ℕ,(Λ t:ℝ)/((t:ℝ)*(logConductor t)^(α-1)) :=
      tsum_nonneg (fun t => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
          (lt_of_lt_of_le zero_lt_one (one_le_logConductor t)).le _)))
    linarith only [ht]
  have he : (logConductor m)^α=(logConductor m)^(α-1)*logConductor m := by
    calc (logConductor m)^α=(logConductor m)^((α-1)+1) := by congr 1; ring
         _ = _ := by rw [Real.rpow_add hL,Real.rpow_one]
  calc (∑ n∈S,ArithmeticEffectivityTheory.weilPrimeKernel m n*
        logarithmicSchurReference (α-1) n)=
        (∑ n∈S,divisorKernel m n*logarithmicSchurReference (α-1) n)+
        ∑ n∈S,divisorKernel n m*logarithmicSchurReference (α-1) n := by
        simp_rw [weilPrimeKernel_eq_divisorKernel_add,add_mul,sum_add_distrib]
       _ ≤ (logarithmicSchurCost (α-1)-1)/Real.sqrt m+Real.log m/Real.sqrt m := by
        have hu := divisorKernel_logReference_upper_bound (α-1) ha m hm S hS
        have hd := divisorKernel_logReference_lower_bound (α-1) (by linarith only [ha]) m hm S hS
        simpa only [logarithmicSchurCost,add_sub_cancel_right] using add_le_add hu hd
       _ ≤ logarithmicSchurCost (α-1)*logConductor m/Real.sqrt m := by
        rw [←add_div]
        apply div_le_div_of_nonneg_right _ hsqrt.le
        dsimp only [logConductor]
        nlinarith only [mul_nonneg hcost hlog]
       _ = _ := by
        rw [he,logarithmicSchurReference]
        field_simp [hsqrt.ne',hp.ne']

/-- The square-root logarithmic conductor weight used in normalized Hilbert coordinates. -/
def logProbeWeight (α : ℝ) (n : ℕ) : ℝ := (logConductor n)^(α/2)

theorem logProbeWeight_pos (α : ℝ) (n : ℕ) : 0 < logProbeWeight α n :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_logConductor n)) _

theorem logProbeWeight_sq (α : ℝ) (n : ℕ) : (logProbeWeight α n)^2=(logConductor n)^α := by
  rw [logProbeWeight,pow_two,←Real.rpow_add
    (lt_of_lt_of_le zero_lt_one (one_le_logConductor n))]
  congr 1
  ring

/-- The actual prime kernel in logarithmically normalized coordinates. -/
def logarithmicPrimeKernel (α : ℝ) (m n : ℕ) : ℝ :=
  ArithmeticEffectivityTheory.weilPrimeKernel m n/(logProbeWeight α m*logProbeWeight α n)

theorem logarithmicPrimeKernel_comm (α : ℝ) (m n : ℕ) :
    logarithmicPrimeKernel α m n=logarithmicPrimeKernel α n m := by
  rw [logarithmicPrimeKernel,logarithmicPrimeKernel,ArithmeticElectrostatics.weilPrimeKernel_comm,
    mul_comm (logProbeWeight α m)]

theorem logarithmicPrimeKernel_nonneg (α : ℝ) (m n : ℕ) :
    0 ≤ logarithmicPrimeKernel α m n :=
  div_nonneg (ArithmeticElectrostatics.weilPrimeKernel_nonneg m n)
    (mul_pos (logProbeWeight_pos α m) (logProbeWeight_pos α n)).le

/-- Normalization converts the variable logarithmic row estimate to a constant Schur bound. -/
theorem logarithmicPrimeKernel_schur_row (α : ℝ) (hα : 2 < α)
    (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hS : ∀ n∈S, 0 < n) :
    (∑ n∈S,logarithmicPrimeKernel α m n*
      (logProbeWeight α n*logarithmicSchurReference (α-1) n)) ≤
      logarithmicSchurCost (α-1)*(logProbeWeight α m*logarithmicSchurReference (α-1) m) := by
  have hq := logProbeWeight_pos α m
  have he (n : ℕ) : logarithmicPrimeKernel α m n*
      (logProbeWeight α n*logarithmicSchurReference (α-1) n)=
      (ArithmeticEffectivityTheory.weilPrimeKernel m n*logarithmicSchurReference (α-1) n)/
        logProbeWeight α m := by
    rw [logarithmicPrimeKernel]
    field_simp [hq.ne',(logProbeWeight_pos α n).ne']
  simp_rw [he]
  rw [←sum_div]
  calc (∑ n∈S,ArithmeticEffectivityTheory.weilPrimeKernel m n*logarithmicSchurReference (α-1) n)/
        logProbeWeight α m ≤
        (logarithmicSchurCost (α-1)*(logConductor m)^α*logarithmicSchurReference (α-1) m)/
          logProbeWeight α m :=
      div_le_div_of_nonneg_right (weilPrimeKernel_logReference_row α hα m hm S hS) hq.le
       _ = _ := by
        rw [←logProbeWeight_sq α m]
        field_simp [hq.ne']

/-- The entire prime matrix has a uniform finite absolute bound above logarithmic exponent two. -/
theorem weilPrimeKernel_logarithmic_finite_bound (α : ℝ) (hα : 2 < α)
    (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n∈S, 0 < n) :
    (∑ m∈S,∑ n∈S,|x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n|) ≤
      logarithmicSchurCost (α-1)*∑ n∈S,(logConductor n)^α*(x n)^2 := by
  classical
  have hs := weighted_double_sum_le_weightedRowBound
    (ι := ↥S) (b := fun n : ↥S => logProbeWeight α n*x n)
    (w := fun n : ↥S => logProbeWeight α n*logarithmicSchurReference (α-1) n)
    (H := logarithmicSchurCost (α-1))
    (K := fun m n : ↥S => logarithmicPrimeKernel α m n)
    (fun n => mul_pos (logProbeWeight_pos α n) (logarithmicSchurReference_pos (α-1) n (hS n n.property)))
    (fun m n => logarithmicPrimeKernel_comm α m n)
    (fun m n => logarithmicPrimeKernel_nonneg α m n)
    (fun m => by
      rw [Finset.sum_coe_sort S (fun n : ℕ => logarithmicPrimeKernel α m n*
        (logProbeWeight α n*logarithmicSchurReference (α-1) n))]
      exact logarithmicPrimeKernel_schur_row α hα m (hS m m.property) S hS)
  have hterm (m n : ℕ) :
      |logProbeWeight α m*x m| * |logProbeWeight α n*x n| * logarithmicPrimeKernel α m n=
      |x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n| := by
    rw [logarithmicPrimeKernel]
    simp only [abs_mul,abs_of_pos (logProbeWeight_pos α m),abs_of_pos (logProbeWeight_pos α n),
      abs_of_nonneg (ArithmeticElectrostatics.weilPrimeKernel_nonneg m n)]
    field_simp [(logProbeWeight_pos α m).ne',(logProbeWeight_pos α n).ne']
  have hsq (n : ℕ) : (logProbeWeight α n*x n)^2=(logConductor n)^α*(x n)^2 := by
    rw [mul_pow,logProbeWeight_sq]
  simp only [hterm,hsq] at hs
  have hrowSum (m : ℕ) : (∑ n : ↥S,|x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n|)=
      ∑ n∈S,|x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n| :=
    Finset.sum_coe_sort S (fun n : ℕ => |x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n|)
  simp_rw [hrowSum] at hs
  rw [Finset.sum_coe_sort S (fun m : ℕ => ∑ n∈S,|x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n|),
    Finset.sum_coe_sort S (fun n : ℕ => (logConductor n)^α*(x n)^2)] at hs
  exact hs

/-- The absolute torsion matrix separates exactly into prime interactions and tame diagonal mass. -/
theorem spacingLimit_absolute_entry (m n : ℕ) (x y : ℝ) :
    |x*y*HeightHomotopyArithmeticCounts.spacingLimitKernel m n|=
      |x*y*ArithmeticEffectivityTheory.weilPrimeKernel m n|+
        if m=n then ArithmeticIntersectionTheory.tameDifferent n*|x*y| else 0 := by
  by_cases h : m=n
  · subst n
    rw [HeightHomotopyArithmeticCounts.spacingLimitKernel_self,
      ArithmeticElectrostatics.weilPrimeKernel_self,mul_zero,abs_zero,zero_add,if_pos rfl,
      abs_mul,abs_of_nonneg (RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m),mul_comm]
  · simp only [HeightHomotopyArithmeticCounts.spacingLimitKernel,if_neg h,add_zero,mul_neg,abs_neg]

/-- The full torsion form has a uniform absolute bound on all finite logarithmic probes. -/
theorem spacingLimit_logarithmic_finite_bound (α : ℝ) (hα : 2 < α)
    (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n∈S, 0 < n) :
    (∑ m∈S,∑ n∈S,|x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n|) ≤
      (logarithmicSchurCost (α-1)+1)*∑ n∈S,(logConductor n)^α*(x n)^2 := by
  have hdiag (m : ℕ) (hm : m∈S) :
      (∑ n∈S,if m=n then ArithmeticIntersectionTheory.tameDifferent n*|x m*x n| else 0)=
        ArithmeticIntersectionTheory.tameDifferent m*(x m)^2 := by
    rw [sum_eq_single m]
    · rw [if_pos rfl,←pow_two,abs_of_nonneg (sq_nonneg _)]
    · intro n _ hnm
      exact if_neg hnm.symm
    · exact fun h => (h hm).elim
  have hd (n : ℕ) (hn : n∈S) :
      ArithmeticIntersectionTheory.tameDifferent n ≤ (logConductor n)^α := by
    have ht := RenormalizedArithmeticPotentialTheory.tameDifferent_le_log (hS n hn)
    have hp : (logConductor n)^(1:ℝ) ≤ (logConductor n)^α :=
      Real.rpow_le_rpow_of_exponent_le (one_le_logConductor n) (by linarith only [hα])
    rw [Real.rpow_one] at hp
    exact ht.trans ((by dsimp only [logConductor]; linarith only : Real.log n ≤ logConductor n).trans hp)
  simp_rw [spacingLimit_absolute_entry,sum_add_distrib]
  rw [sum_congr rfl hdiag]
  calc (∑ m∈S,∑ n∈S,|x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n|)+
        (∑ n∈S,ArithmeticIntersectionTheory.tameDifferent n*(x n)^2) ≤
        logarithmicSchurCost (α-1)*(∑ n∈S,(logConductor n)^α*(x n)^2)+
          ∑ n∈S,(logConductor n)^α*(x n)^2 :=
      add_le_add (weilPrimeKernel_logarithmic_finite_bound α hα S x hS)
        (sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (hd n hn) (sq_nonneg _)))
       _ = _ := by ring

/-- A quadratic torsion summand is bounded below by the negative absolute prime interaction. -/
theorem spacingLimit_quadratic_entry_lower (x : ℕ → ℝ) (m n : ℕ) :
    -|x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n| ≤
      x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n := by
  by_cases h : m=n
  · subst n
    rw [ArithmeticElectrostatics.weilPrimeKernel_self,mul_zero,abs_zero,neg_zero,
      HeightHomotopyArithmeticCounts.spacingLimitKernel_self,←pow_two]
    exact mul_nonneg (sq_nonneg _) (RenormalizedArithmeticPotentialTheory.tameDifferent_nonneg m)
  · rw [HeightHomotopyArithmeticCounts.spacingLimitKernel,if_neg h,add_zero,mul_neg]
    exact neg_le_neg (le_abs_self _)

/-- An explicit logarithmic diagonal compensates every conductor interaction. -/
theorem spacingLimit_logarithmic_compensation (α : ℝ) (hα : 2 < α)
    (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n∈S, 0 < n) :
    0 ≤ (∑ m∈S,∑ n∈S,x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n)+
      logarithmicSchurCost (α-1)*∑ n∈S,(logConductor n)^α*(x n)^2 := by
  have hb := weilPrimeKernel_logarithmic_finite_bound α hα S x hS
  have hn : -(∑ m∈S,∑ n∈S,|x m*x n*ArithmeticEffectivityTheory.weilPrimeKernel m n|) ≤
      ∑ m∈S,∑ n∈S,x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n := by
    rw [←sum_neg_distrib]
    apply sum_le_sum
    intro m _
    rw [←sum_neg_distrib]
    exact sum_le_sum (fun n _ => spacingLimit_quadratic_entry_lower x m n)
  linarith only [hb,hn]

#print axioms spacingLimit_logarithmic_finite_bound
#print axioms spacingLimit_logarithmic_compensation
#print axioms weilPrimeKernel_logarithmic_finite_bound
#print axioms weilPrimeKernel_logReference_row
#print axioms divisorKernel_logReference_upper_bound
#print axioms divisorKernel_logReference_lower_bound
#print axioms divisorKernel_logReference_multiple
#print axioms divisorKernel_logReference_divisor
/-- Prime labels retain their original integer conductors. -/
def primeStarNatEmbedding : Nat.Primes ↪ ℕ :=
  ⟨fun p : Nat.Primes => (p:ℕ),Subtype.val_injective⟩

theorem primeStarNatEmbedding_apply (p : Nat.Primes) : primeStarNatEmbedding p=(p:ℕ) := rfl

/-- A finite prime star, represented by its actual positive integer conductors. -/
def primeStarNatSupport (S : Finset Nat.Primes) : Finset ℕ :=
  insert 1 (S.map primeStarNatEmbedding)

/-- The same prime-star coefficients, extended by zero to other conductors. -/
def primeStarNatProbe (t : ℝ) (x : Nat.Primes → ℝ) (n : ℕ) : ℝ :=
  if h : n.Prime then x ⟨n,h⟩ else if n=1 then t else 0

theorem primeStarNatProbe_one (t : ℝ) (x : Nat.Primes → ℝ) : primeStarNatProbe t x 1=t := by
  rw [primeStarNatProbe,dif_neg Nat.not_prime_one,if_pos rfl]

theorem primeStarNatProbe_prime (t : ℝ) (x : Nat.Primes → ℝ) (p : Nat.Primes) :
    primeStarNatProbe t x p=x p := by
  rw [primeStarNatProbe,dif_pos p.property]
  rfl

theorem primeStarNatSupport_one_not_map (S : Finset Nat.Primes) :
    1∉S.map primeStarNatEmbedding := by
  rintro h
  obtain ⟨p,_,hp⟩ := mem_map.mp h
  exact p.property.ne_one hp

theorem primeStarNatSupport_pos (S : Finset Nat.Primes) :
    ∀ n∈primeStarNatSupport S, 0 < n := by
  intro n hn
  rcases mem_insert.mp hn with rfl|hn
  · exact Nat.zero_lt_one
  · obtain ⟨p,_,rfl⟩ := mem_map.mp hn
    exact p.property.pos

/-- The integer-conductor pairing retains every root, leaf and mixed star term. -/
theorem primeStarNatSupport_pairing (S : Finset Nat.Primes) (t : ℝ)
    (x : Nat.Primes → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ m∈primeStarNatSupport S,∑ n∈primeStarNatSupport S,
      primeStarNatProbe t x m*primeStarNatProbe t x n*K m n)=
      t^2*K 1 1+(∑ p∈S,∑ q∈S,x p*x q*K p q)+
        ∑ p∈S,t*x p*(K 1 p+K p 1) := by
  have hc (p : Nat.Primes) : x p*t*K p 1=t*x p*K p 1 := by ring
  simp only [primeStarNatSupport,sum_insert (primeStarNatSupport_one_not_map S),sum_map,primeStarNatEmbedding_apply,
    primeStarNatProbe_one,primeStarNatProbe_prime,sum_add_distrib,mul_add,hc]
  ring

/-- The logarithmic conductor mass restricts to the original star coefficients. -/
theorem primeStarNatSupport_log_mass (α : ℝ) (S : Finset Nat.Primes) (t : ℝ)
    (x : Nat.Primes → ℝ) :
    (∑ n∈primeStarNatSupport S,(logConductor n)^α*(primeStarNatProbe t x n)^2)=
      t^2+∑ p∈S,(logConductor p)^α*(x p)^2 := by
  simp only [primeStarNatSupport,sum_insert (primeStarNatSupport_one_not_map S),sum_map,primeStarNatEmbedding_apply,
    primeStarNatProbe_one,primeStarNatProbe_prime]
  simp only [logConductor, Nat.cast_one,Real.log_one,add_zero,Real.one_rpow,one_mul]

/-- The arbitrary-diagonal star is an exact restriction of full logarithmic torsion compensation. -/
theorem primeStarNatSupport_compensation (α C : ℝ) (S : Finset Nat.Primes) (t : ℝ)
    (x : Nat.Primes → ℝ) :
    primeStarEnergy S C
      (fun p => ArithmeticIntersectionTheory.tameDifferent p+C*(logConductor p)^α) t x=
      (∑ m∈primeStarNatSupport S,∑ n∈primeStarNatSupport S,
        primeStarNatProbe t x m*primeStarNatProbe t x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n)+
        C*∑ n∈primeStarNatSupport S,(logConductor n)^α*(primeStarNatProbe t x n)^2 := by
  have he : primeStarEnergy S 0 (fun p => ArithmeticIntersectionTheory.tameDifferent p) t x=
      ∑ m∈primeStarNatSupport S,∑ n∈primeStarNatSupport S,
        primeStarNatProbe t x m*primeStarNatProbe t x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n := by
    rw [primeStarEnergy_eq_torsion,primeStarNatSupport_pairing]
    simp only [add_zero,sub_self,ite_self]
  have hterm (p : Nat.Primes) :
      (ArithmeticIntersectionTheory.tameDifferent p+C*(logConductor p)^α)*(x p)^2-
        2*t*primeStarCoupling p*x p=
      (ArithmeticIntersectionTheory.tameDifferent p*(x p)^2-2*t*primeStarCoupling p*x p)+
        C*((logConductor p)^α*(x p)^2) := by ring
  rw [primeStarNatSupport_log_mass,←he,primeStarEnergy,primeStarEnergy]
  simp_rw [hterm,sum_add_distrib,←mul_sum]
  ring

#print axioms primeStarNatSupport_pairing
#print axioms primeStarNatSupport_compensation

open Filter

/-- At or below exponent two, every constant logarithmic correction has square-log prime growth. -/
theorem primeStar_logConductor_diagonal_bound (α C : ℝ) (hα : α ≤ 2) :
    ∀ᶠ p : Nat.Primes in cofinite,
      ArithmeticIntersectionTheory.tameDifferent p+C*(logConductor p)^α ≤
        (1+4*|C|)*(Real.log p)^2 := by
  have hpco : Tendsto (fun p : Nat.Primes => (p:ℕ)) cofinite atTop := by
    rw [←Nat.cofinite_eq_atTop]
    exact (Subtype.val_injective : Function.Injective (fun p : Nat.Primes => (p:ℕ))).tendsto_cofinite
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hpco)
  filter_upwards [hl.eventually_ge_atTop 1] with p hp1
  simp only [Function.comp_apply] at hp1
  have hlog : 0 ≤ Real.log p := by linarith only [hp1]
  have hL : logConductor p ≤ 2*Real.log p := by
    dsimp only [logConductor]
    linarith only [hp1]
  have hpow : (logConductor p)^α ≤ (logConductor p)^2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (one_le_logConductor p) hα
    norm_num at h ⊢
    exact h
  have hsq : (logConductor p)^2 ≤ 4*(Real.log p)^2 := by
    have h := pow_le_pow_left₀ (by linarith [one_le_logConductor p] : 0 ≤ logConductor p) hL 2
    nlinarith only [h]
  have hlog2 : Real.log p ≤ (Real.log p)^2 := by
    simpa only [mul_one,pow_two] using mul_le_mul_of_nonneg_left hp1 hlog
  have hd := (RenormalizedArithmeticPotentialTheory.tameDifferent_le_log p.property.pos).trans hlog2
  calc ArithmeticIntersectionTheory.tameDifferent p+C*(logConductor p)^α ≤
        (Real.log p)^2+|C| * (logConductor p)^α :=
      add_le_add hd (mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg (by linarith [one_le_logConductor p]) _))
       _ ≤ (Real.log p)^2+|C| * (4*(Real.log p)^2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hpow.trans hsq) (abs_nonneg C))
       _ = _ := by ring

/-- Constant logarithmic diagonal compensation of the full torsion matrix has sharp exponent two. -/
theorem spacingLimit_logarithmic_compensation_iff (α : ℝ) :
    (∃ C : ℝ,∀ (S : Finset ℕ) (x : ℕ → ℝ),(∀ n∈S,0 < n) →
      0 ≤ (∑ m∈S,∑ n∈S,x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n)+
        C*∑ n∈S,(logConductor n)^α*(x n)^2) ↔ 2 < α := by
  constructor
  · rintro ⟨C,hC⟩
    have hstar : ∀S t x,0 ≤ primeStarEnergy S C
        (fun p => ArithmeticIntersectionTheory.tameDifferent p+C*(logConductor p)^α) t x := by
      intro S t x
      rw [primeStarNatSupport_compensation]
      exact hC _ _ (primeStarNatSupport_pos S)
    have hclass := (primeStar_complete_classification C
      (fun p => ArithmeticIntersectionTheory.tameDifferent p+C*(logConductor p)^α)).mp hstar
    by_contra h
    exact not_summable_primeStar_of_log_square_bound _ hclass.1 (1+4*|C|)
      (primeStar_logConductor_diagonal_bound α C (le_of_not_gt h)) hclass.2.1
  · intro hα
    exact ⟨logarithmicSchurCost (α-1),fun S x hS => spacingLimit_logarithmic_compensation α hα S x hS⟩

/-- The full finite absolute-form bound exists exactly above the same logarithmic threshold. -/
theorem spacingLimit_logarithmic_finite_bound_iff (α : ℝ) :
    (∃ C : ℝ,∀ (S : Finset ℕ) (x : ℕ → ℝ),(∀ n∈S,0 < n) →
      (∑ m∈S,∑ n∈S,|x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n|) ≤
        C*∑ n∈S,(logConductor n)^α*(x n)^2) ↔ 2 < α := by
  constructor
  · rintro ⟨C,hC⟩
    apply (spacingLimit_logarithmic_compensation_iff α).mp
    refine ⟨C,fun S x hS => ?_⟩
    have hb := hC S x hS
    have hn : -(∑ m∈S,∑ n∈S,|x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n|) ≤
        ∑ m∈S,∑ n∈S,x m*x n*HeightHomotopyArithmeticCounts.spacingLimitKernel m n := by
      rw [←sum_neg_distrib]
      apply sum_le_sum
      intro m _
      rw [←sum_neg_distrib]
      exact sum_le_sum (fun n _ => neg_abs_le _)
    linarith only [hb,hn]
  · intro hα
    exact ⟨logarithmicSchurCost (α-1)+1,fun S x hS => spacingLimit_logarithmic_finite_bound α hα S x hS⟩

#print axioms spacingLimit_logarithmic_compensation_iff
#print axioms spacingLimit_logarithmic_finite_bound_iff

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
