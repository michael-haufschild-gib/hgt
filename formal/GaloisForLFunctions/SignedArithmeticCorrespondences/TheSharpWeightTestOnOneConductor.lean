import GaloisForLFunctions.SignedArithmeticCorrespondences.SeparateConductorEnergiesOnInterleavingSupports

/-!
# The sharp weight test on a single lower conductor

Against the conductor-one atom the first cell is doubled on its diagonal
and all later cells are consecutive differences of the opposing divisor.
Alternating integers expose the dual norm of a positive price.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset MeasureTheory

/-- Power conductor weights agree with the usual real powers at every
positive conductor and take value one at zero. -/
def powerConductorWeight (s : ℝ) (k : ℕ) : ℝ := ((max k 1:ℕ):ℝ)^s

/-- All positive cells read by a fixed conductor-one atom. The partner is
the given signed integral divisor on the window, including its terminal
jump to zero. -/
theorem conductor_one_profile {N : ℕ} (hN : 0<N) (v : ℕ → ℤ) :
    ∃ a b : ℕ → ℤ, (∀ i ∈ Icc 1 N, upperDivisor N a i = if i=1 then 1 else 0) ∧
      (∀ i ∈ Icc 1 N, upperDivisor N b i=v i) ∧
      (∀ k ∈ Icc 1 N, ∑ q ∈ Icc k N, twoSidedCoefficient N a b q =
        (v k:ℝ)+(if k=1 then (v 1:ℝ) else 0)) ∧
      ∀ k ∈ Icc 1 N, twoSidedCoefficient N a b k =
        (v k:ℝ)-(if k+1≤N then (v (k+1):ℝ) else 0)+(if k=1 then (v 1:ℝ) else 0) := by
  obtain ⟨a,ha⟩ := exists_upper_endpoints N (fun i => if i=1 then 1 else 0)
  obtain ⟨b,hb⟩ := exists_upper_endpoints N v
  have h₁ : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl,hN⟩
  have ha' {i : ℕ} (hi : 0 < i) : upperDivisor N a i=if i=1 then 1 else 0 := by
    rw [ha i hi]
    by_cases h : i=1
    · subst i; rw [if_pos (show 1≤N from hN)]
    · simp [h]
  have hb₁ : upperDivisor N b 1=v 1 := by rw [hb 1 Nat.zero_lt_one,if_pos (show 1≤N from hN)]
  refine ⟨a,b,fun i hi => ha' (mem_Icc.mp hi).1,
    fun i hi => (hb i (mem_Icc.mp hi).1).trans (if_pos (mem_Icc.mp hi).2),?_⟩
  let T (k : ℕ) := ∑ i ∈ Icc 1 N, ((upperDivisor N a i:ℝ)*upperDivisor N b (k*i) +
    (upperDivisor N b i:ℝ)*upperDivisor N a (k*i))
  have ht {k : ℕ} (hk : 0<k) : T k =
      (if k≤N then (v k:ℝ) else 0)+(if k=1 then (v 1:ℝ) else 0) := by
    dsimp only [T]
    rw [sum_eq_single_of_mem 1 h₁]
    · rw [Nat.mul_one,ha' Nat.zero_lt_one,ha' hk,hb₁,hb k hk]
      by_cases he : k=1 <;> by_cases hc : k≤N <;> simp [he,hc]
    · intro i hi he
      have hip := (mem_Icc.mp hi).1
      have hki := Nat.le_mul_of_pos_left i hk
      simp [ha' hip,ha' (Nat.mul_pos hk hip),he,show k*i≠1 by omega]
  refine ⟨?_,?_⟩
  · intro k hk
    rw [twoSidedCoefficient_tail]
    exact (ht (mem_Icc.mp hk).1).trans (by rw [if_pos (mem_Icc.mp hk).2])
  intro k hk
  have he : twoSidedCoefficient N a b k=T k-T (k+1) :=
    twoSidedCoefficient_difference (mem_Icc.mp hk).2 a b
  rw [he,ht (mem_Icc.mp hk).1,ht (Nat.succ_pos _),if_pos (mem_Icc.mp hk).2,
    if_neg (show k+1≠1 by have := (mem_Icc.mp hk).1; omega),add_zero]
  ring

/-- Alternating nonnegative integer magnitudes realize at least their
entire weighted linear price on one atom. The two coefficient energies
are exactly the prescribed weighted masses. -/
theorem anchored_price_test {N : ℕ} (hN : 0<N) (r w : ℕ → ℝ)
    (hr : 0≤r 1) (hw : ∀ k, 0≤w k) (m : ℕ → ℕ) :
    ∃ a b : ℕ → ℤ,
      (∑ k ∈ Icc 1 N, w k*(m k:ℝ)) ≤ ∑ k ∈ Icc 1 N, w k* |twoSidedCoefficient N a b k| ∧
      conductorNorm N (fun i => r i*upperDivisor N a i)=r 1 ∧
      conductorNorm N (fun i => r i*upperDivisor N b i)=conductorNorm N (fun i => r i*m i) := by
  let v := fun k => (-1:ℤ)^k*(m k:ℤ)
  obtain ⟨a,b,ha,hb,_,hc⟩ := conductor_one_profile hN v
  have h₁ : 1 ∈ Icc 1 N := mem_Icc.mpr ⟨le_rfl,hN⟩
  refine ⟨a,b,sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left ?_ (hw k)),?_,?_⟩
  · rw [hc k hk]
    let n : ℝ := if k+1≤N then (m (k+1):ℝ) else 0
    have hn : 0≤n := by dsimp [n]; split <;> positivity
    have he : (if k+1≤N then (v (k+1):ℝ) else 0) = -((-1:ℝ)^k)*n := by
      by_cases hd : k+1≤N <;> simp [hd,v,n,pow_succ]
    let e : ℝ := if k=1 then (m k:ℝ) else 0
    have h₀ : 0≤e := by dsimp [e]; split <;> positivity
    have hE : (if k=1 then (v 1:ℝ) else 0)=(-1:ℝ)^k*e := by
      by_cases h : k=1 <;> simp [h,e,v]
    have hv : (v k:ℝ) = (-1:ℝ)^k*(m k:ℝ) := by simp [v]
    rw [he,hE,hv,show (-1:ℝ)^k*(m k:ℝ)- -((-1:ℝ)^k)*n+(-1:ℝ)^k*e =
      (-1:ℝ)^k*((m k:ℝ)+n+e) by ring,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _) hn) h₀)]
    linarith only [hn,h₀]
  · rw [conductorNorm,sum_eq_single_of_mem 1 h₁]
    · simp [ha 1 h₁,Real.sqrt_sq hr]
    · intro k hk hne
      simp [ha k hk,hne]
  · apply congrArg Real.sqrt
    refine sum_congr rfl fun k hk => ?_
    simp [hb k hk,v,mul_pow,pow_right_comm (-1:ℝ) k 2]

private theorem finite_dual_test {N : ℕ} (r w : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hw : ∀ k, 0≤w k) {B : ℝ} (hB : 0≤B)
    (hp : ∀ m : ℕ → ℕ, ∑ k ∈ Icc 1 N, w k*(m k:ℝ) ≤ B*conductorNorm N (fun k => r k*m k)) :
    ∑ k ∈ Icc 1 N, (w k/r k)^2 ≤ B^2 := by
  let S := Icc 1 N
  let T := ∑ k ∈ S, (w k/r k)^2
  let W := ∑ k ∈ S, w k
  have hT : 0≤T := sum_nonneg fun _ _ => sq_nonneg _
  by_contra! hbad
  have hlt : B<Real.sqrt T := (Real.lt_sqrt hB).mpr hbad
  have hgap : 0<T-B*Real.sqrt T := by
    nlinarith only [Real.sq_sqrt hT,mul_lt_mul_of_pos_right hlt (hB.trans_lt hlt)]
  obtain ⟨M,hM⟩ := exists_nat_gt (W/(T-B*Real.sqrt T))
  let m := fun k => ⌊(M:ℝ)*(w k/(r k)^2)⌋₊
  have hlow : (M:ℝ)*T ≤ (∑ k ∈ S, w k*m k)+W := by
    dsimp only [T,W]
    rw [mul_sum,← sum_add_distrib]
    refine sum_le_sum fun k _ => ?_
    calc (M:ℝ)*(w k/r k)^2 = w k*((M:ℝ)*(w k/(r k)^2)) := by ring
         _ ≤ w k*((m k:ℝ)+1) := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le (hw k)
         _ = _ := by ring
  have hentry (k : ℕ) : r k*(m k:ℝ) ≤ (M:ℝ)*(w k/r k) := by
    have hm : (m k:ℝ) ≤ (M:ℝ)*(w k/(r k)^2) :=
      Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hw k) (sq_nonneg _)))
    calc _ ≤ r k*((M:ℝ)*(w k/(r k)^2)) := mul_le_mul_of_nonneg_left hm (hr k).le
         _ = _ := by field_simp [(hr k).ne']
  have he : ∑ k ∈ S, (r k*(m k:ℝ))^2 ≤ (M:ℝ)^2*T := by
    dsimp only [T]
    rw [mul_sum]
    refine sum_le_sum fun k _ => ?_
    exact (pow_le_pow_left₀ (mul_nonneg (hr k).le (Nat.cast_nonneg _)) (hentry k) 2).trans_eq
      (mul_pow _ _ _)
  have hnorm : conductorNorm N (fun k => r k*m k) ≤ (M:ℝ)*Real.sqrt T :=
    (Real.sqrt_le_sqrt he).trans_eq (by rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)])
  have hupper := (hp m).trans (mul_le_mul_of_nonneg_left hnorm hB)
  have hstrict := (div_lt_iff₀ hgap).mp hM
  change (∑ k ∈ S, w k*(m k:ℝ)) ≤ _ at hupper
  linarith only [hlow,hupper,hstrict]

/-- A bound on all positive integer test magnitudes characterizes the
square summability of the dual price. Finite supports and integer scaling
suffice to test this real Hilbert norm. -/
theorem dual_price_summable_of_integer_tests (r w : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hw : ∀ k, 0≤w k) {B : ℝ} (hB : 0≤B)
    (h : ∀ N : ℕ, 0<N → ∀ m : ℕ → ℕ, ∑ k ∈ Icc 1 N, w k*(m k:ℝ) ≤
      B*conductorNorm N (fun k => r k*m k)) : Summable (fun k => (w k/r k)^2) := by
  have hfin (N : ℕ) : ∑ k ∈ Icc 1 N, (w k/r k)^2 ≤ B^2 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using sq_nonneg B
    exact finite_dual_test r w hr hw hB (h N hN)
  apply summable_of_sum_range_le (c := B^2+(w 0/r 0)^2) (fun _ => sq_nonneg _)
  intro N
  cases N with
  | zero => simpa using add_nonneg (sq_nonneg B) (sq_nonneg (w 0/r 0))
  | succ n =>
    have hs : (range (n+1)).erase 0=Icc 1 n := by
      ext j
      simp only [mem_erase,mem_range,mem_Icc]
      omega
    rw [← sum_erase_add _ _ (mem_range.mpr (Nat.succ_pos n) : 0∈range (n+1)),hs]
    exact add_le_add (hfin n) le_rfl

/-- A unit-cost joint estimate on all integer pairs forces the dual price
to be square summable. The testing divisors have one lower conductor
and signed integer upper multiplicities of finite support. -/
theorem dual_price_summable_of_uniform_variation (r w : ℕ → ℝ) (hr : ∀ k, 0<r k)
    (hw : ∀ k, 0≤w k) {C : ℝ} (hC : 0≤C) (h : ∀ (N : ℕ) (a b : ℕ → ℤ),
      ∑ k ∈ Icc 1 N, w k* |twoSidedCoefficient N a b k| ≤
        C*conductorNorm N (fun i => r i*upperDivisor N a i)*
          conductorNorm N (fun i => r i*upperDivisor N b i)) :
    Summable (fun k => (w k/r k)^2) := by
  apply dual_price_summable_of_integer_tests r w hr hw (mul_nonneg hC (hr 1).le)
  intro N hN m
  obtain ⟨a,b,hp,ha,hb⟩ := anchored_price_test hN r w (hr 1).le hw m
  have h' := h N a b
  rw [ha,hb] at h'
  exact hp.trans h'

/-- For increasing individual weights with square-summable reciprocal,
this scalar test exactly classifies the prices admitted by the full
two-sided variation and integrated real jet on arbitrary signed divisors. -/
theorem interleaved_weight_test_iff (r w : ℕ → ℝ) (hr : ∀ k, 0<r k) (hm : Monotone r)
    (hw : ∀ k, 0≤w k) (h₁ : Summable (fun k => (1/r k)^2)) :
    (∃ C : ℝ, 0≤C ∧ ∀ (N : ℕ) (a b : ℕ → ℤ),
      (∑ k ∈ Icc 1 N, w k* |twoSidedCoefficient N a b k|) +
        (∫ x in (0:ℝ)..1, |mixedJetSection N a b x|)/2 ≤
        C*conductorNorm N (fun i => r i*upperDivisor N a i)*
          conductorNorm N (fun i => r i*upperDivisor N b i)) ↔
        Summable (fun k => (w k/r k)^2) := by
  constructor
  · rintro ⟨C,hC,h⟩
    apply dual_price_summable_of_uniform_variation r w hr hw hC
    intro N a b
    have hj := intervalIntegral.integral_nonneg_of_forall (μ := volume) zero_le_one
      (fun x => abs_nonneg (mixedJetSection N a b x))
    exact (le_add_of_nonneg_right (div_nonneg hj (by norm_num))).trans (h N a b)
  · intro h₂
    exact ⟨_,add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (sq_nonneg _),interleaved_joint_uniform r w hr hm hw h₁ h₂⟩

/-- A real upper section against the atom at one. The sole doubled
diagonal is at the first quotient and the section ends at the cutoff. -/
def anchoredCell (N : ℕ) (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  (if k=1 then 2 else 1)*v k-(if k+1≤N then v (k+1) else 0)

/-- Total absolute price in each column of the anchored difference matrix. -/
def anchoredColumnPrice (w : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=1 then 2*w j else w j+w (j-1)

private theorem anchoredColumnPrice_nonneg (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) (j : ℕ) :
    0 ≤ anchoredColumnPrice w j := by
  unfold anchoredColumnPrice
  split
  · exact mul_nonneg (by norm_num) (hw j)
  · exact add_nonneg (hw j) (hw (j-1))

/-- Every integral input to the anchored difference matrix is realized
by actual endpoint jumps of the two divisors. -/
theorem anchored_cell_realization {N : ℕ} (hN : 0<N) (v : ℕ → ℤ) :
    ∃ a b : ℕ → ℤ, (∀ i ∈ Icc 1 N, upperDivisor N a i=if i=1 then 1 else 0) ∧
      (∀ i ∈ Icc 1 N, upperDivisor N b i=v i) ∧
      ∀ k ∈ Icc 1 N, twoSidedCoefficient N a b k=anchoredCell N (fun j => (v j:ℝ)) k := by
  obtain ⟨a,b,ha,hb,_,hc⟩ := conductor_one_profile hN v
  refine ⟨a,b,ha,hb,fun k hk => ?_⟩
  rw [hc k hk,anchoredCell]
  by_cases h : k=1
  · subst k; simp; ring
  · simp [h]

private theorem anchored_column_sum (N : ℕ) (w m : ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, w k*((if k=1 then 2 else 1)*m k+(if k+1 ≤ N then m (k+1) else 0))) =
      ∑ j ∈ Icc 1 N, anchoredColumnPrice w j*m j := by
  let S := Icc 1 N
  have row (k : ℕ) : w k*(if k+1 ≤ N then m (k+1) else 0)=
      ∑ j ∈ S, if k+1=j then w k*m j else 0 := by
    by_cases h : k+1 ≤ N <;> simp [S,h]
  have col (j : ℕ) (hj : j∈S) :
      (∑ k ∈ S, if k+1=j then w k*m j else 0) =
      (if j=1 then 0 else w (j-1))*m j := by
    have hp := (mem_Icc.mp hj).1
    have hN := (mem_Icc.mp hj).2
    have he (k : ℕ) : k+1=j ↔ k=j-1 := by omega
    simp only [he,sum_ite_eq']
    by_cases h : j=1
    · subst j; simp [S]
    · have hm : j-1∈S := mem_Icc.mpr ⟨by omega,by omega⟩
      simp [h,hm]
  change (∑ k ∈ S, _) = ∑ j ∈ S, _
  simp only [mul_add,sum_add_distrib,row,sum_comm (s := S) (t := S) (f := fun k j => if k+1=j then w k*m j else 0)]
  rw [sum_congr rfl col,← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  by_cases h : j=1 <;> simp [anchoredColumnPrice,h] <;> ring

/-- Alternating signs attain every column's triangle bound at once. -/
theorem anchored_alternating_variation (N : ℕ) (w m : ℕ → ℝ) (hm : ∀ k, 0 ≤ m k) :
    (∑ k ∈ Icc 1 N, w k*|anchoredCell N (fun j => (-1:ℝ)^j*m j) k|) =
      ∑ j ∈ Icc 1 N, anchoredColumnPrice w j*m j := by
  rw [← anchored_column_sum]
  refine sum_congr rfl fun k _ => congrArg (w k*·) ?_
  let d : ℝ := if k=1 then 2 else 1
  let t := if k+1 ≤ N then m (k+1) else 0
  have hd : 0 ≤ d := by dsimp [d]; split <;> norm_num
  have ht : 0 ≤ t := by dsimp [t]; split <;> first | exact hm _ | exact le_rfl
  have he : anchoredCell N (fun j => (-1:ℝ)^j*m j) k=(-1:ℝ)^k*(d*m k+t) := by
    by_cases h : k+1 ≤ N <;> simp only [anchoredCell,d,t,h,if_true,if_false,pow_succ] <;> ring
  rw [he,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (add_nonneg (mul_nonneg hd (hm k)) ht)]

private theorem anchored_upper (N : ℕ) (r w v : ℕ → ℝ) (hr : ∀ k, 0<r k) (hw : ∀ k, 0 ≤ w k) :
    (∑ k ∈ Icc 1 N, w k*|anchoredCell N v k|) ≤
      conductorNorm N (fun j => anchoredColumnPrice w j/r j)*conductorNorm N (fun j => r j*v j) := by
  let p := anchoredColumnPrice w
  calc _ ≤ ∑ j ∈ Icc 1 N, p j*|v j| := by
         rw [← anchored_column_sum]
         refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (hw k)
         unfold anchoredCell
         apply (abs_sub _ _).trans_eq
         rw [abs_mul]
         have hd : (0:ℝ) ≤ (if k=1 then 2 else 1) := by split <;> norm_num
         rw [abs_of_nonneg hd]
         by_cases ht : k+1 ≤ N <;> simp only [ht,if_true,if_false,abs_zero]
       _ = ∑ j ∈ Icc 1 N, (p j/r j)*(r j*|v j|) := by
         refine sum_congr rfl fun j _ => ?_
         field_simp [(hr j).ne']
       _ ≤ conductorNorm N (fun j => p j/r j)*conductorNorm N (fun j => r j*|v j|) :=
         Real.sum_mul_le_sqrt_mul_sqrt _ _ _
       _ = _ := by simp only [conductorNorm,mul_pow,sq_abs,p]

/-- The sharp real anchored norm is attained by an alternating section
with magnitudes equal to the column prices divided by squared weights. -/
theorem anchored_real_extremizer (N : ℕ) (r w : ℕ → ℝ) (hr : ∀ k, 0<r k) (hw : ∀ k, 0 ≤ w k) :
    let D := conductorNorm N (fun j => anchoredColumnPrice w j/r j)
    ∃ v : ℕ → ℝ, conductorNorm N (fun j => r j*v j)=D ∧
      (∑ k ∈ Icc 1 N, w k*|anchoredCell N v k|)=D^2 := by
  intro D
  let p := anchoredColumnPrice w
  let m := fun j => p j/(r j)^2
  have hp (j : ℕ) : 0 ≤ p j := anchoredColumnPrice_nonneg w hw j
  have hm (j : ℕ) : 0 ≤ m j := div_nonneg (hp j) (sq_nonneg _)
  refine ⟨fun j => (-1:ℝ)^j*m j,?_,?_⟩
  · apply congrArg Real.sqrt
    refine sum_congr rfl fun j _ => ?_
    change (r j*((-1:ℝ)^j*m j))^2=(p j/r j)^2
    simp only [mul_pow,pow_right_comm (-1:ℝ) j 2,neg_one_sq,one_pow,one_mul,m]
    field_simp [(hr j).ne']
  · rw [anchored_alternating_variation N w m hm]
    change _=(Real.sqrt (∑ j ∈ Icc 1 N, (p j/r j)^2))^2
    rw [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    refine sum_congr rfl fun j _ => ?_
    change p j*(p j/(r j)^2)=(p j/r j)^2
    ring

/-- Real and integral upper sections have exactly the same least
anchored variation bound, including cutoffs zero and one. -/
theorem anchored_optimal_constant (N : ℕ) (r w : ℕ → ℝ) (hr : ∀ k, 0<r k) (hw : ∀ k, 0 ≤ w k)
    {C : ℝ} (hC : 0 ≤ C) :
    ((∀ v : ℕ → ℤ, (∑ k ∈ Icc 1 N, w k*|anchoredCell N (fun j => (v j:ℝ)) k|) ≤
      C*conductorNorm N (fun j => r j*v j)) ↔ conductorNorm N (fun j => anchoredColumnPrice w j/r j) ≤ C) ∧
    ((∀ v : ℕ → ℝ, (∑ k ∈ Icc 1 N, w k*|anchoredCell N v k|) ≤
      C*conductorNorm N (fun j => r j*v j)) ↔ conductorNorm N (fun j => anchoredColumnPrice w j/r j) ≤ C) := by
  let p := anchoredColumnPrice w
  have upper (hc : conductorNorm N (fun j => p j/r j) ≤ C) (v : ℕ → ℝ) :=
    (anchored_upper N r w v hr hw).trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))
  have lower (h : ∀ v : ℕ → ℤ, (∑ k ∈ Icc 1 N, w k*|anchoredCell N (fun j => (v j:ℝ)) k|) ≤
      C*conductorNorm N (fun j => r j*v j)) : conductorNorm N (fun j => p j/r j) ≤ C := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hC,finite_dual_test r p hr (fun j => ?_) hC (fun m => ?_)⟩
    · exact anchoredColumnPrice_nonneg w hw j
    · have he := h (fun j => (-1:ℤ)^j*(m j:ℤ))
      simp only [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast] at he
      rw [anchored_alternating_variation N w (fun j => (m j:ℝ)) (fun j => Nat.cast_nonneg _)] at he
      simpa only [p,conductorNorm,mul_pow,pow_right_comm (-1:ℝ) _ 2,neg_one_sq,one_pow,one_mul] using he
  exact ⟨⟨lower,fun h v => upper h (fun j => (v j:ℝ))⟩,
    ⟨fun h => lower (fun v => h (fun j => (v j:ℝ))),upper⟩⟩

#print axioms anchored_cell_realization
#print axioms anchored_alternating_variation
#print axioms anchored_real_extremizer
#print axioms anchored_optimal_constant

#print axioms dual_price_summable_of_integer_tests
#print axioms dual_price_summable_of_uniform_variation
#print axioms interleaved_weight_test_iff
#print axioms conductor_one_profile
#print axioms anchored_price_test
end GaloisForLFunctions.SignedArithmeticCorrespondences
