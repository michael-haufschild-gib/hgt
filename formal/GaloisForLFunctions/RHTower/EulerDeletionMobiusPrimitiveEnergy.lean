import GaloisForLFunctions.RHTower.EulerDeletionMobiusLogGrowth
import GaloisForLFunctions.RHTower.EulerDeletionPrimitiveHardy
import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation
import GaloisForLFunctions.RHTower.DirichletFirstDifference

/-!
# Arithmetic primitive control of the full Möbius current

The primitive is exactly the full modular Möbius approximant. The zero-endpoint
Abel formula and the critical Hardy estimate transfer its complete arithmetic
square energy to the nonlinear chronological current.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionMobiusPrimitive
open DeletionMobiusCurrent DeletionMixedCurrent DeletionReflectedEnergy
open DeletionChronologicalLimit DeletionJointCirculation DeletionPrimitiveHardy

/-- The unweighted primitive of the literal full Möbius deletion stream. -/
def primitive (N K : ℕ) : ℂ := sourcePrefix N 0 K

/-- Its normalization at the critical square-energy weight. -/
def normalizedPrimitive (N n : ℕ) : ℝ := ‖primitive N (n+1)‖/((n : ℝ)+1)

/-- Complete arithmetic primitive energy, including the entire complementary tail. -/
def primitiveEnergy (N : ℕ) : ℝ := ∑' n : ℕ, normalizedPrimitive N n^2

/-- Exact global identification with the corpus's modular Möbius approximant. -/
theorem primitive_eq_modular (N K : ℕ) : primitive N K= -(bdMobiusModularApproximant N K : ℂ) := by
  have heq : primitive N K = ∑ p ∈ Finset.range N, coefficient p*((K%(p+1) : ℕ) : ℂ) := by
    simp only [primitive,sourcePrefix,endpoint,sourcePath,mixedPath,eulerDeletionWeightedJump,
      neg_zero,Complex.cpow_zero,mul_one]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,eulerDeletionDirichletCoefficient_partialSum]
  rw [heq,bdMobiusModularApproximant,Complex.ofReal_neg,neg_neg,Complex.ofReal_sum]
  rw [show Finset.Icc 1 N=Finset.Ico 1 (N+1) by ext k; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [coefficient,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_intCast,
    Complex.ofReal_natCast,Nat.add_comm]
  ring

/-- Every fixed-cutoff primitive is bounded on its full infinite source path. -/
theorem norm_primitive_le (N K : ℕ) : ‖primitive N K‖ ≤ (N : ℝ) := by
  simpa only [primitive_eq_modular,norm_neg,Complex.norm_real,Real.norm_eq_abs] using
    abs_bdMobiusModularApproximant_le N K

private theorem normalized_nonneg (N n : ℕ) : 0 ≤ normalizedPrimitive N n := by
  unfold normalizedPrimitive
  positivity

/-- The complete arithmetic energy is genuinely summable at each fixed cutoff. -/
theorem summable_normalizedPrimitive_sq (N : ℕ) : Summable (fun n => normalizedPrimitive N n^2) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ)+1)^(-(2 : ℝ))) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ)^(-(2 : ℝ))) 1).2
        (Real.summable_nat_rpow.mpr (by norm_num))
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) (f := fun n : ℕ => (N : ℝ)^2*((n : ℝ)+1)^(-(2 : ℝ)))
  · intro n
    have h := norm_primitive_le N (n+1)
    have hn : 0 < (n : ℝ)+1 := by positivity
    rw [normalizedPrimitive,div_pow,Real.rpow_neg hn.le]
    have hp : ‖primitive N (n+1)‖^2 ≤ (N : ℝ)^2 := by nlinarith [norm_nonneg (primitive N (n+1))]
    simpa only [Real.rpow_two,div_eq_mul_inv] using
      div_le_div_of_nonneg_right hp (show (0 : ℝ) ≤ ((n : ℝ)+1)^2 by positivity)
  · exact hs.mul_left _

private theorem path_factor (N n : ℕ) (s : ℂ) :
    sourcePath N s n=sourcePath N 0 n*kernel s n := by
  simp only [sourcePath,mixedPath,eulerDeletionWeightedJump,neg_zero,Complex.cpow_zero,mul_one,
    Finset.sum_mul,kernel]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private def abelTerm (N : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  primitive N (n+1)*(kernel s n-kernel s (n+1))

/-- Finite Abel formula for the actual primitive, with the endpoint retained. -/
theorem sourcePrefix_abel (N k : ℕ) (s : ℂ) :
    sourcePrefix N s (k+1)=primitive N (k+1)*kernel s k+
      ∑ n ∈ Finset.range k, primitive N (n+1)*(kernel s n-kernel s (n+1)) := by
  have heq : sourcePrefix N s (k+1)=∑ n ∈ Finset.range (k+1), kernel s n*sourcePath N 0 n := by
    unfold sourcePrefix endpoint
    apply Finset.sum_congr rfl
    intro n hn
    rw [path_factor,mul_comm]
  have hb := Finset.sum_range_by_parts (kernel s) (sourcePath N 0) (k+1)
  simp only [smul_eq_mul,Nat.add_sub_cancel] at hb
  rw [heq,hb]
  change kernel s k*primitive N (k+1)-
      (∑ n ∈ Finset.range k, (kernel s (n+1)-kernel s n)*primitive N (n+1)) = _
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib]
  simp_rw [mul_comm (kernel s _) (primitive N _)]
  ring

private theorem summable_abelTerm (N : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Summable (abelTerm N s) := by
  apply Summable.of_norm_bounded ((kernel_increment_summable s hs).mul_left (N : ℝ))
  intro n
  rw [abelTerm,norm_mul,norm_sub_rev]
  exact mul_le_mul_of_nonneg_right (norm_primitive_le N (n+1)) (norm_nonneg _)

private theorem abelTerm_tsum_zero (N : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    ∑' n, abelTerm N rho.1 n=0 := by
  have hs := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hboundary : Tendsto (fun k => primitive N (k+1)*kernel rho.1 k) atTop (nhds 0) := by
    have hnorm (k : ℕ) : ‖primitive N (k+1)*kernel rho.1 k‖ ≤ (N : ℝ)*‖kernel rho.1 k‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_primitive_le N (k+1)) (norm_nonneg _)
    apply squeeze_zero_norm hnorm
    simpa only [norm_zero,mul_zero] using ((kernel_tendsto_zero rho.1 hs).norm).const_mul (N : ℝ)
  have hprefix := (sourcePrefix_zero_endpoint N rho).comp (Filter.tendsto_add_atTop_nat 1)
  have hsum : Tendsto (fun k => ∑ n ∈ Finset.range k, abelTerm N rho.1 n) atTop (nhds 0) := by
    have ht := hprefix.sub hboundary
    simp only [sub_self] at ht
    apply ht.congr
    intro k
    change sourcePrefix N rho.1 (k+1)-primitive N (k+1)*kernel rho.1 k = _
    rw [sourcePrefix_abel]
    simp only [abelTerm,add_sub_cancel_left]
  exact tendsto_nhds_unique (summable_abelTerm N hs).hasSum.tendsto_sum_nat hsum

/-- At an actual zero the primitive formula becomes the full ordinary terminal-tail identity. -/
theorem sourcePrefix_abel_tail (N k : ℕ) (rho : RiemannGaussian.NontrivialZetaZero) :
    sourcePrefix N rho.1 (k+1)=primitive N (k+1)*kernel rho.1 k-
      ∑' n : ℕ, if k ≤ n then primitive N (n+1)*(kernel rho.1 n-kernel rho.1 (n+1)) else 0 := by
  have h := (summable_abelTerm N (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)).sum_add_tsum_compl
    (s := Finset.range k)
  rw [tsum_subtype,abelTerm_tsum_zero] at h
  have heq : (∑' n : ℕ, ((↑(Finset.range k) : Set ℕ)ᶜ).indicator (abelTerm N rho.1) n)=
      ∑' n : ℕ, if k ≤ n then abelTerm N rho.1 n else 0 := by
    apply tsum_congr
    intro n
    simp only [Set.indicator_apply,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_range,not_lt]
  rw [heq] at h
  rw [sourcePrefix_abel]
  change primitive N (k+1)*kernel rho.1 k+(∑ n ∈ Finset.range k, abelTerm N rho.1 n)=
    primitive N (k+1)*kernel rho.1 k-(∑' n : ℕ, if k ≤ n then abelTerm N rho.1 n else 0)
  linear_combination h

private theorem kernel_increment_bound {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖kernel s n-kernel s (n+1)‖ ≤ ‖s‖*((n : ℝ)+1)^(-s.re-1) := by
  have hn : 0 < (n : ℝ)+1 := by positivity
  have h := GaloisForLFunctions.RHTower.norm_cpow_neg_sub_le hs hn
    (show (n : ℝ)+1 ≤ ((n : ℝ)+1)+1 by linarith)
  have hb := GaloisForLFunctions.RHTower.rpow_sub_rpow_succ_le hs hn
  have hc : 0 ≤ ‖s‖/s.re := by positivity
  have he := h.trans (mul_le_mul_of_nonneg_left hb hc)
  have hsne := hs.ne'
  have heq : ‖s‖/s.re*(s.re*((n : ℝ)+1)^(-s.re-1))=‖s‖*((n : ℝ)+1)^(-s.re-1) := by field_simp
  rw [heq] at he
  simpa only [kernel,Nat.cast_add,Nat.cast_one] using he

/-- The complete normalized source prefix is controlled by the critical arithmetic Hardy tail. -/
theorem scaled_sourcePrefix_le (N k : ℕ) (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2 < rho.1.re) :
    ((k : ℝ)+1)^(rho.1.re-1)*‖sourcePrefix N rho.1 (k+1)‖ ≤
      normalizedPrimitive N k+‖rho.1‖*tailTransform rho.1.re (normalizedPrimitive N) k := by
  have hpos := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hupper := RiemannGaussian.NontrivialZetaZero.re_lt_one rho
  let w : ℝ := ((k : ℝ)+1)^(rho.1.re-1)
  let F : ℕ → ℂ := fun n => if k ≤ n then abelTerm N rho.1 n else 0
  have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hF : Summable F := by
    apply ((summable_abelTerm N hpos).indicator {n : ℕ | k ≤ n}).congr
    intro n
    simp only [Set.indicator_apply,Set.mem_setOf_eq,F]
  have hrow := summable_tail_row hs hupper (normalized_nonneg N) (summable_normalizedPrimitive_sq N) k
  have hterm (n : ℕ) : w*‖F n‖ ≤ ‖rho.1‖*(tailKernel rho.1.re k n*normalizedPrimitive N n) := by
    by_cases hkn : k ≤ n
    · simp only [F,hkn,if_true,abelTerm,norm_mul,tailKernel]
      have h := mul_le_mul_of_nonneg_left (kernel_increment_bound hpos n)
        (norm_nonneg (primitive N (n+1)))
      have he : w*(‖primitive N (n+1)‖*(‖rho.1‖*((n : ℝ)+1)^(-rho.1.re-1))) =
          ‖rho.1‖*(((k : ℝ)+1)^(rho.1.re-1)*((n : ℝ)+1)^(-rho.1.re)*normalizedPrimitive N n) := by
        rw [Real.rpow_sub (show (0 : ℝ) < (n : ℝ)+1 by positivity),Real.rpow_one,normalizedPrimitive]
        dsimp [w]
        ring
      exact (mul_le_mul_of_nonneg_left h hw).trans_eq he
    · simp [F,tailKernel,hkn]
  have htail : w*‖∑' n, F n‖ ≤ ‖rho.1‖*tailTransform rho.1.re (normalizedPrimitive N) k := by
    have hsum : (∑' n, w*‖F n‖) ≤ ∑' n, ‖rho.1‖*(tailKernel rho.1.re k n*normalizedPrimitive N n) := by
      apply le_of_tendsto_of_tendsto (hF.norm.mul_left w).hasSum.tendsto_sum_nat
        (hrow.mul_left ‖rho.1‖).hasSum.tendsto_sum_nat
      exact Filter.Eventually.of_forall (fun M => Finset.sum_le_sum (fun n _ => hterm n))
    rw [tsum_mul_left,tsum_mul_left] at hsum
    exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hF.norm) hw).trans hsum
  have hdirect : w*‖primitive N (k+1)*kernel rho.1 k‖=normalizedPrimitive N k := by
    dsimp [w]
    rw [norm_mul,norm_kernel,mul_left_comm,← Real.rpow_add
      (show (0 : ℝ) < (k : ℝ)+1 by positivity)]
    have he : rho.1.re-1 + -rho.1.re = -(1 : ℝ) := by ring
    rw [he,Real.rpow_neg_one,normalizedPrimitive]
    ring
  change w*‖sourcePrefix N rho.1 (k+1)‖ ≤ _
  rw [sourcePrefix_abel_tail]
  change w*‖primitive N (k+1)*kernel rho.1 k-(∑' n, F n)‖ ≤ _
  calc _ ≤ w*(‖primitive N (k+1)*kernel rho.1 k‖+‖∑' n, F n‖) :=
         mul_le_mul_of_nonneg_left (norm_sub_le _ _) hw
       _ = normalizedPrimitive N k+w*‖∑' n, F n‖ := by rw [mul_add,hdirect]
       _ ≤ _ := add_le_add le_rfl htail

private theorem weight_increment_bound {s : ℂ} (hs : 1/2 < s.re) (hs' : s.re < 1) (n : ℕ) :
    weight s (n+1)-weight s n ≤ exponent s*((n : ℝ)+1)^(2*s.re-2) := by
  let x : ℝ := (n : ℝ)+1
  have hx : 0 < x := by dsimp [x]; positivity
  have ha : 0 < exponent s := by unfold exponent; linarith
  have ha' : exponent s ≤ 1 := by unfold exponent; linarith
  have hb := rpow_one_add_le_one_add_mul_self
    (s := 1/x) (by have h0 : 0 ≤ 1/x := (one_div_pos.mpr hx).le; linarith) ha.le ha'
  have hprod : x*(1+1/x)=x+1 := by field_simp
  have heq : (x+1)^exponent s=x^exponent s*(1+1/x)^exponent s := by
    rw [← Real.mul_rpow hx.le (by positivity),hprod]
  have h := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hx.le (exponent s))
  have hexp : exponent s-1=2*s.re-2 := by unfold exponent; ring
  have hbound : (x+1)^exponent s-x^exponent s ≤ exponent s*x^(2*s.re-2) := by
    rw [heq]
    calc _ ≤ x^exponent s*(1+exponent s*(1/x))-x^exponent s := sub_le_sub_right h _
         _ = _ := by rw [← hexp,Real.rpow_sub hx,Real.rpow_one]; ring
  simpa only [weight,Nat.cast_add,Nat.cast_one,x,add_assoc] using hbound

/-- Explicit positive transfer constant on the strict right half of the strip. -/
def currentEnergyConstant (s : ℂ) : ℝ :=
  2*exponent s*(1+‖s‖^2*schurConstant s.re^2)

/-- The full chronological current is bounded by the complete literal arithmetic primitive energy. -/
theorem sourceCurrent_le_primitiveEnergy (N : ℕ) (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2 < rho.1.re) :
    (sourceCurrent N rho.1).re ≤ currentEnergyConstant rho.1*primitiveEnergy N := by
  have hs' := RiemannGaussian.NontrivialZetaZero.re_lt_one rho
  have ha : 0 ≤ exponent rho.1 := by unfold exponent; linarith
  have he := tail_energy_summable_le hs hs' (normalized_nonneg N) (summable_normalizedPrimitive_sq N)
  let B := normalizedPrimitive N
  let T := tailTransform rho.1.re B
  have hterm (n : ℕ) : mixedEnergy (Finset.range N) coefficient rho.1 n ≤
      2*exponent rho.1*(B n^2+‖rho.1‖^2*T n^2) := by
    have hp := scaled_sourcePrefix_le N n rho hs
    have hB : 0 ≤ B n := normalized_nonneg N n
    have hT : 0 ≤ T n := by
      apply tsum_nonneg
      intro j
      have hBj := normalized_nonneg N j
      change 0 ≤ tailKernel rho.1.re n j*normalizedPrimitive N j
      unfold tailKernel
      split_ifs <;> positivity
    have hsq : (((n : ℝ)+1)^(rho.1.re-1)*‖sourcePrefix N rho.1 (n+1)‖)^2 ≤
        2*(B n^2+‖rho.1‖^2*T n^2) := by
      have hw : 0 ≤ ((n : ℝ)+1)^(rho.1.re-1)*‖sourcePrefix N rho.1 (n+1)‖ := by positivity
      change _ ≤ B n+‖rho.1‖*T n at hp
      nlinarith [sq_nonneg (B n-‖rho.1‖*T n)]
    have hpowers : ((n : ℝ)+1)^(2*rho.1.re-2)*‖sourcePrefix N rho.1 (n+1)‖^2 =
        (((n : ℝ)+1)^(rho.1.re-1)*‖sourcePrefix N rho.1 (n+1)‖)^2 := by
      rw [mul_pow,pow_two (((n : ℝ)+1)^(rho.1.re-1)),← Real.rpow_add
        (show (0 : ℝ) < (n : ℝ)+1 by positivity)]
      congr 2
      ring
    change (weight rho.1 (n+1)-weight rho.1 n)*‖sourcePrefix N rho.1 (n+1)‖^2 ≤ _
    calc _ ≤ (exponent rho.1*((n : ℝ)+1)^(2*rho.1.re-2))*‖sourcePrefix N rho.1 (n+1)‖^2 :=
           mul_le_mul_of_nonneg_right (weight_increment_bound hs hs' n) (sq_nonneg _)
         _ = exponent rho.1*(((n : ℝ)+1)^(rho.1.re-1)*‖sourcePrefix N rho.1 (n+1)‖)^2 := by
           rw [mul_assoc,hpowers]
         _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsq ha]
  have hsummable := ((summable_normalizedPrimitive_sq N).add (he.1.mul_left (‖rho.1‖^2))).mul_left (2*exponent rho.1)
  have hsum : (∑' n, mixedEnergy (Finset.range N) coefficient rho.1 n) ≤
      ∑' n, 2*exponent rho.1*(B n^2+‖rho.1‖^2*T n^2) := by
    apply le_of_tendsto_of_tendsto
      (hasSum_mixedEnergy (Finset.range N) coefficient rho).summable.hasSum.tendsto_sum_nat
      hsummable.hasSum.tendsto_sum_nat
    exact Filter.Eventually.of_forall (fun M => Finset.sum_le_sum (fun n _ => hterm n))
  have hQ : (sourceCurrent N rho.1).re=∑' n, mixedEnergy (Finset.range N) coefficient rho.1 n := by
    rw [sourceCurrent,quadraticCurrent_eq_energy]
    simp
  rw [hQ]
  calc _ ≤ ∑' n, 2*exponent rho.1*(B n^2+‖rho.1‖^2*T n^2) := hsum
       _ = 2*exponent rho.1*(primitiveEnergy N+‖rho.1‖^2*∑' n, T n^2) := by
         rw [tsum_mul_left,(summable_normalizedPrimitive_sq N).tsum_add (he.1.mul_left (‖rho.1‖^2)),tsum_mul_left]
         rfl
       _ ≤ 2*exponent rho.1*(primitiveEnergy N+‖rho.1‖^2*(schurConstant rho.1.re^2*primitiveEnergy N)) :=
         mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left he.2 (sq_nonneg _))) (by positivity)
       _ = _ := by unfold currentEnergyConstant; ring

/-- The critical arithmetic energy is controlled by the existing full modular carrier norm. -/
theorem primitiveEnergy_le_two_modular_norm_sq (N : ℕ) :
    primitiveEnergy N ≤ 2*‖bdMobiusModularApproximantVec N‖^2 := by
  have hg := hasSum_stepGram (abs_bdMobiusModularApproximant_le N) (abs_bdMobiusModularApproximant_le N)
  have hGram : stepGram (bdMobiusModularApproximant N) (bdMobiusModularApproximant N)=
      ‖bdMobiusModularApproximantVec N‖^2 := by
    have hi : (RCLike.re (inner ℂ (bdMobiusModularApproximantVec N)
        (bdMobiusModularApproximantVec N)) : ℝ)=‖bdMobiusModularApproximantVec N‖^2 :=
      inner_self_eq_norm_sq _
    rw [bdMobiusModularApproximantVec,inner_stepVec] at hi
    exact hi
  have hterm (n : ℕ) : normalizedPrimitive N n^2 ≤
      2*(bdMobiusModularApproximant N (n+1)*bdMobiusModularApproximant N (n+1)/
        (((n : ℝ)+1)*((n : ℝ)+2))) := by
    rw [normalizedPrimitive,primitive_eq_modular,norm_neg,Complex.norm_real,Real.norm_eq_abs,div_pow,sq_abs]
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg (sq_nonneg (bdMobiusModularApproximant N (n+1))) hn]
  calc primitiveEnergy N ≤ ∑' n, 2*(bdMobiusModularApproximant N (n+1)*bdMobiusModularApproximant N (n+1)/
          (((n : ℝ)+1)*((n : ℝ)+2))) :=
         Summable.tsum_le_tsum hterm (summable_normalizedPrimitive_sq N) (hg.summable.mul_left 2)
       _ = 2*stepGram (bdMobiusModularApproximant N) (bdMobiusModularApproximant N) := by
         rw [tsum_mul_left,hg.tsum_eq]
       _ = _ := by rw [hGram]

private theorem energy_nonneg (N : ℕ) : 0 ≤ primitiveEnergy N := tsum_nonneg (fun _ => sq_nonneg _)

/-- Every actual zero has a cutoff-independent transfer constant for the full absolute current. -/
theorem exists_current_bound_by_primitiveEnergy (rho : RiemannGaussian.NontrivialZetaZero) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, |(sourceCurrent N rho.1).re| ≤ C*primitiveEnergy N := by
  have hright (r : RiemannGaussian.NontrivialZetaZero) (hr : 1/2 < r.1.re) :
      ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, |(sourceCurrent N r.1).re| ≤ C*primitiveEnergy N := by
    refine ⟨1+|currentEnergyConstant r.1|,by positivity,?_⟩
    intro N
    have hnonneg := mixed_energy_prefix_le_current (Finset.range N) coefficient r hr.le 0
    simp only [Finset.range_zero,Finset.sum_empty] at hnonneg
    change 0 ≤ (sourceCurrent N r.1).re at hnonneg
    rw [abs_of_nonneg hnonneg]
    exact (sourceCurrent_le_primitiveEnergy N r hr).trans
      (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (currentEnergyConstant r.1)]) (energy_nonneg N))
  rcases lt_trichotomy rho.1.re (1/2 : ℝ) with hleft | heq | hright'
  · let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
    have hr : r.1=DeletionReflectedGram.partner rho.1 := rfl
    have hs : 1/2 < r.1.re := by
      rw [hr]
      simp only [DeletionReflectedGram.partner,Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]
      linarith
    obtain ⟨C,hC,hbound⟩ := hright r hs
    refine ⟨C,hC,fun N => ?_⟩
    simpa only [hr,sourceCurrent_partner,Complex.neg_re,abs_neg] using hbound N
  · refine ⟨1,by norm_num,fun N => ?_⟩
    rw [sourceCurrent,quadraticCurrent_of_re_half _ _ heq]
    simpa using energy_nonneg N
  · exact hright rho hright'

/-- A source-only cofinal logarithmic bound on the full arithmetic energy supplies the EDQ RH ceiling. -/
theorem riemannHypothesis_of_cofinally_log_bounded_primitiveEnergy
    (hsource : ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      primitiveEnergy N ≤ B*Real.log (N : ℝ)^q) : RiemannHypothesis := by
  apply DeletionMobiusLogGrowth.riemannHypothesis_iff_mobius_current_cofinally_log_bounded.mpr
  intro rho
  obtain ⟨C,hC,hcurrent⟩ := exists_current_bound_by_primitiveEnergy rho
  obtain ⟨q,B,hB⟩ := hsource
  refine ⟨q,C*B,fun K => ?_⟩
  obtain ⟨N,hKN,hN⟩ := hB K
  refine ⟨N,hKN,(hcurrent N).trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN hC.le

/-- A sufficient source ceiling in the corpus's existing modular carrier; no norm convergence is required. -/
theorem riemannHypothesis_of_cofinally_log_bounded_modular_norm
    (hsource : ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      ‖bdMobiusModularApproximantVec N‖^2 ≤ B*Real.log (N : ℝ)^q) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinally_log_bounded_primitiveEnergy
  obtain ⟨q,B,hB⟩ := hsource
  refine ⟨q,2*B,fun K => ?_⟩
  obtain ⟨N,hKN,hN⟩ := hB K
  refine ⟨N,hKN,(primitiveEnergy_le_two_modular_norm_sq N).trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 2)

end RHTower.DeletionMobiusPrimitive
end
