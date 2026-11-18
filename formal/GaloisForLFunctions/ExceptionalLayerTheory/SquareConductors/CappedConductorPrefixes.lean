import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCompleteUpperProductTail
import GaloisForLFunctions.CountingHolography.Sections.SquareGeneratorPrefix

/-!
# The conductor prefix of the capped coprime product

The lower product cutoff n floor(√n) and the cofactor cap n cost six
logarithms on each signed reading. Multiplying by n² and adding costs
N³ times six logarithms through every terminal conductor.
-/

noncomputable section
open Finset
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def conductorLog (n : ℕ) : ℝ := 1+Real.log (2*(n:ℝ))

/-- Actual capped PVC reading at the square conductor. -/
def cappedConductor (n : ℕ) : ℝ := cappedUpperProductReading (n*n.sqrt) n n

/-- Signed weighted prefix at every terminal conductor. -/
def cappedConductorPrefix (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (n:ℝ)^2*cappedConductor n

theorem conductorLog_one_le (n : ℕ) : 1≤conductorLog n := by
  rcases Nat.eq_zero_or_pos n with rfl|hn
  · simp [conductorLog]
  · have hn' : (1:ℝ)≤n := by exact_mod_cast hn
    exact le_add_of_nonneg_right (Real.log_nonneg (by linarith : (1:ℝ)≤2*n))

theorem conductorLog_mono {n N : ℕ} (hn : 0<n) (hnN : n≤N) : conductorLog n≤conductorLog N :=
  add_le_add (le_refl 1) (Real.log_le_log (by positivity)
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnN) (by norm_num)))

/-- The logarithm of the common prime horizon grows at most linearly in
the conductor logarithm. -/
theorem splineHorizon_conductorLog : ∃ J : ℝ, 0≤J ∧ ∀ {n : ℕ}, 0<n →
    1+Real.log (splineHorizon n)≤J*conductorLog n := by
  obtain ⟨K,hK,hwin⟩ := successorSquare_window_bound
  let J := 3+2*Real.log K
  have hklog := Real.log_nonneg hK
  have hj : 0≤J := by dsimp [J]; positivity
  refine ⟨J,hj,fun {n} hn => ?_⟩
  let L := splineHorizon n
  let H := conductorLog n
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hK' : 0<K := zero_lt_one.trans_le hK
  have hH : 1≤H := conductorLog_one_le _
  have hH₀ := zero_le_one.trans hH
  have hL₀ : (0:ℝ)<L := by
    obtain ⟨_,h₁,h₂⟩ := successorSquareWindowScale_bounds n
    have hp : (0:ℝ)<windowEnd ((2*n+1)^2+1) := (by norm_num : (0:ℝ)<9).trans_le (h₁.trans h₂)
    dsimp [L,splineHorizon]; push_cast; positivity
  have hlogn : Real.log n≤Real.log (2*(n:ℝ)) :=
    Real.log_le_log hn' (by linarith)
  have hb := Real.log_le_log hL₀ (hwin hn)
  rw [Real.log_pow,Real.log_mul hK'.ne' hn'.ne'] at hb
  norm_num1 at hb
  have hh := le_mul_of_one_le_right hklog hH
  have hnH : Real.log n≤H-1 := by simpa only [H,conductorLog,add_sub_cancel_left] using hlogn
  change 1+Real.log (L:ℝ)≤(3+2*Real.log K)*H
  linarith only [hb,hh,hnH,hH]

/-- The two cutoffs are simultaneously within the six-logarithm budget. -/
theorem dyadicPrimeContact_cappedConductor : ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n →
    |dyadicPrimeContact n-cappedConductor n| ≤ C*(conductorLog n)^6 := by
  obtain ⟨A,B,C,hA,hB,hC,h⟩ := dyadicPrimeContact_capped_upper_product_tail
  obtain ⟨J,hj,hwin⟩ := splineHorizon_conductorLog
  refine ⟨A*J^6+2*B+C*J,by positivity,fun {n} hn => ?_⟩
  let L := splineHorizon n
  let U := n*n.sqrt
  let H := conductorLog n
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hH : 1≤H := conductorLog_one_le _
  have hH₀ := zero_le_one.trans hH
  have hL : 1+Real.log L≤J*H := hwin hn
  have hlogn : Real.log n≤Real.log (2*(n:ℝ)) :=
    Real.log_le_log hn' (by linarith)
  have hU : 0<U := Nat.mul_pos hn (Nat.sqrt_pos.mpr hn)
  have hU' : (U:ℝ)≤(n:ℝ)^2 := by
    exact_mod_cast (Nat.mul_le_mul_left n (Nat.sqrt_le_self n)).trans_eq (sq n).symm
  have huLog : 1+Real.log U≤2*H := by
    have hu := Real.log_le_log (by exact_mod_cast hU : (0:ℝ)<U) hU'
    rw [Real.log_pow] at hu
    norm_num1 at hu
    calc 1+Real.log (U:ℝ) ≤ 1+2*Real.log (n:ℝ) := add_le_add (le_refl 1) hu
         _ ≤ 2*H := by dsimp only [H,conductorLog]; linarith only [hlogn]
  have huSq : (U:ℝ)^2≤(n:ℝ)^3 := by
    have hs : (n.sqrt:ℝ)^2≤n := by exact_mod_cast (show n.sqrt^2≤n by simpa only [sq] using Nat.sqrt_le n)
    dsimp only [U]; push_cast
    rw [mul_pow,pow_succ (n:ℝ) 2]
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  have hfirst := pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg L)) hL 6
  rw [mul_pow] at hfirst
  have hmid : B*(1+Real.log U)*(U:ℝ)^2/(n:ℝ)^3≤2*B*H := by
    apply (div_le_iff₀ (pow_pos hn' 3)).mpr
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left huLog hB) huSq (sq_nonneg _)
      (by positivity)
    linarith only [hh]
  have hlast : C*n*(1+Real.log L)/(n+1:ℕ)≤C*J*H := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n))).mpr
    have hh := mul_le_mul_of_nonneg_left hL (mul_nonneg hC hn'.le)
    push_cast
    linarith only [hh,mul_nonneg (mul_nonneg hC hj) hH₀]
  apply (h hn hU n).trans
  have hh := le_self_pow₀ hH (by decide : 6≠0)
  change A*(1+Real.log L)^6+_+_≤(A*J^6+2*B+C*J)*H^6
  linarith only [mul_le_mul_of_nonneg_left hfirst hA,hmid,hlast,
    mul_le_mul_of_nonneg_left hh (show 0≤2*B by positivity),mul_le_mul_of_nonneg_left hh (mul_nonneg hC hj)]

private abbrev generatorAt (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)

private theorem generator_log_sum (N : ℕ) : Real.log (squareGeneratorPrefix N:ℝ) =
    ∑ n ∈ Icc 1 N, Real.log (generatorAt n:ℝ) := by
  rw [show Icc 1 N=Ioc 0 N by ext k; simp only [mem_Icc,mem_Ioc]; omega,squareGeneratorPrefix]
  push_cast
  apply Real.log_prod
  intro n _
  exact (show 0<(generatorAt n:ℝ) by exact_mod_cast
    (show 0<generatorAt n from prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _)).ne'

/-- The arithmetic prefix differs from the logarithm of the actual rational
generator product by at most a cubic times six logarithms, at all endpoints. -/
theorem squareGeneratorPrefix_capped_products :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      |Real.log (squareGeneratorPrefix N:ℝ)-cappedConductorPrefix N| ≤
        C*(N:ℝ)^3*(conductorLog N)^6 := by
  obtain ⟨A,hA,ha⟩ := successorSquare_contact_error
  obtain ⟨B,hB,hb⟩ := dyadicPrimeContact_error
  obtain ⟨C,hC,hc⟩ := dyadicPrimeContact_cappedConductor
  let K := A+B+C
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨K,hK,fun N => ?_⟩
  rw [generator_log_sum,cappedConductorPrefix,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have hnrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      |Real.log (generatorAt n:ℝ)-(n:ℝ)^2*cappedConductor n| ≤ K*(N:ℝ)^2*(conductorLog N)^6 := by
    obtain ⟨hn₁,hnN⟩ := mem_Icc.mp hn
    let P := ordinaryPrimeContact (successorSquareTriple n)
    let D := dyadicPrimeContact n
    have he : Real.log (generatorAt n:ℝ)-(n:ℝ)^2*cappedConductor n =
        (Real.log (generatorAt n:ℝ)-(n:ℝ)^2*P)+
        (n:ℝ)^2*(P-D)+(n:ℝ)^2*(D-cappedConductor n) := by ring
    rw [he]
    apply (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans _)
    simp only [abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]
    have hv := one_le_pow₀ (n := 6) (conductorLog_one_le n)
    have hs := mul_le_mul_of_nonneg_left (hb hn₁) (sq_nonneg (n:ℝ))
    have ht := mul_le_mul_of_nonneg_left (hc hn₁) (sq_nonneg (n:ℝ))
    have hlocal : |Real.log (generatorAt n:ℝ)-(n:ℝ)^2*P|+(n:ℝ)^2*|P-D|+
        (n:ℝ)^2*|D-cappedConductor n| ≤ K*(n:ℝ)^2*(conductorLog n)^6 := by
      dsimp only [P,D,K] at *
      linarith only [ha hn₁ (le_refl n),hs,ht,le_mul_of_one_le_right (mul_nonneg (add_nonneg hA hB) (sq_nonneg (n:ℝ))) hv]
    apply hlocal.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) (Nat.cast_le.mpr hnN) 2) hK)
      (pow_le_pow_left₀ (zero_le_one.trans (conductorLog_one_le n)) (conductorLog_mono hn₁ hnN) 6)
      (by positivity) (by positivity)
  apply (sum_le_sum hnrow).trans_eq
  rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
  ring

/-- The six-logarithm error is negligible at every positive exponent. -/
theorem conductorLog_subpower {b : ℝ} (hb : 0<b) :
    ∃ K : ℝ, 0≤K ∧ ∀ {n : ℕ}, 0<n → (conductorLog n)^6≤K*(n:ℝ)^b := by
  let a := b/6
  have ha : 0<a := div_pos hb (by norm_num)
  refine ⟨(1+1/a)^6*(2:ℝ)^b,by positivity,fun {n} hn => ?_⟩
  let t := 2*(n:ℝ)
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have ht : 1≤t := by dsimp [t]; linarith only [hn']
  have ht₀ := zero_lt_one.trans_le ht
  have hbase : conductorLog n≤(1+1/a)*t^a := by
    have h₁ := Real.one_le_rpow ht ha.le
    have h₂ := Real.log_le_rpow_div ht₀.le ha
    change 1+Real.log t≤_
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  have he : (t^a)^6=t^b := by
    rw [←Real.rpow_natCast _ 6,←Real.rpow_mul ht₀.le]
    congr 1; dsimp [a]; ring
  apply (pow_le_pow_left₀ (zero_le_one.trans (conductorLog_one_le n)) hbase 6).trans_eq
  rw [mul_pow,he,show t^b=(2:ℝ)^b*(n:ℝ)^b from Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)]
  ring

#print axioms dyadicPrimeContact_cappedConductor
#print axioms squareGeneratorPrefix_capped_products
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
