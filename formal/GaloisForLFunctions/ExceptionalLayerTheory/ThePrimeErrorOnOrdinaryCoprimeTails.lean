import GaloisForLFunctions.ExceptionalLayerTheory.AveragingTheCoprimeComplementaryTail
import GaloisForLFunctions.ExceptionalLayerTheory.PrimeErrorOnEveryComplementaryTail

/-!
# The prime error on ordinary coprime tails

Transposition makes the complementary cutoff the same in every first-factor
slice. The short factors are bounded by the integer reciprocal estimate.
The long proper powers retain a square-root denominator.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem complete_tail_by_first (D R X a : ℕ) :
    completeComplementTail D R X a =
      ∑ u ∈ Icc 1 X, vonMangoldt u*factorSlice D R X (a*u) u := by
  let f (u v : ℕ) := vonMangoldt u*(innerJump D v*centeredPrimeWeight R (X/u/v))
  have interval (T : ℕ) : Ioc a T=Icc (a+1) T := by ext v; simp only [mem_Icc,mem_Ioc]; omega
  have swapped : completeComplementTail D R X a =
      ∑ u ∈ Icc 1 (X/(a+1)), ∑ v ∈ Icc (a+1) (X/u), f u v := by
    unfold completeComplementTail
    rw [interval]
    apply Eq.trans _ (sum_hyperbola_tail_swap_real X (a+1) f (Nat.succ_pos a))
    apply sum_congr rfl; intro v _
    rw [mul_sum]; apply sum_congr rfl; intro u _
    simp only [f,Nat.div_div_eq_div_mul,Nat.mul_comm v u]; ring
  rw [swapped]
  calc _ = ∑ u ∈ Icc 1 X, ∑ v ∈ Icc (a+1) (X/u), f u v := by
            apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self X (a+1)))
            intro u hu hn
            have hu₁ := (mem_Icc.mp hu).1
            have ht : X/(a+1)<u := by
              by_contra! h; exact hn (mem_Icc.mpr ⟨hu₁,h⟩)
            have hlt : X/u<a+1 := (Nat.div_lt_iff_lt_mul hu₁).mpr (by
              simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (Nat.succ_pos a)).mp ht)
            rw [Icc_eq_empty hlt.not_ge,sum_empty]
       _ = _ := by
            apply sum_congr rfl; intro u hu
            rw [factorSlice,Nat.mul_div_cancel _ (mem_Icc.mp hu).1,interval,mul_sum]

private theorem complete_tail_sub_ordinary :
    ∃ K : ℝ, 0≤K ∧ ∀ {D R X : ℕ}, 1≤D → 1≤R → 1≤X → ∀ F a : ℕ,
    |completeComplementTail D R X a-ordinaryComplementTail D R X F a| ≤
      K*(((D+1 : ℕ) : ℝ)*R*Real.sqrt X+
        F*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(X : ℝ)^(49/100 : ℝ))*(1+Real.log X) := by
  obtain ⟨B,hB,hslice⟩ := factor_slice_bounds
  obtain ⟨C,hC,hshort⟩ := complementary_slice_power_bound
  let E := Real.log 4+4
  have hE : 0≤E := add_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ)≤4)) (by norm_num)
  refine ⟨6*E*B+7*C,by positivity,?_⟩
  intro D R X hD hR hX F a
  let I := Icc 1 X
  let q (u : ℕ) := vonMangoldt u*factorSlice D R X (a*u) u
  let J := 1+Real.log X
  let A := C*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*J*(X : ℝ)^(49/100 : ℝ)
  let T := B*((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  have hlog := Real.log_natCast_nonneg X
  have hJ : 0≤J := by dsimp [J]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hT : 0≤T := by dsimp [T]; positivity
  have lo : I.filter (fun u => u≤F)=Icc 1 (min X F) := by
    ext u; simp only [I,mem_filter,mem_Icc,le_min_iff]; tauto
  have hi : I.filter (fun u => ¬u≤F)=Ioc F X := by
    ext u; simp only [I,mem_filter,mem_Icc,mem_Ioc,not_le]; omega
  have split := sum_filter_add_sum_filter_not I (fun u => u≤F) q
  rw [lo,hi] at split
  let S := Ioc F X
  have primes := sum_filter_add_sum_filter_not S Nat.Prime q
  have eq : completeComplementTail D R X a-ordinaryComplementTail D R X F a =
      (∑ u ∈ Icc 1 (min X F), q u)+(∑ u ∈ S with ¬u.Prime, q u) := by
    rw [complete_tail_by_first]
    change (∑ u ∈ I, q u)-(∑ u ∈ S with u.Prime, q u)=_
    rw [←split]; change _+(∑ u ∈ S, q u)-_=_
    rw [←primes]; ring
  have small : |∑ u ∈ Icc 1 (min X F), q u|≤7*F*A := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ u ∈ Icc 1 (min X F), vonMangoldt u*A := by
              apply sum_le_sum; intro u hu
              obtain ⟨hu₁,hux⟩ := mem_Icc.mp hu
              have ht := (Nat.one_le_div_iff hu₁).mpr (hux.trans (min_le_left ..))
              have hz : ((X/u : ℕ) : ℝ)≤X := by exact_mod_cast Nat.div_le_self X u
              have hl := Real.log_le_log (by exact_mod_cast ht : (0 : ℝ)<(X/u : ℕ)) hz
              have hp := Real.rpow_le_rpow (Nat.cast_nonneg (X/u)) hz (by norm_num : (0 : ℝ)≤49/100)
              dsimp only [q]; rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
              apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
              rw [factorSlice,Nat.mul_div_cancel _ hu₁]
              exact (hshort (D := D) hR ht a).trans (mul_le_mul
                (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hl) (by positivity))
                hp (by positivity) (by positivity))
         _ ≤ _ := by
              rw [←sum_mul]
              exact mul_le_mul_of_nonneg_right ((chebyshevPsi_le_seven (min X F)).trans
                (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right X F) (by norm_num))) hA
  have powers : |∑ u ∈ S with ¬u.Prime, q u|≤T*(6*E*J) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ u ∈ S with ¬u.Prime, T*(primePowerPart u/Real.sqrt u) := by
              apply sum_le_sum; intro u hu
              dsimp only [q]; rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
              have hp := (hslice hD hR X (a*u)).1 u
              apply (mul_le_mul_of_nonneg_left hp vonMangoldt_nonneg).trans_eq
              simp only [primePowerPart,if_neg (mem_filter.mp hu).2,T]; ring
         _ ≤ T*(∑ u ∈ Icc 1 X, primePowerPart u/Real.sqrt u) := by
              rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ hT
              apply sum_le_sum_of_subset_of_nonneg
              · intro u hu
                have hz := mem_Ioc.mp (mem_filter.mp hu).1
                exact mem_Icc.mpr ⟨(Nat.zero_le F).trans_lt hz.1,hz.2⟩
              · intro u _ _; apply div_nonneg _ (Real.sqrt_nonneg _)
                unfold primePowerPart; split <;> first | exact le_rfl | exact vonMangoldt_nonneg
         _ ≤ _ := by
              apply mul_le_mul_of_nonneg_left ((proper_power_half_weight X).trans _) hT
              change 3*E*(2+Real.log X)≤6*E*(1+Real.log X)
              linarith only [mul_nonneg hE hlog]
  rw [eq]
  apply (abs_add_le _ _).trans ((add_le_add small powers).trans _)
  let L := ((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  let H := (F : ℝ)*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(X : ℝ)^(49/100 : ℝ)
  have h₁ : 0≤6*E*B*(H*J) := by dsimp [H]; positivity
  have h₂ : 0≤7*C*(L*J) := by dsimp [L]; positivity
  change 7*F*A+T*(6*E*J)≤(6*E*B+7*C)*(L+H)*J
  dsimp only [L,H,A,T] at h₁ h₂ ⊢
  linarith only [h₁,h₂]

/-- At every admissible complementary cutoff, the discarded ordinary
coprime row is the signed prime-error dilation up to the short first
factors, the proper powers and the explicit factorial approximation. -/
theorem ordinary_coprime_tail_sub_primeErrorTail :
    ∃ K : ℝ, 0≤K ∧ ∀ {D R X F Y a : ℕ}, 1≤D → 1≤R → 1≤X → 2*(D+1)≤F → Y/(F+1)≤a →
    |ordinaryFactorTail F X (coprimeSlice D R X Y)-cappedComplementaryRow D R X F Y a-primeErrorTail D X a| ≤
      K*(((D+1 : ℕ) : ℝ)*R*Real.sqrt X+
        F*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(X : ℝ)^(49/100 : ℝ))*(1+Real.log X)+
      4*(1+mass (D+1))*(420*(1+mass R)*(3+Real.log (128*(128*R^2+1) : ℕ)+2*Real.log X))*Real.sqrt X := by
  obtain ⟨C,hC,hcap⟩ := complement_tail_coprime_comparison
  obtain ⟨B,hB,hfull⟩ := complete_tail_sub_ordinary
  refine ⟨C+B,by positivity,?_⟩
  intro D R X F Y a hD hR hX hF hY
  let L := ((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  let H := (F : ℝ)*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(X : ℝ)^(49/100 : ℝ)
  let J := 1+Real.log X
  let m := completeComplementTail D R X a
  let u := ordinaryComplementTail D R X F a
  let d := ordinaryFactorTail F X (coprimeSlice D R X Y)-cappedComplementaryRow D R X F Y a
  let e := primeErrorTail D X a
  have ht : |u-m|≤B*(L+H)*J := by rw [abs_sub_comm]; exact hfull hD hR hX F a
  have hg : |d-u|≤C*L*J := by
    exact (hcap hD hR hX hF hY).trans_eq (by dsimp only [L,J]; ring)
  have h₀ : 0≤C*H*J := by dsimp [H,J]; have := Real.log_natCast_nonneg X; positivity
  change |d-e|≤(C+B)*(L+H)*J+_
  rw [show d-e=((d-u)+(u-m))+(m-e) by ring]
  apply (abs_add_le _ _).trans (add_le_add _ (completeComplementTail_sub_primeErrorTail hR D X a))
  exact (abs_add_le _ _).trans ((add_le_add hg ht).trans (by linarith only [h₀]))

#print axioms ordinary_coprime_tail_sub_primeErrorTail
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
