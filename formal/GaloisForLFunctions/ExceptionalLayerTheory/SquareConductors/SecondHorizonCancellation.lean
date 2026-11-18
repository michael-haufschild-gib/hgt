import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.HorizonCancellation
import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel

/-!
# Second horizon cancellation for the unit factorial stencil

After both endpoint terms vanish, a second modular primitive charges
each product q at order q² times the second variation of its test.
The discrete mean shift of each divisor disappears against a test of
zero sum.
-/

noncomputable section
open Finset HTGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem unit_horizon_stencil (N q : ℕ) (z : ℕ → ℝ) {M : ℝ} (hM : 0≤M)
    (hf : ∀ d ∈ Icc 1 (128*(128*1^2+1)), |∑ k ∈ range N, z k*centeredQuotient k q d|≤M) :
    |∑ k ∈ range N, z k*centeredPrimeWeight 1 (k/q)| ≤ 1000*(1+mass 1)*M := by
  let F (d : ℕ) := ∑ k ∈ range N, z k*centeredQuotient k q d
  have h₁ := abs_stencil_le (R := 1) le_rfl F (fun d hd =>
    hf d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (by decide)⟩))
  have h₂ := parityFunctional_bound (R := 1) (f := F) (fun d hd =>
    hf d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (by decide)⟩))
  have h₃ := parityFunctional_bound (R := 128*1^2+1) (f := F) (fun d hd =>
    hf d (mem_Icc.mpr ⟨(show 1≤128*1^2+1 by decide).trans (mem_Icc.mp hd).1,(mem_Icc.mp hd).2⟩))
  have he : (∑ k ∈ range N, z k*centeredPrimeWeight 1 (k/q)) =
      stencil 1 F-momentRatio 1*parityFunctional 1 F+(2/63)*primeWeightMean 1*parityFunctional (128*1^2+1) F := by
    simp only [centeredPrimeWeight_expansion (R := 1) le_rfl,mul_sub,mul_add,sum_add_distrib,sum_sub_distrib,
      mul_left_comm (z _) (momentRatio 1),mul_left_comm (z _) ((2/63)*primeWeightMean 1),
      ←mul_sum,stencil_weighted_sum,commute_functional,F]
  rw [he]
  apply (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) le_rfl).trans _)
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2/63)]
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  have h₂' := mul_le_mul (ratio_bound (R := 1) le_rfl) h₂ (abs_nonneg _) (by positivity)
  have h₃' := mul_le_mul (mul_le_mul_of_nonneg_left (mean_bound (R := 1) le_rfl) (by norm_num : (0:ℝ)≤2/63))
    h₃ (abs_nonneg _) (by positivity)
  linarith only [h₁,h₂',h₃',mul_nonneg hm hM,hM]

/-- Both boundary values, the next mesh value and the discrete mean are
kept explicit. The implied constant is independent of q, N and the test. -/
theorem centeredPrimeWeight_second_horizon :
    ∃ C : ℝ, 0≤C ∧ ∀ {q : ℕ}, 0<q → ∀ (N : ℕ) (z : ℕ → ℝ) {E : ℝ}, 0≤E →
      z 0=0 → z N=0 → z (N+1)=0 → (∑ k ∈ range N, z k)=0 →
      (∀ k ∈ range N, |(z k-z (k+1))-(z (k+1)-z (k+2))|≤E) →
      |∑ k ∈ range N, z k*centeredPrimeWeight 1 (k/q)|≤C*(q:ℝ)^2*N*E := by
  let J : ℕ := 128*(128*1^2+1)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  refine ⟨1000*(1+mass 1)*(J:ℝ)^2/12,by positivity,fun {q} hq N z {E} hE h₀ hN hN₁ hz hΔ => ?_⟩
  let M := ((J:ℝ)*q)^2/12*N*E
  have hM : 0≤M := by dsimp [M]; positivity
  suffices h : ∀ d ∈ Icc 1 J, |∑ k ∈ range N, z k*centeredQuotient k q d|≤M by
    exact (unit_horizon_stencil N q z hM h).trans_eq (by dsimp only [M]; ring)
  intro d hd
  let m := d*q
  have hr (k : ℕ) : centeredQuotient k q d =
      centeredModularRamp m k-((1/2:ℝ)/q)/d := by
    dsimp only [centeredQuotient,centeredModularRamp,m]
    rw [div_div,←Nat.cast_mul,Int.fract_div_natCast_eq_div_natCast_mod]
    have hd₀ : 0<d := (mem_Icc.mp hd).1
    push_cast; field_simp; ring
  simp only [hr,mul_sub,sum_sub_distrib,←sum_mul,hz,zero_mul,sub_zero]
  simp_rw [mul_comm (z _)]
  have hb := centeredModularRamp_second_abel m N z
  simp only [h₀,hN,hN₁,mul_zero,add_zero,sub_zero,sub_self] at hb
  rw [hb]
  apply (abs_sum_le_sum_abs _ _).trans
  have hsize : (m:ℝ)^2≤((J:ℝ)*q)^2 := pow_le_pow_left₀ (Nat.cast_nonneg m)
    (by exact_mod_cast Nat.mul_le_mul_right q (mem_Icc.mp hd).2) 2
  calc _ ≤ ∑ _k ∈ range N, (((J:ℝ)*q)^2/12)*E := by
          apply sum_le_sum; intro k hk
          rw [abs_mul]
          exact mul_le_mul ((abs_centeredModularSecondPrimitive_le m _).trans
            (div_le_div_of_nonneg_right hsize (by norm_num))) (hΔ k hk) (abs_nonneg _) (by positivity)
       _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul,M]; ring

#print axioms centeredPrimeWeight_second_horizon
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
