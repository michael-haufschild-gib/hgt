import GaloisForLFunctions.RHTower.MobiusDivisorPrimeCorrelationPhysical
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct

/-!
# Exact changing-core law for the physical dilation mean

The actual prime merger holds on the entire continuous ray. Expanding
its absolutely integrable pairing retains both cross scales and the
doubly copied term. The resulting renewal formula compares one growing
prime core with every next dilation through the original ratio profile.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

/-- Prime processing subtracts the literal dilated head on the entire real ray. -/
theorem mobiusDivisorContinuousHead_insert (P : Finset ℕ)
    (hP : ∀q∈P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p∉P) (x : ℝ) :
    mobiusDivisorContinuousHead (insert p P) x =
      mobiusDivisorContinuousHead P x-Real.sqrt p*mobiusDivisorContinuousHead P (x/p) := by
  have hi : ∀q∈insert p P,q.Prime := by
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hP q hq
  simp only [mobiusDivisorContinuousHead]
  rw [Sieve.sum_divisors_prod_primes_eq hi,
    Finset.sum_powerset_insert hpP,
    Sieve.sum_divisors_prod_primes_eq hP,
    Sieve.sum_divisors_prod_primes_eq hP,mul_sum]
  rw [sub_eq_add_neg,← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro T hT
  have hpT : p∉T := fun h => hpP (mem_powerset.mp hT h)
  have hcop : p.Coprime (∏q∈T,q) := by
    apply Nat.Coprime.prod_right
    intro q hq
    exact (hp.coprime_iff_not_dvd).mpr (fun hd =>
      hpT ((Nat.prime_dvd_prime_iff_eq hp (hP q (mem_powerset.mp hT hq))).mp hd ▸ hq))
  rw [prod_insert hpT,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp,Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg p),div_div]
  push_cast
  ring

private lemma kernel_zero_integrable (P : Finset ℕ) {Y : ℝ} (hY : 0<Y) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (Y*x)*
      mobiusDivisorContinuousHead P x/x^3) (Ioi 0) := by
  apply (integrable_mobiusDivisorDilationMean_kernel P hY).of_forall_sdiff_eq_zero measurableSet_Ioi
  intro x hx
  simp [mobiusDivisorContinuousHead_eq_zero P (le_of_not_gt hx.2)]

private lemma kernel_zero_integral (P : Finset ℕ) (Y : ℝ) :
    (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (Y*x)*
      mobiusDivisorContinuousHead P x/x^3)=mobiusDivisorDilationMean P Y := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  intro x hx
  simp [mobiusDivisorContinuousHead_eq_zero P (le_of_not_gt hx.2)]

private lemma pair_scale (P : Finset ℕ) {A B : ℝ} (hB : 0<B) (x : ℝ) :
    mobiusDivisorContinuousHead P (A*x)*mobiusDivisorContinuousHead P (B*x)/x^3 =
      B^3*(mobiusDivisorContinuousHead P ((A/B)*(B*x))*
        mobiusDivisorContinuousHead P (B*x)/(B*x)^3) := by
  rw [show A/B*(B*x)=A*x by field_simp]
  by_cases hx : x=0
  · simp [hx]
  · field_simp

private lemma pair_integrable (P : Finset ℕ) {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3) (Ioi 0) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff _ 0 hB).mpr
    (by simpa using kernel_zero_integrable P (div_pos hA hB))
  apply IntegrableOn.congr_fun (hi.const_mul (B^3)) _ measurableSet_Ioi
  intro x _
  exact (pair_scale P hB x).symm

private lemma pair_integral (P : Finset ℕ) {A B : ℝ} (hB : 0<B) :
    (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3)=B^2*mobiusDivisorDilationMean P (A/B) := by
  simp_rw [pair_scale P hB]
  rw [integral_const_mul,integral_comp_mul_left_Ioi
    (fun u => mobiusDivisorContinuousHead P ((A/B)*u)*mobiusDivisorContinuousHead P u/u^3) 0 hB,mul_zero,
    smul_eq_mul,kernel_zero_integral]
  field_simp

/-- Exact two-scale renewal retains both cross terms and the doubly copied head. -/
theorem mobiusDivisorDilationMean_insert (P : Finset ℕ)
    (hP : ∀q∈P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p∉P)
    {Y : ℝ} (hY : 0<Y) :
    mobiusDivisorDilationMean (insert p P) Y =
      (1+1/(p:ℝ))*mobiusDivisorDilationMean P Y-
      Real.sqrt p/(p:ℝ)^2*mobiusDivisorDilationMean P ((p:ℝ)*Y)-
      Real.sqrt p*mobiusDivisorDilationMean P (Y/p) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  let K : ℝ→ℝ→ℝ→ℝ := fun A B x =>
    mobiusDivisorContinuousHead P (A*x)*mobiusDivisorContinuousHead P (B*x)/x^3
  have hi₀ : IntegrableOn (K Y 1) (Ioi 0) := pair_integrable P hY zero_lt_one
  have hi₁ : IntegrableOn (K Y (p:ℝ)⁻¹) (Ioi 0) := pair_integrable P hY (inv_pos.mpr hpR)
  have hi₂ : IntegrableOn (K (Y/p) 1) (Ioi 0) := pair_integrable P (div_pos hY hpR) zero_lt_one
  have hi₃ : IntegrableOn (K (Y/p) (p:ℝ)⁻¹) (Ioi 0) := pair_integrable P (div_pos hY hpR) (inv_pos.mpr hpR)
  have he (x : ℝ) :
      mobiusDivisorContinuousHead (insert p P) (Y*x)*
        mobiusDivisorContinuousHead (insert p P) x/x^3 =
      K Y 1 x-Real.sqrt p*K Y (p:ℝ)⁻¹ x-
        Real.sqrt p*K (Y/p) 1 x+(p:ℝ)*K (Y/p) (p:ℝ)⁻¹ x := by
    simp only [mobiusDivisorContinuousHead_insert P hP hp hpP,K,one_mul]
    rw [show Y*x/(p:ℝ)=(Y/p)*x by ring,show x/(p:ℝ)=(p:ℝ)⁻¹*x by ring]
    have hs := Real.sq_sqrt hpR.le
    linear_combination (mobiusDivisorContinuousHead P (Y/p*x)*
      mobiusDivisorContinuousHead P ((p:ℝ)⁻¹*x)/x^3)*hs
  rw [← kernel_zero_integral]
  simp_rw [he]
  change (∫x in Ioi (0:ℝ),
    ((K Y 1-(fun x => Real.sqrt p*K Y (p:ℝ)⁻¹ x))-
      (fun x => Real.sqrt p*K (Y/p) 1 x)) x+
      (fun x => (p:ℝ)*K (Y/p) (p:ℝ)⁻¹ x) x)=_
  rw [integral_add ((hi₀.sub (hi₁.const_mul _)).sub (hi₂.const_mul _)) (hi₃.const_mul _)]
  simp only [Pi.sub_apply]
  have hsub := integral_sub (hi₀.sub (hi₁.const_mul (Real.sqrt p))) (hi₂.const_mul (Real.sqrt p))
  simp only [Pi.sub_apply] at hsub
  rw [hsub,integral_sub hi₀ (hi₁.const_mul _)]
  simp only [integral_const_mul,K]
  rw [pair_integral P zero_lt_one,pair_integral P (inv_pos.mpr hpR),
    pair_integral P zero_lt_one,pair_integral P (inv_pos.mpr hpR)]
  rw [show Y/(p:ℝ)⁻¹=(p:ℝ)*Y by field_simp,
    show (Y/p)/(p:ℝ)⁻¹=Y by field_simp]
  simp only [div_one,one_pow,one_mul]
  field_simp
  ring

end RHTower
