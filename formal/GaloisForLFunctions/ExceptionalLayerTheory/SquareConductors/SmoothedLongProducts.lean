import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.AdjacentLongProducts
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SplineSampling
import GaloisForLFunctions.HTGeometry.DiscreteAbelRing

/-!
# The signed square-conductor spline on the PVC long product

Partial summation is applied to the two dilations together on the
original finite prime window. The ordinary density and the endpoint
are controlled there. The six logarithms of the count approximation
then cost six logarithms in the smoothed contact.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Signed finite differences of the spline against a prefix count. -/
def splineCountReading (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (splineHorizon n), f k*(sampledSpline n k-sampledSpline n (k+1))

private theorem contact_abel {n : ℕ} (hn : 0<n) :
    dyadicPrimeContact n = splineCountReading n (fun k => Chebyshev.theta k) := by
  let f (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
  have theta (N : ℕ) : (∑ k ∈ Icc 1 N, f k) = Chebyshev.theta N := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast,show Ioc 0 N = Icc 1 N by ext j; simp only [mem_Ioc,mem_Icc]; omega]
    simp only [f,←sum_filter]
  have hsum : (∑ k ∈ Icc 1 (splineHorizon n), f k*sampledSpline n k) = dyadicPrimeContact n := by
    simp only [f,ite_mul,zero_mul,←sum_filter]
    have hset : (Icc 1 (splineHorizon n)).filter Nat.Prime = ordinaryPrimeLags (splineHorizon n) := by
      ext k
      simp only [ordinaryPrimeLags,mem_filter,mem_Icc]
      exact ⟨fun h => ⟨⟨h.2.two_le,h.1.2⟩,h.2⟩,fun h => ⟨⟨h.2.pos,h.1.2⟩,h.2⟩⟩
    rw [hset,dyadicPrimeContact]
    exact sum_congr rfl fun k hk => by
      have hp := (mem_filter.mp hk).2
      rw [sampledSpline_prime_contact hn hp.pos,vonMangoldt_apply_prime hp,mul_comm]
  rw [←hsum,HTGeometry.sum_mul_eq_partial_mul_diff_ring]
  simp only [theta,sampledSpline_endpoint hn,mul_zero,add_zero,splineCountReading]

private theorem density_abel {n : ℕ} (hn : 0<n) :
    splineCountReading n (fun k => (k:ℝ)) = ∑ k ∈ Icc 1 (splineHorizon n), sampledSpline n k := by
  have h := HTGeometry.sum_mul_eq_partial_mul_diff_ring (fun _ => (1:ℝ)) (sampledSpline n) (splineHorizon n)
  simpa only [splineCountReading,one_mul,sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,
    Nat.add_sub_cancel,sampledSpline_endpoint hn,mul_zero,add_zero] using h.symm

private theorem theta_transfer (f : ℕ → ℝ)
    (herr : ∃ C : ℝ, 0≤C ∧ ∀ k : ℕ, 1≤k →
      |(Chebyshev.theta k-k)-f k| ≤ C*(1+Real.log k)^6*Real.sqrt k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0<n →
      |dyadicPrimeContact n-splineCountReading n f| ≤ C*(1+Real.log (splineHorizon n))^6 := by
  obtain ⟨K,hK,hrow⟩ := herr
  obtain ⟨M,hM,hdensity⟩ := sampledSpline_density
  obtain ⟨B,_,hB,_,hdiff⟩ := sampledSpline_differences
  obtain ⟨A,hA,hbound⟩ := successorSquare_window_bound
  refine ⟨M+K*B*A^3,by positivity,fun {n} hn => ?_⟩
  let L := splineHorizon n
  let E (k : ℕ) := (Chebyshev.theta k-k)-f k
  let H := 1+Real.log L
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hH : 1≤H := le_add_of_nonneg_right (Real.log_natCast_nonneg L)
  have hroot : Real.sqrt L ≤ A*n := by
    have hs := Real.sqrt_le_sqrt (hbound hn)
    rwa [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) hn'.le)] at hs
  have hE (k : ℕ) (hk : k ∈ Icc 1 L) : |E k| ≤ K*H^6*(A*n) := by
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hk
    have hlog := Real.log_le_log (by exact_mod_cast h₁ : (0:ℝ)<k) (by exact_mod_cast h₂ : (k:ℝ)≤L)
    exact (hrow k h₁).trans (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (by have := Real.log_natCast_nonneg k; positivity) (add_le_add_left hlog 1) 6) hK)
      ((Real.sqrt_le_sqrt (by exact_mod_cast h₂)).trans hroot) (Real.sqrt_nonneg _) (by positivity))
  have hread : |splineCountReading n E| ≤ (K*B*A^3)*H^6 := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _k ∈ Icc 1 L, (K*H^6*(A*n))*(B/(n:ℝ)^3) := by
            apply sum_le_sum
            intro k hk
            rw [abs_mul]
            exact mul_le_mul (hE k hk) ((hdiff hn k).1) (abs_nonneg _) (by positivity)
         _ ≤ (A*n)^2*((K*H^6*(A*n))*(B/(n:ℝ)^3)) := by
            rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
            exact mul_le_mul_of_nonneg_right (hbound hn) (by positivity)
         _ = _ := by field_simp; ring
  have he : dyadicPrimeContact n-splineCountReading n f =
      splineCountReading n (fun k => (k:ℝ))+splineCountReading n E := by
    rw [contact_abel hn]
    unfold splineCountReading
    rw [←sum_sub_distrib,←sum_add_distrib]
    exact sum_congr rfl fun k _ => by dsimp [E]; ring
  rw [he,density_abel hn]
  apply (abs_add_le _ _).trans ((add_le_add (hdensity hn) hread).trans _)
  have h₁ : M/n ≤ M := div_le_self hM (by exact_mod_cast hn)
  have h₂ := le_mul_of_one_le_right hM (one_le_pow₀ (n := 6) hH)
  change M/n+_ ≤ (M+K*B*A^3)*H^6
  linarith only [h₁,h₂]

/-- At every positive square conductor the signed long-product reading
with varying logarithmic cutoffs costs only the six-logarithm allowance. -/
theorem dyadicPrimeContact_long_products :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0<n →
      |dyadicPrimeContact n-splineCountReading n longPrimeRow| ≤ C*(1+Real.log (splineHorizon n))^6 :=
  theta_transfer longPrimeRow theta_longPrimeRow_bound

/-- The complete coprime row at fixed unit stencil cutoffs also has a
uniform approximation. Its moving lower product endpoint is retained. -/
theorem dyadicPrimeContact_unit_stencils :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0<n →
      |dyadicPrimeContact n-splineCountReading n (fun k => coprimePrimeRow 1 1 k (productLower 1 k))| ≤
        C*(1+Real.log (splineHorizon n))^6 := by
  apply theta_transfer
  obtain ⟨K,hK,h⟩ := coprime_prime_row_bound
  obtain ⟨B,hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨K+|B|,by positivity,fun k hk => ?_⟩
  let H := 1+Real.log k
  have hH : 1≤H := le_add_of_nonneg_right (Real.log_natCast_nonneg k)
  have h₁ := h (D := 1) (R := 1) hk le_rfl le_rfl hH
    (by simpa only [Nat.cast_one] using hH) (by simpa only [Nat.cast_one] using hH)
    (show Real.log (k:ℝ) ≤ H from le_add_of_nonneg_left zero_le_one)
  have h₅ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hH (by decide : 5≤6)) hK) (Real.sqrt_nonneg (k:ℝ))
  have h₆ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg B)
    (one_le_pow₀ (n := 6) hH)) (Real.sqrt_nonneg (k:ℝ))
  have hpow := (hB k).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.sqrt_nonneg _))
  change |_| ≤ (K+|B|)*H^6*Real.sqrt k
  rw [abs_le] at h₁ ⊢
  constructor <;> linarith only [h₁.1,h₁.2,h₅,h₆,hpow,Chebyshev.theta_le_psi (k:ℝ)]

#print axioms dyadicPrimeContact_unit_stencils
#print axioms dyadicPrimeContact_long_products
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
