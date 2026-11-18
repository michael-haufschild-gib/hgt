import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CappedConductorPrefixes
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeSignalAtASquareComplement

/-!
# Feedback across conductor prefixes

Remove one prime-square complementary fibre only at multiples of its
square root. The resulting complete-row prefix and its divided copy
have positive feedback after two substitutions.
-/

noncomputable section
open Finset
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def weightedReadingPrefix (f : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, (n:ℝ)^2*f n
def primeContactPrefix := weightedReadingPrefix dyadicPrimeContact

private def completeReading (n : ℕ) := splineCountReading n (fun k => coprimePrimeRow 1 1 k (productLower 1 k))
private def fibreReading (ℓ n : ℕ) := splineCountReading n (squareComplementRow ℓ)

/-- All complete rows, with exactly the specified fibre subtracted at
conductors divisible by ℓ. -/
def deletedSquareFibrePrefix (ℓ N : ℕ) :=
  weightedReadingPrefix completeReading N-
    ∑ m ∈ Icc 1 (N/ℓ), ((ℓ:ℝ)*m)^2*fibreReading ℓ (ℓ*m)

private theorem prefix_allowance {M N : ℕ} (hMN : M≤N) (f : ℕ → ℝ) {K : ℝ} (hK : 0≤K)
    (hf : ∀ n ∈ Icc 1 M, |f n|≤K*(conductorLog N)^6) :
    |weightedReadingPrefix f M|≤K*(N:ℝ)^3*(conductorLog N)^6 := by
  apply (abs_sum_le_sum_abs _ _).trans
  have hrow (n : ℕ) (hn : n ∈ Icc 1 M) :
      |(n:ℝ)^2*f n|≤(N:ℝ)^2*(K*(conductorLog N)^6) := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg n)
      (Nat.cast_le.mpr ((mem_Icc.mp hn).2.trans hMN)) 2) (hf n hn) (abs_nonneg _) (sq_nonneg _)
  apply (sum_le_sum hrow).trans
  rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hMN : (M:ℝ)≤N) (by positivity)).trans_eq (by ring)

/-- The first feedback term is negative, including at the last incomplete
conductor block. -/
theorem square_fibre_prefix_feedback {ℓ : ℕ} (hp : ℓ.Prime) (h₄ : 4<ℓ) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      |primeContactPrefix N-(deletedSquareFibrePrefix ℓ N-ℓ*primeContactPrefix (N/ℓ))| ≤
        C*(N:ℝ)^3*(conductorLog N)^6 := by
  obtain ⟨A,hA,ha⟩ := dyadicPrimeContact_unit_stencils
  obtain ⟨B,hB,hb⟩ := squareComplementRow_dyadicPrimeContact hp h₄
  obtain ⟨J,hJ,hj⟩ := splineHorizon_conductorLog
  refine ⟨A*J^6+ℓ*(2*B*J^6),by positivity,fun N => ?_⟩
  let T := (N:ℝ)^3*(conductorLog N)^6
  have hs {n : ℕ} (hn : 0<n) (hle : n≤N) :
      (1+Real.log (splineHorizon n))^6≤J^6*(conductorLog N)^6 := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (add_nonneg zero_le_one (Real.log_natCast_nonneg _))
      ((hj hn).trans (mul_le_mul_of_nonneg_left (conductorLog_mono hn hle) hJ)) 6
  let E (n : ℕ) := dyadicPrimeContact n-completeReading n
  have hE := prefix_allowance (N := N) le_rfl E (K := A*J^6) (by positivity) fun n hn => by
    obtain ⟨hn₁,hnN⟩ := mem_Icc.mp hn
    exact (ha hn₁).trans ((mul_le_mul_of_nonneg_left (hs hn₁ hnN) hA).trans_eq (by ring))
  let G (m : ℕ) := (ℓ:ℝ)*fibreReading ℓ (ℓ*m)+dyadicPrimeContact m
  have hG := prefix_allowance (Nat.div_le_self N ℓ) G (K := 2*B*J^6) (by positivity) fun m hm => by
    obtain ⟨hm₀,hmq⟩ := mem_Icc.mp hm
    have hmn : ℓ*m≤N := by simpa only [Nat.mul_comm m ℓ] using (Nat.le_div_iff_mul_le hp.pos).mp hmq
    have h₁ := hs (Nat.mul_pos hp.pos hm₀) hmn
    have h₂ := hs hm₀ (hmq.trans (Nat.div_le_self ..))
    exact (hb hm₀).trans ((mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hB).trans_eq (by ring))
  have he : primeContactPrefix N-(deletedSquareFibrePrefix ℓ N-ℓ*primeContactPrefix (N/ℓ)) =
      weightedReadingPrefix E N+ℓ*weightedReadingPrefix G (N/ℓ) := by
    simp only [primeContactPrefix,deletedSquareFibrePrefix,weightedReadingPrefix,E,G,mul_sub,mul_add,
      sum_sub_distrib,sum_add_distrib,mul_sum]
    have ht : (∑ m ∈ Icc 1 (N/ℓ), ((ℓ:ℝ)*m)^2*fibreReading ℓ (ℓ*m)) =
        ∑ m ∈ Icc 1 (N/ℓ), (ℓ:ℝ)*((m:ℝ)^2*(ℓ*fibreReading ℓ (ℓ*m))) :=
      sum_congr rfl fun _ _ => by ring
    rw [ht]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg ℓ)]
  exact (add_le_add hE (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg ℓ))).trans_eq (by ring)

/-- After two substitutions only the signed difference of the deleted
prefixes and positive feedback at N/ℓ² remain. -/
theorem square_fibre_two_step_feedback {ℓ : ℕ} (hp : ℓ.Prime) (h₄ : 4<ℓ) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      |primeContactPrefix N-(deletedSquareFibrePrefix ℓ N-ℓ*deletedSquareFibrePrefix ℓ (N/ℓ)+
        (ℓ:ℝ)^2*primeContactPrefix (N/ℓ^2))| ≤ C*(N:ℝ)^3*(conductorLog N)^6 := by
  obtain ⟨K,hK,h⟩ := square_fibre_prefix_feedback hp h₄
  refine ⟨(1+ℓ)*K,by positivity,fun N => ?_⟩
  let E (j : ℕ) := primeContactPrefix j-(deletedSquareFibrePrefix ℓ j-ℓ*primeContactPrefix (j/ℓ))
  have he : primeContactPrefix N-(deletedSquareFibrePrefix ℓ N-ℓ*deletedSquareFibrePrefix ℓ (N/ℓ)+
      (ℓ:ℝ)^2*primeContactPrefix (N/ℓ^2))=E N-ℓ*E (N/ℓ) := by
    dsimp only [E]; rw [Nat.div_div_eq_div_mul,←sq]; ring
  have hlow : |E (N/ℓ)|≤K*(N:ℝ)^3*(conductorLog N)^6 := by
    rcases Nat.eq_zero_or_pos (N/ℓ) with hz|hn
    · have hh := h 0
      simpa only [hz,Nat.cast_zero,zero_pow (by decide : 3≠0),mul_zero,zero_mul] using
        (hh.trans (by positivity : K*(0:ℝ)^3*(conductorLog 0)^6≤K*(N:ℝ)^3*(conductorLog N)^6))
    · apply (h _).trans
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.cast_le.mpr (Nat.div_le_self ..)) 3) hK)
        (pow_le_pow_left₀ (zero_le_one.trans (conductorLog_one_le _))
          (conductorLog_mono hn (Nat.div_le_self ..)) 6) (by positivity) (by positivity)
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg ℓ)]
  exact (add_le_add (h N) (mul_le_mul_of_nonneg_left hlow (Nat.cast_nonneg ℓ))).trans_eq (by ring)

#print axioms square_fibre_prefix_feedback
#print axioms square_fibre_two_step_feedback
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
