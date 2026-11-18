import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CappedConductorPrefixes
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PeriodicQuotientCancellation

/-!
# The endpoint at quotient zero

Extending a product's horizon down from its first positive quotient adds
the negative of its spline sample. The full periodic extension on the
Mangoldt measure has only a logarithmic factorial error and a linear
density, whose signed spline integral vanishes.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

theorem centeredPrimeWeight_at_zero : centeredPrimeWeight 1 0 = 1 := by
  simp [centeredPrimeWeight, primeWeight, parityCorrection_small, factorialPrefix, stencil]

private theorem sampledSpline_at_zero (n : ℕ) : sampledSpline n 0 = 0 := by
  simp [sampledSpline,dyadicSpline]

private theorem sum_mesh_diff (w : ℕ → ℝ) (b : ℕ) :
    ∑ k ∈ range b, (w k - w (k+1)) = w 0 - w b := by
  induction b with
  | zero => simp
  | succ b ih => rw [Finset.sum_range_succ, ih]; ring

/-- The actual first quotient returns the spline value at the product, with
positive sign. This identity holds throughout the terminal support as well. -/
theorem first_quotient_endpoint {n q : ℕ} (hq : q ≤ splineHorizon n + 1) :
    (∑ k ∈ Ico q (splineHorizon n + 1),
      (sampledSpline n k-sampledSpline n (k+1))*centeredPrimeWeight 1 (k/q)) =
      unitHorizonPair n q + sampledSpline n q := by
  rw [sum_Ico_eq_sub _ hq]
  have hbase : (∑ k ∈ range q,
      (sampledSpline n k-sampledSpline n (k+1))*centeredPrimeWeight 1 (k/q)) =
        -sampledSpline n q := by
    rw [sum_congr rfl (fun k hk => by rw [Nat.div_eq_of_lt (mem_range.mp hk),
      centeredPrimeWeight_at_zero,mul_one]),sum_mesh_diff,sampledSpline_at_zero,zero_sub]
  rw [hbase,sub_neg_eq_add]
  rfl

/-- Difference between restricting to positive quotients and extending over
quotient zero, with precisely the ordinary prime logarithms. -/
def firstQuotientPrimeEndpoint (n : ℕ) : ℝ :=
  ∑ q ∈ ordinaryPrimeLags (splineHorizon n), vonMangoldt q *
    ((∑ k ∈ Ico q (splineHorizon n + 1),
      (sampledSpline n k-sampledSpline n (k+1))*centeredPrimeWeight 1 (k/q)) -
        unitHorizonPair n q)

theorem firstQuotientPrimeEndpoint_eq {n : ℕ} (hn : 0 < n) :
    firstQuotientPrimeEndpoint n = dyadicPrimeContact n := by
  unfold firstQuotientPrimeEndpoint dyadicPrimeContact
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨hi,hp⟩ := mem_filter.mp hq
  have he := first_quotient_endpoint (n := n) ((mem_Icc.mp hi).2.trans (Nat.le_succ _))
  rw [he,add_sub_cancel_left,sampledSpline_prime_contact hn hp.pos,mul_comm]

/-- The returned first endpoint alone approximates the actual rational price
within a quadratic error at every conductor. -/
theorem firstQuotientPrimeEndpoint_price :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
      |Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ) -
        (n:ℝ)^2 * firstQuotientPrimeEndpoint n| ≤ C*(n:ℝ)^2 := by
  obtain ⟨A,hA,ha⟩ := successorSquare_contact_error
  obtain ⟨B,hB,hb⟩ := dyadicPrimeContact_error
  refine ⟨A+B,add_nonneg hA hB,fun {n} hn => ?_⟩
  let P := ordinaryPrimeContact (successorSquareTriple n)
  let g := ordinaryPrimeGenerator (n • successorSquareTriple n)
  have he : Real.log (g:ℝ) - (n:ℝ)^2*firstQuotientPrimeEndpoint n =
      (Real.log (g:ℝ) - (n:ℝ)^2*P) + (n:ℝ)^2*(P-dyadicPrimeContact n) := by
    rw [firstQuotientPrimeEndpoint_eq hn]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]
  exact (add_le_add (ha hn (le_refl n))
    (mul_le_mul_of_nonneg_left (hb hn) (sq_nonneg (n:ℝ)))).trans_eq (by ring)

/-- On any terminal fragment the entire discrepancy between the returned
prime endpoints and the rational conductor prices is at most cubic. -/
theorem firstQuotientPrimeEndpoint_partial_prefix :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L M : ℕ,
      |Real.log ((∏ n ∈ Ioc L M, ordinaryPrimeGenerator (n • successorSquareTriple n) : ℚ):ℝ) -
        ∑ n ∈ Ioc L M, (n:ℝ)^2 * firstQuotientPrimeEndpoint n| ≤ C*(M:ℝ)^3 := by
  obtain ⟨C,hC,h⟩ := firstQuotientPrimeEndpoint_price
  refine ⟨C,hC,fun L M => ?_⟩
  let g (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)
  have hg (n : ℕ) : (g n:ℝ) ≠ 0 := (show 0 < (g n:ℝ) by
    exact_mod_cast (show 0 < g n from prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _)).ne'
  change |Real.log ((∏ n ∈ Ioc L M, g n : ℚ):ℝ) - _| ≤ _
  push_cast
  rw [Real.log_prod (fun n _ => hg n),←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ _n ∈ Ioc L M, C*(M:ℝ)^2 := by
            apply sum_le_sum
            intro n hn
            obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hn
            exact (h ((Nat.zero_le L).trans_lt hlo)).trans (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hhi) 2) hC)
       _ ≤ (M:ℝ)*(C*(M:ℝ)^2) := by
            rw [sum_const,nsmul_eq_mul,Nat.card_Ioc]
            exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M L)) (by positivity)
       _ = _ := by ring

/-- At the first conductor the terminal-fragment product specializes to the
original rational prefix. -/
theorem firstQuotientPrimeEndpoint_prefix :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |Real.log (squareGeneratorPrefix N:ℝ) -
        ∑ n ∈ Ioc 0 N, (n:ℝ)^2 * firstQuotientPrimeEndpoint n| ≤ C*(N:ℝ)^3 := by
  obtain ⟨C,hC,h⟩ := firstQuotientPrimeEndpoint_partial_prefix
  exact ⟨C,hC,fun N => h 0 N⟩

/-- Mangoldt-weighted quotient increment after the quotient-zero extension. -/
def completedMangoldtRow (k : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 k, vonMangoldt q*(centeredPrimeWeight 1 (k/q)-1)

/-- On the complete product range, exchanging products and horizons yields
the periodic quotient weight with its quotient-zero value subtracted. -/
theorem complete_mangoldt_mesh_rows {n : ℕ} (hn : 0 < n) :
    (∑ q ∈ Icc 1 (splineHorizon n), vonMangoldt q * unitHorizonPair n q) =
      splineCountReading n completedMangoldtRow := by
  let L := splineHorizon n
  let z (k : ℕ) := sampledSpline n k-sampledSpline n (k+1)
  have zd : (∑ k ∈ range (L+1), z k) = 0 := by
    dsimp only [z]
    rw [sum_mesh_diff, sampledSpline_at_zero, sampledSpline_endpoint hn, sub_self]
  have origin (q : ℕ) : unitHorizonPair n q =
      ∑ k ∈ Icc 1 L, z k * (centeredPrimeWeight 1 (k/q)-1) := by
    have hs : (∑ k ∈ range (L+1), z k * (centeredPrimeWeight 1 (k/q)-1)) =
        unitHorizonPair n q := by
      simp only [mul_sub,mul_one,sum_sub_distrib,zd,sub_zero]
      rfl
    rw [← hs]
    symm
    apply sum_subset (fun k hk => mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2))
    intro k hk hnmem
    have he : k = 0 := by
      have hL := Nat.le_of_lt_succ (mem_range.mp hk)
      by_contra h
      exact hnmem (mem_Icc.mpr ⟨Nat.pos_of_ne_zero h,hL⟩)
    simp only [he,Nat.zero_div,centeredPrimeWeight_at_zero,sub_self,mul_zero]
  simp_rw [origin,mul_sum]
  rw [sum_comm]
  unfold splineCountReading
  apply sum_congr rfl
  intro k hk
  rw [completedMangoldtRow,sum_mul]
  let f (q : ℕ) := vonMangoldt q*(centeredPrimeWeight 1 (k/q)-1)*z k
  calc _ = ∑ q ∈ Icc 1 L, f q := sum_congr rfl fun q _ => by dsimp [f]; ring
       _ = _ := by
         apply (sum_subset (Icc_subset_Icc_right (mem_Icc.mp hk).2) ?_).symm
         intro q hq hnot
         have hqk : k < q := lt_of_not_ge fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hq).1,h⟩)
         simp only [f,Nat.div_eq_of_lt hqk,centeredPrimeWeight_at_zero,sub_self,mul_zero,zero_mul]

/-- The complete periodic row is the negative integer density within a
logarithmic error. Ordinary factorization enters through the factorial identity. -/
theorem complete_mangoldt_row_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k : ℕ}, 1 ≤ k → |completedMangoldtRow k + k| ≤ K*(1+Real.log k) := by
  let F := 420*(1+mass 1)
  let c := 3+Real.log ((128*(128*1^2+1):ℕ):ℝ)
  have hmass := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; have := Real.log_natCast_nonneg (128*(128*1^2+1)); positivity
  refine ⟨F*(c+2),by positivity,fun {k} hk => ?_⟩
  have hψ : (∑ q ∈ Icc 1 k, vonMangoldt q) = Chebyshev.psi k := by
    unfold Chebyshev.psi
    rw [Nat.floor_natCast]
    rfl
  have he : completedMangoldtRow k + k =
      -((Chebyshev.psi k-k)-∑ q ∈ Icc 1 k, vonMangoldt q*centeredPrimeWeight 1 (k/q)) := by
    simp only [completedMangoldtRow,mul_sub,mul_one,sum_sub_distrib,hψ]
    ring
  rw [he,abs_neg]
  apply (centeredPrimeWeight_factorial (R := 1) le_rfl hk).trans
  change F * (c + 2*Real.log k) ≤ _
  exact (mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg hc (Real.log_natCast_nonneg k)] :
    c+2*Real.log k ≤ (c+2)*(1+Real.log k)) hF).trans_eq (by ring)

/-- The signed full periodic extension costs one conductor logarithm divided
by the conductor. Its first quotient endpoint was removed exactly. -/
theorem complete_mangoldt_mesh_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
      |∑ q ∈ Icc 1 (splineHorizon n), vonMangoldt q*unitHorizonPair n q| ≤ C*conductorLog n/n := by
  obtain ⟨K,hK,hr⟩ := complete_mangoldt_row_error
  obtain ⟨A,hA,ha⟩ := successorSquare_window_bound
  obtain ⟨D,_,hD,_,hd⟩ := sampledSpline_differences
  obtain ⟨J,hJ,hj⟩ := splineHorizon_conductorLog
  obtain ⟨B,hB,hden⟩ := sampledSpline_density
  refine ⟨A^2*K*J*D+B,by positivity,fun {n} hn => ?_⟩
  let L := splineHorizon n
  let E (k : ℕ) := completedMangoldtRow k + k
  have hpos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hH := zero_le_one.trans (conductorLog_one_le n)
  have hE : |splineCountReading n E| ≤ A^2*K*J*D*conductorLog n/n := by
    unfold splineCountReading
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _k ∈ Icc 1 L, (K*(J*conductorLog n))*(D/(n:ℝ)^3) := by
              apply sum_le_sum
              intro k hk
              obtain ⟨hk1,hkL⟩ := mem_Icc.mp hk
              have hl := Real.log_le_log (by exact_mod_cast hk1 : (0:ℝ) < k) (Nat.cast_le.mpr hkL)
              rw [abs_mul]
              exact mul_le_mul ((hr hk1).trans (mul_le_mul_of_nonneg_left
                ((add_le_add (le_refl (1:ℝ)) hl).trans (hj hn)) hK)) ((hd hn k).1) (abs_nonneg _) (by positivity)
         _ ≤ (A*n)^2*((K*(J*conductorLog n))*(D/(n:ℝ)^3)) := by
              rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
              exact mul_le_mul_of_nonneg_right (ha hn) (by positivity)
         _ = _ := by field_simp
  have hdens := _root_.HTGeometry.sum_mul_eq_partial_mul_diff_ring
    (fun _ => (1:ℝ)) (sampledSpline n) L
  have he : splineCountReading n (fun k => (k:ℝ)) = ∑ k ∈ Icc 1 L, sampledSpline n k := by
    simpa only [splineCountReading,one_mul,sum_const,nsmul_eq_mul,mul_one,Nat.card_Icc,
      Nat.add_sub_cancel,sampledSpline_endpoint hn,mul_zero,add_zero,L] using hdens.symm
  have hs : splineCountReading n completedMangoldtRow =
      splineCountReading n E - splineCountReading n (fun k => (k:ℝ)) := by
    unfold splineCountReading
    rw [←sum_sub_distrib]
    exact sum_congr rfl fun k _ => by dsimp only [E]; ring
  rw [complete_mangoldt_mesh_rows hn,hs,he]
  apply (abs_sub _ _).trans ((add_le_add hE (hden hn)).trans _)
  have hB' := le_mul_of_one_le_right hB (conductorLog_one_le n)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith only [hB']) hpos.le

#print axioms firstQuotientPrimeEndpoint_partial_prefix
#print axioms firstQuotientPrimeEndpoint_price
#print axioms first_quotient_endpoint
#print axioms complete_mangoldt_mesh_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
