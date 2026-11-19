import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.DivisorInversionAtTheProductBoundary
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FirstPrimesBeyondTheConductorInTheSignedPrefix
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SeventhDifferencesAcrossTheSignedCofactors

/-!
# The finite mesh at an ordinary first prime

Grouping by product gives a coefficient bounded by its divisor logarithm.
Grouping back by first prime gives a single spline mesh on all admissible
cofactors, with the first positive quotient and the terminal sample retained.
-/

noncomputable section
open Finset ArithmeticFunction Filter
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Ordinary prime divisors above the fixed cutoff carry the signed weight of their cofactor. -/
def firstPrimeProductCoefficient (P q : ℕ) : ℝ :=
  ∑ p ∈ q.divisors with p.Prime ∧ max 4 P < p, vonMangoldt p * innerJump 1 (q/p)

/-- Ordinary factorization bounds the coefficient even for products with several admissible primes. -/
theorem firstPrimeProductCoefficient_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ P q : ℕ, |firstPrimeProductCoefficient P q| ≤ A * Real.log q := by
  let A := 2*(1+mass (1+1))
  have hA : 0 ≤ A := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  refine ⟨A,hA,fun P q => ?_⟩
  let S := q.divisors.filter (fun p => p.Prime ∧ max 4 P < p)
  change |∑ p ∈ S, vonMangoldt p * innerJump 1 (q/p)| ≤ _
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S, vonMangoldt p * A := by
            apply sum_le_sum
            intro p _
            rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
            exact mul_le_mul_of_nonneg_left (innerJump_pointwise_bound 1 (q/p)) vonMangoldt_nonneg
       _ ≤ (∑ p ∈ q.divisors, vonMangoldt p)*A := by
            rw [←sum_mul]
            exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
              (fun _ _ _ => vonMangoldt_nonneg)) hA
       _ = _ := by rw [vonMangoldt_sum,mul_comm]

/-- The product mesh including its positive first quotient sample. -/
def positiveProductPair (n q : ℕ) := (n:ℝ)^2 * (unitHorizonPair n q + sampledSpline n q)

/-- In the unrestricted cofactor row, ordinary divisor inversion separates
the common first-prime cutoff from both moving product endpoints. -/
theorem common_prime_product_row (P U k : ℕ) (f : ℕ → ℝ) :
    (ordinaryFactorTail (max 4 P) k fun p =>
      ∑ v ∈ Ioc (U/p) (k/p), innerJump 1 v * f (p*v)) =
      ∑ q ∈ Ioc U k, firstPrimeProductCoefficient P q * f q := by
  let S := (Ioc (max 4 P) k).filter Nat.Prime
  let a (p q : ℕ) := vonMangoldt p * innerJump 1 (q/p) * f q
  have hp (p : ℕ) (hpS : p ∈ S) :
      vonMangoldt p*(∑ v ∈ Ioc (U/p) (k/p), innerJump 1 v*f (p*v)) =
        ∑ q ∈ Ioc U k, if p ∣ q then a p q else 0 := by
    have hp0 := (mem_filter.mp hpS).2.pos
    rw [←sum_filter,sum_divisible_Ioc hp0,mul_sum]
    exact sum_congr rfl fun v _ => by simp only [a,Nat.mul_div_cancel_left _ hp0,mul_assoc]
  unfold ordinaryFactorTail
  rw [sum_congr rfl hp,sum_comm]
  apply sum_congr rfl
  intro q hq
  obtain ⟨hlo,hqk⟩ := mem_Ioc.mp hq
  have hq0 := (Nat.zero_le U).trans_lt hlo
  have he : S.filter (· ∣ q) = q.divisors.filter (fun p => p.Prime ∧ max 4 P < p) := by
    ext p
    simp only [S,mem_filter,mem_Ioc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨hcut,_⟩,hpr⟩,hd⟩
      exact ⟨⟨hd,hq0.ne'⟩,hpr,hcut⟩
    · rintro ⟨⟨hd,_⟩,hpr,hcut⟩
      exact ⟨⟨⟨hcut,(Nat.le_of_dvd hq0 hd).trans hqk⟩,hpr⟩,hd⟩
  rw [←sum_filter,he,firstPrimeProductCoefficient,sum_mul]

/-- The exact common-cut reading at one conductor. Both terminal horizon
values are retained for each product in the positive quotient sum. -/
theorem common_prime_positive_product_pairs (P U n : ℕ) :
    (n:ℝ)^2*splineCountReading n (fun k => ordinaryFactorTail (max 4 P) k
      (fun p => ∑ v ∈ Ioc (U/p) (k/p), innerJump 1 v*centeredPrimeWeight 1 (k/(p*v)))) =
      ∑ q ∈ Ioc U (splineHorizon n), firstPrimeProductCoefficient P q*positiveProductPair n q := by
  let L := splineHorizon n
  let z (k : ℕ) := sampledSpline n k - sampledSpline n (k+1)
  let f (q k : ℕ) := firstPrimeProductCoefficient P q*(z k*centeredPrimeWeight 1 (k/q))
  have row (k : ℕ) := common_prime_product_row P U k (fun q => centeredPrimeWeight 1 (k/q))
  unfold splineCountReading
  simp_rw [row]
  have exchange : (∑ k ∈ Icc 1 L, (∑ q ∈ Ioc U k,
      firstPrimeProductCoefficient P q*centeredPrimeWeight 1 (k/q))*z k) =
      ∑ q ∈ Ioc U L, ∑ k ∈ Ico q (L+1), f q k := by
    calc _ = ∑ k ∈ Icc 1 L, ∑ q ∈ Ioc U L, if q≤k then f q k else 0 := by
              apply sum_congr rfl
              intro k hk
              have he : (Ioc U L).filter (· ≤ k) = Ioc U k := by
                ext q
                simp only [mem_filter,mem_Ioc]
                exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.trans (mem_Icc.mp hk).2⟩,h.2⟩⟩
              rw [←sum_filter,he,sum_mul]
              exact sum_congr rfl fun q _ => by dsimp only [f]; ring
         _ = _ := by
              rw [sum_comm]
              apply sum_congr rfl
              intro q hq
              have hq0 := (Nat.zero_le U).trans_lt (mem_Ioc.mp hq).1
              have he : (Icc 1 L).filter (q ≤ ·) = Ico q (L+1) := by
                ext k; simp only [mem_filter,mem_Icc,mem_Ico]; omega
              rw [←sum_filter,he]
  rw [exchange,mul_sum]
  apply sum_congr rfl
  intro q hq
  have hL := (mem_Ioc.mp hq).2.trans (Nat.le_succ L)
  simp only [f,←mul_sum]
  rw [first_quotient_endpoint (n := n) hL]
  dsimp only [positiveProductPair]
  ring

private theorem positive_product_pair_grid {n p v : ℕ} (hn : 0<n) (hp : 0<p) (hv : 0<v) :
    positiveProductPair n (p*v) = (n:ℝ)*positiveCofactorProfile (splineHorizon n+1) (p/(n:ℝ)^2) v := by
  let q := p*v
  let b := splineHorizon n+1
  let x := (v:ℝ)*(p/(n:ℝ)^2)
  have hq0 := Nat.mul_pos hp hv
  have hb : splineHorizon n<q*b := (Nat.lt_succ_self _).trans_le (Nat.le_mul_of_pos_left b hq0)
  have he := unitHorizonPair_real_profile hn hq0 hb
  have hq : (q:ℝ)/(n:ℝ)^2=x := by dsimp only [q,x]; push_cast; ring
  rw [hq] at he
  have hzero : dyadicSpline 0=0 := if_neg (lt_irrefl _)
  have hcell : quotientMeshProfile 1 x = -dyadicSpline x := by
    simp [quotientMeshProfile,centeredPrimeWeight_at_zero,hzero]
  have hn0 : (n:ℝ)≠0 := (Nat.cast_pos.mpr hn).ne'
  have hscale : (n:ℝ)^2*(dyadicSpline x/n)=n*dyadicSpline x := by
    linear_combination (n:ℝ)*(div_mul_cancel₀ (dyadicSpline x) hn0)
  change (n:ℝ)^2*(unitHorizonPair n q+dyadicSpline ((q:ℝ)/(n:ℝ)^2)/n) =
    (n:ℝ)*(quotientMeshProfile b x-quotientMeshProfile 1 x)
  rw [hq,hcell]
  linear_combination he+hscale

/-- Exact fixed-first-prime reading on the full horizon. The upper cofactor
is the last natural product; the lower cofactor is the original sharp cut. -/
theorem unrestricted_first_prime_mesh {n : ℕ} (hn : 0<n) (P U : ℕ) :
    (n:ℝ)^2*unrestrictedFirstPrimeReading P U n =
      ordinaryFactorTail (max 4 P) (splineHorizon n) (fun p =>
        (n:ℝ)*∑ v ∈ Ioc (U/p) (splineHorizon n/p),
          innerJump 1 v*positiveCofactorProfile (splineHorizon n+1) (p/(n:ℝ)^2) v) := by
  rw [unrestrictedFirstPrimeReading,common_prime_positive_product_pairs,
    ←common_prime_product_row P U (splineHorizon n) (positiveProductPair n)]
  unfold ordinaryFactorTail
  apply sum_congr rfl
  intro p hp
  congr 1
  dsimp only
  rw [mul_sum]
  apply sum_congr rfl
  intro v hv
  rw [positive_product_pair_grid hn (mem_filter.mp hp).2.pos ((Nat.zero_le _).trans_lt (mem_Ioc.mp hv).1)]
  ring

/-- The far cofactor endpoint lies beyond the last positive spline sample. -/
theorem positive_mesh_reaches_support {n p : ℕ} (hn : 0<n) (hp : 0<p) :
    4*Real.exp 8 < (splineHorizon n+1:ℕ)*((p:ℝ)/(n:ℝ)^2) ∧
    4*Real.exp 8 < (splineHorizon n/p+1:ℕ)*((p:ℝ)/(n:ℝ)^2) := by
  let L := splineHorizon n
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hgeom : 4*(n:ℝ)^2 ≤ ((2*n+1:ℕ):ℝ)^2 := by push_cast; linarith only [hn']
  have hprice := (mul_le_mul_of_nonneg_left hgeom (Real.exp_pos 8).le).trans
    (successorSquareWindowScale_bounds n).2.2
  have hL : 4*Real.exp 8*(n:ℝ)^2 ≤ L := by
    dsimp only [L,splineHorizon]
    push_cast
    linarith only [hprice,Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]
  have top (m : ℕ) (hm : L < m*p) : 4*Real.exp 8 < (m:ℝ)*((p:ℝ)/(n:ℝ)^2) := by
    rw [←mul_div_assoc,lt_div_iff₀ (sq_pos_of_pos hn')]
    exact hL.trans_lt (by exact_mod_cast hm)
  exact ⟨top _ ((Nat.lt_succ_self L).trans_le (Nat.le_mul_of_pos_right (L+1) hp)),
    top _ ((Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (L/p)))⟩

/-- The difference of two first-prime cuts on all their natural cofactors,
including both sharp product endpoints. -/
theorem first_prime_mesh_band {n F P : ℕ} (hn : 0<n) (hFP : F≤P) (U : ℕ) :
    (n:ℝ)^2*(unrestrictedFirstPrimeReading F U n-unrestrictedFirstPrimeReading P U n) =
      ∑ p ∈ (Ioc (max 4 F) (min P (splineHorizon n))).filter Nat.Prime,
        vonMangoldt p*((n:ℝ)*∑ v ∈ Ioc (U/p) (splineHorizon n/p),
          innerJump 1 v*positiveCofactorProfile (splineHorizon n+1) (p/(n:ℝ)^2) v) := by
  rw [mul_sub,unrestricted_first_prime_mesh hn,unrestricted_first_prime_mesh hn]
  let L := splineHorizon n
  let S := (Ioc (max 4 F) L).filter Nat.Prime
  let f (p : ℕ) := vonMangoldt p*((n:ℝ)*∑ v ∈ Ioc (U/p) (L/p),
    innerJump 1 v*positiveCofactorProfile (L+1) (p/(n:ℝ)^2) v)
  have small : S.filter (· ≤ P) = (Ioc (max 4 F) (min P L)).filter Nat.Prime := by
    ext p; simp only [S,mem_filter,mem_Ioc,le_min_iff]; tauto
  have big : S.filter (fun p => ¬p≤P) = (Ioc (max 4 P) L).filter Nat.Prime := by
    ext p; simp only [S,mem_filter,mem_Ioc,max_lt_iff,not_le]
    exact ⟨fun h => ⟨⟨⟨h.1.1.1.1,h.2⟩,h.1.1.2⟩,h.1.2⟩,fun h =>
      ⟨⟨⟨⟨h.1.1.1,hFP.trans_lt h.1.1.2⟩,h.1.2⟩,h.2⟩,h.1.1.2⟩⟩
  have hsplit := sum_filter_add_sum_filter_not S (· ≤ P) f
  rw [small,big] at hsplit
  change (∑ p ∈ S, f p)-(∑ p ∈ (Ioc (max 4 P) L).filter Nat.Prime, f p) = _
  linarith only [hsplit]

#print axioms firstPrimeProductCoefficient_bound
#print axioms common_prime_product_row
#print axioms common_prime_positive_product_pairs
#print axioms unrestricted_first_prime_mesh
#print axioms positive_mesh_reaches_support
#print axioms first_prime_mesh_band

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
