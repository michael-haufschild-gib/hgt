import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheIntegralOnTheRescaledProductShell
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFirstEndpointAboveTheMovingProductCut
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# First primes larger than the conductor

Summing the horizon for a fixed first prime produces a difference of two
real quotient meshes. Both have bounded variation on every finite
cofactor interval up to one logarithm. The coprime inner coefficients
have bounded partial sums, uniformly in the first prime.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The signed inner coefficient after imposing coprimality at a fixed prime. -/
def signedCoprimeCofactor (p v : ℕ) : ℝ := if p.Coprime v then innerJump 1 v else 0

private theorem signedCoprimeCofactor_prefix :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {p : ℕ}, p.Prime → 4 < p → ∀ K : ℕ,
      |∑ v ∈ Icc 1 K, signedCoprimeCofactor p v| ≤ A := by
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (R := 2) (by decide) 0)
  refine ⟨2*(2+mass 2),by positivity,fun {p} hp hp4 K => ?_⟩
  have hi (k : ℕ) : Ioc 0 k=Icc 1 k := by ext v; simp only [mem_Icc,mem_Ioc]; omega
  let I := Ioc 0 K
  let a := innerJump 1
  have split := sum_filter_add_sum_filter_not I (fun v => p ∣ v) a
  have he : I.filter (fun v => ¬p ∣ v) = I.filter (p.Coprime ·) :=
    filter_congr fun _ _ => hp.coprime_iff_not_dvd.symm
  rw [he] at split
  have hcut : (∑ v ∈ I with p.Coprime v, a v) =
      (∑ v ∈ I, a v)-(∑ v ∈ I with p ∣ v, a v) := by rw [←split]; ring
  rw [←hi K]
  change |∑ v ∈ I, (if p.Coprime v then a v else 0)| ≤ _
  rw [←sum_filter,hcut]
  dsimp only [I,a]
  rw [sum_divisible_Ioc hp.pos,Nat.zero_div,hi,hi]
  apply (abs_sub _ _).trans
  linarith only [innerJump_prefix_bound 1 K,innerJump_prime_multiple_prefix_bound le_rfl hp hp4 (K/p)]

/-- Each fixed prime costs a single harmonic sum on any cofactor interval,
uniformly in the real mesh and the far quotient endpoint. -/
theorem signed_cofactor_mesh_interval :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℕ}, p.Prime → 4 < p → ∀ b l m : ℕ, 0 < m →
      ∀ {d : ℝ}, 0 < d →
      |∑ v ∈ Ioc l m, signedCoprimeCofactor p v*quotientMeshProfile b (v*d)| ≤ C*(1+Real.log m) := by
  obtain ⟨A,hA,ha⟩ := signedCoprimeCofactor_prefix
  obtain ⟨D,hD,hv⟩ := quotientMeshProfile_product_variation
  refine ⟨6*A*D,by positivity,fun {p} hp h₄ b l m hm d hd => ?_⟩
  let V (k : ℕ) := quotientMeshProfile b (k*d)
  let H := 1+Real.log (m:ℝ)
  have hH : 1 ≤ H := le_add_of_nonneg_right (Real.log_natCast_nonneg _)
  have hK (K : ℕ) (hKm : K ≤ m) :
      |∑ v ∈ Icc 1 K, signedCoprimeCofactor p v*V v| ≤ 3*A*D*H := by
    rw [_root_.HTGeometry.sum_mul_eq_partial_mul_diff_ring (signedCoprimeCofactor p) V]
    have hcell (v : ℕ) (hvm : v ∈ Icc 1 K) :
        |(∑ j ∈ Icc 1 v, signedCoprimeCofactor p j)*(V v-V (v+1))| ≤ (2*A*D)*(1/(v:ℝ)) := by
      have hpos : (0:ℝ) < v := Nat.cast_pos.mpr (mem_Icc.mp hvm).1
      have he : |V v - V (v+1)| ≤ 2*D/v := by
        rw [abs_sub_comm]
        simpa only [V,Nat.cast_add,Nat.cast_one] using (hv b hpos hd).2
      rw [abs_mul]
      exact (mul_le_mul (ha hp h₄ v) he (abs_nonneg _) hA).trans_eq (by ring)
    have hs := (abs_sum_le_sum_abs _ _).trans (sum_le_sum hcell)
    rw [←mul_sum] at hs
    have hhar : (∑ v ∈ Icc 1 K, 1/(v:ℝ)) ≤ H :=
      (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hKm) (fun v _ _ => by positivity)).trans
        (_root_.RHTower.sum_Icc_one_div_le hm)
    have hc := hs.trans (mul_le_mul_of_nonneg_left hhar (by positivity))
    have hl : |(∑ v ∈ Icc 1 K, signedCoprimeCofactor p v)*V (K+1)| ≤ A*D := by
      rw [abs_mul]
      exact mul_le_mul (ha hp h₄ K) (hv b (Nat.cast_pos.mpr (Nat.succ_pos K)) hd).1 (abs_nonneg _) hA
    apply (abs_add_le _ _).trans ((add_le_add hc hl).trans ?_)
    linarith only [le_mul_of_one_le_right (mul_nonneg hA hD) hH]
  by_cases hlm : l ≤ m
  · have hi (k : ℕ) : Ioc 0 k=Icc 1 k := by ext v; simp only [mem_Icc,mem_Ioc]; omega
    have hs := sum_Ioc_consecutive (fun v => signedCoprimeCofactor p v*V v) (Nat.zero_le l) hlm
    rw [hi,hi] at hs
    change |∑ v ∈ Ioc l m, signedCoprimeCofactor p v*V v| ≤ _
    rw [show (∑ v ∈ Ioc l m, signedCoprimeCofactor p v*V v) =
      (∑ v ∈ Icc 1 m, signedCoprimeCofactor p v*V v)-(∑ v ∈ Icc 1 l, signedCoprimeCofactor p v*V v) by linarith only [hs]]
    exact (abs_sub _ _).trans ((add_le_add (hK m le_rfl) (hK l hlm)).trans_eq (by dsimp only [H]; ring))
  · rw [Ioc_eq_empty_of_le (le_of_not_ge hlm),sum_empty,abs_zero]
    exact mul_nonneg (by positivity) (zero_le_one.trans hH)

private theorem one_cell_mesh (h : ℝ) : quotientMeshProfile 1 h = -dyadicSpline h := by
  have h0 : dyadicSpline 0=0 := if_neg (lt_irrefl _)
  simp [quotientMeshProfile,centeredPrimeWeight_at_zero,h0]

private def firstPrimeSpline (U n p : ℕ) : ℝ :=
  splineCountReading n (fun k => cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) n p)

/-- Exact transposition of the fixed-prime row when the product cutoff
lies above the moving lower horizon. The one-cell subtraction retains
the full price of the first quotient. -/
private theorem firstPrimeSpline_mesh {U n p : ℕ} (hn : 0 < n) (hp : 0<p)
    (hY : ∀ k ≤ splineHorizon n, productLower 1 k ≤ U) :
    (n:ℝ)^2*firstPrimeSpline U n p =
      let b := splineHorizon n+1
      let I := Ioc (U/p) (min (splineHorizon n/p) n)
      (n:ℝ)*∑ v ∈ I, signedCoprimeCofactor p v*
        (quotientMeshProfile b ((v:ℝ)*(p/(n:ℝ)^2))-quotientMeshProfile 1 ((v:ℝ)*(p/(n:ℝ)^2))) := by
  let L := splineHorizon n
  let b := L+1
  let I := Ioc (U/p) (min (L/p) n)
  let z (k : ℕ) := sampledSpline n k-sampledSpline n (k+1)
  let w (v k : ℕ) := centeredPrimeWeight 1 (k/(p*v))
  have bounds (v : ℕ) (hv : v ∈ I) : 0 < p*v ∧ p*v ≤ L := by
    obtain ⟨hv₁,hv₂⟩ := mem_Ioc.mp hv
    exact ⟨Nat.mul_pos hp ((Nat.zero_le _).trans_lt hv₁), by
      simpa only [Nat.mul_comm v p] using (Nat.le_div_iff_mul_le hp).mp (hv₂.trans (min_le_left _ _))⟩
  have cell (k : ℕ) (hk : k ∈ Icc 1 L) :
      cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) n p =
        ∑ v ∈ I, if p*v ≤ k then signedCoprimeCofactor p v*w v k else 0 := by
    have hkl := (mem_Icc.mp hk).2
    have hi : I.filter (fun v => p*v ≤ k) = Ioc (U/p) (min (k/p) n) := by
      ext v
      simp only [I,mem_filter,mem_Ioc,le_min_iff,Nat.le_div_iff_mul_le hp,Nat.mul_comm v p]
      exact ⟨fun h => ⟨h.1.1,h.2,h.1.2.2⟩,fun h => ⟨⟨h.1,h.2.1.trans hkl,h.2.2⟩,h.2.1⟩⟩
    rw [←sum_filter,hi,cappedCoprimeSlice,max_eq_right (hY k hkl),sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases hc : p.Coprime v <;> simp [signedCoprimeCofactor,w,hc,Nat.div_div_eq_div_mul]
  have he : firstPrimeSpline U n p = ∑ v ∈ I, signedCoprimeCofactor p v*
      ∑ k ∈ Ico (p*v) b, z k*w v k := by
    unfold firstPrimeSpline splineCountReading
    calc _ = ∑ k ∈ Icc 1 L, ∑ v ∈ I, if p*v≤k then signedCoprimeCofactor p v*(z k*w v k) else 0 := by
              apply sum_congr rfl
              intro k hk
              rw [cell k hk,sum_mul]
              apply sum_congr rfl
              intro v _
              by_cases h : p*v ≤ k <;> simp only [h,if_true,if_false,zero_mul,z] <;> ring
         _ = _ := by
              rw [sum_comm]
              apply sum_congr rfl
              intro v hv
              have hi : (Icc 1 L).filter (p*v ≤ ·) = Ico (p*v) b := by
                ext k
                have hpos := (bounds v hv).1
                simp only [b,mem_filter,mem_Icc,mem_Ico]
                omega
              rw [←sum_filter,hi,mul_sum]
  rw [he,mul_sum,mul_sum]
  apply sum_congr rfl
  intro v hv
  obtain ⟨hv₀,hvL⟩ := bounds v hv
  have hh : L < (p*v)*b := (Nat.lt_succ_self L).trans_le (Nat.le_mul_of_pos_left b hv₀)
  have hsum := first_quotient_endpoint (n := n) (hvL.trans (Nat.le_succ L))
  change (∑ k ∈ Ico (p*v) b, z k*w v k) = unitHorizonPair n (p*v)+sampledSpline n (p*v) at hsum
  have hprofile := unitHorizonPair_real_profile hn hv₀ hh
  have hd : ((p*v:ℕ):ℝ)/(n:ℝ)^2 = (v:ℝ)*(p/(n:ℝ)^2) := by push_cast; ring
  rw [hd] at hprofile
  rw [hsum,one_cell_mesh,sampledSpline,hd]
  have hn' := (Nat.cast_pos.mpr (α := ℝ) hn).ne'
  have hs (x : ℝ) : (n:ℝ)^2*(x/n)=n*x := by field_simp
  linear_combination signedCoprimeCofactor p v*(hprofile+hs (dyadicSpline ((v:ℝ)*(p/(n:ℝ)^2))))

/-- The capped product after a sharp lower cut on its first prime. -/
def firstPrimeReadingAbove (P U n : ℕ) : ℝ :=
  splineCountReading n (fun k => ordinaryFactorTail (max 4 P) k
    (cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) n))

/-- The original product restricted to first primes above the conductor. -/
abbrev aboveConductorFirstPrimeReading (U n : ℕ) := firstPrimeReadingAbove n U n

/-- In the retained row ordinary factorization recovers the first prime
from the product, even if that product is less than the conductor square. -/
theorem first_prime_above_conductor_unique {n p v : ℕ} (hp : p.Prime) (hnp : n < p)
    (hv : 0 < v) (hvn : v ≤ n) :
    p.Coprime v ∧ ∃! r : ℕ, r.Prime ∧ r ∣ p*v ∧ n < r := by
  refine ⟨hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hv (hvn.trans_lt hnp)),
    p,⟨hp,dvd_mul_right p v,hnp⟩,?_⟩
  rintro r ⟨hr,hd,hnr⟩
  exact (hr.dvd_mul.mp hd).elim ((Nat.prime_dvd_prime_iff_eq hr hp).mp)
    (fun h => (hnr.not_ge ((Nat.le_of_dvd hv h).trans hvn)).elim)

/-- The coprimality indicator disappears from the full retained row while
the sharp cap and the original moving lower endpoint are unchanged. -/
theorem aboveConductorFirstPrimeReading_eq (U n : ℕ) :
    aboveConductorFirstPrimeReading U n = splineCountReading n (fun k =>
      ordinaryFactorTail (max 4 n) k (fun p =>
        ∑ v ∈ Ioc (max (productLower 1 k) U /p) (min (k/p) n),
          innerJump 1 v*centeredPrimeWeight 1 (k/(p*v)))) := by
  unfold aboveConductorFirstPrimeReading firstPrimeReadingAbove
  congr 1
  funext k
  unfold ordinaryFactorTail
  apply sum_congr rfl
  intro p hp
  congr 1
  obtain ⟨hip,hpr⟩ := mem_filter.mp hp
  have hnp := (le_max_right 4 n).trans_lt (mem_Ioc.mp hip).1
  unfold cappedCoprimeSlice
  rw [sum_filter]
  apply sum_congr rfl
  intro v hv
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hv
  have hc := (first_prime_above_conductor_unique hpr hnp ((Nat.zero_le _).trans_lt hl)
    (hu.trans (min_le_right _ _))).1
  rw [if_pos hc,Nat.div_div_eq_div_mul]

private theorem firstPrime_price_partition (P₀ U n : ℕ) :
    cappedUpperProductReading U n n-firstPrimeReadingAbove P₀ U n =
      ∑ p ∈ (Ioc 4 P₀).filter Nat.Prime, vonMangoldt p*firstPrimeSpline U n p := by
  let S := (Ioc 4 P₀).filter Nat.Prime
  let F (k : ℕ) := cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) n
  have row (k : ℕ) : ordinaryFactorTail 4 k (F k)-ordinaryFactorTail (max 4 P₀) k (F k) =
      ∑ p ∈ S, vonMangoldt p*F k p := by
    let P := (Ioc 4 k).filter Nat.Prime
    let f (p : ℕ) := vonMangoldt p*F k p
    have hlo : P.filter (· ≤ P₀) = S.filter (· ≤ k) := by
      ext p; simp only [P,S,mem_filter,mem_Ioc]; tauto
    have hhi : P.filter (fun p => ¬p ≤ P₀) = (Ioc (max 4 P₀) k).filter Nat.Prime := by
      ext p; simp only [P,mem_filter,mem_Ioc,max_lt_iff,not_le]; tauto
    have hkeep : ∑ p ∈ S.filter (· ≤ k), f p = ∑ p ∈ S, f p := by
      apply sum_subset (filter_subset _ _)
      intro p hp hnot
      have hkp := lt_of_not_ge fun h => hnot (mem_filter.mpr ⟨hp,h⟩)
      simp [f,F,cappedCoprimeSlice,Nat.div_eq_of_lt hkp]
    have h := sum_filter_add_sum_filter_not P (· ≤ P₀) f
    rw [hlo,hhi,hkeep] at h
    change (∑ p ∈ P, f p)-(∑ p ∈ (Ioc (max 4 P₀) k).filter Nat.Prime, f p) = _
    linarith only [h]
  let z (k : ℕ) := sampledSpline n k-sampledSpline n (k+1)
  change (∑ k ∈ Icc 1 (splineHorizon n), ordinaryFactorTail 4 k (F k)*z k) -
    (∑ k ∈ Icc 1 (splineHorizon n), ordinaryFactorTail (max 4 P₀) k (F k)*z k) = _
  rw [←sum_sub_distrib]
  simp_rw [←sub_mul,row,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  change _ = vonMangoldt p*∑ k ∈ Icc 1 (splineHorizon n), F k p*z k
  rw [mul_sum]
  exact sum_congr rfl fun k _ => mul_assoc _ _ _

private theorem small_first_prime_price :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P₀ : ℕ) {U n : ℕ}, 0<n → (∀ k ≤ splineHorizon n, productLower 1 k ≤ U) →
      |(n:ℝ)^2*(cappedUpperProductReading U n n-firstPrimeReadingAbove P₀ U n)| ≤
        C*(n:ℝ)*P₀*conductorLog n := by
  obtain ⟨A,hA,h⟩ := signed_cofactor_mesh_interval
  refine ⟨14*A,by positivity,fun P₀ {U n} hn hY => ?_⟩
  let S := (Ioc 4 P₀).filter Nat.Prime
  let H := conductorLog n
  have hH : 0 ≤ H := zero_le_one.trans (conductorLog_one_le n)
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have prime (p : ℕ) (hpS : p ∈ S) : |(n:ℝ)^2*firstPrimeSpline U n p| ≤ n*(2*A*H) := by
    obtain ⟨hi,hp⟩ := mem_filter.mp hpS
    have hp4 := (mem_Ioc.mp hi).1
    let m := min (splineHorizon n/p) n
    let l := U/p
    let b := splineHorizon n+1
    let d := (p:ℝ)/(n:ℝ)^2
    let X (c : ℕ) := ∑ v ∈ Ioc l m, signedCoprimeCofactor p v*quotientMeshProfile c (v*d)
    rw [firstPrimeSpline_mesh hn hp.pos hY]
    simp_rw [mul_sub]
    rw [sum_sub_distrib,abs_mul,abs_of_pos hn']
    apply mul_le_mul_of_nonneg_left _ hn'.le
    change |X b-X 1| ≤ 2*A*H
    have hx (c : ℕ) : |X c| ≤ A*H := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · simp only [X,hm,Ioc_eq_empty_of_le (Nat.zero_le l),sum_empty,abs_zero]
        exact mul_nonneg hA hH
      have hlog := Real.log_le_log (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr (min_le_right _ _) : (m:ℝ) ≤ n)
      have hlo := Real.log_le_log hn' (by linarith only [hn'] : (n:ℝ) ≤ 2*n)
      exact (h hp hp4 c l m hm (div_pos (Nat.cast_pos.mpr hp.pos) (sq_pos_of_pos hn'))).trans
        (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) (hlog.trans hlo)) hA)
    exact (abs_sub _ _).trans ((add_le_add (hx b) (hx 1)).trans_eq (by ring))
  have hs : S ⊆ Icc 1 P₀ := fun p hp => mem_Icc.mpr
    ⟨(mem_filter.mp hp).2.pos,(mem_Ioc.mp (mem_filter.mp hp).1).2⟩
  have hmass := (sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => (show 0 ≤ vonMangoldt p from vonMangoldt_nonneg))).trans
    (_root_.RHTower.sum_vonMangoldt_Icc_le_seven P₀)
  rw [firstPrime_price_partition,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ p ∈ S, vonMangoldt p*(n*(2*A*H)) := by
            apply sum_le_sum
            intro p hp
            rw [mul_left_comm,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
            exact mul_le_mul_of_nonneg_left (prime p hp) vonMangoldt_nonneg
       _ ≤ (7*(P₀:ℝ))*(n*(2*A*H)) := by
            rw [←sum_mul]
            exact mul_le_mul_of_nonneg_right hmass (by positivity)
       _ = _ := by dsimp only [H]; ring

private theorem eventually_seventeenNinths_above_lower :
    ∀ᶠ n : ℕ in atTop, ∀ k ≤ splineHorizon n, productLower 1 k ≤ ⌊(n:ℝ)^(17/9:ℝ)⌋₊ := by
  obtain ⟨T,hT,hwin⟩ := successorSquare_window_bound
  have hup := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<8/9)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),hup.eventually_ge_atTop (2*T)] with n hn hgap
  intro k hk
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hroot := Real.sqrt_le_sqrt ((Nat.cast_le.mpr hk : (k:ℝ) ≤ splineHorizon n).trans (hwin hn))
  rw [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hT) hn'.le)] at hroot
  apply Nat.le_floor
  calc (productLower 1 k:ℝ) ≤ ((2*⌊Real.sqrt (k:ℝ)⌋₊:ℕ):ℝ) := Nat.cast_le.mpr (min_le_right _ _)
       _ ≤ 2*(T*n) := by
         push_cast
         exact mul_le_mul_of_nonneg_left ((Nat.floor_le (Real.sqrt_nonneg _)).trans hroot) (by norm_num)
       _ ≤ (n:ℝ)^(8/9:ℝ)*n := by
         rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hgap hn'.le
       _ = (n:ℝ)^(8/9:ℝ)*(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
       _ = _ := by rw [←Real.rpow_add hn',show (8/9:ℝ)+1=17/9 by norm_num]

private theorem linear_first_prime_cut_fragments (P : ℕ → ℕ) {K : ℝ} (hK : 0≤K)
    (hP : ∀ {n : ℕ}, 0<n → (P n:ℝ)≤K*n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J M : ℕ,
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        firstPrimeReadingAbove (P n) ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨C,hC,hsmall⟩ := small_first_prime_price
  let A := C*K
  have hA : 0≤A := mul_nonneg hC hK
  have h {n U : ℕ} (hn : 0<n) (hY : ∀ k ≤ splineHorizon n, productLower 1 k≤U) :
      |(n:ℝ)^2*(cappedUpperProductReading U n n-firstPrimeReadingAbove (P n) U n)| ≤
        A*(n:ℝ)^2*conductorLog n := by
    apply (hsmall (P n) hn hY).trans
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hP hn)
      (mul_nonneg hC (Nat.cast_nonneg n))) (zero_le_one.trans (conductorLog_one_le n))).trans_eq
      (by dsimp only [A]; ring)
  obtain ⟨k,hk⟩ := Filter.eventually_atTop.mp eventually_seventeenNinths_above_lower
  let U (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let E (n : ℕ) := (n:ℝ)^2*(cappedUpperProductReading (U n) n n-firstPrimeReadingAbove (P n) (U n) n)
  let D := ∑ n ∈ range k, |E n|
  have hD : 0 ≤ D := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨A+D,add_nonneg hA hD,fun J M => ?_⟩
  let X := (M:ℝ)^2*conductorLog M
  have hX : 0 ≤ X := mul_nonneg (sq_nonneg _) (zero_le_one.trans (conductorLog_one_le M))
  have bound (n : ℕ) (hn : n ∈ Ioc J M) : |E n| ≤ (A+D)*X := by
    have hn' := (Nat.zero_le J).trans_lt (mem_Ioc.mp hn).1
    have hnm := (mem_Ioc.mp hn).2
    by_cases hk' : k ≤ n
    · apply (h hn' (hk n hk')).trans
      rw [mul_assoc]
      exact mul_le_mul (le_add_of_nonneg_right hD) (mul_le_mul
        (pow_le_pow_left₀ (Nat.cast_nonneg n) (Nat.cast_le.mpr hnm) 2) (conductorLog_mono hn' hnm)
        (zero_le_one.trans (conductorLog_one_le n)) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (zero_le_one.trans (conductorLog_one_le n))) (add_nonneg hA hD)
    · have h₁ : 1 ≤ X := one_le_mul_of_one_le_of_one_le
        (one_le_pow₀ (by exact_mod_cast (hn'.trans_le hnm) : (1:ℝ) ≤ M)) (conductorLog_one_le M)
      have hE : |E n| ≤ D := single_le_sum (fun j _ => abs_nonneg (E j)) (mem_range.mpr (lt_of_not_ge hk'))
      exact hE.trans ((le_add_of_nonneg_left hA).trans (le_mul_of_one_le_right (add_nonneg hA hD) h₁))
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum bound).trans ?_)
  rw [sum_const,Nat.card_Ioc,nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le M J)) (mul_nonneg (add_nonneg hA hD) hX)).trans_eq
    (by dsimp only [X]; ring)

/-- Removing all first primes at most the conductor costs one cubic
logarithm on every terminal fragment. -/
theorem seventeenNinths_first_primes_beyond_conductor :
    ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ,
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        aboveConductorFirstPrimeReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤ C*(M:ℝ)^3*conductorLog M :=
  linear_first_prime_cut_fragments id (K := 1) zero_le_one (fun {_} _ => by simp)

/-- All primes above this threshold have natural complementary upper bound
at most the conductor, even at the last spline horizon. -/
def capFreeFirstPrimeCut (n : ℕ) := max n (splineHorizon n/(n+1))

private theorem capFreeFirstPrimeCut_linear :
    ∃ K : ℝ, 0≤K ∧ ∀ {n : ℕ}, 0<n → (capFreeFirstPrimeCut n:ℝ)≤K*n := by
  obtain ⟨T,_,hL⟩ := successorSquare_window_bound
  refine ⟨1+T^2,by positivity,fun {n} hn => ?_⟩
  have hn' := Nat.cast_nonneg (α := ℝ) n
  have ht := mul_nonneg (sq_nonneg T) hn'
  have hq : ((splineHorizon n/(n+1):ℕ):ℝ) ≤ T^2*n := by
    apply Nat.cast_div_le.trans
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n) : (0:ℝ)<(n+1:ℕ))).mpr
    apply (hL hn).trans
    push_cast
    nlinarith only [ht]
  rw [capFreeFirstPrimeCut,Nat.cast_max]
  exact max_le (by linarith only [ht]) (by linarith only [hq,hn'])

/-- The surviving ordinary-prime reading. The cofactor has only the
original lower product endpoint and the natural upper product endpoint. -/
def capFreeFirstPrimeReading (U n : ℕ) : ℝ :=
  splineCountReading n (fun k => ordinaryFactorTail (max 4 (capFreeFirstPrimeCut n)) k
    (fun p => ∑ v ∈ Ioc (max (productLower 1 k) U/p) (k/p),
      innerJump 1 v*centeredPrimeWeight 1 (k/(p*v))))

theorem capFreeFirstPrimeReading_eq (n U : ℕ) :
    firstPrimeReadingAbove (capFreeFirstPrimeCut n) U n = capFreeFirstPrimeReading U n := by
  unfold firstPrimeReadingAbove capFreeFirstPrimeReading splineCountReading
  apply sum_congr rfl
  intro k hk
  congr 1
  unfold ordinaryFactorTail
  apply sum_congr rfl
  intro p hp
  congr 1
  obtain ⟨hip,hpr⟩ := mem_filter.mp hp
  have hP := (le_max_right 4 _).trans_lt (mem_Ioc.mp hip).1
  obtain ⟨hnp,hlp⟩ := max_lt_iff.mp hP
  have hkpn : k/p≤n := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpr.pos).mpr
    ((mem_Icc.mp hk).2.trans_lt (by simpa only [Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos n)).mp hlp)))
  rw [cappedCoprimeSlice,min_eq_left hkpn,sum_filter]
  apply sum_congr rfl
  intro v hv
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hv
  rw [if_pos (first_prime_above_conductor_unique hpr hnp ((Nat.zero_le _).trans_lt hl)
    (hu.trans hkpn)).1,Nat.div_div_eq_div_mul]

/-- The entire artificial cofactor cap and coprimality restriction disappear
from the full signed prefix at cubic-logarithmic error on every fragment. -/
theorem seventeenNinths_cap_free_first_prime_fragments :
    ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ,
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        capFreeFirstPrimeReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨K,hK,hP⟩ := capFreeFirstPrimeCut_linear
  simpa only [capFreeFirstPrimeReading_eq] using linear_first_prime_cut_fragments capFreeFirstPrimeCut hK hP

private theorem prefix_upper_iff_of_cubic_log_error (R : ℕ → ℕ → ℝ)
    (herr : ∃ C : ℝ, 0≤C ∧ ∀ J M : ℕ,
      |∑ n ∈ Ioc J M, (n:ℝ)^2*(cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n -
        R ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n)| ≤ C*(M:ℝ)^3*conductorLog M) {η : ℝ} (hη : 0 < η) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n) ≤ C*(M:ℝ)^(3+η)) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*R ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n) ≤ C*(M:ℝ)^(3+η) := by
  obtain ⟨A,hA,h⟩ := herr
  obtain ⟨D,hD,hd⟩ := conductorLog_subpower hη
  let U (n : ℕ) := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let V (M : ℕ) := ∑ n ∈ Ioc 0 M, (n:ℝ)^2*cappedUpperProductReading (U n) n n
  let W (M : ℕ) := ∑ n ∈ Ioc 0 M, (n:ℝ)^2*R (U n) n
  have gap (M : ℕ) (hM : 0 < M) : |V M-W M| ≤ A*D*(M:ℝ)^(3+η) := by
    simp only [V,W,←sum_sub_distrib,←mul_sub]
    apply (h 0 M).trans
    have hl := (le_self_pow₀ (conductorLog_one_le M) (by decide : 6≠0)).trans (hd hM)
    apply (mul_le_mul_of_nonneg_left hl (mul_nonneg hA (pow_nonneg (Nat.cast_nonneg M) 3))).trans_eq
    rw [Real.rpow_add (Nat.cast_pos.mpr hM),
      show (M:ℝ)^(3:ℝ)=(M:ℝ)^3 from Real.rpow_natCast _ 3]
    ring
  change (∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M → V M ≤ C*(M:ℝ)^(3+η)) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M → W M ≤ C*(M:ℝ)^(3+η)
  constructor <;> rintro ⟨C,hC,hC'⟩ <;> refine ⟨C+A*D,by positivity,fun M hM => ?_⟩
  · linarith only [(abs_le.mp (gap M hM)).1,hC' M hM]
  · linarith only [(abs_le.mp (gap M hM)).2,hC' M hM]

/-- At every exponent above three, a one-sided bound on the entire signed
prefix is equivalent to the same bound on the unique-large-prime part. -/
theorem prefix_upper_iff_first_primes_beyond_conductor {η : ℝ} (hη : 0 < η) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n) ≤ C*(M:ℝ)^(3+η)) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*aboveConductorFirstPrimeReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n) ≤ C*(M:ℝ)^(3+η) :=
  prefix_upper_iff_of_cubic_log_error _ seventeenNinths_first_primes_beyond_conductor hη

/-- For the full one-sided bound it suffices to use unrestricted
complementary factors with their natural product endpoints. -/
theorem prefix_upper_iff_cap_free_first_primes {η : ℝ} (hη : 0 < η) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*cappedUpperProductReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n n) ≤ C*(M:ℝ)^(3+η)) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 0 < M →
      (∑ n ∈ Ioc 0 M, (n:ℝ)^2*capFreeFirstPrimeReading ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n) ≤ C*(M:ℝ)^(3+η) :=
  prefix_upper_iff_of_cubic_log_error _ seventeenNinths_cap_free_first_prime_fragments hη

#print axioms signed_cofactor_mesh_interval
#print axioms first_prime_above_conductor_unique
#print axioms aboveConductorFirstPrimeReading_eq
#print axioms firstPrimeSpline_mesh
#print axioms firstPrime_price_partition
#print axioms seventeenNinths_first_primes_beyond_conductor
#print axioms prefix_upper_iff_first_primes_beyond_conductor
#print axioms capFreeFirstPrimeReading_eq
#print axioms seventeenNinths_cap_free_first_prime_fragments
#print axioms prefix_upper_iff_cap_free_first_primes
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
