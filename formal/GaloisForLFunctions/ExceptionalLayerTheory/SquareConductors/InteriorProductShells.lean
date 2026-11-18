import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCompleteUpperProductTail
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SquareDilationOfThePrimeMesh
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.HigherDifferencesOfThePrimeMesh
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SecondHorizonCancellation

/-!
# Interior product shells of the capped ordinary-prime spline

When both product endpoints lie outside the test support, a second
Abel step applies to every pair on the shell. The coprimality and
ordinary first-prime weights remain in the finite sum.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Coprime complementary factors on the shell at a fixed first prime. -/
def cappedShellFactors (n V p : ℕ) := (Ioc (V/p) (min (2*V/p) n)).filter (p.Coprime ·)
private def shellSlice (n V k p : ℕ) := ∑ v ∈ cappedShellFactors n V p,
  innerJump 1 v*centeredPrimeWeight 1 (k/(p*v))

private theorem cap_sub_cap {k p V : ℕ} (hV : 2*V≤k) (n : ℕ) :
    cappedCoprimeSlice 1 1 k V n p-cappedCoprimeSlice 1 1 k (2*V) n p=shellSlice n V k p := by
  let S := (Ioc (V/p) (min (k/p) n)).filter (p.Coprime ·)
  let a (v : ℕ) := innerJump 1 v*centeredPrimeWeight 1 (k/(p*v))
  have hv : V/p≤2*V/p := Nat.div_le_div_right (by omega : V≤2*V)
  have hk : 2*V/p≤k/p := Nat.div_le_div_right hV
  have lo : S.filter (fun v => v≤2*V/p)=cappedShellFactors n V p := by
    ext v; simp only [S,cappedShellFactors,mem_filter,mem_Ioc,le_min_iff]
    constructor
    · exact fun h => ⟨⟨h.1.1.1,h.2,h.1.1.2.2⟩,h.1.2⟩
    · exact fun h => ⟨⟨⟨h.1.1,h.1.2.1.trans hk,h.1.2.2⟩,h.2⟩,h.1.2.1⟩
  have hi : S.filter (fun v => ¬v≤2*V/p)=(Ioc (2*V/p) (min (k/p) n)).filter (p.Coprime ·) := by
    ext v
    simp only [S,mem_filter,mem_Ioc,not_le]
    constructor
    · exact fun h => ⟨⟨h.2,h.1.1.2⟩,h.1.2⟩
    · exact fun h => ⟨⟨⟨hv.trans_lt h.1.1,h.1.2⟩,h.2⟩,h.1.1⟩
  have hs := sum_filter_add_sum_filter_not S (fun v => v≤2*V/p) a
  rw [lo,hi] at hs
  simp only [cappedCoprimeSlice,shellSlice,Nat.div_div_eq_div_mul]
  change (∑ v ∈ S, a v)-(∑ v ∈ _,a v)=∑ v ∈ cappedShellFactors n V p,a v
  linarith only [hs]

/-- Signed horizon reading at one product q, including the terminal mesh value. -/
def splineProductHorizonPair (n q : ℕ) :=
  ∑ k ∈ range (splineHorizon n+1), horizonDifference (sampledSpline n) k*centeredPrimeWeight 1 (k/q)

/-- Exact exchange on an interior shell. The upper cofactor cap n is
imposed before exchanging the primes and horizons. -/
theorem cappedInteriorShell_exchange {n V : ℕ} (hn : 0<n)
    (hbirth : (2*(V:ℝ)+1)<Real.exp (-8)*(n:ℝ)^2)
    (hY : productLower 1 (splineHorizon n)≤V) :
    cappedUpperProductReading V n n-cappedUpperProductReading (2*V) n n =
      ordinaryFactorTail 4 (2*V) (fun p => ∑ v ∈ cappedShellFactors n V p, innerJump 1 v*splineProductHorizonPair n (p*v)) := by
  let L := splineHorizon n
  let z := horizonDifference (sampledSpline n)
  let row (k : ℕ) := ordinaryFactorTail 4 (2*V) (shellSlice n V k)
  have hz (k : ℕ) (hk : k≤2*V) : z k=0 := by
    have hh : (k:ℝ)≤2*(V:ℝ) := by exact_mod_cast hk
    have hn₁ : ((k+1:ℕ):ℝ)<Real.exp (-8)*(n:ℝ)^2 := by push_cast; linarith only [hbirth,hh]
    simp only [z,horizonDifference,sampledSpline_eq_zero_before hn (by linarith only [hbirth,hh] : (k:ℝ)<_),
      sampledSpline_eq_zero_before hn hn₁,sub_self]
  have ha : cappedUpperProductReading V n n-cappedUpperProductReading (2*V) n n =
      ∑ k ∈ Icc 1 L, z k*row k := by
    unfold cappedUpperProductReading splineCountReading
    rw [←sum_sub_distrib]
    apply sum_congr rfl; intro k hk
    rw [←sub_mul]
    change _*z k=z k*row k
    by_cases h : k≤2*V
    · rw [hz k h,mul_zero,zero_mul]
    · rw [mul_comm (z k)]
      congr 1
      have hL := (mem_Icc.mp hk).2
      have hy : productLower 1 k≤V := (min_le_min hL (Nat.mul_le_mul_left _
        (Nat.floor_mono (Real.sqrt_le_sqrt (by exact_mod_cast hL))))).trans hY
      have ht : 2*V≤k := by omega
      have hpad := unit_prime_padding ht (shellSlice n V k) (fun p hp => by
        have hh : min (2*V/p) n=0 := by rw [Nat.div_eq_of_lt hp,zero_min]
        simp only [shellSlice,cappedShellFactors,hh,Ioc_eq_empty_of_le (Nat.zero_le _),filter_empty,sum_empty])
      dsimp only [row]
      rw [hpad]
      simp only [max_eq_right hy,max_eq_right (hy.trans (by omega : V≤2*V)),ordinaryFactorTail,←sum_sub_distrib]
      exact sum_congr rfl fun p _ => by rw [←mul_sub,cap_sub_cap ht]
  have hb : (∑ k ∈ Icc 1 L, z k*row k) = ∑ k ∈ range (L+1), z k*row k := by
    apply sum_subset
    · intro k hk; exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
    · intro k hk hx
      have he : k=0 := by
        have hle := mem_range.mp hk
        by_contra! hnz
        exact hx (mem_Icc.mpr ⟨Nat.pos_of_ne_zero hnz,by omega⟩)
      subst k; rw [hz 0 (Nat.zero_le _),zero_mul]
  rw [ha,hb]
  simp only [row,ordinaryFactorTail,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro p _
  simp only [mul_left_comm (z _) (vonMangoldt p),←mul_sum]
  congr 1
  simp only [shellSlice,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro v _
  simp only [splineProductHorizonPair,z,L,mul_sum]
  exact sum_congr rfl fun k _ => by ring

private theorem horizonPair_bound :
    ∃ K : ℝ, 0≤K ∧ ∀ {n q : ℕ}, 0<n → 0<q →
      1<Real.exp (-8)*(n:ℝ)^2 → |splineProductHorizonPair n q| ≤ K*(q:ℝ)^2/(n:ℝ)^5 := by
  obtain ⟨C,hC,h⟩ := centeredPrimeWeight_second_horizon
  obtain ⟨B,hB,h₃⟩ := sampledSpline_third_difference
  obtain ⟨A,hA,hL⟩ := successorSquare_window_bound
  refine ⟨C*(A^2+1)*B,by positivity,fun {n q} hn hq hstart => ?_⟩
  let t := splineHorizon n+1
  let z := horizonDifference (sampledSpline n)
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hz₀ : sampledSpline n 0=0 := sampledSpline_eq_zero_before hn (by simpa using (zero_lt_one.trans hstart))
  have hz₁ : sampledSpline n 1=0 := sampledSpline_eq_zero_before hn (by simpa using hstart)
  have hzt (k : ℕ) (hk : t≤k) : sampledSpline n k=0 := sampledSpline_eq_zero_after hn hk
  have hterminal (k : ℕ) (hk : t≤k) : z k=0 := by
    rw [show z k=sampledSpline n k-sampledSpline n (k+1) by rfl,hzt k hk,hzt _ (by omega),sub_self]
  have hsum : (∑ k ∈ range t, z k)=0 := by
    have ht := sum_range_sub (fun k => -sampledSpline n k) t
    simpa only [z,horizonDifference,neg_sub_neg,hz₀,hzt t le_rfl,sub_self] using ht
  have hb := h hq t z (show 0≤B/(n:ℝ)^7 by positivity)
    (by simp only [z,horizonDifference,hz₀,hz₁,sub_self]) (hterminal t le_rfl)
    (hterminal _ (Nat.le_succ t)) hsum (fun k _ => by
      simpa only [horizonDifference,z,Nat.add_assoc] using h₃ hn k)
  have hlen : (t:ℝ)≤(A^2+1)*(n:ℝ)^2 := by
    have hw := hL hn
    dsimp [t,splineHorizon]; push_cast at hw ⊢
    linarith only [hw,one_le_pow₀ (n := 2) (by exact_mod_cast hn : (1:ℝ)≤n)]
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen
    (mul_nonneg hC (sq_nonneg (q:ℝ)))) (by positivity : 0≤B/(n:ℝ)^7)
  exact hh.trans_eq (by field_simp <;> ring)

/-- For every interior shell V<pv≤2V and cap v≤n, the full signed
ordinary-prime reading costs V³ log(2V)/n⁵. -/
theorem capped_interior_shell_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ {n V : ℕ}, 0<n → 0<V →
      2*(V:ℝ)+1<Real.exp (-8)*(n:ℝ)^2 → productLower 1 (splineHorizon n)≤V →
      |cappedUpperProductReading V n n-cappedUpperProductReading (2*V) n n| ≤
        C*(V:ℝ)^3*(1+Real.log (2*(V:ℝ)))/(n:ℝ)^5 := by
  obtain ⟨K,hK,h⟩ := horizonPair_bound
  let G := 2*(1+mass (1+1))
  have hG : 0≤G := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  let E := Real.log 4+4
  have hE : 0≤E := by dsimp [E]; have := Real.log_nonneg (by norm_num : (1:ℝ)≤4); positivity
  refine ⟨8*G*K*E,by positivity,fun {n V} hn hv hbirth hY => ?_⟩
  let U := 2*V
  have hu : 0<U := Nat.mul_pos (by decide) hv
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hstart : 1<Real.exp (-8)*(n:ℝ)^2 := by linarith only [hbirth,Nat.cast_nonneg (α := ℝ) V]
  rw [cappedInteriorShell_exchange hn hbirth hY]
  suffices hrow : ∀ p ∈ (Ioc 4 U).filter Nat.Prime,
      |∑ v ∈ cappedShellFactors n V p, innerJump 1 v*splineProductHorizonPair n (p*v)|≤(G*K*(U:ℝ)^3/(n:ℝ)^5)/p by
    exact (ordinaryFactorTail_reciprocal hu (by positivity : 0≤G*K*(U:ℝ)^3/(n:ℝ)^5) hrow).trans_eq
      (by dsimp only [U,E]; push_cast; ring)
  intro p hp
  have hp₀ := (mem_filter.mp hp).2.pos
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp₀
  have hh (v : ℕ) (hmem : v ∈ cappedShellFactors n V p) :
      |innerJump 1 v*splineProductHorizonPair n (p*v)|≤G*(K*(U:ℝ)^2/(n:ℝ)^5) := by
    obtain ⟨hl,hh⟩ := mem_Ioc.mp (mem_filter.mp hmem).1
    have hprod : p*v≤U := by simpa only [Nat.mul_comm v p] using
      (Nat.le_div_iff_mul_le hp₀).mp (hh.trans (min_le_left ..))
    have he := h hn (Nat.mul_pos hp₀ ((Nat.zero_le _).trans_lt hl)) hstart
    rw [abs_mul]
    apply mul_le_mul (innerJump_pointwise_bound 1 v) (he.trans _) (abs_nonneg _) hG
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg (p*v)) (by exact_mod_cast hprod) 2) hK) (by positivity)
  have hcard : (cappedShellFactors n V p).card≤U/p := by
    apply (card_le_card (filter_subset _ _)).trans
    rw [Nat.card_Ioc]
    exact (Nat.sub_le ..).trans (min_le_left ..)
  have hc : ((cappedShellFactors n V p).card:ℝ)*p≤U := by
    exact_mod_cast (Nat.mul_le_mul_right p hcard).trans (Nat.div_mul_le_self U p)
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hh).trans _)
  rw [sum_const,nsmul_eq_mul,le_div_iff₀ hp']
  have he := mul_le_mul_of_nonneg_right hc (by positivity : 0≤G*(K*(U:ℝ)^2/(n:ℝ)^5))
  linarith only [he]

#print axioms capped_interior_shell_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
