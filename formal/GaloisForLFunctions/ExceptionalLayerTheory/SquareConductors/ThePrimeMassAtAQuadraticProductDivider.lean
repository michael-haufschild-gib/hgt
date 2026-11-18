import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFirstEndpointAboveTheMovingProductCut
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PiecewiseSmoothnessOfTheDyadicSpline
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeIntervalsOnTheRescaledConductor
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth

/-!
# Prime mass at a quadratic product divider

Splitting the returned ordinary-prime endpoint by product size produces a
signed density on either side of the cut. It is the primitive of the spline.
The error keeps the last prime-count sample as well as the interior differences.
-/

noncomputable section
open Finset ArithmeticFunction MeasureTheory
open GaloisForLFunctions.CountingHolography.Sections
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def primeAtom (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

/-- The contribution through product K to the n²-weighted returned endpoint. -/
def lowerPrimeEndpointPrice (n K : ℕ) : ℝ :=
  (n:ℝ)^2*∑ k ∈ Icc 1 K, primeAtom k * sampledSpline n k

private theorem lower_price_prime_sum (n K : ℕ) :
    lowerPrimeEndpointPrice n K =
      (n:ℝ)^2*∑ q ∈ ordinaryPrimeLags K, vonMangoldt q * sampledSpline n q := by
  unfold lowerPrimeEndpointPrice
  simp only [primeAtom,ite_mul,zero_mul,←sum_filter]
  have he : (Icc 1 K).filter Nat.Prime = ordinaryPrimeLags K := by
    ext k
    simp only [ordinaryPrimeLags,mem_filter,mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.two_le,h.1.2⟩,h.2⟩,fun h => ⟨⟨h.2.pos,h.1.2⟩,h.2⟩⟩
  rw [he]
  exact congrArg (fun t : ℝ => (n:ℝ)^2*t) (sum_congr rfl fun q hq => by
    rw [vonMangoldt_apply_prime (mem_filter.mp hq).2])

/-- A sharp quadratic divider gives two literal complementary endpoint sums,
including the far product horizon on the upper side. -/
theorem primeEndpoint_quadratic_divider {n K : ℕ} (hK : 2 ≤ K) (hL : K ≤ splineHorizon n) :
    lowerPrimeEndpointPrice n K + (n:ℝ)^2*retainedPrimeEndpoint K n =
      lowerPrimeEndpointPrice n (splineHorizon n) := by
  let S := ordinaryPrimeLags (splineHorizon n)
  let f (q : ℕ) := vonMangoldt q*sampledSpline n q
  have hset : S.filter (· ≤ K) = ordinaryPrimeLags K := by
    ext q
    simp only [S,ordinaryPrimeLags,mem_filter,mem_Icc]
    constructor
    · rintro ⟨⟨⟨h,_⟩,hp⟩,hu⟩
      exact ⟨⟨h,hu⟩,hp⟩
    · rintro ⟨⟨h,hu⟩,hp⟩
      exact ⟨⟨⟨h,hu.trans hL⟩,hp⟩,hu⟩
  have hu : retainedPrimeEndpoint K n = ∑ q ∈ S.filter (fun q => ¬q ≤ K), f q := by
    simp only [not_le]
    apply sum_congr rfl
    intro q hq
    have hm := mem_filter.mp hq
    simp only [f,clippedFirstEndpoint_eq (hK.trans_lt hm.2) (mem_Icc.mp (mem_filter.mp hm.1).1).2]
  rw [lower_price_prime_sum,lower_price_prime_sum,hu,←mul_add,←hset]
  exact congrArg (fun t : ℝ => (n:ℝ)^2*t) (sum_filter_add_sum_filter_not S (· ≤ K) f)

private theorem primeAtom_error (K : ℕ) :
    (∑ k ∈ Icc 1 K, (primeAtom k-1)) = Chebyshev.theta K-K := by
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,mul_one]
  congr 1
  unfold Chebyshev.theta
  rw [Nat.floor_natCast,show Ioc 0 K = Icc 1 K by ext k; simp only [mem_Icc,mem_Ioc]; omega]
  simp only [primeAtom,←sum_filter]

/-- The exact signed prime error at a sharp divider. It occurs with the
opposite sign when the neighboring product interval is restored. -/
theorem lowerPrimeEndpointPrice_abel (n K : ℕ) :
    lowerPrimeEndpointPrice n K - (n:ℝ)^2*(∑ k ∈ Icc 1 K, sampledSpline n k) =
      (n:ℝ)^2*((∑ k ∈ Icc 1 K, (Chebyshev.theta k-k)*
        (sampledSpline n k-sampledSpline n (k+1))) +
        (Chebyshev.theta K-K)*sampledSpline n (K+1)) := by
  rw [lowerPrimeEndpointPrice,←mul_sub,←sum_sub_distrib]
  have h := _root_.HTGeometry.sum_mul_eq_partial_mul_diff_ring (fun k => primeAtom k-1) (sampledSpline n) K
  simp only [primeAtom_error] at h
  rw [←h]
  exact congrArg (fun t : ℝ => (n:ℝ)^2*t) (sum_congr rfl fun k _ => by ring)

private theorem theta_error_above_abscissa {b : ℝ} (hbnd : zeroReSup < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |Chebyshev.theta k-k| ≤ C*(k:ℝ)^b := by
  obtain ⟨A,hA,ha⟩ := exists_abs_chebyshevPsi_sub_le_rpow hbnd
  have hhalf := half_le_zeroReSup.trans_lt hbnd
  have hbpos : 0 < b := lt_trans (by norm_num : (0:ℝ)<1/2) hhalf
  obtain ⟨B,hb⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨A+|B|,by positivity,fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Chebyshev.theta, Real.zero_rpow hbpos.ne']
  have h1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hs : Real.sqrt k ≤ (k:ℝ)^b := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le h1 hhalf.le
  have hp := (hb k).trans (mul_le_mul (le_abs_self B) hs (Real.sqrt_nonneg _) (abs_nonneg _))
  have he := ha k h1
  rw [abs_le] at he ⊢
  have hpos := mul_nonneg (abs_nonneg B) (Real.rpow_nonneg (Nat.cast_nonneg k) b)
  constructor <;> linarith only [he.1,he.2,hp,Chebyshev.theta_le_psi (k:ℝ),hpos]

private theorem current_prime_abscissa : zeroReSup < 8/9 := by
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun q => by
    by_contra! hq
    exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hq
      (riemannZeta_eq_zero_of_xiZeroCopy q)
  linarith only [hΘ]

private theorem theta_error_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |Chebyshev.theta k-k| ≤ C*(k:ℝ)^(8/9:ℝ) :=
  theta_error_above_abscissa current_prime_abscissa

private theorem divider_spline_regular : HasCompactSupport dyadicSpline ∧ ContDiff ℝ 1 dyadicSpline :=
  ⟨HasCompactSupport.intro isCompact_Icc (fun _ hx => dyadicSpline_eq_zero_outside hx),
    contDiff_six_dyadicSpline.of_le (by norm_num)⟩

/-- The first prime moment through the fixed terminal cut. Partial summation
keeps the prime-count error at K as well as its interior sum. -/
private theorem prime_moment_above_abscissa {b : ℝ} (hbnd : zeroReSup < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 0 < K →
      |(∑ p ∈ ordinaryPrimeLags K, (p:ℝ)*Real.log p) - (K:ℝ)*((K:ℝ)+1)/2| ≤
        C*(K:ℝ)^(1+b) := by
  obtain ⟨C,hC,hθ⟩ := theta_error_above_abscissa hbnd
  have hb : 0 ≤ b := (by norm_num : (0:ℝ)≤1/2).trans (half_le_zeroReSup.trans hbnd.le)
  refine ⟨3*C,by positivity,fun K hK => ?_⟩
  have hn : 1 ≤ (K:ℝ) := by exact_mod_cast hK
  let B := C*(K:ℝ)^b
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have herr (j : ℕ) (hj : j ≤ K) : |Chebyshev.theta j-j| ≤ B :=
    (hθ j).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hj)
      hb) hC)
  have hd (m : ℕ) : (∑ p ∈ Icc 1 m, (p:ℝ)) = (m:ℝ)*(m+1)/2 := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_Icc_succ_top (by omega : 1 ≤ m+1),ih]; push_cast; ring
  have hpr : (Icc 1 K).filter Nat.Prime = ordinaryPrimeLags K := by
    ext p
    simp only [ordinaryPrimeLags,mem_filter,mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.two_le,h.1.2⟩,h.2⟩,fun h => ⟨⟨h.2.pos,h.1.2⟩,h.2⟩⟩
  have ha : (∑ p ∈ Icc 1 K, primeAtom p*(p:ℝ)) =
      ∑ p ∈ ordinaryPrimeLags K, (p:ℝ)*Real.log p := by
    simp only [primeAtom,ite_mul,zero_mul,←sum_filter,hpr]
    exact sum_congr rfl fun _ _ => mul_comm ..
  rw [←ha,←hd K,←sum_sub_distrib]
  rw [sum_congr rfl (fun p _ => show primeAtom p*(p:ℝ)-p=(primeAtom p-1)*p by ring),
    _root_.HTGeometry.sum_mul_eq_partial_mul_diff_ring (fun p => primeAtom p-1) (fun p : ℕ => (p:ℝ)),
    primeAtom_error]
  simp only [primeAtom_error,Nat.cast_add,Nat.cast_one,
    show ∀ x : ℝ, x-(x+1) = -1 by intro x; ring,mul_neg_one]
  apply (abs_add_le _ _).trans
  have hsum : |∑ p ∈ Icc 1 K, -(Chebyshev.theta p-p)| ≤ (K:ℝ)*B := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _p ∈ Icc 1 K, B := sum_le_sum fun p hp => (abs_neg _).trans_le (herr p (mem_Icc.mp hp).2)
         _ = _ := by rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
  rw [abs_mul,abs_of_nonneg (show 0 ≤ (K:ℝ)+1 by positivity)]
  apply (add_le_add hsum (mul_le_mul_of_nonneg_right (herr K le_rfl) (by positivity))).trans
  rw [Real.rpow_add (zero_lt_one.trans_le hn),Real.rpow_one]
  have hscale := le_mul_of_one_le_left hB hn
  dsimp only [B] at hscale ⊢
  linarith only [hscale]

/-- A numerical first-moment error from the ordinary prime strip. -/
theorem first_prime_moment_at_cut :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 0 < K →
      |(∑ p ∈ ordinaryPrimeLags K, (p:ℝ)*Real.log p) - (K:ℝ)*((K:ℝ)+1)/2| ≤
        C*(K:ℝ)^(17/9:ℝ) := by
  simpa only [show (1:ℝ)+8/9=17/9 by norm_num] using prime_moment_above_abscissa current_prime_abscissa

/-- The first prime moment has a width-dependent error at the actual zero
abscissa. After a subquadratic change of scale this error has a strict gap
below the price exponent. -/
theorem first_prime_moment_at_width :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 0 < K →
      |(∑ p ∈ ordinaryPrimeLags K, (p:ℝ)*Real.log p) - (K:ℝ)*((K:ℝ)+1)/2| ≤
        C*(K:ℝ)^(1+(1/2+GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth+1/36)) := by
  apply prime_moment_above_abscissa
  have h := zeroReSup_le_of_forall_re_le fun q =>
    re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q)
  rw [GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  linarith only [h]

/-- Density quadrature uniform in the dividing product, including the final mesh cell. -/
private theorem divider_density : ∃ B : ℝ, 0 ≤ B ∧ ∀ {n K : ℕ}, 0 < n → K ≤ splineHorizon n →
    |(∑ k ∈ Icc 1 K, sampledSpline n k) - n*(∫ t in (0:ℝ)..(K:ℝ)/(n:ℝ)^2, dyadicSpline t)| ≤ B/n := by
  obtain ⟨D,hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport divider_spline_regular.1 divider_spline_regular.2 one_ne_zero
  obtain ⟨A,_,hwin⟩ := successorSquare_window_bound
  refine ⟨(D:ℝ)*A^2,by positivity,fun {n K} hn hK => ?_⟩
  let h := ((n:ℝ)^2)⁻¹
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hh : 0<h := inv_pos.mpr (sq_pos_of_pos hn')
  let F := ∑ i ∈ range K, dyadicSpline (((i:ℝ)+1)*h)
  let I := ∫ t in (0:ℝ)..(K:ℝ)*h, dyadicSpline t
  have hmesh : (K:ℝ)*h ≤ A^2 := by
    rw [show (K:ℝ)*h=(K:ℝ)/(n:ℝ)^2 from (div_eq_mul_inv ..).symm]
    apply (div_le_iff₀ (sq_pos_of_pos hn')).mpr
    exact (Nat.cast_le.mpr hK).trans ((hwin hn).trans_eq (mul_pow ..))
  have hq := _root_.RHTower.abs_riemannSum_sub_integral_le (T := K*h) hD.lipschitzOnWith
    divider_spline_regular.2.continuous.continuousOn K hh.le le_rfl
  change |h*F-I| ≤ (D:ℝ)*K*h^2 at hq
  have hquant : |h*F-I| ≤ (D:ℝ)*A^2*h := hq.trans <| calc
    (D:ℝ)*K*h^2 = ((D:ℝ)*((K:ℝ)*h))*h := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmesh D.coe_nonneg) hh.le
  have he : (∑ k ∈ Icc 1 K, sampledSpline n k) = F/n := by
    rw [show Icc 1 K = Ico 1 (K+1) by ext k; simp, sum_Ico_eq_sum_range]
    simp only [F,Nat.add_sub_cancel,sampledSpline,Nat.cast_add,Nat.cast_one,
      div_eq_mul_inv,h,add_comm (1:ℝ),sum_mul]
  rw [he,div_eq_mul_inv (K:ℝ)]
  change |F/n-n*I| ≤ _
  have hsplit : F/n-n*I = n*(h*F-I) := by dsimp only [h]; field_simp
  rw [hsplit,abs_mul,abs_of_pos hn']
  exact (mul_le_mul_of_nonneg_left hquant hn'.le).trans_eq (by dsimp only [h]; field_simp <;> ring)

/-- The quartic density on a partial product range, with a uniform power
saving for every sharp divider in the original finite horizon. -/
theorem lowerPrimeEndpointPrice_density :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n K : ℕ}, 0 < n → K ≤ splineHorizon n →
      |lowerPrimeEndpointPrice n K - (n:ℝ)^3*
        (∫ t in (0:ℝ)..(K:ℝ)/(n:ℝ)^2, dyadicSpline t)| ≤ C*(n:ℝ)^(1+16/9:ℝ) := by
  obtain ⟨A,hA,hwin⟩ := successorSquare_window_bound
  obtain ⟨B,hB,hθ⟩ := theta_error_uniform
  obtain ⟨D,_,hD,_,hd⟩ := sampledSpline_differences
  obtain ⟨S,hs⟩ := divider_spline_regular.1.exists_bound_of_continuous divider_spline_regular.2.continuous
  obtain ⟨J,hJ,hj⟩ := divider_density
  have hS := (norm_nonneg _).trans (hs 0)
  have hA0 := zero_le_one.trans hA
  let T := B*A^(16/9:ℝ)
  have hT : 0 ≤ T := mul_nonneg hB (Real.rpow_nonneg hA0 _)
  refine ⟨T*(A^2*D+S)+J,by positivity,fun {n K} hn hK => ?_⟩
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn' := zero_lt_one.trans_le hn1
  let X := (n:ℝ)^(16/9:ℝ)
  have hX : 1 ≤ X := Real.one_le_rpow hn1 (by norm_num)
  have hX0 := zero_le_one.trans hX
  have hcount (k : ℕ) (hk : k ≤ K) : |Chebyshev.theta k-k| ≤ T*X := by
    have hk' := (Nat.cast_le.mpr (hk.trans hK)).trans (hwin hn)
    have hr := Real.rpow_le_rpow (Nat.cast_nonneg k) hk' (by norm_num : (0:ℝ)≤8/9)
    rw [←Real.rpow_two,←Real.rpow_mul (mul_nonneg hA0 hn'.le),show (2:ℝ)*(8/9)=16/9 by norm_num,
      Real.mul_rpow hA0 hn'.le] at hr
    exact (hθ k).trans ((mul_le_mul_of_nonneg_left hr hB).trans_eq (by dsimp only [T,X]; ring))
  have hE : |∑ k ∈ Icc 1 K, (Chebyshev.theta k-k)*(sampledSpline n k-sampledSpline n (k+1))|
      ≤ (A*n)^2*((T*X)*(D/(n:ℝ)^3)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _k ∈ Icc 1 K, (T*X)*(D/(n:ℝ)^3) := by
              apply sum_le_sum
              intro k hk
              rw [abs_mul]
              exact mul_le_mul (hcount k (mem_Icc.mp hk).2) ((hd hn k).1) (abs_nonneg _) (by positivity)
         _ ≤ _ := by
              rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
              exact mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hK).trans (hwin hn)) (by positivity)
  have hsample : |sampledSpline n (K+1)| ≤ S/n := by
    rw [sampledSpline,abs_div,abs_of_pos hn']
    exact div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hs _) hn'.le
  have hfar : |(Chebyshev.theta K-K)*sampledSpline n (K+1)| ≤ (T*X)*(S/n) := by
    rw [abs_mul]; exact mul_le_mul (hcount K le_rfl) hsample (abs_nonneg _) (by positivity)
  let I := ∫ t in (0:ℝ)..(K:ℝ)/(n:ℝ)^2, dyadicSpline t
  let Z := ∑ k ∈ Icc 1 K, sampledSpline n k
  have he : lowerPrimeEndpointPrice n K-(n:ℝ)^3*I =
      (lowerPrimeEndpointPrice n K-(n:ℝ)^2*Z)+(n:ℝ)^2*(Z-n*I) := by ring
  have herr := (abs_add_le _ _).trans (add_le_add hE hfar)
  change |lowerPrimeEndpointPrice n K-(n:ℝ)^3*I| ≤ _
  rw [he]
  apply (abs_add_le _ _).trans
  dsimp only [Z,I]
  rw [lowerPrimeEndpointPrice_abel,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]
  apply (add_le_add (mul_le_mul_of_nonneg_left herr (sq_nonneg (n:ℝ)))
    (mul_le_mul_of_nonneg_left (hj hn hK) (sq_nonneg (n:ℝ)))).trans
  have hmul := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hJ hX) hn'.le
  rw [Real.rpow_add hn',Real.rpow_one]
  change _ ≤ (T*(A^2*D+S)+J)*(n*X)
  calc _ = T*(A^2*D+S)*(n*X)+n*J := by field_simp
       _ ≤ _ := by linarith only [hmul]

/-- At the whole horizon the density vanishes at the quadrature scale. Both
complementary sharp readings therefore have opposite leading coefficients. -/
theorem upperPrimeEndpointPrice_density :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n K : ℕ}, 0 < n → 2 ≤ K → K ≤ splineHorizon n →
      |(n:ℝ)^2*retainedPrimeEndpoint K n + (n:ℝ)^3*
        (∫ t in (0:ℝ)..(K:ℝ)/(n:ℝ)^2, dyadicSpline t)| ≤ C*(n:ℝ)^(1+16/9:ℝ) := by
  obtain ⟨C,hC,hcut⟩ := lowerPrimeEndpointPrice_density
  obtain ⟨A,hA,ha⟩ := sampledSpline_density
  obtain ⟨B,hB,hb⟩ := divider_density
  refine ⟨2*C+(A+B),by positivity,fun {n K} hn hK hL => ?_⟩
  let L := splineHorizon n
  let I (j : ℕ) := ∫ t in (0:ℝ)..(j:ℝ)/(n:ℝ)^2, dyadicSpline t
  let X := (n:ℝ)^(1+16/9:ℝ)
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hpow : (n:ℝ) ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hn : 1 ≤ (n:ℝ)) (by norm_num : (1:ℝ) ≤ 1+16/9)
  let S := ∑ k ∈ Icc 1 L, sampledSpline n k
  have hS : |S| ≤ A/n := ha hn
  have hSL : |S-n*I L| ≤ B/n := hb hn le_rfl
  have hI : |n*I L| ≤ (A+B)/n := by
    rw [show n*I L=S-(S-n*I L) by ring,add_div]
    exact (abs_sub _ _).trans (add_le_add hS hSL)
  have hmain : |(n:ℝ)^3*I L| ≤ (A+B)*X := by
    rw [show (n:ℝ)^3*I L=(n:ℝ)^2*(n*I L) by ring,abs_mul,abs_of_nonneg (sq_nonneg (n:ℝ))]
    apply (mul_le_mul_of_nonneg_left hI (sq_nonneg (n:ℝ))).trans
    calc _ = (A+B)*n := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left hpow (add_nonneg hA hB)
  have hfull : |lowerPrimeEndpointPrice n L| ≤ C*X+(A+B)*X := by
    have he : lowerPrimeEndpointPrice n L =
        (lowerPrimeEndpointPrice n L-(n:ℝ)^3*I L)+(n:ℝ)^3*I L := by ring
    calc _ = |(lowerPrimeEndpointPrice n L-(n:ℝ)^3*I L)+(n:ℝ)^3*I L| := congrArg abs he
         _ ≤ _ := (abs_add_le _ _).trans (add_le_add (hcut hn le_rfl) hmain)
  have hm := primeEndpoint_quadratic_divider (n := n) hK hL
  have he : (n:ℝ)^2*retainedPrimeEndpoint K n+(n:ℝ)^3*I K =
      lowerPrimeEndpointPrice n L-(lowerPrimeEndpointPrice n K-(n:ℝ)^3*I K) := by
    change _ = lowerPrimeEndpointPrice n (splineHorizon n)-_
    rw [←hm]; ring
  change |(n:ℝ)^2*retainedPrimeEndpoint K n+(n:ℝ)^3*I K| ≤ _
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hfull (hcut hn hL)).trans_eq (by dsimp only [X]; ring))

#print axioms lowerPrimeEndpointPrice_abel
#print axioms first_prime_moment_at_cut
#print axioms first_prime_moment_at_width
#print axioms lowerPrimeEndpointPrice_density
#print axioms upperPrimeEndpointPrice_density
#print axioms primeEndpoint_quadratic_divider
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
