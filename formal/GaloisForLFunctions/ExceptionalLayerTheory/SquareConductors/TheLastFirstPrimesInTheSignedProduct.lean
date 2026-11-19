import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFiniteMeshAtAnOrdinaryFirstPrime
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheLastTwoQuotientCellsOfTheSpline
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMassOnADilatedSpline
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSeventeenNinthsConductorPrefix

/-!
# A quadratic band in the actual first-prime sum

Near the last prime with a nonzero cofactor, only cofactor two and outer
quotient one survive. The coefficient and the spline are both negative,
so every surviving prime contributes positively.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticWeightTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private abbrev R : ℝ := 4*Real.exp 8

/-- The contribution of the actual first primes in the sharp quadratic band,
including the moving cofactor cap, coprimality test and original lower product. -/
def upperFirstPrimeBandPrice (n : ℕ) : ℝ :=
  let U := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  let a := ⌊upperFirstPrimeBandLeft*(n:ℝ)^2⌋₊
  let b := ⌊upperFirstPrimeBandRight*(n:ℝ)^2⌋₊
  (n:ℝ)^2*(firstPrimeReadingAbove a U n-firstPrimeReadingAbove b U n)

/-- Every late member of the band is an ordinary first prime above both
geometric cuts. Only cofactor two at the first positive quotient contributes. -/
theorem upper_first_prime_band_exact :
    ∀ᶠ n : ℕ in atTop, upperFirstPrimeBandPrice n =
      (n:ℝ)*((1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1)*
        ∑ p ∈ (Ioc ⌊upperFirstPrimeBandLeft*(n:ℝ)^2⌋₊
          ⌊upperFirstPrimeBandRight*(n:ℝ)^2⌋₊).filter Nat.Prime,
          Real.log p*dyadicSpline (2*((p:ℝ)/(n:ℝ)^2)) := by
  obtain ⟨K,hK,hcut⟩ := capFreeFirstPrimeCut_linear
  have he := Real.one_le_exp (show (0:ℝ)≤8 by norm_num)
  have ha : 1≤upperFirstPrimeBandLeft := by dsimp only [upperFirstPrimeBandLeft]; linarith only [he]
  have hab : upperFirstPrimeBandLeft≤upperFirstPrimeBandRight := by
    dsimp only [upperFirstPrimeBandLeft,upperFirstPrimeBandRight]; linarith only [he]
  have hbR : 2*upperFirstPrimeBandRight<R := by dsimp only [upperFirstPrimeBandRight,R]; linarith only [he]
  filter_upwards [eventually_ge_atTop (max 4 ⌈K⌉₊)] with n hn
  have hn4 := (le_max_left 4 _).trans hn
  have hn1 : 0<n := by omega
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn1
  have hsq : 0<(n:ℝ)^2 := sq_pos_of_pos hn'
  let L := splineHorizon n
  let A := ⌊upperFirstPrimeBandLeft*(n:ℝ)^2⌋₊
  let B := ⌊upperFirstPrimeBandRight*(n:ℝ)^2⌋₊
  let U := ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  have hAB : A≤B := Nat.floor_mono (mul_le_mul_of_nonneg_right hab hsq.le)
  have hk : K≤(n:ℝ) := (Nat.le_ceil K).trans (Nat.cast_le.mpr ((le_max_right _ _).trans hn))
  have hNA : (n:ℝ)^2≤upperFirstPrimeBandLeft*(n:ℝ)^2 := le_mul_of_one_le_left hsq.le ha
  have hF : capFreeFirstPrimeCut n ≤ A := Nat.le_floor ((hcut hn1).trans
    ((mul_le_mul_of_nonneg_right hk hn'.le).trans ((le_of_eq (pow_two (n:ℝ)).symm).trans hNA)))
  have hncut : n ≤ capFreeFirstPrimeCut n := le_max_left _ _
  have huA : U≤A := Nat.floor_mono (by
    have h := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn1) (by norm_num : (17/9:ℝ)≤2)
    rw [Real.rpow_two] at h
    exact h.trans hNA)
  have hgeom := (positive_mesh_reaches_support hn1 (p := 1) (by decide)).1
  have hL : R*(n:ℝ)^2 < (L:ℝ)+1 := by
    apply (lt_div_iff₀ hsq).mp
    simpa only [L,Nat.cast_one,Nat.cast_add,div_eq_mul_inv,one_mul] using hgeom
  have hB : B ≤ L := Nat.le_of_lt_succ ((Nat.floor_lt (mul_nonneg (zero_le_one.trans (ha.trans hab)) hsq.le)).mpr (by
    push_cast
    exact (mul_le_mul_of_nonneg_right (by linarith only [hbR,ha,hab] : upperFirstPrimeBandRight≤R) hsq.le).trans_lt hL))
  have hb₂ : 2≤L+1 := by
    have := hn4.trans (hncut.trans (hF.trans (hAB.trans hB))); omega
  change (n:ℝ)^2*(firstPrimeReadingAbove A U n-firstPrimeReadingAbove B U n)=_
  rw [firstPrimeReadingAbove_eq_unrestricted hF,firstPrimeReadingAbove_eq_unrestricted (hF.trans hAB),
    first_prime_mesh_band hn1 hAB U,max_eq_right (hn4.trans (hncut.trans hF)),min_eq_left hB]
  conv_rhs => rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  obtain ⟨ht,hp'⟩ := mem_filter.mp hp
  obtain ⟨hpA,hpB⟩ := mem_Ioc.mp ht
  have hp0 := hp'.pos
  let h := (p:ℝ)/(n:ℝ)^2
  have h0 : 0<h := div_pos (Nat.cast_pos.mpr hp0) hsq
  have hl : upperFirstPrimeBandLeft≤h := (le_div_iff₀ hsq).mpr
    ((Nat.floor_lt (mul_nonneg (zero_le_one.trans ha) hsq.le)).mp hpA).le
  have hu : h≤upperFirstPrimeBandRight := (div_le_iff₀ hsq).mpr
    ((Nat.cast_le.mpr hpB).trans (Nat.floor_le (mul_nonneg (zero_le_one.trans (ha.trans hab)) hsq.le)))
  have hm : 2≤L/p := by
    by_contra! hs
    have h := (positive_mesh_reaches_support hn1 hp0).2
    have hcap : ((L/p+1:ℕ):ℝ)≤2 := by exact_mod_cast (show L/p+1≤2 by omega)
    have hsmall := mul_le_mul_of_nonneg_right hcap h0.le
    exact (h.trans_le (hsmall.trans (mul_le_mul_of_nonneg_left hu (by norm_num)))).not_ge hbR.le
  have h3 : 4*Real.exp 8 < 3*h := by
    dsimp only [upperFirstPrimeBandLeft] at hl
    linarith only [hl,Real.exp_pos 8]
  change vonMangoldt p*((n:ℝ)*∑ v ∈ Ioc (U/p) (L/p),
    innerJump 1 v*positiveCofactorProfile (L+1) h v) =
    (n:ℝ)*((1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1)*(Real.log p*dyadicSpline (2*h))
  rw [Nat.div_eq_of_lt (huA.trans_lt hpA),last_first_prime_cofactor hb₂ hm h3,vonMangoldt_apply_prime hp']
  ring

/-- Signed density of the full sharp band, in the doubled spline coordinate. -/
def upperFirstPrimeBandDensity : ℝ :=
  ((1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1/2)*
    ∫ t in 2*upperFirstPrimeBandLeft..2*upperFirstPrimeBandRight, dyadicSpline t

theorem upper_first_prime_band_density_pos : 0<upperFirstPrimeBandDensity := by
  let a := 2*upperFirstPrimeBandLeft
  let b := 2*upperFirstPrimeBandRight
  have hab : a<b := by
    dsimp only [a,b,upperFirstPrimeBandLeft,upperFirstPrimeBandRight]
    linarith only [Real.exp_pos 8]
  obtain ⟨c,hc,hf⟩ := last_first_prime_spline_margin
  have hi : (∫ t in a..b, dyadicSpline t) ≤ ∫ _t in a..b, -c := by
    apply intervalIntegral.integral_mono_on hab.le (contDiff_six_dyadicSpline.continuous.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b)
    intro x hx
    obtain ⟨hl,hr⟩ := hx
    dsimp only [a,b] at hl hr
    have ht := hf (by linarith only [hl] : upperFirstPrimeBandLeft≤x/2)
      (by linarith only [hr] : x/2≤upperFirstPrimeBandRight)
    rw [show 2*(x/2)=x by ring] at ht
    linarith only [ht]
  rw [intervalIntegral.integral_const,smul_eq_mul] at hi
  exact mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg first_even_cofactor_positive first_centered_quotient_negative) two_pos)
    (hi.trans_lt (mul_neg_of_pos_of_neg (sub_pos.mpr hab) (neg_lt_zero.mpr hc)))

/-- The sharp band has an explicit positive cubic term per conductor.
Its ordinary-prime discrepancy is of strictly lower order. -/
theorem upper_first_prime_band_asymptotic :
    ∃ D : ℝ, 0≤D ∧ ∀ᶠ n : ℕ in atTop,
      |upperFirstPrimeBandPrice n-upperFirstPrimeBandDensity*(n:ℝ)^3|≤D*(n:ℝ)^(25/9:ℝ) := by
  let a := upperFirstPrimeBandLeft
  let b := upperFirstPrimeBandRight
  let w := (1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1
  let I (t : ℝ) := ∫ x in (0:ℝ)..2*t, dyadicSpline x
  have ha : 0<a := by dsimp only [a,upperFirstPrimeBandLeft]; positivity
  have hb : 0<b := by dsimp only [b,upperFirstPrimeBandRight]; positivity
  have hab : a≤b := by
    dsimp only [a,b,upperFirstPrimeBandLeft,upperFirstPrimeBandRight]
    linarith only [Real.exp_pos 8]
  have hi : I a+(∫ t in 2*a..2*b, dyadicSpline t)=I b := intervalIntegral.integral_add_adjacent_intervals
    (contDiff_six_dyadicSpline.continuous.intervalIntegrable 0 (2*a))
    (contDiff_six_dyadicSpline.continuous.intervalIntegrable (2*a) (2*b))
  have hD : upperFirstPrimeBandDensity=w/2*(I b-I a) := by
    unfold upperFirstPrimeBandDensity
    apply congrArg (fun t : ℝ => w/2*t)
    change (∫ t in 2*a..2*b, dyadicSpline t)=I b-I a
    linarith only [hi]
  obtain ⟨A,hA,ea⟩ := doubled_prime_spline_at_quadratic_cut ha
  obtain ⟨B,hB,eb⟩ := doubled_prime_spline_at_quadratic_cut hb
  refine ⟨|w| * (B+A),by positivity,?_⟩
  filter_upwards [upper_first_prime_band_exact,eventually_ge_atTop (1:ℕ)] with n he hn
  let d := 2/(n:ℝ)^2
  let P (t : ℝ) := primeSplineSamples d ⌊t*(n:ℝ)^2⌋₊
  let E (t : ℝ) := P t-((n:ℝ)^2/2)*I t
  have hs (p : ℕ) : 2*((p:ℝ)/(n:ℝ)^2) = p*d := by dsimp only [d]; ring
  simp_rw [hs] at he
  rw [prime_spline_band (Nat.floor_mono (mul_le_mul_of_nonneg_right hab (sq_nonneg (n:ℝ))))] at he
  change upperFirstPrimeBandPrice n=n*w*(P b-P a) at he
  have hE : |E b-E a|≤(B+A)*(n:ℝ)^(16/9:ℝ) :=
    (abs_sub _ _).trans ((add_le_add (eb hn) (ea hn)).trans_eq (by ring))
  have hp : (n:ℝ)*(n:ℝ)^(16/9:ℝ)=(n:ℝ)^(25/9:ℝ) := by
    rw [show (25/9:ℝ)=16/9+1 by norm_num,Real.rpow_add_one (Nat.cast_pos.mpr hn).ne']
    exact mul_comm _ _
  rw [he,hD,show n*w*(P b-P a)-w/2*(I b-I a)*(n:ℝ)^3=n*w*(E b-E a) by dsimp only [E]; ring,
    abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
  exact (mul_le_mul_of_nonneg_left hE (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg w))).trans_eq
    (by rw [←hp]; ring)

/-- The original signed band has a strictly positive cubic price per late conductor. -/
theorem upper_first_prime_band_cubic_lower :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^3 ≤ upperFirstPrimeBandPrice n := by
  let C := upperFirstPrimeBandDensity/2
  have hC : 0<C := half_pos upper_first_prime_band_density_pos
  obtain ⟨D,_,h⟩ := upper_first_prime_band_asymptotic
  have hg := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/9)).comp tendsto_natCast_atTop_atTop
  refine ⟨C,hC,?_⟩
  filter_upwards [h,hg.eventually_ge_atTop (D/C),eventually_ge_atTop (1:ℕ)] with n hn hgrow hn1
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn1
  change D/C≤(n:ℝ)^(2/9:ℝ) at hgrow
  have hsmall : D*(n:ℝ)^(25/9:ℝ)≤C*(n:ℝ)^3 := by
    have hd := (div_le_iff₀ hC).mp hgrow
    apply (mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hn'.le _)).trans_eq
    calc _ = C*((n:ℝ)^(2/9:ℝ)*(n:ℝ)^(25/9:ℝ)) := by ring
         _ = _ := by rw [←Real.rpow_add hn',show (2/9:ℝ)+25/9=(3:ℕ) by norm_num,Real.rpow_natCast]
  have e := (abs_le.mp hn).1
  dsimp only [C] at hsmall ⊢
  linarith only [hsmall,e]

/-- Each late partial octave inherits the lower bound at every terminal.
On the complete octave its magnitude is at least a positive multiple of N⁴. -/
theorem upper_first_prime_band_octave_lower :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N≤M →
      C*(M-N:ℕ)*(N:ℝ)^3 ≤ ∑ n ∈ Ioc N M, upperFirstPrimeBandPrice n := by
  obtain ⟨C,hC,h⟩ := upper_first_prime_band_cubic_lower
  obtain ⟨K,hK⟩ := eventually_atTop.mp h
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop K] with N hN
  intro M _
  calc _ = ∑ _n ∈ Ioc N M, C*(N:ℝ)^3 := by rw [sum_const,Nat.card_Ioc,nsmul_eq_mul]; ring
       _ ≤ _ := by
         apply sum_le_sum
         intro n hn
         have hNn := (mem_Ioc.mp hn).1.le
         exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N)
           (Nat.cast_le.mpr hNn) 3) hC.le).trans (hK n (hN.trans hNn))

/-- The ordinary prime strip already forces negative quartic compensation
in the complementary first primes on every complete late octave. -/
theorem upper_first_prime_band_complement_negative :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Ioc N (2*N), ((n:ℝ)^2*seventeenNinthsConductor n-upperFirstPrimeBandPrice n)) ≤
        -c*(N:ℝ)^4 := by
  have hw : zetaZeroWidth ≤ 3/8 := by
    apply (zetaZeroWidth_le_iff_re_le (by norm_num)).mpr
    intro z hz
    by_contra! h
    exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
      (by linarith only [h]) hz.1
  obtain ⟨A,hA,ha⟩ := (width_iff_seventeenNinthsConductorPrefix (by norm_num) (by norm_num)).mp hw
  rw [show 3+2*(3/8:ℝ)=15/4 by norm_num] at ha
  obtain ⟨C,hC,hc⟩ := upper_first_prime_band_octave_lower
  let D := A*((2:ℝ)^(15/4:ℝ)+1)
  have hg := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  refine ⟨C/2,half_pos hC,?_⟩
  filter_upwards [hc,hg.eventually_ge_atTop (D/(C/2)),eventually_ge_atTop (1:ℕ)] with N hN hlarge hN1
  have hn' : (0:ℝ)<N := Nat.cast_pos.mpr hN1
  change D/(C/2)≤(N:ℝ)^(1/4:ℝ) at hlarge
  have htot : ∑ n ∈ Ioc N (2*N), (n:ℝ)^2*seventeenNinthsConductor n =
      seventeenNinthsConductorPrefix (2*N)-seventeenNinthsConductorPrefix N := by
    let f := fun n : ℕ => (n:ℝ)^2*seventeenNinthsConductor n
    have e (m : ℕ) : seventeenNinthsConductorPrefix m=∑ n ∈ Ioc 0 m, f n := by
      change (∑ n ∈ Icc 1 m,f n)=_
      rw [show Icc 1 m=Ioc 0 m by ext n; simp only [mem_Icc,mem_Ioc]; omega]
    rw [e,e,←sum_Ioc_consecutive f (Nat.zero_le N) (by omega : N≤2*N),add_sub_cancel_left]
  have hsmall : D*(N:ℝ)^(15/4:ℝ) ≤ (C/2)*(N:ℝ)^4 := by
    have hd := (div_le_iff₀ (half_pos hC)).mp hlarge
    apply (mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hn'.le (15/4:ℝ))).trans_eq
    calc _ = (C/2)*((N:ℝ)^(1/4:ℝ)*(N:ℝ)^(15/4:ℝ)) := by ring
         _ = _ := by rw [←Real.rpow_add hn',show (1/4:ℝ)+15/4=(4:ℕ) by norm_num,Real.rpow_natCast]
  have hp := (abs_sub (seventeenNinthsConductorPrefix (2*N)) (seventeenNinthsConductorPrefix N)).trans
    (add_le_add (ha (2*N)) (ha N))
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) hn'.le] at hp
  have hp' := (le_abs_self _).trans (hp.trans_eq (show
    A*((2:ℝ)^(15/4:ℝ)*(N:ℝ)^(15/4:ℝ))+A*(N:ℝ)^(15/4:ℝ)=D*(N:ℝ)^(15/4:ℝ) by dsimp only [D]; ring))
  have hband := hN (2*N) (by omega)
  rw [show 2*N-N=N by omega] at hband
  rw [sum_sub_distrib,htot]
  linarith only [hp'.trans hsmall,hband]

#print axioms upper_first_prime_band_complement_negative
#print axioms upper_first_prime_band_octave_lower
#print axioms upper_first_prime_band_asymptotic
#print axioms upper_first_prime_band_density_pos
#print axioms upper_first_prime_band_cubic_lower
#print axioms upper_first_prime_band_exact
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
