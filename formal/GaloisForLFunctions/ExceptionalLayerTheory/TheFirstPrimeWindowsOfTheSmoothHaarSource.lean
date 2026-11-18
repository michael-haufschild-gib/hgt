import GaloisForLFunctions.ExceptionalLayerTheory.SmoothCountsAndTheLargeFactorsOfTheCentralBinomialCoefficient
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteDeletion
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount

/-!
# The first prime windows of the smooth Haar source

Before two primes above the cutoff can divide the same integer, the smooth
Haar source counts single large primes with odd quotient, up to the parity
of the endpoint. In the first doubling interval every such quotient is one.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem sum_smoothAF_eq_count (k y : ℕ) :
    (∑ n ∈ Icc 1 k, (CoprimeMobius.smoothAF (↑(Nat.primesLE y) : Set ℕ) n : ℂ)) =
      (smoothIntegerCount k y : ℂ) := by
  classical
  let E : Set ℕ := ↑(Nat.primesLE y)
  have he : (Icc 1 k).filter (CoprimeMobius.IsSmooth E) = Sieve.smoothUpTo (Nat.primesLE y) k := by
    ext n
    rw [mem_filter,Sieve.mem_smoothUpTo,mem_Icc]
    change ((1≤n ∧ n≤k) ∧ n≠0 ∧ n.primeFactors ⊆ Nat.primesLE y) ↔ _
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,Nat.ne_of_gt h.1.1,h.2⟩
  simp only [CoprimeMobius.smoothAF_apply,Int.cast_ite,Int.cast_one,Int.cast_zero]
  rw [← sum_filter,show (Icc 1 k).filter (CoprimeMobius.IsSmooth E)=_ from he]
  simp [smoothIntegerCount]

/-- The two smooth counts in the Haar source use the same integer endpoint
before and after division by two. -/
theorem smoothHaarSource_count_floor (y : ℕ) {t : ℝ} (ht : 0<t) :
    pmSmoothHaarSource (y+1) t =
      (smoothIntegerCount ⌊1/t⌋₊ y:ℂ)-2*(smoothIntegerCount (⌊1/t⌋₊/2) y:ℂ) := by
  have hf : ⌊1/(2*t)⌋₊=⌊1/t⌋₊/2 := by
    rw [show 1/(2*t)=(1/t)/(2:ℕ) by push_cast; ring,Nat.floor_div_natCast]
  rw [pmSmoothHaarSource_eq_counts _ ht,hf]
  change (∑ n ∈ Icc 1 _, (CoprimeMobius.smoothAF (↑(Nat.primesLE y):Set ℕ) n:ℂ)) -
    2*(∑ n ∈ Icc 1 _, (CoprimeMobius.smoothAF (↑(Nat.primesLE y):Set ℕ) n:ℂ)) = _
  rw [sum_smoothAF_eq_count,sum_smoothAF_eq_count]

/-- On the square-root window the source is the endpoint parity minus the
number of large primes whose quotient is odd. -/
theorem smoothHaarSource_eq_large_prime_count (y : ℕ) {t : ℝ} (ht : 0<t)
    (hs : ⌊1/t⌋₊<(y+1)^2) :
    pmSmoothHaarSource (y+1) t = (⌊1/t⌋₊%2:ℕ) -
      (((largePrimes ⌊1/t⌋₊ y).filter (fun p => 2∣⌊1/t⌋₊/p+1)).card:ℂ) := by
  let k := ⌊1/t⌋₊
  let P := largePrimes k y
  have hk := count_smooth_and_multiples (y := y) (B := k) le_rfl hs
  have hd := count_smooth_and_multiples (y := y) (B := k) (Nat.div_le_self k 2)
    ((Nat.div_le_self k 2).trans_lt hs)
  have hcell (p : ℕ) : k/p=2*((k/2)/p)+(if 2∣k/p+1 then 1 else 0) := by
    have he : (k/2)/p=(k/p)/2 := by rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm 2 p]
    rw [he]
    split <;> omega
  have hsum : (∑ p ∈ P, k/p)=2*(∑ p ∈ P, (k/2)/p)+(P.filter (fun p => 2∣k/p+1)).card := by
    calc
      _ = ∑ p ∈ P, (2*((k/2)/p)+(if 2∣k/p+1 then 1 else 0)) := sum_congr rfl fun p _ => hcell p
      _ = _ := by rw [sum_add_distrib,← mul_sum,← sum_filter]; simp
  change _+ (∑ p ∈ P, _) = _ at hk hd
  rw [smoothHaarSource_count_floor y ht]
  change (smoothIntegerCount k y:ℂ)-2*(smoothIntegerCount (k/2) y:ℂ)=
    (k%2:ℕ)-(↑(P.filter (fun p => 2∣k/p+1)).card:ℂ)
  exact_mod_cast (show (smoothIntegerCount k y:ℤ)-2*(smoothIntegerCount (k/2) y:ℤ)=
    (k%2:ℕ)-(↑(P.filter (fun p => 2∣k/p+1)).card:ℤ) by omega)

/-- On the first doubling interval the smooth source recovers the entire
ordinary prime-count increment from the cutoff. -/
theorem smoothHaarSource_first_doubling (y : ℕ) {t : ℝ} (ht : 0<t)
    (hl : y≤⌊1/t⌋₊) (hu : ⌊1/t⌋₊≤2*y) :
    pmSmoothHaarSource (y+1) t = (⌊1/t⌋₊%2:ℕ)-
      ((Nat.primeCounting ⌊1/t⌋₊:ℂ)-(Nat.primeCounting y:ℂ)) := by
  let k := ⌊1/t⌋₊
  have hs : ⌊1/t⌋₊ < (y+1)^2 := by nlinarith only [hu,Nat.zero_le (y*y)]
  have hset : (largePrimes k y).filter (fun p => 2∣k/p+1) = Nat.primesLE k \ Nat.primesLE y := by
    apply Finset.ext
    intro p
    have he (hp : p≤k) (hy : y<p) : k/p=1 := by
      have hp0 : 0<p := Nat.zero_lt_of_lt hy
      have hlow := (Nat.one_le_div_iff hp0).mpr hp
      have hupper := (Nat.div_lt_iff_lt_mul hp0).mpr (show k<2*p by dsimp only [k]; omega)
      omega
    simp only [Finset.mem_filter,mem_largePrimes,Finset.mem_sdiff,Nat.mem_primesLE]
    constructor
    · exact fun h => ⟨h.1.1,fun hpy => h.1.2.not_ge hpy.1⟩
    · rintro ⟨hp,hpy⟩
      have hy : y<p := lt_of_not_ge (fun h => hpy ⟨h,hp.2⟩)
      exact ⟨⟨hp,hy⟩,by rw [he hp.1 hy]⟩
  rw [smoothHaarSource_eq_large_prime_count y ht hs]
  change (k%2:ℕ)-(↑((largePrimes k y).filter (fun p => 2∣k/p+1)).card:ℂ)=_
  rw [hset,card_sdiff_of_subset (Nat.primesLE_mono hl),Nat.cast_sub (card_le_card (Nat.primesLE_mono hl))]
  simp only [Nat.primesLE_card_eq_primeCounting,k]

/-- The whole fixed interval of primes between two and three times N has
quotient one at every endpoint from three to four times N. -/
theorem smoothHaarSource_outer_window {N y : ℕ} (hy : y≤2*N) (hs : 4*N<(y+1)^2)
    {t : ℝ} (ht : 0<t) (hl : 3*N≤⌊1/t⌋₊) (hu : ⌊1/t⌋₊≤4*N) :
    ((Nat.primeCounting (3*N):ℝ)-Nat.primeCounting (2*N)-1 ≤ -(pmSmoothHaarSource (y+1) t).re) ∧
    (-(pmSmoothHaarSource (y+1) t).re ≤ Nat.primeCounting (4*N)) := by
  let k := ⌊1/t⌋₊
  let A := (largePrimes k y).filter (fun p => 2∣k/p+1)
  have hP : Nat.primesLE (2*N) ⊆ Nat.primesLE (3*N) := Nat.primesLE_mono (by omega)
  have hlow : Nat.primesLE (3*N) \ Nat.primesLE (2*N) ⊆ A := by
    intro p hp
    obtain ⟨h₃,h₂⟩ := mem_sdiff.mp hp
    obtain ⟨hp₃,hpr⟩ := Nat.mem_primesLE.mp h₃
    have hp₂ : 2*N<p := lt_of_not_ge fun h => h₂ (Nat.mem_primesLE.mpr ⟨h,hpr⟩)
    have hpk : p≤k := hp₃.trans hl
    have hdiv : k/p=1 := by
      have hlo := (Nat.one_le_div_iff hpr.pos).mpr hpk
      have hhi := (Nat.div_lt_iff_lt_mul hpr.pos).mpr (show k<2*p by dsimp only [k]; omega)
      omega
    exact mem_filter.mpr ⟨mem_largePrimes.mpr ⟨⟨hpk,hpr⟩,hy.trans_lt hp₂⟩,by rw [hdiv]⟩
  have hupp : A ⊆ Nat.primesLE (4*N) := by
    intro p hp
    exact Nat.primesLE_mono hu (mem_filter.mp (mem_filter.mp hp).1).1
  have hc := card_le_card hlow
  rw [card_sdiff_of_subset hP] at hc
  have hcount := card_le_card hP
  simp only [Nat.primesLE_card_eq_primeCounting] at hc hcount
  have hu' := card_le_card hupp
  rw [Nat.primesLE_card_eq_primeCounting] at hu'
  have hlowR : (Nat.primeCounting (3*N):ℝ)-Nat.primeCounting (2*N)≤A.card := by
    rw [← Nat.cast_sub hcount]
    exact_mod_cast hc
  have hupperR : (A.card:ℝ)≤Nat.primeCounting (4*N) := by exact_mod_cast hu'
  have hmod : ((k%2:ℕ):ℝ)≤1 := by
    exact_mod_cast (show k%2≤1 by omega)
  have he : (pmSmoothHaarSource (y+1) t).re = ((k%2:ℕ):ℝ)-A.card := by
    rw [smoothHaarSource_eq_large_prime_count y ht (hu.trans_lt hs)]
    simp only [Complex.sub_re,Complex.natCast_re,k,A]
  rw [he]
  constructor <;> linarith only [hlowR,hupperR,hmod,Nat.cast_nonneg (α := ℝ) (k%2)]

/-- The prime logarithms dominate the number of selected large primes
throughout the square-root window. -/
private theorem haar_window_upper {y : ℕ} (hy : 2 ≤ y) {t : ℝ} (ht : 0<t)
    (hl : (y:ℝ) ≤ 1/t) (hu : 1/t ≤ (y:ℝ)^2) :
    ‖pmSmoothHaarSource (y+1) t‖ ≤ (Real.log 4+5)/(t*Real.log y) := by
  let k := ⌊1/t⌋₊
  let S := (largePrimes k y).filter (fun p => 2 ∣ k/p+1)
  have hlog := Real.log_pos (show (1:ℝ)<y by exact_mod_cast hy)
  have hk := Nat.floor_le (div_nonneg zero_le_one ht.le)
  change (k:ℝ) ≤ 1/t at hk
  have hks : k < (y+1)^2 := by
    have hb : (k:ℝ) < ((y+1:ℕ):ℝ)^2 := (hk.trans hu).trans_lt (by push_cast; nlinarith only [Nat.cast_nonneg (α := ℝ) y])
    exact_mod_cast hb
  have he : (S.card:ℝ)*Real.log y ≤ Chebyshev.theta k := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      _ = ∑ _ ∈ S, Real.log y := by simp
      _ ≤ ∑ p ∈ S, Real.log p := Finset.sum_le_sum fun p hp => Real.log_le_log
        (by positivity) (by exact_mod_cast (mem_largePrimes.mp (mem_filter.mp hp).1).2.le)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).1) (fun p hp _ =>
          Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
  have hpsi := (Chebyshev.theta_le_psi (k:ℝ)).trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg k))
  have hC : 0 ≤ Real.log 4+4 := by positivity
  have htC := mul_le_mul_of_nonneg_left hk hC
  have hylog : Real.log y ≤ 1/t := (Real.log_le_self (Nat.cast_nonneg _)).trans hl
  have hpar : ((k%2:ℕ):ℝ) ≤ 1 := by exact_mod_cast (show k%2 ≤ 1 by omega)
  have hpt := smoothHaarSource_eq_large_prime_count y ht hks
  change pmSmoothHaarSource (y+1) t = ((k%2:ℕ):ℂ)-(S.card:ℂ) at hpt
  rw [hpt]
  apply (norm_sub_le _ _).trans
  simp only [Complex.norm_natCast]
  apply (le_div_iff₀ (mul_pos ht hlog)).mpr
  have hp := mul_le_mul_of_nonneg_right hpar hlog.le
  have hsum : ((k%2:ℕ)+S.card:ℝ)*Real.log y ≤ (Real.log 4+5)*(1/t) := by
    rw [add_mul]
    linarith only [hp,hylog,he,hpsi,htC]
  have hmul := mul_le_mul_of_nonneg_right hsum ht.le
  field_simp [ht.ne'] at hmul
  linarith only [hmul]

/-- The fixed prime interval between 2N and 3N gives a lower bound
uniform in every cutoff of the next quarter of the square-root window. -/
private theorem eventually_outer_prime_gap :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)/(4*Real.log (4*N:ℕ)) ≤
      (Nat.primeCounting (3*N):ℝ)-Nat.primeCounting (2*N)-1 := by
  obtain ⟨R,hR,h⟩ := PrimeCells.exists_card_windowPrimes_div_ge (1:ℝ) (ε := 1/2) (by norm_num)
  have ht : Tendsto (fun N : ℕ => (4:ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hslow : ∀ᶠ x : ℝ in atTop, 16*Real.log x ≤ x := by
    have ho := Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ)<1/16)
    filter_upwards [ho,eventually_ge_atTop (1:ℝ)] with x hx h1
    change ‖Real.log x‖ ≤ 1/16*‖x‖ at hx
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg h1),Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans h1)] at hx
    linarith only [hx]
  filter_upwards [ht.eventually_ge_atTop R,(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 2,
    ht.eventually hslow,eventually_ge_atTop 1] with N hNR hlog hslow hN
  change 2 ≤ Real.log (4*(N:ℝ)) at hlog
  have hp : (0:ℝ)<N := by exact_mod_cast hN
  have hh := h (4*N) hNR 2 (by norm_num) (by norm_num) (4*N) (6*N) le_rfl
    (by linarith only [hp]) (by linarith only [hp]) (by
      rw [Real.rpow_one,div_le_iff₀ (by linarith only [hlog])]
      nlinarith only [mul_le_mul_of_nonneg_left hlog hp.le])
  have he : _root_.RHTower.windowPrimes ((4*(N:ℝ))/2) ((6*(N:ℝ))/2) =
      Nat.primesLE (3*N) \ Nat.primesLE (2*N) := by
    rw [show 4*(N:ℝ)/2=((2*N:ℕ):ℝ) by push_cast; ring,
      show 6*(N:ℝ)/2=((3*N:ℕ):ℝ) by push_cast; ring]
    apply Finset.ext
    intro p
    simp only [_root_.RHTower.windowPrimes,Nat.floor_natCast,Finset.mem_filter,mem_Ioc,
      Finset.mem_sdiff,Nat.mem_primesLE]
    by_cases hpr : p.Prime <;> simp [hpr] <;> omega
  rw [he,card_sdiff_of_subset (Nat.primesLE_mono (by omega : 2*N ≤ 3*N)),
    Nat.cast_sub (Finset.card_le_card (Nat.primesLE_mono (by omega : 2*N ≤ 3*N)))] at hh
  simp only [Nat.primesLE_card_eq_primeCounting] at hh
  push_cast
  have hh0 : 0 < Real.log (4*(N:ℝ)) := by linarith only [hlog]
  rw [div_le_iff₀ (by positivity)] at hh ⊢
  nlinarith only [hh,hslow]

private theorem reciprocal_square_integral {a b : ℝ} (ha : 0<a) (hab : a ≤ b) (c : ℝ) :
    (∫ t in Set.Ioc a b, (c/t)^2) = c^2*(1/a-1/b) := by
  have hgap : (0:ℝ) ∉ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact fun h => ha.not_ge h.1
  rw [← intervalIntegral.integral_of_le hab]
  have he (t : ℝ) (ht : t ∈ Set.uIcc a b) : (c/t)^2 = c^2*t^(-2:ℝ) := by
    rw [Set.uIcc_of_le hab] at ht
    rw [Real.rpow_neg (ha.le.trans ht.1),show (2:ℝ)=(2:ℕ) by norm_num,Real.rpow_natCast]
    ring
  rw [intervalIntegral.integral_congr he,intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by norm_num,hgap⟩)]
  rw [show (-2:ℝ)+1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one]
  ring

/-- The squared smooth Haar source on the square-root window has size
y²/log²(y). Its lower bound comes from one fixed interval of ordinary primes. -/
theorem smoothHaarSource_square_window_energy :
    ∀ᶠ y : ℕ in atTop,
      (y:ℝ)^2/(6144*(Real.log y)^2) ≤
        (∫ t in Set.Ioc (1/(y:ℝ)^2) (1/(y:ℝ)), ‖pmSmoothHaarSource (y+1) t‖^2) ∧
      (∫ t in Set.Ioc (1/(y:ℝ)^2) (1/(y:ℝ)), ‖pmSmoothHaarSource (y+1) t‖^2) ≤
        (Real.log 4+5)^2*(y:ℝ)^2/(Real.log y)^2 := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp eventually_outer_prime_gap
  filter_upwards [eventually_ge_atTop (max 8 (8*M))] with y hy
  have hy8 : 8 ≤ y := (le_max_left _ _).trans hy
  have hyM := (le_max_right _ _).trans hy
  let N := y^2/4
  have hs : 4*y ≤ y^2 := by nlinarith only [Nat.mul_le_mul_left y (by omega : 4 ≤ y)]
  have h4N : 4*N ≤ y^2 := by dsimp only [N]; omega
  have h8N : y^2 ≤ 8*N := by dsimp only [N]; omega
  have hyN : y ≤ N := by dsimp only [N]; omega
  have hNp : 0 < N := by omega
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hNp
  have hyr : 1 < (y:ℝ) := by exact_mod_cast (show 1 < y by omega)
  have hypos := zero_lt_one.trans hyr
  have hlog := Real.log_pos hyr
  have h4 : 4*(N:ℝ) ≤ (y:ℝ)^2 := by exact_mod_cast h4N
  have h8 : (y:ℝ)^2 ≤ 8*(N:ℝ) := by exact_mod_cast h8N
  have hyn : (y:ℝ) ≤ N := by exact_mod_cast hyN
  let f (t : ℝ) := ‖pmSmoothHaarSource (y+1) t‖^2
  let a := 1/(y:ℝ)^2
  let b := 1/(y:ℝ)
  let d := 1/(4*(N:ℝ))
  let e := 1/(3*(N:ℝ))
  have hap : 0<a := by dsimp only [a]; positivity
  have had : a ≤ d := one_div_le_one_div_of_le (by positivity) h4
  have hde : d ≤ e := one_div_le_one_div_of_le (by positivity) (by linarith only [hNr])
  have heb : e ≤ b := one_div_le_one_div_of_le hypos (by linarith only [hyn,hNr])
  have hab := had.trans (hde.trans heb)
  have hi : IntegrableOn f (Set.Ioc a b) := by
    have hm := memLp_pmSmoothHaarSource (y+1)
    have hi₀ : IntegrableOn f (Set.Ioi 0) :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
    exact hi₀.mono_set (fun _ ht => hap.trans ht.1)
  constructor
  · let V := (N:ℝ)/(8*Real.log y)
    have hv : 0 ≤ V := by dsimp only [V]; positivity
    have hcut : V ≤ (N:ℝ)/(4*Real.log (4*N:ℕ)) := by
      have hlog4 : 0 < Real.log (4*N:ℕ) := Real.log_pos (by exact_mod_cast (show 1<4*N by omega))
      apply div_le_div_of_nonneg_left hNr.le (by positivity)
      have hl := Real.log_le_log (by positivity : 0 < 4*(N:ℝ)) h4
      rw [Real.log_pow] at hl
      norm_num at hl
      push_cast
      linarith only [hl]
    have hsmall : Set.Ioc d e ⊆ Set.Ioc a b := Set.Ioc_subset_Ioc had heb
    have hp (t : ℝ) (ht : t ∈ Set.Ioc d e) : V^2 ≤ f t := by
      have htp := hap.trans (had.trans_lt ht.1)
      have ht4 : 1/t ≤ (4*N:ℕ) := by
        push_cast
        exact (div_le_iff₀ htp).mpr (by have h := (div_le_iff₀ (by positivity : 0 < 4*(N:ℝ))).mp ht.1.le; linarith only [h])
      have ht3 : ((3*N:ℕ):ℝ) ≤ 1/t := by
        push_cast
        exact (le_div_iff₀ htp).mpr (by have h := (le_div_iff₀ (by positivity : 0 < 3*(N:ℝ))).mp ht.2; linarith only [h])
      have hr := smoothHaarSource_outer_window (y := y) (N := N) (by omega)
        (by nlinarith only [h4N,hy8]) htp ((Nat.le_floor_iff (by positivity)).mpr ht3)
        (by exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ 1/t)).trans ht4)
      have hh := hcut.trans ((hM N (by omega)).trans hr.1)
      exact (sq_le_sq₀ hv (norm_nonneg _)).mpr
        (hh.trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _)))
    have hc := setIntegral_mono_on (f := fun _ : ℝ => V^2) (g := f)
      (integrableOn_const (by simp)) (hi.mono_set hsmall) measurableSet_Ioc hp
    rw [setIntegral_const,smul_eq_mul,Real.volume_real_Ioc_of_le hde] at hc
    have hl : (e-d)*V^2 = N/(768*(Real.log y)^2) := by
      dsimp only [d,e,V]; field_simp; ring
    rw [hl] at hc
    apply le_trans _ (hc.trans (setIntegral_mono_set hi
      (Eventually.of_forall fun t => sq_nonneg _) (Eventually.of_forall fun _ ht => hsmall ht)))
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right h8 (sq_nonneg (Real.log y))]
  · let C := (Real.log 4+5)/Real.log y
    have hcut (t : ℝ) (ht : t ∈ Set.Ioc a b) : f t ≤ (C/t)^2 := by
      have ht0 := hap.trans ht.1
      have hl : (y:ℝ) ≤ 1/t := (le_div_iff₀ ht0).mpr
        (by have h := (le_div_iff₀ hypos).mp ht.2; linarith only [h])
      have hu : 1/t ≤ (y:ℝ)^2 := (div_le_iff₀ ht0).mpr
        (by have h := (div_le_iff₀ (sq_pos_of_pos hypos)).mp ht.1.le; linarith only [h])
      apply (sq_le_sq₀ (norm_nonneg _) (by dsimp only [C]; positivity)).mpr
      exact (haar_window_upper (by omega) ht0 hl hu).trans_eq (by dsimp only [C]; ring)
    have hg : IntegrableOn (fun t : ℝ => (C/t)^2) (Set.Ioc a b) := by
      apply (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
      exact ((continuousOn_const.div continuousOn_id fun x hx => (hap.trans_le hx.1).ne').pow 2)
    apply (setIntegral_mono_on hi hg measurableSet_Ioc hcut).trans
    rw [reciprocal_square_integral hap hab]
    dsimp only [a,b,C]
    simp only [one_div,inv_inv]
    rw [div_pow]
    exact (mul_le_mul_of_nonneg_left (sub_le_self _ hypos.le) (by positivity)).trans_eq (by ring)

end GaloisForLFunctions.ExceptionalLayerTheory
