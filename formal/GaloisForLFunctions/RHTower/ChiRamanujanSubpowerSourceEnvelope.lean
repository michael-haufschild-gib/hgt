import GaloisForLFunctions.RHTower.ChiRamanujanUniformLabelSource
import GaloisForLFunctions.RHTower.ChiRamanujanUniformEulerComparison
import GaloisForLFunctions.RHTower.ChiRamanujanGlobalResidueControl
import GaloisForLFunctions.RHTower.ZetaOneLineUniformLower

/-!
# Subpower control of the complete growing BAG arithmetic source

Actual logarithmic bounds for zeta and its reciprocal, together with the
filled residue factor at low frequency, give saturated pole geometry.
The original finite Euler comparison is uniform over all frequencies and
bounded signed abscissa shifts. Applying it to the complete labelled source
retains both numerator cofactors, both label exclusions and all sectors.

For every positive exponent, the full source is bounded by that frequency
power times a background term and both shrinking axis profiles. The background
is retained away from the axes; the pole is retained at low frequency. This
removes the fixed polynomial-growth obstruction to physical Mellin transfer.
Moving-test trace admission and signed cancellation remain separate problems.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace RHTower.BAGTrace

private theorem log_power_subpower (ε : {r : ℝ // 0<r}) :
    ∃ B : ℝ, 0<B ∧ ∀t : ℝ,
      (Real.log (|t|+Real.exp 1))^11 ≤ B*(1+|t|)^ε.1 := by
  let a : ℝ := ε.1/11
  have ha : 0<a := div_pos ε.2 (by norm_num)
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨(Real.exp 1)^ε.1/a^11,by positivity,?_⟩
  intro t
  let w := |t|+Real.exp 1
  have hw : 0<w := by dsimp only [w]; positivity
  have hlog : 0 ≤ Real.log w := Real.log_nonneg (by dsimp only [w]; linarith [abs_nonneg t])
  have hb := Real.log_le_rpow_div hw.le ha
  have hp := pow_le_pow_left₀ hlog hb 11
  have hpow : (w^a)^11=w^ε.1 := by
    rw [←Real.rpow_mul_natCast hw.le]
    congr 1
    dsimp only [a]
    norm_num
  have hbase : w ≤ Real.exp 1*(1+|t|) := by
    dsimp only [w]
    nlinarith [abs_nonneg t]
  calc (Real.log w)^11 ≤ w^ε.1/a^11 := by simpa only [div_pow,hpow] using hp
    _ ≤ (Real.exp 1*(1+|t|))^ε.1/a^11 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg ha.le _)
      exact Real.rpow_le_rpow hw.le hbase ε.2.le
    _ = _ := by
      rw [Real.mul_rpow (Real.exp_pos _).le (by positivity)]
      ring

private theorem scaled_residue_subpower (ε : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀σ : {r : ℝ // r∈Ioc (1 : ℝ) (5/4)}, ∀t : ℝ,
      ‖zetaResidueFactor ((σ.1 : ℂ)+(t : ℂ)*Complex.I)‖ ≤ C*(1+|t|)^ε.1*(1+|t|) ∧
      1+|t| ≤ C*(1+|t|)^ε.1*‖zetaResidueFactor ((σ.1 : ℂ)+(t : ℂ)*Complex.I)‖ := by
  obtain ⟨B,hB,hBb⟩ := log_power_subpower ε
  obtain ⟨K,hK,hKb⟩ := exists_uniform_upper_bound_inv_riemannZeta
  obtain ⟨c,hc,M,hM,hMb⟩ := exists_residue_global_polynomial_disks
  let C := 3*M*3^9+(6+2*K)*B
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro σ t
  let T := 1+|t|
  let z : ℂ := (σ.1 : ℂ)+(t : ℂ)*Complex.I
  have hT : 1 ≤ T := by dsimp only [T]; linarith [abs_nonneg t]
  have hT0 : 0<T := zero_lt_one.trans_le hT
  have hTe : 1 ≤ T^ε.1 := Real.one_le_rpow hT ε.2.le
  have hσ : 1<σ.1 := σ.2.1
  have hσ2 : σ.1 ≤ 2 := by linarith [σ.2.2]
  have hzre : z.re=σ.1 := by simp [z]
  have hzne : z≠1 := by intro hz; have := congrArg Complex.re hz; rw [hzre] at this; simp only [Complex.one_re] at this; linarith
  have hF : ‖zetaResidueFactor z‖=‖z-1‖*‖riemannZeta z‖ := by
    rw [zetaResidueFactor_of_ne hzne,norm_mul]
  have hd : ‖z-1‖ ≤ T := by
    have heq : z-1=((σ.1-1 : ℝ) : ℂ)+(t : ℂ)*Complex.I := by dsimp only [z]; push_cast; ring
    rw [heq]
    have hh := norm_add_le (((σ.1-1 : ℝ) : ℂ)) ((t : ℂ)*Complex.I)
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,
      abs_of_pos (sub_pos.mpr hσ)] at hh
    dsimp only [T]
    linarith
  have htz : |t| ≤ ‖z-1‖ := by
    simpa only [z,Complex.sub_im,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add,
      Complex.one_im,sub_zero] using Complex.abs_im_le_norm (z-1)
  have hCb : 6*B ≤ C := by dsimp only [C]; nlinarith [mul_pos hK hB]
  have hCk : 2*K*B ≤ C := by dsimp only [C]; nlinarith
  have hCm : 3*M*3^9 ≤ C := by dsimp only [C]; nlinarith [mul_pos hK hB]
  by_cases ht : |t| ≤ 2
  · have hm := hMb σ.1 ⟨hσ.le,hσ2⟩ t z
      (by simpa only [z,mem_closedBall,dist_self] using
        (show (0 : ℝ) ≤ c/T^9 from div_nonneg hc.1.le (pow_nonneg hT0.le _)))
    have hsmall : T ≤ 3 := by dsimp only [T]; linarith
    have hpow : T^9 ≤ (3 : ℝ)^9 := pow_le_pow_left₀ hT0.le hsmall 9
    have hFinv : ‖(zetaResidueFactor z)⁻¹‖ ≤ M*3^9 :=
      hm.2.2.trans (mul_le_mul_of_nonneg_left hpow hM.le)
    have hFup : ‖zetaResidueFactor z‖ ≤ M*3^9 :=
      hm.2.1.trans (mul_le_mul_of_nonneg_left hpow hM.le)
    have hnorm : 0<‖zetaResidueFactor z‖ := norm_pos_iff.mpr hm.1
    have hmul : 1 ≤ (M*3^9)*‖zetaResidueFactor z‖ := by
      rw [norm_inv] at hFinv
      exact (inv_le_iff_one_le_mul₀ hnorm).mp hFinv
    constructor
    · change ‖zetaResidueFactor z‖ ≤ C*T^ε.1*T
      have hMC : M*3^9 ≤ C := by nlinarith
      calc ‖zetaResidueFactor z‖ ≤ M*3^9 := hFup
        _ ≤ C := hMC
        _ = C*1*1 := by ring
        _ ≤ C*T^ε.1*T := by gcongr
    · change T ≤ C*T^ε.1*‖zetaResidueFactor z‖
      calc T ≤ 3 := hsmall
        _ ≤ (3*M*3^9)*‖zetaResidueFactor z‖ := by nlinarith
        _ ≤ C*‖zetaResidueFactor z‖ := mul_le_mul_of_nonneg_right hCm hnorm.le
        _ = C*1*‖zetaResidueFactor z‖ := by ring
        _ ≤ C*T^ε.1*‖zetaResidueFactor z‖ := by gcongr
  · have ht2 : 2 < |t| := lt_of_not_ge ht
    have hzim : z.im=t := by simp [z]
    have hz : ‖riemannZeta z‖ ≤ Real.log |t|+5 := by
      have hh := norm_riemannZeta_le_log_add (s := z)
        (by rw [hzre]; exact hσ.le) (by rw [hzre]; exact hσ2)
        (by rw [hzim]; exact ht2.le)
      simpa only [hzim] using hh
    have hl : 1 ≤ Real.log (|t|+Real.exp 1) := by
      have hh := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_left (abs_nonneg t))
      simpa only [Real.log_exp] using hh
    have hlp : Real.log (|t|+Real.exp 1) ≤ (Real.log (|t|+Real.exp 1))^11 := by
      simpa only [pow_one] using pow_le_pow_right₀ hl (by norm_num : 1 ≤ 11)
    have hlogs : Real.log |t| ≤ Real.log (|t|+Real.exp 1) :=
      Real.log_le_log (by linarith) (le_add_of_nonneg_right (Real.exp_pos _).le)
    have hzu : ‖riemannZeta z‖ ≤ 6*B*T^ε.1 := by
      have hb := hBb t
      change (Real.log (|t|+Real.exp 1))^11 ≤ B*T^ε.1 at hb
      nlinarith
    have hzi : ‖(riemannZeta z)⁻¹‖ ≤ K*B*T^ε.1 := by
      have hh := hKb σ.1 t hσ σ.2.2
      exact hh.trans (by simpa only [mul_assoc,T] using mul_le_mul_of_nonneg_left (hBb t) hK.le)
    have hzpos : 0<‖riemannZeta z‖ := norm_pos_iff.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by rw [hzre]; exact hσ))
    have hzprod : 1 ≤ (K*B*T^ε.1)*‖riemannZeta z‖ := by
      rw [norm_inv] at hzi
      exact (inv_le_iff_one_le_mul₀ hzpos).mp hzi
    have hTd : T ≤ 2*‖z-1‖ := by dsimp only [T]; linarith
    constructor
    · change ‖zetaResidueFactor z‖ ≤ C*T^ε.1*T
      rw [hF]
      calc ‖z-1‖*‖riemannZeta z‖ ≤ T*(6*B*T^ε.1) :=
          mul_le_mul hd hzu (norm_nonneg _) hT0.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hCb (by positivity : 0 ≤ T^ε.1*T)]
    · change T ≤ C*T^ε.1*‖zetaResidueFactor z‖
      rw [hF]
      have hh := mul_le_mul_of_nonneg_left hzprod (by positivity : 0 ≤ 2*‖z-1‖)
      have hc := mul_le_mul_of_nonneg_right hCk (by positivity : 0 ≤ T^ε.1*(‖z-1‖*‖riemannZeta z‖))
      nlinarith

private def movingPoint (ρ t : ℝ) (N : ℕ) : ℂ :=
  ((ρ/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I

private theorem movingPoint_re (ρ t : ℝ) (N : ℕ) :
    (movingPoint ρ t N).re=ρ/Real.log N := by
  simp only [movingPoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,mul_zero,zero_mul,sub_self,add_zero]

private theorem movingPoint_im (ρ t : ℝ) (N : ℕ) :
    (movingPoint ρ t N).im=t := by
  simp only [movingPoint,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add]

private def poleSize (N : ℕ) (t : ℝ) : ℝ := 1/Real.log N+|t|

private theorem poleSize_pos {N : ℕ} (hN : 2 ≤ N) (t : ℝ) : 0<poleSize N t := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  dsimp [poleSize]
  positivity

private theorem pole_norm_comparison {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    ‖movingPoint 1 t N‖ ≤ poleSize N t ∧ poleSize N t ≤ 2*‖movingPoint 1 t N‖ := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have he : 0 ≤ 1/Real.log N := by positivity
  have hre := Complex.abs_re_le_norm (movingPoint 1 t N)
  have him := Complex.abs_im_le_norm (movingPoint 1 t N)
  rw [movingPoint_re,abs_of_nonneg he] at hre
  rw [movingPoint_im] at him
  constructor
  · have h := norm_add_le (((1/Real.log N : ℝ) : ℂ)) ((t : ℂ)*Complex.I)
    simpa only [movingPoint,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,
      mul_one,abs_of_nonneg he,poleSize] using h
  · dsimp [poleSize]; linarith


private def finiteQ (a t : ℝ) (N : ℕ) : ℂ :=
  ∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+movingPoint a t N))

private theorem finiteQ_nat (a t : ℝ) (N : ℕ) :
    finiteQ a t N=∏ p ∈ Nat.primesLE N,
      (1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I)) := by
  calc finiteQ a t N = ∏ p ∈ Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+movingPoint a t N)) :=
         Finset.prod_coe_sort (Sieve.primeSubtypeLE N)
           (fun p : Nat.Primes => 1-cubicPrimeBase p (1+movingPoint a t N))
       _ = ∏ p ∈ Nat.primesLE N,(1-(p : ℂ)^(-(1+movingPoint a t N))) :=
         Finset.prod_subtype_of_mem (s := Nat.primesLE N)
           (fun p : ℕ => 1-(p : ℂ)^(-(1+movingPoint a t N)))
           (fun n hn => Nat.prime_of_mem_primesLE hn)
       _ = _ := by
         apply Finset.prod_congr rfl
         intro p hp
         congr 2
         dsimp [movingPoint]
         ring


private def saturatedPole (N : ℕ) (t : ℝ) : ℝ := poleSize N t/(1+|t|)

private theorem saturated_euler_control (A : ℝ) (ε : {r : ℝ // 0<r}) :
    ∃ E : ℝ, 0<E ∧ ∀ᶠ N : ℕ in atTop, ∀a : ℝ, |a| ≤ |A| → ∀t : ℝ,
      saturatedPole N t ≤ E*(1+|t|)^ε.1*‖finiteQ a t N‖ ∧
      ‖finiteQ a t N‖ ≤ E*(1+|t|)^ε.1*saturatedPole N t := by
  obtain ⟨C,hC,hCb⟩ := scaled_residue_subpower ε
  obtain ⟨B,hB,hBb⟩ := criticalFiniteEulerProduct_zeta_comparison A
  have hsmall := (tendsto_drift_zero (1 : ℝ)).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ)<1/4))
  refine ⟨2*Real.exp B*C,by positivity,?_⟩
  filter_upwards [hBb,hsmall,eventually_ge_atTop 2] with N hb hn hN
  intro a ha t
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have he : 0<1/Real.log N := by positivity
  let σ : {r : ℝ // r∈Ioc (1 : ℝ) (5/4)} := ⟨1+1/Real.log N,by constructor <;> linarith⟩
  let z : ℂ := (σ.1 : ℂ)+(t : ℂ)*Complex.I
  let d := movingPoint 1 t N
  let T := 1+|t|
  have hT : 0<T := by dsimp only [T]; positivity
  have hzne : z≠1 := by
    intro hz
    have hh := congrArg Complex.re hz
    simp only [z,σ,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,mul_zero,zero_mul,sub_self,add_zero,Complex.one_re] at hh
    linarith
  have hzd : z-1=d := by dsimp only [z,σ,d,movingPoint]; push_cast; ring
  have hF : ‖zetaResidueFactor z‖=‖d‖*‖riemannZeta z‖ := by
    rw [zetaResidueFactor_of_ne hzne,hzd,norm_mul]
  have hf := hCb σ t
  change ‖zetaResidueFactor z‖ ≤ C*T^ε.1*T ∧ T ≤ C*T^ε.1*‖zetaResidueFactor z‖ at hf
  rw [hF] at hf
  have hq := hb a ha t
  rw [←finiteQ_nat] at hq
  change Real.exp (-B) ≤ ‖finiteQ a t N‖*‖riemannZeta z‖ ∧
    ‖finiteQ a t N‖*‖riemannZeta z‖ ≤ Real.exp B at hq
  have hp := pole_norm_comparison hN t
  have hq1 : 1 ≤ Real.exp B*(‖finiteQ a t N‖*‖riemannZeta z‖) := by
    have hh := mul_le_mul_of_nonneg_left hq.1 (Real.exp_pos B).le
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
    exact hh
  have hdQ : ‖d‖ ≤ Real.exp B*‖finiteQ a t N‖*(C*T^ε.1*T) := by
    calc
      ‖d‖ ≤ (Real.exp B*(‖finiteQ a t N‖*‖riemannZeta z‖))*‖d‖ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1 (norm_nonneg d)
      _ = (Real.exp B*‖finiteQ a t N‖)*(‖d‖*‖riemannZeta z‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hf.1 (by positivity)
  constructor
  · apply (div_le_iff₀ hT).mpr
    change poleSize N t ≤ (2*Real.exp B*C*T^ε.1*‖finiteQ a t N‖)*T
    calc poleSize N t ≤ 2*‖d‖ := hp.2
      _ ≤ 2*(Real.exp B*‖finiteQ a t N‖*(C*T^ε.1*T)) := by gcongr
      _ = _ := by ring
  · change ‖finiteQ a t N‖ ≤ (2*Real.exp B*C*T^ε.1)*(poleSize N t/T)
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hT).mpr
    calc
      ‖finiteQ a t N‖*T ≤ ‖finiteQ a t N‖*(C*T^ε.1*(‖d‖*‖riemannZeta z‖)) :=
        mul_le_mul_of_nonneg_left hf.2 (norm_nonneg _)
      _ = (C*T^ε.1*‖d‖)*(‖finiteQ a t N‖*‖riemannZeta z‖) := by ring
      _ ≤ (C*T^ε.1*‖d‖)*Real.exp B := mul_le_mul_of_nonneg_left hq.2 (by positivity)
      _ ≤ (C*T^ε.1*poleSize N t)*Real.exp B := by gcongr; exact hp.1
      _ ≤ (2*Real.exp B*C*T^ε.1)*poleSize N t := by
        have hp0 := (poleSize_pos hN t).le
        nlinarith [show 0 ≤ Real.exp B*C*T^ε.1*poleSize N t by positivity]

private theorem saturated_zeta_control (ρ : {r : ℝ // 0<r}) (ε : {r : ℝ // 0<r}) :
    ∃ B : ℝ, 0<B ∧ ∀ᶠ N : ℕ in atTop, ∀t : ℝ,
      ‖riemannZeta (1+movingPoint ρ t N)‖*saturatedPole N t ≤ B*(1+|t|)^ε.1 := by
  obtain ⟨C,hC,hCb⟩ := scaled_residue_subpower ε
  let K : ℝ := 1/(ρ : ℝ)+1
  have hK : 0<K := by dsimp only [K]; have := ρ.2; positivity
  refine ⟨K*C,mul_pos hK hC,?_⟩
  have hsmall := (tendsto_drift_zero (ρ : ℝ)).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ)<1/4))
  filter_upwards [hsmall,eventually_ge_atTop 2] with N hsmall hN
  intro t
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hρL : 0<(ρ : ℝ)/Real.log N := div_pos ρ.2 hL
  let σ : {r : ℝ // r∈Ioc (1 : ℝ) (5/4)} := ⟨1+(ρ : ℝ)/Real.log N,by constructor <;> linarith⟩
  let z := 1+movingPoint ρ t N
  have hz : (σ.1 : ℂ)+(t : ℂ)*Complex.I=z := by dsimp only [z,σ,movingPoint]; push_cast; ring
  have hzne : z≠1 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [z,Complex.add_re,Complex.one_re,movingPoint_re] at hre
    linarith
  have hF : ‖zetaResidueFactor z‖=‖movingPoint ρ t N‖*‖riemannZeta z‖ := by
    rw [zetaResidueFactor_of_ne hzne]
    simp only [z,add_sub_cancel_left,norm_mul]
  have hf := (hCb σ t).1
  rw [hz,hF] at hf
  have hre := Complex.abs_re_le_norm (movingPoint ρ t N)
  rw [movingPoint_re,abs_of_pos hρL] at hre
  have him := Complex.abs_im_le_norm (movingPoint ρ t N)
  rw [movingPoint_im] at him
  have heps : 1/Real.log N ≤ ‖movingPoint ρ t N‖/(ρ : ℝ) := by
    apply (le_div_iff₀ ρ.2).mpr
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hre
  have hpole : poleSize N t ≤ K*‖movingPoint ρ t N‖ := by
    dsimp only [poleSize,K]
    calc 1/Real.log N+|t| ≤ ‖movingPoint ρ t N‖/(ρ : ℝ)+‖movingPoint ρ t N‖ := by linarith
      _ = _ := by ring
  change ‖riemannZeta z‖*(poleSize N t/(1+|t|)) ≤ (K*C)*(1+|t|)^ε.1
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<1+|t|)).mpr
  calc ‖riemannZeta z‖*poleSize N t ≤ ‖riemannZeta z‖*(K*‖movingPoint ρ t N‖) :=
      mul_le_mul_of_nonneg_left hpole (norm_nonneg _)
    _ = K*(‖movingPoint ρ t N‖*‖riemannZeta z‖) := by ring
    _ ≤ K*(C*(1+|t|)^ε.1*(1+|t|)) := mul_le_mul_of_nonneg_left hf hK.le
    _ = _ := by ring

private theorem point_sub (a b t u : ℝ) (N : ℕ) :
    movingPoint a t N-movingPoint b u N=movingPoint (a-b) (t-u) N := by
  dsimp [movingPoint]
  push_cast
  ring

private theorem point_neg (a t : ℝ) (N : ℕ) :
    -movingPoint a t N=movingPoint (-a) (-t) N := by
  dsimp [movingPoint]
  push_cast
  ring

private theorem inverse_pole_identity {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    1/(poleSize N t)^2=(Real.log N)^2/(1+Real.log N*|t|)^2 := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have ht : 0<1+Real.log N*|t| := by positivity
  dsimp [poleSize]
  field_simp


private theorem saturatedPole_pos {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    0<saturatedPole N t := div_pos (poleSize_pos hN t) (by positivity)

private theorem saturated_distance_triangle (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (x y : ℝ) :
    (e+|y-x|)/(1+|y-x|) ≤ (e+|x|)/(1+|x|)+(e+|y|)/(1+|y|) := by
  have hab : |y-x| ≤ |x|+|y| := by linarith [abs_sub y x]
  have hp : 0<1+|x|+|y| := by positivity
  calc
    (e+|y-x|)/(1+|y-x|) ≤ (e+|x|+|y|)/(1+|x|+|y|) := by
      apply (div_le_div_iff₀ (by positivity) hp).mpr
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1-e) (by linarith : 0 ≤ |x|+|y|-|y-x|)]
    _ = (e+|x|)/(1+|x|+|y|)+|y|/(1+|x|+|y|) := by ring
    _ ≤ (e+|x|)/(1+|x|)+|y|/(1+|y|) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith [abs_nonneg y])
      · exact div_le_div_of_nonneg_left (abs_nonneg y) (by positivity) (by linarith [abs_nonneg x])
    _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_right (by linarith) (by positivity)) _

private theorem inverse_saturated_distance (e : ℝ) (he : 0<e) (x : ℝ) :
    1/((e+|x|)/(1+|x|))^2 ≤ 2*(1+1/(e+|x|)^2) := by
  have hd : 0<e+|x| := by positivity
  have h1 : 0<1+|x| := by positivity
  rw [div_pow,one_div_div]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have hid : (2*(1+1/(e+|x|)^2))*(e+|x|)^2=2*((e+|x|)^2+1) := by field_simp
  rw [hid]
  nlinarith [abs_nonneg x,sq_nonneg (e+|x|-1)]

private theorem inverse_saturatedPole {N : ℕ} (hN : 2 ≤ N) (t : ℝ) :
    1/(saturatedPole N t)^2 ≤
      2*(1+(Real.log N)^2/(1+Real.log N*|t|)^2) := by
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hh := inverse_saturated_distance (1/Real.log N) (by positivity) t
  change 1/(saturatedPole N t)^2 ≤ 2*(1+1/(poleSize N t)^2) at hh
  rw [inverse_pole_identity hN t] at hh
  exact hh

private theorem saturated_envelope_algebra {Z z₁ z₂ q₁ q₂ q₃ q₄ d₁ d₂ d C B₁ B₂ E T : ℝ}
    (_hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hq₃ : 0<q₃) (hq₄ : 0<q₄) (hd₁ : 0<d₁) (hd₂ : 0<d₂) (hd : 0 ≤ d)
    (hC : 0<C) (hB₁ : 0<B₁) (hB₂ : 0<B₂) (hE : 0<E) (hT : 0<T)
    (hs : Z ≤ C*z₁*z₂*(q₁*q₂/(q₃*q₄)))
    (hζ₁ : z₁*d₁ ≤ B₁*T) (hζ₂ : z₂*d₂ ≤ B₂*T)
    (h₁ : q₁ ≤ E*T*d) (h₂ : q₂ ≤ E*T*d)
    (h₃ : d₁ ≤ E*T*q₃) (h₄ : d₂ ≤ E*T*q₄) (hΔ : d ≤ d₁+d₂) :
    Z ≤ (2*C*B₁*B₂*E^4)*T^6*(1/d₁^2+1/d₂^2) := by
  have hzi₁ : z₁ ≤ B₁*T/d₁ := (le_div_iff₀ hd₁).mpr hζ₁
  have hzi₂ : z₂ ≤ B₂*T/d₂ := (le_div_iff₀ hd₂).mpr hζ₂
  have hi₃ : q₃⁻¹ ≤ E*T/d₁ := by
    apply (le_div_iff₀ hd₁).mpr
    calc q₃⁻¹*d₁=d₁/q₃ := by ring
         _ ≤ E*T := (div_le_iff₀ hq₃).mpr h₃
  have hi₄ : q₄⁻¹ ≤ E*T/d₂ := by
    apply (le_div_iff₀ hd₂).mpr
    calc q₄⁻¹*d₂=d₂/q₄ := by ring
         _ ≤ E*T := (div_le_iff₀ hq₄).mpr h₄
  have hdsq : d^2 ≤ 2*(d₁^2+d₂^2) := by
    nlinarith [mul_nonneg (show 0 ≤ d₁+d₂-d by linarith)
      (show 0 ≤ d₁+d₂+d by linarith),sq_nonneg (d₁-d₂)]
  calc Z ≤ C*z₁*z₂*(q₁*q₂*(q₃⁻¹*q₄⁻¹)) := by simpa only [div_eq_mul_inv,mul_inv] using hs
       _ ≤ C*(B₁*T/d₁)*(B₂*T/d₂)*
           ((E*T*d)*(E*T*d)*((E*T/d₁)*(E*T/d₂))) := by gcongr
       _ = (C*B₁*B₂*E^4)*T^6*d^2/(d₁^2*d₂^2) := by field_simp
       _ ≤ (C*B₁*B₂*E^4)*T^6*(2*(d₁^2+d₂^2))/(d₁^2*d₂^2) := by gcongr
       _ = _ := by field_simp; ring

private theorem uniform_factor_control (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+movingPoint ρ₁ t₁ N) (1+movingPoint ρ₂ t₂ N)‖ ≤
      C*‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*
        (‖finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N‖*
          ‖finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N‖/
          (‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖*‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖)) := by
  obtain ⟨C,hC,hN⟩ := criticalCompletedConeEuler_uniform_factor_bound ρ₁ ρ₂
  refine ⟨C,hC,?_⟩
  filter_upwards [hN] with N hN
  intro t₁ t₂
  have h := hN t₁ t₂
  change ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (1+movingPoint ρ₁ t₁ N) (1+movingPoint ρ₂ t₂ N)‖ ≤
    C*‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*
      ‖((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p
            (1+(movingPoint ρ₂ t₂ N-movingPoint ρ₁ t₁ N))))*
        (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p
            (1+(movingPoint ρ₁ t₁ N-movingPoint ρ₂ t₂ N)))))/
        ((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-movingPoint ρ₁ t₁ N)))*
          (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-movingPoint ρ₂ t₂ N))))‖ at h
  have hneg (a t : ℝ) : 1-movingPoint a t N=1+movingPoint (-a) (-t) N := by
    rw [sub_eq_add_neg,point_neg]
  simp only [point_sub,hneg] at h
  change ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
    (1+movingPoint ρ₁ t₁ N) (1+movingPoint ρ₂ t₂ N)‖ ≤
    C*‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*
      ‖(finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N*
        finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N)/
        (finiteQ (-(ρ₁ : ℝ)) (-t₁) N*finiteQ (-(ρ₂ : ℝ)) (-t₂) N)‖ at h
  simpa only [norm_div,norm_mul] using h


/-- Complete original labelled source with subpower frequency growth,
retaining the bounded-background term and both shrinking axes. -/
theorem criticalCompletedConeEuler_uniform_saturated_axes_bound
    (ρ₁ ρ₂ : {r : ℝ // 0<r}) (ε : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N)
        (1+(((ρ₁ : ℝ)/Real.log N : ℝ) : ℂ)+(t₁ : ℂ)*Complex.I)
        (1+(((ρ₂ : ℝ)/Real.log N : ℝ) : ℂ)+(t₂ : ℂ)*Complex.I)‖ ≤
      C*(1+|t₁|+|t₂|)^ε.1 *
        (1+(Real.log N)^2/(1+Real.log N*|t₁|)^2+
          (Real.log N)^2/(1+Real.log N*|t₂|)^2) := by
  let η : {r : ℝ // 0<r} := ⟨ε.1/6,div_pos ε.2 (by norm_num)⟩
  obtain ⟨C₀,hC₀,hsource⟩ := uniform_factor_control ρ₁ ρ₂
  obtain ⟨B₁,hB₁,hz₁⟩ := saturated_zeta_control ρ₁ η
  obtain ⟨B₂,hB₂,hz₂⟩ := saturated_zeta_control ρ₂ η
  let A : ℝ := |(ρ₁ : ℝ)|+|(ρ₂ : ℝ)|
  obtain ⟨E,hE,heuler⟩ := saturated_euler_control A η
  refine ⟨8*C₀*B₁*B₂*E^4,by positivity,?_⟩
  have hsmall := (tendsto_drift_zero (1 : ℝ)).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hsource,hz₁,hz₂,heuler,hsmall,eventually_ge_atTop 2] with N hs hz₁ hz₂ he hsmall hN
  intro t₁ t₂
  let T : ℝ := 1+|t₁|+|t₂|
  have hT : 0<T := by dsimp [T]; positivity
  have hT₁ : 1+|t₁| ≤ T := by dsimp [T]; linarith [abs_nonneg t₂]
  have hT₂ : 1+|t₂| ≤ T := by dsimp [T]; linarith [abs_nonneg t₁]
  have hTΔ : 1+|t₂-t₁| ≤ T := by dsimp [T]; linarith [abs_sub t₂ t₁]
  have hTΔ' : 1+|t₁-t₂| ≤ T := by dsimp [T]; linarith [abs_sub t₁ t₂]
  have hη : 0 ≤ η.1 := η.2.le
  have hA₁ : |-(ρ₁ : ℝ)| ≤ |A| := by
    rw [abs_neg]
    exact (le_add_of_nonneg_right (abs_nonneg (ρ₂ : ℝ))).trans (le_abs_self A)
  have hA₂ : |-(ρ₂ : ℝ)| ≤ |A| := by
    rw [abs_neg]
    exact (le_add_of_nonneg_left (abs_nonneg (ρ₁ : ℝ))).trans (le_abs_self A)
  have hAΔ : |(ρ₂ : ℝ)-(ρ₁ : ℝ)| ≤ |A| := by
    have hh : |(ρ₂ : ℝ)-(ρ₁ : ℝ)| ≤ A := by dsimp [A]; linarith [abs_sub (ρ₂ : ℝ) (ρ₁ : ℝ)]
    exact hh.trans (le_abs_self A)
  have hAΔ' : |(ρ₁ : ℝ)-(ρ₂ : ℝ)| ≤ |A| := by
    have hh : |(ρ₁ : ℝ)-(ρ₂ : ℝ)| ≤ A := by dsimp [A]; exact abs_sub _ _
    exact hh.trans (le_abs_self A)
  have hqe₁ := he ((ρ₂ : ℝ)-(ρ₁ : ℝ)) hAΔ (t₂-t₁)
  have hqe₂ := he ((ρ₁ : ℝ)-(ρ₂ : ℝ)) hAΔ' (t₁-t₂)
  have hqe₃ := he (-(ρ₁ : ℝ)) hA₁ (-t₁)
  have hqe₄ := he (-(ρ₂ : ℝ)) hA₂ (-t₂)
  have hdp : 0 ≤ saturatedPole N (t₂-t₁) := (saturatedPole_pos hN (t₂-t₁)).le
  have hq₁ : ‖finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N‖ ≤ E*T^η.1*saturatedPole N (t₂-t₁) := by
    apply hqe₁.2.trans
    gcongr
  have hq₂ : ‖finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N‖ ≤ E*T^η.1*saturatedPole N (t₂-t₁) := by
    have hp : saturatedPole N (t₁-t₂)=saturatedPole N (t₂-t₁) := by simp only [saturatedPole,poleSize,abs_sub_comm t₁ t₂]
    have hh := hqe₂.2
    rw [hp] at hh
    apply hh.trans
    gcongr
  have hq₃ : saturatedPole N t₁ ≤ E*T^η.1*‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖ := by
    have hh : saturatedPole N t₁ ≤ E*(1+|t₁|)^η.1*‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖ := by
      simpa only [saturatedPole,poleSize,abs_neg] using hqe₃.1
    apply hh.trans
    gcongr
  have hq₄ : saturatedPole N t₂ ≤ E*T^η.1*‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖ := by
    have hh : saturatedPole N t₂ ≤ E*(1+|t₂|)^η.1*‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖ := by
      simpa only [saturatedPole,poleSize,abs_neg] using hqe₄.1
    apply hh.trans
    gcongr
  have hQ₃ : 0<‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖ := by
    by_contra hh
    have hzero : ‖finiteQ (-(ρ₁ : ℝ)) (-t₁) N‖=0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [hzero,mul_zero] at hq₃
    exact (not_le_of_gt (saturatedPole_pos hN t₁)) hq₃
  have hQ₄ : 0<‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖ := by
    by_contra hh
    have hzero : ‖finiteQ (-(ρ₂ : ℝ)) (-t₂) N‖=0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [hzero,mul_zero] at hq₄
    exact (not_le_of_gt (saturatedPole_pos hN t₂)) hq₄
  have hζ₁ : ‖riemannZeta (1+movingPoint ρ₁ t₁ N)‖*saturatedPole N t₁ ≤ B₁*T^η.1 := by
    apply (hz₁ t₁).trans
    gcongr
  have hζ₂ : ‖riemannZeta (1+movingPoint ρ₂ t₂ N)‖*saturatedPole N t₂ ≤ B₂*T^η.1 := by
    apply (hz₂ t₂).trans
    gcongr
  have hΔ : saturatedPole N (t₂-t₁) ≤ saturatedPole N t₁+saturatedPole N t₂ := by
    have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
    exact saturated_distance_triangle (1/Real.log N) (by positivity) hsmall t₁ t₂
  have hh := saturated_envelope_algebra
    (norm_nonneg (riemannZeta (1+movingPoint ρ₁ t₁ N)))
    (norm_nonneg (riemannZeta (1+movingPoint ρ₂ t₂ N)))
    (norm_nonneg (finiteQ ((ρ₂ : ℝ)-(ρ₁ : ℝ)) (t₂-t₁) N))
    (norm_nonneg (finiteQ ((ρ₁ : ℝ)-(ρ₂ : ℝ)) (t₁-t₂) N))
    hQ₃ hQ₄ (saturatedPole_pos hN t₁) (saturatedPole_pos hN t₂) (saturatedPole_pos hN (t₂-t₁)).le
    hC₀ hB₁ hB₂ hE (Real.rpow_pos_of_pos hT η.1) (hs t₁ t₂) hζ₁ hζ₂ hq₁ hq₂ hq₃ hq₄ hΔ
  have hpow : (T^η.1)^6=T^ε.1 := by
    rw [←Real.rpow_mul_natCast hT.le]
    congr 1
    dsimp only [η]
    norm_num
  rw [hpow] at hh
  have h1 := inverse_saturatedPole hN t₁
  have h2 := inverse_saturatedPole hN t₂
  let a1 := (Real.log N)^2/(1+Real.log N*|t₁|)^2
  let a2 := (Real.log N)^2/(1+Real.log N*|t₂|)^2
  have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
  have ha2 : 0 ≤ a2 := by dsimp only [a2]; positivity
  have hsum : 1/(saturatedPole N t₁)^2+1/(saturatedPole N t₂)^2 ≤ 4*(1+a1+a2) := by
    change 1/(saturatedPole N t₁)^2 ≤ 2*(1+a1) at h1
    change 1/(saturatedPole N t₂)^2 ≤ 2*(1+a2) at h2
    linarith
  have hh2 := hh.trans (mul_le_mul_of_nonneg_left hsum
    (by positivity : 0 ≤ (2*C₀*B₁*B₂*E^4)*T^ε.1))
  have hfinal := hh2.trans_eq (show
    (2*C₀*B₁*B₂*E^4)*T^ε.1*(4*(1+a1+a2))=(8*C₀*B₁*B₂*E^4)*T^ε.1*(1+a1+a2) by ring)
  simpa only [T,a1,a2,movingPoint,add_assoc] using hfinal

end RHTower.BAGTrace