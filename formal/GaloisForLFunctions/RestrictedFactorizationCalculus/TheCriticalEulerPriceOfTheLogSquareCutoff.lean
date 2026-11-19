import GaloisForLFunctions.RestrictedFactorizationCalculus.CenteringThePrimePowerReadingsAtTheirQuotientFloors
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary
import GaloisForLFunctions.RHTower.Sieve.FiniteReciprocalBound
import GaloisForLFunctions.RHTower.PrimeRpowSumAsymptotic
import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic
import GaloisForLFunctions.RHTower.Sieve.KubalalikaLargeScale

/-!
# The critical Euler price of the log-square cutoff

The prime number theorem gives the normalized reciprocal-root mass
with and without a logarithmic weight. Comparing each Euler factor
with its first term determines the order of the critical deletion cost.
-/

noncomputable section

open Filter Finset RHTower RHTower.Sieve
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev rootSum (n : ℕ) := ∑ p ∈ Nat.primesLE n,1/Real.sqrt p
private theorem expose_prime_two {N : ℕ} (hN : 2 ≤ N) (f : ℕ → ℝ) :
    (∑ p ∈ Nat.primesLE N,f p)=f 2+∑ n ∈ Ioc 2 N,if n.Prime then f n else 0 := by
  have set : Nat.primesLE N=insert 2 ((Ioc 2 N).filter Nat.Prime) := by
    ext p
    simp only [Nat.mem_primesLE,mem_insert,mem_filter,mem_Ioc]
    constructor
    · rintro ⟨hi,hp⟩
      exact eq_or_lt_of_le hp.two_le |>.elim (fun eq => Or.inl eq.symm) (fun lt => Or.inr ⟨⟨lt,hi⟩,hp⟩)
    · rintro (rfl | ⟨⟨_,hi⟩,hp⟩)
      · exact ⟨hN,Nat.prime_two⟩
      · exact ⟨hi,hp⟩
  rw [set,sum_insert (by simp),sum_filter]

/-- The ordinary reciprocal-root prime mass, normalized at its upper endpoint. -/
theorem limit_reciprocal_roots_of_primes :
    Tendsto (fun N : ℕ => rootSum N*Real.log N/Real.sqrt N) atTop (𝓝 2) := by
  have half : 0<(1/2:ℝ) := by norm_num
  have core : Tendsto (fun N : ℕ => primeRpowSumIoc (1/2) (N:ℝ)*((1/2)*Real.log N)/(N:ℝ)^(1/2:ℝ))
      atTop (𝓝 1) := (tendsto_primeRpowSumIoc half (by norm_num)).comp tendsto_natCast_atTop_atTop
  have loss : Tendsto (fun N : ℕ => Real.log N/(N:ℝ)^(1/2:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop half).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have out := (core.const_mul 2).add (loss.const_mul (1/Real.sqrt 2))
  rw [mul_one,mul_zero,add_zero] at out
  apply out.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hn
  have eq := expose_prime_two hn (fun p => 1/Real.sqrt p)
  have point (p : ℕ) : (p:ℝ)^((1/2:ℝ)-1)=1/Real.sqrt p := by
    rw [show (1/2:ℝ)-1= -(1/2) by norm_num,Real.rpow_neg (Nat.cast_nonneg _),←Real.sqrt_eq_rpow,one_div]
  simp only [primeRpowSumIoc,Nat.floor_natCast,point,←Real.sqrt_eq_rpow]
  change _ = (∑ p ∈ Nat.primesLE N,1/Real.sqrt p)*Real.log N/Real.sqrt N
  rw [eq]; push_cast; ring

/-- The logarithmically weighted reciprocal-root mass has limiting
coefficient two. This is the mass charged for omitting ordinary primes. -/
theorem limit_log_weighted_roots_of_primes :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N,Real.log p/Real.sqrt p)/Real.sqrt N) atTop (𝓝 2) := by
  have half : 0<(1/2:ℝ) := by norm_num
  have core : Tendsto (fun N : ℕ => primeRpowLogSumIoc (1/2) (N:ℝ)/(N:ℝ)^(1/2:ℝ)) atTop (𝓝 (1/(1/2))) :=
    (tendsto_primeRpowLogSumIoc half).comp tendsto_natCast_atTop_atTop
  have low : Tendsto (fun N : ℕ => (Real.sqrt (N:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have out := core.add (low.const_mul (Real.log 2/Real.sqrt 2))
  rw [show (1:ℝ)/(1/2)=2 by norm_num,mul_zero,add_zero] at out
  apply out.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hn
  have eq := expose_prime_two hn (fun p => Real.log p/Real.sqrt p)
  have point (p : ℕ) : (p:ℝ)^((1/2:ℝ)-1)*Real.log p=Real.log p/Real.sqrt p := by
    rw [show (1/2:ℝ)-1= -(1/2) by norm_num,Real.rpow_neg (Nat.cast_nonneg _),←Real.sqrt_eq_rpow]
    rw [div_eq_mul_inv,mul_comm]
  simp only [primeRpowLogSumIoc,Nat.floor_natCast,point,←Real.sqrt_eq_rpow]
  rw [eq]; push_cast; ring

private theorem root_weight (p : ℕ) : (1/(p:ℝ))^(1/2:ℝ)=1/Real.sqrt p := by
  rw [←Real.sqrt_eq_rpow,Real.sqrt_div zero_le_one,Real.sqrt_one]

private theorem log_product_error :
    ∃ A : ℝ,0<A ∧ ∀ y : ℕ,0 ≤ Real.log (deletionPrice (1/2) y)-rootSum y ∧
      Real.log (deletionPrice (1/2) y)-rootSum y ≤ A*(1+Real.log y) := by
  let r := fun p : ℕ => 1/Real.sqrt p
  let a := 1-r 2
  have h2 := deletion_weight_lt_one (s := 1/2) (by norm_num) Nat.prime_two
  rw [root_weight] at h2
  have ap : 0<a := sub_pos.mpr h2
  refine ⟨1/a,one_div_pos.mpr ap,fun y => ?_⟩
  let P := Nat.primesLE y
  have gap (p : ℕ) (hp : p ∈ P) : 0<1-r p := by
    have h := deletion_weight_lt_one (s := 1/2) (by norm_num) (Nat.prime_of_mem_primesLE hp)
    rw [root_weight] at h; exact sub_pos.mpr h
  have logprod : Real.log (deletionPrice (1/2) y)=∑ p ∈ P,Real.log ((1-r p)⁻¹) := by
    simp only [deletionPrice,root_weight]
    exact Real.log_prod (fun p hp => (inv_pos.mpr (gap p hp)).ne')
  change 0 ≤ Real.log (deletionPrice (1/2) y)-(∑ p ∈ P,r p) ∧ _
  rw [logprod]
  change 0 ≤ (∑ p ∈ P,Real.log ((1-r p)⁻¹))-(∑ p ∈ P,r p) ∧
    (∑ p ∈ P,Real.log ((1-r p)⁻¹))-(∑ p ∈ P,r p) ≤ _
  rw [←sum_sub_distrib]
  constructor
  · apply sum_nonneg
    intro p hp
    have hh := Real.log_le_sub_one_of_pos (gap p hp)
    rw [Real.log_inv]; linarith only [hh]
  · have bound (p : ℕ) (hp : p ∈ P) : Real.log ((1-r p)⁻¹)-r p ≤ (1/a)*(1/(p:ℝ)) := by
      have pr := Nat.prime_of_mem_primesLE hp
      have small : r p ≤ r 2 := one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
        (Real.sqrt_le_sqrt (show (2:ℝ) ≤ p by exact_mod_cast pr.two_le))
      have cap := Real.log_le_sub_one_of_pos (inv_pos.mpr (gap p hp))
      have alg : (1-r p)⁻¹-1-r p=(r p)^2/(1-r p) := by field_simp [(gap p hp).ne']; ring
      have sq : (r p)^2=1/(p:ℝ) := by
        dsimp only [r]; rw [div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      have step := (sub_le_sub_right cap (r p)).trans_eq alg
      exact (step.trans (div_le_div_of_nonneg_left (sq_nonneg _) ap (sub_le_sub_left small 1))).trans_eq
        (by rw [sq]; ring)
    apply (sum_le_sum bound).trans
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_finset_bounded_le_one_add_log P y
      (fun _ hp => (Nat.prime_of_mem_primesLE hp).pos) (fun _ hp => (Nat.mem_primesLE.mp hp).1)) (one_div_pos.mpr ap).le

/-- The logarithm of the half-exponent Euler product is asymptotic to
2√y/log y. Higher powers contribute a negligible normalized error. -/
theorem limit_of_the_critical_euler_price :
    Tendsto (fun y : ℕ => Real.log (deletionPrice (1/2) y)*Real.log y/Real.sqrt y) atTop (𝓝 2) := by
  obtain ⟨A,hA,price⟩ := log_product_error
  have q : 0<(1/4:ℝ) := by norm_num
  have fee := eventually_const_mul_one_add_log_pow_le_rpow q hA 2
  have cast : Tendsto (fun y : ℕ => (y:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have tiny := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop q).comp cast)
  have err : Tendsto (fun y : ℕ => (Real.log (deletionPrice (1/2) y)-rootSum y)*Real.log y/Real.sqrt y)
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ tiny
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with y yp
      exact div_nonneg (mul_nonneg (price y).1 (Real.log_nonneg (Nat.one_le_cast.mpr yp))) (Real.sqrt_nonneg _)
    · filter_upwards [cast fee,eventually_ge_atTop (1:ℕ)] with y paid yp
      let u := (y:ℝ)^(1/4:ℝ)
      have p : 0<(y:ℝ) := Nat.cast_pos.mpr yp
      have up : 0<u := Real.rpow_pos_of_pos p _
      have root := Real.sqrt_pos.mpr p
      have L := Real.log_nonneg (((Nat.one_le_cast (α := ℝ)).mpr yp))
      change A*(1+Real.log y)^2 ≤ u at paid
      have step := mul_le_mul_of_nonneg_right (price y).2 L
      have pad := mul_nonneg hA.le (show 0 ≤ 1+Real.log y by linarith only [L])
      have sq : u*u=Real.sqrt y := by
        dsimp only [u]; rw [Real.sqrt_eq_rpow,←Real.rpow_add p]; norm_num
      change _ ≤ u⁻¹
      apply (div_le_iff₀ root).mpr
      rw [←sq,←mul_assoc,inv_mul_cancel₀ up.ne',one_mul]
      linarith only [step,pad,paid]
  have both := limit_reciprocal_roots_of_primes.add err
  rw [add_zero] at both
  exact both.congr (fun y => by ring)

/-- At exponent one half the log of the deletion product has the exact
order sqrt(y)/log y. Both inequalities hold at every sufficiently large
cutoff, including the lower bound supplied by the ordinary primes. -/
theorem critical_euler_price_at_every_prime_cutoff :
    ∃ C : ℝ,0<C ∧ ∀ᶠ y : ℕ in atTop,
      (1/4)*Real.sqrt y ≤ Real.log (deletionPrice (1/2) y)*Real.log y ∧
      Real.log (deletionPrice (1/2) y)*Real.log y ≤ C*Real.sqrt y := by
  have lim := limit_of_the_critical_euler_price
  refine ⟨3,by norm_num,?_⟩
  filter_upwards [lim.eventually_const_lt (by norm_num : (1:ℝ)<2),
    lim.eventually_lt_const (by norm_num : (2:ℝ)<3),eventually_ge_atTop (1:ℕ)] with y lower upper hy
  have root := Real.sqrt_pos.mpr (((Nat.cast_pos (α := ℝ)).mpr hy))
  exact ⟨by linarith only [(lt_div_iff₀ root).mp lower,root],((div_lt_iff₀ root).mp upper).le⟩

/-- At the moving log-square cutoff the log-price has order
log X/log log X. The upper bound includes both Euler products used in
inverting a sharp cutoff and the cost of the moving endpoint. -/
theorem critical_deletion_at_the_log_square_cutoff :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,let L := Real.log (X:ℝ)
      let b := logSquareCutoff X
      let E := deletionPrice (1/2) b
      (1/32)*L ≤ Real.log E*Real.log L ∧
        ((b:ℝ)+1)*E^2 ≤ Real.exp (C*L/Real.log L) := by
  obtain ⟨C,hC,price⟩ := critical_euler_price_at_every_prime_cutoff
  have logs := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have sqfee := eventually_const_mul_one_add_log_pow_le_rpow zero_lt_one zero_lt_one 2
  refine ⟨6+4*C,by positivity,?_⟩
  filter_upwards [logSquareCutoff_tendsto_atTop price,logs sqfee,logs.eventually_ge_atTop 8,
    (Real.tendsto_log_atTop.comp logs).eventually_ge_atTop 2,eventually_ge_atTop (2:ℕ)]
    with X paid cheap large logLarge pos
  let L := Real.log (X:ℝ)
  let k := ⌊Real.log ((X:ℝ)+1)⌋₊
  let b := logSquareCutoff X
  let E := deletionPrice (1/2) b
  change 8 ≤ L at large
  change 2 ≤ Real.log L at logLarge
  have xp : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have x1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have L0 : 0<L := by linarith only [large]
  have lp : 0<Real.log L := by linarith only [logLarge]
  have log2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have endLog : Real.log ((X:ℝ)+1) ≤ Real.log 2+L := by
    change _ ≤ Real.log 2+Real.log (X:ℝ)
    rw [←Real.log_mul (by norm_num : (2:ℝ) ≠ 0) xp.ne']
    apply Real.log_le_log (by positivity)
    linarith only [x1]
  have top := Nat.floor_le (Real.log_nonneg (by linarith only [x1] : 1 ≤ (X:ℝ)+1))
  change (k:ℝ) ≤ Real.log ((X:ℝ)+1) at top
  have kmax : (k:ℝ) ≤ 2*L := by linarith only [top,endLog,log2,large]
  have lower := Real.log_le_log xp (by linarith : (X:ℝ) ≤ X+1)
  change L ≤ Real.log ((X:ℝ)+1) at lower
  have round : Real.log ((X:ℝ)+1)<(k:ℝ)+1 := Nat.lt_floor_add_one _
  have kmin : L/2 ≤ (k:ℝ) := by linarith only [lower,round,large]
  have bEq : (b:ℝ)=(k:ℝ)^2 := by simp only [b,k,logSquareCutoff,Nat.cast_pow]
  have sqrtEq : Real.sqrt b=k := by rw [bEq,Real.sqrt_sq (Nat.cast_nonneg _)]
  have bk : L ≤ (b:ℝ) := by
    rw [bEq]
    have lowSq := pow_le_pow_left₀ (by positivity : 0 ≤ L/2) kmin 2
    nlinarith only [lowSq,mul_nonneg L0.le (show 0 ≤ L-4 by linarith only [large])]
  have upper : (b:ℝ)+1 ≤ 5*L^2 := by
    rw [bEq]
    nlinarith only [pow_le_pow_left₀ (Nat.cast_nonneg _) kmax 2,
      mul_nonneg (show 0 ≤ L-1 by linarith only [large]) (show 0 ≤ L+1 by linarith only [large])]
  have b0 : (0:ℝ)<b := L0.trans_le bk
  have lelog := Real.log_le_log L0 bk
  have logB := Real.log_le_log (by positivity : 0<(b:ℝ)+1) upper
  rw [Real.log_mul (by norm_num) (pow_pos L0 2).ne',Real.log_pow] at logB
  have log5 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<5)
  have small : Real.log ((b:ℝ)+1) ≤ 4*Real.log L := by
    norm_num only [Nat.cast_ofNat] at logB; linarith only [logB,log5,logLarge]
  have logsmall := (Real.log_le_log b0 (by linarith : (b:ℝ) ≤ b+1)).trans small
  have e1 : 1 ≤ E := deletionPrice_one_le (by norm_num) b
  have en := Real.log_nonneg e1
  change (1/4)*Real.sqrt b ≤ Real.log E*Real.log b ∧ Real.log E*Real.log b ≤ C*Real.sqrt b at paid
  rw [sqrtEq] at paid
  constructor
  · linarith only [paid.1,kmin,mul_le_mul_of_nonneg_left logsmall en]
  · have sq : Real.log L^2 ≤ L := by
      change 1*(1+Real.log L)^2 ≤ L^(1:ℝ) at cheap
      rw [Real.rpow_one,one_mul] at cheap
      exact (pow_le_pow_left₀ lp.le (by linarith : Real.log L ≤ 1+Real.log L) 2).trans cheap
    have eBound := (mul_le_mul_of_nonneg_left lelog en).trans
      (paid.2.trans (mul_le_mul_of_nonneg_left kmax hC.le))
    change ((b:ℝ)+1)*E^2 ≤ _
    apply (Real.log_le_log_iff (by positivity : 0<((b:ℝ)+1)*E^2) (Real.exp_pos _)).mp
    rw [Real.log_mul (by positivity) (pow_ne_zero _ (zero_lt_one.trans_le e1).ne'),
      Real.log_pow,Real.log_exp,le_div_iff₀ lp]
    norm_num only [Nat.cast_ofNat]
    linarith only [mul_le_mul_of_nonneg_right small lp.le,sq,eBound,L0]

/-- The complete smooth main term at the critical cutoff is at most
sqrt X times exp(C log X/log log X), uniformly at all smaller prime
walls at the same observation endpoint. -/
theorem critical_upper_price_of_the_smooth_main_term :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,∀ y ≤ logSquareCutoff X,
      (y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card ≤
        Real.sqrt X*Real.exp (C*Real.log X/Real.log (Real.log X)) := by
  obtain ⟨C,hC,price⟩ := critical_deletion_at_the_log_square_cutoff
  refine ⟨C,hC,?_⟩
  filter_upwards [price] with X paid
  intro y below
  let b := logSquareCutoff X
  let E := deletionPrice (1/2) b
  have sp : 0<(1/2:ℝ) := by norm_num
  have e1 : 1 ≤ E := deletionPrice_one_le sp b
  have cap : (y:ℝ)*deletionPrice (1/2) y ≤ ((b:ℝ)+1)*E^2 := by
    have lower := (Nat.cast_le (α := ℝ)).mpr below
    have square : E ≤ E^2 := by nlinarith only [e1,sq_nonneg (E-1)]
    exact mul_le_mul (by linarith only [lower]) ((deletionPrice_mono sp below).trans square)
      (zero_le_one.trans (deletionPrice_one_le sp y)) (by positivity)
  have bound := smooth_population_le_deletion_price sp y (X/y)
  rw [←Real.sqrt_eq_rpow] at bound
  have hi := Real.sqrt_le_sqrt ((Nat.cast_le (α := ℝ)).mpr (Nat.div_le_self X y))
  have rest := bound.trans (mul_le_mul_of_nonneg_right hi (zero_le_one.trans (deletionPrice_one_le sp y)))
  have total := mul_le_mul_of_nonneg_left rest (Nat.cast_nonneg (α := ℝ) y)
  exact total.trans ((le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left (cap.trans paid.2) (Real.sqrt_nonneg _)))

#print axioms limit_of_the_critical_euler_price
#print axioms limit_log_weighted_roots_of_primes
#print axioms critical_euler_price_at_every_prime_cutoff
#print axioms critical_deletion_at_the_log_square_cutoff
#print axioms critical_upper_price_of_the_smooth_main_term

end GaloisForLFunctions.RestrictedFactorizationCalculus
