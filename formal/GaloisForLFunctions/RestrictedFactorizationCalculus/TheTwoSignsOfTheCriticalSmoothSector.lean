import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeMomentsOfAMovingCriticalEulerTilt
import GaloisForLFunctions.RHTower.RouteEMovingEulerTiltChiSquareContiguity

/-!
# Both Möbius signs in the critical smooth sector

The finite tilt on odd squarefree products has independent prime
occupations. Concentrating its logarithmic weight below the counting
endpoint permits doubling each sampled odd product to realize either sign.
-/
noncomputable section
open Filter Finset RHTower RHTower.Sieve HTGeometry.ConstraintFrameRelativity
open scoped Classical Topology ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Smooth integers up to the logarithmic height H with a prescribed Möbius sign. -/
def signedSmoothSector (b : Bool) (y : ℕ) (H : ℝ) :=
  (smoothUpTo (Nat.primesLE y) ⌊Real.exp H⌋₊).filter
    (fun n => ArithmeticFunction.moebius n=if b then (1:ℤ) else -1)

private def middleConfigurations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (m D : ℝ) :=
  (univ : Finset (Finset ι)).filter (fun S => |linearStat a S-m|<D)

/-- Chebyshev's bound on the finite Boolean gas, with its exact diagonal variance. -/
private theorem half_of_a_prime_tilt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q a : ι → ℝ) (q0 : ∀ i,0 ≤ q i) (q1 : ∀ i,q i ≤ 1)
    {D : ℝ} (dp : 0<D) (small : 2*(∑ i,(a i)^2*(q i*(1-q i))) ≤ D^2) :
    1/2 ≤ ∑ S ∈ middleConfigurations a (∑ i,a i*q i) D,bernoulliWeight q S := by
  let w := bernoulliWeight q
  let F := linearStat a
  let m := ∑ i,a i*q i
  let G := middleConfigurations a m D
  have nn (S : Finset ι) : 0 ≤ w S := bernoulliWeight_nonneg q q0 q1 S
  have mass : (∑ S,w S)=1 := by simpa only [bernoulliExp,mul_one,w] using bernoulliExp_one q
  have mean : (∑ S,w S*F S)=m := bernoulliExp_linearStat q a
  have second : (∑ S,w S*(F S-m)^2)=∑ i,(a i)^2*(q i*(1-q i)) := by
    have cov := bernoulliCov_linearStat q a a
    change (∑ S,w S*(F S*F S))-(∑ S,w S*F S)*(∑ S,w S*F S)=_ at cov
    rw [mean] at cov
    simp only [pow_two]
    rw [←cov]
    have eq (S : Finset ι) : w S*((F S-m)*(F S-m)) =
        w S*(F S*F S)-2*m*(w S*F S)+m^2*w S := by ring
    rw [sum_congr rfl (fun S _ => eq S),sum_add_distrib,sum_sub_distrib,
      ←mul_sum,←mul_sum,mass,mean]
    ring
  have point (S : Finset ι) : D^2*w S ≤
      D^2*(if S∈G then w S else 0)+w S*(F S-m)^2 := by
    by_cases good : S∈G
    · rw [if_pos good]
      exact le_add_of_nonneg_right (mul_nonneg (nn S) (sq_nonneg _))
    · rw [if_neg good,mul_zero,zero_add,mul_comm _ (w S)]
      have out : D ≤ |F S-m| := le_of_not_gt (fun h => good (mem_filter.mpr ⟨mem_univ _,h⟩))
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ dp.le out 2).trans_eq (sq_abs _)) (nn S)
  have budget := sum_le_sum (s := univ) (fun S _ => point S)
  rw [←mul_sum,mass,mul_one,sum_add_distrib,←mul_sum,second,←sum_filter] at budget
  have eq : (univ.filter (fun S : Finset ι => S∈G))=G := by ext; simp
  rw [eq] at budget
  exact (le_of_mul_le_mul_left (a := D^2) (by linarith only [small,budget]) (sq_pos_of_pos dp))

private abbrev oddPrimes (y : ℕ) := (Nat.primesLE y).erase 2
private def configurationPrimes {y : ℕ} (S : Finset ↥(oddPrimes y)) : Finset ℕ :=
  S.map (Function.Embedding.subtype (·∈oddPrimes y))
private def configurationProduct {y : ℕ} (S : Finset ↥(oddPrimes y)) :=
  ∏ p ∈ configurationPrimes S,p

private theorem configuration_factors {y : ℕ} (S : Finset ↥(oddPrimes y)) :
    ∀ p ∈ configurationPrimes S,p ∈ oddPrimes y := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := mem_map.mp hp
  exact q.property

private theorem recover_the_configuration {y : ℕ} (S : Finset ↥(oddPrimes y)) :
    (configurationProduct S).primeFactors=configurationPrimes S :=
  Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primesLE (mem_erase.mp (configuration_factors S p hp)).2)

private theorem configuration_squarefree {y : ℕ} (S : Finset ↥(oddPrimes y)) :
    Squarefree (configurationProduct S) :=
  _root_.Sieve.prodDistinctPrimes_squarefree _
    (fun p hp => Nat.prime_of_mem_primesLE (mem_erase.mp (configuration_factors S p hp)).2)

private theorem configuration_odd {y : ℕ} (S : Finset ↥(oddPrimes y)) :
    Nat.Coprime 2 (configurationProduct S) := by
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  intro dvd
  have mem := Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd,(configuration_squarefree S).ne_zero⟩
  rw [recover_the_configuration] at mem
  exact (mem_erase.mp (configuration_factors S 2 mem)).1 rfl

private theorem log_configuration {y : ℕ} (S : Finset ↥(oddPrimes y)) :
    Real.log (configurationProduct S) = linearStat (fun p : ↥(oddPrimes y) => Real.log (p:ℕ)) S := by
  unfold configurationProduct
  rw [Nat.cast_prod,Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr
    (Nat.prime_of_mem_primesLE (mem_erase.mp (configuration_factors S p hp)).2).ne_zero)]
  simp only [configurationPrimes,sum_map,Function.Embedding.subtype_apply,linearStat]

/-- Select either sign by using each odd product itself or its double. -/
private def signedProduct {y : ℕ} (b : Bool) (S : Finset ↥(oddPrimes y)) :=
  if ArithmeticFunction.moebius (configurationProduct S)=(if b then (1:ℤ) else -1)
  then configurationProduct S else 2*configurationProduct S

private theorem signed_product_injective {y : ℕ} (b : Bool) :
    Function.Injective (signedProduct (y := y) b) := by
  intro S T h
  have same : configurationProduct S=configurationProduct T := by
    let target : ℤ := if b then 1 else -1
    change (if μ (configurationProduct S)=target then configurationProduct S else 2*configurationProduct S)=
      (if μ (configurationProduct T)=target then configurationProduct T else 2*configurationProduct T) at h
    split_ifs at h with i j j
    · exact h
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp (configuration_odd S))
        (by rw [h]; exact dvd_mul_right 2 _))
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp (configuration_odd T))
        (by rw [←h]; exact dvd_mul_right 2 _))
    · exact Nat.eq_of_mul_eq_mul_left (by decide : 0<2) h
  have eq := congrArg Nat.primeFactors same
  rw [recover_the_configuration,recover_the_configuration] at eq
  exact Finset.map_injective _ eq

private theorem signed_product_below {y : ℕ} (yp : 2 ≤ y) (b : Bool) (H : ℝ)
    (S : Finset ↥(oddPrimes y)) (small : Real.log (configurationProduct S)+Real.log 2 ≤ H) :
    signedProduct b S ∈ signedSmoothSector b y H := by
  let n := configurationProduct S
  have sq : Squarefree n := configuration_squarefree S
  have np := Nat.pos_of_ne_zero sq.ne_zero
  have p0 : 0<(n:ℝ) := Nat.cast_pos.mpr np
  have hi : 2*n ≤ ⌊Real.exp H⌋₊ := by
    apply Nat.le_floor
    push_cast
    apply (Real.log_le_log_iff (mul_pos (by norm_num) p0) (Real.exp_pos _)).mp
    rw [Real.log_mul (by norm_num) p0.ne',Real.log_exp,add_comm]
    exact small
  have sm : n.primeFactors ⊆ Nat.primesLE y := by
    rw [show n.primeFactors=configurationPrimes S from recover_the_configuration S]
    exact fun p hp => (mem_erase.mp (configuration_factors S p hp)).2
  change (if μ n=(if b then (1:ℤ) else -1) then n else 2*n) ∈ _
  by_cases fixed : μ n=(if b then (1:ℤ) else -1)
  · rw [if_pos fixed]
    exact mem_filter.mpr ⟨mem_smoothUpTo.mpr ⟨⟨np,by omega⟩,sm⟩,fixed⟩
  · rw [if_neg fixed]
    have signs := ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp
        (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr sq)
    apply mem_filter.mpr
    refine ⟨mem_smoothUpTo.mpr ⟨⟨by omega,hi⟩,?_⟩,?_⟩
    · rw [Nat.primeFactors_mul (by decide : (2:ℕ) ≠ 0) sq.ne_zero,Nat.prime_two.primeFactors]
      exact union_subset (singleton_subset_iff.mpr (Nat.mem_primesLE.mpr ⟨yp,Nat.prime_two⟩)) sm
    · rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (configuration_odd S),
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      change (-1:ℤ)*μ n=(if b then 1 else -1)
      cases b <;> simp only [Bool.false_eq_true,if_false,if_true,neg_one_mul] at fixed ⊢ <;> omega

private def occupation (s : ℝ) (p : ℕ) := (p:ℝ)^(-s)/(1+(p:ℝ)^(-s))

private theorem occupation_bounds (s : ℝ) {p : ℕ} (prime : p.Prime) :
    0 ≤ occupation s p ∧ occupation s p ≤ 1 := by
  have u := Real.rpow_pos_of_pos (Nat.cast_pos.mpr prime.pos : (0:ℝ)<p) (-s)
  have h := add_pos zero_lt_one u
  exact ⟨div_nonneg u.le h.le,(div_le_one h).mpr (by linarith)⟩

private theorem tilt_weight_by_log_product (y : ℕ) (s : ℝ) (S : Finset ↥(oddPrimes y)) :
    let Z := ∑ p ∈ oddPrimes y,Real.log (1+(p:ℝ)^(-s))
    bernoulliWeight (fun p : ↥(oddPrimes y) => occupation s (p:ℕ)) S*Real.exp Z =
      Real.exp (-s*Real.log (configurationProduct S)) := by
  let u := fun p : ↥(oddPrimes y) => ((p:ℕ):ℝ)^(-s)
  let z := fun p => 1+u p
  have prime (p : ↥(oddPrimes y)) := Nat.prime_of_mem_primesLE (mem_erase.mp p.property).2
  have up (p : ↥(oddPrimes y)) : 0<u p := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (prime p).pos) _
  have zp (p : ↥(oddPrimes y)) : 0<z p := add_pos zero_lt_one (up p)
  have part : Real.exp (∑ p ∈ oddPrimes y,Real.log (1+(p:ℝ)^(-s)))=∏ p,z p := by
    rw [←sum_coe_sort,←Real.log_prod (fun p _ => (zp p).ne'),Real.exp_log (prod_pos (fun p _ => zp p))]
  have a (p : ↥(oddPrimes y)) : occupation s (p:ℕ)*z p=u p :=
    div_mul_cancel₀ _ (zp p).ne'
  have b (p : ↥(oddPrimes y)) : (1-occupation s (p:ℕ))*z p=1 := by
    rw [sub_mul,one_mul,a]; dsimp only [z]; ring
  change bernoulliWeight _ S*Real.exp (∑ p ∈ oddPrimes y,Real.log (1+(p:ℝ)^(-s)))=_
  rw [part,←prod_mul_prod_compl S z,bernoulliWeight,mul_mul_mul_comm,←prod_mul_distrib,←prod_mul_distrib]
  simp only [a,b,prod_const_one,mul_one]
  rw [log_configuration,linearStat,mul_sum,Real.exp_sum]
  apply prod_congr rfl
  intro p _
  dsimp only [u]
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (prime p).pos)]
  congr 1; ring

private theorem odd_tilt_at_a_calibrated_mean {y : ℕ} (yp : 2 ≤ y) {s H D : ℝ}
    (sp : 0 ≤ s) (dp : 0<D) (shift : squarefreeEulerMean s y=H-2*D)
    (space : Real.log 2 ≤ D) (variance : 2*Real.log y*(H-2*D) ≤ D^2) (b : Bool) :
    s*(H-4*D)+squarefreeEulerLog s y-2*Real.log 2 ≤ Real.log (signedSmoothSector b y H).card := by
  let P := oddPrimes y
  let q := fun p : ↥P => occupation s (p:ℕ)
  let a := fun p : ↥P => Real.log (p:ℕ)
  let m := ∑ p,a p*q p
  let G := middleConfigurations a m D
  let Z := ∑ p ∈ P,Real.log (1+(p:ℝ)^(-s))
  have prime (p : ↥P) := Nat.prime_of_mem_primesLE (mem_erase.mp p.property).2
  have q0 (p : ↥P) : 0 ≤ q p := (occupation_bounds s (prime p)).1
  have q1 (p : ↥P) : q p ≤ 1 := (occupation_bounds s (prime p)).2
  have a0 (p : ↥P) : 0 ≤ a p := Real.log_natCast_nonneg _
  have ly (p : ↥P) : a p ≤ Real.log y := Real.log_le_log (Nat.cast_pos.mpr (prime p).pos)
    (Nat.cast_le.mpr (Nat.mem_primesLE.mp (mem_erase.mp p.property).2).1)
  have two : 2∈Nat.primesLE y := Nat.mem_primesLE.mpr ⟨yp,Nat.prime_two⟩
  have add := sum_erase_add (Nat.primesLE y) (fun p : ℕ => Real.log p*occupation s p) two
  change _=squarefreeEulerMean s y at add
  rw [←sum_coe_sort,shift] at add
  change m+Real.log 2*occupation s 2=H-2*D at add
  have bounds := occupation_bounds s Nat.prime_two
  have l2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have lo : H-3*D ≤ m := by linarith only [add,mul_le_of_le_one_right l2 bounds.2,space]
  have hi : m ≤ H-2*D := by linarith only [add,mul_nonneg l2 bounds.1]
  have V : (∑ p,(a p)^2*(q p*(1-q p))) ≤ Real.log y*m := by
    dsimp only [m]
    rw [mul_sum]
    apply sum_le_sum
    intro p _
    calc _ = (a p*(1-q p))*(a p*q p) := by ring
         _ ≤ Real.log y*(a p*q p) := mul_le_mul_of_nonneg_right
           ((mul_le_of_le_one_right (a0 p) (sub_le_self _ (q0 p))).trans (ly p)) (mul_nonneg (a0 p) (q0 p))
  have vcap := V.trans (mul_le_mul_of_nonneg_left hi (Real.log_natCast_nonneg y))
  have mass : 1/2 ≤ ∑ S ∈ G,bernoulliWeight q S :=
    half_of_a_prime_tilt q a q0 q1 dp (by linarith only [variance,vcap])
  have window (S : Finset ↥P) (h : S∈G) :
      H-4*D ≤ Real.log (configurationProduct S) ∧ Real.log (configurationProduct S)+Real.log 2 ≤ H := by
    have dist := abs_lt.mp (mem_filter.mp h).2
    rw [log_configuration]
    change H-4*D ≤ linearStat a S ∧ linearStat a S+Real.log 2 ≤ H
    constructor <;> linarith only [dist.1,dist.2,lo,hi,space]
  have per (S : Finset ↥P) (h : S∈G) :
      bernoulliWeight q S*(Real.exp Z*Real.exp (s*(H-4*D))) ≤ 1 := by
    rw [←mul_assoc,tilt_weight_by_log_product,←Real.exp_add]
    apply (Real.exp_le_one_iff).mpr
    linarith only [mul_le_mul_of_nonneg_left (window S h).1 sp]
  have count := sum_le_sum per
  rw [←sum_mul,Finset.sum_const,nsmul_eq_mul,mul_one] at count
  have image_size : G.card ≤ (signedSmoothSector b y H).card := card_le_card_of_injOn
    (signedProduct b) (fun S h => signed_product_below yp b H S (window S h).2) (signed_product_injective b).injOn
  have lower : (1/2:ℝ)*(Real.exp Z*Real.exp (s*(H-4*D))) ≤ (signedSmoothSector b y H).card :=
    (mul_le_mul_of_nonneg_right mass (by positivity)).trans (count.trans (Nat.cast_le.mpr image_size))
  have loglower := Real.log_le_log (by positivity : (0:ℝ)<(1/2)*(Real.exp Z*Real.exp (s*(H-4*D)))) lower
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at loglower
  have price := sum_erase_add (Nat.primesLE y) (fun p : ℕ => Real.log (1+(p:ℝ)^(-s))) two
  change Z+Real.log (1+(2:ℝ)^(-s))=squarefreeEulerLog s y at price
  have atom : (2:ℝ)^(-s) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (neg_nonpos.mpr sp)
  have fee := Real.log_le_log (add_pos zero_lt_one (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _))
    (show 1+(2:ℝ)^(-s) ≤ 2 by linarith only [atom])
  linarith only [price,fee,loglower]

private abbrev allSmoothSector (y : ℕ) (H : ℝ) := smoothUpTo (Nat.primesLE y) ⌊Real.exp H⌋₊

private theorem signed_sector_nonempty {y : ℕ} (yp : 2 ≤ y) {H : ℝ} (large : Real.log 2 ≤ H) (b : Bool) :
    (signedSmoothSector b y H).Nonempty := by
  have h : Real.log (configurationProduct (∅ : Finset ↥(oddPrimes y)))+Real.log 2 ≤ H := by
    simpa [configurationProduct,configurationPrimes] using large
  exact ⟨_,signed_product_below yp b H ∅ h⟩

private theorem log_rankin_at_a_real_height {H s : ℝ} (sp : 0<s) (hp : 0 ≤ H) (y : ℕ) :
    Real.log (allSmoothSector y H).card ≤ s*H+Real.log (deletionPrice s y) := by
  let T := ⌊Real.exp H⌋₊
  have E := zero_lt_one.trans_le (deletionPrice_one_le sp y)
  have one : 1∈allSmoothSector y H := mem_smoothUpTo.mpr ⟨⟨le_rfl,Nat.le_floor (by simpa using Real.exp_le_exp.mpr hp)⟩,by simp⟩
  have card : (0:ℝ)<(allSmoothSector y H).card := Nat.cast_pos.mpr (card_pos.mpr ⟨1,one⟩)
  have paid := smooth_population_le_deletion_price sp y T
  have cap := Real.rpow_le_rpow (Nat.cast_nonneg T) (Nat.floor_le (Real.exp_pos H).le) sp.le
  rw [←Real.exp_mul] at cap
  have bound := Real.log_le_log card (paid.trans (mul_le_mul_of_nonneg_right cap E.le))
  rwa [Real.log_mul (Real.exp_pos _).ne' E.ne',Real.log_exp,mul_comm H s] at bound

private abbrev saddleWidth (y : ℕ) := (y:ℝ)^(1/3:ℝ)

private theorem saddle_scales {Y : ℕ → ℕ} (wall : Tendsto Y atTop atTop) :
    Tendsto (fun n => saddleWidth (Y n)/Real.sqrt (Y n)) atTop (𝓝 0) ∧
    Tendsto (fun n => saddleWidth (Y n)*Real.log (Y n)/Real.sqrt (Y n)) atTop (𝓝 0) ∧
    Tendsto (fun n => Real.log (Y n)/Real.sqrt (Y n)) atTop (𝓝 0) := by
  have cast : Tendsto (fun n => (Y n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp wall
  have p : (0:ℝ)<1/6 := by norm_num
  have inv : Tendsto (fun n => ((Y n:ℝ)^(1/6:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop p).comp cast)
  have log : Tendsto (fun n => Real.log (Y n)/(Y n:ℝ)^(1/6:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop p).tendsto_div_nhds_zero.comp cast
  have half : Tendsto (fun n => Real.log (Y n)/(Y n:ℝ)^(1/2:ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp cast
  have sq (y : ℕ) (yp : 0<y) : Real.sqrt y=saddleWidth y*(y:ℝ)^(1/6:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add (Nat.cast_pos.mpr yp)]; norm_num
  refine ⟨inv.congr' ?_,log.congr' ?_,?_⟩
  · filter_upwards [wall.eventually_ge_atTop 1] with n yn
    rw [sq _ yn]
    field_simp [(Real.rpow_pos_of_pos (Nat.cast_pos.mpr yn : (0:ℝ)<Y n) (1/3)).ne',
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr yn : (0:ℝ)<Y n) (1/6)).ne']
  · filter_upwards [wall.eventually_ge_atTop 1] with n yn
    rw [sq _ yn]
    field_simp [(Real.rpow_pos_of_pos (Nat.cast_pos.mpr yn : (0:ℝ)<Y n) (1/3)).ne',
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr yn : (0:ℝ)<Y n) (1/6)).ne']
  · simpa only [Real.sqrt_eq_rpow] using half

/-- At log-height H asymptotic to a√y, the coefficient of √y/log y after
subtracting H/2 is a(1+log(2/a)), both for either squarefree sign and for
all smooth integers with unrestricted prime multiplicities. -/
theorem critical_smooth_counts_of_both_signs {Y : ℕ → ℕ} (wall : Tendsto Y atTop atTop)
    {H : ℕ → ℝ} {a : ℝ} (ap : 0<a)
    (size : Tendsto (fun n => H n/Real.sqrt (Y n)) atTop (𝓝 a)) :
    let sCount := fun n b => (signedSmoothSector b (Y n) (H n)).card
    let allCount := fun n => (allSmoothSector (Y n) (H n)).card
    let energy := fun (f : ℕ → ℕ) n => (Real.log (f n)-H n/2)*Real.log (Y n)/Real.sqrt (Y n)
    (∀ b,Tendsto (energy (fun n => sCount n b)) atTop (𝓝 (a*(1+Real.log (2/a))))) ∧
      Tendsto (energy allCount) atTop (𝓝 (a*(1+Real.log (2/a)))) := by
  let R := fun n => Real.sqrt (Y n)
  let l := fun n => Real.log (Y n)
  let D := fun n => saddleWidth (Y n)
  let c := Real.log (2/a)
  have cast : Tendsto (fun n => (Y n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp wall
  have root : Tendsto R atTop atTop := Real.tendsto_sqrt_atTop.comp cast
  have logtop : Tendsto l atTop atTop := Real.tendsto_log_atTop.comp cast
  have width : Tendsto D atTop atTop := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).comp cast
  obtain ⟨dr,dlr,lr⟩ := saddle_scales wall
  have norm : Tendsto (fun n => (H n-2*D n)/R n) atTop (𝓝 a) := by
    have h := size.sub (dr.const_mul 2)
    simpa only [mul_zero,sub_zero,sub_div,mul_div_assoc] using h
  obtain ⟨b,conv,saddle⟩ := calibrate_the_finite_prime_mean wall ap norm
  let s := fun n => criticalWallTilt (b n) (Y n)
  have st : Tendsto s atTop (𝓝 (1/2)) := by
    simpa only [s,criticalWallTilt,add_zero] using (conv.div_atTop logtop).const_add (1/2:ℝ)
  obtain ⟨squarefree,geometric,_⟩ := critical_euler_partition_and_mean_limits wall conv
  have coeff : 2*Real.exp (-Real.log (2/a))=a := by
    rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) ap)]; field_simp
  rw [coeff] at squarefree geometric
  have pay := dlr.mul norm
  rw [zero_mul] at pay
  have condition : ∀ᶠ n in atTop,2*l n*(H n-2*D n) ≤ D n^2 := by
    filter_upwards [pay.eventually_lt_const (by norm_num : (0:ℝ)<1/2),wall.eventually_ge_atTop 1] with n tiny yn
    have pos : (0:ℝ)<Y n := Nat.cast_pos.mpr yn
    have rp : 0<R n := Real.sqrt_pos.mpr pos
    have dp : 0<D n := Real.rpow_pos_of_pos pos _
    have cube : D n^3=R n^2 := by
      rw [Real.sq_sqrt pos.le]
      change ((Y n:ℝ)^(1/3:ℝ))^3=_
      rw [←Real.rpow_mul_natCast pos.le]; norm_num
    change D n*l n/R n*((H n-2*D n)/R n)<1/2 at tiny
    have up : 2*(D n*l n)*(H n-2*D n) ≤ R n^2 := by
      rw [div_mul_div_comm] at tiny
      have h := (div_lt_iff₀ (mul_pos rp rp)).mp tiny
      linarith only [h]
    apply le_of_mul_le_mul_left (a := D n) _ dp
    linarith only [up,cube]
  have target := conv.mul size
  have main : ∀ Z : ℕ → ℝ,Tendsto (fun n => Z n*l n/R n) atTop (𝓝 a) →
      Tendsto (fun n => (s n*H n+Z n-H n/2)*l n/R n) atTop (𝓝 (a*(1+c))) := by
    intro Z z
    have h := target.add z
    rw [show Real.log (2/a)*a+a=a*(1+c) by dsimp only [c]; ring] at h
    apply h.congr'
    filter_upwards [logtop.eventually_gt_atTop 0] with n lp
    change b n*(H n/R n)+Z n*l n/R n=_
    change _=((1/2+b n/l n)*H n+Z n-H n/2)*l n/R n
    field_simp [lp.ne']; ring
  have lower := main _ squarefree
  have upper := main _ geometric
  have loss := ((st.mul dlr).const_mul 4).add (lr.const_mul (2*Real.log 2))
  simp only [mul_zero,zero_add] at loss
  have lower' := lower.sub loss
  rw [sub_zero] at lower'
  have Hlarge : ∀ᶠ n in atTop, Real.log 2 ≤ H n := by
    filter_upwards [size.eventually_const_lt (half_lt_self ap),root.eventually_gt_atTop (2*Real.log 2/a),
      wall.eventually_ge_atTop 1] with n high room yn
    have rp : 0<R n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr yn)
    have h := (lt_div_iff₀ rp).mp high
    have k := (div_lt_iff₀ ap).mp room
    linarith only [h,k]
  have bound (t : Bool) : ∀ᶠ n in atTop,
      let normalize := fun x => (x-H n/2)*l n/R n
      let f := squarefreeEulerLog (s n) (Y n)
      let g := Real.log (deletionPrice (s n) (Y n))
      normalize (s n*H n+f)-(4*(s n*(D n*l n/R n))+2*Real.log 2*(l n/R n)) ≤
        normalize (Real.log (signedSmoothSector t (Y n) (H n)).card) ∧
      normalize (Real.log (signedSmoothSector t (Y n) (H n)).card) ≤
        normalize (Real.log (allSmoothSector (Y n) (H n)).card) ∧
      normalize (Real.log (allSmoothSector (Y n) (H n)).card) ≤ normalize (s n*H n+g) := by
    filter_upwards [wall.eventually_ge_atTop 2,saddle,st.eventually_const_lt (by norm_num : (0:ℝ)<1/2),
      width.eventually_ge_atTop (Real.log 2),condition,Hlarge] with n yn hit sp room var hH
    let N := fun x : ℝ => (x-H n/2)*l n/R n
    have mono : Monotone N := fun x z xz => div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sub_le_sub_right xz _) (Real.log_natCast_nonneg _)) (Real.sqrt_nonneg _)
    have dp : 0<D n := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega : 0<Y n)) _
    have lo := mono (odd_tilt_at_a_calibrated_mean yn sp.le dp hit room var t)
    have hi := mono (log_rankin_at_a_real_height sp ((Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)).trans hH) (Y n))
    have sub := card_le_card (filter_subset (fun m : ℕ => μ m=if t then (1:ℤ) else -1) (allSmoothSector (Y n) (H n)))
    have mid := mono (Real.log_le_log (Nat.cast_pos.mpr (card_pos.mpr (signed_sector_nonempty yn hH t))) (Nat.cast_le.mpr sub))
    refine ⟨le_trans (le_of_eq ?_) lo,mid,hi⟩
    dsimp only [N]; ring
  constructor
  · intro t
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' lower' upper
      ((bound t).mono (fun _ h => h.1)) ((bound t).mono (fun _ h => h.2.1.trans h.2.2))
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' lower' upper
      ((bound true).mono (fun _ h => h.1.trans h.2.1)) ((bound true).mono (fun _ h => h.2.2))

#print axioms critical_smooth_counts_of_both_signs

end GaloisForLFunctions.RestrictedFactorizationCalculus
