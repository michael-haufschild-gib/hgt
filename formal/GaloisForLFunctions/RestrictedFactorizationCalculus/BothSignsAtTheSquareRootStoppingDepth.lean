import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSquareRootStoppingDepth
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary
import GaloisForLFunctions.RHTower.Sieve.KubalalikaLargeScale
import GaloisForLFunctions.RHTower.Sieve.MoebiusSquarefreeSmoothRankin

/-!
# Large signed layers at the stopping depth

At each sharp cutoff, distinct products of primes from one box realize
both parities immediately above the moving stopping depth. The factorial
in the binomial count forces an unbounded excess over the endpoint power.
-/

noncomputable section

open Filter Finset
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching RHTower.PrimeCells

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem half_factorial (j : ℕ) : 2^(j/2)*j.factorial ≤ j^j := by
  let m := j/2
  have hm : m ≤ j := Nat.div_le_self ..
  have eq := Nat.factorial_mul_descFactorial (Nat.sub_le j m)
  rw [Nat.sub_sub_self hm] at eq
  rw [←eq]
  calc 2^m*(m.factorial*j.descFactorial (j-m)) ≤ 2^m*(m^m*j^(j-m)) :=
         Nat.mul_le_mul_left _ (Nat.mul_le_mul m.factorial_le_pow (Nat.descFactorial_le_pow ..))
       _ = (2*m)^m*j^(j-m) := by rw [mul_pow]; ring
       _ ≤ j^m*j^(j-m) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by dsimp only [m]; omega) _)
       _ = _ := by rw [←pow_add,Nat.add_sub_of_le hm]

private theorem choose_box_lower {P j : ℕ} (hj : 0<j) {q : ℝ} (hq : 0 ≤ q)
    (supply : (j:ℝ)*q ≤ ((P-j:ℕ):ℝ)) :
    (2:ℝ)^(j/2)*q^j ≤ P.choose j := by
  have h := (Nat.pow_le_pow_left (by omega : P-j ≤ P+1-j) j).trans (Nat.pow_sub_le_descFactorial P j)
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have h' : ((P-j:ℕ):ℝ)^j ≤ (j.factorial:ℝ)*(P.choose j:ℝ) := by exact_mod_cast h
  have low := (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hq) supply j).trans h'
  rw [mul_pow] at low
  have top : (2:ℝ)^(j/2)*(j.factorial:ℝ) ≤ (j:ℝ)^j := by exact_mod_cast half_factorial j
  have both := (mul_le_mul_of_nonneg_right top (pow_nonneg hq j)).trans low
  apply (mul_le_mul_iff_left₀ (Nat.cast_pos.mpr j.factorial_pos : (0:ℝ)<j.factorial)).mp
  calc ((2:ℝ)^(j/2)*q^j)*(j.factorial:ℝ)=((2:ℝ)^(j/2)*j.factorial)*q^j := by ring
       _ ≤ _ := both.trans_eq (mul_comm ..)

/-- Distinct j-prime products really occur in the sharp signed layer
whenever their common box fits below the observation cutoff. -/
private theorem prime_box_le_layer (Y j X : ℕ) (size : Y^j ≤ X) :
    (Nat.primesLE Y).card.choose j ≤ ((terminalAtDepth j X).filter
      (fun n => n.primeFactors.card=j ∧ μ n=(-1:ℤ)^j ∧ n.primeFactors ⊆ Nat.primesLE Y)).card := by
  let P := Nat.primesLE Y
  rw [←card_powersetCard]
  apply card_le_card_of_injOn (fun S : Finset ℕ => ∏ p ∈ S,p)
  · intro S hS
    obtain ⟨sub,card⟩ := mem_powersetCard.mp hS
    have prime (p : ℕ) (hp : p ∈ S) := Nat.prime_of_mem_primesLE (sub hp)
    obtain ⟨sq,factors,hpos⟩ := squarefree_and_primeFactors_prod_primes prime
    have bound : (∏ p ∈ S,p) ≤ Y^j := by
      rw [←card,←prod_const]
      exact prod_le_prod' (fun p hp => (Nat.mem_primesLE.mp (sub hp)).1)
    have cnt := congrArg Finset.card factors
    rw [card] at cnt
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos,bound.trans size⟩,sq⟩,cnt.ge⟩,
      cnt,?_,factors ▸ sub⟩
    rw [moebius_apply_of_squarefree sq,cardFactors_of_squarefree sq,cnt]
  · intro S hS V hV eq
    obtain ⟨subS,_⟩ := mem_powersetCard.mp hS
    obtain ⟨subV,_⟩ := mem_powersetCard.mp hV
    have s := (squarefree_and_primeFactors_prod_primes (fun p hp => Nat.prime_of_mem_primesLE (subS hp))).2.1
    have v := (squarefree_and_primeFactors_prod_primes (fun p hp => Nat.prime_of_mem_primesLE (subV hp))).2.1
    exact s.symm.trans ((congrArg Nat.primeFactors eq).trans v)

private theorem prime_supply_for_box :
    ∀ᶠ y : ℝ in atTop,(19/20)*y ≤ ((Nat.primesLE ⌊y⌋₊).card:ℝ)*Real.log y := by
  obtain ⟨C,hC,T,hT,bound⟩ := exists_abs_theta_sub_le 1
  filter_upwards [eventually_ge_atTop T,Real.tendsto_log_atTop.eventually_ge_atTop (20*C)] with y hy hl
  have hh := (abs_le.mp (bound y hy)).1
  have y0 : 0 ≤ y := by linarith only [hy,hT]
  have l0 : 0<Real.log y := Real.log_pos (by linarith only [hy,hT])
  have small : C*y/Real.log y ≤ y/20 := (div_le_iff₀ l0).mpr (by
    linarith only [mul_le_mul_of_nonneg_right hl y0])
  have hsig := theta_sub_le_card_mul_log (a := 0) le_rfl y0
  rw [windowPrimes_eq_primesLE_sdiff] at hsig
  simp only [Nat.floor_zero,Nat.primesLE_zero,sdiff_empty,Chebyshev.theta_zero,sub_zero] at hsig
  simp only [pow_one] at hh
  linarith only [hh,small,hsig]

private def boxGain : ℝ := Real.log (9/10)+(1/2)*Real.log 2

private theorem boxGain_pos : 0<boxGain := by
  have h := Real.log_pos (by norm_num : (1:ℝ)<(9/10)^2*2)
  rw [Real.log_mul (by norm_num) (by norm_num),Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  dsimp only [boxGain]
  linarith only [h]

/-- The binomial coefficient retains a positive exponential gain in the
number of factors after the leading power of X has been extracted. -/
private theorem box_entropy {L : ℝ} (hL : 0<L) {j : ℕ} (hj : 0<j)
    (Y : ℝ) (logY : Real.log Y=L/j) (y0 : 0<Y) (large : 20*L ≤ Y)
    {P : ℕ} (supply : (19/20)*Y ≤ (P:ℝ)*Real.log Y) :
    Real.exp (L-(j:ℝ)*Real.log L+j*boxGain-Real.log 2) ≤ P.choose j := by
  have j0 : (0:ℝ)<j := Nat.cast_pos.mpr hj
  rw [logY,mul_div_assoc',le_div_iff₀ j0] at supply
  have enough : (j:ℝ)*((9/10)*Y/L)+j ≤ P := by
    apply (le_of_mul_le_mul_right _ hL)
    have one := mul_le_mul_of_nonneg_left large j0.le
    calc ((j:ℝ)*((9/10)*Y/L)+j)*L = j*((9/10)*Y)+j*L := by field_simp
         _ ≤ _ := by linarith only [one,supply]
  have jP : j ≤ P := by
    exact_mod_cast (show (j:ℝ) ≤ P from (le_add_of_nonneg_left (by positivity)).trans enough)
  let q := (9/10)*Y/L
  have q0 : 0<q := by dsimp only [q]; positivity
  have h := choose_box_lower hj q0.le (show (j:ℝ)*q ≤ ((P-j:ℕ):ℝ) by
    rw [Nat.cast_sub jP]; linarith only [enough])
  apply LE.le.trans _ h
  apply (Real.log_le_log_iff (Real.exp_pos _) (mul_pos (pow_pos (by norm_num) _) (pow_pos q0 _))).mp
  rw [Real.log_exp,Real.log_mul (pow_pos (by norm_num : (0:ℝ)<2) _).ne' (pow_pos q0 _).ne',
    Real.log_pow,Real.log_pow]
  have lq : Real.log q=Real.log (9/10)+L/j-Real.log L := by
    rw [q,Real.log_div (by positivity) hL.ne',Real.log_mul (by norm_num) y0.ne',logY]
  have half : (j:ℝ) ≤ 2*((j/2:ℕ):ℝ)+2 := by exact_mod_cast (by omega : j ≤ 2*(j/2)+2)
  have jdiv : (j:ℝ)*(L/j)=L := by field_simp
  rw [lq]
  dsimp only [boxGain]
  linarith only [jdiv,mul_le_mul_of_nonneg_right half (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]

/-- Uniform calibration of both rounding choices for the depth. -/
private theorem calibrated_box {α : ℝ} (hα : 0<α) (small : α<1) (K : ℝ) :
    ∀ᶠ L : ℝ in atTop,∀ j : ℕ,α*L/Real.log L ≤ j → (j:ℝ) ≤ α*L/Real.log L+2 →
      0<j ∧ 20*L ≤ Real.exp (L/j) ∧
        Real.log K+Real.log 2+2*Real.log L ≤ (j:ℝ)*(boxGain/2) := by
  let A := (1+α)/2
  have a0 : 0<A := by dsimp only [A]; positivity
  have gap : 0<A-α := by dsimp only [A]; linarith only [small]
  have extra : 0<1/A-1 := by rw [sub_pos,lt_div_iff₀ a0]; dsimp only [A]; linarith only [small]
  let c := min 1 (α*(boxGain/2)/3)
  have cp : 0<c := lt_min zero_lt_one (div_pos (mul_pos hα (half_pos boxGain_pos)) (by norm_num))
  have square := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound cp
  have linear := Real.isLittleO_log_id_atTop.bound (show 0<(A-α)/2 by positivity)
  filter_upwards [eventually_ge_atTop (2:ℝ),linear,square,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log 20/(1/A-1)),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log K+Real.log 2)] with L L2 lin sq le20 kcap
  intro j lo hi
  have L1 : 1<L := by linarith only [L2]
  have lp := Real.log_pos L1
  have L0 := zero_lt_one.trans L1
  change ‖Real.log L‖ ≤ _*‖L‖ at lin
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg lp.le,abs_of_nonneg L0.le] at lin
  change ‖Real.log L‖ ≤ c*‖L^(1/2:ℝ)‖ at sq
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg lp.le,
    abs_of_nonneg (Real.rpow_nonneg L0.le _),←Real.sqrt_eq_rpow] at sq
  have c1 : c ≤ 1 := min_le_left ..
  have c2 : c ≤ α*(boxGain/2)/3 := min_le_right ..
  have weak := sq.trans ((mul_le_mul_of_nonneg_right c1 (Real.sqrt_nonneg L)).trans_eq (one_mul _))
  have two := (mul_le_mul sq weak lp.le (mul_nonneg cp.le (Real.sqrt_nonneg L)))
  rw [mul_assoc,Real.mul_self_sqrt L0.le] at two
  have low := (div_le_iff₀ lp).mp lo
  have hi' : (j:ℝ)*Real.log L ≤ α*L+2*Real.log L := by
    have prod := mul_le_mul_of_nonneg_right hi lp.le
    rwa [add_mul,div_mul_cancel₀ _ lp.ne'] at prod
  have jl : (j:ℝ)*Real.log L ≤ A*L := by linarith only [hi',lin]
  have jp : (0:ℝ)<j := lt_of_lt_of_le (div_pos (mul_pos hα L0) lp) lo
  refine ⟨Nat.cast_pos.mp jp,?_,?_⟩
  · have se := (div_le_iff₀ extra).mp le20
    have together : (Real.log 20+Real.log L)*(j:ℝ) ≤ L := by
      have jr := mul_le_mul_of_nonneg_right se jp.le
      have rent := mul_le_mul_of_nonneg_left jl (one_div_pos.mpr a0).le
      have eq : 1/A*(A*L)=L := by field_simp
      rw [eq] at rent
      linarith only [rent,jr]
    apply (Real.log_le_log_iff (by positivity : 0<20*L) (Real.exp_pos _)).mp
    rw [Real.log_mul (by norm_num) L0.ne',Real.log_exp]
    exact (le_div_iff₀ jp).mpr together
  · have fund := mul_le_mul_of_nonneg_right c2 L0.le
    have minj := mul_le_mul_of_nonneg_right low (half_pos boxGain_pos).le
    have gain : 3*Real.log L ≤ (j:ℝ)*(boxGain/2) := by
      apply le_of_mul_le_mul_right _ lp
      linarith only [two,fund,minj]
    linarith only [gain,kcap]

/-- The exact depth and sign, retaining the prime box producing the lower bound. -/
def stoppingPrimeBox (j X : ℕ) := (terminalAtDepth j X).filter (fun n =>
  n.primeFactors.card=j ∧ μ n=(-1:ℤ)^j ∧
    n.primeFactors ⊆ Nat.primesLE ⌊Real.exp (Real.log (X:ℝ)/j)⌋₊)

/-- The endpoint gain is exponential in the number of factors. Each
of the two adjacent depths achieves it inside a single prime box. -/
theorem exponential_excess_in_both_stopping_prime_boxes :
    ∃ t : ℝ,0<t ∧ ∀ (α : ℝ),0<α → α<1 → ∀ B : ℝ,
      ∀ᶠ X : ℕ in atTop,∀ j : ℕ,stoppingDepth α X ≤ j → j ≤ stoppingDepth α X+1 →
        B*(X:ℝ)^(1-α)*Real.exp (t*j) ≤ (stoppingPrimeBox j X).card := by
  refine ⟨boxGain/2,half_pos boxGain_pos,?_⟩
  intro α hα small B
  let K := max 1 B
  have Kpos : 0<K := zero_lt_one.trans_le (le_max_left ..)
  have logs : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Y0,primes⟩ := eventually_atTop.mp prime_supply_for_box
  filter_upwards [logs (calibrated_box hα small K),logs.eventually_ge_atTop (max 2 Y0),
    eventually_ge_atTop (1:ℕ)] with X calibration height pos
  let L := Real.log (X:ℝ)
  have L2 : 2 ≤ L := (le_max_left ..).trans height
  have L0 : 0<L := by linarith only [L2]
  have lpos := Real.log_pos (show 1<L by linarith only [L2])
  have X0 : (0:ℝ)<X := Nat.cast_pos.mpr pos
  intro j hj up
  have lower := (Nat.le_ceil (α*L/Real.log L)).trans (Nat.cast_le.mpr hj)
  have plus := Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hα.le L0.le) lpos.le)
  have upper : (j:ℝ) ≤ α*L/Real.log L+2 := by
    have h : (j:ℝ) ≤ (stoppingDepth α X:ℝ)+1 := by exact_mod_cast up
    change (j:ℝ) ≤ (⌈α*L/Real.log L⌉₊:ℝ)+1 at h
    linarith only [h,plus]
  obtain ⟨jp,scale,gain⟩ := calibration j lower upper
  let Y := Real.exp (L/j)
  have y0 : 0<Y := Real.exp_pos _
  have ly : Real.log Y=L/j := Real.log_exp _
  have j0 : (0:ℝ)<j := Nat.cast_pos.mpr jp
  have ybig : Y0 ≤ Y := ((le_max_right 2 Y0).trans height).trans (by
    change 20*L ≤ Y at scale
    linarith only [L0,scale])
  have bin := box_entropy L0 jp Y ly y0 scale (primes Y ybig)
  have jlog : (j:ℝ)*Real.log L ≤ α*L+2*Real.log L := by
    have h := mul_le_mul_of_nonneg_right upper lpos.le
    rwa [add_mul,div_mul_cancel₀ _ lpos.ne'] at h
  have power : K*(X:ℝ)^(1-α)*Real.exp ((boxGain/2)*j) ≤
      Real.exp (L-j*Real.log L+j*boxGain-Real.log 2) := by
    have positive := mul_pos Kpos (Real.rpow_pos_of_pos X0 (1-α))
    apply (Real.log_le_log_iff (mul_pos positive (Real.exp_pos _)) (Real.exp_pos _)).mp
    rw [Real.log_mul positive.ne' (Real.exp_pos _).ne',Real.log_mul Kpos.ne' (Real.rpow_pos_of_pos X0 _).ne',
      Real.log_rpow X0,Real.log_exp,Real.log_exp]
    change Real.log K+(1-α)*L+(boxGain/2)*j ≤ _
    linarith only [jlog,gain]
  have floorSize : ⌊Y⌋₊^j ≤ X := by
    have eq : Y^j=(X:ℝ) := by
      rw [←Real.rpow_natCast,Real.rpow_def_of_pos y0,ly,div_mul_cancel₀ _ j0.ne',Real.exp_log X0]
    exact_mod_cast (pow_le_pow_left₀ (Nat.cast_nonneg ⌊Y⌋₊) (Nat.floor_le y0.le) j).trans eq.le
  have boxed := prime_box_le_layer ⌊Y⌋₊ j X floorSize
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 B)
    (Real.rpow_nonneg X0.le _)) (Real.exp_pos _).le).trans (power.trans (bin.trans (Nat.cast_le.mpr boxed)))

/-- Both adjacent exact layers exceed every fixed multiple of the
endpoint power, at every sufficiently large cutoff. -/
theorem both_exact_layers_exceed_the_endpoint_power {α : ℝ} (hα : 0<α) (small : α<1)
    (B : ℝ) : ∀ᶠ X : ℕ in atTop,∀ j : ℕ,stoppingDepth α X ≤ j → j ≤ stoppingDepth α X+1 →
      B*(X:ℝ)^(1-α) ≤ (((terminalAtDepth j X).filter
        (fun n => n.primeFactors.card=j ∧ μ n=(-1:ℤ)^j)).card:ℝ) := by
  obtain ⟨t,ht,boxes⟩ := exponential_excess_in_both_stopping_prime_boxes
  filter_upwards [boxes α hα small (max 0 B)] with X h
  intro j lo hi
  have sub : stoppingPrimeBox j X ⊆ (terminalAtDepth j X).filter
      (fun n => n.primeFactors.card=j ∧ μ n=(-1:ℤ)^j) := by
    intro n hn
    obtain ⟨mem,d,sign,_⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem,d,sign⟩
  have nonneg := mul_nonneg (le_max_left 0 B) (Real.rpow_nonneg (Nat.cast_nonneg X) (1-α))
  exact (mul_le_mul_of_nonneg_right (le_max_right 0 B) (Real.rpow_nonneg (Nat.cast_nonneg X) _)).trans
    ((le_mul_of_one_le_right nonneg (Real.one_le_exp (mul_nonneg ht.le (Nat.cast_nonneg j)))).trans
      ((h j lo hi).trans (Nat.cast_le.mpr (card_le_card sub))))

private theorem adjacent_depth_of_sign (k : ℕ) (σ : ℤ) (sign : σ=1 ∨ σ= -1) :
    ∃ j : ℕ,k ≤ j ∧ j ≤ k+1 ∧ (-1:ℤ)^j=σ := by
  have par : (-1:ℤ)^k=1 ∨ (-1:ℤ)^k= -1 := by
    rcases Nat.even_or_odd k with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  by_cases eq : (-1:ℤ)^k=σ
  · exact ⟨k,le_rfl,Nat.le_succ _,eq⟩
  · exact ⟨k+1,Nat.le_succ _,le_rfl,by rw [pow_succ]; rcases par with ha | ha <;>
        rcases sign with hb | hb <;> omega⟩

/-- Each sign at and above the stopping depth has superconstant excess
over the nominal endpoint power, uniformly along the entire prefix. -/
theorem both_terminal_signs_exceed_the_endpoint_power {α : ℝ} (hα : 0<α) (small : α<1)
    (B : ℝ) : ∀ᶠ X : ℕ in atTop,∀ σ : ℤ,σ=1 ∨ σ= -1 →
      B*(X:ℝ)^(1-α) ≤ (((terminalAtDepth (stoppingDepth α X) X).filter (fun n => μ n=σ)).card:ℝ) := by
  filter_upwards [both_exact_layers_exceed_the_endpoint_power hα small B] with X layers
  intro σ sign
  let k := stoppingDepth α X
  obtain ⟨j,lo,hi,sg⟩ := adjacent_depth_of_sign k σ sign
  refine (layers j lo hi).trans (Nat.cast_le.mpr (card_le_card ?_))
  intro n hn
  obtain ⟨old,_,value⟩ := mem_filter.mp hn
  obtain ⟨sf,depth⟩ := mem_filter.mp old
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨sf,lo.trans depth⟩,value.trans sg⟩

/-- At the critical smoothness wall (log H)² each sign retains an
exponential gain on the scale log H/log log H, even after charging any
fixed power of log H. -/
theorem exponential_excess_of_each_smooth_sign :
    ∃ c : ℝ,0<c ∧ ∀ (D : ℕ) (B : ℝ),∀ᶠ H : ℕ in atTop,∀ z : ℕ,Real.log H^2 ≤ z →
      ∀ σ : ℤ,σ=1 ∨ σ= -1 → B*Real.sqrt H*Real.log H^D*
        Real.exp (c*Real.log H/Real.log (Real.log H)) ≤
        (((RHTower.Sieve.squarefreeSmoothUpTo z H).filter (fun n => μ n=σ)).card:ℝ) := by
  obtain ⟨t,ht,boxes⟩ := exponential_excess_in_both_stopping_prime_boxes
  refine ⟨t/4,by positivity,?_⟩
  intro D B
  let K := max 0 B
  let C := (4*((D:ℝ)+1))/t
  have cp : 0<C := by dsimp only [C]; positivity
  have logs := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have price := RHTower.Sieve.eventually_const_mul_one_add_log_pow_le_rpow zero_lt_one cp 2
  filter_upwards [boxes (1/2) (by norm_num) (by norm_num) K,logs price,
    logs.eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ)] with H supply funded large pos
  let L := Real.log (H:ℝ)
  let k := stoppingDepth (1/2) H
  have L1 : 1<L := by linarith only [large]
  have L0 := zero_lt_one.trans L1
  have lp := Real.log_pos L1
  have H0 : (0:ℝ)<H := Nat.cast_pos.mpr pos
  intro z wall σ sign
  obtain ⟨j,lo,hi,sg⟩ := adjacent_depth_of_sign k σ sign
  have lower : (1/2)*L/Real.log L ≤ (j:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr lo)
  have j0 := lt_of_lt_of_le (div_pos (by positivity : 0<(1/2)*L) lp) lower
  have len := (div_le_iff₀ lp).mp lower
  have bounded : Real.exp (L/(j:ℝ)) ≤ L^2 := by
    rw [←Real.log_le_log_iff (Real.exp_pos _) (pow_pos L0 2),Real.log_exp,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact (div_le_iff₀ j0).mpr (by linarith only [len])
  have poly : L^D ≤ Real.exp ((t/2)*j) := by
    apply (Real.log_le_log_iff (pow_pos L0 _) (Real.exp_pos _)).mp
    rw [Real.log_pow,Real.log_exp]
    change C*(1+Real.log L)^2 ≤ L^(1:ℝ) at funded
    rw [Real.rpow_one] at funded
    have weak := (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ lp.le (by linarith : Real.log L ≤ 1+Real.log L) 2) cp.le).trans funded
    have bind : C*t=4*((D:ℝ)+1) := div_mul_cancel₀ _ ht.ne'
    apply le_of_mul_le_mul_right _ lp
    nlinarith only [mul_le_mul_of_nonneg_right weak ht.le,
      congrArg (fun a : ℝ => a*(Real.log L)^2) bind,mul_le_mul_of_nonneg_right len ht.le,
      sq_nonneg (Real.log L)]
  have retained : (t/4)*L/Real.log L ≤ (t/2)*(j:ℝ) := (div_le_iff₀ lp).mpr (by
    linarith only [mul_le_mul_of_nonneg_left len ht.le])
  have extra := mul_le_mul poly (Real.exp_le_exp.mpr retained) (Real.exp_pos _).le (Real.exp_pos _).le
  rw [←Real.exp_add,show t/2*j+t/2*j=t*j by ring] at extra
  have sub : stoppingPrimeBox j H ⊆
      (RHTower.Sieve.squarefreeSmoothUpTo z H).filter (fun n => μ n=σ) := by
    intro n hn
    obtain ⟨depth,_,value,factors⟩ := mem_filter.mp hn
    obtain ⟨sf,_⟩ := mem_filter.mp depth
    obtain ⟨obs,square⟩ := mem_filter.mp sf
    refine mem_filter.mpr ⟨RHTower.Sieve.mem_squarefreeSmoothUpTo.mpr ⟨⟨mem_Icc.mp obs,?_⟩,square⟩,value.trans sg⟩
    intro p hp
    obtain ⟨pmax,pr⟩ := Nat.mem_primesLE.mp (factors hp)
    have upper := (Nat.cast_le.mpr pmax).trans (Nat.floor_le (Real.exp_pos _).le)
    exact Nat.mem_primesLE.mpr ⟨Nat.cast_le.mp (upper.trans (bounded.trans wall)),pr⟩
  have supplied := supply j lo hi
  rw [show (1:ℝ)-1/2=1/2 by norm_num,←Real.sqrt_eq_rpow] at supplied
  have base := mul_le_mul_of_nonneg_right (le_max_right 0 B) (Real.sqrt_nonneg H)
  calc _ = (B*Real.sqrt H)*(L^D*Real.exp ((t/4)*L/Real.log L)) := by ring
       _ ≤ (K*Real.sqrt H)*Real.exp (t*j) := mul_le_mul base extra
         (mul_nonneg (pow_nonneg L0.le D) (Real.exp_pos _).le)
         (mul_nonneg (le_max_left 0 B) (Real.sqrt_nonneg H))
       _ ≤ _ := supplied.trans (Nat.cast_le.mpr (card_le_card sub))

/-- Each smooth sign exceeds every fixed square-root-logarithmic price
at every sufficiently large cutoff under the same smoothness wall. -/
theorem both_smooth_signs_exceed_every_square_root_log_price (D : ℕ) (B : ℝ) :
    ∀ᶠ H : ℕ in atTop,∀ z : ℕ,Real.log H^2 ≤ z → ∀ σ : ℤ,σ=1 ∨ σ= -1 →
      B*Real.sqrt H*Real.log H^D ≤
        (((RHTower.Sieve.squarefreeSmoothUpTo z H).filter (fun n => μ n=σ)).card:ℝ) := by
  obtain ⟨c,hc,pop⟩ := exponential_excess_of_each_smooth_sign
  filter_upwards [pop D (max B 0),(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2]
    with H h large
  intro z hz σ sign
  have log0 : 0 ≤ Real.log (H:ℝ) := by linarith only [large]
  have ll := Real.log_nonneg (by linarith only [large] : 1 ≤ Real.log (H:ℝ))
  have le := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left B 0) (Real.sqrt_nonneg H))
    (pow_nonneg log0 D)
  exact le.trans ((le_mul_of_one_le_right (mul_nonneg (mul_nonneg (le_max_right B 0) (Real.sqrt_nonneg H))
    (pow_nonneg log0 D)) (Real.one_le_exp (div_nonneg (mul_nonneg hc.le log0) ll))).trans (h z hz σ sign))

#print axioms exponential_excess_of_each_smooth_sign
#print axioms both_smooth_signs_exceed_every_square_root_log_price
#print axioms exponential_excess_in_both_stopping_prime_boxes
#print axioms both_exact_layers_exceed_the_endpoint_power
#print axioms both_terminal_signs_exceed_the_endpoint_power

end GaloisForLFunctions.RestrictedFactorizationCalculus
