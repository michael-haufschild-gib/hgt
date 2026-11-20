import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.JointOscillationsAtTheLastHalfOfThePrimeRow
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RoughCofactorsAtPrimorialMidpoints

/-!
# Consecutive numerators in the mixed ordinary-prime moment

Fix the middle interval at the half-cut of its first numerator X. Up
to 3X/2, each subsequent middle discrepancy is still its own terminal
Chebyshev increment. A large initial increment therefore pays for a
whole interval of joint excursions in the same fixed test.
-/

open Finset Filter
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

/-- The original mixed prime moment restricted to its first numerator
slab, with the middle cut fixed at half the observation scale. -/
def earlyHalfCutMoment (s a g d η : ℝ) (X : ℕ) : ℝ :=
  let L := terminalBandEndpoint η X
  let N := largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) L
  L*∑ H ∈ N ∩ Icc X (X+X/2),oppositePrimeProduct true s (X/2) L H

private theorem sum_price_mono {D E : Finset ℕ} (h : D⊆E) (s : ℝ) (k L : ℕ) :
    (∑ H ∈ D, oppositePrimeProduct true s k L H)≤∑ H ∈ E, oppositePrimeProduct true s k L H :=
  sum_le_sum_of_subset_of_nonneg h (fun H _ _ =>
    show 0≤oppositePrimeProduct true s k L H from div_nonneg (mul_nonneg (le_max_left ..) (le_max_left ..)) (sq_nonneg _))

theorem earlyHalfCutMoment_le_full (s a g d η : ℝ) (X : ℕ) :
    let L := terminalBandEndpoint η X
    let N := largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) L
    earlyHalfCutMoment s a g d η X≤L*∑ H ∈ N, oppositePrimeProduct true s (X/2) L H := by
  intro L N
  exact mul_le_mul_of_nonneg_left (sum_price_mono inter_subset_left s (X/2) L) (Nat.cast_nonneg L)

private theorem second_quotient {H k n : ℕ} (third : H<3*(k+1)) (lo : k<n) (hi : n≤H/2) :
    H/n=2 := by
  have pn : 0<n := by omega
  have upper : H/n<3 := (Nat.div_lt_iff_lt_mul pn).mpr (by omega)
  have lower : 2≤H/n := (Nat.le_div_iff_mul_le pn).mpr (by omega)
  omega

/-- Throughout the second-quotient interval, moving the lower cut
transfers only even quotients between the two discrepancies. -/
theorem second_quotient_cut_invariance {H k L : ℕ} (hk : k≤H/2) (third : H<3*(k+1)) (hl : H≤L) :
    terminalOddHalf H=oddQuotientPrimeExcess (Ioc k L) H ∧
    oddQuotientPrimeExcess (middleTestFlank true k L H) H=
      oddQuotientPrimeExcess (middleTestFlank true (H/2) H H) H := by
  constructor
  · unfold terminalOddHalf oddQuotientPrimeExcess
    apply sum_subset (fun n hn => mem_Ioc.mpr ⟨hk.trans_lt (mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hl⟩)
    intro n hn missing
    by_cases large : H<n
    · simp [Nat.div_eq_of_lt large]
    have hi : n≤H/2 := le_of_not_gt (fun above => missing (mem_Ioc.mpr ⟨above,le_of_not_gt large⟩))
    simp [second_quotient third (mem_Ioc.mp hn).1 hi]
  · simp only [middleTestFlank,if_true,oddQuotientPrimeExcess]
    apply sum_subset (fun n hn => mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,(mem_Ioc.mp hn).2.trans hk⟩)
    intro n hn missing
    have lo : k<n := lt_of_not_ge (fun h => missing (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1,h⟩))
    simp [second_quotient third lo (mem_Ioc.mp hn).2]

/-- Every cut in the second-quotient interval and every endpoint beyond
the numerator give the very same normalized joint price. -/
theorem second_quotient_joint_price (s : ℝ) {H k L : ℕ} (hk : k≤H/2) (third : H<3*(k+1)) (hl : H≤L) :
    H*oppositePrimeProduct true s k L H=terminalJointHeight s H := by
  obtain ⟨middle,side⟩ := second_quotient_cut_invariance hk third hl
  simp only [terminalJointHeight,oppositePrimeProduct,←middle,side,terminalOddHalf]

/-- The numerator can move while both ends of the denominator interval
stay fixed, up to three halves of the starting numerator. -/
theorem fixed_middle_is_terminal_half {X H L : ℕ} (hx : X≤H) (hshort : 2*H≤3*X) (hl : H≤L) :
    terminalOddHalf H=oddQuotientPrimeExcess (Ioc (X/2) L) H :=
  (second_quotient_cut_invariance (by omega : X/2≤H/2) (by omega) hl).1

private theorem error_movement {a b H : ℕ} (hab : a≤b) (hb : b≤H) :
    |(Chebyshev.theta b-(b:ℝ))-(Chebyshev.theta a-(a:ℝ))|≤((b:ℝ)-a)*(1+Real.log H) := by
  have delta := ExceptionalLayerTheory.FactorialInterval.theta_integer_interval_bound hab
  have dx : 0≤(b:ℝ)-a := sub_nonneg.mpr (Nat.cast_le.mpr hab)
  have dθ := Chebyshev.theta_mono (Nat.cast_le.mpr hab : (a:ℝ)≤b)
  have ld : ((b:ℝ)-a)*Real.log b≤((b:ℝ)-a)*Real.log H := by
    by_cases p : 0<b
    · exact mul_le_mul_of_nonneg_left (Real.log_le_log (Nat.cast_pos.mpr p) (Nat.cast_le.mpr hb)) dx
    · have az : a=0 := by omega
      have bz : b=0 := by omega
      simp [az,bz]
  apply abs_le.mpr
  constructor <;> linarith only [dx,dθ,delta,ld,mul_nonneg dx (Real.log_natCast_nonneg H)]

/-- Two moving endpoints cost at most twice the numerator displacement
times one plus the logarithm of the last numerator. -/
theorem terminal_half_movement {X H : ℕ} (hx : X≤H) :
    |terminalOddHalf H-terminalOddHalf X|≤2*((H:ℝ)-X)*(1+Real.log H) := by
  let E (n : ℕ) := Chebyshev.theta n-(n:ℝ)
  have h₁ := error_movement hx (le_refl H)
  have halves : X/2≤H/2 := by omega
  have h₂ := error_movement halves (Nat.div_le_self H 2)
  have dif : (↑(H/2):ℝ)-(↑(X/2):ℝ)≤(H:ℝ)-X := by
    have d : H/2+X≤H+X/2 := by omega
    have cast : (↑(H/2):ℝ)+X≤(H:ℝ)+(↑(X/2):ℝ) := by exact_mod_cast d
    linarith only [cast]
  have sep : terminalOddHalf H-terminalOddHalf X=(E H-E X)-(E (H/2)-E (X/2)) := by
    rw [terminal_odd_half_eq,terminal_odd_half_eq]
    unfold E
    ring
  rw [sep]
  apply (abs_sub ..).trans
  change |E H-E X|≤_ at h₁
  change |E (H/2)-E (X/2)|≤_ at h₂
  linarith only [h₁,h₂,mul_le_mul_of_nonneg_right dif (add_nonneg zero_le_one (Real.log_natCast_nonneg H))]

private theorem cut_above_root {X H : ℕ} (hX : 16≤X) (hu : 2*H≤3*X) : Real.sqrt H<(↑(X/2):ℝ) := by
  have low : 8≤X/2 := by omega
  have sq : H<(X/2)^2 := by
    have cap : H≤3*(X/2)+1 := by omega
    nlinarith only [cap,low,Nat.mul_le_mul_right (X/2) low]
  exact (Real.sqrt_lt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by exact_mod_cast sq)

/-- All geometric eligibility tests hold throughout the first slab
once the upper denominator endpoint covers the numerator. -/
theorem initial_slab_middle_eligible {X H L : ℕ} {d : ℝ} (hX : 16≤X) (lo : X≤H)
    (sh : 2*H≤3*X) (hL : H≤L) (hd : d≤1/4) :
    H∈middleTestNumerators (Real.log X) d (X/2) L := by
  have hr : 1<(H:ℝ) := by exact_mod_cast (show 1<H by omega)
  have xp : 0<(X:ℝ) := Nat.cast_pos.mpr (by omega)
  have e := Real.rpow_lt_rpow_of_exponent_lt hr (show (1/2:ℝ)+d<1 by linarith only [hd])
  rw [Real.rpow_one] at e
  have ran : H<L^2 := by nlinarith only [hL,Nat.mul_le_mul_right L (show 2≤L by omega),hX,lo]
  exact mem_filter.mpr ⟨mem_range.mpr ran,(Real.exp_log xp).le.trans (Nat.cast_le.mpr lo),
    e.trans_le (Nat.cast_le.mpr hL),cut_above_root hX sh⟩

/-- One large signed increment forces W+1 consecutive *original*
joint numerators and pays their full mixed price in the same test. -/
theorem consecutive_prime_moment_lower_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ {s a g d B : ℝ} {X W L : ℕ}, (s=1 ∨ s= -1) → 0<a → 0≤B → d≤1/4 →
      16≤X → 2*W≤X → X+W≤L → a*Real.exp (g*Real.log X)*Real.sqrt (2*X)≤B →
      B+C*Real.sqrt (2*X)+2*W*(1+Real.log (2*X))<s*terminalOddHalf X →
      let N := largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) L
      Icc X (X+W)⊆N ∧
        (∑ H ∈ Icc X (X+W), B^2/(H:ℝ)^2) ≤ ∑ H ∈ Icc X (X+W), oppositePrimeProduct true s (X/2) L H ∧
        ((W:ℝ)+1)*B^2/(2*X)^2 ≤ ∑ H ∈ Icc X (X+W), oppositePrimeProduct true s (X/2) L H := by
  obtain ⟨C,hC,row⟩ := oppositePrimeProduct_below_endpoint
  refine ⟨C,hC,?_⟩
  intro s a g d B X W L hs ha hB hd hX hW hL floor big N
  let P (H : ℕ) := max 0 (s*oddQuotientPrimeExcess (Ioc (X/2) L) H)
  let Q (H : ℕ) := max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank true (X/2) L H) H)
  have xL : X/2≤L := by omega
  have sg : |s|=1 := by rcases hs with rfl|rfl <;> norm_num
  have point {H : ℕ} (inblock : H∈Icc X (X+W)) :
      H∈N ∧ B^2/(H:ℝ)^2≤oppositePrimeProduct true s (X/2) L H ∧ B^2/(2*X)^2≤B^2/(H:ℝ)^2 := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp inblock
    have sh : 2*H≤3*X := by omega
    have Hle : H≤L := hi.trans hL
    have hr : 1<(H:ℝ) := by exact_mod_cast (show 1<H by omega)
    have H2 : (H:ℝ)≤2*X := by exact_mod_cast (show H≤2*X by omega)
    have hw : (H:ℝ)-X≤W := by
      have cast : (H:ℝ)≤(X:ℝ)+W := by exact_mod_cast hi
      linarith only [cast]
    have logbound := Real.log_le_log (zero_lt_one.trans hr) H2
    have spread := terminal_half_movement lo
    have signed : s*terminalOddHalf X-s*terminalOddHalf H≤2*W*(1+Real.log (2*X)) := by
      have sgap := le_abs_self (s*(terminalOddHalf X-terminalOddHalf H))
      rw [abs_mul,sg,one_mul,abs_sub_comm] at sgap
      have logcost : 1+Real.log H≤1+Real.log (2*X) := by linarith only [logbound]
      have priced := mul_le_mul (mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤2))
        logcost (add_nonneg zero_le_one (Real.log_natCast_nonneg H))
        (mul_nonneg (by norm_num) (Nat.cast_nonneg W))
      linarith only [sgap,spread,priced]
    have mid : B+C*Real.sqrt (2*X)<s*oddQuotientPrimeExcess (Ioc (X/2) L) H := by
      rw [←fixed_middle_is_terminal_half lo sh Hle]
      linarith only [signed,big]
    have tail := ((row s (X/2) L hs xL).1 H Hle (Nat.floor_le_of_le (cut_above_root hX sh).le)).2
    change |P H-Q H|≤_ at tail
    have diff := (le_abs_self _).trans tail
    have sqr := Real.sqrt_le_sqrt H2
    have pc : B<P H := (by linarith only [mid,mul_nonneg hC (Real.sqrt_nonneg (2*X))] :
      B<s*oddQuotientPrimeExcess (Ioc (X/2) L) H).trans_le (le_max_right ..)
    have qc : B<Q H := by
      have p : B+C*Real.sqrt (2*X)<P H := mid.trans_le (le_max_right ..)
      linarith only [p,diff,mul_le_mul_of_nonneg_left sqr hC]
    have thresh := (mul_le_mul_of_nonneg_left sqr (mul_pos ha (Real.exp_pos _)).le).trans floor
    constructor
    · refine mem_filter.mpr ⟨initial_slab_middle_eligible hX lo sh Hle hd,?_,?_⟩
      · exact thresh.trans_lt ((lt_max_iff.mp pc).resolve_left (not_lt_of_ge hB))
      · exact thresh.trans_lt ((lt_max_iff.mp qc).resolve_left (not_lt_of_ge hB))
    · constructor
      · change B^2/(H:ℝ)^2≤P H*Q H/(H:ℝ)^2
        exact div_le_div_of_nonneg_right (by rw [sq]; exact mul_le_mul pc.le qc.le hB (hB.trans pc.le)) (sq_nonneg _)
      · exact div_le_div_of_nonneg_left (sq_nonneg B) (sq_pos_of_pos (zero_lt_one.trans hr))
          (pow_le_pow_left₀ (zero_lt_one.trans hr).le H2 2)
  have inc : Icc X (X+W)⊆N := fun _ h => (point h).1
  have step := sum_le_sum (s:=Icc X (X+W)) (fun H h => (point h).2.1)
  refine ⟨inc,step,?_⟩
  have coarse := sum_le_sum (s:=Icc X (X+W)) (fun H h => (point h).2.2)
  apply le_trans _ (coarse.trans step)
  rw [sum_const,Nat.card_Icc,nsmul_eq_mul,show X+W+1-X=W+1 by omega,Nat.cast_add,Nat.cast_one]
  rw [mul_div_assoc]

private theorem power_dominates {u v : ℝ} (h : u<v) (A : ℝ) :
    ∀ᶠ X : ℕ in atTop, A*(X:ℝ)^u≤(X:ℝ)^v := by
  have grow : Tendsto (fun X : ℕ => (X:ℝ)^(v-u)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr h)).comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop A,eventually_ge_atTop 1] with X high hX
  have xp : 0<(X:ℝ) := Nat.cast_pos.mpr hX
  have mul := mul_le_mul_of_nonneg_right high (Real.rpow_pos_of_pos xp u).le
  simpa only [←Real.rpow_add xp,sub_add_cancel] using mul

private theorem log_cost {x b p : ℝ} (hx : 1≤x) (hp : b<p) :
    x^b*(1+Real.log (2*x))≤(1+Real.log 2+1/(p-b))*x^p := by
  have xp := zero_lt_one.trans_le hx
  have qpos := sub_pos.mpr hp
  have raw := Real.log_le_rpow_div xp.le qpos
  have c : 0≤1+Real.log 2 := add_nonneg zero_le_one (Real.log_nonneg (by norm_num))
  have head := mul_le_mul_of_nonneg_left (Real.one_le_rpow hx qpos.le) c
  have w : 1+Real.log (2*x)≤(1+Real.log 2+1/(p-b))*x^(p-b) := by
    rw [Real.log_mul (by norm_num) xp.ne']
    simp only [div_eq_mul_inv,one_mul] at raw ⊢
    linarith only [raw,head]
  have paid := mul_le_mul_of_nonneg_left w (Real.rpow_pos_of_pos xp b).le
  have power : x^b*x^(p-b)=x^p := by rw [←Real.rpow_add xp,show b+(p-b)=p by ring]
  calc _ ≤ _ := paid
       _ = (1+Real.log 2+1/(p-b))*(x^b*x^(p-b)) := by ring
       _ = _ := by rw [power]

private theorem normalized_block_power {x : ℝ} (hx : 0<x) (A r b η : ℝ) :
    A^2/4*x^(r+2*b-1+η)=x^(1+η)*(x^r*(A*x^b)^2/(2*x)^2) := by
  have powers : x^(r+2*b-1+η)*x^2=x^(1+η)*x^r*(x^b*x^b) := by
    rw [←Real.rpow_two,←Real.rpow_add hx,←Real.rpow_add hx (1+η) r,←Real.rpow_add hx b b,
      ←Real.rpow_add hx]
    congr 1
    ring
  calc _ = A^2*(x^(r+2*b-1+η)*x^2)/(4*x^2) := by field_simp [hx.ne']
       _ = _ := by rw [powers]; field_simp [hx.ne']; ring

private theorem block_from_excursions {s a g d η r b p : ℝ}
    (hs : s=1 ∨ s= -1) (ha : 0<a) (hg : 0≤g) (hb : g+1/2≤b) (bp : b≤p)
    (r1 : r<1) (rp : r<p) (hd : d≤1/4) (hη : 0<η) (A : ℝ) (hA : 0<A)
    (osc : ∀ K : ℝ, 0≤K → ∃ᶠ X : ℕ in atTop, K*(X:ℝ)^p<s*terminalOddHalf X) :
    ∃ᶠ X : ℕ in atTop,
      let L := terminalBandEndpoint η X
      let N := largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) L
      (Real.log X/(1+η)≤Real.log (X/2:ℕ) ∧ Real.log (X/2:ℕ)≤Real.log X) ∧
      Icc X (X+⌊(X:ℝ)^r⌋₊)⊆N ∧ A^2/4*(X:ℝ)^(r+2*b-1+η)≤earlyHalfCutMoment s a g d η X := by
  obtain ⟨C,hC,block⟩ := consecutive_prime_moment_lower_bound
  have half : (1/2:ℝ)≤b := by linarith only [hg,hb]
  let V := A+a*Real.sqrt 2
  -- The exponent gap p−r pays the logarithm in the W-step variation.
  let J := 1+Real.log 2+1/(p-r)
  have Vpos : 0<V := by dsimp [V]; positivity
  have Jpos : 0≤J := by
    dsimp [J]
    exact add_nonneg (add_nonneg zero_le_one (Real.log_nonneg (by norm_num))) (one_div_pos.mpr (sub_pos.mpr rp)).le
  let K := V+C*Real.sqrt 2+2*J
  have Kpos : 0≤K := by dsimp only [K]; positivity
  have events := (((osc K Kpos).and_eventually (power_dominates r1 2)).and_eventually
    (power_dominates (show (1:ℝ)<1+η by linarith only [hη]) 2)).and_eventually (last_half_in_log_band hη)
  apply (events.and_eventually (eventually_ge_atTop 16)).mono
  rintro X ⟨⟨⟨⟨large,narrow⟩,long⟩,cut⟩,hX⟩
  let x := (X:ℝ)
  let W := ⌊x^r⌋₊
  let L := terminalBandEndpoint η X
  let B := V*x^b
  have x1 : 1≤x := Nat.one_le_cast.mpr (by omega)
  have xp := zero_lt_one.trans_le x1
  have xb := Real.rpow_pos_of_pos xp b
  have xr := Real.rpow_pos_of_pos xp r
  have Bpos : 0<B := mul_pos Vpos xb
  have Wlo : (W:ℝ)≤x^r := Nat.floor_le xr.le
  have Wsize : 2*W≤X := by
    rw [Real.rpow_one] at narrow
    have w : 2*(W:ℝ)≤x := (mul_le_mul_of_nonneg_left Wlo (by norm_num)).trans narrow
    change 2*(W:ℝ)≤(X:ℝ) at w
    exact_mod_cast w
  have hl : x^(1+η)≤(L:ℝ) := by
    unfold L terminalBandEndpoint
    rw [Real.rpow_def_of_pos xp,mul_comm (Real.log x) (1+η)]
    exact Nat.le_ceil _
  have XW : X+W≤L := by
    rw [Real.rpow_one] at long
    have two : 2*X≤L := by exact_mod_cast long.trans hl
    omega
  have root : Real.sqrt (2*x)=Real.sqrt 2*x^(1/2:ℝ) := by rw [Real.sqrt_mul (by norm_num),Real.sqrt_eq_rpow x]
  have level : a*Real.exp (g*Real.log X)*Real.sqrt (2*x)≤B := by
    rw [mul_comm g (Real.log X),←Real.rpow_def_of_pos xp,root]
    have q := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le x1 hb)
      (mul_pos ha (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))).le
    rw [Real.rpow_add xp] at q
    change _≤(A+a*Real.sqrt 2)*x^b
    linarith only [q,mul_pos hA xb]
  have sqr := Real.rpow_le_rpow_of_exponent_le x1 (half.trans bp)
  have priced : B+C*Real.sqrt (2*x)+2*W*(1+Real.log (2*x))≤K*x^p := by
    have logpos : 0≤Real.log (2*x) := Real.log_nonneg (by linarith only [x1])
    have w := mul_le_mul_of_nonneg_right Wlo (add_nonneg zero_le_one logpos)
    have tl := w.trans (log_cost x1 rp)
    rw [root]
    change (W:ℝ)*(1+Real.log (2*x))≤J*x^p at tl
    change V*x^b+C*(Real.sqrt 2*x^(1/2:ℝ))+2*W*(1+Real.log (2*x))≤(V+C*Real.sqrt 2+2*J)*x^p
    linarith only [tl,mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le x1 bp) Vpos.le,
      mul_le_mul_of_nonneg_left sqr (mul_nonneg hC (Real.sqrt_nonneg 2))]
  obtain ⟨inside,_,total⟩ := block hs ha Bpos.le hd hX Wsize XW level (priced.trans_lt large)
  let N := largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) L
  have within : Icc X (X+W)⊆N ∩ Icc X (X+X/2) := by
    intro n hn
    obtain ⟨lo,hi⟩ := mem_Icc.mp hn
    exact mem_inter.mpr ⟨inside hn,mem_Icc.mpr ⟨lo,by omega⟩⟩
  -- Count the initial numerator as well, so floor rounding loses no mass.
  refine ⟨cut,inside,?_⟩
  change A^2/4*x^(r+2*b-1+η)≤(L:ℝ)*(∑ H ∈ N ∩ Icc X (X+X/2),oppositePrimeProduct true s (X/2) L H)
  rw [normalized_block_power xp]
  have ampl : A*x^b≤B := by dsimp [B,V]; linarith only [mul_nonneg (mul_nonneg ha.le (Real.sqrt_nonneg 2)) xb.le]
  have base := mul_le_mul (Nat.lt_floor_add_one (x^r)).le (pow_le_pow_left₀ (mul_pos hA xb).le ampl 2)
    (sq_nonneg (A*x^b)) (add_nonneg (Nat.cast_nonneg W) zero_le_one)
  have sub := ((div_le_div_of_nonneg_right base (sq_nonneg (2*x))).trans total).trans (sum_price_mono within s (X/2) L)
  exact mul_le_mul hl sub (div_nonneg (mul_nonneg xr.le (sq_nonneg _)) (sq_nonneg _)) (Nat.cast_nonneg L)

/-- Below the zero abscissa, polynomially many consecutive numerators
pass both original gates. Their contribution alone exceeds arbitrary
multiples of X^(3b−1+η) at the admissible cut ⌊X/2⌋. -/
theorem consecutive_numerators_below_zero_abscissa {s a g d η b : ℝ}
    (hs : s=1 ∨ s= -1) (ha : 0<a) (hg : 0≤g) (hb : g+1/2≤b) (hw : b<zeroReSup)
    (hd : d≤1/4) (hη : 0<η) (A : ℝ) (hA : 0<A) :
    ∃ᶠ X : ℕ in atTop,
      let L := terminalBandEndpoint η X
      let N := largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) L
      (Real.log X/(1+η)≤Real.log (X/2:ℕ) ∧ Real.log (X/2:ℕ)≤Real.log X) ∧
      Icc X (X+⌊(X:ℝ)^b⌋₊)⊆N ∧ A^2/4*(X:ℝ)^(3*b-1+η)≤earlyHalfCutMoment s a g d η X := by
  let p := (b+zeroReSup)/2
  have bp : b<p := by dsimp [p]; linarith only [hw]
  have pw : p<zeroReSup := by dsimp [p]; linarith only [hw]
  simpa only [show b+2*b=3*b by ring] using block_from_excursions hs ha hg hb bp.le
    (hw.trans_le zeroReSup_le_one) bp hd hη A hA (terminal_odd_half_below_abscissa pw hs)

/-- At the square-root gate, either fixed orientation has long blocks
unconditionally. Every exponent r strictly below one half is available
for block length, with mixed price of order X^(r+η). -/
theorem consecutive_numerators_at_square_root {s a d η r : ℝ} (hs : s=1 ∨ s= -1)
    (ha : 0<a) (hd : d≤1/4) (hη : 0<η) (hr : r<1/2) (A : ℝ) (hA : 0<A) :
    ∃ᶠ X : ℕ in atTop,
      let L := terminalBandEndpoint η X
      let N := largeOppositePrimeNumerators true s a 0 d (Real.log X) (X/2) L
      (Real.log X/(1+η)≤Real.log (X/2:ℕ) ∧ Real.log (X/2:ℕ)≤Real.log X) ∧
      Icc X (X+⌊(X:ℝ)^r⌋₊)⊆N ∧ A^2/4*(X:ℝ)^(r+η)≤earlyHalfCutMoment s a 0 d η X := by
  have osc (K : ℝ) (hK : 0≤K) : ∃ᶠ X : ℕ in atTop, K*(X:ℝ)^(1/2:ℝ)<s*terminalOddHalf X := by
    simpa only [←Real.sqrt_eq_rpow] using terminal_odd_half_sqrt_excursions hs K hK
  simpa only [show r+2*(1/2:ℝ)-1=r by ring] using block_from_excursions hs ha
    (le_refl (0:ℝ)) (show 0+1/2≤(1/2:ℝ) by norm_num) le_rfl (hr.trans (by norm_num)) hr hd hη A hA osc

/-- The first numerator slab at one fixed choice of cut and flank
suffices to bound the zero abscissa from an upper moment exponent. -/
theorem half_cut_moment_or_zero_abscissa {s a g d η t : ℝ}
    (hs : s=1 ∨ s= -1) (ha : 0<a) (hg : 0≤g) (hd : d≤1/4) (hη : 0<η) :
    zeroReSup ≤ max (g+1/2) ((t+1-η)/3) ∨ ∀ M : ℝ, 0≤M → ∃ᶠ X : ℕ in atTop,
      M*(X:ℝ)^t<earlyHalfCutMoment s a g d η X := by
  by_cases narrow : zeroReSup ≤ max (g+1/2) ((t+1-η)/3)
  · exact Or.inl narrow
  right
  intro M hM
  have wide := lt_of_not_ge narrow
  let b := max (g+1/2) ((t+1-η)/3)
  have level : g+1/2≤b := le_max_left ..
  have price : t≤3*b-1+η := by linarith only [show (t+1-η)/3≤b from le_max_right ..]
  let A := 2*(M+1)
  have pos : 0<A := by dsimp [A]; positivity
  have coef : M<A^2/4 := by dsimp [A]; nlinarith only [sq_nonneg M,hM]
  have seq := consecutive_numerators_below_zero_abscissa hs ha hg level wide hd hη A pos
  apply (seq.and_eventually (eventually_ge_atTop 1)).mono
  rintro X ⟨⟨_,_,floor⟩,hX⟩
  have x1 : 1≤(X:ℝ) := Nat.one_le_cast.mpr hX
  have power := Real.rpow_le_rpow_of_exponent_le x1 price
  have strict := (mul_lt_mul_of_pos_right coef (Real.rpow_pos_of_pos (zero_lt_one.trans_le x1) t)).trans_le
    (mul_le_mul_of_nonneg_left power (hM.trans coef.le))
  exact strict.trans_le floor

/-- Above the zero abscissa the entire initial slab of numerators,
up to 3X/2, eventually misses the original joint gate. -/
theorem initial_half_cut_eventually_empty {s a g d η : ℝ} (hs : s=1 ∨ s= -1) (ha : 0<a)
    (hw : zeroReSup<g+1/2) (hη : 0<η) :
    ∀ᶠ X : ℕ in atTop, Disjoint (Icc X (X+X/2))
      (largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) (terminalBandEndpoint η X)) := by
  let b := (zeroReSup+(g+1/2))/2
  have wb : zeroReSup<b := by dsimp [b]; linarith only [hw]
  have bv : b<g+1/2 := by dsimp [b]; linarith only [hw]
  have bpos : 0≤b := by linarith only [half_le_zeroReSup,wb]
  obtain ⟨D,hD,cap⟩ := terminal_odd_half_above_abscissa wb
  obtain ⟨H₀,h₀⟩ := eventually_atTop.mp cap
  filter_upwards [power_dominates bv (D*(2:ℝ)^b/a),power_dominates (show (1:ℝ)<1+η by linarith only [hη]) 2,
    eventually_ge_atTop (max H₀ 1)] with X paid large hX
  have xp : 0<(X:ℝ) := Nat.cast_pos.mpr ((le_max_right H₀ 1).trans hX)
  have hl : (X:ℝ)^(1+η)≤(terminalBandEndpoint η X:ℝ) := by
    rw [Real.rpow_def_of_pos xp,mul_comm (Real.log X) (1+η)]
    exact Nat.le_ceil _
  rw [Real.rpow_one] at large
  have two : 2*X≤terminalBandEndpoint η X := by exact_mod_cast large.trans hl
  apply Finset.disjoint_left.mpr
  intro H hH hit
  obtain ⟨lo,hi⟩ := mem_Icc.mp hH
  have sh : 2*H≤3*X := by omega
  have hbig := (mem_filter.mp hit).2.1
  rw [←fixed_middle_is_terminal_half lo sh (show H≤terminalBandEndpoint η X by omega)] at hbig
  have sign : s*terminalOddHalf H≤D*(H:ℝ)^b := by
    apply (le_abs_self _).trans
    rcases hs with rfl|rfl <;> simpa only [one_mul,neg_one_mul,abs_neg] using
      h₀ H ((le_max_left H₀ 1).trans (hX.trans lo))
  have h2 : (H:ℝ)≤2*(X:ℝ) := by exact_mod_cast (show H≤2*X by omega)
  have size := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg H) h2 bpos) hD
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) xp.le] at size
  have price : (D*2^b*(X:ℝ)^b)/a≤(X:ℝ)^(g+1/2) := by
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using paid
  have gated : a*(X:ℝ)^(g+1/2)≤a*Real.exp (g*Real.log X)*Real.sqrt H := by
    rw [Real.rpow_add xp,←Real.sqrt_eq_rpow,mul_comm g (Real.log X),←Real.rpow_def_of_pos xp,←mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.cast_le.mpr lo))
      (mul_nonneg ha.le (Real.rpow_nonneg xp.le _))
  linarith only [hbig,gated,sign,size,(div_le_iff₀ ha).mp price]

/-- With either sign and any fixed positive band width and gate
coefficient, RH is equivalent to eventual disappearance of all early
numerators, for every positive power gate. -/
theorem rh_iff_initial_half_cut_eventually_empty {s a d η : ℝ} (hs : s=1 ∨ s= -1)
    (ha : 0<a) (hd : d≤1/4) (hη : 0<η) :
    RiemannHypothesis ↔ ∀ g : ℝ, 0<g → ∀ᶠ X : ℕ in atTop, Disjoint (Icc X (X+X/2))
      (largeOppositePrimeNumerators true s a g d (Real.log X) (X/2) (terminalBandEndpoint η X)) := by
  constructor
  · intro rh g hg
    have width := ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_zeroReSup_eq_half.mp rh
    exact initial_half_cut_eventually_empty hs ha (by linarith only [width,hg]) hη
  · intro empty
    apply (rh_iff_last_half_eventually_absent hs ha hd hη).mpr
    intro g hg
    exact (empty g hg).mono fun X disj => Finset.disjoint_left.mp disj (mem_Icc.mpr ⟨le_rfl,by omega⟩)

/-- For any fixed band width η>0, a single coefficient, sign and
half-cut suffice: the early mixed moments have upper exponent
1/2+η+3g at every positive gate power g precisely under RH. -/
theorem rh_iff_early_half_cut_moment {s a d η : ℝ} (hs : s=1 ∨ s= -1)
    (ha : 0<a) (hd : d≤1/4) (hη : 0<η) :
    RiemannHypothesis ↔ ∀ g : ℝ, 0<g → ∃ M : ℝ, 0≤M ∧
      ∀ᶠ X : ℕ in atTop, earlyHalfCutMoment s a g d η X≤M*(X:ℝ)^(1/2+η+3*g) := by
  constructor
  · intro rh g hg
    refine ⟨0,le_rfl,?_⟩
    filter_upwards [(rh_iff_initial_half_cut_eventually_empty hs ha hd hη).mp rh g hg] with X empty
    simp only [earlyHalfCutMoment,Finset.disjoint_iff_inter_eq_empty.mp empty.symm,sum_empty,mul_zero,zero_mul,le_refl]
  · intro all
    apply ArithmeticOfSquareRootPrecision.riemannHypothesis_of_zeroReSup_le_half
    by_contra! wide
    let g := (zeroReSup-1/2)/2
    have hg : 0<g := by dsimp [g]; linarith only [wide]
    have depth : g+1/2<zeroReSup := by dsimp [g]; linarith only [wide]
    have eq : (1/2+η+3*g+1-η)/3=g+1/2 := by ring
    rcases half_cut_moment_or_zero_abscissa (t:=1/2+η+3*g) hs ha hg.le hd hη with small|large
    · rw [eq,max_self] at small
      exact depth.not_ge small
    · obtain ⟨M,hM,cap⟩ := all g hg
      obtain ⟨X,big,small⟩ := ((large M hM).and_eventually cap).exists
      exact big.not_ge small

#print axioms rh_iff_early_half_cut_moment
#print axioms rh_iff_initial_half_cut_eventually_empty
#print axioms half_cut_moment_or_zero_abscissa
#print axioms consecutive_numerators_at_square_root
#print axioms consecutive_numerators_below_zero_abscissa
#print axioms fixed_middle_is_terminal_half
#print axioms second_quotient_joint_price
#print axioms terminal_half_movement
#print axioms consecutive_prime_moment_lower_bound
end GaloisForLFunctions.ExclusionOfTheCriticalState
