import GaloisForLFunctions.RestrictedFactorizationCalculus.BothSignsAtTheSquareRootStoppingDepth
import GaloisForLFunctions.RestrictedFactorizationCalculus.SquareRootTruncationOfTheRoughCofactor
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCriticalEulerPriceOfTheLogSquareCutoff

/-!
# Both signs below the rough-cofactor cutoff

A smooth depth box and an independent large prime supply both signs at
the critical exponent of the rough-cofactor truncation. The least
unsigned price of the smooth term in the logarithmic divisor identity
also exceeds square root times every fixed power of the logarithm.
-/

noncomputable section

open Finset Filter RHTower.Sieve RHTower.PrimeCells
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem log_wall_above_smaller_height {H X : ℕ} (hp : 0<H)
    (sep : Real.exp 1*H ≤ (X:ℝ)+1) : Real.log H^2 ≤ (logSquareCutoff X:ℝ) := by
  have hr : (0:ℝ)<H := Nat.cast_pos.mpr hp
  have ld := Real.log_le_log (mul_pos (Real.exp_pos _) hr) sep
  rw [Real.log_mul (Real.exp_pos _).ne' hr.ne',Real.log_exp] at ld
  have round := Nat.lt_floor_add_one (Real.log ((X:ℝ)+1))
  change Real.log H^2 ≤ ((⌊Real.log ((X:ℝ)+1)⌋₊^2:ℕ):ℝ)
  rw [Nat.cast_pow]
  exact pow_le_pow_left₀ (Real.log_nonneg (Nat.one_le_cast.mpr hp)) (by linarith only [ld,round]) 2

private theorem smooth_prime_product {z H d p : ℕ} (hd : d ∈ squarefreeSmoothUpTo z H)
    (pr : p.Prime) (high : z<p) :
    Squarefree (d*p) ∧ roughPart z (d*p)=p ∧ μ (d*p)= -(μ d) := by
  obtain ⟨⟨⟨dp,_⟩,factors⟩,dsq⟩ := mem_squarefreeSmoothUpTo.mp hd
  have dn : d ≠ 0 := Nat.ne_of_gt (show 0<d from dp)
  have nd : ¬p ∣ d := fun dv => high.not_ge ((Nat.mem_primesLE.mp (factors
    (Nat.mem_primeFactors.mpr ⟨pr,dv,dn⟩))).1)
  have cop := (pr.coprime_iff_not_dvd.mpr nd).symm
  have sq := Nat.squarefree_mul_iff.mpr ⟨cop,dsq,Irreducible.squarefree pr⟩
  refine ⟨sq,?_,by rw [isMultiplicative_moebius.map_mul_of_coprime cop,moebius_apply_prime pr]; ring⟩
  have roughSF := sq.squarefree_of_dvd (roughPart_dvd z (d*p))
  rw [←Nat.prod_primeFactors_of_squarefree roughSF,primeFactors_roughPart (mul_ne_zero dn pr.ne_zero),
    Nat.primeFactors_mul dn pr.ne_zero,pr.primeFactors]
  have only : (d.primeFactors ∪ {p}).filter (fun q => ¬q ≤ z)={p} := by
    ext q
    simp only [mem_filter,mem_union,mem_singleton]
    exact ⟨fun ⟨h,notSmall⟩ => h.elim (fun hq => (notSmall (Nat.mem_primesLE.mp (factors hq)).1).elim) id,
      fun eq => eq ▸ ⟨Or.inr rfl,high.not_ge⟩⟩
  rw [only,prod_singleton]

/-- Multiplying smooth integers of one sign by a prime above the sieve
gives distinct integers of the opposite sign and prescribed rough part. -/
theorem products_supply_one_rough_sign (z H X Y : ℕ) (v : ℝ) (v0 : 0<v)
    (zv : (z:ℝ) ≤ v) (size : (H:ℝ)*(2*v) ≤ X) (rough : ⌊2*v⌋₊ ≤ Y) (σ : ℤ) :
    ((squarefreeSmoothUpTo z H).filter (fun n => μ n= -σ)).card*
      (RHTower.windowPrimes v (2*v)).card ≤
      ((smallRoughCofactors z X Y).filter (fun n => μ n=σ)).card := by
  let A := (squarefreeSmoothUpTo z H).filter (fun n => μ n= -σ)
  let P := RHTower.windowPrimes v (2*v)
  rw [←card_product]
  have info (a : ℕ × ℕ) (ha : a ∈ A.product P) :
      Squarefree (a.1*a.2) ∧ roughPart z (a.1*a.2)=a.2 ∧ μ (a.1*a.2)=σ := by
    obtain ⟨d,p⟩ := a
    obtain ⟨dmem,pmem⟩ := mem_product.mp ha
    obtain ⟨ds,mark⟩ := mem_filter.mp dmem
    obtain ⟨pr,lo,_⟩ := (RHTower.mem_windowPrimes v0.le (by positivity)).mp pmem
    have factor := smooth_prime_product ds pr (Nat.cast_lt.mp (zv.trans_lt lo))
    exact ⟨factor.1,factor.2.1,by rw [factor.2.2,mark,neg_neg]⟩
  apply card_le_card_of_injOn (fun a : ℕ × ℕ => a.1*a.2)
  · intro a ha
    obtain ⟨d,p⟩ := a
    obtain ⟨hd,hp⟩ := mem_product.mp ha
    obtain ⟨pr,_,wall⟩ := (RHTower.mem_windowPrimes v0.le (by positivity)).mp hp
    obtain ⟨⟨⟨dp,ht⟩,_⟩,_⟩ := mem_squarefreeSmoothUpTo.mp (mem_filter.mp hd).1
    obtain ⟨sq,r,mark⟩ := info (d,p) ha
    have endp : d*p ≤ X := by exact_mod_cast (mul_le_mul (Nat.cast_le.mpr ht) wall
      (Nat.cast_nonneg p) (Nat.cast_nonneg H)).trans size
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos dp pr.pos,endp⟩,sq⟩,
      r.le.trans ((Nat.le_floor wall).trans rough)⟩,mark⟩
  · rintro ⟨a,p⟩ ah ⟨b,q⟩ bh eq
    have ep : p=q := (info _ ah).2.1.symm.trans ((congrArg (roughPart z) eq).trans (info _ bh).2.1)
    subst q
    have pr := ((RHTower.mem_windowPrimes v0.le (by positivity)).mp (mem_product.mp ah).2).1
    exact Prod.ext (Nat.eq_of_mul_eq_mul_right pr.pos eq) rfl

private abbrev boxHeight (a : ℝ) (X : ℕ) := ⌊(X:ℝ)^a/Real.exp 2⌋₊

/-- A fixed fraction of Xᵃ still supports both smooth signs above
X^(a/2) times every fixed logarithmic power of the original endpoint. -/
private theorem scaled_smooth_boxes {a : ℝ} (ha : 0<a) (a1 : a ≤ 1) :
    ∃ c : ℝ,0<c ∧ ∀ (D : ℕ) (B : ℝ),∀ᶠ X : ℕ in atTop,∀ σ : ℤ,σ=1 ∨ σ= -1 →
      B*(X:ℝ)^(a/2)*Real.log X^D*Real.exp (c*Real.log X/Real.log (Real.log X)) ≤
        (((squarefreeSmoothUpTo (logSquareCutoff X) (boxHeight a X)).filter (fun n => μ n=σ)).card:ℝ) := by
  obtain ⟨t,ht,boxes⟩ := exponential_excess_of_each_smooth_sign
  refine ⟨t*a/2,by positivity,?_⟩
  intro D B
  let E := Real.exp 2
  let K := max 0 B
  let C := (K*(2*E))*(2/a)^D
  have Ep : 0<E := Real.exp_pos _
  have E1 : 1 ≤ E := Real.one_le_exp (by norm_num)
  have E2 : 1 ≤ 2*E := by linarith only [E1]
  have cast : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have grow := (tendsto_rpow_atTop ha).comp cast
  have ftop : Tendsto (boxHeight a) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [grow.eventually_ge_atTop ((N:ℝ)*E)] with X large
    exact Nat.le_floor ((le_div_iff₀ Ep).mpr large)
  have logs := Real.tendsto_log_atTop.comp cast
  filter_upwards [ftop (boxes D C),
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ftop)).eventually_ge_atTop 2,
    grow.eventually_ge_atTop (2*E),logs.eventually_ge_atTop (2*Real.log (2*E)/a),
    eventually_ge_atTop (2:ℕ)] with X supply logH scaled large pos
  let H := boxHeight a X
  let L := Real.log (X:ℝ)
  have xp : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have x1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have lx := Real.log_nonneg x1
  have power := Real.rpow_nonneg xp.le a
  have floor := Nat.floor_le (div_nonneg power Ep.le)
  have floor' := Nat.lt_floor_add_one ((X:ℝ)^a/E)
  have hp : 1 ≤ H := Nat.le_floor ((le_div_iff₀ Ep).mpr (by linarith only [scaled,Ep]))
  have hR : (0:ℝ)<H := Nat.cast_pos.mpr hp
  have small : (H:ℝ)*E ≤ (X:ℝ)^a := (le_div_iff₀ Ep).mp floor
  have up : (X:ℝ)^a ≤ (2*E)*H := by
    have tmp := (div_lt_iff₀ Ep).mp floor'
    have rent := mul_le_mul_of_nonneg_right (Nat.one_le_cast.mpr hp : (1:ℝ) ≤ H) Ep.le
    linarith only [tmp,rent]
  have lenLog : (a/2)*L ≤ Real.log H := by
    have split := Real.log_le_log (Real.rpow_pos_of_pos xp a) up
    rw [Real.log_rpow xp,Real.log_mul (by positivity) hR.ne'] at split
    linarith only [split,(div_le_iff₀ ha).mp large]
  have wall : Real.log H^2 ≤ (logSquareCutoff X:ℝ) := by
    apply log_wall_above_smaller_height hp
    have unit : Real.exp 1 ≤ E := Real.exp_le_exp.mpr (by norm_num)
    have step := ((mul_le_mul_of_nonneg_right unit hR.le).trans (by simpa only [mul_comm] using small)).trans
      ((Real.rpow_le_rpow_of_exponent_le x1 a1).trans_eq (Real.rpow_one _))
    linarith only [step]
  have rootBound : (X:ℝ)^(a/2) ≤ (2*E)*Real.sqrt H := by
    calc _ = Real.sqrt ((X:ℝ)^a) := by rw [Real.sqrt_eq_rpow,←Real.rpow_mul xp.le]; congr 1; ring
         _ ≤ Real.sqrt ((2*E)*H) := Real.sqrt_le_sqrt up
         _ = Real.sqrt (2*E)*Real.sqrt H := Real.sqrt_mul (by positivity) _
         _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr E2)) (Real.sqrt_nonneg _)
  have logBound : L ≤ (2/a)*Real.log H := by
    rw [div_mul_eq_mul_div,le_div_iff₀ ha]; linarith only [lenLog]
  have factor := mul_le_mul rootBound (pow_le_pow_left₀ lx logBound D)
    (pow_nonneg lx D) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  rw [mul_pow] at factor
  have hx : (H:ℝ) ≤ X := by
    have scaledH := le_mul_of_one_le_right hR.le E1
    exact (scaledH.trans small).trans ((Real.rpow_le_rpow_of_exponent_le x1 a1).trans_eq (Real.rpow_one _))
  have ll := Real.log_pos (by linarith only [logH] : 1<Real.log H)
  have logOrder := Real.log_le_log (by linarith only [logH] : 0<Real.log H) (Real.log_le_log hR hx)
  have charge : (t*a/2)*L/Real.log L ≤ t*Real.log H/Real.log (Real.log H) := by
    apply LE.le.trans _ (div_le_div_of_nonneg_left (by positivity) ll logOrder)
    apply div_le_div_of_nonneg_right _ (ll.trans_le logOrder).le
    linarith only [mul_le_mul_of_nonneg_left lenLog ht.le]
  intro σ sign
  have paid := supply (logSquareCutoff X) wall σ sign
  apply LE.le.trans _ paid
  have left := mul_le_mul_of_nonneg_right (le_max_right 0 B) (Real.rpow_nonneg xp.le (a/2))
  have base : B*(X:ℝ)^(a/2)*L^D ≤ C*Real.sqrt H*Real.log H^D := by
    calc _ ≤ K*((X:ℝ)^(a/2)*L^D) := (mul_le_mul_of_nonneg_right left (pow_nonneg lx D)).trans_eq (by ring)
         _ ≤ _ := mul_le_mul_of_nonneg_left factor (le_max_left 0 B)
         _ = _ := by dsimp only [C]; ring
  have c0 : 0 ≤ C := by dsimp only [C,K]; positivity
  exact mul_le_mul base (Real.exp_le_exp.mpr charge) (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg c0 (Real.sqrt_nonneg H)) (pow_nonneg (by linarith only [logH]) _))

private theorem drop_exponential {U V c L K : ℝ} (hc : 0 ≤ c) (hL : 1 ≤ L) (u0 : 0 ≤ U)
    (h : max 0 K*U*Real.exp (c*L/Real.log L) ≤ V) : K*U ≤ V := by
  have e := Real.one_le_exp (div_nonneg (mul_nonneg hc (zero_le_one.trans hL)) (Real.log_nonneg hL))
  exact (mul_le_mul_of_nonneg_right (le_max_right 0 K) u0).trans
    ((le_mul_of_one_le_right (mul_nonneg (le_max_left 0 K) u0) e).trans h)

/-- Every fixed positive power eventually exceeds twice the log-square wall. -/
theorem cutoff_below_power {γ : ℝ} (hγ : 0<γ) :
    ∀ᶠ X : ℕ in atTop,2*(logSquareCutoff X:ℝ) ≤ (X:ℝ)^γ := by
  have g := half_pos hγ
  filter_upwards [log_square_deletion_cost (by norm_num : (1:ℝ)/2<1) g,
    ((tendsto_rpow_atTop g).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2,
    eventually_ge_atTop (1:ℕ)] with X paid size pos
  have e := deletionPrice_one_le (s := 1) zero_lt_one (logSquareCutoff X)
  have one : 1 ≤ (deletionPrice 1 (logSquareCutoff X))^2 := one_le_pow₀ e
  have low := (le_mul_of_one_le_right (by positivity : 0 ≤ (logSquareCutoff X:ℝ)+1) one).trans paid
  rw [show γ=γ/2+γ/2 by ring,Real.rpow_add (Nat.cast_pos.mpr pos)]
  exact mul_le_mul size (by linarith only [low]) (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg X) _)

/-- In the sector with rough part at most X^γ, each Möbius sign
exceeds the nominal endpoint X^((1+γ)/2) times every fixed logarithmic
power. The bound holds at all sufficiently large X. -/
theorem exponential_excess_below_a_polynomial_rough_cut {γ : ℝ} (hg : 0<γ) (small : γ<1) :
    ∃ c : ℝ,0<c ∧ ∀ (D : ℕ) (B : ℝ),∀ᶠ X : ℕ in atTop,∀ σ : ℤ,σ=1 ∨ σ= -1 →
      B*(X:ℝ)^((1+γ)/2)*Real.log X^D*Real.exp (c*Real.log X/Real.log (Real.log X)) ≤
        (((smallRoughCofactors (logSquareCutoff X) X ⌊(X:ℝ)^γ⌋₊).filter (fun n => μ n=σ)).card:ℝ) := by
  let a := 1-γ
  have ap : 0<a := sub_pos.mpr small
  have a1 : a ≤ 1 := sub_le_self _ hg.le
  obtain ⟨c,hc,scaled⟩ := scaled_smooth_boxes ap a1
  refine ⟨c,hc,?_⟩
  intro D B
  let K := max 0 B
  have grow := (tendsto_rpow_atTop hg).comp tendsto_natCast_atTop_atTop
  have halfTop : Tendsto (fun X : ℕ => (X:ℝ)^γ/2) atTop atTop := tendsto_atTop.mpr
    (fun c => (grow.eventually_ge_atTop (2*c)).mono (fun n hn => by dsimp only; linarith only [hn]))
  filter_upwards [scaled (D+1) (3*K),halfTop eventually_dyadic_prime_lower,
    cutoff_below_power hg,eventually_ge_atTop (2:ℕ)] with X boxes prime gap pos
  intro σ sign
  let H := boxHeight a X
  let z := logSquareCutoff X
  let T := (X:ℝ)^γ
  let P := (RHTower.windowPrimes (T/2) (2*(T/2))).card
  let Q := ((squarefreeSmoothUpTo z H).filter (fun n => μ n= -σ)).card
  let L := Real.log (X:ℝ)
  have x0 : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have lx : 0<L := Real.log_pos (by exact_mod_cast (by omega : 1<X))
  have tpos : 0<T := Real.rpow_pos_of_pos x0 γ
  have twice : 2*(T/2)=T := by ring
  have combined : (X:ℝ)^a*T=X := by
    dsimp only [T]; rw [←Real.rpow_add x0,show a+γ=1 by dsimp only [a]; ring,Real.rpow_one]
  have size : (H:ℝ)*(2*(T/2)) ≤ X := by
    have floor := Nat.floor_le (div_nonneg (Real.rpow_nonneg x0.le a) (Real.exp_pos 2).le)
    have h : (H:ℝ) ≤ (X:ℝ)^a := floor.trans
      (div_le_self (Real.rpow_nonneg x0.le a) (Real.one_le_exp (by norm_num)))
    rw [twice]
    exact (mul_le_mul_of_nonneg_right h tpos.le).trans_eq combined
  have product := products_supply_one_rough_sign z H X ⌊T⌋₊ (T/2) (half_pos tpos)
    (by linarith only [gap]) size (by rw [twice]) σ
  have smooth := boxes (-σ) (by rcases sign with h | h <;> simp [h])
  change (3*K)*(X:ℝ)^(a/2)*L^(D+1)*Real.exp (c*L/Real.log L) ≤ (Q:ℝ) at smooth
  change (99/100)*(T/2)/Real.log (2*(T/2)) ≤ (P:ℝ) at prime
  rw [twice,Real.log_rpow x0,div_le_iff₀ (mul_pos hg lx)] at prime
  have density := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right small.le lx.le)
    (Nat.cast_nonneg (α := ℝ) P)
  have pcount : T ≤ 3*(P:ℝ)*L := by linarith only [prime,density,tpos]
  have full : (X:ℝ)^((1+γ)/2)=(X:ℝ)^(a/2)*T := by
    dsimp only [T]; rw [←Real.rpow_add x0]; congr 1; dsimp only [a]; ring
  have squeeze := (mul_le_mul_of_nonneg_right smooth tpos.le).trans
    (mul_le_mul_of_nonneg_left pcount (Nat.cast_nonneg Q))
  have low := mul_le_mul_of_nonneg_right (le_max_right 0 B) (Real.rpow_nonneg x0.le ((1+γ)/2))
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right low (pow_nonneg lx.le D)) (Real.exp_pos _).le).trans
  apply LE.le.trans _ (show (Q:ℝ)*P ≤ _ by exact_mod_cast product)
  apply le_of_mul_le_mul_right _ (show 0<3*L by positivity)
  rw [pow_succ] at squeeze
  rw [full]
  linarith only [squeeze]

/-- The two sign populations have the same second-order scale for every
polynomial rough-part cutoff. The upper bound counts the whole sector. -/
theorem second_order_scale_of_both_rough_signs {γ : ℝ} (hg : 0<γ) (small : γ<1) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ X : ℕ in atTop,∀ σ : ℤ,σ=1 ∨ σ= -1 →
      let L := Real.log (X:ℝ)
      let A := smallRoughCofactors (logSquareCutoff X) X ⌊(X:ℝ)^γ⌋₊
      let P := (X:ℝ)^((1+γ)/2)
      P*Real.exp (c*L/Real.log L) ≤ ((A.filter (fun n => μ n=σ)).card:ℝ) ∧
        (A.card:ℝ) ≤ 2*P*Real.exp (C*L/Real.log L) := by
  obtain ⟨c,hc,lower⟩ := exponential_excess_below_a_polynomial_rough_cut hg small
  obtain ⟨C,hC,upper⟩ := critical_deletion_at_the_log_square_cutoff
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [lower 0 1,upper,eventually_ge_atTop (1:ℕ)] with X lo hi pos
  intro σ sign
  refine ⟨by simpa only [one_mul,pow_zero,mul_one] using lo σ sign,?_⟩
  let b := logSquareCutoff X
  let E := deletionPrice (1/2) b
  let Y := ⌊(X:ℝ)^γ⌋₊
  have sp : 0<(1/2:ℝ) := by norm_num
  have e1 : 1 ≤ E := deletionPrice_one_le sp _
  have price : E ≤ Real.exp (C*Real.log X/Real.log (Real.log X)) := by
    apply LE.le.trans _ hi.2
    have e2 : E ≤ E^2 := by nlinarith only [sq_nonneg (E-1),e1]
    exact e2.trans (le_mul_of_one_le_left (sq_nonneg E) (by have := Nat.cast_nonneg (α := ℝ) b; linarith))
  have x0 := (Nat.cast_pos (α := ℝ)).mpr pos
  have wall := Nat.floor_le (Real.rpow_nonneg x0.le γ)
  have rt := Real.rpow_le_rpow (Nat.cast_nonneg Y) wall sp.le
  rw [←Real.rpow_mul x0.le] at rt
  have up := small_rough_cofactor_card_bound sp (by norm_num) b X Y
  rw [show (1:ℝ)-1/2=1/2 by norm_num] at up
  have rhs := mul_le_mul (mul_le_mul_of_nonneg_right price (Real.rpow_nonneg x0.le (1/2)))
    (div_le_div_of_nonneg_right rt sp.le) (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Y) _) sp.le)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg x0.le _))
  apply up.trans (rhs.trans_eq ?_)
  have combine : (X:ℝ)^(1/2:ℝ)*(X:ℝ)^(γ*(1/2))=(X:ℝ)^((1+γ)/2) := by
    rw [←Real.rpow_add x0]; congr 1; ring
  rw [←combine]
  ring

/-- In particular no fixed logarithmic price attains the nominal power
for either sign, at any fixed polynomial rough-part cutoff. -/
theorem both_signs_below_a_polynomial_rough_cofactor_cut {γ : ℝ} (hg : 0<γ) (small : γ<1)
    (D : ℕ) (B : ℝ) : ∀ᶠ X : ℕ in atTop,∀ σ : ℤ,σ=1 ∨ σ= -1 →
      B*(X:ℝ)^((1+γ)/2)*Real.log X^D ≤ (((smallRoughCofactors
        (logSquareCutoff X) X ⌊(X:ℝ)^γ⌋₊).filter (fun n => μ n=σ)).card:ℝ) := by
  obtain ⟨c,hc,pop⟩ := exponential_excess_below_a_polynomial_rough_cut hg small
  filter_upwards [pop D (max 0 B),(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with X h large
  intro σ sign
  have lx := zero_le_one.trans large
  rw [mul_assoc]
  exact drop_exponential hc.le large (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _) (pow_nonneg lx _))
    (by simpa only [←mul_assoc] using h σ sign)

/-- On purely smooth vertices the same endpoint failure already occurs
in each sign at square root, before any rough prime is attached. -/
theorem both_signs_with_unit_rough_cofactor (D : ℕ) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop,∀ σ : ℤ,σ=1 ∨ σ= -1 → B*Real.sqrt X*Real.log X^D ≤
      (((smallRoughCofactors (logSquareCutoff X) X 1).filter (fun n => μ n=σ)).card:ℝ) := by
  obtain ⟨c,hc,pop⟩ := scaled_smooth_boxes (a := 1) zero_lt_one le_rfl
  filter_upwards [pop D (max 0 B),(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with X supply large
  intro σ sign
  have h := supply σ sign
  rw [←Real.sqrt_eq_rpow] at h
  have paid := drop_exponential hc.le large (mul_nonneg (Real.sqrt_nonneg X) (pow_nonneg (zero_le_one.trans large) D))
    (K := B) (by simpa only [←mul_assoc] using h)
  rw [mul_assoc]
  apply paid.trans (Nat.cast_le.mpr (card_le_card ?_))
  intro n hn
  obtain ⟨mem,mark⟩ := mem_filter.mp hn
  obtain ⟨⟨⟨np,up⟩,factors⟩,sf⟩ := mem_squarefreeSmoothUpTo.mp mem
  have height : boxHeight 1 X ≤ X := by
    apply Nat.cast_le.mp
    have floor := Nat.floor_le (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) 1) (Real.exp_pos _).le)
    rw [Real.rpow_one] at floor
    exact floor.trans (div_le_self (Nat.cast_nonneg X) (Real.one_le_exp (by norm_num)))
  have empty : (n.primeFactors.filter (fun p => ¬p ≤ logSquareCutoff X))=∅ :=
    filter_eq_empty_iff.mpr (fun p hp => not_not.mpr (Nat.mem_primesLE.mp (factors hp)).1)
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨np,up.trans height⟩,sf⟩,
    by simp only [roughPart,empty,prod_empty,le_refl]⟩,mark⟩

private theorem smooth_quotient_walls :
    ∀ᶠ X : ℕ in atTop,let y := logSquareCutoff X
      let T := X/y
      0<T ∧ Real.sqrt X ≤ T ∧ Real.sqrt X ≤ 2*y*Real.sqrt T ∧
        Real.log X ≤ 2*Real.log T ∧ Real.log T^2 ≤ y := by
  filter_upwards [cutoff_below_power (by norm_num : (0:ℝ)<1/2),
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop ⌈Real.exp 1⌉₊,
    eventually_ge_atTop (2:ℕ)] with X small large pos
  let y := logSquareCutoff X
  let T := X/y
  have xp : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have xe : 1 ≤ (X:ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have e : Real.exp 1 ≤ (y:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr large)
  have y1 : 1 ≤ y := Nat.one_le_cast.mp ((Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans e)
  have yx : y ≤ X := by
    apply Nat.cast_le.mp
    have cheap := Real.rpow_le_rpow_of_exponent_le xe (by norm_num : (1:ℝ)/2 ≤ 1)
    rw [Real.rpow_one] at cheap
    linarith only [small,cheap,Nat.cast_nonneg (α := ℝ) y]
  have tp : 1 ≤ T := (Nat.le_div_iff_mul_le y1).mpr (by simpa only [one_mul] using yx)
  have budget : X ≤ 2*y*T := by
    have rem := Nat.mod_add_div X y
    have modulus := Nat.mod_lt X y1
    have lower := Nat.mul_le_mul_left y tp
    change X%y+y*T=X at rem
    rw [show 2*y*T=2*(y*T) by ring]
    omega
  have br : (X:ℝ) ≤ 2*y*T := by exact_mod_cast budget
  rw [←Real.sqrt_eq_rpow] at small
  have xr := Real.sqrt_pos.mpr xp
  have xroot := Real.mul_self_sqrt xp.le
  have a : Real.sqrt X ≤ T := by
    apply le_of_mul_le_mul_left _ xr
    rw [xroot]
    exact br.trans (mul_le_mul_of_nonneg_right small (Nat.cast_nonneg T))
  have b : Real.sqrt X ≤ 2*(y:ℝ)*Real.sqrt T := by
    have h := Real.sqrt_le_sqrt br
    rw [Real.sqrt_mul (by positivity)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_self_iff.mpr (Or.inr
      (by have r := (Nat.one_le_cast (R := ℝ)).mpr y1; linarith only [r]))) (Real.sqrt_nonneg T))
  have logt := Real.log_le_log xr a
  rw [Real.log_sqrt xp.le] at logt
  have bound := mul_le_mul_of_nonneg_right e (Nat.cast_nonneg (α := ℝ) T)
  have down : (y:ℝ)*T ≤ X := by exact_mod_cast Nat.mul_div_le X y
  exact ⟨tp,a,b,by linarith only [logt],log_wall_above_smaller_height tp (by linarith only [bound,down])⟩

private theorem quotient_at_log_square_cutoff_grows :
    Tendsto (fun X : ℕ => X/logSquareCutoff X) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [smooth_quotient_walls,(Real.tendsto_sqrt_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (k:ℝ)] with X wall bound
  exact Nat.cast_le.mp (bound.trans wall.2.1)

/-- At the centered quotient wall the entire smooth main term exceeds
square root times every fixed logarithmic power, even though it costs
X^(1/2+ε) for every ε>0. -/
theorem smooth_main_term_exceeds_every_square_root_log_price (D : ℕ) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop,let y := logSquareCutoff X
      B*Real.sqrt X*Real.log X^D ≤ (y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card := by
  let T := fun X : ℕ => X/logSquareCutoff X
  have grows : Tendsto T atTop atTop := quotient_at_log_square_cutoff_grows
  let K := max 0 B
  let C := K*(2*2^D)
  filter_upwards [grows (both_smooth_signs_exceed_every_square_root_log_price D C),
    smooth_quotient_walls,eventually_ge_atTop (1:ℕ)] with X supply wall pos
  let y := logSquareCutoff X
  have h := supply y wall.2.2.2.2 (1:ℤ) (Or.inl rfl)
  have sub := (filter_subset (fun n => μ n=(1:ℤ)) (squarefreeSmoothUpTo y (T X))).trans
    (filter_subset Squarefree (smoothUpTo (Nat.primesLE y) (T X)))
  have all := mul_le_mul_of_nonneg_left (h.trans (Nat.cast_le.mpr (card_le_card sub))) (Nat.cast_nonneg (α := ℝ) y)
  have lp := Real.log_nonneg (Nat.one_le_cast.mpr pos : (1:ℝ) ≤ X)
  have floor := mul_le_mul wall.2.2.1 (pow_le_pow_left₀ lp wall.2.2.2.1 D)
    (pow_nonneg lp D) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  rw [mul_pow] at floor
  have inn := mul_le_mul_of_nonneg_left floor (le_max_left 0 B)
  have first := mul_le_mul_of_nonneg_right (le_max_right 0 B) (Real.sqrt_nonneg X)
  calc _ ≤ K*(Real.sqrt X*Real.log X^D) := (mul_le_mul_of_nonneg_right first (pow_nonneg lp D)).trans_eq (by ring)
       _ ≤ _ := inn
       _ = (y:ℝ)*(C*Real.sqrt (T X)*Real.log (T X)^D) := by dsimp only [C]; ring
       _ ≤ _ := all

/-- The entire nonnegative smooth term in the centered identity has
size sqrt X times exp(Θ(log X/log log X)). Both bounds concern the
actual population at every sufficiently large cutoff. -/
theorem exact_second_order_scale_of_the_smooth_main_term :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ᶠ X : ℕ in atTop,let y := logSquareCutoff X
      let L := Real.log (X:ℝ)
      let M := (y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card
      Real.sqrt X*Real.exp (c*L/Real.log L) ≤ M ∧ M ≤ Real.sqrt X*Real.exp (C*L/Real.log L) := by
  obtain ⟨t,ht,lower⟩ := exponential_excess_of_each_smooth_sign
  obtain ⟨C,hC,upper⟩ := critical_upper_price_of_the_smooth_main_term
  let T := fun X : ℕ => X/logSquareCutoff X
  have grows : Tendsto T atTop atTop := quotient_at_log_square_cutoff_grows
  have logs := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp grows)
  refine ⟨t/2,C,half_pos ht,hC,?_⟩
  filter_upwards [grows (lower 0 2),smooth_quotient_walls,upper,logs.eventually_ge_atTop 2]
    with X supply wall hi large
  let y := logSquareCutoff X
  let L := Real.log (X:ℝ)
  let l := Real.log (T X:ℝ)
  have l1 : 1<l := by linarith only [large]
  have lp := zero_lt_one.trans l1
  have ll := Real.log_pos l1
  have order : l ≤ L := Real.log_le_log (Nat.cast_pos.mpr wall.1) (Nat.cast_le.mpr (Nat.div_le_self X y))
  have logs_order := Real.log_le_log lp order
  have scale : (t/2)*L/Real.log L ≤ t*l/Real.log l := by
    apply LE.le.trans _ (div_le_div_of_nonneg_left (mul_nonneg ht.le lp.le) ll logs_order)
    apply div_le_div_of_nonneg_right _ (ll.trans_le logs_order).le
    have ready := mul_le_mul_of_nonneg_right wall.2.2.2.1 ht.le
    linarith only [ready]
  have size := supply y wall.2.2.2.2 (1:ℤ) (Or.inl rfl)
  simp only [pow_zero,mul_one] at size
  have sub := (filter_subset (fun n => μ n=(1:ℤ)) (squarefreeSmoothUpTo y (T X))).trans
    (filter_subset Squarefree (smoothUpTo (Nat.primesLE y) (T X)))
  have obs := mul_le_mul_of_nonneg_left (size.trans (Nat.cast_le.mpr (card_le_card sub))) (Nat.cast_nonneg (α := ℝ) y)
  refine ⟨?_,hi y le_rfl⟩
  have product := mul_le_mul wall.2.2.1 (Real.exp_le_exp.mpr scale) (Real.exp_pos _).le
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  exact product.trans ((le_of_eq (by ring)).trans obs)

/-- At every sufficiently large cutoff, one of the two actual signed
readings has a negative excursion beyond any square-root-log budget.
This conclusion retains the sign forced by the smooth population. -/
theorem negative_excursion_in_one_of_the_two_centered_readings (D : ℕ) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop,let y := logSquareCutoff X
      min (∑ n ∈ Icc 1 X,RoughReading.row y n*Real.log n) (centeredPrimePowerRemainder y X) ≤
        -(B*Real.sqrt X*Real.log X^D) := by
  filter_upwards [smooth_main_term_exceeds_every_square_root_log_price D (2*B),
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1] with X cost yp
  let y := logSquareCutoff X
  let L := ∑ n ∈ Icc 1 X,RoughReading.row y n*Real.log n
  let R := centeredPrimePowerRemainder y X
  have total := exact_centered_prime_power_remainder yp X
  change min L R ≤ _
  linarith only [min_le_left L R,min_le_right L R,cost,total]

end GaloisForLFunctions.RestrictedFactorizationCalculus
