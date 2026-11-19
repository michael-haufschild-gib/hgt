import GaloisForLFunctions.RestrictedFactorizationCalculus.RecoveringTheMobiusPrefixFromAnIncreasingPrimeCutoff
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheMertensAbscissaOnOneDensityZeroFixedSet
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSieveResidue
import Mathlib.Analysis.PSeries

/-!
# The explicit log-square rough set

The square-root criterion holds for the full Möbius prefix exactly when
it holds on the fixed set of integers having no prime divisor up to the
square of the integer part of log(n+1). Above one half, the cost of
undoing all the Euler factors through this cutoff is subpolynomial.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical Topology ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The cutoff attached to n itself. -/
def logSquareCutoff (n : ℕ) := ⌊Real.log ((n:ℝ)+1)⌋₊^2

/-- The sharp prefix of the fixed set passing the log-square prime test. -/
def logSquareRoughSet (X : ℕ) :=
  (Icc 1 X).filter (fun n => (primorial (logSquareCutoff n)).Coprime n)

/-- The prime cutoff increases with the tested integer. -/
theorem logSquareCutoff_mono : Monotone logSquareCutoff := by
  intro n m h
  exact Nat.pow_le_pow_left (Nat.floor_le_floor (Real.log_le_log (by positivity)
    (add_le_add_left (Nat.cast_le.mpr h) 1))) _

private theorem sifted_eq_rough (X : ℕ) :
    siftedPrefix logSquareCutoff X=∑ n ∈ logSquareRoughSet X,(μ n:ℝ) := by
  rw [logSquareRoughSet,sum_filter]
  rfl

private theorem cutoff_grows : Tendsto logSquareCutoff atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  have h := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (k:ℝ)
  filter_upwards [h,eventually_ge_atTop (1:ℕ)] with n hn hn1
  change (k:ℝ) ≤ Real.log n at hn
  have hh := hn.trans (Real.log_le_log (Nat.cast_pos.mpr hn1) (by linarith : (n:ℝ) ≤ n+1))
  exact (Nat.le_floor hh).trans (Nat.le_self_pow (by decide : 2 ≠ 0) _)

private theorem log_price_bound {s r : ℝ} (hs : 0<s) (hr : 0<r) (hsr : 1<s+r) :
    ∃ K : ℝ,0<K ∧ ∀ y : ℕ,Real.log (deletionPrice s y) ≤ K*(y:ℝ)^r := by
  let w := fun p : ℕ => (1/(p:ℝ))^s
  let a := 1-w 2
  let f := fun p : ℕ => ((p:ℝ)^(s+r))⁻¹
  have hsum : Summable f := Real.summable_nat_rpow_inv.mpr hsr
  have ha : 0<a := sub_pos.mpr (deletion_weight_lt_one hs Nat.prime_two)
  have fpos (p : ℕ) : 0 ≤ f p := inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hpos : 0 ≤ ∑' n,f n := tsum_nonneg fpos
  refine ⟨((∑' n,f n)+1)/a,div_pos (by linarith only [hpos]) ha,fun y => ?_⟩
  have y0 := Real.rpow_nonneg (Nat.cast_nonneg y) r
  have single (p : ℕ) (hp : p ∈ Nat.primesLE y) :
      Real.log ((1-w p)⁻¹) ≤ ((y:ℝ)^r/a)*f p := by
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hp
    have p0 : (0:ℝ)<p := Nat.cast_pos.mpr hpr.pos
    have p2 : (2:ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have small : w p ≤ w 2 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/p)
      (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) p2) hs.le
    have gap : 0<1-w p := sub_pos.mpr (deletion_weight_lt_one hs hpr)
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr gap)
    have invgap : (1-w p)⁻¹-1=w p/(1-w p) := by field_simp [gap.ne']; ring
    rw [invgap] at hlog
    have hle' := div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1/p) s)
      ha (sub_le_sub_left small 1)
    have eq : w p=(p:ℝ)^r*f p := by
      dsimp only [w,f]
      rw [one_div,Real.inv_rpow p0.le,Real.rpow_add p0]
      field_simp [(Real.rpow_pos_of_pos p0 r).ne',(Real.rpow_pos_of_pos p0 s).ne']
    have hweight := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow p0.le (Nat.cast_le.mpr hle) hr.le) (fpos p)
    calc _ ≤ w p/a := hlog.trans hle'
         _ ≤ ((y:ℝ)^r*f p)/a := div_le_div_of_nonneg_right (eq.trans_le hweight) ha.le
         _ = _ := by ring
  have hnz (p : ℕ) (hp : p ∈ Nat.primesLE y) : (1-w p)⁻¹ ≠ 0 :=
    (inv_pos.mpr (sub_pos.mpr (deletion_weight_lt_one hs (Nat.mem_primesLE.mp hp).2))).ne'
  change Real.log (∏ p ∈ Nat.primesLE y,(1-w p)⁻¹) ≤ _
  rw [Real.log_prod hnz]
  calc _ ≤ ∑ p ∈ Nat.primesLE y,((y:ℝ)^r/a)*f p := sum_le_sum single
       _ = ((y:ℝ)^r/a)*∑ p ∈ Nat.primesLE y,f p := (mul_sum ..).symm
       _ ≤ ((y:ℝ)^r/a)*∑' p,f p := mul_le_mul_of_nonneg_left
         (hsum.sum_le_tsum _ (fun p _ => fpos p)) (div_nonneg y0 ha.le)
       _ ≤ _ := by
         have pos := div_nonneg y0 ha.le
         calc _ ≤ ((y:ℝ)^r/a)*((∑' p,f p)+1) := mul_le_mul_of_nonneg_left (by linarith) pos
              _ = _ := by ring

/-- All Euler factors through the moving log-square cutoff, including the
variation cost of that cutoff, cost less than any positive power above
the exponent one half. -/
theorem log_square_deletion_cost {s η : ℝ} (hs : 1/2<s) (hη : 0<η) :
    ∀ᶠ X : ℕ in atTop,
      ((logSquareCutoff X:ℝ)+1)*(deletionPrice s (logSquareCutoff X))^2 ≤ (X:ℝ)^η := by
  let r := (max 0 (1-s)+1/2)/2
  have hmax : max 0 (1-s)<(1/2:ℝ) := max_lt (by norm_num) (by linarith only [hs])
  have hr : 0<r := by dsimp only [r]; linarith only [le_max_left (0:ℝ) (1-s)]
  have hr2 : 2*r<1 := by dsimp only [r]; linarith only [hmax]
  have hsr : 1<s+r := by dsimp only [r]; linarith only [le_max_right (0:ℝ) (1-s),hmax]
  obtain ⟨K,hK,hlog⟩ := log_price_bound (by linarith only [hs]) hr hsr
  let C := ((1/r)+2*K)*(5:ℝ)^r
  have Cpos : 0<C := by dsimp only [C]; positivity
  have tog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_atTop (sub_pos.mpr hr2)).comp tog).eventually_ge_atTop (C/η)
  filter_upwards [ht,tog.eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ)] with X hX hlog1 hX2
  let L := Real.log X
  let y := logSquareCutoff X
  let E := deletionPrice s y
  have hx : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  change 1 ≤ L at hlog1
  have hl := zero_lt_one.trans_le hlog1
  have boundLog : Real.log ((X:ℝ)+1) ≤ 2*L := by
    have hb : (X:ℝ)+1 ≤ (X:ℝ)^2 := by
      have hxx : (2:ℝ) ≤ X := by exact_mod_cast hX2
      nlinarith only [sq_nonneg ((X:ℝ)-1),hxx]
    have hh := Real.log_le_log (by positivity) hb
    simpa only [Real.log_pow,Nat.cast_ofNat,L] using hh
  have hfloor := (Nat.floor_le (Real.log_nonneg (by linarith only [hx1] : (1:ℝ) ≤ X+1))).trans boundLog
  have hY : (y:ℝ)+1 ≤ 5*L^2 := by
    change ((⌊Real.log ((X:ℝ)+1)⌋₊^2:ℕ):ℝ)+1 ≤ _
    push_cast only [Nat.cast_pow]
    nlinarith only [sq_le_sq' ((neg_nonpos.mpr (by positivity : (0:ℝ) ≤ 2*L)).trans (Nat.cast_nonneg _)) hfloor,
      mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) hlog1]
  have hYr := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (y:ℝ)+1) hY hr.le
  rw [Real.mul_rpow (by norm_num) (sq_nonneg L),←Real.rpow_natCast L 2,←Real.rpow_mul hl.le] at hYr
  norm_num only [Nat.cast_ofNat] at hYr
  have Epos : 0<E := prod_pos (fun p hp => inv_pos.mpr (sub_pos.mpr
    (deletion_weight_lt_one (by linarith only [hs] : 0<s) (Nat.mem_primesLE.mp hp).2)))
  have hlogY := Real.log_le_rpow_div (by positivity : (0:ℝ) ≤ (y:ℝ)+1) hr
  have ystep := Real.rpow_le_rpow (Nat.cast_nonneg y) (by linarith : (y:ℝ) ≤ y+1) hr.le
  have ctl : Real.log ((y:ℝ)+1)+2*Real.log E ≤ C*L^(2*r) := by
    have upE := (hlog y).trans (mul_le_mul_of_nonneg_left (ystep.trans hYr) hK.le)
    have upY := hlogY.trans (div_le_div_of_nonneg_right hYr hr.le)
    change Real.log E ≤ K*(5^r*L^(2*r)) at upE
    calc _ ≤ (5:ℝ)^r*L^(2*r)/r+2*(K*(5^r*L^(2*r))) :=
           add_le_add upY (mul_le_mul_of_nonneg_left upE (by norm_num))
         _ = _ := by dsimp only [C]; ring
  change C/η ≤ L^(1-2*r) at hX
  have hprod := mul_le_mul_of_nonneg_right ((div_le_iff₀ hη).1 hX) (Real.rpow_nonneg hl.le (2*r))
  have eq : L^(1-2*r)*L^(2*r)=L := by rw [←Real.rpow_add hl,sub_add_cancel,Real.rpow_one]
  have ub : C*L^(2*r) ≤ η*L := by
    calc _ ≤ η*(L^(1-2*r)*L^(2*r)) := by linarith only [hprod]
         _ = _ := by rw [eq]
  apply (Real.log_le_log_iff (by positivity : 0<((y:ℝ)+1)*E^2) (Real.rpow_pos_of_pos hx η)).1
  rw [Real.log_mul (by positivity) (pow_ne_zero _ Epos.ne'),Real.log_pow,Real.log_rpow hx]
  exact ctl.trans ub

/-- Counting the coprime classes by full periods and one partial period. -/
theorem coprime_population_in_a_prefix (Q : ℕ) (hQ : 0<Q) (X : ℕ) :
    (((Icc 1 X).filter (fun n => Q.Coprime n)).card:ℝ) ≤
      (Q.totient:ℝ)*((X:ℝ)/Q+1) := by
  let V := (range Q).filter (fun n => Q.Coprime n)
  have sub : ((Icc 1 X).filter (fun n => Q.Coprime n)).card ≤ (V.product (range (X/Q+1))).card := by
    apply card_le_card_of_injOn (fun n => (n%Q,n/Q))
    · intro n hn
      obtain ⟨hi,hcop⟩ := mem_filter.mp hn
      have modcop : Q.Coprime (n%Q) := by
        change Q.gcd (n%Q)=1
        rw [Nat.gcd_comm,(Nat.mod_modEq n Q).gcd_eq,Nat.gcd_comm]
        exact hcop
      exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hQ),modcop⟩,
        mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp hi).2))⟩
    · intro a _ b _ hh
      exact (Nat.mod_add_div a Q).symm.trans (by rw [show a%Q=b%Q from congrArg Prod.fst hh,
        show a/Q=b/Q from congrArg Prod.snd hh,Nat.mod_add_div])
  have hcnt := sub.trans_eq (card_product V (range (X/Q+1)))
  rw [card_range] at hcnt
  have qpos : (0:ℝ)<Q := Nat.cast_pos.mpr hQ
  have hfrac : ((X/Q:ℕ):ℝ) ≤ (X:ℝ)/Q := (le_div_iff₀ qpos).2 (by exact_mod_cast Nat.div_mul_le_self X Q)
  have cast : (((Icc 1 X).filter (fun n => Q.Coprime n)).card:ℝ) ≤ Q.totient*(((X/Q:ℕ):ℝ)+1) := by
    exact_mod_cast hcnt
  exact cast.trans (mul_le_mul_of_nonneg_left (add_le_add_left hfrac _) (Nat.cast_nonneg _))

/-- The explicit fixed set has natural density zero. -/
theorem density_zero_of_log_square_rough_set {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ((logSquareRoughSet X).card:ℝ) ≤ ε*X := by
  obtain ⟨Z,hZ⟩ := (RHTower.WeilSingularArithmetic.tendsto_coprimeDensity_primorial.eventually_lt_const
    (half_pos hε)).exists
  let Q := primorial Z
  have qpos : 0<Q := primorial_pos _
  haveI : NeZero Q := ⟨qpos.ne'⟩
  change RHTower.WeilSingularArithmetic.coprimeDensity Q<ε/2 at hZ
  rw [RHTower.WeilSingularArithmetic.coprimeDensity_eq_totient_div] at hZ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (cutoff_grows.eventually_ge_atTop Z)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2*((N:ℝ)+Q.totient)/ε)] with X hX
  have sub : logSquareRoughSet X ⊆ range N ∪ (Icc 1 X).filter (fun n => Q.Coprime n) := by
    intro n hn
    obtain ⟨hi,hcop⟩ := mem_filter.mp hn
    by_cases early : n<N
    · exact mem_union_left _ (mem_range.mpr early)
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,
        Nat.Coprime.coprime_dvd_left (primorial_dvd_primorial (hN n (le_of_not_gt early))) hcop⟩)
  have hcnt := (card_le_card sub).trans (card_union_le ..)
  rw [card_range] at hcnt
  have hh : ((logSquareRoughSet X).card:ℝ) ≤ N+(((Icc 1 X).filter (fun n => Q.Coprime n)).card:ℝ) := by
    exact_mod_cast hcnt
  have htail := coprime_population_in_a_prefix Q qpos X
  have hm := mul_le_mul_of_nonneg_right hZ.le (Nat.cast_nonneg X)
  have hroom := (div_le_iff₀ hε).1 hX
  calc _ ≤ N+(Q.totient:ℝ)*((X:ℝ)/Q+1) := hh.trans (add_le_add_right htail _)
       _ = ((Q.totient:ℝ)/Q)*X+((N:ℝ)+Q.totient) := by ring
       _ ≤ _ := by linarith only [hm,hroom]

/-- A power estimate beyond a finite initial segment extends to the whole prefix. -/
theorem prefixPower_of_eventual {f : ℕ → ℝ} (h0 : f 0=0) {s C : ℝ} (hs : 0<s)
    (h : ∀ᶠ n : ℕ in atTop,|f n| ≤ C*(n:ℝ)^s) : PrefixPower s f := by
  by_contra hn
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨n,hnN,hbig⟩ := arbitrarily_large_power_witness h0 hs hn N ⌈C⌉₊
  exact hbig.not_ge ((hN n hnN.le).trans (mul_le_mul_of_nonneg_right (Nat.le_ceil C)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

/-- Above one half the two signed prefixes transfer every power with
arbitrarily small exponent loss in either direction. -/
theorem power_transfer_on_the_log_square_rough_set {s : ℝ} (hs : 1/2<s) :
    (PrefixPower s (coprimeMoebiusSum 1) → ∀ η : ℝ,0<η →
      PrefixPower (s+η) (fun X => ∑ n ∈ logSquareRoughSet X,(μ n:ℝ))) ∧
    (PrefixPower s (fun X => ∑ n ∈ logSquareRoughSet X,(μ n:ℝ)) → ∀ η : ℝ,0<η →
      PrefixPower (s+η) (coprimeMoebiusSum 1)) := by
  have hs0 : 0<s := by linarith only [hs]
  constructor
  · rintro ⟨C,hC,h⟩ η hη
    apply prefixPower_of_eventual (C := 4*C) (by simp [logSquareRoughSet]) (add_pos hs0 hη)
    filter_upwards [log_square_deletion_cost hs hη,eventually_ge_atTop (1:ℕ)] with X hprice hX
    have hh := sifted_prefix_from_full_prefix logSquareCutoff logSquareCutoff_mono hs0 hC h X
    rw [sifted_eq_rough] at hh
    let E := deletionPrice s (logSquareCutoff X)
    have hE : 1 ≤ E := deletionPrice_one_le hs0 _
    have hpow := mul_le_mul_of_nonneg_left hE (zero_le_one.trans hE)
    have hsingle : E ≤ E^2 := by linarith only [hpow]
    have hfactor := (mul_le_mul_of_nonneg_left hsingle (by positivity : (0:ℝ) ≤ (logSquareCutoff X:ℝ)+1)).trans hprice
    apply hh.trans
    rw [Real.rpow_add (Nat.cast_pos.mpr hX)]
    calc _ = (4*C)*(((logSquareCutoff X:ℝ)+1)*E)*(X:ℝ)^s := by ring
         _ ≤ (4*C)*(X:ℝ)^η*(X:ℝ)^s := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left hfactor (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg X) _)
         _ = _ := by ring
  · rintro ⟨C,hC,h⟩ η hη
    apply prefixPower_of_eventual (C := 2*C) (by simp [coprimeMoebiusSum]) (add_pos hs0 hη)
    filter_upwards [log_square_deletion_cost hs hη,eventually_ge_atTop (1:ℕ)] with X hprice hX
    have hh := full_prefix_from_sifted_prefix logSquareCutoff logSquareCutoff_mono hs0 hC
      (fun n => by rw [sifted_eq_rough]; exact h n) X
    apply hh.trans
    rw [Real.rpow_add (Nat.cast_pos.mpr hX)]
    calc _ = (2*C)*(((logSquareCutoff X:ℝ)+1)*(deletionPrice s (logSquareCutoff X))^2)*(X:ℝ)^s := by ring
         _ ≤ (2*C)*(X:ℝ)^η*(X:ℝ)^s := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left hprice (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
         _ = _ := by ring

/-- The square-root-plus-epsilon criterion on one explicitly specified
density-zero set, uniformly over every sharp cutoff. -/
theorem square_root_on_the_explicit_log_square_rough_set :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (fun X => ∑ n ∈ logSquareRoughSet X,(μ n:ℝ))) ↔
    ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1) := by
  constructor <;> intro h ε hε
  · have half := half_pos hε
    have hh := (power_transfer_on_the_log_square_rough_set (lt_add_of_pos_right (1/2:ℝ) half)).2 (h _ half) _ half
    rwa [show (1:ℝ)/2+ε/2+ε/2=1/2+ε by ring] at hh
  · have half := half_pos hε
    have hh := (power_transfer_on_the_log_square_rough_set (lt_add_of_pos_right (1/2:ℝ) half)).1 (h _ half) _ half
    rwa [show (1:ℝ)/2+ε/2+ε/2=1/2+ε by ring] at hh

#print axioms log_square_deletion_cost
#print axioms density_zero_of_log_square_rough_set
#print axioms power_transfer_on_the_log_square_rough_set
#print axioms square_root_on_the_explicit_log_square_rough_set

end GaloisForLFunctions.RestrictedFactorizationCalculus
