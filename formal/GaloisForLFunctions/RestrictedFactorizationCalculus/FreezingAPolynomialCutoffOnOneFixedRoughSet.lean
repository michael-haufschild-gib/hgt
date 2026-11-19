import GaloisForLFunctions.RestrictedFactorizationCalculus.RecoveringTheMobiusPrefixFromAnIncreasingPrimeCutoff
import GaloisForLFunctions.RHTower.CausalMobiusThetaUniformCycle
import GaloisForLFunctions.RHTower.Sieve.SelbergTail
import GaloisForLFunctions.RHTower.Sieve.KubalalikaLargeScale

/-!
# Freezing a polynomial cutoff on one fixed rough set

Every divisor of an integer with least prime above its own θ-power
passes the same test. A disagreement with the frozen cutoff X^θ
therefore supplies a prime through X^θ and a surviving cofactor
through X^(1−θ). Their two sieve densities give a full second log.
-/

noncomputable section

open Finset Filter RHTower.Sieve GaloisForLFunctions.BezoutValuationIncidence
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The prime cutoff n^θ attached to the integer being tested. -/
def powerCutoff (θ : ℝ) (n : ℕ) := ⌊(n:ℝ)^θ⌋₊

/-- A single arithmetic set, observed through the real endpoint x. -/
def ownPowerRough (θ : ℝ) (x : ℝ) := (Icc 1 ⌊x⌋₊).filter (fun n =>
  ∀ p ∈ n.primeFactors,powerCutoff θ n<p)

private theorem hereditary {θ : ℝ} (hθ : 0 ≤ θ) {n m : ℕ} (pos : 0<n) (div : m ∣ n)
    (good : ∀ p ∈ n.primeFactors,powerCutoff θ n<p) :
    ∀ p ∈ m.primeFactors,powerCutoff θ m<p := by
  intro p hp
  have sub := Nat.floor_le_floor (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_of_dvd pos div)) hθ)
  exact lt_of_le_of_lt sub (good p (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
    (Nat.dvd_of_mem_primeFactors hp).trans div,pos.ne'⟩))

/-- Integers missed by freezing the test at the observation endpoint. -/
def powerFreezingErrors (θ : ℝ) (X : ℕ) := (ownPowerRough θ X).filter (fun n =>
  ∃ p ∈ n.primeFactors,p ≤ powerCutoff θ X)

/-- Each discrepancy supplies its least prime and a cofactor which
passes the original moving test. Both rectangle bounds are sharp in
the exponents. -/
theorem power_freezing_errors_le_prime_cofactor_product {θ : ℝ} (hθ : 0<θ) (small : θ<1) (X : ℕ) :
    (powerFreezingErrors θ X).card ≤ (Nat.primesLE (powerCutoff θ X)).card*
      (ownPowerRough θ ((X:ℝ)^(1-θ))).card := by
  rw [←card_product]
  apply card_le_card_of_injOn (fun n => (n.minFac,n/n.minFac))
  · intro n hn
    obtain ⟨mem,⟨q,hq,cut⟩⟩ := mem_filter.mp hn
    obtain ⟨obs,good⟩ := mem_filter.mp mem
    rw [Nat.floor_natCast] at obs
    obtain ⟨pos,nt⟩ := mem_Icc.mp obs
    have unit : n ≠ 1 := by rintro rfl; simpa using hq
    let p := n.minFac
    let m := n/p
    have pr := Nat.minFac_prime unit
    have hp := Nat.mem_primeFactors.mpr ⟨pr,Nat.minFac_dvd _,Nat.ne_of_gt (show 0<n from pos)⟩
    have psmall : p ≤ powerCutoff θ X :=
      (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le (Nat.dvd_of_mem_primeFactors hq)).trans cut
    have pm : p*m=n := Nat.mul_div_cancel' (Nat.minFac_dvd _)
    have mpos : 0< m := by
      apply Nat.pos_of_ne_zero; intro z
      have zero : n=0 := pm.symm.trans (by rw [z,mul_zero])
      exact Nat.ne_of_gt (show 0<n from pos) zero
    have md : m ∣ n := ⟨p,pm.symm.trans (mul_comm ..)⟩
    have n0 : (0:ℝ)<n := Nat.cast_pos.mpr pos
    have less : (n:ℝ)^θ<p := (Nat.floor_lt (Real.rpow_nonneg n0.le _)).mp (good p hp)
    have product : (p:ℝ)*m=n := by exact_mod_cast pm
    have mmax : (m:ℝ) ≤ (X:ℝ)^(1-θ) := by
      apply LE.le.trans _ (Real.rpow_le_rpow n0.le (Nat.cast_le.mpr nt) (sub_nonneg.mpr small.le))
      apply le_of_mul_le_mul_left _ (Real.rpow_pos_of_pos n0 θ)
      rw [←Real.rpow_add n0,show θ+(1-θ)=1 by ring,Real.rpow_one]
      exact (mul_le_mul_of_nonneg_right less.le (Nat.cast_nonneg m)).trans_eq product
    exact mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨psmall,pr⟩,mem_filter.mpr
      ⟨mem_Icc.mpr ⟨mpos,Nat.le_floor mmax⟩,hereditary hθ.le pos md good⟩⟩
  · intro n _ m _ eq
    have first : n.minFac=m.minFac := congrArg Prod.fst eq
    have second : n/n.minFac=m/m.minFac := congrArg Prod.snd eq
    exact (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm.trans
      ((congrArg₂ (· * ·) first second).trans (Nat.mul_div_cancel' (Nat.minFac_dvd m)))

/-- The logarithm of the integer polynomial cutoff eventually retains
at least half of its real exponent. -/
theorem logarithmic_bounds_on_a_power_cutoff {a : ℝ} (ha : 0<a) :
    ∀ᶠ x : ℝ in atTop,2 ≤ ⌊x^a⌋₊ ∧ a*Real.log x/2 ≤ Real.log ⌊x^a⌋₊ := by
  filter_upwards [(tendsto_rpow_atTop ha).eventually_ge_atTop 4,
    Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log 2/a),eventually_ge_atTop (1:ℝ)]
    with x high logHigh x1
  have x0 := zero_lt_one.trans_le x1
  have two : 2 ≤ ⌊x^a⌋₊ := Nat.le_floor (by push_cast; linarith only [high])
  refine ⟨two,?_⟩
  have half : x^a/2 ≤ (⌊x^a⌋₊:ℝ) := by linarith only [Nat.lt_floor_add_one (x^a),high]
  have read := Real.log_le_log (by positivity : 0<x^a/2) half
  rw [Real.log_div (Real.rpow_pos_of_pos x0 _).ne' (by norm_num),Real.log_rpow x0] at read
  linarith only [read,(div_le_iff₀ ha).mp logHigh]

/-- A fixed power-rough set has at most C x/log x members through x.
The bound counts repeated prime factors as well. -/
theorem upper_count_on_one_polynomial_rough_set {θ : ℝ} (hθ : 0<θ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ x : ℝ in atTop,((ownPowerRough θ x).card:ℝ)*Real.log x ≤ C*x := by
  let a := min (θ/2) (1/8)
  have ha : 0<a := lt_min (half_pos hθ) (by norm_num)
  have eighth : a ≤ 1/8 := min_le_right ..
  let K := Real.exp (4*mertensSecondUpperConst)
  have kp : 0<K := Real.exp_pos _
  refine ⟨2+4/a,by positivity,?_⟩
  filter_upwards [logarithmic_bounds_on_a_power_cutoff ha,eventually_ge_atTop (2:ℝ),
    eventually_const_mul_one_add_log_pow_le_rpow (by norm_num : (0:ℝ)<1/2) zero_lt_one 1,
    eventually_const_mul_one_add_log_pow_le_rpow (by norm_num : (0:ℝ)<1/4) kp 4]
    with x zlog x2 sqrtLog fourth
  let z := ⌊x^a⌋₊
  have x1 : (1:ℝ) ≤ x := by linarith only [x2]
  have xp := zero_lt_one.trans_le x1
  have lx := Real.log_pos (show 1<x by linarith only [x2])
  have ztwo : 2 ≤ z := zlog.1
  have zpos : (0:ℝ)<z := Nat.cast_pos.mpr (by omega)
  have lz := Real.log_pos (show (1:ℝ)<z by exact_mod_cast (by have := zlog.1; omega : 1<z))
  let R := (Ioc 0 ⌊x⌋₊).filter (fun n => ∀ p ∈ Nat.primesLE z,¬p ∣ n)
  have sub : ownPowerRough θ x ⊆ Icc 1 ⌊Real.sqrt x⌋₊ ∪ R := by
    intro n hn
    obtain ⟨obs,good⟩ := mem_filter.mp hn
    obtain ⟨pos,upper⟩ := mem_Icc.mp obs
    by_cases low : n ≤ ⌊Real.sqrt x⌋₊
    · exact mem_union_left _ (mem_Icc.mpr ⟨pos,low⟩)
    · have root := (Nat.floor_lt (Real.sqrt_nonneg x)).mp (lt_of_not_ge low)
      have hpow := Real.rpow_le_rpow (Real.sqrt_nonneg x) root.le hθ.le
      rw [Real.sqrt_eq_rpow,←Real.rpow_mul xp.le,show (1/2:ℝ)*θ=θ/2 by ring] at hpow
      have cut : z ≤ powerCutoff θ n := Nat.floor_le_floor
        ((Real.rpow_le_rpow_of_exponent_le x1 (min_le_left (θ/2) _)).trans hpow)
      refine mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨pos,upper⟩,fun p hp dvd => ?_⟩)
      exact (good p (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hp,dvd,Nat.ne_of_gt (show 0<n from pos)⟩)).not_ge
        ((Nat.mem_primesLE.mp hp).1.trans cut)
  have raw := (card_le_card sub).trans (card_union_le ..)
  rw [Nat.card_Icc,Nat.add_sub_cancel] at raw
  have rcount := card_rough_Ioc_le_selberg 0 ⌊x⌋₊ z z (Nat.zero_le _) (by omega : 1 ≤ z)
    le_rfl zlog.1 lz
  change (R.card:ℝ) ≤ _ at rcount
  simp only [Nat.cast_zero,sub_zero] at rcount
  have floorx := Nat.floor_le xp.le
  have zle : (z:ℝ) ≤ x^a := Nat.floor_le (Real.rpow_nonneg xp.le _)
  have a1 : a ≤ 1 := by linarith only [eighth]
  have zX := zle.trans ((Real.rpow_le_rpow_of_exponent_le x1 a1).trans_eq (Real.rpow_one x))
  have logz := Real.log_le_log zpos zX
  have z2 : (z:ℝ)*z ≤ x^(1/4:ℝ) := by
    have h := mul_self_le_mul_self (Nat.cast_nonneg z) zle
    rw [←Real.rpow_add xp] at h
    exact h.trans (Real.rpow_le_rpow_of_exponent_le x1 (by linarith only [eighth]))
  have logs : K*Real.log z^(4:ℝ) ≤ x^(1/4:ℝ) := by
    rw [show (4:ℝ)=((4:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lz.le (by linarith only [logz]) 4) kp.le).trans fourth
  have err : selbergFibreError z z ≤ Real.sqrt x := by
    unfold selbergFibreError
    rw [Nat.cast_mul,Real.sqrt_eq_rpow,show (1/2:ℝ)=1/4+1/4 by norm_num,Real.rpow_add xp]
    exact mul_le_mul z2 logs (mul_nonneg kp.le (Real.rpow_nonneg lz.le _))
      (Real.rpow_nonneg xp.le _)
  have den : (2/Real.log z)*Real.log x ≤ 4/a := by
    rw [div_mul_eq_mul_div,div_le_div_iff₀ lz ha]
    linarith only [zlog.2]
  have main := mul_le_mul_of_nonneg_left den xp.le
  have rt : Real.log x ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]; simp only [pow_one,one_mul] at sqrtLog
    linarith only [sqrtLog]
  have paid := (mul_le_mul_of_nonneg_left rt (Real.sqrt_nonneg x)).trans_eq (Real.mul_self_sqrt xp.le)
  have count : ((ownPowerRough θ x).card:ℝ) ≤ (⌊Real.sqrt x⌋₊:ℝ)+R.card := by exact_mod_cast raw
  have bound := count.trans (add_le_add (Nat.floor_le (Real.sqrt_nonneg x)) (rcount.trans (add_le_add
    (mul_le_mul_of_nonneg_right floorx (div_nonneg (by norm_num) lz.le)) err)))
  linarith only [mul_le_mul_of_nonneg_right bound lx.le,main,paid]

private theorem prime_population_subset {θ : ℝ} (small : θ<1) (x : ℝ) :
    Nat.primesLE ⌊x⌋₊ ⊆ ownPowerRough θ x := by
  intro p hp
  obtain ⟨bound,pr⟩ := Nat.mem_primesLE.mp hp
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨pr.pos,bound⟩,?_⟩
  intro q hq
  rw [pr.primeFactors,mem_singleton] at hq
  subst q
  have base : (1:ℝ)<p := by exact_mod_cast pr.one_lt
  apply (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg p) _)).mpr
  exact (Real.rpow_lt_rpow_of_exponent_lt base small).trans_eq (Real.rpow_one _)

/-- At every sufficiently large observation cutoff, freezing its
polynomial prime threshold misclassifies at most C X/log² X integers.
The estimate is unsigned and counts nonsquarefree integers as well. -/
theorem second_log_saving_for_freezing_a_polynomial_cutoff {θ : ℝ} (hθ : 0<θ) (small : θ<1) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ X : ℕ in atTop,
      ((powerFreezingErrors θ X).card:ℝ)*Real.log X^2 ≤ D*X := by
  obtain ⟨C,hC,sieve⟩ := upper_count_on_one_polynomial_rough_set hθ
  have tail := sub_pos.mpr small
  let D := C^2/(θ*(1-θ))
  have dp : 0<D := div_pos (pow_pos hC _) (mul_pos hθ tail)
  refine ⟨D,dp,?_⟩
  filter_upwards [(tendsto_rpow_atTop hθ |>.comp tendsto_natCast_atTop_atTop) sieve,
    (tendsto_rpow_atTop tail |>.comp tendsto_natCast_atTop_atTop) sieve,
    eventually_ge_atTop (2:ℕ)] with X a b pos
  have x0 : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have log0 := Real.log_pos (show (1:ℝ)<X by exact_mod_cast (by omega : 1<X))
  let P := (Nat.primesLE (powerCutoff θ X)).card
  let Q := (ownPowerRough θ ((X:ℝ)^(1-θ))).card
  have pbound : (P:ℝ)*(θ*Real.log X) ≤ C*(X:ℝ)^θ := by
    change ((ownPowerRough θ ((X:ℝ)^θ)).card:ℝ)*Real.log ((X:ℝ)^θ) ≤ _ at a
    rw [Real.log_rpow x0] at a
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (prime_population_subset small _)))
      (mul_nonneg hθ.le log0.le)).trans a
  change (Q:ℝ)*Real.log ((X:ℝ)^(1-θ)) ≤ _ at b
  rw [Real.log_rpow x0] at b
  have prod := mul_le_mul pbound b (mul_nonneg (Nat.cast_nonneg Q) (mul_nonneg tail.le log0.le))
    (mul_nonneg hC.le (Real.rpow_nonneg x0.le _))
  have size : ((powerFreezingErrors θ X).card:ℝ) ≤ (P:ℝ)*Q := by
    exact_mod_cast power_freezing_errors_le_prime_cofactor_product hθ small X
  have iden : (X:ℝ)^θ*(X:ℝ)^(1-θ)=X := by rw [←Real.rpow_add x0,show θ+(1-θ)=1 by ring,Real.rpow_one]
  apply (mul_le_mul_iff_left₀ (mul_pos hθ tail)).mp
  calc _ ≤ ((P:ℝ)*Q*Real.log X^2)*(θ*(1-θ)) := mul_le_mul_of_nonneg_right
             (mul_le_mul_of_nonneg_right size (sq_nonneg _)) (mul_pos hθ tail).le
       _ = ((P:ℝ)*(θ*Real.log X))*((Q:ℝ)*((1-θ)*Real.log X)) := by ring
       _ ≤ _ := prod
       _ = (D*X)*(θ*(1-θ)) := by
         calc C*(X:ℝ)^θ*(C*(X:ℝ)^(1-θ)) = C^2*((X:ℝ)^θ*(X:ℝ)^(1-θ)) := by ring
              _ = _ := by rw [iden]; dsimp only [D]; field_simp [(mul_pos hθ tail).ne']

private theorem primorial_test (y n : ℕ) (pos : 0<n) :
    (primorial y).Coprime n ↔ ∀ p ∈ n.primeFactors,y<p := by
  constructor
  · intro h p hp
    have pr := Nat.prime_of_mem_primeFactors hp
    exact lt_of_not_ge (fun bad => pr.not_dvd_one (h ▸ Nat.dvd_gcd
      (pr.dvd_primorial_iff.mpr bad) (Nat.dvd_of_mem_primeFactors hp)))
  · exact RHTower.coprime_primorial_of_primeFactors_gt pos

/-- The unsigned discrepancy pays for changing the actual signed
prefix from the fixed arithmetic set to the frozen prime cutoff. -/
theorem signed_freezing_error {θ : ℝ} (hθ : 0<θ) (X : ℕ) :
    |siftedPrefix (powerCutoff θ) X-coprimeMoebiusSum (primorial (powerCutoff θ X)) X| ≤
      (powerFreezingErrors θ X).card := by
  unfold siftedPrefix coprimeMoebiusSum
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  let e := fun n : ℕ => (∀ p ∈ n.primeFactors,powerCutoff θ n<p) ∧
    ∃ p ∈ n.primeFactors,p ≤ powerCutoff θ X
  have cnt : ((powerFreezingErrors θ X).card:ℝ)=∑ n ∈ Icc 1 X,if e n then 1 else 0 := by
    simp only [powerFreezingErrors,ownPowerRough,Nat.floor_natCast,filter_filter,←sum_boole,e]
  rw [cnt]
  apply sum_le_sum
  intro n hn
  obtain ⟨pos,nt⟩ := mem_Icc.mp hn
  have ne : powerCutoff θ n ≤ powerCutoff θ X := Nat.floor_le_floor
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr nt) hθ.le)
  simp only [coprimeMoebiusIndicator,primorial_test _ _ pos]
  by_cases fixed : ∀ p ∈ n.primeFactors,powerCutoff θ X<p
  · have own : ∀ p ∈ n.primeFactors,powerCutoff θ n<p := fun p hp => ne.trans_lt (fixed p hp)
    have no : ¬e n := fun ⟨_,p,hp,low⟩ => (fixed p hp).not_ge low
    simp [fixed,own,no]
  · by_cases own : ∀ p ∈ n.primeFactors,powerCutoff θ n<p
    · have paid : e n := ⟨own,by simpa only [not_forall,exists_prop,not_lt] using fixed⟩
      simp only [fixed,own,if_true,if_false,sub_zero,paid]
      exact_mod_cast (abs_moebius_le_one (n := n))
    · have no : ¬e n := fun h => own h.1
      simp [fixed,own,no]

end GaloisForLFunctions.RestrictedFactorizationCalculus
