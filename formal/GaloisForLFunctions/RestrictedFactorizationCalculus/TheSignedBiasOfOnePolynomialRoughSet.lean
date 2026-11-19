import GaloisForLFunctions.RestrictedFactorizationCalculus.FreezingAPolynomialCutoffOnOneFixedRoughSet
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheLogarithmicThresholdForRoughMobiusCharge

/-!
# The signed bias of one polynomially rough set

The negative smooth main term at the quotient endpoint survives when
every integer uses its own polynomial cutoff. In particular each such
fixed arithmetic set has a signed imbalance of order X/log X at every
sufficiently large endpoint.
-/

noncomputable section

open Filter Finset RHTower.Sieve GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem powers_fit {θ : ℝ} (hθ : 0<θ) (small : θ<1) :
    ∃ j : ℕ,∀ Z : ℕ,∀ᶠ X : ℕ in atTop,Z ≤ powerCutoff θ X ∧ Z*powerCutoff θ X ≤ X ∧ X ≤ powerCutoff θ X^j := by
  let j := ⌈2/θ⌉₊
  have enough := (div_le_iff₀ hθ).mp (Nat.le_ceil (2/θ))
  refine ⟨j,fun Z => ?_⟩
  have grows := (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have quotient := (tendsto_rpow_atTop (sub_pos.mpr small)).comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_natCast_atTop_atTop (logarithmic_bounds_on_a_power_cutoff hθ),
    grows.eventually_ge_atTop (Z:ℝ),quotient.eventually_ge_atTop (Z:ℝ),eventually_ge_atTop (2:ℕ)]
    with X hlog hy hq pos
  let y := powerCutoff θ X
  have xp : (0:ℝ)<X := by exact_mod_cast (by omega : 0<X)
  have x1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have equal : (X:ℝ)^(1-θ)*(X:ℝ)^θ=X := by rw [←Real.rpow_add xp,sub_add_cancel,Real.rpow_one]
  have upper : (Z:ℝ)*y ≤ X := by
    rw [←equal]
    exact mul_le_mul hq (Nat.floor_le (Real.rpow_nonneg xp.le _)) (Nat.cast_nonneg _) (Real.rpow_nonneg xp.le _)
  have y2 : 2 ≤ y := hlog.1
  have yp : (0:ℝ)<y := Nat.cast_pos.mpr (by omega)
  refine ⟨Nat.le_floor hy,by exact_mod_cast upper,?_⟩
  have pow : (X:ℝ) ≤ (y:ℝ)^j := by
    apply (Real.log_le_log_iff xp (pow_pos yp _)).mp
    rw [Real.log_pow]
    have low := mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg (α := ℝ) j)
    have paid := mul_le_mul_of_nonneg_right enough (Real.log_nonneg x1)
    linarith only [low,paid]
  exact_mod_cast pow

private theorem weighted_freezing_error {θ : ℝ} (hθ : 0<θ) (small : θ<1) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop,|Real.log X*siftedPrefix (powerCutoff θ) X-
      Real.log X*coprimeMoebiusSum (primorial (powerCutoff θ X)) X| ≤ ε*X := by
  obtain ⟨D,hD,errors⟩ := second_log_saving_for_freezing_a_polynomial_cutoff hθ small
  have large := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (D/ε)
  filter_upwards [errors,large,eventually_ge_atTop (2:ℕ)] with X err hi pos
  have lx := Real.log_pos (show (1:ℝ)<X by exact_mod_cast (by omega : 1<X))
  have limit := (div_le_iff₀ hε).mp hi
  have gap := mul_le_mul_of_nonneg_right (signed_freezing_error hθ X) (sq_nonneg (Real.log X))
  rw [←mul_sub,abs_mul,abs_of_nonneg lx.le]
  apply le_of_mul_le_mul_right _ lx
  linarith only [gap,err,mul_le_mul_of_nonneg_right limit (Nat.cast_nonneg (α := ℝ) X)]

private theorem frozen_points_pass_their_own_cutoff {θ : ℝ} (hθ : 0<θ) {k X : ℕ} (hk : k ≤ X) :
    RoughReading.freeSet (powerCutoff θ X) k ⊆ ownPowerRough θ k := by
  intro n hn
  obtain ⟨hi,free⟩ := mem_filter.mp hn
  apply mem_filter.mpr
  refine ⟨by simpa only [Nat.floor_natCast] using hi,?_⟩
  intro p hp
  have bound : powerCutoff θ n ≤ powerCutoff θ X := Nat.floor_le_floor
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr ((mem_Icc.mp hi).2.trans hk)) hθ.le)
  exact bound.trans_lt (lt_of_not_ge (show ¬p ≤ powerCutoff θ X from free.2 p hp))

/-- Under a polynomial cutoff, both changing the logarithmic weight and
rounding each rough cofactor floor cost at most X/log X. -/
private theorem variation_and_rounding_at_power_cutoff {θ : ℝ} (hθ : 0<θ) (small : θ<1) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,let y := powerCutoff θ X
      (logVariation y X+2*y*(RoughReading.freeSet y (X/y)).card)*Real.log X ≤ C*X := by
  obtain ⟨A,hA,upper⟩ := upper_count_on_one_polynomial_rough_set hθ
  obtain ⟨N,fromN⟩ := eventually_atTop.mp upper
  have d := sub_pos.mpr small
  let C := (2*A+1)+2*(A/(1-θ))
  have cp : 0<C := by dsimp only [C]; positivity
  refine ⟨C,cp,?_⟩
  have cast : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have grow := (tendsto_rpow_atTop d).comp cast
  have root := Real.tendsto_sqrt_atTop.comp cast
  have prices := eventually_const_mul_one_add_log_pow_le_rpow (by norm_num : (0:ℝ)<1/2) zero_lt_one 2
  filter_upwards [root.eventually_ge_atTop N,grow.eventually_ge_atTop N,cast prices,
    cast (logarithmic_bounds_on_a_power_cutoff hθ),eventually_ge_atTop (2:ℕ)] with X rn qn fee two pos
  let y := powerCutoff θ X
  let L := Real.log (X:ℝ)
  let H := Real.sqrt X
  let δ := 2*A/L
  have x0 : (0:ℝ)<X := Nat.cast_pos.mpr (by omega)
  have x1 : (1:ℝ) ≤ X := by exact_mod_cast (by omega : 1 ≤ X)
  have lx : 0<L := Real.log_pos (by exact_mod_cast (by omega : 1<X))
  have h0 : 0<H := Real.sqrt_pos.mpr x0
  have δp : 0<δ := by dsimp only [δ]; positivity
  have yc : 2 ≤ y := two.1
  have yp : (0:ℝ)<y := Nat.cast_pos.mpr (by omega)
  have count (k : ℕ) (hk : k ≤ X) : ((RoughReading.freeSet y k).card:ℝ) ≤ δ*k+H := by
    by_cases early : (k:ℝ) ≤ H
    · have pop := card_le_card (filter_subset (RHTower.CoprimeMobius.IsFree (RoughReading.banned y)) (Icc 1 k))
      rw [Nat.card_Icc,Nat.add_sub_cancel] at pop
      exact ((Nat.cast_le.mpr pop).trans early).trans (le_add_of_nonneg_left (mul_nonneg δp.le (Nat.cast_nonneg _)))
    · have kh : H<(k:ℝ) := lt_of_not_ge early
      have logk := Real.log_le_log h0 kh.le
      rw [Real.log_sqrt x0.le] at logk
      let R := ((RoughReading.freeSet y k).card:ℝ)
      have obs := (Nat.cast_le (α := ℝ)).mpr (card_le_card (frozen_points_pass_their_own_cutoff hθ hk))
      have paid := (mul_le_mul_of_nonneg_right obs (show 0 ≤ Real.log k by
        linarith only [logk,lx] )).trans (fromN k (rn.trans kh.le))
      have half := mul_le_mul_of_nonneg_left logk (show 0 ≤ R by dsimp only [R]; positivity)
      apply LE.le.trans _ (le_add_of_nonneg_right h0.le)
      change R ≤ (2*A/L)*k
      rw [div_mul_eq_mul_div,le_div_iff₀ lx]
      linarith only [half,paid]
  have v := rough_log_variation_from_prefix_counts y X δp count
  have vf : logVariation y X*L ≤ (2*A+1)*X := by
    have l2 : L^2 ≤ H := by
      rw [Real.sqrt_eq_rpow]
      exact (pow_le_pow_left₀ lx.le (by linarith : L ≤ 1+L) 2).trans (by simpa only [one_mul] using fee)
    have p := (mul_le_mul_of_nonneg_left l2 h0.le).trans_eq (Real.mul_self_sqrt x0.le)
    have eq : δ*(X:ℝ)*L=2*A*X := by dsimp only [δ]; field_simp
    linarith only [mul_le_mul_of_nonneg_right v lx.le,p,eq]
  let u := (X:ℝ)/y
  have xpow := Nat.floor_le (Real.rpow_nonneg x0.le θ)
  have uq : (X:ℝ)^(1-θ) ≤ u := by
    apply (le_div_iff₀ yp).mpr
    apply (mul_le_mul_of_nonneg_left xpow (Real.rpow_nonneg x0.le (1-θ))).trans_eq
    rw [←Real.rpow_add x0,sub_add_cancel,Real.rpow_one]
  have ru := fromN u (qn.trans uq)
  have floor : ⌊u⌋₊=X/y := by dsimp only [u]; rw [Nat.floor_div_natCast,Nat.floor_natCast]
  have same : ownPowerRough θ u=ownPowerRough θ (X/y:ℕ) := by simp only [ownPowerRough,floor,Nat.floor_natCast]
  rw [same] at ru
  have incl := (Nat.cast_le (α := ℝ)).mpr (card_le_card (frozen_points_pass_their_own_cutoff hθ (Nat.div_le_self X y)))
  let R := ((RoughReading.freeSet y (X/y)).card:ℝ)
  have logu := Real.log_le_log (Real.rpow_pos_of_pos x0 (1-θ)) uq
  rw [Real.log_rpow x0] at logu
  have budget := (mul_le_mul_of_nonneg_right incl ((mul_nonneg d.le lx.le).trans logu)).trans ru
  have paid := (mul_le_mul_of_nonneg_left logu (show 0 ≤ R by dsimp only [R]; positivity)).trans budget
  have eq : u*y=X := div_mul_cancel₀ _ yp.ne'
  have round : ((y:ℝ)*R)*L ≤ (A/(1-θ))*X := by
    rw [div_mul_eq_mul_div,le_div_iff₀ d]
    linarith only [mul_le_mul_of_nonneg_right paid yp.le,congrArg (A*·) eq]
  dsimp only [C]
  change (logVariation y X+2*(y:ℝ)*R)*L ≤ _
  linarith only [vf,round]

/-- On the fixed set with a polynomial least-prime threshold the
ordinary signed prefix has an explicit main term and an error of
order X/log² X, uniformly at every sufficiently large endpoint. -/
theorem second_log_error_in_the_signed_smooth_main_term {θ : ℝ} (hθ : 0<θ) (small : θ<1) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,let y := powerCutoff θ X
      |Real.log X*siftedPrefix (powerCutoff θ) X+(y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card| *
        Real.log X ≤ K*X := by
  obtain ⟨A,hA,vr⟩ := variation_and_rounding_at_power_cutoff hθ small
  obtain ⟨C,hC,Y,Y4,pr⟩ := prime_error_over_rough_cofactors
  obtain ⟨D,hD,freeze⟩ := second_log_saving_for_freezing_a_polynomial_cutoff hθ small
  obtain ⟨_,fit⟩ := powers_fit hθ small
  let K := A+12*C/θ+D
  have kp : 0<K := by dsimp only [K]; positivity
  refine ⟨K,kp,?_⟩
  have logs := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [vr,freeze,fit Y,tendsto_natCast_atTop_atTop (logarithmic_bounds_on_a_power_cutoff hθ),
    logs.eventually_ge_atTop (4*(1+Real.log 2)/θ),eventually_ge_atTop (2:ℕ)] with X var fr wall scale hi pos
  let y := powerCutoff θ X
  let L := Real.log (X:ℝ)
  have lx : 0<L := Real.log_pos (by exact_mod_cast (by omega : 1<X))
  have yp : 0<y := (show 0<Y by omega).trans_le wall.1
  have yX : y ≤ X := (Nat.le_mul_of_pos_left y (by omega : 0<Y)).trans wall.2.1
  have ypR : (0:ℝ)<y := Nat.cast_pos.mpr yp
  have t := (div_le_iff₀ hθ).mp hi
  have two := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have ly : 1 ≤ Real.log y := by linarith only [scale.2,t,two]
  have lower : θ*L/4 ≤ Real.log ((y:ℝ)/2) := by
    rw [Real.log_div ypR.ne' (by norm_num)]
    linarith only [scale.2,t,two]
  have lhalf := lt_of_lt_of_le (div_pos (mul_pos hθ lx) (by norm_num)) lower
  have sq : Real.log ((y:ℝ)/2) ≤ Real.log y^2 := by
    rw [Real.log_div ypR.ne' (by norm_num)]
    nlinarith only [ly,two,sq_nonneg (Real.log y-1)]
  have rate : (2/Real.log ((y:ℝ)/2)+1/Real.log y^2)*L ≤ 12/θ := by
    have weak := div_le_div_of_nonneg_left zero_le_one lhalf sq
    apply (mul_le_mul_of_nonneg_right (add_le_add_left weak _) lx.le).trans
    rw [←add_div,div_mul_eq_mul_div,div_le_div_iff₀ lhalf hθ]
    linarith only [lower]
  let E := ∑ m ∈ RoughReading.freeSet y (X/y),
    |roughPrimePowerReading y (X/m)-((X:ℝ)/m-y)|
  have e := mul_le_mul_of_nonneg_right (pr y X wall.1 yX) lx.le
  have primeCost : E*L ≤ (12*C/θ)*X := by
    have h := mul_le_mul_of_nonneg_left rate (mul_nonneg hC.le (Nat.cast_nonneg (α := ℝ) X))
    calc _ ≤ (C*X)*((2/Real.log ((y:ℝ)/2)+1/Real.log y^2)*L) := e.trans_eq (by ring)
         _ ≤ _ := h
         _ = _ := by ring
  let M := coprimeMoebiusSum (primorial y) X
  let S := (y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card
  have b := smooth_main_term_error_at_every_rough_cutoff yp X
  have rowEq : M=∑ n ∈ Icc 1 X,RoughReading.row y n :=
    sum_congr rfl (fun n hn => primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1)
  rw [←rowEq] at b
  change |L*M+S| ≤ logVariation y X+E+2*y*(RoughReading.freeSet y (X/y)).card at b
  have full := mul_le_mul_of_nonneg_right b lx.le
  have err := (mul_le_mul_of_nonneg_right (signed_freezing_error hθ X) (sq_nonneg L)).trans fr
  let F := siftedPrefix (powerCutoff θ) X
  have tri := abs_add_le (L*(F-M)) (L*M+S)
  rw [show L*(F-M)+(L*M+S)=L*F+S by ring,abs_mul,abs_of_nonneg lx.le] at tri
  change |L*F+S| *L ≤ K*X
  dsimp only [K]
  linarith only [mul_le_mul_of_nonneg_right tri lx.le,err,full,var,primeCost]

/-- The ordinary sharp signed prefix of one fixed polynomially rough
set tracks the negative smooth population at the quotient wall. -/
theorem signed_smooth_main_term_on_one_polynomial_rough_set {θ : ℝ} (hθ : 0<θ) (small : θ<1)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop,let y := powerCutoff θ X
      |Real.log X*siftedPrefix (powerCutoff θ) X+(y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card| ≤ ε*X := by
  obtain ⟨Z,_,boundary⟩ := signed_rough_prefix_tracks_smooth_population (half_pos hε)
  obtain ⟨_,walls⟩ := powers_fit hθ small
  filter_upwards [walls Z,weighted_freezing_error hθ small (half_pos hε)] with X hx error
  have paid := boundary _ X hx.1 hx.2.1
  let A := Real.log X*siftedPrefix (powerCutoff θ) X
  let B := Real.log X*coprimeMoebiusSum (primorial (powerCutoff θ X)) X
  let y := powerCutoff θ X
  let P := (y:ℝ)*(smoothUpTo (Nat.primesLE y) (X/y)).card
  change |A+P| ≤ _
  have tri := abs_add_le (A-B) (B+P)
  rw [show A-B+(B+P)=A+P by ring] at tri
  linarith only [tri,error,paid]

/-- The negative excess on this single arithmetic set is at least
c X/log X at every sufficiently large observation. -/
theorem negative_charge_on_one_polynomial_rough_set {θ : ℝ} (hθ : 0<θ) (small : θ<1) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ X : ℕ in atTop,
      Real.log X*siftedPrefix (powerCutoff θ) X ≤ -(c*X) := by
  obtain ⟨j,fit⟩ := powers_fit hθ small
  obtain ⟨c,hc,Z,_,negative⟩ := negative_charge_of_every_polynomial_rough_cutoff j
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [fit Z,weighted_freezing_error hθ small (half_pos hc)] with X hx gap
  have bound := negative _ X hx.1 hx.2.1 hx.2.2
  linarith only [bound,(abs_le.mp gap).2]

#print axioms second_log_error_in_the_signed_smooth_main_term
#print axioms signed_smooth_main_term_on_one_polynomial_rough_set
#print axioms negative_charge_on_one_polynomial_rough_set

end GaloisForLFunctions.RestrictedFactorizationCalculus
