import GaloisForLFunctions.RestrictedFactorizationCalculus.IndependentPrimeWindowsOnRoughCofactors
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothPopulationAtAnInteriorQuotientCut
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothPopulationInASignedRoughPrefix
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# The smooth proportion at every interior quotient cut

Both endpoints of every retained prime interval lie above the sieve.
Prime errors and floor residues have uniformly sublinear total absolute
price on rough cofactors. Divisor inversion identifies the common raw
profile as the positive smooth fraction at the cofactor cutoff.
-/
noncomputable section
open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem density_of_rough_cofactors {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,y ≤ Z → ((RoughReading.freeSet y Z).card:ℝ) ≤ ε*Z := by
  obtain ⟨Y,K,_,count⟩ := uniform_rough_count_at_large_walls (half_pos ep)
  filter_upwards [eventually_ge_atTop Y,tendsto_natCast_atTop_atTop.eventually_ge_atTop (K/(ε/2))] with y late size
  intro Z order
  have room := (div_le_iff₀ (half_pos ep)).mp (size.trans (Nat.cast_le.mpr order))
  linarith only [count y late Z,room]

/-- Relative to X, even the sum of absolute errors tends to zero
uniformly over all independently chosen sharp rough-cofactor windows. -/
theorem vanishing_absolute_price_of_all_rough_prime_subwindows {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → y*Z ≤ X →
      ∀ S : Finset ℕ,S ⊆ RoughReading.freeSet y Z → ∀ l u : ℕ → ℕ,
      (∀ m ∈ S,y ≤ l m ∧ l m ≤ u m ∧ u m ≤ X/m) →
      ∀ a : ℕ → ArithmeticFunction ℝ,
      (∀ m ∈ S,∀ q ∈ Ioc (l m) (u m),|a m q| ≤ vonMangoldt q) →
      (∀ m ∈ S,∀ q ∈ Ioc (l m) (u m),q.Prime → a m q=roughOrdinaryPrimeWeight y q) →
      (∑ m ∈ S,|centeredPrimeInterval (a m) y (l m) (u m)|) ≤ ε*X := by
  let θ := RHTower.zetaZeroAbscissa
  let s := (θ+1)/2
  have strip : θ<1 := ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths.trans_lt (by norm_num)
  have hs : θ<s := by dsimp only [s]; linarith only [strip]
  have d : 0<1-s := by dsimp only [s]; linarith only [strip]
  obtain ⟨C,_,price⟩ := absolute_price_of_independent_quotient_subwindows hs (by linarith only [d])
  let h := ε/2
  have hp : 0<h := half_pos ep
  have grow : Tendsto (fun y : ℕ => (y:ℝ)^(1-s)) atTop atTop := (tendsto_rpow_atTop d).comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop (C/h),density_of_rough_cofactors hp,eventually_ge_atTop (1:ℕ)]
    with y late density yp
  intro Z X yz room S sub l u supported a dom fix
  have nsub : S ⊆ Icc 1 Z := sub.trans (filter_subset ..)
  have raw := price y X Z yp S nsub l u supported a dom fix
  have cap := (Nat.cast_le.mpr (card_le_card sub)).trans (density Z yz)
  have room' : (y:ℝ)*Z ≤ X := by exact_mod_cast room
  have xpos : 0<X := (Nat.mul_pos yp (yp.trans yz)).trans_le room
  have x0 : 0<(X:ℝ) := Nat.cast_pos.mpr xpos
  have crossing := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg y) (Nat.cast_nonneg Z)) room' d.le
  rw [Real.mul_rpow (Nat.cast_nonneg y) (Nat.cast_nonneg Z)] at crossing
  have scale : (X:ℝ)^s*((X:ℝ)^(1-s))=X := by rw [←Real.rpow_add x0,show s+(1-s)=1 by ring,Real.rpow_one]
  have base := ((mul_le_mul_of_nonneg_left crossing (Real.rpow_nonneg x0.le s)).trans_eq scale)
  have afford := (div_le_iff₀ hp).mp late
  have prime := mul_le_mul_of_nonneg_right afford (mul_nonneg (Real.rpow_nonneg x0.le s) (Real.rpow_nonneg (Nat.cast_nonneg Z) (1-s)))
  have floor := mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α := ℝ) y)
  dsimp only [h] at *
  linarith only [raw,prime,floor,mul_le_mul_of_nonneg_left base hp.le,mul_le_mul_of_nonneg_left room' hp.le]

private theorem rough_weight_at_most_one {y Z m : ℕ} (hm : m ∈ RoughReading.freeSet y Z) :
    |RoughReading.row y m| ≤ 1 := by
  rw [RoughReading.row_value,if_pos (mem_filter.mp hm).2]
  exact_mod_cast abs_moebius_le_one (n := m)

private theorem cutoff_floor_room (n : ℕ) {m : ℕ} (mp : 0< m) :
    ((n/m:ℕ):ℝ) ≤ (n:ℝ)/m ∧ (n:ℝ)/m ≤ ((n/m:ℕ):ℝ)+1 := by
  have pos : 0<(m:ℝ) := Nat.cast_pos.mpr mp
  have upper : n ≤ (n/m+1)*m := by
    calc n = m*(n/m)+n%m := (Nat.div_add_mod n m).symm
         _ ≤ (n/m+1)*m := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm m]; exact Nat.add_le_add_left (Nat.mod_lt _ mp).le _
  exact ⟨(le_div_iff₀ pos).mpr (by exact_mod_cast Nat.div_mul_le_self n m),
    (div_le_iff₀ pos).mpr (by exact_mod_cast upper)⟩

private theorem smooth_rounding_per_cofactor {y Z X m : ℕ} (yp : 0<y) (zp : 0<Z) (room : y*Z ≤ X)
    (mp : 0< m) (mz : m ≤ Z) :
    |(∑ q ∈ Ioc (X/Z) (X/m),exactQuotientFloorWeight y q)-(X:ℝ)/Z*(⌊(Z:ℝ)/m⌋:ℝ)| ≤ 3*((X:ℝ)/Z) := by
  let K := X/Z
  let t := X/m
  let z := (X:ℝ)/Z
  have zpos : 0<(Z:ℝ) := Nat.cast_pos.mpr zp
  have ysmall : (y:ℝ) ≤ z := (le_div_iff₀ zpos).mpr (by exact_mod_cast room)
  have z1 := (Nat.one_le_cast.mpr yp).trans ysmall
  have z0 := zero_le_one.trans z1
  have order : K ≤ t := (Nat.le_div_iff_mul_le mp).mpr
    ((Nat.mul_le_mul_left K mz).trans (Nat.div_mul_le_self X Z))
  have floor (n : ℕ) : 0 ≤ quotientFloorCenter y n ∧ quotientFloorCenter y n ≤ n ∧
      (n:ℝ) ≤ quotientFloorCenter y n+y := by
    have exactPrice : quotientFloorCenter y n+((n%y:ℕ):ℝ)=n := by unfold quotientFloorCenter; exact_mod_cast Nat.div_add_mod n y
    have residue := (Nat.cast_le (α := ℝ)).mpr (Nat.mod_lt n yp).le
    exact ⟨mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      by linarith only [exactPrice,Nat.cast_nonneg (α := ℝ) (n%y)],by linarith only [exactPrice,residue]⟩
  have base : z*((Z:ℝ)/m)=(X:ℝ)/m := by
    dsimp only [z]
    field_simp [zpos.ne', (Nat.cast_pos.mpr mp : (0:ℝ)< m).ne'] <;> ring
  have low := (mul_le_mul_of_nonneg_left (Int.floor_le ((Z:ℝ)/m)) z0).trans_eq base
  have high := mul_le_mul_of_nonneg_left (Int.lt_floor_add_one ((Z:ℝ)/m)).le z0
  rw [base] at high
  have small := cutoff_floor_room X mp
  have ksmall := (floor K).2.1.trans (cutoff_floor_room X zp).1
  rw [exact_floor_weight_in_an_interval y order]
  change |quotientFloorCenter y t-quotientFloorCenter y K-z*(⌊(Z:ℝ)/m⌋:ℝ)| ≤ 3*z
  change (t:ℝ) ≤ (X:ℝ)/m ∧ (X:ℝ)/m ≤ (t:ℝ)+1 at small
  apply abs_le.mpr
  constructor <;> linarith only [high,low,small.1,small.2,z1,ysmall,(floor K).1,ksmall,(floor t).2.1,(floor t).2.2]

/-- At every interior cut the original upper floor sector tracks the
positive smooth proportion, with at most three cutoff lengths per rough cofactor. -/
theorem exact_floor_profile_at_an_interior_cut {y Z X : ℕ} (yp : 0<y) (zp : 0<Z) (room : y*Z ≤ X) :
    |upperQuotientReading (exactQuotientFloorWeight y) y X Z-
      (X:ℝ)/Z*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card| ≤
      3*((X:ℝ)/Z)*(RoughReading.freeSet y Z).card := by
  rw [positive_smooth_center_at_an_interior_quotient_cut _ _ _ zp]
  have per (m : ℕ) (hm : m ∈ RoughReading.freeSet y Z) := smooth_rounding_per_cofactor yp zp room
    (mem_Icc.mp (mem_filter.mp hm).1).1 (mem_Icc.mp (mem_filter.mp hm).1).2
  apply (abs_sum_le_sum_abs ..).trans
  have bounds := sum_le_sum (fun m (hm : m ∈ RoughReading.freeSet y Z) =>
    (mul_le_mul_of_nonneg_right (rough_weight_at_most_one hm) (abs_nonneg _)).trans
      ((one_mul _).le.trans (per m hm)))
  simp only [abs_mul,sum_const,nsmul_eq_mul] at bounds ⊢
  exact bounds.trans_eq (mul_comm ..)

private theorem raw_price_from_centered_subwindows {y Z X : ℕ} (yp : 0<y) (zp : 0<Z)
    (room : y*Z ≤ X) (a : ArithmeticFunction ℝ) :
    |upperQuotientReading a y X Z-(X:ℝ)/Z*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card| ≤
      (∑ m ∈ RoughReading.freeSet y Z,|centeredPrimeInterval a y (X/Z) (X/m)|)+
      3*((X:ℝ)/Z)*(RoughReading.freeSet y Z).card := by
  let S := RoughReading.freeSet y Z
  let k := X/Z
  let F := exactQuotientFloorWeight y
  let center := (X:ℝ)/Z*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card
  have gap : upperQuotientReading a y X Z-center-(upperQuotientReading F y X Z-center)=
      ∑ m ∈ S,RoughReading.row y m*centeredPrimeInterval a y k (X/m) := by
    dsimp only [center]
    rw [positive_smooth_center_at_an_interior_quotient_cut a y X zp,
      positive_smooth_center_at_an_interior_quotient_cut F y X zp,←sum_sub_distrib]
    apply sum_congr rfl
    intro m _
    rw [←mul_sub,sub_sub_sub_cancel_right]
    change _*(_-_) = _*(∑ q ∈ Ioc k (X/m),(a q-F q))
    rw [sum_sub_distrib]
  have signed := abs_sum_le_sum_abs (fun m => RoughReading.row y m*centeredPrimeInterval a y k (X/m)) S
  have pay := sum_le_sum (fun m (hm : m ∈ S) => (mul_le_mul_of_nonneg_right (rough_weight_at_most_one hm)
    (abs_nonneg (centeredPrimeInterval a y k (X/m)))).trans_eq (one_mul _))
  simp only [abs_mul] at signed
  have charge := signed.trans pay
  rw [←gap] at charge
  have triangle := abs_add_le ((upperQuotientReading a y X Z-center)-(upperQuotientReading F y X Z-center)) (upperQuotientReading F y X Z-center)
  rw [sub_add_cancel] at triangle
  exact triangle.trans (add_le_add charge (exact_floor_profile_at_an_interior_cut yp zp room))

/-- The error consists of a power price for the prime endpoints and the
actual number of rough floor residues. The cofactor cutoff may be arbitrary. -/
theorem quantitative_smooth_profile_at_every_interior_cut {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s) (small : s<1) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ y Z X : ℕ,0<y → y ≤ Z → y*Z ≤ X →
      ∀ a : ArithmeticFunction ℝ,(∀ q,|a q| ≤ vonMangoldt q) →
      (∀ p,p.Prime → a p=roughOrdinaryPrimeWeight y p) →
      |upperQuotientReading a y X Z-(X:ℝ)/Z*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card| ≤
      C*(X:ℝ)^s*(Z:ℝ)^(1-s)+4*((X:ℝ)/Z)*(RoughReading.freeSet y Z).card := by
  obtain ⟨C,c0,cost⟩ := absolute_price_of_independent_quotient_subwindows strip small
  refine ⟨C,c0,fun y Z X yp yz room a dom fix => ?_⟩
  let S := RoughReading.freeSet y Z
  let k := X/Z
  have zp : 0<Z := (show 0<y from yp).trans_le yz
  have yk : y ≤ k := (Nat.le_div_iff_mul_le zp).mpr room
  have bounds (m : ℕ) (hm : m ∈ S) : y ≤ k ∧ k ≤ X/m ∧ X/m ≤ X/m := by
    obtain ⟨mp,mz⟩ := mem_Icc.mp (mem_filter.mp hm).1
    exact ⟨yk,(Nat.le_div_iff_mul_le mp).mpr ((Nat.mul_le_mul_left k mz).trans (Nat.div_mul_le_self X Z)),le_rfl⟩
  have prime := cost y X Z yp S (filter_subset ..) (fun _ => k) (fun m => X/m) bounds
    (fun _ => a) (fun _ _ q _ => dom q) (fun _ _ q _ => fix q)
  have cap : (y:ℝ) ≤ (X:ℝ)/Z := (le_div_iff₀ (Nat.cast_pos.mpr zp)).mpr (by exact_mod_cast room)
  have rounding := mul_le_mul_of_nonneg_right cap (Nat.cast_nonneg (α := ℝ) S.card)
  exact (raw_price_from_centered_subwindows yp zp room a).trans (by linarith only [prime,rounding])

/-- The full positive smooth proportion survives on the raw ordinary-prime
and edited prime-power readings. Both quotient endpoints may move throughout
the entire range y ≤ Z, yZ ≤ X. -/
theorem raw_prime_profile_at_every_interior_cut {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughOrdinaryPrimeWeight y p) →
      |upperQuotientReading a y X Z-(X:ℝ)/Z*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card| ≤ ε*X := by
  filter_upwards [vanishing_absolute_price_of_all_rough_prime_subwindows (half_pos ep),
    density_of_rough_cofactors (div_pos ep (by norm_num : (0:ℝ)<6)),eventually_ge_atTop (1:ℕ)] with y sublinear count yp
  intro Z X yz room a dom fix
  let S := RoughReading.freeSet y Z
  let k := X/Z
  have zp : 0<Z := (show 0<y from yp).trans_le yz
  have yk : y ≤ k := (Nat.le_div_iff_mul_le zp).mpr room
  have admissible (m : ℕ) (hm : m ∈ S) : y ≤ k ∧ k ≤ X/m ∧ X/m ≤ X/m := by
    obtain ⟨mp,mz⟩ := mem_Icc.mp (mem_filter.mp hm).1
    exact ⟨yk,(Nat.le_div_iff_mul_le mp).mpr ((Nat.mul_le_mul_left k mz).trans (Nat.div_mul_le_self X Z)),le_rfl⟩
  have price := sublinear Z X yz room S (fun _ h => h) (fun _ => k) (fun m => X/m) admissible
    (fun _ => a) (fun _ _ q _ => dom q) (fun _ _ q _ => fix q)
  have positive : 0<(Z:ℝ) := Nat.cast_pos.mpr zp
  have room' := mul_le_mul_of_nonneg_left (count Z yz) (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (div_nonneg (Nat.cast_nonneg X) positive.le))
  have unify : 3*((X:ℝ)/Z)*(ε/6*Z)=ε/2*X := by field_simp [positive.ne']; ring
  have fit := room'.trans_eq unify
  exact (raw_price_from_centered_subwindows yp zp room a).trans (by linarith only [fit,price])

end GaloisForLFunctions.RestrictedFactorizationCalculus
