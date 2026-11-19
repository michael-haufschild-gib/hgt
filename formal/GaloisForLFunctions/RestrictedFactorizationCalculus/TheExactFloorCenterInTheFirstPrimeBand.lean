import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothPopulationAtAnInteriorQuotientCut
import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeErrorInTheCenteredUnitWindow

/-!
# The original floor center through the first prime band

The ordinary-prime and exact-floor readings carry the same macroscopic
profile at every interior quotient wall with y ≤ Z ≤ y². Their
difference is uniformly sublinear, including at polynomial sieve walls.
-/
noncomputable section
open Finset Filter ArithmeticFunction
open scoped Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The two residue errors are both in [0,y). Their difference costs
only one copy of the wall at every retained cofactor. -/
private theorem floor_window_error {y : ℕ} (pos : 0<y) (k t : ℕ) :
    |((t:ℝ)-k)-(quotientFloorCenter y t-quotientFloorCenter y k)| ≤ y := by
  have e (n : ℕ) : quotientFloorCenter y n+((n%y:ℕ):ℝ)=n := by
    unfold quotientFloorCenter
    exact_mod_cast Nat.div_add_mod n y
  have h1 : ((t%y:ℕ):ℝ) ≤ y := Nat.cast_le.mpr (Nat.mod_lt _ pos).le
  have h2 : ((k%y:ℕ):ℝ) ≤ y := Nat.cast_le.mpr (Nat.mod_lt _ pos).le
  apply abs_le.mpr
  constructor <;> linarith only [e t,e k,h1,h2,Nat.cast_nonneg (α := ℝ) (t%y),Nat.cast_nonneg (α := ℝ) (k%y)]

/-- Subtracting the original quotient floor makes the entire upper
reading o(X), uniformly for y ≤ Z ≤ y² and yZ ≤ X. Each proper prime
power can be independently assigned any signed admissible weight. -/
theorem centered_first_prime_band_for_every_cofactor_selection {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → Z ≤ y^2 → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      ∀ v : ℕ → ℝ,(∀ m,|v m| ≤ 1) →
      |∑ m ∈ Icc 1 Z,RoughReading.row y m*
        (v m*∑ q ∈ Ioc (X/Z) (X/m),(a-exactQuotientFloorWeight y) q)| ≤ ε*X := by
  let η := ε/5
  have hp : 0<η := div_pos ep (by norm_num)
  obtain ⟨N,_,window⟩ := ordinary_prime_interval_price hp
  filter_upwards [reciprocal_mass_above_the_prime_wall (ε := 1) zero_lt_one,density_of_the_first_prime_band hp,
    eventually_ge_atTop N,eventually_ge_atTop (2:ℕ)] with y reciprocal count large yp
  intro Z X yz zz room a dom same v cap
  let K := X/Z
  let P := RHTower.Sieve.bigPrimeSet y Z
  let w := fun m : ℕ => ∑ q ∈ Ioc K (X/m),(a-exactQuotientFloorWeight y) q
  have pos : 0<y := by omega
  have zp := pos.trans_le yz
  have yk : y ≤ K := (Nat.le_div_iff_mul_le zp).mpr room
  have per (m : ℕ) (mp : 0< m) (mz : m ≤ Z) : |w m| ≤ η*((X:ℝ)/m)+y := by
    let t := X/m
    have kt : K ≤ t := (Nat.le_div_iff_mul_le mp).mpr
      ((Nat.mul_le_mul_left K mz).trans (Nat.div_mul_le_self X Z))
    have err := window y K yk (large.trans yk) a dom same (t:ℝ) (Nat.cast_le.mpr kt)
    rw [Nat.floor_natCast] at err
    have price := floor_window_error pos K t
    have tp : (t:ℝ) ≤ (X:ℝ)/m := (le_div_iff₀ (Nat.cast_pos.mpr mp)).mpr (by exact_mod_cast Nat.div_mul_le_self X m)
    change |∑ q ∈ Ioc K t,(a-exactQuotientFloorWeight y) q| ≤ _
    simp only [ArithmeticFunction.sub_apply,sum_sub_distrib,exact_floor_weight_in_an_interval y kt]
    have tri := abs_sub_le (∑ q ∈ Ioc K t,a q) ((t:ℝ)-K) (quotientFloorCenter y t-quotientFloorCenter y K)
    exact tri.trans (add_le_add (err.trans (mul_le_mul_of_nonneg_left tp hp.le)) price)
  have charged (m : ℕ) (mp : 0< m) (mz : m ≤ Z) : |v m*w m| ≤ η*((X:ℝ)/m)+y := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (cap m) (abs_nonneg _)).trans ((one_mul _).le.trans (per m mp mz))
  have one : |v 1*w 1| ≤ η*X+y := by simpa only [Nat.cast_one,div_one] using charged 1 (by decide) zp
  have each (p : ℕ) (h : p ∈ P) := charged p (mem_filter.mp h).2.pos (mem_Icc.mp (mem_filter.mp h).1).2
  have tail := (abs_sum_le_sum_abs (fun p => v p*w p) P).trans (sum_le_sum each)
  rw [sum_add_distrib,sum_const,nsmul_eq_mul] at tail
  have factor : (∑ p ∈ P,η*((X:ℝ)/p))=η*X*∑ p ∈ P,1/(p:ℝ) := by
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ => by ring)
  rw [factor] at tail
  change |∑ m ∈ Icc 1 Z,RoughReading.row y m*(v m*w m)| ≤ _
  rw [rough_row_through_the_first_prime_band zp zz (fun m => v m*w m)]
  have z := (div_le_iff₀ (Nat.cast_pos.mpr zp)).mp (count Z yz)
  have price := (mul_le_mul_of_nonneg_right z (Nat.cast_nonneg (α := ℝ) y)).trans_eq
    (by ring : η*(Z:ℝ)*y=η*((y:ℝ)*Z))
  have room' : (y:ℝ)*Z ≤ X := by exact_mod_cast room
  have rounding := price.trans (mul_le_mul_of_nonneg_left room' hp.le)
  have yl := Real.log_pos (show (1:ℝ)<y by exact_mod_cast (show 1<y by omega))
  have zl := Real.log_pos (show (1:ℝ)<Z by exact_mod_cast (show 1<Z by omega))
  have maxlog := Real.log_le_log (Nat.cast_pos.mpr zp) (Nat.cast_le.mpr zz)
  rw [Nat.cast_pow,Real.log_pow] at maxlog
  have ratio : Real.log Z/Real.log y ≤ 2 := (div_le_iff₀ yl).mpr (by simpa using maxlog)
  have logbound := (Real.log_le_log (div_pos zl yl) ratio).trans (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2))
  have sumcap : (∑ p ∈ P,1/(p:ℝ)) ≤ 2 := by linarith only [(abs_le.mp (reciprocal Z yz)).2,logbound]
  have hmass := mul_le_mul_of_nonneg_left sumcap (mul_nonneg hp.le (Nat.cast_nonneg X))
  have tri := abs_sub (v 1*w 1) (∑ p ∈ P,v p*w p)
  dsimp only [η] at *
  linarith only [tri,one,tail,rounding,hmass,mul_nonneg ep.le (Nat.cast_nonneg (α := ℝ) X)]

/-- The original centered prime reading vanishes after normalization by X
uniformly throughout the first rough prime band. -/
theorem original_floor_cancels_the_first_prime_band {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → Z ≤ y^2 → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      |upperQuotientReading (a-exactQuotientFloorWeight y) y X Z| ≤ ε*X := by
  filter_upwards [centered_first_prime_band_for_every_cofactor_selection ep,eventually_ge_atTop (1:ℕ)] with y price yp
  intro Z X yz zz room a dom same
  rw [transpose_the_upper_quotient_cells _ _ _ (yp.trans yz)]
  simpa only [one_mul] using price Z X yz zz room a dom same (fun _ => 1) (fun _ => by norm_num)

#print axioms centered_first_prime_band_for_every_cofactor_selection
#print axioms original_floor_cancels_the_first_prime_band
end GaloisForLFunctions.RestrictedFactorizationCalculus
