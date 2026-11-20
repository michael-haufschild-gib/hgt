import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTotalVariationOfTheFirstRoughPrimeBand
import GaloisForLFunctions.RestrictedFactorizationCalculus.BothSignsBelowTheRoughCofactorCutoff

/-!
# Absolute cost of the transposed rough prime-power interior

The log-square sieve wall grows more slowly than every positive power.
Each fixed polynomial cofactor band therefore survives removal of a
power-sized head. Its total variation approaches two minus its smooth
proportion. Letting the polynomial degree grow gives an absolute cost
of at least (2−o(1))X for the literal Mangoldt row.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Topology Classical
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Sum of the magnitudes of the transposed prime-power increments. -/
def absoluteRoughInterior (y X T : ℕ) :=
  ∑ q∈Icc 1 X,|roughMangoldtWeight y q*interiorKernel y X T q|

private theorem visible_band (y X T Z : ℕ) (hT : T ≤ X/Z) :
    primeBandVariation (roughMangoldtWeight y) y X Z ≤ absoluteRoughInterior y X T := by
  calc _ = ∑ q∈Ioc (X/Z) X,|roughMangoldtWeight y q*interiorKernel y X T q| := by
         apply sum_congr rfl
         intro q hq
         have hh := (min_le_right X T).trans_lt (hT.trans_lt (mem_Ioc.mp hq).1)
         have hz : coprimeMoebiusSum (primorial y) 0=0 := by simp [coprimeMoebiusSum]
         simp only [interiorKernel,Nat.div_eq_of_lt hh,hz,sub_zero]
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun q hq =>
         mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hq).1,(mem_Ioc.mp hq).2⟩)
           (fun q _ _ => abs_nonneg _)

private theorem eventually_small_smooth_proportion {δ : ℝ} (hδ : 0 < δ) :
    ∃ j : ℕ,0 < j ∧ ∀ᶠ y : ℕ in atTop,
      ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) (y^j)).card:ℝ)/((y^j:ℕ):ℝ) ≤ δ := by
  obtain ⟨C,_,hC⟩ := uniform_logarithmic_upper_bound_for_smooth_population
  obtain ⟨j,hj⟩ := exists_nat_gt (2/δ)
  have jpos : 0 < j := by exact_mod_cast ((div_pos (by norm_num) hδ).trans hj)
  refine ⟨j,jpos,?_⟩
  filter_upwards [eventually_ge_atTop 2,(Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop)).eventually_ge_atTop C]
    with y hy hlog
  have hl : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let S := (RHTower.Sieve.smoothUpTo (Nat.primesLE y) (y^j)).card
  have h := hC y (y^j) (by omega)
  rw [Nat.cast_pow,Real.log_pow] at h
  have hb := mul_le_mul_of_nonneg_left (show Real.log y+C ≤ 2*Real.log y by change C ≤ Real.log (y:ℝ) at hlog; linarith only [hlog])
    (pow_nonneg (Nat.cast_nonneg (α:=ℝ) y) j)
  have hmul : ((S:ℝ)*j)*Real.log y ≤ (2*(y:ℝ)^j)*Real.log y := by
    change (S:ℝ)*(j*Real.log y) ≤ _ at h
    nlinarith only [h,hb]
  have hs := (mul_le_mul_iff_left₀ hl).mp hmul
  have hratio := (div_lt_iff₀ hδ).mp hj
  have ypow : 0 < (y:ℝ)^j := pow_pos (Nat.cast_pos.mpr (by omega)) j
  rw [Nat.cast_pow,div_le_iff₀ ypow]
  change (S:ℝ) ≤ _
  have hjr : 0 < (j:ℝ) := Nat.cast_pos.mpr jpos
  apply (mul_le_mul_iff_left₀ hjr).mp
  calc (S:ℝ)*j ≤ 2*(y:ℝ)^j := hs
       _ ≤ (j*δ)*(y:ℝ)^j := mul_le_mul_of_nonneg_right hratio.le ypow.le
       _ = _ := by ring

private theorem room_for_every_fixed_band (j : ℕ) {α : ℝ} (ha : 0 ≤ α) (h1 : α < 1) :
    ∀ᶠ X : ℕ in atTop,let y := logSquareCutoff X
      y*(y^j) ≤ X ∧ ∀ T : ℕ,(T:ℝ) ≤ (X:ℝ)^α → T ≤ X/(y^j) := by
  let β := (1-α)/((j:ℝ)+1)
  have hβ : 0 < β := div_pos (sub_pos.mpr h1) (by positivity)
  filter_upwards [cutoff_below_power hβ,logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with X hw hy hX
  let y := logSquareCutoff X
  have hx : 0 < (X:ℝ) := Nat.cast_pos.mpr hX
  have hx1 : (1:ℝ) ≤ X := Nat.one_le_cast.mpr hX
  change 2*(y:ℝ) ≤ (X:ℝ)^β at hw
  have hw' : (y:ℝ) ≤ (X:ℝ)^β := by linarith only [hw,Nat.cast_nonneg (α:=ℝ) y]
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) y) hw' (j+1)
  have hcollapse : ((X:ℝ)^β)^(j+1)=(X:ℝ)^(β*((j+1:ℕ):ℝ)) := by
    rw [Real.rpow_mul hx.le,Real.rpow_natCast]
  have hparam : β*((j+1:ℕ):ℝ)=1-α := by
    dsimp only [β];rw [Nat.cast_succ,div_mul_cancel₀ _ (by positivity)]
  rw [hcollapse,hparam] at hpow
  have hlow : (y:ℝ)^j ≤ (y:ℝ)^(j+1) := by
    apply pow_le_pow_right₀ (by exact_mod_cast hy)
    omega
  have hupper : (X:ℝ)^(1-α) ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 (show 1-α ≤ 1 by linarith)
  refine ⟨?_,fun T hT => ?_⟩
  · have hnat : y^(j+1) ≤ X := by exact_mod_cast hpow.trans hupper
    simpa only [pow_succ,mul_comm] using hnat
  · apply (Nat.le_div_iff_mul_le (pow_pos hy j)).mpr
    have hprod := mul_le_mul hT (hlow.trans hpow) (pow_nonneg (Nat.cast_nonneg _) j) (Real.rpow_nonneg hx.le _)
    rw [←Real.rpow_add hx,show α+(1-α)=1 by ring,Real.rpow_one] at hprod
    exact_mod_cast hprod

/-- Every power-sized head below exponent one leaves at least (2−ε)X
of absolute increment mass for the actual rough Mangoldt input. -/
theorem absolute_price_after_sublinear_prime_head {α ε : ℝ} (ha : 0 ≤ α) (h1 : α < 1) (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,∀ T : ℕ,(T:ℝ) ≤ (X:ℝ)^α →
      (2-ε)*(X:ℝ) ≤ absoluteRoughInterior (logSquareCutoff X) X T := by
  obtain ⟨j,hj,hs⟩ := eventually_small_smooth_proportion (half_pos hε)
  filter_upwards [room_for_every_fixed_band j ha h1,logSquareCutoff_tendsto_atTop hs,
    logSquareCutoff_tendsto_atTop (total_variation_and_smooth_proportion j (half_pos hε)),
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop 1] with X room hsmall hvar hy hx
  intro T hT
  let y := logSquareCutoff X
  have hnon (q : ℕ) : 0 ≤ roughMangoldtWeight y q := by
    rw [roughMangoldtWeight,roughRestriction_apply];split <;> simp [vonMangoldt_nonneg]
  have hv := hvar (y^j) X (Nat.le_self_pow hj.ne' y) le_rfl room.1
    (roughMangoldtWeight y) hnon (mangoldt_dominated y) (fun _ _ => rfl)
  have hp := visible_band y X T (y^j) (room.2 T hT)
  apply le_trans _ hp
  apply (le_div_iff₀ (Nat.cast_pos.mpr hx : 0 < (X:ℝ))).mp
  let d := ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) (y^j)).card:ℝ)/((y^j:ℕ):ℝ)
  let v := primeBandVariation (roughMangoldtWeight y) y X (y^j)/(X:ℝ)
  change d ≤ ε/2 at hsmall
  change |v-(2-d)| ≤ ε/2 at hv
  change 2-ε ≤ v
  linarith only [(abs_le.mp hv).1,hsmall]

/-- The four-sevenths interior retains this linear absolute cost at
every sufficiently large cutoff. -/
theorem absolute_price_at_four_sevenths {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop,(2-ε)*(X:ℝ) ≤
      absoluteRoughInterior (logSquareCutoff X) X ⌊(X:ℝ)^(4/7:ℝ)⌋₊ := by
  filter_upwards [absolute_price_after_sublinear_prime_head (by norm_num : (0:ℝ) ≤ 4/7)
    (by norm_num : (4/7:ℝ) < 1) hε] with X h
  exact h _ (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end GaloisForLFunctions.RestrictedFactorizationCalculus
