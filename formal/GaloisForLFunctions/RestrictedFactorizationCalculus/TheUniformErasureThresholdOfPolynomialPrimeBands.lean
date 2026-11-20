import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothDensityReadByTheRelativeSignRadius

/-!
# Loss of a common erasure threshold as the cofactor degree grows

A fixed polynomial cofactor range admits a positive relative erasure
radius. No positive radius survives all polynomial degrees, even for
unmodified Mangoldt increments. The order of these two quantifiers
therefore matters.
-/
noncomputable section
open Filter Finset ArithmeticFunction
open scoped Topology Classical
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev density (y Z : ℕ) : ℝ :=
  ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card:ℝ)/(Z:ℝ)

private theorem positive_density (j : ℕ) :
    ∃ c : ℝ,0 < c ∧ ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,y ≤ Z → Z ≤ y^j → c ≤ density y Z := by
  obtain ⟨c,hc,A,_,neg⟩ := negative_charge_of_every_polynomial_rough_cutoff (j+1)
  obtain ⟨B,_,Bbound⟩ := signed_rough_prefix_tracks_smooth_population (half_pos hc)
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [eventually_ge_atTop A,eventually_ge_atTop B,eventually_ge_atTop (1:ℕ)] with y ay by' yp
  intro Z yz limit
  have zp := yp.trans yz
  have room : Z*y ≤ y^(j+1) := by rw [pow_succ];exact Nat.mul_le_mul_right y limit
  have hn := neg y (Z*y) ay (Nat.mul_le_mul_right y (ay.trans yz)) room
  have hs := (abs_le.mp (Bbound y (Z*y) by' (Nat.mul_le_mul_right y (by'.trans yz)))).1
  rw [Nat.mul_div_cancel _ yp,Nat.cast_mul] at hs
  rw [Nat.cast_mul] at hn
  apply (le_div_iff₀ (Nat.cast_pos.mpr zp : 0 < (Z:ℝ))).mpr
  apply (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr yp : 0 < (y:ℝ))).mp
  linarith only [hs,hn]

private theorem density_le_one {y Z : ℕ} (zp : 0 < Z) : density y Z ≤ 1 := by
  have c := card_le_card (filter_subset (fun s : ℕ => s.primeFactors ⊆ Nat.primesLE y) (Icc 1 Z))
  rw [Nat.card_Icc,Nat.add_sub_cancel] at c
  exact (div_le_iff₀ (Nat.cast_pos.mpr zp : 0 < (Z:ℝ))).mpr (by
    rw [one_mul];exact_mod_cast c)

/-- A single positive radius protects every band up to fixed polynomial
degree, uniformly in the observation and in nonnegative proper-power edits. -/
theorem erasure_radius_bounded_below_on_polynomial_bands (j : ℕ) :
    ∃ δ : ℝ,0 < δ ∧ ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → Z ≤ y^j → y*Z ≤ X →
      ∀ a : ArithmeticFunction ℝ,(∀ q,0 ≤ a q) → (∀ q,|a q| ≤ vonMangoldt q) →
        (∀ p,p.Prime → a p=roughMangoldtWeight y p) → δ ≤ bandErasureRadius a y X Z := by
  obtain ⟨c,hc,low⟩ := positive_density j
  have eps : 0 < c/4 := by positivity
  refine ⟨c/4,eps,?_⟩
  filter_upwards [low,smooth_density_from_relative_robustness j eps,eventually_ge_atTop (1:ℕ)]
    with y minD approx yp
  intro Z X yz room large a nn dom sam
  have d0 := minD Z yz room
  have d1 := density_le_one (y:=y) (yp.trans yz)
  let d := density y Z
  have den : 0 < 2-d := by linarith only [d1]
  have ratio : c/2 ≤ d/(2-d) := (le_div_iff₀ den).mpr (by
    have dpos := hc.le.trans d0
    nlinarith only [d0,mul_nonneg hc.le dpos])
  have b := (abs_le.mp (approx Z X yz room large a nn dom sam)).1
  change -(c/4) ≤ bandErasureRadius a y X Z-d/(2-d) at b
  linarith only [ratio,b]

/-- At some fixed degree every sufficiently late unmodified Mangoldt band
can be erased by independent errors below the prescribed positive radius. -/
theorem arbitrarily_small_errors_erase_a_polynomial_band {δ : ℝ} (hδ : 0 < δ) :
    ∃ j : ℕ,0 < j ∧ ∀ᶠ y : ℕ in atTop,∀ X : ℕ,y*y^j ≤ X →
      ∃ e : ℕ → ℝ,(∀ q,|e q| ≤ δ) ∧
        upperQuotientReading (perturbIncrements (roughMangoldtWeight y) e) y X (y^j)=0 := by
  obtain ⟨C,_,upper⟩ := uniform_logarithmic_upper_bound_for_smooth_population
  obtain ⟨j,hj⟩ := exists_nat_gt (4/δ)
  have jp : 0 < j := by exact_mod_cast ((div_pos (by norm_num) hδ).trans hj)
  refine ⟨j,jp,?_⟩
  have grow := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [grow.eventually_ge_atTop C,eventually_ge_atTop (2:ℕ),
    smooth_density_from_relative_robustness j (half_pos hδ)] with y past hy approx
  intro X room
  let Z := y^j
  have yp : 0 < y := by omega
  have zp : 0 < (Z:ℝ) := Nat.cast_pos.mpr (Nat.pow_pos yp)
  have ly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ratio : density y Z ≤ δ/2 := by
    have h := upper y Z yp
    change _*Real.log ((y^j:ℕ):ℝ) ≤ (Z:ℝ)*_ at h
    rw [Nat.cast_pow,Real.log_pow] at h
    have jbound := (div_lt_iff₀ hδ).mp hj
    have num := h.trans (mul_le_mul_of_nonneg_left (show Real.log y+C ≤ 2*Real.log y by linarith) zp.le)
    have cut : ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card:ℝ)*j ≤ 2*Z := by
      apply (mul_le_mul_iff_left₀ ly).mp
      linarith only [num]
    apply (div_le_iff₀ zp).mpr
    apply (mul_le_mul_iff_left₀ (Nat.cast_pos.mpr jp : 0 < (j:ℝ))).mp
    nlinarith only [cut,mul_le_mul_of_nonneg_left jbound.le zp.le]
  have lim := approx Z X (Nat.le_self_pow jp.ne' y) le_rfl room (roughMangoldtWeight y)
    (fun q => by rw [roughMangoldtWeight,roughRestriction_apply];split <;> simp [vonMangoldt_nonneg])
    (mangoldt_dominated _) (fun _ _ => rfl)
  let d := density y Z
  have d1 := density_le_one (y:=y) (Nat.pow_pos yp : 0 < Z)
  have den : 1 ≤ 2-d := by linarith only [d1]
  have d0 : 0 ≤ d := div_nonneg (Nat.cast_nonneg _) zp.le
  have bound : d/(2-d) ≤ d := div_le_self d0 den
  apply (band_erasure_iff _ _ _ _ hδ).mpr
  have h := (abs_le.mp lim).2
  change bandErasureRadius _ y X Z - d/(2-d) ≤ δ/2 at h
  change d ≤ δ/2 at ratio
  linarith only [h,ratio,bound]

end GaloisForLFunctions.RestrictedFactorizationCalculus
