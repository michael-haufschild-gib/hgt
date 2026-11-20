import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTotalVariationOfTheFirstRoughPrimeBand

/-!
# Relative perturbations of the first rough prime band

In the perturbation inequality used for Corollary 5.2 by Shi, Chen,
Huang and Wang, a Lipschitz norm bounds the worst possible displacement.
For a finite quotient reading and coordinatewise relative errors the
extreme readings can be attained. The signed and absolute prime profiles
then give a sharp radius for preserving the sign.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Topology Classical
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Multiplicative error in each observed arithmetic increment. -/
def perturbIncrements (a : ArithmeticFunction ℝ) (e : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun q => (1+e q)*a q,by simp⟩

private def term (a : ArithmeticFunction ℝ) (y X q : ℕ) :=
  a q*coprimeMoebiusSum (primorial y) (X/q)

private theorem perturbation_identity (a : ArithmeticFunction ℝ) (e : ℕ → ℝ) (y X Z : ℕ) :
    upperQuotientReading (perturbIncrements a e) y X Z-upperQuotientReading a y X Z =
      ∑ q∈Ioc (X/Z) X,e q*term a y X q := by
  simp only [upperQuotientReading,←sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  change (1+e q)*a q*_-a q*_=e q*(a q*_)
  ring

private theorem aligned_error (a : ArithmeticFunction ℝ) (y X Z : ℕ) (t : ℝ) :
    ∃ e : ℕ → ℝ,(∀ q,|e q| ≤ |t|) ∧
      upperQuotientReading (perturbIncrements a e) y X Z =
        upperQuotientReading a y X Z+t*primeBandVariation a y X Z := by
  let e := fun q => if 0 ≤ term a y X q then t else -t
  refine ⟨e,fun q => ?_,?_⟩
  · dsimp only [e];split <;> simp
  · have h := perturbation_identity a e y X Z
    have he (q : ℕ) : e q*term a y X q=t*|term a y X q| := by
      dsimp only [e]
      split_ifs with hp
      · rw [abs_of_nonneg hp]
      · rw [abs_of_neg (lt_of_not_ge hp)];ring
    simp_rw [he] at h
    change _ = _+t*∑ q∈Ioc (X/Z) X,|term a y X q|
    rw [mul_sum]
    linarith only [h]

private theorem total_nonneg (a : ArithmeticFunction ℝ) (y X Z : ℕ) :
    0 ≤ primeBandVariation a y X Z := sum_nonneg fun _ _ => abs_nonneg _

/-- All readings compatible with independent relative errors of size δ
fill the closed interval with radius δ times the exact absolute row mass. -/
theorem possible_perturbed_band_readings (a : ArithmeticFunction ℝ) (y X Z : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ) :
    (∃ e : ℕ → ℝ,(∀ q,|e q| ≤ δ) ∧ v=upperQuotientReading (perturbIncrements a e) y X Z) ↔
      |v-upperQuotientReading a y X Z| ≤ δ*primeBandVariation a y X Z := by
  let S := upperQuotientReading a y X Z
  let V := primeBandVariation a y X Z
  constructor
  · rintro ⟨e,he,rfl⟩
    rw [perturbation_identity,primeBandVariation,mul_sum]
    apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum
    intro q _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (he q) (abs_nonneg _)
  · intro h
    by_cases hV : V=0
    · change |v-S| ≤ δ*V at h
      rw [hV,mul_zero,abs_nonpos_iff] at h
      obtain ⟨e,hp,he⟩ := aligned_error a y X Z 0
      refine ⟨e,fun q => (hp q).trans (by simpa only [abs_zero] using hδ),?_⟩
      rw [he,zero_mul,add_zero]
      exact sub_eq_zero.mp h
    · have hp : 0 < V := lt_of_le_of_ne (total_nonneg _ _ _ _) (Ne.symm hV)
      let t := (v-S)/V
      have hsmall : |t| ≤ δ := by
        change |(v-S)/V| ≤ δ
        rw [abs_div,abs_of_pos hp,div_le_iff₀ hp]
        exact h
      obtain ⟨e,hb,he⟩ := aligned_error a y X Z t
      refine ⟨e,fun q => (hb q).trans hsmall,?_⟩
      change _=S+t*V at he
      rw [he,show t*V=v-S from div_mul_cancel₀ _ hV]
      ring

private theorem band_input_nonneg (y n : ℕ) : 0 ≤ roughMangoldtWeight y n := by
  rw [roughMangoldtWeight,roughRestriction_apply]
  split <;> simp [vonMangoldt_nonneg]

/-- Signed rough Mangoldt charge in the first band at the log-square cutoff. -/
def logSquarePrimeBandCharge (X : ℕ) :=
  let y := logSquareCutoff X
  upperQuotientReading (roughMangoldtWeight y) y X (y^2)

/-- Absolute mass of the same rough Mangoldt row. -/
def logSquarePrimeBandVariation (X : ℕ) :=
  let y := logSquareCutoff X
  primeBandVariation (roughMangoldtWeight y) y X (y^2)

private theorem signed_limit :
    Tendsto (fun X : ℕ => logSquarePrimeBandCharge X/(X:ℝ)) atTop (𝓝 (1-Real.log 2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [upper_prime_charge_at_the_log_square_cutoff (half_pos hε)] with X h
  simpa only [Real.dist_eq,logSquarePrimeBandCharge] using (h _ (mangoldt_dominated _) (fun _ _ => rfl)).trans_lt (half_lt_self hε)

private theorem room :
    ∀ᶠ X : ℕ in atTop,logSquareCutoff X*(logSquareCutoff X)^2 ≤ X := by
  filter_upwards [log_square_deletion_cost (by norm_num : (1:ℝ)/2 < 1) (by norm_num : (0:ℝ) < 1/3)]
    with X hx
  let y := logSquareCutoff X
  have hp := deletionPrice_one_le (by norm_num : (0:ℝ) < 1) y
  have h₂ : 1 ≤ (deletionPrice 1 y)^2 := by nlinarith only [hp,sq_nonneg (deletionPrice 1 y-1)]
  have hw : (y:ℝ) ≤ (X:ℝ)^(1/3:ℝ) := by
    have ht := le_mul_of_one_le_right (show 0 ≤ (y:ℝ)+1 by positivity) h₂
    exact (by linarith : (y:ℝ) ≤ (y:ℝ)+1).trans (ht.trans hx)
  have h := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) y) hw 3
  rw [show ((X:ℝ)^(1/3:ℝ))^3=(X:ℝ) by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)];norm_num] at h
  change y*y^2 ≤ X
  rw [mul_comm,←pow_succ]
  exact_mod_cast h

private theorem absolute_limit :
    Tendsto (fun X : ℕ => logSquarePrimeBandVariation X/(X:ℝ)) atTop (𝓝 (1+Real.log 2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hrow := logSquareCutoff_tendsto_atTop (total_variation_through_first_prime_band (half_pos hε))
  filter_upwards [hrow,room,logSquareCutoff_tendsto_atTop.eventually_ge_atTop 2] with X h hroom htwo
  let y := logSquareCutoff X
  have hden : 0 < Real.log y := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hr : Real.log ((y^2:ℕ):ℝ)/Real.log y=2 := by
    rw [Nat.cast_pow,Real.log_pow];push_cast;field_simp [hden.ne']
  have hh := h (y^2) X (Nat.le_self_pow (by decide : 2≠0) y) le_rfl hroom
    (roughMangoldtWeight y) (band_input_nonneg y) (mangoldt_dominated y) (fun _ _ => rfl)
  rw [hr] at hh
  exact hh.trans_lt (half_lt_self hε)

/-- The relative coordinate error at which the extremal signed reading
reaches zero tends to (1−log 2)/(1+log 2) for the actual rough Mangoldt row. -/
theorem relative_sign_radius_at_log_square_cutoff :
    Tendsto (fun X : ℕ => logSquarePrimeBandCharge X/logSquarePrimeBandVariation X) atTop (𝓝 ((1-Real.log 2)/(1+Real.log 2))) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := signed_limit.div absolute_limit (by positivity)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with X hx
  change (logSquarePrimeBandCharge X/(X:ℝ))/(logSquarePrimeBandVariation X/(X:ℝ))=_
  rw [div_div_div_cancel_right₀ (Nat.cast_pos.mpr hx : 0 < (X:ℝ)).ne']

/-- Signed charge after changing each increment by its own relative error. -/
def observedPrimeBand (X : ℕ) (e : ℕ → ℝ) :=
  let y := logSquareCutoff X
  upperQuotientReading (perturbIncrements (roughMangoldtWeight y) e) y X (y^2)

private theorem minimum_profile (δ : ℝ) :
    Tendsto (fun X : ℕ => (logSquarePrimeBandCharge X-δ*logSquarePrimeBandVariation X)/(X:ℝ))
      atTop (𝓝 (1-Real.log 2-δ*(1+Real.log 2))) := by
  simpa only [sub_div,mul_div_assoc] using signed_limit.sub (absolute_limit.const_mul δ)

/-- Below the critical radius all relative perturbations preserve the sign
at every sufficiently large cutoff. -/
theorem all_positive_below_prime_band_radius {δ : ℝ} (hd : 0 ≤ δ)
    (hsmall : δ < (1-Real.log 2)/(1+Real.log 2)) :
    ∀ᶠ X : ℕ in atTop,∀ e : ℕ → ℝ,(∀ q,|e q| ≤ δ) → 0 < observedPrimeBand X e := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := (lt_div_iff₀ (by linarith only [hlog] : 0 < 1+Real.log 2)).mp hsmall
  filter_upwards [(minimum_profile δ).eventually_const_lt (sub_pos.mpr ht),eventually_ge_atTop 1]
    with X hmin hX
  intro e he
  have hx : 0 < (X:ℝ) := Nat.cast_pos.mpr hX
  have hnum := (div_pos_iff_of_pos_right hx).mp hmin
  let y := logSquareCutoff X
  have hbd := (possible_perturbed_band_readings (roughMangoldtWeight y) y X (y^2) hd
    (observedPrimeBand X e)).mp ⟨e,he,rfl⟩
  change |observedPrimeBand X e-logSquarePrimeBandCharge X| ≤ δ*logSquarePrimeBandVariation X at hbd
  linarith only [(abs_le.mp hbd).1,hnum]

/-- Above the critical radius some admissible relative perturbation reverses
the sign at each sufficiently large cutoff. -/
theorem negative_attained_above_prime_band_radius {δ : ℝ} (hd : 0 ≤ δ)
    (hlarge : (1-Real.log 2)/(1+Real.log 2) < δ) :
    ∀ᶠ X : ℕ in atTop,∃ e : ℕ → ℝ,(∀ q,|e q| ≤ δ) ∧ observedPrimeBand X e < 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := (div_lt_iff₀ (by linarith only [hlog] : 0 < 1+Real.log 2)).mp hlarge
  filter_upwards [(minimum_profile δ).eventually_lt_const (sub_neg.mpr ht),eventually_ge_atTop 1]
    with X hmin hX
  let y := logSquareCutoff X
  obtain ⟨e,he,hval⟩ := aligned_error (roughMangoldtWeight y) y X (y^2) (-δ)
  have hnum : logSquarePrimeBandCharge X-δ*logSquarePrimeBandVariation X < 0 := by
    simpa only [zero_mul] using (div_lt_iff₀ (Nat.cast_pos.mpr hX : 0 < (X:ℝ))).mp hmin
  refine ⟨e,fun q => by simpa only [abs_neg,abs_of_nonneg hd] using he q,?_⟩
  change observedPrimeBand X e=logSquarePrimeBandCharge X+ -δ*logSquarePrimeBandVariation X at hval
  linarith only [hval,hnum]

end GaloisForLFunctions.RestrictedFactorizationCalculus
