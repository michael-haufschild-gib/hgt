import GaloisForLFunctions.RHTower.MobiusMertensAbsoluteMomentExponentLaw
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CumulativeQuadratureOfTheGcdDeficit
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdDeficitAtTheEighthPowerEndpoints

/-!
# Exact exponent of the positive gcd shortfall

On an r-power grid the cumulative positive shortfall has logarithmic
growth exponent max(0,1-r(1-Θ)). The lower bound uses the cofinal
arithmetic obstruction. The upper bound uses the uniform cofactor-density
estimate and sums its pointwise error against the power grid.
-/

noncomputable section
open Filter Finset
open scoped Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Positive part of the arithmetic growth exponent on the r-power grid. -/
def gcdGridExponent (r : ℕ) : ℝ :=
  max 0 (1-(r:ℝ)*(1-_root_.RHTower.zetaZeroAbscissa))

private theorem row_representation (r m : ℕ) :
    powerGridGcdDeficit r (m+1) - powerGridGcdDeficit r m =
      max (Real.log 2 - Real.log (octaveGcdProduct ((m+1)^r) ((m+1)^(r+1))) /
        ((m:ℝ)+1)^(r+1)) 0 := by
  simp only [powerGridGcdDeficit, sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)),
    add_sub_cancel_left, Nat.cast_succ]

/-- Each individual positive shortfall is bounded by the derivative
scale of every power strictly above the arithmetic exponent. -/
theorem gcd_increment_upper_power (s : ℕ) {e : ℝ} (he : gcdGridExponent (s+2) < e) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : ℕ, powerGridGcdDeficit (s+2) (i+1)-powerGridGcdDeficit (s+2) i ≤
      B*((i:ℝ)+1)^(e-1) := by
  let r := s+2
  have hr : 0 < (r:ℝ) := by dsimp only [r]; positivity
  have he₀ : 0 < e := lt_of_le_of_lt (le_max_left ..) he
  have heΘ : 1-(r:ℝ)*(1-_root_.RHTower.zetaZeroAbscissa) < e :=
    lt_of_le_of_lt (le_max_right ..) he
  let t := 1+(e-1)/(r:ℝ)
  have ht : _root_.RHTower.zeroReSup < t := by
    apply (_root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
      _root_.RHTower.re_le_zetaZeroAbscissa (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy q)).trans_lt
    have h := (lt_div_iff₀ hr).mpr (by linarith only [heΘ] :
        (_root_.RHTower.zetaZeroAbscissa-1)*(r:ℝ) < e-1)
    dsimp only [t]; linarith only [h]
  obtain ⟨A,hA,hprice⟩ := gcd_product_density_above_zero_width ht
  let B := 22 + Real.log 2 + A
  have hlog := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  have hB : 0 ≤ B := by dsimp only [B]; linarith only [hA,hlog]
  have hrow (i : ℕ) : powerGridGcdDeficit r (i+1) - powerGridGcdDeficit r i ≤
      B * ((i:ℝ)+1)^(e-1) := by
    cases i with
    | zero =>
      simpa only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] using
        (gcd_deficit_increment_bounds r 0).2.trans (by dsimp only [B]; linarith only [hA] : Real.log 2 ≤ B)
    | succ i =>
      let m := i+2
      have hm : 2 ≤ m := by dsimp only [m]; omega
      have hm₁ : 1 ≤ m := by omega
      have hm₀ : 0 < (m:ℝ) := Nat.cast_pos.mpr hm₁
      have hmR : 1 ≤ (m:ℝ) := Nat.one_le_cast.mpr hm₁
      rw [row_representation]
      change max (Real.log 2 - Real.log (octaveGcdProduct (m^r) (m^(r+1))) /
        (((i+1:ℕ):ℝ)+1)^(r+1)) 0 ≤ B * (((i+1:ℕ):ℝ)+1)^(e-1)
      rw [← Nat.cast_succ]
      change max (Real.log 2 - Real.log (octaveGcdProduct (m^r) (m^(r+1))) /
        (m:ℝ)^(r+1)) 0 ≤ B * (m:ℝ)^(e-1)
      have h := hprice (one_le_pow₀ hm₁ (n := r)) hm₁
      rw [Nat.cast_pow, ← pow_succ', ← pow_succ', ← Real.rpow_natCast (m:ℝ) r,
        ← Real.rpow_mul hm₀.le] at h
      have hscale : (r:ℝ)*(t-1) = e-1 := by
        dsimp only [t]
        field_simp
        ring
      rw [hscale] at h
      have hp : (m:ℝ)⁻¹ ≤ (m:ℝ)^(e-1) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hmR (by linarith only [he₀])
      have hsq : 1/(m:ℝ)^2 ≤ (m:ℝ)⁻¹ := by
        rw [← one_div (m:ℝ)]
        exact one_div_le_one_div_of_le hm₀ (by nlinarith only [mul_nonneg hm₀.le (sub_nonneg.mpr hmR)])
      have hhalf : 1/(2*(m:ℝ)) ≤ (m:ℝ)⁻¹ := by
        rw [← one_div (m:ℝ)]
        exact one_div_le_one_div_of_le hm₀ (by linarith only [hm₀])
      have hc := (le_abs_self _).trans (cofactor_density_half_step hm)
      have hd := (neg_le_abs _).trans h
      have hp₀ := Real.rpow_nonneg hm₀.le (e-1)
      apply max_le _ (mul_nonneg hB hp₀)
      dsimp only [B]
      rw [show 20/(m:ℝ)^2 = 20*(1/(m:ℝ)^2) by ring] at hc
      linarith only [hc,hd,mul_le_mul_of_nonneg_left (hsq.trans hp) (by norm_num : (0:ℝ) ≤ 20),
        hhalf.trans hp,mul_nonneg hlog hp₀,hp₀]
  exact ⟨B,hB,hrow⟩

/-- Every exponent strictly above the grid exponent bounds the complete
prefix, uniformly in the endpoint. -/
theorem gcd_grid_upper_power (s : ℕ) {e : ℝ} (he : gcdGridExponent (s+2) < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 + powerGridGcdDeficit (s+2) k ≤ C*((k:ℝ)+1)^e := by
  let r := s+2
  have he₀ : 0 < e := lt_of_le_of_lt (le_max_left ..) he
  obtain ⟨B,hB,hrow⟩ := gcd_increment_upper_power s he
  have hd₀ : powerGridGcdDeficit r 0 = 0 := by simp [powerGridGcdDeficit]
  refine ⟨1+B*(1+1/e), by positivity, fun k => ?_⟩
  have hh := sum_le_sum (s := range k) (fun i _ => hrow i)
  rw [sum_range_sub, hd₀, sub_zero, ←mul_sum] at hh
  have h := hh.trans (mul_le_mul_of_nonneg_left
    (_root_.GaloisForLFunctions.ArithmeticGaugeTheory.sum_rpow_sub_one_le he₀ k) hB)
  have hpow := Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg k : 0 ≤ (k:ℝ)) :
    (1:ℝ) ≤ k+1) he₀.le
  change 1 + powerGridGcdDeficit r k ≤ _
  linarith only [h,hpow]

/-- Every nonnegative power below the grid exponent is eventually exceeded,
even after multiplication by an arbitrary fixed constant. -/
theorem gcd_grid_eventually_above_power (s : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hlt : b < gcdGridExponent (s+2)) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C*(k:ℝ)^b < powerGridGcdDeficit (s+2) k := by
  by_contra! hf
  have h := zero_abscissa_of_power_grid_budget s (by norm_num : |(-1:ℝ)| = 1) hb
    ⟨C,hf.mono (fun k hk => (sub_nonneg.mp (sparse_gcd_deficit_comparison (s+2) k).1).trans hk)⟩
  obtain hbad | hbad := lt_max_iff.mp hlt
  · exact (not_lt_of_ge hb) hbad
  · have hh := (le_div_iff₀ (by positivity : 0 < (s:ℝ)+2)).mp h
    push_cast at hbad
    linarith only [hbad,hh]

private theorem log_nat_top : Tendsto (fun k : ℕ => Real.log k) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The log growth rate is an ordinary limit along all integer endpoints. -/
theorem gcd_grid_logarithmic_exponent (s : ℕ) :
    Tendsto (fun k : ℕ => Real.log (1+powerGridGcdDeficit (s+2) k) / Real.log k)
      atTop (𝓝 (gcdGridExponent (s+2))) := by
  have hn (k : ℕ) : 0 ≤ powerGridGcdDeficit (s+2) k :=
    sum_nonneg (fun _ _ => le_max_right _ _)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    by_cases h : b < 0
    · exact Eventually.of_forall fun k => h.trans_le
        (div_nonneg (Real.log_nonneg (by linarith only [hn k])) (Real.log_natCast_nonneg k))
    filter_upwards [gcd_grid_eventually_above_power s (le_of_not_gt h) hb 1,
      eventually_ge_atTop 2] with k hk hk₂
    have hk₁ : (1:ℝ) < k := Nat.one_lt_cast.mpr hk₂
    have hkr := zero_lt_one.trans hk₁
    have hD : (k:ℝ)^b < 1+powerGridGcdDeficit (s+2) k := by linarith only [hk]
    have hl := Real.log_lt_log (Real.rpow_pos_of_pos hkr b) hD
    rw [Real.log_rpow hkr] at hl
    exact (lt_div_iff₀ (Real.log_pos hk₁)).mpr hl
  · intro b hb
    obtain ⟨e,he,heb⟩ := exists_between hb
    obtain ⟨C,hC,h⟩ := gcd_grid_upper_power s he
    have he₀ : 0 ≤ e := (le_max_left ..).trans he.le
    let A := C*2^e
    have hA : 0 < A := by dsimp only [A]; positivity
    have ht : Tendsto (fun k : ℕ => Real.log A / Real.log k + e) atTop (𝓝 (0+e)) :=
      (tendsto_const_nhds.div_atTop log_nat_top).add_const e
    filter_upwards [ht.eventually_lt_const (by simpa using heb : 0+e < b),
      eventually_ge_atTop 2] with k hk hk₂
    have hk₁ : (1:ℝ) < k := Nat.one_lt_cast.mpr hk₂
    have hkr := zero_lt_one.trans hk₁
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (k:ℝ)+1)
      (by linarith only [hk₁] : (k:ℝ)+1 ≤ 2*k) he₀
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hkr.le] at hpow
    have hD := (h k).trans (mul_le_mul_of_nonneg_left hpow hC.le)
    rw [←mul_assoc] at hD
    have hl := Real.log_le_log (by linarith only [hn k]) hD
    change _ ≤ Real.log (A * (k:ℝ)^e) at hl
    rw [Real.log_mul hA.ne' (Real.rpow_pos_of_pos hkr e).ne', Real.log_rpow hkr] at hl
    apply lt_of_le_of_lt _ hk
    apply (div_le_iff₀ (Real.log_pos hk₁)).mpr
    rwa [add_mul, div_mul_cancel₀ _ (Real.log_pos hk₁).ne']

/-- The normalized sum of individually weighted gcd readings recovers the
same exponent as the logarithm of the entire shortfall. -/
theorem gcd_reciprocal_reading_exponent (s : ℕ) :
    Tendsto (fun k : ℕ => gcdDeficitLogSum (s+2) k / Real.log k) atTop
      (𝓝 (gcdGridExponent (s+2))) := by
  obtain ⟨_,hc,_⟩ := gcd_log_sum_limiting_error (s+2)
  have h := (gcd_grid_logarithmic_exponent s).sub (hc.div_atTop log_nat_top)
  rw [sub_zero] at h
  exact h.congr fun k => by rw [sub_div]; ring

/-! ## Superlevel counts and power moments

The layer decomposition in Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, Proposition 2.4) suggests measuring the heights of
individual losses. For these arithmetic data, Hölder's inequality and the
pointwise prime estimate force nearly full logarithmic density at every
level just below the critical power.
-/

/-- Individual positive loss at the next grid point. -/
def shortfallAt (r i : ℕ) : ℝ := powerGridGcdDeficit r (i+1)-powerGridGcdDeficit r i

private theorem shortfall_nonneg (r i : ℕ) : 0 ≤ shortfallAt r i := (gcd_deficit_increment_bounds r i).1

private theorem sum_shortfall (r K : ℕ) :
    ∑ i ∈ range K, shortfallAt r i = powerGridGcdDeficit r K := by
  simp only [shortfallAt,sum_range_sub,show powerGridGcdDeficit r 0=0 by simp [powerGridGcdDeficit],sub_zero]

/-- Above the critical moment index the magnitudes of the individual
shortfalls are summable to that power. -/
theorem summable_shortfall_power (s : ℕ) {p : ℝ} (hp : 1<p)
    (hg : gcdGridExponent (s+2) < 1-p⁻¹) :
    Summable (fun i => shortfallAt (s+2) i ^ p) := by
  obtain ⟨e,he,hep⟩ := exists_between hg
  obtain ⟨B,hB,h⟩ := gcd_increment_upper_power s he
  have hp₀ := zero_lt_one.trans hp
  have hsmall : (e-1)*p < -1 := by
    have hf := mul_lt_mul_of_pos_right hep hp₀
    rw [sub_mul,one_mul,inv_mul_cancel₀ hp₀.ne'] at hf
    linarith only [hf]
  have hs := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hsmall)
  have hbound : Summable (fun i : ℕ => B^p*((i:ℝ)+1)^((e-1)*p)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hs.mul_left (B^p)
  apply Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (shortfall_nonneg _ i) p) _ hbound
  intro i
  have hh := Real.rpow_le_rpow (shortfall_nonneg _ i) (h i) hp₀.le
  have base : 0 ≤ (i:ℝ)+1 := by positivity
  rw [Real.mul_rpow hB (Real.rpow_nonneg base (e-1)),←Real.rpow_mul base] at hh
  exact hh

/-- Every finite p-moment forces the corresponding strip width. This
also forces divergence at all indices below the critical index. -/
theorem grid_exponent_le_of_summable_shortfall (s : ℕ) {p : ℝ} (hp : 1 ≤ p)
    (hs : Summable (fun i => shortfallAt (s+2) i ^ p)) :
    gcdGridExponent (s+2) ≤ 1-p⁻¹ := by
  let r := s+2
  let M := (∑' i,shortfallAt r i^p)^p⁻¹
  have ha : 0 ≤ 1-p⁻¹ := sub_nonneg.mpr ((inv_le_one₀ (zero_lt_one.trans_le hp)).mpr hp)
  by_contra! h
  obtain ⟨k,hk⟩ := (gcd_grid_eventually_above_power s ha h M).exists
  have hh := _root_.RHTower.sum_le_card_rpow_mul_sum_rpow (s := range k)
    (fun i _ => shortfall_nonneg r i) hp
  rw [sum_shortfall,card_range] at hh
  have hsum := hs.sum_le_tsum (range k) (fun i _ => Real.rpow_nonneg (shortfall_nonneg r i) p)
  have hpow := Real.rpow_le_rpow (sum_nonneg (fun i _ => Real.rpow_nonneg (shortfall_nonneg r i) p))
    hsum (inv_nonneg.mpr (zero_le_one.trans hp))
  apply hk.not_ge
  refine hh.trans ?_
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The exact strip parameter is the transition in the unweighted
power sums of the single-site losses. -/
theorem grid_exponent_iff_shortfall_moments (s : ℕ) {b : ℝ} (hb : 0 ≤ b) (hb1 : b<1) :
    gcdGridExponent (s+2) ≤ b ↔
      ∀ e ∈ Set.Ioo b 1, Summable (fun i => shortfallAt (s+2) i ^ (1-e)⁻¹) := by
  have param {e : ℝ} (he : e ∈ Set.Ioo b 1) : 1 < (1-e)⁻¹ :=
    (one_lt_inv₀ (sub_pos.mpr he.2)).mpr (by linarith only [hb,he.1])
  constructor
  · intro hg e he
    apply summable_shortfall_power s (param he)
    simpa only [inv_inv,sub_sub_cancel] using hg.trans_lt he.1
  · intro hs
    by_contra! hg
    obtain ⟨e,he,he'⟩ := exists_between (lt_min hg hb1)
    have hm : e ∈ Set.Ioo b 1 := ⟨he,he'.trans_le (min_le_right _ _)⟩
    have hc := grid_exponent_le_of_summable_shortfall s (param hm).le (hs e hm)
    rw [inv_inv,sub_sub_cancel] at hc
    exact (he'.trans_le (min_le_left _ _)).not_ge hc

private theorem subpower_iff_zero_exponent (s : ℕ) :
    subpowerGcdGrid (s+2) ↔ gcdGridExponent (s+2) ≤ 0 := by
  rw [subpower_gcd_grid_iff_octave,subpower_octave_grid_iff_abscissa s (by norm_num : |(-1:ℝ)|=1),
    gcdGridExponent,max_le_iff, and_iff_right le_rfl, le_div_iff₀ (by positivity)]
  push_cast
  constructor <;> intro h <;> linarith only [h]

/-- On the square grid RH is equivalent to summability of every power
strictly greater than one of the individual positive gcd deficits. -/
theorem rh_iff_all_shortfall_moments :
    RiemannHypothesis ↔ ∀ p : ℝ, 1<p → Summable (fun i => shortfallAt 2 i ^ p) := by
  rw [riemannHypothesis_iff_square_cube_gcd_deficit,subpower_iff_zero_exponent 0]
  constructor
  · intro hg p hp
    exact summable_shortfall_power 0 hp (hg.trans_lt (sub_pos.mpr
      ((inv_lt_one₀ (zero_lt_one.trans hp)).mpr hp)))
  · intro hm
    apply (grid_exponent_iff_shortfall_moments 0 (b := 0) le_rfl zero_lt_one).mpr
    intro e he
    exact hm _ ((one_lt_inv₀ (sub_pos.mpr he.2)).mpr (by linarith only [he.1]))

/-- The same power budget holds on any finite selection of sites, with
its own cardinality in place of the ambient endpoint. The selection can
depend on all the observed shortfalls. -/
theorem arbitrary_shortfall_sum (s : ℕ) {e : ℝ} (he : gcdGridExponent (s+2) < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ, ∑ i ∈ S,shortfallAt (s+2) i ≤ C*(S.card:ℝ)^e := by
  let r := s+2
  have he₀ : 0<e := (le_max_left ..).trans_lt he
  by_cases he₁ : e<1
  · let p := (1-e)⁻¹
    have hp : 1<p := (one_lt_inv₀ (sub_pos.mpr he₁)).mpr (by linarith only [he₀])
    have hexp : 1-p⁻¹=e := by simp [p]
    have hs := summable_shortfall_power s hp (hexp ▸ he)
    let C := (∑' i,shortfallAt r i^p)^p⁻¹
    have hnon (i : ℕ) : 0 ≤ shortfallAt r i^p := Real.rpow_nonneg (shortfall_nonneg r i) _
    refine ⟨C,Real.rpow_nonneg (tsum_nonneg hnon) _,fun S => ?_⟩
    have h := _root_.RHTower.sum_le_card_rpow_mul_sum_rpow (s := S)
      (fun i _ => shortfall_nonneg r i) hp.le
    rw [hexp] at h
    rw [mul_comm C]
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (sum_nonneg (fun i _ => hnon i))
      (hs.sum_le_tsum S (fun i _ => hnon i)) (inv_nonneg.mpr (zero_le_one.trans hp.le))) (by positivity))
  · have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    refine ⟨Real.log 2,hlog,fun S => ?_⟩
    by_cases hs : S.Nonempty
    · have hsum := sum_le_sum (s := S) (fun i _ => (gcd_deficit_increment_bounds r i).2)
      rw [sum_const,nsmul_eq_mul,mul_comm] at hsum
      have hc : 1≤(S.card:ℝ) := Nat.one_le_cast.mpr hs.card_pos
      exact hsum.trans (mul_le_mul_of_nonneg_left (by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hc (le_of_not_gt he₁)) hlog)
    · rw [not_nonempty_iff_eq_empty.mp hs,card_empty,sum_empty,Nat.cast_zero,Real.zero_rpow he₀.ne',mul_zero]

private theorem exponent_margin {g α : ℝ} (hg : 0<g) (ha : 0 ≤ α) (ha₁ : α<1) :
    ∃ e : ℝ, g<e ∧ α*e<g := by
  by_cases hz : α=0
  · exact ⟨g+1,by linarith,by simpa only [hz,zero_mul]⟩
  · have hp := ha.lt_of_ne (Ne.symm hz)
    obtain ⟨e,he,hα⟩ := exists_between ((lt_div_iff₀ hp).mpr (mul_lt_of_lt_one_right hg ha₁))
    exact ⟨e,he,by simpa only [mul_comm] using (lt_div_iff₀ hp).mp hα⟩

/-- Removing any at most K^α sites, with α<1, preserves all strict
lower growth exponents. The deleted set may vary adversarially with K. -/
theorem trimmed_shortfall_above_power (s : ℕ) {α b : ℝ} (hα : 0≤α) (hα₁ : α<1)
    (hb : 0 ≤ b) (hbg : b<gcdGridExponent (s+2)) (C : ℝ) :
    ∀ᶠ K : ℕ in atTop, ∀ E ⊆ range K, (E.card:ℝ) ≤ (K:ℝ)^α →
      C*(K:ℝ)^b < ∑ i ∈ range K \ E,shortfallAt (s+2) i := by
  let g := gcdGridExponent (s+2)
  obtain ⟨e,he,hae⟩ := exponent_margin (hb.trans_lt hbg) hα hα₁
  obtain ⟨D,hD,hbudget⟩ := arbitrary_shortfall_sum s he
  let t := max b (α*e)
  have ht : 0≤t := hb.trans (le_max_left _ _)
  have htg : t<g := max_lt hbg hae
  have he₀ : 0 ≤ e := ((hb.trans_lt hbg).trans he).le
  filter_upwards [gcd_grid_eventually_above_power s ht htg (|C|+D),eventually_ge_atTop 1] with K hK hk
  intro E hE hc
  have hpos : 1≤(K:ℝ) := Nat.one_le_cast.mpr hk
  have hdiscard := (hbudget E).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hc he₀) hD)
  rw [← Real.rpow_mul (Nat.cast_nonneg _)] at hdiscard
  have h₁ := hdiscard.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hpos (le_max_right _ _ : α*e≤t)) hD)
  have h₂ := mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le hpos (le_max_left _ _ : b≤t))
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _)
  have hsum := Finset.sum_sdiff (f := shortfallAt (s+2)) hE
  rw [sum_shortfall] at hsum
  linarith only [h₁,h₂,hK,hsum]

/-- Every late endpoint has more than K^α individual deficits of size
at least K^(g−1−η) whenever the arithmetic exponent g is positive.
This holds for every α<1 and every positive slack η. -/
theorem many_near_critical_shortfalls (s : ℕ) (hg : 0<gcdGridExponent (s+2))
    {α η : ℝ} (hα : 0≤α) (hα₁ : α<1) (hη : 0<η) :
    ∀ᶠ K : ℕ in atTop, (K:ℝ)^α <
      (((range K).filter (fun i => (K:ℝ)^(gcdGridExponent (s+2)-1-η) ≤ shortfallAt (s+2) i)).card:ℝ) := by
  let g := gcdGridExponent (s+2)
  let b := max 0 (g-η)
  have hb : 0 ≤ b := le_max_left _ _
  have hbg : b<g := max_lt hg (sub_lt_self _ hη)
  filter_upwards [trimmed_shortfall_above_power s hα hα₁ hb hbg 1,eventually_ge_atTop 1] with K hK hk
  let H := (range K).filter (fun i => (K:ℝ)^(g-1-η) ≤ shortfallAt (s+2) i)
  change (K:ℝ)^α < (H.card:ℝ)
  by_contra! h
  have hlarge := hK H (filter_subset _ _) h
  have hsmall : ∀ i ∈ range K \ H,shortfallAt (s+2) i ≤ (K:ℝ)^(g-1-η) := by
    intro i hi
    have hh := mem_sdiff.mp hi
    exact le_of_lt (lt_of_not_ge (fun h => hh.2 (mem_filter.mpr ⟨hh.1,h⟩)))
  have hsum := sum_le_sum hsmall
  rw [sum_const,nsmul_eq_mul] at hsum
  have hc : ((range K \ H).card:ℝ) ≤ K := by
    exact_mod_cast ((card_le_card (sdiff_subset : range K \ H ⊆ range K)).trans_eq (card_range K))
  have hupper := hsum.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hreal : 0 < (K:ℝ) := Nat.cast_pos.mpr hk
  have hpow : (K:ℝ)*(K:ℝ)^(g-1-η)=(K:ℝ)^(g-η) := by
    conv_lhs => lhs; rw [←Real.rpow_one (K:ℝ)]
    rw [← Real.rpow_add hreal]; congr 1; ring
  rw [hpow] at hupper
  have hbnd := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hk) (le_max_right 0 (g-η))
  rw [one_mul] at hlarge
  exact hlarge.not_ge (hupper.trans hbnd)

/-- Adversarial deletion of a power-sparse set leaves the full
logarithmic growth rate unchanged, at every grid exponent. -/
theorem trimmed_shortfall_exponent (s : ℕ) {α : ℝ} (hα : 0≤α) (hα₁ : α<1)
    (E : ℕ → Finset ℕ) (hE : ∀ᶠ K : ℕ in atTop, E K ⊆ range K ∧ ((E K).card:ℝ) ≤ (K:ℝ)^α) :
    Tendsto (fun K : ℕ => Real.log (1+∑ i ∈ range K \ E K,shortfallAt (s+2) i) / Real.log K)
      atTop (𝓝 (gcdGridExponent (s+2))) := by
  let S := fun K => ∑ i ∈ range K \ E K,shortfallAt (s+2) i
  have hnon (K : ℕ) : 0≤S K := sum_nonneg (fun i _ => shortfall_nonneg _ i)
  apply tendsto_order.mpr
  constructor
  · intro b hb
    by_cases h : b<0
    · exact Eventually.of_forall (fun K => h.trans_le (div_nonneg
        (Real.log_nonneg (le_add_of_nonneg_right (hnon K))) (Real.log_natCast_nonneg K)))
    filter_upwards [trimmed_shortfall_above_power s hα hα₁ (le_of_not_gt h) hb 1,
      hE,eventually_ge_atTop 2] with K hK he hk
    have hp : (1:ℝ)<K := Nat.one_lt_cast.mpr hk
    have hl : (K:ℝ)^b < 1+S K := by
      have hx := hK _ he.1 he.2
      change 1*(K:ℝ)^b < S K at hx
      linarith only [hx]
    have hlog := Real.log_lt_log (Real.rpow_pos_of_pos (zero_lt_one.trans hp) _) hl
    rw [Real.log_rpow (zero_lt_one.trans hp)] at hlog
    exact (lt_div_iff₀ (Real.log_pos hp)).mpr hlog
  · intro b hb
    filter_upwards [(gcd_grid_logarithmic_exponent s).eventually_lt_const hb,eventually_ge_atTop 2] with K hK hk
    have hs : S K ≤ powerGridGcdDeficit (s+2) K := by
      rw [← sum_shortfall]
      exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun i _ _ => shortfall_nonneg _ i)
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (Real.log_le_log (by linarith only [hnon K])
      (add_le_add le_rfl hs)) (Real.log_natCast_nonneg K)) hK

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
