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

/-- Every exponent strictly above the grid exponent bounds the complete
prefix, uniformly in the endpoint. -/
theorem gcd_grid_upper_power (s : ℕ) {e : ℝ} (he : gcdGridExponent (s+2) < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 + powerGridGcdDeficit (s+2) k ≤ C*((k:ℝ)+1)^e := by
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
        field_simp <;> ring
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

#print axioms gcd_grid_upper_power
#print axioms gcd_grid_eventually_above_power
#print axioms gcd_grid_logarithmic_exponent
#print axioms gcd_reciprocal_reading_exponent

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
