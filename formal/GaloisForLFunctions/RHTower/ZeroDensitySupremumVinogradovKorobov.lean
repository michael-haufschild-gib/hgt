import GaloisForLFunctions.RHTower.VinogradovKorobovWidthComparison
import GaloisForLFunctions.RHTower.XiZeroShortWeightVanishing

/-!
# The weighted zero sum with the Vinogradov–Korobov saving

With the surrogate width `w(T) = (max 1 (log T))^{-5/7}/10¹²` the dyadic majorant
`tsum_zeroShortWeight_le` reads, at `X = x^{2u}` and `L = log x`,

`Σ_ρ x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|)) ≤ (finite low part) + C (3L)^{B+2} e^{-κ L^{2/7}}
  + C (3L)² x^{-u(2 - A/2)/4}`,

because `x^{-δ w(x^{2u})} = exp(-κ L^{2/7})` exactly, with `κ = δ (2u)^{-5/7}/10¹²` and
`δ = 1 - uA`.  Since `2/7 > 1/4`, every one of the three pieces is `o(exp(-K (log x)^{1/4}))` for
every constant `K`, which is the exponential saving

`sup_σ x^{σ-1} N(σ, T) ≪ exp(-(log x)^{1/4})`

in the form the explicit formula consumes.  The density bound enters only as data, so everything
here is unconditional.
-/

set_option autoImplicit false

namespace RHTower

noncomputable section

open Filter Topology RHTower.Sieve

/-! ## Monotonicity of the zero weight in the height cut-off -/

/-- `zeroShortWeight` grows with the cut-off `Y`. -/
theorem zeroShortWeight_mono_right {x Y Y' : ℝ} (hx : 0 ≤ x) (hYY' : Y ≤ Y') (q : XiZeroCopy) :
    zeroShortWeight x Y (q.1 : ℂ) ≤ zeroShortWeight x Y' (q.1 : ℂ) := by
  have hN : (0 : ℝ) < ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ :=
    mul_pos (norm_pos_iff.mpr (xiZeroCopy_ne_zero q)) (norm_pos_iff.mpr (xiZeroCopy_one_sub_ne_zero q))
  rw [zeroShortWeight, zeroShortWeight]
  gcongr

/-- The total zero weight grows with the cut-off `Y`. -/
theorem tsum_zeroShortWeight_mono_right {x Y Y' : ℝ} (hx : 1 ≤ x) (hY : 0 ≤ Y) (hYY' : Y ≤ Y') :
    ∑' q : XiZeroCopy, zeroShortWeight x Y (q.1 : ℂ)
      ≤ ∑' q : XiZeroCopy, zeroShortWeight x Y' (q.1 : ℂ) :=
  Summable.tsum_le_tsum (fun q => zeroShortWeight_mono_right (by linarith) hYY' q)
    (summable_zeroShortWeight hx hY) (summable_zeroShortWeight hx (le_trans hY hYY'))

/-! ## An exponential saving beats a quarter power of the logarithm -/

/-- `e^{K L^{1/4}} (3L)^n e^{-κ L^e} → 0` for every `e > 1/4`: the exponent gap is absorbed by
`L^{e - 1/4} → ∞`, and the remaining `e^{-(κ/2)L^e}` beats `L^{n+1}` through `e^{-t} ≤ m!/t^m`. -/
theorem tendsto_exp_quarter_mul_pow_mul_exp_neg_rpow (n : ℕ) {K κ e : ℝ} (hκ : 0 < κ)
    (he : 1 / 4 < e) :
    Tendsto (fun L : ℝ => Real.exp (K * L ^ ((1 : ℝ) / 4))
      * ((3 * L) ^ n * Real.exp (-(κ * L ^ e)))) atTop (𝓝 0) := by
  set m : ℕ := 4 * (n + 1) with hm
  set C : ℝ := 3 ^ n * (m.factorial : ℝ) / (κ / 2) ^ m with hC
  have hup : Tendsto (fun L : ℝ => C / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ),
      (tendsto_rpow_atTop (show (0 : ℝ) < e - 1 / 4 by linarith)).eventually_ge_atTop
        (2 * K / κ)] with L hL1 hLe
    have hL0 : (0 : ℝ) < L := by linarith
    have h14 : (0 : ℝ) ≤ L ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hL0.le _
    have ht0 : (0 : ℝ) < κ / 2 * L ^ e := by positivity
    -- the quarter power is swallowed by half the saving
    have hsplit : L ^ e = L ^ ((1 : ℝ) / 4) * L ^ (e - 1 / 4) := by
      rw [← Real.rpow_add hL0]
      ring_nf
    have hq : K * L ^ ((1 : ℝ) / 4) ≤ κ / 2 * L ^ e := by
      have h := mul_le_mul_of_nonneg_left hLe
        (by positivity : (0 : ℝ) ≤ κ / 2 * L ^ ((1 : ℝ) / 4))
      have he2 : κ / 2 * L ^ ((1 : ℝ) / 4) * (2 * K / κ) = K * L ^ ((1 : ℝ) / 4) := by
        field_simp
      rw [hsplit]
      calc K * L ^ ((1 : ℝ) / 4) = κ / 2 * L ^ ((1 : ℝ) / 4) * (2 * K / κ) := he2.symm
        _ ≤ κ / 2 * L ^ ((1 : ℝ) / 4) * L ^ (e - 1 / 4) := h
        _ = κ / 2 * (L ^ ((1 : ℝ) / 4) * L ^ (e - 1 / 4)) := by ring
    have hexp : Real.exp (K * L ^ ((1 : ℝ) / 4)) * Real.exp (-(κ * L ^ e))
        ≤ Real.exp (-(κ / 2 * L ^ e)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      linarith
    -- the saving beats `L^{n+1}`
    have hfac := exp_neg_le_factorial_div ht0 m
    have hpowm : (κ / 2 * L ^ e) ^ m = (κ / 2) ^ m * L ^ (e * m) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ e) m, ← Real.rpow_mul hL0.le]
    have hge : L ^ ((n : ℝ) + 1) ≤ L ^ (e * m) := by
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      rw [hm]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hLn1 : L ^ ((n : ℝ) + 1) = L ^ (n + 1) := by
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hden : (κ / 2 : ℝ) ^ m * L ^ (n + 1) ≤ (κ / 2 * L ^ e) ^ m := by
      rw [hpowm, ← hLn1]
      exact mul_le_mul_of_nonneg_left hge (by positivity)
    have hle2 : (m.factorial : ℝ) / (κ / 2 * L ^ e) ^ m
        ≤ (m.factorial : ℝ) / ((κ / 2) ^ m * L ^ (n + 1)) := by
      have hf : (0 : ℝ) ≤ (m.factorial : ℝ) := Nat.cast_nonneg _
      exact div_le_div_of_nonneg_left hf (by positivity) hden
    calc Real.exp (K * L ^ ((1 : ℝ) / 4)) * ((3 * L) ^ n * Real.exp (-(κ * L ^ e)))
        = (3 * L) ^ n * (Real.exp (K * L ^ ((1 : ℝ) / 4)) * Real.exp (-(κ * L ^ e))) := by ring
      _ ≤ (3 * L) ^ n * Real.exp (-(κ / 2 * L ^ e)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (3 * L) ^ n * ((m.factorial : ℝ) / ((κ / 2) ^ m * L ^ (n + 1))) :=
          mul_le_mul_of_nonneg_left (le_trans hfac hle2) (by positivity)
      _ = C / L := by
          rw [hC, mul_pow, pow_succ]
          field_simp

/-- `e^{K (log x)^{1/4}} (log x + 2)^k x^{-a} → 0`. -/
theorem tendsto_exp_quarter_mul_logPow_mul_rpow_neg (k : ℕ) {K a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (K * Real.log x ^ ((1 : ℝ) / 4))
      * ((Real.log x + 2) ^ k * x ^ (-a))) atTop (𝓝 0) := by
  have hcomp := (tendsto_exp_quarter_mul_pow_mul_exp_neg_rpow k (K := K) ha
    (by norm_num : (1 : ℝ) / 4 < 1)).comp Real.tendsto_log_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have := Real.log_nonneg hx
    have : (0 : ℝ) ≤ x ^ (-a) := Real.rpow_nonneg (by linarith) _
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
    have hL1 : (1 : ℝ) ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]; exact hx
    have hxa : x ^ (-a) = Real.exp (-(a * Real.log x ^ (1 : ℝ))) := by
      rw [Real.rpow_one, Real.rpow_def_of_pos hx0]
      ring_nf
    have hpk : (Real.log x + 2) ^ k ≤ (3 * Real.log x) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith) k
    rw [hxa]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpk (Real.exp_nonneg _)) (Real.exp_nonneg _)

/-! ## The weighted zero sum against a quarter power of the logarithm -/

/-- The zero-free saving at the surrogate width is exactly `exp(-κ L^{2/7})`. -/
theorem rpow_neg_surrogate_eq_exp {x u δ : ℝ} (hx : 0 < x) (hu : 0 < u)
    (hL : 1 ≤ 2 * u * Real.log x) :
    x ^ (-(δ * vinogradovKorobovSurrogateWidth (x ^ (2 * u))))
      = Real.exp (-(δ * (2 * u) ^ (-(5 : ℝ) / 7) / 10 ^ 12 * Real.log x ^ ((2 : ℝ) / 7))) := by
  have hL0 : (0 : ℝ) < Real.log x := by nlinarith
  have hlogX : Real.log (x ^ (2 * u)) = 2 * u * Real.log x := Real.log_rpow hx _
  have hw : vinogradovKorobovSurrogateWidth (x ^ (2 * u))
      = (2 * u * Real.log x) ^ (-(5 : ℝ) / 7) / 10 ^ 12 := by
    rw [vinogradovKorobovSurrogateWidth_eq (by rw [hlogX]; exact hL), hlogX]
  have hfac : (2 * u * Real.log x) ^ (-(5 : ℝ) / 7)
      = (2 * u) ^ (-(5 : ℝ) / 7) * Real.log x ^ (-(5 : ℝ) / 7) :=
    Real.mul_rpow (by positivity) hL0.le
  have hcollapse : Real.log x ^ (-(5 : ℝ) / 7) * Real.log x = Real.log x ^ ((2 : ℝ) / 7) := by
    nth_rewrite 2 [show Real.log x = Real.log x ^ (1 : ℝ) from (Real.rpow_one _).symm]
    rw [← Real.rpow_add hL0]
    norm_num
  rw [Real.rpow_def_of_pos hx, hw, hfac]
  congr 1
  rw [← hcollapse]
  ring

/-- **The exponential saving in the weighted zero sum.**  Under any density exponent `A < 4` with
`uA < 1`, the zero weight is `o(exp(-K (log x)^{1/4}))` for every constant `K ≥ 0`. -/
theorem tendsto_exp_quarter_mul_tsum_zeroShortWeight_of_density {K A u c D T₀d : ℝ} {B : ℕ}
    (hA0 : 0 ≤ A) (hA4 : A < 4) (hu : 0 < u) (hu2 : u ≤ 1 / 2) (huA : u * A < 1)
    (hc : 1 ≤ c) (hD : 0 ≤ D)
    (hdens : ∀ T : ℝ, T₀d ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ))) :
    Tendsto (fun x : ℝ => Real.exp (K * Real.log x ^ ((1 : ℝ) / 4))
      * ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)) atTop (𝓝 0) := by
  obtain ⟨T₁, hT₁, hfree⟩ := exists_zeroHeightBox_zeroFree_fiveSevenths
  have hδ : 0 < 1 - u * A := by linarith
  set δ := 1 - u * A with hδdef
  set c₁ : ℝ := 2 - A / 2 with hc₁
  have hc₁0 : 0 < c₁ := by rw [hc₁]; linarith
  set T₀ : ℝ := max (max T₀d T₁) 1 with hT₀
  have hT₀1 : 1 ≤ T₀ := le_max_right _ _
  set w : ℝ → ℝ := vinogradovKorobovSurrogateWidth with hw
  set P : ℝ := (1 + (B + 1) / (c₁ / 4)) ^ B with hP
  have hPb : ∀ T : ℝ, 1 ≤ T → (1 + Real.log T) ^ B ≤ P * T ^ (c₁ / 4) :=
    fun T hT => one_add_log_pow_le_rpow B (by positivity) hT
  have hdens' : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ)) :=
    fun T hT σ h1 h2 => hdens T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT) σ h1 h2
  have hfree' : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, (zeroHeightBox σ T).Nonempty → σ ≤ 1 - w T :=
    fun T hT σ hN => hfree T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT) σ hN
  have hw0 : ∀ T : ℝ, 0 ≤ w T := fun T => vinogradovKorobovSurrogateWidth_nonneg T
  have hwanti : ∀ T T' : ℝ, T₀ ≤ T → T ≤ T' → w T' ≤ w T := fun T T' hT hTT' =>
    vinogradovKorobovSurrogateWidth_antitone (le_trans hT₀1 hT) hTT'
  set Low := (finite_xiOrdinateWindow T₀ 0).toFinset with hLow
  set κ : ℝ := δ * (2 * u) ^ (-(5 : ℝ) / 7) / 10 ^ 12 with hκ
  have hκ0 : 0 < κ := by
    rw [hκ]
    have : (0 : ℝ) < (2 * u) ^ (-(5 : ℝ) / 7) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  set G : ℝ := 1 / (1 - (2 : ℝ) ^ (-(c₁ / 8))) with hG
  set H₁ : ℝ → ℝ := fun x => (1 + Real.log (x ^ (2 * u)) / Real.log 2)
      * (1 + Real.log (x ^ (2 * u))) ^ B * x ^ (-(δ * w (x ^ (2 * u)))) with hH₁
  set U : ℝ → ℝ := fun x => ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1)
      + 8 * c * D * ((Real.log x + 2) * H₁ x)
      + 8 * c * D * P * G * ((Real.log x + 2) * x ^ (-(u * c₁ / 4))) with hU
  -- the three pieces of the majorant
  have hLowT : Tendsto (fun x : ℝ => Real.exp (K * Real.log x ^ ((1 : ℝ) / 4))
      * ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1)) atTop (𝓝 0) := by
    simp_rw [Finset.mul_sum]
    have h := tendsto_finsetSum Low
      (f := fun (q : XiZeroCopy) (x : ℝ) =>
        Real.exp (K * Real.log x ^ ((1 : ℝ) / 4)) * x ^ ((q.1 : ℂ).re - 1))
      (a := fun _ => (0 : ℝ)) (x := atTop) (fun q _ => by
        have hpos : 0 < 1 - (q.1 : ℂ).re := by linarith [xiZeroCopy_re_lt_one q]
        refine (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 0 (K := K) hpos).congr fun x => ?_
        rw [pow_zero, one_mul]
        congr 2
        ring)
    simpa using h
  have hmidT : Tendsto (fun x : ℝ => Real.exp (K * Real.log x ^ ((1 : ℝ) / 4))
      * ((Real.log x + 2) * H₁ x)) atTop (𝓝 0) := by
    have hcomp := (tendsto_exp_quarter_mul_pow_mul_exp_neg_rpow (B + 2) (K := K) hκ0
      (by norm_num : (1 : ℝ) / 4 < 2 / 7)).comp Real.tendsto_log_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hL := Real.log_nonneg hx
      have hX1 : 1 ≤ x ^ (2 * u) := Real.one_le_rpow hx (by linarith)
      have hlX := Real.log_nonneg hX1
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      rw [hH₁]
      dsimp only
      have : 0 ≤ x ^ (-(δ * w (x ^ (2 * u)))) := Real.rpow_nonneg (by linarith) _
      positivity
    · filter_upwards [eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (Real.exp (1 / (2 * u)))]
        with x hx hxu
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
      have hL1 : (1 : ℝ) ≤ Real.log x := by
        rw [Real.le_log_iff_exp_le hx0]; exact hx
      have hLu : 1 / (2 * u) ≤ Real.log x := by
        rw [← Real.log_exp (1 / (2 * u))]
        exact Real.log_le_log (Real.exp_pos _) hxu
      have hLuu : 1 ≤ 2 * u * Real.log x := by
        rw [div_le_iff₀ (by linarith)] at hLu
        linarith
      set L := Real.log x with hLdef
      have hlogX : Real.log (x ^ (2 * u)) = 2 * u * L := by rw [Real.log_rpow hx0]
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have hf2 : 1 + Real.log (x ^ (2 * u)) / Real.log 2 ≤ 3 * L := by
        rw [hlogX]
        have : 2 * u * L / Real.log 2 ≤ 2 * L := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        linarith
      have hf3 : 1 + Real.log (x ^ (2 * u)) ≤ 3 * L := by rw [hlogX]; nlinarith
      have hf3' : (0 : ℝ) ≤ 1 + Real.log (x ^ (2 * u)) := by rw [hlogX]; positivity
      have hf2' : (0 : ℝ) ≤ 1 + Real.log (x ^ (2 * u)) / Real.log 2 := by
        rw [hlogX]
        have : (0 : ℝ) ≤ 2 * u * L / Real.log 2 := by positivity
        linarith
      have hwid : x ^ (-(δ * w (x ^ (2 * u)))) = Real.exp (-(κ * L ^ ((2 : ℝ) / 7))) := by
        rw [hw, hκ, hLdef]
        exact rpow_neg_surrogate_eq_exp hx0 hu hLuu
      simp only [Function.comp_apply]
      rw [hH₁]
      dsimp only
      rw [hwid, ← hLdef]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
      calc (L + 2) * ((1 + Real.log (x ^ (2 * u)) / Real.log 2)
            * (1 + Real.log (x ^ (2 * u))) ^ B * Real.exp (-(κ * L ^ ((2 : ℝ) / 7))))
          ≤ (3 * L) * ((3 * L) * (3 * L) ^ B * Real.exp (-(κ * L ^ ((2 : ℝ) / 7)))) := by
            gcongr
            linarith
        _ = (3 * L) ^ (B + 2) * Real.exp (-(κ * L ^ ((2 : ℝ) / 7))) := by ring
  have htailT : Tendsto (fun x : ℝ => Real.exp (K * Real.log x ^ ((1 : ℝ) / 4))
      * ((Real.log x + 2) * x ^ (-(u * c₁ / 4)))) atTop (𝓝 0) := by
    have h := tendsto_exp_quarter_mul_logPow_mul_rpow_neg 1 (K := K)
      (show (0 : ℝ) < u * c₁ / 4 by positivity)
    exact h.congr fun x => by rw [pow_one]
  have hUT : Tendsto (fun x : ℝ => Real.exp (K * Real.log x ^ ((1 : ℝ) / 4)) * U x)
      atTop (𝓝 0) := by
    have h := (hLowT.add (hmidT.const_mul (8 * c * D))).add (htailT.const_mul (8 * c * D * P * G))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun x => ?_
    rw [hU]
    ring
  -- squeeze the zero weight under the majorant
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUT ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_nonneg (Real.exp_nonneg _) (tsum_nonneg fun q => zeroShortWeight_nonneg (by linarith)
      (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)) _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hmaj := tsum_zeroShortWeight_le w hx hu.le hA0 hA4 hδ.le hc hD hT₀1 hPb hdens' hfree'
      hw0 hwanti
    have h4 := four_mul_ceil_rpow_le hx
    have hL := Real.log_nonneg hx
    have hX1 : 1 ≤ x ^ (2 * u) := Real.one_le_rpow hx (by linarith)
    have hlX := Real.log_nonneg hX1
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hG0 : 0 ≤ G := by
      rw [hG]
      have : (2 : ℝ) ^ (-(c₁ / 8)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have : 0 < 1 - (2 : ℝ) ^ (-(c₁ / 8)) := by linarith
      positivity
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    have hbr : 0 ≤ c * D * (H₁ x + P * x ^ (-(u * c₁ / 4)) * G) := by
      rw [hH₁]
      dsimp only
      have : 0 ≤ x ^ (-(δ * w (x ^ (2 * u)))) := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ x ^ (-(u * c₁ / 4)) := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ c := by linarith
      positivity
    have hle := le_trans hmaj (majorant_rearrange_le hbr h4)
    exact mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)

end

end RHTower
