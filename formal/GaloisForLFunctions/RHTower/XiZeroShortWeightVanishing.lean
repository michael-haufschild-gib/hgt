import GaloisForLFunctions.RHTower.XiZeroShortWeightDyadic
import GaloisForLFunctions.RHTower.XiZeroFreeHeightBox
import GaloisForLFunctions.RHTower.ZetaZeroDensityEightThirds

/-!
# The weighted zero sum vanishes below the exponent `3/8`

For `0 < u < 3/8` and `c ≥ 1`,

`Σ_ρ x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|)) → 0`   as `x → ∞`.

Take `A = 8/3 + (3 - 8u)/8`, so that `uA < 1` and `A < 4`.  The zero-density estimate with exponent
`A` and the Route-T zero-free region feed the dyadic majorant.  Its three parts vanish:

* the finitely many zeros below the density threshold contribute `x^{β-1} → 0`;
* shells below `x^{2u}` contribute at most `(3L)^{B+2} exp(-κ L^{1/10}/(1 + log 4L)²)` with
  `L = log x`, which tends to `0` because `exp(-κ L^{1/20}) ≤ m!/(κ^m L^{m/20})`;
* shells above `x^{2u}` contribute `O((log x) x^{-u(2-A/2)/4})`.
-/

namespace RHTower

noncomputable section

open Complex Filter Topology RHTower.Sieve

theorem exp_neg_le_factorial_div {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Real.exp (-t) ≤ (m.factorial : ℝ) / t ^ m := by
  have h := Real.pow_div_factorial_le_exp t ht.le m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos t) (by positivity)]
  rw [div_le_iff₀ hf] at h
  linarith

/-- Eventually `(1 + log 4L)² ≤ L^{1/20}`. -/
theorem eventually_one_add_log_four_sq_le :
    ∀ᶠ L : ℝ in atTop, (1 + Real.log (4 * L)) ^ 2 ≤ L ^ (1 / 20 : ℝ) := by
  have ho := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 20)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [ho, eventually_ge_atTop (12 : ℝ)] with L hL hL12
  have hL0 : 0 < L := by linarith
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogL : Real.log 4 + 1 ≤ Real.log L := by
    have h12 : Real.log 12 ≤ Real.log L := Real.log_le_log (by norm_num) hL12
    have : Real.log 12 = Real.log 4 + Real.log 3 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    linarith
  have hlogL0 : 0 ≤ Real.log L := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have h4 : 1 + Real.log (4 * L) ≤ 2 * Real.log L := by
    rw [Real.log_mul (by norm_num) hL0.ne']
    linarith
  have h14 : 0 ≤ 1 + Real.log (4 * L) := by
    rw [Real.log_mul (by norm_num) hL0.ne']
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogL0 _),
    abs_of_nonneg (Real.rpow_nonneg hL0.le _), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] at hL
  nlinarith

/-- **The polylogarithm against the zero-free saving.** -/
theorem tendsto_pow_mul_exp_neg_log_ratio (n : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L : ℝ => (3 * L) ^ n
      * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2))) atTop (𝓝 0) := by
  set m : ℕ := 20 * (n + 1) with hm
  set K : ℝ := 3 ^ n * (m.factorial : ℝ) / κ ^ m with hK
  have hup : Tendsto (fun L : ℝ => K / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    positivity
  · filter_upwards [eventually_one_add_log_four_sq_le, eventually_ge_atTop (12 : ℝ)] with L hQ hL
    have hL0 : 0 < L := by linarith
    have hQ0 : 0 < (1 + Real.log (4 * L)) ^ 2 := by
      have : 0 ≤ Real.log (4 * L) := Real.log_nonneg (by linarith)
      positivity
    have hL20 : 0 < L ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hL0 _
    -- the exponent is at least `κ L^{1/20}`
    have hratio : L ^ (1 / 20 : ℝ) ≤ L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2 := by
      rw [le_div_iff₀ hQ0]
      have h10 : L ^ (1 / 10 : ℝ) = L ^ (1 / 20 : ℝ) * L ^ (1 / 20 : ℝ) := by
        rw [← Real.rpow_add hL0]
        norm_num
      rw [h10]
      exact mul_le_mul_of_nonneg_left hQ hL20.le
    have hexp : Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2))
        ≤ Real.exp (-(κ * L ^ (1 / 20 : ℝ))) := by
      rw [Real.exp_le_exp]
      nlinarith
    have hfac := exp_neg_le_factorial_div (mul_pos hκ hL20) m
    have hpow : (κ * L ^ (1 / 20 : ℝ)) ^ m = κ ^ m * L ^ (n + 1) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 20 : ℝ)), ← Real.rpow_mul hL0.le, hm]
      congr 1
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [hpow] at hfac
    have hLn : (0 : ℝ) < (3 * L) ^ n := by positivity
    calc (3 * L) ^ n * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2))
        ≤ (3 * L) ^ n * ((m.factorial : ℝ) / (κ ^ m * L ^ (n + 1))) :=
          mul_le_mul_of_nonneg_left (le_trans hexp hfac) hLn.le
      _ = K / L := by
          rw [hK, mul_pow, pow_succ]
          field_simp

/-- `(log x + 2) x^{-a} → 0`. -/
theorem tendsto_log_add_two_mul_rpow_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x + 2) * x ^ (-a)) atTop (𝓝 0) := by
  have hup : Tendsto (fun x : ℝ => 6 / a ^ 2 / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have := Real.log_nonneg hx
    have : 0 ≤ x ^ (-a) := Real.rpow_nonneg (by linarith) _
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 2)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 2) hx
    have hL : 2 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      exact hx
    have hL0 : 0 < Real.log x := by linarith
    have hfac := exp_neg_le_factorial_div (mul_pos ha hL0) 2
    have hrp : x ^ (-a) = Real.exp (-(a * Real.log x)) := by
      rw [Real.rpow_def_of_pos hx0]
      ring_nf
    rw [hrp]
    have hf2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hf2] at hfac
    calc (Real.log x + 2) * Real.exp (-(a * Real.log x))
        ≤ (Real.log x + 2) * (2 / (a * Real.log x) ^ 2) :=
          mul_le_mul_of_nonneg_left hfac (by linarith)
      _ ≤ 6 / a ^ 2 / Real.log x := by
          rw [mul_pow, div_div, mul_div_assoc']
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith

theorem four_mul_ceil_rpow_le {x : ℝ} (hx : 1 ≤ x) :
    4 * ((⌈Real.log x⌉₊ + 1 : ℕ) : ℝ) * x ^ (1 / (2 * ((⌈Real.log x⌉₊ + 1 : ℕ) : ℝ)))
      ≤ 8 * (Real.log x + 2) := by
  have hx0 : 0 < x := by linarith
  have hL := Real.log_nonneg hx
  set M : ℝ := ((⌈Real.log x⌉₊ + 1 : ℕ) : ℝ) with hM
  have hM1 : M ≤ Real.log x + 2 := by
    rw [hM]
    push_cast
    linarith [Nat.ceil_lt_add_one hL]
  have hLM : Real.log x ≤ M := by
    rw [hM]
    push_cast
    linarith [Nat.le_ceil (Real.log x)]
  have hM0 : 0 < M := by rw [hM]; positivity
  have hhalf : Real.exp (1 / 2) ≤ 2 := by
    by_contra h
    push Not at h
    have h2 : (2 : ℝ) * 2 < Real.exp (1 / 2) * Real.exp (1 / 2) :=
      mul_lt_mul'' h h (by norm_num) (by norm_num)
    rw [← Real.exp_add] at h2
    norm_num at h2
    have := Real.exp_one_lt_d9
    linarith
  have hxp : x ^ (1 / (2 * M)) ≤ 2 := by
    rw [Real.rpow_def_of_pos hx0]
    refine le_trans (Real.exp_le_exp.mpr ?_) hhalf
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hxp0 : 0 ≤ x ^ (1 / (2 * M)) := Real.rpow_nonneg hx0.le _
  nlinarith

theorem majorant_rearrange_le {S M xM c D H P xa G L : ℝ} (hbr : 0 ≤ c * D * (H + P * xa * G))
    (h4 : 4 * M * xM ≤ 8 * (L + 2)) :
    S + 4 * M * c * D * xM * (H + P * xa * G)
      ≤ S + 8 * c * D * ((L + 2) * H) + 8 * c * D * P * G * ((L + 2) * xa) := by
  have e1 : 4 * M * c * D * xM * (H + P * xa * G) = (4 * M * xM) * (c * D * (H + P * xa * G)) := by
    ring
  have e2 : S + 8 * c * D * ((L + 2) * H) + 8 * c * D * P * G * ((L + 2) * xa)
      = S + (8 * (L + 2)) * (c * D * (H + P * xa * G)) := by ring
  rw [e1, e2]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h4 hbr)

/-- **The weighted zero sum vanishes.**  For `0 < u < 3/8` and `c ≥ 1`,
`Σ_ρ x^{β-1} min(1, c x^{2u}/(|ρ||1-ρ|)) → 0`. -/
theorem tendsto_tsum_zeroShortWeight {u c : ℝ} (hu : 0 < u) (hu' : u < 3 / 8) (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ => ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ))
      atTop (𝓝 0) := by
  set ε : ℝ := (3 - 8 * u) / 8 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  obtain ⟨T₀d, hdens⟩ := exists_zeroHeightBox_ncard_le hε0 hε1
  obtain ⟨Ap, T₁, hT₁, hfree⟩ := exists_zeroHeightBox_zeroFree
  have hD : 0 ≤ zeroDensityConstant := by
    unfold zeroDensityConstant classCountConstant
    positivity
  generalize zeroDensityConstant = D at hdens hD
  generalize classCountLogExponent + 4 = B at hdens
  set A : ℝ := 8 / 3 + ε with hA
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hA4 : A < 4 := by rw [hA, hε]; linarith
  have hδ : 0 < 1 - u * A := by
    have : 1 - u * A = (3 - 8 * u) * (1 / 3 - u / 8) := by rw [hA, hε]; ring
    rw [this]
    exact mul_pos (by linarith) (by linarith)
  set δ := 1 - u * A with hδdef
  set c₁ : ℝ := 2 - A / 2 with hc₁
  have hc₁0 : 0 < c₁ := by rw [hc₁]; linarith
  set T₀ : ℝ := max (max T₀d T₁) 1 with hT₀
  have hT₀1 : 1 ≤ T₀ := le_max_right _ _
  set w : ℝ → ℝ := fun T => routeTWidthPolylogLower Ap (4 * T / 3) with hw
  set P : ℝ := (1 + (B + 1) / (c₁ / 4)) ^ B with hP
  have hPb : ∀ T : ℝ, 1 ≤ T → (1 + Real.log T) ^ B ≤ P * T ^ (c₁ / 4) :=
    fun T hT => one_add_log_pow_le_rpow B (by positivity) hT
  have hdens' : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ)) :=
    fun T hT σ h1 h2 => hdens T (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT) σ h1 h2
  have hfree' : ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ, (zeroHeightBox σ T).Nonempty → σ ≤ 1 - w T :=
    fun T hT σ hN => hfree T (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT) σ hN
  have hw0 : ∀ T : ℝ, 0 ≤ w T := fun T => (routeTWidthPolylogLower_pos Ap _).le
  have hwanti : ∀ T T' : ℝ, T₀ ≤ T → T ≤ T' → w T' ≤ w T := by
    intro T T' hT hTT'
    have hT0 : 0 ≤ T := by linarith
    refine routeTWidthPolylogLower_antitone ?_
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  set Low := (finite_xiOrdinateWindow T₀ 0).toFinset with hLow
  set C : ℝ := 10 * routeTZeroFreeDeltaEnvelopeConstant Ap with hC
  have hC0 : 0 < C := by
    rw [hC]
    have := routeTZeroFreeDeltaEnvelopeConstant_pos Ap
    positivity
  set κ : ℝ := δ / (4 * C) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  set G : ℝ := 1 / (1 - (2 : ℝ) ^ (-(c₁ / 8))) with hG
  set H₁ : ℝ → ℝ := fun x => (1 + Real.log (x ^ (2 * u)) / Real.log 2)
      * (1 + Real.log (x ^ (2 * u))) ^ B * x ^ (-(δ * w (x ^ (2 * u)))) with hH₁
  set U : ℝ → ℝ := fun x => ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1)
      + 8 * c * D * ((Real.log x + 2) * H₁ x)
      + 8 * c * D * P * G * ((Real.log x + 2) * x ^ (-(u * c₁ / 4))) with hU
  -- the majorant tends to zero
  have hLowT : Tendsto (fun x : ℝ => ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum Low (f := fun (q : XiZeroCopy) (x : ℝ) => x ^ ((q.1 : ℂ).re - 1))
      (a := fun _ => (0 : ℝ)) (x := atTop) (fun q _ => by
        have hpos : 0 < 1 - (q.1 : ℂ).re := by linarith [xiZeroCopy_re_lt_one q]
        have := tendsto_rpow_neg_atTop hpos
        refine this.congr fun x => ?_
        congr 1
        ring)
    simpa using h
  have hmidT : Tendsto (fun x : ℝ => (Real.log x + 2) * H₁ x) atTop (𝓝 0) := by
    have hcomp := (tendsto_pow_mul_exp_neg_log_ratio (B + 2) hκ0).comp Real.tendsto_log_atTop
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
    · filter_upwards [eventually_ge_atTop (Real.exp 12)] with x hx
      have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 12) hx
      have hL12 : 12 ≤ Real.log x := by
        rw [Real.le_log_iff_exp_le hx0]
        exact hx
      have hx1 : 1 ≤ x := by
        have := Real.add_one_le_exp 12
        linarith
      set L := Real.log x with hLdef
      have hlogX : Real.log (x ^ (2 * u)) = 2 * u * L := by rw [Real.log_rpow hx0]
      have hwid := rpow_neg_width_le_exp (A := Ap) hx1 (by linarith) hu.le (by linarith) hδ.le
      rw [← hC, ← hκ, ← hLdef] at hwid
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      have hf1 : L + 2 ≤ 3 * L := by linarith
      have hf2 : 1 + Real.log (x ^ (2 * u)) / Real.log 2 ≤ 3 * L := by
        rw [hlogX]
        have : 2 * u * L / Real.log 2 ≤ 2 * L := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        linarith
      have hf3 : 1 + Real.log (x ^ (2 * u)) ≤ 3 * L := by rw [hlogX]; nlinarith
      have hf3' : 0 ≤ 1 + Real.log (x ^ (2 * u)) := by rw [hlogX]; positivity
      have hf2' : 0 ≤ 1 + Real.log (x ^ (2 * u)) / Real.log 2 := by
        rw [hlogX]
        have : 0 ≤ 2 * u * L / Real.log 2 := by positivity
        linarith
      have hE0 : 0 ≤ x ^ (-(δ * w (x ^ (2 * u)))) := Real.rpow_nonneg hx0.le _
      have hwx : w (x ^ (2 * u)) = routeTWidthPolylogLower Ap (4 * x ^ (2 * u) / 3) := rfl
      rw [hH₁]
      dsimp only
      rw [hwx] at hE0 ⊢
      calc (L + 2) * ((1 + Real.log (x ^ (2 * u)) / Real.log 2) * (1 + Real.log (x ^ (2 * u))) ^ B
            * x ^ (-(δ * routeTWidthPolylogLower Ap (4 * x ^ (2 * u) / 3))))
          ≤ (3 * L) * ((3 * L) * (3 * L) ^ B
            * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2))) := by
            gcongr
        _ = (3 * L) ^ (B + 2) * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2)) := by
            ring
  have htailT : Tendsto (fun x : ℝ => (Real.log x + 2) * x ^ (-(u * c₁ / 4))) atTop (𝓝 0) :=
    tendsto_log_add_two_mul_rpow_neg (by positivity)
  have hUT : Tendsto U atTop (𝓝 0) := by
    have h := (hLowT.add (hmidT.const_mul (8 * c * D))).add (htailT.const_mul (8 * c * D * P * G))
    simpa [hU] using h
  -- squeeze
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUT ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact tsum_nonneg fun q => zeroShortWeight_nonneg (by linarith)
      (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)) _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hmaj := tsum_zeroShortWeight_le w hx hu.le hA0 hA4 hδ.le hc hD hT₀1 hPb hdens' hfree'
      hw0 hwanti
    refine le_trans hmaj ?_
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
    have hP0 : 0 ≤ P := by
      rw [hP]
      positivity
    have hbr : 0 ≤ c * D * (H₁ x + P * x ^ (-(u * c₁ / 4)) * G) := by
      rw [hH₁]
      dsimp only
      have : 0 ≤ x ^ (-(δ * w (x ^ (2 * u)))) := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ x ^ (-(u * c₁ / 4)) := Real.rpow_nonneg (by linarith) _
      have : 0 ≤ c := by linarith
      positivity
    exact majorant_rearrange_le hbr h4

end

end RHTower
