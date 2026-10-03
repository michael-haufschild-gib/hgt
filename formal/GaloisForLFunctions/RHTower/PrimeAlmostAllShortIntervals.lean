import GaloisForLFunctions.RHTower.ChebyshevMultiplicativeWindowZeroSum
import GaloisForLFunctions.RHTower.ZetaZeroSumMeanSquare
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths
import GaloisForLFunctions.RHTower.XiThreeHalvesSummability

/-!
# Primes in almost all intervals `(x, x + x^θ]`, `θ > 1/6`

Fix `1/6 < θ < 1`, `h = X^θ`, `δ = h/(2X)`, `η = δ/8`.  For `x ∈ [X, 2X]` the multiplicative window
bound `psi_mul_window_ge` gives

`ψ(x + h) - ψ(x) ≥ (3/4)δx - 4/(ηx²) + Re Σ_ρ x^ρ d_ρ`.

Split the zeros at `|γ| = X⁴`.  The far zeros cost at most `72Σ/(ηX)`, `Σ = Σ_ρ |ρ-½|^{-3/2}`
(`xiSpectralPoint_inv_three_halves_summable`).  The near ones form a finite sum `D(x)`, whose mean
square over `[X, 2X]` is at most `4W Σ_ρ |d_ρ|² X^{2β-2}` (`integral_norm_sq_zeroSum_div_cube_le`)
with `W ≪ log² X` (`sum_inv_one_add_abs_im_sub_le`).  Since `|d_ρ|² ≤ 4δ² min(1, 48/(δ²|ρ||1-ρ|))`,

`Σ_ρ |d_ρ|² X^{2β-2} ≤ 4δ² Σ_ρ (X²)^{β-1} min(1, 192 (X²)^{1-θ}/(|ρ||1-ρ|))`,

the zero weight of `XiZeroShortWeightDyadic` at `x = X²`, `u = (1-θ)/2 < 5/12`.  With the density
exponent `12/5 + ε` it vanishes faster than any power of `log X`
(`tendsto_logPow_mul_tsum_zeroShortWeight_seven_twelfths`).  Chebyshev's inequality then bounds the
measure of the `x ∈ [X, 2X]` with `ψ(x + h) - ψ(x) < h/4` by `o(X)`
(`tendsto_volume_psi_short_deficit`).
-/

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory RHTower.Sieve

/-- `(log x + 2)^k x^{-a} → 0`. -/
theorem tendsto_log_add_two_pow_mul_rpow_neg (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => (Real.log x + 2) ^ k * x ^ (-a)) atTop (𝓝 0) := by
  induction k generalizing a with
  | zero => simpa using tendsto_rpow_neg_atTop ha
  | succ k ih =>
    have h := (tendsto_log_add_two_mul_rpow_neg (half_pos ha)).mul (ih (half_pos ha))
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show -a = -(a / 2) + -(a / 2) by ring, Real.rpow_add hx, pow_succ]
    ring

/-- **The weighted zero sum vanishes faster than every power of `log x`** under any density
exponent `A < 4` with `uA < 1`. -/
theorem tendsto_logPow_mul_tsum_zeroShortWeight_of_density (k : ℕ) {A u c D T₀d : ℝ} {B : ℕ}
    (hA0 : 0 ≤ A) (hA4 : A < 4) (hu : 0 < u) (hu2 : u ≤ 1 / 2) (huA : u * A < 1) (hc : 1 ≤ c)
    (hD : 0 ≤ D)
    (hdens : ∀ T : ℝ, T₀d ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
      ((zeroHeightBox σ T).ncard : ℝ) ≤ D * (1 + Real.log T) ^ B * T ^ (A * (1 - σ))) :
    Tendsto (fun x : ℝ => (Real.log x + 2) ^ k
      * ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)) atTop (𝓝 0) := by
  obtain ⟨Ap, T₁, hT₁, hfree⟩ := exists_zeroHeightBox_zeroFree
  have hδ : 0 < 1 - u * A := by linarith
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
  have hLowT : Tendsto (fun x : ℝ => (Real.log x + 2) ^ k * ∑ q ∈ Low, x ^ ((q.1 : ℂ).re - 1))
      atTop (𝓝 0) := by
    simp_rw [Finset.mul_sum]
    have h := tendsto_finsetSum Low
      (f := fun (q : XiZeroCopy) (x : ℝ) => (Real.log x + 2) ^ k * x ^ ((q.1 : ℂ).re - 1))
      (a := fun _ => (0 : ℝ)) (x := atTop) (fun q _ => by
        have hpos : 0 < 1 - (q.1 : ℂ).re := by linarith [xiZeroCopy_re_lt_one q]
        refine (tendsto_log_add_two_pow_mul_rpow_neg k hpos).congr fun x => ?_
        congr 2
        ring)
    simpa using h
  have hmidT : Tendsto (fun x : ℝ => (Real.log x + 2) ^ (k + 1) * H₁ x) atTop (𝓝 0) := by
    have hcomp := (tendsto_pow_mul_exp_neg_log_ratio (B + 2 + k) hκ0).comp Real.tendsto_log_atTop
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
      have hwid := rpow_neg_width_le_exp (A := Ap) hx1 (by linarith) hu.le hu2 hδ.le
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
      have hL2 : 0 ≤ L + 2 := by linarith
      rw [hH₁]
      dsimp only
      rw [hwx] at hE0 ⊢
      calc (L + 2) ^ (k + 1) * ((1 + Real.log (x ^ (2 * u)) / Real.log 2)
            * (1 + Real.log (x ^ (2 * u))) ^ B
            * x ^ (-(δ * routeTWidthPolylogLower Ap (4 * x ^ (2 * u) / 3))))
          ≤ (3 * L) ^ (k + 1) * ((3 * L) * (3 * L) ^ B
            * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2))) := by
            gcongr
        _ = (3 * L) ^ (B + 2 + k)
              * Real.exp (-κ * (L ^ (1 / 10 : ℝ) / (1 + Real.log (4 * L)) ^ 2)) := by
            ring
  have htailT : Tendsto (fun x : ℝ => (Real.log x + 2) ^ (k + 1) * x ^ (-(u * c₁ / 4))) atTop
      (𝓝 0) := tendsto_log_add_two_pow_mul_rpow_neg (k + 1) (by positivity)
  have hUT : Tendsto (fun x : ℝ => (Real.log x + 2) ^ k * U x) atTop (𝓝 0) := by
    have h := (hLowT.add (hmidT.const_mul (8 * c * D))).add (htailT.const_mul (8 * c * D * P * G))
    simp only [mul_zero, add_zero] at h
    refine h.congr fun x => ?_
    rw [hU]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUT ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hL : 0 ≤ Real.log x + 2 := by linarith [Real.log_nonneg hx]
    exact mul_nonneg (pow_nonneg hL k) (tsum_nonneg fun q => zeroShortWeight_nonneg (by linarith)
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
    have hle := le_trans hmaj (majorant_rearrange_le hbr h4)
    have hLk : 0 ≤ (Real.log x + 2) ^ k := pow_nonneg (by linarith) k
    exact mul_le_mul_of_nonneg_left hle hLk

/-- **The weighted zero sum vanishes faster than every power of `log x` below `5/12`.** -/
theorem tendsto_logPow_mul_tsum_zeroShortWeight_seven_twelfths (k : ℕ) {u c : ℝ} (hu : 0 < u)
    (hu' : u < 5 / 12) (hc : 1 ≤ c) :
    Tendsto (fun x : ℝ => (Real.log x + 2) ^ k
      * ∑' q : XiZeroCopy, zeroShortWeight x (c * x ^ (2 * u)) (q.1 : ℂ)) atTop (𝓝 0) := by
  set ε : ℝ := min 1 ((1 / u - 12 / 5) / 2) with hε
  have hgap : 0 < 1 / u - 12 / 5 := by
    rw [sub_pos, lt_div_iff₀ hu]
    linarith
  have hε0 : 0 < ε := lt_min one_pos (by linarith)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεle : ε ≤ (1 / u - 12 / 5) / 2 := min_le_right _ _
  obtain ⟨D, hD, T₀, -, hdens⟩ := exists_zeroHeightBox_ncard_le_twelve_fifths hε0 hε1
  have huA : u * (12 / 5 + ε) < 1 := by
    have h1 : u * (12 / 5 + ε) ≤ u * (12 / 5 + (1 / u - 12 / 5) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hu.le
    have h2 : u * (12 / 5 + (1 / u - 12 / 5) / 2) = (1 + 12 * u / 5) / 2 := by
      field_simp
      ring
    linarith
  exact tendsto_logPow_mul_tsum_zeroShortWeight_of_density k (by positivity) (by linarith) hu
    (by linarith) huA hc hD hdens

/-- A far zero: `1/γ² ≤ (3/√T)|ρ - ½|^{-3/2}` once `T < |γ|` and `1 ≤ T`. -/
theorem inv_sq_im_le_spectral {T : ℝ} (hT : 1 ≤ T) {q : XiZeroCopy}
    (hq : T < |(q.1 : ℂ).im|) :
    1 / (q.1 : ℂ).im ^ 2
      ≤ 3 / Real.sqrt T * (1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) := by
  set g := |(q.1 : ℂ).im| with hg
  set r := ‖xiSpectralPoint q‖ with hr
  have hg1 : 1 < g := lt_of_le_of_lt hT hq
  have hrg : g ≤ r := by
    rw [hr, norm_xiSpectralPoint]
    have := Complex.abs_im_le_norm ((q.1 : ℂ) - 1 / 2)
    simpa using this
  have hr2 : r ≤ 2 * g := by
    rw [hr, norm_xiSpectralPoint]
    have h1 := Complex.norm_le_abs_re_add_abs_im ((q.1 : ℂ) - 1 / 2)
    have hre : |((q.1 : ℂ) - 1 / 2).re| ≤ 1 / 2 := by
      simp only [Complex.sub_re]
      norm_num
      rw [abs_le]
      constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
    have him : |((q.1 : ℂ) - 1 / 2).im| = g := by simp [hg]
    linarith
  have hr0 : 0 < r := by linarith
  have hsT : Real.sqrt T ≤ Real.sqrt g := Real.sqrt_le_sqrt hq.le
  have hsr : Real.sqrt r ≤ Real.sqrt 2 * Real.sqrt g := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hr2
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hgg : Real.sqrt g * Real.sqrt g = g := Real.mul_self_sqrt (by linarith)
  have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hsr0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hsg0 : 0 ≤ Real.sqrt g := Real.sqrt_nonneg g
  have hkey : Real.sqrt T * (r * Real.sqrt r) ≤ 3 * g ^ 2 := by
    calc Real.sqrt T * (r * Real.sqrt r)
        ≤ Real.sqrt g * ((2 * g) * (Real.sqrt 2 * Real.sqrt g)) := by
          gcongr
      _ = 2 * Real.sqrt 2 * g * (Real.sqrt g * Real.sqrt g) := by ring
      _ ≤ 2 * (3 / 2) * g * g := by rw [hgg]; gcongr
      _ = 3 * g ^ 2 := by ring
  have hsq : (q.1 : ℂ).im ^ 2 = g ^ 2 := by rw [hg, sq_abs]
  rw [hsq, div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **The far zeros.**  With `F` the zeros of ordinate at most `T` (`1 ≤ T`), `1 ≤ x`,
`0 < 2η ≤ δ ≤ 1`: `|Σ_{ρ ∉ F} x^ρ d_ρ| ≤ 36x/(η√T) Σ_ρ |ρ-½|^{-3/2}`. -/
theorem norm_tsum_compl_mulWindow_le {x T δ η : ℝ} (hx : 1 ≤ x) (hT : 1 ≤ T) (hη : 0 < η)
    (hηδ : 2 * η ≤ δ) (hδ : δ ≤ 1) :
    ‖∑' q : ↑(((finite_xiOrdinateWindow T 0).toFinset : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ,
        (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ) * multWindowCoeff δ η ((q : XiZeroCopy).1 : ℂ)‖
      ≤ 36 * x / (η * Real.sqrt T)
        * ∑' q : XiZeroCopy, 1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖) := by
  set F : Finset XiZeroCopy := (finite_xiOrdinateWindow T 0).toFinset with hF
  set S : XiZeroCopy → ℝ := fun q => 1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
    with hS
  have hSs : Summable S := xiSpectralPoint_inv_three_halves_summable
  have hS0 : ∀ q, 0 ≤ S q := fun q => by rw [hS]; positivity
  have hx0 : 0 < x := by linarith
  have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  set M : ℝ := 36 * x / (η * Real.sqrt T) with hM
  have hpt : ∀ q : XiZeroCopy, q ∉ F →
      ‖(x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ)‖ ≤ M * S q := by
    intro q hq
    have hγ : T < |(q.1 : ℂ).im| := by
      rw [hF, Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff, sub_zero] at hq
      exact lt_of_not_ge hq
    have hρ0 := xiZeroCopy_re_pos q
    have hρ1 := xiZeroCopy_re_lt_one q
    have hd := norm_multWindowCoeff_le_div hη hηδ hδ hρ0 hρ1
    have hP : (q.1 : ℂ).im ^ 2 ≤ ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ := by
      have h1 := Complex.abs_im_le_norm (q.1 : ℂ)
      have h2 := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
      have h3 : |(1 - (q.1 : ℂ)).im| = |(q.1 : ℂ).im| := by simp
      rw [h3] at h2
      rw [← sq_abs]
      nlinarith [abs_nonneg (q.1 : ℂ).im]
    have hγ1 : 1 < |(q.1 : ℂ).im| := lt_of_le_of_lt hT hγ
    have hγ2 : 0 < (q.1 : ℂ).im ^ 2 := by
      rw [← sq_abs]
      positivity
    have hxp : ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      calc x ^ (q.1 : ℂ).re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hρ1.le
        _ = x := Real.rpow_one x
    have hsp := inv_sq_im_le_spectral hT hγ
    rw [norm_mul]
    calc ‖(x : ℂ) ^ (q.1 : ℂ)‖ * ‖multWindowCoeff δ η (q.1 : ℂ)‖
        ≤ x * (12 / (η * (q.1 : ℂ).im ^ 2)) := by
          gcongr
          refine le_trans hd ?_
          gcongr
      _ = 12 * x / η * (1 / (q.1 : ℂ).im ^ 2) := by
          field_simp
      _ ≤ 12 * x / η * (3 / Real.sqrt T * S q) := by
          gcongr
      _ = M * S q := by
          rw [hM]
          field_simp
          ring
  set f : XiZeroCopy → ℂ := fun q => (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ) with hf
  have hsub : ∑' q : ↑((F : Set XiZeroCopy)ᶜ), f q = ∑' q, ((F : Set XiZeroCopy)ᶜ).indicator f q :=
    tsum_subtype _ f
  have hind : ∀ q : XiZeroCopy, ‖((F : Set XiZeroCopy)ᶜ).indicator f q‖ ≤ M * S q := by
    intro q
    by_cases hq : q ∈ F
    · rw [Set.indicator_of_notMem (by simpa using hq), norm_zero]
      exact mul_nonneg (by positivity) (hS0 q)
    · rw [Set.indicator_of_mem (by simpa using hq)]
      exact hpt q hq
  have hsumnorm : Summable fun q => ‖((F : Set XiZeroCopy)ᶜ).indicator f q‖ :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hind (hSs.mul_left M)
  change ‖∑' q : ↑((F : Set XiZeroCopy)ᶜ), f q‖ ≤ _
  rw [hsub]
  refine le_trans (norm_tsum_le_tsum_norm hsumnorm) ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hind hsumnorm (hSs.mul_left M)

/-- The multiplicative step `δ = X^θ/(2X)`. -/
def almostAllStep (θ X : ℝ) : ℝ := X ^ θ / (2 * X)

/-- The zeros of ordinate at most `X⁴`. -/
def almostAllLowZeros (X : ℝ) : Finset XiZeroCopy := (finite_xiOrdinateWindow (X ^ 4) 0).toFinset

/-- The near zero sum `D(x) = Σ_{|γ| ≤ X⁴} d_ρ x^ρ`. -/
def almostAllLowSum (θ X x : ℝ) : ℂ :=
  ∑ q ∈ almostAllLowZeros X,
    multWindowCoeff (almostAllStep θ X) (almostAllStep θ X / 8) (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)

/-- `Σ_ρ |ρ - ½|^{-3/2}`. -/
def xiSpectralThreeHalvesMass : ℝ :=
  ∑' q : XiZeroCopy, 1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)

theorem xiSpectralThreeHalvesMass_nonneg : 0 ≤ xiSpectralThreeHalvesMass :=
  tsum_nonneg fun q => by positivity

/-- **The pointwise bound.**  For `2 ≤ X`, `200(Σ + 1) ≤ X^θ` and `x ∈ [X, 2X]`:
`ψ(x + X^θ) - ψ(x) ≥ (5/16)X^θ - |D(x)|`. -/
theorem psi_short_ge_sub_norm_lowSum {θ X x : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hX : 2 ≤ X)
    (hh : 200 * (xiSpectralThreeHalvesMass + 1) ≤ X ^ θ) (hx : x ∈ Set.Icc X (2 * X)) :
    5 / 16 * X ^ θ - ‖almostAllLowSum θ X x‖ ≤ Chebyshev.psi (x + X ^ θ) - Chebyshev.psi x := by
  set h := X ^ θ with hhdef
  set δ := almostAllStep θ X with hδdef
  set η := δ / 8 with hηdef
  set Ms := xiSpectralThreeHalvesMass with hMs
  have hMs0 : 0 ≤ Ms := xiSpectralThreeHalvesMass_nonneg
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hx0 : 0 < x := by linarith [hx.1]
  have hx2 : 2 ≤ x := le_trans hX hx.1
  have hh200 : 200 ≤ h := by nlinarith
  have hhX : h ≤ X := Real.rpow_le_self_of_one_le hX1 hθ1.le
  have hδ : δ = h / (2 * X) := rfl
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η ≤ δ := by rw [hηdef]; linarith
  have hδX : δ * X = h / 2 := by rw [hδ]; field_simp
  have hηX : η * X = h / 16 := by rw [hηdef]; linarith
  have hδx : δ * x ≤ h := by nlinarith [hx.2]
  have hmono : Chebyshev.psi (x + δ * x) ≤ Chebyshev.psi (x + h) :=
    Chebyshev.psi_mono (by linarith)
  have hlow := psi_mul_window_ge hx2 hη0 h2η hδ1
  -- the zero sum: near part plus far part
  set f : XiZeroCopy → ℂ := fun q => (x : ℂ) ^ (q.1 : ℂ) * multWindowCoeff δ η (q.1 : ℂ) with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded (summable_norm_inv_mul_one_sub.mul_left (12 * x / η))
      fun q => ?_
    have hd := norm_multWindowCoeff_le_div hη0 h2η hδ1 (xiZeroCopy_re_pos q)
      (xiZeroCopy_re_lt_one q)
    have hxp : ‖(x : ℂ) ^ (q.1 : ℂ)‖ ≤ x := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      exact Real.rpow_le_self_of_one_le (by linarith) (xiZeroCopy_re_lt_one q).le
    rw [norm_inv_mul_one_sub_eq, hf]
    dsimp only
    rw [norm_mul]
    calc ‖(x : ℂ) ^ (q.1 : ℂ)‖ * ‖multWindowCoeff δ η (q.1 : ℂ)‖
        ≤ x * (12 / (η * (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))) := by gcongr
      _ = 12 * x / η * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) := by
          field_simp
  have hsplit := hfs.sum_add_tsum_compl (s := almostAllLowZeros X)
  have hlowsum : ∑ q ∈ almostAllLowZeros X, f q = almostAllLowSum θ X x := by
    rw [almostAllLowSum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hf]
    exact mul_comm _ _
  have htail := norm_tsum_compl_mulWindow_le (x := x) (T := X ^ 4) (by linarith)
    (one_le_pow₀ hX1) hη0 h2η hδ1
  have hsq : Real.sqrt (X ^ 4) = X ^ 2 := by
    rw [show X ^ 4 = (X ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq] at htail
  change _ ≤ 36 * x / (η * X ^ 2) * Ms at htail
  set tail := ∑' q : ↑(((finite_xiOrdinateWindow (X ^ 4) 0).toFinset : Finset XiZeroCopy)
      : Set XiZeroCopy)ᶜ, (x : ℂ) ^ ((q : XiZeroCopy).1 : ℂ)
        * multWindowCoeff δ η ((q : XiZeroCopy).1 : ℂ) with htaildef
  have hre : -‖almostAllLowSum θ X x‖ - ‖tail‖ ≤ (∑' q : XiZeroCopy, f q).re := by
    rw [← hsplit, Complex.add_re, ← hlowsum]
    have h1 := Complex.abs_re_le_norm (∑ q ∈ almostAllLowZeros X, f q)
    have h2 := Complex.abs_re_le_norm tail
    have h3 := neg_abs_le (∑ q ∈ almostAllLowZeros X, f q).re
    have h4 := neg_abs_le tail.re
    have : (∑' q : ↑((almostAllLowZeros X : Set XiZeroCopy)ᶜ), f q) = tail := rfl
    rw [this]
    linarith
  -- the far part is small
  have htail' : ‖tail‖ ≤ 1152 * Ms / h := by
    refine le_trans htail ?_
    have hxX : x ≤ 2 * X := hx.2
    have e1 : 36 * x / (η * X ^ 2) * Ms ≤ 36 * (2 * X) / (η * X ^ 2) * Ms := by gcongr
    have e2 : 36 * (2 * X) / (η * X ^ 2) * Ms = 1152 * Ms / h := by
      have : η * X ^ 2 = h / 16 * X := by rw [← hηX]; ring
      rw [this]
      field_simp
      ring
    linarith
  -- the trivial-zero term is small
  have htriv : 4 / (η * x ^ 2) ≤ 64 / (h * X) := by
    have hxx : X ^ 2 ≤ x ^ 2 := by nlinarith [hx.1]
    have : η * X ^ 2 = h / 16 * X := by rw [← hηX]; ring
    calc 4 / (η * x ^ 2) ≤ 4 / (η * X ^ 2) := by gcongr
      _ = 64 / (h * X) := by rw [this]; field_simp; ring
  have hmain : (δ - 2 * η) * x ≥ 3 / 8 * h := by
    have : δ - 2 * η = 3 / 4 * δ := by rw [hηdef]; ring
    rw [this]
    nlinarith [hx.1]
  have hsmall : 64 / (h * X) + 1152 * Ms / h ≤ h / 16 := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by norm_num)]
    have h2 : 200 * (Ms + 1) * 200 ≤ h * h := by nlinarith
    have h3 : 512 + 18432 * Ms ≤ h * h := by linarith
    have h4 : 1024 + 18432 * X * Ms ≤ h * h * X := by
      have hm := mul_le_mul_of_nonneg_right h3 hX0.le
      calc 1024 + 18432 * X * Ms ≤ 512 * X + 18432 * X * Ms := by linarith
        _ = (512 + 18432 * Ms) * X := by ring
        _ ≤ h * h * X := hm
    have hpos : 0 ≤ h := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hpos
    calc (64 * h + h * X * (1152 * Ms)) * 16 = h * (1024 + 18432 * X * Ms) := by ring
      _ ≤ h * (h * h * X) := h5
      _ = h * (h * X * h) := by ring
  linarith

/-- The harmonic weight `W(X) = 32(|K| + log(3X⁴ + 4))(1 + log(2X⁴ + 1))`. -/
def almostAllHarmonicWeight (X : ℝ) : ℝ :=
  32 * (|xiLineTwoLogDerivConstant| + Real.log (3 * X ^ 4 + 4)) * (1 + Real.log (2 * X ^ 4 + 1))

/-- **Chebyshev's inequality on `[X, 2X]`.**  The measure of the `x ∈ [X, 2X]` with
`ψ(x + X^θ) - ψ(x) < X^θ/4` is at most `8192 W(X) X Σ_ρ zeroShortWeight(X², 192(X²)^{1-θ})`. -/
theorem volume_psi_short_deficit_le {θ X : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hX : 2 ≤ X)
    (hh : 200 * (xiSpectralThreeHalvesMass + 1) ≤ X ^ θ) :
    (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ Chebyshev.psi (x + X ^ θ) - Chebyshev.psi x < X ^ θ / 4}).toReal
      ≤ 8192 * almostAllHarmonicWeight X * X
        * ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2)))
            (q.1 : ℂ) := by
  set h := X ^ θ with hhdef
  set δ := almostAllStep θ X with hδdef
  set η := δ / 8 with hηdef
  set F := almostAllLowZeros X with hF
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hMs0 := xiSpectralThreeHalvesMass_nonneg
  have hh200 : 200 ≤ h := by nlinarith
  have hhX : h ≤ X := Real.rpow_le_self_of_one_le hX1 hθ1.le
  have hδ : δ = h / (2 * X) := rfl
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have h2η : 2 * η ≤ δ := by rw [hηdef]; linarith
  set g : ℝ → ℝ := fun x => ‖almostAllLowSum θ X x‖ ^ 2 / x ^ 3 with hg
  set c : ℝ := (h / 16) ^ 2 / (2 * X) ^ 3 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  -- the exceptional set lies in a superlevel set of `g`
  have hsub : {x : ℝ | x ∈ Set.Icc X (2 * X)
      ∧ Chebyshev.psi (x + X ^ θ) - Chebyshev.psi x < X ^ θ / 4}
      ⊆ {x : ℝ | c ≤ g x} ∩ Set.Icc X (2 * X) := by
    rintro x ⟨hx, hlt⟩
    refine ⟨?_, hx⟩
    have hpt := psi_short_ge_sub_norm_lowSum hθ0 hθ1 hX hh hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hn : h / 16 ≤ ‖almostAllLowSum θ X x‖ := by linarith
    have hn2 : (h / 16) ^ 2 ≤ ‖almostAllLowSum θ X x‖ ^ 2 := by
      have : 0 ≤ h / 16 := by positivity
      nlinarith
    have hx3 : x ^ 3 ≤ (2 * X) ^ 3 := by
      have := hx.2
      gcongr
    show c ≤ ‖almostAllLowSum θ X x‖ ^ 2 / x ^ 3
    rw [hc]
    calc (h / 16) ^ 2 / (2 * X) ^ 3 ≤ (h / 16) ^ 2 / x ^ 3 := by gcongr
      _ ≤ ‖almostAllLowSum θ X x‖ ^ 2 / x ^ 3 := by gcongr
  -- Markov
  have hcontD : ContinuousOn (fun x : ℝ => almostAllLowSum θ X x) (Set.Icc X (2 * X)) := by
    refine continuousOn_finsetSum _ fun q _ => continuousOn_const.mul ?_
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (by linarith [hx.1]))
  have hcontg : ContinuousOn g (Set.Icc X (2 * X)) := by
    refine (hcontD.norm.pow 2).div (continuousOn_pow 3) fun x hx => ?_
    have : 0 < x := by linarith [hx.1]
    positivity
  have hgint : Integrable g (volume.restrict (Set.Icc X (2 * X))) :=
    hcontg.integrableOn_Icc
  have hg0 : 0 ≤ᵐ[volume.restrict (Set.Icc X (2 * X))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have : 0 < x := by linarith [hx.1]
    simp only [Pi.zero_apply, hg]
    positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hg0 hgint c
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Icc] at hmarkov
  have hint_eq : ∫ x, g x ∂(volume.restrict (Set.Icc X (2 * X))) = ∫ x in X..2 * X, g x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  rw [hint_eq] at hmarkov
  -- the mean square
  have hW : ∀ q ∈ F, ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|)
      ≤ almostAllHarmonicWeight X := by
    intro q hq
    have hmem : ∀ q' ∈ F, |(q'.1 : ℂ).im| ≤ X ^ 4 := by
      intro q' hq'
      rw [hF, almostAllLowZeros, Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff,
        sub_zero] at hq'
      exact hq'
    have hq4 := hmem q hq
    have hR : ∀ q' ∈ F, |(q'.1 : ℂ).im - (q.1 : ℂ).im| ≤ 2 * X ^ 4 := by
      intro q' hq'
      have := hmem q' hq'
      have := abs_sub (q'.1 : ℂ).im (q.1 : ℂ).im
      linarith
    have hharm := sum_inv_one_add_abs_im_sub_le F (t := (q.1 : ℂ).im) (by positivity) hR
    have hcomm : ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|)
        = ∑ q' ∈ F, 1 / (1 + |(q'.1 : ℂ).im - (q.1 : ℂ).im|) := by
      refine Finset.sum_congr rfl fun q' _ => ?_
      rw [abs_sub_comm]
    rw [hcomm]
    refine le_trans hharm ?_
    rw [almostAllHarmonicWeight]
    have hl : Real.log (|(q.1 : ℂ).im| + 2 * X ^ 4 + 4) ≤ Real.log (3 * X ^ 4 + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hl0 : 0 ≤ 1 + Real.log (2 * X ^ 4 + 1) := by
      have : 0 ≤ Real.log (2 * X ^ 4 + 1) :=
        Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 4) hX1])
      linarith
    gcongr
  have hms := integral_norm_sq_zeroSum_div_cube_le hX0 F
    (fun q => multWindowCoeff δ η (q.1 : ℂ)) hW
  -- each coefficient against the zero weight
  have hY : 192 * (X ^ 2) ^ (2 * ((1 - θ) / 2)) = 48 / δ ^ 2 := by
    have e1 : (X ^ 2) ^ (2 * ((1 - θ) / 2)) = X ^ 2 / h ^ 2 := by
      rw [hhdef, show 2 * ((1 - θ) / 2) = 1 - θ by ring, ← Real.rpow_natCast X 2,
        ← Real.rpow_mul hX0.le, ← Real.rpow_natCast (X ^ θ) 2, ← Real.rpow_mul hX0.le,
        ← Real.rpow_sub hX0]
      congr 1
      push_cast
      ring
    rw [e1, hδ]
    field_simp
    ring
  have hcoef : ∀ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 4 * δ ^ 2 * zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ) := by
    intro q _
    have hρ0 := xiZeroCopy_re_pos q
    have hρ1 := xiZeroCopy_re_lt_one q
    have hd1 := norm_multWindowCoeff_le_two_mul hη0 h2η hρ0 hρ1
    have hd2 := norm_multWindowCoeff_le_div hη0 h2η hδ1 hρ0 hρ1
    have hρne := xiZeroCopy_ne_zero q
    have hρ1ne : 1 - (q.1 : ℂ) ≠ 0 := xiZeroCopy_one_sub_ne_zero q
    set P := ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ with hP
    have hP0 : 0 < P := mul_pos (norm_pos_iff.mpr hρne) (norm_pos_iff.mpr hρ1ne)
    set d := ‖multWindowCoeff δ η (q.1 : ℂ)‖ with hd
    have hd0 : 0 ≤ d := norm_nonneg _
    have hd2' : d ≤ 96 / (δ * P) := by
      refine le_trans hd2 (le_of_eq ?_)
      rw [hηdef]
      field_simp
      ring
    have hXp : X ^ (2 * (q.1 : ℂ).re - 2) = (X ^ 2) ^ ((q.1 : ℂ).re - 1) := by
      rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX0.le]
      congr 1
      push_cast
      ring
    rw [zeroShortWeight, hY, hXp]
    have hXp0 : 0 ≤ (X ^ 2) ^ ((q.1 : ℂ).re - 1) := Real.rpow_nonneg (by positivity) _
    have hmin : d ^ 2 ≤ 4 * δ ^ 2 * min 1 (48 / δ ^ 2 / P) := by
      rcases le_total 1 (48 / δ ^ 2 / P) with hle | hle
      · rw [min_eq_left hle]
        nlinarith
      · rw [min_eq_right hle]
        have : d ^ 2 ≤ 2 * δ * (96 / (δ * P)) := by
          rw [sq]
          exact mul_le_mul hd1 hd2' hd0 (by positivity)
        refine le_trans this (le_of_eq ?_)
        field_simp
        ring
    calc d ^ 2 * (X ^ 2) ^ ((q.1 : ℂ).re - 1)
        ≤ 4 * δ ^ 2 * min 1 (48 / δ ^ 2 / P) * (X ^ 2) ^ ((q.1 : ℂ).re - 1) := by gcongr
      _ = 4 * δ ^ 2 * ((X ^ 2) ^ ((q.1 : ℂ).re - 1) * min 1 (48 / δ ^ 2 / P)) := by ring
  have hzsum : ∑ q ∈ F, zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ)
      ≤ ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2)))
          (q.1 : ℂ) := by
    refine Summable.sum_le_tsum F (fun q _ => zeroShortWeight_nonneg (by positivity)
      (by positivity) _) (summable_zeroShortWeight (one_le_pow₀ hX1) (by positivity))
  set Z := ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2)))
    (q.1 : ℂ) with hZ
  have hW0 : 0 ≤ almostAllHarmonicWeight X := by
    rw [almostAllHarmonicWeight]
    have h1 : 0 ≤ Real.log (3 * X ^ 4 + 4) :=
      Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 4) hX1])
    have h2 : 0 ≤ Real.log (2 * X ^ 4 + 1) :=
      Real.log_nonneg (by nlinarith [one_le_pow₀ (n := 4) hX1])
    positivity
  have hsumcoef : ∑ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
      ≤ 4 * δ ^ 2 * Z := by
    calc ∑ q ∈ F, ‖multWindowCoeff δ η (q.1 : ℂ)‖ ^ 2 * X ^ (2 * (q.1 : ℂ).re - 2)
        ≤ ∑ q ∈ F, 4 * δ ^ 2 * zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2)))
            (q.1 : ℂ) := Finset.sum_le_sum hcoef
      _ = 4 * δ ^ 2 * ∑ q ∈ F, zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2)))
            (q.1 : ℂ) := by rw [Finset.mul_sum]
      _ ≤ 4 * δ ^ 2 * Z := by gcongr
  have hgeq : (fun x : ℝ => ‖∑ q ∈ F, multWindowCoeff δ η (q.1 : ℂ) * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2
      / x ^ 3) = g := rfl
  rw [hgeq] at hms
  -- assemble
  have hvol : (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ Chebyshev.psi (x + X ^ θ) - Chebyshev.psi x < X ^ θ / 4}).toReal
      ≤ (volume ({x : ℝ | c ≤ g x} ∩ Set.Icc X (2 * X))).toReal := by
    refine ENNReal.toReal_mono ?_ (measure_mono hsub)
    refine ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hfinal : c * (volume ({x : ℝ | c ≤ g x} ∩ Set.Icc X (2 * X))).toReal
      ≤ 16 * almostAllHarmonicWeight X * δ ^ 2 * Z := by
    refine le_trans hmarkov (le_trans hms ?_)
    have := mul_le_mul_of_nonneg_left hsumcoef (by positivity : 0 ≤ 4 * almostAllHarmonicWeight X)
    linarith
  have hcδ : 16 * almostAllHarmonicWeight X * δ ^ 2 * Z / c
      = 8192 * almostAllHarmonicWeight X * X * Z := by
    rw [hc, hδ]
    field_simp
    ring
  rw [← hcδ, le_div_iff₀ hc0]
  nlinarith

theorem almostAllHarmonicWeight_le {X : ℝ} (hX : 1 ≤ X) :
    almostAllHarmonicWeight X
      ≤ 64 * (|xiLineTwoLogDerivConstant| + 2) * (Real.log (X ^ 2) + 2) ^ 2 := by
  set K := |xiLineTwoLogDerivConstant| with hK
  have hK0 : 0 ≤ K := abs_nonneg _
  have hX0 : 0 < X := by linarith
  set L := Real.log (X ^ 2) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (one_le_pow₀ hX)
  have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX
  have hlog4 : Real.log (X ^ 4) = 2 * L := by
    rw [hL, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith
  have hl7 : Real.log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    exact he2
  have hl3 : Real.log 3 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith
  have ha : Real.log (3 * X ^ 4 + 4) ≤ 2 * (L + 2) := by
    calc Real.log (3 * X ^ 4 + 4) ≤ Real.log (7 * X ^ 4) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 7 + 2 * L := by rw [Real.log_mul (by norm_num) (by positivity), hlog4]
      _ ≤ 2 * (L + 2) := by linarith
  have hb : 1 + Real.log (2 * X ^ 4 + 1) ≤ 2 * (L + 2) := by
    have : Real.log (2 * X ^ 4 + 1) ≤ Real.log (3 * X ^ 4) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity), hlog4] at this
    linarith
  have hb0 : 0 ≤ 1 + Real.log (2 * X ^ 4 + 1) := by
    have : 0 ≤ Real.log (2 * X ^ 4 + 1) := Real.log_nonneg (by linarith)
    linarith
  have hKa : K + Real.log (3 * X ^ 4 + 4) ≤ (K + 2) * (L + 2) := by nlinarith
  have hKa0 : 0 ≤ K + Real.log (3 * X ^ 4 + 4) := by
    have : 0 ≤ Real.log (3 * X ^ 4 + 4) := Real.log_nonneg (by linarith)
    linarith
  rw [almostAllHarmonicWeight, ← hK]
  calc 32 * (K + Real.log (3 * X ^ 4 + 4)) * (1 + Real.log (2 * X ^ 4 + 1))
      ≤ 32 * ((K + 2) * (L + 2)) * (2 * (L + 2)) := by gcongr
    _ = 64 * (K + 2) * (L + 2) ^ 2 := by ring

/-- **Primes are dense in almost all short intervals.**  For `1/6 < θ < 1`, the measure of the
`x ∈ [X, 2X]` with `ψ(x + X^θ) - ψ(x) < X^θ/4` is `o(X)`. -/
theorem tendsto_volume_psi_short_deficit {θ : ℝ} (hθ : 1 / 6 < θ) (hθ1 : θ < 1) :
    Tendsto (fun X : ℝ => (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ Chebyshev.psi (x + X ^ θ) - Chebyshev.psi x < X ^ θ / 4}).toReal / X) atTop (𝓝 0) := by
  have hθ0 : 0 < θ := by linarith
  have hu : 0 < (1 - θ) / 2 := by linarith
  have hu' : (1 - θ) / 2 < 5 / 12 := by linarith
  have hlim := (tendsto_logPow_mul_tsum_zeroShortWeight_seven_twelfths 2 hu hu'
    (c := 192) (by norm_num)).comp (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0))
  set K := |xiLineTwoLogDerivConstant| with hK
  have hK0 : 0 ≤ K := abs_nonneg _
  have hlim3 := hlim.const_mul (8192 * (64 * (K + 2)))
  rw [mul_zero] at hlim3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim3 ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  · have hev : ∀ᶠ X : ℝ in atTop, 200 * (xiSpectralThreeHalvesMass + 1) ≤ X ^ θ :=
      (tendsto_rpow_atTop hθ0).eventually_ge_atTop _
    filter_upwards [hev, eventually_ge_atTop (2 : ℝ)] with X hXh hX2
    have hX0 : 0 < X := by linarith
    have hv := volume_psi_short_deficit_le hθ0 hθ1 hX2 hXh
    have hW := almostAllHarmonicWeight_le (by linarith : (1 : ℝ) ≤ X)
    rw [← hK] at hW
    set Z := ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2) (192 * (X ^ 2) ^ (2 * ((1 - θ) / 2)))
      (q.1 : ℂ) with hZ
    have hZ0 : 0 ≤ Z := tsum_nonneg fun q => zeroShortWeight_nonneg (by positivity)
      (by positivity) _
    show _ / X ≤ 8192 * (64 * (K + 2)) * ((Real.log (X ^ 2) + 2) ^ 2 * Z)
    rw [div_le_iff₀ hX0]
    calc _ ≤ 8192 * almostAllHarmonicWeight X * X * Z := hv
      _ ≤ 8192 * (64 * (K + 2) * (Real.log (X ^ 2) + 2) ^ 2) * X * Z := by gcongr
      _ = 8192 * (64 * (K + 2)) * ((Real.log (X ^ 2) + 2) ^ 2 * Z) * X := by ring

/-- A positive `θ` window contains a prime. -/
theorem exists_prime_of_theta_window_pos {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hpos : 0 < Chebyshev.theta b - Chebyshev.theta a) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ (p : ℝ) ≤ b := by
  rw [Sieve.theta_sub_eq_sum_Ioc hab] at hpos
  obtain ⟨p, hp, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp
  refine ⟨p, hp.2, ?_, ?_⟩
  · have h1 : (⌊a⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hp.1.1
    linarith [Nat.lt_floor_add_one a]
  · have h1 : (p : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast hp.1.2
    linarith [Nat.floor_le (show 0 ≤ b by linarith)]

/-- **Primes in almost all short intervals.**  For `1/6 < θ < 1`, the measure of the
`x ∈ [X, 2X]` such that `(x, x + X^θ]` contains no prime is `o(X)`. -/
theorem tendsto_volume_no_prime_short {θ : ℝ} (hθ : 1 / 6 < θ) (hθ1 : θ < 1) :
    Tendsto (fun X : ℝ => (volume {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ ¬ ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + X ^ θ}).toReal / X) atTop (𝓝 0) := by
  have hθ0 : 0 < θ := by linarith
  have hmain := tendsto_volume_psi_short_deficit hθ hθ1
  have hlog : ∀ᶠ X : ℝ in atTop, (Real.log X + 2) ^ 2 * X ^ (-(θ / 2)) ≤ Real.log 2 / 64 :=
    (tendsto_log_add_two_pow_mul_rpow_neg 2 (by positivity : 0 < θ / 2)).eventually
      (ge_mem_nhds (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  · filter_upwards [hlog, eventually_ge_atTop (3 : ℝ),
      (tendsto_rpow_atTop hθ0).eventually_ge_atTop 1] with X hXl hX3 hXθ
    have hX0 : 0 < X := by linarith
    refine div_le_div_of_nonneg_right ?_ hX0.le
    have hsub : {x : ℝ | x ∈ Set.Icc X (2 * X)
        ∧ ¬ ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + X ^ θ}
        ⊆ {x : ℝ | x ∈ Set.Icc X (2 * X)
          ∧ Chebyshev.psi (x + X ^ θ) - Chebyshev.psi x < X ^ θ / 4} := by
      rintro x ⟨hx, hnp⟩
      refine ⟨hx, lt_of_not_ge fun hge => hnp ?_⟩
      have hx2 : 2 ≤ x := by linarith [hx.1]
      have hleak := Sieve.chebyshevPsi_window_le_theta_window_add_local_primePower
        (a := x) (b := x + X ^ θ) hx2 (by linarith) (by linarith)
      rw [show x + X ^ θ - x = X ^ θ by ring] at hleak
      have hb : Real.log (x + X ^ θ) ≤ Real.log X + 2 := by
        have hθX : X ^ θ ≤ X := Real.rpow_le_self_of_one_le (by linarith) hθ1.le
        calc Real.log (x + X ^ θ) ≤ Real.log (3 * X) :=
              Real.log_le_log (by linarith) (by linarith [hx.2])
          _ = Real.log 3 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
          _ ≤ Real.log X + 2 := by
              have : Real.log 3 ≤ 2 := by
                rw [Real.log_le_iff_le_exp (by norm_num)]
                have := Real.add_one_le_exp (2 : ℝ)
                have h2 : (2 : ℝ) + 1 ≤ Real.exp 2 := this
                have h3 : Real.exp 1 ≥ 2 := by
                  have := Real.add_one_le_exp (1 : ℝ)
                  linarith
                have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
                  rw [← Real.exp_add]; norm_num
                nlinarith
              linarith
      have hb0 : 0 ≤ Real.log (x + X ^ θ) := Real.log_nonneg (by linarith)
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hsq : Real.sqrt (X ^ θ) = X ^ (θ / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
        ring_nf
      rw [hsq] at hleak
      have hhalf : 1 ≤ X ^ (θ / 2) := Real.one_le_rpow (by linarith) (by positivity)
      have hsplit : X ^ θ = X ^ (θ / 2) * X ^ (θ / 2) := by
        rw [← Real.rpow_add hX0]
        ring_nf
      have hneg : X ^ (θ / 2) * X ^ (-(θ / 2)) = 1 := by
        rw [← Real.rpow_add hX0]
        simp
      have hL : 0 ≤ Real.log X + 2 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ X)]
      have hlk : Real.log (x + X ^ θ) / Real.log 2 * (X ^ (θ / 2) + 1) * Real.log (x + X ^ θ)
          ≤ X ^ θ / 32 := by
        have e1 : Real.log (x + X ^ θ) / Real.log 2 * (X ^ (θ / 2) + 1) * Real.log (x + X ^ θ)
            ≤ (Real.log X + 2) ^ 2 * (2 * X ^ (θ / 2)) / Real.log 2 := by
          rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlog2]
          have : Real.log (x + X ^ θ) * Real.log (x + X ^ θ) ≤ (Real.log X + 2) ^ 2 := by
            rw [sq]
            exact mul_le_mul hb hb hb0 hL
          calc Real.log (x + X ^ θ) * (X ^ (θ / 2) + 1) * Real.log (x + X ^ θ)
              = Real.log (x + X ^ θ) * Real.log (x + X ^ θ) * (X ^ (θ / 2) + 1) := by ring
            _ ≤ (Real.log X + 2) ^ 2 * (2 * X ^ (θ / 2)) := by
                gcongr
                linarith
        have e2 : (Real.log X + 2) ^ 2 * (2 * X ^ (θ / 2))
            = 2 * ((Real.log X + 2) ^ 2 * X ^ (-(θ / 2))) * X ^ θ := by
          rw [hsplit]
          have : X ^ (θ / 2) = X ^ (θ / 2) * (X ^ (θ / 2) * X ^ (-(θ / 2))) := by
            rw [hneg, mul_one]
          conv_lhs => rw [this]
          ring
        rw [e2] at e1
        refine le_trans e1 ?_
        rw [div_le_iff₀ hlog2]
        have hXθ0 : 0 ≤ X ^ θ := by linarith
        nlinarith
      have hθw : 0 < Chebyshev.theta (x + X ^ θ) - Chebyshev.theta x := by linarith
      exact exists_prime_of_theta_window_pos (by linarith) (by linarith) hθw
    refine ENNReal.toReal_mono ?_ (measure_mono hsub)
    refine ne_of_lt (lt_of_le_of_lt (measure_mono fun x hx => hx.1) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top

end

end RHTower
