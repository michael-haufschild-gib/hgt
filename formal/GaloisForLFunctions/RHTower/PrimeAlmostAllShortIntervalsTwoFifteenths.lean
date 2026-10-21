import GaloisForLFunctions.RHTower.PrimeShortIntervalsSeventeenThirtiethsSharp
import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervalsAsymptotic

/-!
# Guth–Maynard Corollary 1.4: almost all short intervals of relative length `X^{θ-1}`, `θ > 2/15`

For `2/15 < θ < 1` the measure of the `x ∈ [X, 2X]` with

`|ψ(x + X^{θ-1}x) - ψ(x) - X^{θ-1}x| > exp(-(log X)^{1/4}) · X^{θ-1}x`

is at most `X exp(-(log X)^{1/4})` for all large `X`
(`exists_volume_psi_almost_all_short_le`).

The second-moment layer is already unconditional: Chebyshev's inequality
(`volume_psi_short_asymptotic_le`) bounds that measure by
`25600 ε^{-2} W(X) X Σ_ρ zeroShortWeight(X², (192/5ε)(X²)^{1-θ})` with
`W(X) ≤ 64(|K| + 2)(log X² + 2)²`.  Taking `ε = exp(-(log X)^{1/4})` costs only
`exp(3(log X)^{1/4})` and a polylogarithm, while the zero weight at
`u = (1-θ)/2 < 13/30` carries the Vinogradov–Korobov saving `exp(-κ(log X)^{2/7})`; since
`2/7 > 1/4` the saving wins.  The sub-polynomial factor `192/(5ε)` is absorbed by raising the
exponent from `u` to `u' = (u + 13/30)/2 < 13/30`.

The condition `u < 13/30` is exactly `θ > 2/15`.  The density input carries the single datum
`hGM : GuthMaynardLargeValuesBound`.
-/

set_option autoImplicit false

noncomputable section

namespace RHTower

open Filter Topology MeasureTheory RHTower.Sieve RHTower.GuthMaynard

/-- `(3L)^n e^{-κ L^e} → 0` for every `e > 0`:  `e^{-t} ≤ m!/t^m` with `e m ≥ n + 1`. -/
theorem tendsto_pow_mul_exp_neg_rpow (n : ℕ) {κ e : ℝ} (hκ : 0 < κ) (he : 0 < e) :
    Tendsto (fun L : ℝ => (3 * L) ^ n * Real.exp (-(κ * L ^ e))) atTop (𝓝 0) := by
  obtain ⟨m, hm1⟩ : ∃ m : ℕ, ((n : ℝ) + 1) ≤ e * m := by
    obtain ⟨m, hm⟩ := exists_nat_gt (((n : ℝ) + 1) / e)
    refine ⟨m, ?_⟩
    rw [div_lt_iff₀ he] at hm
    linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 3 ^ n * (m.factorial : ℝ) / κ ^ m := ⟨_, rfl⟩
  have hup : Tendsto (fun L : ℝ => C / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL1
    have hL0 : (0 : ℝ) < L := by linarith
    have ht0 : (0 : ℝ) < κ * L ^ e := by positivity
    have hfac := exp_neg_le_factorial_div ht0 m
    have hpowm : (κ * L ^ e) ^ m = κ ^ m * L ^ (e * m) := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ e) m, ← Real.rpow_mul hL0.le]
    have hLn1 : L ^ ((n : ℝ) + 1) = L ^ (n + 1) := by
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hge : L ^ ((n : ℝ) + 1) ≤ L ^ (e * m) := Real.rpow_le_rpow_of_exponent_le hL1 hm1
    have hden : (κ : ℝ) ^ m * L ^ (n + 1) ≤ (κ * L ^ e) ^ m := by
      rw [hpowm, ← hLn1]
      exact mul_le_mul_of_nonneg_left hge (by positivity)
    have hle2 : (m.factorial : ℝ) / (κ * L ^ e) ^ m
        ≤ (m.factorial : ℝ) / (κ ^ m * L ^ (n + 1)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hden
    calc (3 * L) ^ n * Real.exp (-(κ * L ^ e))
        ≤ (3 * L) ^ n * ((m.factorial : ℝ) / (κ ^ m * L ^ (n + 1))) :=
          mul_le_mul_of_nonneg_left (le_trans hfac hle2) (by positivity)
      _ = C / L := by rw [hC, mul_pow, pow_succ]; field_simp

/-- The harmonic weight is eventually below `e^{(log X)^{1/4}}`:  a square of logarithms against a
quarter power in the exponent. -/
theorem eventually_log_sq_le_exp_quarter :
    ∀ᶠ X : ℝ in atTop,
      (Real.log (X ^ 2) + 2) ^ 2 ≤ Real.exp (Real.log X ^ ((1 : ℝ) / 4)) := by
  have hcomp := (tendsto_pow_mul_exp_neg_rpow 2 (κ := 1)
    (by norm_num : (0 : ℝ) < 1 / 4)).comp Real.tendsto_log_atTop
  have hsmall := hcomp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 2)] with X hX hXe
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXe
  have hL2 : (2 : ℝ) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; exact hXe
  have hlogsq : Real.log (X ^ 2) = 2 * Real.log X := by
    rw [Real.log_pow]; norm_num
  have hbound : (Real.log (X ^ 2) + 2) ^ 2 ≤ (3 * Real.log X) ^ 2 := by
    rw [hlogsq]
    have : 2 * Real.log X + 2 ≤ 3 * Real.log X := by linarith
    nlinarith [hL2]
  have hX' : (3 * Real.log X) ^ 2 * Real.exp (-(1 * Real.log X ^ ((1 : ℝ) / 4))) < 1 := hX
  have hE0 : (0 : ℝ) < Real.exp (Real.log X ^ ((1 : ℝ) / 4)) := Real.exp_pos _
  have hinv : Real.exp (-(1 * Real.log X ^ ((1 : ℝ) / 4)))
      = 1 / Real.exp (Real.log X ^ ((1 : ℝ) / 4)) := by
    rw [one_mul, Real.exp_neg, one_div]
  rw [hinv, mul_one_div, div_lt_one hE0] at hX'
  linarith

/-- **Guth–Maynard Corollary 1.4.**  For `2/15 < θ < 1` there is `X₀` with

`vol {x ∈ [X, 2X] : |ψ(x + X^{θ-1}x) - ψ(x) - X^{θ-1}x| > e^{-(log X)^{1/4}} X^{θ-1}x}
   ≤ X e^{-(log X)^{1/4}}`

for all `X ≥ X₀`.  Carries the Theorem 1.1 datum. -/
theorem exists_volume_psi_almost_all_short_le (hGM : GuthMaynardLargeValuesBound) {θ : ℝ}
    (hθ : 2 / 15 < θ) (hθ1 : θ < 1) :
    ∃ X₀ : ℝ, 4 ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧
        Real.exp (-(Real.log X ^ ((1 : ℝ) / 4))) * (X ^ (θ - 1) * x)
          < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x
              - X ^ (θ - 1) * x|}).toReal
        ≤ X * Real.exp (-(Real.log X ^ ((1 : ℝ) / 4))) := by
  have hθ0 : 0 < θ := by linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = (1 - θ) / 2 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hudef]; linarith
  have hu13 : u < 13 / 30 := by rw [hudef]; linarith
  obtain ⟨u', hu'def⟩ : ∃ u' : ℝ, u' = (u + 13 / 30) / 2 := ⟨_, rfl⟩
  have hu'0 : 0 < u' := by rw [hu'def]; linarith
  have hu'13 : u' < 13 / 30 := by rw [hu'def]; linarith
  have huu' : u < u' := by rw [hu'def]; linarith
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ, Kc = |xiLineTwoLogDerivConstant| := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := hKcdef ▸ abs_nonneg _
  obtain ⟨Cst, hCstdef⟩ : ∃ Cst : ℝ, Cst = 1638400 * (Kc + 2) := ⟨_, rfl⟩
  have hCst0 : 0 < Cst := by rw [hCstdef]; linarith
  -- the zero weight at `x = X²`, exponent `u'`, with the saving `e^{-5(log X²)^{1/4}}`
  have hZ := ((tendsto_exp_quarter_mul_tsum_zeroShortWeight_seventeen_thirtieths hGM (K := 5)
    (c := 1) hu'0 hu'13 le_rfl).comp
    (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0))).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / Cst by positivity))
  -- absorbing the sub-polynomial factor `192/(5ε)` into `(X²)^{2(u'-u)}`
  have habs := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 0 (K := 1)
    (show (0 : ℝ) < 4 * (u' - u) by linarith)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 5 / 192 by norm_num))
  -- the `hbig` threshold of the second-moment bound
  have hthr := (tendsto_exp_quarter_mul_logPow_mul_rpow_neg 0 (K := 2)
    (show (0 : ℝ) < 2 * θ by linarith)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / (16 * (64 + 1152 * xiSpectralThreeHalvesMass) + 1) by
      have := xiSpectralThreeHalvesMass_nonneg
      positivity))
  have hδ : ∀ᶠ X : ℝ in atTop, X ^ (θ - 1) ≤ 1 / 2 := by
    have h := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 - θ by linarith)
    have h' := h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    exact h'.mono fun X hX => by rwa [show -(1 - θ) = θ - 1 by ring] at hX
  have hmain : ∀ᶠ X : ℝ in atTop,
      (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧
        Real.exp (-(Real.log X ^ ((1 : ℝ) / 4))) * (X ^ (θ - 1) * x)
          < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x
              - X ^ (θ - 1) * x|}).toReal
        ≤ X * Real.exp (-(Real.log X ^ ((1 : ℝ) / 4))) := by
    filter_upwards [hZ, habs, hthr, hδ, eventually_log_sq_le_exp_quarter,
      eventually_ge_atTop (Real.exp 2), eventually_ge_atTop (4 : ℝ)]
      with X hZX habsX hthrX hδX hwX hXe hX4
    have hX0 : (0 : ℝ) < X := by linarith
    have hX1 : (1 : ℝ) ≤ X := by linarith
    have hL2 : (2 : ℝ) ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hX0]; exact hXe
    have hLq : (0 : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
    have hE0 : (0 : ℝ) < Real.exp (Real.log X ^ ((1 : ℝ) / 4)) := Real.exp_pos _
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = Real.exp (-(Real.log X ^ ((1 : ℝ) / 4))) := ⟨_, rfl⟩
    have hε0 : 0 < ε := hεdef ▸ Real.exp_pos _
    have hε1 : ε ≤ 1 := by
      rw [hεdef, Real.exp_le_one_iff]; linarith
    have hεE : ε * Real.exp (Real.log X ^ ((1 : ℝ) / 4)) = 1 := by
      rw [hεdef, ← Real.exp_add]
      simp
    -- the Chebyshev bound of the second-moment layer
    have hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * X ^ (2 * θ) := by
      rw [pow_zero, one_mul] at hthrX
      have hxp : (0 : ℝ) < X ^ (2 * θ) := Real.rpow_pos_of_pos hX0 _
      have hrw : X ^ (-(2 * θ)) = 1 / X ^ (2 * θ) := by rw [Real.rpow_neg hX0.le, one_div]
      rw [hrw, mul_one_div, div_lt_div_iff₀ hxp (by positivity)] at hthrX
      have hεsq : ε ^ 2 * Real.exp (2 * Real.log X ^ ((1 : ℝ) / 4)) = 1 := by
        rw [hεdef, sq, ← Real.exp_add, ← Real.exp_add]
        simp only [Real.exp_eq_one_iff]
        ring
      have hE2 : (0 : ℝ) < Real.exp (2 * Real.log X ^ ((1 : ℝ) / 4)) := Real.exp_pos _
      have hεsq0 : (0 : ℝ) < ε ^ 2 := by positivity
      have hM0 : (0 : ℝ) ≤ 16 * (64 + 1152 * xiSpectralThreeHalvesMass) := by
        have := xiSpectralThreeHalvesMass_nonneg
        positivity
      nlinarith [hthrX, hεsq, hE2, hεsq0, hM0]
    have hvol := volume_psi_short_asymptotic_le hε0 hε1 hX4 hδX hbig
    rw [← hεdef] at hvol ⊢
    -- the zero weight, after raising the exponent and clearing the harmonic weight
    obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
      (192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ) := ⟨_, rfl⟩
    obtain ⟨Z', hZ'def⟩ : ∃ Z' : ℝ, Z' = ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
      (1 * (X ^ 2) ^ (2 * u')) (q.1 : ℂ) := ⟨_, rfl⟩
    have hXsq1 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ hX1
    have hXsq0 : (0 : ℝ) < X ^ 2 := by positivity
    have hcut : 192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2)) ≤ 1 * (X ^ 2) ^ (2 * u') := by
      rw [one_mul, ← hudef]
      have hsplit : (X ^ 2) ^ (2 * u') = (X ^ 2) ^ (2 * u) * (X ^ 2) ^ (2 * (u' - u)) := by
        rw [← Real.rpow_add hXsq0]
        congr 1
        ring
      have hfac : 192 / (5 * ε) ≤ (X ^ 2) ^ (2 * (u' - u)) := by
        rw [pow_zero, one_mul] at habsX
        have hxp : (0 : ℝ) < X ^ (4 * (u' - u)) := Real.rpow_pos_of_pos hX0 _
        have hrw : X ^ (-(4 * (u' - u))) = 1 / X ^ (4 * (u' - u)) := by
          rw [Real.rpow_neg hX0.le, one_div]
        rw [hrw, mul_one_div, div_lt_div_iff₀ hxp (by norm_num)] at habsX
        have hXsq : (X ^ 2) ^ (2 * (u' - u)) = X ^ (4 * (u' - u)) := by
          rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX0.le]
          congr 1
          push_cast
          ring
        rw [hXsq]
        have hdiv : (192 : ℝ) / (5 * ε) = 192 / 5 * (1 / ε) := by ring
        have hεinv : 1 / ε = Real.exp (Real.log X ^ ((1 : ℝ) / 4)) := by
          rw [hεdef, Real.exp_neg, one_div, inv_inv]
        rw [hdiv, hεinv]
        linarith
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hXsq0.le _)
    have hZle : Z ≤ Z' := by
      rw [hZdef, hZ'def]
      exact tsum_zeroShortWeight_mono_right hXsq1 (by positivity) hcut
    have hZ'0 : 0 ≤ Z' := by
      rw [hZ'def]
      exact tsum_nonneg fun q => zeroShortWeight_nonneg hXsq0.le (by positivity) _
    -- the saving beats `ε³` and the polylogarithmic weight
    have hZ'small : Real.exp (5 * Real.log X ^ ((1 : ℝ) / 4)) * Z' < 1 / Cst := by
      have hcompX : Real.exp (5 * Real.log (X ^ 2) ^ ((1 : ℝ) / 4)) * Z' < 1 / Cst := by
        rw [hZ'def]
        exact hZX
      have hmono : Real.log X ^ ((1 : ℝ) / 4) ≤ Real.log (X ^ 2) ^ ((1 : ℝ) / 4) := by
        have hlogsq : Real.log (X ^ 2) = 2 * Real.log X := by rw [Real.log_pow]; norm_num
        rw [hlogsq]
        exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have hexp : Real.exp (5 * Real.log X ^ ((1 : ℝ) / 4))
          ≤ Real.exp (5 * Real.log (X ^ 2) ^ ((1 : ℝ) / 4)) := by
        rw [Real.exp_le_exp]; linarith
      nlinarith [hZ'0, hcompX, hexp]
    have hW := almostAllHarmonicWeight_le hX1
    rw [← hKcdef] at hW
    have hW0 : 0 ≤ almostAllHarmonicWeight X := by
      rw [almostAllHarmonicWeight, ← hKcdef]
      have h1 : 0 ≤ Real.log (3 * X ^ 4 + 4) := Real.log_nonneg (by nlinarith [pow_pos hX0 4])
      have h2 : 0 ≤ Real.log (2 * X ^ 4 + 1) := Real.log_nonneg (by nlinarith [pow_pos hX0 4])
      positivity
    -- assemble
    have hkey : 25600 / ε ^ 2 * almostAllHarmonicWeight X * X * Z ≤ X * ε := by
      have hstep1 : 25600 / ε ^ 2 * almostAllHarmonicWeight X * X * Z
          ≤ 25600 / ε ^ 2 * (64 * (Kc + 2) * Real.exp (Real.log X ^ ((1 : ℝ) / 4))) * X * Z' := by
        have h1 : almostAllHarmonicWeight X
            ≤ 64 * (Kc + 2) * Real.exp (Real.log X ^ ((1 : ℝ) / 4)) := by
          refine le_trans hW ?_
          have : (0 : ℝ) ≤ 64 * (Kc + 2) := by linarith
          exact mul_le_mul_of_nonneg_left hwX this
        have hpos : (0 : ℝ) < 25600 / ε ^ 2 := by positivity
        gcongr
        · positivity
      refine le_trans hstep1 ?_
      -- `25600 ε^{-2} · 64(Kc+2) e^{Lq} · Z' ≤ ε`  from  `Cst · Z' ≤ e^{-5Lq}`
      have hεcube : ε ^ 2 * ε = Real.exp (-(3 * Real.log X ^ ((1 : ℝ) / 4))) := by
        rw [hεdef, sq, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have hE5 : (0 : ℝ) < Real.exp (5 * Real.log X ^ ((1 : ℝ) / 4)) := Real.exp_pos _
      have hprod : Real.exp (-(3 * Real.log X ^ ((1 : ℝ) / 4)))
          * Real.exp (5 * Real.log X ^ ((1 : ℝ) / 4))
          = Real.exp (2 * Real.log X ^ ((1 : ℝ) / 4)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
      have hZ'bd : Cst * Z' ≤ 1 := by
        have h := (div_le_one hCst0).mp (le_of_lt (lt_of_le_of_lt (by nlinarith [hZ'0, hE0]) hZ'small))
        nlinarith [hZ'small, hE0, hZ'0, hCst0]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hε2]
      have hEge : (1 : ℝ) ≤ Real.exp (2 * Real.log X ^ ((1 : ℝ) / 4)) := by
        rw [Real.one_le_exp_iff]; linarith
      nlinarith [hZ'small, hεcube, hprod, hE5, hZ'0, hX0, hKc0, hCst0, hEge, hX1]
    calc _ ≤ 25600 / ε ^ 2 * almostAllHarmonicWeight X * X * Z := by rw [hZdef]; exact hvol
      _ ≤ X * ε := hkey
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hmain
  exact ⟨max X₀ 4, le_max_right _ _, fun X hX => hX₀ X (le_trans (le_max_left _ _) hX)⟩

end RHTower

end
