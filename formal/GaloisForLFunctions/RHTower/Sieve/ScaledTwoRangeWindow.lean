/-
# The Möbius short-interval mean square at a constant multiple of the window

The two-range assembly proves the fibre mean square at the window `exp((log x)^β)` for every
`0 < β < 1`.  Shrinking that window by a fixed constant `c ≤ 1` changes two things and nothing else.
The Dirichlet polynomial loses at most the window length in terms, and a Dirichlet polynomial with
bounded coefficients changes by at most the number of dropped terms, so the head integral grows by
at most `4 W (h+1)²` — negligible against the square of the length, since `W h² ≍ √x · h · log log x`
while the length is `≍ √x`.  The height at which the head bound is taken rescales by `1/c`, and the
free parameter `ω` of the Route E gate absorbs that exactly.

Main results:
* `norm_logPoly_le_of_subset`, `setIntegral_normSq_logPoly_le_of_subset` — truncating a Dirichlet
  polynomial costs the number of dropped terms.
* `exists_twoRange_head_budget` — the two-range head bound, packaged.
* `averagedMeanSquare_moebius_scaledLength_all` — **the mean square at every window
  `c · exp((log x)^β)`, for every `0 < β < 1`**.
-/
import GaloisForLFunctions.RHTower.Sieve.TwoRangeAssembly
import GaloisForLFunctions.RHTower.Sieve.ScaledCardLength

open Filter Topology MeasureTheory
open scoped BigOperators
open ArithmeticFunction (moebius)

namespace RHTower.Sieve

local notation "μ" => ArithmeticFunction.moebius

/-- Dropping terms from a Dirichlet polynomial costs at most the number of dropped terms. -/
theorem norm_logPoly_le_of_subset {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) {s t : Finset ℕ}
    (hst : s ⊆ t) (w : ℝ) :
    ‖logPoly a s w‖ ≤ ‖logPoly a t w‖ + (((t.card : ℕ) : ℝ) - ((s.card : ℕ) : ℝ)) := by
  classical
  have hsplit : logPoly a (t \ s) w + logPoly a s w = logPoly a t w := by
    rw [logPoly, logPoly, logPoly, ← Finset.sum_sdiff hst]
  have hsub : logPoly a s w = logPoly a t w - logPoly a (t \ s) w := by
    rw [← hsplit]
    ring
  have htail : ‖logPoly a (t \ s) w‖ ≤ (((t \ s).card : ℕ) : ℝ) := by
    rw [logPoly]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ n ∈ t \ s,
        ‖a n * Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I)‖
          ≤ (1 : ℝ) := by
      intro n _
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact ha n
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (((t \ s).card : ℕ) : ℝ) = ((t.card : ℕ) : ℝ) - ((s.card : ℕ) : ℝ) := by
    have hle : s.card ≤ t.card := Finset.card_le_card hst
    have hnat : (t \ s).card = t.card - s.card := by
      have := Finset.card_sdiff_add_card_eq_card hst
      omega
    rw [hnat, Nat.cast_sub hle]
  rw [hsub]
  refine le_trans (norm_sub_le _ _) ?_
  rw [← hcard]
  linarith [htail]

/-- The mean square of a shorter Dirichlet polynomial, from the longer one. -/
theorem setIntegral_normSq_logPoly_le_of_subset {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1)
    {s t : Finset ℕ} (hst : s ⊆ t) {W B : ℝ} (hW : 0 ≤ W)
    (hb : (∫ w in Set.Icc (-W) W, ‖logPoly a t w‖ ^ 2) ≤ B) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ 2 * B + 4 * W * (((t.card : ℕ) : ℝ) - ((s.card : ℕ) : ℝ)) ^ 2 := by
  classical
  set D : ℝ := ((t.card : ℕ) : ℝ) - ((s.card : ℕ) : ℝ) with hD
  have hD0 : 0 ≤ D := by
    rw [hD, sub_nonneg]
    exact_mod_cast Finset.card_le_card hst
  have hcontS : Continuous fun w : ℝ => ‖logPoly a s w‖ ^ 2 :=
    ((continuous_logPoly a s).norm).pow 2
  have hcontT : Continuous fun w : ℝ => ‖logPoly a t w‖ ^ 2 :=
    ((continuous_logPoly a t).norm).pow 2
  have hintS : IntegrableOn (fun w : ℝ => ‖logPoly a s w‖ ^ 2) (Set.Icc (-W) W) :=
    (hcontS.continuousOn).integrableOn_compact isCompact_Icc
  have hintT : IntegrableOn (fun w : ℝ => ‖logPoly a t w‖ ^ 2) (Set.Icc (-W) W) :=
    (hcontT.continuousOn).integrableOn_compact isCompact_Icc
  have hintC : IntegrableOn (fun _ : ℝ => 2 * D ^ 2) (Set.Icc (-W) W) :=
    (continuous_const.continuousOn).integrableOn_compact isCompact_Icc
  have hptw : ∀ w ∈ Set.Icc (-W) W,
      ‖logPoly a s w‖ ^ 2 ≤ 2 * ‖logPoly a t w‖ ^ 2 + 2 * D ^ 2 := by
    intro w _
    have h := norm_logPoly_le_of_subset ha hst w
    rw [← hD] at h
    nlinarith [norm_nonneg (logPoly a s w), norm_nonneg (logPoly a t w), hD0,
      sq_nonneg (‖logPoly a t w‖ - D)]
  have hmono : (∫ w in Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2)
      ≤ ∫ w in Set.Icc (-W) W, (2 * ‖logPoly a t w‖ ^ 2 + 2 * D ^ 2) := by
    refine setIntegral_mono_on hintS ((hintT.const_mul 2).add hintC) measurableSet_Icc hptw
  have hval : (∫ w in Set.Icc (-W) W, (2 * ‖logPoly a t w‖ ^ 2 + 2 * D ^ 2))
      = 2 * (∫ w in Set.Icc (-W) W, ‖logPoly a t w‖ ^ 2) + 4 * W * D ^ 2 := by
    rw [integral_add ((hintT.const_mul 2)) hintC, integral_const_mul, setIntegral_const]
    have hvol : (volume : Measure ℝ).real (Set.Icc (-W) W) = 2 * W := by
      rw [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      ring
    rw [hvol, smul_eq_mul]
    ring
  rw [hval] at hmono
  nlinarith [hmono, hb, sq_nonneg D, hW]

/-- **The head budget of the two-range assembly, packaged.**  The two-range architecture bounds the
head integral of the Möbius Dirichlet polynomial at every `0 < β < 1` by a quantity negligible
against the square of the polynomial length. -/
theorem exists_twoRange_head_budget {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ B : ℝ → ℝ,
      (∀ᶠ x : ℝ in atTop, 0 ≤ B x ∧
        (∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
          ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (twoRangeLength β x)) w‖ ^ 2) ≤ B x)
      ∧ Tendsto (fun x : ℝ => B x / (((twoRangeLength β x : ℕ) : ℝ)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨A₀, δ₀, Ctot, hδ₀, hCtot, hhigh, hlim⟩ :=
    exists_twoRange_high_bound (a := 19 / 20) (b := 99 / 100) (c' := 3) (β := β) (A₃ := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hβ0 hβ1 (by norm_num)
  obtain ⟨Kd, hKd, hdiscb⟩ :=
    exists_discBudget_bound (β := β) (b := 99 / 100) (A₃ := 8) hβ0 hβ1 (by norm_num) (by norm_num)
  have hρ0 := twoRangeHighRho_nonneg (A₀ := A₀) (δ₀ := δ₀) (Ctot := Ctot) (a₁ := 19 / 20)
    (b := 99 / 100) (c' := 3) (β := β) (A₃ := 8) hCtot.le (by norm_num) (by norm_num) hβ0 hβ1
  have hρ : Tendsto (fun x : ℝ => (Real.log x) ^ (3 : ℝ)
      * (8 * twoRangeHighRho A₀ δ₀ Ctot (19 / 20) (99 / 100) 3 β 8 x
        * (Real.log x) ^ (99 / 100 + (3 : ℝ)))) atTop (𝓝 0) := by
    have h := hlim ((3 : ℝ) + 99 / 100 + 3) (by norm_num) (by norm_num)
    have h8 := h.const_mul (8 : ℝ)
    rw [show ((8 : ℝ) * 0) = 0 by ring] at h8
    refine h8.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
    have hid : (Real.log x) ^ ((3 : ℝ) + 99 / 100 + 3)
        = (Real.log x) ^ (3 : ℝ) * (Real.log x) ^ (99 / 100 + (3 : ℝ)) := by
      rw [show (3 : ℝ) + 99 / 100 + 3 = 3 + (99 / 100 + 3) by ring, Real.rpow_add hlogx]
    rw [hid]
    ring
  have hUf := tendsto_exceptionalFactor (a := β / 2) (c := 2 + β) (A := β + 2) (β := β)
    (a₁ := 19 / 20) (b := 99 / 100) (c' := 3) (A₃ := 8) hβ0 hβ1 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have hbnd := twoRangeBudget_bound (A₀ := A₀) (δ₀ := δ₀) (Ctot := Ctot) (Kd := Kd)
    (a := β / 2) (c := 2 + β) (A := β + 2) (β := β) (a₁ := 19 / 20) (b := 99 / 100) (c' := 3)
    (A₃ := 8) hβ0 hβ1 (by linarith) (by linarith) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hhigh hdiscb hρ0 (by norm_num)
  have hrel := tendsto_twoRangeBudget_div_sq (A₀ := A₀) (δ₀ := δ₀) (Ctot := Ctot) (Kd := Kd)
    (a := β / 2) (c := 2 + β) (A := β + 2) (β := β) (a₁ := 19 / 20) (b := 99 / 100) (c' := 3)
    (A₃ := 8) (E := 3) hβ0 hβ1 (by linarith) (by linarith) (by linarith) (by linarith)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hρ0 hρ hUf
  refine ⟨fun x => twoRangeBudget A₀ δ₀ Ctot Kd (β / 2) (2 + β) (β + 2) β (19 / 20)
    (99 / 100) 3 8 x, ?_, hrel⟩
  filter_upwards [hbnd] with x hb
  have hI : (0 : ℝ) ≤ ∫ w in Set.Icc (-(twoRangeTop β x)) (twoRangeTop β x),
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 (twoRangeLength β x)) w‖ ^ 2 :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun w _ => by positivity
  exact ⟨le_trans hI hb, hb⟩

/-- The length of the shrunken Dirichlet polynomial. -/
noncomputable def scaledFibreLength (c β x : ℝ) : ℕ := ⌊Real.sqrt x + scaledLength c β x⌋₊

theorem scaledFibreLength_le {c β : ℝ} (hc1 : c ≤ 1) (x : ℝ) :
    scaledFibreLength c β x ≤ twoRangeLength β x := by
  refine Nat.floor_le_floor ?_
  have h0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have : scaledLength c β x ≤ cardLength β x := by
    calc scaledLength c β x = c * cardLength β x := rfl
      _ ≤ 1 * cardLength β x := mul_le_mul_of_nonneg_right hc1 h0.le
      _ = cardLength β x := one_mul _
  linarith

theorem sqrt_le_scaledFibreLength {c β x : ℝ} (h1 : 1 ≤ scaledLength c β x) :
    Real.sqrt x ≤ ((scaledFibreLength c β x : ℕ) : ℝ) := by
  have hle : Real.sqrt x + 1 ≤ Real.sqrt x + scaledLength c β x := by linarith
  have hfl : Real.sqrt x + scaledLength c β x - 1
      ≤ ((⌊Real.sqrt x + scaledLength c β x⌋₊ : ℕ) : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.sqrt x + scaledLength c β x)
    linarith
  rw [scaledFibreLength]
  linarith

theorem twoRangeLength_le_two_mul_sqrt {β x : ℝ}
    (hcl : cardLength β x ≤ Real.sqrt x) :
    ((twoRangeLength β x : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
  have := Nat.floor_le (add_nonneg (Real.sqrt_nonneg x) (cardLength_pos β x).le)
  rw [twoRangeLength]
  linarith

/-- The scaled head budget, relative to the shorter length. -/
theorem scaledBudget_ratio_le {Bv Mv Nv hw S Lg Ll : ℝ}
    (hB0 : 0 ≤ Bv) (hN0 : 0 < Nv) (hw0 : 0 < hw) (hS0 : 0 < S) (hLg1 : 1 ≤ Lg)
    (hLl0 : 0 ≤ Ll) (hLlog : Ll ≤ Lg) (hlow : S ≤ Nv) (hmid : Nv ≤ Mv) (hhigh : Mv ≤ 2 * S)
    (hgap : Mv - Nv ≤ 2 * hw) :
    (2 * Bv + 4 * (Mv / hw * Ll) * (Mv - Nv) ^ 2) / Nv ^ 2
      ≤ 8 * (Bv / Mv ^ 2) + 32 * (Lg * (hw / S)) := by
  have hM0 : 0 < Mv := lt_of_lt_of_le hN0 hmid
  have hgap0 : (0 : ℝ) ≤ Mv - Nv := by linarith
  have hMN : Mv ≤ 2 * Nv := by linarith
  have hMsq : Mv ^ 2 ≤ 4 * Nv ^ 2 := by nlinarith [hM0.le, hN0.le]
  have hA : 2 * Bv / Nv ^ 2 ≤ 8 * (Bv / Mv ^ 2) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < Nv ^ 2)]
    have hBM : 8 * (Bv / Mv ^ 2) * Nv ^ 2 = 8 * Bv * (Nv ^ 2 / Mv ^ 2) := by
      field_simp
    rw [hBM]
    have hfrac : (1 : ℝ) / 4 ≤ Nv ^ 2 / Mv ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith [hB0, hfrac]
  have hgsq : (Mv - Nv) ^ 2 ≤ 4 * hw ^ 2 := by nlinarith
  have hMhw0 : (0 : ℝ) ≤ Mv / hw := div_nonneg hM0.le hw0.le
  have hnum : 4 * (Mv / hw * Ll) * (Mv - Nv) ^ 2 ≤ 32 * S * hw * Lg := by
    have h1 : 4 * (Mv / hw * Ll) * (Mv - Nv) ^ 2 ≤ 4 * (Mv / hw * Lg) * (4 * hw ^ 2) := by
      have hTle : Mv / hw * Ll ≤ Mv / hw * Lg := mul_le_mul_of_nonneg_left hLlog hMhw0
      have hTnn : (0 : ℝ) ≤ Mv / hw * Lg := mul_nonneg hMhw0 (by linarith)
      nlinarith [sq_nonneg (Mv - Nv)]
    have h2 : 4 * (Mv / hw * Lg) * (4 * hw ^ 2) = 16 * Mv * hw * Lg := by
      field_simp
      ring
    have h3 : 16 * Mv * hw * Lg ≤ 32 * S * hw * Lg := by
      have hpos : (0 : ℝ) ≤ hw * Lg := mul_nonneg hw0.le (by linarith)
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * S - Mv by linarith) hpos]
    linarith [h1, h2.le, h2.ge, h3]
  have hnn : (0 : ℝ) ≤ 4 * (Mv / hw * Ll) * (Mv - Nv) ^ 2 := by
    have : (0 : ℝ) ≤ Mv / hw * Ll := mul_nonneg hMhw0 hLl0
    nlinarith [sq_nonneg (Mv - Nv)]
  have hSsq : S * S ≤ Nv ^ 2 := by nlinarith
  have hB2 : 4 * (Mv / hw * Ll) * (Mv - Nv) ^ 2 / Nv ^ 2 ≤ 32 * (Lg * (hw / S)) := by
    have h1 : 4 * (Mv / hw * Ll) * (Mv - Nv) ^ 2 / Nv ^ 2 ≤ (32 * S * hw * Lg) / Nv ^ 2 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have h2 : (32 * S * hw * Lg) / Nv ^ 2 ≤ (32 * S * hw * Lg) / (S * S) := by
      refine div_le_div_of_nonneg_left ?_ (by positivity) hSsq
      nlinarith [hw0.le, hS0.le, hLg1]
    have h3 : (32 * S * hw * Lg) / (S * S) = 32 * (Lg * (hw / S)) := by
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  rw [add_div]
  linarith [hA, hB2]

/-- **The Möbius short-interval mean square at every window `c · exp((log x)^β)`, for every
`0 < β < 1`.**  Shrinking the window by a constant factor shortens the Dirichlet polynomial by at
most the window length, which costs `4 W (h+1)²` in the head integral — negligible against the
square of the length — and rescales the height, which the free parameter `ω` absorbs. -/
theorem averagedMeanSquare_moebius_scaledLength_all {c β : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    AveragedMeanSquare (fun n => ((μ n : ℤ) : ℝ)) (scaledLength c β) := by
  classical
  obtain ⟨B, hB, hBrel⟩ := exists_twoRange_head_budget hβ0 hβ1
  have hbasic : ∀ᶠ x : ℝ in atTop,
      4 ≤ x ∧ 1 ≤ scaledLength c β x ∧ scaledLength c β x ≤ Real.sqrt x
        ∧ cardLength β x ≤ Real.sqrt x ∧ 1 / c ≤ Real.log (Real.log x)
        ∧ 1 ≤ cardLength β x ∧ 1 ≤ Real.log x := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℝ),
      (tendsto_scaledLength hc0 hβ0).eventually_ge_atTop (1 : ℝ),
      scaledLength_le_sqrt hc1 hβ0 hβ1, cardLength_le_sqrt hβ0 hβ1,
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (1 / c),
      (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with
      x hx4 hsc1 hscs hcls hu1 hcl1 hlogx
    exact ⟨hx4, hsc1, hscs, hcls, hu1, hcl1, hlogx⟩
  have hgeom : ∀ᶠ x : ℝ in atTop,
      Real.sqrt x ≤ ((scaledFibreLength c β x : ℕ) : ℝ)
        ∧ ((scaledFibreLength c β x : ℕ) : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ)
        ∧ ((twoRangeLength β x : ℕ) : ℝ) ≤ 2 * Real.sqrt x
        ∧ (0 : ℝ) < Real.sqrt x := by
    filter_upwards [hbasic] with x hx
    obtain ⟨hx4, hsc1, -, hcls, -, -, -⟩ := hx
    have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hlow : Real.sqrt x ≤ ((scaledFibreLength c β x : ℕ) : ℝ) :=
      sqrt_le_scaledFibreLength hsc1
    have hmid : ((scaledFibreLength c β x : ℕ) : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := by
      exact_mod_cast scaledFibreLength_le hc1 x
    exact ⟨hlow, hmid, twoRangeLength_le_two_mul_sqrt hcls, hs0⟩
  refine averagedMeanSquare_moebius_of_headSmall (hh := scaledLength c β)
    (ω := fun x => c * (((twoRangeLength β x : ℕ) : ℝ) / ((scaledFibreLength c β x : ℕ) : ℝ))
      * Real.log (Real.log x))
    (B := fun x => 2 * B x + 4 * twoRangeTop β x
      * (((twoRangeLength β x : ℕ) : ℝ) - ((scaledFibreLength c β x : ℕ) : ℝ)) ^ 2)
    (tendsto_scaledLength hc0 hβ0) ?_ ?_ ?_
  · filter_upwards [hbasic, hgeom, hB] with x hx hg hb
    obtain ⟨hx4, hsc1, hscs, hcls, hu1, hcl1, hlogx⟩ := hx
    obtain ⟨hlow, hmid, hhigh, hs0⟩ := hg
    have hM'0 : (0 : ℝ) < ((scaledFibreLength c β x : ℕ) : ℝ) := lt_of_lt_of_le hs0 hlow
    have hsc0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
    have hcl0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hllnn : (0 : ℝ) ≤ Real.log (Real.log x) :=
      le_trans (le_of_lt (one_div_pos.mpr hc0)) hu1
    have hTop0 : (0 : ℝ) ≤ twoRangeTop β x := by
      rw [twoRangeTop, twoRangeCut]
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hcl0.le) hllnn
    have hheadT : headT₀ x (scaledLength c β x)
        (c * (((twoRangeLength β x : ℕ) : ℝ) / ((scaledFibreLength c β x : ℕ) : ℝ))
          * Real.log (Real.log x)) = twoRangeTop β x := by
      rw [headT₀, headG, twoRangeTop, twoRangeCut, scaledLength,
        show ⌊Real.sqrt x + c * cardLength β x⌋₊ = scaledFibreLength c β x from rfl]
      field_simp
    have hratio1 : (1 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ)
        / ((scaledFibreLength c β x : ℕ) : ℝ) := by
      rw [le_div_iff₀ hM'0, one_mul]
      exact hmid
    have hω1 : (1 : ℝ) ≤ c * (((twoRangeLength β x : ℕ) : ℝ)
        / ((scaledFibreLength c β x : ℕ) : ℝ)) * Real.log (Real.log x) := by
      have hll : (0 : ℝ) < Real.log (Real.log x) :=
        lt_of_lt_of_le (one_div_pos.mpr hc0) hu1
      have h1 : c * 1 * (1 / c) ≤ c * (((twoRangeLength β x : ℕ) : ℝ)
          / ((scaledFibreLength c β x : ℕ) : ℝ)) * Real.log (Real.log x) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hratio1 hc0.le) hu1
          (le_of_lt (one_div_pos.mpr hc0)) (by positivity)
      have hone : c * 1 * (1 / c) = 1 := by field_simp
      linarith [h1, hone.symm.le, hone.le]
    have hB'0 : (0 : ℝ) ≤ 2 * B x + 4 * twoRangeTop β x
        * (((twoRangeLength β x : ℕ) : ℝ) - ((scaledFibreLength c β x : ℕ) : ℝ)) ^ 2 := by
      have := hb.1
      have hsq := sq_nonneg (((twoRangeLength β x : ℕ) : ℝ)
        - ((scaledFibreLength c β x : ℕ) : ℝ))
      nlinarith [hTop0]
    refine ⟨hx4, hsc1, hscs, hω1, hB'0, ?_⟩
    rw [hheadT]
    have hsub : (Finset.Icc 1 (scaledFibreLength c β x)) ⊆ Finset.Icc 1 (twoRangeLength β x) := by
      refine Finset.Icc_subset_Icc_right ?_
      exact scaledFibreLength_le hc1 x
    have hfib : fibreIndex x (scaledLength c β x) = Finset.Icc 1 (scaledFibreLength c β x) := rfl
    rw [hfib]
    have hmain := setIntegral_normSq_logPoly_le_of_subset
      (a := fun n => ((μ n : ℤ) : ℂ)) norm_moebius_complex_le_one_moebiusHeadGate hsub hTop0 hb.2
    have hcardT : ((Finset.Icc 1 (twoRangeLength β x)).card : ℝ)
        = ((twoRangeLength β x : ℕ) : ℝ) := by
      rw [Nat.card_Icc]
      norm_num
    have hcardS : ((Finset.Icc 1 (scaledFibreLength c β x)).card : ℝ)
        = ((scaledFibreLength c β x : ℕ) : ℝ) := by
      rw [Nat.card_Icc]
      norm_num
    rw [hcardT, hcardS] at hmain
    exact hmain
  · refine Filter.tendsto_atTop_mono' _ ?_
      (Filter.Tendsto.const_mul_atTop hc0
        (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))
    filter_upwards [hbasic, hgeom] with x hx hg
    obtain ⟨-, -, -, -, hu1, -, -⟩ := hx
    obtain ⟨hlow, hmid, -, hs0⟩ := hg
    have hM'0 : (0 : ℝ) < ((scaledFibreLength c β x : ℕ) : ℝ) := lt_of_lt_of_le hs0 hlow
    have hratio1 : (1 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ)
        / ((scaledFibreLength c β x : ℕ) : ℝ) := by
      rw [le_div_iff₀ hM'0, one_mul]
      exact hmid
    have hll : (0 : ℝ) < Real.log (Real.log x) :=
      lt_of_lt_of_le (one_div_pos.mpr hc0) hu1
    show c * Real.log (Real.log x) ≤ _
    have hstep : c * 1 ≤ c * (((twoRangeLength β x : ℕ) : ℝ)
        / ((scaledFibreLength c β x : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hratio1 hc0.le
    nlinarith [hstep, hll.le]
  · have hlimA : Tendsto (fun x : ℝ => 8 * (B x / (((twoRangeLength β x : ℕ) : ℝ)) ^ 2))
        atTop (𝓝 0) := by
      have h := hBrel.const_mul (8 : ℝ)
      rwa [mul_zero] at h
    have hlimB : Tendsto (fun x : ℝ =>
        32 * ((Real.log x) ^ (1 : ℝ) * (cardLength β x / Real.sqrt x))) atTop (𝓝 0) := by
      have h := (tendsto_rpow_log_mul_cardLength_div_sqrt hβ0 hβ1 1).const_mul (32 : ℝ)
      rwa [mul_zero] at h
    have hsum := hlimA.add hlimB
    rw [add_zero] at hsum
    refine squeeze_zero' ?_ ?_ hsum
    · filter_upwards [hbasic, hgeom, hB] with x hx hg hb
      obtain ⟨-, -, -, -, hu1, -, -⟩ := hx
      obtain ⟨hlow, -, -, hs0⟩ := hg
      have hM'0 : (0 : ℝ) < ((scaledFibreLength c β x : ℕ) : ℝ) := lt_of_lt_of_le hs0 hlow
      have hllnn : (0 : ℝ) ≤ Real.log (Real.log x) :=
        le_trans (le_of_lt (one_div_pos.mpr hc0)) hu1
      have hTop0 : (0 : ℝ) ≤ twoRangeTop β x := by
        rw [twoRangeTop, twoRangeCut]
        exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (cardLength_pos β x).le) hllnn
      have hsq := sq_nonneg (((twoRangeLength β x : ℕ) : ℝ)
        - ((scaledFibreLength c β x : ℕ) : ℝ))
      have hnum : (0 : ℝ) ≤ 2 * B x + 4 * twoRangeTop β x
          * (((twoRangeLength β x : ℕ) : ℝ) - ((scaledFibreLength c β x : ℕ) : ℝ)) ^ 2 := by
        nlinarith [hb.1]
      positivity
    · filter_upwards [hbasic, hgeom, hB] with x hx hg hb
      obtain ⟨hx4, hsc1, hscs, hcls, hu1, hcl1, hlogx⟩ := hx
      obtain ⟨hlow, hmid, hhigh, hs0⟩ := hg
      have hw0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
      have hLl0 : (0 : ℝ) ≤ Real.log (Real.log x) :=
        le_trans (le_of_lt (one_div_pos.mpr hc0)) hu1
      have hLlog : Real.log (Real.log x) ≤ Real.log x := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Real.log x)
        linarith
      have hgap : ((twoRangeLength β x : ℕ) : ℝ) - ((scaledFibreLength c β x : ℕ) : ℝ)
          ≤ 2 * cardLength β x := by
        have hup : ((twoRangeLength β x : ℕ) : ℝ) ≤ Real.sqrt x + cardLength β x := by
          rw [twoRangeLength]
          exact Nat.floor_le (add_nonneg (Real.sqrt_nonneg x) hw0.le)
        have hdown : Real.sqrt x + scaledLength c β x - 1
            ≤ ((scaledFibreLength c β x : ℕ) : ℝ) := by
          have := Nat.sub_one_lt_floor (Real.sqrt x + scaledLength c β x)
          rw [scaledFibreLength]
          linarith
        have hsc0 : (0 : ℝ) < scaledLength c β x := scaledLength_pos hc0 β x
        linarith
      have hTopv : twoRangeTop β x
          = ((twoRangeLength β x : ℕ) : ℝ) / cardLength β x * Real.log (Real.log x) := rfl
      rw [hTopv, Real.rpow_one]
      exact scaledBudget_ratio_le hb.1 (lt_of_lt_of_le hs0 hlow) hw0 hs0 hlogx hLl0 hLlog
        hlow hmid hhigh hgap

end RHTower.Sieve
