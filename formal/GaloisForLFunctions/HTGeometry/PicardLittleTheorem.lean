import GaloisForLFunctions.HTGeometry.JensenProximityReciprocalBound
import GaloisForLFunctions.HTGeometry.BriotBouquetTwoRootNoGo

/-!
# Picard's little theorem

An entire function that omits two distinct values is constant.

The proof is the second main theorem with every counting term removed.  Both `N(r, a_j)` vanish
because the values are omitted; the ramification term `m(r, 1/F')` is discharged by Jensen's
*inequality* rather than by the zero-free identity, so the derivative is allowed to vanish — the
zeros of `F'` contribute a non-negative counting term which only improves the estimate.  What is
left, after the logarithmic-derivative estimate at the two omitted values and the Borel growth lemma,
is `T(r,F) = O(log r)`, hence `F` is a polynomial; and a polynomial that omits a value is constant.

The nonvanishing needed to run the second main theorem is codiscrete rather than global: the
derivative of a nonconstant entire function is a nonzero entire function, so its zeros are isolated.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Real Set Filter

/-- An entire function that is not identically zero has finite meromorphic order at every point. -/
theorem meromorphicOrderAt_ne_top_of_exists_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hne : ∃ w, g w ≠ 0) (u : ℂ) : meromorphicOrderAt g u ≠ ⊤ := by
  intro htop
  obtain ⟨w, hw⟩ := hne
  have hA : AnalyticAt ℂ g u := hg.analyticAt u
  rw [hA.meromorphicOrderAt_eq] at htop
  have hord : analyticOrderAt g u = ⊤ := by
    by_contra hc
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hc
    rw [← hn] at htop
    exact absurd htop (by exact_mod_cast WithTop.coe_ne_top)
  have hnhds : g =ᶠ[nhds u] 0 := analyticOrderAt_eq_top.mp hord
  have hAn : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hall := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ u) hnhds
  exact hw (hall (Set.mem_univ w))

/-- A nonconstant entire function has a nonvanishing derivative somewhere. -/
theorem exists_deriv_ne_zero_of_nonconstant {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) : ∃ w, deriv F w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hnc ⟨F 0, funext fun z => is_const_of_deriv_eq_zero hF hcon z 0⟩

/-- A nonconstant entire function is not identically zero. -/
theorem exists_ne_zero_of_nonconstant {F : ℂ → ℂ}
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) : ∃ w, F w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hnc ⟨0, funext hcon⟩

/-- The zeros of the derivative of a nonconstant entire function are codiscrete on every circle. -/
theorem codiscrete_deriv_ne_zero_of_nonconstant {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) (r : ℝ) :
    ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv F z ≠ 0 := by
  refine MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero
    (fun z _ => ((hF.deriv).analyticAt z).meromorphicAt) ?_
  intro u _
  exact meromorphicOrderAt_ne_top_of_exists_ne_zero hF.deriv
    (exists_deriv_ne_zero_of_nonconstant hF hnc) u

set_option maxHeartbeats 1000000 in
/-- **The omitting second main theorem, with the derivative allowed to vanish.**  Splitting
`F' = (F − a₁)·(F'/(F − a₁))` keeps every logarithmic derivative taken at an omitted value; the
ramification term is bounded by Jensen's inequality, whose correction is the trailing coefficient of
`F'` at the origin. -/
theorem characteristic_le_of_omits_two_shifted_general {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂)
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) {r K : ℝ} (hr : 1 ≤ r)
    (hfmt : ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + K) :
    characteristic F ⊤ r
      ≤ 2 * proximity (fun z => deriv F z / (F z - a₁)) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₂)) ⊤ r
        + ((2 * K + 2 * Real.posLog (2 / ‖a₁ - a₂‖)
            + Real.posLog (2 * (2 / ‖a₁ - a₂‖)) + Real.log 2 + Real.log 2)
          - Real.log ‖meromorphicTrailingCoeffAt (deriv F) 0‖
          + (Real.posLog ‖a₁‖ + Real.log 2)) := by
  classical
  have hr0 : r ≠ 0 := by intro h; rw [h] at hr; linarith
  have hδ : 0 < ‖a₁ - a₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hane)
  have hsep : ∀ i j : Fin 2, i ≠ j → ‖a₁ - a₂‖ ≤ ‖(![a₁, a₂] i) - (![a₁, a₂] j)‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [norm_sub_rev]
  have hcod := codiscrete_deriv_ne_zero_of_nonconstant hF hnc r
  have hsmt := mul_characteristic_le_of_separated_entire (f := F) ![a₁, a₂] hδ hr0 hsep hF hfmt hcod
  have hcount : ∑ j : Fin 2, logCounting F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r = 0 := by
    have hz1 : logCounting F ((a₁ : ℂ) : WithTop ℂ) r = 0 := by
      rw [logCounting_eq_zero_of_omits hF h₁]; rfl
    have hz2 : logCounting F ((a₂ : ℂ) : WithTop ℂ) r = 0 := by
      rw [logCounting_eq_zero_of_omits hF h₂]; rfl
    rw [Fin.sum_univ_two]
    show logCounting F ((a₁ : ℂ) : WithTop ℂ) r + logCounting F ((a₂ : ℂ) : WithTop ℂ) r = 0
    rw [hz1, hz2, add_zero]
  have hprox : ∑ j : Fin 2, proximity (fun z => deriv F z / (F z - ![a₁, a₂] j)) ⊤ r
      = proximity (fun z => deriv F z / (F z - a₁)) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₂)) ⊤ r := by
    rw [Fin.sum_univ_two]
    rfl
  have hderivdiff : Differentiable ℂ (deriv F) := hF.deriv
  have hram : proximity (fun z => (deriv F z)⁻¹) ⊤ r
      ≤ proximity (deriv F) ⊤ r - Real.log ‖meromorphicTrailingCoeffAt (deriv F) 0‖ :=
    proximity_inv_le_sub hderivdiff hr
  have hshiftne : ∀ z, F z - a₁ ≠ 0 := fun z h => h₁ z (by linear_combination h)
  have hmshift : Meromorphic (fun z => F z - a₁) :=
    fun z => (((hF.sub_const a₁)).analyticAt z).meromorphicAt
  have hmquot : Meromorphic (fun z => deriv F z / (F z - a₁)) :=
    fun z => ((hderivdiff.analyticAt z).meromorphicAt).div (hmshift z)
  have heqfac : deriv F =ᶠ[codiscreteWithin (sphere (0 : ℂ) |r|)]
      (fun z => F z - a₁) * fun z => deriv F z / (F z - a₁) := by
    filter_upwards with z
    show deriv F z = (F z - a₁) * (deriv F z / (F z - a₁))
    field_simp
    rw [mul_div_assoc, div_self (hshiftne z), mul_one]
  have hsplit : proximity (deriv F) ⊤ r
      ≤ proximity (fun z => F z - a₁) ⊤ r
        + proximity (fun z => deriv F z / (F z - a₁)) ⊤ r :=
    proximity_top_le_of_codiscrete_mul hr0 heqfac hmshift hmquot
  have hAF : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hAc : AnalyticOnNhd ℂ (fun _ : ℂ => -a₁) Set.univ := fun z _ => analyticAt_const
  have hAs : AnalyticOnNhd ℂ (fun z => F z - a₁) Set.univ :=
    fun z _ => ((hF.sub_const a₁)).analyticAt z
  have hshiftle : proximity (fun z => F z - a₁) ⊤ r
      ≤ proximity F ⊤ r + (Real.posLog ‖a₁‖ + Real.log 2) := by
    have hadd := GaloisForLFunctions.Nevanlinna.characteristic_add_le hAF hAc r
    have hconst := GaloisForLFunctions.Nevanlinna.characteristic_const_eq (-a₁) r
    have hfun : (fun z => F z + -a₁) = fun z => F z - a₁ := by funext z; ring
    rw [hfun, hconst, norm_neg] at hadd
    rw [← GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd hAs,
      ← GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd hAF]
    linarith
  have hchar : proximity F ⊤ r = characteristic F ⊤ r := by
    rw [characteristic_top_eq_proximity_of_analyticOnNhd hAF]
  rw [hcount, hprox, zero_add] at hsmt
  push_cast at hsmt
  linarith [hsmt, hram, hsplit, hshiftle, hchar]

set_option maxHeartbeats 1000000 in
/-- **The quantitative bound with the derivative allowed to vanish.**  For an entire `F` omitting two
values, the characteristic at radius `r` is bounded by a logarithm of the characteristic at any
larger radius `R`. -/
theorem characteristic_le_log_of_omits_two_general {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂)
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {K : ℝ}
    {r R : ℝ} (hr : 1 ≤ r) (hrR : r < R) (hR : 1 ≤ R)
    (hfmt : ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + K) :
    characteristic F ⊤ r
      ≤ (3 / α) * Real.log (1 + (2 * R / (R - r) ^ 2
          * (2 * characteristic F ⊤ R
            + (2 * (Real.posLog ‖a₁‖ + Real.log 2) + 2 * (Real.posLog ‖a₂‖ + Real.log 2)
              + |Real.log ‖F 0 - a₁‖| + |Real.log ‖F 0 - a₂‖|))) ^ α)
        + ((2 * K + 2 * Real.posLog (2 / ‖a₁ - a₂‖)
            + Real.posLog (2 * (2 / ‖a₁ - a₂‖)) + Real.log 2 + Real.log 2)
          - Real.log ‖meromorphicTrailingCoeffAt (deriv F) 0‖
          + (Real.posLog ‖a₁‖ + Real.log 2)) := by
  classical
  have hr0 : 0 < r := by linarith
  set X : ℝ := 2 * R / (R - r) ^ 2 with hX
  have hRpos : (0 : ℝ) < R := by linarith
  have hRr : (0 : ℝ) < R - r := by linarith
  have hX0 : 0 < X := by
    rw [hX]
    positivity
  set Cbig : ℝ := 2 * (Real.posLog ‖a₁‖ + Real.log 2) + 2 * (Real.posLog ‖a₂‖ + Real.log 2)
    + |Real.log ‖F 0 - a₁‖| + |Real.log ‖F 0 - a₂‖| with hCbig
  have hTR : 0 ≤ characteristic F ⊤ R := characteristic_nonneg_of_entire hF R
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkey : ∀ a : ℂ, a = a₁ ∨ a = a₂ →
      2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖|
        ≤ 2 * characteristic F ⊤ R + Cbig := by
    intro a ha12
    have hshift := characteristic_sub_const_le hF a R
    have habs : (0 : ℝ) ≤ |Real.log ‖F 0 - a‖| := abs_nonneg _
    rcases ha12 with rfl | rfl
    · have h2 : (0 : ℝ) ≤ 2 * (Real.posLog ‖a₂‖ + Real.log 2) := by
        have := Real.posLog_nonneg (x := ‖a₂‖)
        linarith
      have h3 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₂‖| := abs_nonneg _
      rw [hCbig]
      linarith
    · have h2 : (0 : ℝ) ≤ 2 * (Real.posLog ‖a₁‖ + Real.log 2) := by
        have := Real.posLog_nonneg (x := ‖a₁‖)
        linarith
      have h3 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₁‖| := abs_nonneg _
      rw [hCbig]
      linarith
  have hbound : ∀ a : ℂ, (∀ z, F z ≠ a) → a = a₁ ∨ a = a₂ →
      proximity (fun z => deriv F z / (F z - a)) ⊤ r
        ≤ (1 / α) * Real.log (1 + (X * (2 * characteristic F ⊤ R + Cbig)) ^ α) := by
    intro a ha ha12
    refine le_trans (proximity_logDeriv_le_of_omits hα0 hα1 hr0 hrR hR hF ha) ?_
    have hmono : X * (2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖|)
        ≤ X * (2 * characteristic F ⊤ R + Cbig) :=
      mul_le_mul_of_nonneg_left (hkey a ha12) hX0.le
    have hnn : (0 : ℝ) ≤ X * (2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖|) := by
      have h0 : 0 ≤ characteristic (fun w => F w - a) ⊤ R :=
        characteristic_nonneg_of_entire (hF.sub_const a) R
      have h1 : (0 : ℝ) ≤ |Real.log ‖F 0 - a‖| := abs_nonneg _
      have : (0 : ℝ) ≤ 2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖| := by
        linarith
      positivity
    have hrpow := Real.rpow_le_rpow hnn hmono hα0.le
    have hlogle : Real.log (1 + (X * (2 * characteristic (fun w => F w - a) ⊤ R
          + |Real.log ‖F 0 - a‖|)) ^ α)
        ≤ Real.log (1 + (X * (2 * characteristic F ⊤ R + Cbig)) ^ α) := by
      refine Real.log_le_log (by positivity) (by linarith)
    have hαinv : (0 : ℝ) ≤ 1 / α := by positivity
    exact mul_le_mul_of_nonneg_left hlogle hαinv
  have hsmt := characteristic_le_of_omits_two_shifted_general hF hane h₁ h₂ hnc hr hfmt
  have hb1 := hbound a₁ h₁ (Or.inl rfl)
  have hb2 := hbound a₂ h₂ (Or.inr rfl)
  have hthree : (3 : ℝ) / α = 3 * (1 / α) := by ring
  rw [hthree]
  linarith [hsmt, hb1, hb2]

set_option maxHeartbeats 2000000 in
/-- **The characteristic of a function omitting two values is `O(log r)`**, with no hypothesis on the
zeros of the derivative.  The Borel growth lemma at exponent `1/2` supplies, inside every window, a
radius where the shifted characteristic does not double; there the quantitative bound collapses to a
logarithm. -/
theorem exists_characteristic_le_log_of_omits_two_general {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂)
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) {K : ℝ}
    (hfmt : ∀ r : ℝ, r ≠ 0 → ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + K) :
    ∃ A B : ℝ, 1 ≤ A ∧ ∀ s : ℝ, 1 ≤ s → characteristic F ⊤ s ≤ 6 * Real.log (s + A) + B := by
  classical
  set W : ℝ := Nevanlinna.borelWindow (1 / 2) with hW
  have hW1 : 1 ≤ W := Nevanlinna.one_le_borelWindow _
  set Cbig : ℝ := 2 * (Real.posLog ‖a₁‖ + Real.log 2) + 2 * (Real.posLog ‖a₂‖ + Real.log 2)
    + |Real.log ‖F 0 - a₁‖| + |Real.log ‖F 0 - a₂‖| with hCbigdef
  have hCbig0 : 0 ≤ Cbig := by
    have h1 := Real.posLog_nonneg (x := ‖a₁‖)
    have h2 := Real.posLog_nonneg (x := ‖a₂‖)
    have h3 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h4 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₁‖| := abs_nonneg _
    have h5 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₂‖| := abs_nonneg _
    rw [hCbigdef]
    linarith
  set Csmall : ℝ := (2 * K + 2 * Real.posLog (2 / ‖a₁ - a₂‖)
      + Real.posLog (2 * (2 / ‖a₁ - a₂‖)) + Real.log 2 + Real.log 2)
    - Real.log ‖meromorphicTrailingCoeffAt (deriv F) 0‖
    + (Real.posLog ‖a₁‖ + Real.log 2) with hCsmalldef
  set D : ℝ := 4 + Cbig with hD
  have hD4 : (4 : ℝ) ≤ D := by rw [hD]; linarith
  set B' : ℝ := max (6 * Real.log 2 + Csmall) 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨max 6 (W + 1), 6 * Real.log (2 * D) + 2 * B' + 1156, le_max_of_le_left (by norm_num), ?_⟩
  intro s hs
  obtain ⟨x, hxmem, hxborel⟩ :=
    Nevanlinna.exists_mem_Icc_lt_two_mul_rpow_window (monotone_charPlusOne hF)
      (one_le_charPlusOne hF) (by norm_num : (0:ℝ) < 1/2) s
  have hxs : s ≤ x := hxmem.1
  have hxW : x ≤ s + W := hxmem.2
  have hx1 : (1 : ℝ) ≤ x := le_trans hs hxs
  have hx0 : (0 : ℝ) < x := by linarith
  set T₀ : ℝ := characteristic F ⊤ x with hT₀
  have hT₀0 : 0 ≤ T₀ := characteristic_nonneg_of_entire hF x
  have hTx : charPlusOne F x = T₀ + 1 := charPlusOne_eq hx1
  set step : ℝ := (charPlusOne F x) ^ (-(1/2 : ℝ)) with hstep
  have hstep0 : 0 < step := Real.rpow_pos_of_pos (by linarith [one_le_charPlusOne hF x]) _
  have hstep1 : step ≤ 1 := by
    rw [hstep]
    refine Real.rpow_le_one_of_one_le_of_nonpos (one_le_charPlusOne hF x) (by norm_num)
  set R : ℝ := x + step with hR
  have hxR : x < R := by rw [hR]; linarith
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; linarith
  have hRx1 : R ≤ x + 1 := by rw [hR]; linarith
  have hcharR : characteristic F ⊤ R ≤ 2 * T₀ + 1 := by
    have h := hxborel
    rw [hTx] at h
    have hR' : charPlusOne F R = characteristic F ⊤ R + 1 := charPlusOne_eq hR1
    rw [hR'] at h
    linarith
  have hmain := characteristic_le_log_of_omits_two_general hF hane h₁ h₂ hnc
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1) hx1 hxR hR1 (hfmt x (ne_of_gt hx0))
  rw [← hCbigdef, ← hCsmalldef, ← hT₀] at hmain
  have hstepsq : (R - x) ^ 2 = (T₀ + 1)⁻¹ := by
    have hxx : R - x = step := by rw [hR]; ring
    rw [hxx, hstep, hTx, ← Real.rpow_natCast ((T₀ + 1) ^ (-(1/2 : ℝ))) 2,
      ← Real.rpow_mul (by linarith)]
    norm_num
    rw [Real.rpow_neg_one]
  have hT1pos : (0 : ℝ) < T₀ + 1 := by linarith
  have hfactor : 2 * R / (R - x) ^ 2 = 2 * R * (T₀ + 1) := by
    rw [hstepsq]
    field_simp
  set y : ℝ := 2 * R / (R - x) ^ 2 * (2 * characteristic F ⊤ R + Cbig) with hy
  have hy0 : 0 ≤ y := by
    have h1 : 0 ≤ characteristic F ⊤ R := characteristic_nonneg_of_entire hF R
    have h2 : (0 : ℝ) < 2 * R / (R - x) ^ 2 := by
      rw [hfactor]
      positivity
    rw [hy]
    have : (0 : ℝ) ≤ 2 * characteristic F ⊤ R + Cbig := by linarith
    positivity
  have hyle : y ≤ 2 * D * (x + 1) * (T₀ + 1) ^ 2 := by
    rw [hy, hfactor]
    have hinner : 2 * characteristic F ⊤ R + Cbig ≤ D * (T₀ + 1) := by
      rw [hD]
      nlinarith [hcharR, hCbig0, hT₀0]
    have hRle : 2 * R * (T₀ + 1) ≤ 2 * (x + 1) * (T₀ + 1) := by nlinarith [hRx1, hT1pos]
    have hinner0 : (0 : ℝ) ≤ 2 * characteristic F ⊤ R + Cbig := by
      have := characteristic_nonneg_of_entire hF R
      linarith
    calc 2 * R * (T₀ + 1) * (2 * characteristic F ⊤ R + Cbig)
        ≤ 2 * (x + 1) * (T₀ + 1) * (2 * characteristic F ⊤ R + Cbig) :=
          mul_le_mul_of_nonneg_right hRle hinner0
      _ ≤ 2 * (x + 1) * (T₀ + 1) * (D * (T₀ + 1)) := by
          refine mul_le_mul_of_nonneg_left hinner ?_
          nlinarith [hx1, hT1pos]
      _ = 2 * D * (x + 1) * (T₀ + 1) ^ 2 := by ring
  have hbig1 : (1 : ℝ) ≤ 2 * D * (x + 1) * (T₀ + 1) ^ 2 := by
    have hq1 : (1:ℝ) ≤ (T₀ + 1) ^ 2 := by nlinarith [hT₀0]
    have hq2 : (2:ℝ) ≤ x + 1 := by linarith
    have h2 : (16 : ℝ) ≤ 2 * D * (x + 1) := by nlinarith [hD4, hq2]
    nlinarith [h2, hq1]
  have hposlog : Real.posLog y ≤ Real.log (2 * D) + Real.log (x + 1) + 2 * Real.log (T₀ + 1) := by
    have hmono : Real.posLog y ≤ Real.posLog (2 * D * (x + 1) * (T₀ + 1) ^ 2) :=
      Real.posLog_le_posLog hy0 hyle
    have heq : Real.posLog (2 * D * (x + 1) * (T₀ + 1) ^ 2)
        = Real.log (2 * D * (x + 1) * (T₀ + 1) ^ 2) := by
      refine Real.posLog_eq_log ?_
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * D * (x + 1) * (T₀ + 1) ^ 2)]
      exact hbig1
    rw [heq] at hmono
    have hsplit : Real.log (2 * D * (x + 1) * (T₀ + 1) ^ 2)
        = Real.log (2 * D) + Real.log (x + 1) + 2 * Real.log (T₀ + 1) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow]
      push_cast
      ring
    linarith [hmono, hsplit]
  have hlogy : Real.log (1 + y ^ ((1:ℝ)/2))
      ≤ Real.log 2 + (1/2) * (Real.log (2 * D) + Real.log (x + 1) + 2 * Real.log (T₀ + 1)) := by
    refine le_trans (log_one_add_rpow_le hy0 (by norm_num)) ?_
    linarith [hposlog]
  have hself : T₀ ≤ (3 * Real.log (2 * D) + 3 * Real.log (x + 1))
      + 6 * Real.log (T₀ + 1) + B' := by
    have hval : (3 : ℝ) / (1/2) = 6 := by norm_num
    rw [hval] at hmain
    have hBle : 6 * Real.log 2 + Csmall ≤ B' := le_max_left _ _
    linarith [hmain, hlogy, hBle]
  have hAB0 : (0 : ℝ) ≤ (3 * Real.log (2 * D) + 3 * Real.log (x + 1)) + B' := by
    have h1 : (0 : ℝ) ≤ Real.log (2 * D) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    linarith
  have hfinal := le_of_le_add_six_log hT₀0 hAB0 hself
  have hmonos : characteristic F ⊤ s ≤ T₀ := by
    have hmono := ValueDistribution.characteristic_monotoneOn
      (f := F) (fun z => (hF.analyticAt z).meromorphicAt)
    exact hmono (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr hx0) hxs
  have hlogx : Real.log (x + 1) ≤ Real.log (s + max 6 (W + 1)) := by
    refine Real.log_le_log (by linarith) ?_
    have : W + 1 ≤ max 6 (W + 1) := le_max_right _ _
    linarith
  linarith [hfinal, hmonos, hlogx]

set_option maxHeartbeats 1000000 in
/-- **Picard's little theorem.**  An entire function that omits two distinct values is constant.
The second main theorem loses both counting terms to the omitted values and its ramification term to
Jensen's inequality, so the characteristic grows at most logarithmically; the function is therefore a
polynomial, and a polynomial that omits a value is constant. -/
theorem eq_const_of_omits_two {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂) :
    ∃ b : ℂ, F = fun _ => b := by
  classical
  by_contra hnc
  have horder : ∀ u, meromorphicOrderAt F u ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_exists_ne_zero hF (exists_ne_zero_of_nonconstant hnc)
  have hmF : Meromorphic F := fun z => (hF.analyticAt z).meromorphicAt
  have hmS : ∀ a : ℂ, Meromorphic (F - fun _ => a) :=
    fun a z => ((hF.sub_const a).analyticAt z).meromorphicAt
  set K₁ : ℝ := (Real.posLog ‖a₁‖ + Real.log 2)
    + max |Real.log ‖((F - fun _ : ℂ => a₁) : ℂ → ℂ) 0‖|
        |Real.log ‖meromorphicTrailingCoeffAt ((F - fun _ : ℂ => a₁) : ℂ → ℂ) 0‖| with hK₁
  set K₂ : ℝ := (Real.posLog ‖a₂‖ + Real.log 2)
    + max |Real.log ‖((F - fun _ : ℂ => a₂) : ℂ → ℂ) 0‖|
        |Real.log ‖meromorphicTrailingCoeffAt ((F - fun _ : ℂ => a₂) : ℂ → ℂ) 0‖| with hK₂
  have hfmt : ∀ r : ℝ, r ≠ 0 → ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + max K₁ K₂ := by
    intro r _ j
    fin_cases j
    · have h := characteristic_top_le_characteristic_coe (f := F) (a₀ := a₁) (r := r) hmF (hmS a₁)
      have hle : K₁ ≤ max K₁ K₂ := le_max_left _ _
      show characteristic F ⊤ r ≤ characteristic F ((a₁ : ℂ) : WithTop ℂ) r + max K₁ K₂
      rw [← hK₁] at h
      linarith
    · have h := characteristic_top_le_characteristic_coe (f := F) (a₀ := a₂) (r := r) hmF (hmS a₂)
      have hle : K₂ ≤ max K₁ K₂ := le_max_right _ _
      show characteristic F ⊤ r ≤ characteristic F ((a₂ : ℂ) : WithTop ℂ) r + max K₁ K₂
      rw [← hK₂] at h
      linarith
  obtain ⟨A, B, hA, hbd⟩ :=
    exists_characteristic_le_log_of_omits_two_general hF hane h₁ h₂ hnc hfmt
  obtain ⟨M, hM⟩ := exists_polyGrowth_of_characteristic_le_log hF horder hA hbd
  obtain ⟨p, hp⟩ := exists_polynomial_of_polynomial_growth hF hM
  have hroot : ∀ w : ℂ, (p - Polynomial.C a₁).eval w ≠ 0 := by
    intro w hw
    refine h₁ w ?_
    rw [hp w]
    have : p.eval w - a₁ = 0 := by simpa using hw
    linear_combination this
  have hdeg : (p - Polynomial.C a₁).natDegree = 0 := by
    by_contra hne
    have hpos : 0 < (p - Polynomial.C a₁).degree := by
      have hne0 : p - Polynomial.C a₁ ≠ 0 := by
        intro hz
        exact hroot 0 (by rw [hz]; simp)
      rw [Polynomial.degree_eq_natDegree hne0]
      exact_mod_cast Nat.pos_of_ne_zero hne
    obtain ⟨w, hw⟩ := Complex.exists_root hpos
    exact hroot w hw
  obtain ⟨b, hb⟩ := Polynomial.natDegree_eq_zero.mp hdeg
  refine hnc ⟨b + a₁, ?_⟩
  funext z
  have hpz : p.eval z - a₁ = b := by
    have := congrArg (fun q : Polynomial ℂ => q.eval z) hb
    simp only [Polynomial.eval_sub, Polynomial.eval_C] at this
    exact this.symm
  rw [hp z]
  linear_combination hpz

/-- **A nonconstant entire function omits at most one value.**  The complement of its range is a
subsingleton — the sharp form of Picard's little theorem, attained by `exp`, which omits exactly
`0`. -/
theorem subsingleton_compl_range_of_nonconstant {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hnc : ¬ ∃ b : ℂ, F = fun _ => b) : (Set.range F)ᶜ.Subsingleton := by
  intro a₁ ha₁ a₂ ha₂
  by_contra hane
  refine hnc (eq_const_of_omits_two hF hane ?_ ?_)
  · intro z hz
    exact ha₁ ⟨z, hz⟩
  · intro z hz
    exact ha₂ ⟨z, hz⟩

end GaloisForLFunctions.HTGeometry
