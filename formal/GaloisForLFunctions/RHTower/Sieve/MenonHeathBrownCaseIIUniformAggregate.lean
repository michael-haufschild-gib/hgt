import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIAmplitudeCancellation

/-!
# Uniform aggregation of Menon's Case II

Every Case-II selection has a factor at least `a^(1/8)`: this is the defining medium-factor
lower edge, while a long factor is at least `a^(1/3)`.  Combined with selected-factor
cancellation, the common amplitude is therefore uniform across all degree-three
Heath--Brown labels.  Summing the color-fibre bounds retains the complete label multiplicity.
-/

namespace RHTower.Sieve

noncomputable section

/-- Every degree-three Case-II selection has selected factor at least `a^(1/8)`, in both the
medium and long branches. -/
theorem menonHeathBrownCaseIISelection_factorLower
    {L X a cells : ℕ} {T0 t sigma tau V Δ Q y : ℝ}
    {label : MenonHeathBrownCaseIILabel L X cells}
    (ha : 1 ≤ a)
    (hselection :
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma tau V Δ Q y label) :
    (a : ℝ) ^ (1 / 8 : ℝ) ≤
      (((2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) := by
  cases hlong : label.isLong with
  | false =>
      have hbranch := hselection.2.2.2.2.2
      simp only [hlong, Bool.false_eq_true, ↓reduceIte] at hbranch
      exact hbranch.1
  | true =>
      have hbranch := hselection.2.2.2.2.2
      simp only [hlong, ↓reduceIte] at hbranch
      have haReal : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hexponents : (1 / 8 : ℝ) ≤ 1 / 3 := by norm_num
      exact (Real.rpow_le_rpow_of_exponent_le haReal hexponents).trans hbranch.1.le

/-- The degree-three Case-II color fibres aggregate with a single physical-scale amplitude.
The lower amplitude retains `min(T,a^(delta/8))`; the upper energy retains the exact
`(a/64)^(2-2*sigma)` box-window power and every label is counted. -/
theorem card_mul_sq_le_menonHeathBrownCaseII_uniform
    {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
    (S : Finset ℕ) (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    {selectedY tau : ℕ → ℝ}
    (ha : 1 ≤ a) (hX : 1 ≤ X) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (hΔT : Δ / 2 ≤ T)
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (hactive : ∀ label : MenonHeathBrownCaseIILabel L X cells,
      (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
        heathBrownBoxFactorKind 3 label.box.m label.factor = .log) ∧
      ((heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
          MenonHeathBrownCaseIIZetaOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
          MenonHeathBrownCaseIILogOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        MenonHeathBrownCaseIIDerivativeTwentySixBound
          L X cells S color sigma Δ Q T label))
    (hsigma : 1 ≤ sigma) :
    let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
    let Vmin : ℝ :=
      min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope X) *
        menonHeathBrownCaseIICoreThreshold L X Q
    let Hmax : ℝ :=
      (12 * W ^ 2 *
          (1 + Real.log (W * (X : ℝ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
    (S.card : ℝ) * Vmin ^ 2 ≤
      (Fintype.card (MenonHeathBrownCaseIILabel L X cells) : ℝ) * Hmax := by
  let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
  let Vmin : ℝ :=
    min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope X) *
      menonHeathBrownCaseIICoreThreshold L X Q
  let Hmax : ℝ :=
    (12 * W ^ 2 *
        (1 + Real.log (W * (X : ℝ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
  have haReal : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hVmin : 0 < Vmin := by
    dsimp only [Vmin]
    have hE : 0 < maynardLongPolylogEnvelope X :=
      lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
    have hbase : 0 < (a : ℝ) ^ (1 / 8 : ℝ) :=
      Real.rpow_pos_of_pos (zero_lt_one.trans_le haReal) _
    have hgain : 0 < ((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26 :=
      Real.rpow_pos_of_pos hbase _
    positivity
  have hfibre : ∀ label : MenonHeathBrownCaseIILabel L X cells,
      ((menonHeathBrownCaseIIColorFibre S color label).card : ℝ) * Vmin ^ 2 ≤ Hmax := by
    intro label
    by_cases hne : (menonHeathBrownCaseIIColorFibre S color label).Nonempty
    · have hactiveLabel := hactive label hne
      obtain ⟨r, hr⟩ := hne
      have hselected := isMenonHeathBrownCaseIISelection_on_colorFibre
        hselection label hr
      have hbox := hselected.2.2.1
      let N : ℝ :=
        (((2 ^ heathBrownBoxFactorExponent
          label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
      let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
        i ∈ (Finset.univ.erase label.factor)}
      let q : I → ℕ := fun i =>
        heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
      let A : ℝ := (groupedDyadicLower q : ℝ)
      let G : ℝ := min T (N ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope X) *
        menonHeathBrownCaseIICoreThreshold L X Q
      let B : ℝ := 12 * W ^ 2 *
        (1 + Real.log (W * (X : ℝ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)
      have hNlower : (a : ℝ) ^ (1 / 8 : ℝ) ≤ N := by
        simpa only [N] using menonHeathBrownCaseIISelection_factorLower ha hselected
      have hdelta : 0 ≤ maynardDerivativeDeficit 26 := by
        rw [maynardDerivativeDeficit]
        positivity
      have hpow : ((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26 ≤
          N ^ maynardDerivativeDeficit 26 :=
        Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hNlower hdelta
      have hmin : min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) ≤
          min T (N ^ maynardDerivativeDeficit 26) := min_le_min_left T hpow
      have hden : 0 < 5120 * maynardLongPolylogEnvelope X := by
        have := one_le_maynardLongPolylogEnvelope X
        positivity
      have hVG : Vmin ≤ G := by
        dsimp only [Vmin, G]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right hmin hden.le) hthreshold.le
      have hAone : 1 ≤ A := by
        dsimp only [A]
        exact_mod_cast one_le_groupedDyadicLower q
      have hApos : 0 < A := zero_lt_one.trans_le hAone
      have hdiv : T / A ≤ T := by
        rw [div_le_iff₀ hApos]
        nlinarith [zero_le_one.trans hT]
      have hTH : B * (T / A + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma)) ≤ Hmax := by
        dsimp only [Hmax]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by
            dsimp only [B, W]
            have hWR : 1 ≤ menonHeathBrownCaseIIComplementWidthConstant := by
              norm_num [menonHeathBrownCaseIIComplementWidthConstant]
            have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
            have hlog : 0 ≤ Real.log
                (menonHeathBrownCaseIIComplementWidthConstant * (X : ℝ)) :=
              Real.log_nonneg (one_le_mul_of_one_le_of_one_le hWR hXR)
            positivity))
          (Real.rpow_nonneg (by positivity) _)
      have hraw := windowRelevant_menonHeathBrownCaseII_baseAmplitude_fibreBound
        (a := (a : ℝ)) (sigma := sigma) (Q := Q) (T := T)
        (S := S) (color := color) (by positivity) hX hT hΔ hΔT hthreshold
        label hbox hactiveLabel.1 hactiveLabel.2 hsigma
      have hsq : Vmin ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hVmin.le hVG 2
      exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans
        (hraw.trans hTH)
    · have hempty : menonHeathBrownCaseIIColorFibre S color label = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hHmax : 0 ≤ Hmax := by
        dsimp only [Hmax, W]
        have hWR : 1 ≤ menonHeathBrownCaseIIComplementWidthConstant := by
          norm_num [menonHeathBrownCaseIIComplementWidthConstant]
        have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
        have hlog : 0 ≤ Real.log
            (menonHeathBrownCaseIIComplementWidthConstant * (X : ℝ)) :=
          Real.log_nonneg (one_le_mul_of_one_le_of_one_le hWR hXR)
        positivity
      rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact hHmax
  have hresult := card_mul_sq_le_card_labels_mul_of_color_fibre_bounds
    S color hVmin (fun _ => Vmin) (fun _ => Hmax)
    (fun _ => le_rfl) (fun _ => le_rfl) (by
      intro label
      simpa only [menonHeathBrownCaseIIColorFibre] using hfibre label)
  simpa only [Vmin, Hmax, W] using hresult

end

end RHTower.Sieve
