import Mathlib

/-!
# The Paley–Zygmund inequality

A nonnegative random variable with a finite second moment exceeds any fixed fraction of its mean
with probability bounded below by the ratio of its moments:

```text
(1 − θ)² (E Z)²  ≤  E[Z²] · P(Z > θ E Z) ,      0 ≤ θ < 1 .
```

The proof avoids Hölder.  Splitting the mean at the threshold gives `(1 − θ) E Z ≤ E[Z · 1_A]`, and
the pointwise arithmetic–geometric bound `Z · 1_A ≤ (t/2) 1_A + Z²/(2t)`, valid for every `t > 0`
because it rearranges to `(t − Z)² ≥ 0`, integrates to `E[Z · 1_A] ≤ (t/2) P(A) + E[Z²]/(2t)`.
Choosing `t = √(E[Z²]/P(A))` makes the right side `√(E[Z²] P(A))`, which is Cauchy–Schwarz with the
constant recovered exactly.

This is the standard route from an unbounded second moment to a genuine probabilistic lower bound:
it converts `E[Z²] → ∞` with `E[Z⁴] = O((E[Z²])²)` into a uniform positive probability that `Z` is
large, which no moment identity alone supplies.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The pointwise arithmetic–geometric bound behind Cauchy–Schwarz. -/
theorem le_half_add_sq_div (t : ℝ) (ht : 0 < t) (z : ℝ) : z ≤ t / 2 + z ^ 2 / (2 * t) := by
  rw [div_add_div _ _ (by norm_num : (2 : ℝ) ≠ 0) (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (t - z)]

/-- **The Paley–Zygmund inequality.** -/
theorem paley_zygmund [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hmZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (hZi : Integrable Z μ) (hZ2 : Integrable (fun x => Z x ^ 2) μ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ x, Z x ∂μ) ^ 2
      ≤ (∫ x, Z x ^ 2 ∂μ) * (μ {x | θ * (∫ x, Z x ∂μ) < Z x}).toReal := by
  set m : ℝ := ∫ x, Z x ∂μ with hmdef
  set s : ℝ := ∫ x, Z x ^ 2 ∂μ with hsdef
  set A : Set Ω := {x | θ * m < Z x} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_lt measurable_const hmZ
  have hm0 : 0 ≤ m := integral_nonneg hZ0
  have hs0 : 0 ≤ s := integral_nonneg fun x => sq_nonneg _
  set p : ℝ := (μ A).toReal with hpdef
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hθm : 0 ≤ θ * m := mul_nonneg hθ0 hm0
  -- split the mean at the threshold
  have hsplit : (1 - θ) * m ≤ ∫ x in A, Z x ∂μ := by
    have hadd : (∫ x in A, Z x ∂μ) + ∫ x in Aᶜ, Z x ∂μ = m := integral_add_compl hAmeas hZi
    have hconst : IntegrableOn (fun _ : Ω => θ * m) Aᶜ μ :=
      (integrable_const (θ * m)).integrableOn
    have hle : ∫ x in Aᶜ, Z x ∂μ ≤ ∫ _x in Aᶜ, (θ * m) ∂μ := by
      refine setIntegral_mono_on hZi.integrableOn hconst hAmeas.compl ?_
      intro x hx
      simpa [hAdef, not_lt] using hx
    have hval : ∫ _x in Aᶜ, (θ * m) ∂μ = (μ Aᶜ).toReal * (θ * m) := by
      simp [smul_eq_mul, measureReal_def]
    have hle1 : (μ Aᶜ).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (by norm_num) (prob_le_one (μ := μ) (s := Aᶜ))
    have : ∫ x in Aᶜ, Z x ∂μ ≤ θ * m := by
      refine hle.trans ?_
      rw [hval]
      nlinarith [hθm, hle1, ENNReal.toReal_nonneg (a := μ Aᶜ)]
    linarith [hadd, this]
  -- the arithmetic-geometric bound on the tail piece
  have hAM : ∀ t : ℝ, 0 < t → ∫ x in A, Z x ∂μ ≤ (t / 2) * p + s / (2 * t) := by
    intro t ht
    have hconst : IntegrableOn (fun _ : Ω => t / 2) A μ :=
      (integrable_const (t / 2)).integrableOn
    have hquad : IntegrableOn (fun x : Ω => Z x ^ 2 / (2 * t)) A μ :=
      (hZ2.integrableOn).div_const _
    have hmono : ∫ x in A, Z x ∂μ ≤ ∫ x in A, (t / 2 + Z x ^ 2 / (2 * t)) ∂μ := by
      refine setIntegral_mono_on hZi.integrableOn (hconst.add hquad) hAmeas ?_
      intro x _
      exact le_half_add_sq_div t ht (Z x)
    have hsplit2 : ∫ x in A, (t / 2 + Z x ^ 2 / (2 * t)) ∂μ
        = (μ A).toReal * (t / 2) + (∫ x in A, Z x ^ 2 ∂μ) / (2 * t) := by
      rw [integral_add hconst hquad, setIntegral_const, smul_eq_mul, integral_div,
        measureReal_def]
    have htail : ∫ x in A, Z x ^ 2 ∂μ ≤ s := by
      have hcompl : 0 ≤ ∫ x in Aᶜ, Z x ^ 2 ∂μ :=
        setIntegral_nonneg hAmeas.compl fun x _ => sq_nonneg _
      have hadd : (∫ x in A, Z x ^ 2 ∂μ) + ∫ x in Aᶜ, Z x ^ 2 ∂μ = s :=
        integral_add_compl hAmeas hZ2
      linarith
    have hdiv : (∫ x in A, Z x ^ 2 ∂μ) / (2 * t) ≤ s / (2 * t) := by
      gcongr
    calc ∫ x in A, Z x ∂μ ≤ ∫ x in A, (t / 2 + Z x ^ 2 / (2 * t)) ∂μ := hmono
      _ = (μ A).toReal * (t / 2) + (∫ x in A, Z x ^ 2 ∂μ) / (2 * t) := hsplit2
      _ ≤ p * (t / 2) + s / (2 * t) := by rw [← hpdef]; linarith
      _ = (t / 2) * p + s / (2 * t) := by ring
  -- conclude
  rcases eq_or_lt_of_le hp0 with hpz | hppos
  · -- zero probability forces a zero mean
    have hmz : m = 0 := by
      by_contra hne
      have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hne)
      have hkey : ∀ t : ℝ, 0 < t → (1 - θ) * m ≤ s / (2 * t) := by
        intro t ht
        have := hsplit.trans (hAM t ht)
        rw [← hpz] at this
        simpa using this
      obtain ⟨t, ht, hts⟩ : ∃ t : ℝ, 0 < t ∧ s / (2 * t) < (1 - θ) * m := by
        refine ⟨(s + 1) / ((1 - θ) * m), by positivity, ?_⟩
        rw [div_lt_iff₀ (by positivity)]
        have hθne : (1 : ℝ) - θ ≠ 0 := by linarith
        have h1 : (2 : ℝ) * ((s + 1) / ((1 - θ) * m)) * ((1 - θ) * m) = 2 * (s + 1) := by
          field_simp
        nlinarith [hs0, h1]
      exact absurd (hkey t ht) (not_le.2 hts)
    rw [hmz, ← hpz]
    simp
  · -- positive probability: optimize the free parameter
    rcases eq_or_lt_of_le hs0 with hsz | hspos
    · -- a zero second moment forces a zero mean
      have hZae : Z =ᵐ[μ] 0 := by
        have hsq : (fun x => Z x ^ 2) =ᵐ[μ] 0 :=
          (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (Z x)) hZ2).1 hsz.symm
        filter_upwards [hsq] with x hx
        have : Z x ^ 2 = 0 := hx
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      have hmz : m = 0 := by
        rw [hmdef, integral_congr_ae hZae]
        simp
      rw [hmz, ← hsz]
      simp
    · have hpne : p ≠ 0 := ne_of_gt hppos
      have ht : (0 : ℝ) < Real.sqrt (s / p) := Real.sqrt_pos.2 (by positivity)
      have hr : Real.sqrt (s / p) ^ 2 = s / p := Real.sq_sqrt (by positivity)
      set r : ℝ := Real.sqrt (s / p) with hrdef
      have hsr : s = r ^ 2 * p := by
        rw [hr]
        field_simp
      have hbound := hsplit.trans (hAM r ht)
      have hkey : (r / 2) * p + s / (2 * r) = Real.sqrt (s * p) := by
        have hsp : s * p = (r * p) ^ 2 := by rw [hsr]; ring
        rw [hsp, Real.sqrt_sq (by positivity), hsr]
        field_simp
        ring
      rw [hkey] at hbound
      have hlhs : 0 ≤ (1 - θ) * m := mul_nonneg (by linarith) hm0
      have hsp2 : Real.sqrt (s * p) ^ 2 = s * p := Real.sq_sqrt (by positivity)
      nlinarith [hbound, hlhs, hsp2, Real.sqrt_nonneg (s * p)]

end GaloisForLFunctions.HTGeometry

end
