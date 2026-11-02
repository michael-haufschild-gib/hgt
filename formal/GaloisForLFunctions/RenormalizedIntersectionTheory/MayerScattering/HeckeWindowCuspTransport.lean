import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.FareyLewisTransferAndCuspSeparation
import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.MayerWindowFoldTransfer

/-!
# The cusp channel of a window Hecke operator

The two dilation branches of `T₂` are logarithmic shifts. Its remaining branches approach
`1/2` and `2` at the two cusps. For an input vanishing above `R`, the upper tail is exactly
`(a+1)^(-2s) f(2a/(a+1))` once `a > 2R`. Thus finite output support is controlled by a
one-sided germ at `2`, rather than by the value at `2` alone.
-/

noncomputable section

open Complex Set Filter Topology

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Beyond twice the input cutoff, precisely the nonlinear cusp branch survives. -/
theorem lewisHeckeT2_eq_cusp_of_two_mul_lt (s : ℂ) {f : ℝ → ℂ} {R a : ℝ}
    (hR : 0 ≤ R) (hf : ∀ x > R, f x = 0) (ha : 2 * R < a) :
    lewisHeckeT2 s f a =
      ((a + 1 : ℝ) : ℂ) ^ (-(2 * s)) * f (2 * a / (a + 1)) := by
  rw [lewisHeckeT2, hf (2 * a) (by linarith), hf (a / 2) (by linarith),
    hf ((a + 1) / 2) (by linarith)]
  ring

/-- Removing the explicit cusp weight recovers the input at a point approaching `2` from below. -/
theorem lewisHeckeT2_normalized_cusp (s : ℂ) {f : ℝ → ℂ} {R a : ℝ}
    (hR : 0 ≤ R) (hf : ∀ x > R, f x = 0) (ha : 2 * R < a) :
    ((a + 1 : ℝ) : ℂ) ^ (2 * s) * lewisHeckeT2 s f a = f (2 * a / (a + 1)) := by
  have ha1 : 0 < a + 1 := by linarith
  rw [lewisHeckeT2_eq_cusp_of_two_mul_lt s hR hf ha, ← mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha1.ne')]
  simp only [add_neg_cancel, Complex.cpow_zero, one_mul]

/-- An upper compact cutoff survives `T₂` exactly when the input vanishes on a left germ at `2`.
The criterion retains the entire germ; vanishing at a single endpoint is insufficient. -/
theorem lewisHeckeT2_upper_cutoff_iff (s : ℂ) {f : ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ x > R, f x = 0) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ a > B, lewisHeckeT2 s f a = 0) ↔
      ∃ b ∈ Ioo (0 : ℝ) 2, ∀ x ∈ Ioo b 2, f x = 0 := by
  constructor
  · rintro ⟨B, hB, hzero⟩
    let C := max B (2 * R) + 1
    have hC : 0 < C := by dsimp [C]; linarith [le_max_left B (2 * R)]
    have hC1 : 0 < C + 1 := by linarith
    refine ⟨2 * C / (C + 1), ⟨div_pos (by linarith) hC1, ?_⟩, ?_⟩
    · apply (div_lt_iff₀ hC1).mpr
      linarith
    · intro x hx
      have hx2 : 0 < 2 - x := by linarith [hx.2]
      have hCx : C < x / (2 - x) := by
        have := (div_lt_iff₀ hC1).mp hx.1
        apply (lt_div_iff₀ hx2).mpr
        nlinarith only [this]
      have harg : 2 * (x / (2 - x)) / (x / (2 - x) + 1) = x := by
        have hden : x / (2 - x) + 1 = 2 / (2 - x) := by
          field_simp [hx2.ne']; ring
        rw [hden]
        field_simp [hx2.ne']
      have hlarge : 2 * R < x / (2 - x) := by
        dsimp [C] at hCx
        linarith [le_max_right B (2 * R)]
      have hBlarge : B < x / (2 - x) := by
        dsimp [C] at hCx
        linarith [le_max_left B (2 * R)]
      have heq := lewisHeckeT2_normalized_cusp s hR hf hlarge
      rw [hzero _ hBlarge, mul_zero, harg] at heq
      exact heq.symm
  · rintro ⟨b, hb, hzero⟩
    refine ⟨max (2 * R) (b / (2 - b)), le_max_of_le_left (by positivity), ?_⟩
    intro a ha
    have haR : 2 * R < a := lt_of_le_of_lt (le_max_left _ _) ha
    have hab : b / (2 - b) < a := lt_of_le_of_lt (le_max_right _ _) ha
    have ha1 : 0 < a + 1 := by linarith
    have hb2 : 0 < 2 - b := by linarith [hb.2]
    have hsmall : 2 * a / (a + 1) < 2 := (div_lt_iff₀ ha1).mpr (by linarith)
    have hlarge : b < 2 * a / (a + 1) := by
      apply (lt_div_iff₀ ha1).mpr
      have := (div_lt_iff₀ hb2).mp hab
      nlinarith only [this]
    rw [lewisHeckeT2_eq_cusp_of_two_mul_lt s hR hf haR, hzero _ ⟨hlarge, hsmall⟩,
      mul_zero]

private theorem periodWindowProfile_eq_zero_iff (s : ℂ) (f : ℝ → ℂ) {b : ℝ}
    (hb : 0 < b) : periodWindowProfile s f b = 0 ↔ f b = 0 := by
  have hw : 0 < (b + b⁻¹) ^ (-3 : ℝ) * b ^ s.re :=
    mul_pos (Real.rpow_pos_of_pos (add_pos hb (inv_pos.mpr hb)) _)
      (Real.rpow_pos_of_pos hb _)
  simp only [periodWindowProfile, mul_eq_zero,
    Complex.ofReal_ne_zero.mpr hw.ne', false_or]

/-- The normalized lift has exactly the same zero set as the original window on `b > 1`. -/
theorem windowPeriodLift_eq_zero_iff (s : ℂ) (H : ℝ → ℝ) {b : ℝ} (hb : 1 < b) :
    windowPeriodLift s H b = 0 ↔ H (-Real.log b) = 0 := by
  rw [← periodWindowProfile_eq_zero_iff s _ (zero_lt_one.trans hb),
    periodWindowProfile_windowPeriodLift s H hb, Complex.ofReal_eq_zero]

private theorem windowPeriodLift_upper_cutoff (s : ℂ) {H : ℝ → ℝ} {A : ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) :
    ∀ b > max 1 (Real.exp A), windowPeriodLift s H b = 0 := by
  intro b hb
  have hb1 : 1 < b := lt_of_le_of_lt (le_max_left _ _) hb
  have hAb : A < Real.log b := (Real.lt_log_iff_exp_lt (zero_lt_one.trans hb1)).mpr
    (lt_of_le_of_lt (le_max_right _ _) hb)
  apply (windowPeriodLift_eq_zero_iff s H hb1).mpr
  exact hv _ fun h => by linarith [h.1]

/-- Exact finite-window admission for the Hecke image of a window lift. The open interval
samples the right germ of `H` at `-log 2`, including windows whose endpoint is `-log 2`. -/
theorem hecke_windowPeriodLift_upper_cutoff_iff (s : ℂ) {H : ℝ → ℝ} {A : ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ a > B, lewisHeckeT2 s (windowPeriodLift s H) a = 0) ↔
      ∃ b ∈ Ico (1 : ℝ) 2, ∀ x ∈ Ioo b 2, H (-Real.log x) = 0 := by
  rw [lewisHeckeT2_upper_cutoff_iff s
    (show 0 ≤ max 1 (Real.exp A) by positivity) (windowPeriodLift_upper_cutoff s hv)]
  constructor
  · rintro ⟨b, hb, hzero⟩
    refine ⟨max 1 b, ⟨le_max_left _ _, max_lt (by norm_num) hb.2⟩, ?_⟩
    intro x hx
    have hx1 : 1 < x := lt_of_le_of_lt (le_max_left _ _) hx.1
    exact (windowPeriodLift_eq_zero_iff s H hx1).mp
      (hzero x ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, hx.2⟩)
  · rintro ⟨b, hb, hzero⟩
    refine ⟨b, ⟨by linarith [hb.1], hb.2⟩, ?_⟩
    intro x hx
    exact (windowPeriodLift_eq_zero_iff s H (lt_of_le_of_lt hb.1 hx.1)).mpr (hzero x hx)

/-- Before the first prime enters, every window lift has a finite Hecke output cutoff. -/
theorem hecke_windowPeriodLift_upper_cutoff_of_lt_log_two (s : ℂ) {H : ℝ → ℝ} {A : ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (hA : A < Real.log 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a > B, lewisHeckeT2 s (windowPeriodLift s H) a = 0 := by
  apply (hecke_windowPeriodLift_upper_cutoff_iff s hv).mpr
  refine ⟨max 1 (Real.exp A), ⟨le_max_left _ _, max_lt (by norm_num) ?_⟩, ?_⟩
  · exact (Real.lt_log_iff_exp_lt (by norm_num)).mp hA
  · intro x hx
    have hx1 : 1 < x := lt_of_le_of_lt (le_max_left _ _) hx.1
    exact (windowPeriodLift_eq_zero_iff s H hx1).mp
      (windowPeriodLift_upper_cutoff s hv x hx.1)

/-- Reflection survives the full Hecke action, including its cusp branch. -/
theorem lewisModularInversion_hecke_windowPeriodLift (s : ℂ) (H : ℝ → ℝ) {a : ℝ}
    (ha : 0 < a) :
    lewisModularInversion s (lewisHeckeT2 s (windowPeriodLift s H)) a =
      lewisHeckeT2 s (windowPeriodLift s H) a := by
  rw [lewisModularInversion_heckeT2 s _ ha]
  unfold lewisHeckeT2
  rw [lewisModularInversion_windowPeriodLift s H (by positivity : 0 < 2 * a),
    lewisModularInversion_windowPeriodLift s H (by positivity : 0 < a / 2),
    lewisModularInversion_windowPeriodLift s H (by positivity : 0 < (a + 1) / 2),
    lewisModularInversion_windowPeriodLift s H (by positivity : 0 < 2 * a / (a + 1))]

/-- A finite multiplicative window for the Hecke image exists exactly when the window's
right germ at the first-prime position vanishes. Inversion ties the two cusp conditions. -/
theorem hecke_windowPeriodLift_finite_window_iff (s : ℂ) {H : ℝ → ℝ} {A : ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) :
    (∃ B : ℝ, 1 ≤ B ∧ ∀ a > 0, a ∉ Icc B⁻¹ B →
      lewisHeckeT2 s (windowPeriodLift s H) a = 0) ↔
      ∃ b ∈ Ico (1 : ℝ) 2, ∀ x ∈ Ioo b 2, H (-Real.log x) = 0 := by
  rw [← hecke_windowPeriodLift_upper_cutoff_iff s hv]
  constructor
  · rintro ⟨B, hB, hzero⟩
    refine ⟨B, by linarith, fun a ha => hzero a (by linarith) ?_⟩
    exact fun hm => (not_lt_of_ge hm.2) ha
  · rintro ⟨B, hB, hzero⟩
    let C := max 1 B
    have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨C, le_max_left _ _, ?_⟩
    intro a ha hout
    by_cases hupper : C < a
    · exact hzero a (lt_of_le_of_lt (le_max_right _ _) hupper)
    have hlower : a < C⁻¹ := by
      by_contra hn
      exact hout ⟨le_of_not_gt hn, le_of_not_gt hupper⟩
    have hinv : C < a⁻¹ := by
      apply (lt_inv_comm₀ hC ha).mpr
      exact hlower
    have hz := hzero a⁻¹ (lt_of_le_of_lt (le_max_right _ _) hinv)
    have hfix := lewisModularInversion_hecke_windowPeriodLift s H ha
    rw [lewisModularInversion, hz, mul_zero] at hfix
    exact hfix.symm

/-- A continuous window which is nonzero at the first-prime position produces a noncompact
Hecke tail, at every complex parameter. No resonance or positivity assumption enters. -/
theorem hecke_windowPeriodLift_no_cutoff_of_first_prime_ne_zero (s : ℂ)
    {H : ℝ → ℝ} {A : ℝ} (hc : Continuous H)
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (hprime : H (-Real.log 2) ≠ 0) :
    ¬ ∃ B : ℝ, 0 ≤ B ∧ ∀ a > B, lewisHeckeT2 s (windowPeriodLift s H) a = 0 := by
  rw [hecke_windowPeriodLift_upper_cutoff_iff s hv]
  rintro ⟨b, hb, hzero⟩
  have hcont : ContinuousAt (fun x : ℝ => H (-Real.log x)) 2 :=
    hc.continuousAt.comp (Real.continuousAt_log (by norm_num)).neg
  obtain ⟨l, u, hlu, hne⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hcont.eventually_ne hprime)
  have hmax : max b l < 2 := max_lt hb.2 hlu.1
  let x := (max b l + 2) / 2
  have hx2 : x < 2 := by dsimp [x]; linarith
  have hxmax : max b l < x := by dsimp [x]; linarith
  have hxb : b < x := lt_of_le_of_lt (le_max_left _ _) hxmax
  have hxl : l < x := lt_of_le_of_lt (le_max_right _ _) hxmax
  exact hne ⟨hxl, hx2.trans hlu.2⟩ (hzero x ⟨hxb, hx2⟩)

#print axioms lewisHeckeT2_upper_cutoff_iff
#print axioms hecke_windowPeriodLift_finite_window_iff
#print axioms hecke_windowPeriodLift_no_cutoff_of_first_prime_ne_zero

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
