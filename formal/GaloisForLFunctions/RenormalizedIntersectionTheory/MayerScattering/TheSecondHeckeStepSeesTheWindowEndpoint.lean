import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckeWindowCuspTransport

/-!
# The second Hecke step sees the window endpoint

Below multiplicative radius `4/3`, the left germ of `T₂f` at `2` is precisely the
halved left germ of `f` at `1`. Thus a second Hecke step detects the endpoint germ
which the first step misses. Arbitrarily short smooth windows admit a compact
first image and a noncompact second image.
-/

noncomputable section
open Complex Set

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

open GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

private theorem cuspThreshold_mem {R : ℝ} (hR : 1 ≤ R) (hR4 : R < 4 / 3) :
    R / (2 - R) ∈ Ioo (0 : ℝ) 2 := by
  have hd : 0 < 2 - R := by linarith
  exact ⟨div_pos (by linarith) hd, (div_lt_iff₀ hd).mpr (by linarith)⟩

/-- Near the first cusp, a sufficiently short input leaves exactly the halving branch. -/
theorem lewisHeckeT2_eq_half_near_two (s : ℂ) {f : ℝ → ℂ} {R x : ℝ}
    (hR : 1 ≤ R) (hR4 : R < 4 / 3) (hf : ∀ y > R, f y = 0)
    (hx : R / (2 - R) < x) :
    lewisHeckeT2 s f x = (2 : ℂ) ^ (-(2 * s)) * f (x / 2) := by
  have hd : 0 < 2 - R := by linarith
  have hb : R < x * (2 - R) := (div_lt_iff₀ hd).mp hx
  have hx1 : 1 < x := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hd.le
    nlinarith only [hm, hb, hR]
  have hlin : R < (x + 1) / 2 := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos hd.le
      (show x + 1 - 2 * R ≤ 0 by linarith [le_of_not_gt hn])
    nlinarith only [hm, hb, sq_nonneg (R - 1)]
  have hfrac : R < 2 * x / (x + 1) :=
    (lt_div_iff₀ (by linarith : 0 < x + 1)).mpr (by nlinarith only [hb])
  rw [lewisHeckeT2, hf (2 * x) (by linarith), hf ((x + 1) / 2) hlin,
    hf (2 * x / (x + 1)) hfrac]
  ring

private theorem hecke_near_two_zero_iff (s : ℂ) {f : ℝ → ℂ} {R x : ℝ}
    (hR : 1 ≤ R) (hR4 : R < 4 / 3) (hf : ∀ y > R, f y = 0)
    (hx : R / (2 - R) < x) :
    lewisHeckeT2 s f x = 0 ↔ f (x / 2) = 0 := by
  rw [lewisHeckeT2_eq_half_near_two s hR hR4 hf hx]
  constructor
  · intro hz
    have h := congrArg (fun z : ℂ => (2 : ℂ) ^ (2 * s) * z) hz
    rw [← mul_assoc, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)] at h
    simpa only [add_neg_cancel, Complex.cpow_zero, one_mul, mul_zero] using h
  · intro hz
    rw [hz, mul_zero]

/-- The second Hecke image of an input supported below `4/3` has a finite upper cutoff
exactly when the input vanishes on a left germ at `1`. -/
theorem lewisHeckeT2_twice_upper_cutoff_iff (s : ℂ) {f : ℝ → ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hR4 : R < 4 / 3) (hf : ∀ y > R, f y = 0) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ a > B, lewisHeckeT2 s (lewisHeckeT2 s f) a = 0) ↔
      ∃ b ∈ Ioo (0 : ℝ) 1, ∀ x ∈ Ioo b 1, f x = 0 := by
  obtain ⟨B, hB, hTf⟩ := (lewisHeckeT2_upper_cutoff_iff s
    (show 0 ≤ R by linarith) hf).mpr ⟨R, ⟨by linarith, by linarith⟩, fun x hx => hf x hx.1⟩
  rw [lewisHeckeT2_upper_cutoff_iff s hB hTf]
  have hc := cuspThreshold_mem hR hR4
  constructor
  · rintro ⟨b, hb, hz⟩
    let d := max b (R / (2 - R))
    have hd0 : 0 < d := lt_of_lt_of_le hb.1 (le_max_left _ _)
    have hd2 : d < 2 := max_lt hb.2 hc.2
    refine ⟨d / 2, ⟨by linarith, by linarith⟩, fun x hx => ?_⟩
    have hxd : d < 2 * x := by linarith [hx.1]
    have hxb := lt_of_le_of_lt (le_max_left b (R / (2 - R))) hxd
    have hxc := lt_of_le_of_lt (le_max_right b (R / (2 - R))) hxd
    have he := (hecke_near_two_zero_iff s hR hR4 hf hxc).mp (hz (2 * x) ⟨hxb, by linarith [hx.2]⟩)
    have harg : 2 * x / 2 = x := by ring
    rwa [harg] at he
  · rintro ⟨b, hb, hz⟩
    let d := max (2 * b) (R / (2 - R))
    have hd0 : 0 < d := lt_of_lt_of_le (by linarith [hb.1]) (le_max_left _ _)
    have hd2 : d < 2 := max_lt (by linarith [hb.2]) hc.2
    refine ⟨d, ⟨hd0, hd2⟩, fun x hx => ?_⟩
    apply (hecke_near_two_zero_iff s hR hR4 hf
      (lt_of_le_of_lt (le_max_right _ _) hx.1)).mpr
    apply hz
    exact ⟨by linarith [le_max_left (2 * b) (R / (2 - R)), hx.1], by linarith [hx.2]⟩

private theorem windowPeriodLift_zero_iff_below_one (s : ℂ) (H : ℝ → ℝ)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    windowPeriodLift s H x = 0 ↔ H (Real.log x) = 0 := by
  have hxi : 1 < x⁻¹ := (lt_inv_comm₀ zero_lt_one hx).mpr (by simpa using hx1)
  have he : windowPeriodLift s H x = 0 ↔ windowPeriodLift s H x⁻¹ = 0 := by
    constructor
    · intro hz
      have h := lewisModularInversion_windowPeriodLift s H (inv_pos.mpr hx)
      rw [lewisModularInversion, inv_inv, hz, mul_zero] at h
      exact h.symm
    · intro hz
      have h := lewisModularInversion_windowPeriodLift s H hx
      rw [lewisModularInversion, hz, mul_zero] at h
      exact h.symm
  rw [he, windowPeriodLift_eq_zero_iff s H hxi, Real.log_inv, neg_neg]

/-- Below length `log(4/3)`, the second Hecke image is compact at the upper cusp exactly
when the original window vanishes on a left neighbourhood of its endpoint `0`. -/
theorem hecke_windowPeriodLift_twice_upper_cutoff_iff (s : ℂ) {H : ℝ → ℝ} {A : ℝ}
    (hv : ∀ y, y ∉ Icc (-A) 0 → H y = 0) (hA : A < Real.log (4 / 3)) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ a > B,
      lewisHeckeT2 s (lewisHeckeT2 s (windowPeriodLift s H)) a = 0) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ Ioo (-ε) 0, H u = 0 := by
  let R := max 1 (Real.exp A)
  have hR : 1 ≤ R := le_max_left _ _
  have hR4 : R < 4 / 3 := max_lt (by norm_num)
    ((Real.lt_log_iff_exp_lt (by norm_num)).mp hA)
  have hf : ∀ x > R, windowPeriodLift s H x = 0 := by
    intro x hx
    have hx1 : 1 < x := lt_of_le_of_lt hR hx
    apply (windowPeriodLift_eq_zero_iff s H hx1).mpr
    have hAx : A < Real.log x := (Real.lt_log_iff_exp_lt (by linarith)).mpr
      (lt_of_le_of_lt (le_max_right _ _) hx)
    exact hv _ fun hm => by linarith [hm.1]
  rw [lewisHeckeT2_twice_upper_cutoff_iff s hR hR4 hf]
  constructor
  · rintro ⟨b, hb, hz⟩
    have hl : Real.log b < 0 := Real.log_neg hb.1 hb.2
    refine ⟨-Real.log b, by linarith, fun u hu => ?_⟩
    have hub : b < Real.exp u := by
      rw [← Real.exp_log hb.1]
      exact Real.exp_lt_exp.mpr (by linarith [hu.1])
    have hu1 : Real.exp u < 1 := by simpa using Real.exp_lt_exp.mpr hu.2
    have hzero := (windowPeriodLift_zero_iff_below_one s H (Real.exp_pos u) hu1).mp
      (hz (Real.exp u) ⟨hub, hu1⟩)
    simpa only [Real.log_exp] using hzero
  · rintro ⟨ε, hε, hz⟩
    have hb : Real.exp (-ε) < 1 := by
      simpa using Real.exp_lt_exp.mpr (show -ε < 0 by linarith)
    refine ⟨Real.exp (-ε), ⟨Real.exp_pos _, hb⟩, fun x hx => ?_⟩
    have hx0 : 0 < x := (Real.exp_pos _).trans hx.1
    apply (windowPeriodLift_zero_iff_below_one s H hx0 hx.2).mpr
    exact hz _ ⟨(Real.lt_log_iff_exp_lt hx0).mpr hx.1, Real.log_neg hx0 hx.2⟩

#print axioms lewisHeckeT2_twice_upper_cutoff_iff
#print axioms hecke_windowPeriodLift_twice_upper_cutoff_iff

/-- Every positive window contains a smooth test whose first Hecke image has finite support
at the upper cusp but whose second image does not, simultaneously at all complex parameters. -/
theorem exists_windowTest_hecke_cutoff_but_twice_no_cutoff {A : ℝ} (hA : 0 < A) :
    ∃ H : ℝ → ℝ, IsWindowTest A H ∧ ∀ s : ℂ,
      (∃ C : ℝ, 0 ≤ C ∧ ∀ a > C, lewisHeckeT2 s (windowPeriodLift s H) a = 0) ∧
      ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ a > C,
        lewisHeckeT2 s (lewisHeckeT2 s (windowPeriodLift s H)) a = 0 := by
  have hlog : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
  let B := min A (Real.log (4 / 3)) / 2
  have hB : 0 < B := div_pos (lt_min hA hlog) (by norm_num)
  have hBA : B ≤ A := by
    have hm := min_le_left A (Real.log (4 / 3))
    dsimp [B]
    linarith
  have hBl : B < Real.log (4 / 3) := by
    have hm := min_le_right A (Real.log (4 / 3))
    dsimp [B]
    linarith
  have hB2 : B < Real.log 2 := hBl.trans
    (Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num))
  obtain ⟨H, hsupp, hdiff, -⟩ :=
    (isOpen_Ioo : IsOpen (Ioo (-B) 0)).exists_contDiff_support_eq (n := 2)
  have hvB : ∀ u, u ∉ Icc (-B) 0 → H u = 0 := by
    intro u hu
    by_contra hn
    have hm : u ∈ Ioo (-B) 0 := hsupp ▸ hn
    exact hu ⟨hm.1.le, hm.2.le⟩
  have hvA : ∀ u, u ∉ Icc (-A) 0 → H u = 0 := by
    intro u hu
    exact hvB u fun hm => hu ⟨by linarith [hm.1], hm.2⟩
  refine ⟨H, ⟨hdiff, hvA⟩, fun s => ⟨
    hecke_windowPeriodLift_upper_cutoff_of_lt_log_two s hvB hB2, ?_⟩⟩
  rw [hecke_windowPeriodLift_twice_upper_cutoff_iff s hvB hBl]
  rintro ⟨ε, hε, hz⟩
  let u := -(min B ε / 2)
  have hm : 0 < min B ε := lt_min hB hε
  have hu0 : u < 0 := by dsimp [u]; linarith
  have huB : -B < u := by
    have := min_le_left B ε
    dsimp [u]
    linarith
  have huε : -ε < u := by
    have := min_le_right B ε
    dsimp [u]
    linarith
  have hn : u ∈ Function.support H := hsupp.symm ▸ (show u ∈ Ioo (-B) 0 from ⟨huB, hu0⟩)
  exact hn (hz u ⟨huε, hu0⟩)

#print axioms exists_windowTest_hecke_cutoff_but_twice_no_cutoff

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
