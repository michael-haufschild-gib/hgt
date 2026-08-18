import Mathlib

/-!
# The Mellin transform of a summatory step profile

For a profile `R : ℕ → ℝ` the step function `x ↦ R ⌊x⌋₊` has, on `Re s > max(0, θ)` with `R`
bounded by `C N^θ`,

```text
s ∫_1^∞ R⌊x⌋ x^{-s-1} dx  =  ∑_{k} R(k+1) ( (k+1)^{-s} − (k+2)^{-s} ) ,
```

the integral form of Abel summation.  The half line is partitioned into the unit windows
`[k+1, k+2)` on which the step function is constant.
-/

noncomputable section

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

/-- The unit windows partition the closed half line `[1,∞)`. -/
theorem iUnion_unitWindow : (⋃ k : ℕ, Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2)) = Set.Ici (1:ℝ) := by
  ext x
  constructor
  · rintro ⟨s, ⟨k, rfl⟩, hx⟩
    have : (k : ℝ) + 1 ≤ x := hx.1
    have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    simp only [Set.mem_Ici]
    linarith
  · intro hx
    simp only [Set.mem_Ici] at hx
    refine Set.mem_iUnion.2 ⟨⌊x⌋₊ - 1, ?_⟩
    have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
    have h1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.2 hx
    have hfl : ((⌊x⌋₊ : ℝ)) ≤ x := Nat.floor_le hx0
    have hfl2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have hcast : ((⌊x⌋₊ - 1 : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - 1 := by
      have : (1:ℕ) ≤ ⌊x⌋₊ := h1
      push_cast [Nat.cast_sub this]
      ring
    rw [Set.mem_Ico, hcast]
    constructor
    · linarith
    · linarith

theorem pairwise_disjoint_unitWindow :
    Pairwise (Function.onFun Disjoint fun k : ℕ => Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2)) := by
  intro i j hij
  simp only [Function.onFun]
  rcases lt_or_gt_of_ne hij with h | h
  · refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    have h1 : x < (i : ℝ) + 2 := hxi.2
    have h2 : (j : ℝ) + 1 ≤ x := hxj.1
    have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  · refine Set.disjoint_left.2 ?_
    intro x hxi hxj
    have h1 : x < (j : ℝ) + 2 := hxj.2
    have h2 : (i : ℝ) + 1 ≤ x := hxi.1
    have : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith

/-- The floor is constant on a unit window. -/
theorem floor_eq_of_mem_unitWindow {k : ℕ} {x : ℝ} (hx : x ∈ Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2)) :
    ⌊x⌋₊ = k + 1 := by
  have hx0 : (0:ℝ) ≤ x := by
    have : (0:ℝ) ≤ (k : ℝ) + 1 := by positivity
    exact le_trans this hx.1
  rw [Nat.floor_eq_iff hx0]
  constructor
  · push_cast
    exact hx.1
  · push_cast
    have := hx.2
    linarith

theorem abs_profile_floor_le {R : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |R N| ≤ C * (N : ℝ) ^ θ) {x : ℝ} (hx : 1 ≤ x) :
    |R ⌊x⌋₊| ≤ C * (x ^ θ + 1) := by
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have h1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).2 hx
  have hone : (1:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
  have hle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hkey : ((⌊x⌋₊ : ℕ) : ℝ) ^ θ ≤ x ^ θ + 1 := by
    rcases le_or_gt 0 θ with hθ | hθ
    · have : ((⌊x⌋₊ : ℕ) : ℝ) ^ θ ≤ x ^ θ :=
        Real.rpow_le_rpow (by linarith) hle hθ
      linarith
    · have h2 : ((⌊x⌋₊ : ℕ) : ℝ) ^ θ ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hone (le_of_lt hθ)
      have h3 : (0:ℝ) ≤ x ^ θ := Real.rpow_nonneg hx0 θ
      linarith
  calc |R ⌊x⌋₊| ≤ C * ((⌊x⌋₊ : ℕ) : ℝ) ^ θ := hb _
    _ ≤ C * (x ^ θ + 1) := by
        exact mul_le_mul_of_nonneg_left hkey hC

theorem norm_stepProfile_le {R : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |R N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} {x : ℝ} (hx : 1 ≤ x) :
    ‖(R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)‖
      ≤ C * (x ^ (θ - s.re - 1) + x ^ (-s.re - 1)) := by
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hxpos, Complex.norm_real]
  have hre : (-s - 1).re = -s.re - 1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  rw [hre]
  have hnn : (0:ℝ) ≤ x ^ (-s.re - 1) := Real.rpow_nonneg (le_of_lt hxpos) _
  have hsplit : x ^ (θ - s.re - 1) = x ^ θ * x ^ (-s.re - 1) := by
    rw [← Real.rpow_add hxpos]
    ring_nf
  calc |R ⌊x⌋₊| * x ^ (-s.re - 1)
      ≤ (C * (x ^ θ + 1)) * x ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right (abs_profile_floor_le hC hb hx) hnn
    _ = C * (x ^ θ * x ^ (-s.re - 1) + x ^ (-s.re - 1)) := by ring
    _ = C * (x ^ (θ - s.re - 1) + x ^ (-s.re - 1)) := by rw [hsplit]

theorem integrableOn_stepProfile {R : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |R N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re) (hθs : θ < s.re) :
    IntegrableOn (fun x : ℝ => (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) (Set.Ioi (1:ℝ)) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) (volume.restrict (Set.Ioi (1:ℝ))) := by
    refine (Complex.measurable_ofReal.comp
      (Measurable.of_discrete.comp Nat.measurable_floor)).aestronglyMeasurable.mul ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have htpos : (0:ℝ) < t := lt_trans one_pos ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-s - 1)
      (Or.inr (ne_of_gt htpos))).continuousWithinAt
  have hdom : IntegrableOn
      (fun x : ℝ => C * (x ^ (θ - s.re - 1) + x ^ (-s.re - 1))) (Set.Ioi (1:ℝ)) := by
    refine MeasureTheory.Integrable.const_mul ?_ C
    refine MeasureTheory.Integrable.add ?_ ?_
    · exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    · exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine MeasureTheory.Integrable.mono' hdom hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  exact norm_stepProfile_le hC hb (le_of_lt hx)

theorem integral_unitWindow_cpow (k : ℕ) {s : ℂ} (hs : s ≠ 0) :
    (∫ x in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2), (x : ℂ) ^ (-s - 1))
      = ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) / s := by
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hle : ((k : ℝ) + 1) ≤ ((k : ℝ) + 2) := by linarith
  have hzero : (0:ℝ) ∉ Set.uIcc ((k : ℝ) + 1) ((k : ℝ) + 2) := by
    rw [Set.uIcc_of_le hle]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h
    linarith
  have hr : (-s - 1) ≠ -1 := by
    intro h
    apply hs
    have : -s = 0 := by linear_combination h
    simpa using congrArg (fun z => -z) this
  have hcpow := integral_cpow (a := (k : ℝ) + 1) (b := (k : ℝ) + 2) (r := -s - 1)
    (Or.inr ⟨hr, hzero⟩)
  have hexp : -s - 1 + 1 = -s := by ring
  rw [hexp] at hcpow
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle, hcpow]
  field_simp
  ring

/-- **The integral form of Abel summation.**  The Mellin transform of the step profile
`x ↦ R ⌊x⌋` is `1/s` times the increment series of `R`. -/
theorem mellin_stepProfile_eq_tsum {R : ℕ → ℝ} {C θ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N : ℕ, |R N| ≤ C * (N : ℝ) ^ θ) {s : ℂ} (hs : 0 < s.re) (hθs : θ < s.re) :
    s * (∫ x in Set.Ioi (1:ℝ), (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      = ∑' k : ℕ, (R (k + 1) : ℂ)
          * ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hint := integrableOn_stepProfile hC hb hs hθs
  have hintIci : IntegrableOn (fun x : ℝ => (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      (Set.Ici (1:ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hint
  have hIci : (∫ x in Set.Ioi (1:ℝ), (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      = ∫ x in Set.Ici (1:ℝ), (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) :=
    MeasureTheory.integral_Ici_eq_integral_Ioi.symm
  have hsplit : (∫ x in Set.Ici (1:ℝ), (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      = ∑' k : ℕ, ∫ x in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
          (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) := by
    rw [← iUnion_unitWindow]
    refine MeasureTheory.integral_iUnion (fun k => measurableSet_Ico)
      pairwise_disjoint_unitWindow ?_
    rw [iUnion_unitWindow]
    exact hintIci
  have hpiece : ∀ k : ℕ, (∫ x in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
      (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      = (R (k + 1) : ℂ)
        * ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) / s := by
    intro k
    have hcongr : (∫ x in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
        (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
        = ∫ x in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
          (R (k + 1) : ℂ) * (x : ℂ) ^ (-s - 1) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ico ?_
      intro x hx
      show (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) = (R (k + 1) : ℂ) * (x : ℂ) ^ (-s - 1)
      rw [floor_eq_of_mem_unitWindow hx]
    rw [hcongr, MeasureTheory.integral_const_mul, integral_unitWindow_cpow k hs0]
    ring
  rw [hIci, hsplit]
  have hfun : (fun k : ℕ => ∫ x in Set.Ico ((k : ℝ) + 1) ((k : ℝ) + 2),
      (R ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))
      = fun k : ℕ => s⁻¹ * ((R (k + 1) : ℂ)
        * ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s))) := by
    funext k
    rw [hpiece k]
    field_simp
  rw [hfun, tsum_mul_left, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]

end GaloisForLFunctions.HTGeometry

end
